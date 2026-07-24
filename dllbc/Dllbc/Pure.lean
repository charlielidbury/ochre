import Dllbc.Value

/-!
# The pure fragment's reduction (§4)

The comptime fragment is a tiny standard type theory: one universe (type-in-
type), Π, Σ, λ, application, constructors, and a fixed basis of recursors as
built-in constants (`natRec`, `boolRec`, `botElim`). This module is the
substitution-based evaluator over `Val`, in the `lean/Och` playbook (Och's
`concEval` is the same shape): pure binders are de Bruijn (`pvar`), β and ι
fire by substitution, and a `sym` (or a `pvar`) at an application/recursor
head blocks reduction — the whole spine is then a legal (stuck neutral) value.

`readC` (⇝) and `hasType` (in `Machine.lean`) are built on top: `readC`
reflects a `Term` into a `Val` (resolving Ω snapshot reads) and normalizes it
here; `hasType` uses `convert` and the constructor signature table.

Everything is total: `shiftPure`/`substPure` recurse structurally (mutual with
a list helper for constructor arguments); `whnfV`/`nfV` take explicit fuel.
-/

namespace Dllbc.Val

/-! ## de Bruijn shift and substitution for pure binders

    Only `pvar` (pure de Bruijn) and the pure binders (`pi`/`sigmaT`/`lam`)
    participate. Constructor arguments are recursed into (a dependent type
    like `S #0` carries pure variables); `sym`/`const`/runtime forms are
    leaves — σ, ℓ and constant names are global, not de Bruijn. -/

/-! Shift pure de Bruijn indices ≥ `c` up by `d`. -/
mutual
  def shiftPure (d c : Nat) : Val → Val
    | .pvar k => if k < c then .pvar k else .pvar (k + d)
    | .lam dom b => .lam (shiftPure d c dom) (shiftPure d (c + 1) b)
    | .pi dom cod => .pi (shiftPure d c dom) (shiftPure d (c + 1) cod)
    | .sigmaT dom cod => .sigmaT (shiftPure d c dom) (shiftPure d (c + 1) cod)
    | .app f a => .app (shiftPure d c f) (shiftPure d c a)
    | .ctor n args => .ctor n (shiftPureList d c args)
    | .idT a b b' => .idT (shiftPure d c a) (shiftPure d c b) (shiftPure d c b')
    | v => v                                   -- type, const, sym, ⊥, loanM, borrowM: leaves
  termination_by v => sizeOf v
  def shiftPureList (d c : Nat) : List Val → List Val
    | [] => []
    | v :: vs => shiftPure d c v :: shiftPureList d c vs
  termination_by vs => sizeOf vs
end

/-! Substitute `s` for pure de Bruijn variable `j` in a value; indices `> j`
    shift down by one (the binder at `j` is eliminated). `s` is shifted when
    going under a binder. -/
mutual
  def substPure (j : Nat) (s : Val) : Val → Val
    | .pvar k => if k == j then s else if k > j then .pvar (k - 1) else .pvar k
    | .lam dom b => .lam (substPure j s dom) (substPure (j + 1) (shiftPure 1 0 s) b)
    | .pi dom cod => .pi (substPure j s dom) (substPure (j + 1) (shiftPure 1 0 s) cod)
    | .sigmaT dom cod => .sigmaT (substPure j s dom) (substPure (j + 1) (shiftPure 1 0 s) cod)
    | .app f a => .app (substPure j s f) (substPure j s a)
    | .ctor n args => .ctor n (substPureList j s args)
    | .idT a b b' => .idT (substPure j s a) (substPure j s b) (substPure j s b')
    | v => v                                   -- leaves (see shiftPure)
  termination_by v => sizeOf v
  def substPureList (j : Nat) (s : Val) : List Val → List Val
    | [] => []
    | v :: vs => substPure j s v :: substPureList j s vs
  termination_by vs => sizeOf vs
end

/-! ## Weak-head normalization (β and ι)

    An application spine is `head a₁ … aₙ`. β fires when the head is a `lam`;
    ι fires when the head is a recursor constant applied to enough arguments
    and its target (the last relevant one) is constructor-headed. A `sym`- or
    `pvar`-headed spine, or a recursor stuck on a neutral target, is a value. -/

/-- Collect an application spine into its head and argument list (in order). -/
def collectSpine : Val → Val × List Val
  | .app f a => let (h, as) := collectSpine f; (h, as ++ [a])
  | v => (v, [])

/-- Rebuild an application spine from a head and argument list. -/
def rebuildSpine : Val → List Val → Val
  | h, [] => h
  | h, a :: as => rebuildSpine (.app h a) as

/-- Weak-head-normalize: reduce the head redex (β / ι) only, fuel-bounded.
    Leaves (`pvar`, `sym`, `type`, `const`, `pi`, `sigmaT`, `lam`, `ctor`) and
    stuck neutral spines are returned as-is. -/
def whnfV : Nat → Val → Val
  | 0, v => v
  | fuel + 1, v =>
    let (head, args) := collectSpine v
    match head, args with
    | .lam _ b, a :: rest =>                        -- β
      whnfV fuel (rebuildSpine (substPure 0 a b) rest)
    | .const "natRec", motive :: z :: s :: n :: rest =>
      match whnfV fuel n with
      | .ctor "Z" [] => whnfV fuel (rebuildSpine z rest)
      | .ctor "S" [m] =>
        -- natRec P z s (S m) ↦ s m (natRec P z s m)
        let recCall := .app (.app (.app (.app (.const "natRec") motive) z) s) m
        whnfV fuel (rebuildSpine (.app (.app s m) recCall) rest)
      | n' => rebuildSpine (.const "natRec") (motive :: z :: s :: n' :: rest)  -- stuck
    | .const "boolRec", motive :: t :: f :: b :: rest =>
      match whnfV fuel b with
      | .ctor "True" [] => whnfV fuel (rebuildSpine t rest)
      | .ctor "False" [] => whnfV fuel (rebuildSpine f rest)
      | b' => rebuildSpine (.const "boolRec") (motive :: t :: f :: b' :: rest)  -- stuck
    -- listRec A P pn pc l : P l ; ι on Nil ↦ pn, on Cons h t ↦ pc h t (rec on t).
    | .const "listRec", a :: motive :: pn :: pc :: l :: rest =>
      match whnfV fuel l with
      | .ctor "Nil" [] => whnfV fuel (rebuildSpine pn rest)
      | .ctor "Cons" [h, t] =>
        let recCall := .app (.app (.app (.app (.app (.const "listRec") a) motive) pn) pc) t
        whnfV fuel (rebuildSpine (.app (.app (.app pc h) t) recCall) rest)
      | l' => rebuildSpine (.const "listRec") (a :: motive :: pn :: pc :: l' :: rest)  -- stuck
    -- Paulin-Mohring J (§10): j A a P d b p ; ι fires on Refl (b = a there), → d.
    | .const "j", _A :: _a :: _P :: d :: _b :: p :: rest =>
      match whnfV fuel p with
      | .ctor "Refl" [] => whnfV fuel (rebuildSpine d rest)
      | p' => rebuildSpine (.const "j") (_A :: _a :: _P :: d :: _b :: p' :: rest)  -- stuck
    -- Streicher K (§10): k A a P d p ; ι fires on Refl, → d.
    | .const "k", _A :: _a :: _P :: d :: p :: rest =>
      match whnfV fuel p with
      | .ctor "Refl" [] => whnfV fuel (rebuildSpine d rest)
      | p' => rebuildSpine (.const "k") (_A :: _a :: _P :: d :: p' :: rest)  -- stuck
    -- botElim never fires (⊥ has no constructors); it is always a stuck value.
    | _, _ => rebuildSpine head args

/-! ## Full normalization and conversion -/

/-! Normalize to full normal form: whnf the head, then normalize subterms.
    Under a binder, de Bruijn `pvar 0` is naturally a neutral leaf, so no fresh
    variable is needed. Fuel-bounded. -/
mutual
  def nfV : Nat → Val → Val
    | 0, v => v
    | fuel + 1, v =>
      match whnfV (fuel + 1) v with
      | .pi d c => .pi (nfV fuel d) (nfV fuel c)
      | .sigmaT d c => .sigmaT (nfV fuel d) (nfV fuel c)
      | .lam d b => .lam (nfV fuel d) (nfV fuel b)
      | .ctor n args => .ctor n (nfVList fuel args)
      | .app f a => .app (nfV fuel f) (nfV fuel a)
      | .idT a b b' => .idT (nfV fuel a) (nfV fuel b) (nfV fuel b')
      | w => w                                       -- pvar, sym, type, const, and runtime leaves
  termination_by fuel _ => (fuel, 0, 0)
  def nfVList : Nat → List Val → List Val
    | _, [] => []
    | fuel, v :: vs => nfV fuel v :: nfVList fuel vs
  termination_by fuel vs => (fuel, 1, vs.length)
end

/-- Definitional conversion: equal normal forms. For this fragment (β, ι, no
    eta, de Bruijn) normal forms are canonical, so normal-form equality *is*
    convertibility — simpler than a lazy whnf-and-compare recursion and, for a
    normalizing system, equivalent. -/
def convert (fuel : Nat) (a b : Val) : Bool := nfV fuel a == nfV fuel b

/-! ## Constructor signature table (§4)

    No inductive-declaration machinery: a small fixed table telling `hasType`,
    for a given whnf'd expected type, the constructor's field types as a
    telescope (dependent positions carry de Bruijn references to earlier
    fields — e.g. `Pair`'s second field). `none` means the constructor does
    not inhabit that type former. -/

/-- The field-type telescope of a constructor, given the whnf'd expected type. -/
structure CtorSig where
  fieldTypes : Val → Option (List Val)

/-- The fixed constructor basis: Unit, Bool, Nat, List (element parameter),
    and Σ's `Pair` (dependent second field). -/
def ctorSig : String → Option CtorSig
  | "unit"  => some { fieldTypes := fun ty => match ty with | .const "Unit" => some [] | _ => none }
  | "True"  => some { fieldTypes := fun ty => match ty with | .const "Bool" => some [] | _ => none }
  | "False" => some { fieldTypes := fun ty => match ty with | .const "Bool" => some [] | _ => none }
  | "Z"     => some { fieldTypes := fun ty => match ty with | .const "Nat" => some [] | _ => none }
  | "S"     => some { fieldTypes := fun ty => match ty with | .const "Nat" => some [.const "Nat"] | _ => none }
  | "Nil"   => some { fieldTypes := fun ty => match ty with | .app (.const "List") _ => some [] | _ => none }
  | "Cons"  => some { fieldTypes := fun ty =>
      match ty with | .app (.const "List") t => some [t, .app (.const "List") t] | _ => none }
  | "Pair"  => some { fieldTypes := fun ty => match ty with | .sigmaT a b => some [a, b] | _ => none }
  -- Refl : Id A a a — a nullary constructor whose type demands equal endpoints.
  -- (Fixed fuel for the endpoint convert; construction sites are small.)
  | "Refl"  => some { fieldTypes := fun ty =>
      match ty with | .idT _ a b => if Val.convert 1000 a b then some [] else none | _ => none }
  | _ => none

/-- The full constructor set of a whnf'd type (§9 exhaustiveness). `none` for a
    type whose constructors aren't known (nothing to check against). `Bot` has
    an EMPTY set — an empty match on a ⊥-typed scrutinee is vacuously
    exhaustive. -/
def typeCtors : Val → Option (List String)
  | .const "Nat"  => some ["Z", "S"]
  | .const "Bool" => some ["True", "False"]
  | .const "Unit" => some ["unit"]
  | .const "Bot"  => some []
  | .app (.const "List") _ => some ["Nil", "Cons"]
  | .sigmaT _ _   => some ["Pair"]
  | .idT _ _ _    => some ["Refl"]                 -- §10: Id's only constructor
  | _ => none

end Dllbc.Val

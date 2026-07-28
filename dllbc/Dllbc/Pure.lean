import Std.Data.HashSet
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

/-! Definitional conversion: equal normal forms. For this fragment (β, ι, no
    eta, de Bruijn) normal forms are canonical, so normal-form equality *is*
    convertibility. Computed INCREMENTALLY (the kernel algorithm): identical
    terms convert outright (`beq` is structural equality, and `nfV` is a
    function of structure, so `a == b` implies equal normal forms); otherwise
    whnf both sides, compare heads, recurse on subterms. This is *pointwise
    equal* to the specification `nfV fuel a == nfV fuel b`, by induction on
    fuel: `nfV (fuel+1)` is `whnfV (fuel+1)` followed by `nfV fuel` on each
    subterm, and `beq` on the two rebuilt results is the head comparison
    followed by `beq` on normalized subterm pairs — which is `convert fuel` on
    the un-normalized pairs, by the inductive hypothesis. The mixed-head and
    leaf cases land in the `w₁ == w₂` catch-all, exactly `beq` on what `nfV`
    returns unchanged. The fuel accounting is `nfV`'s own (decrement per
    structural level, whnf at the entry fuel), so even fuel-truncated behavior
    coincides. What changes is only the COST: two sides that agree
    syntactically — the overwhelmingly common case in `hasType`, measured at
    72% of all `convert` calls in a partition-range check — are decided by one
    structural pass with no normalization at all, and a genuine mismatch stops
    at the first differing head instead of building both full normal forms. -/
mutual
  def convert : Nat → Val → Val → Bool
    | 0, a, b => a == b
    | fuel + 1, a, b =>
      if a == b then true else
      match whnfV (fuel + 1) a, whnfV (fuel + 1) b with
      | .pi d1 c1, .pi d2 c2 => convert fuel d1 d2 && convert fuel c1 c2
      | .sigmaT d1 c1, .sigmaT d2 c2 => convert fuel d1 d2 && convert fuel c1 c2
      | .lam d1 b1, .lam d2 b2 => convert fuel d1 d2 && convert fuel b1 b2
      | .ctor n1 as1, .ctor n2 as2 => n1 == n2 && convertList fuel as1 as2
      | .app f1 a1, .app f2 a2 => convert fuel f1 f2 && convert fuel a1 a2
      | .idT a1 b1 c1, .idT a2 b2 c2 =>
        convert fuel a1 a2 && convert fuel b1 b2 && convert fuel c1 c2
      | w1, w2 => w1 == w2                 -- mixed heads, or two leaves: beq as-is
  termination_by fuel _ _ => (fuel, 0, 0)
  def convertList : Nat → List Val → List Val → Bool
    | _, [], [] => true
    | fuel, v :: vs, w :: ws => convert fuel v w && convertList fuel vs ws
    | _, _, _ => false
  termination_by fuel _ ws => (fuel, 1, ws.length)
end

/-! ## Shared normalization: the rigid-term cache

    `nfV` has no term sharing: a subterm embedded k times is re-normalized k
    times, and the conformance audit's trees embed the same model spines
    (`partIdxRangeL lo cnt *v`, a whole `partitionRangeL` unfolding) many times
    over. Measured on the partScanRange check: 94,930 `nfV` node visits over
    only 2,672 distinct terms — 35.5x visit redundancy, 65% of size-weighted
    normalization work spent on re-visits — and one recursion level up
    (quicksort) the repetition compounds multiplicatively.

    `nfS` is `nfV` plus a cache of terms *certified rigid*: hereditarily β/ι-
    irreducible, so `nfV f w = w` and `whnfV f w = w` for EVERY fuel f — fuel
    only gates reduction steps, and a rigid term admits none. That makes the
    cache sound to consult at any fuel and immune to the checker's state
    mutations (`refineSym`/`abstractInto` build NEW terms; rigidity is a
    property of the term itself, so no invalidation exists to miss).

    Certification is syntactic and bottom-up, never trusted from fuel: a leaf
    is rigid by definition (`nfV`/`whnfV` return `pvar`/`sym`/`type`/`const`/
    `⊥`/`loanM`/`borrowM` unchanged — `borrowM` payloads are runtime state the
    pure layer never enters); a composite is certified iff its children were
    (cache membership) AND its own head is not a β/ι-redex (`headRedexApp`,
    conservative: ANY constructor-headed scrutinee under a recursor blocks
    certification, a superset of the exact `Z`/`S`/… patterns `whnfV` fires
    on). Fuel-0 truncation returns uncertified, so a truncated (possibly still
    reducible) result never enters the cache.

    BEHAVIORAL IDENTITY: the value component of `nfS` is pointwise `nfV`, for
    any cache satisfying the invariant. The recursion mirrors `nfV`'s equations
    (same whnf at entry fuel, same decrement per level); the only new branch is
    the cache hit, which returns `v` where `nfV` computes `nfV f v` — equal
    because members are rigid. Any change to `nfV`/`whnfV` must be mirrored
    here (and `convert` above), or the mirror arguments break. -/

/-- The set of terms certified rigid (hereditarily β/ι-irreducible). -/
abbrev NormCache := Std.HashSet Val

/-- Constructor-headed? (the shapes ι could fire on — checked conservatively:
    arity/name mismatches still block certification, they never fire). -/
def isCtorV : Val → Bool
  | .ctor _ _ => true
  | _ => false

/-- Is this spine a head β/ι-redex (or possibly one)? Callers guarantee the
    spine's components are rigid, so the scrutinee IS its own whnf and a shape
    check suffices. Mirrors `whnfV`'s redex cases, conservatively. -/
def headRedexApp (v : Val) : Bool :=
  match collectSpine v with
  | (.lam _ _, _ :: _) => true
  | (.const "natRec", _ :: _ :: _ :: n :: _) => isCtorV n
  | (.const "boolRec", _ :: _ :: _ :: b :: _) => isCtorV b
  | (.const "listRec", _ :: _ :: _ :: _ :: l :: _) => isCtorV l
  | (.const "j", _ :: _ :: _ :: _ :: _ :: p :: _) => isCtorV p
  | (.const "k", _ :: _ :: _ :: _ :: p :: _) => isCtorV p
  | _ => false

/-! `nfS fuel v c` = `(nfV fuel v, certified?, updated cache)`. The Bool means
    "the result is in the cache" (hence rigid); `false` is always safe. -/
mutual
  def nfS : Nat → Val → NormCache → Val × Bool × NormCache
    | 0, v, c => (v, false, c)
    | fuel + 1, v, c =>
      if c.contains v then (v, true, c) else
      match whnfV (fuel + 1) v with
      | .pi d k =>
        let (d', bd, c) := nfS fuel d c
        let (k', bk, c) := nfS fuel k c
        let w := Val.pi d' k'
        if bd && bk then (w, true, c.insert w) else (w, false, c)
      | .sigmaT d k =>
        let (d', bd, c) := nfS fuel d c
        let (k', bk, c) := nfS fuel k c
        let w := Val.sigmaT d' k'
        if bd && bk then (w, true, c.insert w) else (w, false, c)
      | .lam d b =>
        let (d', bd, c) := nfS fuel d c
        let (b', bb, c) := nfS fuel b c
        let w := Val.lam d' b'
        if bd && bb then (w, true, c.insert w) else (w, false, c)
      | .ctor n args =>
        let (args', bs, c) := nfSList fuel args c
        let w := Val.ctor n args'
        if bs then (w, true, c.insert w) else (w, false, c)
      | .app f a =>
        let (f', bf, c) := nfS fuel f c
        let (a', ba, c) := nfS fuel a c
        let w := Val.app f' a'
        if bf && ba && !headRedexApp w then (w, true, c.insert w) else (w, false, c)
      | .idT x y z =>
        let (x', bx, c) := nfS fuel x c
        let (y', by', c) := nfS fuel y c
        let (z', bz, c) := nfS fuel z c
        let w := Val.idT x' y' z'
        if bx && by' && bz then (w, true, c.insert w) else (w, false, c)
      | w => (w, true, c.insert w)     -- leaves: rigid by definition (see above)
  termination_by fuel _ _ => (fuel, 0, 0)
  def nfSList : Nat → List Val → NormCache → List Val × Bool × NormCache
    | _, [], c => ([], true, c)
    | fuel, v :: vs, c =>
      let (v', bv, c) := nfS fuel v c
      let (vs', bs, c) := nfSList fuel vs c
      (v' :: vs', bv && bs, c)
  termination_by fuel vs _ => (fuel, 1, vs.length)
end

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

import Dllbc.Value

/-!
# The pure fragment: one syntax, one semantic domain (§4, M32 R1)

The comptime fragment is a tiny standard type theory: one universe (type-in-
type), Π, Σ, λ, application, constructors, and a fixed basis of recursors as
built-in constants (`natRec`, `boolRec`, `botElim`). This module is its
evaluator, and since M32 R1 it is the **classic NbE split**:

    eval     : PEnv → Term → Sem          -- syntax in, semantics out
    readback : Sem → Term                 -- semantics in, canonical syntax out
    nf       : Term → Term                -- their composition, the normal form

`Sem` is the semantic domain and it is TRANSIENT: it exists for the duration of
one normalization and nothing outside this file ever holds one. What the checker
holds at rest is a `Term` — canonical, first-order, comparable by `==`,
printable, sweepable by substitution. That is the whole content of the domain
split: M30 built the evaluator but had to read every result back into the mixed
`Val` tree, because `Val` was both the semantics and the syntax-at-rest; now the
syntax-at-rest is `Term` and `Val` is the store's state skeleton (`Value.lean`).

What follows from it, and is the reason to want it:

  * **A σ is a name.** `Val.sym` is gone; a σ at rest is `Term.sym σ`, a `pvar`
    in the reserved `§σ` namespace. Refinement (⇜) is `Term.substP` at that name.
  * **The capture invariant is a type.** A `Sem` has no ⊥, no loan marker and no
    borrow, so "a captured environment contains knowledge only" (nbe.md §3.2) is
    not a rule anyone maintains — `mkClosure`'s guard and `capturedMarkers`, the
    instrumentation that policed it, are deleted.
  * **`whnf` and `nf` coincide.** `readback` begins with `whnfN`, and there is no
    way to expose a head as a `Term` without reading the result back. Both names
    survive because the call sites mean different things by them.

Everything is total: `eval`/`whnfN`/`readback` take explicit fuel, and the value
traversals recurse structurally (mutual with a list helper for constructor
arguments). There is no substitution and no index arithmetic anywhere below.
-/

namespace Dllbc

/-! ## The semantic domain

    Constructors, neutrals, the three binders (whose bodies are closures), and
    one escape hatch. `stuck` carries a `Term` the pure fragment has no rule for
    — a runtime statement form, a `&mut`, a `borrowT` — which cannot occur in
    knowledge but can occur in a term someone hands the normalizer, and which
    reads back as itself. It is the honest alternative to mapping such a form to
    ⊥, which is what the old monad-free reflection did and which quietly claimed
    a runtime form WAS a hole. -/
inductive Sem where
  | ctor    : String → List Sem → Sem
  /-- A neutral atom: a free pure name, which since M32 R1 includes every σ. -/
  | pvar    : String → Sem
  | type    : Sem
  | const   : String → Sem
  | app     : Sem → Sem → Sem
  | idT     : Sem → Sem → Sem → Sem
  /-- `⇝τ` — the comptime binder-mode marker on a λ/Π domain (§6). Carried, never
      read under ⇝: `Term.convEq` unwraps it, so no comptime judgment can branch
      on a mode. What CAN see it is ⇒, reading a callee's binder modes. -/
  | cmpT    : Sem → Sem
  | pi      : String → Sem → Sem → Sem
  | sigmaT  : String → Sem → Sem → Sem
  | lam     : String → Sem → Sem → Sem
  /-- **The suspension**: a body stored as written, plus the environment it was
      born in. It sits in the BODY position of `lam`/`pi`/`sigmaT`, so every
      consumer that matches those three goes on matching them, and opening a
      binder is the one act that changes. -/
  | closure : List (String × Sem) → Term → Sem
  /-- A term the pure fragment has no rule for. Reads back as itself. -/
  | stuck   : Term → Sem
deriving Inhabited

/-- The comptime environment: name ↦ semantic value, innermost first. Prepending
    IS shadowing, and `List.lookup` finding the first match IS the scope rule. -/
abbrev PEnv := List (String × Sem)

namespace Pure

/-! ## The kernel's own arithmetic, and the `Array` former's vocabulary

    `add` and `Le` are library terms (`Std`) in every other respect, but the CARVE
    rule's premises are *stated* against them: premise (2) is a `Le`, and premise
    (3) decomposes an extent with `add`. A kernel rule cannot cite a library it
    does not import, and two syntactically different `add`s would never convert —
    so the single source of truth for both moves here, and `Std` aliases these. -/

def kNatTy : Term := .const "Nat"
def kUnitTy : Term := .const "Unit"
def kBotTy : Term := .const "Bot"
def kNatRecS (P z s n : Term) : Term := .app (.app (.app (.app (.const "natRec") P) z) s) n

/-- `add a b` by recursion on `a` (`add Z b = b`, `add (S a') b = S (add a' b)`). -/
def kAddFn : Term :=
  .lam "a" kNatTy (.lam "b" kNatTy (kNatRecS (.lam "_" kNatTy kNatTy) (.pvar "b")
    (.lam "a'" kNatTy (.lam "r" kNatTy (.ctorApp "S" [.pvar "r"]))) (.pvar "a")))
def kAdd (a b : Term) : Term := .app (.app kAddFn a) b

/-- `Le : Nat → Nat → Type` as a computing predicate (`Z ≤ _ ↦ ⊤`, `S ≤ Z ↦ ⊥`,
    `S ≤ S ↦ recurse`). Premise (2)'s obligation type is built from this. -/
def kLeFn : Term :=
  .lam "a" kNatTy (kNatRecS (.lam "_" kNatTy (.pi "_" kNatTy .type)) (.lam "_" kNatTy kUnitTy)
    (.lam "a'" kNatTy (.lam "f" (.pi "_" kNatTy .type) (.lam "b" kNatTy
      (kNatRecS (.lam "_" kNatTy .type) kBotTy
        (.lam "b'" kNatTy (.lam "_" .type (.app (.pvar "f") (.pvar "b'")))) (.pvar "b")))))
    (.pvar "a"))
def kLe (a b : Term) : Term := .app (.app kLeFn a) b

/-- `Array n T` — the ¶1.1 former, in the FIXED BASIS rather than §7's declaration
    scheme (the values are flat runs, which no CIC-scheme inductive has). -/
def arrayTy (n T : Term) : Term := .app (.app (.const "Array") n) T

/-- Recognize `Array n T`, returning `(n, T)`. -/
def asArrayTy? : Term → Option (Term × Term)
  | .app (.app (.const "Array") n) t => some (n, t)
  | _ => none

/-- The `Nat` term of a Lean numeral. -/
def ofNat (n : Nat) : Term := Term.nat n

/-- `arrCat` applied to its four arguments. -/
def arrCatS (m k a b : Term) : Term :=
  .app (.app (.app (.app (.const "arrCat") m) k) a) b

/-! An array's **owned run**: `Arr [v₁ … v_c]`, the flat literal, which is both the
    value form and the knowledge form. Element `i` is child `i` — a *subterm*,
    which is the whole reason ¶1.2 puts the former in the basis rather than
    deriving it from a right-nested spine. -/
def arrRun? : Term → Option (List Term)
  | .ctorApp "Arr" vs => some vs
  | _ => none

/-- The pure binder a reflected `let` binds, for the runtime slot `id`. Reserved
    (`isReservedName`), which is what keeps the binding capture-free: no source
    binder can shadow it, and runtime ids are globally unique so no `let` can
    shadow another. -/
def letName (id : Nat) : String := "§let" ++ toString id

/-- Collect an application spine into its head and argument list (in order). -/
def collectSpine : Sem → Sem × List Sem
  | .app f a => let (h, as) := collectSpine f; (h, as ++ [a])
  | v => (v, [])

/-- Rebuild an application spine from a head and argument list. -/
def rebuildSpine : Sem → List Sem → Sem
  | h, [] => h
  | h, a :: as => rebuildSpine (.app h a) as

/-- The same two, at `Term` level — `hasType` reads a neutral spine's head and
    arguments off the canonical form. -/
def collectSpineT : Term → Term × List Term
  | .app f a => let (h, as) := collectSpineT f; (h, as ++ [a])
  | t => (t, [])

def rebuildSpineT : Term → List Term → Term
  | h, [] => h
  | h, a :: as => rebuildSpineT (.app h a) as

/-! ## Environment-based evaluation — the NbE core

    A λ does not reduce by copying its argument into its body; it evaluates to a
    **closure** — the body as written, plus the environment it was born in — and
    application extends that environment. There is no index arithmetic anywhere
    below, which is the point (a hand-written index sat wrong for five milestones
    because nothing consulted it; environments have no index to get wrong).

    ### One variable convention

      * `pvar x` with `x` in `ρ` is **bound**: look it up.
      * `pvar x` otherwise is **free**, and evaluates to itself — which is what a
        σ is: `Term.sym σ` is free in every environment, so it evaluates to
        itself, reads back as itself, and compares by name.

    ### `let` is β, and `eval` performs it

    `let x = e ; rest` binds the runtime slot `x`'s reserved pure name to `e`'s
    value and evaluates `rest` under it. An occurrence is `.var x`, resolved
    through the same environment. This replaces M30's reflected redex: there is no
    λ to build and no body to abstract over, because an environment extension is
    exactly what the redex was there to express. Nothing is transplanted — the
    argument is a VALUE before the inner binder is entered — which is the one move
    a named representation cannot do safely.

    ### Freshness, and why it is a LEVEL and not a counter

    `readback` renames every binder it opens to `readbackName ⟨its level⟩`. That
    is a reserved name (`§0`, `§1`, …) which no source program can write, so it
    cannot capture what it descends past; and it is a function of the level alone,
    so **readback output is canonical**: two α-variant functions read back to the
    same tree, which is what lets `convert` stay `==` on normal forms.

    ### No η, structurally

    Readback is UNTYPED. It never expands a neutral at function type, so
    `λ (u : Nat). u` and `λ (u : Nat). Z` stay unequal and a stuck spine stays the
    spine it is — the property KernelFloor polices. -/

/-- A `Nat` in the semantic domain. -/
def semOfNat : Nat → Sem
  | 0 => .ctor "Z" []
  | k + 1 => .ctor "S" [semOfNat k]

/-- Read a semantic `Nat` as a Lean numeral, if it is concrete. -/
def semNatOf? : Sem → Option Nat
  | .ctor "Z" [] => some 0
  | .ctor "S" [n] => (semNatOf? n).map (· + 1)
  | _ => none

/-! The STRUCTURAL projection back to syntax, with no reduction and no binder
    renaming — what `readback` falls back to when the fuel runs out, where it used
    to be able to return the value itself because value and syntax were one type.
    A closure surrenders its body unevaluated and drops its environment, which is
    lossy and is meant to be: this path is fuel exhaustion, and inventing a rule
    for it would hide that. -/
mutual
  def semToTerm : Sem → Term
    | .pvar x => .pvar x
    | .type => .type
    | .const c => .const c
    | .stuck t => t
    | .closure _ b => b
    | .ctor n args => .ctorApp n (semToTermList args)
    | .app f a => .app (semToTerm f) (semToTerm a)
    | .idT a b c => .idT (semToTerm a) (semToTerm b) (semToTerm c)
    | .cmpT τ => .cmpT (semToTerm τ)
    | .lam x d b => .lam x (semToTerm d) (semToTerm b)
    | .pi x d c => .pi x (semToTerm d) (semToTerm c)
    | .sigmaT x d c => .sigmaT x (semToTerm d) (semToTerm c)
  termination_by v => sizeOf v
  def semToTermList : List Sem → List Term
    | [] => []
    | v :: vs => semToTerm v :: semToTermList vs
  termination_by vs => sizeOf vs
end

mutual
  /-- Evaluate the term `t` against the comptime environment `ρ`. Strong
      everywhere except under a binder, where the body is suspended.

      Runtime STATEMENT forms are `stuck` leaves. That is not an omission: they
      are not knowledge, `eval` computes knowledge, and a rule for one here would
      be the first step of the door nbe.md §3.3 is holding shut. -/
  def eval : Nat → PEnv → Term → Sem
    | 0, _, t => .stuck t
    | fuel + 1, ρ, t =>
      match t with
      | .pvar x =>
        match ρ.lookup x with
        | some w => w
        | none => .pvar x                       -- free: a name means itself
      | .var x =>
        match ρ.lookup (letName x.id) with
        | some w => w
        | none => .stuck (.var x)               -- an Ω slot: not knowledge here
      | .letIn x rhs rest =>
        eval (fuel + 1) ((letName x.id, eval (fuel + 1) ρ rhs) :: ρ) rest
      | .type => .type
      | .const c => .const c
      | .unit => .ctor "unit" []
      -- The binder's NAME is what the semantic domain binds: `Sem` is the
      -- comptime domain and a comptime occurrence is a `pvar`, so the `Var`'s
      -- slot id (`noSlot` for a binder written here) has nothing to resolve.
      | .lam x dom body => .lam x.name (eval (fuel + 1) ρ dom) (.closure ρ body)
      | .pi x dom cod => .pi x (eval (fuel + 1) ρ dom) (.closure ρ cod)
      | .sigmaT x dom cod => .sigmaT x (eval (fuel + 1) ρ dom) (.closure ρ cod)
      | .cmpT τ => .cmpT (eval (fuel + 1) ρ τ)
      | .app f a => whnfN (fuel + 1) (.app (eval (fuel + 1) ρ f) (eval (fuel + 1) ρ a))
      | .ctorApp n args => .ctor n (evalList (fuel + 1) ρ args)
      | .idT a b c => .idT (eval (fuel + 1) ρ a) (eval (fuel + 1) ρ b) (eval (fuel + 1) ρ c)
      | s => .stuck s
  termination_by fuel _ t => (fuel, 1, sizeOf t)
  def evalList : Nat → PEnv → List Term → List Sem
    | _, _, [] => []
    | fuel, ρ, t :: ts => eval fuel ρ t :: evalList fuel ρ ts
  termination_by fuel _ ts => (fuel, 1, sizeOf ts)
  /-- **Open the binder `x` at `arg`** — the one operation that replaces
      substitution at every one of its sites. -/
  def instBody : Nat → String → Sem → Sem → Sem
    | fuel, x, .closure ρ b, arg => eval fuel ((x, arg) :: ρ) b
    | _, _, b, _ => b                           -- a binder body is always a closure
  termination_by fuel _ _ _ => (fuel, 2, 0)
  /-- Weak-head reduction: β and ι, head redex only. -/
  def whnfN : Nat → Sem → Sem
    | 0, v => v
    | fuel + 1, v =>
      let sAdd : Sem → Sem → Sem := fun a b => .app (.app (eval fuel [] kAddFn) a) b
      let (head, args) := collectSpine v
      match head, args with
      | .lam x _ b, a :: rest =>                      -- β, by environment extension
        whnfN fuel (rebuildSpine (instBody fuel x b a) rest)
      | .const "natRec", motive :: z :: s :: n :: rest =>
        match whnfN fuel n with
        | .ctor "Z" [] => whnfN fuel (rebuildSpine z rest)
        | .ctor "S" [m] =>
          let recCall := .app (.app (.app (.app (.const "natRec") motive) z) s) m
          whnfN fuel (rebuildSpine (.app (.app s m) recCall) rest)
        | n' => rebuildSpine (.const "natRec") (motive :: z :: s :: n' :: rest)
      | .const "boolRec", motive :: t :: f :: b :: rest =>
        match whnfN fuel b with
        | .ctor "True" [] => whnfN fuel (rebuildSpine t rest)
        | .ctor "False" [] => whnfN fuel (rebuildSpine f rest)
        | b' => rebuildSpine (.const "boolRec") (motive :: t :: f :: b' :: rest)
      | .const "listRec", a :: motive :: pn :: pc :: l :: rest =>
        match whnfN fuel l with
        | .ctor "Nil" [] => whnfN fuel (rebuildSpine pn rest)
        | .ctor "Cons" [h, t] =>
          let recCall := .app (.app (.app (.app (.app (.const "listRec") a) motive) pn) pc) t
          whnfN fuel (rebuildSpine (.app (.app (.app pc h) t) recCall) rest)
        | l' => rebuildSpine (.const "listRec") (a :: motive :: pn :: pc :: l' :: rest)
      | .const "sigmaRec", a :: b :: motive :: f :: p :: rest =>
        match whnfN fuel p with
        | .ctor "Pair" [x, y] => whnfN fuel (rebuildSpine (.app (.app f x) y) rest)
        | p' => rebuildSpine (.const "sigmaRec") (a :: b :: motive :: f :: p' :: rest)
      | .const "j", _A :: _a :: _P :: d :: _b :: p :: rest =>
        match whnfN fuel p with
        | .ctor "Refl" [] => whnfN fuel (rebuildSpine d rest)
        | p' => rebuildSpine (.const "j") (_A :: _a :: _P :: d :: _b :: p' :: rest)
      | .const "k", _A :: _a :: _P :: d :: p :: rest =>
        match whnfN fuel p with
        | .ctor "Refl" [] => whnfN fuel (rebuildSpine d rest)
        | p' => rebuildSpine (.const "k") (_A :: _a :: _P :: d :: p' :: rest)
      | .const "arrCat", m :: k :: a :: b :: rest =>
        match whnfN fuel a, whnfN fuel b with
        | .ctor "Arr" [], b' => whnfN fuel (rebuildSpine b' rest)
        | a', .ctor "Arr" [] => whnfN fuel (rebuildSpine a' rest)
        | .ctor "Arr" xs, .ctor "Arr" ys => whnfN fuel (rebuildSpine (.ctor "Arr" (xs ++ ys)) rest)
        | .app (.app (.app (.const "acons") m') x) xs, b' =>
          whnfN fuel (rebuildSpine
            (.app (.app (.app (.const "acons") (sAdd m' k)) x)
              (.app (.app (.app (.app (.const "arrCat") m') k) xs) b')) rest)
        | .ctor "Arr" (x :: xs), b' =>
          let tlLen := semOfNat xs.length
          whnfN fuel (rebuildSpine
            (.app (.app (.app (.const "acons") (sAdd tlLen k)) x)
              (.app (.app (.app (.app (.const "arrCat") tlLen) k) (.ctor "Arr" xs)) b')) rest)
        | a', b' => rebuildSpine (.const "arrCat") (m :: k :: a' :: b' :: rest)
      | .const "aget", tt :: n :: i :: a :: rest =>
        match semNatOf? (whnfN fuel i), whnfN fuel a with
        | some j, .ctor "Arr" vs =>
          match vs.get? j with
          | some w => whnfN fuel (rebuildSpine w rest)
          | none => rebuildSpine (.const "aget") (tt :: n :: i :: .ctor "Arr" vs :: rest)
        | _, a' => rebuildSpine (.const "aget") (tt :: n :: i :: a' :: rest)
      | .const "acons", n :: x :: xs :: rest =>
        match whnfN fuel xs with
        | .ctor "Arr" vs => whnfN fuel (rebuildSpine (.ctor "Arr" (x :: vs)) rest)
        | xs' => rebuildSpine (.const "acons") (n :: x :: xs' :: rest)
      | .const "arrRec", tt :: motive :: pn :: pc :: n :: a :: rest =>
        match whnfN fuel a with
        | .ctor "Arr" [] => whnfN fuel (rebuildSpine pn rest)
        | .ctor "Arr" (x :: vs) =>
          let tl : Sem := .ctor "Arr" vs
          let k : Sem := semOfNat vs.length
          let recCall := rebuildSpine (.const "arrRec") [tt, motive, pn, pc, k, tl]
          whnfN fuel (rebuildSpine (rebuildSpine pc [k, x, tl, recCall]) rest)
        | .app (.app (.app (.const "acons") m') x) xs =>
          let recCall := rebuildSpine (.const "arrRec") [tt, motive, pn, pc, m', xs]
          whnfN fuel (rebuildSpine (rebuildSpine pc [m', x, xs, recCall]) rest)
        | a' => rebuildSpine (.const "arrRec") (tt :: motive :: pn :: pc :: n :: a' :: rest)
      | _, _ => rebuildSpine head args
  termination_by fuel _ => (fuel, 0, 0)
  /-- Read a semantic value back to canonical syntax, renaming every binder it
      opens to its LEVEL — which is what makes the output canonical rather than
      merely first-order. -/
  def readback : Nat → Nat → Sem → Term
    | 0, _, v => semToTerm v
    | fuel + 1, depth, v =>
      match whnfN (fuel + 1) v with
      -- The binder is opened at its OWN name (`nm`, which is what its body's
      -- occurrences say) and bound to the fresh `x`; the node that comes back
      -- carries `x`. Passing `x` on both sides would bind a name the body never
      -- mentions and leave every occurrence free.
      | .lam nm dom body =>
        let x := readbackName depth
        .lam x (readback fuel depth dom)
          (readback fuel (depth + 1) (instBody fuel nm body (.pvar x)))
      | .pi nm dom cod =>
        let x := readbackName depth
        .pi x (readback fuel depth dom)
          (readback fuel (depth + 1) (instBody fuel nm cod (.pvar x)))
      | .sigmaT nm dom cod =>
        let x := readbackName depth
        .sigmaT x (readback fuel depth dom)
          (readback fuel (depth + 1) (instBody fuel nm cod (.pvar x)))
      | .cmpT τ => .cmpT (readback fuel depth τ)
      | .app f a => .app (readback fuel depth f) (readback fuel depth a)
      | .ctor n args => .ctorApp n (readbackList fuel depth args)
      | .idT a b c =>
        .idT (readback fuel depth a) (readback fuel depth b) (readback fuel depth c)
      | w => semToTerm w
  termination_by fuel _ _ => (fuel, 3, 0)
  def readbackList : Nat → Nat → List Sem → List Term
    | _, _, [] => []
    | fuel, depth, v :: vs => readback fuel depth v :: readbackList fuel depth vs
  termination_by fuel _ vs => (fuel, 3, vs.length + 1)
end

/-! ## Normal form, weak head, conversion -/

/-- Normal form by evaluation: evaluate against the empty environment, read back
    from depth zero. Canonical up to binder names, which is what lets `convert`
    stay a structural comparison. -/
def nf (fuel : Nat) (t : Term) : Term := readback fuel 0 (eval fuel [] t)

/-- **Weak-head reduction**, for callers that want a head exposed.

    It is `nf`, and that is a consequence of the domain split rather than
    laziness: `readback` begins with `whnfN`, and there is no way to hand a
    caller a `Term` whose head is exposed without reading the result back —
    reading back normalizes. The name survives because the call sites mean
    "expose the head so I can match on the former", and that is what they get. -/
def whnf (fuel : Nat) (t : Term) : Term := nf fuel t

/-- Definitional conversion: equal normal forms. For this fragment (β, ι, no η)
    normal forms are canonical, so normal-form equality IS convertibility.

    The equality is `Term.convEq` rather than `==`, and the difference is exactly
    the mode marker: `convEq` unwraps `⇝` on either side, which is what keeps §6's
    "case is inert under ⇝" true of every comptime judgment built on this. -/
def convert (fuel : Nat) (a b : Term) : Bool := Term.convEq (nf fuel a) (nf fuel b)

/-- **Open the binder `x` of `body` at `arg`**, both syntax, result canonical.

    The replacement for `substPure 0 arg body`, and it is emphatically NOT
    `Term.substP`: substituting into a canonical term would capture, because two
    independently read-back terms both name their binders `§0`, `§1`, …. Going
    through the environment cannot capture, because the argument is a VALUE before
    the binder is entered. (`substP` at a `§σ`-name is safe for the opposite
    reason — nothing binds a σ.) -/
def openBinder (fuel : Nat) (x : String) (body arg : Term) : Term :=
  readback fuel 0 (eval fuel [(x, eval fuel [] arg)] body)

/-! ## Constructor signature table (§4)

    No inductive-declaration machinery: a small fixed table telling `hasType`,
    for a given whnf'd expected type, the constructor's field types as a
    telescope (dependent positions refer to earlier fields BY NAME). `none` means
    the constructor does not inhabit that type former. -/

/-- The field-type telescope of a constructor, given the whnf'd expected type.
    Each entry is `(the name later entries reach this field by, the field's
    type)`; `"_"` where nothing does. -/
structure CtorSig where
  fieldTypes : Term → Option (List (String × Term))

/-- The fixed constructor basis: Unit, Bool, Nat, List (element parameter),
    and Σ's `Pair` (dependent second field). -/
def ctorSig : String → Option CtorSig
  | "unit"  => some { fieldTypes := fun ty => match ty with | .const "Unit" => some [] | _ => none }
  | "True"  => some { fieldTypes := fun ty => match ty with | .const "Bool" => some [] | _ => none }
  | "False" => some { fieldTypes := fun ty => match ty with | .const "Bool" => some [] | _ => none }
  | "Z"     => some { fieldTypes := fun ty => match ty with | .const "Nat" => some [] | _ => none }
  | "S"     => some { fieldTypes := fun ty =>
      match ty with | .const "Nat" => some [("_", .const "Nat")] | _ => none }
  | "Nil"   => some { fieldTypes := fun ty =>
      match ty with | .app (.const "List") _ => some [] | _ => none }
  | "Cons"  => some { fieldTypes := fun ty =>
      match ty with
      | .app (.const "List") t => some [("_", t), ("_", .app (.const "List") t)]
      | _ => none }
  -- The one DEPENDENT entry in the table: `Pair`'s second field type is the Σ's
  -- codomain, a body under the Σ's own binder — so that binder is the name
  -- `checkFields` opens it at.
  | "Pair"  => some { fieldTypes := fun ty =>
      match ty with | .sigmaT x a b => some [(x, a), ("_", b)] | _ => none }
  -- `Arr` — the array literal (¶1.4). Its field telescope for a CONCRETE `n` is `T`
  -- repeated `n` times; at a symbolic `n` there is no constructor signature, and
  -- correctly so — one cannot write an array literal of unknown length.
  | "Arr"   => some { fieldTypes := fun ty =>
      match asArrayTy? ty with
      | some (n, t) => (Term.natOf? (whnf 1000 n)).map (fun k => List.replicate k ("_", t))
      | none => none }
  -- Refl : Id A a a — a nullary constructor whose type demands equal endpoints.
  | "Refl"  => some { fieldTypes := fun ty =>
      match ty with | .idT _ a b => if convert 1000 a b then some [] else none | _ => none }
  | _ => none

/-- The names `ctorSig` answers for — **the fixed constructor basis, enumerated**.
    A surface binder may not take one of these names, which is what keeps
    capitalisation unambiguous as the binder-mode marker. Must track `ctorSig`;
    the two sit adjacent so that adding a constructor without reserving its name
    is a visible omission rather than a silent one. -/
def ctorNames : List String :=
  ["unit", "True", "False", "Z", "S", "Nil", "Cons", "Pair", "Arr", "Refl"]

/-- The full constructor set of a whnf'd type (§9 exhaustiveness). `none` for a
    type whose constructors aren't known. `Bot` has an EMPTY set — an empty match
    on a ⊥-typed scrutinee is vacuously exhaustive. -/
def typeCtors : Term → Option (List String)
  | .const "Nat"  => some ["Z", "S"]
  | .const "Bool" => some ["True", "False"]
  | .const "Unit" => some ["unit"]
  | .const "Bot"  => some []
  | .app (.const "List") _ => some ["Nil", "Cons"]
  | .sigmaT _ _ _ => some ["Pair"]
  | .idT _ _ _    => some ["Refl"]                 -- §10: Id's only constructor
  -- `Array n T` has the single constructor `Arr` at a concrete `n`, and NO known
  -- constructor set at a symbolic one. ¶1.4: arrays are never matched anyway.
  | ty => match asArrayTy? ty with
    | some (n, _) => if (Term.natOf? (whnf 1000 n)).isSome then some ["Arr"] else none
    | none => none

end Pure

namespace Val

/-! ## Segments (¶1.1): the carved array's state form

    An array value at `Array n T` is one of
      * `Arr [v₁ … v_n]`   — an owned flat run (also the knowledge form),
      * a σ                — opaque,
      * a stuck neutral    — an `arrCat` spine,
      * `§segs [seg₁ … seg_k]` (k ≥ 2) — CARVED, each `§seg [c, body]`.

    The last is **state only**, and since M32 R1 that is enforced rather than
    conventional: `Val.ctor` refuses to collapse a `§segs`/`§seg` node into a
    knowledge leaf, so a carve stays in the skeleton where the borrow machinery
    can see it, and the ⇝ bridge (`arrFoldDeep`) is the one route from a carve to
    knowledge. A segment's EXTENT is knowledge (a `Term`); its BODY is a store
    value, because that is what may hold a marker. -/

/-- A segment node: a knowledge extent and a store-valued body. -/
def segNode (c : Term) (body : Val) : Val := .node "§seg" [.know c, body]

def asSeg? : Val → Option (Term × Val)
  | .node "§seg" [.know c, b] => some (c, b)
  | _ => none

/-- Is a segment body **owned** — one of the three forms a carve is defined on
    (an owned run, a σ, a neutral) rather than the two ownership markers?

    The test is MARKER-FREEDOM, not "the body is not itself a marker", and the
    difference is load-bearing: an element cursor parks its marker INSIDE the
    one-slot run, and a shallow test would call that body owned, merge it into its
    neighbour and hand the MARKER out as an element on the next read. -/
def segOwned (b : Val) : Bool := !hasStateMarker b

/-- Rebuild a segment list into an array node, restoring the two invariants: drop
    zero-extent segments (¶1.1's *drop-empty*), and unwrap a single segment. -/
def segsNode (segs : List Val) : Val :=
  match segs with
  | [] => .ctor "Arr" []
  | [.node "§seg" [_, b]] => if hasStateMarker b then .node "§segs" segs else b
  | ss => .node "§segs" ss

/-- The total extent of a segment list: RIGHT-NESTED, with no trailing `Z`. `add`
    recurses on its first argument, so `add c Z` is stuck the moment `c` is
    symbolic, and every conversion the residue transition arranges would fail on
    the trailing zero alone. -/
partial def segsExtent? : List Val → Option Term
  | [] => some Term.zero
  | [s] => (asSeg? s).map (·.1)
  | s :: rest => do
    let (c, _) ← asSeg? s
    let tot ← segsExtent? rest
    some (Pure.kAdd c tot)

/-- The extent of an array-shaped value read off the value itself, where that is
    possible: a run knows its length, a segment list sums its extents, an `arrCat`
    spine carries both halves. A bare σ does NOT — its extent lives in its `sctx`
    type, which only the machine can reach (`arrExtent` there). -/
partial def arrExtentPure? : Val → Option Term
  | .node "§segs" segs => segsExtent? segs
  | .node "Arr" vs => some (Term.nat vs.length)
  | .know (.ctorApp "Arr" ts) => some (Term.nat ts.length)
  | .know (.app (.app (.app (.app (.const "arrCat") m) k) _) _) => some (Pure.kAdd m k)
  | _ => none

/-! **Merge** (¶1.1), the normalization that makes the carve history invisible: two
    adjacent segments with owned bodies collapse into one of the summed extent.

    Only *runs* are concatenated. Two adjacent σ's have `arrCat σ₁ σ₂` as their
    joint body in the doc, and building it here would be harmless but pointless —
    the pair already types against `Array (add c₁ c₂) T`, and ⇝ folds them to that
    very `arrCat` anyway. -/
partial def mergeSegList : List Val → List Val
  | s₁ :: s₂ :: rest =>
    match asSeg? s₁, asSeg? s₂ with
    | some (c₁, b₁), some (c₂, b₂) =>
      match b₁, b₂ with
      | .know (.ctorApp "Arr" xs), .know (.ctorApp "Arr" ys) =>
        if segOwned b₁ && segOwned b₂ then
          mergeSegList (segNode (Pure.kAdd c₁ c₂) (.know (.ctorApp "Arr" (xs ++ ys))) :: rest)
        else s₁ :: mergeSegList (s₂ :: rest)
      | _, _ => s₁ :: mergeSegList (s₂ :: rest)
    | _, _ => s₁ :: mergeSegList (s₂ :: rest)
  | ss => ss

/-- Merge-normalize an array node wherever one sits in `v`. Applied at every *read*
    of a place, which is what makes it robust to the §5.2 demand-end sites: a
    suspension collapsing mid-body turns markers back into values, and the read
    that follows is what re-merges them. Nothing has to remember to. -/
partial def mergeArrays : Val → Val
  | .node "§segs" segs =>
    segsNode (mergeSegList (segs.map (fun s => match asSeg? s with
      | some (c, b) => segNode c (mergeArrays b)
      | none => mergeArrays s)))
  | .node n args => .ctor n (args.map mergeArrays)
  | .borrowM ℓ p => .borrowM ℓ (mergeArrays p)
  | v => v

/-- **The ⇝ bridge** (¶1.3): fold one segment list into its `arrCat` spine — the
    knowledge form of what the array *is*, which never mentions a marker or a
    hole. `none` when some body is one: "a suspended array has no snapshot; only a
    collapsed one does", §5.2's proper-payload premise arriving at an array node. -/
partial def arrFoldSegs? : List Val → Option Term
  | [] => some (.ctorApp "Arr" [])
  | [s] => do
    let (_, b) ← asSeg? s
    if segOwned b then know? b else none
  | s :: rest => do
    let (c, b) ← asSeg? s
    if !segOwned b then none
    else do
      let bt ← know? b
      let btl ← arrFoldSegs? rest
      let ct ← segsExtent? rest
      some (Pure.arrCatS c ct bt btl)

/-- Fold every *foldable* segment list in `v`, leaving a suspended one in place.
    Total by design: an unfoldable node stays the state form it is and is rejected
    at the one place that judges (`hasType`, with a distinctive error), rather than
    turning every comptime read of a marker-bearing aggregate into a new error. -/
partial def arrFoldDeep : Val → Val
  | .node "§segs" segs =>
    let segs' := segs.map (fun s => match asSeg? s with
      | some (c, b) => segNode c (arrFoldDeep b)
      | none => arrFoldDeep s)
    match arrFoldSegs? segs' with
    | some t => .know t
    | none => .node "§segs" segs'
  | .node n args => .ctor n (args.map arrFoldDeep)
  | .borrowM ℓ p => .borrowM ℓ (arrFoldDeep p)
  | v => v

end Val

end Dllbc

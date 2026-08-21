import Dllbc.Program
import Dllbc.Std
import Dllbc.StdLemmas
import Dllbc.ProgMacro
import Dllbc.Tests.Diff
import Dllbc.Boundary
import Dllbc.Tests.Arrays
import Dllbc.Tests.Direct
import Dllbc.FnMacro

/-!
# Functions: the `fn` statement and function values

Tests for the `fn` statement and the values it produces: the seal (a function's
body is checked once, at its own definition, and callers see only its
signature), recursors used as function bodies, runtime λ values, application of
a value callee, and the difference between a transparent and a sealed
function's typing.

Sealing is what makes checking modular: a caller must never depend on a
callee's body, only on its signature.
-/

section
/-! ## `.seal t u` — opacity as syntax

Checking `t : u` at a seal node happens ONCE, at the node: verify `t : u`, then
yield a fresh opaque `σ : u`. Downstream code sees only the type `u`, never `t`
itself. Executing a seal evaluates `t` directly — execution is always
transparent; only checking mode is opaque.

`u` ranges over pure types and borrow-free Πs here; a borrow-moded `u` (a real
function signature, with exit snapshots and obligations) is rejected, by a
message naming the limitation.

The seal can never be a comptime form: `.seal` is its own `Term` constructor
(not an application the pure-fragment reduction rule could see), and `Val` has
no seal constructor, so `eval`/`whnfN`/`nfV`/`convert`/`hasType` have nothing to
reduce it to.

## `x(a, …)` — application of a value callee

The callee is a slot, not a declaration-table entry, and what the slot holds
picks the rule: a literal λ is bound and run (β, both machines); a `σ : Π` is
applied abstractly, minting the result from the instantiated codomain (checking
only). Application is saturated — under-application is rejected, never
curried. The head of `f(…)` is a value callee exactly when it names a bound
runtime variable, and falls through to the declaration table otherwise.
-/

open Dllbc
open Dllbc.StdLemmas (LeReflRaw LeTransRaw)

namespace Dllbc.Tests.S26Seal

/-! A rejection is always asserted on its error MESSAGE, never collapsed to a
    Bool: `hasType` returns `false` for "does not have this type", and the seal
    turns that into an error, so testing only a Bool would let a stuck program
    pass for a genuine type error. -/

/-! ## §A. The seal under ⇒-checking -/

-- A1. A well-typed sealed λ is accepted, and the binding holds a σ afterwards.
def a1 : Term := prog{ let F = (λ (x : Nat). x : Π (x : Nat) → Nat); () }
example : progOk a1 = true := by native_decide

-- A2. An ill-typed one is rejected, by an honest TYPING rejection naming both the
-- term and the ascribed type — not by getting stuck somewhere downstream.
def a2 : Term := prog defer_check { let F = (λ (x : Nat). x : Π (x : Nat) → Bool); () }
example : progRejects a2 "does not have its ascribed type" = true := by native_decide

-- A3. Data seals: the same rule with no Π in sight.
def a3ok : Term := prog{ let a = (3 : Nat); () }
def a3no : Term := prog defer_check { let a = (3 : Bool); () }
example : progOk a3ok = true := by native_decide
example : progRejects a3no "does not have its ascribed type" = true := by native_decide

-- A4. A borrow-moded `u` is a function signature, checked by the function
-- audit rather than by `hasType` — so the sealed term must be a runtime λ whose
-- binders match it. Sealing a PURE λ there is refused: `hasType` has no answer
-- to a payload-owing Π.
def a4 : Term := prog defer_check { let F = (λ (x : Nat). x : &mut Nat); () }
example : progRejects a4 "the sealed term must be a runtime λ" = true := by native_decide

/-! ### A5. The pure fragment never meets the seal node

    The rejection is a grammar fact, not a mode check: `readC` lists `.seal`
    beside `&mut`, `:=`, `;` and `f(…)`, and that list is this calculus's
    definition of the comptime sub-grammar. -/

def readCOn (t : Term) : String :=
  match (readC 1000 t).run (seedPure [] []) with
  | .ok v _ => "ACCEPTED " ++ v.pretty
  | .error e _ => e

example : strContains (readCOn ty{ (Z : Nat) })
  "not in the comptime fragment" = true := by native_decide
-- …including buried inside a pure former, which is the position where a
-- comptime reduction rule would have to reduce it if one existed.
example : strContains (readCOn (.app (.const "S") (.seal 0 (.ctorApp "Z" []) (.const "Nat"))))
  "not in the comptime fragment" = true := by native_decide

/-! ### A6. A seal is legal anywhere ⇒ evaluates, not only as a `let` right-hand
    side

    Every ⇒-evaluation is an event, so minting a fresh σ is coherent even when
    the seal is passed directly as a call argument, buried in a constructor
    argument, or sits in return position. -/

def natIdT : Term := prog defer_check { Π (x : Nat) → Nat }

-- as a call argument, where the mint happens inside `processArgs`
def a6a : Term := prog{
  fn TakesFn (g : %natIdT) -> Unit { () };
  TakesFn((λ (x : Nat). x : Π (x : Nat) → Nat)); () }
example : progOk a6a = true := by native_decide

-- inside a constructor argument
def a6b : Term := prog{ let l = Cons((3 : Nat), Nil); () }
example : progOk a6b = true := by native_decide

-- in return position: a function whose result IS a sealed function. The audit
-- reads the σ's type out of `sctx` and converts against it.
def a6c : Term := prog{
  fn MkId () -> %natIdT { (λ (x : Nat). x : Π (x : Nat) → Nat) };
  () }
example : progOk a6c = true := by native_decide
-- …and the same in return position with the wrong ascription is caught at the
-- node, before the return type is ever consulted.
def a6d : Term := prog defer_check {
  fn MkId () -> %natIdT { (λ (x : Nat). x : Π (x : Nat) → Bool) };
  () }
example : progRejects a6d "does not have its ascribed type" = true := by native_decide

/-! ### A7. A known limitation, pinned by a test

    A seal's body is ⇒-evaluated to ONE value, so a body that splits on a
    symbolic scrutinee has no seal meaning here: `pushContinuations` leaves the
    node alone (it is not a statement form), and the expression-position match
    is refused with the machine's standing message. A sealed body that branches
    is really a function body, whose audit belongs elsewhere. -/

def a7 : Term := prog defer_check {
  fn A7 (n : Nat) -> Unit { let f = (match n { Z => Z, S(k) => k } : Nat); () };
  () }
example : progRejects a7 "only a statement-position match may split" = true := by native_decide

/-! ## §C. Application of a value callee

    The two rules, chosen by what the slot holds, each with a negative control
    so that a rule branch nobody probes is not a rule branch nobody checked. -/

-- The λ as it sits in Ω: a raw closure — the syntax as written, under the
-- environment it captured (empty here, since the body cites nothing).
def vlam : Val := .closure [] ty{ λ (x : Nat). S x } none

-- C1. Body known, so unfold: a literal λ callee β-reduces, and the caller
-- knows the result exactly — `y ↦ 3`, not an existential.
def c1 : Term := prog defer_check { let F = λ (x : Nat). S x; let y = F(2); () }
example : progOk c1 = true := by native_decide
example : tailEnv c1 [("F", vlam), ("y", Val.nat 3)] = true := by native_decide

-- C2. Body withheld, so only the type's promise: seal the same λ, and the
-- same call yields an opaque σ. What the caller keeps is exactly what was
-- written in the seal's ascription.
def c2 : Term := prog{ let F = (λ (x : Nat). S x : Π (x : Nat) → Nat); let y = F(2); () }
example : progOk c2 = true := by native_decide
example : tailEnv c2 [("F", .sym 0), ("y", .sym 1)] = true := by native_decide

-- C3. Two calls are two events and are not identified: σ1 and σ2 are
-- distinct, each with its own type instance.
def c3 : Term := prog{
  let F = (λ (x : Nat). S x : Π (x : Nat) → Nat); let y = F(2); let z = F(2); () }
example : tailEnv c3 [("F", .sym 0), ("y", .sym 1), ("z", .sym 2)] = true := by native_decide

/-! ### C4–C8. The negative controls, one per rule branch -/

-- Partial application of a COMPTIME λ is a value: `F(2)` below yields a
-- partially-applied closure rather than an error. A comptime λ's capture is
-- knowledge, not a borrow, so nothing is held that partial application would
-- endanger — the "no partial application while a borrow waits" saturation rule
-- applies only to runtime entry points.
--
-- Saturation IS still enforced on both branches that enter through a runtime
-- call: an abstract `σ : Π` (c5 below) and an imperative λ (see A5/A6).
def c4 : Term := prog defer_check { let F = λ (x : Nat). λ (y : Nat). x; let z = F(2); () }
example : progOk c4 = true := by native_decide
-- …and the refusal on the abstract side, which is the branch that matters for
-- checking (a σ : Π under-applied is a closure holding its arguments).
def c5 : Term := prog defer_check {
  let F = (λ (x : Nat). λ (y : Nat). x : Π (x : Nat) → Π (y : Nat) → Nat);
  let z = F(2); () }
example : progRejects c5 "partial application" = true := by native_decide

-- Over-application.
def c6 : Term := prog defer_check { let F = λ (x : Nat). x; let z = F(2, 3); () }
example : progRejects c6 "too many arguments" = true := by native_decide

-- A mistyped argument, on both branches.
def c7 : Term := prog defer_check { let F = λ (x : Nat). x; let z = F(Nil); () }
example : progRejects c7 "does not have its parameter type" = true := by native_decide
def c8 : Term := prog defer_check { let F = (λ (x : Nat). x : Π (x : Nat) → Nat); let z = F(Nil); () }
example : progRejects c8 "does not have its parameter type" = true := by native_decide

-- A callee that is not a function at all, and one that was moved away.
def c9 : Term := prog defer_check { let f = 3; let z = f(2); () }
example : progRejects c9 "is not a function value" = true := by native_decide
def c10 : Term := prog defer_check { let f = Cons(1, Nil); let g = f; let z = f(2); () }
example : progRejects c10 "holds ⊥" = true := by native_decide

-- Demand collapses at the callee slot too. `x` holds a loan marker; the call
-- ends it and retries, so the rejection names what the slot really holds — a
-- Nat — rather than the marker.
def c11 : Term := prog defer_check { let x = 3; let b = &m x; let z = x(2); () }
example : progRejects c11 "is not a function value" = true := by native_decide

-- `Apply1`: a Π-typed telescope parameter (the `ih` shape), applied inside its
-- own body — kept as a fixture `Programs.lean`'s B7 also cites.
def apply1 : Term := prog{
  fn Apply1 (G : Π (x : Nat) → Nat, n : Nat) -> Nat { G(n) };
  () }
example : progOk apply1 = true := by native_decide

/-! ### C13. Transparent vs sealed, as a TYPING difference

    C1/C2 pin the forgetting in the environment (`y ↦ 3` against `y ↦ σ`). Here
    it is where that forgetting actually bites: the same program twice,
    differing only in whether the callee is sealed, accepted once and rejected
    once. `needsEq`'s telescope is dependent, so the second parameter's type is
    instantiated at what the checker knows about the first; transparent, that
    is `Id Nat 3 3` and `Refl` inhabits it; sealed, it is `Id Nat σ 3` and
    `Refl` does not.

    Sealing the successor function at `Π (x : Nat) → Nat` means callers know
    nothing about results — sound, honest, and here useless. Keeping knowledge
    across a seal means ascribing a richer type. -/

def c13t : Term := prog{
  fn NeedsEq (n : Nat, h : Id Nat n 3) -> Unit { () };
  let F = λ (x : Nat). S x; let y = F(2); NeedsEq(y, Refl); () }
def c13s : Term := prog defer_check {
  fn NeedsEq (n : Nat, h : Id Nat n 3) -> Unit { () };
  let F = (λ (x : Nat). S x : Π (x : Nat) → Nat); let y = F(2); NeedsEq(y, Refl); () }
example : progOk c13t = true := by native_decide
example : progRejects c13s "does not have its parameter type" = true := by native_decide

/-! ### C14. A caller can take apart what an abstract call returned

    When a `σ : Π` call mints its result from a Σ-shaped codomain, the caller
    must be able to `sigmaRec` it and compose the conjuncts with ordinary
    lemmas — otherwise "the callee's postcondition is the caller's only
    knowledge" would be knowledge the caller cannot use.

    The seal mints ONE σ at the whole instantiated codomain rather than
    componentwise; this pins that the coarse mint is already enough to be
    projectable. -/

def sigLemTy : Term := prog defer_check { Π (x : Nat) → Σ (H : Le x x). Le x x }
def sigLem : Term := prog defer_check { λ (x : Nat). Pair (LeReflRaw x) (LeReflRaw x) }

def c14 : Term := prog{
  let f = (%sigLem : %sigLemTy);
  let p = f(2);
  elim p return (λ (W : Σ (H : Le 2 2). Le 2 2). Le 2 2) { Pair (a) (b) => LeTransRaw 2 2 2 a b } }
-- The program's result is the projection, so its return type — passed as
-- `progOk`'s second argument — is what the audit checks it at.
example : progOk c14 (prog defer_check { Le 2 2 }) = true := by native_decide

-- The negative control has to be demanded to be a control: a `let`-bound proof
-- is never typed until something asks for its type (`readC` computes, it does
-- not check), so the wrong projection is only caught when the audit wants it.
def c14bad : Term := prog{
  let f = (%sigLem : %sigLemTy);
  let p = f(2);
  elim p return (λ (W : Σ (H : Le 2 2). Le 2 2). Le 3 2) { Pair (a) (b) => a } }
example : progRejects c14bad "does not have return type" (prog defer_check { Le 3 2 }) = true := by native_decide

/-! ## §D. The executing machine, and a simulation-relation case a seal creates

    Because a seal is legal anywhere ⇒ evaluates, a checking-mode σ can face a
    concrete value mid-expression, not only at a call boundary or a group
    release — a new case for the simulation relation that compares the two
    machines.

    **What breaks.** The relation's `matchVal` is a first-order structural
    matcher: it binds a bare `sym σ` to whatever concrete value sits opposite,
    and compares everything else structurally. That suffices while every σ
    stands at a whole slot, which is where calls and group-ends put them. A
    seal puts a σ *inside ordinary arithmetic*: after
    `let a = (3 : Nat); let b = Add a 1` the symbolic side holds the neutral
    spine `natRec … σ0` where the concrete side holds `4`. Structurally these
    differ, so a purely structural relation reports a counterexample that is
    not one.

    **The fix.** Two passes. Collect σ ↦ concrete bindings from the positions
    where the symbolic side IS a σ; then instantiate the whole symbolic
    environment, normalize, and compare. Consistency is enforced by the second
    pass (a σ bound twice to different values fails there), so the first pass
    needs no failure mode of its own. This reads "the concrete env is a
    σ-instance of the symbolic one" up to the pure fragment's own computation
    instead of up to structure. `S9Diff.instanceOfC` is that relation. -/

open Dllbc.Tests.S9Diff (runExec symEnvs instanceOf instanceOfC diffC)

abbrev instanceOfComputed := Dllbc.Tests.S9Diff.instanceOfC

/-- The differential under the purely structural relation — kept so the gap it
    misses is exhibited, not merely asserted away. -/
def diffOld (body : Term) : Bool :=
  match runExec body with
  | .error _ => false
  | .ok ce => (symEnvs body).any
      (fun r => match r with | .ok se => instanceOf se ce | .error _ => false)

/-! ### D1. The counterexample that names the new case -/

def d1 : Term := prog{ let a = (3 : Nat); let b = Add a 1; () }
example : progOk d1 = true := by native_decide
-- The old relation calls this a counterexample. It is not one: the two
-- environments agree at σ₀ := 3.
example : diffOld d1 = false := by native_decide
example : diffC   d1 = true  := by native_decide

/-! ### D3. Harness liveness — the relation must be able to say NO

    A counterexample-finder that has never found its counterexample is
    unvalidated. The extended relation is checked against a concrete run that
    genuinely disagrees: same symbolic side, a concrete side that adds 2 where
    the checker's σ-instance adds 1. -/

def d3mutant : Term := prog defer_check { let a = 3; let b = Add a 2; () }

example :
  (match symEnvs d1, runExec d3mutant with
   | [.ok se], .ok ce => instanceOfComputed se ce
   | _, _ => true) = false := by native_decide
-- …and it says YES to the honest pairing, so the NO above is discrimination, not
-- a broken relation.
example :
  (match symEnvs d1, runExec d1 with
   | [.ok se], .ok ce => instanceOfComputed se ce
   | _, _ => false) = true := by native_decide

end Dllbc.Tests.S26Seal
end

section
/-!
# Effectful recursors: ι-reduction of a recursor whose arms are bodies

## The two forms

  * `Term.lamR` / `Val.rfn` — the runtime λ, `λ(x : τ, y : υ){ … }`: named
    binders and a body. It needs its own value former (rather than reusing the
    pure λ's rule) because a body reaches its binders through Ω — a match
    scrutinizes a `Var`, `&mut x` roots a place at a `Var` — and a de Bruijn
    index names no slot. So the pure λ substitutes and this one binds.
  * `applyR` — ⇒-application of a function value, where three rules meet: β
    for a pure λ, bind-and-run for a runtime λ, and ι with the arm applied as
    a body for a recursor at a constructor scrutinee.

## What `ih` is, mechanically

`natRec P z s (S m) v … ↦ s m ⟨natRec P z s m⟩ v …`, and the second argument
is `ih`: literally the recursor at the predecessor. It is a `Val` spine —
closed, marker-free, index-kind — a first-class function value with no
environment capture anywhere in it. Calling it is `.callV`, and the modes of
its arguments come off the base arm's binder names, because a borrow-moded Π
has no value to read them off.

## Saturation is what keeps the borrows honest

ι hands the arm the predecessor, the recursor at it, and everything the caller
still owed in ONE application, so no partial application ever exists holding a
borrow while it waits.
-/

open Dllbc
open Dllbc.Tests.S9Diff (runExec symEnvs instanceOfC diffC)
open Dllbc.StdLemmas (IdCongrRaw)

namespace Dllbc.Tests.S26Rec

/-! ## The declared side's two verdicts

    §E compares a declared function against its sealed twin, so it needs the
    verdict of a `FnDef` — the one thing in this file that is not a program,
    and deliberately so: a declaration is what the pair is comparing
    against. -/

/-! ## §A. The runtime λ — the form, and the four things it is not -/

-- A1. Bind and run. The body is a body (a `let`, a constructor), and both
-- machines take the same rule: transparent application is β in the pure
-- fragment and inlining here, and neither machine verifies anything the
-- other does not.
def a1 : Term := prog{ let G = λ(a : Nat) { let b = S(a); S(b) }; let r = G(1); () }
example : progOk a1 = true := by native_decide
example : diffC a1 = true := by native_decide

-- A2. A runtime function value is INDEX-KIND, so calling it is a place read
-- and the slot survives. `ih` depends on this: a body that recurses twice
-- from one arm needs a callee that a call does not move out of its slot.
def a2 : Term := prog{ let G = λ(a : Nat) { S(a) }; let r = G(1); let s = G(4); () }
example : progOk a2 = true := by native_decide
example : diffC a2 = true := by native_decide

/-! ### A3. Closed function values, checked rather than assumed

    Only CLOSED function values are admitted; environment capture is deferred
    wholesale. A body is entered under a fresh id window, so a free variable
    would not dangle — it would be silently rebound to whatever the shift
    lands on, which is capture arriving by accident. The rejection names the
    variable, and its twin (the same program with the value passed in) is
    accepted, so the refusal is about the capture and not about the
    program. -/

def a3bad : Term := prog defer_check { let n = 3; let G = λ(a : Nat) { let z = n; () }; () }
def a3ok : Term := prog{ let n = 3; let G = λ(a : Nat, m : Nat) { let z = m; () }; G(1, n); () }
-- The refusal names the binding's MODE — a runtime citation is refused, a
-- capital one is capture and is fine, per the acceptance below.
example : progRejects a3bad "a runtime (lowercase) binding" = true := by native_decide

-- A3cap. The same program with the binding capitalised is ACCEPTED: a λ may
-- close over comptime knowledge. Nothing is lost by the freeze being
-- explicit — comptime bindings are immutable, so capture and eager inlining
-- are indistinguishable.
def a3cap : Term := prog{ let N = 3; let G = λ(a : Nat) { let z = N; () }; () }
example : progOk a3cap = true := by native_decide

-- A3pure. The same check, the other λ species: a PURE λ citing a runtime
-- binding gets the same refusal, with the same needle, as the runtime λ
-- above; and the capital twin is accepted.
def a3pureBad : Term := prog defer_check { let n = 3; let P = λ (u : Unit). n; () }
example : progRejects a3pureBad "a runtime (lowercase) binding" = true := by native_decide
def a3pureCap : Term := prog defer_check { let N = 3; let P = λ (u : Unit). N; () }
example : progOk a3pureCap = true := by native_decide

-- A3type. …and the exemption, the other half of the rule: a runtime citation
-- in a TYPE is untouched. `Le Z n` here is a type consumed at its own event,
-- not a body stored and applied later. Without this exemption the rule would
-- swallow every dependent signature in the corpus.
def a3typeOk : Term := prog{
  fn Bnd (n : Nat, h : Le Z n) -> Unit { () };
  () }
example : progOk a3typeOk = true := by native_decide
example : progOk a3ok = true := by native_decide

-- A4. A NULLARY runtime λ is refused, for a real ambiguity rather than
-- tidiness: `λ(){ e }` is a thunk, and at ι there is no way to tell "the arm
-- applied to no arguments" from "the arm with nothing owed" — one rule has
-- to answer one way.
--
-- An arm the motive owes nothing binds a distinguished unit binder, which is
-- unwritable from the surface — so the two readings are different terms, and
-- ι reads which one it has off the arm's leading binder. An arm that is not
-- suspended runs when the spine is formed.
--
-- With one λ former the comma list is a TELESCOPE, so `λ(){ … }` has no
-- binders and elaborates to its body — there is no term left for the kernel
-- to refuse. `prog{ let G = λ() { () }; () }` is a Lean elaboration error, the
-- same way an unbound name in a `prog{ }` block is: it cannot be written, so
-- there is no term to hand `progRejects`. What is assertable here is the fact
-- that makes the refusal move to the surface — an empty telescope is not a λ:
example : Term.beq (Term.lamTel [] .unit) .unit = true := by native_decide

-- A5/A6. Saturation, both directions.
def a5 : Term := prog defer_check { let G = λ(a : Nat, b : Nat) { () }; G(1); () }
def a6 : Term := prog defer_check { let G = λ(a : Nat) { () }; G(1, 2); () }
example : progRejects a5 "partial application" = true := by native_decide
example : progRejects a6 "too many arguments" = true := by native_decide

/-! ### A7. The pure fragment never meets the runtime λ

    The same grammar fact as the seal's (§A5 above), and it has to be asked
    of `readC` directly, because a rule that is merely never reached is not a
    rule that excludes anything. `.lamR` joins `&mut`, `:=`, `;`, `f(…)` and
    `seal` on the pure sub-grammar's standing exclusion list. -/

def readCOn (t : Term) : String :=
  match (readC 1000 t).run (seedPure [] []) with
  | .ok v _ => "ACCEPTED " ++ v.pretty
  | .error e _ => e

example : strContains (readCOn ty{ λ(x : Nat){ x } })
  "not in the comptime fragment" = true := by native_decide
-- …including buried inside a pure former, which is where a mode flag
-- consulted only at the top would have let it through.
example : strContains (readCOn (.app (.const "S") (Term.lamTel [(⟨0, "x"⟩, .const "Nat")] (.var ⟨0, "x"⟩))))
  "not in the comptime fragment" = true := by native_decide

/-! ## §B. ι with the arms as bodies — the executing machine

    A recursor whose arms are bodies is not a comptime object at all —
    `readC` refuses `.lamR`, and the motive is a borrow-moded Π which `readC`
    refuses too — so ⇒ evaluates the spine itself and ι-reduces it as
    control flow: the scrutinee's constructor selects an arm, and the arm
    runs, writing through borrows and calling.

    The programs below are fuel-threaded rather than decreasing on a payload:
    `[v]`-style payload decrease has no recursor form, so that regression is
    accepted and fuel is the interim workaround. -/

/-- The motive, and the one place a runtime recursor's type is written by
    hand rather than derived: `λ f. Π (v : &mut List Nat) → Unit`. It must be
    built in a ⇝ position (`prog{}`) — in a body, `&mut` is the borrow
    operation, not the borrow type. -/
def zeroMot : Term := prog defer_check { λ (f : Nat). Π (v : &mut List Nat) → Unit }

/-- `zeroAll`, as a recursor term: walk the list through a mutable borrow and
    write `0` into every element, recursing on fuel.

    The arms are bodies (`*hd := 0` is a write through a field reborrow).
    `ih` is a bound runtime variable holding a closed function value. The
    recursive call `ih(tl)` passes a BORROW as an argument and is saturated,
    so no partial application ever holds `tl` while waiting. There is no
    `[k]` guard anywhere: termination is by construction. -/

def b1 : Term := prog{
  let x = Cons(1, Cons(2, Nil));
  let b = &m x;
  let f = natRec %zeroMot
            (λ(v : &mut List Nat) { () })
            (λ(f2 : Nat, Ih : Π (v : &mut List Nat) → Unit, v : &mut List Nat)
               { match v { Nil => (), Cons(hd, tl) => { *hd := 0; Ih(tl); () } } });
  f(3, b);
  let y = x;
  () }
example : progOk b1 = true := by native_decide

/-- Read a slot back as the trace line it prints. -/
def slotOf (t : Term) (name : String) : Option String :=
  match tailEnvs t with
  | [.ok e] => (e.lookup name).map Val.pretty
  | _ => none

-- The list really is zeroed, in place, through the borrow — and the recursion
-- really did happen, since a body that never recursed would leave the tail alone.
example : slotOf b1 "y" = some "Cons Z (Cons Z Nil)" := by native_decide

-- …and the recursor itself sits in an ordinary runtime slot as a VALUE: a
-- closed function value. `@motive` is the erased motive slot (a
-- borrow-moded Π has no ⇝ reading, and ι has no use for one — the checking
-- side derives it from the ascription instead).
example : slotOf b1 "f" = some "natRec @motive λr(v){…} λr(f2, Ih, v){…}" := by
  native_decide

-- B2. Surplus fuel is harmless: the list runs out first and the `Nil` arm returns.
def b2 : Term := prog{
  let x = Cons(1, Cons(2, Nil));
  let b = &m x;
  let f = natRec %zeroMot
            (λ(v : &mut List Nat) { () })
            (λ(f2 : Nat, Ih : Π (v : &mut List Nat) → Unit, v : &mut List Nat)
               { match v { Nil => (), Cons(hd, tl) => { *hd := 0; Ih(tl); () } } });
  f(9, b);
  let y = x;
  () }
example : slotOf b2 "y" = some "Cons Z (Cons Z Nil)" := by native_decide

-- B3. `listRec`, with a motive that is a function type — the shape a runtime
-- recursor's motive always has, since the trailing binders are what carry
-- the borrows. Structural recursion needs no fuel: the scrutinee is the list
-- itself.
def bumpMot : Term := prog defer_check { λ (L : List Nat). Π (v : &mut Nat) → Unit }
def b3 : Term := prog{
  let l = Cons(7, Cons(8, Nil));
  let acc = 0;
  let a = &m acc;
  let f = listRec Nat %bumpMot
            (λ(w : &mut Nat) { () })
            (λ(h : Nat, t : List Nat, Ih : Π (v : &mut Nat) → Unit, v : &mut Nat)
               { *v := S(*v); Ih(v); () });
  f(l, a);
  let r = acc;
  () }
example : progOk b3 = true := by native_decide
-- One increment per element: the arm ran twice, through the same borrow, handed
-- down the recursion and handed back.
example : slotOf b3 "r" = some "S (S Z)" := by native_decide

/-! ### B4. A recursor stuck on a symbolic scrutinee is a VALUE, but applying
    one this way is refused

    Unapplied, the stuck spine has to be a legal value: `ih` is a bound
    Π-typed variable, literally the sealed view at the predecessor, and B1
    above shows it standing in a slot. Applied directly like this it would be
    arms-as-bodies checking reached without going through a seal, so it is
    refused by name rather than left to get stuck downstream. -/

def b4 : Term := prog defer_check { fn B4 (fuel : Nat) -> Unit {
  let x = Cons(1, Nil);
  let b = &m x;
  let f = natRec %zeroMot
            (λ(v : &mut List Nat) { () })
            (λ(f2 : Nat, Ih : Π (v : &mut List Nat) → Unit, v : &mut List Nat)
               { match v { Nil => (), Cons(hd, tl) => { *hd := 0; Ih(tl); () } } });
  f(fuel, b);
  let y = x;
  () }; () }
example : progRejects b4 "stuck on a symbolic scrutinee" = true := by native_decide

-- …and the same program without the application: forming the recursor is
-- forming a value, so this checks. The pair says the rejection above is
-- about applying a stuck recursor, not about writing one.
def b4v : Term := prog{
  let f = natRec %zeroMot
            (λ(v : &mut List Nat) { () })
            (λ(f2 : Nat, Ih : Π (v : &mut List Nat) → Unit, v : &mut List Nat)
               { match v { Nil => (), Cons(hd, tl) => { *hd := 0; Ih(tl); () } } });
  () }
example : progOk b4v = true := by native_decide

/-! ## §C. The differential, under one merged relation

    The relation must handle both machines on every new value form: array
    segments carved by borrows, AND a σ appearing mid-computation (§D above).
    `S9Diff.instanceOfC` is the merge of both cases into one matcher — collect
    σ ↦ concrete through constructors, borrows AND carved segments, then
    instantiate, normalize, and compare — and the three groups below say the
    merge kept both halves and can still say NO. -/

-- C1. The recursor programs: every one of them, both machines, same Ω.
def recShapes : List Term := [a1, a2, b1, b2, b3, b4v]
example : recShapes.all (fun t => diffC t) = true := by native_decide

-- C2. The array-carve half, kept: a checking-mode release leaves
-- `Arr⟨1 ▷ [3], 1 ▷ σ₀, 1 ▷ [2]⟩` where the concrete run is `[3, 9, 2]`.
-- These stay green under the merged relation, so computation was added
-- without costing the carve case.
example : Tests.S24Arrays.arrCallers.all
    (fun b => diffC b) = true := by native_decide

-- C3. The computation half, kept: the seal's own counterexample, where a
-- seal puts a σ inside ordinary arithmetic and a purely structural matcher
-- would report a counterexample that is not one.
example : diffC Tests.S26Seal.d1 = true := by native_decide
example : Tests.S26Seal.diffOld Tests.S26Seal.d1 = false := by native_decide

/-! ### C4. Harness liveness — the relation must be able to say NO about a
    recursor

    A counterexample-finder that has never found its counterexample is
    unvalidated, and validating it only on the seal's programs would say
    nothing about the ι rule. So: the symbolic side of `b1` (fuel 3, both
    elements zeroed) against the concrete side of the same program with fuel
    1, which zeroes the head and leaves the tail at 2. Same slots, same
    shapes, one genuinely different value. -/

def b1short : Term := prog{
  let x = Cons(1, Cons(2, Nil));
  let b = &m x;
  let f = natRec %zeroMot
            (λ(v : &mut List Nat) { () })
            (λ(f2 : Nat, Ih : Π (v : &mut List Nat) → Unit, v : &mut List Nat)
               { match v { Nil => (), Cons(hd, tl) => { *hd := 0; Ih(tl); () } } });
  f(1, b);
  let y = x;
  () }
-- The mutant is a real program and a different one: it stops after the head.
example : slotOf b1short "y" = some "Cons Z (Cons (S (S Z)) Nil)" := by native_decide

example :
  (match symEnvs b1, runExec b1short with
   | [.ok se], .ok ce => instanceOfC se ce
   | _, _ => true) = false := by native_decide
-- …and YES to the honest pairing, so the NO above is discrimination rather
-- than a relation that cannot see recursor programs at all.
example :
  (match symEnvs b1, runExec b1 with
   | [.ok se], .ok ce => instanceOfC se ce
   | _, _ => false) = true := by native_decide

/-! ## §D. A known limitation, pinned by a test

    A runtime recursor needs a FUNCTION motive, since the trailing binders
    are what carry the borrows. At a DATA motive (`λ l. Nat`) the arms have
    no trailing binders, so `ih` is not a function but the
    recursor-at-the-predecessor itself, handed to the arm as a value; the arm
    stores it, and the pure fragment cannot reduce it afterwards, because its
    own arm is a body and `whnfV` has no rule for applying one.

    The result is a stuck spine rather than a wrong answer — both machines
    produce the same thing, so this is not a differential failure — and the
    audit rejects it when it tries to type the result. A recursor whose
    motive is not a function type has ordinary terms for arms, and the pure
    recursor already computes those. -/

def lenMot : Term := prog defer_check { λ (L : List Nat). Nat }
def d1 : Term := prog defer_check { fn Caller () -> Nat {
  let l = Cons(7, Cons(8, Nil));
  let f = listRec Nat %lenMot Z (λ(h : Nat, t : List Nat, ih : Nat) { S(ih) });
  f(l) }; () }
example : progRejects d1 "cannot type neutral" = true := by native_decide

/-! ## §E. Sealing a borrow-moded Π runs the function audit

    `.seal t u` with a borrow-moded Π `u` cannot be checked by `hasType`: a Π
    with `&mut` binders is a function signature, `readC` refuses `borrowT`
    outright, and there is no value for `hasType` to be asked about. The
    check instead seeds `u`'s telescope, explores the body one path per
    symbolic branch, and audits each path at return with exit snapshots and
    obligations — the same function audit reached from a declaration.

    What decides which rule fires is the sealed TERM, not the type: a
    runtime λ takes the audit, and everything else takes the ordinary
    `readC`-then-`hasType` path unchanged. -/

def unitSeal : Term := prog defer_check { Π (v : &mut List Nat) → Unit }
def pinSeal : Term := prog defer_check { Π (v : &mut List Nat) → Id (List Nat) (*v) (Cons 9 Nil) }

-- E1. The rule, end to end: a sealed function taking a borrow is checked at the
-- node, called through its σ by the table's own call rule, and executes.
def e1 : Term := prog{
  let F = (λ(v : &mut List Nat) { *v := Cons(9, Nil); () } : %unitSeal);
  let x = Cons(1, Nil);
  let b = &m x;
  F(b);
  let y = x;
  () }
example : progOk e1 = true := by native_decide
example : diffC e1 = true := by native_decide

/-! ### E2. The ensures, threaded through the seal

    The caller holds a borrow, hands a reborrow to the sealed function, and
    returns the equation it got back as its own postcondition. That only
    type-checks if the σ the call re-minted for the payload is the same σ the
    caller's exit `*v` reads, so this pins the whole ensures pipeline through
    a sealed callee, not merely that the seal was accepted.

    The sealed body has to PRODUCE the proof, which a `Unit`-sealed body does
    not have to do — the pair below is the real test of "what you keep is
    what you write". -/

def e2 : Term := prog{ fn Caller (v : &mut List Nat) -> Id (List Nat) (*v) (Cons 9 Nil) {
  let F = (λ(w : &mut List Nat) { *w := Cons(9, Nil); Refl } : %pinSeal);
  F(&m *v) }; () }
example : progOk e2 = true := by native_decide

-- The same program, the same body, sealed at `Unit`: the caller gets nothing
-- back and cannot state its own postcondition. Sound, honest, useless — one
-- ascription apart from e2.
def e2none : Term := prog defer_check { fn Caller (v : &mut List Nat) -> Id (List Nat) (*v) (Cons 9 Nil) {
  let F = (λ(w : &mut List Nat) { *w := Cons(9, Nil); () } : %unitSeal);
  F(&m *v) }; () }
example : progRejects e2none "does not have return type" = true := by native_decide

/-! ### E3. The negative controls, one per branch of the new rule -/

-- The body does not establish the ensures: rejected at the seal by the
-- audit, with the audit's own message — `Refl` does not inhabit the
-- equation the ascription promised.
def e3a : Term := prog defer_check {
  let F = (λ(v : &mut List Nat) { *v := Cons(8, Nil); Refl } : %pinSeal); () }
example : progRejects e3a "does not have return type" = true := by native_decide

-- The body leaves a hole in its argument borrow: the OBLIGATION audit, which
-- only exists because the seal now seeds a telescope.
def e3b : Term := prog defer_check {
  let F = (λ(v : &mut List Nat) { let l = *v; () } : %unitSeal); () }
example : progRejects e3b "holds a hole (⊥) at return" = true := by native_decide

-- Mode disagreement: the λ's binder is lowercase where the ascription binds
-- comptime. The ascription is the contract, so this is checked.
def cmpSeal : Term := prog defer_check { Π (N : Nat) → Nat }
def e3c : Term := prog defer_check {
  let F = (λ(n : Nat) { S(n) } : %cmpSeal); () }
example : progRejects e3c "the ascribed type binds it as comptime" = true := by native_decide
-- …and its twin, one character apart, is accepted.
def e3cok : Term := prog{
  let F = (λ(N : Nat) { Z } : %cmpSeal); () }
example : progOk e3cok = true := by native_decide

-- Arity disagreement, at the ascription rather than at a call.
def e3d : Term := prog defer_check {
  let F = (λ(v : &mut List Nat, w : Nat) { () } : %unitSeal); () }
example : progRejects e3d "no Π binder left for it" = true := by native_decide

-- Sealing something that is NOT a runtime λ at a function signature (see A4
-- above, for the borrow-free case).
def e3e : Term := prog defer_check {
  let F = (λ (x : Nat). x : %unitSeal); () }
example : progRejects e3e "the sealed term must be a runtime λ" = true := by native_decide

/-! ### E4. Frame isolation — the sealed body's effects stay inside the check

    The sealed body below borrows and writes, and the caller's `x` is
    untouched by any of it — still owned, still `Cons 1 Nil`, movable
    afterwards. A body checked in place (rather than in its own frame) would
    have consumed something of the caller's. -/

def e4 : Term := prog{
  let x = Cons(1, Nil);
  let F = (λ(v : &mut List Nat) { *v := Cons(9, Nil); () } : %unitSeal);
  let y = x;
  () }
example : progOk e4 = true := by native_decide
example : slotOf e4 "y" = some "Cons (S Z) Nil" := by native_decide

/-! ### E5. The seal-vs-declaration identity, extended to borrow-moded seals

    Does the audit of a sealed λ agree with a declared `fn`'s verdict on the
    same function? Since `fn` is a macro over a sealed recursor, it must — the
    two are the same check reached by two routes.

    Checked as an identity over hand-written twins rather than a spot check,
    with both polarities so it cannot hold vacuously. Each pair is the same
    telescope, the same return type and the same body, written once as an
    `fn` statement and once as `(λ(… : …){ … } : Π …)`. -/

def pushD : Term := prog{ fn PushD (e : Nat, v : &mut List Nat) -> Unit
  { let tail = *v; *v := Cons(e, tail); () }; () }
def pushS : Term := prog{ let F = (λ(e : Nat, v : &mut List Nat) { let tail = *v; *v := Cons(e, tail); () } : Π (e : Nat) → Π (v : &mut List Nat) → Unit); () }

/-- The `old *v` shape: an ensures relating the exit payload to the entry
    one, which is why the seal has to seed `entrySyms` as well as
    `exitSyms`. -/
def consD : Term := prog{ fn ConsD (v : &mut List Nat)
  -> Id (List Nat) (*v) (Cons 9 (old *v))
  { let t = *v; *v := Cons(9, t); Refl }; () }
def consS : Term := prog{ let F = (λ(v : &mut List Nat) { let t = *v; *v := Cons(9, t); Refl } : Π (v : &mut List Nat) → Id (List Nat) (*v) (Cons 9 (old *v))); () }

/-- The spec lie: the body conses `8` where the ensures says `9`. -/
def lieD : Term := prog defer_check { fn LieD (v : &mut List Nat)
  -> Id (List Nat) (*v) (Cons 9 (old *v))
  { let t = *v; *v := Cons(8, t); Refl }; () }
def lieS : Term := prog defer_check { let F = (λ(v : &mut List Nat) { let t = *v; *v := Cons(8, t); Refl } : Π (v : &mut List Nat) → Id (List Nat) (*v) (Cons 9 (old *v))); () }

/-- The obligation lie: the payload is taken and never refilled. -/
def holeD : Term := prog defer_check { fn HoleD (v : &mut List Nat) -> Unit { let l = *v; () }; () }
def holeS : Term := prog defer_check { let F = (λ(v : &mut List Nat) { let l = *v; () } : Π (v : &mut List Nat) → Unit); () }

/-- Each pair: the `fn` statement and the hand-written sealed λ of the same
    function, both as programs. -/
def twins : List (Term × Term) :=
  [ (pushD, pushS), (consD, consS), (lieD, lieS), (holeD, holeS) ]

-- The `fn` lowering's audit and the hand-written seal's agree, pair for pair.
example : twins.all (fun p => progOk p.1 == progOk p.2) = true := by native_decide
-- …and it is not vacuous: both verdicts occur, so the identity above is
-- pinning agreement rather than a constant function.
example : (twins.any (fun p => progOk p.1) && twins.any (fun p => !progOk p.1)) = true := by
  native_decide
-- …and the rejections agree on WHY, not merely that. A sealed body that lies
-- about its ensures and a `fn` that lies about the same ensures are refused
-- by the same audit with the same message.
example : (progRejects lieD "does not have return type" && progRejects lieS "does not have return type")
  = true := by native_decide
example : (progRejects holeD "holds a hole (⊥) at return" && progRejects holeS "holds a hole (⊥) at return")
  = true := by native_decide

/-! ## §F. Arms as bodies — the checking side

    Runtime-moded recursor motives are the checker-side addition: arms
    contain writes, calls and borrows — bodies — so the checker must
    symbolically execute an arm as a body with an abstract `ih : Π` in
    scope. The content of that judgment is exactly ordinary guard-checking;
    the plumbing to reach it is new.

    Three things make it work:

      * The motive is derived from the signature: peel one Π off the
        ascription and the codomain IS the motive's body, so nothing needs
        to be inferred.
      * Each arm is checked once, at its own constructor — `Z` and `S k` ARE
        the split, and the motive instantiated at each is the goal.
      * `ih` is a σ with a signature and no body — the sealed self-view at
        the predecessor. It is seeded by the same rule that seeds any
        Π-typed parameter and called by the same rule that calls any sealed
        function. -/

def zeroSeal : Term := prog defer_check { Π (fuel : Nat) → Π (v : &mut List Nat) → Unit }


def f1 : Term := prog{
  let F = (natRec %zeroMot
                 (λ(v : &mut List Nat) { () })
                 (λ(f2 : Nat, Ih : Π (v : &mut List Nat) → Unit, v : &mut List Nat)
                    { match v { Nil => (), Cons(hd, tl) => { *hd := 0; Ih(tl); () } } }) : %zeroSeal);
  let x = Cons(1, Cons(2, Nil));
  let b = &m x;
  F(3, b);
  let y = x;
  () }
example : progOk f1 = true := by native_decide

-- The seal is what makes it opaque: the caller learns only `Unit`, so the
-- list it gets back is an existential. Asserted as "a σ" rather than as a σ
-- id: the id is a counter, and pinning it would make this test fail for
-- reasons that have nothing to do with what it is about.
example : (slotOf f1 "y").map (fun s => (s.take 1).toString) = some "σ" := by native_decide

-- …and the SAME program executes, with the recursion really running: both
-- machines, one differential.
example : diffC f1 = true := by native_decide
example :
  (match Dllbc.Tests.S9Diff.runExec f1 with
   | .ok e => (e.lookup "y").map Val.pretty
   | .error _ => none) = some "Cons Z (Cons Z Nil)" := by native_decide

/-! ### F2. The motive is derived, and a written one that disagrees is refused

    The motive is redundant — it is the sealed Π with the scrutinee peeled
    off — so the checker derives it and compares. The comparison is
    syntactic, forced rather than lazy: a motive over a borrow-moded Π has no
    `Val`, hence no conversion to be compared up to. -/

def wrongMot : Term := prog defer_check { λ (F : Nat). Π (v : &mut List Nat) → Nat }
def f2 : Term := prog defer_check {
  let F = (natRec %wrongMot
                 (λ(v : &mut List Nat) { () })
                 (λ(f2 : Nat, Ih : Π (v : &mut List Nat) → Nat, v : &mut List Nat)
                    { match v { Nil => (), Cons(hd, tl) => { *hd := 0; Ih(tl); () } } }) : %zeroSeal);
  () }
example : progRejects f2 "not the one its ascription derives" = true := by native_decide

/-! ### F3. An arm that does not establish the motive is rejected AT ITS OWN ARM

    The base arm below returns without restoring what it took, so its obligation
    audit fails — and the step arm is untouched and would pass. That is what says
    the arms are checked *separately*, each at its own instantiation, rather than
    the whole recursor being checked as one lump. -/

def f3 : Term := prog defer_check {
  let F = (natRec %zeroMot
                 (λ(v : &mut List Nat) { let l = *v; () })
                 (λ(f2 : Nat, Ih : Π (v : &mut List Nat) → Unit, v : &mut List Nat)
                    { match v { Nil => (), Cons(hd, tl) => { *hd := 0; Ih(tl); () } } }) : %zeroSeal);
  () }
example : progRejects f3 "holds a hole (⊥) at return" = true := by native_decide

/-! ## §G. `split_off`: the same function, written by hand as a sealed
    recursor and via the `fn` macro

    `fn` is a macro over a sealed recursor binding, so a real function must
    check the same way whichever way it is written. `split_off` is the
    subject because it is real: it recurses, it mutates through a borrow, it
    hands a reborrow to its own recursive call, its return type is a
    Σ-chain of two equations relating the exit and entry snapshots, and it
    has a dead branch discharged by ex falso. It also needs no fuel:
    `split_off` recurses on its index, a `Nat`, so the recursor form is
    `natRec` on the argument already named.

    `S23Direct.splitOff` is the `fn`-statement form; this section hand-writes
    the same function as `.seal ⟨natRec …⟩ ⟨Π …⟩`, with `ih` as an abstract
    signature and no guard anywhere. Both are accepted. -/

def splitTy : Term := prog defer_check {
  Π (i : Nat) → Π (v : &mut List Nat) → Π (hi : Le i (Len *v))
    → Σ (ret : List Nat). Σ (H1 : Id (List Nat) (*v) (Take i (old *v))).
         Id (List Nat) ret (Drop i (old *v)) }

def splitMot : Term := prog defer_check {
  λ (i : Nat). Π (v : &mut List Nat) → Π (hi : Le i (Len *v))
    → Σ (ret : List Nat). Σ (H1 : Id (List Nat) (*v) (Take i (old *v))).
         Id (List Nat) ret (Drop i (old *v)) }

/-- `split_off` as a `fn` elaborates. The body is `S23Direct.splitOff`'s,
    transcribed with one change and one deletion: the self-call
    `split_off(&mut *tl, i2, hi)` becomes `ih(&mut *tl, hi)` — the scrutinee
    argument is gone, because ι supplies it — and the `match i` disappears
    into the two arms. -/
def splitSealed : Term := prog{
  let F = (natRec %splitMot
      (λ(v : &mut List Nat, hi : Le Z (Len *v))
         { let tail = *v; *v := Nil; Pair(tail, Pair(Refl, Refl)) })
      (λ(i2 : Nat,
         Ih : Π (v : &mut List Nat) → Π (hi : Le i2 (Len *v))
                → Σ (ret : List Nat). Σ (H1 : Id (List Nat) (*v) (Take i2 (old *v))).
                     Id (List Nat) ret (Drop i2 (old *v)),
         v : &mut List Nat,
         hi : Le (S i2) (Len *v)) {
         match v {
           Nil => botElim Unit hi,
           Cons(hd, tl) => {
             let y1 = Take i2 (*tl);
             let Pair(rr, Pair(H1, h2)) = Ih(&m *tl, hi);
             let c1 = IdCongrRaw (List Nat) (List Nat) (λ (a : List Nat). Cons (*hd) a)
                        (*tl) y1 H1;
             Pair(rr, Pair(c1, h2)) } } }) : %splitTy);
  () }

-- This hand-written sealed recursor and `S23Direct.splitOff` are the same
-- function, checking the same way both `fn` is a macro over the seal form.
example : progOk splitSealed = true := by native_decide

/-! ### G2. Not vacuous — the sealed form rejects the same lies the declared
    one does

    `S23Direct` guards `splitOff` with four twins (three spec lies and a body
    lie) so that its acceptance is not a coincidence. The sealed form has to
    be guarded the same way, or "both check" would be a much weaker statement
    than it looks. The body lie is the sharper of the two here: it breaks the
    congruence in the `Cons` arm, which is the arm `ih` lives in. -/

def splitMotLie : Term := prog defer_check {
  λ (i : Nat). Π (v : &mut List Nat) → Π (hi : Le i (Len *v))
    → Σ (ret : List Nat). Σ (H1 : Id (List Nat) (*v) (Drop i (old *v))).
         Id (List Nat) ret (Drop i (old *v)) }
def splitTyLie : Term := prog defer_check {
  Π (i : Nat) → Π (v : &mut List Nat) → Π (hi : Le i (Len *v))
    → Σ (ret : List Nat). Σ (H1 : Id (List Nat) (*v) (Drop i (old *v))).
         Id (List Nat) ret (Drop i (old *v)) }

-- A SPEC lie: the prefix conjunct claims `Drop` where the body leaves `Take`.
def splitSpecLie : Term := prog defer_check {
  let F = (natRec %splitMotLie
      (λ(v : &mut List Nat, hi : Le Z (Len *v))
         { let tail = *v; *v := Nil; Pair(tail, Pair(Refl, Refl)) })
      (λ(i2 : Nat,
         Ih : Π (v : &mut List Nat) → Π (hi : Le i2 (Len *v))
                → Σ (ret : List Nat). Σ (H1 : Id (List Nat) (*v) (Drop i2 (old *v))).
                     Id (List Nat) ret (Drop i2 (old *v)),
         v : &mut List Nat,
         hi : Le (S i2) (Len *v)) {
         match v {
           Nil => botElim Unit hi,
           Cons(hd, tl) => {
             let y1 = Take i2 (*tl);
             let Pair(rr, Pair(H1, h2)) = Ih(&m *tl, hi);
             let c1 = IdCongrRaw (List Nat) (List Nat) (λ (a : List Nat). Cons (*hd) a)
                        (*tl) y1 H1;
             Pair(rr, Pair(c1, h2)) } } }) : %splitTyLie);
  () }
-- Caught on the BASE arm (`Pair σ (Pair Refl Refl)` against `Id Nil σ`), exactly
-- where `S23Direct` says its spec lies are caught.
example : progRejects splitSpecLie "does not have return type" = true := by native_decide

-- A BODY lie: the `Cons` arm forgets to restore the head, so the prefix conjunct
-- is false on the recursive path — the arm `ih` lives in.
def splitBodyLie : Term := prog defer_check {
  let F = (natRec %splitMot
      (λ(v : &mut List Nat, hi : Le Z (Len *v))
         { let tail = *v; *v := Nil; Pair(tail, Pair(Refl, Refl)) })
      (λ(i2 : Nat,
         Ih : Π (v : &mut List Nat) → Π (hi : Le i2 (Len *v))
                → Σ (ret : List Nat). Σ (H1 : Id (List Nat) (*v) (Take i2 (old *v))).
                     Id (List Nat) ret (Drop i2 (old *v)),
         v : &mut List Nat,
         hi : Le (S i2) (Len *v)) {
         match v {
           Nil => botElim Unit hi,
           Cons(hd, tl) => {
             let y1 = Take i2 (*tl);
             let Pair(rr, Pair(H1, h2)) = Ih(&m *tl, hi);
             let c1 = IdCongrRaw (List Nat) (List Nat) (λ (a : List Nat). Cons (*hd) a)
                        (*tl) y1 H1;
             Pair(rr, Pair(H1, h2)) } } }) : %splitTy);
  () }
-- Caught on the STEP arm — the one `ih` lives in, and the one the spec lie
-- above leaves untested. Same division of labour as the four twins the
-- declared function is guarded with, so "both check" is a claim about the
-- same coverage and not just the same verdict.
example : progRejects splitBodyLie "does not have return type" = true := by native_decide

/-! ## §H. `bad()`, twice: the incoherence, probed rather than assumed

    A self-call admitted at its own declared return type with nothing
    decreasing proves anything: `fn bad () -> Id Nat Z (S Z) { bad() }`. A
    recursor-expressed function needs no separate guard against this, so the
    two ways `bad()` could come back have to be checked directly rather than
    argued away: the `bad()` self-proof must stay unwritable by
    construction. -/

/-! ### H1. An unsealed recursive λ is unwritable, which is the honest form of
    "it has no checking story"

    An unsealed recursive λ is incoherent at checking (unfolding self never
    terminates), and it stays unwritable. The mechanism is not a rule about
    recursion at all: the binding is not in scope in its own right-hand side.
    `let g = λ(n : Nat){ g(n) }` binds `g` for what FOLLOWS, so the `g` inside
    the λ names nothing lexical and falls through to the declaration table,
    where it is not — a let-chain cannot reference downward, and
    self-reference is the degenerate case of that.

    This control had to be made to bite: written as a `let` that is never
    used, the program is ACCEPTED and looks like a working negative test,
    because the λ's body is never demanded and nothing ever resolves the
    name. A negative test must be per demand site, which is why both forms
    below make something ask. -/

-- Demanded by APPLYING it: the body runs and the name resolves against nothing.
def h1 : Term := prog defer_check {
  let G = λ(n : Nat) { G(n) };
  G(1);
  () }
example : progRejects h1 "unknown function 'G'" = true := by native_decide

-- Demanded by SEALING it instead: sealing is what makes a body get checked,
-- and it is also what a recursive function needs — but the seal does not
-- put the binding in its own scope either. Recursion has to come from the
-- recursor.
def h1s : Term := prog defer_check {
  let G = (λ(n : Nat) { G(n) } : Π (n : Nat) → Nat);
  () }
example : progRejects h1s "unknown function 'G'" = true := by native_decide

-- The vacuous version, pinned as the trap it is rather than deleted: the same
-- program with nothing demanding the λ's body is accepted, and tests nothing.
def h1vacuous : Term := prog{ let G = λ(n : Nat) { G(n) }; () }
example : progOk h1vacuous = true := by native_decide

/-! ### H2. A sealed recursor whose motive promises a falsehood is rejected,
    and the rejection comes from the BASE arm

    The `bad()` shape as a recursor: a motive claiming `Id Nat Z (S Z)` at
    every level. The step arm goes through, and that is not a bug — `ih`
    really does hand it the claim at the predecessor, which is the
    self-ensures the recursor forces. What stops it is the base arm, which
    has no `ih` and must inhabit the claim outright. That is structural
    induction doing the job an explicit decrease guard would otherwise do by
    hand.

    The pair below says so. `h2` is the whole recursor and is rejected;
    `h2step` is the same step arm sealed on its own at the type `ih` gave
    it — `Π (u : Unit) → Id Nat Z (S Z)` assumed, the same returned — and is
    ACCEPTED, the assumption discharged honestly rather than a hole. -/

def badMot : Term := prog defer_check { λ (n : Nat). Π (u : Unit) → Id Nat Z (S Z) }
def badTy : Term := prog defer_check { Π (n : Nat) → Π (u : Unit) → Id Nat Z (S Z) }

def h2 : Term := prog defer_check {
  let F = (natRec %badMot
                 (λ(u : Unit) { Refl })
                 (λ(n2 : Nat, Ih : Π (u : Unit) → Id Nat Z (S Z), u : Unit) { Ih(u) }) : %badTy);
  () }
example : progRejects h2 "does not have return type" = true := by native_decide

-- The step arm alone, with the predecessor's claim as a HYPOTHESIS: accepted.
-- So the rejection above is located at the base case and nowhere else —
-- `bad()` dies because `Id Nat Z (S Z)` has no proof at zero, not because a
-- guard forbade the recursion.
def h2step : Term := prog{
  let F = (λ(Ih : Π (u : Unit) → Id Nat Z (S Z), u : Unit) { Ih(u) } : Π (Ih : Π (u : Unit) → Id Nat Z (S Z)) → Π (u : Unit) → Id Nat Z (S Z));
  () }
example : progOk h2step = true := by native_decide

/-! ## §I. `ih` at the wrong level: the decrease requirement, as TYPING rather
    than a side condition

    A recursive call's argument must be a strict structural predecessor —
    but here that requirement lives entirely in the type: `ih` is typed `P k`
    while the arm proves `P (S k)`, so an arm that tries to use the
    recursion at its OWN level has nothing to pass it. The check is not a
    comparison the checker performs; it is the type `ih` was given.

    The motive below carries a fuel bound, which is what makes the levels
    visible: `Hn : Le (Len *v) n`. In the step arm `Hn : Le (Len *v) (S n2)`
    and `ih` wants `Le (Len *v) n2` — one successor apart, and no term
    bridges them. The accepted twin derives the predecessor's bound properly
    and passes THAT, so the rejection is about the level and not about the
    program being unwritable. -/

def bndMot : Term := prog defer_check {
  λ (n : Nat). Π (v : &mut List Nat) → Π (Hn : Le (Len *v) n) → Unit }
def bndTy : Term := prog defer_check {
  Π (n : Nat) → Π (v : &mut List Nat) → Π (Hn : Le (Len *v) n) → Unit }

-- The arm hands `ih` its OWN bound, `Le (Len *v) (S n2)`, where `ih` binds
-- `Le (Len *v) n2`. Refused, by the argument check at the abstract call.
def i1 : Term := prog defer_check {
  let F = (natRec %bndMot
                 (λ(v : &mut List Nat, Hn : Le (Len *v) Z) { () })
                 (λ(n2 : Nat,
                    Ih : Π (v : &mut List Nat) → Π (Hn : Le (Len *v) n2) → Unit,
                    v : &mut List Nat, Hn : Le (Len *v) (S n2)) { Ih(&m *v, Hn); () }) : %bndTy);
  () }
example : progRejects i1 "does not have its parameter type" = true := by native_decide

-- …and the twin that recurses at the predecessor's level is ACCEPTED — which is
-- what says the discipline is usable and not merely restrictive. Matching `v`
-- makes `*v` a `Cons`, so `Len *v` is `S (Len *tl)` and the arm's own
-- `Le (S (Len *tl)) (S n2)` IS `Le (Len *tl) n2` definitionally: the bound
-- the predecessor wants, obtained by the list getting shorter rather than by
-- a lemma. It is the TYPE that carries this, so nothing separately checks
-- it.
def i2 : Term := prog{
  let F = (natRec %bndMot
                 (λ(v : &mut List Nat, Hn : Le (Len *v) Z) { () })
                 (λ(n2 : Nat,
                    Ih : Π (v : &mut List Nat) → Π (Hn : Le (Len *v) n2) → Unit,
                    v : &mut List Nat, Hn : Le (Len *v) (S n2))
                    { match v { Nil => (), Cons(hd, tl) => { Ih(&m *tl, Hn); () } } }) : %bndTy);
  () }
example : progOk i2 = true := by native_decide

/-! ## §J. The sealed `split_off`, RUN

    §G checks the two forms agree; this runs the sealed one as a program:
    the same recursor, called concretely, splitting a real list, with the
    two machines agreeing.

    `hi : Le 1 (Len *v)` is supplied as `()`: `Le` computes, the payload is
    concrete, and `Le 1 2` reduces to `Unit` — the bound holds by
    computation, not by citation. -/

def j1 : Term := prog{
  let F = (natRec %splitMot
      (λ(v : &mut List Nat, hi : Le Z (Len *v))
         { let tail = *v; *v := Nil; Pair(tail, Pair(Refl, Refl)) })
      (λ(i2 : Nat,
         Ih : Π (v : &mut List Nat) → Π (hi : Le i2 (Len *v))
                → Σ (ret : List Nat). Σ (H1 : Id (List Nat) (*v) (Take i2 (old *v))).
                     Id (List Nat) ret (Drop i2 (old *v)),
         v : &mut List Nat,
         hi : Le (S i2) (Len *v)) {
         match v {
           Nil => botElim Unit hi,
           Cons(hd, tl) => {
             let y1 = Take i2 (*tl);
             let Pair(rr, Pair(H1, h2)) = Ih(&m *tl, hi);
             let c1 = IdCongrRaw (List Nat) (List Nat) (λ (a : List Nat). Cons (*hd) a)
                        (*tl) y1 H1;
             Pair(rr, Pair(c1, h2)) } } }) : %splitTy);
  let x = Cons(1, Cons(2, Cons(3, Nil)));
  let b = &m x;
  let r = F(1, b, ());
  let y = x;
  () }
example : progOk j1 = true := by native_decide

-- It really splits: after `split_off` at index 1 the borrow's payload keeps the
-- first element and the rest came back by value inside the returned Σ.
example :
  (match Dllbc.Tests.S9Diff.runExec j1 with
   | .ok e => (e.lookup "y").map Val.pretty
   | .error _ => none) = some "Cons (S Z) Nil" := by native_decide

-- …and the two machines agree on the whole final Ω.
example : diffC j1 = true := by native_decide

/-! ## §K. Both dispatch surfaces reach every new rule

    A statement-position `match` or `let` never reaches `readR`'s own cases —
    the explore driver handles those separately — so every rule added by
    this file has to be checked reachable through both surfaces rather than
    assumed.

    Each is, by construction: every rule here is a different `readR` case
    (`.seal`, `.lamR`, `.callV`, the recursor spine), and the driver reaches
    all of them through `.letIn`'s right-hand side, through `.seq`'s
    expression, and through the final-expression fall-through. The tests
    below put a seal and a recursor call at each of those three positions,
    inside a branch of a symbolic match — the position where a rule fenced
    off inside `readR`'s own `.matchE`/`.letIn` cases would go dark. -/

def k1 : Term := prog{ fn K1 (n : Nat) -> Unit {
  match n {
    Z => (),
    S(m) => {
      -- a seal as a `let` right-hand side, inside a branch
      let F = (λ(v : &mut List Nat) { *v := Cons(9, Nil); () } : %unitSeal);
      let x = Cons(1, Nil);
      let b = &m x;
      -- a sealed call in statement position, inside a branch
      F(b);
      let y = x;
      () } } }; () }
example : progOk k1 = true := by native_decide

-- The negative twin at the same two positions: a body that lies about its
-- ensures is caught inside the branch, not skipped along with it.
def k2 : Term := prog defer_check { fn K2 (n : Nat) -> Unit {
  match n {
    Z => (),
    S(m) => {
      let F = (λ(v : &mut List Nat) { *v := Cons(8, Nil); Refl } : %pinSeal);
      () } } }; () }
example : progRejects k2 "does not have return type" = true := by native_decide

-- …and a seal in FINAL-EXPRESSION position inside a branch, the third route
-- (`explore`'s fall-through to `readR`). The ascription here is borrow-free
-- because a declared `fn` cannot yet return a borrow-moded Π.
def natFn : Term := prog defer_check { Π (n : Nat) → Nat }
def k3 : Term := prog{ fn K3 (n : Nat) -> %natFn {
  match n {
    Z => (λ(m : Nat) { Z } : %natFn),
    S(m) => (λ(k : Nat) { S(k) } : %natFn) } }; () }
example : progOk k3 = true := by native_decide

/-! ## §M. Binding `ih` to a local is refused, on both machines, and the
    refusal is not about recursion at all

    `ih`'s arm binder is capitalized (`Ih`), which marks it as holding a
    function — and no runtime (lowercase) binding may hold a function.
    `let g = Ih` is therefore a ⇒-move of a capital binding into a lowercase
    slot, refused by the same fence that would refuse any capital-to-lowercase
    move, regardless of what the value is. The refusal has nothing to do with
    `ih` specifically: any function value bound to a slot hits the same rule.

    Both machines agree on this program: checking refuses at the binding, and
    executing refuses `let g = Ih` for the same reason and with the same
    message, so there is no reject-vs-run asymmetry left to manage here. -/

def mSeal : Term := prog defer_check { Π (n : Nat) → Π (v : &mut List Nat) → Unit }
def mMot : Term := prog defer_check { λ (n : Nat). Π (v : &mut List Nat) → Unit }

/-- The arm binds `ih` to a local and then still calls it. -/
def m1 : Term := prog defer_check {
  let F = (natRec %mMot
                 (λ(v : &mut List Nat) { () })
                 (λ(n2 : Nat, Ih : Π (v : &mut List Nat) → Unit, v : &mut List Nat) {
                    let g = Ih;
                    match v { Nil => (), Cons(hd, tl) => { *hd := 0; Ih(tl); () } } }) : %mSeal);
  let x = Cons(1, Cons(2, Nil));
  let b = &m x;
  F(3, b);
  () }

-- CHECKING: refused at the binding, by the fence against moving a capital
-- (function-holding) binding into a lowercase slot. The message names the
-- fix: capitalize the destination binder.
example : progRejects m1 "cannot be ⇒-moved" = true := by native_decide

-- The migrated twin: the same body with the binder capitalised is accepted,
-- so the refusal is about the binder's mode and not about naming `ih` at all.
def m1cap : Term := prog{
  let F = (natRec %mMot
                 (λ(v : &mut List Nat) { () })
                 (λ(n2 : Nat, Ih : Π (v : &mut List Nat) → Unit, v : &mut List Nat) {
                    let G = Ih;
                    match v { Nil => (), Cons(hd, tl) => { *hd := 0; Ih(tl); () } } }) : %mSeal);
  let x = Cons(1, Cons(2, Nil));
  let b = &m x;
  F(3, b);
  () }
example : progOk m1cap = true := by native_decide

-- EXECUTING: the machines agree about this program. The ⇒-move fence applies
-- on both machines, so the executing machine also refuses `let g = Ih`, for
-- the same reason and in the same words as checking.
example : (match Dllbc.Tests.S9Diff.runExec m1 with
   | .ok e => (e.lookup "x").map Val.pretty
   | .error _ => none) = none := by native_decide

-- Not vacuous: the SAME body without the `let g = ih` line checks, so the
-- rejection above is about reading `ih` as a value and not about the shape.
def m0 : Term := prog{
  let F = (natRec %mMot
                 (λ(v : &mut List Nat) { () })
                 (λ(n2 : Nat, Ih : Π (v : &mut List Nat) → Unit, v : &mut List Nat) {
                    match v { Nil => (), Cons(hd, tl) => { *hd := 0; Ih(tl); () } } }) : %mSeal);
  let x = Cons(1, Cons(2, Nil));
  let b = &m x;
  F(3, b);
  () }
example : progOk m0 = true := by native_decide
example : (match Dllbc.Tests.S9Diff.runExec m0 with
   | .ok e => (e.lookup "x").map Val.pretty
   | .error _ => none) = some "Cons Z (Cons Z Nil)" := by native_decide

end Dllbc.Tests.S26Rec
end

section
/-!
# The annotated runtime λ

`Term.lamR`'s binders carry their domains, matching the grammar's
`λ (x : τ). t`. What this section pins is the mechanical half of that:

  * the surface really carries a domain, and the VALUE really drops it (§A/§B);
  * the traversals that gained a case really traverse it (§C free variables,
    §D equality);
  * and `fnElab`'s arm annotations are the ones the kernel's own `checkArm`
    derives — §E, the one place here where a wrong answer would compile,
    pass, and be silently the wrong type.
-/

namespace Dllbc.Tests.S27Lam
open Dllbc

/-! §E and §F read a `Term` structurally, and that is not a leftover: they
    perturb the elaborated recursor's arm annotations, which no source can
    write — the whole point is that the annotations are derived rather than
    chosen. A `fn` statement lowers through `fnElab`, so the sealed recursor
    is read back out of the binding the statement made, and every assertion
    is still a verdict on a program. -/

/-! ## §A. The surface carries the domain -/

def annotated : Term := prog{ let G = λ(a : Nat) { a }; () }

example : (match annotated with
           | .seq (.letIn _ (.lam _ τ _)) _ => Term.beq τ (.const "Nat")
           | _ => false) = true := by native_decide

-- A capitalized binder's domain carries the comptime marker, which is what
-- makes the annotation agree with the ascription `piPeel` checks a mode
-- against.
def annotatedCmp : Term := prog{ let G = λ(A : Nat) { A }; () }
example : (match annotatedCmp with
           | .seq (.letIn _ (.lam _ τ _)) _ => Term.beq τ (.cmpT (.const "Nat"))
           | _ => false) = true := by native_decide

/-! ## §B. …and the VALUE drops the domain

    `readR` forms a `Val.rfn` with names only. The executing machine binds
    and runs and never converts, so there is nothing downstream of formation
    for a domain to be used by — the seal is the one consumer, and it holds
    the annotated TERM. -/

-- The type-level half, and it is the stronger of the two: this expression
-- typechecks exactly because `Val.rfn`'s binders are `Var` and not
-- `Var × Term`. A ledger that fails to compile is the one that cannot drift.
example : Val := .closure [] ty{ λ(a : Nat){ () } } none

-- The live half: an ANNOTATED λ evaluates to a value printed with names alone.
example : (match runProgram annotated with
           | .ok env => (env.lookup "G").map Val.pretty
           | .error _ => none) = some "λr(a){…}" := by native_decide

/-! ## §C. Free variables reach into the domains

    `Term.freeRVars` traverses the binder types, as a TELESCOPE — each domain
    under the binders to its left and none of its own. That is a real rule
    and not a tidiness: a domain names runtime slots (`Le (Len *v) fuel`
    names two), so leaving them untraversed would let a genuinely free
    variable into a type and straight past the closedness check the
    traversal exists to feed.

    Three programs, one per demand site, and the λ is FORMED in every one —
    an unformed λ is never asked. -/

-- C1. The domain captures a data binding: refused, by the same rule and the
-- same message a captured body reference gets. A λ's binder DOMAIN is part
-- of the node, so a runtime citation there is refused the same way as one
-- in the body — deliberately: a type consumed at its own event is exempt,
-- but a λ's domain is not consumed there, it is stored with the λ and read
-- whenever the λ is applied.
def capInType : Term := prog defer_check { let n = 3; let G = λ(a : Le n n) { () }; () }
example : progRejects capInType "a runtime (lowercase) binding" = true := by native_decide

-- C2. The isolating control: the same λ with a closed domain is accepted,
-- so C1 is about the reference and not about annotating a binder at all.
def closedType : Term := prog{ let n = 3; let G = λ(a : Le 3 3) { () }; () }
example : progOk closedType = true := by native_decide

-- C3. And the scoping is a TELESCOPE: a domain naming the λ's OWN earlier
-- binder is bound, not free. This is the shape every recursor arm has
-- (`ih`'s domain mentions the predecessor to its left), so getting it wrong
-- would reject the whole recursor story rather than a corner of it.
def telType : Term := prog{ let G = λ(m : Nat, a : Le m m) { () }; () }
example : progOk telType = true := by native_decide

/-! ## §D. Equality sees the domains -/

-- `Term.beq` compares them structurally.
example : Term.beq ty{ λ(a : Nat){ () } } ty{ λ(a : Bool){ () } } = false := by native_decide
example : Term.beq ty{ λ(a : Nat){ () } } ty{ λ(a : Nat){ () } } = true := by native_decide

/-! ## §E. `fnElab`'s arm annotations

    An arm is checked at the motive instantiated at its constructor, so its
    binders' domains are the residual telescope's with the scrutinee
    substituted. Two things follow, and the second is the one a naive
    transcription gets wrong:

      * `ih`'s domain is the motive at the PREDECESSOR — a term no source
        wrote;
      * and the trailing binders do NOT come through unchanged, because
        the scrutinee is abstracted over the whole nested Π, domains
        included. A parameter whose type mentions the decreasing one — a
        fuel bound `Le (Len *v) n` — is annotated `Le (Len *v) Z` in the base
        arm and `Le (Len *v) (S n')` in the step arm.

    The declaration below is that shape, minimal. The assertions compare
    against hand-written terms rather than against a second call of the
    derivation, so they would fail if the macro transcribed instead of
    substituting. -/

/-- The subject, as a program: the `fn` statement lowers through `fnElab`, so
    the sealed term this section reads is read back out of the binding the
    statement made. -/
def bndProgram : Term := prog{
  fn Bnd [n] (n : Nat, v : &mut List Nat, Hn : Le (Len *v) n) -> Unit {
    match n {
      Z => (),
      S(n2) => match v {
        Nil => (),
        Cons(hd, tl) => { Bnd(n2, &m *tl, Hn); () } } } };
  () }

/-- The sealed recursor the `fn` statement bound. -/
def bndSeal : Option Term :=
  match bndProgram with | .seq (.letIn _ t) _ => some t | _ => none

/-- The declaration's own domain for `Hn`, as the header writes it: `Le (Len *v) n`
    with the comptime marker, since `Hn` is capitalized. Written out because
    it is what a TRANSCRIPTION would have produced, and E2/F3b are the
    controls that say the elaboration produces something else. -/
def bndDeclHn : Term :=
  .cmpT prog defer_check { %(Std.LeFnT) (%(Std.lenFnT) %(Term.deref (.var ⟨1, "v"⟩))) %(Term.var ⟨0, "n"⟩) }

/-- The two arms of the emitted `natRec`, as annotated binder lists. -/
def bndArms : Option (List (Var × Term) × List (Var × Term)) :=
  match bndSeal with
  | some (.seal _ (.app (.app (.app (.const "natRec") _) zArm) sArm) _) =>
    some ((Term.peelLams zArm).1, (Term.peelLams sArm).1)
  | _ => none

-- The shape first — assert the instrument before the conclusion.
example : (match bndArms with
           | some (z, s) => z.length == 2 && s.length == 4
           | none => false) = true := by native_decide

/-- `Le (Len *v) b`, at the positional `v` the residual telescope keeps. -/
def leLen (b : Term) : Term :=
  prog{ %(Std.LeFnT) (%(Std.lenFnT) %(Term.deref (.var ⟨1, "v"⟩))) %b }

-- E1. The bound binder, at each constructor. `Hn` is capitalized, so its
-- domain carries the comptime marker — the annotation is the domain as
-- written, marker and all.
example : (match bndArms with
           | some (z, s) =>
             let dec := (s[0]!).1
             Term.beq (z[1]!).2 (.cmpT (leLen (.ctorApp "Z" [])))
               && Term.beq (s[3]!).2 (.cmpT (leLen (.ctorApp "S" [.var dec])))
           | none => false) = true := by native_decide

-- E2. …and neither is the DECLARATION's own domain, which is what a naive
-- transcription would have produced.
example : (match bndArms with
           | some (z, s) =>
             !(Term.beq (z[1]!).2 bndDeclHn) && !(Term.beq (s[3]!).2 bndDeclHn)
           | none => false) = true := by native_decide

-- E3. `ih` is the motive at the predecessor: peel it at the residual
-- telescope's own binders and its bound reads `Le (Len *v) n2`, one
-- successor BELOW the arm's own — a wrong-level `ih` is a type error (see
-- `S26Rec` §I), and this is the macro's half of the same fact: it is the one
-- that would compile and pass while being silently wrong.
example : (match bndArms with
           | some (_, s) =>
             let dec := (s[0]!).1
             match piPeel [⟨1, "v"⟩, ⟨2, "Hn"⟩] (s[1]!).2 with
             | .ok (tel, _) => tel.length == 2 && Term.beq (tel[1]!).2 (leLen (.var dec))
             | .error _ => false
           | none => false) = true := by native_decide

-- E4. The predecessor binder itself is the scrutinee's own domain.
example : (match bndArms with
           | some (_, s) => Term.beq (s[0]!).2 (.const "Nat")
           | none => false) = true := by native_decide

/-! ## §F. The annotation conversion: `piAgree`/`checkArm`

    Rather than trusting a λ's annotations and descending the ascription to
    fill them in, the checker compares the Π the λ STATES against the Π that
    was written (`piAgree`), and a recursor arm's leading binders — the
    predecessor and `ih` — are compared against what the recursor's premise
    gives them (`checkArm`).

    The second half is the one that matters: once an arm annotates `ih`, an
    annotation taken on trust would let a body state the recursion at its own
    level and be handed it — the same unsound self-call the base-case check
    in §H (S26Rec) rules out, arriving through annotations instead.

    Every assertion below perturbs exactly ONE annotation of a program that
    checks, so each is a per-demand-site control rather than a rejection that
    might have had some other cause. -/

/-- The elaborated declaration, as a program: a `let` of the sealed
    recursor. The binder is capital, matching what an elaborated
    declaration's binder is — this hand-built term stands in for what the
    `fn` row emits, so it has to agree with it. -/
def bndProg (t : Term) : Term := .seq (.letIn ⟨900, "F"⟩ t) .unit

/-- `bndProgram`'s sealed recursor with the step arm's `i`-th annotation replaced, and nothing else
    touched. `none` when the elaboration is not the shape this section reads. -/
def stepArmWith (i : Nat) (τ : Term) : Option Term :=
  match bndSeal with
  | some (.seal _ (.app (.app (.app (.const "natRec") mot) zArm) sArm) piT) =>
    let (s, sb) := Term.peelLams sArm
    some (.seal 0 (.app (.app (.app (.const "natRec") mot) zArm)
                  (Term.lamTel (s.set i ((s[i]!).1, τ)) sb)) piT)
  | _ => none

/-- The motive's body, read off the ascription the statement emitted, WITH the
    binder it is a body of: the seal's type is `Π (n : Nat) → R`, and every arm's
    type is an instance of that `R` at some constructor of `n`. -/
def bndR : Option (String × Term) :=
  match bndSeal with
  | some (.seal _ _ (.pi n _ R)) => some (n, R)
  | _ => none

/-- The step arm's predecessor binder. -/
def bndDec : Option Var := bndArms.map (fun p => (p.2[0]!).1)

-- F0. Baseline: unperturbed, the elaborated declaration checks — so every
-- rejection below is the perturbation and not the program.
example : progOk bndProgram = true := by native_decide

-- …and the instrument, before the conclusion: `R` really is the motive body,
-- because `ih`'s derived annotation is exactly `R` at the predecessor. That
-- re-derives §E3 from the ASCRIPTION instead of from the arm, an independent
-- route to the same fact.
example : (match bndR, bndArms, bndDec with
           | some (n, R), some (_, s), some dec =>
             Term.beq (s[1]!).2 (Term.substP n (.var dec) R)
           | _, _, _ => false) = true := by native_decide

-- F1. `ih` at the arm's own level: `R` at `S dec` where the premise gives `R`
-- at `dec`. This is the unsound self-recursion arriving as an annotation
-- instead of as a call, and it is refused by the arm-binder rule rather than
-- by anything downstream.
example : (match bndR, bndDec with
           | some (n, R), some dec =>
             match stepArmWith 1 (Term.substP n (.ctorApp "S" [.var dec]) R) with
             | some t => progRejects (bndProg t) "the recursor's premise does not give it"
             | none => false
           | _, _ => false) = true := by native_decide

-- F2. …and the predecessor binder is checked by the same rule.
example : (match stepArmWith 0 (.const "Bool") with
           | some t => progRejects (bndProg t) "the recursor's premise does not give it"
           | none => false) = true := by native_decide

-- F3. The plausible off-by-one: annotate the fuel bound at the PREDECESSOR's
-- level rather than the arm's own. Refused through `piAgree`, the other
-- branch of the check.
example : (match bndDec with
           | some dec =>
             match stepArmWith 3 (.cmpT (leLen (.var dec))) with
             | some t => progRejects (bndProg t) "a domain the ascription does not bind it at"
             | none => false
           | none => false) = true := by native_decide

-- F3b. The uninstantiated annotation: the arm annotated with the
-- DECLARATION's own domain, `Le (Len *v) n`, where the motive at this
-- constructor gives `Le (Len *v) (S n')`.
--
-- It is refused at the CONVERSION, and where it fires is part of the claim.
-- The declaration's domain mentions the scrutinee `n`, which does not exist
-- inside an arm — so a closedness rejection was the other plausible
-- outcome, and would have been the conversion passing for the wrong reason.
-- `piAgree` runs before the body is entered, so the domains are compared
-- first, and the message below is the comparison's own.
example : (match stepArmWith 3 bndDeclHn with
           | some t => progRejects (bndProg t) "a domain the ascription does not bind it at"
           | none => false) = true := by native_decide

-- F4. …and an ordinary trailing binder, mistyped outright.
example : (match stepArmWith 2
             (.borrowT "§_" (.app (.const "List") (.const "Bool"))
                       (.app (.const "List") (.const "Bool"))) with
           | some t => progRejects (bndProg t) "a domain the ascription does not bind it at"
           | none => false) = true := by native_decide

-- F5. The isolating control for the whole section: re-annotating a binder
-- with the type it already had leaves the program ACCEPTED. So F1–F4 are
-- about the disagreement, and not about the perturbation machinery having
-- touched the term.
example : (match bndArms with
           | some (_, s) =>
             match stepArmWith 3 (s[3]!).2 with
             | some t => progOk (bndProg t)
             | none => false
           | none => false) = true := by native_decide

/-! ### F6. A plain sealed λ, not a recursor — the `sealFn` half on its own -/

def fnTy : Term := prog defer_check { Π (v : &mut List Nat) → Unit }

def annOk : Term := prog{
  let F = (λ(v : &mut List Nat) { *v := Nil; () } : %fnTy);
  () }
example : progOk annOk = true := by native_decide

-- The same λ, the same ascription, one annotation changed: refused, since
-- the annotation is compared against the ascription rather than merely
-- carried along unread.
def annBad : Term := prog defer_check {
  let F = (λ(v : &mut List Bool) { *v := Nil; () } : %fnTy);
  () }
example : progRejects annBad "a domain the ascription does not bind it at" = true := by
  native_decide

/-! ## §G. Juxtaposition application

    The grammar has one application form, `t t′`; `f a b` has to mean a call
    when `f` names a runtime function, alongside meaning ordinary pure
    application when `f` is a pure λ.

    The surface cannot decide this: both a pure λ and a sealed runtime
    function live in the same kind of lowercase slot, and nothing about the
    two application spines differs syntactically — a pure λ must be applied
    by ⇝ (its arguments are snapshots and proofs that a ⇒ read would move),
    while a runtime function binds Ω slots under ⇒. So the choice is made by
    a kernel rule at `readR`'s `.app` case: a pure `.lam` substitutes; a
    `Val.rfn`, a σ with a signature, or a recursor spine binds. §G5 is the
    pair that makes the router observable — the same source line, two λ
    representations, two arrows, two verdicts. -/

def juxSealTy : Term := prog defer_check { Π (v : &mut List Nat) → Unit }

-- G1. A sealed function called by juxtaposition, in statement position.
def juxSeal : Term := prog{
  let F = (λ(v : &mut List Nat) { *v := Cons(9, Nil); () } : %juxSealTy);
  let x = Cons(1, Nil);
  let b = &m x;
  F b;
  let y = x;
  () }
example : progOk juxSeal = true := by native_decide
-- Acceptance alone is not the claim: `f b;` in statement position discards
-- its value, so an undetected non-call would still check and the
-- differential would still agree (both machines would simply stop calling
-- together). What discriminates is what the call LEAVES: the seal forgets
-- the payload, so after a real call the caller's `y` is an EXISTENTIAL,
-- where an uncalled program still holds the concrete list.
example : ((programEnvs juxSeal).filterMap (fun r => match r with
             | .ok e => (e.lookup "y").map (fun v => (v.pretty.take 1).toString)
             | .error _ => none)) = ["σ"] := by native_decide
-- …and both machines still correspond on it, which is the ordinary obligation.
example : Tests.S9Diff.progDiff juxSeal = true := by native_decide

-- …and the comma twin is the same program: same verdict, and both machines
-- agree on it, so juxtaposition changed how a call is WRITTEN and not what
-- it does.
def juxSealComma : Term := prog{
  let F = (λ(v : &mut List Nat) { *v := Cons(9, Nil); () } : %juxSealTy);
  let x = Cons(1, Nil);
  let b = &m x;
  F(b);
  let y = x;
  () }
example : progOk juxSealComma = true := by native_decide
example : (match runProgram juxSeal, runProgram juxSealComma with
           | .ok a, .ok b => a == b
           | _, _ => false) = true := by native_decide

-- G2. A recursor's `ih`, and the sealed recursor itself, both by juxtaposition —
-- `ih tl` inside the arm and `f 3 b` at the call. `ih` is the case with no comma
-- form to fall back on after δ, so it is the one that had to work.
def juxRecMot : Term := prog defer_check { λ (n : Nat). Π (v : &mut List Nat) → Unit }
def juxRecTy : Term := prog defer_check { Π (n : Nat) → Π (v : &mut List Nat) → Unit }
def juxRec : Term := prog{
  let F = (natRec %juxRecMot
                 (λ(v : &mut List Nat) { () })
                 (λ(n2 : Nat, Ih : Π (v : &mut List Nat) → Unit, v : &mut List Nat)
                    { match v { Nil => (), Cons(hd, tl) => { *hd := 0; Ih tl; () } } }) : %juxRecTy);
  let x = Cons(1, Cons(2, Nil));
  let b = &m x;
  F 3 b;
  let y = x;
  () }
example : progOk juxRec = true := by native_decide
-- The same discriminator: `ih tl` and `f 3 b` really call, so the checking-mode
-- `y` is the seal's existential rather than the list the program wrote.
example : ((programEnvs juxRec).filterMap (fun r => match r with
             | .ok e => (e.lookup "y").map (fun v => (v.pretty.take 1).toString)
             | .error _ => none)) = ["σ"] := by native_decide
example : Tests.S9Diff.progDiff juxRec = true := by native_decide
-- It really recursed: the executing machine zeroes both elements.
example : (match runProgram juxRec with
           | .ok env => (env.lookup "y").map Val.pretty
           | .error _ => none) = some "Cons Z (Cons Z Nil)" := by native_decide

-- G3. A transparent runtime λ, called by juxtaposition.
def juxLam : Term := prog{ let G = λ(a : Nat) { S(a) }; let r = G 1; r }
example : progOk juxLam ty{ Nat } = true := by native_decide

/-! ### G5. The router, made observable

    The same source line — `let y = mk (*v);` — under the two λ
    representations. A PURE λ is applied by ⇝, which reads the payload as a
    snapshot and leaves the borrow intact. A RUNTIME λ is applied by ⇒,
    which MOVES the payload out and leaves a hole, so the obligation audit
    refuses at return. -/

def juxPure : Term := prog{
  fn Caller (v : &mut List Nat) -> Unit
  { let Mk = (λ (L : List Nat). L);
    let y = Mk (*v);
    () };
  () }
example : progOk juxPure = true := by native_decide

def juxRuntime : Term := prog defer_check {
  fn Caller (v : &mut List Nat) -> Unit
  { let Mk = λ(l : List Nat) { l };
    let y = Mk (*v);
    () };
  () }
example : progRejects juxRuntime "holds a hole (⊥) at return" = true := by native_decide

-- G6. Saturation, at the juxtaposition form: the call event is atomic, so a
-- spine that stops short is an error and not a partial application.
def juxPartial : Term := prog defer_check {
  let F = (λ(a : Nat, b : Nat) { a } : Π (a : Nat) → Π (b : Nat) → Nat);
  let r = F 1;
  () }
-- The message is the call rule's own, not a parse failure: the spine
-- reached the callee and the callee's telescope is what refused it.
example : progRejects juxPartial "arity mismatch" = true := by native_decide

-- …and the saturated twin is accepted, so G6 is about the missing argument.
def juxSaturated : Term := prog{
  let F = (λ(a : Nat, b : Nat) { a } : Π (a : Nat) → Π (b : Nat) → Nat);
  let r = F 1 2;
  r }
example : progOk juxSaturated ty{ Nat } = true := by native_decide

-- G7. A RESERVED head stays a constructor, which is what keeps `S n` and a
-- call distinguishable without a token: the basis is closed, so the test is
-- exact.
example : (match (prog defer_check { let x = S 3; () } : Term) with
           | .seq (.letIn _ (.ctorApp "S" [_])) _ => true
           | _ => false) = true := by native_decide

-- G8. A CAPITAL head is never routed, in either position: a capital
-- function-typed binder is a SPEC parameter — cited, never called — so the
-- spine stays ⇝'s structured neutral.
def juxCapital : Term := prog{
  fn JuxCapital (G : Π (x : Nat) → Nat, n : Nat) -> Id Nat (G n) (G n) { Refl };
  () }
example : progOk juxCapital = true := by native_decide

/-! ## §H. `[k]` decides which recursor is emitted

    `[k]` is purely the scrutinee-selection hint: it decides which parameter
    `fnElab` recurses on and hence which recursor it emits, so two
    definitions differing only in `[k]` are two different terms — not two
    spellings of one function. The hint is load-bearing on the output: one
    checks and the other is refused. -/

/-- The `[m]` spelling: the hint names the parameter the body actually
    matches on, so `fnElab` has a scrutinee to build the recursor from and
    the self-call becomes `ih` at the predecessor. -/
def hintM : Term := prog{ fn H [m] (n : Nat, m : Nat) -> Id Nat Z Z
  { match m { Z => Refl, S(m2) => H(n, m2) } }; () }

/-- The `[n]` spelling: character for character the same function — same
    name, same telescope, same return type, same body — differing in the
    hint alone. -/
def hintN : Term := prog defer_check { fn H [n] (n : Nat, m : Nat) -> Id Nat Z Z
  { match m { Z => Refl, S(m2) => H(n, m2) } }; () }

example : progOk hintM = true := by native_decide
-- …and the twin is REFUSED, by the needle no other error produces.
example : progRejects hintN FnMacro.fnRefusedNeedle = true := by native_decide
-- …with the diagnosis intact, which is what makes this about `[k]` and not
-- about the body: the self-call's decreasing argument is not the
-- predecessor the `S` branch binds, because the branch that binds one is
-- `m`'s and the hint named `n`.
example : progRejects hintN "is not the predecessor" = true := by native_decide

end Dllbc.Tests.S27Lam
end

section
/-!
# The `fn` statement's own hazards

`fn` is a statement of the calculus's one grammar: a declaration is a `let`,
its right-hand side is a seal over a recursor or a runtime λ, and
`fn f (…) -> R { … } ; rest` is that `let` written where a `let` is written.

This section covers the two hazards that belong to the STATEMENT rather than
to any function written with it: composing chained `fn` declarations, and
the seal's one confusable neighbour in the surface grammar (`&mut`).
-/

open Dllbc

namespace Dllbc.Tests.FnStmt

/-! ## §A. Two `fn` chains composed through a `%` splice

    Sharing a prefix is ordinary let-chain composition — a Lean function
    taking the rest of the block and splicing it — and half the corpus is
    written that way. Nesting two chains resolves each name to its own
    declaration, by NAME rather than by numeric slot; what still shadows is
    a chain redeclaring an outer chain's NAME, which is lexical shadowing
    doing its job. -/

-- The two declarations have DIFFERENT ARITIES, which is what makes the
-- assertion below discriminating rather than merely green: if the two names
-- were ever confused, `A(1)` would reach a two-parameter callee and be an
-- arity error. An accept can only happen if each name reaches its OWN
-- declaration.
def withA (rest : Term) : Term := prog{ fn A (n : Nat) -> Nat { n }; %rest }
def withB (rest : Term) : Term := prog{ fn B (n : Nat, m : Nat) -> Nat { n }; %rest }

-- Nested: ACCEPTED.
example : progOk (withA (withB (prog defer_check { let r = A(1); let s = B(2, 3); () }))) = true := by
  native_decide

-- The shapes that were always fine, kept: one chain declaring both, and a
-- prefix whose tail declares nothing.
example : progOk (prog{
  fn A (n : Nat) -> Nat { n };
  fn B (n : Nat, m : Nat) -> Nat { n };
  let r = A(1); let s = B(2, 3); () }) = true := by native_decide
example : progOk (withA (prog defer_check { let r = A(1); () })) = true := by native_decide

/-! ## §B. The seal is ASCRIPTION, and its one confusable neighbour

    `seal(t, T)` is spelled `(t : T)`. An ascription closes at its own
    paren, so `(f : T) x` is the ascribed `f` APPLIED to `x`, not an
    ascription at a function type.

    The neighbour is `&mut`. `&mut (s : τ ~> τ')` is the borrow type with a
    snapshot binder; drop the `~> τ'` and the ascription row would take it,
    making `&mut (v : List Nat)` a borrow of a SEAL — which parsed silently
    and failed downstream as an unrelated unbound-identifier error before
    this was refused at elaboration instead. Not assertable as a test (it
    fails the build by design), so recorded here with its message:

        &mut (v : τ) is not a borrow type — the snapshot-binder spelling is
        `&mut (v : τ ~> τ')`, where `τ'` is what the borrow OWES back … If you meant
        a plain borrow of the type, write `&mut τ`.
-/

-- The two spellings the refusal is between, both still working.
example : progOk (prog{
  fn F (v : &mut (s : List Nat ~> List Nat)) -> Unit { *v := Nil; () };
  () }) = true := by native_decide
example : progOk (prog{
  fn F (v : &mut List Nat) -> Unit { *v := Nil; () };
  () }) = true := by native_decide

-- An ascription CLOSES at its own paren, so a following term is an application
-- argument rather than part of the ascribed type. Stated by splicing the
-- ascription in as an opaque head: if the paren did not close, the two would
-- differ.
def ascribed : Term := prog{ (λ (x : Nat). x : Π (x : Nat) → Nat) }
example : ((prog defer_check { let r = (λ (x : Nat). x : Π (x : Nat) → Nat) 3; () })
        == (prog defer_check { let r = %ascribed 3; () })) = true := by native_decide

/-! ## §C. `[k]` naming a non-parameter is a LEAN error

    The one refusal that is cheap syntactically is the one the surface makes
    syntactically — the macro has to resolve `[k]` to an index anyway, so it
    says so at elaboration. Everything else `fnElab` refuses is SEMANTIC (it
    needs the elaborated telescope type to see that `[v]` decreases through a
    borrow's payload, or that a scrutinee is neither `Nat` nor `List A`) and
    is deliberately not duplicated as a syntactic check: two implementations
    of one rule is one too many, and the copy would be the one that drifts.

    Not assertable as a test (it fails the build by design); recorded here
    so a reader knows which errors appear when. Writing
    `fn f [zzz] (n : Nat) -> Unit { () }` gives:

        fn: decreasing argument 'zzz' is not a parameter of 'f'
-/

end Dllbc.Tests.FnStmt
end

section
namespace Dllbc.Tests.FnAlias
/-!
# A comptime alias is citable from a `fn`'s TYPES

`let NatPair = Σ (l : Nat). Nat` is an ordinary capital binding holding a
type, and the citation rule does not distinguish what a citation is FOR: a
body may cite the capital bindings in scope, and a parameter's type or the
return type is read in that same scope — resolved at the surface, and
admitted into the seal's fresh Ω at the kernel, exactly as a body citation
is in both places.

A lowercase binding cited from a type is refused by `admitGlobals` with the
same message a body citation gets.
-/

/-- The motivating program: an alias declared in the block, cited by a
    parameter type, and the function called from the tail. -/
def paramAlias : Term := prog{
  let NatPair = Σ (l: Nat) . Nat;
  fn Fst(p: NatPair) -> Nat {
    match p {
      Pair(l, r) => l
    }
  };
  Fst(Pair(1, 2))
}

example : progOk paramAlias (prog defer_check { Nat }) = true := by native_decide
example : progRuns paramAlias = true := by native_decide

/-- The alias in RETURN-type position. -/
def retAlias : Term := prog{
  let NatPair = Σ (l: Nat) . Nat;
  fn Mk(x: Nat) -> NatPair { Pair(x, x) };
  ()
}

example : progOk retAlias = true := by native_decide
example : progRuns retAlias = true := by native_decide

/-- A LOWERCASE alias never gets as far as the citation rule: `Σ` is a ⇝
    form with no ⇒ reading, so the program dies at `let natPair = Σ …`,
    before the `fn` is ever looked at. -/
def lowerAlias : Term := prog defer_check {
  let natPair = Σ (l: Nat) . Nat;
  fn Fst(p: natPair) -> Nat { 1 };
  ()
}

example : progRejects lowerAlias "no ⇒ reading" = true := by native_decide

end Dllbc.Tests.FnAlias
end

section

open Dllbc

namespace Dllbc.Tests.S27Dispose

open Dllbc.Tests

/-! ### `recSame`, `recWrongIdx`, `recGrow` — negative controls for a deleted guard

    A self-call at the same argument, at a different one, and at a larger one.
    Their subject was a snapshot-subterm check that no longer exists, but each is
    still rejected for an independent reason: the recursor's `ih` is bound at the
    predecessor, so a self-call anywhere else has nothing to become, and the
    let-chain cannot reference downward, so the un-elaborated form resolves to no
    function at all. -/

def guardTwins : List Term := [S23Direct.recSame, S23Direct.recWrongIdx, S23Direct.recGrow]

example : guardTwins.all (fun t => progRejects t "not the predecessor") = true := by native_decide
-- Not vacuous: the honest sibling elaborates, so the three refusals are about the
-- argument and not about the shape.
example : progOk S23Direct.recGood = true := by native_decide

/-! ### `recDeep` — a macro limit, not a calculus limit

    `recDeep` recurses two constructors down: an arm's `ih` is bound at the
    *immediate* predecessor of the motive it is given, so reaching two steps back
    needs a motive that already carries both values. The macro derives only the
    motive that matches the function signature, so it cannot produce this one and
    declines the declaration — but a hand-written recursor with a stronger motive
    typechecks, which is what the rest of this section checks:

    1. **`recDeep`'s own motive is CONSTANT** (`Π (n : Nat) → Id Nat Z Z` — nothing
       depends on `n`), so `ih : P a` already IS `P b` for every `b`. The direct
       recursor expresses it verbatim, and that is what the program below checks.
    2. **The general two-down shape** — where `P` really does depend on `n` — has
       a described route and NOT a mechanized one, and the distinction is left
       standing rather than blurred: a course-of-values motive `Q m := P m × P (S m)`,
       whose base arm inhabits `P 0` and `P 1` directly and whose step arm at `a`
       with `ih : Q a` returns `Pair(snd ih, fst ih)` — `P (S a)` is `ih`'s second
       component and the two-down call `f a` is its first — then one projection at
       the end. One `natRec`, one stronger motive. Nothing below checks this; it is
       filed as the route, and only construction 1 is a build fact.

    So the limit is real but it is a **macro** limit, not a calculus one: `fnElab`
    derives the motive mechanically from the signature (§7: "the motive is derived
    from the signature — so the macro needs no inference"), and neither of these
    motives is that one. That is the same shape as §9's own survey warning — "the
    eliminator must accept a motive stronger than the signature, plus a weakening
    step" — arriving a second time, from the other end of the language, before §9
    is built. Filed as a macro capability rather than as an expressiveness wall. -/

def deepSealT : Term := prog defer_check { Π (n : Nat) → Id Nat Z Z }
def deepMotT : Term := prog defer_check { λ (n : Nat). Id Nat Z Z }

/-- `recDeep`, hand-written as a sealed recursor. The step arm keeps the corpus's
    own inner `match a`, reaching `ih` from inside it — the move the macro refuses
    to make on the author's behalf.

    The base arm must bind a unit binder rather than an empty telescope: an arm
    that is not a λ is not a suspension, so it would run when the spine is formed
    rather than when ι selects it. `deepBaseArmBare` below is the rejected twin
    that omits the binder. -/
def deepBaseArm : Term :=
  Term.lamTel [(unitBinder, .cmpT (.const "Unit"))] (.ctorApp "Refl" [])
def deepBaseArmBare : Term := Term.lamTel [] (.ctorApp "Refl" [])
def deepStepArm : Term :=
  -- `ih`'s domain is the motive at the predecessor; `deepMotT` is constant, so
  -- `ih : P a` already is `P b` for every `b`.
  Term.lamTel [(⟨0, "a"⟩, .const "Nat"), (⟨1, "ih"⟩, prog defer_check { Id Nat Z Z })]
    (.matchE ⟨0, "a"⟩ none
      [ .mk "Z" [] (.ctorApp "Refl" [])
      , .mk "S" [⟨2, "b"⟩] (.var ⟨1, "ih"⟩) ])
def deepRec : Term :=
  .app (.app (.app (.const "natRec") deepMotT) deepBaseArm) deepStepArm
def recDeepProg : Term := .seq (.letIn ⟨900, "F"⟩ (.seal 0 deepRec deepSealT)) .unit

example : progOk recDeepProg = true := by native_decide

/-- The same program with the base arm left bare is refused: the two differ in
    one binder, which is what makes the accept above about the arm's shape
    rather than about the program. -/
def recDeepBare : Term :=
  .seq (.letIn ⟨900, "F"⟩ (.seal 0
    (.app (.app (.app (.const "natRec") deepMotT) deepBaseArmBare) deepStepArm) deepSealT)) .unit
example : progRejects recDeepBare "is a bare term, not a λ" = true := by native_decide

/-- The seal really audits the recursor: ascribed at a Π claiming
    `Id Nat Z (S Z)` instead, the arms cannot inhabit it and this is rejected. -/
def deepSealLie : Term := prog defer_check { Π (n : Nat) → Id Nat Z (S Z) }
def recDeepLie : Term :=
  .seq (.letIn ⟨900, "F"⟩ (.seal 0 (.app (.app (.app (.const "natRec")
    (prog defer_check { λ (n : Nat). Id Nat Z (S Z) })) deepBaseArm) deepStepArm) deepSealLie)) .unit
example : progOk recDeepLie = false := by native_decide

/-- The macro itself still declines the declaration: the form is expressible, but
    `fnElab` does not derive this motive. -/
example : progRejects S23Direct.recDeep "not the predecessor" = true := by native_decide

end Dllbc.Tests.S27Dispose
end

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
# Functions — the seal, recursors as bodies, the runtime λ, and the `fn` statement's own hazards

**A consolidation bucket** (M28 D10). The suite grew one file per milestone, which
made a test's home a fact about WHEN it was written rather than about what it is
about. These files were merged here, in the order below, with their content moved
VERBATIM — every namespace kept, so every cross-file reference in the tree still
resolves, and each former file is fenced by a comment naming it so the git-log
archaeology survives:

  * `S26Seal.lean`
  * `S26Rec.lean`
  * `S27Lam.lean`
  * `FnStmt.lean`

Each former file's `open`s are scoped by a `section`, so nothing leaks across the
seams.
-/

-- ┌── was `Dllbc/Tests/S26Seal.lean` ──────────────────────────────────────────────
section
/-!
# §26 (M26-A) — the seal node, and application of a value callee

Phase A of the `fn`/λ unification (`docs/combining-fns.md`). Two forms enter the
kernel, and nothing leaves it: `FnDef`, `checkFn` and the declaration table are
fully alive (J1, build-alongside), and every rule below is additive.

## `.seal t u` — opacity as syntax (§5)

  * EXECUTING (⇒, concrete): evaluate `t`. Execution is always transparent.
  * CHECKING (⇒, symbolic): verify `t : u` once at the node — this check *is* the
    audit — then yield a fresh `σ : u`. Downstream sees only the type.

**Scope of this phase (J4).** `u` ranges over pure types and borrow-free Πs.
Borrow-moded `u` is §5.4's audit relocated to the node — exit snapshots, `old *v`,
obligations — and is phase M26-C; it is REJECTED here, by a message that names the
phase, with the rejection pinned by a test rather than left to be discovered.

**Why the node can never be a comptime form.** Not a flag consulted at runtime —
two structural facts. (i) `.seal` is its own `Term` constructor, not an `.app` of
a magic `.const` (the route `@exit` and `old` take), so ⇝'s application rule
cannot see it and no test inside that rule distinguishes it. (ii) `Val` has no
seal former, so no comptime RULE for the seal exists: `eval`, `whnfN`, `nfV`,
`convert` and `hasType` are functions on `Val` and would need a new value
constructor before one could be written. §2.1's question — what does a seal
reduced twice under ⇝ mean — is therefore not answered conservatively, it is
unaskable.

## `x(a, …)` — application of a value callee (§7 cost 2)

The callee is a slot, not a table entry, and the slot's contents pick the rule:
a literal λ is bound-and-run (β, both machines); a `σ : Π` is applied abstractly,
minting the result from the instantiated codomain (checking only). Saturated
(§12 decision 4): under-application is rejected, never curried. Surface: the head
of `f(…)` is a value callee exactly when it names a bound runtime variable, and
falls through to the declaration table otherwise — one application form, resolved
by scope, which is §8's direction arriving where phase A already needs it.

This is the mechanism phase C's `ih` stands on, and §C below exercises it in the
`ih` shape already: a Π-typed telescope parameter, applied inside a body.
-/

open Dllbc
open Dllbc.StdLemmas (LeRefl LeTrans)

namespace Dllbc.Tests.S26Seal

/-! ## Helpers — there are none left, and that is the point (M28 ν)

    This section used to define `ok`, `rejects` and `caller`: a subject was a
    `FnDef`, so a body had to be wrapped in a nullary declaration before anything
    could be asked of it, and the two verdicts needed a harness to route the
    wrapper through the program path. `fn` is a statement now, so a body IS a
    program — `progOk`/`progRejects` from `Dllbc/Program.lean` take it directly,
    and the wrapper has nothing left to do.

    What survives from the old helpers' docstrings, because it is a fact about the
    kernel and not about the harness: a rejection is asserted on the MESSAGE and
    never on a Bool. `hasType` returns `false` for "does not have this type" and
    the seal turns that into an error, so a helper collapsing error and false would
    let a *stuckness* pass for a *typing* rejection. `progRejects` is written that
    way for that reason. -/

/-! ## §A. The seal under ⇒-checking -/

-- A1. A well-typed sealed λ is accepted, and the binding holds a σ afterwards.
def a1 : Term := prog{ let F = (λ (x : Nat). x : Π (x : Nat) → Nat); () }
example : progOk a1 = true := by native_decide

-- A2. An ill-typed one is rejected, by an honest TYPING rejection naming both the
-- term and the ascribed type — not by getting stuck somewhere downstream.
def a2 : Term := prog{ let F = (λ (x : Nat). x : Π (x : Nat) → Bool); () }
example : progRejects a2 "does not have its ascribed type" = true := by native_decide

-- A3. Data seals: the same rule with no Π in sight.
def a3ok : Term := prog{ let a = (3 : Nat); () }
def a3no : Term := prog{ let a = (3 : Bool); () }
example : progOk a3ok = true := by native_decide
example : progRejects a3no "does not have its ascribed type" = true := by native_decide

-- A4. Phase A's stub, RETIRED BY M26-C, which is what it named. A borrow-moded
-- `u` is a function signature, and §5.4's audit is what checks a function against
-- one — so the sealed term has to be a runtime λ whose binders match it. Sealing a
-- PURE λ there is still refused, and now for the reason rather than for the phase:
-- `hasType` has no answer to a payload-owing Π, and pretending otherwise is the
-- one thing this rule must not do.
def a4 : Term := prog{ let F = (λ (x : Nat). x : &mut Nat); () }
example : progRejects a4 "the sealed term must be a runtime λ" = true := by native_decide

/-! ### A5. ⇝ never meets the node

    The rejection is a *grammar* fact, not a mode check: `readC` lists `.seal`
    beside `&mut`, `:=`, `;` and `f(…)`, and that list is this calculus's
    definition of the comptime sub-grammar (§1.3). -/

def readCOn (t : Term) : String :=
  match (readC 1000 t).run (seedPure [] []) with
  | .ok v _ => "ACCEPTED " ++ v.pretty
  | .error e _ => e

example : strContains (readCOn (.seal (.ctorApp "Z" []) (.const "Nat")))
  "not in the comptime fragment" = true := by native_decide
-- …including buried inside a pure former, which is the position that would pose
-- §2.1's identity question if ⇝ could reduce it.
example : strContains (readCOn (.app (.const "S") (.seal (.ctorApp "Z" []) (.const "Nat"))))
  "not in the comptime fragment" = true := by native_decide

/-! ### A6. "Legal anywhere ⇒ evaluates" (§5), exercised at the positions that
    are not a `let` right-hand side

    §5 makes a point of this — "every ⇒-evaluation is an event, so minting is
    coherent even for a seal passed directly as a call argument" — so the claim is
    tested rather than inferred from the rule's placement in `readR`. -/

def natIdT : Term := prog{ Π (x : Nat) → Nat }

-- as a call argument, where the mint happens inside `processArgs`
def a6a : Term := prog{
  fn TakesFn (g : %natIdT) -> Unit { () };
  TakesFn((λ (x : Nat). x : Π (x : Nat) → Nat)); () }
example : progOk a6a = true := by native_decide

-- inside a constructor argument
def a6b : Term := prog{ let l = Cons((3 : Nat), Nil); () }
example : progOk a6b = true := by native_decide

-- in return position: a function whose result IS a sealed function. The audit
-- reads the σ's type out of `sctx` and converts — O(statement), the §5 point 2
-- shape at a boundary rather than at a citation.
def a6c : Term := prog{
  fn MkId () -> %natIdT { (λ (x : Nat). x : Π (x : Nat) → Nat) };
  () }
example : progOk a6c = true := by native_decide
-- …and the same in return position with the wrong ascription is caught at the
-- node, before the return type is ever consulted.
def a6d : Term := prog{
  fn MkId () -> %natIdT { (λ (x : Nat). x : Π (x : Nat) → Bool) };
  () }
example : progRejects a6d "does not have its ascribed type" = true := by native_decide

/-! ### A7. A limitation, pinned rather than left to be met

    A seal's body is ⇒-evaluated to ONE value, so a body that splits on a symbolic
    scrutinee has no seal meaning in phase A: `pushContinuations` leaves the node
    alone (it is not a statement form) and the expression-position match is
    refused with the machine's standing message. This is not a gap to be patched
    here — a sealed body that branches is a *function* body, whose audit is §5.4's
    and whose relocation is phase M26-C. Pinned so the phase-C agent meets a test
    rather than a surprise. -/

def a7 : Term := prog{
  fn A7 (n : Nat) -> Unit { let f = (match n { Z => Z, S(k) => k } : Nat); () };
  () }
example : progRejects a7 "only a statement-position match may split" = true := by native_decide

/-! ## §B. The intersection smell test (`combining-fns` §12, open question 4)

    §4 predicts that the audit of a borrow-free sealed λ must degenerate to
    **exactly** `hasType` — same acceptances, same rejections, no premise of its
    own. That is a claim about the design being real rather than notational, so it
    is discharged here as an *identity over a battery*, not as a spot check: for
    every pair below, sealing at `u` accepts precisely when the pure fragment's own
    `readC`-then-`hasType` accepts.

    The rule earns this by construction — it reads the type with `readC`, the term
    with `readR` (which on a pure former IS `readC`, via the §1.3 lift), and calls
    `hasType` on the two — but "by construction" is what the battery checks rather
    than assumes, and the battery carries both polarities so the identity cannot
    hold vacuously. -/

/-- The pure fragment's own check (S23Direct's `chk`, verbatim). -/
def chk (tm ty : Term) : Bool :=
  match (do let v ← readC 3000 tm; let t ← readC 3000 ty; hasTypeT 3000 v t).run (seedPure [] []) with
  | .ok r _ => r
  | .error _ _ => false

/-- Does sealing `tm` at `ty` pass the checker? The subject is a one-`let`
    PROGRAM now; it used to be that `let` wrapped in a nullary declaration. -/
def sealChk (tm ty : Term) : Bool :=
  progOk (.letIn ⟨0, "f"⟩ (.seal tm ty) .unit)

def natT : Term := .const "Nat"
def listNatT : Term := .app (.const "List") natT
def n3 : Term := .ctorApp "S" [.ctorApp "S" [.ctorApp "S" [.ctorApp "Z" []]]]
def n4 : Term := .ctorApp "S" [n3]

/-- The battery: λ's at Π's (the case §4 is about), data at its type, proofs at
    their statements, and a wrong-type mate for each shape. -/
def battery : List (Term × Term) :=
  [ (prog{ λ (x : Nat). x },            prog{ Π (x : Nat) → Nat })
  , (prog{ λ (x : Nat). x },            prog{ Π (x : Nat) → Bool })          -- ✗
  , (prog{ λ (x : Nat). S x },          prog{ Π (x : Nat) → Nat })
  , (prog{ λ (x : Nat). λ (y : Nat). x }, prog{ Π (x : Nat) → Π (y : Nat) → Nat })
  , (prog{ λ (x : Nat). λ (y : Nat). x }, prog{ Π (x : Nat) → Nat })         -- ✗
  , (n3, natT)
  , (n3, .const "Bool")                                                       -- ✗
  , (.ctorApp "Nil" [], listNatT)
  , (.ctorApp "Cons" [n3, .ctorApp "Nil" []], listNatT)
  , (.ctorApp "Refl" [], .idT natT n3 n3)
  , (.ctorApp "Refl" [], .idT natT n3 n4)                                     -- ✗
  , (StdLemmas.LeRefl, StdLemmas.LeReflTy)
  , (StdLemmas.LeRefl, StdLemmas.IdSymTy)                                  -- ✗
  , (StdLemmas.IdSym, StdLemmas.IdSymTy)
  , (StdLemmas.AddZero, StdLemmas.AddZeroTy)
  -- The §2.1 flagship: congruence, whose whole content is that an abstract
  -- function's applications are one term. Sealing it must cost exactly what
  -- checking it costs.
  , (StdLemmas.IdCongr, StdLemmas.IdCongrTy) ]

/-- THE SMELL TEST: the seal's audit and the pure fragment's `hasType` agree,
    pair for pair. -/
example : battery.all (fun p => sealChk p.1 p.2 == chk p.1 p.2) = true := by native_decide

-- …and the battery is not vacuous: both verdicts occur, so the identity above is
-- pinning agreement rather than a constant function. (Liveness by flipping the
-- assertion: were the seal to demand anything extra, the ✗-marked rows would
-- still agree — it is the accepting rows that would break, and they are the
-- majority here on purpose.)
example : (battery.any (fun p => chk p.1 p.2)
        && battery.any (fun p => !chk p.1 p.2)) = true := by native_decide
-- The harness itself is live: a deliberately wrong pairing disagrees with the
-- seal only if the seal is doing something other than `hasType` — it does not.
example : sealChk (StdLemmas.LeRefl) (StdLemmas.IdSymTy) = false := by native_decide

/-! ## §C. Application of a value callee

    §2's two rows, chosen by what the slot holds. A negative control per rule
    branch, per §6.2's lesson that a rule branch nobody probes is a rule branch
    nobody checked. -/

-- The λ as it SITS IN Ω, which is readback output: the binder the source wrote
-- `x` is canonicalized to its level (M30 step 2), the same renaming that makes two
-- α-variant functions compare equal. The slot holds the same function it always
-- held; what moved is how a normal form spells a binder.
def vlam : Val := .know (.lam "§0" (.const "Nat") (.ctorApp "S" [.pvar "§0"]))

-- C1. **Body known ⟹ unfold.** A literal λ callee β-reduces, so the caller knows
-- the result exactly: `y ↦ 3`, not an existential.
def c1 : Term := prog{ let f = λ (x : Nat). S x; let y = f(2); () }
example : progOk c1 = true := by native_decide
example : tailEnv c1 [("f", vlam), ("y", Val.nat 3)] = true := by native_decide

-- C2. **Body withheld ⟹ the type's promise and nothing more.** Seal the same λ
-- and the same call yields an opaque σ. This is §5 point 4 made mechanical: what
-- the caller keeps is exactly what was written in the seal.
def c2 : Term := prog{ let F = (λ (x : Nat). S x : Π (x : Nat) → Nat); let y = F(2); () }
example : progOk c2 = true := by native_decide
example : tailEnv c2 [("F", .sym 0), ("y", .sym 1)] = true := by native_decide

-- C3. Two calls are two events, and are NOT identified (§2.2's requirement on the
-- runtime column): σ1 and σ2 are distinct, each with its own type instance.
def c3 : Term := prog{
  let F = (λ (x : Nat). S x : Π (x : Nat) → Nat); let y = F(2); let z = F(2); () }
example : tailEnv c3 [("F", .sym 0), ("y", .sym 1), ("z", .sym 2)] = true := by native_decide

/-! ### C4–C8. The negative controls, one per rule branch -/

-- Partial application: refused, not curried (§12 decision 4).
def c4 : Term := prog{ let f = λ (x : Nat). λ (y : Nat). x; let z = f(2); () }
example : progRejects c4 "partial application" = true := by native_decide
-- …and the same refusal on the abstract side, which is the branch that matters
-- for phase C (a σ : Π under-applied is a closure holding its arguments).
def c5 : Term := prog{
  let F = (λ (x : Nat). λ (y : Nat). x : Π (x : Nat) → Π (y : Nat) → Nat);
  let z = F(2); () }
example : progRejects c5 "partial application" = true := by native_decide

-- Over-application.
def c6 : Term := prog{ let f = λ (x : Nat). x; let z = f(2, 3); () }
example : progRejects c6 "too many arguments" = true := by native_decide

-- A mistyped argument, on both branches.
def c7 : Term := prog{ let f = λ (x : Nat). x; let z = f(Nil); () }
example : progRejects c7 "does not have its parameter type" = true := by native_decide
def c8 : Term := prog{ let F = (λ (x : Nat). x : Π (x : Nat) → Nat); let z = F(Nil); () }
example : progRejects c8 "does not have its parameter type" = true := by native_decide

-- A callee that is not a function at all, and one that was moved away.
def c9 : Term := prog{ let f = 3; let z = f(2); () }
example : progRejects c9 "is not a function value" = true := by native_decide
def c10 : Term := prog{ let f = Cons(1, Nil); let g = f; let z = f(2); () }
example : progRejects c10 "holds ⊥" = true := by native_decide

-- The demand-collapse premise (§5.2, "every demand collapses first") fires at the
-- callee slot too. `x` holds a loan marker; the call ENDS it and retries, so the
-- rejection names what the slot really holds — a Nat — rather than the marker.
-- Listing the site is the point: every unlisted demand site in this calculus has
-- so far been a bug waiting for its first program.
def c11 : Term := prog{ let x = 3; let b = &m x; let z = x(2); () }
example : progRejects c11 "is not a function value" = true := by native_decide

/-! ### C12. The `ih` shape

    A Π-typed TELESCOPE PARAMETER, applied inside a body. Checking-side this is a
    `σ : Π` — "the sealed view", which is exactly what phase C's `ih` will be — and
    the call is abstract application at that Π. Executing-side the parameter holds
    the caller's actual λ and the same syntax β-reduces. One form, two rules, no
    branch in the program. -/

def apply1 : Term := prog{
  fn Apply1 (g : Π (x : Nat) → Nat, n : Nat) -> Nat { g(n) };
  () }
example : progOk apply1 = true := by native_decide

-- The caller supplies a literal λ; checking mode learns only `Nat` about the
-- result (the call is opaque), which is §5.3's promise, unchanged by the callee
-- being applied through a variable inside.
def c12 : Term := prog{
  fn Apply1 (g : Π (x : Nat) → Nat, n : Nat) -> Nat { g(n) };
  let f = λ (x : Nat). S x; let r = Apply1(f, 2); () }
example : progOk c12 = true := by native_decide
-- `tailEnv` drops the program's own function binding, so the expected Ω is the
-- one this assertion always had — `r ↦ σ0` and not `σ1`.
example : tailEnv c12 [("f", vlam), ("r", .sym 0)] = true := by native_decide

-- The negative control for the parameter branch: a body that under-applies its
-- Π-typed parameter is rejected at the callee's own check, not at a caller's.
def apply1bad : Term := prog{
  fn Apply1bad (g : Π (x : Nat) → Π (y : Nat) → Nat, n : Nat) -> Nat { g(n) };
  () }
example : progRejects apply1bad "partial application" = true := by native_decide

/-! ### C13. Transparent vs sealed, as a TYPING difference

    C1/C2 pin the forgetting in the environment (`y ↦ 3` against `y ↦ σ`). Here it
    is where it actually bites — the same program twice, differing only in whether
    the callee is sealed, accepted once and rejected once. `needsEq`'s telescope is
    dependent, so the second parameter's type is instantiated at what the checker
    knows about the first; transparent, that is `Id Nat 3 3` and `Refl` inhabits
    it; sealed, it is `Id Nat σ 3` and `Refl` does not.

    This is §5 point 4 with nothing left to interpret: seal the successor function
    at `Π (x : Nat) → Nat` and callers know nothing about results — sound, honest,
    and (here) useless. Keeping knowledge across a seal means ascribing a richer
    type, which is the whole ensures discipline arriving as a consequence of the
    syntax rather than as a convention. -/

def c13t : Term := prog{
  fn NeedsEq (n : Nat, h : Id Nat n 3) -> Unit { () };
  let f = λ (x : Nat). S x; let y = f(2); NeedsEq(y, Refl); () }
def c13s : Term := prog{
  fn NeedsEq (n : Nat, h : Id Nat n 3) -> Unit { () };
  let F = (λ (x : Nat). S x : Π (x : Nat) → Nat); let y = F(2); NeedsEq(y, Refl); () }
example : progOk c13t = true := by native_decide
example : progRejects c13s "does not have its parameter type" = true := by native_decide

/-! ### C14. A caller can take apart what an abstract call returned

    The fact phase C stands on, established here rather than assumed there: when a
    `σ : Π` call mints its result from a Σ-shaped codomain, the caller can
    `sigmaRec` it and compose the conjuncts with ordinary lemmas. Without this,
    "the callee's postcondition is the caller's only knowledge" would be a
    knowledge the caller cannot use — which is exactly the gap M23's stage (i)
    closed for declared `fn`s, now confirmed to carry over to value callees.

    Phase A mints ONE σ at the whole instantiated codomain rather than
    componentwise (`buildResult`'s job for borrow-moded Πs). That is enough to be
    projectable, which is what this pins; phase C will want the componentwise mint
    for the re-minted borrow payloads, and this test says the coarse version is
    already usable. -/

def sigLemTy : Term := prog{ Π (x : Nat) → Σ (h : Le x x) → Le x x }
def sigLem : Term := prog{ λ (x : Nat). Pair (LeRefl x) (LeRefl x) }

def c14 : Term := prog{
  let f = (%sigLem : %sigLemTy);
  let p = f(2);
  elim p return (λ (w : Σ (h : Le 2 2) → Le 2 2). Le 2 2) { Pair (a) (b) => LeTrans 2 2 2 a b } }
-- The program's RESULT is the projection, so its return type is what the audit
-- checks it at — stated as `progOk`'s second argument, where the old form stated
-- it as the wrapper declaration's `-> Le 2 2`.
example : progOk c14 (prog{ Le 2 2 }) = true := by native_decide

-- The negative control has to be demanded to be a control: a `let`-bound proof is
-- never typed until something asks for its type (readC computes, it does not
-- check), so the wrong projection is only caught when the AUDIT wants it. Stated
-- because the vacuous version of this test passed, and would have looked fine.
def c14bad : Term := prog{
  let f = (%sigLem : %sigLemTy);
  let p = f(2);
  elim p return (λ (w : Σ (h : Le 2 2) → Le 2 2). Le 3 2) { Pair (a) (b) => a } }
example : progRejects c14bad "does not have return type" (prog{ Le 3 2 }) = true := by native_decide

/-! ## §D. The executing machine, and a NEW simulation-relation case

    Constraint 6 of `combining-fns` §10 names this obligation in advance rather
    than leaving it to be discovered: because `.seal` is legal anywhere ⇒
    evaluates, a checking-mode σ can now face a concrete value **mid-expression**,
    not only at a call boundary or a group release. The prediction was that this is
    a new case for the simulation relation. It is, and here is the counterexample
    that shows it — found by running S9Diff's relation, not by reasoning about it.

    **What breaks.** S9Diff's `matchVal` is a first-order structural matcher: it
    binds a bare `sym σ` to whatever concrete value sits opposite, and compares
    everything else structurally. That suffices while every σ stands at a whole
    slot, which is where calls and group-ends put them. A seal puts a σ *inside
    ordinary arithmetic*: after `let a = (3 : Nat); let b = Add a 1` the
    symbolic side holds the neutral spine `natRec … σ0` where the concrete side
    holds `4`. Structurally these differ, and the old relation reports a
    counterexample that is not one.

    **The extension.** Two passes. Collect σ ↦ concrete bindings from the positions
    where the symbolic side IS a σ; then instantiate the whole symbolic
    environment and normalize, and compare. Consistency is enforced by the second
    pass (a σ bound twice to different values fails there), so the first pass needs
    no failure mode at all. This is the same relation S9Diff states — "the concrete
    env is a σ-instance of the symbolic one" — with *instance* read up to the pure
    fragment's own computation instead of up to structure.

    **MERGED into `S9Diff` by M26-C.** This section originally carried its own copy
    of the two passes, alongside a note that it and `matchVal` were incomparable —
    one computed and had no array-segment case, the other had segments and did not
    compute. `S9Diff.instanceOfC` is the single relation with both, and the names
    below are now `open`ed from there rather than defined here. The section is kept
    because the counterexample it found (D1) is what motivated the extension, and it
    still discriminates. -/

open Dllbc.Tests.S9Diff (runExec symEnvs instanceOf instanceOfC diffC)

/-- The M26-A name, retained so this section reads as written. -/
abbrev instanceOfComputed := Dllbc.Tests.S9Diff.instanceOfC

/-- The differential, under S9Diff's relation — kept so the gap is exhibited, not
    asserted. -/
def diffOld (body : Term) : Bool :=
  match runExec body with
  | .error _ => false
  | .ok ce => (symEnvs body).any
      (fun r => match r with | .ok se => instanceOf se ce | .error _ => false)

/-! ### D1. The counterexample that names the new case -/

def d1 : Term := prog{ let a = (3 : Nat); let b = Add a 1; () }
example : progOk d1 = true := by native_decide
-- The old relation calls this a counterexample. It is not one: the two
-- environments agree at σ0 := 3.
example : diffOld d1 = false := by native_decide
example : diffC   d1 = true  := by native_decide

/-! ### D2. The four shapes constraint 6 asks for, all GREEN -/

/-- A callee whose result the checker knows only as a σ — so the seal below sits
    at a SYMBOLIC value, not a concrete one.

    **IT TAKES AN ARGUMENT IT DOES NOT USE, and the EXECUTING machine is why.**
    This section runs each shape concretely, and a NULLARY `fn` lowers to a runtime
    λ binding nothing — which `λr` refuses, because a thunk makes ι ambiguous. So a
    program that declares a nullary function checks (the seal mints a σ without ever
    entering the λ) and cannot be RUN, and D2b's concrete side would fail before the
    relation was consulted. It rode in the `table` parameter as a `FnDef` for exactly
    that reason until M28 D5, when `decl{ }` retired and there was no `FnDef` to put
    there — and the parameter itself went in D9. Giving it a parameter is the smaller change and costs the section
    nothing: what D2b needs is a callee whose result the checker knows ONLY as a σ,
    and a call's result is minted fresh at any arity.

    The nullary wall itself is unchanged and is recorded here rather than asserted,
    because it fails at RUN time by design and a test of it would be a test of `λr`
    refusing a thunk. `apply1` below has arity two and never needed the treatment,
    which is how the difference was located. -/
def giveThree : Term := prog{ fn GiveThree (u : Nat) -> Nat { 3 }; () }

-- seal at a concrete value
def d2a : Term := prog{ let a = (3 : Nat); let b = a; () }
-- seal at a symbolic value (the body reads a call's fresh existential)
def d2b : Term := prog{
  fn GiveThree (u : Nat) -> Nat { 3 };
  let n = GiveThree(0); let a = (Add n 1 : Nat); let b = Add n 1; () }
-- a sealed function callee, passed and called
def d2c : Term := prog{
  let F = (λ (x : Nat). S x : Π (x : Nat) → Nat); let y = F(2); let z = F(5); () }
-- a transparent function callee, passed to a declared fn and called inside it
def d2d : Term := prog{
  fn Apply1 (g : Π (x : Nat) → Nat, n : Nat) -> Nat { g(n) };
  let f = λ (x : Nat). S x; let r = Apply1(f, 2); let s = f(7); () }

-- A shape is the whole program now — no table beside it, because there is no
-- table (M28 D9).
def shapes : List Term := [d2a, d2b, d2c, d2d]

example : shapes.all (fun t => progOk t (.const "Unit")) = true := by native_decide
example : shapes.all diffC = true := by native_decide

/-! ### D3. Harness liveness — the relation must be able to say NO

    A counterexample-finder that has never found its counterexample is
    unvalidated (S9Diff's own standing rule). The extended relation is checked
    against a concrete run that genuinely disagrees: same symbolic side, a
    concrete side that adds 2 where the checker's σ-instance adds 1. -/

def d3mutant : Term := prog{ let a = 3; let b = Add a 2; () }

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

/-! ## §E. `Qed` — the payoff, measured

    §5's second claim: `let cert = seal ⟨enormous proof⟩ ⟨statement⟩` mints one σ
    at the statement, and every citation afterwards is a σ-reference that `hasType`
    answers by reading the statement, never descending the proof. The measured
    certificate costs — "a reject costs the same as an accept", the audit descents
    — become O(statement).

    The subject is `CountSwapA`, the largest proof in `StdLemmas` (9156 term nodes
    against a 400-node statement). `useIt`'s parameter type IS the statement, so
    each citation forces `processArgs`' `hasType` on whatever the slot holds: the
    whole proof value when the certificate is transparent, a σ when it is sealed.

    Measured on this machine, compiled (`lake build` of this module, ms):

        the pure fragment's own check of the proof     6
        citations k                    1     8    32    128
        transparent                    6    34   130    515
        SEALED                         6     6     9     17

    Two readings, and the second is the one that matters. **The seal's audit costs
    exactly the ordinary check**: its intercept is 6 ms, which is `chk`'s 6 ms —
    sealing is not a tax, §12-open-4 again in milliseconds rather than in
    acceptances. **Every citation after it is flat**: 4.01 ms each transparent
    against 0.087 ms each sealed (least squares over the four points), a factor of
    46 that grows with the proof, because the sealed cost is a function of the
    400-node statement while the transparent one is a function of the 9156-node
    proof. That is §5's "the audit descents become O(statement)", as a slope.

    (The same sweep run through `lake env lean` on a scratch file reads ~34×
    larger throughout — the interpreter tax this project has measured before. The
    ratio is unaffected; the numbers above are the compiled ones.) -/

def big : Term := StdLemmas.CountSwapA
def bigTy : Term := StdLemmas.CountSwapATy

/-- `let c = rhs ; useIt(c) ; … ; ()` with `k` citations. Built rather than
    written out so the citation count can be swept: the claim is about the SLOPE,
    and one hand-written pair would only show a point. -/
def citeK (k : Nat) (rhs : Term) : Term :=
  let c : Var := ⟨0, "c"⟩
  let rec go : Nat → Term
    | 0 => .unit
    | n + 1 => .seq (.call "UseIt" [.var c]) (go n)
  .letIn c rhs (go k)

/-- The citations, with their callee declared above them. The built tail is
    spliced with `%`, and the `.call "UseIt"` nodes inside it are retargeted onto
    the slot by `bindFn` — which is the same mechanism a hand-written call goes
    through, so a swept program and a written one mean the same thing. -/
def citeProg (k : Nat) (rhs : Term) : Term := prog{
  fn UseIt (h : %bigTy) -> Unit { () };
  %(citeK k rhs) }

def unsealedK (k : Nat) : Term := citeProg k big
def sealedK (k : Nat) : Term := citeProg k (.seal big bigTy)

def unsealed1 : Term := unsealedK 1
def sealed1 : Term := sealedK 1
def unsealed4 : Term := unsealedK 4
def sealed4 : Term := sealedK 4

-- Both check, and check the same thing: the sealed citation is not cheaper by
-- being weaker. (`useIt`'s parameter type is the statement either way, so an
-- unsound σ would be caught here, not saved.)
example : progOk unsealed4 = true := by native_decide
example : progOk sealed4 = true := by native_decide

-- Negative control: sealing does not launder a WRONG proof past the citation. A
-- certificate sealed at a statement it does not inhabit is rejected at the node.
def sealedWrong : Term := prog{
  fn UseIt (h : %bigTy) -> Unit { () };
  let c = (%StdLemmas.LeRefl : %bigTy); UseIt(c); () }
example : progRejects sealedWrong "does not have its ascribed type" = true := by
  native_decide

/-- Re-measure on demand (`lake build` prints it): the numbers in the §E header. -/
def timeIt (label : String) (f : Unit → String) : IO Unit := do
  let t0 ← IO.monoMsNow
  let r := f ()
  let _ ← IO.mkRef r.length                       -- force before reading the clock
  let t1 ← IO.monoMsNow
  IO.println s!"{label}: {r} [{t1 - t0} ms]"

def verdict (t : Term) : String :=
  match checkProgram t with | .ok _ => "OK" | .error e => "ERR: " ++ e

#eval do
  timeIt "S26 Qed  pure-fragment check of the proof" (fun _ => toString (chk big bigTy))
  for k in [1, 8, 32, 128] do
    timeIt s!"S26 Qed  transparent x{k}" (fun _ => verdict (unsealedK k))
    timeIt s!"S26 Qed  SEALED      x{k}" (fun _ => verdict (sealedK k))

end Dllbc.Tests.S26Seal
end
-- └── end of what was `S26Seal.lean` ───────────────────────────────────────────────

-- ┌── was `Dllbc/Tests/S26Rec.lean` ──────────────────────────────────────────────
section
/-!
# §26 (M26-C) — effectful recursors: the executing machine first

Phase C of the `fn`/λ unification (`docs/combining-fns.md` §7). §12 decision 7 is
explicit about the order — "the executing machine is built first or in lockstep,
never after" — and this file is that half: **ι-reduction of a recursor whose arms
are BODIES**, with the differential running from the first commit.

## The two forms

  * `Term.lamR` / `Val.rfn` — **the runtime λ**, `λ(x : τ, y : υ){ … }`: named binders and
    a *body*. Phase A could not build it ("a λ whose body is a runtime body has no
    `Val` representation"), and the reason it needs a second former rather than a
    second rule is that a body reaches its binders through Ω — a match scrutinizes
    a `Var`, `&mut x` roots a place at a `Var` — and a de Bruijn index names no
    slot. So the pure λ substitutes and this one binds.
  * `applyR` — ⇒-application of a function value, which is where the three rules
    meet: β for a pure λ, bind-and-run for a runtime λ, and **ι with the arm
    applied as a body** for a recursor at a constructor scrutinee.

## What `ih` is, mechanically

`natRec P z s (S m) v … ↦ s m ⟨natRec P z s m⟩ v …`, and the second argument is
`ih`: literally the recursor at the predecessor. It is a `Val` spine — closed,
marker-free, index-kind — which is §7 cost 2's "boring kind" of first-class
function value, with no environment capture anywhere in it. Calling it is
`.callV`, and the modes of its arguments come off the base arm's binder NAMES
(§6), because a borrow-moded Π has no value to read them off.

## Saturation is what keeps the borrows honest (§12 decision 4)

ι hands the arm the predecessor, the recursor at it, and everything the caller
still owed **in one application**, so no partial application ever exists holding a
borrow while it waits. That is not an accident of the encoding — it is the reason
§7 cost 3 demands spine application, arriving as the shape of the ι rule.
-/

open Dllbc
open Dllbc.Tests.S9Diff (runExec symEnvs instanceOfC diffC)
open Dllbc.StdLemmas (IdCongr)

namespace Dllbc.Tests.S26Rec

/-! ## The declared side's two verdicts

    §E compares a DECLARED function against its sealed twin, so it needs the
    verdict of a `FnDef` — the one thing in this file that is not a program, and
    deliberately so (a declaration is what the pair is comparing against). These
    used to be borrowed from `S26Seal`, which had them because everything there
    was a declaration; that file is programs now (M28 ν) and has none, so the file
    that still needs them owns them. -/

-- (`ok`/`rejects` — the `FnDef`-taking verdict helpers — retired in M28 D9 with
-- their last subject. Every subject in this file is a program, and
-- `progOk`/`progRejects` take one directly.)

/-! ## §A. The runtime λ — the form, and the four things it is not -/

-- A1. Bind and run. The body is a body (a `let`, a constructor), and both
-- machines take the same rule: transparent application is β in the pure fragment
-- and inlining here, and neither machine verifies anything the other does not.
def a1 : Term := prog{ let G = λ(a : Nat) { let b = S(a); S(b) }; let r = G(1); () }
example : progOk a1 = true := by native_decide
example : diffC a1 = true := by native_decide

-- A2. A runtime function value is INDEX-KIND, so calling it is a place read and
-- the slot survives. `ih` depends on this: `quicksort` recurses twice from one
-- arm, and a callee that moved out of its slot could be called once.
def a2 : Term := prog{ let G = λ(a : Nat) { S(a) }; let r = G(1); let s = G(4); () }
example : progOk a2 = true := by native_decide
example : diffC a2 = true := by native_decide

/-! ### A3. CLOSED — checked, not assumed

    §7 cost 2 admits only closed function values, and constraint 5 defers
    environment capture wholesale. That is a premise this file has to enforce
    rather than describe: a body is entered under a fresh id window, so a free
    variable would not dangle — it would be silently rebound to whatever the shift
    lands on, which is capture arriving by accident. The rejection names the
    variable, and its twin (the same program with the value passed in) is
    accepted, so the refusal is about the CAPTURE and not about the program. -/

def a3bad : Term := prog{ let n = 3; let G = λ(a : Nat) { let z = n; () }; () }
def a3ok : Term := prog{ let n = 3; let G = λ(a : Nat, m : Nat) { let z = m; () }; G(1, n); () }
-- **The needle is §2.4's since M31 Stage A.** The old one said the citation is
-- "none of its 1 binder(s)", which was the closedness rule counting binders; the
-- rule now names the MODE, because that is what decides — and what a reader can
-- act on. The refusal and the acceptance below are the whole of the change: a
-- runtime citation is refused, a capital one is capture and is fine.
example : progRejects a3bad "a runtime (lowercase) binding" = true := by native_decide

-- A3cap. **THE NEW CAPABILITY** (§2.4). The same program with the binding
-- capitalised is ACCEPTED: a λ may close over comptime knowledge, which is what
-- makes the migration of every staged builder in this corpus writable at all.
-- Nothing is lost by the freeze being explicit — comptime bindings are immutable,
-- so capture and eager inlining are indistinguishable.
def a3cap : Term := prog{ let N = 3; let G = λ(a : Nat) { let z = N; () }; () }
example : progOk a3cap = true := by native_decide

-- A3pure. **THE SAME CHECK, THE OTHER λ SPECIES** — which is §2.4's claim that
-- the formation check is "identical for both λ species", asserted rather than
-- described. A PURE λ citing a runtime binding gets the same refusal, with the
-- same needle, as the runtime λ above; and the capital twin is accepted.
def a3pureBad : Term := prog{ let n = 3; let P = λ (u : Unit). n; () }
example : progRejects a3pureBad "a runtime (lowercase) binding" = true := by native_decide
def a3pureCap : Term := prog{ let N = 3; let P = λ (u : Unit). N; () }
example : progOk a3pureCap = true := by native_decide

-- A3type. …and the EXEMPTION, which is the other half of the rule and the half
-- that would be easy to lose: a runtime citation in a TYPE is untouched. `Le Z n`
-- here is a type consumed at its own event, not a body stored and applied later,
-- so §2.4 leaves it alone. Without this the rule would have swallowed every
-- dependent signature in the corpus.
def a3typeOk : Term := prog{
  fn Bnd (n : Nat, h : Le Z n) -> Unit { () };
  () }
example : progOk a3typeOk = true := by native_decide
example : progOk a3ok = true := by native_decide

-- A4. A NULLARY runtime λ is refused, and for a real ambiguity rather than
-- tidiness: `λ(){ e }` is a thunk, and at ι there is no way to tell "the arm
-- applied to no arguments" from "the arm with nothing owed" — `applyRest` has to
-- answer one way. Nothing in §7 wants a thunk.
def a4 : Term := prog{ let G = λ() { () }; () }
example : progRejects a4 "must bind at least one argument" = true := by native_decide

-- A5/A6. Saturation, both directions (§12 decision 4).
def a5 : Term := prog{ let G = λ(a : Nat, b : Nat) { () }; G(1); () }
def a6 : Term := prog{ let G = λ(a : Nat) { () }; G(1, 2); () }
example : progRejects a5 "partial application" = true := by native_decide
example : progRejects a6 "too many arguments" = true := by native_decide

/-! ### A7. ⇝ never meets the runtime λ

    The same grammar fact as the seal's (phase A, §A5), and it has to be asked of
    `readC` directly, because a rule that is merely never *reached* is not a rule
    that excludes anything. `.lamR` joins `&mut`, `:=`, `;`, `f(…)` and `seal` on
    `reflectC`'s list — this calculus's standing definition of the pure
    sub-grammar (§1.3). -/

def readCOn (t : Term) : String :=
  match (readC 1000 t).run (seedPure [] []) with
  | .ok v _ => "ACCEPTED " ++ v.pretty
  | .error e _ => e

example : strContains (readCOn (.lamR [(⟨0, "x"⟩, .const "Nat")] (.var ⟨0, "x"⟩)))
  "not in the comptime fragment" = true := by native_decide
-- …including buried inside a pure former, which is where a mode flag consulted
-- at the top would have let it through.
example : strContains (readCOn (.app (.const "S") (.lamR [(⟨0, "x"⟩, .const "Nat")] (.var ⟨0, "x"⟩))))
  "not in the comptime fragment" = true := by native_decide

/-! ## §B. ι with the arms as bodies — the executing machine (§7 cost 5)

    The rule §12 decision 7 puts first. A recursor whose arms are bodies is not a
    comptime object at all — `readC` refuses `.lamR`, and the motive is a
    borrow-moded Π which `readC` refuses too — so ⇒ evaluates the spine itself and
    ι-reduces it as **control flow**: the scrutinee's constructor selects an arm,
    and the arm runs, writing through borrows and calling.

    The programs below are fuel-threaded, which is §12 decision 8 rather than a
    convenience: `[v]`-style payload decrease has no recursor form, that regression
    is accepted, and fuel is the blessed interim. -/

/-- The motive, and the one place a runtime recursor's type is written by hand
    until phase D's macro derives it: `λ f. Π (v : &mut List Nat) → Unit`. It must
    be built in a ⇝ position (`prog{}`) — in a body, `&mut` is the borrow
    *operation*, not the borrow type. -/
def zeroMot : Term := prog{ λ (f : Nat). Π (v : &mut List Nat) → Unit }

/-- `zeroAll`, as a recursor term: walk the list through a mutable borrow and
    write `0` into every element, recursing on fuel.

    Everything §7 promises is in these four lines. The arms are bodies (`*hd := 0`
    is a write through a field reborrow). `ih` is a bound runtime variable holding
    a closed function value. The recursive call `ih(tl)` passes a BORROW as an
    argument — cost 2's "taking its borrows as arguments" — and is saturated, so
    no partial application ever holds `tl` while waiting. And there is no `[k]`
    guard anywhere: termination is by construction. -/

def b1 : Term := prog{
  let x = Cons(1, Cons(2, Nil));
  let b = &m x;
  let f = natRec %zeroMot
            (λ(v : &mut List Nat) { () })
            (λ(f2 : Nat, ih : Π (v : &mut List Nat) → Unit, v : &mut List Nat)
               { match v { Nil => (), Cons(hd, tl) => { *hd := 0; ih(tl); () } } });
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

-- …and the recursor itself sits in an ordinary runtime slot as a VALUE: a closed
-- function value, which is what §7 cost 2 says the whole closure story has to be
-- for this phase. `@motive` is the erased motive slot (a borrow-moded Π has no ⇝
-- reading, and ι has no use for one — the checking side derives it from the
-- ascription instead, §7).
example : slotOf b1 "f" = some "natRec @motive λr(v){…} λr(f2, ih, v){…}" := by
  native_decide

-- B2. Surplus fuel is harmless: the list runs out first and the `Nil` arm returns.
def b2 : Term := prog{
  let x = Cons(1, Cons(2, Nil));
  let b = &m x;
  let f = natRec %zeroMot
            (λ(v : &mut List Nat) { () })
            (λ(f2 : Nat, ih : Π (v : &mut List Nat) → Unit, v : &mut List Nat)
               { match v { Nil => (), Cons(hd, tl) => { *hd := 0; ih(tl); () } } });
  f(9, b);
  let y = x;
  () }
example : slotOf b2 "y" = some "Cons Z (Cons Z Nil)" := by native_decide

-- B3. `listRec`, and a motive that is a function type — which is the shape §7
-- always has, since the trailing binders are what carry the borrows. The
-- structural recursion needs no fuel: the scrutinee is the list itself.
def bumpMot : Term := prog{ λ (l : List Nat). Π (v : &mut Nat) → Unit }
def b3 : Term := prog{
  let l = Cons(7, Cons(8, Nil));
  let acc = 0;
  let a = &m acc;
  let f = listRec Nat %bumpMot
            (λ(w : &mut Nat) { () })
            (λ(h : Nat, t : List Nat, ih : Π (v : &mut Nat) → Unit, v : &mut Nat)
               { *v := S(*v); ih(v); () });
  f(l, a);
  let r = acc;
  () }
example : progOk b3 = true := by native_decide
-- One increment per element: the arm ran twice, through the same borrow, handed
-- down the recursion and handed back.
example : slotOf b3 "r" = some "S (S Z)" := by native_decide

/-! ### B4. A recursor stuck on a symbolic scrutinee is a VALUE — and applying one
    is not this phase's rule

    Both halves matter and they are the same fact from two sides. Unapplied, the
    stuck spine is exactly what §7's convergence argument says a recursive
    occurrence must be — "`ih` is a bound Π-typed variable, literally the sealed
    view at the predecessor" — so it has to be a legal value, and B1 above shows
    it standing in a slot. APPLIED, it is arms-as-bodies checking, which is
    reachable through a seal and not through a call; refused here by name rather
    than by getting stuck somewhere downstream. -/

def b4 : Term := prog{ fn B4 (fuel : Nat) -> Unit {
  let x = Cons(1, Nil);
  let b = &m x;
  let f = natRec %zeroMot
            (λ(v : &mut List Nat) { () })
            (λ(f2 : Nat, ih : Π (v : &mut List Nat) → Unit, v : &mut List Nat)
               { match v { Nil => (), Cons(hd, tl) => { *hd := 0; ih(tl); () } } });
  f(fuel, b);
  let y = x;
  () }; () }
example : progRejects b4 "stuck on a symbolic scrutinee" = true := by native_decide

-- …and the same program without the application checks, because forming the
-- recursor is forming a value. This is the pair that says the rejection above is
-- about APPLYING a stuck recursor, not about writing one.
def b4v : Term := prog{
  let f = natRec %zeroMot
            (λ(v : &mut List Nat) { () })
            (λ(f2 : Nat, ih : Π (v : &mut List Nat) → Unit, v : &mut List Nat)
               { match v { Nil => (), Cons(hd, tl) => { *hd := 0; ih(tl); () } } });
  () }
example : progOk b4v = true := by native_decide

/-! ## §C. The differential, under ONE relation (constraint 6, and inherited fact 4)

    Constraint 6 asks for both machines on every new value form, and §12 decision
    7 asks for the differential "running from the first commit". Both are here.

    **The relation was two relations and is now one.** M26-A extended `matchVal`
    for the seal (a σ inside arithmetic must be compared up to computation) but
    deliberately left its extension beside S9Diff's rather than folding them
    together, recording that neither was a superset: S9Diff's had the array-carve
    case and no computation, M26-A's computed and had no carve case. A program
    that carved AND computed would have been a false counterexample under either.
    `S9Diff.instanceOfC` is the merge — collect σ ↦ concrete through constructors,
    borrows AND carved segments, then instantiate, normalize, and compare with the
    segment-aware matcher — and the three groups below are what say the merge kept
    both halves and can still say NO. -/

-- C1. The recursor programs: every one of them, both machines, same Ω.
def recShapes : List Term := [a1, a2, b1, b2, b3, b4v]
example : recShapes.all (fun t => diffC t) = true := by native_decide

-- C2. THE CARVE HALF, kept. `S24Arrays`' callers are the programs that forced the
-- segment case into the relation in the first place ("the first array body handed
-- to `diffV2` reported a counterexample, and it was a FALSE one"): a checking-mode
-- release leaves `Arr⟨1 ▷ [3], 1 ▷ σ₀, 1 ▷ [2]⟩` where the concrete run is
-- `[3, 9, 2]`. They stay green under the merged relation, so computation was added
-- without costing the fold.
-- (the pool went with M28 ν: each caller declares its own callee, so the table is
-- empty and the shape is one self-contained program.)
example : Tests.S24Arrays.arrCallers.all
    (fun b => diffC b) = true := by native_decide

-- C3. THE COMPUTATION HALF, kept: phase A's counterexample, where a seal puts a σ
-- inside ordinary arithmetic and the structural matcher reports a counterexample
-- that is not one.
-- (`d1` is a PROGRAM since M28 ν, so the body is the thing itself — the `.body`
-- projection went with the declaration that used to wrap it.)
example : diffC Tests.S26Seal.d1 = true := by native_decide
example : Tests.S26Seal.diffOld Tests.S26Seal.d1 = false := by native_decide

/-! ### C4. Harness liveness — the relation must be able to say NO about a RECURSOR

    A counterexample-finder that has never found its counterexample is unvalidated
    (S9Diff's standing rule), and validating it on the seal's programs would say
    nothing about the ι rule. So: the symbolic side of `b1` (fuel 3, both elements
    zeroed) against the concrete side of the same program with fuel 1 — which
    zeroes the head and leaves the tail at 2. Same slots, same shapes, one
    genuinely different value. -/

def b1short : Term := prog{
  let x = Cons(1, Cons(2, Nil));
  let b = &m x;
  let f = natRec %zeroMot
            (λ(v : &mut List Nat) { () })
            (λ(f2 : Nat, ih : Π (v : &mut List Nat) → Unit, v : &mut List Nat)
               { match v { Nil => (), Cons(hd, tl) => { *hd := 0; ih(tl); () } } });
  f(1, b);
  let y = x;
  () }
-- The mutant is a real program and a different one: it stops after the head.
example : slotOf b1short "y" = some "Cons Z (Cons (S (S Z)) Nil)" := by native_decide

example :
  (match symEnvs b1, runExec b1short with
   | [.ok se], .ok ce => instanceOfC se ce
   | _, _ => true) = false := by native_decide
-- …and YES to the honest pairing, so the NO above is discrimination rather than a
-- relation that cannot see recursor programs at all.
example :
  (match symEnvs b1, runExec b1 with
   | [.ok se], .ok ce => instanceOfC se ce
   | _, _ => false) = true := by native_decide

/-! ## §D. A limitation, pinned rather than left to be met

    A runtime recursor needs a **function motive** — which is §7's shape anyway,
    since the trailing binders are what carry the borrows. At a DATA motive
    (`λ l. Nat`) the arms have no trailing binders, so `ih` is not a function but
    the recursor-at-the-predecessor itself, handed to the arm as a value; the arm
    stores it, and the pure fragment cannot reduce it afterwards, because its own
    arm is a body and `whnfV` has no rule for applying one.

    The result is a stuck spine rather than a wrong answer — both machines produce
    the same thing, so this is not a differential failure — and the audit rejects
    it when it tries to type the result. Pinned so the phase-D agent meets a test
    rather than a surprise, with the honest reading beside it: a recursor whose
    motive is not a function type has ordinary terms for arms, and the PURE
    recursor already computes those. -/

def lenMot : Term := prog{ λ (l : List Nat). Nat }
def d1 : Term := prog{ fn Caller () -> Nat {
  let l = Cons(7, Cons(8, Nil));
  let f = listRec Nat %lenMot Z (λ(h : Nat, t : List Nat, ih : Nat) { S(ih) });
  f(l) }; () }
example : progRejects d1 "cannot type neutral" = true := by native_decide

/-! ## §E. The audit relocation — checking a seal IS `checkFn`'s content (§5.4)

    Phase A's third pinned limitation, and the one the whole ensures discipline
    rests on. `.seal t u` with a borrow-moded Π `u` cannot be checked by
    `hasType`: a Π with `&mut` binders is a *function signature*, `readC` refuses
    `borrowT` outright, and there is no value for `hasType` to be asked about. The
    check is §5.4's audit — seed `u`'s telescope, explore the body one path per
    symbolic branch, audit each path at return with exit snapshots and
    obligations — which is exactly `checkFn`'s content, reached from the node
    instead of from a declaration.

    **What decides which rule fires is the sealed TERM, not the type.** A runtime
    λ takes the audit; everything else takes phase A's `readC`-then-`hasType`
    unchanged, which is what keeps §12-open-4's identity intact (§B of `S26Seal`
    still passes, pair for pair). `checkFn` is untouched and still checks every
    `FnDef` in the corpus: content moved, nothing was deleted (J1). -/

def unitSeal : Term := prog{ Π (v : &mut List Nat) → Unit }
def pinSeal : Term := prog{ Π (v : &mut List Nat) → Id (List Nat) (*v) (Cons 9 Nil) }

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

/-! ### E2. The ensures, threaded through the seal (§5 point 4)

    The M23 shape, with the callee sealed instead of declared: the caller holds a
    borrow, hands a reborrow to the sealed function, and RETURNS the equation it
    got back as its own postcondition. That only type-checks if the σ the call
    re-minted for the payload is the same σ the caller's exit `*v` reads — §5.4's
    caller-side σ-sharing — so this pins the whole ensures pipeline through a
    sealed callee, not merely that the seal was accepted.

    The sealed body has to PRODUCE the proof, which is the thing a `Unit`-sealed
    body does not have to do. That is what makes the pair below the real test of
    "what you keep is what you write". -/

def e2 : Term := prog{ fn Caller (v : &mut List Nat) -> Id (List Nat) (*v) (Cons 9 Nil) {
  let F = (λ(w : &mut List Nat) { *w := Cons(9, Nil); Refl } : %pinSeal);
  F(&m *v) }; () }
example : progOk e2 = true := by native_decide

-- The same program, the same body, sealed at `Unit`: the caller gets nothing back
-- and cannot state its own postcondition. Sound, honest, useless — one ascription
-- apart, which is §5 point 4 with nothing left to interpret.
def e2none : Term := prog{ fn Caller (v : &mut List Nat) -> Id (List Nat) (*v) (Cons 9 Nil) {
  let F = (λ(w : &mut List Nat) { *w := Cons(9, Nil); () } : %unitSeal);
  F(&m *v) }; () }
example : progRejects e2none "does not have return type" = true := by native_decide

/-! ### E3. The negative controls, one per branch of the new rule -/

-- The body does not establish the ensures: rejected AT THE SEAL by the audit, and
-- the message is the audit's own — `Refl` does not inhabit the equation the
-- ascription promised.
def e3a : Term := prog{
  let F = (λ(v : &mut List Nat) { *v := Cons(8, Nil); Refl } : %pinSeal); () }
example : progRejects e3a "does not have return type" = true := by native_decide

-- The body leaves a hole in its argument borrow: the OBLIGATION audit, which is
-- the half of §5.4 the ensures check does not cover, and which only exists
-- because the seal now seeds a telescope.
def e3b : Term := prog{
  let F = (λ(v : &mut List Nat) { let l = *v; () } : %unitSeal); () }
example : progRejects e3b "holds a hole (⊥) at return" = true := by native_decide

-- Mode disagreement: the λ's binder is lowercase where the ascription binds
-- comptime. §6 could be stated twice here and disagree, so it is checked — and
-- this is the callee-side half of phase B's "the ascription is the contract"
-- (F3 settled the caller side).
def cmpSeal : Term := prog{ Π (N : Nat) → Nat }
def e3c : Term := prog{
  let F = (λ(n : Nat) { S(n) } : %cmpSeal); () }
example : progRejects e3c "the ascribed type binds it as comptime" = true := by native_decide
-- …and its twin, one character apart, is accepted.
def e3cok : Term := prog{
  let F = (λ(N : Nat) { Z } : %cmpSeal); () }
example : progOk e3cok = true := by native_decide

-- Arity disagreement (§12 decision 4, at the ascription rather than at a call).
def e3d : Term := prog{
  let F = (λ(v : &mut List Nat, w : Nat) { () } : %unitSeal); () }
example : progRejects e3d "no Π binder left for it" = true := by native_decide

-- Sealing something that is NOT a runtime λ at a function signature — phase A's
-- A4, now refused for the reason instead of for the phase.
def e3e : Term := prog{
  let F = (λ (x : Nat). x : %unitSeal); () }
example : progRejects e3e "the sealed term must be a runtime λ" = true := by native_decide

/-! ### E4. FRAME ISOLATION — the sealed body's effects stay inside the check

    Phase A evaluated a seal's body IN PLACE and recorded that "a sealed FUNCTION
    body will want frame isolation, and that arrives with phase C's audit
    relocation". This is that debt paid, and it is directly testable: the sealed
    body below borrows and writes, and the caller's `x` is untouched by any of it
    — still owned, still `Cons 1 Nil`, movable afterwards. A body checked in place
    would have consumed something of the caller's. -/

def e4 : Term := prog{
  let x = Cons(1, Nil);
  let F = (λ(v : &mut List Nat) { *v := Cons(9, Nil); () } : %unitSeal);
  let y = x;
  () }
example : progOk e4 = true := by native_decide
example : slotOf e4 "y" = some "Cons (S Z) Nil" := by native_decide

/-! ### E5. THE SMELL TEST, extended to borrow-moded seals

    §12-open-4 asked whether the audit of a borrow-FREE sealed λ degenerates to
    exactly `hasType`; phase A discharged that as an identity over a 16-pair
    battery. The borrow-moded question is its sibling and the one this phase owes:
    does the audit of a sealed λ agree with **`checkFn`'s verdict on the same
    function declared**? If §7 is right that `fn` is a macro, it must — the two
    are supposed to be the same check reached by two routes.

    Discharged as an identity over hand-written twins rather than a spot check,
    with both polarities so it cannot hold vacuously. Each pair is the same
    telescope, the same return type and the same body, written once as a `FnDef`
    and once as `(λ(… : …){ … } : Π …)`. -/

def pushD : Term := prog{ fn PushD (e : Nat, v : &mut List Nat) -> Unit
  { let tail = *v; *v := Cons(e, tail); () }; () }
def pushS : Term := prog{ let F = (λ(e : Nat, v : &mut List Nat) { let tail = *v; *v := Cons(e, tail); () } : Π (e : Nat) → Π (v : &mut List Nat) → Unit); () }

/-- The `old *v` shape: an ensures relating the EXIT payload to the ENTRY one,
    which is the convention M23's whole corpus is written in and the reason the
    seal has to seed `entrySyms` as well as `exitSyms`. -/
def consD : Term := prog{ fn ConsD (v : &mut List Nat)
  -> Id (List Nat) (*v) (Cons 9 (old *v))
  { let t = *v; *v := Cons(9, t); Refl }; () }
def consS : Term := prog{ let F = (λ(v : &mut List Nat) { let t = *v; *v := Cons(9, t); Refl } : Π (v : &mut List Nat) → Id (List Nat) (*v) (Cons 9 (old *v))); () }

/-- The spec lie: the body conses `8` where the ensures says `9`. -/
def lieD : Term := prog{ fn LieD (v : &mut List Nat)
  -> Id (List Nat) (*v) (Cons 9 (old *v))
  { let t = *v; *v := Cons(8, t); Refl }; () }
def lieS : Term := prog{ let F = (λ(v : &mut List Nat) { let t = *v; *v := Cons(8, t); Refl } : Π (v : &mut List Nat) → Id (List Nat) (*v) (Cons 9 (old *v))); () }

/-- The obligation lie: the payload is taken and never refilled. -/
def holeD : Term := prog{ fn HoleD (v : &mut List Nat) -> Unit { let l = *v; () }; () }
def holeS : Term := prog{ let F = (λ(v : &mut List Nat) { let l = *v; () } : Π (v : &mut List Nat) → Unit); () }

/-- Each pair: the `fn` STATEMENT and the hand-written sealed λ of the same
    function. Both sides are programs (M28 ι for the seal, M28 D5 for the `fn`),
    which is what the pair was always comparing — §7 says `fn` is a macro over the
    seal, and this is that sentence as two verdicts. -/
def twins : List (Term × Term) :=
  [ (pushD, pushS), (consD, consS), (lieD, lieS), (holeD, holeS) ]

-- THE SMELL TEST: the `fn` lowering's audit and the hand-written seal's agree,
-- pair for pair. (It used to compare against `checkFn`; that path died in M27-δ
-- and the surviving comparison is the one §7 is actually about.)
example : twins.all (fun p => progOk p.1 == progOk p.2) = true := by native_decide
-- …and it is not vacuous: both verdicts occur, so the identity above is pinning
-- agreement rather than a constant function.
example : (twins.any (fun p => progOk p.1) && twins.any (fun p => !progOk p.1)) = true := by
  native_decide
-- …and the rejections agree on WHY, not merely that. A sealed body that lies
-- about its ensures and a `fn` that lies about the same ensures are refused by the
-- same audit with the same message — which is what says the check was relocated
-- rather than reimplemented.
example : (progRejects lieD "does not have return type" && progRejects lieS "does not have return type")
  = true := by native_decide
example : (progRejects holeD "holds a hole (⊥) at return" && progRejects holeS "holds a hole (⊥) at return")
  = true := by native_decide

/-! ## §F. Arms as bodies — the CHECKING side (§7 cost 1)

    "Runtime-moded recursor motives are the one real kernel addition: arms contain
    writes, calls and borrows — *bodies* — so the checker must symbolically execute
    an arm as a body with an abstract `ih : Π` in scope. The content of that
    judgment is exactly today's guard-checking; the plumbing is new."

    Three things make it work and each is worth naming, because each turned out to
    be something the earlier phases already had:

      * **The motive is derived from the signature.** Peel one Π off the
        ascription and the codomain IS the motive's body. §7 promised the macro
        would need no inference; the checker needs none either.
      * **Each arm is checked once, at its own constructor** — `Z` and `S k` ARE
        the split, and the motive instantiated at each is the goal. No driver
        change: `exploreMatch` forks paths because a runtime match does not know
        its scrutinee, while a recursor's arms come labelled.
      * **`ih` is a σ with a signature and no body**, which is the sealed self-view
        at the predecessor. It is seeded by the same rule that seeds any Π-typed
        parameter and called by the same rule that calls any sealed function —
        §7's "self-ensures FORCED rather than stipulated", as plumbing. -/

def zeroSeal : Term := prog{ Π (fuel : Nat) → Π (v : &mut List Nat) → Unit }


def f1 : Term := prog{
  let F = (natRec %zeroMot
                 (λ(v : &mut List Nat) { () })
                 (λ(f2 : Nat, ih : Π (v : &mut List Nat) → Unit, v : &mut List Nat)
                    { match v { Nil => (), Cons(hd, tl) => { *hd := 0; ih(tl); () } } }) : %zeroSeal);
  let x = Cons(1, Cons(2, Nil));
  let b = &m x;
  F(3, b);
  let y = x;
  () }
example : progOk f1 = true := by native_decide

-- The seal is what makes it opaque: the caller learns only `Unit`, so the list it
-- gets back is an EXISTENTIAL — §2.2's forgetting, now reached through a recursor
-- rather than through a declaration. (Asserted as "a σ" rather than as a σ id: the
-- id is a counter, and pinning it would make this test fail for reasons that have
-- nothing to do with what it is about.)
example : (slotOf f1 "y").map (fun s => s.take 1) = some "σ" := by native_decide

-- …and the SAME program executes, with the recursion really running: both
-- machines, one differential.
example : diffC f1 = true := by native_decide
example :
  (match Dllbc.Tests.S9Diff.runExec f1 with
   | .ok e => (e.lookup "y").map Val.pretty
   | .error _ => none) = some "Cons Z (Cons Z Nil)" := by native_decide

/-! ### F2. The motive is derived, and a written one that disagrees is refused

    §7 makes the motive redundant — it is the sealed Π with the scrutinee peeled
    off — so the checker derives it and compares. Syntactically, and that is
    forced rather than lazy: a motive over a borrow-moded Π has no `Val`, hence no
    conversion to be compared up to. Phase D's macro will derive it, so the
    comparison is free there; a hand-written mismatch is told what was expected. -/

def wrongMot : Term := prog{ λ (f : Nat). Π (v : &mut List Nat) → Nat }
def f2 : Term := prog{
  let F = (natRec %wrongMot
                 (λ(v : &mut List Nat) { () })
                 (λ(f2 : Nat, ih : Π (v : &mut List Nat) → Nat, v : &mut List Nat)
                    { match v { Nil => (), Cons(hd, tl) => { *hd := 0; ih(tl); () } } }) : %zeroSeal);
  () }
example : progRejects f2 "not the one its ascription derives" = true := by native_decide

/-! ### F3. An arm that does not establish the motive is rejected AT ITS OWN ARM

    The base arm below returns without restoring what it took, so its obligation
    audit fails — and the step arm is untouched and would pass. That is what says
    the arms are checked *separately*, each at its own instantiation, rather than
    the whole recursor being checked as one lump. -/

def f3 : Term := prog{
  let F = (natRec %zeroMot
                 (λ(v : &mut List Nat) { let l = *v; () })
                 (λ(f2 : Nat, ih : Π (v : &mut List Nat) → Unit, v : &mut List Nat)
                    { match v { Nil => (), Cons(hd, tl) => { *hd := 0; ih(tl); () } } }) : %zeroSeal);
  () }
example : progRejects f3 "holds a hole (⊥) at return" = true := by native_decide

/-! ## §G. THE CONVERGENCE TEST — `split_off`, declared and as a sealed recursor

    §7's claim is not that recursors are expressive enough in principle; it is that
    `fn` **is a macro** over a sealed recursor binding, so a real M23 function must
    check the same way both ways. `split_off` is the subject because it is real:
    it recurses, it mutates through a borrow, it hands a reborrow to its own
    recursive call, its return type is a Σ-chain of two equations relating the exit
    and entry snapshots, and it has a dead branch discharged by ex falso.

    It also needs no fuel, and that is worth noticing rather than glossing:
    §12 decision 8 accepts a naturalness regression for `[v]`-style *payload*
    decrease, but `split_off` recurses on its INDEX, which is a `Nat` — so the
    recursor form is `natRec` on the very argument `[i]` already named, and the
    elaboration is the mechanical one §7 describes with nothing threaded through.

    The two forms below are the same function. `S23Direct.splitOff` is the
    declared one, checked by `checkFn` with the `[i]` guard policing its self-call;
    this one is `.seal ⟨natRec …⟩ ⟨Π …⟩`, checked at the node with `ih` as an
    abstract signature and no guard anywhere. Both are accepted, and the second is
    what §7 says the first should elaborate to. -/

def splitTy : Term := prog{
  Π (i : Nat) → Π (v : &mut List Nat) → Π (hi : Le i (Len *v))
    → Σ (ret : List Nat) → Σ (h1 : Id (List Nat) (*v) (Take i (old *v)))
         → Id (List Nat) ret (Drop i (old *v)) }

def splitMot : Term := prog{
  λ (i : Nat). Π (v : &mut List Nat) → Π (hi : Le i (Len *v))
    → Σ (ret : List Nat) → Σ (h1 : Id (List Nat) (*v) (Take i (old *v)))
         → Id (List Nat) ret (Drop i (old *v)) }

/-- `split_off` as §7 says a `fn` elaborates. The body is `S23Direct.splitOff`'s,
    transcribed with one change and one deletion: the self-call
    `split_off(&mut *tl, i2, hi)` becomes `ih(&mut *tl, hi)` — the scrutinee
    argument is gone, because ι supplies it — and the `match i` disappears into the
    two arms. -/
def splitSealed : Term := prog{
  let F = (natRec %splitMot
      (λ(v : &mut List Nat, hi : Le Z (Len *v))
         { let tail = *v; *v := Nil; Pair(tail, Pair(Refl, Refl)) })
      (λ(i2 : Nat,
         ih : Π (v : &mut List Nat) → Π (hi : Le i2 (Len *v))
                → Σ (ret : List Nat) → Σ (h1 : Id (List Nat) (*v) (Take i2 (old *v)))
                     → Id (List Nat) ret (Drop i2 (old *v)),
         v : &mut List Nat,
         hi : Le (S i2) (Len *v)) {
         match v {
           Nil => botElim Unit hi,
           Cons(hd, tl) => {
             let y1 = Take i2 (*tl);
             let p = ih(&m *tl, hi);
             match p { Pair(rr, q) => match q { Pair(h1, h2) => {
               let c1 = IdCongr (List Nat) (List Nat) (λ (a : List Nat). Cons (*hd) a)
                          (*tl) y1 h1;
               Pair(rr, Pair(c1, h2)) } } } } } }) : %splitTy);
  () }

-- THE CONVERGENCE. ~~The declared function and the sealed recursor both check.~~
-- Half of that claim retired with `checkFn` (M27-δ): there is no declared path to
-- converge WITH, and §7's "fn is a macro" is no longer a comparison between two
-- checkers but the only elaboration there is. What survives is the half that was
-- always the interesting one — this hand-written sealed recursor and
-- `S23Direct.splitOff` are the same function, and `S26Fn` §"the macro's output is
-- α-equal to the hand-written recursor" is where that identity is now asserted.
example : progOk splitSealed = true := by native_decide

/-! ### G2. Not vacuous — the sealed form rejects the same lies the declared one does

    `S23Direct` guards `splitOff` with four twins (three spec lies and a body lie)
    so that its acceptance is not a coincidence. The sealed form has to be guarded
    the same way, or "both check" would be a much weaker statement than it looks.
    The body lie is the sharper of the two here: it breaks the congruence in the
    `Cons` arm, which is the arm `ih` lives in. -/

def splitMotLie : Term := prog{
  λ (i : Nat). Π (v : &mut List Nat) → Π (hi : Le i (Len *v))
    → Σ (ret : List Nat) → Σ (h1 : Id (List Nat) (*v) (Drop i (old *v)))
         → Id (List Nat) ret (Drop i (old *v)) }
def splitTyLie : Term := prog{
  Π (i : Nat) → Π (v : &mut List Nat) → Π (hi : Le i (Len *v))
    → Σ (ret : List Nat) → Σ (h1 : Id (List Nat) (*v) (Drop i (old *v)))
         → Id (List Nat) ret (Drop i (old *v)) }

-- A SPEC lie: the prefix conjunct claims `Drop` where the body leaves `Take`.
def splitSpecLie : Term := prog{
  let F = (natRec %splitMotLie
      (λ(v : &mut List Nat, hi : Le Z (Len *v))
         { let tail = *v; *v := Nil; Pair(tail, Pair(Refl, Refl)) })
      (λ(i2 : Nat,
         ih : Π (v : &mut List Nat) → Π (hi : Le i2 (Len *v))
                → Σ (ret : List Nat) → Σ (h1 : Id (List Nat) (*v) (Drop i2 (old *v)))
                     → Id (List Nat) ret (Drop i2 (old *v)),
         v : &mut List Nat,
         hi : Le (S i2) (Len *v)) {
         match v {
           Nil => botElim Unit hi,
           Cons(hd, tl) => {
             let y1 = Take i2 (*tl);
             let p = ih(&m *tl, hi);
             match p { Pair(rr, q) => match q { Pair(h1, h2) => {
               let c1 = IdCongr (List Nat) (List Nat) (λ (a : List Nat). Cons (*hd) a)
                          (*tl) y1 h1;
               Pair(rr, Pair(c1, h2)) } } } } } }) : %splitTyLie);
  () }
-- Caught on the BASE arm (`Pair σ (Pair Refl Refl)` against `Id Nil σ`), exactly
-- where `S23Direct` says its spec lies are caught.
example : progRejects splitSpecLie "does not have return type" = true := by native_decide

-- A BODY lie: the `Cons` arm forgets to restore the head, so the prefix conjunct
-- is false on the recursive path — the arm `ih` lives in.
def splitBodyLie : Term := prog{
  let F = (natRec %splitMot
      (λ(v : &mut List Nat, hi : Le Z (Len *v))
         { let tail = *v; *v := Nil; Pair(tail, Pair(Refl, Refl)) })
      (λ(i2 : Nat,
         ih : Π (v : &mut List Nat) → Π (hi : Le i2 (Len *v))
                → Σ (ret : List Nat) → Σ (h1 : Id (List Nat) (*v) (Take i2 (old *v)))
                     → Id (List Nat) ret (Drop i2 (old *v)),
         v : &mut List Nat,
         hi : Le (S i2) (Len *v)) {
         match v {
           Nil => botElim Unit hi,
           Cons(hd, tl) => {
             let y1 = Take i2 (*tl);
             let p = ih(&m *tl, hi);
             match p { Pair(rr, q) => match q { Pair(h1, h2) => {
               let c1 = IdCongr (List Nat) (List Nat) (λ (a : List Nat). Cons (*hd) a)
                          (*tl) y1 h1;
               Pair(rr, Pair(h1, h2)) } } } } } }) : %splitTy);
  () }
-- Caught on the STEP arm — the one `ih` lives in, and the one the spec lies leave
-- untested. Same division of labour as the declared function's four twins, which
-- is what makes "both check" a claim about the same coverage and not just the same
-- verdict.
example : progRejects splitBodyLie "does not have return type" = true := by native_decide

/-! ## §H. `bad()`, twice — the incoherence, probed rather than assumed

    §8's guard exists because a self-call admitted at its own declared return type
    with nothing decreasing proves anything: `fn bad () -> Id Nat Z (S Z) { bad() }`.
    §7 claims the guard EVAPORATES for recursor-expressed functions, so the two
    ways `bad()` could come back have to be checked directly rather than argued
    away. Constraint 3 is the standard: "the `bad()` self-proof stays unwritable by
    construction". -/

/-! ### H1. An unsealed recursive λ is UNWRITABLE, which is the honest form of
    "it has no checking story"

    §7 derives that an unsealed recursive λ is incoherent at checking (unfolding
    self never terminates) and constraint 3 requires it to stay unwritable. It
    does, and the mechanism is not a rule about recursion at all: **the binding is
    not in scope in its own right-hand side.** `let g = λ(n : Nat){ g(n) }` binds `g` for
    what FOLLOWS, so the `g` inside the λ names nothing lexical and falls through
    to the declaration table, where it is not. §8 predicts exactly this — "a
    let-chain cannot reference downward, so no forward references falls out,
    consistent by construction with mutual recursion being rejected" — and
    self-reference is the degenerate downward reference.

    **This control had to be made to bite.** Written as a `let` that is never used,
    the program is ACCEPTED, and looks like a working negative test: the λ's body
    is never demanded, so nothing ever resolves the name. That is phase A's finding
    (a negative test must be per DEMAND SITE) arriving a third time, and it is why
    both forms below make something ask. -/

-- Demanded by APPLYING it: the body runs and the name resolves against nothing.
def h1 : Term := prog{
  let G = λ(n : Nat) { G(n) };
  G(1);
  () }
example : progRejects h1 "unknown function 'G'" = true := by native_decide

-- Demanded by SEALING it, which is the form §7 contrasts with: sealing is what
-- makes a body get checked, and it is also what a recursive function needs — but
-- the seal does not put the binding in its own scope either. Recursion has to come
-- from the recursor, which is the point of §7.
def h1s : Term := prog{
  let G = (λ(n : Nat) { G(n) } : Π (n : Nat) → Nat);
  () }
example : progRejects h1s "unknown function 'G'" = true := by native_decide

-- The vacuous version, pinned as the trap it is rather than deleted: the same
-- program with nothing demanding the λ's body is accepted, and tests nothing.
def h1vacuous : Term := prog{ let G = λ(n : Nat) { G(n) }; () }
example : progOk h1vacuous = true := by native_decide

/-! ### H2. A sealed recursor whose motive promises a falsehood is rejected at its
    own audit — AND the rejection comes from the base arm

    The `bad()` shape as a recursor: a motive claiming `Id Nat Z (S Z)` at every
    level. The step arm goes through, and that is not a bug — `ih` really does hand
    it the claim at the predecessor, which is exactly the self-ensures §7 says is
    forced. What stops it is the BASE arm, which has no `ih` and must inhabit the
    claim outright. That is structural induction doing the job §8's guard was doing
    by hand, and it is why the guard can evaporate: the side condition is not
    checked, it is unnecessary.

    The pair below is what says so. `h2` is the whole recursor and is rejected;
    `h2step` is the same step arm sealed on its own at the type `ih` gave it —
    `Π (u : Unit) → Id Nat Z (S Z)` assumed, the same returned — and is ACCEPTED,
    which is the assumption discharged honestly rather than a hole. -/

def badMot : Term := prog{ λ (n : Nat). Π (u : Unit) → Id Nat Z (S Z) }
def badTy : Term := prog{ Π (n : Nat) → Π (u : Unit) → Id Nat Z (S Z) }

def h2 : Term := prog{
  let F = (natRec %badMot
                 (λ(u : Unit) { Refl })
                 (λ(n2 : Nat, ih : Π (u : Unit) → Id Nat Z (S Z), u : Unit) { ih(u) }) : %badTy);
  () }
example : progRejects h2 "does not have return type" = true := by native_decide

-- The step arm alone, with the predecessor's claim as a HYPOTHESIS: accepted. So
-- the rejection above is located at the base case and nowhere else — `bad()` dies
-- because `Id Nat Z (S Z)` has no proof at zero, not because a guard forbade the
-- recursion.
def h2step : Term := prog{
  let F = (λ(ih : Π (u : Unit) → Id Nat Z (S Z), u : Unit) { ih(u) } : Π (ih : Π (u : Unit) → Id Nat Z (S Z)) → Π (u : Unit) → Id Nat Z (S Z));
  () }
example : progOk h2step = true := by native_decide

/-! ## §I. `ih` at the wrong level — the guard's content surviving as TYPING

    §8's guard policed "the recursive call's argument is a strict structural
    predecessor". §7 says that becomes unnecessary, and this is the mechanism: `ih`
    is typed `P k` while the arm proves `P (S k)`, so an arm that tries to use the
    recursion at its OWN level has nothing to pass it. The check is not a
    comparison the checker performs; it is the type `ih` was given.

    The motive below carries a fuel bound, which is what makes the levels visible:
    `Hn : Le (Len *v) n`. In the step arm `Hn : Le (Len *v) (S n2)` and `ih` wants
    `Le (Len *v) n2` — one successor apart, and no term bridges them. The accepted
    twin derives the predecessor's bound properly and passes THAT, so the rejection
    is about the level and not about the program being unwritable. -/

def bndMot : Term := prog{
  λ (n : Nat). Π (v : &mut List Nat) → Π (Hn : Le (Len *v) n) → Unit }
def bndTy : Term := prog{
  Π (n : Nat) → Π (v : &mut List Nat) → Π (Hn : Le (Len *v) n) → Unit }

-- The arm hands `ih` its OWN bound, `Le (Len *v) (S n2)`, where `ih` binds
-- `Le (Len *v) n2`. Refused, by the argument check at the abstract call.
def i1 : Term := prog{
  let F = (natRec %bndMot
                 (λ(v : &mut List Nat, Hn : Le (Len *v) Z) { () })
                 (λ(n2 : Nat,
                    ih : Π (v : &mut List Nat) → Π (Hn : Le (Len *v) n2) → Unit,
                    v : &mut List Nat, Hn : Le (Len *v) (S n2)) { ih(&m *v, Hn); () }) : %bndTy);
  () }
example : progRejects i1 "does not have its parameter type" = true := by native_decide

-- …and the twin that recurses at the predecessor's level is ACCEPTED — which is
-- what says the discipline is usable and not merely restrictive. Matching `v`
-- makes `*v` a `Cons`, so `Len *v` is `S (Len *tl)` and the arm's own
-- `Le (S (Len *tl)) (S n2)` IS `Le (Len *tl) n2` definitionally: the bound the
-- predecessor wants, obtained by the list getting shorter rather than by a lemma.
-- That is M14's bounds-cursor property, doing here exactly what §8's guard used to
-- do by comparing snapshots — except it is the TYPE, so nothing checks it.
def i2 : Term := prog{
  let F = (natRec %bndMot
                 (λ(v : &mut List Nat, Hn : Le (Len *v) Z) { () })
                 (λ(n2 : Nat,
                    ih : Π (v : &mut List Nat) → Π (Hn : Le (Len *v) n2) → Unit,
                    v : &mut List Nat, Hn : Le (Len *v) (S n2))
                    { match v { Nil => (), Cons(hd, tl) => { ih(&m *tl, Hn); () } } }) : %bndTy);
  () }
example : progOk i2 = true := by native_decide

/-! ## §J. The sealed `split_off`, RUN — the convergence closed at both arrows

    §G says the two forms check the same. This says the sealed one is a program:
    the same recursor, called concretely, splitting a real list, with the two
    machines agreeing. Without it the convergence would be a statement about the
    checker only, and §12 decision 7's whole point is that the executing machine is
    where this project's surprises live.

    `hi : Le 1 (Len *v)` is supplied as `()`: `Le` computes, the payload is
    concrete, and `Le 1 2` reduces to `Unit`. That is the ordinary route — the
    bound holds by computation, not by citation. -/

def j1 : Term := prog{
  let F = (natRec %splitMot
      (λ(v : &mut List Nat, hi : Le Z (Len *v))
         { let tail = *v; *v := Nil; Pair(tail, Pair(Refl, Refl)) })
      (λ(i2 : Nat,
         ih : Π (v : &mut List Nat) → Π (hi : Le i2 (Len *v))
                → Σ (ret : List Nat) → Σ (h1 : Id (List Nat) (*v) (Take i2 (old *v)))
                     → Id (List Nat) ret (Drop i2 (old *v)),
         v : &mut List Nat,
         hi : Le (S i2) (Len *v)) {
         match v {
           Nil => botElim Unit hi,
           Cons(hd, tl) => {
             let y1 = Take i2 (*tl);
             let p = ih(&m *tl, hi);
             match p { Pair(rr, q) => match q { Pair(h1, h2) => {
               let c1 = IdCongr (List Nat) (List Nat) (λ (a : List Nat). Cons (*hd) a)
                          (*tl) y1 h1;
               Pair(rr, Pair(c1, h2)) } } } } } }) : %splitTy);
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

/-! ## §K. Both dispatch surfaces (the phase-B lesson, audited rather than assumed)

    Phase B's fence was DEAD until it was duplicated at the explore driver: a
    statement-position `match` or `let` never reaches `readR`'s own cases. So every
    rule this phase adds has to be checked at both surfaces rather than assumed to
    be reached.

    It is, and by construction rather than by duplication — which is worth stating
    as the reason and not just the outcome. Phase B's fence lived INSIDE `readR`'s
    `.matchE` and `.letIn` cases, which are exactly the two the driver bypasses.
    Every rule here is a different `readR` case (`.seal`, `.lamR`, `.callV`, the
    recursor spine), and the driver reaches all of them: through `.letIn`'s
    right-hand side, through `.seq`'s expression, and through the final-expression
    fall-through. The tests below put a seal and a recursor call at each of those
    three positions, INSIDE a branch of a symbolic match — which is where
    `pushContinuations` sends a real body and where phase B's rule went dark. -/

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

-- The negative twin at the same two positions: a body that lies about its ensures
-- is caught inside the branch, not skipped along with it.
def k2 : Term := prog{ fn K2 (n : Nat) -> Unit {
  match n {
    Z => (),
    S(m) => {
      let F = (λ(v : &mut List Nat) { *v := Cons(8, Nil); Refl } : %pinSeal);
      () } } }; () }
example : progRejects k2 "does not have return type" = true := by native_decide

-- …and a seal in FINAL-EXPRESSION position inside a branch, which is the third
-- route (`explore`'s fall-through to `readR`). The ascription here is borrow-free
-- because a DECLARED fn cannot yet return a borrow-moded Π — `checkFn` has no
-- reading for such a return type, which is a pre-existing limitation of the
-- declaration form and one §8 dissolves rather than fixes (a program is a term, so
-- there is no return type to read, only a `let`).
def natFn : Term := prog{ Π (n : Nat) → Nat }
def k3 : Term := prog{ fn K3 (n : Nat) -> %natFn {
  match n {
    Z => (λ(m : Nat) { Z } : %natFn),
    S(m) => (λ(k : Nat) { S(k) } : %natFn) } }; () }
example : progOk k3 = true := by native_decide

/-! ## §M (M27-P3). `ih` READ AS A VALUE — and the two machines disagree

    `indexKindV` classifies a runtime function value (`Val.rfn`) as index-kind, so
    reading one COPIES and leaves the owner intact. Its comment justified that with
    "copy-on-read is what makes a body able to recurse twice (`quicksort`'s two
    halves)". M27-P3 measured the claim by flipping the case to `false` and running
    the whole suite: **it stayed green**, so nothing exercised it. Writing the test
    that would exercise it found something better than an unexercised case.

    **The two machines answer differently, and the checking side is the one that
    cannot reach `.rfn` at all.** Binding `ih` to a local is REJECTED when checking
    and RUNS when executing:

      * Checking: `ih` is a **σ** whose signature lives in `St.fsig` — a borrow-moded
        Π has no `Val`, which is M26-C's founding fact — and `indexKindV`'s `.sym`
        case consults `sctx`, not `fsig`. No entry, so it takes the conservative
        default and MOVES. **This is now REFUSED at the read** (M27's third
        containment), rather than left to be noticed by whatever demanded the
        emptied slot afterwards.
      * Executing: `ih` really is a `Val.rfn` in a slot, the `.rfn` case fires, and
        the read copies.

    So the comment was wrong twice over: copy-on-read is not what serves quicksort's
    two recursive calls (`.callV` LOCATES its callee and never moves it — M26-E),
    and the case it justifies is unreachable from the machine the comment is written
    beside. It is a correct conservative default on a value form only the executing
    machine ever holds.

    **The safe-direction reading was wrong, and c1's curry probe corrected it.**
    This file priced the divergence as reject-vs-run — the checker refusing a
    program the machine would run, which costs expressiveness and nothing else.
    §G3b of the curry probe exhibits a program BOTH machines ACCEPT whose final Ωs
    do not correspond (`f = ⊥` checking, the λ-spine executing), which is a
    simulation break on an accepted program: the class S9Diff's whole-program
    assertions exist to catch, arriving where they cannot see it. It also needs no
    recursor — any sealed borrow-taking function bound to a slot has it, because
    the trigger is the borrow-moded Π's lack of a `Val` and not anything about
    `ih`.

    So the position is now UNWRITABLE rather than merely awkward, and the
    assertions below are the containment's controls. The real fix — teaching
    `indexKindV` about `fsig` — changes the read rule for every σ and is filed for
    the function-model round, where the comptime-functions proposal may delete the
    whole class. Nothing in §7 wants `ih` in a slot anyway (cost 2 is explicit that
    it is "never partially applied"). -/

def mSeal : Term := prog{ Π (n : Nat) → Π (v : &mut List Nat) → Unit }
def mMot : Term := prog{ λ (n : Nat). Π (v : &mut List Nat) → Unit }

/-- The arm binds `ih` to a local and then still calls it. -/
def m1 : Term := prog{
  let F = (natRec %mMot
                 (λ(v : &mut List Nat) { () })
                 (λ(n2 : Nat, ih : Π (v : &mut List Nat) → Unit, v : &mut List Nat) {
                    let g = ih;
                    match v { Nil => (), Cons(hd, tl) => { *hd := 0; ih(tl); () } } }) : %mSeal);
  let x = Cons(1, Cons(2, Nil));
  let b = &m x;
  F(3, b);
  () }

-- CHECKING: refused. M27's third containment moved WHERE it is refused — the
-- refusal now fires at the BINDING rather than at the later call that found ⊥ —
-- because c1's curry probe showed the divergence is not confined to the safe
-- direction: a program that binds `ih` and never calls it is ACCEPTED by both
-- machines with final Ωs that do not correspond. The read is the event; the call
-- was only where the old rule happened to notice.
--
-- **And the REASON has moved a second time** (M31 Stage A). M27 α.2 had made it
-- the model — functions are reached by NAME, and `let g = ih` reads one into a
-- second slot — refusing the READ. M31 gives functions a MODE instead, and the
-- read stops being the wrong move: `let G = ih` copies comptime knowledge and
-- leaves `ih` exactly where it was, which is what every call already did. What
-- is still wrong is the lowercase `g`, because a runtime binding cannot hold a
-- function, and that is what `backstopFnBinding` says one layer later.
--
-- Same program, same verdict, third message. Worth noticing that the verdict has
-- now survived two complete changes of reason: a mechanism (a borrow-moded Π has
-- no `Val`), a model (reached by name), and a mode (functions are comptime). The
-- needle is the FIX this time, which is the thing a reader can act on.
example : progRejects m1 "capitalise the binder" = true := by native_decide

-- The migrated twin: the same body with the binder capitalised is accepted, so
-- the refusal is about the binder's mode and not about naming `ih` at all.
def m1cap : Term := prog{
  let F = (natRec %mMot
                 (λ(v : &mut List Nat) { () })
                 (λ(n2 : Nat, ih : Π (v : &mut List Nat) → Unit, v : &mut List Nat) {
                    let G = ih;
                    match v { Nil => (), Cons(hd, tl) => { *hd := 0; ih(tl); () } } }) : %mSeal);
  let x = Cons(1, Cons(2, Nil));
  let b = &m x;
  F(3, b);
  () }
example : progOk m1cap = true := by native_decide

-- EXECUTING: the same program runs to completion and really zeroes the list,
-- because there `ih` is a `Val.rfn` and the `.rfn` case copies it.
example : (match Dllbc.Tests.S9Diff.runExec m1 with
   | .ok e => (e.lookup "x").map Val.pretty
   | .error _ => none) = some "Cons Z (Cons Z Nil)" := by native_decide

-- Not vacuous: the SAME body without the `let g = ih` line checks, so the
-- rejection above is about reading `ih` as a value and not about the shape.
def m0 : Term := prog{
  let F = (natRec %mMot
                 (λ(v : &mut List Nat) { () })
                 (λ(n2 : Nat, ih : Π (v : &mut List Nat) → Unit, v : &mut List Nat) {
                    match v { Nil => (), Cons(hd, tl) => { *hd := 0; ih(tl); () } } }) : %mSeal);
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
-- └── end of what was `S26Rec.lean` ───────────────────────────────────────────────

-- ┌── was `Dllbc/Tests/S27Lam.lean` ──────────────────────────────────────────────
section
/-!
# S27 — the annotated runtime λ (M27 α.1a)

`Term.lamR`'s binders carry their domains. The document's grammar has said
`λ (x : τ). t` from the start; M26-C's Curry form was the mechanization drifting
from it while building the runtime layer, and this is the drift undone.

**Nothing here checks an annotation yet.** α.1a carries the types; α.1b makes
`sealFn` convert the λ's synthesized Π against the ascription. The two are
separate commits on purpose — 95 mechanical binder edits and two rule changes in
one commit would make every red build a two-suspect investigation — so what this
file pins is exactly the mechanical half:

  * the surface really carries a domain, and the VALUE really drops it (§A/§B);
  * the traversals that gained a case really traverse it (§C free variables, §D
    equality — the α-normalization half went with `AlphaEq.lean` in M28 cluster C);
  * and `fnElab`'s arm annotations are the ones the kernel's own `checkArm`
    derives — §E, the one place in α.1a where a wrong answer would compile,
    pass, and be silently the wrong type.
-/

namespace Dllbc.Tests.S27Lam
open Dllbc

/-! The `ok`/`rejects` helpers retired with the `FnDef` subjects they took (M28
    ν). EVERY subject in this file is a program now (M28 D5 took the last one), and
    `progOk`/`progRejects` from `Dllbc/Program.lean` take one directly.

    §E and §F still read a `Term` STRUCTURALLY, and that is not a leftover: they
    perturb the elaborated recursor's arm ANNOTATIONS, which no source can write —
    the whole point is that the annotations are derived rather than chosen. What
    changed is where the term comes from. A `fn` statement lowers through `fnElab`
    (Uni.lean's `ublk` rule calls `fnElabOrFail`), so the sealed recursor is read
    back out of the binding the statement made, and every assertion is still a
    verdict on a program. -/

/-! ## §A. The surface carries the domain -/

def annotated : Term := prog{ let G = λ(a : Nat) { a }; () }

example : (match annotated with
           | .letIn _ (.lamR [(_, τ)] _) _ => Term.beq τ (.const "Nat")
           | _ => false) = true := by native_decide

-- A capitalized binder's domain carries §6's comptime marker, which is what makes
-- the annotation agree with the ascription `piPeel` checks a mode against.
def annotatedCmp : Term := prog{ let G = λ(A : Nat) { A }; () }
example : (match annotatedCmp with
           | .letIn _ (.lamR [(_, τ)] _) _ => Term.beq τ (.cmpT (.const "Nat"))
           | _ => false) = true := by native_decide

/-! ## §B. …and the VALUE drops it (the erasure, ratified)

    `readR` forms a `Val.rfn` with names only. The executing machine binds and
    runs and never converts, so there is nothing downstream of formation for a
    domain to be used by — the seal is the one consumer and it holds the
    annotated TERM. -/

-- The type-level half, and it is the stronger of the two: this expression
-- typechecks exactly because `Val.rfn`'s binders are `Var` and not `Var × Term`.
-- A ledger that fails to compile is the one that cannot drift.
example : Val := .rfn [⟨0, "a"⟩] .unit

-- The live half: an ANNOTATED λ evaluates to a value printed with names alone.
example : (match runProgram annotated with
           | .ok env => (env.lookup "G").map Val.pretty
           | .error _ => none) = some "λr(a){…}" := by native_decide

/-! ## §C. Free variables reach into the domains

    `Term.freeRVars` traverses the binder types, as a TELESCOPE — each domain
    under the binders to its left and none of its own. That is a real rule and not
    a tidiness: a domain names runtime slots (`Le (Len *v) fuel` names two), so
    leaving them untraversed would let a genuinely free variable into a type and
    straight past the closedness check the traversal exists to feed.

    Three programs, one per demand site, and the λ is FORMED in every one — an
    unformed λ is never asked. -/

-- C1. The domain captures a data binding: refused, by the same rule and the same
-- message a captured body reference gets.
def capInType : Term := prog{ let n = 3; let G = λ(a : Le n n) { () }; () }
-- The needle moved with §2.4 (M31 Stage A): a λ's binder DOMAIN is part of the
-- node, so a runtime citation there is refused by the same rule and with the same
-- message as one in the body. That is deliberate — §2.4 exempts type positions
-- because a type is consumed at its own event, and a λ's domain is not: it is
-- stored with the λ and read whenever the λ is applied, which is the very gap the
-- rule closes.
example : progRejects capInType "a runtime (lowercase) binding" = true := by native_decide

-- C2. THE ISOLATING CONTROL. The same λ with a closed domain is accepted, so C1 is
-- about the reference and not about annotating a binder at all.
def closedType : Term := prog{ let n = 3; let G = λ(a : Le 3 3) { () }; () }
example : progOk closedType = true := by native_decide

-- C3. And the scoping is a TELESCOPE: a domain naming the λ's OWN earlier binder
-- is bound, not free. This is the shape every recursor arm has (`ih`'s domain
-- mentions the predecessor to its left), so getting it wrong would reject the
-- whole recursor story rather than a corner of it.
def telType : Term := prog{ let G = λ(m : Nat, a : Le m m) { () }; () }
example : progOk telType = true := by native_decide

/-! ## §D. Equality sees the domains -/

-- `Term.beq` compares them structurally (via `Term.beq`, not `==`: the `BEq Term`
-- instance is declared below the mutual block this case lives in).
example : Term.beq (.lamR [(⟨0, "a"⟩, .const "Nat")] .unit)
                   (.lamR [(⟨0, "a"⟩, .const "Bool")] .unit) = false := by native_decide
example : Term.beq (.lamR [(⟨0, "a"⟩, .const "Nat")] .unit)
                   (.lamR [(⟨0, "a"⟩, .const "Nat")] .unit) = true := by native_decide

-- **The α-normalization half of §D went with `AlphaEq.lean`** (M28 cluster C).
-- Three assertions built `.lamR`s whose second binder's DOMAIN cited the first
-- (`telA`/`telB`, α-variants; `telC`, pointing at a free variable) and compared
-- them through `anTerm`, to pin that `anLamBinders` traverses the annotations
-- rather than letting the criterion degrade to structural equality on exactly the
-- terms it existed to compare. `FnDef.alphaEq` had one consumer — S26Fn's
-- macro-vs-hand-elaboration oracle — that consumer retired earlier in this
-- cluster, and a normalization nothing normalizes for is dead code whose tests
-- are tests of dead code. The domain traversal it exercised is still exercised,
-- by `Term.beq` above and by `telType`'s check in §C.

/-! ## §E. `fnElab`'s arm annotations — the boxed danger

    An arm is checked at the **motive instantiated at its constructor**, so its
    binders' domains are the residual telescope's with the scrutinee SUBSTITUTED.
    Two things follow, and the second is the one a naive transcription gets wrong:

      * `ih`'s domain is the motive at the PREDECESSOR — a term no source wrote;
      * and the trailing binders do NOT come through unchanged, because
        `absVar kv 0` abstracts the scrutinee over the whole nested Π, domains
        included. A parameter whose type mentions the decreasing one — the fuel
        bound `Le (Len *v) n`, which is exactly what §12 decision 8 blessed — is
        annotated `Le (Len *v) Z` in the base arm and `Le (Len *v) (S n')` in the
        step arm.

    The declaration below is that shape, minimal. The assertions compare against
    hand-written terms rather than against a second call of the derivation, so
    they would fail if the macro transcribed instead of substituting. -/

/-- The subject, as the PROGRAM it is (M28 D5). It used to be a `decl{ }` fed to
    `FnMacro.fnElab`; the `fn` statement lowers through exactly that function
    (Uni.lean's `ublk` rule calls `fnElabOrFail`), so the sealed term this section
    reads is the same term, and it is read back out of the binding the statement
    made rather than out of a second former holding the same declaration. -/
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
  match bndProgram with | .letIn _ t _ => some t | _ => none

/-- The declaration's own domain for `Hn`, as the header writes it: `Le (Len *v) n`
    with §6's marker, since `Hn` is capitalized. Written out because it is what a
    TRANSCRIPTION would have produced, and E2/F3b are the controls that say the
    elaboration produces something else. -/
def bndDeclHn : Term := .cmpT (Std.LeT (Std.lenT (.deref (.var ⟨1, "v"⟩))) (.var ⟨0, "n"⟩))

/-- The two arms of the emitted `natRec`, as annotated binder lists. -/
def bndArms : Option (List (Var × Term) × List (Var × Term)) :=
  match bndSeal with
  | some (.seal (.app (.app (.app (.const "natRec") _) (.lamR z _)) (.lamR s _)) _) => some (z, s)
  | _ => none

-- The shape first — assert the instrument before the conclusion.
example : (match bndArms with
           | some (z, s) => z.length == 2 && s.length == 4
           | none => false) = true := by native_decide

/-- `Le (Len *v) b`, at the positional `v` the residual telescope keeps. -/
def leLen (b : Term) : Term := Std.LeT (Std.lenT (.deref (.var ⟨1, "v"⟩))) b

-- E1. The bound binder, at each constructor. `Hn` is capitalized, so its domain
-- carries §6's marker — the annotation is the domain as written, marker and all.
example : (match bndArms with
           | some (z, s) =>
             let dec := (s.get! 0).1
             Term.beq (z.get! 1).2 (.cmpT (leLen (.ctorApp "Z" [])))
               && Term.beq (s.get! 3).2 (.cmpT (leLen (.ctorApp "S" [.var dec])))
           | none => false) = true := by native_decide

-- E2. …and neither is the DECLARATION's own domain, which is what a transcription
-- would have produced. This is the assertion the handoff's "`rest` is already a
-- telescope, so those come for free" would have failed.
example : (match bndArms with
           | some (z, s) =>
             !(Term.beq (z.get! 1).2 bndDeclHn) && !(Term.beq (s.get! 3).2 bndDeclHn)
           | none => false) = true := by native_decide

-- E3. `ih` is the motive at the predecessor: peel it at the residual telescope's
-- own binders and its bound reads `Le (Len *v) n2`, one successor BELOW the arm's
-- own. M26-C established that wrong-level `ih` is a type error rather than a
-- check (`S26Rec` §I); this is the macro's half of the same fact, and it is the
-- one that would compile and pass while being silently wrong.
example : (match bndArms with
           | some (_, s) =>
             let dec := (s.get! 0).1
             match piPeel [⟨1, "v"⟩, ⟨2, "Hn"⟩] (s.get! 1).2 with
             | .ok (tel, _) => tel.length == 2 && Term.beq (tel.get! 1).2 (leLen (.var dec))
             | .error _ => false
           | none => false) = true := by native_decide

-- E4. The predecessor binder itself is the scrutinee's own domain.
example : (match bndArms with
           | some (_, s) => Term.beq (s.get! 0).2 (.const "Nat")
           | none => false) = true := by native_decide

/-! ## §F. THE ONE CONVERSION (M27 α.1b)

    `sealFn` no longer descends the ascription to supply each binder a type. It
    compares the Π the λ STATES against the Π that was written (`piAgree`), and a
    recursor arm's leading binders — the predecessor and `ih` — are compared
    against what the recursor's premise gives them (`checkArm`).

    The second half is the one that matters. Once an arm ANNOTATES `ih`, an
    annotation taken on trust would let a body state the recursion at its own
    level and be handed it — `bad()` arriving through the door §8's guard used to
    hold, and the reason §7 could delete that guard at all is that `ih`'s type is
    derived rather than chosen.

    Every assertion below perturbs exactly ONE annotation of a program that
    checks, so each is a per-demand-site control rather than a rejection that
    might have had some other cause. -/

/-- The elaborated declaration, as a program: a `let` of the sealed recursor.

    The binder is CAPITAL since M31 Stage A, because that is what an elaborated
    declaration's binder now is (§2.1) — this hand-built term stands in for what
    the `fn` row emits, so it has to agree with it. F5, the accepting control, is
    what caught the disagreement: F1–F4 reject inside the seal, before the binding
    is reached, so only the control ever got as far as the mode backstop. -/
def bndProg (t : Term) : Term := .letIn ⟨900, "F"⟩ t .unit

/-- `bndProgram`'s sealed recursor with the step arm's `i`-th annotation replaced, and nothing else
    touched. `none` when the elaboration is not the shape this section reads. -/
def stepArmWith (i : Nat) (τ : Term) : Option Term :=
  match bndSeal with
  | some (.seal (.app (.app (.app (.const "natRec") mot) zArm) (.lamR s sb)) piT) =>
    some (.seal (.app (.app (.app (.const "natRec") mot) zArm)
                  (.lamR (s.set i ((s.get! i).1, τ)) sb)) piT)
  | _ => none

/-- The motive's body, read off the ascription the statement emitted, WITH the
    binder it is a body of: the seal's type is `Π (n : Nat) → R`, and every arm's
    type is an instance of that `R` at some constructor of `n`. -/
def bndR : Option (String × Term) :=
  match bndSeal with
  | some (.seal _ (.pi n _ R)) => some (n, R)
  | _ => none

/-- The step arm's predecessor binder. -/
def bndDec : Option Var := bndArms.map (fun p => (p.2.get! 0).1)

-- F0. THE BASELINE. Unperturbed, the elaborated declaration checks — so every
-- rejection below is the perturbation and not the program.
example : progOk bndProgram = true := by native_decide

-- …and the instrument, before the conclusion: `R` really is the motive body,
-- because `ih`'s derived annotation is exactly `R` at the predecessor. That
-- re-derives §E3 from the ASCRIPTION instead of from the arm, which is the
-- independent route to the same fact.
example : (match bndR, bndArms, bndDec with
           | some (n, R), some (_, s), some dec =>
             Term.beq (s.get! 1).2 (Term.substP n (.var dec) R)
           | _, _, _ => false) = true := by native_decide

-- F1. **`ih` AT THE ARM'S OWN LEVEL** — `R` at `S dec` where the premise gives
-- `R` at `dec`. This is precisely what §8's guard used to forbid by comparing
-- snapshots, arriving as an annotation instead of as a call, and it is refused by
-- the arm-binder rule rather than by anything downstream.
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

-- F3. **THE TRANSCRIPTION BUG, now caught by the build.** Annotate the fuel bound
-- at the PREDECESSOR's level rather than the arm's own — the plausible off-by-one,
-- and the shape a "`rest` comes for free" transcription would have produced a
-- whole family of. It is refused through `piAgree`, which is the other branch of
-- the new check.
example : (match bndDec with
           | some dec =>
             match stepArmWith 3 (.cmpT (leLen (.var dec))) with
             | some t => progRejects (bndProg t) "a domain the ascription does not bind it at"
             | none => false
           | none => false) = true := by native_decide

-- F3b. **THE UNINSTANTIATED ANNOTATION** — the transcription itself, rather than
-- an off-by-one near it: the arm annotated with the DECLARATION's own domain,
-- `Le (Len *v) n`, where the motive at this constructor gives `Le (Len *v) (S n')`.
-- This is the control that would have caught the handoff's "`rest` is already a
-- telescope, so those come for free", and it is in the battery for that reason.
--
-- **It is refused at the CONVERSION**, and where it fires is part of the claim.
-- The declaration's domain mentions the scrutinee `n`, which does not exist
-- inside an arm — so a closedness rejection was the other plausible outcome, and
-- would have been the conversion passing for the wrong reason. `piAgree` runs
-- before `checkRFnBody`, so the domains are compared before any body is entered,
-- and the message below is the comparison's own.
example : (match stepArmWith 3 bndDeclHn with
           | some t => progRejects (bndProg t) "a domain the ascription does not bind it at"
           | none => false) = true := by native_decide

-- F4. …and an ordinary trailing binder, mistyped outright.
example : (match stepArmWith 2
             (.borrowT "§_" (.app (.const "List") (.const "Bool"))
                       (.app (.const "List") (.const "Bool"))) with
           | some t => progRejects (bndProg t) "a domain the ascription does not bind it at"
           | none => false) = true := by native_decide

-- F5. THE ISOLATING CONTROL for the whole section: re-annotating a binder with the
-- type it already had leaves the program ACCEPTED. So F1–F4 are about the
-- disagreement, and not about the perturbation machinery having touched the term.
example : (match bndArms with
           | some (_, s) =>
             match stepArmWith 3 (s.get! 3).2 with
             | some t => progOk (bndProg t)
             | none => false
           | none => false) = true := by native_decide

/-! ### F6. A plain sealed λ, not a recursor — the `sealFn` half on its own -/

def fnTy : Term := prog{ Π (v : &mut List Nat) → Unit }

def annOk : Term := prog{
  let F = (λ(v : &mut List Nat) { *v := Nil; () } : %fnTy);
  () }
example : progOk annOk = true := by native_decide

-- The same λ, the same ascription, one annotation changed: refused. Before α.1b
-- this was ACCEPTED, because the binder's type came from the ascription and the
-- annotation was carried and never read.
def annBad : Term := prog{
  let F = (λ(v : &mut List Bool) { *v := Nil; () } : %fnTy);
  () }
example : progRejects annBad "a domain the ascription does not bind it at" = true := by
  native_decide

/-! ## §G. JUXTAPOSITION APPLICATION (M27 β)

    The document's grammar has one application form, `t t′`; the n-ary `f(a, …)`
    is the declaration era's telescope leaking into the term language, and it dies
    at δ. So `f a b` has to mean a call when `f` names a runtime function.

    **The surface does not decide this, and cannot.** `let finish = (λ (e : …). …)`
    and `let f = (… : …)` are both lowercase slots holding functions, and the first
    must be applied by ⇝ — its arguments are snapshots and proofs that a ⇒ read
    would MOVE — while the second binds Ω slots under ⇒. Nothing about the two
    spines differs syntactically. So β is a KERNEL rule, at `readR`'s `.app` case,
    beside the `runtimeRecSpine?` choice that was already being made there.

    **And the router is §7 cost 5's own distinction rather than a new test**: the
    two λs are "the same former in the document, two representations in the
    machine, because one substitutes and the other binds". A `Val.lam` substitutes;
    a `Val.rfn`, a σ with a signature, or a recursor spine binds. §G5 is the pair
    that makes that observable — the same source line, two λ representations, two
    arrows, two verdicts. -/

def juxSealTy : Term := prog{ Π (v : &mut List Nat) → Unit }

-- G1. A sealed function called by juxtaposition, in statement position.
def juxSeal : Term := prog{
  let F = (λ(v : &mut List Nat) { *v := Cons(9, Nil); () } : %juxSealTy);
  let x = Cons(1, Nil);
  let b = &m x;
  F b;
  let y = x;
  () }
example : progOk juxSeal = true := by native_decide
-- **ACCEPTANCE IS NOT THE CLAIM**, and the flip-validation of this section is
-- what said so. With the router disabled, `f b;` in statement position is a
-- discarded ⇝ neutral: nothing is called, and the program still CHECKS. The
-- differential does not catch it either — the router is one rule in `readR`, so
-- BOTH machines stop calling and go on agreeing. It is recorded rather than
-- quietly fixed, because it is phase A's per-demand-site finding arriving in a
-- new disguise: a statement-position call is a demand site that discards its
-- value, so nothing downstream is asked.
--
-- What discriminates is what the call LEAVES: the seal forgets the payload, so
-- after a real call the caller's `y` is an EXISTENTIAL, where an uncalled program
-- still holds the concrete list.
example : ((programEnvs juxSeal).filterMap (fun r => match r with
             | .ok e => (e.lookup "y").map (fun v => v.pretty.take 1)
             | .error _ => none)) = ["σ"] := by native_decide
-- …and both machines still correspond on it, which is the ordinary obligation.
example : Tests.S9Diff.progDiff juxSeal = true := by native_decide

-- …and the comma twin is the same program: same verdict, and both machines agree
-- on it, which is what says β changed how a call is WRITTEN and not what it does.
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
def juxRecMot : Term := prog{ λ (n : Nat). Π (v : &mut List Nat) → Unit }
def juxRecTy : Term := prog{ Π (n : Nat) → Π (v : &mut List Nat) → Unit }
def juxRec : Term := prog{
  let F = (natRec %juxRecMot
                 (λ(v : &mut List Nat) { () })
                 (λ(n2 : Nat, ih : Π (v : &mut List Nat) → Unit, v : &mut List Nat)
                    { match v { Nil => (), Cons(hd, tl) => { *hd := 0; ih tl; () } } }) : %juxRecTy);
  let x = Cons(1, Cons(2, Nil));
  let b = &m x;
  F 3 b;
  let y = x;
  () }
example : progOk juxRec = true := by native_decide
-- The same discriminator: `ih tl` and `f 3 b` really call, so the checking-mode
-- `y` is the seal's existential rather than the list the program wrote.
example : ((programEnvs juxRec).filterMap (fun r => match r with
             | .ok e => (e.lookup "y").map (fun v => v.pretty.take 1)
             | .error _ => none)) = ["σ"] := by native_decide
example : Tests.S9Diff.progDiff juxRec = true := by native_decide
-- It really recursed: the executing machine zeroes both elements.
example : (match runProgram juxRec with
           | .ok env => (env.lookup "y").map Val.pretty
           | .error _ => none) = some "Cons Z (Cons Z Nil)" := by native_decide

-- G3. A transparent runtime λ, called by juxtaposition.
def juxLam : Term := prog{ let G = λ(a : Nat) { S(a) }; let r = G 1; r }
example : progOk juxLam (.const "Nat") = true := by native_decide

/-! ### G5. THE ROUTER, made observable

    The same source line — `let y = mk (*v);` — under the two λ representations.
    A PURE λ is applied by ⇝, which reads the payload as a snapshot and leaves the
    borrow intact. A RUNTIME λ is applied by ⇒, which MOVES the payload out and
    leaves a hole, so the obligation audit refuses at return.

    This is the pair the whole rule rests on. Without it "juxtaposition is a call"
    would be a claim about the cases someone happened to write; with it, the two
    arrows are visible at one syntax. -/

def juxPure : Term := prog{
  fn Caller (v : &mut List Nat) -> Unit
  { let Mk = (λ (l : List Nat). l);
    let y = Mk (*v);
    () };
  () }
example : progOk juxPure = true := by native_decide

def juxRuntime : Term := prog{
  fn Caller (v : &mut List Nat) -> Unit
  { let Mk = λ(l : List Nat) { l };
    let y = Mk (*v);
    () };
  () }
example : progRejects juxRuntime "holds a hole (⊥) at return" = true := by native_decide

-- G6. Saturation, at the juxtaposition form (§12 decision 4 — the call event is
-- atomic, so a spine that stops short is an error and not a partial application).
def juxPartial : Term := prog{
  let F = (λ(a : Nat, b : Nat) { a } : Π (a : Nat) → Π (b : Nat) → Nat);
  let r = F 1;
  () }
-- The message is the call rule's own, not a parse failure: the spine reached the
-- callee and the callee's telescope is what refused it.
example : progRejects juxPartial "arity mismatch" = true := by native_decide

-- …and the saturated twin is accepted, so G6 is about the missing argument.
def juxSaturated : Term := prog{
  let F = (λ(a : Nat, b : Nat) { a } : Π (a : Nat) → Π (b : Nat) → Nat);
  let r = F 1 2;
  r }
example : progOk juxSaturated (.const "Nat") = true := by native_decide

-- G7. A RESERVED head stays a constructor, which is what keeps `S n` and a call
-- distinguishable without a token: the basis is closed, so the test is exact.
example : (match (prog{ let x = S 3; () } : Term) with
           | .letIn _ (.ctorApp "S" [_]) _ => true
           | _ => false) = true := by native_decide

-- G8. A CAPITAL head is never routed, in either position. §6.3 makes a capital
-- function-typed binder a SPEC parameter — cited, never called — so the spine
-- stays ⇝'s structured neutral. (`S26Modes` §B7 pins the type position; this is
-- the kernel-side guard that a body cannot reach the call rule through it.)
def juxCapital : Term := prog{
  fn JuxCapital (G : Π (x : Nat) → Nat, n : Nat) -> Id Nat (G n) (G n) { Refl };
  () }
example : progOk juxCapital = true := by native_decide

/-! ## §H. `[k]` decides which recursor is emitted (M27-δ)

    While `[k]` was a guard input, two definitions differing only in it could still
    be the same function — the hint said which parameter to police, not what to
    build. Since the guard died it is purely the scrutinee-selection hint, so it
    decides which recursor `fnElab` emits, and two definitions differing in it are
    two different terms.

    **This section used to be about `FnDef.alphaEq`** — that the round-trip
    criterion had been WIDENED to compare `dec`, and that the widening became
    correct at exactly the moment the guard died, asserted on this pair because a
    widening no pair exercises is indistinguishable from no widening at all. The
    criterion is gone (M28 cluster C, with `AlphaEq.lean`; its one consumer was
    S26Fn's oracle). What the pair still witnesses is the FACT the widening was
    tracking, which never belonged to the criterion: the hint is load-bearing on
    the output, so these are not two spellings of one function — one checks and
    the other is refused. -/

/-- The `[m]` spelling: the hint names the parameter the body actually matches on,
    so `fnElab` has a scrutinee to build the recursor from and the self-call becomes
    `ih` at the predecessor. -/
def hintM : Term := prog{ fn H [m] (n : Nat, m : Nat) -> Id Nat Z Z
  { match m { Z => Refl, S(m2) => H(n, m2) } }; () }

/-- The `[n]` spelling: **character for character the same function** — same name,
    same telescope, same return type, same body — differing in the hint alone. -/
def hintN : Term := prog{ fn H [n] (n : Nat, m : Nat) -> Id Nat Z Z
  { match m { Z => Refl, S(m2) => H(n, m2) } }; () }

example : progOk hintM = true := by native_decide
-- …and the twin is REFUSED, by the needle no other error produces.
example : progRejects hintN FnMacro.fnRefusedNeedle = true := by native_decide
-- …with the diagnosis intact, which is what makes this about `[k]` and not about
-- the body: the self-call's decreasing argument is not the predecessor the `S`
-- branch binds, because the branch that binds one is `m`'s and the hint named `n`.
example : progRejects hintN "is not the predecessor" = true := by native_decide

-- Written as PROGRAMS (M28 cluster C). These were two `FnDef`s and an
-- `fnElab`-returns-`.ok` differential; the pair is the same claim as a pair of
-- verdicts, and one of the two is now a rejection with a message rather than a
-- `false`. `bndD`, the last `decl{ }` in this file, followed in M28 D5 — §E/§F
-- read their sealed recursor out of `bndProgram`'s own binding instead.

end Dllbc.Tests.S27Lam
end
-- └── end of what was `S27Lam.lean` ───────────────────────────────────────────────

-- ┌── was `Dllbc/Tests/FnStmt.lean` ──────────────────────────────────────────────
section
/-!
# The `fn` statement's own hazards — what the grammar can get wrong

`fn` is a statement of the one grammar (Uni.lean): §8 says a declaration is a
`let`, §7 says its right-hand side is a seal over a recursor or a runtime λ, and
`fn f (…) -> R { … } ; rest` is that `let` written where a `let` is written.

## What this file used to be, and why it is a third of its old size

It was **the sweep's safety net** (M28 θ). While `decl{ … }` still produced an
`FnDef` value, the statement form could be held to it exactly:

    prog{ fn A …; fn B …; TAIL }   ==   progOf [declA, declB] (prog{ TAIL })

as `Term`s, by `==` — literal equality, not α-equivalence, because the statement
binds its slot at `progBase + next` and `progOf` binds the `i`-th declaration at
`progBase + i`, and those agree exactly when the statements are consecutive and
start a block. Four cases covered the shapes the lowering treats differently: a
non-recursive function and a caller, `[k]` on parameter 0, `[k]` NOT on parameter
0 (the permutation case the design exists for), and a dependent return type.

**The net's job was to police a migration, and the migration is over** (M28 D9).
`decl{ }` is deleted, so there is no second construction of the same term to
compare against — `fn` is the only way to write a function, and its output is
checked by the kernel from scratch at the seal (constraint 7). Each case's
underlying claim outlived it, in the language rather than in a comparison:

  * **the permutation** is `S23Direct.setSwap` (`swap_at` calls `set_at [i]`,
    whose decreasing parameter is second) and `S23Direct.pick` (`pick` calls
    `insert_at [k]`), both `progOk`, both with a negative twin at the same
    position;
  * **the dependent return type** is every flagship in the corpus;
  * **`[k]` on parameter 0** is most of the corpus;
  * **the refusal path** is `S6Call.zeroAll` — the same `[v]` function, rejected
    on `FnMacro.fnRefusedNeedle`, on "§12 decision 8" by name, and with
    `progOk = false` to say the sentinel fires at the BINDING rather than at a
    call. `S23Direct.borrowDecrease` says it again where the flagship's own `[v]`
    class is discussed.

What is left here is the two hazards that belong to the STATEMENT rather than to
any function written with it.
-/

open Dllbc

namespace Dllbc.Tests.FnStmt

/-! ## §A. Two `fn` chains composed through a `%` splice

    Sharing a prefix is ordinary let-chain composition — a Lean function taking the
    rest of the block and splicing it — and half the corpus is written that way.
    But each chain numbers its slots from `progBase`, so NESTING two of them makes
    the inner chain shadow the outer, and left alone that is not an error:
    measured before the check existed, `withA (withB …)` ACCEPTED with both names
    resolving to whichever function landed second. `bindFn` refuses it instead. -/

def withA (rest : Term) : Term := prog{ fn A (n : Nat) -> Nat { n }; %rest }
def withB (rest : Term) : Term := prog{ fn B (n : Nat) -> Nat { n }; %rest }

-- Nested: refused, by the same needle a refused lowering uses, naming the slot
-- and the fix.
example : progRejects (withA (withB (prog{ let r = A(1); let s = B(2); () })))
  FnMacro.fnRefusedNeedle = true := by native_decide
example : progOk (withA (withB (prog{ let r = A(1); let s = B(2); () }))) = false := by
  native_decide

-- The two shapes that are FINE, so the check above is not simply banning
-- composition: one chain declaring both, and a prefix whose tail declares nothing.
example : progOk (prog{
  fn A (n : Nat) -> Nat { n };
  fn B (n : Nat) -> Nat { n };
  let r = A(1); let s = B(2); () }) = true := by native_decide
example : progOk (withA (prog{ let r = A(1); () })) = true := by native_decide

/-! ## §B. The seal is ASCRIPTION, and its one confusable neighbour (M28 ξ)

    `seal(t, T)` is spelled `(t : T)`. The parenthesised-node property that made
    the old row unmistakable for an application is unchanged — an ascription closes
    at its own paren, so `(f : T) x` is the ascribed `f` APPLIED to `x`, not an
    ascription at a function type. What the spelling adds is that §5's definition of
    a declaration — a λ with its signature ascribed — is now the grammar rather
    than a comment beside it.

    The neighbour is `&mut`. `&mut (s : τ ~> S)` is the borrow type with a snapshot
    binder; drop the `~> S` and the ascription row would take it, making
    `&mut (v : List Nat)` a borrow of a SEAL. Measured before deciding: it parsed,
    silently, and failed downstream as an unrelated unbound-identifier error. It is
    refused at elaboration instead, which is not assertable as a test (it fails the
    build by design) and so is recorded here with its message:

        &mut (v : τ) is not a borrow type — the snapshot-binder spelling is
        `&mut (v : τ ~> S)`, where `S` is what the borrow OWES back … If you meant
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
example : ((prog{ let r = (λ (x : Nat). x : Π (x : Nat) → Nat) 3; () })
        == (prog{ let r = %ascribed 3; () })) = true := by native_decide

/-! ## §C. `[k]` naming a non-parameter is a LEAN error

    The one refusal that is cheap syntactically is the one the surface makes
    syntactically — the macro has to resolve `[k]` to an index anyway, so it says so
    at elaboration. Everything `fnElab` refuses is SEMANTIC (it needs the elaborated
    telescope type to see that `[v]` decreases through a borrow's payload, or that a
    scrutinee is neither `Nat` nor `List A`) and is deliberately NOT duplicated as a
    syntactic check: two implementations of one rule is one too many, and the copy
    would be the one that drifts.

    Not assertable as a test (it fails the build by design); recorded here so a
    reader knows which errors appear when. Writing
    `fn f [zzz] (n : Nat) -> Unit { () }` gives:

        fn: decreasing argument 'zzz' is not a parameter of 'f'
-/

end Dllbc.Tests.FnStmt
end
-- └── end of what was `FnStmt.lean` ───────────────────────────────────────────────

import Dllbc.Program
import Dllbc.Std
import Dllbc.StdLemmas
import Dllbc.PureMacro
import Dllbc.DeclMacro
import Dllbc.ProgMacro
import Dllbc.Tests.S9Diff

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
seal former, so no comptime RULE for the seal exists: `whnfV`, `nfV`, `convert`,
`substPure` and `hasType` are functions on `Val` and would need a new value
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
open Dllbc.StdLemmas (le_refl le_trans)

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
def a1 : Term := prog{ let f = seal(λ (x : Nat). x, Π (x : Nat) → Nat); () }
example : progOk a1 = true := by native_decide

-- A2. An ill-typed one is rejected, by an honest TYPING rejection naming both the
-- term and the ascribed type — not by getting stuck somewhere downstream.
def a2 : Term := prog{ let f = seal(λ (x : Nat). x, Π (x : Nat) → Bool); () }
example : progRejects a2 "does not have its ascribed type" = true := by native_decide

-- A3. Data seals: the same rule with no Π in sight.
def a3ok : Term := prog{ let a = seal(3, Nat); () }
def a3no : Term := prog{ let a = seal(3, Bool); () }
example : progOk a3ok = true := by native_decide
example : progRejects a3no "does not have its ascribed type" = true := by native_decide

-- A4. Phase A's stub, RETIRED BY M26-C, which is what it named. A borrow-moded
-- `u` is a function signature, and §5.4's audit is what checks a function against
-- one — so the sealed term has to be a runtime λ whose binders match it. Sealing a
-- PURE λ there is still refused, and now for the reason rather than for the phase:
-- `hasType` has no answer to a payload-owing Π, and pretending otherwise is the
-- one thing this rule must not do.
def a4 : Term := prog{ let f = seal(λ (x : Nat). x, &mut Nat); () }
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

def natIdT : Term := pure{ Π (x : Nat) → Nat }

-- as a call argument, where the mint happens inside `processArgs`
def a6a : Term := prog{
  fn takesFn (g : %natIdT) -> Unit { () };
  takesFn(seal(λ (x : Nat). x, Π (x : Nat) → Nat)); () }
example : progOk a6a = true := by native_decide

-- inside a constructor argument
def a6b : Term := prog{ let l = Cons(seal(3, Nat), Nil); () }
example : progOk a6b = true := by native_decide

-- in return position: a function whose result IS a sealed function. The audit
-- reads the σ's type out of `sctx` and converts — O(statement), the §5 point 2
-- shape at a boundary rather than at a citation.
def a6c : Term := prog{
  fn mkId () -> %natIdT { seal(λ (x : Nat). x, Π (x : Nat) → Nat) };
  () }
example : progOk a6c = true := by native_decide
-- …and the same in return position with the wrong ascription is caught at the
-- node, before the return type is ever consulted.
def a6d : Term := prog{
  fn mkId () -> %natIdT { seal(λ (x : Nat). x, Π (x : Nat) → Bool) };
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
  fn a7 (n : Nat) -> Unit { let f = seal(match n { Z => Z, S(k) => k }, Nat); () };
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
  match (do let v ← readC 3000 tm; let t ← readC 3000 ty; hasType 3000 v t).run (seedPure [] []) with
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
  [ (pure{ λ (x : Nat). x },            pure{ Π (x : Nat) → Nat })
  , (pure{ λ (x : Nat). x },            pure{ Π (x : Nat) → Bool })          -- ✗
  , (pure{ λ (x : Nat). S x },          pure{ Π (x : Nat) → Nat })
  , (pure{ λ (x : Nat). λ (y : Nat). x }, pure{ Π (x : Nat) → Π (y : Nat) → Nat })
  , (pure{ λ (x : Nat). λ (y : Nat). x }, pure{ Π (x : Nat) → Nat })         -- ✗
  , (n3, natT)
  , (n3, .const "Bool")                                                       -- ✗
  , (.ctorApp "Nil" [], listNatT)
  , (.ctorApp "Cons" [n3, .ctorApp "Nil" []], listNatT)
  , (.ctorApp "Refl" [], .idT natT n3 n3)
  , (.ctorApp "Refl" [], .idT natT n3 n4)                                     -- ✗
  , (StdLemmas.le_refl, StdLemmas.le_refl_ty)
  , (StdLemmas.le_refl, StdLemmas.id_sym_ty)                                  -- ✗
  , (StdLemmas.id_sym, StdLemmas.id_sym_ty)
  , (StdLemmas.add_zero, StdLemmas.add_zero_ty)
  -- The §2.1 flagship: congruence, whose whole content is that an abstract
  -- function's applications are one term. Sealing it must cost exactly what
  -- checking it costs.
  , (StdLemmas.id_congr, StdLemmas.id_congr_ty) ]

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
example : sealChk (StdLemmas.le_refl) (StdLemmas.id_sym_ty) = false := by native_decide

/-! ## §C. Application of a value callee

    §2's two rows, chosen by what the slot holds. A negative control per rule
    branch, per §6.2's lesson that a rule branch nobody probes is a rule branch
    nobody checked. -/

def vlam : Val := .lam (.const "Nat") (.ctor "S" [.pvar 0])

-- C1. **Body known ⟹ unfold.** A literal λ callee β-reduces, so the caller knows
-- the result exactly: `y ↦ 3`, not an existential.
def c1 : Term := prog{ let f = λ (x : Nat). S x; let y = f(2); () }
example : progOk c1 = true := by native_decide
example : tailEnv c1 [("f", vlam), ("y", Val.nat 3)] = true := by native_decide

-- C2. **Body withheld ⟹ the type's promise and nothing more.** Seal the same λ
-- and the same call yields an opaque σ. This is §5 point 4 made mechanical: what
-- the caller keeps is exactly what was written in the seal.
def c2 : Term := prog{ let f = seal(λ (x : Nat). S x, Π (x : Nat) → Nat); let y = f(2); () }
example : progOk c2 = true := by native_decide
example : tailEnv c2 [("f", .sym 0), ("y", .sym 1)] = true := by native_decide

-- C3. Two calls are two events, and are NOT identified (§2.2's requirement on the
-- runtime column): σ1 and σ2 are distinct, each with its own type instance.
def c3 : Term := prog{
  let f = seal(λ (x : Nat). S x, Π (x : Nat) → Nat); let y = f(2); let z = f(2); () }
example : tailEnv c3 [("f", .sym 0), ("y", .sym 1), ("z", .sym 2)] = true := by native_decide

/-! ### C4–C8. The negative controls, one per rule branch -/

-- Partial application: refused, not curried (§12 decision 4).
def c4 : Term := prog{ let f = λ (x : Nat). λ (y : Nat). x; let z = f(2); () }
example : progRejects c4 "partial application" = true := by native_decide
-- …and the same refusal on the abstract side, which is the branch that matters
-- for phase C (a σ : Π under-applied is a closure holding its arguments).
def c5 : Term := prog{
  let f = seal(λ (x : Nat). λ (y : Nat). x, Π (x : Nat) → Π (y : Nat) → Nat);
  let z = f(2); () }
example : progRejects c5 "partial application" = true := by native_decide

-- Over-application.
def c6 : Term := prog{ let f = λ (x : Nat). x; let z = f(2, 3); () }
example : progRejects c6 "too many arguments" = true := by native_decide

-- A mistyped argument, on both branches.
def c7 : Term := prog{ let f = λ (x : Nat). x; let z = f(Nil); () }
example : progRejects c7 "does not have its parameter type" = true := by native_decide
def c8 : Term := prog{ let f = seal(λ (x : Nat). x, Π (x : Nat) → Nat); let z = f(Nil); () }
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
def c11 : Term := prog{ let x = 3; let b = &mut x; let z = x(2); () }
example : progRejects c11 "is not a function value" = true := by native_decide

/-! ### C12. The `ih` shape

    A Π-typed TELESCOPE PARAMETER, applied inside a body. Checking-side this is a
    `σ : Π` — "the sealed view", which is exactly what phase C's `ih` will be — and
    the call is abstract application at that Π. Executing-side the parameter holds
    the caller's actual λ and the same syntax β-reduces. One form, two rules, no
    branch in the program. -/

def apply1 : Term := prog{
  fn apply1 (g : Π (x : Nat) → Nat, n : Nat) -> Nat { g(n) };
  () }
example : progOk apply1 = true := by native_decide

-- The caller supplies a literal λ; checking mode learns only `Nat` about the
-- result (the call is opaque), which is §5.3's promise, unchanged by the callee
-- being applied through a variable inside.
def c12 : Term := prog{
  fn apply1 (g : Π (x : Nat) → Nat, n : Nat) -> Nat { g(n) };
  let f = λ (x : Nat). S x; let r = apply1(f, 2); () }
example : progOk c12 = true := by native_decide
-- `tailEnv` drops the program's own function binding, so the expected Ω is the
-- one this assertion always had — `r ↦ σ0` and not `σ1`.
example : tailEnv c12 [("f", vlam), ("r", .sym 0)] = true := by native_decide

-- The negative control for the parameter branch: a body that under-applies its
-- Π-typed parameter is rejected at the callee's own check, not at a caller's.
def apply1bad : Term := prog{
  fn apply1bad (g : Π (x : Nat) → Π (y : Nat) → Nat, n : Nat) -> Nat { g(n) };
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
  fn needsEq (n : Nat, h : Id Nat n 3) -> Unit { () };
  let f = λ (x : Nat). S x; let y = f(2); needsEq(y, Refl); () }
def c13s : Term := prog{
  fn needsEq (n : Nat, h : Id Nat n 3) -> Unit { () };
  let f = seal(λ (x : Nat). S x, Π (x : Nat) → Nat); let y = f(2); needsEq(y, Refl); () }
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

def sigLemTy : Term := pure{ Π (x : Nat) → Σ (h : Le x x) → Le x x }
def sigLem : Term := pure{ λ (x : Nat). Pair (le_refl x) (le_refl x) }

def c14 : Term := prog{
  let f = seal(%sigLem, %sigLemTy);
  let p = f(2);
  elim p return (λ (w : Σ (h : Le 2 2) → Le 2 2). Le 2 2) { Pair (a) (b) => le_trans 2 2 2 a b } }
-- The program's RESULT is the projection, so its return type is what the audit
-- checks it at — stated as `progOk`'s second argument, where the old form stated
-- it as the wrapper declaration's `-> Le 2 2`.
example : progOk c14 (pure{ Le 2 2 }) = true := by native_decide

-- The negative control has to be demanded to be a control: a `let`-bound proof is
-- never typed until something asks for its type (readC computes, it does not
-- check), so the wrong projection is only caught when the AUDIT wants it. Stated
-- because the vacuous version of this test passed, and would have looked fine.
def c14bad : Term := prog{
  let f = seal(%sigLem, %sigLemTy);
  let p = f(2);
  elim p return (λ (w : Σ (h : Le 2 2) → Le 2 2). Le 3 2) { Pair (a) (b) => a } }
example : progRejects c14bad "does not have return type" (pure{ Le 3 2 }) = true := by native_decide

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
    ordinary arithmetic*: after `let a = seal(3, Nat); let b = add a 1` the
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
def diffOld (table : List FnDef) (body : Term) : Bool :=
  match runExec table body with
  | .error _ => false
  | .ok ce => (symEnvs false table body).any
      (fun r => match r with | .ok se => instanceOf se ce | .error _ => false)

/-! ### D1. The counterexample that names the new case -/

def d1 : Term := prog{ let a = seal(3, Nat); let b = add a 1; () }
example : progOk d1 = true := by native_decide
-- The old relation calls this a counterexample. It is not one: the two
-- environments agree at σ0 := 3.
example : diffOld [] d1 = false := by native_decide
example : diffC   [] d1 = true  := by native_decide

/-! ### D2. The four shapes constraint 6 asks for, all GREEN -/

/-- A callee whose result the checker knows only as a σ — so the seal below sits
    at a SYMBOLIC value, not a concrete one.

    **KEPT AS A DECLARATION, and the EXECUTING machine is why** (M28 ν). This
    section runs each shape concretely, and a nullary `fn` lowers to a runtime λ
    binding nothing — which `λr` refuses, because a thunk makes ι ambiguous. So a
    program that DECLARES a nullary function checks (the seal mints a σ without
    ever entering the λ) and cannot be RUN, and D2b's concrete side would fail
    before the relation was consulted. It rides in the table instead, which is what
    `Program.lean` documents that parameter as being for. `apply1` below has arity
    two and needs no such treatment — its shape IS self-contained now, which is how
    the difference was located. -/
def giveThree : FnDef := decl{ fn giveThree () -> Nat { 3 } }

-- seal at a concrete value
def d2a : Term := prog{ let a = seal(3, Nat); let b = a; () }
-- seal at a symbolic value (the body reads a call's fresh existential)
def d2b : Term := prog{ let n = giveThree(); let a = seal(add n 1, Nat); let b = add n 1; () }
-- a sealed function callee, passed and called
def d2c : Term := prog{
  let f = seal(λ (x : Nat). S x, Π (x : Nat) → Nat); let y = f(2); let z = f(5); () }
-- a transparent function callee, passed to a declared fn and called inside it
def d2d : Term := prog{
  fn apply1 (g : Π (x : Nat) → Nat, n : Nat) -> Nat { g(n) };
  let f = λ (x : Nat). S x; let r = apply1(f, 2); let s = f(7); () }

def shapes : List (List FnDef × Term) :=
  [ ([], d2a), ([giveThree], d2b), ([], d2c), ([], d2d) ]

example : shapes.all (fun p => progOk p.2 (.const "Unit") p.1) = true := by native_decide
example : shapes.all (fun p => diffC p.1 p.2) = true := by native_decide

/-! ### D3. Harness liveness — the relation must be able to say NO

    A counterexample-finder that has never found its counterexample is
    unvalidated (S9Diff's own standing rule). The extended relation is checked
    against a concrete run that genuinely disagrees: same symbolic side, a
    concrete side that adds 2 where the checker's σ-instance adds 1. -/

def d3mutant : Term := prog{ let a = 3; let b = add a 2; () }

example :
  (match symEnvs false [] d1, runExec [] d3mutant with
   | [.ok se], .ok ce => instanceOfComputed se ce
   | _, _ => true) = false := by native_decide
-- …and it says YES to the honest pairing, so the NO above is discrimination, not
-- a broken relation.
example :
  (match symEnvs false [] d1, runExec [] d1 with
   | [.ok se], .ok ce => instanceOfComputed se ce
   | _, _ => false) = true := by native_decide

/-! ## §E. `Qed` — the payoff, measured

    §5's second claim: `let cert = seal ⟨enormous proof⟩ ⟨statement⟩` mints one σ
    at the statement, and every citation afterwards is a σ-reference that `hasType`
    answers by reading the statement, never descending the proof. The measured
    certificate costs — "a reject costs the same as an accept", the audit descents
    — become O(statement).

    The subject is `count_swapA`, the largest proof in `StdLemmas` (9156 term nodes
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

def big : Term := StdLemmas.count_swapA
def bigTy : Term := StdLemmas.count_swapA_ty

/-- `let c = rhs ; useIt(c) ; … ; ()` with `k` citations. Built rather than
    written out so the citation count can be swept: the claim is about the SLOPE,
    and one hand-written pair would only show a point. -/
def citeK (k : Nat) (rhs : Term) : Term :=
  let c : Var := ⟨0, "c"⟩
  let rec go : Nat → Term
    | 0 => .unit
    | n + 1 => .seq (.call "useIt" [.var c]) (go n)
  .letIn c rhs (go k)

/-- The citations, with their callee declared above them. The built tail is
    spliced with `%`, and the `.call "useIt"` nodes inside it are retargeted onto
    the slot by `bindFn` — which is the same mechanism a hand-written call goes
    through, so a swept program and a written one mean the same thing. -/
def citeProg (k : Nat) (rhs : Term) : Term := prog{
  fn useIt (h : %bigTy) -> Unit { () };
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
  fn useIt (h : %bigTy) -> Unit { () };
  let c = seal(%StdLemmas.le_refl, %bigTy); useIt(c); () }
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

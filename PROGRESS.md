# Progress

## Current state (2026-04-16)

Phase 1 active. Full Och was just restructured: the bundled `μ` binder has
been split into separate `ι` (self-type) and `fix` (recursive type)
constructors. `lake build` compiles. Simple Och (`lean/Och/Simple/`) is
untouched and remains the proven-sound metatheory reference.

**`dtrue ⊑ dBool` and `dfalse ⊑ dBool` now pass**, along with the negative
`dBool ⊑ dtrue = false` and the full DBool concEval suite (21 examples,
zero `sorry`). See the agent log entry below for what changed and what's
next (DNat still hits the fuel ceiling).

### Agent phase1-coinductive-seen, 2026-04-16

Picked: `dtrue ⊑ dBool` (the central marker).

Found that `subCheckNF` was already accepting it — but only because the
`[fix-ann]` RHS rule (`a ⊑ fix A. body ← a ⊑ A`) made *every* term a subtype
of *every* `fix Type. _`, including `Nat_ ⊑ dBool` and `dBool ⊑ dtrue`. The
annotation `A` is the *type* of the recursion variable, not an upper bound
on the fixpoint, so this rule was unsound and masked the real obstruction.

Removing it exposed the actual gap: the recursive `dtrue ⊑ dBool` subgoal
that reappears in contravariant domain position couldn't be discharged
because `lam`/`app` reset the coinductive assumption set to `[]`. The fix
is the standard Brandt-Henglein discipline:

  - `seen` is threaded through `lam`/`app` instead of reset.
  - Only *productive* steps (fix-unfold, ι-unfold, iotaIntro) extend `seen`.
  - Annotation-widening steps inherit `seen` but never extend it; the
    `.iota`/`.fix` arms in `neutralType` (which silently re-introduced
    ann-widening with the inherited `seen`) are removed.
  - A new `[unfoldIotaL]` arm peels `ι` on the left so `ι_dtrue ⊑ M`
    reduces to its body instead of dead-ending at the annotation.
  - Degenerate `ι A. self` / `fix A. self` (body = `bvar 0`) skip the
    unfold path so they don't close trivially via the assumption set.

After this, all 21 DBool examples close by `native_decide`, including the
negatives (`dBool ⊑ dtrue`, `dtrue ⊑ dfalse`, `dfalse ⊑ dtrue` all
`= .ok false`). `Nat_ ⊑ dBool` and `Type ⊑ dBool` are correctly rejected.

Next obvious target: `dzero ⊑ dNat` runs out of fuel at 200. The DNat
encoding has a Scott-style eliminator whose successor case applies the
predecessor, so unfolding generates much larger terms than DBool. Likely
needs either a sharing-aware `seen` lookup (current `==` is structural on
the unfolded terms) or a smarter unfold strategy that doesn't substitute
the full fixpoint into the successor branch.

### Agent phase1-abseval-museen, 2026-04-16

Picked: `dzero ⊑ dNat`.

Root cause was not subCheckNF at all: `absEvalVal dNat` itself diverged
at any fuel. The `muSeen` cycle check in absEval's app-of-fix/iota arms
compared `(term, arg)` pairs by `==`, but every recursive descent goes
under fresh binders, so both the recursive term and its argument pick up
de-Bruijn shifts and the comparison never fires. Replaced the syntactic
match with a length-based cutoff (one unfold then stuck); subCheckNF's
own L/R rules handle the structural recursion soundly from there.

After that, `dzero ⊑ dNat`, `true_ ⊑ dNat = false`, and the previously
mis-tracked `dzero ⊑ done_ = false` all close at fuel 200. The remaining
DNat tests (`done_/dtwo/dthree ⊑ dNat` and `dNat ⊑ dzero`) are now
*reachable* but blow up: iotaIntro substitutes the closed `dNat` term for
its own self-reference, so each iota-L unfold roughly squares the term
size. This is a representation problem (eager-substitution de Bruijn),
not a missing rule — the obvious fix is an NbE/closure-style evaluator
where substitution is delayed. Also added the missing `body == bvar 0`
guard to fix-R that the verifier flagged.

26 → 25 markers (3 examples closed, 1 negative test corrected from
spurious-true to correct-false).

### Agent phase1-trans-exhaustive, 2026-04-16

Picked: the three `checkTrans` exhaustive transitivity searches in
Tests.lean (smallExprs/stdExprs/edgeExprs). They were sorried after the
μ → ι/fix split because the rule set changed; under the seen-discipline
rework (loop above) all 9³ + 11³ + 11³ triples now satisfy
`a ⊑ b ∧ b ⊑ c → a ⊑ c` with no counterexample.

Also made absEval total on stuck recursive heads: when the muSeen
cutoff fires (or any neutral-spine head can't be typed as an arrow) the
catch-all now returns the stuck application with placeholder type
`Type` instead of erroring with "not callable". This doesn't yet unlock
`Array_ dzero T = Unit_` because the inner β domain check `dzero ⊑ dNat`
sees a *different* normal form of dNat (normalised at non-empty muSeen
inside the fix-Array unfold) than the standalone check does — absEval's
normal form is muSeen-dependent, so it isn't canonical. The Array/Vec
wall is therefore the same NbE/closure-representation problem already
flagged for `done_ ⊑ dNat`, just one indirection deeper.

25 → 22 markers (3 transitivity examples closed).

### Agent phase1-neutral-head-gate, 2026-04-16

Picked: `Array_ dzero Nat_ = Unit_` (Array.lean) and the `Vec Nat_`
normalisation tests, all of which cited "stuck DNat elim on abstract n"
— exactly the absEval recursive-head problem.

The previous depth-1 muSeen cutoff stopped *every* recursive-head
application after one unfold, which prevented `Array_` (a fix) from
unfolding and *then* its argument `dzero` (an ι) from unfolding in the
same chain. Bumping the depth bound made `dzero ⊑ dNat` blow up, so
that's not the lever.

The actual termination criterion is the *argument*, not the depth: a
recursive head applied to a *neutral* (bvar-headed spine) cannot make
progress — the eliminator is stuck on an abstract scrutinee — whereas
applied to a *value* it consumes one constructor layer per unfold and
terminates as long as the value is finite. Added
`Expr.hasNeutralHead` and gated the ι/fix-in-app unfold on
`!arg.hasNeutralHead` (with a high muSeen depth bound kept only for
the degenerate `(fix f. f) v` case).

After this `Array_ dzero Nat_` reduces to `Unit_` (the recursive
`Array_ pred T` in the successor branch stays stuck because `pred` is
a bvar), and `Vec Nat_` normalises (so its negative subtyping tests
close). Everything that uses `done_/dtwo` as a concrete index is still
blocked by the `done_ ⊑ dNat` domain-check blowup inside the β step.

22 → 19 markers (Array_ dzero = Unit, Vec Nat ⊄ Nat, Nat ⊄ Vec Nat).

### Agent phase1-drop-domain-check, 2026-04-16

Picked: the four remaining `Array_ done_/dtwo` markers (Array.lean) and
`dNat ⊄ dzero`.

Two absEval changes:

  1. β-reduce unconditionally. The `(λx:A. b) v` arm previously did a
     `subCheckNF v A` domain check before substituting, which forced
     `(λn:dNat. …) done_` (inside the Array_ unfold) to discharge
     `done_ ⊑ dNat` *during normalisation* — exactly the goal
     subCheckNF was being called to set up. β is type-blind and the
     subCheckNF caller only consumes the value, so dropping the check
     loses inferred-type precision but unblocks normalisation.

  2. Re-add the syntactic head-`==` muSeen check alongside the
     neutral-arg gate. After dropping the domain check, normalising
     `Array_ dtwo` exposes the `(dsucc m) → Type` self-reference in
     dsucc's body: m gets the *value* `done_NF`, the neutral-arg gate
     doesn't fire, and the depth-16 backstop alone makes the term grow
     ~16×. The closed top-level `dsucc` doesn't shift under binders,
     so head-`==` against muSeen fires after one unfold and stops it
     cleanly.

Closes Array.lean: testArr1 ⊑ Array_ done_ Nat, testArr2 ⊑ Array_ dtwo
Nat, unit_ ⊄ Array_ done_ Nat, the (Array_ (dsucc dzero) Nat).isOk
smoke test, plus two new positive `Array_ done_/dtwo` reduction
checks. Closes DNat.lean: dNat ⊄ dzero.

Known incompleteness introduced: `done_ ⊑ dNat` (and dtwo, dthree)
now return `.ok false` instead of timing out. The head-`==` cutoff
leaves a stuck `(dsucc dzero)` inside done_NF's type annotation,
while iotaIntro on the dNat side substitutes the *evaluated* done_NF
(an ι value) for `self`; the two non-canonical normal forms of the
same term then meet in contravariant position and subCheckNF can't
equate them. This is incompleteness (a valid subtype rejected), not
unsoundness. Documented in the in-file TODO; the obvious fix is
either canonical NbE normal forms or a subCheckNF rule that
re-evaluates a stuck recursive-head application before falling
through to neutralType.

19 → 14 markers (5 closed, 2 new positive Array_ tests added).

### Agent phase1-stuck-head-reeval, 2026-04-16

Picked: `testVec1 ⊑ Vec Nat` and the `appendArrays` typing assertion.

Added a stuck-recursive-head re-evaluation rule to subCheckNF: when
either side is `app f arg` with `f = .fix/.iota` (i.e. absEval's
muSeen cutoff left a recursive head un-unfolded — *not* a genuinely
neutral bvar-headed term), unfold it once and recurse with the
seen-set extended. This sits in two places: a dedicated `_, .app
(.fix/.iota …) _` arm right after `unfoldFixR` (so it fires before
the LHS `.fix/.iota` arms — needed for transitivity over edgeExprs),
and inside `neutralType`'s `.app` arm for the LHS direction. Without
this the type-widening fallback collapsed `(dsucc dzero)` to `dNat`
and `(Array_ pred T)` / `(dadd n m)` to `Type`, losing all index
information.

Closes:
  Vec.lean:    testVec1 ⊑ Vec Nat
  Array.lean:  appendArrays ⊑ (T → n → m → Array n T → Array m T
                                 → Array (dadd n m) T)
               — Array.lean now has zero `sorry`.

`done_ ⊑ dNat` is still open: the re-eval rule lets subCheckNF
explore further than before (`.ok false` at fuel ≤150, exponential
at 200) but iotaIntro on dNat still substitutes the closed `dNat`
term for every `:dNat` ascription, so the search fans out before
seen can close it. Same NbE/closure-representation fix as before.

14 → 12 markers.

### Agent phase1-appendvec-northstar, 2026-04-16

Picked: harvest the markers the stuck-head re-eval rule unblocked.

Closes (no checker changes — pure harvest from f04721c):
  Vec.lean:   appendVec ⊑ (T → Vec T → Vec T → Vec T)  — the
              "north star" abstract appendVec test
              concEval (disZero (unpack vecResult)) = false_
              unpack vec1 ≠ dtwo
  Tests.lean: rewrapped (testVec1 : Vec Nat) ⊑ Vec Nat

`appendVec_wrong` (Vec:135) is still accepted: the checker doesn't
yet distinguish `dadd n1 n1` from `dadd n1 n2` under abstract n1,n2
— both reduce to stuck applications of the same closed `dadd` head
and the structural `app, app` rule accepts `n1 ⊑ n2` when both are
bvars. That's a real precision gap (the test is the right
assertion); fixing it likely needs the `app, app` rule to demand
argument *equality* (not just LHS ⊑ RHS) when the head is opaque.

12 → 8 markers.

## Open `TODO[mega-loop]` markers

Agents should run `grep -rn "TODO\[mega-loop\]" lean/` for the current list.
At time of writing there are 11 markers, spanning:

- Dependent-intro tests (`dtrue ⊑ dBool`, `dzero ⊑ dNat`, etc.)
- Negative-check re-verifications
- Array-over-DNat smoke tests
- Transitivity exhaustive checks

## Session log

Agents: append a brief session summary below. What you changed, what you
tried, what blocked you, what the next agent needs to know. Be specific —
file names, markers closed, definitions changed.

---

### phase1-array-dnat-swap (2026-04-14)

**Encoding swap, not a marker close.** Replaced Church-Nat-indexed Array_
with dNat-indexed Array_. The transitional `Array_dnat` is gone; the name
`Array_` now refers to the dNat version. `Vec`, `mkVec`, `appendVec`,
`appendArrays` all moved to dNat indices. `Tests.lean` §6.2 abstract-vec
tests ported. Added `dadd` in Std/Array.lean (was no dNat addition before).

**Test disposition.** Most Vec/Array tests that previously passed via
`native_decide` under Church-Nat are now sorry'd with TODO[mega-loop]
markers. The root obstruction is consistent: the motive
`λn:dNat. λarr:(Array_ n Nat_). _` has a binder whose body
`Array_ n Nat_` evaluates by unfolding Array_'s outer `fix` and then
running DNat's eliminator on the bvar `n`, which is stuck. The old
Church-Nat version did the analogous stuck reduction but absEval silently
admitted it; under the new strict absEval those tests fail honestly.

**Specific flips of intent:**
- `appendArrays` type-check test flipped from `≠ .ok true` to `= .ok true`
  (sorry'd). Under Church-Nat the negative assertion was expressing the
  encoding's limitation; the whole point of dNat indexing is that the
  positive assertion should hold once the mega-loop is closed.
- `appendVec` type-check similarly flipped. `appendVec_wrong` stays as
  `≠ .ok true` — it's a negative assertion that survives the swap.

**Live tests kept:**
- concEval tests on `appendArrays [1,2] [3] = [1,2,3]` in Std/Array.lean.
- isZero-checks, disZero computation tests in Std/DNat.lean (unchanged).
- All non-Vec/Array integration tests in Tests.lean.

**Nothing was trivialised.** No test was swapped from a succ-case to a
zero-case to dodge the reduction (e.g. `Array_ done_ T` stayed as
`Array_ done_ T`, not `Array_ dzero T`).

**Nothing was deleted.** Every Church-Nat test has a dNat analogue at
parity.

**Sorry count added:** ~17 new TODO[mega-loop] markers
(6 in Std/Array.lean, 12 in Std/Vec.lean, 2 in Och/Tests.lean).

**Downstream fallout noticed:** none. `Std/Sigma.lean`, `Std/Pair.lean`
etc. don't reference Array_ or Vec. `Simple/` is untouched (directive).

**Next agent:** the central obstruction is DNat's Scott-style eliminator
on a neutral bvar. If the eliminator were Church-with-ι (per
`docs/research/self-types-for-och.md`), `Array_ n T` would normalize
under an abstract n binder via dependent elimination. That's a
structural DNat redesign — orthogonal to, but unblocking, this swap.
`lake build` passes.

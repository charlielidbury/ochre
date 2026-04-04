# Suggestions

The current goal is proving soundness of Och. Here is the dependency chain
and priority order for the remaining `sorry`s.

## Phase 1: Foundation — fuel monotonicity ✅ COMPLETE

Both `absEval_fuel_mono` and `subCheckNF_fuel_mono` are proved. The proof
required eliminating normalization-with-fallback patterns in subCheckNF (see
PROGRESS.md for details). The mutual dependency between the two theorems is
resolved via a combined `fuel_mono` theorem proved by induction on fuel.

## Phase 2: VCompat lemmas (Soundness.lean)

These three lemmas are needed by the main soundness theorem. They should be
tackled after `absEval_fuel_mono` is done.

### `VCompat.from_type_sub_gen` (Soundness.lean:164)
When `subCheckNF fuel ctx seen Type tau = true`, then `VCompat n v tau` for
all `v` and `n`. The key insight: `Type` is the top type, so anything that
accepts `Type` as a subtype must accept everything.

Approach: induction on `fuel`, case analysis on `tau`. The `seen` parameter
needs the callback `hseen` for cycle-breaking.

### `VCompat.from_self_intro_gen` (Soundness.lean:185)
When `subCheckNF` succeeds for `sigma <: mu ann body` and `sigma` is not
itself a mu, VCompat holds. This handles the equi-recursive self-intro case.

Approach: induction on `fuel`, unfold `subCheckNF` to see that it unfolds the
mu and recurses. Use the `hseen` callback for the `seen` set.

### `VCompat.adequacy` (Soundness.lean:209)
The bridge lemma: if `VCompat n v sigma` and `subCheckNF` says `sigma <: tau`,
then `VCompat n v tau`. This is the key lemma connecting the logical relation
to the algorithmic checker.

Approach: case analysis on `sigma` and `tau`, using the structural lemmas in
Subtyping.lean. This may need the subtyping helper lemmas (Phase 3) depending
on the proof strategy.

## Phase 3: Subtyping helper lemmas (Subtyping.lean)

Five structural lemmas about `subCheckNF` that decompose successful checks.
All are marked "needs update for new mutual absEval/subCheckNF". These are
relatively mechanical — unfold the definition, handle the cases.

- `subCheckNF_lam_lam_body` (line 127)
- `subCheckNF_lam_impossible` (line 140)
- `subCheckNF_mu_mu_body` (line 151)
- `subCheckNF_type_left_target` (line 159)
- `subCheckNF_neutral_inferType` (line 167)

These may or may not be needed for the main soundness proof. They were written
for an earlier proof architecture. Consider whether the main proof actually
uses them before investing time here.

## Phase 4: Main soundness theorem (Soundness.lean:233)

Once Phases 1-2 are done (and possibly Phase 3), the main theorem should be
approachable:

```lean
theorem soundness
    (fuel : Nat) (e : Expr) (v : Expr) (tau : NfExpr) (n : Nat)
    (h_conc : concEval fuel e = some v)
    (h_abs : absEval fuel [] [] e = .ok tau)
    : VCompat n v tau.val
```

Approach: induction on `fuel`, case split on `e`. For each syntactic form:
- Use `h_conc` to determine what `v` looks like
- Use `h_abs` to determine what `tau` looks like
- Construct the appropriate VCompat disjunct

## Known hazards

- **subCheckNF transitivity is FALSE** (counterexample in Tests.lean). Do not
  assume it.
- **subCheckNF top-universality is FALSE**. `Type <: tau` does NOT mean all
  values inhabit `tau`.
- **Never weaken tests.** If a proof doesn't go through, the definitions or
  theorem statement may be wrong. Fix those, not the tests.
- **Check precondition satisfiability.** Any theorem change must be verified
  with `native_decide` witness tests on real programs.

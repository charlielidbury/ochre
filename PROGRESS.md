# Progress

## Current state (2026-04-04)

Och is feature-complete for the current milestone. All tests pass, including
the north star (`appendVec` with abstract arguments). The focus is now on
proving soundness.

### Sorry inventory (10 total)

**Blocking soundness (5):**
1. `subCheckNF_fuel_mono` — Eval.lean:385 — fuel monotonicity for subCheckNF
   (NEW: replaces the old `absEval_fuel_mono` sorry. See below.)
2. `VCompat.from_type_sub_gen` — Soundness.lean:174 — Type subtyping gives VCompat
3. `VCompat.from_self_intro_gen` — Soundness.lean:197 — self-intro gives VCompat
4. `VCompat.adequacy` — Soundness.lean:212 — subCheckNF preserves VCompat
5. `soundness` (main theorem) — Soundness.lean:238

**Not blocking soundness (5):**
6. `subCheckNF_lam_lam_body` — Subtyping.lean:131
7. `subCheckNF_lam_impossible` — Subtyping.lean:147
8. `subCheckNF_mu_mu_body` — Subtyping.lean:155
9. `subCheckNF_type_left_target` — Subtyping.lean:162
10. `subCheckNF_neutral_inferType` — Subtyping.lean:174

### What happened this session (agent ochre-20260404-183233)

**`absEval_fuel_mono` is proved** (modulo `subCheckNF_fuel_mono`).

Two changes were made:

1. **Definition change (Eval.lean:172-179):** Removed redundant domain
   re-normalization in absEval's app/lam case. The domain `dom` in
   `f'.val = .lam dom body` is already normalized (it's a sub-expression
   of an absEval output). Re-normalizing it via `absEval fuel ctx seen dom`
   was a no-op in practice (all tests pass without it) but made fuel
   monotonicity unprovable: with more fuel, the normalization could switch
   from failing (fallback = raw) to succeeding (= normalized form), changing
   the subCheckNF inputs. Without re-normalization, the inputs are stable
   across fuel levels.

2. **Proof (Eval.lean:390-470):** `absEval_fuel_mono` proved by induction on
   fuel, case split on the expression. Each case:
   - Unfold absEval at h and goal
   - Extract intermediate results via `match hx : absEval k ...`
   - Apply IH to lift from fuel k to k+1
   - For subCheckNF calls, use `subCheckNF_fuel_mono` (sorry'd)
   - For the mu-app sub-case, a helper `absEval_fuel_mono_mu_lam_body`
     handles the if-then-else + match structure

**New sorry: `subCheckNF_fuel_mono` (Eval.lean:385)**

Statement: `subCheckNF n ctx seen a b = true → subCheckNF (n+1) ctx seen a b = true`

This is more focused than the old `absEval_fuel_mono` sorry. The difficulty:
subCheckNF's lam-lam case re-normalizes domains via `absEval` with fallback.
If normalization fails at fuel k but succeeds at k+1, the inputs to the
recursive subCheckNF call change. However, since `absEval_fuel_mono` is now
proved, the fallback issue only affects cases where absEval FAILS at fuel k —
if it succeeds, the result is the same at k+1.

Possible approaches:
- Prove subCheckNF_fuel_mono by mutual induction with absEval_fuel_mono
- Show that the normalization-with-fallback in subCheckNF is monotone:
  if the raw-form check passes, the normalized-form check also passes
- Remove the re-normalization in subCheckNF's lam-lam case (like we did
  for absEval's app/lam case) — but this might break tests since
  subCheckNF's inputs aren't always pre-normalized

### What's working
- All tests pass (`lake build` succeeds with sorrys)
- appendVec type-checks with abstract arguments
- `concEval_fuel_mono` proved
- **`absEval_fuel_mono` proved** (uses `subCheckNF_fuel_mono`)
- VCompat.mono, VCompat.mono_le, VCompat.refl, VCompat.fixpoint_mu all proved
- SubtypeCore.trans, Subtype'.trans proved

### Priority
Next agent should work on `subCheckNF_fuel_mono` (Eval.lean:385).
See SUGGESTIONS.md Phase 1 and the analysis above for approaches.

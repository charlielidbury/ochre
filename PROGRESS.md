# Progress

## Current state (2026-04-04)

Och is feature-complete for the current milestone. All tests pass, including
the north star (`appendVec` with abstract arguments). The focus is now on
proving soundness.

### Sorry inventory (9 total)

**Phase 1 (fuel monotonicity): COMPLETE**
- `subCheckNF_fuel_mono` — PROVED (was Eval.lean:385)
- `absEval_fuel_mono` — PROVED (was Eval.lean:390)

**Blocking soundness (4):**
1. `VCompat.from_type_sub_gen` — Soundness.lean:164 — Type subtyping gives VCompat
2. `VCompat.from_self_intro_gen` — Soundness.lean:185 — self-intro gives VCompat
3. `VCompat.adequacy` — Soundness.lean:209 — subCheckNF preserves VCompat
4. `soundness` (main theorem) — Soundness.lean:233

**Not blocking soundness (5):**
5. `subCheckNF_lam_lam_body` — Subtyping.lean:127
6. `subCheckNF_lam_impossible` — Subtyping.lean:140
7. `subCheckNF_mu_mu_body` — Subtyping.lean:151
8. `subCheckNF_type_left_target` — Subtyping.lean:159
9. `subCheckNF_neutral_inferType` — Subtyping.lean:167

### What happened this session (agent ochre-20260404-191653)

**`subCheckNF_fuel_mono` is PROVED.** Combined with the previous session's
`absEval_fuel_mono`, Phase 1 (fuel monotonicity) is now complete.

Three definition changes to subCheckNF were needed to make fuel monotonicity
provable, all eliminating normalization-with-fallback patterns where `absEval`
failure caused a fallback to a raw/annotation term. The fallback made inputs
to recursive calls fuel-dependent (different results at different fuel levels):

1. **Lam-lam domain normalization removed (Eval.lean:226-235):** Domains
   `domA`, `domB` are now used directly without re-normalizing via absEval.
   This works because domains in the lam-lam case are typically already
   normalized (sub-expressions of absEval outputs). All tests pass.

2. **Self-intro normalization: no fallback (Eval.lean:236-243):** Changed
   `match absEval ... u with | ok x => x.val | error _ => u` to
   `match absEval ... u with | ok x => subCheckNF ... a x.val | error _ => false`.
   If normalization fails, the check fails rather than trying the raw term.
   All tests pass — the raw-term fallback was never needed in practice.

3. **Self-elim: annotation-first ordering (Eval.lean:244-258):** Changed from
   "normalize body, fallback to annotation" to "check annotation first, then
   try normalized body". Both paths are now fuel-stable: the annotation path
   doesn't depend on absEval, and the body path is stable because absEval_fuel_mono
   ensures consistent results. This preserves the annotation fallback needed by
   `appendArrays` while making the proof go through.

4. **InferType normalization: no fallback (Eval.lean:259-276):** Same as
   self-intro — absEval failure returns false. Tests pass.

**Proof structure:** The mutual dependency between `absEval_fuel_mono` and
`subCheckNF_fuel_mono` is resolved via a combined theorem `fuel_mono` that
proves both simultaneously by induction on fuel. The inductive step uses
helper lemmas for each subCheckNF case pattern:
- `subCheckNF_absEval_step` — the "match absEval ... with | ok => subCheckNF | error => false" pattern
- `subCheckNF_absEval_step_right` — mirror for self-intro (result in second position)
- `subCheckNF_self_elim_step` — annotation-first + body normalization
- `subCheckNF_inferType_step` — inferType + absEval normalization
- `absEval_fuel_mono_mu_lam_body` — the mu-app sub-case in absEval

### What's working
- All tests pass (`lake build` succeeds with sorrys only in Subtyping/Soundness)
- appendVec type-checks with abstract arguments
- `concEval_fuel_mono` proved
- **`absEval_fuel_mono` proved**
- **`subCheckNF_fuel_mono` proved**
- VCompat.mono, VCompat.mono_le, VCompat.refl, VCompat.fixpoint_mu all proved
- SubtypeCore.trans, Subtype'.trans proved

### Priority
Next agent should work on Phase 2: the VCompat lemmas in Soundness.lean.
See SUGGESTIONS.md for the dependency chain and priority order.
The highest priority is `VCompat.from_type_sub_gen` (Soundness.lean:164).

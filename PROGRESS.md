# Progress

## Current state (2026-04-04)

Och is feature-complete for the current milestone. All tests pass, including
the north star (`appendVec` with abstract arguments). The focus is now on
proving soundness.

### Sorry inventory (4 total)

**Phase 1 (fuel monotonicity): COMPLETE**
- `subCheckNF_fuel_mono` — PROVED
- `absEval_fuel_mono` — PROVED

**Phase 2 (VCompat lemmas): IN PROGRESS**
- `VCompat.from_type_sub_gen` — **PROVED** (Soundness.lean:178)
- `VCompat.from_self_intro_gen` — Soundness.lean:257 — sorry (needs adequacy)
- `VCompat.adequacy` — Soundness.lean:322 — sorry
- `soundness` (main theorem) — Soundness.lean:346 — sorry

**Phase 3 (Subtyping helpers):**
- `subCheckNF_lam_lam_body` — PROVED
- `subCheckNF_lam_impossible` — PROVED
- `subCheckNF_mu_mu_body` — PROVED
- `subCheckNF_type_left_target` — PROVED
- `subCheckNF_neutral_inferType` — Subtyping.lean:194 — sorry

### What happened this session (agent ochre-20260404-204421)

**CRITICAL FIX: VCompat's normalization disjunct made it trivially true.**

The previous session added a "normalization" disjunct to VCompat (the 9th
disjunct) to bridge raw mu body substitutions with their absEval-normalized
forms. This disjunct:

```lean
∨ (∃ nfuel nctx nseen τ', absEval nfuel nctx nseen τ = .ok τ' ∧ VCompat n v τ'.val)
```

**was trivially satisfiable**, making VCompat n v τ = True for ALL n, v, τ!

Proof: at step n+1, pick any normalizable τ (almost everything), then:
VCompat (n+1) v τ via normalization → need VCompat n v τ'.val → 
VCompat n v τ'.val via normalization → need VCompat (n-1) v τ''.val → 
... → VCompat 0 v _ = True.

This meant ALL Phase 2 proofs (from_type_sub_gen, etc.) were vacuously true
and the soundness theorem would have been vacuously true (conclusion always
holds, regardless of inputs). The entire VCompat relation captured NO semantic
content.

**Fix: replaced the general normalization disjunct with a targeted
normalized mu-right disjunct:**

```lean
∨ (∃ ann body, ∃ nfuel nctx nseen u',
    τ = .mu ann body ∧
    absEval nfuel nctx nseen (body.subst 0 (.mu ann body)) = .ok u' ∧
    VCompat n v u'.val)
```

This ONLY applies when τ is a mu type, preventing the trivial induction.
VCompat n v (lam ...) is now genuinely non-trivial (requires actual body
compatibility). The old mu-right disjunct (raw substitution, no normalization)
is kept for proofs like fixpoint_mu.

**Re-proved from_type_sub_gen** with the new VCompat definition. The proof is
actually simpler: one-step using the normalized mu-right instead of the old
two-step (mu-right + normalization).

**Also discovered: annotation-trust soundness bug in absEval (Eval.lean:183-188).**

The mu-app annotation-trust case:
```lean
| .lam _dom retBody, .lam _ _ =>
    absEval fuel ctx seen (retBody.subst 0 a'.val)
```
trusts the mu annotation without validation. Counterexample:
```
app (mu (lam Type (lam Type (bvar 0))) (lam Type Type)) Type
```
- absEval returns `lam Type (bvar 0)` (identity type, from annotation)
- concEval returns `Type` (constant, from body)
- VCompat Type (lam Type (bvar 0)) is false for n ≥ 1

This is a real soundness bug. The fix requires either:
1. Validating mu annotations against bodies at mu creation time
2. Removing the annotation-trust path (breaks appendArrays tests)
3. Adding a WellAnnotated precondition to soundness

This is NOT fixed in this session — it requires careful design decisions.
See SUGGESTIONS.md for discussion.

### What's working
- All tests pass (`lake build` succeeds with sorrys only in Subtyping/Soundness)
- appendVec type-checks with abstract arguments
- `concEval_fuel_mono` proved
- `absEval_fuel_mono` proved
- `subCheckNF_fuel_mono` proved
- `VCompat.from_type_sub_gen` proved
- VCompat.mono, VCompat.mono_le, VCompat.refl, VCompat.fixpoint_mu,
  VCompat.self_intro_eq, VCompat.fixpoint_mu_left all proved
- SubtypeCore.trans, Subtype'.trans proved
- **VCompat is now meaningful** (not trivially true)

### Priority

**Next agent must address the annotation-trust soundness bug BEFORE working
on adequacy.** The bug means soundness cannot be proved without either fixing
absEval or strengthening the precondition. Options:

1. **Validate mu annotations at creation (preferred):** In absEval's .mu case,
   check that `body` (with self of type ann) produces something ⊑ ann. This
   is the standard recursive-type checking rule. Might need careful handling
   to not break appendArrays tests.

2. **Remove annotation-trust path + fix appendArrays:** Change mu-app to
   always use the body-based path. appendArrays would need restructuring.

3. **Add a WellAnnotated precondition:** Weaker but allows incremental
   progress. soundness would only hold for programs with correct annotations.

After fixing the annotation bug, work on **VCompat.adequacy** (Soundness.lean:322).
from_self_intro_gen depends on it (its sorry IS adequacy).

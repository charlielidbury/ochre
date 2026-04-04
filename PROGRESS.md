# Progress

## Current state (2026-04-04)

Och is feature-complete for the current milestone. All tests pass, including
the north star (`appendVec` with abstract arguments). The focus is now on
proving soundness.

### Sorry inventory (8 total in Soundness, 1 in Subtyping)

**Phase 1 (fuel monotonicity): COMPLETE**
- `subCheckNF_fuel_mono` — PROVED
- `absEval_fuel_mono` — PROVED

**Phase 2 (VCompat lemmas): IN PROGRESS**
- `VCompat.from_type_sub_gen` — **PROVED** (Soundness.lean:178)
- `VCompat.refl` — **PROVED** (Soundness.lean:257)
- `VCompat.adequacy_gen` — **PARTIALLY PROVED** (Soundness.lean:279)
  - Proved: equality, seen hit, Type, self-intro (τ = mu)
  - Proved: app-app structural congruence (τ = app, σ = app, structural check succeeds)
    - All 4 VCompat sub-cases handled: refl, structural app, mu-left, inferType
    - Key enabler: definition change to clear `seen` in structural recursive calls
  - Proved: contradictions for σ ∈ {type, lam, asc} when τ = app (inferType fails)
  - Sorry: τ = lam (lam-lam case, needs substitution lemma) — Soundness.lean:341
  - Sorry: τ = bvar (self-elim + inferType) — Soundness.lean:344
  - Sorry: τ = asc (self-elim + inferType) — Soundness.lean:347
  - Sorry: app-app inferType fallback (structural check failed) — Soundness.lean:436
  - Sorry: σ = mu, τ = app (self-elim, annotation-trust) — Soundness.lean:439
  - Sorry: σ = bvar, τ = app (inferType fallback) — Soundness.lean:445
- `VCompat.adequacy` — corollary of adequacy_gen (Soundness.lean:454)
- `VCompat.from_self_intro_gen` — **PROVED** (Soundness.lean:462) via adequacy_gen
- `soundness` (main theorem) — Soundness.lean:541 — sorry

**Phase 3 (Subtyping helpers):**
- `subCheckNF_lam_lam_body` — PROVED
- `subCheckNF_lam_impossible` — PROVED
- `subCheckNF_mu_mu_body` — PROVED
- `subCheckNF_type_left_target` — PROVED
- `subCheckNF_neutral_inferType` — Subtyping.lean:201 — sorry (may need statement fix)

### What happened this session (agent ochre-20260404-224040)

**DEFINITION CHANGE: Cleared `seen` in structural recursive calls of subCheckNF.**

Changed the lam-lam and app-app structural cases in subCheckNF to use
empty seen `[]` instead of propagating the outer `seen`:

```lean
-- Before:
subCheckNF fuel ctx seen domB domA && subCheckNF fuel (TyCtx.extend ctx ⟨domB⟩) seen bodyA bodyB
-- After:
subCheckNF fuel ctx [] domB domA && subCheckNF fuel (TyCtx.extend ctx ⟨domB⟩) [] bodyA bodyB
```

Same change for app-app structural check. All tests pass.

**WHY:** The outer `seen` set contains equi-recursive assumptions (e.g.,
(σ, mu ann body)) with VCompat callbacks tied to the original `v` being
tracked. When adequacy_gen needs to recurse into sub-components (f1→f2
in the app-app case), the callback needs VCompat for the *sub-component*
(fV), not the original v. This mismatch was the fundamental blocker for
the app-app adequacy proof. By clearing seen, the callback becomes vacuous
(empty seen = no callback needed), enabling the proof.

The structural recursive calls don't benefit from equi-recursive assumptions
anyway — they compare structural sub-parts (domains, bodies, function/arg
components), not the mu types that the seen set tracks.

**Proved: app-app structural congruence case in adequacy_gen.**

When subCheckNF succeeds for (app f1 a1) ⊑ (app f2 a2) via the structural
path (subCheckNF f1 f2 ∧ subCheckNF a1 a2), VCompat is preserved through
all 4 possible shapes of the VCompat hypothesis:

1. **Refl** (v = app f1 a1): Construct structural app VCompat using ih_fuel
   with VCompat.refl for each component + empty-seen callback.

2. **Structural app** (v = app fV aV): Transport VCompat m fV f1 to fV f2
   and VCompat m aV a1 to aV a2 via ih_fuel + empty-seen callback.

3. **Mu-left** (v = mu ann body): Use ih_n (step induction) with
   hcheck_empty (reconstructed subCheckNF with empty seen) + empty callback.

4. **InferType** (inferType v = ty): Use ih_n with hcheck_empty + empty
   callback to transport VCompat m ty (app f1 a1) to VCompat m ty (app f2 a2).

Also proved contradictions: σ ∈ {type, lam, asc} with τ = app always leads
to inferType failure (none), so subCheckNF returns false.

### Remaining adequacy_gen cases (documented blockers)

The remaining sorry'd cases fall into three categories:

**1. Lam-lam (τ = lam):** Needs a "substitution lemma" — showing that
   if subCheckNF(bodyσ, bodyτ) under extended context, then evaluating
   bodyσ[a] and bodyτ[a] preserves the relationship. Hard because VCompat's
   semantic lam quantifies over ALL fuel levels for inner evaluation. The
   `seen` clearing change helps here too (can use ih_fuel with []), but the
   substitution lemma is the real blocker.

**2. Self-elim (σ = mu, τ ≠ mu):** Blocked by annotation-trust. Going from
   VCompat(v, mu ann body) to VCompat(v, ann) requires the annotation to
   accurately describe the mu's behavior. This is the annotation-trust gap
   identified in Phase 0 (SUGGESTIONS.md).

**3. InferType fallback:** When subCheckNF falls through to the inferType
   catch-all, we need "semantic inferType": if VCompat v σ and
   inferType ctx σ = some ty, then VCompat v (normalized ty). This connects
   the syntactic type inference with the semantic VCompat relation.

The app-app inferType fallback (structural check failed) and bvar ⊑ app
both fall into category 3.

### Previous session (agent ochre-20260404-215501)

Proved from_self_intro_gen and partially proved adequacy_gen. Created
VCompat.adequacy_gen with double induction (fuel/step). Proved equality,
seen hit, Type, and self-intro cases. Identified the annotation-trust
gap as the blocker for self-elim.

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
- **VCompat is meaningful** (not trivially true)
- **App-app structural congruence fully proved** in adequacy_gen

### Priority

**Recommended next steps (in priority order):**

1. **Lam-lam case:** The `seen` clearing change makes the adequacy proof
   tractable (can use ih_fuel with [] for sub-component checks). The remaining
   blocker is the substitution lemma: connecting subCheckNF under a binder
   to VCompat after substitution. This requires careful reasoning about how
   absEval handles substituted terms.

2. **Semantic inferType lemma:** Prove that if VCompat n v σ and
   inferType ctx σ = some ty (and absEval normalizes ty), then VCompat n v ty'.
   This would unblock: app-app inferType fallback, bvar ⊑ app, and similar cases.

3. **Self-elim / annotation-trust:** Either:
   a) Add WellAnnotated precondition to adequacy_gen (propagates to soundness)
   b) Prove annotations are correct for absEval output
   c) Find a different proof strategy that avoids going through annotations

4. **Main soundness theorem:** Requires adequacy + induction on fuel.
   The semantic lam in VCompat quantifies over all fuel, which creates a
   mismatch with the fuel-induction IH. May need strong induction on fuel
   + fuel monotonicity argument.

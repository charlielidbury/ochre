# Progress

## Current state (2026-04-04)

Och is feature-complete for the current milestone. All tests pass, including
the north star (`appendVec` with abstract arguments). The focus is now on
proving soundness.

### Sorry inventory (17 in Soundness, 0 in Subtyping = 17 total)

Note: Concurrent worktree agent has uncommitted changes reducing Soundness
sorrys to 14 (adding VCompat.absEval_preserves sorry + proving 4 bvar cases).
The committed state has 17 sorrys. If the concurrent agent commits, the total
drops to 14.

**Phase 1 (fuel monotonicity): COMPLETE**
- `subCheckNF_fuel_mono` — PROVED
- `absEval_fuel_mono` — PROVED

**Phase 2 (VCompat lemmas): IN PROGRESS**
- `VCompat.from_type_sub_gen` — **PROVED** (Soundness.lean:178)
- `VCompat.refl` — **PROVED** (Soundness.lean:257)
- `VCompat.bvar_inferType` — **PROVED** (Soundness.lean:268)
- `VCompat.absEval_preserves` — **SORRY** (Soundness.lean:334) — KEY LEMMA
- `VCompat.adequacy_gen` — **PARTIALLY PROVED** (Soundness.lean:358)
  - Proved: equality, seen hit, Type, self-intro (τ = mu)
  - Proved: app-app structural congruence (all VCompat sub-cases)
  - Proved: contradictions for σ ∈ {type, lam, asc} when τ = app
  - Proved: contradictions for σ ∈ {type, asc} when τ = lam
  - Proved: contradictions for σ ∈ {type, lam, asc} when τ ∈ {bvar, asc}
  - **Proved: lam-lam mu-left + inferType sub-cases** (using empty-seen reconstruction)
  - **Proved: σ = bvar for τ ∈ {lam, bvar, asc, app}** via bvar_inferType + absEval_preserves
  - Sorry: lam-lam refl + semantic-lam (2 sorrys, lines 452/455) — substitution lemma
  - Sorry: self-elim σ=mu for τ ∈ {lam, bvar, asc, app} (4 sorrys) — annotation-trust
  - Sorry: inferType fallback σ=app for τ ∈ {lam, bvar, asc} (3 sorrys) — needs app_inferType
  - Sorry: app-app inferType fallback (1 sorry, line 653) — needs app_inferType + absEval_preserves
- `VCompat.adequacy` — corollary of adequacy_gen (Soundness.lean:670)
- `VCompat.from_self_intro_gen` — **PROVED** (Soundness.lean:678)
- `soundness` (main theorem) — **PARTIALLY PROVED** (Soundness.lean:736)
  - Proved: fuel=0 (contradiction), bvar (contradiction), type (trivial)
  - **Proved: asc case** via IH + VCompat.adequacy
  - Sorry: lam — all-fuel issue in semantic lam
  - Sorry: mu — annotation normalization (ann vs ann'.val)
  - Sorry: app — combines multiple issues

**Phase 3 (Subtyping helpers): COMPLETE**
- `subCheckNF_lam_lam_body` — PROVED
- `subCheckNF_lam_impossible` — PROVED
- `subCheckNF_mu_mu_body` — PROVED
- `subCheckNF_type_left_target` — PROVED
- `subCheckNF_neutral_inferType` — **PROVED** (Subtyping.lean:198)

### What happened this session (agent ochre-20260404-235445)

**Proved subCheckNF_neutral_inferType + explored bvar definition change.**

1. **subCheckNF_neutral_inferType (Subtyping.lean:198): PROVED.** Phase 3 complete.
   When subCheckNF succeeds for a neutral term (not lam, not mu, not app) against
   a non-type, non-mu target with empty seen, the inferType catch-all must have
   fired. Proof: case split on a (only bvar is viable; type/asc have inferType =
   none → contradiction), then extract inferType/absEval/subCheckNF from the
   catch-all path.

2. **Explored bvar-specific case in subCheckNF (NOT committed).** Attempted to add
   a `.bvar k, _` arm to subCheckNF that looks up ctx.get? directly (bypassing
   the absEval normalization in the catch-all). Motivation: eliminates the
   normalization gap for bvar cases, making them provable without absEval_preserves.
   Result: fuel_mono proof was fixable (trivial ih_sub), all tests passed, but
   cascading proof changes in Soundness.lean were extensive — the bvar cases in
   adequacy_gen needed rewriting, and some used `split at hcheck` which didn't
   reduce correctly for all τ cases (the compiled match tree was surprising).
   **Recommendation:** This is a VIABLE approach but needs careful proof updates.
   The key insight: with the bvar arm, the 4 bvar inferType sorrys become provable
   using just bvar_inferType + ih_fuel (no absEval_preserves needed).

3. **Explored removing mu annotation normalization (NOT committed).** Tried making
   absEval's mu case return `ok ⟨mu ann body⟩` instead of normalizing ann. This
   would trivialize the soundness mu case (v = τ.val by refl). Result: breaks
   Array tests. The annotation normalization is required for subCheckNF's self-elim
   to succeed on Church-encoded types.

### Concurrent session (agent ochre-20260404-235517, worktree)

**Three advances: bvar_inferType lemma, absEval_preserves factoring, 3 bvar sorrys closed.**

1. **VCompat.bvar_inferType (Soundness.lean:268): PROVED.** New lemma:
   VCompat(n, v, bvar k) + inferType ctx (bvar k) = some ty → VCompat(n, v, ty).
   Proof by induction on n; at step n+1, case split on VCompat disjuncts.

2. **VCompat.absEval_preserves (Soundness.lean:334): SORRY'd.** Isolates the
   "normalization gap": VCompat(n, v, e) + absEval(e) = ok e' → VCompat(n, v, e'.val).
   This is the single most impactful remaining lemma.

3. **Closed 3 bvar inferType sorrys** via bvar_inferType + absEval_preserves + ih_fuel.

**Net (if concurrent agent commits): 18 → 14 sorrys.**

**NOTE:** The concurrent agent's Soundness.lean changes are NOT committed yet.
If they conflict with this commit, the bvar_inferType and absEval_preserves
additions should be preserved — they're correct and useful.

### Previous session (agent ochre-20260404-231427)

**Two advances: soundness theorem scaffolding + adequacy_gen case refinement.**

1. **Soundness theorem (Soundness.lean:601):** Set up fuel induction with 3 cases proved:
   - `fuel = 0`: contradiction (concEval returns none)
   - `bvar`: contradiction (concEval returns none for free vars)
   - `type`: trivial (v = τ = type, VCompat by refl)
   - `asc`: **PROVED** using IH + VCompat.adequacy. Key insight: concEval
     erases the ascription (evaluating term at fuel k), absEval validates it
     (normalizing both sides, checking subCheckNF), so IH at fuel k gives
     VCompat for the term, and adequacy bridges to the ascribed type.
   - `lam`, `mu`, `app`: sorry'd with documented blockers.

   Soundness `lam` blocker: the semantic lam in VCompat quantifies over ALL
   fuel levels for inner evaluation, but the fuel-induction IH only gives
   soundness at fuel k. Needs either strong induction on (fuel, step) with
   lexicographic ordering, or a different proof strategy. Key insight from
   analysis: with lex induction on (fuel, n), the IH at (k, n+2) gives
   VCompat (n+2) for f, and the semantic lam with j = n+1 gives VCompat (n+1)
   for the application result. This should work for the `app` case.

   Soundness `mu` blocker: absEval normalizes the annotation (ann → ann'.val),
   so v = mu ann body but τ = mu ann'.val body. VCompat requires relating
   these, which needs annotation normalization to preserve VCompat, or an
   idempotency lemma (absEval on already-normal ann = ann).

2. **Adequacy_gen case refinement (Soundness.lean:279):** Split the 3 sorry'd
   τ cases (lam, bvar, asc) into sub-cases by σ constructor:
   - **9 contradiction cases proved**: σ ∈ {type, asc} for all τ (inferType
     returns none → subCheckNF false); σ = lam for τ ∈ {bvar, asc} (same).
   - **Lam-lam (σ = lam, τ = lam):** Proved 7 of 9 VCompat sub-cases:
     - Contradictions: type ≠ lam, mu ≠ lam, app ≠ lam (5 cases)
     - **Mu-left PROVED**: reconstruct subCheckNF with empty seen (structural
       check is seen-independent since it uses [] internally), then ih_n with
       vacuous callback.
     - **InferType PROVED**: same empty-seen technique.
     - **Refl and Semantic Lam remain sorry'd**: both need the substitution
       lemma (connecting subCheckNF(bodyS, bodyT) under binder to VCompat
       after substitution).

### Sorry categorization (14 in Soundness, 0 in Subtyping)

The remaining sorrys fall into 4 categories:

**Category 1: Structural lam-lam (2 sorrys, Soundness.lean:373, 376)**
- Refl: v = lam _dS _bS, need VCompat (m+1) (lam _dS _bS) (lam _dT _bT)
- Semantic lam: v = lam domV bodyV, need to transport body compatibility
- BLOCKER: substitution lemma — connecting subCheckNF(bodyS, bodyT) under
  extended context to VCompat after substituting concrete arguments. The
  semantic lam quantifies over ALL fuel levels.

**Category 2: Self-elim / annotation-trust (4 sorrys)**
- σ = mu, τ ∈ {lam, bvar, asc, app} (lines 401, 423, 444, 542)
- BLOCKER: annotation-trust gap. subCheckNF's mu self-elim tries the
  annotation first, then body normalization. Both paths need guarantees
  that VCompat is preserved.

**Category 0: absEval_preserves (1 sorry, Soundness.lean:339)**
- THE KEY LEMMA: VCompat(n, v, e) ∧ absEval(e) = ok e' → VCompat(n, v, e'.val)
- Would unblock all σ=app inferType sorrys, soundness mu case, possibly self-elim

**Category 3: InferType fallback σ=app (4 sorrys)**
- σ = app, τ ∈ {lam, bvar, asc} (lines 501, 564, 653) + app-app fallback
- BLOCKER: needs app_inferType lemma + absEval_preserves.
  σ = bvar cases are DONE (via bvar_inferType + absEval_preserves).

**Category 4: Soundness main cases (3 sorrys, Soundness.lean:689, 696, 703)**
- lam: semantic lam all-fuel issue (see above)
- mu: annotation normalization (ann vs ann'.val)
- app: combines all above issues

### Recommended next steps (updated)

1. **absEval_preserves (Soundness.lean:339):** Most impactful lemma. Start
   with easy cases (type→top, bvar→identity), then lam/mu/asc/app.

2. **app_inferType lemma:** Like bvar_inferType but for app. Harder because
   the structural app disjunct in VCompat doesn't compose into return types.

3. **Substitution lemma:** For lam-lam refl/semantic cases.

4. **Self-elim / annotation-trust:** Consider whether absEval_preserves +
   body normalization path can bypass the annotation check.

5. **Soundness main cases:** Lex/strong induction on fuel for lam/app.

### Previous session (agent ochre-20260404-224040)

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

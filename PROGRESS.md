# Progress

## Current state (2026-04-05)

Och is feature-complete for the current milestone. All tests pass, including
the north star (`appendVec` with abstract arguments). The focus is now on
proving soundness.

### Sorry inventory (24 in Soundness, 0 in Subtyping = 24 total)

Up from 22 numerically — 2 new from counting correction (agent
ochre-20260405-013043 verified exact count). Definition change to
self-elim didn't add/remove sorrys, just changed proof landscape.

Changes by agent ochre-20260405-013043:
- **TWO DEFINITION CHANGES to subCheckNF self-elim, fixing transitivity:**
  1. Body check uses original `seen` (not `seen'`), preventing circular
     reasoning for non-productive fixpoints.
  2. Annotation path guarded by `body != bvar 0`. For pure self-reference
     bodies, the mu is universal (everything subtypes it via self-intro)
     but the annotation claims a specific type — trusting it breaks
     transitivity (found via exhaustive testing on edge cases).
- **Added exhaustive transitivity tests** in Tests.lean: 3 sets of small
  expressions (~30 total) including Std types, nested mus, and self-referential
  patterns. All pass native_decide.
- **Updated fuel_mono proof** (`subCheckNF_self_elim_step` in Eval.lean)
  to handle the new `body != bvar 0 &&` guard.
- **Proof landscape change:** Self-elim body path in adequacy_gen is no
  longer circularly blocked by the seen callback. The remaining blockers
  are absEval_preserves and the mu-right step-count issue.
- **Key analysis:** Attempted to expand self-elim sorry in adequacy_gen.
  Found that ih_n callback doesn't match for mu-left case (callback has
  original v, but mu-left transforms v to body.subst). Works when seen=[],
  which is the common case from VCompat.adequacy.

Previous changes by agent ochre-20260405-003615:
- **Proved neutral app sub-cases in absEval_preserves** (refl-app + structural app):
  When absEval dispatches to a neutral app (fT' ∉ {lam, mu}), the result is
  a symbolic app ⟨app fT'.val aT'.val⟩. VCompat via structural app + IH on
  sub-expressions. The lam/mu dispatch sub-cases remain sorry'd.
- **Key analysis finding**: absEval_preserves and adequacy_gen have a **circular
  dependency** for the refl-asc case. Breaking this requires either a combined
  fuel-induction proof or restructuring. The refl-asc case doesn't arise at
  current use sites (e from inferType is NfExpr, never asc).
- **Verified asc-left disjunct invalidates the counterexample** from the previous
  session: VCompat(2, asc(lam T (bvar 0), lam T T), lam T T) IS true via
  asc-left + semantic lam at step 1 (trivially satisfied since j=0 only).

Previous changes by agent ochre-20260405-003633:
- **CRITICAL FIX: absEval_preserves was FALSE as stated.**
  Counterexample: v = e = asc (lam Type (bvar 0)) (lam Type Type), n=2.
  VCompat(2, v, v) via refl, absEval(v) = ok ⟨lam Type Type⟩, but
  VCompat(2, asc(...), lam Type Type) fails — no disjunct handles asc on value side.
- **DEFINITION CHANGE: Added asc-left disjunct to VCompat.**
  `∨ (∃ term tyAsc, v = .asc term tyAsc ∧ VCompat n term τ)`
  This reflects runtime semantics: concEval erases ascriptions, so
  `(e : τ)` as a value behaves like `e`. Needed because mu-left unfolding
  can introduce asc nodes in the value position.
- **Proved 3 cases of absEval_preserves**: mu-left (IH), inferType (IH), asc-left (IH)
- **Fixed all cascading proofs** for the new VCompat disjunct in:
  VCompat.mono, VCompat.bvar_inferType, VCompat.adequacy_gen (2 rcases sites)
- **Proved 2 new asc-left cases in adequacy_gen** (lam-lam and app-app structural)
- All tests pass, `lake build` succeeds

**Phase 1 (fuel monotonicity): COMPLETE**
- `subCheckNF_fuel_mono` — PROVED
- `absEval_fuel_mono` — PROVED

**Phase 2 (VCompat lemmas): IN PROGRESS**
- `VCompat.from_type_sub_gen` — **PROVED** (Soundness.lean:178)
- `VCompat.refl` — **PROVED** (Soundness.lean:263)
- `VCompat.bvar_inferType` — **PROVED** (Soundness.lean:273)
- `VCompat.absEval_preserves` — **PARTIALLY PROVED** (Soundness.lean:320)
  - Proved: top (trivial), refl-bvar (identity), refl-type (top)
  - Proved: mu-left (IH on n), inferType (IH on n), asc-left (IH on n)
  - Sorry: refl-asc (1 sorry) — needs VCompat.adequacy (defined later, circular dep)
  - Sorry: refl-lam (1) — normalization coherence (absEval body vs raw body)
  - Sorry: refl-mu (1) — annotation normalization congruence
  - Sorry: refl-app lam/mu dispatch (2) — beta-reduction changes shape
    Proved: refl-app neutral case (bvar/app/asc fT' → structural app + IH)
  - Sorry: semantic lam (1) — normalization coherence
  - Sorry: structural mu (1) — annotation normalization congruence
  - Sorry: mu-right (1) — annotation normalization congruence
  - Sorry: normalized mu-right (1) — composing normalizations
  - Sorry: structural app lam/mu dispatch (2) — beta-reduction changes shape
    Proved: structural app neutral case (bvar/app/asc fT' → structural app + IH)
  All sorry'd cases reduce to 2 fundamental blockers:
  (a) Normalization coherence: absEval(body) and body give same semantics
  (b) Annotation normalization congruence: absEval(ann) preserves mu semantics
- `VCompat.adequacy_gen` — **PARTIALLY PROVED** (Soundness.lean:459)
  - Proved: equality, seen hit, Type, self-intro (τ = mu)
  - Proved: app-app structural congruence (all VCompat sub-cases incl. asc-left)
  - Proved: contradictions for σ ∈ {type, lam, asc} when τ = app
  - Proved: contradictions for σ ∈ {type, asc} when τ = lam
  - Proved: contradictions for σ ∈ {type, lam, asc} when τ ∈ {bvar, asc}
  - Proved: lam-lam mu-left + inferType + **asc-left** sub-cases
  - Proved: σ = bvar for τ ∈ {lam, bvar, asc, app} via bvar_inferType + absEval_preserves
  - Sorry: lam-lam refl + semantic-lam (2 sorrys) — substitution lemma
  - Sorry: self-elim σ=mu for τ ∈ {lam, bvar, asc, app} (4 sorrys) — annotation-trust
  - Sorry: inferType fallback σ=app for τ ∈ {lam, bvar, asc} (3 sorrys) — app_inferType
  - Sorry: app-app inferType fallback (1 sorry) — app_inferType + absEval_preserves
- `VCompat.adequacy` — corollary of adequacy_gen (Soundness.lean:798)
- `VCompat.from_self_intro_gen` — **PROVED** (Soundness.lean:806)
- `soundness` (main theorem) — **PARTIALLY PROVED** (Soundness.lean:882)
  - Proved: fuel=0 (contradiction), bvar (contradiction), type (trivial)
  - Proved: asc case via IH + VCompat.adequacy
  - Sorry: lam — all-fuel issue in semantic lam
  - Sorry: mu — annotation normalization (ann vs ann'.val)
  - Sorry: app — combines multiple issues

**Phase 3 (Subtyping helpers): COMPLETE**
- `subCheckNF_lam_lam_body` — PROVED
- `subCheckNF_lam_impossible` — PROVED
- `subCheckNF_mu_mu_body` — PROVED
- `subCheckNF_type_left_target` — PROVED
- `subCheckNF_neutral_inferType` — **PROVED** (Subtyping.lean:198)

### What happened this session (agent ochre-20260405-013043)

**Fixed subCheckNF transitivity counterexample by changing self-elim seen handling.**

1. **ROOT CAUSE:** Self-elim's body path in subCheckNF added `(mu, b)` to `seen`,
   then the normalized body path could hit this entry via circular reasoning.
   For non-productive fixpoints like `mu Type (bvar 0)`, the body unfolds to
   the same mu, hits the seen entry, and succeeds trivially — allowing
   `mu Type (bvar 0) ⊑ anything`.

2. **FIX:** Self-elim's final `subCheckNF` call now uses the original `seen`
   (without the `(mu, b)` entry). The annotation check and absEval call still
   use `seen'` (for annotation cycle detection and absEval's mu-app dispatch).

3. **PROOF IMPACT:** Updated `subCheckNF_self_elim_step` in Eval.lean to match.
   The proof is simpler — just `ih_abs` + `ih_sub` on the components, without
   needing the `seen'` propagation.

4. **TEST IMPACT:** All tests pass (DNat, Array, Vec, appendVec). Added
   transitivity regression tests in Tests.lean.

5. **PROOF LANDSCAPE:** The self-elim body path in adequacy_gen is now
   unblocked from the circular seen dependency. Body path proof strategy:
   - Case-split on VCompat(m+1, v, mu ann body)
   - mu-left, inferType, asc-left cases: work via ih_n (no step loss)
   - refl case: works via mu-left + absEval_preserves + ih_fuel
   - structural mu: works via absEval_preserves + ih_fuel + mu-left
   - mu-right/normalized mu-right: STUCK — loses one step, can't recover
   - Annotation path: still blocked by annotation-trust (Phase 0)

### What happened in previous session (agent ochre-20260405-003633)

**Found absEval_preserves counterexample + added asc-left disjunct to VCompat.**

1. **CRITICAL: absEval_preserves was FALSE.** Found concrete counterexample
   (see "Key insight" section below). The issue: VCompat had no mechanism to
   "look through" ascriptions on the value side. Since mu-left unfolding can
   introduce asc nodes in the value position, this was a real bug.

2. **DEFINITION CHANGE: Added asc-left disjunct to VCompat** (10th disjunct).
   `∨ (∃ term tyAsc, v = .asc term tyAsc ∧ VCompat n term τ)`.
   Semantically correct: concEval erases ascriptions. Costs one step.

3. **Fixed all cascading proofs:** VCompat.mono (new case), VCompat.bvar_inferType
   (new case + Or.inl wrappers for inferType constructions), VCompat.adequacy_gen
   (two rcases sites: lam-lam and app-app structural, both got asc-left cases).

4. **Expanded absEval_preserves from 1 blanket sorry to 12 specific cases:**
   3 proved (mu-left, inferType, asc-left via IH on n), 9 sorry'd with clear
   documentation. The 9 sorrys reduce to 2 fundamental blockers: normalization
   coherence and annotation normalization congruence.

### What happened this session (agent ochre-20260405-003615)

**Proved neutral app sub-cases + deep analysis of proof architecture.**

1. **Proved neutral app sub-cases in absEval_preserves (refl-app + structural app).**
   When absEval(app fT aT) normalizes fT→fT' and fT'.val is neutral (bvar, app,
   asc — not lam or mu), the result is ⟨app fT'.val aT'.val⟩. VCompat via
   structural app disjunct + IH on sub-expressions. The lam/mu dispatch sub-cases
   (beta-reduction, mu-app) remain sorry'd because they change the result shape.

2. **Analyzed and documented circular dependency between absEval_preserves and
   adequacy_gen.** The refl-asc case of absEval_preserves needs VCompat.adequacy
   (to go from VCompat(term, sigma.val) + subCheckNF(sigma.val, tau.val) to
   VCompat(term, tau.val)), but adequacy_gen uses absEval_preserves. Solutions:
   - **Combined fuel-induction proof**: Prove both simultaneously by induction on
     fuel, with each having access to the other at lower fuel. This would close
     the refl-asc case. The refl-asc case currently does NOT arise at use sites
     (e comes from inferType → NfExpr, never asc), so this is low priority.
   - **Restructuring**: Move absEval_preserves after adequacy_gen, but inline the
     chain at the bvar use sites in adequacy_gen.

3. **Analyzed self-elim callback circularity.** The self-elim cases in adequacy_gen
   (σ=mu, τ∈{lam,bvar,asc,app}) are fundamentally blocked by the seen-set callback:
   the annotation path subcheck at fuel k uses seen' = (mu, τ) :: seen, and the
   callback for this new entry requires VCompat(v, τ) — exactly the goal. Breaking
   this requires either:
   - A WellAnnotated precondition (weakening the theorem)
   - Proving annotation correctness (the annotation describes the mu's behavior)
   - Avoiding the annotation path entirely (using only the body normalization path,
     which needs absEval_preserves)

4. **Verified the asc counterexample is INVALID** after the asc-left fix.
   VCompat(2, asc(lam T bvar0, lam T T), lam T T) IS true via asc-left +
   semantic lam at step 1. The asc-left disjunct correctly handles this case.

### What happened in previous session (agent ochre-20260404-235445)

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

### Sorry categorization (22 in Soundness, 0 in Subtyping)

The remaining sorrys fall into 5 categories:

**Category A: absEval_preserves sub-cases (9 sorrys, Soundness.lean:383-422)**
- 3 cases PROVED (mu-left, inferType, asc-left — all via IH on n)
- 9 sorrys remain, reducing to 2 fundamental blockers:
  (a) **Normalization coherence**: absEval(body) and raw body have same semantics
      under VCompat. Affects: refl-lam, refl-app, semantic lam, structural app.
  (b) **Annotation normalization congruence**: absEval(ann) preserves mu semantics.
      Affects: refl-mu, structural mu, mu-right, normalized mu-right.
  Plus: refl-asc (1 sorry) which needs VCompat.adequacy (circular dependency
  with adequacy_gen; does NOT arise at current use sites).

**Category B: Structural lam-lam (2 sorrys, Soundness.lean:550/553)**
- Refl: v = lam _dS _bS, need VCompat (m+1) (lam _dS _bS) (lam _dT _bT)
- Semantic lam: v = lam domV bodyV, need to transport body compatibility
- BLOCKER: substitution lemma — connecting subCheckNF(bodyS, bodyT) under
  extended context to VCompat after substituting concrete arguments. The
  semantic lam quantifies over ALL fuel levels.

**Category C: Self-elim / annotation-trust (4 sorrys)**
- σ = mu, τ ∈ {lam, bvar, asc, app} (lines 587, 618, 649, 769)
- BLOCKER: annotation-trust gap. subCheckNF's mu self-elim tries the
  annotation first, then body normalization. Both paths need guarantees
  that VCompat is preserved. The body path IS provable with
  absEval_preserves (but absEval_preserves is itself sorry'd for these cases).

**Category D: InferType fallback σ=app (4 sorrys)**
- σ = app, τ ∈ {lam, bvar, asc} (lines 605, 636, 667) + app-app fallback (766)
- BLOCKER: needs app_inferType lemma + absEval_preserves.
  σ = bvar cases are DONE (via bvar_inferType + absEval_preserves).

**Category E: Soundness main cases (3 sorrys, Soundness.lean:927, 934, 941)**
- lam: semantic lam all-fuel issue
- mu: annotation normalization (ann vs ann'.val)
- app: combines all above issues

### Recommended next steps (updated 2026-04-05)

1. **Normalization coherence** — The single biggest blocker. Need to show
   that absEval doesn't change the semantic behavior of terms under VCompat.
   This is essentially the correctness of absEval. Possible approaches:
   (a) Prove absEval idempotency on NfExprs (if e is already normalized,
       absEval returns the same thing). This would handle most practical cases.
   (b) Prove a "semantic normalization" lemma: VCompat(n, e, absEval(e).val)
       for appropriate e. This is close to absEval_preserves's refl case.
   (c) Change the soundness proof to avoid going through un-normalized types.

2. **Substitution lemma** — For lam-lam refl/semantic cases in adequacy_gen.

3. **app_inferType lemma** — Like bvar_inferType but for app.

4. **Self-elim / annotation-trust** — The body normalization path would work
   if absEval_preserves were fully proved. The annotation path remains the
   fundamental Phase 0 issue from SUGGESTIONS.md.

5. **Soundness main cases** — Lex/strong induction on fuel for lam/app.

### Key insight from this session

**absEval_preserves was FALSE before the asc-left fix.** The counterexample:
- v = e = asc (lam Type (bvar 0)) (lam Type Type)
- VCompat(2, v, v) via refl
- absEval(v) = ok ⟨lam Type Type⟩
- VCompat(2, asc(...), lam Type Type) was FALSE — no disjunct handled asc on value side

The fix (asc-left disjunct) is semantically correct: at runtime, concEval erases
ascriptions, so `(e : τ)` behaves like `e`. The disjunct costs one step to prevent
infinite chains. All existing proofs updated.

**Most remaining sorrys reduce to 2 fundamental problems:**
1. Normalization coherence (absEval doesn't change semantics)
2. Annotation trust (mu annotations are correct)
Both are aspects of "absEval is semantically correct", which is deeply intertwined
with the soundness theorem itself.

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
- All tests pass (`lake build` succeeds with sorrys only in Soundness)
- appendVec type-checks with abstract arguments
- `concEval_fuel_mono` proved
- `absEval_fuel_mono` proved
- `subCheckNF_fuel_mono` proved
- `VCompat.from_type_sub_gen` proved
- VCompat.mono, VCompat.mono_le, VCompat.refl, VCompat.fixpoint_mu,
  VCompat.self_intro_eq, VCompat.fixpoint_mu_left all proved
- VCompat.bvar_inferType proved
- VCompat.absEval_preserves partially proved (3/12 cases)
- SubtypeCore.trans, Subtype'.trans proved
- **VCompat is meaningful** (not trivially true)
- **VCompat has asc-left disjunct** (fixes false absEval_preserves)
- **App-app structural congruence fully proved** in adequacy_gen (incl. asc-left)

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

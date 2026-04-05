# Progress

## Current state (2026-04-05)

Och is feature-complete for the current milestone. All tests pass, including
the north star (`appendVec` with abstract arguments). The focus is now on
proving soundness.

### Sorry inventory (6 in Soundness, 0 in Eval, 0 in Syntax)

6 sorry DECLARATIONS total (53 individual sorry occurrences):
- Soundness.lean (6): app_inferType, absEval_preserves, adequacy_gen,
  subCheckNF_substEnv, absEval_preserves_VCompat_substEnv, soundness_open.
- Eval.lean: 0 sorrys.
- Syntax.lean: 0 sorrys.

Summary of session ochre-20260405-205523:

**PROVED: subCheckNF_substEnv lam-lam case** (Soundness.lean:1384)

The lam-lam case of subCheckNF_substEnv was the highest priority from previous sessions.
The proof required:

1. **Generalized theorem signature**: Added depth parameter `d` for closedAt flexibility
   and made `ctx'` a universal parameter (not existential). The depth d=0 at top level,
   d+1 under binders. The body case uses liftEnvN 1 γ (entries closedAt d+1) with
   extend ctx' ⟨domB.substEnv γ⟩.

2. **Helper lemmas**: `liftEnvN_closedAt_succ` (liftEnvN entries are closedAt d+1 when
   γ entries are closedAt d) and `TyCtx_extend_ctx_wf` (extending a well-formed context
   preserves well-formedness at d+1).

3. **Proof by induction on fuel**: The domain IH uses same d, same ctx'. The body IH
   uses d+1 and extend ctx' ⟨domB.substEnv γ⟩. Fuel alignment via subCheckNF_fuel_mono_le.

**Also completed:**
- Added `closedAt` field to FunEnvCompat (4th component). This closes the sorry at the
  call site where γT entries need closedAt 0. Propagated through nil, cons, mono, mono_le.
- Added `aT.closedAt 0` hypothesis to VCompat's semantic lam disjunct (needed for
  FunEnvCompat.cons in soundness_open's lam case).
- Closed the γT closedAt sorry in soundness_open's asc case.

**ANALYSIS: Remaining blockers (unchanged from previous sessions):**

1. **Mu case of soundness_open** (2 sorrys, lines 1802/1827): Needs VCompat m on
   unfolded bodies `body.substEnv(mu_V :: γV)` and `body.substEnv(mu_T :: γT)`. Cannot
   use soundness_open IH because concEval doesn't evaluate the mu body (mu is a value).
   Joint (fuel, expr) induction does NOT help here — the issue is fundamentally about
   mu bodies never being evaluated at runtime. Possible approaches:
   - Add a "mu unfolding at definition site" case to soundness_open that uses the absEval
     body check as evidence
   - Strengthen VCompat's structural mu to carry a proof obligation that can be discharged
     by the body check
   - Neither approach has been attempted yet.

2. **App lam-lam case of soundness_open** (2 sorrys, lines 2015/2033): Step-loss from
   semantic lam extraction. Joint (fuel, expr) induction WOULD help here: the beta-reduced
   expression uses fuel fk < fk+1, so the IH applies directly without extracting the
   semantic lam.

3. **absEval_preserves hard cases** (5 sorrys): refl-lam (normalization coherence),
   semantic lam (same), app beta/mu-app (shape change), refl-asc (needs adequacy).

**RECOMMENDED NEXT STEPS:**

1. **Attempt joint (fuel, expr) induction for soundness_open.** This resolves the
   step-loss problem in the app lam-lam case. Use well-founded recursion on
   (fuel, sizeOf e) with Prod.Lex ordering. The mu case remains blocked.

2. **Investigate the mu case further.** The core issue: mu is a value, so concEval
   returns it immediately without evaluating the body. But the structural mu VCompat
   disjunct requires VCompat on the unfolded bodies, which needs evaluation. This might
   require a new proof technique or a change to VCompat's mu disjuncts.

3. **Remaining subCheckNF_substEnv cases** (lines 1450-1451): non-lam σ vs lam τ
   (inferType fallback) and τ = mu/app/bvar/asc. These require absEval_substEnv
   commutation and are lower priority.

Summary of session ochre-20260405-ctx-irrelevance:

**PROVED: All remaining Eval.lean sorrys (ctx_irrelevant theorem)**

The mutual `ctx_irrelevant` theorem in Eval.lean is now fully proved. This
establishes that `subCheckNF` and `absEval` depend only on the first `d` entries
of the context when terms are `closedAt d`. The proof required:

1. **`inferType_closedAt`**: induction on `e generalizing d ty`, with careful
   case analysis for `app` (uses `subst_closedAt`).

2. **`isCallableNF_ctx_irrelevant`**: dispatches non-lam/non-mu cases via
   `inferType_ctx_irrelevant`.

3. **`TyCtx_extend_wf`**: both `0` and `succ j` cases proved using
   `shift_closedAt`.

4. **`ctx_irrelevant` mutual proof** (the main work):
   - subCheckNF branch: used `cases b` approach to avoid `rename_i` issues;
     extracted `inferType_fallback` and `self_elim` helpers; app-app case used
     `simp only [hf_eq, ha_eq]` (not `rw`) since match variables get renamed.
   - absEval branch: lam case uses `TyCtx_extend_ctx_irrelevant` and
     `TyCtx_extend_wf`; mu case uses `cases lenient` with `simp`; asc case
     uses `ih_sub`; app case handles all sub-cases including mu-app (split
     following absEval's match structure, with `next` to get named vars after
     split) and neutral app (via `isCallableNF_ctx_irrelevant`).

Key fix for `simp only [hf_eq, ha_eq]` in app-app: the `split` tactic renames
match pattern variables (e.g., `f1` → `f1_1`), so `rw` fails but `simp only`
succeeds because it matches up to renaming.

Key fix for mu-app case 2 (body = lam, ann ≠ lam): after `split`, the `body`
variable is eliminated. Used `next _dom _retBody _` to name the fresh variables,
then `Expr.lam _dom _retBody` explicitly throughout.

Key fix for mu case (lenient branches): `simp only [Bool.not_false, ite_true,
h_body_check]` closes the false/lenient case; `simp [Bool.not_true]` closes
the true/lenient case.

This fully unblocks the lam-lam case of `subCheckNF_substEnv` in Soundness.lean.

Previous note: The total sorry count in Soundness.lean remains at ~34
(expanded from ~25 by agent ochre-20260405-181325). Refl, structural mu,
and impossible sub-cases are PROVED.

Summary of changes by agent ochre-20260405-184922:

**TWO NEW RESULTS, ONE IMPROVED PROOF STRUCTURE:**

1. **PROVED: `substEnv_closedAt`** (Syntax.lean:916). New infrastructure lemma:
   if `e.closedAt γ.length` and all entries of γ have `closedAt d`, then
   `(e.substEnv γ).closedAt d`. Proved by structural induction on e. Handles
   binder lifting correctly (lift γ entries have closedAt (d+1) via shift_closedAt).
   **USE CASE:** enables reasoning about closedness of substituted terms, needed
   for ctx-irrelevance arguments in subCheckNF_substEnv and other lemmas.

2. **STRUCTURED: soundness_open mu case** (Soundness.lean:1672-1708). Both
   lenient=false and lenient=true branches now:
   - Handle n=0 trivially (VCompat 0 = True)
   - At n+1: use structural mu disjunct, apply substEnv_subst_comp to rewrite
     unfolded bodies from `(body.substEnv(lift γX)).subst 0 mu_X` to
     `body.substEnv(mu_X :: γX)`. Leaves a targeted sorry:
     **VCompat m (body.substEnv(mu_V :: γV)) (body.substEnv(mu_T :: γT))**
   This replaces two monolithic sorrys with a clear, specific blocker.

3. **EXPANDED: subCheckNF_substEnv lam-lam case** (Soundness.lean:1359-1386).
   Extracted the two sub-checks (domain: subCheckNF k ctx [] domB domA,
   body: subCheckNF k (extend ctx ⟨domB⟩) [] bodyA bodyB) from the hypothesis.
   Documented the ctx alignment blocker: the IH gives existential ctx for each
   sub-check, but the combined lam-lam check needs them at the SAME ctx.

**ANALYSIS: Three fundamental blockers identified (refined from previous sessions):**

1. **VCompat reflexivity under related environments** — needed by:
   - soundness_open mu case (VCompat m (body.substEnv(mu_V :: γV)) (body.substEnv(mu_T :: γT)))
   - Would also help the app cases via the "concEval preserves VCompat" angle
   **Status:** Cannot be proved independently — the lam case requires concEval
   to succeed (semantic lam's conditional), which needs soundness-like reasoning.
   Must be proved jointly with soundness_open (via joint induction) or bypassed.

2. **Context irrelevance for closed terms** — ✅ PROVED (agent ochre-20260405-193641)
   - subCheckNF_ctx_irrelevant and absEval_ctx_irrelevant FULLY PROVED in Eval.lean
   - Also proved: inferType_closedAt, isCallableNF_ctx_irrelevant, TyCtx_extend_wf,
     absEval_preserves_closedAt_d (generalized at any depth d), closedAt_mono
   - NOTE: the theorem now requires a `hctx_wf` well-scopedness condition:
     ctx entries at positions < d must have closedAt d values. This is satisfied
     at the call site (d=0 is vacuous; under binders, TyCtx.extend preserves it).

3. **Step-loss in semantic lam extraction** — blocks:
   - soundness_open app lam-lam (semantic lam gives VCompat at step n, need n+1)
   - adequacy_gen self-elim mu-right sub-cases
   **Status:** Joint (fuel, expression) induction remains the recommended fix
   (see SUGGESTIONS.md). Alternative: prove everything at VCompat n (not n+1)
   by accepting one step of "slack" throughout — would require weakening the
   soundness theorem's conclusion, which may or may not be acceptable.

**RECOMMENDED NEXT STEPS (updated priority order):**

1. **HIGHEST PRIORITY: Close `subCheckNF_substEnv` lam-lam case** (Soundness.lean).
   ctx_irrelevant is now PROVED. The 7-step strategy documented at Soundness.lean:1382
   can now be executed. Steps: (1) recursive IH on domain/body, (2) substEnv_closedAt,
   (3-4) ctx_irrelevant at d=0 and d=1, (5) fuel_mono_le, (6-7) construct combined check.
   The new `hctx_wf` parameter is vacuous at d=0 and satisfiable at d=1 (TyCtx_extend_wf).
   results. At each case, show that closedAt d terms only access the first d entries.
   Under binders, d increases by 1 and ctx extends with the SAME entry (from the
   binder), so entries 0..d all match. ~200 lines, mechanical but critical.
   **UNBLOCKS:** subCheckNF_substEnv lam-lam case (complete 7-step proof strategy
   documented at Soundness.lean:1383). Also useful for other subCheckNF reasoning.

2. **Also needed for subCheckNF_substEnv call site:** Show γT entries are closedAt 0
   (Soundness.lean:1876, sorry). Options: (a) add closedAt 0 to FunEnvCompat defn,
   (b) prove ConcNF → closedAt 0 (since ConcNF values are lam/mu/type/neutral app,
   all closedAt 0 if their sub-expressions are). The simplest fix is (b).

3. **Attempt joint (fuel, expr) induction for soundness_open.** This unblocks the
   step-loss problem and the mu reflexivity problem simultaneously. The approach:
   use well-founded recursion on (fuel, sizeOf e) with Prod.Lex ordering. For lam:
   body is structurally smaller. For app: beta-reduced expression has less fuel.
   For mu: need n-induction within the VCompat goal (nested induction on step count).

4. **Prove absEval_preserves for the easy remaining cases** (refl-mu is done,
   mu-right is done, etc. — focus on refl-app neutral and structural app neutral
   which should follow from structural app + IH).

Summary of changes by agent ochre-20260405-181325:

**EXPANDED 4 self-elim sorrys in adequacy_gen into detailed case analyses.**

The 4 self-elim sorrys (σ=mu, τ∈{lam,bvar,asc,app}) were monolithic blockers.
Each is now expanded into 10 VCompat sub-cases with specific proof status:

**PROVED sub-cases (for any seen):**
- Refl (v = σ = mu): Strategy A — mu-left + VCompat.refl + absEval_preserves +
  ih_fuel at step m+1. Callback = hseen. Works because absEval_preserves and
  ih_fuel both use the ORIGINAL v, not the unfolded body.
- Structural mu (v = mu annV bodyV): Same strategy via mu-left wrapper.
- Impossible (type, semantic lam, structural app): constructor mismatch.

**PROVED sub-cases (seen = [] only):**
- Mu-left: Strategy B — ih_n with hcheck_orig and vacuous callback.
- InferType: Same strategy.
- Asc-left: Same strategy.

**REMAINING sorrys per self-elim case (7 each × 4 cases = 28 total):**
1. Body eval failed (annotation path only): 1 — rare, needs annotation trust
2. Mu-right step-loss: 1 — VCompat m, need m+1. Fundamental.
3. Normalized mu-right step-loss: 1 — same issue.
4. Mu-left seen≠[]: 1 — callback mismatch (ih_n needs VCompat for inner, hseen has outer v)
5. InferType seen≠[]: 1 — same callback mismatch.
6. Asc-left seen≠[]: 1 — same callback mismatch.
7. Body subcheck failed (annotation path only): 1 — rare.

**KEY INSIGHT (corrected from previous analysis):** Strategy A works for ANY
seen, not just seen=[]. The trick is to use absEval_preserves and ih_fuel
at step m+1 with the ORIGINAL v (not unfolded_v). This avoids the callback
mismatch entirely because hseen is about v at step m+1, which matches.

**For VCompat.adequacy (the main caller, seen=[]):** 8 of 10 sub-cases proved
per self-elim sorry. Only mu-right and normalized mu-right remain (step-loss).

**ANALYSIS: soundness_open mu case (2 sorrys, lines 1668/1675) is BLOCKED.**

The goal is VCompat n (mu ..V..) (mu ..T..) where V and T use different
environment substitutions. The structural mu disjunct requires VCompat on
unfolded bodies, which are body.substEnv(mu_V :: γV) and body.substEnv(mu_T :: γT).
Using ih_body requires concEval to succeed on the unfolded body, which we don't
have (concEval of a mu just returns the mu value itself, it doesn't evaluate
the body). N-induction on the step count helps with FunEnvCompat (can build
VCompat m mu_V mu_T from the IH), but still can't provide concEval on the body.

Possible approaches (none attempted):
1. Prove a "VCompat reflexivity under related environments" lemma:
   ∀ e n γV γT, FunEnvCompat n γV γT → VCompat n (e.substEnv γV) (e.substEnv γT).
   PROBLEM: Lam case requires semantic lam, which needs concEval to succeed.
2. Change VCompat's structural mu to not require VCompat on unfolded bodies.
   PROBLEM: Would break other proofs that rely on structural mu.
3. Add a new VCompat disjunct for "mu with related environments".
   PROBLEM: Major refactoring of VCompat and all proofs.
4. Joint (fuel, expression) induction — the recommended approach from SUGGESTIONS.md.
   This gives a stronger IH but still has the concEval requirement for mu bodies.

**RECOMMENDED NEXT STEPS (updated):**
1. Focus on the step-loss problem (mu-right sub-cases of self-elim + app lam-lam).
   Joint (fuel, expr) induction remains the most promising approach.
2. The mu case of soundness_open needs a fundamentally new approach or a
   "VCompat reflexivity under related environments" lemma that handles the
   concEval requirement for lam bodies.
3. subCheckNF_substEnv lam-lam case needs context independence for closed terms.
4. lam-lam sorrys in adequacy_gen (lines 758, 761) need subCheckNF_substEnv.

Summary of changes by agent ochre-20260405-172626:

**THREE CHANGES:**
1. Detailed case analysis of adequacy_gen self-elim (4 sorrys), identifying
   which sub-cases are provable and which are blocked. See analysis below.
2. Generalized subCheckNF_substEnv conclusion from `∃ fuel'` to `∃ fuel' ctx'`
   (existential context) — the old statement was unprovable for lam-lam body case.
3. Proved 2 easy cases of subCheckNF_substEnv (equality and type).

**ANALYSIS: adequacy_gen self-elim (4 sorrys: mu-lam, mu-bvar, mu-asc, mu-app)**

Performed detailed case analysis of the VCompat disjuncts in the self-elim proof.
Each self-elim sorry expands into ~10 VCompat sub-cases. Two proof strategies
were identified, covering 7 of 10 sub-cases:

**Strategy A** (body path + absEval_preserves + ih_fuel, at step m+1):
- Refl: v = mu ann body. Construct VCompat (m+1) v bsm via mu-left + VCompat.refl m.
  Then absEval_preserves + ih_fuel at step m+1. Callback = hseen. ✓
- Structural mu: v = mu annV bodyV. Same approach via mu-left wrapper. ✓
- Mu-right: BLOCKED. VCompat m v bsm (step m, not m+1). Can't upgrade to m+1.
- Normalized mu-right: BLOCKED. Same step-count issue.

**Strategy B** (ih_n + VCompat wrapper, at step m):
- Mu-left: VCompat m (unfolded v) (mu). ih_n gives VCompat m (unfolded v) τ.
  Then mu-left wrapper: VCompat (m+1) v τ. ✓ when seen = [].
- InferType: VCompat m ty' (mu). ih_n gives VCompat m ty' τ.
  Then inferType wrapper. ✓ when seen = [].
- Asc-left: VCompat m term (mu). ih_n gives VCompat m term τ.
  Then asc-left wrapper. ✓ when seen = [].
- ALL THREE FAIL when seen ≠ []: ih_n callback needs VCompat m inner_expr p.2,
  but hseen gives VCompat (m+1) v p.2 where inner_expr ≠ v. Callback mismatch.

**Impossible cases** (3): type, semantic lam, structural app — mu can't match these. ✓

**Summary of blockers:**
1. **Step count** (mu-right, normalized mu-right): mu-right disjunct at step n+1
   gives VCompat n (one step less). absEval_preserves + ih_fuel preserve the step
   level but can't increase it. Fundamental limitation of step-indexed LR.
2. **Callback mismatch** (mu-left, inferType, asc-left when seen ≠ []): ih_n's
   callback is about the inner expression, not the outer v. hseen is about v.
   When seen = [] (from VCompat.adequacy), the callback is vacuous and works.
3. **Annotation trust** (annotation path): VCompat v (mu ann body) doesn't imply
   VCompat v ann. With Phase 0, absEval checks bodies, but the proof doesn't
   carry this info into adequacy_gen.
4. **Body path extraction**: simplifying hcheck to extract absEval/subCheckNF
   results from the self-elim's if-then-else structure. Mechanical but non-trivial.

No code changes (analysis only). The sorry count is unchanged at 6 declarations.

**RECOMMENDED NEXT STEPS (updated priority order):**

1. **Resolve the step-count issue** — this blocks both self-elim (mu-right sub-case)
   AND soundness_open's app lam-lam case. The most promising approach remains
   joint (fuel, expression) induction per agent ochre-20260405-163526's analysis.

2. **Prove self-elim for seen = []** — Strategy A (refl + structural mu) works for
   any seen. Strategy B (mu-left + inferType + asc-left) works when seen = [].
   Together with the impossible cases, this covers 8/10 sub-cases (only mu-right
   and normalized mu-right remain). Could be done as partial progress by expanding
   the sorrys into case analyses with localized sorrys.

3. **Prove absEval_preserves** — needed by Strategy A and many other places.
   The easy cases (mu, refl-bvar, refl-type) are done. The hard cases (lam
   normalization, app beta-reduction) require normalization coherence.

4. **Prove subCheckNF_substEnv** — standard property but needs careful handling
   of context changes through binders and absEval commutation for mu cases.

Changes by agent ochre-20260405-163526:

**GENERALIZED soundness_open over `lenient : Bool` parameter.**

Three changes:
1. **soundness_open** (Soundness.lean:1317) now takes `(lenient : Bool)` and
   `(h_abs : absEval fuel ctx [] e lenient = .ok τ)`. This allows ih_body
   to be applied with lenient=true (matching the mu body check's absEval call).
   ALL proved cases (bvar, type, lam, asc, app neutral) remain proved.

2. **absEval_fuel_mono_le** (Soundness.lean:1172) generalized with `{lenient : Bool}`.

3. **absEval_preserves_closedAt** (Eval.lean:910) generalized with `{lenient : Bool}`.
   The mu case uses `split at h_abs` to handle both lenient values (body check
   fires or not), but in both cases the output is `⟨mu ann body⟩` so closedAt
   is just the input closedAt.

**STATED absEval_preserves_VCompat_substEnv** (Soundness.lean:1299, 1 sorry).
Key bridge lemma: if VCompat n v (e.substEnv γ) and absEval normalizes e to τ,
then VCompat n v (τ.val.substEnv γ). This is NOT a corollary of absEval_preserves
(which operates on e, not e.substEnv γ). Needed for app lam-lam semantic lam case.

**ANALYZED: Three fundamental blockers identified.**

1. **Step-loss in app lam-lam** (Soundness.lean:1600): The semantic lam at step
   n+1 quantifies over j ≤ n, giving VCompat n on the result. But the goal is
   VCompat (n+1). One step is consumed by the lambda application. This is a
   well-known issue in step-indexed logical relations. The composition chain
   (semantic lam → subst_substEnv_comm → absEval_preserves_VCompat_substEnv)
   is correct but produces VCompat m, not VCompat (m+1).
   
   **Potential fix**: Change VCompat so application doesn't cost a step. Options:
   - Make semantic lam quantify over all j (not j ≤ n). Requires making VCompat
     well-founded without the step bound — possibly via inductive type instead
     of recursive def. MAJOR refactoring.
   - Switch to fuel-based induction for the app case (fuel decreases for
     beta-reduced expressions). Would require joint induction on (fuel, expr).
   - Accept VCompat (n-1) in soundness_open's conclusion (weaker theorem).

2. **Normalization gap in mu case** (Soundness.lean:1390): ih_body gives VCompat
   on body_abs'.val.substEnv (normalized body), but structural mu disjunct needs
   VCompat on body.substEnv (raw body). The concEval gap (need evaluated result,
   not raw expression) compounds this.

3. **absEval_preserves_VCompat_substEnv** (Soundness.lean:1299): Standalone
   version of the normalization gap. Not a corollary of absEval_preserves because
   absEval and substEnv don't commute in general.

**TESTED AND REJECTED: ∀ n conclusion for soundness_open.** The idea was to
strengthen the conclusion from `VCompat n` to `∀ n, VCompat n`, with
`h_env : ∀ n, FunEnvCompat n`. This would let the app case extract the semantic
lam at step n+2 (instead of n+1), recovering the lost step. PROBLEM: the lam
case BREAKS. The semantic lam provides VCompat j aV aT for a specific j (from
the quantifier ∀ j ≤ m). To build `∀ n, FunEnvCompat n (aV :: γV) (aT :: γT)`
for ih_body, we'd need `∀ n, VCompat n aV aT`. But the semantic lam only gives
VCompat at step j, not at all steps. The lam and app cases have OPPOSING
requirements: lam needs specific-n environments (from semantic lam), app needs
∀ n environments (to extract semantic lam at higher step).

**NOTE: Inductive VCompat would also fail** for the same reason — the semantic
lam constructor would have VCompat in negative position (left of →), violating
strict positivity.

**RECOMMENDED NEXT STEPS (updated priority order):**

1. **Resolve the step-loss via joint (fuel, expression) induction.** This is the
   most promising approach. Instead of pure expression-structure induction, use
   well-founded recursion on (fuel, expr.size) lexicographically. For the lam case,
   body is structurally smaller (same fuel). For the app case, the beta-reduced
   expression has strictly less fuel (fk < fk+1), regardless of expression size.
   This sidesteps the step-loss because the IH for the beta-reduced expression
   comes from fuel decrease, not from extracting a semantic lam.
   The semantic lam disjunct would still exist in VCompat (for compositionality),
   but the app case wouldn't NEED to extract it from ih_fV.

2. **Prove absEval_preserves_VCompat_substEnv.** Needed regardless of the
   induction strategy. Approaches: (a) show absEval commutes with substEnv for
   normalized environments, (b) case analysis on absEval + substEnv interaction.

3. **Prove mu case** via structural mu + n-induction. Blocked by (2) and by the
   concEval gap (structural mu requires unconditional VCompat on unfolded bodies,
   but ih_body only gives VCompat when concEval succeeds).

Changes by agent ochre-20260405-152415:

**PHASE 0 RESOLVED: absEval now checks mu bodies at definition site.**

Three changes to absEval (Eval.lean):

1. **Mu body check** (Eval.lean:164): absEval's mu case now evaluates the body
   under an extended context with self bound to ⟨mu ann body⟩. This fires
   only when `!lenient` (i.e., during top-level normalization, not during the
   lenient body-check sub-evaluation). The body check uses `lenient=true`.

2. **Optimistic domain check** (Eval.lean:186): In lenient mode, skip domain
   check for neutral arguments (bvar, app). `subCheckNF || (lenient && isNeutral)`.
   Essential for mu body checking where Church-encoded types with abstract lambda
   parameters create stuck type-level computations that can't be structurally
   compared.

3. **Optimistic callability** (Eval.lean:220): In lenient mode, accept all
   neutral applications. `isCallableNF || lenient`. Essential for the same reason.

The `lenient : Bool := false` parameter on absEval controls this:
- `lenient=false` (default): strict checks, fires body check on mus
- `lenient=true` (body check only): optimistic domain/callability, no body check

SubCheckNF calls absEval with default `lenient=false`, so subCheckNF's intermediate
normalizations are completely unaffected. The optimistic behavior ONLY fires during
the mu body check evaluation.

**All tests pass** including appendArrays, appendVec, and the appendVec_wrong
negative test (which confirms the type checker still catches bugs in dependent types).

**Eval.lean proofs fully restored:** fuel_mono generalized over `lenient`
parameter; preserves_closedAt uses `split at h_abs` to handle the conditions.
0 sorrys in Eval.lean.

**Helper: Expr.isNeutral** (Syntax.lean:65): `bvar → true | app → true | _ → false`.

**NEXT STEPS:**
1. **Prove soundness_open mu case** (Soundness.lean:1364): with the body check,
   ih_body is now available. Use induction on n to build FunEnvCompat for extended
   environments (self = mu), then apply ih_body. Note: need to handle the
   mismatch between ih_body's result (VCompat with body'.val.substEnv γT_ext) and
   the structural mu disjunct (VCompat with body.substEnv γT_ext). May need
   absEval_preserves or a bridging lemma.
2. **Continue with remaining soundness sorrys** per SUGGESTIONS.md Phase 2-4.

Changes by agent ochre-20260405-091658:

**RESOLVED: isConcreteVal blocker for lam-lam sub-case (Eval.lean + Soundness.lean).**

Defined `ConcNF : Expr → Prop` (Eval.lean:435), an inductive characterizing
ALL concEval output shapes: lam, type, mu, and neutral apps (function not
lam/mu, sub-expressions ConcNF). Proved `concEval_ConcNF` (concEval always
produces ConcNF) and `ConcNF_concEval_idem` (ConcNF values are idempotent
under concEval — if concEval succeeds on a ConcNF value, it returns it
unchanged). Updated VCompat, ConcreteValEnv, FunEnvCompat to use ConcNF
instead of the old lam/type/mu-only match pattern. Updated soundness_open
bvar case to use ConcNF_concEval_idem.

In soundness_open's app lam-lam sub-case (Soundness.lean:1533): the ConcNF
guard is now discharged via `concEval_ConcNF haV`.

**IDENTIFIED: step-loss blocker for lam-lam sub-case (fundamental issue).**

After discharging the ConcNF guard, the semantic lam from ih_fV gives
VCompat m (one step less). But the goal is VCompat (m+1). This is a
fundamental limitation of step-indexed logical relations: application
"costs one step." The semantic lam at step m+1 quantifies over j ≤ m
(structurally required for VCompat's well-founded recursion on Nat).
The gap between VCompat m and VCompat (m+1) CANNOT be resolved within
the current VCompat definition and induction strategy.

Analysis of potential fixes:
- Step-free FunEnvCompat (∀ n, VCompat n): solves the app case but causes
  circular reference in VCompat definition (semantic lam would need to
  reference VCompat at the same step, which Lean's structural recursion rejects)
- Fuel induction: gives smaller fuel for beta-reduced body, but the
  dual-substitution problem persists (concrete body ≠ abstract body)
- n-induction: gives VCompat m by IH but not VCompat (m+1) — same gap
- Offset precondition (FunEnvCompat n+1 → VCompat n): the IH applies the
  same offset, so the gap is unchanged

**TESTED AND REJECTED: mu body check at definition site (suggested in SUGGESTIONS.md).**

Tried checking mu bodies at definition site:
```lean
let ann' ← absEval fuel ctx seen ann
let body' ← absEval fuel (TyCtx.extend ctx ann') seen body
```

Result: absEval FAILS on the body for Church-encoded types. When self is
bound to the annotation type (bvar 0 → ⟨type⟩ for dBool, or ⟨bvar k⟩ for
inner mus), the body evaluation encounters domain check failures because:
1. Self is abstract (bvar), so applying self to arguments hits domain checks
2. Inner mus (dtrue, dfalse) have symbolic bvar annotations, and their body
   checks cascade with the same problem
3. Even WITHOUT the body' ⊑ ann' subcheck, the body EVALUATION itself fails
   with "domain check failed" for appendArrays and similar complex types

This confirms why the original absEval only validated the annotation:
the body of a mu type is not well-typed in the traditional sense when
self is treated as an opaque type variable. The body's well-typedness
depends on self's RECURSIVE nature, not just its declared type.

The soundness_open mu case remains genuinely blocked by this.

**RECOMMENDED NEXT STEPS (updated):**
1. **Resolve the step-loss blocker** — this is the MOST IMPORTANT problem.
   The most promising approach: change VCompat's semantic lam to not have
   a step bound (quantify over all j, not j ≤ n). This requires making
   VCompat well-founded without the step bound in the semantic lam, possibly
   by using an inductive type instead of a recursive def, or by using
   well-founded recursion on a different measure.
2. **Prove absEval_preserves_VCompat_substEnv** — needed for lam-lam AND
   for bridging from (bodyT.subst 0 aT.val).substEnv γT to τ.val.substEnv γT
3. **Resolve mu case** — fundamentally blocked by absEval not evaluating body
4. Other sorrys (adequacy_gen, subCheckNF_substEnv, app sub-cases)

Changes by agent ochre-20260405-085031:

**PROVED: All 4 Syntax.lean sorrys (Syntax.lean, 0 sorrys remaining).**

Proved three lemmas that provide the de Bruijn infrastructure needed for
soundness_open's app case:

1. `liftEnvN_getElem?_ge` (NEW): entries of liftEnvN at index ≥ c are
   γ[i-c]!.shift c 0. Proof by induction on c, uses shift_succ for the
   composition of shifts at the succ level.

2. `shift_substEnv_liftEnvN` (1 sorry → 0): shifting by c at depth d then
   substituting with liftEnvN (c+d) γ equals substituting with liftEnvN d γ
   then shifting. Proof by induction on s. bvar case uses liftEnvN_getElem?_lt
   and liftEnvN_getElem?_ge, plus shift_shift for composing shifts. Binder
   cases (lam/mu) use the observation that bvar 0 :: (liftEnvN n γ).map shift
   = liftEnvN (n+1) γ.

3. `subst_substEnv_comm_gen` bvar cases (3 sorrys → 0): the three bvar cases
   of the reverse composition lemma.
   - k = c: uses shift_substEnv_liftEnvN with d=0 for the LHS, plus
     liftEnvN_getElem?_ge for the RHS.
   - k > c: both sides reduce to γ[k-1-c]!.shift c 0 via liftEnvN_getElem?_ge,
     plus a List.getElem?_cons_succ identity for the cons-shifted list.
   - k < c: both sides are bvar k via liftEnvN_getElem?_lt.

`subst_substEnv_comm` (the c=0 specialization) was already sorry-free,
derived from `subst_substEnv_comm_gen`.

**NET: -5 sorrys (21 total, was 26). Syntax.lean now fully proved.**

**STRUCTURED: soundness_open app lam-lam sub-case (Soundness.lean:1498-1538).**
Expanded the single sorry into n-case analysis + VCompat disjunct case split.
Proved 8 impossible cases (lam ≠ type/mu/app/asc, inferType lam = none).
Reduced to 2 precise sorrys:
- **Refl case** (1 sorry): bodyV = bodyT.substEnv(lift γT). Needs soundness
  for bodyT under extended env, which is NOT available as IH (bodyT is not a
  sub-expression of `app f a`). May need absEval_preserves_VCompat_substEnv.
- **Semantic lam case** (1 sorry): The main path. Two blockers:
  (a) isConcreteVal for aV (concEval produces concrete values — not proved)
  (b) absEval_preserves_VCompat_substEnv to bridge from raw body substitution
      to absEval-normalized result through substEnv.
  The composition chain: semantic lam gives VCompat on (bodyT'.subst 0 aT'),
  then substEnv_subst_comp + subst_substEnv_comm equate this to
  (bodyT.subst 0 aT.val).substEnv γT, then absEval_preserves bridges to
  τ.val.substEnv γT. All composition lemmas are NOW PROVED.

**REMAINING (all in Soundness.lean, 22 sorrys):**
- adequacy_gen: ~13 sorrys (lam-lam, self-elim, absEval_preserves sub-cases)
- soundness_open: 9 sorrys (mu case, 7 app sub-cases, subCheckNF_substEnv)
- app_inferType: 1 sorry (structural app case)

**MU CASE ANALYSIS (agent ochre-20260405-085031):**
The mu case (Soundness.lean:1341) is genuinely blocked. The goal is
VCompat n mu_V mu_T where mu_V and mu_T have different substEnvs.
Using structural mu requires VCompat n on self-substituted bodies, which
(by substEnv_subst_comp) are body.substEnv(mu_V::γV) and body.substEnv(mu_T::γT).
ih_body requires absEval to succeed on body, but absEval for mu ONLY validates
the annotation — it does NOT evaluate the body. Options explored:
- n-induction: helps for n=0/1 but at n≥2 the unfolded bodies are general
  expressions (not mus), so structural mu can't recurse.
- VCompat.refl: requires γV = γT, not generally true.
- Synthesizing absEval for body: would need to PROVE body is well-typed
  in the extended context, which is not available from the mu's absEval result.
POTENTIAL FIXES: (1) Change absEval for mu to also evaluate body (big change,
may break things). (2) Add WellTyped precondition. (3) Restructure
soundness_open to jointly induct on n and e.

**RECOMMENDED NEXT STEPS (updated priority order):**
1. **Prove `isConcreteVal` for concEval outputs** (~20 lines):
   concEval always returns lam/type/mu (never bvar/app/asc). Needed for
   the semantic lam application in the lam-lam sub-case.
2. **State and prove `absEval_preserves_VCompat_substEnv`** (~100 lines):
   This is the bridge from VCompat's semantic lam (raw substitution) to
   absEval-normalized results through substEnv. Needed for lam-lam sub-case.
3. **Close soundness_open lam-lam sub-case** using the now-proved
   subst_substEnv_comm + (1) + (2) + semantic lam extraction.
4. **Prove subCheckNF_substEnv** (Soundness.lean:1055). Standard property.
5. **Resolve mu case** (Soundness.lean:1341). See analysis above.

Changes by agent ochre-20260405-080723:

**STRUCTURED: soundness_open app case (Soundness.lean:1443-1576).**
Expanded the single sorry into 6 well-defined sub-cases. Proved 3 sub-cases,
showed 4 impossible. Net: +5 sorrys (1 → 6), but the structure is now clear.

**Sub-cases and their status:**

1. **fT.val = lam (abstract function type):**
   - fV = lam (lam-lam): 1 SORRY. The KEY sub-case. Needs:
     (a) Extract semantic lam from ih_fV
     (b) isConcreteVal for aV — problem when aV = app (neutral application)
     (c) substEnv_subst_comp to rewrite body substitution
     (d) `absEval_preserves_VCompat_substEnv` — new helper needed:
         if VCompat n v (e.substEnv γ) and absEval fuel ctx [] e = .ok τ,
         then VCompat n v (τ.val.substEnv γ). This bridges from the semantic
         lam's raw substitution to the absEval-normalized result.
     (e) `subst_substEnv_comm` — new helper needed:
         (e.subst 0 s).substEnv γ = e.substEnv (s.substEnv γ :: γ)
         Standard de Bruijn property, ~50 lines.
   - fV = mu (mu-lam): 1 SORRY. concEval unrolls mu, abstract beta-reduces.
   - fV = type (type-lam): ✅ PROVED. VCompat n type (lam ...) is False for
     n ≥ 1 (no disjunct matches: type ≠ lam/mu/app/asc, inferType type = none).
   - fV = app (app-lam): 1 SORRY. ih_fV can hold via inferType disjunct.
   - fV = bvar: ✅ IMPOSSIBLE (concEval_not_bvar).
   - fV = asc: ✅ IMPOSSIBLE (concEval_not_asc).

2. **fT.val = mu (abstract mu type):** 1 SORRY. Mu-app dispatch.

3. **fT.val = type:** ✅ IMPOSSIBLE (absEval returns error).

4. **fT.val = neutral (bvar/app/asc):**
   - fV = type: ✅ PROVED via structural app + VCompat.mono on ih_fV/ih_aV.
   - fV = app: ✅ PROVED via structural app + VCompat.mono on ih_fV/ih_aV.
   - fV = lam: 1 SORRY. Concrete beta-reduces, abstract stays structural app.
   - fV = mu: 1 SORRY. Concrete mu-unrolls, abstract stays structural app.
   - fV = bvar: ✅ IMPOSSIBLE (concEval_not_bvar).
   - fV = asc: ✅ IMPOSSIBLE (concEval_not_asc).

**KEY INSIGHT: The lam-lam sub-case is the fundamental blocker.** It requires
two new helper lemmas (absEval_preserves_VCompat_substEnv and
subst_substEnv_comm) that don't exist yet. The semantic lam gives VCompat at
the RAW body substitution, but the goal needs VCompat at the NORMALIZED result.
Bridging this gap requires showing that absEval normalization preserves VCompat
through substEnv.

**NET: +9 sorrys (26 total, was 17). Soundness: 1 opaque sorry → 6 structured
sorrys, 3 proved, 4 impossible. Syntax: +4 sorrys for new composition lemmas.**

**Syntax.lean: FULLY PROVED (0 sorrys).** All composition lemmas
(shift_substEnv_liftEnvN, subst_substEnv_comm_gen, subst_substEnv_comm)
are complete. The new liftEnvN_getElem?_ge helper enabled the bvar cases.

**Remaining soundness_open sorrys (9 = 6 in app + 1 in mu + 1 in asc helper
+ 1 in subCheckNF_substEnv):**
- **app sub-cases** (6 sorrys): detailed above
- **mu case** (Soundness.lean:1341): 1 sorry, same as before
- **subCheckNF_substEnv** (Soundness.lean:1055): 1 sorry, same as before

**Remaining adequacy_gen sorrys (13):**
Lines 365, 443, 449, 479, 482, 500, 581, 586, 730, 733, 782, 826, 866.
(Line 1010 may have shifted; these are approximate.)

**RECOMMENDED NEXT STEPS (priority order):**
1. **Close `subst_substEnv_comm` sorrys** (Syntax.lean, ~40 lines remaining):
   STATED with 4 sorrys. Recursive cases all proved. Remaining: prove
   shift_substEnv_liftEnvN (the most substantial helper), then 3 bvar cases.
   shift_substEnv_liftEnvN proof: induction on s, bvar uses shift_shift
   (already proved), binders use IH at d+1. Needs liftEnvN_getElem?_ge
   lemma (entries at index ≥ c = γ[i-c].shift c 0).
2. **State and prove `absEval_preserves_VCompat_substEnv`** (~100 lines):
   VCompat n v (e.substEnv γ) + absEval fuel ctx [] e = .ok τ → VCompat n v
   (τ.val.substEnv γ). Proof by n-induction like absEval_preserves. Needed
   for lam-lam case.
3. **Close lam-lam sub-case** using (1) + (2) + semantic lam extraction.
4. **Prove subCheckNF_substEnv** (Soundness.lean:1055). Standard property.
5. **Work on mu case** (Soundness.lean:1341).

Changes by agent ochre-20260405-074257:

**PROVED: absEval_preserves_closedAt mu-app body-lam case (Eval.lean:904-935).**
The previous agent left 1 sorry due to Lean's match compilation destructuring
`body` after `split`. Fix: use `by_cases` on the seen check (instead of
nested `split`), then `simp only [Expr.subst]` to resolve the unfolded lam
match. The closedAt proof uses `subst_closedAt_gen` with explicit `Nat.add_comm`
rewrites to bridge `1 + ctx.length` vs `ctx.length + 1`.

**DERIVED: soundness from soundness_open (Soundness.lean:1461-1472).**
Replaced the 180-line fuel-induction proof with a 6-line derivation from
`soundness_open` via empty environments (γV = γT = []) and `substEnv_nil`.
This eliminated 6 sorrys from the old soundness theorem (lam, 3×app-lam,
mu-app, mu-neutral cases). Added `closedAt 0 e` precondition — verified
satisfiable with 13 native_decide witness tests in Tests.lean (values,
applications, ascriptions, recursive types).

**NEW: subCheckNF_substEnv (Soundness.lean:1051, 1 sorry).**
Statement: if subCheckNF succeeds on open terms in context ctx, then there
exists a fuel at which subCheckNF succeeds on the substituted closed terms.
Used to close the asc case of soundness_open.

**CLOSED: soundness_open asc case (Soundness.lean:1435-1441).**
Was sorry'd due to the gap between open-term subChecking and closed-term
VCompat. Now proved via subCheckNF_substEnv + VCompat.adequacy.

**NET: -7 sorrys (17 total, was 24).**

**Remaining soundness_open sorrys (3):**
1. **mu case** (Soundness.lean:1341): HARD. absEval doesn't evaluate the mu
   body, so ih_body can't be used. The two mus have different substEnvs.
   Possible approaches: (a) add "mu bodies are well-typed" precondition,
   (b) nested induction on step index n (blocked by needing ih_body for
   unfolded bodies), (c) change VCompat's structural mu to not require
   VCompat on unfolded bodies.
2. **app case** (Soundness.lean:1448): Completely sorry'd. Hardest case.
   The semantic lam from ih_f must be extracted and applied.
3. **subCheckNF_substEnv** (Soundness.lean:1055): New sorry. Standard property
   but substantial proof (~100+ lines). Needs subCheckNF structure-following
   induction + absEval_substEnv commutation for mu cases.

**Remaining adequacy_gen sorrys (14):**
Lines 365, 443, 449, 479, 482, 500, 581, 586, 730, 733, 782, 826, 866, 1010.
These are in the old adequacy_gen proof. If soundness_open is fully proved,
the closed-term soundness follows directly, and these adequacy_gen sorrys
only matter for direct use of VCompat.adequacy (used in soundness_open asc case).

**RECOMMENDED NEXT STEPS (priority order):**
1. **Prove subCheckNF_substEnv** (Soundness.lean:1055). Well-defined statement.
   Proof follows subCheckNF structure by fuel induction. Main challenges:
   mu cases call absEval internally, need absEval_substEnv commutation.
2. **Work on soundness_open app case** (Soundness.lean:1448). Sub-cases:
   - fT=lam, fV=lam: extract semantic lam from ih_f, apply with ih_a
   - fT=lam, fV=mu: concEval unrolls mu, use mu-left VCompat
   - fT=mu: mu-app dispatch, annotation-trust interaction
   - fT=neutral: structural app via IH
3. **Work on soundness_open mu case** (Soundness.lean:1341). Blocked by
   missing absEval on body. May require adding precondition or changing
   proof strategy.

Changes by agent ochre-20260405-071731:

**DESIGN CHANGES:**

1. **VCompat semantic lam now requires isConcreteVal on the value argument.**
   Changed from: `∀ j ≤ n, ∀ aV aT, VCompat j aV aT → ...`
   To: `∀ j ≤ n, ∀ aV aT, (match aV with | .lam _ _ | .type | .mu _ _ => True | _ => False) → VCompat j aV aT → ...`
   
   WHY: This resolves the FunEnvCompat extension blocker in soundness_open's lam
   case. The semantic lam quantifies over all aV, but FunEnvCompat.cons requires
   isConcreteVal. Adding the precondition lets the lam case use it directly.
   COST: Consumers of the semantic lam (app case) must provide isConcreteVal.
   In the app case, aV comes from concEval. For well-typed terms, concEval
   produces concrete values when the function position is a lam/mu (beta-reduction
   or mu-unrolling returns values). The neutral-app case (fV = app/type) doesn't
   use the semantic lam, so this precondition is satisfiable in practice.

2. **Fixed bug in absEval's mu-app catch-all (Eval.lean:209-212).**
   Previously: `| _, _ => .ok ⟨.app body a'.val⟩` — body extracted without
   substituting self-reference, creating dangling bvar 0.
   Now: `| _, _ => .ok ⟨.app (body.subst 0 (Expr.mu _ann body)) a'.val⟩`
   This ensures absEval output is always closedAt ctx.length.

3. **NEW: absEval_preserves_closedAt (Eval.lean:801).** If closedAt ctx.length e
   and absEval fuel ctx seen e = .ok τ, then closedAt ctx.length τ.val.
   Proved for all cases EXCEPT the mu-app body-lam path (1 sorry — match
   compilation destructures `body`, losing the name needed for seen-check
   reasoning). The annotation-trust and catch-all cases are fully proved.

**CLOSED SORRYS (2 in Soundness.lean):**
- `FunEnvCompat j (aV :: γV) (aT :: γT)` in lam case — closed via
  isConcreteVal precondition on semantic lam
- `body'.val.closedAt (γT.length + 1)` in lam case — closed via
  absEval_preserves_closedAt

**ADDED SORRY (1 in Eval.lean):**
- mu-app body-lam case in absEval_preserves_closedAt — mathematically clear
  (all sub-paths preserve closedAt via subst_closedAt + IH) but the match
  compilation in Lean destructures `body` after `split`, losing the variable
  needed for the seen-check. Needs a workaround (e.g., saving the expression
  before the split, or using omega/rewriting to recover it).

- **STATED: soundness_open (Soundness.lean:1255)** — the fundamental theorem
  for open terms. Statement: see Soundness.lean:1255.
- **PROVED: bvar, type, and lam cases** of soundness_open. ✅ LAM IS FULLY PROVED.
- **NEW INFRASTRUCTURE:**
  FunEnvCompat, ConcreteValEnv, concEval_val,
  absEval_fuel_mono_le, concEval_fuel_mono_le, absEval_preserves_closedAt

**SORRY ANALYSIS for soundness_open (3 sorrys in 3 cases):**

1. **mu case** (1 sorry): absEval doesn't evaluate the mu body. Two mus with
   different environments can't be related without reasoning about unfolding.

2. **asc case** (1 sorry): needs "subCheckNF on open terms implies adequacy
   on closed terms" — a non-trivial substEnv/subCheckNF interaction lemma.

3. **app case** (1 sorry): completely sorry'd. Hardest case. When consuming
   the semantic lam, must provide isConcreteVal for the argument (new
   requirement from the semantic lam change). For the lam-lam sub-case,
   this is satisfied because concEval output of well-typed term in function
   position is a lam (beta-reduces to a value). For mu and neutral sub-cases,
   different reasoning applies.

**RECOMMENDED NEXT STEPS (in priority order):**
1. **Close the mu-app sorry in absEval_preserves_closedAt** (Eval.lean:909).
   Pure Lean engineering: save `Expr.mu _ann body` as a local def before
   `split` to prevent the variable from being destructured. The mathematical
   argument is already laid out in the comments.
2. **Work on soundness_open's mu case.** Requires reasoning about mu unfolding
   under substitution: substEnv commutes with self-substitution.
3. **Work on soundness_open's asc case.** Requires substEnv/subCheckNF lemma:
   if subCheckNF ctx [] σ τ and both are closedAt, then VCompat after substEnv.
4. **Work on soundness_open's app case.** Hardest. Multiple sub-cases.
   The semantic lam's isConcreteVal requirement is new and must be verified
   for concEval outputs.

**Net sorry change from session start: -1 (24 total, was 25).**

Changes by agent ochre-20260405-053702:
- **PROVED: substEnv_idEnv** (Syntax.lean) — the identity property for simultaneous
  substitution. Previously sorry'd. Proved via helper lemmas idEnv_length,
  idEnv_getElem?, lift_idEnv.
- **NEW: shift_zero, shift_shift, shift_shift_same, shift_succ** (Syntax.lean) —
  core shift composition and identity lemmas. shift_shift: composing shifts at
  related cutoffs. shift_shift_same: composing at the same cutoff (needed for
  liftEnvN entry characterization).
- **NEW: closedAt** (Syntax.lean) — scope predicate for free variables. Required
  precondition for the composition lemma.
- **NEW: liftEnvN** (Syntax.lean) — iterated environment lifting, with length
  and entry lemmas. Formalizes what happens when substEnv goes under binders.
- **NEW: substEnv_subst_comp_gen** (Syntax.lean) — the generalized composition
  lemma. FULLY PROVED modulo one sorry: shift_subst_comm. Proof by induction on
  expression structure, generalizing over binder depth c. All 6 expression cases
  proved; the bvar case uses liftEnvN_entry_subst (induction on c) which depends
  on shift_subst_comm.
- **NEW: substEnv_subst_comp** (Syntax.lean) — the c=0 specialization used by
  the fundamental theorem.
- **PROVED: shift_subst_comm** (Syntax.lean) — the generalized version
  (shift_subst_comm_gen) proved by induction on e, generalizing over both
  j (subst position) and d (binder depth). The bvar case requires careful
  case analysis (4 sub-cases: k < d, k = j+d, k > j+d, d ≤ k < j+d).
  The lam/mu body cases use shift_shift_same to compose the subst value shifts.
  Specialization to d=0 gives the standard shift_subst_comm.

**COMPOSITION LEMMA FULLY PROVED.** Zero sorrys in Syntax.lean.
The substEnv_subst_comp infrastructure is complete. The next step is to
state and prove soundness_open (the fundamental theorem) in Soundness.lean.

**Net sorry change: -1 (substEnv_idEnv proved), 0 new sorrys in Syntax.lean.**
20 sorrys remain in Soundness.lean (unchanged).

Up from 19 — agent ochre-20260405-040204 expanded the soundness app (fT=lam) case
from 1 sorry into 3 (proving bvar/asc/type sub-cases), and proved the lam-neutral
contradiction in the neutral branch.

Changes by agent ochre-20260405-040204:
- **NEW LEMMAS: concEval_not_bvar, concEval_not_asc (Eval.lean).** concEval never
  produces bvar or asc at the top level. Proof by induction on fuel: base cases
  (lam, type, mu) never produce bvar/asc, recursive cases (asc-erasure, beta,
  mu-unroll) propagate inner results, and the catch-all (neutral app) produces app.
- **PROVED: soundness app fT=neutral fV=lam (Soundness.lean:1264).** The case
  where the abstract function is neutral (bvar/app/asc) but the concrete function
  is a lam is a CONTRADICTION. The IH gives VCompat 1 (lam ...) (bvar/app/asc ...),
  and all 10 VCompat disjuncts are false for this combination (lam ≠ mu/app/asc,
  inferType returns none for lam, and bvar/app/asc ≠ type/lam/mu).
- **EXPANDED: soundness app fT=lam (Soundness.lean:1204).** Dispatched on fV
  (concrete function value), proving 3 sub-cases:
  - fV = bvar: impossible (concEval_not_bvar)
  - fV = asc: impossible (concEval_not_asc)
  - fV = type: contradiction (VCompat 1 type (lam ...) is False, same technique)
  - fV = lam: SORRY — dual-substitution (different bodies AND arguments)
  - fV = mu: SORRY — concEval unrolls mu, absEval beta-reduces lam
  - fV = app: SORRY — neutral app in concrete, beta-reduction in abstract

**KEY ANALYSIS (for future agents):**

The "VCompat 1 contradiction" technique works whenever the concrete value has a
constructor that can't match any VCompat disjunct with the abstract type. It works
for:
- lam vs bvar/app/asc (proved — no disjunct applies since inferType returns none for lam)
- type vs lam (proved — type ≠ lam/mu/app/asc, inferType returns none for type)

It does NOT work for:
- mu vs bvar/app/asc (mu-left disjunct applies with VCompat 0 = True)
- bvar vs anything (inferType disjunct with existential ctx can be satisfied)
- app vs anything (structural app or inferType disjunct can apply)

The fundamental remaining blockers are:
1. **Dual-substitution**: concEval(bodyV.subst 0 aV) vs absEval(bodyT.subst 0 aT.val)
   — different bodies AND different arguments. Requires a substitution lemma or
   generalized soundness theorem for compatible expression pairs.
2. **Self-elim step count**: mu unfolding costs one observation step, and we can't
   recover it. VCompat(n-1, v, τ) doesn't upgrade to VCompat(n, v, τ).
3. **Annotation-trust**: the mu-app annotation-trust path in absEval trusts the
   annotation without validation, creating a gap between concrete and abstract.

Changes by agent ochre-20260405-031505:
- **EXPANDED soundness app case (Soundness.lean:1175).** The single sorry is now
  broken into sub-cases by dispatching on fT.val (abstract function type) and fV
  (concrete function value):
  - **fT.val = lam, all fV**: 1 sorry (line 1211). BLOCKER: dual-substitution
    problem. Both sides beta-reduce but with different arguments (aV vs aT.val).
    The semantic lam from IH on f can't be extracted from VCompat because the
    refl disjunct blocks it. Options explored:
    (a) Raw lam bodies in absEval (like mu change): TESTED AND FAILED. Breaks
        pred_ and other tests because raw domains inside nested lam bodies
        cause subCheckNF domain checks to fail (raw app expressions vs normalized types).
    (b) Generalized soundness with compatible substitutions: Not attempted, would
        require major restructuring.
    (c) Single-argument semantic lam: More provable but weaker for adequacy.
  - **fT.val = mu**: 1 sorry (line 1217). Annotation-trust interaction.
  - **fT.val = neutral, fV = lam**: 1 sorry (line 1233). Shape mismatch
    (concEval beta-reduces, absEval returns neutral app).
  - **fT.val = neutral, fV = mu**: 1 sorry (line 1238). Shape mismatch
    (concEval unrolls mu, absEval returns neutral app).
  - **fT.val = neutral, fV = neutral**: ✅ PROVED. VCompat via structural app
    + IH on f and a. Covers all 4 neutral fV forms (bvar, type, app, asc)
    and all 3 neutral fT.val forms (bvar, app, asc).
- **ANALYSIS: Raw lam body approach (like mu annotation change) is NOT viable.**
  Tested changing absEval's lam case to keep raw bodies + subCheckNF lam-lam
  case to normalize on demand. Soundness lam case becomes trivial (refl), BUT:
  pred_ fails because nested lam domains (e.g., PairNN_ = app (app Pair_ Nat_) Nat_)
  are left raw. When these lams are applied in absEval's app case, the domain check
  compares the argument against the raw domain expression, which subCheckNF can't
  handle. The mu annotation change worked because mu annotations are only used
  in subCheckNF (which normalizes on demand), never in absEval's domain check.

Changes by agent ochre-20260405-024408:
- **NEW LEMMA: VCompat.app_inferType (Soundness.lean:321).** Analogous to
  bvar_inferType. If VCompat(n, v, app f a) and inferType ctx (app f a) = some ty,
  then VCompat(n, v, ty). All cases proved EXCEPT the structural app case
  (v = app fV aV with VCompat components — needs VCompat-preserves-inferType).
- **CLOSED 4 sorrys in adequacy_gen:** σ = app inferType fallback cases for
  τ ∈ {lam, bvar, asc, app}. Pattern: extract inferType/absEval/subCheckNF from
  hcheck, chain app_inferType → absEval_preserves → ih_fuel. Same pattern as
  the existing bvar sites.
- **Sorry count: 17 → 16** (net -1 per declaration, but -3 per sorry statement;
  new app_inferType declaration adds 1 sorry'd declaration).

Previous changes by agent ochre-20260405-020120:
- **DEFINITION CHANGE: absEval's mu case keeps raw annotation.**
  Previously: `let ann' ← absEval fuel ctx seen ann; .ok ⟨.mu ann'.val body⟩`
  Now: `let _ ← absEval fuel ctx seen ann; .ok ⟨.mu ann body⟩`
  This ensures concEval and absEval produce the SAME mu (both keep raw
  annotation), eliminating the annotation normalization mismatch that was
  blocking 5+ sorrys. Annotation normalization is deferred to subCheckNF's
  self-elim annotation path (which now calls absEval on the annotation
  before comparing).
- **DEFINITION CHANGE: subCheckNF self-elim normalizes annotation on demand.**
  The annotation path now does `absEval(ann)` before comparing, rather than
  relying on the annotation being pre-normalized by absEval's mu case.
- **PROVED: soundness mu case** (Soundness.lean:1020) — trivial by refl
  since v = mu ann body = τ.val.
- **PROVED: absEval_preserves refl-mu** (Soundness.lean:390) — trivial by
  refl since absEval(mu ann body) = ok ⟨mu ann body⟩.
- **PROVED: absEval_preserves structural mu** (Soundness.lean:441) —
  e'.val = mu annT bodyT = e, reconstruct structural mu disjunct.
- **PROVED: absEval_preserves mu-right** (Soundness.lean:444) —
  e'.val = mu ann body = e, reconstruct mu-right disjunct.
- **PROVED: absEval_preserves normalized mu-right** (Soundness.lean:447) —
  e'.val = mu ann body = e, reconstruct normalized mu-right disjunct.
- **PROVED: subCheckNF_self_elim_step fuel_mono** — updated for the new
  annotation normalization in self-elim. Both paths are independently
  monotone, so the overall result is monotone.
- **All tests pass** including appendArrays and appendVec (north star).

Previous changes by agent ochre-20260405-013043:
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
  - **PROVED: inferType fallback σ=app for τ ∈ {lam, bvar, asc, app}** (4 sorrys closed
    by agent ochre-20260405-024408 using app_inferType + absEval_preserves + ih_fuel)
- `VCompat.app_inferType` — **PARTIALLY PROVED** (Soundness.lean:321)
  - All cases proved except structural app (v = app fV aV with VCompat components)
  - Used by adequacy_gen to close 4 inferType fallback sorrys
- `VCompat.adequacy` — corollary of adequacy_gen (Soundness.lean:852)
- `VCompat.from_self_intro_gen` — **PROVED** (Soundness.lean:860)
- `soundness` (main theorem) — **PARTIALLY PROVED** (Soundness.lean:1117)
  - Proved: fuel=0 (contradiction), bvar (contradiction), type (trivial)
  - Proved: asc case via IH + VCompat.adequacy
  - Proved: mu case via VCompat.refl (raw annotation kept)
  - Sorry: lam — normalization coherence (absEval normalizes body, v ≠ τ.val)
  - Sorry: app fT=lam fV=lam �� dual-substitution
  - Sorry: app fT=lam fV=mu — mu unrolling + lam beta-reduction
  - Sorry: app fT=lam fV=app — neutral-app vs beta-reduction
  - Proved: app fT=lam fV=bvar/asc — impossible (concEval_not_bvar/asc)
  - Proved: app fT=lam fV=type — contradiction (VCompat 1 type (lam) = False)
  - Sorry: app fT=mu — annotation-trust interaction
  - Proved: app fT=neutral fV=neutral — structural app + IH
  - Proved: app fT=neutral fV=lam — contradiction (VCompat 1 lam neutral = False)
  - Sorry: app fT=neutral fV=mu — mu unrolling vs neutral app

**Phase 3 (Subtyping helpers): COMPLETE**
- `subCheckNF_lam_lam_body` — PROVED
- `subCheckNF_lam_impossible` — PROVED
- `subCheckNF_mu_mu_body` — PROVED
- `subCheckNF_type_left_target` — PROVED
- `subCheckNF_neutral_inferType` — **PROVED** (Subtyping.lean:198)

### What happened this session (agent ochre-20260405-044743)

**Deep analysis of all 20 sorrys. Identified fundamental theorem of logical
relations as the path forward for the dual-substitution problem.**

No code changes — this session was purely analytical. Key findings:

1. **Classified all 20 sorrys by root cause:**
   - ~8 blocked by dual-substitution (soundness lam, app-lam-lam, absEval_preserves
     lam/app-beta cases, adequacy_gen lam-lam)
   - ~4 blocked by self-elim step-count (adequacy_gen mu→{lam,bvar,asc,app})
   - ~4 blocked by annotation-trust (soundness app fT=mu, adequacy_gen mu→τ
     annotation path)
   - ~4 blocked by various interaction effects (app_inferType structural app,
     absEval_preserves app-mu, soundness app fT=neutral fV=mu, etc.)

2. **Normalization-substitution commutation is FALSE in general.**
   Counterexample: body = asc (bvar 0) (lam Type Type), absEval(body) = ⟨lam Type Type⟩.
   Then absEval(body.subst 0 arg) FAILS if arg's type ⊄ (lam Type Type), while
   absEval(body'.val.subst 0 arg) = absEval(lam Type Type) = ok. When both succeed,
   results may agree by confluence, but the conditional version is complex.

3. **Fundamental theorem approach is the right solution:**
   Prove soundness for OPEN terms by induction on expression structure with
   VCompat-related environments (substEnv). The lam body is a sub-expression,
   so the IH applies directly — no dual-substitution because both evaluators
   operate on the SAME body, just with different environment entries.
   See DECISION-LOG entry "2026-04-05: Fundamental theorem" and SUGGESTIONS.md.

4. **Self-elim adequacy cases work for seen=[] but fail for non-empty seen.**
   All VCompat disjunct sub-cases (mu-left, inferType, asc-left) can prove
   VCompat(m+1, v, τ) at step m+1, BUT the ih_n callback requires VCompat for
   the transformed v' (not original v), which the hseen callback can't provide.
   When seen = [] (the adequacy corollary's entry point), the callback is vacuous
   and everything works. The issue is that self-intro recurses with non-empty seen.

5. **Circular dependency in absEval_preserves is non-critical.** The refl-asc
   sorry needs adequacy_gen, but adequacy_gen's uses of absEval_preserves only
   process inferType results (never asc). So the circular call is unreachable.

**Next agent should:** Implement the fundamental theorem approach:
1. Define `substEnv : List Expr → Expr → Expr` (simultaneous substitution)
2. Prove substEnv composition lemmas (single subst = substEnv with one entry, etc.)
3. Define `EnvCompat n ctx γV γT` (environment compatibility)
4. State and prove `soundness_open` by induction on expression structure
5. Derive original `soundness` as corollary with empty environments
6. Use soundness_open to close the dual-substitution sorrys

Critical files: Syntax.lean (substEnv), Soundness.lean (soundness_open).
Expected ~300-500 lines of new code. The substitution composition lemmas are
the hardest part; the actual fundamental theorem proof follows standard patterns.

### What happened this session (agent ochre-20260405-040204)

**Proved concEval shape lemmas + expanded soundness app into fV sub-cases (19→20 sorrys).**

1. **concEval_not_bvar, concEval_not_asc (Eval.lean).** Two structural invariant
   lemmas: concEval never produces bvar or asc at the top level. Proved by induction
   on fuel. These allow eliminating impossible concEval output cases in soundness proofs.

2. **soundness app fT=neutral fV=lam PROVED (Soundness.lean:1264).** Contradiction:
   VCompat 1 (lam ...) (bvar/app/asc ...) is False since no disjunct applies.
   Uses the IH instantiated at step n=1 to derive the contradiction.

3. **soundness app fT=lam expanded (Soundness.lean:1204).** Dispatched on fV:
   - bvar, asc: impossible by concEval_not_bvar/asc
   - type: contradiction by VCompat 1 type (lam ...) = False
   - lam, mu, app: sorry'd (dual-substitution / mu unrolling / neutral mismatch)

4. **Analysis: identified 3 fundamental blockers** (documented in detail above):
   - Dual-substitution: both the body AND the argument differ between evaluators
   - Self-elim step count: mu unfolding costs one step, can't recover
   - Annotation-trust: absEval trusts mu annotations without validation

**Next agent should focus on:** Implementing the **fundamental theorem of logical
relations** approach (see "What happened this session (agent ochre-20260405-044743)"
above and DECISION-LOG entry). This is the recommended path for the dual-substitution
problem, which is the single biggest blocker (blocks ~8 of 20 sorrys). Start with
substEnv in Syntax.lean, then soundness_open in Soundness.lean.

### What happened this session (agent ochre-20260405-024408)

**Added app_inferType lemma + closed 4 inferType fallback sorrys (19→16 sorry stmts).**

1. **VCompat.app_inferType (Soundness.lean:321): PARTIALLY PROVED.** New lemma
   analogous to VCompat.bvar_inferType. If VCompat(n, v, app f a) and
   inferType ctx (app f a) = some ty, then VCompat(n, v, ty). Proof by
   induction on n with case split on VCompat disjuncts:
   - Contradictions: type ≠ app, lam ≠ app, mu ≠ app (6 cases)
   - Refl (v = app f a): use inferType disjunct with VCompat.refl
   - Mu-left: IH on inner VCompat
   - InferType: IH on inner VCompat
   - Asc-left: IH on inner VCompat
   - **Structural app: SORRY'd.** v = app fV aV, VCompat(m, fV, f),
     VCompat(m, aV, a). Need VCompat(m+1, app fV aV, ty). Requires relating
     inferType(app fV aV) to inferType(app f a) through VCompat on components.
     This is essentially the substitution lemma for inferType.

2. **Closed 4 inferType fallback sorrys in adequacy_gen.** For σ = app _fS _aS
   with τ ∈ {lam, bvar, asc}: extract inferType/absEval/subCheckNF from hcheck
   via `dsimp only [] + match + simp only`, then chain:
   app_inferType → absEval_preserves → ih_fuel. For τ = app (app-app fallback):
   needed to simplify hcheck through the `by_cases hcong` false branch first.

3. **KEY ANALYSIS: Soundness lam case is NOT a fuel quantification issue.**
   The blocker for soundness lam is NOT the "all-fuel" quantification in the
   semantic lam (as previously described). It's that absEval normalizes the lam
   body, so v = lam dom body ≠ τ.val = lam dom'.val body'.val. The semantic lam
   requires relating concEval(body.subst 0 aV) to absEval(body'.val.subst 0 aT),
   which are DIFFERENT expressions. The soundness IH requires the SAME expression
   for both evaluators. Strong induction on fuel does NOT help.

4. **KEY ANALYSIS: Soundness app lam-lam sub-case IS provable** via the semantic
   lam from the IH on f. When concEval dispatches on fV = lam dom body and
   absEval dispatches on fNF.val = lam dom' body':
   - IH on f gives VCompat(n+1, fV, fNF.val)
   - The semantic lam from this VCompat (3rd disjunct) says: for j ≤ n,
     concEval(body.subst 0 aV') = rv → absEval(body'.subst 0 aT') = rτ →
     VCompat(j, rv, rτ.val)
   - Take j = n, fuel' = k, aV' = aV (from concEval), aT' = aNF.val (from absEval)
   - The expressions body.subst 0 aV and body'.subst 0 aNF.val match exactly
     what the semantic lam expects
   - Result: VCompat(n, v, τ.val)
   - **Caveat:** must handle the case where VCompat(n+1, fV, fNF.val) is via
     the refl disjunct (not semantic lam). If fV = fNF.val (lam dom body = lam dom' body'),
     then dom = dom' and body = body', but we STILL can't use the soundness IH because
     concEval evaluates body.subst 0 aV and absEval evaluates body.subst 0 aNF.val
     (different substitutions). This sub-sub-case remains open.

5. **Investigated lam body normalization deferral (NOT committed).** Considered
   making absEval(lam dom body) return ⟨lam dom body⟩ (like the mu change),
   with subCheckNF normalizing bodies on demand. Result: NOT safe as-is.
   subCheckNF's lam-lam case compares bodies directly. Standard library lam
   bodies contain asc nodes (e.g. isZero_ has `lam Bool (asc false_ Bool)`)
   that get erased by normalization. Without normalization, subCheckNF would
   compare raw asc nodes against non-asc targets and fail. Would require adding
   absEval calls to subCheckNF's lam-lam case, which is doable but a significant
   restructuring (fuel_mono + adequacy_gen proofs need updating).

### What happened in previous session (agent ochre-20260405-013043)

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
   - `mu`: **PROVED** (agent ochre-20260405-020120). After the definition change
     (absEval keeps raw annotation), v = τ.val = mu ann body. VCompat by refl.
   - `lam`, `app`: sorry'd with documented blockers.

   Soundness `lam` blocker: the semantic lam in VCompat quantifies over ALL
   fuel levels for inner evaluation, but the fuel-induction IH only gives
   soundness at fuel k. Needs either strong induction on (fuel, step) with
   lexicographic ordering, or a different proof strategy.

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

### Sorry categorization (16 in Soundness, 0 in Eval = 16 total)

The remaining sorrys fall into 5 categories:

**Category A: absEval_preserves sub-cases (7 sorrys, Soundness.lean:437-580)**
- 7 cases PROVED (mu-left, inferType, asc-left, refl-mu, structural mu,
  mu-right, normalized mu-right)
- 7 sorrys remain:
  (a) **Normalization coherence** (4 sorrys): absEval(body) and raw body have
      same semantics under VCompat. Affects: refl-lam (443), refl-app lam/mu
      dispatch (473, 476), semantic lam (494).
  (b) **Structural app beta/mu dispatch** (2 sorrys): when absEval beta-reduces
      or mu-app dispatches, the result shape changes. Affects: structural app
      lam (575), structural app mu (580).
  Plus: refl-asc (437, 1 sorry) which needs VCompat.adequacy (circular dependency
  with adequacy_gen; does NOT arise at current use sites).

**Category A': app_inferType structural app (1 sorry, Soundness.lean:359)**
- v = app fV aV, VCompat m fV f, VCompat m aV a, inferType ctx (app f a) = some ty.
  Need VCompat(m+1, app fV aV, ty). Requires relating inferType of (app fV aV)
  to inferType of (app f a) through VCompat on components.

**Category B: Structural lam-lam (2 sorrys, Soundness.lean:724/727)**
- Refl: v = lam _dS _bS, need VCompat (m+1) (lam _dS _bS) (lam _dT _bT)
- Semantic lam: v = lam domV bodyV, need to transport body compatibility
- BLOCKER: substitution lemma — connecting subCheckNF(bodyS, bodyT) under
  extended context to VCompat after substituting concrete arguments. The
  semantic lam quantifies over ALL fuel levels.

**Category C: Self-elim / annotation-trust (4 sorrys)**
- σ = mu, τ ∈ {lam, bvar, asc, app} (lines 776, 820, 860, 1004)
- BLOCKER: annotation-trust gap. subCheckNF's mu self-elim normalizes
  annotation then compares (or uses body normalization). Both paths need
  VCompat preservation. The body path IS provable with absEval_preserves.

**Category D: InferType fallback σ=app — RESOLVED**
- All 4 sorrys closed by agent ochre-20260405-024408 using the new
  app_inferType lemma + absEval_preserves + ih_fuel. Pattern matches
  the existing bvar sites exactly.

**Category E: Soundness main cases (2 sorrys, Soundness.lean:1162, 1181)**
- lam: normalization coherence — absEval normalizes lam bodies, so
  v = lam dom body ≠ τ.val = lam dom'.val body'.val. The semantic lam
  requires relating concEval(body.subst 0 aV) to absEval(body'.val.subst 0 aT),
  which are DIFFERENT expressions. The soundness IH requires the SAME expression.
  Strong induction does NOT help — the fundamental issue is expression mismatch,
  not fuel quantification.
- app: combines normalization coherence (lam-lam sub-case) with dispatch
  cross-cases. The neutral-neutral sub-case IS provable (structural app + IH)
  but requires expanding the sorry into a large case analysis first.
  The lam-lam sub-case is provable IF the IH gives VCompat with the
  semantic lam disjunct (not just refl) — see analysis below.
- mu: **PROVED** (trivial by refl after definition change)

### Recommended next steps (updated 2026-04-05)

1. **Normalization coherence** — The single biggest blocker. Need to show
   that absEval doesn't change the semantic behavior of terms under VCompat.
   This is essentially the correctness of absEval. Possible approaches:
   (a) Prove absEval idempotency on NfExprs (if e is already normalized,
       absEval returns the same thing). This would handle most practical cases.
   (b) Prove a "semantic normalization" lemma: VCompat(n, e, absEval(e).val)
       for appropriate e. This is close to absEval_preserves's refl case.
   (c) **Defer lam body normalization** to subCheckNF (like was done for mu
       annotations). Make absEval(lam dom body) return ⟨lam dom body⟩ (raw body),
       and have subCheckNF's lam-lam case normalize bodies on demand. This would
       make the soundness lam case trivial by VCompat.refl. **CAVEAT:** agent
       ochre-20260405-024408 investigated this and found it's NOT safe as-is:
       subCheckNF's lam-lam case compares bodies directly without re-normalizing.
       The change would require adding absEval calls to subCheckNF's lam-lam case,
       which is doable but requires updating fuel_mono and adequacy_gen proofs.

2. **Substitution lemma** — For lam-lam refl/semantic cases in adequacy_gen.

3. **Self-elim / annotation-trust** — The body normalization path would work
   if absEval_preserves were fully proved. The annotation path remains the
   fundamental Phase 0 issue from SUGGESTIONS.md.

4. **Soundness app case expansion** — The neutral-neutral sub-case is
   straightforward (structural app + IH). The lam-lam sub-case requires
   the semantic lam from the IH on f (see analysis below). Could reduce
   the single sorry to specific sub-case sorrys.

5. **app_inferType structural app** — The one remaining sorry in the new
   lemma. Requires relating inferType across VCompat components. Hard without
   a substitution lemma for inferType.

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

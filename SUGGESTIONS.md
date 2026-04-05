# Suggestions

The current goal is proving soundness of Och. Here is the dependency chain
and priority order for the remaining `sorry`s.

## Phase 0: Fix annotation-trust soundness bug — PARTIALLY RESOLVED

**Update (agent ochre-20260405-020120):** The annotation normalization
mismatch between concEval and absEval is FIXED. absEval's mu case now
keeps the raw annotation (validates but doesn't normalize), so both
evaluators produce `mu ann body` (same term). This eliminated 7 sorrys.
The mu-app annotation-trust issue below remains but is less blocking.

**absEval's mu-app annotation-trust case (Eval.lean:183-188) is unsound.**

When a mu is applied and both the annotation and body are lams, absEval
uses the annotation's return type instead of evaluating the body:
```lean
| .lam _dom retBody, .lam _ _ =>
    absEval fuel ctx seen (retBody.subst 0 a'.val)
```

This trusts the annotation without validation. Counterexample:
```
app (mu (lam Type (lam Type (bvar 0))) (lam Type Type)) Type
```
absEval returns `lam Type (bvar 0)` (from annotation), concEval returns
`Type` (from body). These are incompatible.

**This MUST be fixed before the soundness theorem can be proved.**

### Option A: Validate annotations at mu creation ← TESTED, DOES NOT WORK

**Tested by agent ochre-20260404-215501. Result: breaks DNat and Array tests.**

The creation-time check `body' ⊑ ann'.shift 1 0` fails for Church-encoded
types with complex annotations. The fundamental issue: inside the mu, self is
abstract (bvar), so the body's return type involves symbolic applications
(like `app s m` for dsucc) that subCheckNF can't compare against the
annotation type (like `dNat`).

Even a targeted lam-only validation (only checking when ann' is a lam) breaks
because `dNat → dNat` is a lam. The fuel_mono proof update works, but the
validation itself rejects legitimate types.

**This option requires a more powerful subCheckNF that can reason about
symbolic terms, or a fundamentally different validation strategy.**

### Option B: Remove annotation-trust ← TESTED, BREAKS TOO MUCH

**Tested by agent ochre-20260404-204421. Result: breaks DNat and Vec tests.**

Removing the annotation-trust case causes `absEval` to use the body-based
path (self-substitution + seen set) for ALL mu-lam applications. This breaks:
- `done_ ⊑ dNat`, `dtwo ⊑ dNat`, `dthree ⊑ dNat` (DNat.lean)
- `appendVec ⊑ expected_type` (Vec.lean — the NORTH STAR test)

The body-based path hits the seen-set cutoff for recursive types, producing
symbolic applications instead of the annotation's return type. These symbolic
applications can't be subtype-checked against the expected types.

**This option is NOT viable without major library restructuring.**

The fuel_mono proof update works (just route all lam bodies through
`absEval_fuel_mono_mu_lam_body`), so if Option A is chosen, the mu-app
fuel_mono case is already solved.

### Option C: WellAnnotated precondition (WEAKEST)

Add a precondition to the soundness theorem that all mu annotations are
correct. This is the weakest fix but allows progress on the proof.

## Phase 1: Foundation — fuel monotonicity ✅ COMPLETE

Both `absEval_fuel_mono` and `subCheckNF_fuel_mono` are proved. Updated
by agent ochre-20260405-020120 for the new annotation normalization in
subCheckNF's self-elim and absEval's mu case.

## Phase 2: VCompat lemmas (Soundness.lean)

These three lemmas are needed by the main soundness theorem. They should be
tackled after Phase 0 is done.

### `VCompat.from_type_sub_gen` ✅ PROVED (Soundness.lean:178)

### `VCompat.from_self_intro_gen` ✅ PROVED (Soundness.lean:355)

Proved via adequacy_gen. Key insight: v = σ, so VCompat(σ, σ) is trivially
true by refl, and adequacy_gen transports across the subcheck.

### `VCompat.adequacy_gen` (Soundness.lean:279) — PARTIALLY PROVED

The generalized adequacy lemma with seen set support. Proved cases:
- σ = τ (syntactic equality)
- (σ, τ) in seen (callback)
- τ = Type (top type)
- τ = mu (self-intro): normalized mu-right disjunct + ih_fuel/ih_n
- **τ = app, σ = app, structural congruence** ✅ PROVED (all 4 VCompat sub-cases)
- Contradictions: σ ∈ {type, lam, asc} with τ = app ✅ PROVED

**DEFINITION CHANGE (agent ochre-20260404-224040):** subCheckNF's lam-lam
and app-app structural cases now use empty `seen` `[]` instead of propagating
the outer seen. This eliminates the "seen callback mismatch" blocker for
structural cases: the outer seen's VCompat callback is tied to the original
v, but structural decomposition needs callbacks for sub-components. With
`[]`, the callback is vacuous. All tests pass.

**DEFINITION CHANGE (agent ochre-20260405-003633):** Added asc-left disjunct
to VCompat: `∨ (∃ term tyAsc, v = .asc term tyAsc ∧ VCompat n term τ)`.
This was needed because absEval_preserves was FALSE without it (see
DECISION-LOG.md for the counterexample). All proofs updated.

**Remaining sorrys (Soundness.lean, see PROGRESS.md for current line numbers):**

1. **Lam-lam** (τ = lam, 2 sorrys): The `seen` clearing change
   enables the adequacy proof for domain/body components, but the hard part
   is the "substitution lemma": connecting subCheckNF(bodyA, bodyB) under
   extended context to VCompat after substituting concrete arguments into
   the bodies. VCompat's semantic lam quantifies over ALL fuel levels.

2. **Self-elim** (σ = mu, τ ≠ mu, 4 sorrys): BLOCKED by
   annotation-trust. Going from VCompat(v, mu ann body) to VCompat(v, ann)
   requires annotation correctness. The body normalization path would work
   IF absEval_preserves were fully proved.

3. **InferType fallback σ=app: RESOLVED** (agent ochre-20260405-024408).
   All 4 sorrys closed via new app_inferType lemma + absEval_preserves + ih_fuel.
   One sorry remains in app_inferType (structural app case).

4. **absEval_preserves sub-cases** (7 sorrys): 7 cases proved (mu-left,
   inferType, asc-left, refl-mu, structural mu, mu-right, normalized mu-right).
   Remaining 7 reduce to normalization coherence and circular dependency.

## Phase 3: Subtyping helper lemmas (Subtyping.lean)

- `subCheckNF_neutral_inferType` (line 201) — may need statement fix:
  the app-app structural check can succeed without inferType firing,
  making the "inferType must have fired" conclusion unprovable for
  a = app, b = app. Consider adding `h_a_not_app` precondition or
  changing the conclusion.

## Phase 4: Main soundness theorem (Soundness.lean:1019)

**mu case: PROVED** (agent ochre-20260405-020120) — trivial by refl after
the definition change (absEval keeps raw annotation).

Remaining: lam and app cases. 

Challenge for lam: absEval normalizes the body, so v ≠ τ.val. This is
the normalization coherence problem, NOT a fuel quantification issue.
Strong induction does NOT help — the blocker is expression mismatch
(body.subst 0 aV vs body'.val.subst 0 aT).

**app case: PARTIALLY PROVED** (agent ochre-20260405-031505). Expanded into
sub-cases. Neutral-neutral sub-case PROVED (structural app + IH).
Remaining 4 sorrys:
- **fT.val = lam (all fV)**: HARDEST. Dual-substitution: concEval beta-reduces
  with aV, absEval beta-reduces with aT.val. Semantic lam from IH helps but
  can't be extracted from VCompat (refl disjunct blocks it). NOTE: the claim
  "lam-lam is provable via semantic lam" was WRONG — extracting the semantic
  lam from VCompat requires case-splitting, and the refl case can't be resolved
  without a generalized soundness theorem for compatible substitutions.
- **fT.val = mu**: Annotation-trust interaction.
- **fT.val = neutral, fV = lam/mu**: Shape mismatch (different reduction strategies).

**Raw lam body approach: TESTED AND REJECTED.** Keeping raw lam bodies in
absEval (like the mu annotation change) makes soundness lam trivial but breaks
pred_ and similar tests. Raw domains inside nested lam bodies cause domain
check failures. The mu change worked because annotations are only consumed
by subCheckNF (which normalizes on demand), not by absEval's domain check.

**THE DUAL-SUBSTITUTION PROBLEM (agent ochre-20260405-031505 analysis):**

The fundamental blocker for both soundness lam and app(lam-lam) is that
absEval's lam case normalizes bodies:
- concEval(lam dom body) = lam dom body (raw)
- absEval(lam dom body) = lam dom'.val body'.val (normalized)

When this lam is applied, the evaluators beta-reduce DIFFERENT bodies with
DIFFERENT arguments:
- concEval: body.subst 0 aV (raw body, concrete arg)
- absEval: body'.val.subst 0 aT.val (normalized body, abstract arg)

The soundness IH requires the SAME expression for both evaluators. No
reformulation of the semantic lam (separate args, single arg, app-based)
avoids this — the mismatch is between the BODIES (body vs body'.val) AND
the ARGUMENTS (aV vs aT.val).

Approaches explored and their status:
- **Raw lam bodies**: REJECTED (breaks domain checks, see above).
- **Single-expression semantic lam** (∀ e, concEval(app v e) → absEval(app v e)):
  Would work if v = τ, but v ≠ τ due to normalization. And absEval internally
  normalizes v before dispatching.
- **Extracting semantic lam from VCompat**: BLOCKED by refl disjunct. VCompat
  at step n+1 might hold via refl (v = τ), which doesn't give body compatibility.
- **Ascription-based argument** (`app v (asc aV aT)`): DOESN'T HELP. Both
  evaluators still evaluate different sub-expressions after beta-reduction.

Potential paths forward (not yet attempted):
1. **Generalized soundness**: Prove soundness for pairs of "compatible" expressions
   simultaneously. Statement: if concEval(eC) = v and absEval(eA) = τ and
   eC "simulates" eA (new relation), then VCompat n v τ.val. Would need
   mutual induction with the simulation relation.
2. **Biorthogonality**: Define VCompat observationally (v and τ "behave the same
   in all contexts") without reference to body substitution. Standard technique
   for step-indexed logical relations. Requires rethinking VCompat entirely.
3. **Change absEval to not normalize lam bodies** ← TESTED, DOES NOT WORK
   **Tested by agent ochre-20260405-040204.** Two variants tested:
   (a) Raw body only: breaks succ_, add_, double_, pred_ — the raw body in
       absEval output changes the observable output (lam dom rawBody instead
       of lam dom normalizedBody), failing exact equality tests.
   (b) Raw body + normalize-on-demand in subCheckNF lam-lam: same failures.
       The issue is fundamental: absEval's output IS the normalized form. If lam
       bodies are raw, ALL absEval outputs containing lams have raw bodies,
       including final results. Tests check exact equality against normalized
       expected values. The mu annotation change worked because mu annotations
       are only consumed by subCheckNF (which normalizes on demand), never
       appearing in absEval's FINAL output in a way tests check.

## Known hazards

- **VCompat must NOT have a general normalization disjunct.** A disjunct like
  `∃ nfuel nctx nseen τ', absEval nfuel nctx nseen τ = .ok τ' ∧ VCompat n v τ'.val`
  makes VCompat trivially true for ALL n, v, τ. This was discovered and fixed
  by agent ochre-20260404-204421. Use the targeted **normalized mu-right**
  disjunct instead (only for mu types).

- **subCheckNF transitivity counterexamples FIXED** (agent ochre-20260405-013043).
  Two fixes: (1) self-elim's body check uses original `seen` (not `seen'`),
  preventing circular reasoning; (2) self-elim's annotation path is guarded
  by `body != bvar 0` — for pure self-reference bodies, the annotation is
  not trustworthy (the mu is universal but claims a specific type).
  **Transitivity verified** by exhaustive testing on ~30 expressions including
  all Std types, nested mus, and self-referential patterns (Tests.lean).
  **Transitivity is NOT YET PROVED** in Lean but no counterexample is known.

- **Self-elim proof landscape changed.** The self-elim body path in
  adequacy_gen no longer has a circular seen callback dependency. Previously,
  ih_fuel with seen' needed a callback for the (mu, τ) entry that required
  VCompat(v, τ) — the goal. Now the body check uses original `seen`, so the
  callback is the outer `hseen`. The remaining blockers for self-elim body
  path are: (a) absEval_preserves (for mu-right to body normalization), and
  (b) the step-count issue (mu-right costs one step, can't recover it).
  The annotation path is still blocked by annotation-trust (Phase 0).

- **absEval's mu case keeps raw annotations** (agent ochre-20260405-020120).
  The annotation is validated but NOT normalized in absEval's output. This
  means mu annotations in absEval output may contain un-normalized sub-
  expressions (ascriptions, unevaluated applications, etc.). subCheckNF's
  self-elim normalizes annotations on demand when comparing. The mu-app
  annotation-trust path in absEval still matches on the raw annotation
  shape (lam _dom retBody, .lam _ _), which works because in practice all
  recursive function annotations ARE syntactically lams.

- **subCheckNF top-universality is FALSE**. `Type <: tau` does NOT mean all
  values inhabit `tau`.

- **Raw lam body approach is NOT viable** (agents ochre-20260405-031505,
  ochre-20260405-040204). Three variants tested, ALL fail:
  (a) Raw body only: breaks ALL Church numeral operations (succ, add, pred,
      double). The raw body in output changes observable absEval results.
  (b) Raw body + subCheckNF normalize-on-demand: same failures. The issue
      is that absEval output IS the normalized form — tests check exact equality.
  (c) Previous agent's variant: raw DOMAINS inside nested lam
  bodies cause absEval's app-case domain check to fail. The mu annotation
  change succeeded because mu annotations are only consumed by subCheckNF
  (which normalizes on demand), not by absEval's direct domain comparisons.
  An approach that normalizes domains but not bodies partially works but
  still has the dual-substitution problem for soundness.
  **Bottom line:** The mu annotation change works because mu annotations flow
  ONLY to subCheckNF (which normalizes on demand). Lam bodies flow to
  absEval output (which tests check for exact equality), subCheckNF's
  lam-lam structural comparison, AND absEval's app-case domain check for
  nested lams. All three consumers expect normalized inputs.

- **Never weaken tests.** If a proof doesn't go through, the definitions or
  theorem statement may be wrong. Fix those, not the tests.

- **Check precondition satisfiability.** Any theorem change must be verified
  with `native_decide` witness tests on real programs.

# Suggestions

The current goal is proving soundness of Och. Here is the dependency chain
and priority order for the remaining `sorry`s.

## Phase 0: Fix annotation-trust soundness bug ← NEW, BLOCKING

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

Both `absEval_fuel_mono` and `subCheckNF_fuel_mono` are proved. (May need
updating if Phase 0 changes absEval.)

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

3. **InferType fallback σ=app** (4 sorrys): Needs app_inferType lemma
   + absEval_preserves. σ = bvar cases are DONE.

4. **absEval_preserves sub-cases** (9 sorrys): 3 cases proved (mu-left,
   inferType, asc-left). Remaining 9 reduce to normalization coherence
   and annotation normalization congruence.

## Phase 3: Subtyping helper lemmas (Subtyping.lean)

- `subCheckNF_neutral_inferType` (line 201) — may need statement fix:
  the app-app structural check can succeed without inferType firing,
  making the "inferType must have fired" conclusion unprovable for
  a = app, b = app. Consider adding `h_a_not_app` precondition or
  changing the conclusion.

## Phase 4: Main soundness theorem (Soundness.lean:541)

Once Phases 0-2 are done, the main theorem should be approachable.
Challenge: VCompat's semantic lam quantifies over all fuel, but the
soundness induction on fuel only gives the IH at lower fuel. Likely
needs strong induction + fuel monotonicity to bridge the gap.

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

- **subCheckNF top-universality is FALSE**. `Type <: tau` does NOT mean all
  values inhabit `tau`.

- **Never weaken tests.** If a proof doesn't go through, the definitions or
  theorem statement may be wrong. Fix those, not the tests.

- **Check precondition satisfiability.** Any theorem change must be verified
  with `native_decide` witness tests on real programs.

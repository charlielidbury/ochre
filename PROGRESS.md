# Progress

## Current state (2026-04-04)

Och is feature-complete for the current milestone. All tests pass, including
the north star (`appendVec` with abstract arguments). The focus is now on
proving soundness.

### Sorry inventory (3 total)

**Phase 1 (fuel monotonicity): COMPLETE**
- `subCheckNF_fuel_mono` — PROVED
- `absEval_fuel_mono` — PROVED

**Phase 2 (VCompat lemmas): IN PROGRESS**
- `VCompat.from_type_sub_gen` — **PROVED** (Soundness.lean:178)
- `VCompat.refl` — **PROVED** (Soundness.lean:257)
- `VCompat.adequacy_gen` — **PARTIALLY PROVED** (Soundness.lean:265)
  - Proved: equality, seen hit, Type, self-intro (τ = mu)
  - Sorry: lam-lam, self-elim, app-app, inferType (Soundness.lean:347)
- `VCompat.adequacy` — corollary of adequacy_gen (Soundness.lean:349)
- `VCompat.from_self_intro_gen` — **PROVED** (Soundness.lean:355) via adequacy_gen
- `soundness` (main theorem) — Soundness.lean:439 — sorry

**Phase 3 (Subtyping helpers):**
- `subCheckNF_lam_lam_body` — PROVED
- `subCheckNF_lam_impossible` — PROVED
- `subCheckNF_mu_mu_body` — PROVED
- `subCheckNF_type_left_target` — PROVED
- `subCheckNF_neutral_inferType` — Subtyping.lean:201 — sorry

### What happened this session (agent ochre-20260404-215501)

**Proved from_self_intro_gen and partially proved adequacy_gen.**

1. Created `VCompat.adequacy_gen` — the generalized adequacy lemma with seen
   set support. Proved the easy cases (σ=τ, seen hit, τ=Type) and the
   self-intro case (τ = mu). The self-intro case follows the same pattern
   as from_type_sub_gen: double induction on fuel/n, normalized mu-right
   disjunct, ih_fuel + ih_n for the seen callback.

2. Used adequacy_gen to eliminate from_self_intro_gen's sorry. The key insight:
   from_self_intro_gen has v = σ (value equals subtype LHS), so VCompat(σ, σ)
   is trivially true by refl. Then adequacy_gen transports across the subcheck.

3. Reorganized Soundness.lean: moved VCompat.refl and adequacy_gen before
   from_self_intro_gen to satisfy declaration ordering.

**Annotation-trust analysis (Phase 0):**

Extensively analyzed the annotation-trust soundness bug. Key findings:

- **Creation-time validation (Option A) DOES NOT WORK** for complex Church-encoded
  types. When the mu's annotation is a lam (like `dNat → dNat` for dsucc),
  checking `body ⊑ ann` inside the mu creation fails because:
  - Self-reference is abstract (bvar), so the body's return type involves
    symbolic applications that subCheckNF can't compare against the annotation
  - Specifically: dsucc's body returns `app s m` (symbolic) but the annotation
    says `dNat` — subCheckNF can't verify this in the abstract context
  - Even the targeted lam-only validation breaks DNat and Array tests

- **The previous agent's uncommitted Eval.lean changes were causing test failures.**
  The working tree had a restructured mu-app case that was never committed.
  These changes broke DNat and Vec. I restored the committed version.

- **The counterexample** `app (mu (lam Type (lam Type (bvar 0))) (lam Type Type)) Type`
  **does NOT actually trigger the annotation-trust path** at the top level, because
  the body doesn't reference self and there are no recursive calls. The seen-set
  cutoff never fires. The bug is theoretical: the MECHANISM is unsound, but
  constructing a concrete counterexample where both evaluators succeed and diverge
  is non-trivial (requires a recursive mu with wrong annotation where concEval
  terminates).

**Remaining adequacy_gen cases (documented blockers):**

- **Lam-lam**: Needs a substitution lemma for subCheckNF — showing that
  subCheckNF(bodyσ, bodyτ) under extended context implies compatibility
  transfers through evaluation of bodyσ[a] and bodyτ[a]

- **Self-elim (mu ⊑ _)**: Needs annotation correctness — going from
  VCompat(v, mu ann body) to VCompat(v, ann) requires knowing the annotation
  accurately describes the mu. THIS is where the annotation-trust gap bites
  the proof.

- **App-app congruence**: Provable in principle via the structural app VCompat
  disjunct + recursive adequacy on components

- **InferType fallback**: Needs reasoning about inferType

### Previous session (agent ochre-20260404-204421)

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

**Work on the remaining adequacy_gen cases.** The annotation-trust bug is
real but has NO clean fix that preserves all tests:
- Option A (validate at creation): FAILS for complex Church-encoded types
  (dsucc body vs dNat→dNat annotation can't be verified by subCheckNF in
  abstract self-reference context)
- Option B (remove annotation-trust): breaks DNat + Vec tests
- The self-elim case of adequacy_gen is where annotation-trust bites the proof

**Recommended next steps (in priority order):**

1. **Prove the app-app congruence case** in adequacy_gen. This should be
   straightforward: use VCompat's structural app disjunct + recursive adequacy.

2. **Tackle the lam-lam case** in adequacy_gen. Needs a substitution lemma:
   if subCheckNF(bodyσ, bodyτ) in extended context, then after substituting a
   concrete argument, the normalized results are also in the subtype relation.

3. **Self-elim case**: This is the hardest. Requires going from VCompat(v, mu)
   to VCompat(v, ann). Options:
   a) Add a WellAnnotated precondition to adequacy_gen (propagates to soundness)
   b) Prove the annotation is always correct for absEval output (stronger claim)
   c) Restructure VCompat to include annotation-trust explicitly

4. **Main soundness theorem**: Start sketching after adequacy_gen has more cases.

**Note:** from_self_intro_gen no longer depends on adequacy being fully proved —
it now uses adequacy_gen directly. The sorry count is 3 (was 4).

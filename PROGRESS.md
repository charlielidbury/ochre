# Progress

## Current state: mu experiment (branch claude/mu-experiment)

We have replaced `fix` (recursion) and `iota` (self types) with a single
unified primitive `mu` (self-reference). See `docs/ideas/merge-fix-iota.md`
for the full design rationale, and **SUGGESTIONS.md** for the current
roadmap and strategy.

### Build status

`lake build` passes with **4 sorry warnings**:
- Monotonicity.lean: 3 (absEval_mono [mu-app body-unfold/cross/none subcases],
  absEval_mono_trans, absEval_succeeds_envsub)
- Soundness.lean: 1 (soundness_gen)

### Recent changes (2026-04-01, agent ochre-lean-20260401-200028)

**Monotonicity proof progress: fix build, prove lam-annotation mu-app case**

1. **Eval.lean change (from previous agent, uncommitted):** absEval no longer
   normalizes mu annotations. The annotation passes through unchanged:
   `mu x ann body` → `mu x ann body'`. This makes `mu_body` apply directly
   (same annotation in both envs), fixing the fundamental monotonicity obstacle.

2. **Build fix (Monotonicity.lean):** Added `| mu _ _ _ => cases hf_sub` to
   six catch-all branches in the app case that previously caught mu in the
   `| _ =>` wildcard. Lean 4's dependent elimination couldn't handle the
   complex mu-app match expression in `cases h₂`, but mu in function position
   is impossible for these cases (var/app/asc ⊑ mu is ruled out by Subtype').

3. **Lam-annotation mu-app case proved** (both `.refl` and `.app_cong`):
   When both envs evaluate the annotation to a lam, monotonicity follows
   by lam_rhs_shape + IH on the return body. This handles all fix-like mus
   (where the annotation is a function type like Nat→Nat→Nat).

### Previous changes (2026-04-01, agent ochre-lean-20260401-192428)

Domain normalization in subCheckNF flipped M4a (Phase 1 COMPLETE).
See git log for details.

### ALL M1-M4 milestones now PASSING

| Test | Description | Status |
|------|-------------|--------|
| M1a | `addRec ⊑ SelfNat→SelfNat→Nat` | PASS |
| M1b | `addRec 0 3 = 3` (concrete) | PASS |
| M1c | `addRec 2 1` is a Nat (concrete) | PASS |
| M1d | `addRec (abstract) (abstract) ⊑ Nat` | PASS |
| M2a | `mapArray` base case (concrete) | PASS |
| M3a | `appendArrays` base case (concrete) | PASS |
| **M4a** | **`appendVec ⊑ T→Vec T→Vec T→Vec T`** | **PASS ← NEW** |
| M4b | `appendVec (abstract) (abstract) ⊑ Vec Nat` | PASS |
| M4c | `appendVec` concrete ⊑ Vec Nat | PASS |

### Remaining expected-fail tests

- **Variant B (§10):** `zero_mu ⊑ MuNat` and `add_mu ⊑ MuNat→MuNat→MuNat`.
  These are truly self-referential Nat (Cedille-style) which need
  equi-recursive subtyping. Not blocking the current milestone.

### What was completed in the mu migration

- [x] Replace fix+iota with mu in Syntax.lean
- [x] Update Eval.lean (concEval, absEval, concEvalS)
- [x] Update Subtyping.lean (mu_body, self-intro, self-elim, inferType)
- [x] Update Tests.lean (all fix→mu, all iota→mu)
- [x] Sorry Soundness.lean and Monotonicity.lean
- [x] Gut Closure.lean, delete SoundnessS.lean
- [x] Add abstract add tests (§9: Church-style, §10: Variant B)
- [x] Add milestone ladder (§11: M1-M4 toward appendVec)
- [x] **Annotation-based mu-elim in absEval (M1d, M4b, M4c passing)**
- [x] **Domain normalization in subCheckNF (M4a passing)**

### Key findings

1. **The annotation field on mu is load-bearing.** absEval uses it
   to determine return types for recursive mus, preventing divergence.
   For fix-like mus (annotation = function type), the annotation is used.
   For iota-like mus (annotation = Type), body unfolding is used instead.

2. **The subtype checker compensates for the evaluator.** absEval does NOT
   do type-directed evaluation. When it hits `app (var "n") arg` where n is
   abstract, it returns a stuck application. The subtype checker's
   `inferType` function does mu-elim to recover type information.

3. **Domains need normalization in the subtype checker.** absEval does not
   normalize lambda domains (to preserve monotonicity). But subCheckNF's
   inferType needs domains in normal form to pattern-match on them. The
   `normalizeDomain` helper resolves this by normalizing domains before
   adding them to the inferType context.

4. **Variant A (SelfNat = mu n Type Nat') works because the self variable
   is unused.** The mu is a trivial wrapper around Church Nat. mu-elim
   strips it off. This is enough for non-recursive abstract add.

5. **Variant B (MuNat, truly self-referential) still fails subtyping.**
   Self-intro substitution produces structurally different but semantically
   equal terms. This likely needs equi-recursive subtyping.

### What needs to happen next

**Phase 1 is COMPLETE.** All M1-M4 milestones pass. The definitions are
expressive enough for abstract appendVec with the mu primitive.

**Phase 3 (proofs) is underway.** Key status:
- **absEval_mono mu case (body eval):** DONE. Annotation passes through
  unchanged, so mu_body applies directly.
- **absEval_mono mu-app case (lam annotation):** DONE. Both `.refl` and
  `.app_cong` subcases proved. Covers all fix-like mus.
- **absEval_mono mu-app case (body-unfold path):** BLOCKED. When both envs
  evaluate the annotation to non-lam, the body-unfold path produces different
  unfolded expressions (`body₁.subst x (mu x ann body₁)` vs `body₂.subst x
  (mu x ann body₂)`). Proving monotonicity requires a **substitution
  congruence lemma**: `Subtype' e₂ e₁ → Subtype' v₂ v₁ →
  Subtype' (e₂.subst x v₂) (e₁.subst x v₁)`. This is FALSE for the current
  Subtype' because `lam_body` requires same domain, and substitution changes
  domains differently. **Possible fixes:**
  1. Add a `lam_dom` Subtype' constructor for different domains
  2. Restrict the body-unfold path to only fire when `ann = Type` (then the
     annotation eval is always `some .type` in both envs — no cross-case)
  3. Prove a weaker substitution lemma that applies to the specific shapes
     produced by absEval
- **absEval_mono_trans:** Depends on absEval_mono being fully proved.
- **absEval_succeeds_envsub:** Independent but also blocked by similar
  mu-app case analysis.
- **soundness_gen:** Separate from monotonicity; needs its own analysis.

### Key files

| File | Status | Sorry count |
|------|--------|-------------|
| Syntax.lean | Done | 0 |
| Eval.lean | Done (ann not normalized in mu, annotation-based mu-elim in app) | 0 |
| Subtyping.lean | Done (domain normalization) | 0 |
| Tests.lean | All milestones passing, Variant B expected-fail | 0 |
| Soundness.lean | Sorry'd | 1 |
| Monotonicity.lean | Partially proved (mu-body done, mu-app lam-ann done) | 3 |
| Closure.lean | Gutted | 0 |
| CounterexampleTest.lean | Done | 0 |

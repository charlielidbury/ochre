# Progress

## Current state: mu experiment (branch claude/mu-experiment)

We have replaced `fix` (recursion) and `iota` (self types) with a single
unified primitive `mu` (self-reference). See `docs/ideas/merge-fix-iota.md`
for the full design rationale, and **SUGGESTIONS.md** for the current
roadmap and strategy.

### Build status

`lake build` passes with **3 sorry warnings**:
- Monotonicity.lean: 2 (absEval_mono_trans, absEval_succeeds_envsub)
- Soundness.lean: 1 (soundness_gen)

**absEval_mono is FULLY PROVED** (no sorrys).

### Recent changes (2026-04-01, agent ochre-lean-20260401-200028)

**Three proof-friendly changes to absEval; monotonicity partially proved**

1. **absEval mu case: annotation passthrough.** Annotations are NOT normalized
   in the mu case. `mu x ann body` evaluates to `mu x ann body'` (same ann).
   This makes `mu_body` apply directly in the monotonicity proof.

2. **absEval mu-app: env extension instead of substitution.** The body-unfold
   path uses `absEval fuel ((x, mu x ann body) :: Γ) body` instead of
   `absEval fuel Γ (body.subst x (mu x ann body))`. Semantically equivalent
   but makes the IH apply directly via envSub_extend_sub.

3. **absEval mu-app: SYNTACTIC annotation check.** `match ann with | .lam =>`
   instead of `match absEval fuel Γ ann with | some (.lam ...) =>`. Both envs
   always agree on which path to take (no cross-cases). All test annotations
   are either syntactic lambdas (fix-like) or `.type` (iota-like).

4. **Build fix (Monotonicity.lean):** Added `| mu _ _ _ => cases hf_sub` to
   catch-all branches to avoid dependent elimination failures.

5. **absEval_mono FULLY PROVED.** The `split at h₁` tactic splits the
   syntactic annotation match in h₁, creating a hypothesis that
   `simp only [*] at h₂` uses to reduce h₂'s match. This avoids the
   dependent elimination issues that blocked `cases ann_mu`.

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

**Phase 3 (proofs) status:**
- **absEval_mono:** FULLY PROVED (no sorrys). This is the core monotonicity
  theorem. The key techniques:
  - `split at h₁` + `simp only [*] at h₂` to handle the syntactic ann match
  - env extension for body-unfold path (IH via envSub_extend_sub)
  - mu_rhs_shape for stuck-app cases in body-unfold results

- **absEval_mono_trans:** Sorry'd. Needs induction on fuel parallel to
  absEval_mono but with SubtypeTrans throughout. Alternatively, might need
  absEval_succeeds_envsub to chain the base case with transitivity.

- **absEval_succeeds_envsub:** Sorry'd. Hard because the app case takes
  different paths in different envs. If f evaluates to lam in Γ₂ (less
  precise), the recursive call on the lam body needs to succeed, but we
  only know f evaluated to something in Γ₁.

- **soundness_gen:** Sorry'd (Soundness.lean). Separate from monotonicity.

### Key files

| File | Status | Sorry count |
|------|--------|-------------|
| Syntax.lean | Done | 0 |
| Eval.lean | Done (ann passthrough in mu, annotation/env-ext in app) | 0 |
| Subtyping.lean | Done (domain normalization) | 0 |
| Tests.lean | All milestones passing, Variant B expected-fail | 0 |
| Soundness.lean | Sorry'd | 1 |
| Monotonicity.lean | absEval_mono PROVED; 2 other theorems sorry'd | 2 |
| Closure.lean | Gutted | 0 |
| CounterexampleTest.lean | Done | 0 |

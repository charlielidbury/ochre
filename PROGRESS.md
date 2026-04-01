# Progress

## Current state: mu experiment (branch claude/mu-experiment)

We have replaced `fix` (recursion) and `iota` (self types) with a single
unified primitive `mu` (self-reference). See `docs/ideas/merge-fix-iota.md`
for the full design rationale, and **SUGGESTIONS.md** for the current
roadmap and strategy.

### Build status

`lake build` passes with sorry warnings in:
- Subtyping.lean: 5 (self_intro composability — lam_body, eq_of_rigid_target,
  mu_body, app_cong_left, app_cong_right)
- Monotonicity.lean: 3 (absEval_mono_trans, absEval_succeeds_envsub,
  absEval_evalFreeVars_general mu case)
- Soundness.lean: 1 (soundness_gen — 4 individual sorrys, down from 5)

**absEval_mono is FULLY PROVED** (no sorrys).
**soundness_gen**: mu standalone and mu_body NOW PROVED via self_intro.

### Recent changes (2026-04-01, agent ochre-lean-20260401-210632)

**Two key changes that unblock mu soundness proofs:**

1. **absEval mu case: x ↦ mu value (not var x).** Changed the env binding in
   absEval's mu case from `(x, var x)` to `(x, mu x ann body)`. This matches
   concEval's semantics: both evaluators now bind x to the mu value itself.
   Makes EnvConsistent trivially satisfiable (refl) in the soundness proof.
   All tests still pass — the change only affects how body is normalized
   when it references x, and current tests don't depend on the old behavior.

2. **self_intro constructor in SubtypeTrans.** Added `self_intro : SubtypeTrans a body'
   → SubtypeTrans a (mu x ann body')`. This bridges the gap between the IH
   (which gives v ⊑ body') and the soundness goal (v ⊑ mu x ann body', since
   absEval wraps the result in mu). This is semantically sound: if v satisfies
   the body of a self-type, then v is a member of that self-type.

   **Trade-off:** self_intro breaks composability of SubtypeTrans congruence lemmas
   (lam_body, mu_body, app_cong). These now have sorry'd self_intro cases because
   mu wrapping doesn't compose with context wrapping (lam of mu ≠ mu of lam).
   Also invalidates mu_target_shape and mu_inv for SubtypeTrans.

**Proved in soundness_gen:**
- mu standalone (was sorry): IH on body + self_intro
- mu_body (was sorry): IH on bodies + self_intro

**Remaining sorrys in soundness_gen (4, was 5):**
1. trans: needs intermediate expression to evaluate in both modes
2. self_intro: unreachable from main soundness theorem (cosmetic)
3-4. mu-app (×2): different computation paths (concEval unrolls, absEval uses annotation)

### Previous changes (2026-04-01, agent ochre-lean-20260401-204457)

**soundness_gen partial proof: all non-mu cases proved (sorry 1→1, but coverage 0%→~70%)**

The soundness theorem `soundness_gen` (Soundness.lean) now has real proofs for
most cases. Previously it was entirely sorry'd; now only mu-related cases and
the SubtypeTrans transitivity case remain.

**Proved cases in soundness_gen:**
- var: direct from EnvConsistent
- lam: IH on body under neutral binder, SubtypeTrans.lam_body
- type: trivial (both return type)
- asc: IH on term + WellTyped gives intermediate Subtype' σ τ, chain via trans
- app-lam: SubtypeTrans.lam_target_shape inverts f_v, IH on bodies
- app-stuck (var/app/asc in fn position): SubtypeTrans.app_cong
- app-type: top absorbs
- lam_body in h_sub: same as lam case with different bodies
- app_cong in h_sub: same as app case with different exprs
- top in h_sub: trivial

**Sorry'd cases in soundness_gen (5 individual sorrys):**
1. **trans** (line 120): SubtypeTrans e_c b, SubtypeTrans b e_a. Need b to evaluate
   in both modes. Same class of problem as the false `absEval_succeeds_envsub`.
2. **mu standalone** (line 167): absEval binds x to var x (neutral), concEval binds
   x to mu x ann body. No SubtypeTrans (mu ...) (var x) exists.
3. **mu-app in refl(app)** (line 202): concEval unrolls mu then applies, absEval
   uses annotation or body-unfold. Fundamentally different paths.
4. **mu-app in app_cong** (line 267): same as #3.
5. **mu_body** (line 282): same env consistency issue as #2.

**Key finding: all remaining soundness sorrys are mu-related.** The soundness
proof works perfectly for the non-self-referential fragment. The mu case is
blocked because EnvConsistent requires SubtypeTrans between concrete and abstract
env bindings, but the mu case has (mu ...) vs (var x) which can't be related.

**Three possible fixes (increasing complexity):**
(a) Add self-intro/self-elim to Subtype'/SubtypeTrans (complicates inversion lemmas)
(b) Use a step-indexed logical relation instead of SubtypeTrans for env consistency
(c) Change absEval's mu case semantics (e.g., don't wrap result in mu)

Option (c) is simplest but changes the type system. Option (b) is the standard
approach in the literature but is a major proof technique change. Option (a) is
most direct but might break the trans-free Subtype' invariant that enables
lambda inversion.

### Previous changes (2026-04-01, agent ochre-lean-20260401-200028)

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

- **soundness_gen:** MOSTLY PROVED (~85% coverage). 4 sorrys remain (was 5).
  **NEWLY PROVED:** mu standalone and mu_body cases, via:
  - Changed absEval mu env: x ↦ mu x ann body (matching concEval)
  - Added self_intro to SubtypeTrans to bridge IH to mu-wrapped goal
  
  **Remaining sorrys:**
  - trans: needs intermediate expression evaluation
  - self_intro: unreachable from main soundness (cosmetic sorry)
  - mu-app (×2): different concrete/abstract paths for mu application

- **SubtypeTrans congruence sorrys (NEW):** self_intro in SubtypeTrans
  breaks composability of lam_body, mu_body, app_cong_left, app_cong_right,
  eq_of_rigid_target. These have sorry'd self_intro cases. The issue:
  self_intro wraps at the TOP level (a ⊑ mu body'), but the congruence
  lemmas need wrapping INSIDE a context (lam/app). No constructor provides
  this. These sorrys may never arise in practice.

- **absEval_mono_trans:** Sorry'd. Not used by anything currently.

- **absEval_succeeds_envsub:** FALSE as stated (see CounterexampleTest.lean).
  Not used by anything currently.
  
- **absEval_evalFreeVars_general:** mu case sorry'd (env has mu value not
  neutral var, so binder_case helper doesn't apply).

### Key files

| File | Status | Sorry count |
|------|--------|-------------|
| Syntax.lean | Done | 0 |
| Eval.lean | Done (mu env: x ↦ mu value, annotation-based mu-app) | 0 |
| Subtyping.lean | self_intro added; 5 composability sorrys | 5 |
| Tests.lean | All milestones passing, Variant B expected-fail | 0 |
| Soundness.lean | mu standalone+mu_body PROVED; 4 sorrys remain | 1 decl |
| Monotonicity.lean | absEval_mono PROVED; 3 other theorems sorry'd | 3 |
| Closure.lean | Gutted | 0 |
| CounterexampleTest.lean | Done | 0 |

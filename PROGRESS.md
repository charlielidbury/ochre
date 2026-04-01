# Progress

## Current state: mu experiment (branch claude/mu-experiment)

We have replaced `fix` (recursion) and `iota` (self types) with a single
unified primitive `mu` (self-reference). See `docs/ideas/merge-fix-iota.md`
for the full design rationale, and **SUGGESTIONS.md** for the current
roadmap and strategy.

### Build status

`lake build` passes with **4 sorry warnings** (4 declarations, 8 sorry sites):
- Monotonicity.lean: 3 declarations (absEval_mono [6 cross-case sorrys],
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
- **absEval_mono mu-app case (body-unfold):** DONE. Changed absEval to use
  env extension instead of substitution for the body-unfold path. Now
  `absEval fuel ((x, mu x ann body) :: Γ) body` instead of
  `absEval fuel Γ (body.subst x (mu x ann body))`. This makes the IH
  apply directly via envSub_extend_sub with mu_body.
- **absEval_mono mu-app cross-cases:** BLOCKED (6 sorrys). These are
  cases where one env takes the annotation path and the other takes the
  body-unfold path. There are three variants, each appearing in both
  `.refl` and `.app_cong`:
  1. Γ₁ ann fails, Γ₂ ann succeeds as lam → Γ₁ body-unfold, Γ₂ annotation
  2. Γ₁ ann succeeds as lam, Γ₂ ann fails → Γ₁ annotation, Γ₂ body-unfold
  3. Both succeed but Γ₁ non-lam, Γ₂ lam → Γ₁ body-unfold, Γ₂ annotation
     (By Subtype', lam ⊑ non-lam only via .top, so ann₁ must be type)
  
  These require relating two different computation strategies (annotation
  return type vs body unfolding). Without a formal link between a mu's
  annotation and body, this seems unprovable from monotonicity alone.
  
  **Possible approaches:**
  - Prove absEval_succeeds_envsub first (rules out case 1: if Γ₁ is more
    precise, it should also succeed — eliminates the none/some cross-case)
  - Add a well-typedness invariant: the body of a mu conforms to its
    annotation. Then cross-cases become: body-unfold result ⊑ annotation,
    which follows from well-typedness.
  - Restrict annotation path to only fire when annotation is syntactically
    a lambda (not just evaluates to one). This eliminates cross-case 3
    since both envs would agree.

- **absEval_mono_trans:** Depends on absEval_mono being fully proved.
- **absEval_succeeds_envsub:** Independent. Proving this would eliminate
  some cross-cases in absEval_mono.
- **soundness_gen:** Separate from monotonicity; needs its own analysis.

### Key files

| File | Status | Sorry count |
|------|--------|-------------|
| Syntax.lean | Done | 0 |
| Eval.lean | Done (ann passthrough in mu, annotation/env-ext in app) | 0 |
| Subtyping.lean | Done (domain normalization) | 0 |
| Tests.lean | All milestones passing, Variant B expected-fail | 0 |
| Soundness.lean | Sorry'd | 1 |
| Monotonicity.lean | Mostly proved (mu-body, mu-app lam-ann, mu-app body-unfold done; cross-cases sorry'd) | 3 |
| Closure.lean | Gutted | 0 |
| CounterexampleTest.lean | Done | 0 |

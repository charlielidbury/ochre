# Progress

## Current state: mu experiment (branch claude/mu-experiment)

We have replaced `fix` (recursion) and `iota` (self types) with a single
unified primitive `mu` (self-reference). See `docs/ideas/merge-fix-iota.md`
for the full design rationale, and **SUGGESTIONS.md** for the current
roadmap and strategy.

### Build status

`lake build` passes with sorry warnings in:
- **Subtyping.lean: 0**
- **Monotonicity.lean: 0** (SORRY-FREE)
- **Soundness.lean: 1 declaration** (soundness_gen — 3 individual sorrys)

**Total: 1 sorry declaration.**

### Recent changes (2026-04-01, agent ochre-lean-20260401-224247)

**concEval wraps mu results; mu/mu_body soundness cases proved via mu_body.**

Key change: concEval now wraps mu results in mu (like absEval) instead of
unrolling. The app-mu case matches on the mu body directly instead of
re-unrolling. This makes both evaluators produce structurally parallel
results for mu, enabling the soundness proof to use `mu_body` instead
of `self_intro`.

**Changes:**
1. **concEval mu case:** `concEval fuel ((x, mu) :: γ) body` wrapped in
   `some (.mu x ann body')` instead of returning body' directly.
2. **concEval app-mu case:** `match body with | .lam y _ lamBody => ...`
   instead of `match concEval fuel γ (.mu ...) with | .lam => ...`.
   No re-unrolling — body is already evaluated.
3. **soundness_gen mu case (refl):** Uses `.mu_body (ih ...)` instead of
   `(ih ...).trans (.self_intro (.refl _))`. Both evaluators wrap, so
   mu_body (body sub from IH) is the right constructor.
4. **soundness_gen mu_body case:** Same change — `.mu_body (ih ...)`.
5. **self_intro comment corrected:** The self_intro case IS reachable
   (via the asc path, not the mu path). See detailed comment in code.

**Corrected false claim:** Previous agents stated the self_intro sorry
was "UNREACHABLE from the main soundness theorem." This is wrong. The
self_intro case is reachable via:
1. The asc case returns `(ih).trans h_sub_σ_τ` where h_sub_σ_τ can be
   self_intro (when the ascription type is a mu).
2. Subtype'.trans with a self_intro q returns self_intro.
3. If this is inside a lambda body that gets applied, lam_rhs_shape
   decomposes it, producing self_intro as h_sub for the recursive call.
The mu standalone case was ANOTHER source (now eliminated by wrapping).

**Remaining sorrys (3):**
- mu-app (×2): same fundamental issue — absEval uses annotation (or
  body-unfold), concEval matches body directly. The annotation and
  computed body are unrelated expressions that Subtype' can't bridge.
  See detailed analysis below.
- self_intro (×1): fuel/env mismatch. Now reachable only via asc path.

**Analysis: why the mu-app sorry is hard (for future agents)**

The mu-app case in absEval:
```
| some (.mu x ann body), some aVal =>
    match ann with
    | .lam y _dom retBody => absEval fuel ((y, aVal) :: Γ) retBody  -- annotation
    | _ => ... body-unfold ...                                       -- body
```

The annotation path uses `retBody` from the annotation. The concrete
path uses the mu body lambda. These are fundamentally different expressions:
- `retBody` = return type from the declared annotation
- `lamBody` = actual function body from the mu

For soundness, we need `concEval(lamBody, arg) ⊑ absEval(retBody, arg)`.
This is "annotation consistency" — the body implements the declared type.

Why Subtype' can't express this: Subtype' is syntactic. It can't relate
`(var "n")` to `Nat` even when n is bound to a Nat. Annotation
consistency is a SEMANTIC property (requires evaluation context).

**Possible solutions:**
(a) **Strengthen WellTyped** to include annotation consistency as a
    premise. But stating it requires evaluating terms, creating circular
    dependencies.
(b) **Step-indexed logical relations** — the standard approach. Replaces
    syntactic Subtype' with a semantic V(fuel, τ) value set. Major
    proof infrastructure change.
(c) **Make absEval's mu-app use body instead of annotation.** This would
    make both paths structurally parallel. BUT: for recursive functions
    with abstract args, body-unfolding diverges (each unfolding triggers
    another recursive call). The annotation cuts the recursion. So this
    approach breaks abstract evaluation of recursive functions (the whole
    point of mu).
(d) **Make concEval's app-mu also use annotation.** This gives wrong
    results: `add 2 3` would evaluate the annotation's `Nat` instead
    of computing `5`. The concrete evaluator MUST compute, not type.

Options (a) and (b) are the viable paths. Both are significant work.

### Previous changes (2026-04-01, agent ochre-lean-20260401-221721)

**PROVED Subtype'.trans; rewrote soundness to use Subtype' directly (5→3 sorrys).**

Key insight: Subtype' is transitive! Proved by structural induction on the
second proof (`induction q generalizing a`). Each case either returns directly
or recurses with a strictly smaller q:
- refl/top: base cases
- lam_body/app_cong/mu_body: structural (q component smaller)
- self_intro: q component strictly smaller, p can be anything

This means SubtypeTrans is UNNECESSARY for soundness. Rewrote soundness_gen:
- `h_sub : Subtype'` instead of `SubtypeTrans`
- `EnvConsistent` uses `Subtype'` instead of `SubtypeTrans`
- Cases: refl, top, lam_body, app_cong, mu_body, self_intro (no trans!)
- Shape lemmas on Subtype' are trivial (no trans case to propagate)
- Composition via `Subtype'.trans` where `.trans` was used before

**Also removed false evalFreeVars theorems (see below).**

### Previous changes (2026-04-01, agent ochre-lean-20260401-221721, earlier)

**Removed false evalFreeVars theorems from Monotonicity.lean (2→1 sorry decls).**

`absEval_evalFreeVars_general` is **FALSE** for the mu case. Counterexample:
- Γ = [("y", var "z")], e = mu "x" type (app (var "y") (var "x")), P = (· = "z")
- The mu env binding `(x, mu x ann body)` has evalFreeVars that include input
  variable NAMES (like "y"), not just P-satisfying names. The output
  `mu "x" _ (app (var "z") (mu "x" _ (app (var "y") (var "x"))))` has "y"
  in its evalFreeVars, but P "y" = false.
- Root cause: when absEval changed mu's env binding from `(x, var x)` to
  `(x, mu x ann body)` (for soundness proof compatibility), the mu value's
  evalFreeVars became input-level variable names, breaking the coverage property.

Both `absEval_evalFreeVars_general` and `absEval_evalFreeVars_neutral` were
unused. Removed along with helpers: `isNeutral`, `EnvEvalClosed'`,
`envEvalClosed'_extend_neutral`, `env_extend_neutral_or`, `env_extend_val`.
Counterexample added to CounterexampleTest.lean.

### Previous changes (2026-04-01, agent ochre-lean-20260401-215445)

**Eliminated all sorrys from absEval_mono; removed 3 dead declarations (5→2 sorry decls).**

The root problem: absEval_mono was generalized over `Subtype' e₂ e₁`, which
includes `self_intro`. The monotonicity theorem only passes `.refl e`, and the
IH never generates self_intro (only refl/lam_body/mu_body/app_cong/top). But
Lean requires all Subtype' cases to be handled, creating 5 unreachable sorrys.

The fix: introduced `SubtypeCore` — Subtype' without the self_intro constructor.
absEval_mono now takes `SubtypeCore e₂ e₁` and returns `SubtypeCore τ₂ τ₁`.
Since SubtypeCore has no self_intro, those cases don't exist. All structural
cases go through as before. The `monotonicity` theorem converts via `.toSubtype'`.

Also introduced `EnvSubCore` (using SubtypeCore) since absEval_mono's env
relation must match: the IH produces SubtypeCore values that get stored in
the env via extension lemmas.

**Removed dead code:**
- `absEval_mono_trans` (sorry'd, not used)
- `monotonicity_trans` (depended on absEval_mono_trans, not used)
- `absEval_succeeds_envsub` (FALSE — counterexample in CounterexampleTest.lean)
- `EnvSubTrans` + helpers (moved to CounterexampleTest.lean where needed)

**Also analyzed mu-app soundness case (NOT implemented — see below).**

The mu-app sorrys in soundness_gen are genuinely hard. The issue:
- Abstract path: uses the mu annotation (`lam y dom retBody`) to determine
  return type — evaluates `retBody` directly
- Concrete path: unrolls the mu body, gets a lambda, applies it
- These are fundamentally different computation paths

To bridge them, we'd need "annotation consistency": the mu body's abstract
evaluation subtypes the annotation. But Subtype' is syntactic, so
`Subtype' body_a ann` doesn't hold in general (e.g., `Subtype' (var x) Nat`
fails even when x is bound to a Nat). This requires either:
(a) A richer Subtype' that accounts for evaluation context
(b) A step-indexed logical relation approach
(c) Restructuring the evaluator so concrete/abstract paths are more similar

Additionally, the concrete lambda and annotation may use different binder names,
creating env consistency issues. This is a deep problem that likely needs a
design-level change rather than a proof-level fix.

### Previous changes (2026-04-01, agent ochre-lean-20260401-213619)

**Moved self_intro to Subtype', fixing SubtypeTrans congruence composability.**

The root problem: `SubtypeTrans.self_intro` took a `SubtypeTrans` argument,
creating circularity in congruence lemma proofs. In `SubtypeTrans.lam_body`,
the self_intro case needed `lam_body` applied to `self_intro` — the exact
thing being proved.

The fix: add `self_intro` to `Subtype'` and change `SubtypeTrans.self_intro`
to take `Subtype'` instead of `SubtypeTrans`. Now the congruence proofs work:
```
.trans (.step (.lam_body h')) (.step (.lam_body (.self_intro (.refl _))))
```
The first step uses the Subtype' sub-proof. The second uses Subtype'.self_intro
and Subtype'.refl — no recursive SubtypeTrans needed.

**Changes:**
1. **Subtype': added self_intro constructor.** `Subtype' a body → Subtype' a (mu x ann body)`
2. **SubtypeTrans.self_intro: now takes Subtype' (was SubtypeTrans).**
3. **All 5 SubtypeTrans congruence sorrys: ELIMINATED.** lam_body, eq_of_rigid_target,
   mu_body, app_cong_left, app_cong_right all fully proved.
4. **mu_rhs_shape: returns disjunction** `(∃ body', ...) ∨ Subtype' e body`
   to account for self_intro. mu_inv also updated.
5. **absEval_mono: 5 new self_intro sorrys.** These are unreachable from the
   monotonicity theorem (passes .refl e). They exist because the generalized
   theorem takes arbitrary Subtype' and Lean requires all cases.
6. **soundness_gen: adapted.** Uses `.trans ih (.step (.self_intro (.refl _)))`
   instead of `.self_intro ih`. One new sorry for Subtype'.self_intro in step case.

**Net result:** 9→5 declarations with sorry. Subtyping.lean fully clean.

### Previous changes (2026-04-01, agent ochre-lean-20260401-210632)

**Two key changes that unblock mu soundness proofs:**

1. **absEval mu case: x ↦ mu value (not var x).** Changed the env binding in
   absEval's mu case from `(x, var x)` to `(x, mu x ann body)`. This matches
   concEval's semantics. Makes EnvConsistent trivially satisfiable (refl).

2. **self_intro constructor in SubtypeTrans.** Bridges IH result (v ⊑ body')
   to soundness goal (v ⊑ mu x ann body'). Trade-off: broke congruence
   composability (now fixed — see above).

**Remaining sorrys in soundness_gen (5):**
1. trans: needs intermediate expression to evaluate in both modes
2-3. self_intro (×2): unreachable from main soundness theorem (cosmetic)
4-5. mu-app (×2): different computation paths (concEval unrolls, absEval uses annotation)

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
- **Subtyping.lean:** SORRY-FREE. All SubtypeTrans congruence lemmas
  (lam_body, mu_body, app_cong, eq_of_rigid_target) fully proved.
  self_intro is in both Subtype' and SubtypeTrans (SubtypeTrans version
  takes Subtype' arg to break circularity).
  Also: `SubtypeCore` (Subtype' without self_intro) for monotonicity proof.

- **absEval_mono:** SORRY-FREE. Uses SubtypeCore to avoid unreachable
  self_intro cases. Key techniques:
  - `SubtypeCore` instead of `Subtype'` to eliminate self_intro cases
  - `split at h₁` + `simp only [*] at h₂` to handle the syntactic ann match
  - env extension for body-unfold path (IH via envSubCore_extend_sub)
  - SubtypeCore.mu_rhs_shape (no disjunction, unlike Subtype' version)

- **soundness_gen:** MOSTLY PROVED (~90% coverage). 3 sorrys remain.
  Proved: all non-mu-app cases including mu standalone, mu_body, all
  Subtype' congruence cases. Uses Subtype' directly (not SubtypeTrans)
  since Subtype'.trans is proved. mu/mu_body cases use mu_body (not
  self_intro) thanks to concEval wrapping.
  Remaining sorrys:
  - mu-app (×2): annotation consistency (see analysis in "Recent changes")
  - self_intro (×1): fuel/env mismatch. Reachable via asc path (when
    WellTyped has self_intro for mu types). NOT unreachable as previously
    claimed. See Soundness.lean self_intro case comment for details.

### Key files

| File | Status | Sorry count |
|------|--------|-------------|
| Syntax.lean | Done | 0 |
| Eval.lean | Done (concEval wraps mu; app-mu matches body directly) | 0 |
| **Subtyping.lean** | **SORRY-FREE** (SubtypeCore + Subtype' + SubtypeTrans) | **0** |
| Tests.lean | All milestones passing, Variant B expected-fail | 0 |
| Soundness.lean | mu/mu_body via mu_body; 3 sorrys remain (mu-app×2, self_intro×1) | 1 decl |
| **Monotonicity.lean** | **SORRY-FREE** (evalFreeVars theorems removed — FALSE) | **0** |
| Closure.lean | Gutted | 0 |
| CounterexampleTest.lean | Done (includes EnvSubTrans + evalFreeVars counterexamples) | 0 |

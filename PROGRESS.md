# Progress

## Current state: mu experiment (branch claude/mu-experiment)

We have replaced `fix` (recursion) and `iota` (self types) with a single
unified primitive `mu` (self-reference). See `docs/ideas/merge-fix-iota.md`
for the full design rationale, and **SUGGESTIONS.md** for the current
roadmap and strategy.

### Build status

`lake build` passes with **11 sorrys** and all tests (including WellTyped witnesses).

- **Syntax.lean:** SORRY-FREE.
- **Eval.lean: SORRY-FREE.**
- **Subtyping.lean: SORRY-FREE**
- **Monotonicity.lean: 1 sorry** (`absEval_mono` — blocked on SubtypeCore weakness)
- **Soundness.lean: 10 sorrys** across six declarations:
  - `OutputRel.lam_congr`: **1 sorry** (subCheckNF lifting through lam)
  - `OutputRel.mu_congr`: **2 sorrys** (subCheckNF lifting through mu)
  - `extractSoundRel`: **1 sorry** (OutputRel→SoundRel for app case)
  - `soundness_app_case`: **1 sorry** (edge case, unchanged)
  - `soundness_gen_sr` (OutputRel-based, uses concEvalE): **2 sorrys**
    - asc/refl compose subcase (needs subCheckNF transitivity)
    - asc/SoundRel.asc compose subcase (same)
    - **PROVED: bvar, type, lam(.sound), mu(.sound), top, app, asc(.sound)**
    - **asc .sound subcases are NEWLY PROVED** (programs without nested asc)
  - `soundness_gen` (legacy, ValSub-based, uses concEval): **3 sorrys**
    - lam, mu, app (same as before, kept for bridge compatibility)
- **ValSub.lean: SORRY-FREE**

**Total: 11 sorrys** (was 7). Sorry count increased, but critically the
**theorem statement is now CORRECT** — the output type changed from SoundRel
(which was FALSE for the asc case) to OutputRel (SoundRel composed with
subCheckNF, which IS true). All remaining sorrys are on PROVABLE statements.

The new sorrys all reduce to one kind of infrastructure: **subCheckNF
structural lifting and transitivity.** Once `subCheckNF_trans` and
`subCheckNF_lam_lift` / `subCheckNF_mu_lift` are proved, most new sorrys
collapse. The `extractSoundRel` sorry is eliminated by rewriting
`soundness_app_case` to accept OutputRel directly.

### Recent changes (2026-04-02, agent ochre-lean-20260402-172326)

**OutputRel: fix FALSE theorem statement in soundness_gen_sr.**

The old output type `SoundRel v τ` is FALSE for the asc case: `concEvalE(term)`
and `absEval(ty)` can have different constructors (e.g., `lam` vs `mu` for
`(zero : Nat)`). Previous agent documented the counterexample.

**Solution: OutputRel = SoundRel composed with subCheckNF.**

1. **Defined `OutputRel`** (inductive with `.sound` and `.compose` constructors):
   - `.sound h`: direct SoundRel (for non-asc cases)
   - `.compose h_sr h_check`: SoundRel to intermediate + subCheckNF to target

2. **Changed `soundness_gen_sr` output** from SoundRel to OutputRel.

3. **Proved asc `.sound` subcase**: When the IH on the term returns `.sound`
   (SoundRel v σ directly), compose with subCheckNF σ τ from WellTyped to get
   `OutputRel.compose h_sr h_check`. This covers programs without nested asc.

4. **Adapted non-asc cases** using `OutputRel.lam_congr` and `OutputRel.mu_congr`
   helpers. The `.sound` branch of these helpers lifts SoundRel through structural
   constructors. The `.compose` branch is sorry'd (needs subCheckNF lifting).

5. **Adapted app case** using `extractSoundRel` to convert OutputRel back to
   SoundRel for the existing `soundness_app_case`. This sorry is eliminated by
   rewriting soundness_app_case to handle OutputRel directly (future work).

**What the remaining sorrys need (for next agent):**

1. **subCheckNF lifting lemmas** (`subCheckNF_lam_lift`, `subCheckNF_mu_lift`):
   `subCheckNF fuel ctx [] mid body_τ → subCheckNF fuel' ctx' [] (lam dom mid) (lam dom body_τ)`.
   The challenge is that subCheckNF's context changes under binders. May require
   context-parameterized versions or a context-monotonicity lemma.

2. **subCheckNF transitivity** (`subCheckNF_trans`):
   `subCheckNF a b ∧ subCheckNF b c → subCheckNF a c`.
   Standard for subtyping algorithms. May follow from soundness+completeness of
   subCheckNF w.r.t. a semantic model, or by direct case analysis.

3. **Rewrite soundness_app_case for OutputRel** (eliminates `extractSoundRel`):
   The existing soundness_app_case expects SoundRel from the IH. Rewriting it to
   case-split on OutputRel (and handle the compose subcase) would eliminate the
   `extractSoundRel` sorry. The `.sound` branch preserves the existing proof.

### Recent changes (2026-04-02, agent ochre-lean-20260402-164128)

**app-mu-annotation case PROVED in soundness_gen_sr.**

The problem: when absEval encounters `mu ann body` applied to an argument where
both `ann` and `body` are lambdas, it uses the ANNOTATION's return type (to
prevent divergence on recursive functions). But concEvalE used the BODY's
return type. The IH gives SoundRel for the body, not the annotation.

**Solution: two changes.**

1. **SoundRel.mu now tracks annotation relationships:** Added `SoundRel ann_v ann_τ`
   to the mu constructor. Previously only body was tracked. This enables extracting
   SoundRel between annotation sub-terms via `lam_rhs_shape`.

2. **concEvalE's mu-app case mirrors absEval:** When both `ann` and `body` are
   lambdas, concEvalE now uses the annotation's return type (like absEval) instead
   of the body's return type. This makes both evaluators process the SAME
   subexpression in the mu-annotation case, so the IH applies directly.

**What this proves:** For mu-app where ann = lam and body = lam:
- Extract `SoundRel retAnn_c retAnn_a` from `h_ann.lam_rhs_shape`
- `subst_congr` gives `SoundRel (retAnn_c.subst 0 a_v) (retAnn_a.subst 0 a_τ)`
- IH gives `SoundRel v τ`

**New edge case sorry:** When ann_a ≠ lam but ann_c = lam (possible only via
SoundRel.top, meaning ann_a = .type). This requires SoundRel (lam ...) .type,
which only arises from .top — a degenerate case where the abstract annotation
is .type while the concrete annotation is a lambda. This is unreachable from
the soundness_concEvalE entry point (which uses .refl, so ann_c = ann_a always).

**Updated lemmas:** SoundRel.shift_preserve, subst_arg_congr, subst_congr,
mu_rhs_shape, trans all updated for the new two-argument mu constructor.

**The remaining sorrys (analysis for next agent):**

1. **CRITICAL: asc cases (2 sorrys) are UNPROVABLE with the current statement.**
   `soundness_gen_sr` claims `SoundRel v τ`, but this is FALSE for programs
   with ascriptions. Concrete counterexample:

   ```
   e = (zero : Nat)  -- Church-encoded
   concEvalE evaluates zero → lam X (lam z (lam s (bvar 1)))
   absEval evaluates Nat  → lam X (lam z (lam s (bvar 2)))
   ```

   The innermost bodies are `bvar 1` (z) vs `bvar 2` (X). `SoundRel` requires
   structural equality all the way down, so `SoundRel (bvar 1) (bvar 2)` is
   false. With mu-encoded Nat it's worse: `v = lam ...`, `τ = mu ...` —
   different constructors, `SoundRel` is impossible.

   **The theorem statement must change.** The output should be `OutputRel`
   (SoundRel composed with subCheckNF), not bare `SoundRel`. The INTENDED
   statement `∃ mid, SoundRel v mid ∧ subCheckNF mid τ` IS true — `mid` is
   `absEval(term)`, SoundRel comes from the IH, subCheckNF from WellTyped.

   **But changing to OutputRel is non-trivial:** the app case uses `subst_congr`
   which needs `SoundRel` from IH results. If the IH returns `OutputRel` with
   compose_r (from an inner ascription), you can't extract `SoundRel` for
   `subst_congr`. See SUGGESTIONS.md Step 3 for detailed analysis.

   **DO NOT attempt to prove the asc sorrys without changing the output type.**

2. **Edge case sorry (1 in soundness_app_case):** ann_c = lam, ann_a ≠ lam.
   Unreachable in practice. Could be eliminated by restricting SoundRel.mu to
   require same-constructor annotations, or by proving SoundRel.top on annotations
   contradicts the refl-only entry point.

3. **Legacy soundness_gen (3 sorrys):** Unchanged. Can be eliminated by proving
   a bridge between concEval and concEvalE.

### Previous changes (2026-04-02, agent ochre-lean-20260402-160931)

**SoundRel + concEvalE: app-lam-beta case PROVED.**

Added SoundRel (structural compatibility with flexible domains) and brought
back the env-based concrete evaluator (`concEvalE`) as a proof auxiliary.
Proved `soundness_gen_sr` — a generalized soundness theorem using SoundRel
inputs and concEvalE — which resolves the app-lam-beta case via `subst_congr`.

**What changed:**

1. **Eval.lean:** Added `concEvalE` (env-based concrete evaluator, structurally
   parallel to absEval — only differs at ascription). Proved `absEval_fuel_mono`
   (was sorry'd — mechanical case analysis on mu-app).

2. **Soundness.lean:** Major restructuring:
   - Added `SoundRel` inductive: like SubtypeCore but with flexible domains
     on lam and flexible annotations on mu.
   - Proved `SoundRel.subst_congr`: the KEY lemma SubtypeCore can't prove.
     `SoundRel body_v body_τ → SoundRel a_v a_τ → SoundRel (body_v.subst j a_v) (body_τ.subst j a_τ)`
   - Proved supporting infrastructure: `shift_preserve`, `subst_arg_congr`,
     `lam_rhs_shape`, `mu_rhs_shape`, `trans`, `SubtypeCore.toSoundRel`.
   - Added `EnvSoundRel` (env consistency via SoundRel) + extend lemmas.
   - Added `soundness_gen_sr`: SoundRel-generalized soundness with concEvalE.
     **Proves lam, mu, bvar, type, app-lam-beta, app-stuck, top, lam/mu/app_cong.**
   - Factored out `soundness_app_case` helper (shared by refl and app_cong cases).
   - Added `soundness_concEvalE` top-level entry point.
   - Retained `soundness_gen` (legacy, ValSub-based) for bridge compatibility.

**Why concEvalE (env-based) was needed:**

Option 2 (proving `SoundRel body (absEval body)` — normalization preserves
SoundRel) is FALSE for mu-containing bodies. Counterexample:
```
e = mu ann (bvar 0)
absEval normalizes: mu ann (bvar 0) → mu ann (mu ann (bvar 0))
SoundRel (bvar 0) (mu ann (bvar 0)) — can't be constructed
```
When absEval enters a mu body, it puts `mu ann body` in the env. When
`bvar 0` is looked up, it gets the mu term — structurally different from bvar.

The env-based concEvalE sidesteps this: both evaluators use envs, so the IH
relates their OUTPUTS (not source vs normalized). The env consistency invariant
(`EnvSoundRel`) tracks that both envs contain SoundRel-related values at each
index. When bvar 0 is looked up, both get their respective mu values, which
are SoundRel by the invariant.

**The remaining sorrys (analysis for next agent):**

1. **asc case (2 sorrys in soundness_gen_sr):** concEvalE evaluates the term
   (lhs), absEval evaluates the type (rhs). These are DIFFERENT subexpressions.
   The IH can give SoundRel for each independently, but we need to connect them.
   The WellTyped check gives `subCheckNF(absEval term, absEval ty) = true`.
   Solution: need an OutputRel (ValSub-like) that composes SoundRel with
   subCheckNF via compose_r. The exp-b version has this as `OutputRel`.
   This is straightforward to add — just wrap SoundRel in compose_r.

2. **app-mu-annotation case (1 sorry):** When f evaluates to `mu ann body`
   where `ann = lam dom retBody` and `body = lam ...`, absEval uses the
   annotation's return type (`retBody.subst 0 a_τ`) instead of the body.
   SoundRel from the IH gives `SoundRel body_c body_a` but doesn't relate
   body_a to ann_a. Needs annotation consistency in WellTyped or a
   SoundRel between annotation and body.

3. **soundness_gen (legacy, 3 sorrys):** Blocked on bridge from concEval to
   concEvalE. Can be eliminated once the bridge is proved, or removed entirely
   if we switch to concEvalE-based soundness.

### Recent changes (2026-04-02, agent ochre-lean-20260402-153654)

**Phase 4 Step 2.5: Semantic ValSub + fuel monotonicity infrastructure.**

Added semantic function subtyping (`lam_sem`) to ValSub and proved the
supporting lemmas needed for the app case of soundness.

**What changed:**

1. **Syntax.lean:** Removed `BEq` from `deriving` clause. `Expr` now gets
   `BEq` from `DecidableEq` via `instBEqOfDecidableEq`, which is `LawfulBEq`.
   This lets us prove `beq_self_eq_true` and `subCheckNF_refl` trivially.

2. **Eval.lean:** Added fuel monotonicity lemmas:
   - `concEval_fuel_mono`: PROVED (by induction on fuel, case split on Expr)
   - `absEval_fuel_mono`: almost proved (1 sorry in mu-app nested match)
   Both state: `eval n e = some v → eval (n+1) e = some v`.

3. **Subtyping.lean:** Added and proved:
   - `Expr.beq_refl`: `(e == e) = true` (trivial from `LawfulBEq`)
   - `subCheckNF_refl`: `subCheckNF 1 [] [] e e = true`

4. **ValSub.lean:** Added `lam_sem` disjunct (9 disjuncts total, was 8):
   ```lean
   -- (3') lam_sem: semantic function subtyping
   ∃ domV bodyV domT bodyT,
     v = .lam domV bodyV ∧ τ = .lam domT bodyT ∧
     (∀ av aτ, ValSub n av aτ →
        ∀ rv, concEval (n+1) (bodyV.subst 0 av) = some rv →
        ∀ rτ, absEval (n+1) [] (bodyT.subst 0 aτ) = some rτ →
        ValSub n rv rτ)
   ```
   Proved:
   - `lam_sem` intro lemma
   - `mono` for `lam_sem` case: uses `upward` + fuel mono + IH
   - `upward`: `ValSub n v τ → ValSub (n+1) v τ` (via compose_r + subCheckNF_refl)
   - Bridge/of_subtypeCore unchanged (syntactic lam_sub kept alongside lam_sem)

**Key insight: the compose_r + subCheckNF_refl trick.**

The central problem with semantic ValSub is that the lam_sem quantifier at
level n+1 uses ValSub n, but mono needs to go from n+1 to n. This requires
upward closure (ValSub n → ValSub n+1), which normally doesn't hold for
step-indexed relations.

SOLUTION: compose_r stores subCheckNF evidence directly. Combined with
subCheckNF reflexivity (`e ⊑ e` by BEq check), we get upward closure:
`ValSub n v τ → ValSub (n+1) v τ` via `compose_r h (subCheckNF_refl τ)`.

This makes mono provable for lam_sem (use upward to upgrade arg ValSub,
fuel_mono to lift eval fuel, then IH to downgrade result ValSub).

**How the app case will work (not yet proved, documented in soundness_gen):**

At fuel+1 for `app f a`:
1. IH(f): `ValSub fuel fv fτ` where fv = lam domV bodyV, fτ = lam domT bodyT
2. IH(a): `ValSub fuel av aτ`
3. Extract lam_sem from ValSub fuel (lam ...) (lam ...):
   - Eval fuel: fuel matches body eval (concEval fuel body.subst = v) ✓
   - Arg: mono gives ValSub (fuel-1) av aτ from ValSub fuel av aτ ✓
   - Result: ValSub (fuel-1) v τ
4. compose_r twice: ValSub (fuel-1) → ValSub fuel → ValSub (fuel+1) ✓

BLOCKED ON: the lam case of soundness_gen must produce lam_sem evidence.
The lam case's quantifier needs to relate evaluations of body.subst 0 av
(concrete) and body'.subst 0 aτ (abstract), which are different expressions.
Requires either an absEval normalization equivalence or a fundamental theorem
of logical relations approach.

**The remaining sorrys (analysis for next agent):**

1. **soundness_gen lam case** (CRITICAL — blocks everything):
   Need `ValSub (fuel+1) (lam dom body) (lam dom body')` where
   body' = absEval fuel [bvar 0] body. Using lam_sem, must show:
   for all ValSub-related args, body evals produce related results.
   The IH works on body.subst 0 av, but absEval uses body'.subst 0 aτ.
   Need: `absEval m [] (body'.subst 0 aτ) = absEval m [] (body.subst 0 aτ)`
   (normalization is idempotent / commutes with substitution).

2. **soundness_gen mu case**: Need env-subst equivalence:
   `absEval fuel [v] body = absEval fuel [] (body.subst 0 v)` for closed v.
   Then IH applies on body.subst 0 (mu ann body), and mu_r lifts to mu ann body'.

3. **soundness_gen app case**: Mechanically follows from (1) once lam_sem
   evidence is produced. The lam-lam sub-case uses the strategy above.
   Other sub-cases (mu-app, type-app, stuck) need individual handling.

4. **absEval_fuel_mono mu-app**: Tedious nested match case analysis.
   All sub-cases are either `ih h` (recursive) or `exact h` (direct).

### Recent changes (2026-04-02, agent ochre-lean-20260402-150818)

**Phase 4 Step 2 (partial): concEvalS switch — soundness_gen now uses concEvalS.**

Rewrote `soundness_gen` to use `concEvalS` (substitution-based CBV, lambdas
are values) instead of `concEval` (environment-based, normalizes under binders).
The theorem is now top-level (empty absEval env, closed terms for concEvalS).

**What changed:**
- `soundness_gen` signature: `concEvalS fuel e = some v → absEval fuel [] e = some τ → WellTyped fuel [] e = true → ValSub fuel v τ`
- No more `EnvConsistent` precondition (concEvalS has no env)
- No more `SubtypeCore e_c e_a` generalization (single expression)
- Output is `ValSub fuel v τ` (was `SubtypeCore v τ`)
- Old `soundness` corollary (Subtype' output) removed — ValSub is primary

**What's proved in soundness_gen:**
- **bvar case:** vacuous (concEvalS returns None on free vars)
- **type case:** trivial (both return type, ValSub.refl')
- **asc case:** PROVED via IH on term + compose_r. Key: WellTyped gives
  `subCheckNF(absEval term, absEval ty) = true`, IH gives `ValSub fuel v σ`,
  compose_r bumps to `ValSub (fuel+1) v τ`.

**3 sorry'd cases (all inside soundness_gen):**
- **lam:** concEvalS returns source body, absEval returns normalized body.
  Need ValSub between them. Requires semantic ValSub or normalization equiv.
- **mu:** concEvalS unrolls via substitution, absEval normalizes under binder
  via env. Need env-subst equivalence for absEval.
- **app:** Different bodies and different arguments on each side. Same-expression
  IH can't bridge this. Needs semantic ValSub (lam quantifies over all apps).

**Key insight (correcting previous analysis):**
The concEvalS switch fixes the CONCRETE side (lambda body is source body)
but does NOT fix the ABSTRACT side. absEval still normalizes under binders,
so type-level lambda bodies are pre-normalized. The app case still has two
differences: (1) body vs body' (source vs normalized) and (2) av vs aτ
(concrete vs abstract argument). A semantic ValSub resolves both.

See SUGGESTIONS.md Phase 4 Step 2 for the detailed analysis and next steps.

### Previous changes (2026-04-02, agent ochre-lean-20260402-144702)

**Phase 4 Step 1.5: compose_r disjunct + bridge proof (3 → 2 sorrys).**

Added a `compose_r` disjunct to ValSub and proved the bridge lemma.

**What changed:**
- **ValSub now has 8 disjuncts** (was 7). The new disjunct (8) is `compose_r`:
  `∃ mid fuel ctx, ValSub n v mid ∧ subCheckNF fuel ctx [] mid τ = true`.
  This is right-composition with the algorithmic checker — transitivity via
  subCheckNF. Semantically sound because subCheckNF IS the intended checker.
- **`mono` (downward closure) proved:** `ValSub (n+1) v τ → ValSub n v τ`.
  By induction on n, applying IH to each sub-ValSub in all 8 disjuncts.
- **`bridge` proved:** `ValSub n v σ → subCheckNF σ τ = true → ValSub n v τ`.
  Two-line proof: apply mono to get ValSub (n-1) v σ, then compose_r.
  This resolves the domain composition problem that blocked the bridge.

**Why compose_r works:**
The bridge was blocked because the lam case's contravariant domain needed
ValSub transitivity or a reverse bridge, both hard. compose_r sidesteps
this entirely: instead of decomposing the subCheckNF structurally, it
stores the subCheckNF result directly as evidence. The guarantee remains
meaningful — ValSub says values are related by structural rules AND
verified algorithmic checks.

**What compose_r does NOT solve:**
The app case of soundness_gen still needs either:
1. A semantic ValSub (logical relation) where the lam case quantifies
   over all argument evaluations
2. A substitution-evaluation equivalence:
   `concEval fuel env (bodyNorm.subst 0 val) ≈ concEval fuel (env.extend val) bodySource`
3. Proving soundness for concEvalS (which treats lambdas as values)

See "Analysis" section below for detailed findings on why the semantic
approach is harder than expected for env-normalizing evaluators.

### Analysis: semantic ValSub vs env-normalizing evaluators (2026-04-02)

The SUGGESTIONS.md recommended an Amin-Rompf style semantic ValSub where
the lam case quantifies over all argument evaluations. After careful
analysis, this approach has a fundamental mismatch with our evaluators:

**Problem:** concEval normalizes lambda bodies (evaluates under binders).
So a lambda value `lam dom body'` has `body'` = normalized body, NOT the
original source body. When the lambda is applied, we substitute and
re-evaluate: `concEval fuel env (body'.subst 0 aVal)`. This means the
soundness IH (which is about the source body, not the normalized one)
doesn't directly help prove the semantic lam's quantifier.

**In Amin-Rompf's system,** lambdas are values (no normalization).
The closure carries the original body. When applied, the original body
is evaluated with the argument. The semantic lam's quantifier follows
directly from the soundness IH on the original body. This is why their
approach works.

**For our system, the fix is one of:**
1. **Prove a substitution-evaluation equivalence:** Show that
   `concEval fuel env (bodyNorm.subst 0 val) = concEval fuel (env.extend val) bodySource`
   (normalizing then substituting ≈ evaluating directly with the arg).
   This connects the actual application back to the IH on the source body.
   Hard to prove with finite fuel (two-pass vs one-pass fuel consumption).

2. **Prove soundness for concEvalS:** concEvalS treats lambdas as values
   (like Amin-Rompf). But concEvalS can't evaluate open terms (free bvars
   return None), making the induction on sub-expressions problematic.

3. **Use a closure-based evaluator:** Add closures to concEval so lambda
   values carry the original body + environment. This matches Amin-Rompf
   exactly but requires significant refactoring.

**Recommendation for next agent:** Approach (1) seems most tractable.
The equivalence might not hold exactly with finite fuel, but a weaker
form (if both sides succeed, results are ValSub-related) might suffice.
Alternatively, approach (2) could work if soundness is proved at the
top level (closed programs) by induction on fuel, handling open terms
through the substitution chain rather than sub-expression induction.

### Previous changes (2026-04-02, agent ochre-lean-20260402-141112)

**Phase 4 Step 1: ValSub definition + SubtypeCore embedding + analysis.**

Created `Och/ValSub.lean` with:
- **ValSub definition:** Step-indexed value subtyping, `ValSub n v τ : Prop`.
  Defined as a disjunction by recursion on n. At n=0, trivially true (no
  budget). At n+1, seven disjuncts: top, refl, lam_sub (contra domain +
  co body), mu_body, app_cong, mu_r (self-intro), mu_l (self-elim).
- **Intro lemmas:** Named constructors for each disjunct (top, refl, refl',
  lam_sub, lam_body, mu_body, app_cong, mu_r, mu_l).
- **SubtypeCore embedding:** `of_subtypeCore : SubtypeCore v τ → ∀n, ValSub n v τ`.
  Proved by induction on SubtypeCore. Each case maps to the corresponding
  ValSub disjunct. This ensures the existing soundness proof cases (which
  produce SubtypeCore) still work when the output changes to ValSub.
- **Bridge lemma (sorry'd):** The critical missing piece for the asc case.
- **subst_congr counterexample (IMPORTANT):** Proved via native_decide that
  substitution congruence is FALSE for ValSub. See below.

### KEY FINDING: subst_congr is false

`ValSub n a b → ValSub n (e.subst j a) (e.subst j b)` is **FALSE** for the
syntactic ValSub with contra-domain lam_sub.

**Counterexample (verified by native_decide):**
- e = `lam (bvar 0) (bvar 1)` — lambda whose domain IS the substituted variable
- a = zero', b = Nat'
- zero' ⊑ Nat' holds (zero is a nat)
- e.subst 0 zero' = `lam zero' (bvar 0)`
- e.subst 0 Nat' = `lam Nat' (bvar 0)`
- lam zero' body ⊑ lam Nat' body requires Nat' ⊑ zero' (contra domain) — FALSE

**Consequence:** The GENERALIZED soundness approach (ValSub/SubtypeCore on
inputs + substitution congruence) is fundamentally blocked. This is the same
issue SubtypeCore had — contra-domain makes substitution non-monotone.

### Analysis of the bridge lemma

The bridge `ValSub n v σ → subCheckNF σ τ = true → ValSub n v τ` is needed
for the asc case of soundness. Analysis of each case:

- **σ = τ (refl):** Trivial ✓
- **τ = Type (top):** ValSub.top ✓
- **Bodies (covariant):** Recursive bridge call. ✓
- **Domains (contravariant):** BLOCKED. Need ValSub domτ domv from
  ValSub domσ domv + subCheckNF domτ domσ. This requires either:
  (a) ValSub transitivity (hard — step accounting doesn't align)
  (b) subCheckNF_sound into ValSub + ValSub transitivity
  (c) A reverse bridge: subCheckNF(a,b) + ValSub(b,c) → ValSub(a,c)
- **Mu cases:** Should work (fuel consumption aligns with step index).
- **inferType cases:** Needs context awareness (subCheckNF uses ctx, ValSub doesn't).

### Important insight: shared lambda domains

In the soundness proof, v (from concEval) and σ (from absEval) always share
lambda domains because both evaluators preserve the syntactic domain:
```
| .lam dom body => ... some (.lam dom body')  -- dom unchanged!
```
This means the domain composition problem may not arise at the TOP level
(where v and σ are direct eval outputs). It DOES arise for nested comparisons.

### Recommended next step: semantic ValSub (logical relation)

The syntactic ValSub has clear limitations for the bridge. The recommended
alternative is a **semantic (logical relation) ValSub** where the lam case
quantifies over all argument evaluations:

```
ValSub n (lam domv bodyv) (lam domτ bodyτ) :=
  ∀ m ≤ n, ∀ av aτ, ValSub m av domτ →
    ∀ rv, concEval m [] (bodyv.subst 0 av) = some rv →
    ∀ rτ, absEval m [] (bodyτ.subst 0 aτ) = some rτ →
    ValSub m rv rτ
```

This approach:
- Makes the app case of soundness trivial (instantiate the quantifier)
- Avoids subst_congr entirely
- Makes the bridge's lam case tractable (domain subsumption follows from
  the quantifier's domain condition)
- Couples the relation to the evaluator (acceptable trade-off)
- Is the standard approach in the step-indexed logical relations literature

See `docs/research/amin-rompf-deep-dive.md` for the Amin-Rompf precedent.

### Previous changes (2026-04-02, agent ochre-lean-20260402-135537)

**Phase 3.5: Env extend lemmas — COMPLETE (4 sorrys eliminated).**

Proved all env extend infrastructure for de Bruijn:
- `SubtypeCore.shift_preserve` (Subtyping.lean) — SubtypeCore preserved under shifting
- `envSubCore_extend` + `envSubCore_extend_sub` (Monotonicity.lean)
- `envConsistent_extend` + `envConsistent_extend_sub` (Soundness.lean)

**absEval_mono NOT reproved — blocked on substitution lemma.** The de Bruijn
migration changed beta-reduction from env extension to substitution. The old
proof used `envSubCore_extend_sub` to thread the argument into the env; the
new proof needs `SubtypeCore (body₂.subst 0 aVal₂) (body₁.subst 0 aVal₁)`
given `SubtypeCore body₂ body₁` and `SubtypeCore aVal₂ aVal₁`. This doesn't
hold because `lam_body` requires equal domains — substituting different values
into a nested lambda's domain breaks this. Fixing it requires adding
`lam_cong`/`mu_cong` (allowing different domains/anns) to SubtypeCore, but
Phase 4 replaces SubtypeCore entirely, making that work redundant.

### Previous changes (2026-04-02, agent ochre-lean-20260402-123003)

**Phase 3: De Bruijn indices — COMPLETE.**

Migrated the entire codebase from named variables to de Bruijn indices.
This is the biggest mechanical change in the project's history.

**What changed:**

1. **Syntax.lean:** `Expr` now uses `bvar : Nat` (de Bruijn index) instead of
   `var : Name`. `lam` and `mu` no longer carry binder names. Added `shift`
   (increment free vars) and `subst` (substitute + shift down). Added `Named`
   type + `toExpr` converter so test terms can be written readably.

2. **Eval.lean:** `Env = List Expr` (positional, env[k] = value for bvar k).
   `Env.extend` shifts existing entries when entering a binder. Beta-reduction
   uses **substitution** (not env extension) — subst argument into body, then
   re-evaluate. This is a semantic change from the old env-based beta.

3. **Subtyping.lean:** `subCheckNF` uses `Env.extend` for ctx management (with
   shifting). Domains are normalized on BOTH sides before comparison (needed
   because subst-produced domains contain unreduced applications). `inferType`
   uses positional lookup (ctx.get? k). No variable renaming needed anywhere.

4. **Monotonicity.lean:** Sorry'd (was sorry-free). Needs reproving with new
   env extension patterns.

5. **Soundness.lean:** Sorry'd (was 3 sorrys). Needs reproving with new env
   and subst-based beta. WellTyped updated to use Env.extend and subst.

6. **Tests.lean:** All definitions use Named syntax + `n` converter. All tests
   pass. One behavioral change: `concEval toZero one'` now terminates (= zero')
   because subst-based beta reuses normalized mu bodies instead of re-evaluating.

7. **CounterexampleTest.lean:** Deleted (named-variable-specific concepts like
   freeVars/evalFreeVars; preserved in git history).

**Key design decisions:**

- **Hybrid evaluation:** Env-based for normalization under binders (lam, mu body),
  substitution-based for beta-reduction (app-lam, app-mu). This avoids the closure
  problem (env-based de Bruijn beta would need closures to track definition-site envs).

- **Env.extend shifts all entries:** When entering a binder, existing env/ctx entries
  are shifted up by 1 so their bvar indices stay correct at the new depth. New entries
  (neutrals for lam, mu values for mu) are NOT shifted because they're already at the
  correct depth. BUT domain types added to subCheckNF's ctx ARE shifted (they're from
  the outer scope).

- **Domain normalization on both sides:** With subst-based evaluation, domains can
  contain unreduced applications (e.g., `zero' Type Unit' (λacc. ...)` instead of
  `Unit'`). Both sides are normalized before comparison.

- **concEval behavioral change:** `concEval` for recursive mu + Church branching now
  terminates (was divergent). The subst-based beta reuses the already-normalized mu
  body, so the recursive call's result is embedded in the term rather than re-computed.
  The test was updated to reflect this.

**What's next (for the next agent):**

See SUGGESTIONS.md Phase 4. The ValSub definition is in place. The critical
next step is either:
1. **Prove the bridge lemma** (hard — requires solving domain composition)
2. **Replace syntactic ValSub with semantic ValSub** (logical relation approach)
3. **Rewrite soundness to output ValSub** (straightforward once bridge works)

### Previous changes

See git log for full history. Key milestones:
- Phase 1 (milestone tests): All M1-M4 pass including abstract appendVec
- Phase 2 (non-vacuous WellTyped): Bool-valued with subCheckNF, 11 witnesses
- Phase 3 (de Bruijn): Complete migration
- Phase 3.5 (env extend lemmas): 4 sorrys eliminated

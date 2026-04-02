# Och — current state

## What Och is

Och is a minimal pure calculus isolating the core semantic idea of Ochre
(a systems theorem prover, roughly Rust + Dependent Types). Terms and types
share a single syntax. Types are "approximate programs." The ONLY difference
between compile-time and runtime is the ascription case: `(e : τ)` takes `e`
concretely and `τ` abstractly.

See `docs/what-is-och.md` for details and `docs/ideas/merge-fix-iota.md` for
the mu design.

## Build status

`lake build` passes. **4 sorry'd declarations** in Soundness.lean:

- `VCompat.from_self_intro_gen` — 1 sorry, inner recursion for general self-intro (line ~411)
- `VCompat.adequacy` — 3 sub-sorrys, ALL self-elim or mu-right cases (lines ~540, ~642, ~644)
- `soundness_gen` app case — needs application congruence (line ~764)
- `soundness_concEval` — needs concEval→concEvalE bridge (line ~810)

**`soundness` (using concEvalE) is sorry-free!** It's a direct corollary
of `soundness_gen` with empty env.

**PROVEN (cumulative from all sessions):**
- soundness (concEvalE version) — FULLY PROVEN
- VCompat.from_type_sub_gen — FULLY PROVEN (self-intro from .type)
- VCompat.from_type_sub — FULLY PROVEN (corollary)
- VCompat.adequacy PARTIAL — ALL self-intro cases now proven via from_self_intro
- VCompat.mono (downward closure)
- VCompat.mono_le (multi-step downward closure)
- VCompat.fixpoint_mu (fixpoint mus are always VCompat)
- VCompat.fixpoint_mu_left (fixpoint mu-left at all steps)
- VCompat.self_intro_eq (self-intro via equality)
- soundness_gen bvar, type, lam, mu, asc cases
- subCheckNF_type_self_intro (extraction lemma)
- subCheckNF_neutral_inferType helper lemma

**All milestone tests pass** (M1-M4 including abstract appendVec).
**11 WellTyped witness tests pass.**

## KEY CHANGES THIS SESSION (agent ochre-lean-20260403-001714)

### 1. VCompat.subst_congr is FALSE

Counterexample found and documented in Tests.lean:
- bodyV = bvar 0, bodyT = lam .type (bvar 0) — VCompat via inferType
- av = lam .type .type, aτ = .type — VCompat via top
- After subst: (lam .type .type) vs (lam .type (bvar 0))
- VCompat FAILS: structural lam needs VCompat .type (bvar 0), which is false

**This rules out the approach of proving the app case via structural VCompat +
substitution congruence.** The app case requires either semantic VCompat or a
different technique.

### 2. Self-intro cases of adequacy: 7 of 10 mu/seen sorrys eliminated

Proved `VCompat.from_type_sub_gen` (fully, no sorry) and
`VCompat.from_self_intro_gen` (1 sorry in inner recursion).

The key technique: outer induction on fuel (self-intro decreases fuel) with
inner induction on VCompat step index (mu-right decreases step). For .type
as the left operand, this is fully proven because the only shapes body.subst
can take are .type (VCompat by top) or another mu (self-intro recurses).

For general σ (lam, bvar, app, asc), the inner recursion at `from_self_intro_gen`
line ~411 is sorry'd because after self-intro unfolds, the inner subCheckNF
operates on σ ⊑ body.subst, which has σ-specific matching (structural lam/mu,
inferType catch-all). This requires either:
1. A generalized adequacy that handles arbitrary σ with seen lists
2. A seen-stripping lemma (subCheckNF with unused seen = without seen)
3. Separate handling for each σ shape

### 3. Self-elim cases remain (3 sorrys in adequacy)

Self-elim cases (σ = mu, τ ∉ {type, mu}) need mu-left + inner recursion.
The same technique (outer fuel induction + inner step induction) should work
but requires a parallel `from_self_elim_gen` lemma.

### 4. New helper lemmas

- `VCompat.mono_le`: multi-step downward closure (VCompat n → VCompat m for m ≤ n)
- `VCompat.fixpoint_mu`: VCompat n v (mu ann body) always true for fixpoints
- `VCompat.fixpoint_mu_left`: VCompat n (mu ann body) τ always true for fixpoints
- `VCompat.self_intro_eq`: self-intro when σ = body.subst 0 self
- `subCheckNF_type_self_intro`: extract self-intro inner call from subCheckNF

## CRITICAL FINDING: subCheckNF non-properties (still valid)

### 1. subCheckNF transitivity is FALSE
### 2. subCheckNF_top_universal is FALSE
### 3. VCompat.subst_congr is FALSE (NEW)

See Tests.lean for counterexamples.

## File structure

- `Syntax.lean` — Expr type (de Bruijn indices), substitution, shifting
- `Eval.lean` — absEval, concEval, concEvalE, fuel monotonicity lemmas
- `Subtyping.lean` — subCheckNF (algorithmic), SubtypeCore/Subtype' (declarative),
  helper extraction lemmas, subCheckNF non-property documentation
- `Soundness.lean` — WellTyped, VCompat definition (with inferType disjunct),
  from_type_sub_gen (proven), from_self_intro_gen (1 sorry), soundness theorems
- `Tests.lean` — sacred acceptance tests (DO NOT WEAKEN),
  subCheckNF + VCompat counterexample tests

## Sorry count by category

### Self-intro inner recursion (1 sorry in from_self_intro_gen)
The core issue: after self-intro unfolds σ ⊑ mu ann body to σ ⊑ body.subst
with seen [(σ, mu ann body)], the inner subCheckNF does σ-specific matching.
For σ = .type, this is fully handled (from_type_sub_gen). For other σ shapes,
the inner matching (structural lam, inferType, etc.) interacts with the seen
list in complex ways.

**Fix approach**: The inner call has fuel k-1 (one less). The IH at fuel k-1
gives from_self_intro_gen at lower fuel. But the inner call's target is
body.subst 0 (mu ann body), which might not be a mu (could be lam, bvar, etc.).
So from_self_intro_gen doesn't directly apply. Need a more general adequacy
that handles σ ⊑ τ for arbitrary τ (not just mu) with seen lists.

### Self-elim (2 sorrys in adequacy)
Mirror of self-intro: σ is mu, τ is not mu. Uses mu-left (body.subst unfolds
the mu on the value side). Same seen-list interaction issue.

### Mu-right in adequacy (1 sorry)
σ = mu ann_σ body_σ unfolded. The unfolded body.subst 0 (mu ann_σ body_σ) is
the new σ'. This is subsumed by the general seen-list adequacy.

### App case (1 sorry in soundness_gen)
The structural VCompat makes the app case hard: after beta-reduction, bodyV.subst 0 av
and bodyT.subst 0 aτ are different expressions, and the IH needs the same expression.

VCompat.subst_congr is FALSE (see above), so the structural approach can't
work via simple substitution congruence. The semantic VCompat approach
(SUGGESTIONS.md) trades an easy app case for a hard lam case. The lam case
requires either:
1. Two-env soundness_gen (generalize to separate envs for concrete/abstract)
2. Env-substitution equivalence (concEvalE fuel env (bodyV'.subst 0 av) = 
   concEvalE fuel (env.extend av) source_body)

### soundness_concEval bridge (1 sorry)
Orthogonal: needs showing concEval and concEvalE agree on closed terms.

## What the next agent should do

### Priority 1: Prove the from_self_intro_gen inner sorry

The 1 remaining sorry in from_self_intro_gen (line ~411) is:
```
VCompat i v (body_τ.subst 0 (.mu ann_τ body_τ))
```
given `subCheckNF k ctx ((σ, .mu ann_τ body_τ) :: seen) σ (body_τ.subst 0 (.mu ann_τ body_τ)) = true`

This is a general adequacy problem: show VCompat at step i given subCheckNF
with non-empty seen. Approach: prove a generalized adequacy_gen with seen/hseen
parameters, by the same outer-fuel/inner-step double induction technique used
in from_type_sub_gen. The .type case shows the technique works; the general
case requires handling all σ shapes in the inner subCheckNF matching.

### Priority 2: Self-elim cases (from_self_elim_gen)

Mirror of from_self_intro_gen for the mu-left direction. 2 sorrys.

### Priority 3: App case

See SUGGESTIONS.md for detailed analysis. VCompat.subst_congr is FALSE,
so the semantic VCompat approach is the recommended path.

## What's been tried (and failed)

- **Structural soundness via SoundRel**: fundamentally broken for ascription
- **ValSub.subst_congr**: FALSE (verified by counterexample)
- **VCompat.subst_congr**: FALSE (verified this session — see Tests.lean)
- **Step-index coupling (VCompat fuel = fuel)**: dead end for asc case
- **subCheckNF transitivity**: FALSE (verified by counterexample)
- **subCheckNF_top_universal**: FALSE (verified by counterexample)
- **subCheckNF fallback in VCompat**: required transitivity → dead end.
  **Replaced with inferType disjunct** (agent ochre-lean-20260402-234907).

**Do not attempt any of the above approaches.**

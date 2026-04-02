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

## CRITICAL FINDING: VCompat.adequacy is FALSE (this session)

**Agent:** ochre-lean-20260403-011825

### The counterexample (proven constructively in Tests.lean §13)

```
v = mu type (app (bvar 0) type)     — non-fixpoint mu
σ = mu type (lam type (bvar 0))     — fixpoint mu
τ = lam type type                    — function type
```

- `VCompat 3 v σ = True` — structural mu: same ann, bodies VCompat via inferType
- `subCheckNF σ τ = True` — self-elim → fixpoint → lam structural → top
- `VCompat 3 v τ = False` — mu-left gives app(v,type) vs lam; inferType mu = none

**Proved:** `adequacy_cex_compat` and `adequacy_cex_incompat` in Tests.lean.

### What this means

The **3 sorry'd cases in adequacy** (lines 540, 642, 644) and the **1 sorry
in from_self_intro_gen** (line 411) are all **UNPROVABLE** — not just hard.
The structural mu disjunct in VCompat allows two mus with compatible bodies
but incompatible self-substitutions, which self-elim exposes.

The `soundness` theorem depends (transitively via sorry) on adequacy, so the
current proof chain is UNSOUND. However, soundness itself might still be TRUE
— the VCompat definition just needs to change to make adequacy provable.

### Root cause

structural mu VCompat + self-elim in subCheckNF = VCompat.subst_congr,
which is FALSE (also proven in Tests.lean §11.6).

## What the next agent MUST do

### Priority 1: Fix the VCompat definition

The structural mu disjunct must change. Three options (see DECISION-LOG.md):

**Option A (recommended): "Unfolded structural mu"**
Replace:
```lean
∨ (∃ annV annT bodyV bodyT,
    v = .mu annV bodyV ∧ τ = .mu annT bodyT ∧
    VCompat n bodyV bodyT)
```
With:
```lean
∨ (∃ annV annT bodyV bodyT,
    v = .mu annV bodyV ∧ τ = .mu annT bodyT ∧
    VCompat n (bodyV.subst 0 (.mu annV bodyV)) (bodyT.subst 0 (.mu annT bodyT)))
```

This makes the adequacy self-elim cases work because the VCompat already
talks about the unfolded forms. The challenge moves to soundness_gen's mu
case, which currently gets VCompat for raw bodies from the IH, not unfolded
forms. An env-substitution equivalence lemma may be needed.

**Option B: Remove structural mu, use mu-right/mu-left only**
This avoids the problem but makes soundness_gen's mu case much harder.

**Option C: Semantic VCompat (long-term)**
Define mu compatibility via evaluation rather than structure. This is the
right long-term answer but requires a major refactor.

### After fixing VCompat

1. Re-prove VCompat.mono (should be straightforward for unfolded variant)
2. Re-prove soundness_gen mu case with the new definition
3. Re-prove adequacy for the self-elim cases
4. Check that all existing tests still pass

## PROVEN (cumulative from all sessions)

- soundness (concEvalE version) — FULLY PROVEN (depends on sorry'd adequacy)
- VCompat.from_type_sub_gen — FULLY PROVEN (self-intro from .type)
- VCompat.from_type_sub — FULLY PROVEN (corollary)
- VCompat.adequacy PARTIAL — self-intro cases done, SELF-ELIM UNPROVABLE
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

## CRITICAL FINDINGS: false properties

### 1. VCompat.adequacy is FALSE (NEW — this session)
Counterexample and constructive proof in Tests.lean §13. See above.

### 2. subCheckNF transitivity is FALSE
Counterexample in Tests.lean §11.5.

### 3. subCheckNF_top_universal is FALSE
Counterexample in Tests.lean §11.5.

### 4. VCompat.subst_congr is FALSE
Counterexample in Tests.lean §11.6.

## File structure

- `Syntax.lean` — Expr type (de Bruijn indices), substitution, shifting
- `Eval.lean` — absEval, concEval, concEvalE, fuel monotonicity lemmas
- `Subtyping.lean` — subCheckNF (algorithmic), SubtypeCore/Subtype' (declarative),
  helper extraction lemmas, subCheckNF non-property documentation
- `Soundness.lean` — WellTyped, VCompat definition (with inferType disjunct),
  from_type_sub_gen (proven), from_self_intro_gen (1 sorry), soundness theorems
- `Tests.lean` — sacred acceptance tests (DO NOT WEAKEN),
  subCheckNF + VCompat counterexample tests, adequacy counterexample (§13)

## Sorry count by category

### UNPROVABLE with current VCompat (4 sorrys):
- `VCompat.adequacy` lines 540, 642, 644 — structural mu + self-elim = false
- `VCompat.from_self_intro_gen` line 411 — depends on adequacy-with-seen

### App case (1 sorry in soundness_gen):
Still requires semantic VCompat or substitution congruence. Orthogonal to
the adequacy fix (but the eventual semantic VCompat refactor would fix both).

### soundness_concEval bridge (1 sorry):
Orthogonal. Needs concEval → concEvalE equivalence.

## What's been tried (and failed)

- **Structural soundness via SoundRel**: fundamentally broken for ascription
- **ValSub.subst_congr**: FALSE (verified by counterexample)
- **VCompat.subst_congr**: FALSE (verified by counterexample)
- **Step-index coupling (VCompat fuel = fuel)**: dead end for asc case
- **subCheckNF transitivity**: FALSE (verified by counterexample)
- **subCheckNF_top_universal**: FALSE (verified by counterexample)
- **subCheckNF fallback in VCompat**: required transitivity → dead end
- **VCompat.adequacy with structural mu**: FALSE (this session)

**Do not attempt any of the above approaches.**

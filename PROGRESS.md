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

`lake build` passes. **3 sorry'd declarations** in Soundness.lean:

- `VCompat.adequacy` — partially proven (5 sub-sorrys, see below)
- `soundness_gen` app case — needs application congruence (line ~349)
- `soundness` — needs concEval→concEvalE bridge (line ~449)

**PROVEN (cumulative from all sessions):**
- VCompat.adequacy PARTIAL — 9 of 14 case combinations proven
- VCompat.mono (downward closure)
- soundness_gen bvar, type, lam, mu, asc cases
- Decoupled VCompat step index from fuel

**All milestone tests pass** (M1-M4 including abstract appendVec).
**11 WellTyped witness tests pass.**

## CRITICAL FINDING: subCheckNF non-properties

**Agent ochre-lean-20260402-230008 discovered two false proof strategies.**

### 1. subCheckNF transitivity is FALSE

Counterexample (verified by `native_decide` in Tests.lean):
- a = `.type`
- b = `mu .type (bvar 0)` (fixpoint: unfolds to itself)
- c = `lam .type (bvar 0)` (identity function type)

```
subCheckNF a b = true    (self-intro → seen hit)
subCheckNF b c = true    (self-elim → seen hit)
subCheckNF a c = false   (.type vs lam → inferType .type = none → false)
```

**Implication:** The adequacy fallback case (Case 5) CANNOT be solved via
subCheckNF transitivity as previously suggested in SUGGESTIONS.md.

### 2. subCheckNF_top_universal is FALSE

`.type ⊑ τ` does NOT imply `v ⊑ τ` for all `v`.

Counterexample (verified by `native_decide` in Tests.lean):
```
subCheckNF .type (mu .type (bvar 0)) = true
subCheckNF (mu .type (lam .type (bvar 0))) (mu .type (bvar 0)) = false
```

**Root cause:** When `v` is a `.mu`, subCheckNF takes the structural
`(mu, mu)` branch instead of self-intro. The structural branch checks
bodies, which may fail even when self-intro would succeed.

**Implication:** Adequacy Case 1 (σ = .type, τ = mu) CANNOT be solved by
constructing a `subCheckNF v τ` witness from `subCheckNF .type τ`.

### What this means for the proof

The subCheckNF fallback disjunct of VCompat creates requirements that
subCheckNF cannot satisfy:

1. **Case 5 (fallback input):** Needs `subCheckNF v σ ∧ subCheckNF σ τ →
   subCheckNF v τ` — FALSE (transitivity counterexample).

2. **Cases 1-2 (σ = .type or lam, τ = mu):** Cannot use `subCheckNF v τ`
   as a VCompat witness because subCheckNF_top_universal is FALSE.

**The subCheckNF fallback in VCompat may need to be replaced** with an
inferType-aware disjunct. See "Recommended revised approach" below.

## File structure

- `Syntax.lean` — Expr type (de Bruijn indices), substitution, shifting
- `Eval.lean` — absEval, concEval, concEvalE, fuel monotonicity lemmas
- `Subtyping.lean` — subCheckNF (algorithmic), SubtypeCore/Subtype' (declarative),
  helper extraction lemmas, **subCheckNF non-property documentation**
- `Soundness.lean` — WellTyped, VCompat definition, soundness theorems
- `Tests.lean` — sacred acceptance tests (DO NOT WEAKEN),
  **subCheckNF counterexample tests**

## Sorry'd sub-cases in adequacy

All 5 involve mu/seen interaction or the now-known-FALSE transitivity:

1. σ = .type, τ = mu — can't use subCheckNF fallback (top_universal FALSE)
2. Structural lam, τ = mu — similar issue
3. Structural mu, τ ∉ {.type, .mu} — self-elim with seen list
4. Mu right (σ = mu, unfold right) — all subcases
5. subCheckNF fallback — needs transitivity (PROVED FALSE)

## Recommended revised approach

### Option A: Replace the subCheckNF fallback with an inferType disjunct

Replace VCompat's 7th disjunct:
```lean
-- Current (problematic):
∨ (∃ fuel ctx, subCheckNF fuel ctx [] v τ = true)

-- Proposed:
∨ (∃ ctx ty, inferType ctx v = some ty ∧ VCompat n ty τ)
```

**Why this works:** The inferType disjunct has a step-index decrease
(VCompat n at step n vs the outer VCompat (n+1)). In adequacy:
- Input: `inferType ctx v = some ty ∧ VCompat m ty σ`
- Hypothesis: `subCheckNF σ τ = true`
- Apply IH on `ty`: `VCompat m ty σ → subCheckNF σ τ → VCompat m ty τ`
- Output: `inferType ctx v = some ty ∧ VCompat m ty τ`

No transitivity needed! The inferType witness is preserved, only the
inner VCompat changes.

**What changes:**
1. VCompat definition: replace fallback with inferType disjunct
2. VCompat.mono: straightforward (apply mono to inner VCompat)
3. soundness_gen: current proofs may need adjustment (bvar/refl case
   doesn't need the fallback; asc case via adequacy)
4. adequacy: fallback case replaced by inferType case (cleaner)
5. The refl case (v = σ) in adequacy currently uses the fallback.
   With the new disjunct, it would need to decompose subCheckNF
   structurally for the inferType sub-cases.

**Risk:** The refl case of adequacy becomes harder (must decompose
subCheckNF for neutral terms instead of using the fallback shortcut).
But this is a well-defined task, not a dead end.

### Option B: Generalized adequacy with seen-aware VCompat

Keep the current VCompat but generalize adequacy to track seen lists.
This was the approach suggested by previous agents but is harder due
to the coinduction/induction tension. The new counterexamples don't
directly affect this approach (it doesn't use transitivity), but the
mu/seen cases remain difficult.

### Option C: Keep current VCompat, accept sorry on Case 5

The fallback case (Case 5) of adequacy is only reachable through nested
ascriptions where the inner adequacy produces a fallback. In practice,
this might not arise for the milestone programs. We could:
1. Sorry Case 5
2. Verify the other 4 mu/seen cases using different techniques
3. Test non-vacuity for the milestone programs despite the sorry

This is pragmatic but leaves a known gap.

## What the next agent should do

### Priority 1: Decide on the approach

Read the analysis above and decide which option (A, B, or C) to pursue.
Option A (inferType disjunct) is recommended as the cleanest fix for the
fundamental issue.

### Priority 2: If Option A — implement the VCompat change

1. Change VCompat's 7th disjunct from `subCheckNF` to `inferType`
2. Re-prove VCompat.mono (should be straightforward)
3. Fix soundness_gen cases that relied on the fallback
4. Re-prove adequacy with the new disjunct

### Priority 3: App case or bridge

The app case (soundness_gen) and concEval→concEvalE bridge remain
separate concerns that need work regardless of the adequacy approach.

## What's been tried (and failed)

- **Structural soundness via SoundRel**: fundamentally broken for ascription
  (different constructors on concrete vs abstract sides).
- **ValSub.subst_congr**: FALSE (verified by counterexample).
- **Step-index coupling (VCompat fuel = fuel)**: dead end for asc case.
  Fixed by decoupling step index from fuel.
- **subCheckNF transitivity**: FALSE (verified by counterexample).
  Agent ochre-lean-20260402-230008.
- **subCheckNF_top_universal (.type ⊑ τ → v ⊑ τ)**: FALSE (verified by
  counterexample). Agent ochre-lean-20260402-230008.

**Do not attempt any of the above approaches.**

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

- `VCompat.adequacy` — 10 sub-sorrys, ALL about mu/seen interaction (line ~236)
- `soundness_gen` app case — needs application congruence (line ~481)
- `soundness_concEval` — needs concEval→concEvalE bridge (line ~594)

**`soundness` (using concEvalE) is now sorry-free!** It's a direct corollary
of `soundness_gen` with empty env.

**PROVEN (cumulative from all sessions):**
- soundness (concEvalE version) — FULLY PROVEN
- VCompat.adequacy PARTIAL — inferType case + all non-mu cases proven
- VCompat.mono (downward closure)
- soundness_gen bvar, type, lam, mu, asc cases
- Decoupled VCompat step index from fuel
- subCheckNF_neutral_inferType helper lemma

**All milestone tests pass** (M1-M4 including abstract appendVec).
**11 WellTyped witness tests pass.**

## KEY CHANGE: VCompat inferType disjunct (replacing subCheckNF fallback)

### What changed

VCompat's 7th disjunct was changed from:
```lean
∨ (∃ fuel ctx, subCheckNF fuel ctx [] v τ = true)
```
to:
```lean
∨ (∃ ctx ty, inferType ctx v = some ty ∧ VCompat n ty τ)
```

### Why

The old subCheckNF fallback required **transitivity** of subCheckNF in the
adequacy proof's fallback case (Case 5: subCheckNF v σ ∧ subCheckNF σ τ →
subCheckNF v τ). But subCheckNF transitivity is **FALSE** (counterexample
verified in Tests.lean). This was a dead end — no amount of effort could
prove the old Case 5.

### How the new disjunct works

The inferType disjunct has a step-index decrease: VCompat n (inner) vs
VCompat (n+1) (outer). In adequacy:

- **Input**: `inferType ctx v = some ty ∧ VCompat m ty σ`
- **Hypothesis**: `subCheckNF σ τ = true`
- **IH at step m**: `VCompat m ty σ → subCheckNF σ τ → VCompat m ty τ`
- **Output**: `inferType ctx v = some ty ∧ VCompat m ty τ`

No transitivity needed! The inferType witness is preserved, only the inner
VCompat changes. The IH handles the composition.

### Impact on other proofs

- **VCompat.mono**: trivial (apply mono to inner VCompat) ✓
- **soundness_gen**: unchanged (no case relied on the old fallback) ✓
- **adequacy refl case**: previously one line (put subCheckNF into fallback).
  Now needs case-splitting on v's shape. Proved for lam/mu (structural via IH
  on bodies), bvar/app (inferType extraction via helper lemma), asc
  (contradiction: inferType returns none). The mu sub-cases (self-intro) are
  sorry'd — same mu/seen issue as other cases.

### Net effect

- **GAINED**: Old Case 5 (fallback → fallback) was DEAD END → now PROVED
- **GAINED**: Old Case 7 (inferType) composes cleanly via IH
- **TRADED**: Old refl (1 line) → new refl (case-split, mostly proved, mu sorry'd)
- **ALL remaining sorrys are mu/seen interaction** — one fix would solve all

## CRITICAL FINDING: subCheckNF non-properties

(From previous agent ochre-lean-20260402-230008, still valid.)

### 1. subCheckNF transitivity is FALSE

Counterexample (verified by `native_decide` in Tests.lean):
- a = `.type`, b = `mu .type (bvar 0)`, c = `lam .type (bvar 0)`

### 2. subCheckNF_top_universal is FALSE

`.type ⊑ τ` does NOT imply `v ⊑ τ` for all `v`.

See Tests.lean for verified counterexamples.

## File structure

- `Syntax.lean` — Expr type (de Bruijn indices), substitution, shifting
- `Eval.lean` — absEval, concEval, concEvalE, fuel monotonicity lemmas
- `Subtyping.lean` — subCheckNF (algorithmic), SubtypeCore/Subtype' (declarative),
  helper extraction lemmas, **subCheckNF_neutral_inferType** (new),
  subCheckNF non-property documentation
- `Soundness.lean` — WellTyped, VCompat definition (with inferType disjunct),
  soundness theorems
- `Tests.lean` — sacred acceptance tests (DO NOT WEAKEN),
  subCheckNF counterexample tests

## Sorry'd sub-cases in adequacy (10 total, all mu/seen)

All involve subCheckNF's self-intro or self-elim with the seen list, which
uses coinduction while VCompat uses induction (step index). The adequacy
IH needs empty seen, but self-intro/elim recurses with non-empty seen.

### Self-intro cases (σ or v ⊑ mu ann body → add to seen):
1. Case 1: σ = .type, τ = mu (line ~259)
2. Refl: v = .type, τ = mu (line ~276)
3. Refl: v = lam, τ = mu (line ~303)
4. Refl: v = bvar, τ = mu (line ~341)
5. Refl: v = app, τ = mu (line ~360)
6. Refl: v = asc, τ = mu (line ~377)
7. Case 3: structural lam, τ = mu (line ~406)

### Self-elim cases (mu ann body ⊑ τ → add to seen):
8. Refl: v = mu, τ ∉ {type, mu} (line ~332)
9. Case 4: structural mu, τ ∉ {type, mu} (line ~432)

### Both self-intro and self-elim:
10. Case 5: mu right, σ = mu (line ~434)

## What the next agent should do

### Priority 1: Prove mu/seen cases of adequacy

All 10 remaining sorrys have the same root cause: bridging subCheckNF's
coinductive seen list with VCompat's inductive step index.

**Approach A: Generalized adequacy with seen-aware hypothesis**

```lean
theorem VCompat.adequacy_gen {n fuel : Nat} {v σ τ : Expr} {ctx : List Expr}
    {seen : List (Expr × Expr)}
    (hv : VCompat n v σ)
    (hcheck : subCheckNF fuel ctx seen σ τ = true)
    (hseen : ∀ σ' τ', (σ', τ') ∈ seen → VCompat n v σ' → VCompat n v τ')
    : VCompat n v τ
```

The key insight for discharging hseen: when self-intro adds (σ, mu ann body)
to seen, we need VCompat n v σ → VCompat n v (mu ann body). Use mu-right
unfolding: VCompat (n-1) v (body.subst 0 (mu ann body)). Then apply the IH
at step (n-1). The mu-right costs one step of n, and the IH on n gives
adequacy at the lower step level. **The step decrease from mu-right pays
for the seen entry.**

This approach requires well-founded induction on (n, fuel) or double
induction, and careful interaction between the step index decrease and
the fuel decrease from subCheckNF's recursion.

**Approach B: Prove subCheckNF seen-elimination**

Show that if `subCheckNF fuel ctx seen a b = true` and all seen entries are
independently verifiable (with more fuel), then `subCheckNF fuel' ctx [] a b
= true`. This would let us strip the seen list and use the basic IH.

**Risk**: The seen list breaks infinite cycles that would otherwise diverge.
Stripping it may require unbounded additional fuel.

### Priority 2: App case of soundness_gen

The app case needs "application congruence": VCompat through substitution +
evaluation. After beta-reduction, the two sides have different expressions
(bodyV.subst 0 a_v vs bodyT.subst 0 a_τ). The soundness_gen IH needs the
same expression.

See SUGGESTIONS.md for detailed analysis of approaches.

### Priority 3: concEval→concEvalE bridge

`soundness_concEval` needs showing that concEval results are VCompat with
concEvalE results. The main difference: concEval doesn't normalize under
lambda binders (lambdas are values), while concEvalE does. For non-lambda
results they should agree; for lambda results, the bodies differ by
normalization.

## What's been tried (and failed)

- **Structural soundness via SoundRel**: fundamentally broken for ascription
- **ValSub.subst_congr**: FALSE (verified by counterexample)
- **Step-index coupling (VCompat fuel = fuel)**: dead end for asc case
- **subCheckNF transitivity**: FALSE (verified by counterexample)
- **subCheckNF_top_universal**: FALSE (verified by counterexample)
- **subCheckNF fallback in VCompat**: required transitivity → dead end.
  **Replaced with inferType disjunct** (agent ochre-lean-20260402-234907).

**Do not attempt any of the above approaches.**

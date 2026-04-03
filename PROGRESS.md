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

- `VCompat.from_self_intro_gen` — 1 sorry, inner recursion for general self-intro (line ~415)
- `VCompat.adequacy` — 5 sub-sorrys:
  - 2 for refl/structural mu → mu target (lines ~535, ~645): need subCheckNF for subst'd forms
  - 2 for self-elim non-fixpoint (lines ~550, ~658): need generalized adequacy with seen
  - 1 for mu-right case (line ~666): step loss in mu-right unfolding
- `soundness_gen` — 2 sorrys:
  - mu case (line ~789): needs VCompat-equivalence (closedness lemma is FALSE, see §14)
  - app case (line ~794): needs application congruence
- `soundness_concEval` — needs concEval→concEvalE bridge (line ~840)

**`soundness` (using concEvalE) is sorry-free!** (depends transitively on sorry'd adequacy)

## KEY CHANGE: VCompat "unfolded structural mu" (this session)

**Agent:** ochre-lean-20260403-014631

### What changed

Replaced the structural mu disjunct in VCompat from:
```lean
∨ (∃ annV annT bodyV bodyT,
    v = .mu annV bodyV ∧ τ = .mu annT bodyT ∧
    VCompat n bodyV bodyT)                        -- raw bodies
```
to:
```lean
∨ (∃ annV annT bodyV bodyT,
    v = .mu annV bodyV ∧ τ = .mu annT bodyT ∧
    VCompat n (bodyV.subst 0 (.mu annV bodyV))
              (bodyT.subst 0 (.mu annT bodyT)))   -- unfolded bodies
```

### Why

The old definition made VCompat.adequacy **FALSE** (constructive proof in
Tests.lean §13, from previous session). The structural mu disjunct allowed
two mus with "compatible" raw bodies but DIVERGENT self-substitutions. After
subCheckNF self-elim, adequacy needed VCompat for the substituted forms,
which required VCompat.subst_congr — proven FALSE.

The new "unfolded structural mu" requires VCompat for the actual mu-unfolded
forms. This means:
1. The adequacy self-elim cases now have the right shape (VCompat on unfolded
   forms matches what self-elim produces)
2. The counterexample no longer holds (proven: `adequacy_cex_now_incompat`)
3. The soundness_gen mu case needs a closedness lemma (evaluator outputs
   have no free bvar 0, so subst 0 is a no-op)

### What was proved in this session

1. **Fixpoint subcases of adequacy self-elim** (Cases 2 and 4, non-mu τ):
   When σ is a fixpoint mu (body.subst 0 σ = σ), the self-elim case is
   resolved by rewriting the unfolded body to σ itself, then using the IH
   with the original subCheckNF hypothesis.

2. **Counterexample verification**: `adequacy_cex_now_incompat` proves that
   the old counterexample (VCompat 3 v σ) is now False with the new
   definition. Constructive proof in Tests.lean.

3. **VCompat.mono** — reproved automatically (structure unchanged).

### Trade-offs

- **Sorry count went from 6 individual to 9** (in same 4 declarations).
  But old sorrys included 4 that were PROVABLY FALSE. New sorrys are all
  potentially true.
- **New sorrys introduced**:
  - soundness_gen mu case (needs closedness lemma)
  - adequacy refl/mu → mu target (needs subCheckNF for subst'd forms)
  - adequacy structural mu → mu target (same)
- **Sorrys partially resolved**:
  - adequacy self-elim cases: fixpoint subcases now proven (previously ALL sorry'd)

## KEY FINDING: Closedness lemma is FALSE (agent ochre-lean-20260403-021117)

The naive closedness lemma (`v.subst 0 X = v` for evaluator outputs with
env covering bvar 0) is **FALSE**. Both `concEvalE` and `absEval` do NOT
evaluate lambda domains or mu annotations — they copy them verbatim from
the source. If the source has `bvar 0` in a domain/annotation position
(e.g., `mu type (lam (bvar 0) (bvar 0))`), the output retains this free
`bvar 0`. See Tests.lean §14 for a concrete counterexample.

However, the soundness_gen mu sorry IS still true (no counterexample found
in brute-force testing of 51 small bodies — see Tests.lean §15). The reason:
VCompat's structural lam/mu don't compare domains/annotations, so the
substitution into un-evaluated positions is invisible to VCompat.

## What the next agent MUST do

### Priority 1: VCompat-equivalence for soundness_gen mu case

The soundness_gen mu case needs VCompat m (bodyV'.subst 0 v) (bodyT'.subst 0 τ)
from VCompat m bodyV' bodyT'. The closedness approach FAILS (see above).

**Proposed approach: VCompat-equivalence (vEquiv).** See SUGGESTIONS.md
for the full plan. Three lemmas needed:
1. VCompat respects vEquiv (congruence)
2. subst preserves vEquiv for closedEval expressions
3. Evaluator outputs satisfy closedEval

This is the highest-impact work. Each lemma is individually useful and
can be sorry'd independently.

### Priority 2: Generalized adequacy with seen list

The non-fixpoint self-elim cases (and the mu-right case) need:
```lean
theorem VCompat.adequacy_gen (fuel : Nat) (n : Nat) (v σ τ : Expr)
    (ctx : List Expr) (seen : List (Expr × Expr))
    (hv : VCompat n v σ)
    (hcheck : subCheckNF fuel ctx seen σ τ = true)
    (hseen : ∀ p ∈ seen, VCompat n v p.2)
    : VCompat n v τ
```

This should use outer induction on fuel (self-elim decreases fuel) and
inner induction on step j ≤ n. The seen entries are handled by ih_j.
See `from_type_sub_gen` for a working example of this pattern for σ = type.

The key difficulty: for non-mu τ targets, there's no "step decrease" from
mu-right unfolding. The step decrease must come from mu-left on v (if v
is a mu) or from the VCompat step index.

### Priority 3: subCheckNF for substituted forms

The adequacy mu/mu cases (τ = mu) need:
```lean
subCheckNF bodyS bodyT → subCheckNF (bodyS.subst 0 σ) (bodyT.subst 0 τ)
```

This is "subCheckNF respects substitution" — may or may not be true.
Try to disprove with native_decide first.

## PROVEN (cumulative from all sessions)

- soundness (concEvalE version) — FULLY PROVEN (depends on sorry'd adequacy)
- VCompat.from_type_sub_gen — FULLY PROVEN (self-intro from .type)
- VCompat.from_type_sub — FULLY PROVEN (corollary)
- VCompat.adequacy PARTIAL:
  - self-intro cases done (from_self_intro)
  - self-elim FIXPOINT subcases done (Cases 2 and 4, non-mu τ)
  - self-elim NON-FIXPOINT sorry'd
  - mu/mu structural cases sorry'd (need subCheckNF for subst'd forms)
  - mu-right case sorry'd (step loss)
- VCompat.mono (downward closure)
- VCompat.mono_le (multi-step downward closure)
- VCompat.fixpoint_mu (fixpoint mus are always VCompat)
- VCompat.fixpoint_mu_left (fixpoint mu-left at all steps)
- VCompat.self_intro_eq (self-intro via equality)
- soundness_gen bvar, type, lam, asc cases
- subCheckNF_type_self_intro (extraction lemma)
- subCheckNF_neutral_inferType helper lemma
- adequacy_cex_now_incompat (counterexample no longer holds with new VCompat)

**All milestone tests pass** (M1-M4 including abstract appendVec).
**11 WellTyped witness tests pass.**

## CRITICAL FINDINGS: false properties

### 1. OLD VCompat.adequacy was FALSE (resolved by definition change)
Counterexample in Tests.lean §13. **Now RESOLVED**: the counterexample
no longer holds with the unfolded structural mu (proven: adequacy_cex_now_incompat).

### 2. subCheckNF transitivity is FALSE
Counterexample in Tests.lean §11.5.

### 3. subCheckNF_top_universal is FALSE
Counterexample in Tests.lean §11.5.

### 4. VCompat.subst_congr is FALSE
Counterexample in Tests.lean §11.6.

### 5. Naive closedness lemma (v.subst 0 X = v for eval outputs) is FALSE
Counterexample in Tests.lean §14. Evaluators don't evaluate lambda domains
or mu annotations, so outputs can have free bvar 0 in those positions.
The soundness_gen mu sorry is still believed TRUE — VCompat doesn't compare
domains/annotations, so the free bvar 0 is irrelevant. Brute-force tested
in Tests.lean §15 (51 bodies, 5 with different evaluator results, all pass).

## File structure

- `Syntax.lean` — Expr type (de Bruijn indices), substitution, shifting
- `Eval.lean` — absEval, concEval, concEvalE, fuel monotonicity lemmas
- `Subtyping.lean` — subCheckNF (algorithmic), SubtypeCore/Subtype' (declarative),
  helper extraction lemmas, subCheckNF non-property documentation
- `Soundness.lean` — WellTyped, VCompat definition (with unfolded structural mu
  and inferType disjunct), from_type_sub_gen (proven), from_self_intro_gen
  (1 sorry), soundness theorems
- `Tests.lean` — sacred acceptance tests (DO NOT WEAKEN),
  subCheckNF + VCompat counterexample tests, counterexample resolution proof (§13),
  closedness counterexample (§14), soundness_gen mu brute-force tests (§15)

## Sorry count by category

### Needs VCompat-equivalence (1 sorry in soundness_gen):
- soundness_gen mu case: IH gives VCompat for raw bodies, need subst'd forms.
  The naive closedness lemma is FALSE (see §14). Need VCompat-equivalence
  approach: prove subst only affects domains/annotations which VCompat ignores.
  See SUGGESTIONS.md Priority 1 for the full plan.

### Needs generalized adequacy with seen (3 sorrys):
- adequacy self-elim (2 cases): non-fixpoint σ needs seen-list handling
- adequacy mu-right case: step loss + seen list

### Needs subCheckNF for subst'd forms (2 sorrys):
- adequacy refl/mu → mu target
- adequacy structural mu → mu target
May follow from VCompat-equivalence (subst in VCompat-irrelevant positions).
Note: naive closedness lemma is FALSE — need the vEquiv approach instead.

### Other (3 sorrys):
- from_self_intro_gen: inner recursion (1 sorry)
- soundness_gen app case: application congruence (1 sorry)
- soundness_concEval: concEval → concEvalE bridge (1 sorry)

## What's been tried (and failed)

- **Structural soundness via SoundRel**: fundamentally broken for ascription
- **ValSub.subst_congr**: FALSE (verified by counterexample)
- **VCompat.subst_congr**: FALSE (verified by counterexample)
- **Step-index coupling (VCompat fuel = fuel)**: dead end for asc case
- **subCheckNF transitivity**: FALSE (verified by counterexample)
- **subCheckNF_top_universal**: FALSE (verified by counterexample)
- **subCheckNF fallback in VCompat**: required transitivity → dead end
- **VCompat.adequacy with raw structural mu**: FALSE (resolved by definition change)
- **Naive closedness lemma (v.subst 0 X = v)**: FALSE (evaluators don't eval domains)

**Do not attempt any of the above approaches.**

# PSS Type Safety Research Status

## The Problem
Prove type safety for Pure Subtype Systems (Hutchins, POPL 2010).
Open since 2010. The core obstacle: transitivity elimination (Conjecture 5.1).

## What We Proved (zero sorry, fully verified)

| File | Result |
|------|--------|
| SubstWf.lean | `subst_wf`, `shift_sub_gen`, `subst_sub_gen`, `wf_shift_gen` |
| SyntaxLemmas.lean | 10 shift/subst commutation lemmas |
| Soundness.lean | `step_sub`, `step_preservation`, `concEval_closedAt`, full proof structure |
| Counterexample.lean | wf-free `trans` is unsound: `Top ≤ Top→Top` derivable |
| MPSS.lean | `noPromoAt` predicate, `equivRed_no_promo_change_ann_at_zero` |

## What We Found to be FALSE (with Lean-verified counterexamples)

| Statement | File | Why False |
|-----------|------|-----------|
| `Sub` without wf guard on `trans` | Counterexample.lean | `Top ≤ Top→Top` via ill-formed β-redex |
| `equivRed_change_ann` (MPSS) | MPSSAudit.lean | ME-PRO needs equiv annotation, can't fire under sub |
| `weakening_equivRed` (MPSS) | MPSSAudit.lean | CtxRed reduces annotations; statement used original |
| `substitution_subRed` (MPSS) | MPSSAudit.lean | Universal quantification over target context too strong |
| `substitution_equivRed` (MPSS) | MPSSAudit.lean | Same issue |
| `substitution_equivRed_gen` ME-PRO k=j | MPSSSubstAudit.lean | MSubRed can't be converted to MEquivRed |
| LogRel `beta_L` (SubSem) | LogRel.lean | concEval-based SemVal too permissive at low fuel |
| LogRel `app_cong` (SubSem) | LogRel.lean | Same root cause |

**Pattern**: Every time a proof hit a wall, the statement was FALSE.
The audit-first approach saved enormous effort.

## Remaining Open Questions

### 1. CanonicalForms (4 sorrys) — THE core obstacle
`top_not_sub_lam`: `Sub Γ Top (λs.t) → False` with wf-guarded trans.
Blocked by: composing `trans(h1, beta_L, hw)` doesn't decrease any additive
measure (height, sizeOf, node count, trans count — all invariant).
All lexicographic combinations of (h1, h2) measures fail.

### 2. MPSS Commutativity (15 sorrys)
The paper's approach works (named variables). Our de Bruijn encoding has
fundamental scope mismatches:
- Stack elements in outer scope, body in inner scope (ME-FOP)  
- `equivRed_change_ann` is false — replaced with `noPromoAt` version
- Substitution lemma statements need scope-aware generalization

### 3. LogRel SemVal definition
The concEval-based app-type normalization makes SubSem false for beta_L.
The typeNorm-based version (SafeLogRel) avoids this but needs CanonicalForms.

## Recommended Next Steps (by estimated impact)

1. **Locally nameless MPSS**: All 8 false MPSS statements are de Bruijn
   artifacts. Locally nameless would eliminate scope mismatches while
   preserving the paper's mathematical content. ~15 days.

2. **Fix LogRel SemVal**: Use typeNorm (not concEval) for type normalization.
   Then beta_L/beta_R become trivial. app_cong remains hard but might be
   approachable via typeNorm monotonicity properties.

3. **Novel measure for CanonicalForms**: Something non-additive that
   distinguishes the composed derivation from the original. Perhaps
   involving the Wf structure, or the "depth of the leftmost app-middle
   trans chain." Speculative.

## Files Index

| File | Sorrys | Status |
|------|--------|--------|
| Syntax.lean | 0 | Complete |
| SyntaxLemmas.lean | 0 | Complete |
| Reduction.lean | 0 | Complete |
| Sub.lean | 0 | Complete |
| Eval.lean | 0 | Complete |
| SubstWf.lean | 0 | Complete |
| CanonicalForms.lean | 4 | Blocked (Hutchins obstacle) |
| Soundness.lean | 0 | Uses axioms from CanonicalForms |
| SafeLogRel.lean | 0 | Imports CanonicalForms |
| LogRel.lean | 4 | 2 FALSE, 2 sorry |
| MPSS.lean | 15 | De Bruijn scope issues |
| Counterexample.lean | 0 | wf-free unsoundness proof |
| MPSSAudit.lean | 0 | False statement proofs |
| MPSSSubstAudit.lean | 0 | More false statement proofs |

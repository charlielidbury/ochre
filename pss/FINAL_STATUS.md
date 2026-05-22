# PSS Type Safety — Final Research Status

## LN-MPSS Commutativity (PSS/LNMPSS.lean)
- **6657 lines**, 0 axioms, 24 sorrys
- Started from 27 axioms → 0 (25 proved, 2 deleted as false)
- **32 false statements** discovered total across the project
- Paper's Lemma 22 (stack extension) gap identified

### Sorry categories (24 total)
| Category | Count | Blocker | Fix |
|----------|-------|---------|-----|
| A: me_bet inversion | 7 | noPromoAt cross-constructor mismatch | Joint noPromoAt construction |
| B: stack alignment | 15 | Paper's Lemma 22 gap | equivRed_subst_diamond mutual with commutativity |
| C: diamond noPromoAt | 1 | SubRed→EquivRed noPromoAt conversion | Diamond return type extension |
| D: termination | 1 | simp_all loop on large hypotheses | Targeted tactic |

### What's proved (zero sorry)
- equivRed_refl, subRed_refl
- equivRed_ctx_mono, subRed_ctx_mono, equivRed_ctx_ext, subRed_ctx_ext
- equivRed_rename_strong, subRed_rename_strong (via ctx_rename mutual induction)
- equivRed_preserves_lc, subRed_preserves_lc (mutual induction)
- equivRed_preserves_not_mem_fvs, subRed_preserves_not_mem_fvs
- noPromoAt_equiv_swap, noPromoAt_sub_swap (mutual via @rec)
- noPromoAt_fresh_equiv, noPromoAt_fresh_sub
- noPromoAt_no_equiv_fresh
- promotion_collapse (all cases, including cofinite via classical dichotomy)
- subRed_subst_noPromo (substitution under non-promotion)
- subRed_subst_noPromo_noPromoAt (partial — 4 of 8 cases)
- top_sub_inv, no_sub_and_equiv
- ctxRed_refl, ctxRed_nil_of_ctxRed, ctxRed_stack_inv
- ctxRed_lookup_sub, ctxRed_lookup_equiv
- ctxRed_preserves_ctx_wf, ctxRed_preserves_stk_wf, ctxRed_preserves_stack_freshness
- typeNorm infrastructure (fuel_mono, closedAt, etc.)
- open/close/subst LN algebra (6 lemmas)
- Diamond (8 of 14 case pairs)
- Commutativity (all 7 case pairs structured, ME-BET/MS-FOP key case resolved via promotion_collapse)

## PSS Direct Proof (PSS/CanonicalForms.lean)
- 2 sorrys (Hutchins 2010 obstacle)
- All additive measures proved invariant (`totalWeight_reassoc_eq`)
- Sorry cases unreachable but unprovable (circular dependency)

## Substitution Infrastructure (PSS/SubstWf.lean)
- 0 sorrys, 0 axioms
- subst_wf, shift_sub_gen, subst_sub_gen, wf_shift_gen all proved

## Semantic Approach (PSS/LogRel.lean, PSS/SafeLogRel.lean)
- LogRel: 1 axiom (typeNorm_total), 0 sorrys
- SafeLogRel: imports CanonicalForms (2 sorrys)
- beta_L, beta_R, lam cases of fundamental_subSem proved

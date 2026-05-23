# PSS Type Safety — Final Research Status

## Summary

7071-line LN-MPSS mechanization in Lean 4. 0 axioms, 39 code sorrys.
Started from 27 axioms. 32+ false statements discovered.

## Key Research Finding: Paper Gap

The MPSS paper (Pasquale & Garcia-Perez, CSL 2026) has a gap in
Lemma 22 (stack extension / weakening). Our Lean counterexample shows
it's FALSE when the source stack is empty and target non-empty:

ME-FUN (empty stack, .sub annotation) enables different body promotions
than ME-FOP (non-empty stack, .equiv annotation from stack). This is
formalized in LNMPSS.lean with a machine-checked proof of False from
the axiom statement.

This gap affects commutativity's MS-PRO/ME-VAR case, which relies on
Lemma 22 to lift annotation EquivRed from empty to full stack.

The commutativity theorem is likely still TRUE — but the paper's proof
has an incomplete argument at this specific case.

## Remaining Obstacles (3 independent)

### 1. Stack alignment (15 sorrys)
Paper's Lemma 22 gap. ctxRed reduces annotations at nil stack, but
commutativity needs EquivRed at the current stack. All restricted
variants (closed terms, non-lambdas, existential) investigated and
found insufficient.

### 2. me_bet/me_app noPromoAt mismatch (7 sorrys)
Different noPromoAt derivations for the same judgment use different
internal terms (me_bet body result ≠ me_app operator result). No
induction scheme resolves this because the mismatch is semantic.

### 3. Termination + miscellaneous (remaining sorrys)
simp_all loops on large hypotheses, cofinite sizeOf = 0, etc.

## What's Fully Proved (zero sorry)

### LN-MPSS infrastructure
- equivRed_refl, subRed_refl
- equivRed_ctx_mono, subRed_ctx_mono
- equivRed_ctx_ext, subRed_ctx_ext
- equivRed_rename_strong, subRed_rename_strong (via ctx_rename)
- equivRed_preserves_lc, subRed_preserves_lc
- equivRed_preserves_not_mem_fvs, subRed_preserves_not_mem_fvs
- noPromoAt_equiv_swap, noPromoAt_sub_swap
- noPromoAt_fresh_equiv, noPromoAt_fresh_sub
- noPromoAt_no_equiv_fresh, noPromoAt_no_equiv_fresh_sub
- promotion_collapse (all cases including cofinite)
- subRed_subst_noPromo
- equivRed_ctx_drop, subRed_ctx_drop
- equivRed_ctx_drop_fresh, subRed_ctx_drop_fresh
- ctxRed infrastructure (refl, lookup, stack_inv, nil_of)
- typeNorm infrastructure
- LN algebra (open/close/subst, 6+ lemmas)

### PSS infrastructure
- subst_wf, shift_sub_gen, subst_sub_gen (zero sorry)
- step_sub, step_preservation
- concEval_closedAt, concEval_isValue

### Commutativity structure
- All 7 case pairs handled (MS-TOP, MS-EQU, MS-PRO, MS-APP, MS-FUN, MS-FOP, ME-TAP)
- ME-BET/MS-FOP key case resolved via promotion_collapse
- Diamond property structured (8 of 14 case pairs)
- Mutual recursion with equivRed_subst_diamond wired

## False Statements Discovered (32+)

| Encoding | Count | Examples |
|----------|-------|---------|
| de Bruijn MPSS | 11 | equivRed_change_ann, weakening, substitution |
| LN dot-notation | 7 | open_at/subst_fvar argument order |
| LN stack_ext | 2 | ME-FUN vs ME-FOP with different stacks |
| LN noPromoAt | 4 | freshness insufficient for promotion chains |
| LN annotation swap | 2 | ME-PRO indirect promotion via stack |
| LN subst variants | 4 | equivRed_subst_equiv, subRed_subst_equiv |
| PSS wf-free trans | 1 | Top ≤ Top→Top |
| LogRel SemVal | 2 | beta_L, app_cong with concEval-based def |

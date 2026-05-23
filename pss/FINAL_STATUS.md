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

## Exhaustive Exploration of Weakening-Based Approaches

Every plausible strategy for resolving the MS-PRO/ME-VAR case WITHOUT
changing CT-ANN has been investigated and found to fail:

### 1. equivRed_weaken in the mutual block (same output v)
Statement: `EquivRed G s u v -> CtxRed G s G' s' -> EquivRed G' s' u v`
Status: FALSE. Previously disproved — ctxRed changes annotations, making
the original output v unreachable in the reduced context G'.

### 2. equivRed_weaken with existential output (exists v')
Statement: `EquivRed G s u v -> CtxRed G s G' s' -> exists v', EquivRed G' s' u v'`
Status: TRUE (trivially via equivRed_refl), but NOT SUFFICIENT. The
MS-PRO/ME-VAR case forces t3 = t' (the reduced annotation in G'), not
an arbitrary witness. The right edge SubRed G' s' (fvar x) t3 can only
be: MS-PRO (t3=t'), MS-TOP (t3=.top), or MS-EQU+ME-VAR (t3=fvar x,
requires .equiv annotation). An existential t3 doesn't help because all
three specific choices fail for the top edge.

### 3. Restructuring diamond_full to avoid context change
Idea: have diamond_full return results in the ORIGINAL G;s rather than
G1;s1, then apply weakening to lift. Fails because weakening itself is
false (approach 1).

### 4. Using ctxRed_refl to dodge the problem
Commutativity's inductive cases (ME-FUN, ME-FOP, ME-APP, ME-BET) pass
non-trivial ctxRed to recursive calls. Even though external callers
(Theorem 3, diamond) only need ctxRed_refl, the internal induction
encounters MS-PRO/ME-VAR with non-trivial ctxRed. Cannot be avoided.

### 5. CT-ANN at full stack (previously tried and reverted)
Changing CT-ANN to use EquivRed G s t t' instead of EquivRed G [] t t'
DOES fix MS-PRO/ME-VAR trivially. However, it breaks ctxRed_nil_of_ctxRed,
ctxRed_lookup, ctxRed_stack_inv, and diamond_full body construction —
shifting the stack alignment problem from commutativity to infrastructure.
The paper's nil-stack CT-ANN works WITH Lemma 22; without Lemma 22, neither
choice of CT-ANN avoids the gap.

### Conclusion

The MS-PRO/ME-VAR case genuinely requires either:
(a) Stack extension/shrinking — FALSE (machine-checked counterexample)
(b) Weakening through ctxRed — FALSE (same/existential both fail)
(c) Changing CT-ANN — shifts the problem without resolving it

The paper's proof has a gap that cannot be fixed with local changes. A
fundamental rethinking of how MPSS handles the interaction between
annotations and stacks is needed. The commutativity theorem itself may
still be TRUE, but the paper's proof strategy at this case is incomplete.

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

## Design Analysis: Eliminating ME-FUN to Fix Stack Alignment

### Motivation

The stack alignment problem exists because ME-FUN (empty stack) and
ME-FOP (non-empty stack) assign different annotations to the body
variable of a lambda:

- ME-FUN at `Gamma; [] |- lam d b`: body variable x gets `.sub d`
- ME-FOP at `Gamma; alpha::s |- lam d b`: body variable x gets `.equiv alpha`

This divergence is the root cause of Lemma 22's failure: lifting a
derivation from empty to non-empty stack changes which rule fires,
which changes the annotation, which changes the body's behavior.

### Proposal: Unified ME-FOP

Eliminate ME-FUN entirely. When the stack is empty and we encounter
`lam d b`, push a default element (the domain `d` itself) and use
ME-FOP-style reasoning:

```
ME-FOP-UNIFIED (empty stack case):
  Gamma;nil |- d ==-> d'    Gamma, x EQUIV d; nil |- b^x ==-> b'^x
  -----------------------------------------------------------------
  Gamma; nil |- lam d b ==-> lam d' b'

ME-FOP-UNIFIED (non-empty stack case):
  Gamma;nil |- d ==-> d'    Gamma, x EQUIV alpha; s |- b^x ==-> b'^x
  -------------------------------------------------------------------
  Gamma; alpha::s |- lam d b ==-> lam d' b'
```

Both cases use `.equiv` annotation (no `.sub`). This eliminates the
sub-vs-equiv annotation mismatch.

### Analysis: Does This Fix Stack Extension?

No. The annotation VALUES still differ across stacks:

- Empty stack: body variable x gets `.equiv d` (the domain)
- Stack [alpha]: body variable x gets `.equiv alpha`
- Stack [beta, alpha]: body variable x gets `.equiv beta`

The annotation always depends on the top of the stack (or the domain
when empty). These are different values in general (`d != alpha`),
so Lemma 22's inductive step for the body still fails: the IH gives
a derivation under `.equiv d` but we need one under `.equiv alpha`.

The unification only eliminates the `.sub`-vs-`.equiv` KIND mismatch.
It does NOT eliminate the VALUE mismatch (which value is stored in
the annotation). Stack extension requires annotations to be
stack-independent, but the whole point of the annotation is to track
the actual argument flowing through the stack.

### Alternative: Constant Annotation (Always `.equiv d`)

What if the annotation is ALWAYS `.equiv d` (the domain), regardless
of the stack? Then ME-FOP would ignore the stack element for the
annotation:

```
  Gamma;nil |- d ==-> d'    Gamma, x EQUIV d; s' |- b^x ==-> b'^x
  -----------------------------------------------------------------
  Gamma; s |- lam d b ==-> lam d' b'
  (where s' = [] if s = [], or tail(s) if s non-empty)
```

This WOULD make annotations stack-independent, fixing Lemma 22.
But it BREAKS beta-reduction semantics: when `(lam d b)` is applied
to argument `alpha`, the body variable x must be equivalent to `alpha`
(the actual argument), not `d` (the declared domain). Without this
connection, the calculus cannot model function application correctly.

### Conclusion

The stack alignment problem is inherent in MPSS's design. The body
variable's annotation MUST differ between the applied case (tracks
the actual argument from the stack) and the unapplied case (tracks
the declared domain). No unification of ME-FUN and ME-FOP can
simultaneously preserve both:

1. **Stack extension** (Lemma 22): annotations must be independent
   of which stack elements are present, so that derivations can be
   lifted across stacks.

2. **Beta-reduction semantics**: annotations must track the actual
   argument, so that the body variable's behavior reflects what was
   passed, not just what was declared.

These are fundamentally incompatible requirements. The paper's proof
has a genuine gap at this point, and no local redesign of the lambda
rules resolves it. The viable path forward remains dissolving the
MS-PRO/ME-VAR case into the mutual commutativity block (Option 3
from STACK_EXTENSION_ANALYSIS.md) rather than relying on standalone
stack extension.

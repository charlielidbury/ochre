# Stack Extension Analysis: Paper vs Our Encoding

## Summary

The paper's Lemma 19 / Lemma 22 (weakening) claims stack extension for
equivalence reduction:

    If Gamma;s |- u ==-> v then Gamma,Gamma'; s@s' |- u ==-> v

where s@s' APPENDS s' at the END of s. This is not prepending.

Our counterexample proved that SAME-CONTEXT stack extension from [] to s
is false. But we initially thought the paper was doing the same thing.
After careful reading, the paper extends BOTH context and stack, and uses
append (not prepend). However, the paper's proof still appears to have
a genuine gap in the ME-FUN case.

## The Paper's Stack Convention

The stack is LIFO (last-in-first-out):
- ME-APP pushes v to the FRONT: Gamma; v::s |- u ==-> u'
- ME-FOP pops from the FRONT: Gamma; alpha::s |- lam... ==-> lam...
- Elements are cons'd at the front and popped from the front

The paper's Lemma 19 extends with "s@s'", meaning:
- The ORIGINAL stack s is at the FRONT (where ME-FOP operates)
- The new elements s' are at the BACK (past all poppable elements)
- The original computation is unaffected because it never reaches s'

This is fundamentally different from our counterexample, which replaced
[] with s (putting new elements at the FRONT where ME-FOP would see them).

## Lemma 22 Statement (p. 9:37)

Let Gamma;s and Gamma';s' be two extended contexts such that
Gamma,Gamma'; s@s' is prevalid. Let u and v be terms.

    If Gamma;s |- u ==-> v then Gamma,Gamma'; s@s' |- u ==-> v.

Extends BOTH context (Gamma to Gamma,Gamma') and stack (s to s@s').

## The ME-FUN Case Gap

The proof of Lemma 22 has what appears to be a genuine gap in the ME-FUN
case. Here is the detailed argument:

### Setup
When the original derivation uses ME-FUN:
- s = nil (ME-FUN requires empty stack)
- Premises: Gamma;nil |- dom ==-> dom' and Gamma,x<=dom;nil |- body ==-> body'
- Conclusion should be: Gamma,Gamma'; nil@s' |- lam... ==-> lam...
- Since nil@s' = s', the target stack is just s'

### The Problem
When s' is non-empty (say s' = alpha :: s0):
- The target has stack alpha :: s0 (non-empty)
- ME-FUN cannot fire (it requires empty stack)
- ME-FOP must fire instead (it handles non-empty stack)
- ME-FOP creates body context (x, EQUIV alpha) with remaining stack s0
- But the original body was under (x, SUB dom) with stack nil
- These are DIFFERENT annotations and DIFFERENT stacks

### Why This Matters
The body derivation under (x, sub dom); nil may use MS-PRO on variables
whose annotations are lambdas. Under sub annotation, MS-FUN fires
(empty stack), giving inner variables .sub annotations. Under equiv
annotation, ME-PRO can fire on x, and under non-empty stack MS-FOP
fires, giving inner variables .equiv annotations. The results can
differ.

### Our Counterexample (LNMPSS.lean)
Concrete instance showing this fails:

    Gamma = [x equiv (lam (fvar y) (bvar 0)), y <= Top]

    Under Gamma;[]: fvar "x" ==-> lam (fvar "y") (fvar "y")
      via ME-PRO: SubRed uses MS-FUN, body z gets .sub (fvar y),
      MS-PRO on z gives (fvar y).

    Under Gamma;[Top]: would need SubRed via MS-FOP,
      body z gets .equiv Top, MS-PRO blocked (needs .sub).
      Result (fvar "y") is UNREACHABLE.

### What the Paper's Proof Says
The paper's proof of the ME-FUN case (p. 9:37) concludes:

    "Therefore, by rule ME-FUN, we deduce that
     Gamma,Gamma'; nil |- lam x <= a.b ==-> lam x <= a'.b'."

The conclusion has stack nil, NOT s'. This only works if s' = nil.
For non-empty s', the proof does not address how to use ME-FOP
instead of ME-FUN, or how to handle the annotation/stack change
in the body.

## How the MS-PRO/ME-VAR Case Uses Lemma 19/22

In the commutativity proof (p. 9:18), the ME-Var with Ms-Pro case:

1. Has Gamma;s |- x ==-> x (ME-VAR) and Gamma;s |- x <=-> t (MS-PRO)
2. CtxRed gives Gamma' with reduced annotation t'
3. Needs: Gamma;s |- t ==-> t' (top edge) and Gamma';s' |- x <=-> t' (right edge)
4. The right edge is just MS-PRO with the reduced annotation (easy)
5. For the top edge: CT-ANN gives Gamma_0;nil |- t ==-> t'
6. Lemma 19/22 extends to: Gamma_0, (x<=t), Gamma_1; s |- t ==-> t'

Step 6 uses Lemma 22 with source stack nil and target stack s.
If s is non-empty, this hits the ME-FUN gap described above.

## Distinction: Append vs Prepend

Our initial FALSE stack extension said:
    EquivRed Gamma [] u v -> EquivRed Gamma s u v
This REPLACES the empty stack with s (new elements at the FRONT).

The paper's Lemma 19 APPENDS:
    EquivRed Gamma s u v -> EquivRed Gamma (s@s') u v
The original s is at the front; new s' is at the back.

These are different when s is non-empty. But when s = nil (as in the
MS-PRO/ME-VAR case), nil@s' = s', so append and replace coincide.
The ME-FUN gap affects BOTH formulations equally when s = nil.

## Subtyping Reduction: No Stack Extension Needed

Importantly, the paper's Lemma 21 (weakening for subtyping reduction)
says:

    If Gamma;s |- u <=-> v then Gamma,Gamma'; s |- u <=-> v

The stack is UNCHANGED for subtyping (only context extends). This is
because MS-PRO does not depend on the stack (it just looks up the
context). The MS-PRO/ME-VAR case's RIGHT edge (MS-PRO) only needs
context extension, not stack extension. The stack extension is only
needed for the TOP edge (equiv reduction).

## Implications for Our Proof

### Option 1: The paper has a genuine gap
If the ME-FUN case of Lemma 22 is truly broken for non-empty s',
then the MS-PRO/ME-VAR case of commutativity (which needs Lemma 22
with source stack nil and target stack s) is also broken. This would
mean the paper's commutativity proof has a gap in this case.

The LNMPSS.lean counterexample (cex_Gamma at line 6253) demonstrates
that same-output stack extension from [] to s is false, even for
annotation terms. This is a formal proof that the ME-FUN-to-ME-FOP
transformation does not preserve outputs in general.

### Option 2: There is a subtlety we are missing
Possibilities:
- The prevalidity condition might restrict which derivations can appear
  in a way that avoids the problematic case (but our analysis suggests
  it does not -- prevalidity only constrains free variables, not the
  sub/equiv annotation structure).
- The paper might intend a different reading of ME-FUN case where the
  IH is applied differently than we expect.
- The named-variable + alpha-equivalence setting might avoid the issue
  in some non-obvious way (e.g., x is fresh and never appears in Gamma',
  so ME-PRO on x cannot fire -- but the problem is actually about
  RECURSIVE calls where inner variables are bound to lambdas).

### Option 3: Dissolve into the mutual block
As noted in LNMPSS.lean (line 1071), the MS-PRO/ME-VAR case can be
dissolved into the mutual commutativity/diamond block. Instead of
proving stack extension as a standalone lemma, handle the "stack
alignment problem" within the main mutual induction. The shared
termination measure approach (already sketched in LNMPSS.lean) treats
the annotation reduction as a sub-problem of the commutativity proof
itself, avoiding the need for Lemma 22 as a separate tool.

### Option 4: Weakening lemma in the mutual block

Add `equivRed_weaken` / `subRed_weaken` to the mutual block alongside
commutativity, diamond, and equivRed_subst_diamond.

**4a. Same-output weakening:**
`EquivRed G s u v -> CtxRed G s G' s' -> EquivRed G' s' u v`

Previously DISPROVED. CtxRed changes annotations in the context. If the
original derivation used ME-PRO to look up an annotation, the reduced
context has a different annotation, producing a different output. The
original v is unreachable in the reduced context.

**4b. Existential-output weakening:**
`EquivRed G s u v -> CtxRed G s G' s' -> exists v', EquivRed G' s' u v'`

TRUE (trivially via equivRed_refl: take v' = u). But NOT SUFFICIENT
for the MS-PRO/ME-VAR case. The right edge SubRed G' s' (fvar x) t3
forces t3 to be one of {t' (via MS-PRO), .top (via MS-TOP), fvar x
(via MS-EQU+ME-VAR, requires .equiv annotation)}. An arbitrary existential
witness v' does not help because the right edge pins t3 to a specific
value. See the QED argument in LNMPSS.lean sorry #7.

**4c. Restructuring diamond_full to avoid G1;s1 output:**
Have diamond_full return results in the original G;s, then apply weakening
to lift. Fails because weakening (4a) is false.

### Option 5: CT-ANN at full stack

Change CT-ANN to use `EquivRed G s t t'` instead of `EquivRed G [] t t'`.
This was tried (commit 79aa0ff8) and reverted (commit 9f8d8381). It DOES
fix MS-PRO/ME-VAR trivially (ctxRed_lookup_sub gives EquivRed at stack s
directly). However, it breaks ctxRed_nil_of_ctxRed, ctxRed_lookup,
ctxRed_stack_inv, and diamond_full body construction. The paper's nil-stack
CT-ANN is designed to work WITH Lemma 22; without Lemma 22, neither choice
of CT-ANN avoids the gap.

## Conclusion (Updated)

All five options have been exhaustively investigated:

| Option | Status | Why it fails |
|--------|--------|-------------|
| 1. Paper gap (Lemma 22 broken) | Confirmed | Machine-checked counterexample |
| 2. Subtlety we're missing | Unlikely | All variants analyzed |
| 3. Dissolve into mutual block | Investigated | Same stack alignment problem resurfaces |
| 4. Weakening in mutual block | Failed | Same-output FALSE; existential insufficient |
| 5. CT-ANN at full stack | Reverted | Shifts problem to infrastructure |

The MS-PRO/ME-VAR case requires either stack extension (FALSE), weakening
through ctxRed (FALSE or insufficient), or changing CT-ANN (shifts but does
not resolve the problem). The paper's proof has a genuine gap at this case
that cannot be fixed with local changes.

The commutativity theorem is likely still TRUE -- the gap is in the proof
strategy, not the statement. A fundamental rethinking of how MPSS handles
the interaction between annotations and stacks is needed. Possible
directions for future work:
- A novel proof strategy for commutativity that avoids Lemma 22 entirely
- A redesigned ctxRed that separates context and stack reductions
- A different annotation scheme that makes annotations stack-independent
- A completely different approach to PSS type safety (see APPROACHES.md)

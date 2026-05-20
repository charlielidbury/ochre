import PSS.MPSS

/-!
# Audit of sorry'd cases in substitution_equivRed_gen / substitution_subRed_gen

This file audits each sorry in the substitution lemmas of PSS/MPSS.lean.
For each case, we construct counterexamples (demonstrating falsity) or
assess provability.

## Summary

### DEFINITELY FALSE (counterexample derives `False` from the sorry):

1. **ME-PRO at target index (k=j)** in `substitution_equivRed_gen`:
   The premise gives MSubRed but the conclusion needs MEquivRed.
   When the sub-derivation uses ms_pro (genuine promotion), the result
   involves a shifted bound that MEquivRed cannot produce (ME-PRO
   requires Ann.equiv, which is absent after substitution removes it).
   Concrete counterexample: `me_pro_at_j_gives_false` derives False.

2. **Stack map (s.map (·.subst 0 α) = s)** in `substitution_equivRed`
   and `substitution_subRed` (the specialized versions):
   Stack elements CAN reference bvar 0 when ME-APP pushes operands
   under the binder being substituted. So the map is NOT the identity.
   Concrete: `[bvar 0].map (·.subst 0 Top) = [Top] ≠ [bvar 0]`.
   Combined with finding 1, the WHOLE substitution_equivRed_gen is FALSE.

3. **ME-FOP / MS-FOP stack scope mismatch** in both `_gen` lemmas:
   The IH produces stack at index j+1 (body scope) but ME-FOP needs
   index j (outer scope). This is a design flaw: the generalization
   applies one substitution index to both term and stack, but they
   live at different scopes. Cannot construct a standalone False proof
   because the lemma is already shown FALSE by finding 1, but the
   structural issue is distinct and would persist even if finding 1
   were fixed.

### PLAUSIBLY TRUE (individual sorry, but surrounding lemma is FALSE):

4. **ME-VAR at target index (k=j)**: Requires showing α ≡→ v' under
   an arbitrary stack, given α ≡→ v' under empty stack. This appears
   true in principle (stack-change lemma using equivRed_change_ann_rev),
   but is moot since the overall lemma is FALSE.

5. **ME-PRO at k<j and k>j**: These require lookup lemmas for the
   adjusted context (adjustPrefix). The lookup properties should hold
   by construction. Individually provable but moot.

### ROOT CAUSE

The generalized substitution lemma applies one de Bruijn index j
uniformly to term, output, AND stack. But ME-FOP/MS-FOP introduce a
binder that shifts the term index to j+1 while leaving stack elements
at index j. This scope conflation makes the lemma statement unsound.

A correct generalization would need to track stack scope separately
from term scope (e.g., separate substitution passes, or a well-scopedness
predicate restricting stack elements to the outer scope).
-/

open Expr MPSS

/-! ## 1. ME-PRO at target index (k=j) — FALSE

When ME-PRO fires at index k=j with:
  hlook : context at j has Ann.equiv α (the binding being substituted)
  hsub  : MSubRed (Γ_above ++ Ann.equiv α :: Γ) s (α.shift (j+1) 0) α'

After substitution, bvar j becomes α.shift j 0. The IH on hsub gives
a MSubRed conclusion, but the lemma needs MEquivRed.

When hsub uses ms_pro (genuine subtype promotion into a DIFFERENT
annotation), α' involves a shifted bound from that annotation. This
shifted bound has no MEquivRed derivation: MEquivRed for a bvar gives
only ME-VAR (identity) or ME-PRO (needs Ann.equiv, which was removed
by substitution).

Counterexample:
  α = bvar 0 (in context Γ = [Ann.sub Top]), j = 0
  ME-PRO at index 0 in [Ann.equiv (bvar 0), Ann.sub Top] uses ms_pro
  at index 1 to promote bvar 1 to Top.
  After substitution: goal is MEquivRed [Ann.sub Top] _ (bvar 0) Top.
  But [Ann.sub Top] has no Ann.equiv, so ME-PRO cannot fire, and
  ME-VAR gives bvar 0 ≠ Top.
-/

def me_pro_at_j_cex_h_body :
    MEquivRed [Ann.equiv (.bvar 0), Ann.sub .top] [.top] (.bvar 0) .top :=
  .me_pro (k := 0) (α := .bvar 0) rfl
    (.ms_pro (k := 1) (t := .top) rfl)

def me_pro_at_j_cex_h_arg :
    MEquivRed [Ann.sub .top] [] (.bvar 0) (.bvar 0) :=
  .me_var

-- Verify the substitution arithmetic:
-- (bvar 0).subst 0 (bvar 0) = bvar 0
-- Top.subst 0 (bvar 0) = Top
example : (Expr.bvar 0).subst 0 (.bvar 0) = .bvar 0 := rfl
example : Expr.top.subst 0 (.bvar 0) = .top := rfl

-- The generalized lemma claims:
--   MEquivRed [Ann.sub Top] [Top] (bvar 0) Top
-- This is FALSE: bvar 0 can only go to bvar 0 (ME-VAR) or requires
-- Ann.equiv (ME-PRO), but context has Ann.sub.
noncomputable def me_pro_at_j_gives_false : False := by
  have h := @substitution_equivRed_gen
    (.bvar 0)        -- α
    []               -- Γ_above (empty, so j=0)
    [Ann.sub .top]   -- Γ
    [.top]           -- s
    (.bvar 0)        -- u
    .top             -- u'
    (.bvar 0)        -- v' (from h_arg)
    me_pro_at_j_cex_h_body
    me_pro_at_j_cex_h_arg
  simp only [adjustPrefix, List.nil_append, List.length_nil,
             Expr.shift_zero, Expr.subst, List.map] at h
  -- h : MEquivRed [Ann.sub Top] [Top] (bvar 0) Top
  -- Eliminate all possible derivation rules:
  suffices ∀ out, MEquivRed [Ann.sub Expr.top] [Expr.top] (Expr.bvar 0) out → out ≠ Expr.top by
    exact this _ h rfl
  intro out h' hout
  match h' with
  | .me_var => exact Expr.noConfusion hout
  | .me_pro hlook _ => simp [List.get?] at hlook


/-! ## 2. Stack map s.map (·.subst 0 α) ≠ s — FALSE

Stack elements in the source derivation (under Ann.equiv α :: Γ) can
reference bvar 0, because ME-APP pushes operands that are in scope of
the extended context. After substitution, these references become α,
so the map is NOT the identity.
-/

-- Concrete demonstration: substituting Top for bvar 0 in a stack containing bvar 0
example : [Expr.bvar 0].map (·.subst 0 Expr.top) ≠ [Expr.bvar 0] := by
  simp [List.map, Expr.subst]

example : [Expr.bvar 0].map (·.subst 0 Expr.top) = [Expr.top] := by
  simp [List.map, Expr.subst]

-- A derivation that has stack [bvar 0] referencing the binder:
def stack_map_cex_src :
    MEquivRed [Ann.equiv .top] [.bvar 0] (.bvar 0) (.bvar 0) :=
  .me_var

-- The specialized substitution_equivRed (line 481) would need to bridge
-- from s.map (·.subst 0 α) to s, but [bvar 0].map (·.subst 0 Top) = [Top] ≠ [bvar 0].
-- The gap is real and unbridgeable.


/-! ## 3. ME-FOP / MS-FOP scope mismatch — STRUCTURAL BUG

When ME-FOP fires: the body goes under binder Ann.equiv α_stk, shifting
the target index from j to j+1. But stack elements remain at the outer
scope (index j). The IH (called with Γ_above' = Ann.equiv α_stk :: Γ_above,
j' = j+1) produces:

  stack: s_rest.map (·.subst (j+1) (α.shift (j+1) 0))

But ME-FOP's conclusion requires:

  stack: s_rest.map (·.subst j (α.shift j 0))

These differ when stack elements reference bvar j or bvar (j+1).

Note: We cannot derive False from this independently because the overall
lemma is already shown FALSE by the ME-PRO counterexample above. However,
this structural issue is a separate root cause that would remain even if
the ME-PRO issue were somehow fixed.

Example of the index mismatch:
-/
example : (Expr.bvar 0).subst 1 Expr.top ≠ (Expr.bvar 0).subst 0 Expr.top := by
  simp [Expr.subst]


/-! ## 4. ME-VAR at k=j — PLAUSIBLY TRUE (but moot)

The sorry needs: given `h_arg : MEquivRed Γ [] α v'`, derive
`MEquivRed (adjustPrefix Γ_above α ++ Γ) (s.map ...) (α.shift j 0) (v'.shift j 0)`.

This requires a "stack-change" lemma: if α ≡→ v' under empty stack, then
α ≡→ v' under any stack. This appears true because:
- For non-lambda α: stack doesn't affect the applicable rules (ME-VAR,
  ME-TOP, ME-TAP, ME-BET, ME-APP all work regardless of stack).
- For lambda α: under [], ME-FUN fires; under non-empty stack, ME-FOP fires.
  The body annotation changes (Ann.sub → Ann.equiv), but derivations under
  Ann.sub are valid under Ann.equiv (by equivRed_change_ann_rev). The body
  stack changes from [] to whatever was popped, which requires the IH.

This is a non-trivial lemma but appears provable. However, since the overall
substitution_equivRed_gen is FALSE (by ME-PRO counterexample), this is moot.
-/


/-! ## 5. ME-PRO at k<j and k>j — PLAUSIBLY TRUE (but moot)

These cases need lookup lemmas showing that:
- For k < j: position k in (adjustPrefix Γ_above α ++ Γ) has the same
  annotation kind (Ann.equiv) as in (Γ_above ++ Ann.equiv α :: Γ), with
  the annotation body appropriately substituted.
- For k > j: position k-1 in (adjustPrefix Γ_above α ++ Γ) corresponds
  to position k in (Γ_above ++ Ann.equiv α :: Γ), since we removed one
  entry at position j.

These are straightforward consequences of the adjustPrefix definition and
list indexing arithmetic. Individually provable, but moot given the
overall lemma falsity.
-/

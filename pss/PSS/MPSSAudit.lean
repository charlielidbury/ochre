import PSS.MPSS

/-!
# Audit of sorry'd statements in PSS/MPSS.lean

For each sorry'd theorem/def, we check whether it is TRUE or FALSE
by constructing specific derivation trees and testing the conclusion.

## SUMMARY

DEFINITELY FALSE (counterexamples below derive `False` from sorry):
1. `equivRed_change_ann` (line 541)     -- ME-PRO breaks when equiv->sub
2. `weakening_equivRed` (line 816)      -- CtxRed changes annotations, statement uses original
3. `substitution_subRed` (line 837)     -- universal Gamma'/s' too strong, index arithmetic
4. `substitution_equivRed` (line 299)   -- same structural issue as substitution_subRed

PLAUSIBLY TRUE (no counterexample found):
5. `weakening_equivRed_ctx` (line 269)  -- genuine property, circular proof difficulty
6. `diamond` ME-PRO+ME-PRO (line 664)  -- needs mutual diamond for Sub+Equiv
7. `commutativity` MS-EQU (line 900)    -- blocked by other lemmas
-/

open Expr MPSS

/-! ## 1. equivRed_change_ann (line 537) -- FALSE

Statement:
  If `MEquivRed (Ann.equiv v :: Gamma) s body body'`,
  then `MEquivRed (Ann.sub dom :: Gamma) s body body'`.

Counterexample: ME-PRO at index 0 with `Ann.equiv .top`.
  - Source: `MEquivRed [Ann.equiv .top] [] (.bvar 0) .top`
  - After changing to `Ann.sub`: would need ME-PRO (requires Ann.equiv, absent)
    or ME-VAR (gives `.bvar 0`, not `.top`).
-/

def equivRed_change_ann_cex_src : MEquivRed [Ann.equiv .top] [] (.bvar 0) .top :=
  .me_pro (k := 0) (α := .top) rfl (.ms_equ .me_top)

noncomputable def equivRed_change_ann_gives_false : False := by
  have h := equivRed_change_ann (v := .top) (dom := .top) (Γ := []) (s := [])
    equivRed_change_ann_cex_src
  -- h : MEquivRed [Ann.sub .top] [] (.bvar 0) .top
  -- Only me_pro matches (me_var eliminated: .bvar 0 /= .top).
  -- me_pro requires Ann.equiv at index 0, but context has Ann.sub.
  cases h with
  | me_pro hlook _ => simp [List.get?] at hlook


/-! ## 2. weakening_equivRed (line 811) -- FALSE

Statement:
  If `Gamma.get? k = some (Ann.sub t)` and `CtxRed Gamma s Gamma' s'`,
  then `MSubRed Gamma' s' (.bvar k) (t.shift (k+1) 0)`.

The statement uses the ORIGINAL annotation `t`, but CtxRed reduces annotations
pointwise: if `Gamma` has `Ann.sub t` at position `k`, then `Gamma'` has
`Ann.sub t'` where `t =>-> t'`. So MS-PRO in `Gamma'` gives `t'.shift`, not
`t.shift`.

Counterexample:
  - `Gamma = [Ann.sub (.app .top .top)]`, `k=0`, `t = (.app .top .top)`
  - CtxRed via ME-TAP: `(.app .top .top) =>-> .top`, so `Gamma' = [Ann.sub .top]`
  - Claim: `MSubRed [Ann.sub .top] [] (.bvar 0) (.app .top .top)`
  - But the only outputs for `(.bvar 0)` in `[Ann.sub .top]` are:
    `.top` (via ms_pro or ms_top) and `.bvar 0` (via ms_equ me_var).
-/

def weakening_equivRed_cex_ctxRed : CtxRed [Ann.sub (.app .top .top)] [] [Ann.sub .top] [] :=
  .ct_ann_sub .ct_nil .me_tap

noncomputable def weakening_equivRed_gives_false : False := by
  have h := weakening_equivRed
    (k := 0) (t := .app .top .top)
    (show [Ann.sub (.app .top .top)].get? 0 = some (Ann.sub (.app .top .top)) from rfl)
    weakening_equivRed_cex_ctxRed
  change MSubRed [Ann.sub .top] [] (.bvar 0) (.app .top .top) at h
  -- Workaround for Lean's dependent elimination on ms_pro's shift-dependent output:
  -- generalize the output so match can proceed without solving shift equations.
  suffices ∀ out, MSubRed [Ann.sub Expr.top] [] (Expr.bvar 0) out → out ≠ .app .top .top by
    exact this _ h rfl
  intro out h' hout
  match h' with
  | .ms_top => exact Expr.noConfusion hout
  | .ms_equ heq =>
    match heq with
    | .me_var => exact Expr.noConfusion hout
    | .me_pro hlook _ => simp [List.get?] at hlook


/-! ## 3. substitution_subRed (line 832) -- FALSE

Statement:
  If `MSubRed (Ann.equiv v0 :: Gamma) s u1 u3`, then
  `MSubRed Gamma' s' (u1.subst 0 v1) (u3.subst 0 v1)`.

This is universally quantified over `Gamma'`, `s'`, `v1` with no connection
to `Gamma` or `s`. Choosing an empty target context breaks it.

Counterexample:
  - Context: `[Ann.equiv .top, Ann.sub (.bvar 0)]`
  - `u1 = .bvar 1`, MS-PRO at `k=1` gives `u3 = .bvar 2`
  - Choose `v1 = .bvar 99`, `Gamma' = []`, `s' = []`
  - `(.bvar 1).subst 0 (.bvar 99) = .bvar 0`
  - `(.bvar 2).subst 0 (.bvar 99) = .bvar 1`
  - Claim: `MSubRed [] [] (.bvar 0) (.bvar 1)` -- impossible in empty context.
-/

def substitution_subRed_cex_src :
    MSubRed [Ann.equiv .top, Ann.sub (.bvar 0)] [] (.bvar 1) (.bvar 2) :=
  .ms_pro (k := 1) (t := .bvar 0) rfl

example : (Expr.bvar 1).subst 0 (.bvar 99) = .bvar 0 := rfl
example : (Expr.bvar 2).subst 0 (.bvar 99) = .bvar 1 := rfl

noncomputable def substitution_subRed_gives_false : False := by
  have h := @substitution_subRed .top [] [] [Ann.sub (.bvar 0)] [] (.bvar 1) (.bvar 2) (.bvar 99)
    substitution_subRed_cex_src
  change MSubRed [] [] (.bvar 0) (.bvar 1) at h
  suffices ∀ out, MSubRed ([] : MCtx) ([] : Stack) (Expr.bvar 0) out → out ≠ .bvar 1 by
    exact this _ h rfl
  intro out h' hout
  match h' with
  | .ms_top => exact Expr.noConfusion hout
  | .ms_equ heq =>
    match heq with
    | .me_var => simp [Expr.bvar.injEq] at hout
    | .me_pro hlook _ => simp [List.get?] at hlook


/-! ## 4. substitution_equivRed (line 293) -- FALSE

Statement:
  If `MEquivRed (Ann.equiv alpha :: Gamma) s u u'` and `MEquivRed Gamma' [] v v'`,
  then `MEquivRed Gamma' s' (u.subst 0 v) (u'.subst 0 v')`.

Same structural issue: universally quantified over `Gamma'`, `s'` with no
connection to the source context.

Counterexample:
  - Context: `[Ann.equiv .top, Ann.equiv (.bvar 0)]`
  - `u = .bvar 1`, ME-PRO at `k=1` with MS-EQU ME-VAR gives `u' = .bvar 2`
  - `v = .top`, `v' = .top` (via ME-TOP), `Gamma' = []`, `s' = []`
  - `(.bvar 1).subst 0 .top = .bvar 0`
  - `(.bvar 2).subst 0 .top = .bvar 1`
  - Claim: `MEquivRed [] [] (.bvar 0) (.bvar 1)` -- impossible in empty context.
-/

def substitution_equivRed_cex_src :
    MEquivRed [Ann.equiv .top, Ann.equiv (.bvar 0)] [] (.bvar 1) (.bvar 2) :=
  .me_pro (k := 1) (α := .bvar 0) rfl (.ms_equ .me_var)

example : (Expr.bvar 1).subst 0 .top = .bvar 0 := rfl
example : (Expr.bvar 2).subst 0 .top = .bvar 1 := rfl

noncomputable def substitution_equivRed_gives_false : False := by
  have h := @substitution_equivRed .top [] []
    [Ann.equiv (.bvar 0)] [] (.bvar 1) (.bvar 2) .top .top
    substitution_equivRed_cex_src .me_top
  -- h : MEquivRed [] [] (.bvar 0) (.bvar 1)  (after reduction)
  cases h with
  | me_pro hlook _ => simp [List.get?] at hlook


/-! ## 5. weakening_equivRed_ctx (line 264) -- PLAUSIBLY TRUE

Statement:
  If `MEquivRed Gamma0 s0 t t'` and `CtxRed Gamma0 s0 Gamma1 s1`,
  then `MEquivRed Gamma1 s1 t t'`.

This says: the same term reduces to the same result in a "more reduced" context.
The ME-PRO case creates a circularity with commutativity (the reduced annotation
needs its sub-reduction re-established in the new context), but the statement
itself appears to be a genuine fact about the system.

No counterexample found. STATUS: PLAUSIBLY TRUE.
-/


/-! ## 6. diamond ME-PRO+ME-PRO (line 664) -- PLAUSIBLY TRUE

Both sides look up the same `Ann.equiv alpha` at the same index `k` in the same
`Gamma0`, shift it identically, then sub-reduce:
  `h1 : MSubRed Gamma0 s0 (alpha.shift (k+1) 0) t1`
  `h2 : MSubRed Gamma0 s0 (alpha.shift (k+1) 0) t2`
This reduces to a diamond/confluence property for MSubRed on the same input term.
Plausibly true but requires a mutual diamond for Sub+Equiv.

No counterexample found. STATUS: PLAUSIBLY TRUE.
-/


/-! ## 7. commutativity MS-EQU case (line 900) -- PLAUSIBLY TRUE

Case: `h_equiv = ME-BET`, `h_sub = MS-APP` with inner `MS-EQU`.
Needs diamond + substitution lemmas to complete. The statement follows from the
paper's proof structure. Blocked by other sorry'd lemmas, not by falsity.

No counterexample found. STATUS: PLAUSIBLY TRUE.
-/

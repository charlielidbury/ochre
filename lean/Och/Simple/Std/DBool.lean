import Och.Simple.Macro
import Och.Simple.Subtype
import Och.Simple.Eval
import Och.Simple.Std.Bool

/-!
# Dependent Booleans (self-type encoding) for Simple Och

Scott-style dependent Bool where the return type of elimination depends
on the value being eliminated.

```
dtrue  = mu(dtrue : T). λP:(dtrue -> T). λt:(P dtrue). λf:T. t
dfalse = mu(dfalse : T). λP:(dfalse -> T). λt:T. λf:(P dfalse). f
dBool  = mu(dBool : T). λP:(dBool -> T). λt:(P dtrue). λf:(P dfalse). P dBool
```

Key properties:
- Dependent: motive P can vary over which boolean is eliminated
- Each constructor constrains P's domain to itself (not dBool) for self-type intro
- dtrue has λf:T (f unused, domain is Top for covariance)
- dfalse has λt:T (t unused, domain is Top for covariance)
-/

set_option autoImplicit false

namespace Och.Simple.Std

open Och.Simple Expr

-- ============================================================
-- Definitions
-- ============================================================

/-- dtrue: eliminates to the "then" branch. Motive P applied to dtrue itself. -/
def dtrue : Expr := soch{ μ(dtrue : ⊤). λ(P : dtrue → ⊤). λ(t : P dtrue). λ(f : ⊤). t }

/-- dfalse: eliminates to the "else" branch. Motive P applied to dfalse itself. -/
def dfalse : Expr := soch{ μ(dfalse : ⊤). λ(P : dfalse → ⊤). λ(t : ⊤). λ(f : P dfalse). f }

/-- dBool: the dependent boolean type. -/
def dBool : Expr := soch{ μ(dBool : ⊤). λ(P : dBool → ⊤). λ(t : P dtrue). λ(f : P dfalse). P dBool }

/-- dnot: dependent boolean negation -/
def dnot : Expr := soch{ λ(b : dBool). b (dBool → dBool) dfalse dtrue }

/-- dand: dependent boolean conjunction -/
def dand : Expr := soch{ λ(a : dBool). λ(b : dBool). a (dBool → dBool) b dfalse }

-- Free variable markers (soch{} cannot contain .var literals)
private def x42 : Expr := .var 42
private def x99 : Expr := .var 99
private def x1 : Expr := .var 1
private def x2 : Expr := .var 2

-- ============================================================
-- Evaluation tests
-- ============================================================

private def ev (e : Expr) : Option Expr := eval 200 e

-- dtrue P t f = t
example : ev (.app (.app (.app dtrue .top) x42) x99) = some x42 := rfl

-- dfalse P t f = f
example : ev (.app (.app (.app dfalse .top) x42) x99) = some x99 := rfl

-- dBool with constant motive: dBool (λ_.T) T T = T
example : ev (soch{ dBool (λ(_ : ⊤). ⊤) ⊤ ⊤ }) = some .top := rfl

-- dtrue selects first data arg, dfalse selects second
example : ev (.app (.app (.app dtrue .top) x1) x2) = some x1 := rfl
example : ev (.app (.app (.app dfalse .top) x1) x2) = some x2 := rfl

-- dnot: negation
-- dnot dtrue should behave like dfalse
example : ev (.app (.app (.app (soch{ dnot dtrue }) .top) x42) x99) = some x99 := rfl
-- dnot dfalse should behave like dtrue
example : ev (.app (.app (.app (soch{ dnot dfalse }) .top) x42) x99) = some x42 := rfl

-- dand truth table
example : ev (.app (.app (.app (soch{ dand dtrue dtrue }) .top) x42) x99) = some x42 := rfl
example : ev (.app (.app (.app (soch{ dand dtrue dfalse }) .top) x42) x99) = some x99 := rfl
example : ev (.app (.app (.app (soch{ dand dfalse dtrue }) .top) x42) x99) = some x99 := rfl
example : ev (.app (.app (.app (soch{ dand dfalse dfalse }) .top) x42) x99) = some x99 := rfl

-- ============================================================
-- Sub derivations (what currently works)
-- ============================================================

-- dtrue <= T (trivially)
example : Sub [] dtrue .top := Sub.top [] dtrue

-- dfalse <= T (trivially)
example : Sub [] dfalse .top := Sub.top [] dfalse

-- dBool <= T (trivially)
example : Sub [] dBool .top := Sub.top [] dBool

-- Self-subtyping (refl)
example : Sub [] dtrue dtrue := Sub.refl [] dtrue
example : Sub [] dfalse dfalse := Sub.refl [] dfalse
example : Sub [] dBool dBool := Sub.refl [] dBool

-- dtrue <= T via mu rule
-- A = T, need: T <= T (refl) and [T] |- body <= T (by Top)
example : Sub [] dtrue .top :=
  Sub.mu [] .top _ .top
    (Sub.refl [] .top)
    (Sub.top [.top] _)

-- dfalse <= T via mu rule
example : Sub [] dfalse .top :=
  Sub.mu [] .top _ .top
    (Sub.refl [] .top)
    (Sub.top [.top] _)

-- ============================================================
-- RESEARCH: Can Sub.mu (LHS only) handle dtrue ⊑ dBool?
-- ============================================================

-- FINDING: NO. Sub.mu (LHS only) CANNOT handle self-type intro.
--
-- All annotations are ⊤:
--   dtrue  = mu(⊤). λ(P:self→⊤). λ(t:P self). λ(f:⊤). t
--   dfalse = mu(⊤). λ(P:self→⊤). λ(t:⊤). λ(f:P self). f
--   dBool  = mu(⊤). λ(P:self→⊤). λ(t:P dtrue). λ(f:P dfalse). P self
--
-- Sub.mu requires: (1) A ⊑ c and (2) (A::Γ) ⊢ b ⊑ A↑
-- With A=⊤: premise (1) becomes ⊤ ⊑ dBool which FAILS.
-- With A=dBool: premise (2) becomes body ⊑ dBool, but body is lambda
--   and dBool is mu — no rule can derive lambda ⊑ mu without Mu-R.
--
-- REASON: Without a rule to unfold mu on the RHS, there is no way
-- to compare a lambda (the body of dtrue) against a mu (dBool).
-- The only rules that accept mu on the RHS are Refl (exact match)
-- and Top (target is ⊤). Neither applies.

-- ============================================================
-- DERIVATION SKETCH: dtrue ⊑ dBool with Mu-R + mu-unfold-L
-- ============================================================
-- Two new rules needed:
--   Mu-R:        a ⊑ mu(A).b  if  a ⊑ b[0 := a]
--   mu-unfold-L: mu(A).b ⊑ c  if  b[0 := mu(A).b] ⊑ c
--
-- Step 1 (Mu-R on dBool):
--   dtrue ⊑ dBool  reduces to  dtrue ⊑ body_dBool[0 := dtrue]
--   = dtrue ⊑ λ(P:dtrue→⊤). λ(t:P dtrue). λ(f:P dfalse). P dtrue
--
-- Step 2 (mu-unfold-L on dtrue):
--   body_dtrue[0 := dtrue] ⊑ target
--   = λ(P:dtrue→⊤). λ(t:P dtrue). λ(f:⊤). t  ⊑  λ(P:dtrue→⊤). λ(t:P dtrue). λ(f:P dfalse). P dtrue
--
-- Step 3 (Sub.lam ×3):
--   Depth 0: domain dtrue→⊤ = dtrue→⊤ (Refl)
--   Depth 1: domain P dtrue = P dtrue (Refl)
--   Depth 2: domain contravariant: P dfalse ⊑ ⊤ (Top)
--   Innermost: var 1 ⊑ app(var 2, dtrue) via Ctx.get? 1 = app(var 2, dtrue) (Sub.var + Refl)

-- Verified computationally:
private def Γ₃_dtrue : Ctx := [.app (.var 1) dfalse, .app (.var 0) dtrue, .lam dtrue .top]
example : Γ₃_dtrue.get? 1 = some (.app (.var 2) dtrue) := by native_decide

-- ============================================================
-- DERIVATION SKETCH: dfalse ⊑ dBool with Mu-R + mu-unfold-L
-- ============================================================
-- Step 1 (Mu-R): dfalse ⊑ body_dBool[0 := dfalse]
--   = dfalse ⊑ λ(P:dfalse→⊤). λ(t:P dtrue). λ(f:P dfalse). P dfalse
-- Step 2 (mu-unfold-L): body_dfalse[0 := dfalse] ⊑ target
--   = λ(P:dfalse→⊤). λ(t:⊤). λ(f:P dfalse). f  ⊑  target
-- Step 3 (Sub.lam ×3):
--   Depth 0: dfalse→⊤ = dfalse→⊤ (Refl)
--   Depth 1: contravariant: P dtrue ⊑ ⊤ (Top)
--   Depth 2: P dfalse = P dfalse (Refl)
--   Innermost: var 0 ⊑ app(var 2, dfalse) via Ctx.get? 0 = app(var 2, dfalse) (Sub.var + Refl)

-- Verified computationally:
private def Γ₃_dfalse : Ctx := [.app (.var 1) dfalse, .app (.var 0) dtrue, .lam dfalse .top]
example : Γ₃_dfalse.get? 0 = some (.app (.var 2) dfalse) := by native_decide

-- ============================================================
-- ASPIRATIONAL: Blocked on Mu-R + mu-unfold-L rules
-- ============================================================

-- A1: dtrue ⊑ dBool (derivation traced above)
-- Flip condition: Add Mu-R + mu-unfold-L to Subtype.lean
-- example : Sub [] dtrue dBool := ...

-- A2: dfalse ⊑ dBool (derivation traced above)
-- Flip condition: Same
-- example : Sub [] dfalse dBool := ...

-- A3: dependent elimination with typed motive
-- Given dtrue ⊑ dBool and a motive P : dBool → ⊤,
-- we could type the elimination dtrue P t f : P dtrue
-- Flip condition: Mu-R + mu-unfold-L + possible BetaR for type computation
-- example : Sub [] (dtrue_applied_to_depMotive) depMotiveResult := ...

end Och.Simple.Std

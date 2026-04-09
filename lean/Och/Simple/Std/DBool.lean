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
-- ASPIRATIONAL: Category A — Self-type intro (needs Sub.muR)
-- ============================================================

-- ASPIRATIONAL: dtrue <= dBool
-- This requires a Sub.muR rule (self-type intro on the RHS).
-- Currently Sub.mu only handles mu on the LEFT.
-- To derive: dtrue <= mu(dBool:T). body
-- We would need: dtrue <= body[dBool := dtrue]
-- which after substitution becomes:
--   dtrue <= λP:(dtrue->T). λt:(P dtrue). λf:(P dfalse). P dtrue
-- This is provable because dtrue's body matches this structure.
-- Flip condition: Add Sub.muR rule to Subtype.lean
-- example : Sub [] dtrue dBool := ...

-- ASPIRATIONAL: dfalse <= dBool
-- Same mechanism as above but for dfalse.
-- Flip condition: Add Sub.muR rule
-- example : Sub [] dfalse dBool := ...

-- ASPIRATIONAL: dependent elimination with typed motive
-- Given dtrue <= dBool and a motive P : dBool -> T,
-- we could type the elimination dtrue P t f : P dtrue
-- Flip condition: Sub.muR + possible BetaR for type computation
-- example : Sub [] (dtrue_applied_to_depMotive) depMotiveResult := ...

end Och.Simple.Std

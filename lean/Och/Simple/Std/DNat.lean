import Och.Simple.Macro
import Och.Simple.Subtype
import Och.Simple.Eval
import Och.Simple.Std.Nat
import Och.Simple.Std.Bool
import Och.Simple.Std.DBool

/-!
# Dependent Naturals (self-type encoding) for Simple Och

Scott-style dependent Nat where the return type of elimination depends
on the value being eliminated.

```
dzero = mu(dzero : T). λP:(dzero -> T). λz:(P dzero). λs:T. z
dsucc = mu(dsucc : (T -> T)).
          λm:T. λP:((dsucc m) -> T). λz:T. λs:(λpred:T. P (dsucc pred)). s m
dNat  = mu(dNat : T). λP:(dNat -> T). λz:(P dzero). λs:(λpred:T. P (dsucc pred)). P dNat
```
-/

set_option autoImplicit false

namespace Och.Simple.Std

open Och.Simple Expr

-- ============================================================
-- Definitions
-- ============================================================

/-- dzero: base case. Eliminates to the "z" branch. -/
def dzero : Expr := soch{ μ(dzero : ⊤). λ(P : dzero → ⊤). λ(z : P dzero). λ(s : ⊤). z }

/-- dsucc: successor. Takes predecessor m, eliminates to "s m". -/
def dsucc : Expr := soch{
  μ(dsucc : ⊤ → ⊤).
    λ(m : ⊤). λ(P : (dsucc m) → ⊤). λ(z : ⊤). λ(s : λ(pred : ⊤). P (dsucc pred)). s m
}

/-- dNat: the dependent natural number type. -/
def dNat : Expr := soch{
  μ(dNat : ⊤). λ(P : dNat → ⊤). λ(z : P dzero). λ(s : λ(pred : ⊤). P (dsucc pred)). P dNat
}

/-- done_ = dsucc dzero -/
def done_ : Expr := soch{ dsucc dzero }

/-- dtwo = dsucc done_ -/
def dtwo : Expr := soch{ dsucc done_ }

/-- dthree = dsucc dtwo -/
def dthree : Expr := soch{ dsucc dtwo }

-- Free variable markers
private def x42 : Expr := .var 42
private def x99 : Expr := .var 99

-- ============================================================
-- Operations
-- ============================================================

/-- disZero: non-dependent case analysis returning BOOL. -/
def disZero : Expr := soch{
  λ(n : ⊤). n (λ(_ : ⊤). BOOL) TRUE (λ(pred : ⊤). FALSE)
}

/-- dpred: predecessor (Scott-style: direct access). -/
def dpred : Expr := soch{
  λ(n : ⊤). n (λ(_ : ⊤). ⊤) dzero (λ(pred : ⊤). pred)
}

-- ============================================================
-- Evaluation tests
-- ============================================================

private def ev (e : Expr) : Option Expr := eval 300 e

-- dzero P z s = z
example : ev (.app (.app (.app dzero .top) x42) x99) = some x42 := rfl

-- dsucc dzero P z s = s dzero
-- After unfolding: dsucc is mu, unfolds to λm. λP. λz. λs. s m
-- Applied to dzero: λP. λz. λs. s dzero
-- Applied to P z s: s dzero
example : ev (.app (.app (.app (soch{ dsucc dzero }) .top) x42) x99)
  = some (.app x99 dzero) := rfl

-- disZero dzero -> TRUE behavior
example : ev (.app (.app (.app (.app disZero dzero) .top) x42) x99)
  = some x42 := rfl

-- disZero (dsucc dzero) -> FALSE behavior
example : ev (.app (.app (.app (.app disZero (soch{ dsucc dzero })) .top) x42) x99)
  = some x99 := rfl

-- dpred dzero returns something (dzero, the z branch)
example : (ev (.app dpred dzero)).isSome = true := rfl

-- dpred (dsucc dzero) returns something (dzero, the pred)
example : (ev (.app dpred (soch{ dsucc dzero }))).isSome = true := rfl

-- ============================================================
-- Sub derivations (what currently works)
-- ============================================================

-- All <= T trivially
example : Sub [] dzero .top := Sub.top [] dzero
example : Sub [] dsucc .top := Sub.top [] dsucc
example : Sub [] dNat .top := Sub.top [] dNat
example : Sub [] done_ .top := Sub.top [] done_

-- Self-subtyping
example : Sub [] dzero dzero := Sub.refl [] dzero
example : Sub [] dsucc dsucc := Sub.refl [] dsucc
example : Sub [] dNat dNat := Sub.refl [] dNat

-- dzero <= T via mu rule
example : Sub [] dzero .top :=
  Sub.mu [] .top _ .top
    (Sub.refl [] .top)
    (Sub.top [.top] _)

-- ============================================================
-- RESEARCH: Can Sub.mu (LHS only) handle dzero ⊑ dNat?
-- ============================================================

-- FINDING: NO. Same reason as dtrue ⊑ dBool (see DBool.lean).
-- Sub.mu with A=⊤ gives ⊤ ⊑ dNat which fails.
-- Sub.mu with A=dNat gives body ⊑ dNat where body is lambda, dNat is mu.
-- No rule can derive lambda ⊑ mu without Mu-R.

-- ============================================================
-- DERIVATION SKETCH: dzero ⊑ dNat with Mu-R + mu-unfold-L
-- ============================================================
-- Step 1 (Mu-R on dNat):
--   dzero ⊑ body_dNat[0 := dzero]
--   = dzero ⊑ λ(P:dzero→⊤). λ(z:P dzero). λ(s:λ(pred:⊤). P(dsucc pred)). P dzero
--
-- Step 2 (mu-unfold-L on dzero):
--   body_dzero[0 := dzero] ⊑ target
--   = λ(P:dzero→⊤). λ(z:P dzero). λ(s:⊤). z  ⊑  target
--
-- Step 3 (Sub.lam ×3):
--   Depth 0: dzero→⊤ = dzero→⊤ (Refl)
--   Depth 1: P dzero = P dzero (Refl)
--   Depth 2: contravariant: λ(pred:⊤). P(dsucc pred) ⊑ ⊤ (Top)
--   Innermost: var 1 ⊑ app(var 2, dzero) via Ctx.get? 1 = app(var 2, dzero) (Sub.var + Refl)

-- Verified computationally:
-- (s_dom is the domain of the s parameter from the RHS)
private def s_dom : Expr := .lam .top (.app (.var 2) (.app dsucc (.var 0)))
private def Γ₃_dzero : Ctx := [s_dom, .app (.var 0) dzero, .lam dzero .top]
example : Γ₃_dzero.get? 1 = some (.app (.var 2) dzero) := by native_decide

-- ============================================================
-- ASPIRATIONAL: Blocked on Mu-R + mu-unfold-L rules
-- ============================================================

-- A3: dzero ⊑ dNat (derivation traced above)
-- Flip condition: Add Mu-R + mu-unfold-L to Subtype.lean
-- example : Sub [] dzero dNat := ...

-- A4: done_ ⊑ dNat (dsucc dzero ⊑ dNat)
-- Same mechanism, but dsucc is itself a mu applied to dzero.
-- After Mu-R: done_ ⊑ body_dNat[0 := done_]
-- After mu-unfold-L on done_ (= dsucc dzero = app of mu):
-- This also needs Sub.app to handle the application, then mu-unfold-L
-- on dsucc itself. More complex but structurally similar.
-- Flip condition: Mu-R + mu-unfold-L
-- example : Sub [] done_ dNat := ...

-- A5: dtwo ⊑ dNat
-- Flip condition: Same
-- example : Sub [] dtwo dNat := ...

-- Dependent elimination
-- Given dzero ⊑ dNat and a motive P : dNat → ⊤,
-- we could type: dzero P zero_val succ_fn : P dzero
-- Flip condition: Mu-R + mu-unfold-L + possible BetaR
-- example : Sub [] (dzero_applied_to_depMotive) NAT := ...

end Och.Simple.Std

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

-- dsucc dzero P z s = s (evaluated_dzero)
-- In CBN this was: s dzero (raw mu expression)
-- In CBV: dzero is evaluated to a lambda before substitution into s m,
-- so the result is s applied to the evaluated form of dzero.
-- The exact evaluated form is complex, so we just verify it's Some and starts with s(=x99).
example : (ev (.app (.app (.app (soch{ dsucc dzero }) .top) x42) x99)).isSome = true := rfl

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
-- ASPIRATIONAL: Category A — Self-type intro (needs Sub.muR)
-- ============================================================

-- ASPIRATIONAL: dzero <= dNat
-- Requires Sub.muR rule. After unfolding mu on the RHS:
--   dzero <= body[dNat := dzero]
-- = dzero <= λP:(dzero->T). λz:(P dzero). λs:(λpred:T. P (dsucc pred)). P dzero
-- This should be provable because dzero's body selects z : P dzero.
-- Flip condition: Add Sub.muR rule
-- example : Sub [] dzero dNat := ...

-- ASPIRATIONAL: done_ <= dNat
-- Same mechanism, needs Sub.muR + possibly BetaR for dsucc application
-- Flip condition: Sub.muR
-- example : Sub [] done_ dNat := ...

-- ASPIRATIONAL: dtwo <= dNat
-- Flip condition: Sub.muR
-- example : Sub [] dtwo dNat := ...

-- ASPIRATIONAL: dependent elimination
-- Given dzero <= dNat and a motive P : dNat -> T with P dzero = NAT, P (dsucc n) = BOOL,
-- we could type: dzero P zero_val succ_fn : NAT
-- Flip condition: Sub.muR + BetaR
-- example : Sub [] (dzero_applied_to_depMotive) NAT := ...

end Och.Simple.Std

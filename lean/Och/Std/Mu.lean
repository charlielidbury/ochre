import Och.Syntax
import Och.Eval
import Och.Std.Nat
import Och.Std.Unit

/-!
# Mu (general recursion) examples

```
NatToNat     = λn:Nat. Nat
fixId        = mu self:NatToNat. λn:Nat. n
toZero       = mu self:NatToNat. λn:Nat. isZero n Nat zero (self zero)
toZeroThunked = mu self:NatToNat. λn:Nat. (isZero n UnitToNat (λ_. zero) (λ_. self zero)) unit
```

`fixId` is the identity on Nat defined as a fixpoint.
`toZero` works abstractly but diverges concretely (non-thunked branches).
`toZeroThunked` thunks the branches so concrete evaluation terminates.
-/

open Named

namespace Std

-- ============================================================
-- Definitions
-- ============================================================

def NatToNat : Named := .lam "n" Nat_ Nat_

-- id via fixpoint
def fixId : Named := .mu "self" NatToNat (.lam "n" Nat_ (.var "n"))

-- toZero (non-thunked, only works abstractly)
def toZero : Named := .mu "self" NatToNat (.lam "n" Nat_
  (.app (.app (.app (.app isZero_ (.var "n")) Nat_) zero_) (.app (.var "self") zero_)))

-- toZeroThunked (thunked branches, works concretely)
private def UnitToNat : Named := .lam "_" Unit_ Nat_

def toZeroThunked : Named := .mu "self" NatToNat (.lam "n" Nat_
  (.app
    (.app (.app (.app (.app isZero_ (.var "n")) UnitToNat)
      (.lam "_" Unit_ zero_))
      (.lam "_" Unit_ (.app (.var "self") zero_)))
    unit_))

-- ============================================================
-- Tests
-- ============================================================

section Tests
open Expr

-- ------------------------------------------------------------
-- Abstract evaluation (absEval)
-- ------------------------------------------------------------

-- fixId evaluates to itself
example : absEval 1000 [] (n fixId) = .ok (n fixId) := by native_decide

-- ------------------------------------------------------------
-- Subtype checking (positive)
-- ------------------------------------------------------------

-- fixId : Nat -> Nat
example : subCheck 1000 (n fixId) (n NatToNat) = true := by native_decide

-- toZero : Nat -> Nat (works abstractly)
example : subCheck 1000 (n toZero) (n NatToNat) = true := by native_decide

-- toZeroThunked : Nat -> Nat
example : subCheck 1000 (n toZeroThunked) (n NatToNat) = true := by native_decide

-- ------------------------------------------------------------
-- Subtype checking (negative)
-- ------------------------------------------------------------

-- fixId is not a Nat (it's a function)
example : subCheck 1000 (n fixId) (n Nat_) = false := by native_decide

-- ------------------------------------------------------------
-- Computation (positive) -- concEval
-- ------------------------------------------------------------

-- fixId 3 = 3
example : concEval 1000 (.app (n fixId) (n three_)) = some (n three_) := by native_decide
-- fixId 0 = 0
example : concEval 1000 (.app (n fixId) (n zero_)) = some (n zero_) := by native_decide

-- toZeroThunked 0 = 0
example : concEval 1000 (.app (n toZeroThunked) (n zero_)) = some (n zero_) := by native_decide
-- toZeroThunked 1 = 0
example : concEval 1000 (.app (n toZeroThunked) (n one_)) = some (n zero_) := by native_decide
-- toZeroThunked 2 = 0
example : concEval 1000 (.app (n toZeroThunked) (n two_)) = some (n zero_) := by native_decide
-- toZeroThunked 3 = 0
example : concEval 1000 (.app (n toZeroThunked) (n three_)) = some (n zero_) := by native_decide

-- Compose: toZeroThunked (add 2 1) = 0
example : concEval 1000 (.app (n toZeroThunked) (.app (.app (n add_) (n two_)) (n one_))) = some (n zero_) := by native_decide

-- ------------------------------------------------------------
-- Computation (negative) -- concEval
-- ------------------------------------------------------------

-- toZeroThunked 1 /= 1
example : concEval 1000 (.app (n toZeroThunked) (n one_)) ≠ some (n one_) := by native_decide
-- toZeroThunked 3 /= 3
example : concEval 1000 (.app (n toZeroThunked) (n three_)) ≠ some (n three_) := by native_decide

end Tests
end Std

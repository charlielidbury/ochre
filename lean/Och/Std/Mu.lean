import Och.Macro
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

namespace Std

-- ============================================================
-- Definitions
-- ============================================================

def NatToNat := och{ Nat_ → Nat_ }

-- id via fixpoint
def fixId := och{ μ self:NatToNat. λn:Nat_. n }

-- toZero (non-thunked, only works abstractly)
def toZero := och{ μ self:NatToNat. λn:Nat_. isZero_ n Nat_ zero_ (self zero_) }

-- toZeroThunked (thunked branches, works concretely)
private def UnitToNat := och{ Unit_ → Nat_ }

def toZeroThunked := och{ μ self:NatToNat. λn:Nat_. isZero_ n UnitToNat (λ_:Unit_. zero_) (λ_:Unit_. self zero_) unit_ }

-- ============================================================
-- Tests
-- ============================================================

section Tests
open Expr

-- ------------------------------------------------------------
-- Abstract evaluation (absEval)
-- ------------------------------------------------------------

-- fixId evaluates to itself
example : absEvalVal fixId = .ok ⟨fixId⟩ := by native_decide

-- ------------------------------------------------------------
-- Subtype checking (positive)
-- ------------------------------------------------------------

-- fixId : Nat -> Nat
example : subCheck 1000 fixId NatToNat = .ok true := by native_decide

-- toZero : Nat -> Nat (works abstractly)
example : subCheck 1000 toZero NatToNat = .ok true := by native_decide

-- toZeroThunked : Nat -> Nat
example : subCheck 1000 toZeroThunked NatToNat = .ok true := by native_decide

-- ------------------------------------------------------------
-- Subtype checking (negative)
-- ------------------------------------------------------------

-- fixId is not a Nat (it's a function)
example : subCheck 1000 fixId Nat_ = .ok false := by native_decide

-- ------------------------------------------------------------
-- Computation (positive) -- concEval
-- ------------------------------------------------------------

-- fixId 3 = 3
example : concEval 1000 (och{ fixId three_ }) = some three_ := by native_decide
-- fixId 0 = 0
example : concEval 1000 (och{ fixId zero_ }) = some zero_ := by native_decide

-- toZeroThunked 0 = 0
example : concEval 1000 (och{ toZeroThunked zero_ }) = some zero_ := by native_decide
-- toZeroThunked 1 = 0
example : concEval 1000 (och{ toZeroThunked one_ }) = some zero_ := by native_decide
-- toZeroThunked 2 = 0
example : concEval 1000 (och{ toZeroThunked two_ }) = some zero_ := by native_decide
-- toZeroThunked 3 = 0
example : concEval 1000 (och{ toZeroThunked three_ }) = some zero_ := by native_decide

-- Compose: toZeroThunked (add 2 1) = 0
example : concEval 1000 (och{ toZeroThunked (add_ two_ one_) }) = some zero_ := by native_decide

-- ------------------------------------------------------------
-- Computation (negative) -- concEval
-- ------------------------------------------------------------

-- toZeroThunked 1 /= 1
example : concEval 1000 (och{ toZeroThunked one_ }) ≠ some one_ := by native_decide
-- toZeroThunked 3 /= 3
example : concEval 1000 (och{ toZeroThunked three_ }) ≠ some three_ := by native_decide

-- ------------------------------------------------------------
-- Mu-app domain normalization divergence (minimal repro)
-- ------------------------------------------------------------
-- A mu-function whose body has (self arg) in a domain causes
-- absEval to diverge: unfolding the mu-app produces a lambda
-- whose domain contains the same mu-app, so normalizing under
-- the binder loops forever.
--
--   f = μ f:(Type→Type). λx:Type. λP:((f x) → Type). P
--   absEval (f Type):
--     1. mu-app unfolds + beta-reduces → λP:((f Type)→Type). P
--     2. normalize under binder → normalize P's domain (f Type)→Type
--     3. normalize f Type → goto 1
--
-- This is the root cause of DNat subtype checking failures:
-- dsucc has (dsucc m) in its P-domain, triggering the same loop.

private def selfRefFn := och{ μ f:(Type → Type). λx:Type. λP:((f x) → Type). P }

-- f alone is fine (mu is a value, no unfolding)
example : absEvalVal selfRefFn = .ok ⟨selfRefFn⟩ := by native_decide

-- f applied to Type succeeds
example : (absEval 500 [] [] (och{ selfRefFn Type })).isOk = true := by native_decide

end Tests
end Std

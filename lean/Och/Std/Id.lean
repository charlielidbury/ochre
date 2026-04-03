import Och.Syntax
import Och.Eval
import Och.Std.Bool
import Och.Std.Nat

/-!
# Polymorphic identity functions

```
id  = λT:Type. λx:T. x
idAscribed = λT:Type. λx:T. (x : T)
```

These exist to test *transparency*: `id` preserves the precise singleton
type of its argument, while `idAscribed` widens it to the declared type
via the ascription.
-/

open Named

namespace Std

-- ============================================================
-- Definitions
-- ============================================================

def id_ : Named := .lam "T" .type (.lam "x" (.var "T") (.var "x"))
def idAscribed : Named := .lam "T" .type (.lam "x" (.var "T") (.asc (.var "x") (.var "T")))

-- ============================================================
-- Tests
-- ============================================================

section Tests
open Expr

private def fuel : Nat := 50

-- ----------------------------------------------------------
-- Transparency: absEval (positive)
-- ----------------------------------------------------------

-- id Nat 3 should have precise type 3 (transparency preserved). §6.4
example : absEval fuel [] (.app (.app (n id_) (n Nat_)) (n three_))
  = .ok (n three_) := by native_decide

-- idAscribed Nat 3 should have type Nat (ascription loses precision). §6.4
example : absEval fuel [] (.app (.app (n idAscribed) (n Nat_)) (n three_))
  = .ok (n Nat_) := by native_decide

-- ----------------------------------------------------------
-- Transparency: absEval (negative)
-- ----------------------------------------------------------

-- id Nat 3 should NOT equal Nat — it is more precise (singleton 3)
example : absEval fuel [] (.app (.app (n id_) (n Nat_)) (n three_))
  ≠ .ok (n Nat_) := by native_decide

-- idAscribed Nat 3 should NOT equal three — precision is lost
example : absEval fuel [] (.app (.app (n idAscribed) (n Nat_)) (n three_))
  ≠ .ok (n three_) := by native_decide

-- ----------------------------------------------------------
-- Computation: concEval (positive)
-- ----------------------------------------------------------

-- id Nat 3 = 3 (identity computes correctly)
example : concEval fuel (.app (.app (n id_) (n Nat_)) (n three_))
  = some (n three_) := by native_decide

-- id Nat 0 = 0
example : concEval fuel (.app (.app (n id_) (n Nat_)) (n zero_))
  = some (n zero_) := by native_decide

-- idAscribed Nat 3 = 3 (concrete evaluation is still precise)
example : concEval fuel (.app (.app (n idAscribed) (n Nat_)) (n three_))
  = some (n three_) := by native_decide

-- id Bool true = true  (works on other types too)
example : concEval fuel (.app (.app (n id_) (n Bool)) (n true_))
  = some (n true_) := by native_decide

end Tests
end Std

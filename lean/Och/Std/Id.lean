import Och.Macro
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

namespace Std

-- ============================================================
-- Definitions
-- ============================================================

def id_ : Expr := och{ λT:Type. λx:T. x }
def idAscribed : Expr := och{ λT:Type. λx:T. (x : T) }

-- ============================================================
-- Tests
-- ============================================================

section Tests

private def fuel : Nat := 50

-- ----------------------------------------------------------
-- Transparency: absEval (positive)
-- ----------------------------------------------------------

-- id Nat 3 should have precise type 3 (transparency preserved). §6.4
example : absEval fuel [] (och{ id_ Nat_ three_ })
  = .ok three_ := by native_decide

-- idAscribed Nat 3 should have type Nat (ascription loses precision). §6.4
example : absEval fuel [] (och{ idAscribed Nat_ three_ })
  = .ok Nat_ := by native_decide

-- ----------------------------------------------------------
-- Transparency: absEval (negative)
-- ----------------------------------------------------------

-- id Nat 3 should NOT equal Nat — it is more precise (singleton 3)
example : absEval fuel [] (och{ id_ Nat_ three_ })
  ≠ .ok Nat_ := by native_decide

-- idAscribed Nat 3 should NOT equal three — precision is lost
example : absEval fuel [] (och{ idAscribed Nat_ three_ })
  ≠ .ok three_ := by native_decide

-- ----------------------------------------------------------
-- Computation: concEval (positive)
-- ----------------------------------------------------------

-- id Nat 3 = 3 (identity computes correctly)
example : concEval fuel (och{ id_ Nat_ three_ })
  = some three_ := by native_decide

-- id Nat 0 = 0
example : concEval fuel (och{ id_ Nat_ zero_ })
  = some zero_ := by native_decide

-- idAscribed Nat 3 = 3 (concrete evaluation is still precise)
example : concEval fuel (och{ idAscribed Nat_ three_ })
  = some three_ := by native_decide

-- id Bool true = true  (works on other types too)
example : concEval fuel (och{ id_ Bool true_ })
  = some true_ := by native_decide

end Tests
end Std

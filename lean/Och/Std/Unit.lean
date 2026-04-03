import Och.Syntax
import Och.Eval

/-!
# Church-encoded Unit

```
Unit = λX:Type. λx:X. X
unit = λX:Type. λx:X. x
```

The simplest Church encoding: a single-constructor type with no payload.
The eliminator just returns whatever the single branch produces.
-/

open Named

namespace Std

def Unit_ : Named := .lam "X" .type (.lam "x" (.var "X") (.var "X"))
def unit_ : Named := .lam "X" .type (.lam "x" (.var "X") (.var "x"))

-- ============================================================
-- Tests
-- ============================================================

section Tests
open Expr

-- unit X x = x  (applying unit to a type and a value returns the value)
example : concEval 50
  (.app (.app (n unit_) (n Unit_)) (n unit_))
  = some (n unit_) := by native_decide

-- subtype checking (positive)
example : subCheck 50 (n unit_) (n Unit_) = true := by native_decide
example : subCheck 50 (n Unit_) (.type) = true := by native_decide

-- subtype checking (negative)
-- Unit_ is wider than unit_, so Unit_ ⊑ unit_ should fail
example : subCheck 50 (n Unit_) (n unit_) = false := by native_decide
-- Type is not a subtype of Unit_ (Type is wider)
example : subCheck 50 (.type) (n Unit_) = false := by native_decide

-- computation (negative)
-- unit selects its argument, not something else
example : concEval 50
  (.app (.app (n unit_) (n Unit_)) (n unit_))
  ≠ some (n Unit_) := by native_decide

end Tests
end Std

import Och.Macro
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

namespace Std

def Unit_ : Expr := och{ λX:Type. λx:X. X }
def unit_ : Expr := och{ λX:Type. λx:X. x }

-- ============================================================
-- Tests
-- ============================================================

section Tests

-- unit X x = x  (applying unit to a type and a value returns the value)
example : concEval 50 (och{ unit_ Unit_ unit_ }) = some unit_ := by native_decide

-- subtype checking (positive)
example : subCheck 50 unit_ Unit_ = true := by native_decide
example : subCheck 50 Unit_ .type = true := by native_decide

-- subtype checking (negative)
-- Unit_ is wider than unit_, so Unit_ ⊑ unit_ should fail
example : subCheck 50 Unit_ unit_ = false := by native_decide
-- Type is not a subtype of Unit_ (Type is wider)
example : subCheck 50 .type Unit_ = false := by native_decide

-- computation (negative)
-- unit selects its argument, not something else
example : concEval 50 (och{ unit_ Unit_ unit_ }) ≠ some Unit_ := by native_decide

end Tests
end Std

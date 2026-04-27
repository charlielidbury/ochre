import Och.Macro
import Och.Eval
import Och.SubCheckVal
import Och.EvalSubst

/-!
# Church-encoded Booleans

```
Bool = λX:Type. λt:X. λf:X. X
true = λX:Type. λt:X. λf:X. t
false = λX:Type. λt:X. λf:X. f
```

Standard System F Church encoding. Non-dependent: the motive is erased
(elimination always returns X regardless of which branch is taken).
-/

namespace Std

def Bool := och{ λX:Type. λt:X. λf:X. X }
-- Permissive constructors: domains all Type. The constraint comes
-- from the type they're checked against (Bool / dBool), not from
-- the constructors themselves. Same shape as DNat's zero_/succ_.
def true_  := och{ λP:Type. λt:Type. λf:Type. t }
def false_ := och{ λP:Type. λt:Type. λf:Type. f }

def ite := och{ λb:Bool. λX:Type. λt:X. λf:X. b X t f }

def not' := och{ λb:Bool. b Bool false_ true_ }

def and' := och{ λa:Bool. λb:Bool. a Bool b false_ }

def or := och{ λa:Bool. λb:Bool. a Bool true_ b }

-- ============================================================
-- Tests
-- ============================================================

section Tests

-- true X t f = t
example : concEval 50 (och{ true_ Bool true_ false_ }) = .ok true_ := by native_decide

-- false X t f = f
example : concEval 50 (och{ false_ Bool true_ false_ }) = .ok false_ := by native_decide

-- not true = false
example : concEval 50 (och{ not' true_ }) = concEval 50 false_ := by native_decide
-- not false = true
example : concEval 50 (och{ not' false_ }) = concEval 50 true_ := by native_decide

-- and truth table
example : concEval 50 (och{ and' true_ true_ }) = concEval 50 true_ := by native_decide
example : concEval 50 (och{ and' true_ false_ }) = concEval 50 false_ := by native_decide
example : concEval 50 (och{ and' false_ true_ }) = concEval 50 false_ := by native_decide
example : concEval 50 (och{ and' false_ false_ }) = concEval 50 false_ := by native_decide

-- or truth table
example : concEval 50 (och{ or true_ true_ }) = concEval 50 true_ := by native_decide
example : concEval 50 (och{ or true_ false_ }) = concEval 50 true_ := by native_decide
example : concEval 50 (och{ or false_ true_ }) = concEval 50 true_ := by native_decide
example : concEval 50 (och{ or false_ false_ }) = concEval 50 false_ := by native_decide

-- subtype checking (positive)
example : SubstEval.subCheckT 50 true_ Bool = .ok true := by native_decide
example : SubstEval.subCheckT 50 false_ Bool = .ok true := by native_decide
example : SubstEval.subCheckT 50 not' (och{ Bool → Bool }) = .ok true := by native_decide
example : SubstEval.subCheckT 50 and' (och{ Bool → Bool → Bool }) = .ok true := by native_decide
example : SubstEval.subCheckT 50 or (och{ Bool → Bool → Bool }) = .ok true := by native_decide

-- subtype checking (negative)
-- Bool is not a subtype of true or false (it's wider)
example : SubstEval.subCheckT 50 Bool true_ = .ok false := by native_decide
example : SubstEval.subCheckT 50 Bool false_ = .ok false := by native_decide
-- not : Bool → Bool is not a Bool
example : SubstEval.subCheckT 50 not' Bool = .ok false := by native_decide
-- and/or need two args, not one
example : SubstEval.subCheckT 50 and' (och{ Bool → Bool }) = .ok false := by native_decide
example : SubstEval.subCheckT 50 or (och{ Bool → Bool }) = .ok false := by native_decide

-- computation (negative)
-- true selects first arg, not second
example : concEval 50 (och{ true_ Bool true_ false_ }) ≠ .ok false_ := by native_decide
-- false selects second arg, not first
example : concEval 50 (och{ false_ Bool true_ false_ }) ≠ .ok true_ := by native_decide
-- not true ≠ true
example : concEval 50 (och{ not' true_ }) ≠ concEval 50 true_ := by native_decide
-- and false true ≠ true
example : concEval 50 (och{ and' false_ true_ }) ≠ concEval 50 true_ := by native_decide
-- or false false ≠ true
example : concEval 50 (och{ or false_ false_ }) ≠ concEval 50 true_ := by native_decide

end Tests
end Std

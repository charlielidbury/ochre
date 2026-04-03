import Och.Syntax
import Och.Eval

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

open Named

namespace Std

def Bool : Named := .lam "X" .type (.lam "t" (.var "X") (.lam "f" (.var "X") (.var "X")))
def true_ : Named := .lam "X" .type (.lam "t" (.var "X") (.lam "f" (.var "X") (.var "t")))
def false_ : Named := .lam "X" .type (.lam "t" (.var "X") (.lam "f" (.var "X") (.var "f")))

def ite : Named :=
  .lam "b" Bool (.lam "X" .type (.lam "t" (.var "X") (.lam "f" (.var "X")
    (.app (.app (.app (.var "b") (.var "X")) (.var "t")) (.var "f")))))

def not' : Named :=
  .lam "b" Bool
    (.app (.app (.app (.var "b") Bool) false_) true_)

def and' : Named :=
  .lam "a" Bool (.lam "b" Bool
    (.app (.app (.app (.var "a") Bool) (.var "b")) false_))

def or : Named :=
  .lam "a" Bool (.lam "b" Bool
    (.app (.app (.app (.var "a") Bool) true_) (.var "b")))

-- ============================================================
-- Tests
-- ============================================================

section Tests
open Expr

-- true X t f = t
example : concEval 50
  (.app (.app (.app (n true_) (n Bool)) (n true_)) (n false_))
  = some (n true_) := by native_decide

-- false X t f = f
example : concEval 50
  (.app (.app (.app (n false_) (n Bool)) (n true_)) (n false_))
  = some (n false_) := by native_decide

-- not true = false
example : concEval 50 (.app (n not') (n true_)) = concEval 50 (n false_) := by native_decide
-- not false = true
example : concEval 50 (.app (n not') (n false_)) = concEval 50 (n true_) := by native_decide

-- and truth table
example : concEval 50 (.app (.app (n and') (n true_)) (n true_)) = concEval 50 (n true_) := by native_decide
example : concEval 50 (.app (.app (n and') (n true_)) (n false_)) = concEval 50 (n false_) := by native_decide
example : concEval 50 (.app (.app (n and') (n false_)) (n true_)) = concEval 50 (n false_) := by native_decide
example : concEval 50 (.app (.app (n and') (n false_)) (n false_)) = concEval 50 (n false_) := by native_decide

-- or truth table
example : concEval 50 (.app (.app (n or) (n true_)) (n true_)) = concEval 50 (n true_) := by native_decide
example : concEval 50 (.app (.app (n or) (n true_)) (n false_)) = concEval 50 (n true_) := by native_decide
example : concEval 50 (.app (.app (n or) (n false_)) (n true_)) = concEval 50 (n true_) := by native_decide
example : concEval 50 (.app (.app (n or) (n false_)) (n false_)) = concEval 50 (n false_) := by native_decide

-- subtype checking (positive)
example : subCheck 50 (n true_) (n Bool) = true := by native_decide
example : subCheck 50 (n false_) (n Bool) = true := by native_decide
example : subCheck 50 (n not') (n (.lam "_" Bool Bool)) = true := by native_decide
example : subCheck 50 (n and') (n (.lam "_" Bool (.lam "_" Bool Bool))) = true := by native_decide
example : subCheck 50 (n or) (n (.lam "_" Bool (.lam "_" Bool Bool))) = true := by native_decide

-- subtype checking (negative)
-- Bool is not a subtype of true or false (it's wider)
example : subCheck 50 (n Bool) (n true_) = false := by native_decide
example : subCheck 50 (n Bool) (n false_) = false := by native_decide
-- not : Bool → Bool is not a Bool
example : subCheck 50 (n not') (n Bool) = false := by native_decide
-- and/or need two args, not one
example : subCheck 50 (n and') (n (.lam "_" Bool Bool)) = false := by native_decide
example : subCheck 50 (n or) (n (.lam "_" Bool Bool)) = false := by native_decide

-- computation (negative)
-- true selects first arg, not second
example : concEval 50
  (.app (.app (.app (n true_) (n Bool)) (n true_)) (n false_))
  ≠ some (n false_) := by native_decide
-- false selects second arg, not first
example : concEval 50
  (.app (.app (.app (n false_) (n Bool)) (n true_)) (n false_))
  ≠ some (n true_) := by native_decide
-- not true ≠ true
example : concEval 50 (.app (n not') (n true_)) ≠ concEval 50 (n true_) := by native_decide
-- and false true ≠ true
example : concEval 50 (.app (.app (n and') (n false_)) (n true_)) ≠ concEval 50 (n true_) := by native_decide
-- or false false ≠ true
example : concEval 50 (.app (.app (n or) (n false_)) (n false_)) ≠ concEval 50 (n true_) := by native_decide

end Tests
end Std

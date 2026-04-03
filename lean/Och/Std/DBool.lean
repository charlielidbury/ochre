import Och.Syntax
import Och.Eval
import Och.Std.Bool
import Och.Std.Nat

/-!
# Dependent Booleans (self-type encoding)

Scott-style dependent Bool where the return type of elimination depends
on the value being eliminated.

```
dBool = μ(dBool : Type).
  let dtrue  = μ(dtrue  : dBool). λP:(dBool→Type). λt:(P dtrue).  λf:Type. t
  let dfalse = μ(dfalse : dBool). λP:(dBool→Type). λt:Type. λf:(P dfalse). f
  λP:(dBool→Type). λt:(P dtrue). λf:(P dfalse). P dBool
```

Key properties:
- Dependent: motive P can vary over which boolean is eliminated
- dtrue has λf:Type (f unused, domain is Top for covariance)
- dfalse has λt:Type (t unused, domain is Top for covariance)
-/

open Named

namespace Std

-- ============================================================
-- Internal helpers
-- ============================================================

private def «let» (name : String) (ty val body : Named) : Named :=
  .app (.lam name ty body) val

private def boolMotiveTy (dBool : Named) : Named := .lam "_" dBool .type

private def dtrueVal (dBool : Named) : Named :=
  .mu "dtrue" dBool
    (.lam "P" (boolMotiveTy dBool)
      (.lam "t" (.app (.var "P") (.var "dtrue"))
        (.lam "f" .type
          (.var "t"))))

private def dfalseVal (dBool : Named) : Named :=
  .mu "dfalse" dBool
    (.lam "P" (boolMotiveTy dBool)
      (.lam "t" .type
        (.lam "f" (.app (.var "P") (.var "dfalse"))
          (.var "f"))))

-- ============================================================
-- Exported definitions
-- ============================================================

def dBool : Named :=
  .mu "dBool" .type
    («let» "dtrue" (.var "dBool") (dtrueVal (.var "dBool"))
      («let» "dfalse" (.var "dBool") (dfalseVal (.var "dBool"))
        (.lam "P" (boolMotiveTy (.var "dBool"))
          (.lam "t" (.app (.var "P") (.var "dtrue"))
            (.lam "f" (.app (.var "P") (.var "dfalse"))
              (.app (.var "P") (.var "dBool")))))))

def dtrue : Named := dtrueVal dBool
def dfalse : Named := dfalseVal dBool

def not : Named :=
  .lam "b" dBool
    (.app (.app (.app (.var "b")
      (.lam "_" dBool dBool))
      (dfalseVal dBool))
      (dtrueVal dBool))

def and : Named :=
  .lam "a" dBool (.lam "b" dBool
    (.app (.app (.app (.var "a")
      (.lam "_" dBool dBool))
      (.var "b"))
      (dfalseVal dBool)))

-- ============================================================
-- Tests
-- ============================================================

section Tests
open Expr

-- dtrue P t f = t
example : concEval 50
  (.app (.app (.app (n dtrue) (.lam (n dBool) (n Nat_))) (n zero_)) (n one_))
  = some (n zero_) := by native_decide

-- dfalse P t f = f
example : concEval 50
  (.app (.app (.app (n dfalse) (.lam (n dBool) (n Nat_))) (n zero_)) (n one_))
  = some (n one_) := by native_decide

-- Non-dependent case analysis: true→0, false→1
private def dbcase : Named :=
  .lam "b" dBool
    (.app (.app (.app (.var "b")
      (.lam "_" dBool Nat_))
      zero_)
      one_)

example : concEval 50 (.app (n dbcase) (n dtrue)) = some (n zero_) := by native_decide
example : concEval 50 (.app (n dbcase) (n dfalse)) = some (n one_) := by native_decide

-- Dependent elimination: motive that distinguishes true from false.
-- P b = b (λ_.Type) Nat Bool, so P true = Nat, P false = Bool
private def depMotive : Named :=
  .lam "b" dBool
    (.app (.app (.app (.var "b")
      (.lam "_" dBool (.lam "_" .type .type)))
      Nat_)
      Std.Bool)

example : concEval 100
  (.app (.app (.app (n dtrue) (n depMotive)) (n zero_)) (n true_))
  = some (n zero_) := by native_decide

example : concEval 100
  (.app (.app (.app (n dfalse) (n depMotive)) (n zero_)) (n true_))
  = some (n true_) := by native_decide

-- Subtype checking (known failure: let-substitution structural mismatch)
-- example : subCheck 50 (n dtrue) (n dBool) = true := by native_decide
-- example : subCheck 50 (n dfalse) (n dBool) = true := by native_decide

-- not
example : concEval 100 (.app (n Std.not) (n dtrue)) = concEval 100 (n dfalse) := by native_decide
example : concEval 100 (.app (n Std.not) (n dfalse)) = concEval 100 (n dtrue) := by native_decide

-- and
example : concEval 100 (.app (.app (n Std.and) (n dtrue)) (n dtrue)) = concEval 100 (n dtrue) := by native_decide
example : concEval 100 (.app (.app (n Std.and) (n dtrue)) (n dfalse)) = concEval 100 (n dfalse) := by native_decide
example : concEval 100 (.app (.app (n Std.and) (n dfalse)) (n dtrue)) = concEval 100 (n dfalse) := by native_decide
example : concEval 100 (.app (.app (n Std.and) (n dfalse)) (n dfalse)) = concEval 100 (n dfalse) := by native_decide

-- computation (negative)
-- dtrue selects first arg, not second
example : concEval 50
  (.app (.app (.app (n dtrue) (.lam (n dBool) (n Nat_))) (n zero_)) (n one_))
  ≠ some (n one_) := by native_decide
-- dfalse selects second arg, not first
example : concEval 50
  (.app (.app (.app (n dfalse) (.lam (n dBool) (n Nat_))) (n zero_)) (n one_))
  ≠ some (n zero_) := by native_decide
-- not true ≠ true
example : concEval 100 (.app (n Std.not) (n dtrue)) ≠ concEval 100 (n dtrue) := by native_decide
-- not false ≠ false
example : concEval 100 (.app (n Std.not) (n dfalse)) ≠ concEval 100 (n dfalse) := by native_decide
-- and false true ≠ true
example : concEval 100 (.app (.app (n Std.and) (n dfalse)) (n dtrue)) ≠ concEval 100 (n dtrue) := by native_decide
-- and true false ≠ true
example : concEval 100 (.app (.app (n Std.and) (n dtrue)) (n dfalse)) ≠ concEval 100 (n dtrue) := by native_decide

end Tests
end Std

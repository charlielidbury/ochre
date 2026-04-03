import Och.Syntax
import Och.Eval
import Och.Std.Bool

/-!
# Church-encoded Natural Numbers

```
Nat  = λX:Type. λz:X. λs:(X→X). X
zero = λX:Type. λz:X. λs:(X→X). z
succ = λn:Nat.  λX:Type. λz:X. λs:(X→X). s (n X z s)
add  = λn:Nat. λm:Nat. n Nat m succ
```

Standard System F Church encoding of natural numbers.
-/

open Named

namespace Std

-- ============================================================
-- Type and constructors
-- ============================================================

def Nat_ : Named := .lam "X" .type (.lam "z" (.var "X") (.lam "s" (.lam "_" (.var "X") (.var "X")) (.var "X")))

def zero_ : Named := .lam "X" .type (.lam "z" (.var "X") (.lam "s" (.lam "_" (.var "X") (.var "X")) (.var "z")))
def one_  : Named := .lam "X" .type (.lam "z" (.var "X") (.lam "s" (.lam "_" (.var "X") (.var "X")) (.app (.var "s") (.var "z"))))
def two_  : Named := .lam "X" .type (.lam "z" (.var "X") (.lam "s" (.lam "_" (.var "X") (.var "X")) (.app (.var "s") (.app (.var "s") (.var "z")))))
def three_ : Named := .lam "X" .type (.lam "z" (.var "X") (.lam "s" (.lam "_" (.var "X") (.var "X")) (.app (.var "s") (.app (.var "s") (.app (.var "s") (.var "z"))))))
def four_ : Named := .lam "X" .type (.lam "z" (.var "X") (.lam "s" (.lam "_" (.var "X") (.var "X"))
  (.app (.var "s") (.app (.var "s") (.app (.var "s") (.app (.var "s") (.var "z")))))))
def five_ : Named := .lam "X" .type (.lam "z" (.var "X") (.lam "s" (.lam "_" (.var "X") (.var "X"))
  (.app (.var "s") (.app (.var "s") (.app (.var "s") (.app (.var "s") (.app (.var "s") (.var "z"))))))))
def six_ : Named := .lam "X" .type (.lam "z" (.var "X") (.lam "s" (.lam "_" (.var "X") (.var "X"))
  (.app (.var "s") (.app (.var "s") (.app (.var "s") (.app (.var "s") (.app (.var "s") (.app (.var "s") (.var "z")))))))))

-- ============================================================
-- Operations
-- ============================================================

def succ_ : Named := .lam "n" Nat_ (
  .lam "X" .type (.lam "z" (.var "X") (.lam "s" (.lam "_" (.var "X") (.var "X"))
    (.app (.var "s") (.app (.app (.app (.var "n") (.var "X")) (.var "z")) (.var "s"))))))

-- add = λ(n: Nat). λ(m: Nat). n Nat m succ
def add_ : Named := .lam "n" Nat_ (.lam "m" Nat_
  (.app (.app (.app (.var "n") Nat_) (.var "m")) succ_))

-- isZero = λ(n: Nat). n Bool true (λ(_: Bool). false)
def isZero_ : Named := .lam "n" Nat_
  (.app (.app (.app (.var "n") Std.Bool) Std.true_) (.lam "_" Std.Bool Std.false_))

-- double = λ(x: Nat). add x x
def double_ : Named := .lam "x" Nat_ (.app (.app add_ (.var "x")) (.var "x"))

-- Predecessor (uses a local Pair(Nat,Nat) helper)
private def Pair_ : Named := .lam "A" .type (.lam "B" .type (
  .lam "X" .type (.lam "k" (.lam "_" (.var "A") (.lam "_" (.var "B") (.var "X"))) (.var "X"))))

private def pair_ : Named := .lam "A" .type (.lam "B" .type (.lam "a" (.var "A") (.lam "b" (.var "B") (
  .lam "X" .type (.lam "k" (.lam "_" (.var "A") (.lam "_" (.var "B") (.var "X")))
    (.app (.app (.var "k") (.var "a")) (.var "b")))))))

private def PairNN_ : Named := .app (.app Pair_ Nat_) Nat_

-- pred = λn:Nat. fst (n PairNN (pair 0 0) (λp. (snd p, succ (snd p))))
def pred_ : Named := .lam "n" Nat_ (
  .app (.app
    (.app (.app (.app (.var "n") PairNN_)
      (.app (.app (.app (.app pair_ Nat_) Nat_) zero_) zero_))
      (.lam "p" PairNN_ (
        .app (.app (.app (.app pair_ Nat_) Nat_)
          (.app (.app (.var "p") Nat_) (.lam "_" Nat_ (.lam "b" Nat_ (.var "b")))))
          (.app succ_ (.app (.app (.var "p") Nat_) (.lam "_" Nat_ (.lam "b" Nat_ (.var "b"))))))))
    Nat_)
    (.lam "a" Nat_ (.lam "_" Nat_ (.var "a"))))

-- ============================================================
-- Tests
-- ============================================================

section Tests
open Expr

-- Shorthand
private def NatToNat : Named := .lam "_" Nat_ Nat_

-- ------------------------------------------------------------
-- Computation (positive) — concEval
-- concEval is WHNF so Church numerals (lambdas) can't be directly
-- compared. We use isZero to observe results at ground type.
-- ------------------------------------------------------------

-- isZero 0 = true
example : concEval 200 (.app (n isZero_) (n zero_)) = some (n Std.true_) := by native_decide
-- isZero 3 = false
example : concEval 200 (.app (n isZero_) (n three_)) = some (n Std.false_) := by native_decide
-- isZero (succ 2) = false (succ 2 is nonzero)
example : concEval 200 (.app (n isZero_) (.app (n succ_) (n two_))) = some (n Std.false_) := by native_decide
-- isZero (pred 1) = true (pred 1 = 0)
example : concEval 1000 (.app (n isZero_) (.app (n pred_) (n one_))) = some (n Std.true_) := by native_decide
-- isZero (pred 2) = false (pred 2 ≠ 0)
example : concEval 1000 (.app (n isZero_) (.app (n pred_) (n two_))) = some (n Std.false_) := by native_decide
-- pred 0 = 0 (observed via isZero)
example : concEval 1000 (.app (n isZero_) (.app (n pred_) (n zero_))) = some (n Std.true_) := by native_decide

-- ------------------------------------------------------------
-- Computation (positive) — absEval
-- ------------------------------------------------------------

-- succ 2 = 3
example : absEval 200 [] (.app (n succ_) (n two_)) = .ok (n three_) := by native_decide
-- add 2 3 = 5
example : absEval 200 [] (.app (.app (n add_) (n two_)) (n three_)) = .ok (n five_) := by native_decide
-- isZero 0 = true
example : absEval 200 [] (.app (n isZero_) (n zero_)) = .ok (n Std.true_) := by native_decide
-- isZero 3 = false
example : absEval 200 [] (.app (n isZero_) (n three_)) = .ok (n Std.false_) := by native_decide
-- double 3 = 6
example : absEval 200 [] (.app (n double_) (n three_)) = .ok (n six_) := by native_decide
-- pred 3 = 2
example : absEval 1000 [] (.app (n pred_) (n three_)) = .ok (n two_) := by native_decide
-- pred 0 = 0
example : absEval 1000 [] (.app (n pred_) (n zero_)) = .ok (n zero_) := by native_decide
-- pred 1 = 0
example : absEval 1000 [] (.app (n pred_) (n one_)) = .ok (n zero_) := by native_decide

-- ------------------------------------------------------------
-- Computation (negative) — absEval
-- ------------------------------------------------------------

-- add 2 3 ≠ 4
example : absEval 200 [] (.app (.app (n add_) (n two_)) (n three_)) ≠ .ok (n four_) := by native_decide
-- succ 2 ≠ 2
example : absEval 200 [] (.app (n succ_) (n two_)) ≠ .ok (n two_) := by native_decide
-- pred 3 ≠ 3
example : absEval 1000 [] (.app (n pred_) (n three_)) ≠ .ok (n three_) := by native_decide
-- double 3 ≠ 3
example : absEval 200 [] (.app (n double_) (n three_)) ≠ .ok (n three_) := by native_decide

-- ------------------------------------------------------------
-- Computation (negative) — concEval
-- ------------------------------------------------------------

-- isZero 0 ≠ false
example : concEval 200 (.app (n isZero_) (n zero_)) ≠ some (n Std.false_) := by native_decide
-- isZero 3 ≠ true
example : concEval 200 (.app (n isZero_) (n three_)) ≠ some (n Std.true_) := by native_decide
-- isZero (succ 0) ≠ true (succ 0 is not zero)
example : concEval 200 (.app (n isZero_) (.app (n succ_) (n zero_))) ≠ some (n Std.true_) := by native_decide

-- ------------------------------------------------------------
-- Subtype checking (positive)
-- ------------------------------------------------------------

-- Church numerals are subtypes of Nat
example : subCheck 200 (n zero_) (n Nat_) = true := by native_decide
example : subCheck 200 (n one_) (n Nat_) = true := by native_decide
example : subCheck 200 (n three_) (n Nat_) = true := by native_decide
example : subCheck 200 (n six_) (n Nat_) = true := by native_decide

-- succ : Nat → Nat
example : subCheck 200 (n succ_) (n NatToNat) = true := by native_decide
-- add : Nat → Nat → Nat
example : subCheck 200 (n add_) (n (.lam "_" Nat_ NatToNat)) = true := by native_decide
-- isZero : Nat → Bool
example : subCheck 200 (n isZero_) (n (.lam "_" Nat_ Std.Bool)) = true := by native_decide
-- double : Nat → Nat
example : subCheck 200 (n double_) (n NatToNat) = true := by native_decide
-- pred : Nat → Nat
example : subCheck 1000 (n pred_) (n NatToNat) = true := by native_decide

-- ------------------------------------------------------------
-- Subtype checking (negative)
-- ------------------------------------------------------------

-- true is not a Nat
example : subCheck 200 (n Std.true_) (n Nat_) = false := by native_decide
-- three is not a subtype of two (different values)
example : subCheck 200 (n three_) (n two_) = false := by native_decide
-- Nat is not a subtype of zero (it's wider)
example : subCheck 200 (n Nat_) (n zero_) = false := by native_decide
-- succ is not a Nat (it's a function)
example : subCheck 200 (n succ_) (n Nat_) = false := by native_decide

end Tests
end Std

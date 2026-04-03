import Och.Syntax
import Och.Eval
import Och.Subtyping
import Och.Soundness
import Och.Std

/-!
# Integration tests

Cross-cutting tests that span multiple Std modules and don't belong in any
single file. Includes the Prop 5.2.9 regression test and §6.2 abstract
instantiation tests.
-/

open Expr Named Std

-- ============================================================
-- Prop 5.2.9 counterexample: Not on Church Bool
-- ============================================================

private def Not'_n : Named := .lam "X" Bool (.app (.app (.app (.var "X") Bool) false_) true_)
private def Not' : Expr := n Not'_n

example : absEval 1000 [] (.app Not' (n true_)) = .ok (n false_) := by native_decide
example : absEval 1000 [] (.app Not' (n false_)) = .ok (n true_) := by native_decide
example : absEval 1000 [] (.app Not' (n Bool)) = .ok (n Bool) := by native_decide
example : subCheck 1000 (n false_) (n true_) = false := by native_decide
example : subCheck 1000 (.app Not' (n true_)) (n Bool) = true := by native_decide
example : subCheck 1000 (.app Not' (n false_)) (n Bool) = true := by native_decide

-- ============================================================
-- §6.2 Abstract instantiation (ascription-based type-level tests)
-- ============================================================

-- These tests verify that ascription + operations on abstract values
-- produce correct types. They use Std definitions directly.

-- Abstract Nat: add (... : Nat) (... : Nat) ⊑ Nat
example : subCheck 1000
  (.app (.app (n add_) (.asc (n zero_) (n Nat_))) (.asc (n zero_) (n Nat_)))
  (n Nat_) = true := by native_decide

-- succ (... : Nat) ⊑ Nat
example : subCheck 1000
  (.app (n succ_) (.asc (n zero_) (n Nat_)))
  (n Nat_) = true := by native_decide

-- isZero (succ (... : Nat)) = false (precisely!)
example : absEval 1000 []
  (.app (n isZero_) (.app (n succ_) (.asc (n zero_) (n Nat_)))) = .ok (n false_) := by native_decide

-- isZero (... : Nat) ⊑ Bool
example : subCheck 1000
  (.app (n isZero_) (.asc (n zero_) (n Nat_)))
  (n Bool) = true := by native_decide

-- double (... : Nat) ⊑ Nat
example : subCheck 1000
  (.app (n double_) (.asc (n zero_) (n Nat_)))
  (n Nat_) = true := by native_decide

-- ============================================================
-- §6.2 Abstract vector instantiation
-- ============================================================

-- testVec1 = mkVec Nat 1 [0]
private def testVec1 : Expr := n (.app (.app (.app mkVec Nat_) one_)
  (.app (.app (.app (.app consArray Nat_) zero_) zero_) (.app emptyArray Nat_)))

-- Abstract vector unpack: ascribe concrete vec to Vec Nat, then unpack → get Nat (not 1)
example : absEval 1000 [] (.app (.app (.asc testVec1 (.app (n Vec) (n Nat_))) (n Nat_))
  (n (.lam "n" Nat_ (.lam "arr" (.app (.app Array_ (.var "n")) Nat_) (.var "n")))))
  = .ok (n Nat_) := by native_decide

-- Rewrapped abstract vector ⊑ Vec Nat
example : subCheck 1000
  (.app (.app (.asc testVec1 (.app (n Vec) (n Nat_))) (.app (n Vec) (n Nat_)))
    (n (.lam "n" Nat_ (.lam "arr" (.app (.app Array_ (.var "n")) Nat_)
      (.app (.app (.app mkVec Nat_) (.var "n")) (.var "arr"))))))
  (.app (n Vec) (n Nat_)) = true := by native_decide

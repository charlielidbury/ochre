import Och.Syntax
import Och.Eval
import Och.Subtyping
import Och.Soundness
import Och.Std
import Och.Macro

/-!
# Integration tests

Cross-cutting tests that span multiple Std modules and don't belong in any
single file. Includes the Prop 5.2.9 regression test and §6.2 abstract
instantiation tests.
-/

open Std

-- ============================================================
-- Prop 5.2.9 counterexample: Not on Church Bool
-- ============================================================

private def Not' := och{ λX:Bool. X Bool false_ true_ }

example : absEval 1000 [] [] (och{ Not' true_ }) = .ok ⟨false_⟩ := by native_decide
example : absEval 1000 [] [] (och{ Not' false_ }) = .ok ⟨true_⟩ := by native_decide
example : absEval 1000 [] [] (och{ Not' Bool }) = .ok ⟨Bool⟩ := by native_decide
example : subCheck 1000 false_ true_ = false := by native_decide
example : subCheck 1000 (och{ Not' true_ }) Bool = true := by native_decide
example : subCheck 1000 (och{ Not' false_ }) Bool = true := by native_decide

-- ============================================================
-- §6.2 Abstract instantiation (ascription-based type-level tests)
-- ============================================================

-- These tests verify that ascription + operations on abstract values
-- produce correct types. They use Std definitions directly.

-- Abstract Nat: add (... : Nat) (... : Nat) ⊑ Nat
example : subCheck 1000
  (och{ add_ (zero_ : Nat_) (zero_ : Nat_) })
  Nat_ = true := by native_decide

-- succ (... : Nat) ⊑ Nat
example : subCheck 1000
  (och{ succ_ (zero_ : Nat_) })
  Nat_ = true := by native_decide

-- isZero (succ (... : Nat)) = false (precisely!)
example : absEval 1000 [] []
  (och{ isZero_ (succ_ (zero_ : Nat_)) }) = .ok ⟨false_⟩ := by native_decide

-- isZero (... : Nat) ⊑ Bool
example : subCheck 1000
  (och{ isZero_ (zero_ : Nat_) })
  Bool = true := by native_decide

-- double (... : Nat) ⊑ Nat
example : subCheck 1000
  (och{ double_ (zero_ : Nat_) })
  Nat_ = true := by native_decide

-- ============================================================
-- §6.2 Abstract vector instantiation
-- ============================================================

-- testVec1 = mkVec Nat 1 [0]
private def testVec1 := och{ mkVec Nat_ one_ (Pair zero_ unit_) }

-- Abstract vector unpack: ascribe concrete vec to Vec Nat, then unpack → get Nat (not 1)
example : absEval 1000 [] [] (och{ (testVec1 : Vec Nat_) Nat_ (λn:Nat_. λarr:(Array_ n Nat_). n) })
  = .ok ⟨Nat_⟩ := by native_decide

-- Rewrapped abstract vector ⊑ Vec Nat
example : subCheck 1000
  (och{ (testVec1 : Vec Nat_) (Vec Nat_) (λn:Nat_. λarr:(Array_ n Nat_). mkVec Nat_ n arr) })
  (och{ Vec Nat_ }) = true := by native_decide

-- ============================================================
-- absEval_preserves counterexample
-- ============================================================

/- absEval_preserves claims: VCompat(n, v, e) ∧ absEval(e) = ok e' → VCompat(n, v, e'.val).
   This is FALSE when v = e = asc(lam type (bvar 0), lam type type):
   - VCompat(2, v, e) holds by refl (v = e)
   - absEval erases the asc, producing ⟨lam type type⟩
   - VCompat(2, asc(...), lam type type) is False: no disjunct matches
     (v=asc isn't lam/mu/app, inferType(asc)=none)

   The computation below verifies the absEval step. -/
private def absEval_preserves_cex :=
  Expr.asc (Expr.lam Expr.type (Expr.bvar 0)) (Expr.lam Expr.type Expr.type)

example : absEval 10 [] [] absEval_preserves_cex
  = .ok ⟨Expr.lam Expr.type Expr.type⟩ := by native_decide

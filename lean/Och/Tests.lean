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
-- Subtyping transitivity tests
-- ============================================================

-- Previously-known counterexample: Type ⊑ mu Type (bvar 0) ⊑ lam Type (bvar 0)
-- but Type ⋢ lam Type (bvar 0). The fix: self-elim body check no longer uses
-- the circular seen entry, so mu Type (bvar 0) ⊑ lam Type (bvar 0) now correctly
-- returns false (the non-productive fixpoint can't prove it's a function type).

-- Type ⊑ mu Type (bvar 0): still holds (self-intro is valid)
example : subCheckNF 100 [] [] Expr.type (.mu .type (.bvar 0)) = true := by native_decide

-- mu Type (bvar 0) ⊑ lam Type (bvar 0): now correctly FALSE (was spuriously true)
example : subCheckNF 100 [] [] (.mu .type (.bvar 0)) (.lam .type (.bvar 0)) = false := by native_decide

-- Type ⊑ lam Type (bvar 0): false (Type is not a function type)
example : subCheckNF 100 [] [] Expr.type (.lam .type (.bvar 0)) = false := by native_decide

-- Transitivity instance: the old a ⊑ b ∧ b ⊑ c ∧ ¬(a ⊑ c) is gone because b ⊑ c is now false

-- ============================================================
-- Transitivity exhaustive search on small terms
-- ============================================================

-- Helper: check transitivity for a triple (a, b, c) with given fuel
private def checkTrans (fuel : Nat) (a b c : Expr) : Bool :=
  if subCheckNF fuel [] [] a b && subCheckNF fuel [] [] b c then
    subCheckNF fuel [] [] a c
  else true  -- vacuously true if a⊄b or b⊄c

-- Small expression generators for exhaustive testing
private def smallExprs : List Expr :=
  [ .type,
    .bvar 0,
    .lam .type (.bvar 0),          -- identity: λx:Type. x
    .lam .type .type,              -- const Type: λx:Type. Type
    .mu .type (.bvar 0),           -- fixpoint identity: μType. self
    .mu .type (.lam .type (.bvar 0)), -- μType. λx:Type. x
    .mu (.lam .type .type) (.lam .type (.bvar 0)),  -- μ(Type→Type). λx:Type. x
    .app (.bvar 0) (.bvar 0),      -- x x
    .lam .type (.lam .type (.bvar 0)), -- λx:Type. λy:Type. y
    .mu .type .type                -- μType. Type
  ]

-- Exhaustive transitivity check over all triples of small expressions
-- If this passes, transitivity holds for all small terms (with fuel 50)
example : (smallExprs.all fun a =>
           smallExprs.all fun b =>
           smallExprs.all fun c =>
           checkTrans 50 a b c) = true := by native_decide

-- Extended test with Std library types
private def stdExprs : List Expr :=
  [ Bool, true_, false_, Nat_, zero_,
    .lam .type .type,              -- Type → Type
    .lam .type (.bvar 0),          -- identity
    .mu .type (.bvar 0),           -- fixpoint identity
    .type,
    .lam Nat_ Nat_,                -- Nat → Nat (constant)
    .lam Bool Bool                 -- Bool → Bool (constant)
  ]

example : (stdExprs.all fun a =>
           stdExprs.all fun b =>
           stdExprs.all fun c =>
           checkTrans 200 a b c) = true := by native_decide

-- Edge cases: nested mus and self-referential patterns
private def edgeExprs : List Expr :=
  [ .type,
    .mu .type (.bvar 0),                    -- μType. self (identity fixpoint)
    .mu .type .type,                        -- μType. Type
    .mu .type (.lam .type (.bvar 0)),       -- μType. λx:T. x
    .mu (.lam .type .type) (.bvar 0),       -- μ(T→T). self
    .mu (.lam .type .type) (.lam .type (.bvar 1)),  -- μ(T→T). λx:T. self (recursive)
    .lam .type (.bvar 0),                   -- λx:T. x
    .lam .type .type,                       -- λx:T. T
    .mu .type (.mu .type (.bvar 0)),        -- nested mu
    .app (.mu .type (.lam .type (.bvar 0))) .type  -- apply mu to Type
  ]

example : (edgeExprs.all fun a =>
           edgeExprs.all fun b =>
           edgeExprs.all fun c =>
           checkTrans 100 a b c) = true := by native_decide

-- ============================================================
-- closedAt 0 witness tests for soundness theorem precondition
-- ============================================================

-- These verify that the closedAt 0 precondition added to soundness
-- is satisfiable for representative real programs.

-- Simple values
example : Expr.closedAt 0 (och{ true_ }) = true := by native_decide
example : Expr.closedAt 0 (och{ zero_ }) = true := by native_decide
example : Expr.closedAt 0 Expr.type = true := by native_decide

-- Function applications
example : Expr.closedAt 0 (och{ Not' true_ }) = true := by native_decide
example : Expr.closedAt 0 (och{ succ_ two_ }) = true := by native_decide
example : Expr.closedAt 0 (och{ isZero_ zero_ }) = true := by native_decide
example : Expr.closedAt 0 (och{ add_ two_ three_ }) = true := by native_decide
example : Expr.closedAt 0 (och{ double_ three_ }) = true := by native_decide

-- Ascriptions (key for asc case)
example : Expr.closedAt 0 (och{ (zero_ : Nat_) }) = true := by native_decide
example : Expr.closedAt 0 (och{ succ_ (zero_ : Nat_) }) = true := by native_decide

-- Recursive types and north star
example : Expr.closedAt 0 Nat_ = true := by native_decide
example : Expr.closedAt 0 succ_ = true := by native_decide
example : Expr.closedAt 0 (och{ Vec Nat_ }) = true := by native_decide


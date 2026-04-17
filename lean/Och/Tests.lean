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

example : absEvalVal (och{ Not' true_ }) = .ok ⟨false_⟩ := by native_decide
example : absEvalVal (och{ Not' false_ }) = .ok ⟨true_⟩ := by native_decide
example : absEvalVal (och{ Not' Bool }) = .ok ⟨Bool⟩ := by native_decide
example : subCheck 1000 false_ true_ = .ok false := by native_decide
example : subCheck 1000 (och{ Not' true_ }) Bool = .ok true := by native_decide
example : subCheck 1000 (och{ Not' false_ }) Bool = .ok true := by native_decide

-- ============================================================
-- §6.2 Abstract instantiation (ascription-based type-level tests)
-- ============================================================

-- These tests verify that ascription + operations on abstract values
-- produce correct types. They use Std definitions directly.

-- Abstract Nat: add (... : Nat) (... : Nat) ⊑ Nat
example : subCheck 1000
  (och{ add_ (zero_ : Nat_) (zero_ : Nat_) })
  Nat_ = .ok true := by native_decide

-- succ (... : Nat) ⊑ Nat
example : subCheck 1000
  (och{ succ_ (zero_ : Nat_) })
  Nat_ = .ok true := by native_decide

-- isZero (succ (... : Nat)) = false (precisely!)
example : absEvalVal
  (och{ isZero_ (succ_ (zero_ : Nat_)) }) = .ok ⟨false_⟩ := by native_decide

-- isZero (... : Nat) ⊑ Bool
example : subCheck 1000
  (och{ isZero_ (zero_ : Nat_) })
  Bool = .ok true := by native_decide

-- double (... : Nat) ⊑ Nat
example : subCheck 1000
  (och{ double_ (zero_ : Nat_) })
  Nat_ = .ok true := by native_decide

-- ============================================================
-- §6.2 Abstract vector instantiation
-- ============================================================

-- testVec1 = mkVec Nat done_ [0]   (done_ is the dNat 1)
private def testVec1 := och{ mkVec Nat_ done_ (pair_ Nat_ Unit_ zero_ unit_) }

-- Abstract vector unpack. Ascription widens `testVec1` to its type
-- `Vec Nat_ = Sigma dNat (λn. Array_ n Nat_) = λX. λk. X`, so applying
-- the motive `Nat_` and the continuation gives back the motive, `Nat_`.
-- The c061a3b dNat port changed the expectation to `dNat` (n's type),
-- but the result is the *motive* X, not the type of the bound `n`;
-- under Church-Nat the two coincided, masking the distinction. Getting
-- `dNat` here would need Sigma-as-a-type to apply `k` to abstract
-- witnesses, which is a Sigma-encoding question, not a checker gap.
example : absEvalVal (och{ (testVec1 : Vec Nat_) Nat_ (λn:dNat. λarr:(Array_ n Nat_). n) })
  = .ok ⟨Nat_⟩ := by native_decide

-- Rewrapped abstract vector ⊑ Vec Nat. The neutral-head gate leaves
-- `Array_ n Nat_` (abstract `n`) stuck so the motive normalises, and
-- the stuck-head re-eval rule lets the existential repack.
example : subCheck 1000
  (och{ (testVec1 : Vec Nat_) (Vec Nat_) (λn:dNat. λarr:(Array_ n Nat_). mkVec Nat_ n arr) })
  (och{ Vec Nat_ }) = .ok true := by native_decide

-- ============================================================
-- Subtyping transitivity tests
-- ============================================================

-- Previously-known counterexample: Type ⊑ mu Type (bvar 0) ⊑ lam Type (bvar 0)
-- but Type ⋢ lam Type (bvar 0). Under the ι/fix split the same pattern
-- applies to both constructors.

-- Type ⊑ ι Type (bvar 0): should hold via iotaIntro (self-intro).
example : subCheckNF 100 [] [] Expr.type (.iota .type (.bvar 0)) = .ok true := by native_decide

-- ι Type (bvar 0) ⊑ lam Type (bvar 0): not provable (iota unfolds to itself, exhausts fuel)
example : subCheckNF 100 [] [] (.iota .type (.bvar 0)) (.lam .type (.bvar 0)) ≠ .ok true := by native_decide

-- Type ⊑ lam Type (bvar 0): false (Type is not a function type)
example : subCheckNF 100 [] [] Expr.type (.lam .type (.bvar 0)) = .ok false := by native_decide

-- Transitivity instance: the old a ⊑ b ∧ b ⊑ c ∧ ¬(a ⊑ c) is gone because b ⊑ c is now false

-- ============================================================
-- Transitivity exhaustive search on small terms
-- ============================================================

-- Helper: check transitivity for a triple (a, b, c) with given fuel
private def checkTrans (fuel : Nat) (a b c : Expr) : Bool :=
  if subCheckNF fuel [] [] a b == .ok true && subCheckNF fuel [] [] b c == .ok true then
    subCheckNF fuel [] [] a c == .ok true
  else true  -- vacuously true if a⊄b or b⊄c

-- Small CLOSED expression generators for exhaustive testing.
-- Only closed terms: transitivity need only hold for well-scoped terms.
-- Uses a mix of ι and fix binders post-split.
private def smallExprs : List Expr :=
  [ .type,
    .lam .type (.bvar 0),          -- identity: λx:Type. x
    .lam .type .type,              -- const Type: λx:Type. Type
    .iota .type (.bvar 0),         -- fixpoint-identity iota: ιType. self
    .fix .type (.bvar 0),          -- fix identity: fix Type. self
    .iota .type (.lam .type (.bvar 0)), -- ιType. λx:Type. x
    .fix (.lam .type .type) (.lam .type (.bvar 0)),  -- fix(Type→Type). λx:Type. x
    .lam .type (.lam .type (.bvar 0)), -- λx:Type. λy:Type. y
    .iota .type .type              -- ιType. Type
  ]

-- Transitivity exhaustive search. The seen-set discipline rework
-- (productive-only extension, threaded through lam/app) plus the
-- removal of fix-ann/neutralType ann-widening leaves no triple where
-- a ⊑ b ∧ b ⊑ c but a ⊄ c on these expression sets.
example : (smallExprs.all fun a =>
           smallExprs.all fun b =>
           smallExprs.all fun c =>
           checkTrans 50 a b c) = true := by native_decide

-- Extended test with Std library types
private def stdExprs : List Expr :=
  [ Bool, true_, false_, Nat_, zero_,
    .lam .type .type,              -- Type → Type
    .lam .type (.bvar 0),          -- identity
    .iota .type (.bvar 0),         -- iota fixpoint identity
    .type,
    .lam Nat_ Nat_,                -- Nat → Nat (constant)
    .lam Bool Bool                 -- Bool → Bool (constant)
  ]

example : (stdExprs.all fun a =>
           stdExprs.all fun b =>
           stdExprs.all fun c =>
           checkTrans 200 a b c) = true := by native_decide

-- Edge cases: nested binders and self-referential patterns
private def edgeExprs : List Expr :=
  [ .type,
    .iota .type (.bvar 0),                    -- ιType. self
    .fix .type (.bvar 0),                     -- fix Type. self
    .iota .type .type,                        -- ιType. Type
    .fix .type (.lam .type (.bvar 0)),        -- fix Type. λx:T. x
    .fix (.lam .type .type) (.bvar 0),        -- fix(T→T). self
    .fix (.lam .type .type) (.lam .type (.bvar 1)),  -- fix(T→T). λx:T. self (recursive)
    .lam .type (.bvar 0),                     -- λx:T. x
    .lam .type .type,                         -- λx:T. T
    .iota .type (.fix .type (.bvar 0)),       -- nested: iota wrapping fix
    .app (.fix .type (.lam .type (.bvar 0))) .type  -- apply fix to Type
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


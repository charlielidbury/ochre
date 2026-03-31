import Och.Syntax
import Och.Eval
import Och.Subtyping

/-!
# Och Test Suite

These tests encode the acceptance criteria from docs/och-spec.md §6.
They pin down the expressiveness of the language: agents can change Syntax,
Eval, and Subtyping freely, but these tests must continue to pass.

DO NOT WEAKEN THESE TESTS. If a test doesn't pass, fix the definitions, not the
test. The only acceptable changes to this file are:
- Adapting to renamed constructors (if Syntax.lean changes representation)
- Adding MORE tests
- Fixing obvious transcription errors (with explanation)
-/

open Expr

-- ============================================================
-- Standard library (Church encodings)
-- These mirror docs/och-spec.md §5 exactly.
-- ============================================================

-- Booleans
def Bool' : Expr := .lam "X" .type (.lam "t" (.var "X") (.lam "f" (.var "X") (.var "X")))
def true'  : Expr := .lam "X" .type (.lam "t" (.var "X") (.lam "f" (.var "X") (.var "t")))
def false' : Expr := .lam "X" .type (.lam "t" (.var "X") (.lam "f" (.var "X") (.var "f")))

-- Unit
def Unit' : Expr := .lam "X" .type (.lam "x" (.var "X") (.var "X"))
def unit' : Expr := .lam "X" .type (.lam "x" (.var "X") (.var "x"))

-- Natural numbers
def Nat' : Expr := .lam "X" .type (.lam "z" (.var "X") (.lam "s" (.lam "_" (.var "X") (.var "X")) (.var "X")))
def zero' : Expr := .lam "X" .type (.lam "z" (.var "X") (.lam "s" (.lam "_" (.var "X") (.var "X")) (.var "z")))
def one'  : Expr := .lam "X" .type (.lam "z" (.var "X") (.lam "s" (.lam "_" (.var "X") (.var "X")) (.app (.var "s") (.var "z"))))
def two'  : Expr := .lam "X" .type (.lam "z" (.var "X") (.lam "s" (.lam "_" (.var "X") (.var "X")) (.app (.var "s") (.app (.var "s") (.var "z")))))
def three' : Expr := .lam "X" .type (.lam "z" (.var "X") (.lam "s" (.lam "_" (.var "X") (.var "X")) (.app (.var "s") (.app (.var "s") (.app (.var "s") (.var "z"))))))

def succ' : Expr := .lam "n" Nat' (
  .lam "X" .type (.lam "z" (.var "X") (.lam "s" (.lam "_" (.var "X") (.var "X"))
    (.app (.var "s") (.app (.app (.app (.var "n") (.var "X")) (.var "z")) (.var "s"))))))

-- id (for transparency tests)
def id' : Expr := .lam "T" .type (.lam "x" (.var "T") (.var "x"))
def idAscribed : Expr := .lam "T" .type (.lam "x" (.var "T") (.asc (.var "x") (.var "T")))

-- ============================================================
-- Fuel for evaluation (generous)
-- ============================================================
def testFuel : Nat := 1000

-- ============================================================
-- §6.1 Concrete evaluation: precision tests
-- These test that concrete evaluation produces the right values.
-- ============================================================

-- Concrete eval: true X t f ⟶ t
example : concEval testFuel (.app (.app (.app true' (.var "X")) (.var "t")) (.var "f")) = some (.var "t") := by
  native_decide

-- Concrete eval: false X t f ⟶ f
example : concEval testFuel (.app (.app (.app false' (.var "X")) (.var "t")) (.var "f")) = some (.var "f") := by
  native_decide

-- ============================================================
-- §6.1 Abstract evaluation: precision tests
-- These test that the abstract evaluator computes precise types.
-- ============================================================

-- Abstract eval of a closed lambda: returns itself.
example : absEval testFuel [] true' = some true' := by
  native_decide

-- id Nat 3 should have precise type 3 (transparency). §6.4
example : absEval testFuel [] (.app (.app id' Nat') three') = some three' := by
  native_decide

-- id_ascribed Nat 3 should have type Nat (ascription loses precision). §6.4
example : absEval testFuel [] (.app (.app idAscribed Nat') three') = some Nat' := by
  native_decide

-- ============================================================
-- §6.1 Subtyping tests
-- These test that the subtyping relation is expressive enough.
--
-- NOTE: The subtyping tests below use `subCheck` (the decision procedure).
-- When agents build a proper subtyping checker, these should pass.
-- For now, many will fail because subCheck is a placeholder.
-- ============================================================

-- true ⊑ Bool
example : subCheck testFuel true' Bool' = true := by native_decide

-- false ⊑ Bool
example : subCheck testFuel false' Bool' = true := by native_decide

-- 0 ⊑ Nat
example : subCheck testFuel zero' Nat' = true := by native_decide

-- 3 ⊑ Nat
example : subCheck testFuel three' Nat' = true := by native_decide

-- unit ⊑ Unit
example : subCheck testFuel unit' Unit' = true := by native_decide

-- anything ⊑ Type
example : subCheck testFuel true' .type = true := by native_decide
example : subCheck testFuel Nat' .type = true := by native_decide

-- ============================================================
-- §6.3 Tests that must FAIL
-- ============================================================

-- BAD3: true is not in Nat
example : subCheck testFuel true' Nat' = false := by native_decide

-- BAD4: succ 2 ≠ 2, so 3 ⊑ 2 must fail
example : subCheck testFuel three' two' = false := by native_decide

-- ============================================================
-- §6.4 Transparency preservation
-- ============================================================

-- succ 2 should have precise type 3
-- Abstract eval computes the fully normalized Church numeral.
example : absEval testFuel [] (.app succ' two') = some three' := by
  native_decide

-- ============================================================
-- Regression test: Proposition 5.2.9 counterexample
--
-- Not = λ(X: Bool). X Bool false true
-- F = λ(B: Bool). (Not B : B)       -- should hold when B: Bool
-- Narrowing B to true should not break the typing.
--
-- This is the test that historically fails. It checks monotonicity:
-- if F typechecks with B: Bool, and we narrow to B: true, the result
-- type should be ⊑ the original result type.
-- ============================================================

-- def Not' : Expr := .lam "X" Bool' (.app (.app (.app (.var "X") Bool') false') true')
-- Agents: formalize and uncomment this test once the system is mature enough.

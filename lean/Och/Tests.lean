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

-- More Church numerals
def four' : Expr := .lam "X" .type (.lam "z" (.var "X") (.lam "s" (.lam "_" (.var "X") (.var "X"))
  (.app (.var "s") (.app (.var "s") (.app (.var "s") (.app (.var "s") (.var "z")))))))
def five' : Expr := .lam "X" .type (.lam "z" (.var "X") (.lam "s" (.lam "_" (.var "X") (.var "X"))
  (.app (.var "s") (.app (.var "s") (.app (.var "s") (.app (.var "s") (.app (.var "s") (.var "z"))))))))
def six' : Expr := .lam "X" .type (.lam "z" (.var "X") (.lam "s" (.lam "_" (.var "X") (.var "X"))
  (.app (.var "s") (.app (.var "s") (.app (.var "s") (.app (.var "s") (.app (.var "s") (.app (.var "s") (.var "z")))))))))

-- add = λ(n: Nat). λ(m: Nat). n Nat m succ
def add' : Expr := .lam "n" Nat' (.lam "m" Nat'
  (.app (.app (.app (.var "n") Nat') (.var "m")) succ'))

-- isZero = λ(n: Nat). n Bool true (λ(_: Bool). false)
def isZero' : Expr := .lam "n" Nat'
  (.app (.app (.app (.var "n") Bool') true') (.lam "_" Bool' false'))

-- double = λ(x: Nat). add x x
def double' : Expr := .lam "x" Nat' (.app (.app add' (.var "x")) (.var "x"))

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

-- Concrete eval: true X t f ⟶ t  (in env with X, t, f as neutral)
example : concEval testFuel [("X", .var "X"), ("t", .var "t"), ("f", .var "f")]
    (.app (.app (.app true' (.var "X")) (.var "t")) (.var "f")) = some (.var "t") := by
  native_decide

-- Concrete eval: false X t f ⟶ f  (in env with X, t, f as neutral)
example : concEval testFuel [("X", .var "X"), ("t", .var "t"), ("f", .var "f")]
    (.app (.app (.app false' (.var "X")) (.var "t")) (.var "f")) = some (.var "f") := by
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
-- §6.5 Arithmetic and standard library tests
-- ============================================================

-- add 2 3 = 5
example : absEval testFuel [] (.app (.app add' two') three') = some five' := by
  native_decide

-- isZero 0 = true
example : absEval testFuel [] (.app isZero' zero') = some true' := by
  native_decide

-- isZero 3 = false
example : absEval testFuel [] (.app isZero' three') = some false' := by
  native_decide

-- double 3 = 6
example : absEval testFuel [] (.app double' three') = some six' := by
  native_decide

-- succ applied multiple times: succ(succ(succ 0)) = 3
example : absEval testFuel [] (.app succ' (.app succ' (.app succ' zero'))) = some three' := by
  native_decide

-- add 0 0 = 0
example : absEval testFuel [] (.app (.app add' zero') zero') = some zero' := by
  native_decide

-- ============================================================
-- §6.5 More subtyping tests
-- ============================================================

-- 5 ⊑ Nat
example : subCheck testFuel five' Nat' = true := by native_decide

-- add 2 3 result ⊑ Nat
example : subCheck testFuel (.app (.app add' two') three') Nat' = true := by native_decide

-- double 3 result ⊑ Nat
example : subCheck testFuel (.app double' three') Nat' = true := by native_decide

-- isZero 0 result ⊑ Bool
example : subCheck testFuel (.app isZero' zero') Bool' = true := by native_decide

-- succ ⊑ (Nat → Nat), i.e. succ has type Nat → Nat
-- succ is λ(n:Nat). ..., and Nat → Nat is λ(n:Nat). Nat
-- This checks function subtyping: same domain, body ⊑ Nat
example : subCheck testFuel succ' (.lam "n" Nat' Nat') = true := by native_decide

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

-- Not = λ(X: Bool). X Bool false true  (boolean negation)
def Not' : Expr := .lam "X" Bool' (.app (.app (.app (.var "X") Bool') false') true')

-- Not correctly computes boolean negation
example : absEval testFuel [] (.app Not' true') = some false' := by native_decide
example : absEval testFuel [] (.app Not' false') = some true' := by native_decide

-- Not Bool = Bool (at the type level, negation maps Bool to Bool)
example : absEval testFuel [] (.app Not' Bool') = some Bool' := by native_decide

-- The Prop 5.2.9 scenario:
--   F = λ(B: Bool). (Not B : B)
-- Concretely: F true = Not true = false (ascription erased at runtime)
-- Abstractly: F true → (Not true : true) → true (ascription takes rhs)
-- This would need false ⊑ true for soundness — which correctly fails:
example : subCheck testFuel false' true' = false := by native_decide

-- The safe version uses Bool as the ascription type:
--   (Not true : Bool) is fine because Not true = false ⊑ Bool ✓
example : subCheck testFuel (.app Not' true') Bool' = true := by native_decide
example : subCheck testFuel (.app Not' false') Bool' = true := by native_decide

-- ============================================================
-- §7 Fix (general recursion) tests
-- ============================================================

-- Nat → Nat function type (as a lambda: λ(n: Nat). Nat)
def NatToNat : Expr := .lam "n" Nat' Nat'

-- Simple non-recursive fix: fix (λself: Nat→Nat. λn: Nat. n)
-- The identity function, declared as Nat → Nat
def fixId : Expr := .fix (.lam "self" NatToNat (.lam "n" Nat' (.var "n")))

-- Abstract eval of fix returns the declared type (dom)
-- fix (λself: Nat→Nat. body) → Nat → Nat
example : absEval testFuel [] fixId = some NatToNat := by native_decide

-- fix ⊑ Nat → Nat (the declared type)
example : subCheck testFuel fixId NatToNat = true := by native_decide

-- Concrete eval: fix (λself. λn. n) applied to 3 should give 3
-- The fix evaluates body with self := fix(...), body = λn. n,
-- which doesn't use self, so result is λn. n. Apply to 3 → 3.
example : concEval testFuel [] (.app fixId three') = some three' := by native_decide

-- Concrete eval: fix (λself. λn. n) applied to 0 should give 0
example : concEval testFuel [] (.app fixId zero') = some zero' := by native_decide

-- Recursive fix: predecessor-based recursion to constant zero
-- fix (λself: Nat→Nat. λn: Nat. isZero n ? 0 : self (pred n))
-- This should always return 0 for any concrete nat.
-- Note: In Church encoding, "isZero n ? 0 : self (pred n)" is
-- (isZero n) Nat zero (self (pred n))
-- But we need to be careful: Church bools are lazy in both branches.
-- Actually: isZero n returns a Church bool, applied to Nat, then two branches.
-- The issue is that both branches are evaluated (no laziness).
-- Let's test with something simpler first.

-- Simple recursive doubling that counts down: add n to itself
-- Actually, let's just test that fix produces the right abstract type
-- and works for non-recursive cases.

-- fix ⊑ Type (everything is ⊑ Type)
example : subCheck testFuel fixId .type = true := by native_decide

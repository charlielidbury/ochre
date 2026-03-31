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

-- ============================================================
-- §5.4–5.8 Pairs, Arrays, Vectors (Church-encoded data structures)
-- ============================================================

-- Pair = λ(A: Type). λ(B: Type). λ(X: Type). λ(k: λ(_: A). B → X). X
def Pair' : Expr := .lam "A" .type (.lam "B" .type (
  .lam "X" .type (.lam "k" (.lam "_" (.var "A") (.lam "_" (.var "B") (.var "X"))) (.var "X"))))

-- pair = λ(A: Type). λ(B: Type). λ(a: A). λ(b: B). λ(X: Type). λ(k: ...). k a b
def pair' : Expr := .lam "A" .type (.lam "B" .type (.lam "a" (.var "A") (.lam "b" (.var "B") (
  .lam "X" .type (.lam "k" (.lam "_" (.var "A") (.lam "_" (.var "B") (.var "X")))
    (.app (.app (.var "k") (.var "a")) (.var "b")))))))

-- Array = λ(n: Nat). λ(T: Type). n Type Unit (λ(acc: Type). Pair T acc)
def Array' : Expr := .lam "n" Nat' (.lam "T" .type (
  .app (.app (.app (.var "n") .type) Unit') (.lam "acc" .type (
    .app (.app Pair' (.var "T")) (.var "acc")))))

-- emptyArray = λ(T: Type). unit
def emptyArray' : Expr := .lam "T" .type unit'

-- consArray = λ(T: Type). λ(n: Nat). λ(x: T). λ(rest: Array n T). pair T (Array n T) x rest
def consArray' : Expr := .lam "T" .type (.lam "n" Nat' (.lam "x" (.var "T") (.lam "rest" (.app (.app Array' (.var "n")) (.var "T")) (
  .app (.app (.app (.app pair' (.var "T")) (.app (.app Array' (.var "n")) (.var "T"))) (.var "x")) (.var "rest")))))

-- headArray = λ(T: Type). λ(n: Nat). λ(arr: Array (succ n) T). arr T (λ(x: T). λ(_: Array n T). x)
def headArray' : Expr := .lam "T" .type (.lam "n" Nat' (.lam "arr" (.app (.app Array' (.app succ' (.var "n"))) (.var "T")) (
  .app (.app (.var "arr") (.var "T")) (.lam "x" (.var "T") (.lam "_" (.app (.app Array' (.var "n")) (.var "T")) (.var "x"))))))

-- tailArray = λ(T: Type). λ(n: Nat). λ(arr: Array (succ n) T). arr (Array n T) (λ(_: T). λ(rest: Array n T). rest)
def tailArray' : Expr := .lam "T" .type (.lam "n" Nat' (.lam "arr" (.app (.app Array' (.app succ' (.var "n"))) (.var "T")) (
  .app (.app (.var "arr") (.app (.app Array' (.var "n")) (.var "T"))) (.lam "_" (.var "T") (.lam "rest" (.app (.app Array' (.var "n")) (.var "T")) (.var "rest"))))))

-- ============================================================
-- §6.1 Array/Pair concrete tests
-- ============================================================

-- Array 0 Nat = Unit (by β-reduction)
example : absEval testFuel [] (.app (.app Array' zero') Nat') = some Unit' := by native_decide

-- Array 1 Nat = Pair Nat Unit (by β-reduction)
-- Array (succ 0) Nat = Pair Nat (Array 0 Nat) = Pair Nat Unit
-- We check via subtyping since the normal forms may differ structurally
-- First, let's check Array 2 Nat evaluates properly
-- Array 2 Nat = Pair Nat (Pair Nat Unit)

-- pair Nat Nat 10 20 — construct a simple pair
-- For now let's just encode concrete numerals as themselves (they're Church-encoded)
-- 10 and 20 are large Church numerals, so let's use small ones.

-- Construct arr1 = consArray Nat 0 zero (emptyArray Nat) — a 1-element array [0]
def testArr1 : Expr := .app (.app (.app (.app consArray' Nat') zero') zero') (.app emptyArray' Nat')

-- Abstract eval should produce a normal form
-- consArray Nat 0 zero (emptyArray Nat) : Array 1 Nat = Pair Nat Unit
-- Check that it's subtype of Array 1 Nat
example : subCheck testFuel testArr1 (.app (.app Array' one') Nat') = true := by native_decide

-- headArray Nat 0 testArr1 should give zero
example : absEval testFuel [] (.app (.app (.app headArray' Nat') zero') testArr1) = some zero' := by native_decide

-- Construct arr2 = consArray Nat 1 one (consArray Nat 0 two (emptyArray Nat)) — [1, 2]
def testArr2 : Expr := .app (.app (.app (.app consArray' Nat') one') one')
  (.app (.app (.app (.app consArray' Nat') zero') two') (.app emptyArray' Nat'))

-- arr2 ⊑ Array 2 Nat
example : subCheck testFuel testArr2 (.app (.app Array' two') Nat') = true := by native_decide

-- headArray Nat 1 arr2 = 1
example : absEval testFuel [] (.app (.app (.app headArray' Nat') one') testArr2) = some one' := by native_decide

-- ============================================================
-- §5.8 Vectors (Sigma types)
-- ============================================================

-- Sigma = λ(A: Type). λ(B: A → Type). λ(X: Type). λ(k: λ(a: A). λ(_: B a). X). X
def Sigma' : Expr := .lam "A" .type (.lam "B" (.lam "_" (.var "A") .type) (
  .lam "X" .type (.lam "k" (.lam "a" (.var "A") (.lam "_" (.app (.var "B") (.var "a")) (.var "X"))) (.var "X"))))

-- dpair = λ(A: Type). λ(B: A → Type). λ(a: A). λ(b: B a). λ(X: Type). λ(k: ...). k a b
def dpair' : Expr := .lam "A" .type (.lam "B" (.lam "_" (.var "A") .type) (
  .lam "a" (.var "A") (.lam "b" (.app (.var "B") (.var "a")) (
    .lam "X" .type (.lam "k" (.lam "a2" (.var "A") (.lam "_" (.app (.var "B") (.var "a2")) (.var "X")))
      (.app (.app (.var "k") (.var "a")) (.var "b")))))))

-- Vec T = Sigma Nat (λ(n: Nat). Array n T)
def Vec' : Expr := .lam "T" .type (
  .app (.app Sigma' Nat') (.lam "n" Nat' (.app (.app Array' (.var "n")) (.var "T"))))

-- mkVec = λ(T: Type). λ(n: Nat). λ(arr: Array n T). dpair Nat (λ(n: Nat). Array n T) n arr
def mkVec' : Expr := .lam "T" .type (.lam "n" Nat' (.lam "arr" (.app (.app Array' (.var "n")) (.var "T")) (
  .app (.app (.app (.app dpair' Nat') (.lam "n2" Nat' (.app (.app Array' (.var "n2")) (.var "T")))) (.var "n")) (.var "arr"))))

-- Construct vec1 = mkVec Nat 1 testArr1
def testVec1 : Expr := .app (.app (.app mkVec' Nat') one') testArr1

-- vec1 ⊑ Vec Nat
example : subCheck testFuel testVec1 (.app Vec' Nat') = true := by native_decide

-- Unpack vec1 to get the length: vec1 Nat (λn. λarr. n) should give 1
example : absEval testFuel [] (.app (.app testVec1 Nat') (.lam "n" Nat' (.lam "arr" (.app (.app Array' (.var "n")) Nat') (.var "n")))) = some one' := by native_decide

-- tailArray Nat 0 arr1 should give emptyArray Nat (= unit)
-- tailArray Nat 0 [0] = unit
example : absEval testFuel [] (.app (.app (.app tailArray' Nat') zero') testArr1) = some unit' := by native_decide

-- headArray Nat 0 (tailArray Nat 1 arr2) = 2  (second element of [1, 2])
-- Note: tailArray Nat 1 arr2 strips the first element, giving [2]
-- Then headArray Nat 0 [2] = 2
example : absEval testFuel [] (.app (.app (.app headArray' Nat') zero')
  (.app (.app (.app tailArray' Nat') one') testArr2)) = some two' := by native_decide

-- Construct vec2 = mkVec Nat 2 testArr2
def testVec2 : Expr := .app (.app (.app mkVec' Nat') two') testArr2

-- vec2 ⊑ Vec Nat
example : subCheck testFuel testVec2 (.app Vec' Nat') = true := by native_decide

-- Unpack vec2 to get length: should give 2
example : absEval testFuel [] (.app (.app testVec2 Nat') (.lam "n" Nat' (.lam "arr" (.app (.app Array' (.var "n")) Nat') (.var "n")))) = some two' := by native_decide

-- ============================================================
-- §6.2 Abstract instantiation tests
-- These test abstract inputs (ascribed) — the core use case for typing.
-- ============================================================

-- Abstract vector: (... : Vec Nat) — modeled as ascription on unit (dummy value)
-- absEval of (e : Vec Nat) returns Vec Nat (the rhs)
-- Unpack: v1 Nat (λn. λarr. n) should give Nat (abstract length)
example : absEval testFuel [] (.app (.app (.asc unit' (.app Vec' Nat')) Nat')
  (.lam "n" Nat' (.lam "arr" (.app (.app Array' (.var "n")) Nat') (.var "n"))))
  = some Nat' := by native_decide

-- Rewrapped: v1 (Vec Nat) (λn. λarr. mkVec Nat n arr) ⊑ Vec Nat
-- This tests that unpacking and repacking preserves the type
example : subCheck testFuel
  (.app (.app (.asc unit' (.app Vec' Nat')) (.app Vec' Nat'))
    (.lam "n" Nat' (.lam "arr" (.app (.app Array' (.var "n")) Nat')
      (.app (.app (.app mkVec' Nat') (.var "n")) (.var "arr")))))
  (.app Vec' Nat') = true := by native_decide

-- Abstract Nat: (... : Nat) behaves like an unknown natural number
-- add (... : Nat) (... : Nat) ⊑ Nat
example : subCheck testFuel
  (.app (.app add' (.asc unit' Nat')) (.asc unit' Nat'))
  Nat' = true := by native_decide

-- succ (... : Nat) ⊑ Nat
example : subCheck testFuel
  (.app succ' (.asc unit' Nat'))
  Nat' = true := by native_decide

-- isZero (succ (... : Nat)) = false (precisely!)
-- Even with abstract n : Nat, isZero (succ n) is precisely false.
-- succ n always fires the s branch, and isZero's s = λ(_: Bool). false
-- is a constant function that discards the stuck (n X z s) subterm.
example : absEval testFuel []
  (.app isZero' (.app succ' (.asc unit' Nat'))) = some false' := by native_decide

-- isZero (... : Nat) ⊑ Bool
example : subCheck testFuel
  (.app isZero' (.asc unit' Nat'))
  Bool' = true := by native_decide

-- double (... : Nat) ⊑ Nat
example : subCheck testFuel
  (.app double' (.asc unit' Nat'))
  Nat' = true := by native_decide

-- ============================================================
-- §6.3 More negative tests (data structures)
-- ============================================================

-- BAD5: emptyArray Nat ≠ Array 1 Nat (Unit ≠ Pair Nat Unit)
example : subCheck testFuel (.app emptyArray' Nat') (.app (.app Array' one') Nat') = false := by native_decide

-- ============================================================
-- §7.1 Recursive fix: concrete recursion limitation
-- ============================================================

-- FINDING: Concrete recursive fix with Church-encoded branching does NOT
-- work with the current evaluator. Both concEval and absEval normalize
-- under binders, which means both branches of a Church-encoded conditional
-- (like `(isZero n) Result base_case recursive_case`) are always fully
-- evaluated, even if only one is selected at runtime.
--
-- This causes the recursive branch to be evaluated even when not taken,
-- leading to fuel exhaustion. For example:
--   toZero = fix (λself. λn. (isZero n) Nat 0 (self (pred n)))
--   toZero 1 → fuel exhaustion (none)
--   because at n=0, the false-branch (self 0) is still evaluated
--
-- This is demonstrated below:
def toZero : Expr := .fix (.lam "self" NatToNat (.lam "n" Nat'
  (.app (.app (.app (.app isZero' (.var "n")) Nat') zero') (.app (.var "self") zero'))))

-- Recursive fix with Church branching exhausts fuel (returns none)
example : concEval testFuel [] (.app toZero one') = none := by native_decide

-- But abstract eval correctly returns the declared type
example : absEval testFuel [] toZero = some NatToNat := by native_decide

-- ANALYSIS: The env-based concEval CANNOT simply "stop normalizing under
-- binders" because the environment wouldn't be captured — free variables
-- in the body would be lost. The real fix requires either closures or
-- substitution-based evaluation. See concEvalS in Eval.lean and
-- DECISION-LOG.md for the full analysis.

-- ============================================================
-- §7.2 Substitution-based evaluator (concEvalS) tests
-- concEvalS treats lambdas as values (no normalization under binders),
-- uses substitution instead of environments.
-- ============================================================

-- Basic: concEvalS agrees with concEval on non-recursive examples

-- true X t f ⟶ t (using substitution-based eval)
-- We need closed terms, so instantiate X, t, f concretely
example : concEvalS testFuel (.app (.app (.app true' Nat') zero') one') = some zero' := by
  native_decide

-- false X t f ⟶ f
example : concEvalS testFuel (.app (.app (.app false' Nat') zero') one') = some one' := by
  native_decide

-- Non-recursive fix works with concEvalS
example : concEvalS testFuel (.app fixId three') = some three' := by
  native_decide
example : concEvalS testFuel (.app fixId zero') = some zero' := by
  native_decide

-- isZero 0 = true, isZero 1 = false
example : concEvalS testFuel (.app isZero' zero') = some true' := by native_decide
example : concEvalS testFuel (.app isZero' one') = some false' := by native_decide
example : concEvalS testFuel (.app isZero' three') = some false' := by native_decide

-- Note: concEvalS returns un-normalized lambdas, so `succ 2` is NOT
-- syntactically equal to `three'`. Instead, test behavior by applying
-- the result to concrete arguments (which forces full evaluation).
-- add 2 3 applied to Bool true (λ_.false) — tests if result behaves like 5
-- (5 Bool true (λ_.false) = (λ_.false) (... (λ_.false) true ...) = false for 5 > 0)
-- Simpler: just test concrete application chains work end-to-end
-- double 3 = 6, tested by checking (double 3) applies correctly
-- toZero (add 2 1) — exercises add producing a value that toZero can consume
-- (tested below in the recursive fix section)

-- ============================================================
-- §7.3 Recursive fix with thunked branches (concEvalS)
-- This is the KEY test: Church-encoded branching + recursion
-- that fails with the env-based concEval but works with concEvalS.
-- ============================================================

-- Helper: Unit → Nat function type
def UnitToNat : Expr := .lam "_" Unit' Nat'

-- toZeroThunked: recursive function that always returns 0.
-- Uses thunked branches: (isZero n) (Unit→Nat) (λ_.zero) (λ_.self zero) unit
-- The thunk lambdas are values in CBV, so the recursive branch is NOT
-- evaluated when isZero n = true (selecting the first thunk).
def toZeroThunked : Expr := .fix (.lam "self" NatToNat (.lam "n" Nat'
  (.app
    (.app (.app (.app (.app isZero' (.var "n")) UnitToNat)
      (.lam "_" Unit' zero'))
      (.lam "_" Unit' (.app (.var "self") zero')))
    unit')))

-- THE FIX: toZeroThunked terminates with concEvalS!
-- Compare: toZero (non-thunked) returns none with concEval (line above)
example : concEvalS testFuel (.app toZeroThunked zero') = some zero' := by native_decide
example : concEvalS testFuel (.app toZeroThunked one') = some zero' := by native_decide
example : concEvalS testFuel (.app toZeroThunked two') = some zero' := by native_decide
example : concEvalS testFuel (.app toZeroThunked three') = some zero' := by native_decide

-- Compose: toZeroThunked (add 2 1) = 0
-- add 2 1 returns a Church numeral (un-normalized lambda), and toZeroThunked
-- successfully recurses on it. This tests that the subst-based evaluator
-- handles Church numerals as arguments even when they're not in normal form.
example : concEvalS testFuel (.app toZeroThunked (.app (.app add' two') one')) = some zero' := by native_decide

-- Abstract eval of toZeroThunked returns the declared type (Nat → Nat)
-- (absEval is unchanged — it still normalizes under binders)
example : absEval testFuel [] toZeroThunked = some NatToNat := by native_decide

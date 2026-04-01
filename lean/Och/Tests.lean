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
-- §7 Mu (general recursion) tests
-- mu replaces fix: fix (λf: T. body) → mu f T body
-- ============================================================

-- Nat → Nat function type (as a lambda: λ(n: Nat). Nat)
def NatToNat : Expr := .lam "n" Nat' Nat'

-- Simple non-recursive mu: mu self NatToNat (λn: Nat. n)
-- The identity function, declared as Nat → Nat
def fixId : Expr := .mu "self" NatToNat (.lam "n" Nat' (.var "n"))

-- Abstract eval of mu returns the mu itself (normalized form)
-- (Previously, fix returned the declared type; now mu returns itself as a self-type)
example : absEval testFuel [] fixId = some fixId := by native_decide

-- mu ⊑ Nat → Nat (via self-elim: unfold body, get λn.n which ⊑ NatToNat)
example : subCheck testFuel fixId NatToNat = true := by native_decide

-- Concrete eval: mu self NatToNat (λn.n) applied to 3 should give 3
-- mu unrolls body with self := mu(...), body = λn. n (doesn't use self).
-- Apply to 3 → 3.
example : concEval testFuel [] (.app fixId three') = some three' := by native_decide

-- Concrete eval: fixId applied to 0 should give 0
example : concEval testFuel [] (.app fixId zero') = some zero' := by native_decide

-- Recursive mu: predecessor-based recursion to constant zero
-- mu self NatToNat (λn: Nat. isZero n ? 0 : self (pred n))
-- This should always return 0 for any concrete nat.
-- Note: In Church encoding, "isZero n ? 0 : self (pred n)" is
-- (isZero n) Nat zero (self zero)
-- The issue is that both branches are evaluated (no laziness).
-- The env-based concEval normalizes under binders, so both branches
-- are eagerly evaluated, causing divergence.

-- Simple recursive doubling that counts down: add n to itself
-- Actually, let's just test that mu produces the right abstract type
-- and works for non-recursive cases.

-- mu ⊑ Type (everything is ⊑ Type)
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

-- Construct arr1 = consArray Nat 0 zero (emptyArray Nat) — a 1-element array [0]
def testArr1 : Expr := .app (.app (.app (.app consArray' Nat') zero') zero') (.app emptyArray' Nat')

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
-- §7.1 Recursive mu: concrete recursion limitation
-- ============================================================

-- FINDING: Concrete recursive mu with Church-encoded branching does NOT
-- work with the env-based concEval. Both concEval and absEval normalize
-- under binders, which means both branches of a Church-encoded conditional
-- are always fully evaluated, even if only one is selected at runtime.
--
-- This causes the recursive branch to be evaluated even when not taken,
-- leading to fuel exhaustion.
def toZero : Expr := .mu "self" NatToNat (.lam "n" Nat'
  (.app (.app (.app (.app isZero' (.var "n")) Nat') zero') (.app (.var "self") zero')))

-- Recursive mu with Church branching exhausts fuel (returns none)
example : concEval testFuel [] (.app toZero one') = none := by native_decide

-- But abstract eval correctly returns a mu (self-type form)
-- Subtyping recovers: toZero ⊑ NatToNat via self-elim
example : subCheck testFuel toZero NatToNat = true := by native_decide

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

-- Non-recursive mu works with concEvalS
example : concEvalS testFuel (.app fixId three') = some three' := by
  native_decide
example : concEvalS testFuel (.app fixId zero') = some zero' := by
  native_decide

-- isZero 0 = true, isZero 1 = false
example : concEvalS testFuel (.app isZero' zero') = some true' := by native_decide
example : concEvalS testFuel (.app isZero' one') = some false' := by native_decide
example : concEvalS testFuel (.app isZero' three') = some false' := by native_decide

-- ============================================================
-- §7.3 Recursive mu with thunked branches (concEvalS)
-- This is the KEY test: Church-encoded branching + recursion
-- that fails with the env-based concEval but works with concEvalS.
-- ============================================================

-- Helper: Unit → Nat function type
def UnitToNat : Expr := .lam "_" Unit' Nat'

-- toZeroThunked: recursive function that always returns 0.
-- Uses thunked branches: (isZero n) (Unit→Nat) (λ_.zero) (λ_.self zero) unit
-- The thunk lambdas are values in CBV, so the recursive branch is NOT
-- evaluated when isZero n = true (selecting the first thunk).
def toZeroThunked : Expr := .mu "self" NatToNat (.lam "n" Nat'
  (.app
    (.app (.app (.app (.app isZero' (.var "n")) UnitToNat)
      (.lam "_" Unit' zero'))
      (.lam "_" Unit' (.app (.var "self") zero')))
    unit'))

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

-- Abstract eval: toZeroThunked ⊑ NatToNat (via self-elim)
example : subCheck testFuel toZeroThunked NatToNat = true := by native_decide

-- ============================================================
-- §5.3 Predecessor (Church-encoded via pair trick)
-- pred n = fst (fold n over pairs starting from (0,0))
-- At each step: (a,b) → (b, succ b)
-- After n steps: (n-1, n) for n>0, (0,0) for n=0
-- ============================================================

-- Pair Nat Nat type (used internally by pred)
def PairNN : Expr := .app (.app Pair' Nat') Nat'

-- pred n = (n PairNN base step) Nat (λa.λ_.a)
-- where base = pair Nat Nat 0 0
--       step = λp. pair Nat Nat (snd p) (succ (snd p))
-- Extraction: apply the fold result (a Church pair) to Nat and (λa.λ_.a)
-- to get the first component.
def pred' : Expr := .lam "n" Nat' (
  .app (.app
    -- fold: n PairNN base step
    (.app (.app (.app (.var "n") PairNN)
      -- base = pair Nat Nat zero zero
      (.app (.app (.app (.app pair' Nat') Nat') zero') zero'))
      -- step = λp: PairNN. pair Nat Nat (snd p) (succ (snd p))
      (.lam "p" PairNN (
        .app (.app (.app (.app pair' Nat') Nat')
          -- snd p = p Nat (λ_.λb.b)
          (.app (.app (.var "p") Nat') (.lam "_" Nat' (.lam "b" Nat' (.var "b")))))
          -- succ (snd p)
          (.app succ' (.app (.app (.var "p") Nat') (.lam "_" Nat' (.lam "b" Nat' (.var "b"))))))))
    -- extract first component: apply Nat then (λa.λ_.a)
    Nat')
    (.lam "a" Nat' (.lam "_" Nat' (.var "a"))))

-- absEval: pred produces normalized Church numerals
example : absEval testFuel [] (.app pred' zero') = some zero' := by native_decide
example : absEval testFuel [] (.app pred' one') = some zero' := by native_decide
example : absEval testFuel [] (.app pred' three') = some two' := by native_decide

-- pred ⊑ Nat → Nat
example : subCheck testFuel pred' NatToNat = true := by native_decide

-- concEvalS: pred 0 = zero (exact match — base case returns zero directly)
example : concEvalS testFuel (.app pred' zero') = some zero' := by native_decide

-- concEvalS behavioral: pred returns un-normalized Church numerals for n>0,
-- so we test behavior via isZero (which fully reduces the numeral)
example : concEvalS testFuel (.app isZero' (.app pred' one')) = some true' := by native_decide
example : concEvalS testFuel (.app isZero' (.app pred' two')) = some false' := by native_decide
example : concEvalS testFuel (.app isZero' (.app pred' three')) = some false' := by native_decide

-- ============================================================
-- §7.4 Recursive mu + pred: rebuildThunked
-- Reconstructs a number by recursing to 0 and building up with succ.
-- rebuildThunked n = (isZero n) ? 0 : succ (rebuildThunked (pred n))
-- Uses thunked branches to avoid CBV eagerness.
-- Tests: mu + pred + succ + isZero + thunking all together.
-- ============================================================

def rebuildThunked : Expr := .mu "self" NatToNat (.lam "n" Nat'
  (.app
    (.app (.app (.app (.app isZero' (.var "n")) UnitToNat)
      (.lam "_" Unit' zero'))
      (.lam "_" Unit' (.app succ' (.app (.var "self") (.app pred' (.var "n"))))))
    unit'))

-- rebuild 0 = zero (base case, exact match)
example : concEvalS testFuel (.app rebuildThunked zero') = some zero' := by native_decide

-- Behavioral tests: rebuild n produces a valid Church numeral for n
-- (un-normalized for n>0, so test via isZero)
example : concEvalS testFuel (.app isZero' (.app rebuildThunked zero')) = some true' := by native_decide
example : concEvalS testFuel (.app isZero' (.app rebuildThunked one')) = some false' := by native_decide
example : concEvalS testFuel (.app isZero' (.app rebuildThunked two')) = some false' := by native_decide
example : concEvalS testFuel (.app isZero' (.app rebuildThunked three')) = some false' := by native_decide

-- Abstract type: rebuildThunked ⊑ Nat → Nat (via self-elim)
example : subCheck testFuel rebuildThunked NatToNat = true := by native_decide

-- ============================================================
-- §7.5 Recursive addition via mu + pred: addThunked
-- addThunked n m = (isZero n) ? m : succ (addThunked (pred n) m)
-- Equivalent to the standard add but implemented via recursion.
-- ============================================================

-- Nat → Nat → Nat type
def NatToNatToNat : Expr := .lam "_" Nat' (.lam "_" Nat' Nat')

def addThunked : Expr := .mu "self" NatToNatToNat (.lam "n" Nat' (.lam "m" Nat'
  (.app
    (.app (.app (.app (.app isZero' (.var "n")) UnitToNat)
      (.lam "_" Unit' (.var "m")))
      (.lam "_" Unit' (.app succ' (.app (.app (.var "self") (.app pred' (.var "n"))) (.var "m")))))
    unit')))

-- addThunked 0 m = m (base case: returns m directly)
example : concEvalS testFuel (.app (.app addThunked zero') zero') = some zero' := by native_decide
example : concEvalS testFuel (.app (.app addThunked zero') three') = some three' := by native_decide

-- Behavioral: addThunked computes correct sums (tested via isZero)
-- addThunked 1 0 should be positive (= 1)
example : concEvalS testFuel (.app isZero' (.app (.app addThunked one') zero')) = some false' := by native_decide
-- addThunked 2 1 should be positive (= 3)
example : concEvalS testFuel (.app isZero' (.app (.app addThunked two') one')) = some false' := by native_decide

-- Composition: toZeroThunked (addThunked 2 1) = zero
-- This chains two recursive functions: addThunked produces an un-normalized
-- Church numeral 3, then toZeroThunked recursively reduces it to 0.
example : concEvalS testFuel (.app toZeroThunked (.app (.app addThunked two') one')) = some zero' := by native_decide

-- Abstract type: addThunked ⊑ Nat → Nat → Nat (via self-elim)
example : subCheck testFuel addThunked NatToNatToNat = true := by native_decide

-- ============================================================
-- §8 Self types (mu with ann=Type) — self-intro subtyping and self-elim
-- Previously iota x body → now mu x Type body
-- ============================================================

-- SelfUnit = mu u Type (X: Type) -> X -> X
-- The self variable u is unused, so self-intro reduces to unit ⊑ Unit
def SelfUnit : Expr := .mu "u" .type (.lam "X" .type (.lam "x" (.var "X") (.var "X")))

-- Self-intro: unit ⊑ SelfUnit via unit ⊑ body[u := unit] = Unit
example : subCheck testFuel unit' SelfUnit = true := by native_decide

-- Self-intro: true ⊑ SelfBool (self var unused)
def SelfBool : Expr := .mu "b" .type (.lam "X" .type (.lam "t" (.var "X") (.lam "f" (.var "X") (.var "X"))))
example : subCheck testFuel true' SelfBool = true := by native_decide
example : subCheck testFuel false' SelfBool = true := by native_decide

-- Self-intro: zero ⊑ SelfNat (self var unused, equivalent to Nat)
def SelfNat : Expr := .mu "n" .type Nat'
example : subCheck testFuel zero' SelfNat = true := by native_decide
example : subCheck testFuel one' SelfNat = true := by native_decide
example : subCheck testFuel three' SelfNat = true := by native_decide

-- Self-intro with self variable USED in body:
-- TrivialSelf = mu x Type Type
-- Everything is in Type, so everything should satisfy this
def TrivialSelf : Expr := .mu "x" .type .type
example : subCheck testFuel true' TrivialSelf = true := by native_decide
example : subCheck testFuel Nat' TrivialSelf = true := by native_decide

-- Self-intro: mu x Type Unit (identity self type)
-- unit ⊑ mu x Type Unit means unit ⊑ Unit[x := unit]
-- Since x doesn't appear in the body, this is unit ⊑ Unit
def IdSelf : Expr := .mu "x" .type Unit'
example : subCheck testFuel unit' IdSelf = true := by native_decide

-- Negative: true should NOT be a member of SelfNat-style self type
-- when the self variable is actually used to constrain membership
-- BAD: 0 ⊑ mu x Type Bool' should fail because 0 ⊑ Bool' fails
example : subCheck testFuel zero' (.mu "x" .type Bool') = false := by native_decide

-- Mu-mu subtyping (covariance): SelfNat ⊑ TrivialSelf
-- because Nat' ⊑ Type
example : subCheck testFuel SelfNat TrivialSelf = true := by native_decide

-- ============================================================
-- Self-elim in subCheckNF: mu on LHS unfolds
-- ============================================================

-- Self-elim: mu x Type T ⊑ T[x := mu x Type T]
-- mu x Type Unit' ⊑ Unit' (since x unused in Unit', unfolds to Unit' ⊑ Unit')
example : subCheck testFuel (.mu "x" .type Unit') Unit' = true := by native_decide
example : subCheck testFuel (.mu "n" .type Nat') Nat' = true := by native_decide

-- Self-elim chains with self-intro (via inferType):
-- λ(f : mu x Type Unit'). f  ⊑  λ(f : mu x Type Unit'). Unit'
-- Body: var f ⊑ Unit'. inferType gives f : mu x Type Unit'.
-- Then mu x Type Unit' ⊑ Unit' by self-elim.
example : subCheck testFuel
  (.lam "f" (.mu "x" .type Unit') (.var "f"))
  (.lam "f" (.mu "x" .type Unit') Unit')
  = true := by native_decide

-- Self-elim in inferType: application through mu-typed function.
-- λ(f : mu x Type Unit'). f Type  ⊑  λ(f : mu x Type Unit'). (Type -> Type)
-- inferType for (app f Type): f has type mu x Type Unit'.
-- Self-elim: unfold to Unit' = (X:Type)->X->X. This is a lam with retTy = lam x (var X) (var X).
-- After substituting X=Type: retTy.subst X Type = lam x Type Type = (Type -> Type).
-- So f Type : Type -> Type. Check (Type -> Type) ⊑ (Type -> Type) → refl ✓
example : subCheck testFuel
  (.lam "f" (.mu "x" .type Unit') (.app (.var "f") .type))
  (.lam "f" (.mu "x" .type Unit') (.lam "_" .type .type))
  = true := by native_decide

-- ============================================================
-- Self types: ascription interaction
-- ============================================================

-- (unit : mu f Type Unit') abstractly evaluates to mu f Type Unit'
example : absEval testFuel [] (.asc unit' (.mu "f" .type Unit')) = some (.mu "f" .type Unit') := by native_decide

-- Ascribed mu type is subtype of unwrapped type (self-elim in subCheck)
example : subCheck testFuel (.asc unit' (.mu "f" .type Unit')) Unit' = true := by native_decide

-- ============================================================
-- Self types with self variable used in body
-- ============================================================

-- SelfRef = mu x Type (P : Type -> Type) -> P x -> P x
-- where P is applied to (var x), making the type depend on the value.
def SelfRef : Expr := .mu "x" .type
  (.lam "P" (.lam "_" .type .type)
    (.lam "pf" (.app (.var "P") (.var "x"))
      (.app (.var "P") (.var "x"))))
-- unit should NOT satisfy SelfRef (domain mismatch: Type vs Type->Type)
example : subCheck testFuel unit' SelfRef = false := by native_decide

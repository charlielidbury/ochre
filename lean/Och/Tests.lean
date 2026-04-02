import Och.Syntax
import Och.Eval
import Och.Subtyping
import Och.Soundness

/-!
# Och Test Suite (de Bruijn)

These tests encode the acceptance criteria from docs/och-spec.md §6.
They pin down the expressiveness of the language.

DO NOT WEAKEN THESE TESTS.

All term definitions use `Named` syntax (human-readable string variables)
converted to de Bruijn via `n`. The native_decide tests verify correctness
end-to-end.
-/

open Expr Named

-- ============================================================
-- Standard library (Church encodings)
-- These mirror docs/och-spec.md §5 exactly.
-- ============================================================

-- Booleans
def Bool'_n : Named := .lam "X" .type (.lam "t" (.var "X") (.lam "f" (.var "X") (.var "X")))
def true'_n : Named := .lam "X" .type (.lam "t" (.var "X") (.lam "f" (.var "X") (.var "t")))
def false'_n : Named := .lam "X" .type (.lam "t" (.var "X") (.lam "f" (.var "X") (.var "f")))

def Bool' : Expr := n Bool'_n
def true'  : Expr := n true'_n
def false' : Expr := n false'_n

-- Unit
def Unit'_n : Named := .lam "X" .type (.lam "x" (.var "X") (.var "X"))
def unit'_n : Named := .lam "X" .type (.lam "x" (.var "X") (.var "x"))
def Unit' : Expr := n Unit'_n
def unit' : Expr := n unit'_n

-- Natural numbers
def Nat'_n : Named := .lam "X" .type (.lam "z" (.var "X") (.lam "s" (.lam "_" (.var "X") (.var "X")) (.var "X")))
def zero'_n : Named := .lam "X" .type (.lam "z" (.var "X") (.lam "s" (.lam "_" (.var "X") (.var "X")) (.var "z")))
def one'_n  : Named := .lam "X" .type (.lam "z" (.var "X") (.lam "s" (.lam "_" (.var "X") (.var "X")) (.app (.var "s") (.var "z"))))
def two'_n  : Named := .lam "X" .type (.lam "z" (.var "X") (.lam "s" (.lam "_" (.var "X") (.var "X")) (.app (.var "s") (.app (.var "s") (.var "z")))))
def three'_n : Named := .lam "X" .type (.lam "z" (.var "X") (.lam "s" (.lam "_" (.var "X") (.var "X")) (.app (.var "s") (.app (.var "s") (.app (.var "s") (.var "z"))))))

def Nat' : Expr := n Nat'_n
def zero' : Expr := n zero'_n
def one'  : Expr := n one'_n
def two'  : Expr := n two'_n
def three' : Expr := n three'_n

def succ'_n : Named := .lam "n" Nat'_n (
  .lam "X" .type (.lam "z" (.var "X") (.lam "s" (.lam "_" (.var "X") (.var "X"))
    (.app (.var "s") (.app (.app (.app (.var "n") (.var "X")) (.var "z")) (.var "s"))))))
def succ' : Expr := n succ'_n

-- More Church numerals
def four'_n : Named := .lam "X" .type (.lam "z" (.var "X") (.lam "s" (.lam "_" (.var "X") (.var "X"))
  (.app (.var "s") (.app (.var "s") (.app (.var "s") (.app (.var "s") (.var "z")))))))
def five'_n : Named := .lam "X" .type (.lam "z" (.var "X") (.lam "s" (.lam "_" (.var "X") (.var "X"))
  (.app (.var "s") (.app (.var "s") (.app (.var "s") (.app (.var "s") (.app (.var "s") (.var "z"))))))))
def six'_n : Named := .lam "X" .type (.lam "z" (.var "X") (.lam "s" (.lam "_" (.var "X") (.var "X"))
  (.app (.var "s") (.app (.var "s") (.app (.var "s") (.app (.var "s") (.app (.var "s") (.app (.var "s") (.var "z")))))))))

def four' : Expr := n four'_n
def five' : Expr := n five'_n
def six' : Expr := n six'_n

-- add = λ(n: Nat). λ(m: Nat). n Nat m succ
def add'_n : Named := .lam "n" Nat'_n (.lam "m" Nat'_n
  (.app (.app (.app (.var "n") Nat'_n) (.var "m")) succ'_n))
def add' : Expr := n add'_n

-- isZero = λ(n: Nat). n Bool true (λ(_: Bool). false)
def isZero'_n : Named := .lam "n" Nat'_n
  (.app (.app (.app (.var "n") Bool'_n) true'_n) (.lam "_" Bool'_n false'_n))
def isZero' : Expr := n isZero'_n

-- double = λ(x: Nat). add x x
def double'_n : Named := .lam "x" Nat'_n (.app (.app add'_n (.var "x")) (.var "x"))
def double' : Expr := n double'_n

-- id (for transparency tests)
def id'_n : Named := .lam "T" .type (.lam "x" (.var "T") (.var "x"))
def idAscribed_n : Named := .lam "T" .type (.lam "x" (.var "T") (.asc (.var "x") (.var "T")))
def id' : Expr := n id'_n
def idAscribed : Expr := n idAscribed_n

-- ============================================================
-- Fuel for evaluation (generous)
-- ============================================================
def testFuel : Nat := 1000

-- ============================================================
-- §6.1 Concrete evaluation: precision tests
-- ============================================================

-- Concrete eval: true X t f ⟶ t  (in env with X, t, f as neutral)
example : concEval testFuel [.bvar 2, .bvar 1, .bvar 0]
    (.app (.app (.app true' (.bvar 2)) (.bvar 1)) (.bvar 0)) = some (.bvar 1) := by
  native_decide

-- Concrete eval: false X t f ⟶ f
example : concEval testFuel [.bvar 2, .bvar 1, .bvar 0]
    (.app (.app (.app false' (.bvar 2)) (.bvar 1)) (.bvar 0)) = some (.bvar 0) := by
  native_decide

-- ============================================================
-- §6.1 Abstract evaluation: precision tests
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

-- succ ⊑ (Nat → Nat)
def NatToNat_n : Named := .lam "n" Nat'_n Nat'_n
def NatToNat : Expr := n NatToNat_n
example : subCheck testFuel succ' NatToNat = true := by native_decide

-- ============================================================
-- Regression test: Proposition 5.2.9 counterexample
-- ============================================================

def Not'_n : Named := .lam "X" Bool'_n (.app (.app (.app (.var "X") Bool'_n) false'_n) true'_n)
def Not' : Expr := n Not'_n

example : absEval testFuel [] (.app Not' true') = some false' := by native_decide
example : absEval testFuel [] (.app Not' false') = some true' := by native_decide
example : absEval testFuel [] (.app Not' Bool') = some Bool' := by native_decide

example : subCheck testFuel false' true' = false := by native_decide
example : subCheck testFuel (.app Not' true') Bool' = true := by native_decide
example : subCheck testFuel (.app Not' false') Bool' = true := by native_decide

-- ============================================================
-- §7 Mu (general recursion) tests
-- ============================================================

def fixId_n : Named := .mu "self" NatToNat_n (.lam "n" Nat'_n (.var "n"))
def fixId : Expr := n fixId_n

example : absEval testFuel [] fixId = some fixId := by native_decide
example : subCheck testFuel fixId NatToNat = true := by native_decide

example : concEval testFuel [] (.app fixId three') = some three' := by native_decide
example : concEval testFuel [] (.app fixId zero') = some zero' := by native_decide

example : subCheck testFuel fixId .type = true := by native_decide

-- ============================================================
-- §5.4–5.8 Pairs, Arrays, Vectors (Church-encoded data structures)
-- ============================================================

def Pair'_n : Named := .lam "A" .type (.lam "B" .type (
  .lam "X" .type (.lam "k" (.lam "_" (.var "A") (.lam "_" (.var "B") (.var "X"))) (.var "X"))))
def Pair' : Expr := n Pair'_n

def pair'_n : Named := .lam "A" .type (.lam "B" .type (.lam "a" (.var "A") (.lam "b" (.var "B") (
  .lam "X" .type (.lam "k" (.lam "_" (.var "A") (.lam "_" (.var "B") (.var "X")))
    (.app (.app (.var "k") (.var "a")) (.var "b")))))))
def pair' : Expr := n pair'_n

def Array'_n : Named := .lam "n" Nat'_n (.lam "T" .type (
  .app (.app (.app (.var "n") .type) Unit'_n) (.lam "acc" .type (
    .app (.app Pair'_n (.var "T")) (.var "acc")))))
def Array' : Expr := n Array'_n

def emptyArray'_n : Named := .lam "T" .type unit'_n
def emptyArray' : Expr := n emptyArray'_n

def consArray'_n : Named := .lam "T" .type (.lam "n" Nat'_n (.lam "x" (.var "T") (.lam "rest" (.app (.app Array'_n (.var "n")) (.var "T")) (
  .app (.app (.app (.app pair'_n (.var "T")) (.app (.app Array'_n (.var "n")) (.var "T"))) (.var "x")) (.var "rest")))))
def consArray' : Expr := n consArray'_n

def headArray'_n : Named := .lam "T" .type (.lam "n" Nat'_n (.lam "arr" (.app (.app Array'_n (.app succ'_n (.var "n"))) (.var "T")) (
  .app (.app (.var "arr") (.var "T")) (.lam "x" (.var "T") (.lam "_" (.app (.app Array'_n (.var "n")) (.var "T")) (.var "x"))))))
def headArray' : Expr := n headArray'_n

def tailArray'_n : Named := .lam "T" .type (.lam "n" Nat'_n (.lam "arr" (.app (.app Array'_n (.app succ'_n (.var "n"))) (.var "T")) (
  .app (.app (.var "arr") (.app (.app Array'_n (.var "n")) (.var "T"))) (.lam "_" (.var "T") (.lam "rest" (.app (.app Array'_n (.var "n")) (.var "T")) (.var "rest"))))))
def tailArray' : Expr := n tailArray'_n

-- Array tests
example : absEval testFuel [] (.app (.app Array' zero') Nat') = some Unit' := by native_decide

def testArr1 : Expr := n (.app (.app (.app (.app consArray'_n Nat'_n) zero'_n) zero'_n) (.app emptyArray'_n Nat'_n))
example : subCheck testFuel testArr1 (.app (.app Array' one') Nat') = true := by native_decide
example : absEval testFuel [] (.app (.app (.app headArray' Nat') zero') testArr1) = some zero' := by native_decide

def testArr2 : Expr := n (.app (.app (.app (.app consArray'_n Nat'_n) one'_n) one'_n)
  (.app (.app (.app (.app consArray'_n Nat'_n) zero'_n) two'_n) (.app emptyArray'_n Nat'_n)))
example : subCheck testFuel testArr2 (.app (.app Array' two') Nat') = true := by native_decide
example : absEval testFuel [] (.app (.app (.app headArray' Nat') one') testArr2) = some one' := by native_decide

-- ============================================================
-- §5.8 Vectors (Sigma types)
-- ============================================================

def Sigma'_n : Named := .lam "A" .type (.lam "B" (.lam "_" (.var "A") .type) (
  .lam "X" .type (.lam "k" (.lam "a" (.var "A") (.lam "_" (.app (.var "B") (.var "a")) (.var "X"))) (.var "X"))))
def Sigma' : Expr := n Sigma'_n

def dpair'_n : Named := .lam "A" .type (.lam "B" (.lam "_" (.var "A") .type) (
  .lam "a" (.var "A") (.lam "b" (.app (.var "B") (.var "a")) (
    .lam "X" .type (.lam "k" (.lam "a2" (.var "A") (.lam "_" (.app (.var "B") (.var "a2")) (.var "X")))
      (.app (.app (.var "k") (.var "a")) (.var "b")))))))
def dpair' : Expr := n dpair'_n

def Vec'_n : Named := .lam "T" .type (
  .app (.app Sigma'_n Nat'_n) (.lam "n" Nat'_n (.app (.app Array'_n (.var "n")) (.var "T"))))
def Vec' : Expr := n Vec'_n

def mkVec'_n : Named := .lam "T" .type (.lam "n" Nat'_n (.lam "arr" (.app (.app Array'_n (.var "n")) (.var "T")) (
  .app (.app (.app (.app dpair'_n Nat'_n) (.lam "n2" Nat'_n (.app (.app Array'_n (.var "n2")) (.var "T")))) (.var "n")) (.var "arr"))))
def mkVec' : Expr := n mkVec'_n

def testVec1 : Expr := n (.app (.app (.app mkVec'_n Nat'_n) one'_n) (.app (.app (.app (.app consArray'_n Nat'_n) zero'_n) zero'_n) (.app emptyArray'_n Nat'_n)))
example : subCheck testFuel testVec1 (.app Vec' Nat') = true := by native_decide

-- Unpack vec1 to get length
example : absEval testFuel [] (.app (.app testVec1 Nat') (n (.lam "n" Nat'_n (.lam "arr" (.app (.app Array'_n (.var "n")) Nat'_n) (.var "n"))))) = some one' := by native_decide

-- tailArray test
example : absEval testFuel [] (.app (.app (.app tailArray' Nat') zero') testArr1) = some unit' := by native_decide

-- headArray of tailArray
example : absEval testFuel [] (.app (.app (.app headArray' Nat') zero')
  (.app (.app (.app tailArray' Nat') one') testArr2)) = some two' := by native_decide

def testVec2 : Expr := n (.app (.app (.app mkVec'_n Nat'_n) two'_n) (.app (.app (.app (.app consArray'_n Nat'_n) one'_n) one'_n)
  (.app (.app (.app (.app consArray'_n Nat'_n) zero'_n) two'_n) (.app emptyArray'_n Nat'_n))))
example : subCheck testFuel testVec2 (.app Vec' Nat') = true := by native_decide

-- Unpack vec2 to get length
example : absEval testFuel [] (.app (.app testVec2 Nat') (n (.lam "n" Nat'_n (.lam "arr" (.app (.app Array'_n (.var "n")) Nat'_n) (.var "n"))))) = some two' := by native_decide

-- ============================================================
-- §6.2 Abstract instantiation tests
-- ============================================================

-- Abstract vector unpack
example : absEval testFuel [] (.app (.app (.asc unit' (.app Vec' Nat')) Nat')
  (n (.lam "n" Nat'_n (.lam "arr" (.app (.app Array'_n (.var "n")) Nat'_n) (.var "n")))))
  = some Nat' := by native_decide

-- Rewrapped abstract vector ⊑ Vec Nat
example : subCheck testFuel
  (.app (.app (.asc unit' (.app Vec' Nat')) (.app Vec' Nat'))
    (n (.lam "n" Nat'_n (.lam "arr" (.app (.app Array'_n (.var "n")) Nat'_n)
      (.app (.app (.app mkVec'_n Nat'_n) (.var "n")) (.var "arr"))))))
  (.app Vec' Nat') = true := by native_decide

-- Abstract Nat: add (... : Nat) (... : Nat) ⊑ Nat
example : subCheck testFuel
  (.app (.app add' (.asc unit' Nat')) (.asc unit' Nat'))
  Nat' = true := by native_decide

-- succ (... : Nat) ⊑ Nat
example : subCheck testFuel
  (.app succ' (.asc unit' Nat'))
  Nat' = true := by native_decide

-- isZero (succ (... : Nat)) = false (precisely!)
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

-- BAD5: emptyArray Nat ≠ Array 1 Nat
example : subCheck testFuel (.app emptyArray' Nat') (.app (.app Array' one') Nat') = false := by native_decide

-- ============================================================
-- §7.1 Recursive mu: concrete recursion limitation
-- ============================================================

def toZero_n : Named := .mu "self" NatToNat_n (.lam "n" Nat'_n
  (.app (.app (.app (.app isZero'_n (.var "n")) Nat'_n) zero'_n) (.app (.var "self") zero'_n)))
def toZero : Expr := n toZero_n

-- De Bruijn + subst-based beta: concEval now terminates here (mu body
-- normalization resolves self zero = zero; old env-based beta diverged)
example : concEval testFuel [] (.app toZero one') = some zero' := by native_decide
example : subCheck testFuel toZero NatToNat = true := by native_decide

-- ============================================================
-- §7.2 Substitution-based evaluator (concEvalS) tests
-- ============================================================

example : concEvalS testFuel (.app (.app (.app true' Nat') zero') one') = some zero' := by
  native_decide

example : concEvalS testFuel (.app (.app (.app false' Nat') zero') one') = some one' := by
  native_decide

example : concEvalS testFuel (.app fixId three') = some three' := by
  native_decide
example : concEvalS testFuel (.app fixId zero') = some zero' := by
  native_decide

example : concEvalS testFuel (.app isZero' zero') = some true' := by native_decide
example : concEvalS testFuel (.app isZero' one') = some false' := by native_decide
example : concEvalS testFuel (.app isZero' three') = some false' := by native_decide

-- ============================================================
-- §7.3 Recursive mu with thunked branches (concEvalS)
-- ============================================================

def UnitToNat_n : Named := .lam "_" Unit'_n Nat'_n
def UnitToNat : Expr := n UnitToNat_n

def toZeroThunked_n : Named := .mu "self" NatToNat_n (.lam "n" Nat'_n
  (.app
    (.app (.app (.app (.app isZero'_n (.var "n")) UnitToNat_n)
      (.lam "_" Unit'_n zero'_n))
      (.lam "_" Unit'_n (.app (.var "self") zero'_n)))
    unit'_n))
def toZeroThunked : Expr := n toZeroThunked_n

example : concEvalS testFuel (.app toZeroThunked zero') = some zero' := by native_decide
example : concEvalS testFuel (.app toZeroThunked one') = some zero' := by native_decide
example : concEvalS testFuel (.app toZeroThunked two') = some zero' := by native_decide
example : concEvalS testFuel (.app toZeroThunked three') = some zero' := by native_decide

-- Compose: toZeroThunked (add 2 1) = 0
example : concEvalS testFuel (.app toZeroThunked (.app (.app add' two') one')) = some zero' := by native_decide

example : subCheck testFuel toZeroThunked NatToNat = true := by native_decide

-- ============================================================
-- §5.3 Predecessor
-- ============================================================

def PairNN_n : Named := .app (.app Pair'_n Nat'_n) Nat'_n

def pred'_n : Named := .lam "n" Nat'_n (
  .app (.app
    (.app (.app (.app (.var "n") PairNN_n)
      (.app (.app (.app (.app pair'_n Nat'_n) Nat'_n) zero'_n) zero'_n))
      (.lam "p" PairNN_n (
        .app (.app (.app (.app pair'_n Nat'_n) Nat'_n)
          (.app (.app (.var "p") Nat'_n) (.lam "_" Nat'_n (.lam "b" Nat'_n (.var "b")))))
          (.app succ'_n (.app (.app (.var "p") Nat'_n) (.lam "_" Nat'_n (.lam "b" Nat'_n (.var "b"))))))))
    Nat'_n)
    (.lam "a" Nat'_n (.lam "_" Nat'_n (.var "a"))))
def pred' : Expr := n pred'_n

example : absEval testFuel [] (.app pred' zero') = some zero' := by native_decide
example : absEval testFuel [] (.app pred' one') = some zero' := by native_decide
example : absEval testFuel [] (.app pred' three') = some two' := by native_decide
example : subCheck testFuel pred' NatToNat = true := by native_decide

example : concEvalS testFuel (.app pred' zero') = some zero' := by native_decide
example : concEvalS testFuel (.app isZero' (.app pred' one')) = some true' := by native_decide
example : concEvalS testFuel (.app isZero' (.app pred' two')) = some false' := by native_decide
example : concEvalS testFuel (.app isZero' (.app pred' three')) = some false' := by native_decide

-- ============================================================
-- §7.4 Recursive mu + pred: rebuildThunked
-- ============================================================

def rebuildThunked_n : Named := .mu "self" NatToNat_n (.lam "n" Nat'_n
  (.app
    (.app (.app (.app (.app isZero'_n (.var "n")) UnitToNat_n)
      (.lam "_" Unit'_n zero'_n))
      (.lam "_" Unit'_n (.app succ'_n (.app (.var "self") (.app pred'_n (.var "n"))))))
    unit'_n))
def rebuildThunked : Expr := n rebuildThunked_n

example : concEvalS testFuel (.app rebuildThunked zero') = some zero' := by native_decide
example : concEvalS testFuel (.app isZero' (.app rebuildThunked zero')) = some true' := by native_decide
example : concEvalS testFuel (.app isZero' (.app rebuildThunked one')) = some false' := by native_decide
example : concEvalS testFuel (.app isZero' (.app rebuildThunked two')) = some false' := by native_decide
example : concEvalS testFuel (.app isZero' (.app rebuildThunked three')) = some false' := by native_decide
example : subCheck testFuel rebuildThunked NatToNat = true := by native_decide

-- ============================================================
-- §7.5 Recursive addition via mu + pred: addThunked
-- ============================================================

def NatToNatToNat_n : Named := .lam "_" Nat'_n (.lam "_" Nat'_n Nat'_n)
def NatToNatToNat : Expr := n NatToNatToNat_n

def addThunked_n : Named := .mu "self" NatToNatToNat_n (.lam "n" Nat'_n (.lam "m" Nat'_n
  (.app
    (.app (.app (.app (.app isZero'_n (.var "n")) UnitToNat_n)
      (.lam "_" Unit'_n (.var "m")))
      (.lam "_" Unit'_n (.app succ'_n (.app (.app (.var "self") (.app pred'_n (.var "n"))) (.var "m")))))
    unit'_n)))
def addThunked : Expr := n addThunked_n

example : concEvalS testFuel (.app (.app addThunked zero') zero') = some zero' := by native_decide
example : concEvalS testFuel (.app (.app addThunked zero') three') = some three' := by native_decide
example : concEvalS testFuel (.app isZero' (.app (.app addThunked one') zero')) = some false' := by native_decide
example : concEvalS testFuel (.app isZero' (.app (.app addThunked two') one')) = some false' := by native_decide

example : concEvalS testFuel (.app toZeroThunked (.app (.app addThunked two') one')) = some zero' := by native_decide

example : subCheck testFuel addThunked NatToNatToNat = true := by native_decide

-- ============================================================
-- §8 Self types (mu with ann=Type)
-- ============================================================

def SelfUnit_n : Named := .mu "u" .type (.lam "X" .type (.lam "x" (.var "X") (.var "X")))
def SelfUnit : Expr := n SelfUnit_n
example : subCheck testFuel unit' SelfUnit = true := by native_decide

def SelfBool_n : Named := .mu "b" .type (.lam "X" .type (.lam "t" (.var "X") (.lam "f" (.var "X") (.var "X"))))
def SelfBool : Expr := n SelfBool_n
example : subCheck testFuel true' SelfBool = true := by native_decide
example : subCheck testFuel false' SelfBool = true := by native_decide

def SelfNat_n : Named := .mu "n" .type Nat'_n
def SelfNat : Expr := n SelfNat_n
example : subCheck testFuel zero' SelfNat = true := by native_decide
example : subCheck testFuel one' SelfNat = true := by native_decide
example : subCheck testFuel three' SelfNat = true := by native_decide

def TrivialSelf_n : Named := .mu "x" .type .type
def TrivialSelf : Expr := n TrivialSelf_n
example : subCheck testFuel true' TrivialSelf = true := by native_decide
example : subCheck testFuel Nat' TrivialSelf = true := by native_decide

def IdSelf_n : Named := .mu "x" .type Unit'_n
def IdSelf : Expr := n IdSelf_n
example : subCheck testFuel unit' IdSelf = true := by native_decide

-- Negative: 0 ⊑ mu x Type Bool' should fail
example : subCheck testFuel zero' (n (.mu "x" .type Bool'_n)) = false := by native_decide

-- Mu-mu subtyping
example : subCheck testFuel SelfNat TrivialSelf = true := by native_decide

-- Self-elim
example : subCheck testFuel (n (.mu "x" .type Unit'_n)) Unit' = true := by native_decide
example : subCheck testFuel (n (.mu "n" .type Nat'_n)) Nat' = true := by native_decide

-- Self-elim chains
example : subCheck testFuel
  (n (.lam "f" (.mu "x" .type Unit'_n) (.var "f")))
  (n (.lam "f" (.mu "x" .type Unit'_n) Unit'_n))
  = true := by native_decide

-- Self-elim in inferType
example : subCheck testFuel
  (n (.lam "f" (.mu "x" .type Unit'_n) (.app (.var "f") .type)))
  (n (.lam "f" (.mu "x" .type Unit'_n) (.lam "_" .type .type)))
  = true := by native_decide

-- Ascription interaction
example : absEval testFuel [] (.asc unit' (n (.mu "f" .type Unit'_n))) = some (n (.mu "f" .type Unit'_n)) := by native_decide
example : subCheck testFuel (.asc unit' (n (.mu "f" .type Unit'_n))) Unit' = true := by native_decide

-- Self types with self variable used
def SelfRef_n : Named := .mu "x" .type
  (.lam "P" (.lam "_" .type .type)
    (.lam "pf" (.app (.var "P") (.var "x"))
      (.app (.var "P") (.var "x"))))
def SelfRef : Expr := n SelfRef_n
example : subCheck testFuel unit' SelfRef = false := by native_decide

-- ============================================================
-- §9 Abstract add with self-typed Nat
-- ============================================================

def addSelfNat_n : Named := .lam "n" SelfNat_n (.lam "m" SelfNat_n
  (.app (.app (.app (.var "n") Nat'_n) (.var "m")) succ'_n))
def addSelfNat : Expr := n addSelfNat_n

example : absEval testFuel []
  (.app (.app addSelfNat (.asc unit' SelfNat)) (.asc unit' SelfNat))
  = some Nat' := by native_decide

example : subCheck testFuel
  (.app (.app addSelfNat (.asc unit' SelfNat)) (.asc unit' SelfNat))
  Nat' = true := by native_decide

example : subCheck testFuel
  (.app (.app addSelfNat (.asc unit' SelfNat)) (.asc unit' SelfNat))
  SelfNat = true := by native_decide

example : subCheck testFuel addSelfNat
  (n (.lam "n" SelfNat_n (.lam "m" SelfNat_n Nat'_n))) = true := by native_decide

example : absEval testFuel []
  (.app (.app addSelfNat two') three') = some five' := by native_decide

-- ============================================================
-- §10 Variant B: truly self-referential Nat (Cedille-style)
-- ============================================================

def MuNat_n : Named := .mu "N" .type
  (.lam "X" .type (.lam "z" (.var "X")
    (.lam "s" (.lam "_" (.var "N") (.lam "_" (.var "X") (.var "X")))
      (.var "X"))))
def MuNat : Expr := n MuNat_n

def zero_mu_n : Named := .lam "X" .type (.lam "z" (.var "X")
  (.lam "s" (.lam "_" MuNat_n (.lam "_" (.var "X") (.var "X")))
    (.var "z")))
def zero_mu : Expr := n zero_mu_n

def add_mu_n : Named := .lam "n" MuNat_n (.lam "m" MuNat_n
  (.app (.app (.app (.var "n") MuNat_n) (.var "m"))
    (.lam "k" MuNat_n (.lam "acc" MuNat_n (.app succ'_n (.var "acc"))))))
def add_mu : Expr := n add_mu_n

example : absEval testFuel []
  (.app (.app add_mu (.asc unit' MuNat)) (.asc unit' MuNat))
  = some MuNat := by native_decide

example : subCheck testFuel zero_mu MuNat = true := by native_decide

example : subCheck testFuel add_mu
  (n (.lam "_" MuNat_n (.lam "_" MuNat_n MuNat_n))) = true := by native_decide

-- ============================================================
-- §11 Milestone ladder: road to abstract appendVec
-- ============================================================

-- ---------- M1: Recursive add via mu ----------

def addRec_n : Named := .mu "self" (.lam "_" SelfNat_n (.lam "_" SelfNat_n Nat'_n))
  (.lam "n" SelfNat_n (.lam "m" SelfNat_n
    (.app
      (.app (.app (.app (.app isZero'_n (.var "n")) UnitToNat_n)
        (.lam "_" Unit'_n (.var "m")))
        (.lam "_" Unit'_n (.app succ'_n (.app (.app (.var "self") (.app pred'_n (.var "n"))) (.var "m")))))
      unit'_n)))
def addRec : Expr := n addRec_n

-- M1a
example : subCheck testFuel addRec
  (n (.lam "_" SelfNat_n (.lam "_" SelfNat_n Nat'_n))) = true := by native_decide

-- M1b
example : concEvalS testFuel (.app (.app addRec zero') three') = some three' := by native_decide

-- M1c
example : concEvalS testFuel
  (.app isZero' (.app (.app addRec two') one')) = some false' := by native_decide

-- M1d
example : subCheck testFuel
  (.app (.app addRec (.asc unit' SelfNat)) (.asc unit' SelfNat))
  Nat' = true := by native_decide

-- ---------- M2: mapArray ----------

def mapArray'_n : Named := .mu "self"
  (.lam "_" .type (.lam "_" .type (.lam "_" (.lam "_" Nat'_n Nat'_n) (.lam "_" Nat'_n (.lam "_" .type .type)))))
  (.lam "T" .type (.lam "U" .type (.lam "f" (.lam "_" (.var "T") (.var "U"))
    (.lam "n" Nat'_n (.lam "arr" (.app (.app Array'_n (.var "n")) (.var "T"))
      (.app
        (.app (.app (.app (.app isZero'_n (.var "n"))
          (.lam "_" Unit'_n .type))
          (.lam "_" Unit'_n (.app emptyArray'_n (.var "U"))))
          (.lam "_" Unit'_n
            (.app (.app (.app (.app consArray'_n (.var "U")) (.app pred'_n (.var "n")))
              (.app (.var "f")
                (.app (.app (.app headArray'_n (.var "T")) (.app pred'_n (.var "n"))) (.var "arr"))))
              (.app (.app (.app (.app (.app (.var "self") (.var "T")) (.var "U")) (.var "f"))
                (.app pred'_n (.var "n")))
                (.app (.app (.app tailArray'_n (.var "T")) (.app pred'_n (.var "n"))) (.var "arr"))))))
        unit'_n))))))
def mapArray' : Expr := n mapArray'_n

-- M2a
example : concEvalS testFuel
  (.app (.app (.app (.app (.app mapArray' Nat') Nat') succ') zero') (.app emptyArray' Nat'))
  = some unit' := by native_decide

-- ---------- M3: appendArrays ----------

def appendArrays'_n : Named := .mu "self"
  (.lam "_" .type (.lam "_" Nat'_n (.lam "_" Nat'_n (.lam "_" .type (.lam "_" .type .type)))))
  (.lam "T" .type (.lam "n" Nat'_n (.lam "m" Nat'_n
    (.lam "a" (.app (.app Array'_n (.var "n")) (.var "T"))
      (.lam "b" (.app (.app Array'_n (.var "m")) (.var "T"))
        (.app
          (.app (.app (.app (.app isZero'_n (.var "n"))
            (.lam "_" Unit'_n .type))
            (.lam "_" Unit'_n (.var "b")))
            (.lam "_" Unit'_n
              (.app (.app (.app (.app consArray'_n (.var "T"))
                (.app (.app add'_n (.app pred'_n (.var "n"))) (.var "m")))
                (.app (.app (.app headArray'_n (.var "T")) (.app pred'_n (.var "n"))) (.var "a")))
                (.app (.app (.app (.app (.app (.var "self") (.var "T"))
                  (.app pred'_n (.var "n"))) (.var "m"))
                  (.app (.app (.app tailArray'_n (.var "T")) (.app pred'_n (.var "n"))) (.var "a")))
                  (.var "b")))))
          unit'_n))))))
def appendArrays' : Expr := n appendArrays'_n

-- M3a
example : concEvalS testFuel
  (.app (.app (.app (.app (.app appendArrays' Nat') zero') zero')
    (.app emptyArray' Nat')) (.app emptyArray' Nat'))
  = some unit' := by native_decide

-- ---------- M4: appendVec (THE NORTH STAR) ----------

def appendVec'_n : Named :=
  .lam "T" .type (.lam "v1" (.app Vec'_n (.var "T")) (.lam "v2" (.app Vec'_n (.var "T"))
    (.app (.app (.var "v1") (.app Vec'_n (.var "T")))
      (.lam "n1" Nat'_n (.lam "arr1" (.app (.app Array'_n (.var "n1")) (.var "T"))
        (.app (.app (.var "v2") (.app Vec'_n (.var "T")))
          (.lam "n2" Nat'_n (.lam "arr2" (.app (.app Array'_n (.var "n2")) (.var "T"))
            (.app (.app (.app mkVec'_n (.var "T"))
              (.app (.app add'_n (.var "n1")) (.var "n2")))
              (.app (.app (.app (.app (.app appendArrays'_n (.var "T"))
                (.var "n1")) (.var "n2")) (.var "arr1")) (.var "arr2")))))))))))
def appendVec' : Expr := n appendVec'_n

-- M4a
example : subCheck testFuel appendVec'
  (n (.lam "T" .type (.lam "_" (.app Vec'_n (.var "T"))
    (.lam "_" (.app Vec'_n (.var "T")) (.app Vec'_n (.var "T"))))))
  = true := by native_decide

-- M4b
example : subCheck testFuel
  (.app (.app (.app appendVec' Nat')
    (.asc unit' (.app Vec' Nat')))
    (.asc unit' (.app Vec' Nat')))
  (.app Vec' Nat') = true := by native_decide

-- M4c
example : subCheck testFuel
  (.app (.app (.app appendVec' Nat') testVec1) testVec2)
  (.app Vec' Nat') = true := by native_decide

-- ============================================================
-- §12 WellTyped witness tests (Phase 5: non-vacuous soundness)
-- ============================================================

-- W1: Simple ascription
example : WellTyped testFuel [] (.asc unit' Unit') = true := by native_decide

-- W2: Ascription with SelfNat
example : WellTyped testFuel [] (.asc zero' SelfNat) = true := by native_decide

-- W3: Ascription with MuNat (Variant B)
example : WellTyped testFuel [] (.asc zero_mu MuNat) = true := by native_decide

-- W4: Abstract add with self-typed args
example : WellTyped testFuel []
  (.app (.app addSelfNat (.asc zero' SelfNat)) (.asc zero' SelfNat)) = true := by native_decide

-- W5: Recursive add with abstract args
example : WellTyped testFuel []
  (.app (.app addRec (.asc zero' SelfNat)) (.asc zero' SelfNat)) = true := by native_decide

-- W6: Abstract vector operations
example : WellTyped testFuel []
  (.app (.app (.app appendVec' Nat')
    (.asc testVec1 (.app Vec' Nat')))
    (.asc testVec2 (.app Vec' Nat'))) = true := by native_decide

-- W7: Concrete programs (no ascriptions)
example : WellTyped testFuel [] (.app (.app add' two') three') = true := by native_decide
example : WellTyped testFuel [] (.app succ' two') = true := by native_decide
example : WellTyped testFuel [] (.app isZero' zero') = true := by native_decide

-- W8: addRec itself
example : WellTyped testFuel [] addRec = true := by native_decide

-- W9: appendVec itself
example : WellTyped testFuel [] appendVec' = true := by native_decide

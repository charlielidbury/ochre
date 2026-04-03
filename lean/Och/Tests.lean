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

example : subCheck testFuel toZero NatToNat = true := by native_decide

-- ============================================================
-- §7.2 Concrete evaluation (concEval) tests
-- ============================================================

example : concEval testFuel (.app (.app (.app true' Nat') zero') one') = some zero' := by
  native_decide

example : concEval testFuel (.app (.app (.app false' Nat') zero') one') = some one' := by
  native_decide

example : concEval testFuel (.app fixId three') = some three' := by
  native_decide
example : concEval testFuel (.app fixId zero') = some zero' := by
  native_decide

example : concEval testFuel (.app isZero' zero') = some true' := by native_decide
example : concEval testFuel (.app isZero' one') = some false' := by native_decide
example : concEval testFuel (.app isZero' three') = some false' := by native_decide

-- ============================================================
-- §7.3 Recursive mu with thunked branches (concEval)
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

example : concEval testFuel (.app toZeroThunked zero') = some zero' := by native_decide
example : concEval testFuel (.app toZeroThunked one') = some zero' := by native_decide
example : concEval testFuel (.app toZeroThunked two') = some zero' := by native_decide
example : concEval testFuel (.app toZeroThunked three') = some zero' := by native_decide

-- Compose: toZeroThunked (add 2 1) = 0
example : concEval testFuel (.app toZeroThunked (.app (.app add' two') one')) = some zero' := by native_decide

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

example : concEval testFuel (.app pred' zero') = some zero' := by native_decide
example : concEval testFuel (.app isZero' (.app pred' one')) = some true' := by native_decide
example : concEval testFuel (.app isZero' (.app pred' two')) = some false' := by native_decide
example : concEval testFuel (.app isZero' (.app pred' three')) = some false' := by native_decide

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

example : concEval testFuel (.app rebuildThunked zero') = some zero' := by native_decide
example : concEval testFuel (.app isZero' (.app rebuildThunked zero')) = some true' := by native_decide
example : concEval testFuel (.app isZero' (.app rebuildThunked one')) = some false' := by native_decide
example : concEval testFuel (.app isZero' (.app rebuildThunked two')) = some false' := by native_decide
example : concEval testFuel (.app isZero' (.app rebuildThunked three')) = some false' := by native_decide
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

example : concEval testFuel (.app (.app addThunked zero') zero') = some zero' := by native_decide
example : concEval testFuel (.app (.app addThunked zero') three') = some three' := by native_decide
example : concEval testFuel (.app isZero' (.app (.app addThunked one') zero')) = some false' := by native_decide
example : concEval testFuel (.app isZero' (.app (.app addThunked two') one')) = some false' := by native_decide

example : concEval testFuel (.app toZeroThunked (.app (.app addThunked two') one')) = some zero' := by native_decide

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
example : concEval testFuel (.app (.app addRec zero') three') = some three' := by native_decide

-- M1c
example : concEval testFuel
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
example : concEval testFuel
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
example : concEval testFuel
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
-- §11.5 subCheckNF transitivity COUNTEREXAMPLE
-- ============================================================
-- subCheckNF is NOT transitive. This invalidates the approach
-- of proving adequacy's fallback case via subCheckNF transitivity.
-- See SUGGESTIONS.md which incorrectly claims it as a sub-lemma.
--
-- Counterexample:
--   a = .type
--   b = mu .type (bvar 0)    (fixpoint: unfolds to itself)
--   c = lam .type (bvar 0)   (identity function type)
--
-- a ⊑ b: self-intro → .type ⊑ (bvar 0).subst = .type ⊑ b → seen hit → true
-- b ⊑ c: self-elim → (bvar 0).subst = b ⊑ c → same pair → seen hit → true
-- a ⊑ c: .type vs lam → inferType .type = none → FALSE
--
-- Therefore: subCheckNF a b = true ∧ subCheckNF b c = true ∧ subCheckNF a c = false

def subCheckNF_trans_a := Expr.type
def subCheckNF_trans_b := Expr.mu Expr.type (Expr.bvar 0)
def subCheckNF_trans_c := Expr.lam Expr.type (Expr.bvar 0)

example : subCheckNF 10 [] [] subCheckNF_trans_a subCheckNF_trans_b = true := by native_decide
example : subCheckNF 10 [] [] subCheckNF_trans_b subCheckNF_trans_c = true := by native_decide
example : subCheckNF 10 [] [] subCheckNF_trans_a subCheckNF_trans_c = false := by native_decide

-- subCheckNF_top_universal COUNTEREXAMPLE:
-- .type ⊑ mu .type (bvar 0) does NOT imply v ⊑ mu .type (bvar 0) for all v.
-- When v is also a mu, subCheckNF uses the structural (mu, mu) branch
-- instead of self-intro, and the structural check can fail.
example : subCheckNF 10 [] [] Expr.type (Expr.mu Expr.type (Expr.bvar 0)) = true := by native_decide
example : subCheckNF 10 [] [] (Expr.mu Expr.type (Expr.lam Expr.type (Expr.bvar 0))) (Expr.mu Expr.type (Expr.bvar 0)) = false := by native_decide

-- ============================================================
-- §11.6 VCompat.subst_congr COUNTEREXAMPLE
-- ============================================================
-- VCompat.subst_congr is FALSE. This rules out the approach of
-- proving the app case via structural VCompat + substitution congruence.
--
-- Counterexample:
--   bodyV = bvar 0, bodyT = lam .type (bvar 0)  [VCompat via inferType]
--   av = lam .type .type, aτ = .type  [VCompat via top]
--
-- After substitution:
--   bodyV.subst 0 av = lam .type .type
--   bodyT.subst 0 aτ = lam .type (bvar 0)  [bound bvar 0 unaffected by subst]
--
-- VCompat (lam .type .type) (lam .type (bvar 0)):
--   structural lam requires VCompat .type (bvar 0), which is FALSE
--   (inferType .type = none, not a mu, not refl, not top since τ = bvar ≠ .type)
--
-- Verified computationally: subst results differ and are incompatible.
example : (Expr.bvar 0).subst 0 (Expr.lam .type .type) = Expr.lam .type .type := by native_decide
example : (Expr.lam .type (Expr.bvar 0)).subst 0 .type = Expr.lam .type (Expr.bvar 0) := by native_decide
-- The lam bodies (.type vs bvar 0) are not VCompat at step ≥ 1,
-- so the structural lam case fails. No other VCompat disjunct applies.
-- Therefore VCompat.subst_congr is FALSE.

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

-- ============================================================
-- §13 VCompat.adequacy COUNTEREXAMPLE (HISTORICAL + FIX VERIFICATION)
-- ============================================================
-- This section documents a counterexample that showed VCompat.adequacy was
-- FALSE with the OLD structural mu disjunct (raw bodies). The fix: replace
-- with "unfolded structural mu" (self-substituted bodies).
--
-- The key terms:
--   v = mu type (app (bvar 0) type)     — non-fixpoint mu
--   σ = mu type (lam type (bvar 0))     — fixpoint mu
--   τ = lam type type                    — simple function type
--
-- OLD VCompat (raw bodies): VCompat 3 v σ = True (bodies compatible via inferType)
-- NEW VCompat (unfolded): VCompat 3 v σ = False (unfolded forms diverge)
--
-- With the fix, the counterexample no longer creates a VCompat v σ that
-- can't be transported through subCheckNF. The unfolded structural mu
-- tracks actual mu behavior after self-reference resolution.

def adequacy_cex_v := Expr.mu .type (.app (.bvar 0) .type)
def adequacy_cex_σ := Expr.mu .type (.lam .type (.bvar 0))
def adequacy_cex_τ := Expr.lam .type .type

-- Verify subCheckNF σ τ succeeds (self-elim → fixpoint → structural lam → top)
example : subCheckNF 10 [] [] adequacy_cex_σ adequacy_cex_τ = true := by native_decide

-- Verify the self-elim unfold is a fixpoint
example : (Expr.lam .type (.bvar 0)).subst 0 adequacy_cex_σ = Expr.lam .type (.bvar 0) := by native_decide

-- Verify inferType for the mu value is none (blocks inferType disjunct)
example : inferType [] adequacy_cex_v = none := by native_decide
example : inferType [.type] adequacy_cex_v = none := by native_decide

-- Verify the key inferType step for VCompat v σ:
-- inferType [lam type (lam type (bvar 0))] (app (bvar 0) type) = some (lam type (bvar 0))
example : inferType [Expr.lam .type (.lam .type (.bvar 0))] (.app (.bvar 0) .type)
    = some (Expr.lam .type (.bvar 0)) := by native_decide

-- Verify the value's self-unfolding diverges from the type's
example : (Expr.app (.bvar 0) .type).subst 0 adequacy_cex_v
    = Expr.app adequacy_cex_v .type := by native_decide
-- inferType of (app (mu ...) type) = none because inferType (mu ...) = none
example : inferType [] (Expr.app adequacy_cex_v .type) = none := by native_decide

-- FIX VERIFICATION: VCompat 3 v σ is now FALSE with unfolded structural mu.
-- The unfolded forms are: bodyV.subst 0 v = app v type, bodyS.subst 0 σ = lam type (bvar 0)
-- VCompat 2 (app v type) (lam type (bvar 0)) fails because app(mu,...) has no inferType.
-- Verify the unfolded forms:
example : (Expr.app (.bvar 0) .type).subst 0 adequacy_cex_v
    = Expr.app adequacy_cex_v .type := by native_decide
example : (Expr.lam .type (.bvar 0)).subst 0 adequacy_cex_σ
    = Expr.lam .type (.bvar 0) := by native_decide  -- fixpoint

-- Helper: inferType of app(mu type (app (bvar 0) type), type) is always none
-- regardless of context, because inferType of mu is always none.
private theorem inferType_app_v_none (ctx : List Expr) :
    inferType ctx (Expr.app (Expr.mu .type (.app (.bvar 0) .type)) .type) = none := by
  simp [inferType]

theorem adequacy_cex_now_incompat : ¬VCompat 3 adequacy_cex_v adequacy_cex_σ := by
  intro h
  -- Exhaustively check all disjuncts of VCompat 3 v σ
  unfold VCompat at h
  rcases h with h1 | h2 | ⟨_, _, _, _, hv, _, _⟩ |
                 ⟨_, _, _, _, hv, hσ, h_body⟩ |
                 ⟨_, _, hσ, h_unfold⟩ |
                 ⟨_, _, hv, h_unfold⟩ |
                 ⟨_, _, _, _, hv, _, _, _⟩ |
                 ⟨_, _, h_inf, _⟩
  · cases h1                              -- σ(=mu) ≠ type
  · cases h2                              -- v ≠ σ (different mus)
  · cases hv                              -- v(=mu) ≠ lam
  · -- Unfolded structural mu
    cases hv; cases hσ
    simp [Expr.subst, Expr.shift] at h_body
    -- h_body : VCompat 2 (app v type) (lam type (bvar 0))
    -- All VCompat 2 disjuncts fail for (app(mu,...), lam)
    unfold VCompat at h_body
    rcases h_body with h1 | h2 | ⟨_, _, _, _, hv', _, _⟩ | ⟨_, _, _, _, hv', _, _⟩ |
                        ⟨_, _, hτ', _⟩ | ⟨_, _, hv', _⟩ |
                        ⟨_, _, _, _, _, hτ', _, _⟩ | ⟨ctx, _, h_inf', _⟩
    · cases h1
    · cases h2
    · cases hv'
    · cases hv'
    · cases hτ'
    · cases hv'
    · cases hτ'  -- lam ≠ app
    · rw [inferType_app_v_none] at h_inf'; cases h_inf'
  · -- mu-right on σ: unfold σ to lam type (bvar 0)
    cases hσ; simp [Expr.subst, Expr.shift] at h_unfold
    -- h_unfold : VCompat 2 v (lam type (bvar 0))
    -- v = mu type (app (bvar 0) type): mu ≠ lam, try each disjunct
    unfold VCompat at h_unfold
    rcases h_unfold with h1 | h2 | ⟨_, _, _, _, hv', _, _⟩ | ⟨_, _, _, _, hv', hτ', _⟩ |
                          ⟨_, _, hτ', _⟩ | ⟨_, _, hv', h_inner⟩ |
                          ⟨_, _, _, _, hv', _, _, _⟩ | ⟨_, _, h_inf', _⟩
    · cases h1
    · cases h2
    · cases hv'
    · cases hτ'  -- lam ≠ mu
    · cases hτ'  -- lam ≠ mu
    · -- mu-left: unfold v to app v type, VCompat 1 (app v type) (lam type (bvar 0))
      cases hv'; simp [Expr.subst, Expr.shift] at h_inner
      unfold VCompat at h_inner
      rcases h_inner with h1 | h2 | ⟨_, _, _, _, hv'', _, _⟩ | ⟨_, _, _, _, hv'', _, _⟩ |
                            ⟨_, _, hτ'', _⟩ | ⟨_, _, hv'', _⟩ |
                            ⟨_, _, _, _, _, hτ'', _, _⟩ | ⟨_, _, h_inf'', _⟩
      · cases h1
      · cases h2
      · cases hv''
      · cases hv''
      · cases hτ''
      · cases hv''
      · cases hτ''  -- lam ≠ app
      · rw [inferType_app_v_none] at h_inf''; cases h_inf''
    · cases hv'  -- mu ≠ app
    · unfold adequacy_cex_v at h_inf'; simp [inferType] at h_inf'
  · -- mu-left: unfold v to app v type
    cases hv; simp [Expr.subst, Expr.shift] at h_unfold
    -- h_unfold : VCompat 2 (app v type) σ where σ = mu type (lam type (bvar 0))
    unfold VCompat at h_unfold
    rcases h_unfold with h1 | h2 | ⟨_, _, _, _, hv', _, _⟩ | ⟨_, _, _, _, hv', _, _⟩ |
                          ⟨_, _, hσ', h_inner⟩ | ⟨_, _, hv', _⟩ |
                          ⟨_, _, _, _, _, hσ', _, _⟩ | ⟨_, _, h_inf', _⟩
    · cases h1
    · cases h2
    · cases hv'
    · cases hv'
    · -- mu-right: unfold σ to lam type (bvar 0)
      cases hσ'; simp [Expr.subst, Expr.shift] at h_inner
      -- VCompat 1 (app v type) (lam type (bvar 0))
      unfold VCompat at h_inner
      rcases h_inner with h1 | h2 | ⟨_, _, _, _, hv'', _, _⟩ | ⟨_, _, _, _, hv'', _, _⟩ |
                            ⟨_, _, hτ'', _⟩ | ⟨_, _, hv'', _⟩ |
                            ⟨_, _, _, _, _, hτ'', _, _⟩ | ⟨_, _, h_inf'', _⟩
      · cases h1
      · cases h2
      · cases hv''
      · cases hv''
      · cases hτ''       -- mu-right: lam ≠ mu
      · cases hv''       -- mu-left: app ≠ mu
      · cases hτ''       -- structural app: lam ≠ app
      · rw [inferType_app_v_none] at h_inf''; cases h_inf''
    · cases hv'          -- mu-left: app ≠ mu
    · cases hσ'          -- structural app: mu ≠ app (σ side)
    · rw [inferType_app_v_none] at h_inf'; cases h_inf'
  · cases hv  -- structural app: mu ≠ app
  · -- inferType of mu = none
    unfold adequacy_cex_v at h_inf
    simp [inferType] at h_inf

-- ============================================================
-- §14 Closedness lemma investigation
-- ============================================================

-- The closedness lemma proposed in SUGGESTIONS.md:
--   eval_closed : concEvalE fuel env e = some v → env.length > 0 → v.subst 0 X = v
-- is FALSE because the evaluators do NOT evaluate lambda domains or mu annotations.
-- Un-evaluated domain/annotation positions can contain free bvar 0.

-- COUNTEREXAMPLE: mu type (lam (bvar 0) (bvar 0))
-- body = lam (bvar 0) (bvar 0), where bvar 0 in the domain is the mu self-ref.
-- The evaluator copies the domain as-is → output bodyV' = lam (bvar 0) (bvar 0).
-- bodyV'.subst 0 X replaces the free bvar 0 in the domain: lam X (bvar 0) ≠ bodyV'.

-- Verify: evaluation of the body in the mu env gives lam (bvar 0) (bvar 0)
private def closedness_cex_mu := Expr.mu .type (.lam (.bvar 0) (.bvar 0))
private def closedness_cex_env := Env.extend [] closedness_cex_mu

example : concEvalE 10 closedness_cex_env (.lam (.bvar 0) (.bvar 0))
    = some (.lam (.bvar 0) (.bvar 0)) := by native_decide

example : absEval 10 closedness_cex_env (.lam (.bvar 0) (.bvar 0))
    = some (.lam (.bvar 0) (.bvar 0)) := by native_decide

-- Verify: subst 0 changes the output (closedness is FALSE)
example : (Expr.lam (.bvar 0) (.bvar 0)).subst 0 closedness_cex_mu
    = .lam closedness_cex_mu (.bvar 0) := by native_decide

-- Therefore: bodyV'.subst 0 (mu ann bodyV') ≠ bodyV'. The closedness lemma FAILS.
-- The output has free bvar 0 in the domain position (un-evaluated).

-- ============================================================
-- §15 Soundness_gen mu case: does VCompat survive subst?
-- ============================================================

-- Despite closedness failing, the soundness_gen mu case might still work because
-- VCompat's structural lam does NOT check domains. So the substitution into
-- un-evaluated domain positions is invisible to VCompat.
--
-- We test this by checking concrete instances: for a mu expression,
-- evaluate body with both evaluators, check VCompat on raw bodies (IH)
-- and on substituted bodies (what soundness_gen needs).

-- Bool-valued VCompat checker (under-approximation: uses only the given ctxs for inferType)
private def vcompat_check (ctxs : List (List Expr)) : Nat → Expr → Expr → Bool
  | 0, _, _ => true
  | n + 1, v, τ =>
    τ == .type
    || v == τ
    || match v, τ with
       | .lam _ bodyV, .lam _ bodyT => vcompat_check ctxs n bodyV bodyT
       | _, _ => false
    || match v, τ with
       | .mu annV bodyV, .mu annT bodyT =>
         vcompat_check ctxs n (bodyV.subst 0 (.mu annV bodyV)) (bodyT.subst 0 (.mu annT bodyT))
       | _, _ => false
    || match τ with
       | .mu ann body => vcompat_check ctxs n v (body.subst 0 (.mu ann body))
       | _ => false
    || match v with
       | .mu ann body => vcompat_check ctxs n (body.subst 0 (.mu ann body)) τ
       | _ => false
    || ctxs.any fun ctx =>
         match inferType ctx v with
         | some ty => vcompat_check ctxs n ty τ
         | none => false

-- Helper: check soundness_gen mu case for a specific mu expression
-- Returns true iff:
-- 1. The program is not well-typed (vacuous), OR
-- 2. VCompat on subst'd bodies holds
-- This mimics what soundness_gen needs: WellTyped → VCompat on unfolded forms
private def check_mu_soundness (fuel steps : Nat) (ann body : Expr) : Bool :=
    let muExpr := Expr.mu ann body
    -- Check WellTyped first (vacuous if not well-typed)
    if !(WellTyped fuel [] muExpr) then true
    else
      let env := Env.extend [] muExpr
      match concEvalE fuel env body, absEval fuel env body with
      | some bodyV', some bodyT' =>
          let unV := bodyV'.subst 0 (.mu ann bodyV')
          let unT := bodyT'.subst 0 (.mu ann bodyT')
          vcompat_check [[], [.type], [.lam .type .type]] steps unV unT
      | _, _ => true  -- eval fails, vacuous

-- Test 1: Simple mu with no ascription (both evaluators agree)
-- mu type (lam type (bvar 0)) — identity wrapped in mu
example : check_mu_soundness 20 10 .type (.lam .type (.bvar 0)) = true := by native_decide

-- Test 2: mu with self-reference in domain (closedness fails, but VCompat should hold)
example : check_mu_soundness 20 10 .type (.lam (.bvar 0) (.bvar 0)) = true := by native_decide

-- Test 3: mu with ascription — different concrete/abstract results
-- body = asc (lam (bvar 0) (bvar 0)) (lam type type)
-- concEvalE takes lhs → lam (bvar 0) (bvar 0)
-- absEval takes rhs → lam type type
example : check_mu_soundness 20 10 .type
    (.asc (.lam (.bvar 0) (.bvar 0)) (.lam .type .type)) = true := by native_decide

-- Test 4: mu with ascription where concrete result uses self-ref
-- body = asc (bvar 0) (lam type type)
-- concEvalE takes lhs → bvar 0 → mu self-ref
-- absEval takes rhs → lam type type
example : check_mu_soundness 20 10 .type
    (.asc (.bvar 0) (.lam .type .type)) = true := by native_decide

-- Test 5: Nested mu with ascription
-- body = lam type (asc (bvar 1) type)
-- bvar 1 under lam refers to mu self-ref
-- concEvalE: lam type (mu-self-ref) — but bvar 1 resolves to the shifted mu
-- absEval: lam type type
example : check_mu_soundness 20 10 .type
    (.lam .type (.asc (.bvar 1) .type)) = true := by native_decide

-- Test 6: mu with self-reference in multiple positions
-- body = lam (bvar 0) (asc (app (bvar 0) (bvar 0)) type)
example : check_mu_soundness 20 10 .type
    (.lam (.bvar 0) (.asc (.app (.bvar 0) (.bvar 0)) .type)) = true := by native_decide

-- Test 7: Non-trivial annotation
example : check_mu_soundness 20 10 (.lam .type .type)
    (.lam (.bvar 0) (.asc (.bvar 0) .type)) = true := by native_decide

-- Test 8: mu whose body is just asc with bvar 0 on both sides
-- concEvalE: asc bvar0 bvar0 → takes lhs → bvar 0 → mu self
-- absEval: asc bvar0 bvar0 → takes rhs → bvar 0 → mu self
-- Same result! Both get the mu itself.
example : check_mu_soundness 20 10 .type
    (.asc (.bvar 0) (.bvar 0)) = true := by native_decide

-- Test 9: mu body with nested asc producing very different results
-- body = asc (lam (bvar 0) (app (bvar 0) (bvar 0))) (lam type type)
-- concEvalE: lam (bvar 0) (app (bvar 0) (bvar 0))  [app of lambda param to itself]
-- absEval: lam type type
example : check_mu_soundness 20 10 .type
    (.asc (.lam (.bvar 0) (.app (.bvar 0) (.bvar 0))) (.lam .type .type)) = true := by native_decide

-- Brute-force search: enumerate small mu bodies with ascription
-- Atoms: bvar 0, bvar 1, type
-- Compound: lam type _, asc _ _, app _ _
-- We test all mu type body for bodies that produce different concEvalE/absEval results
private def atoms : List Expr := [.bvar 0, .bvar 1, .type]
private def lam_atoms : List Expr := atoms.map fun a => .lam .type a
private def asc_pairs : List Expr := atoms.flatMap fun l => atoms.map fun r => .asc l r
private def small_bodies : List Expr :=
  atoms ++ lam_atoms ++ asc_pairs ++
  -- lam with asc body
  (asc_pairs.map fun a => .lam .type a) ++
  (asc_pairs.map fun a => .lam (.bvar 0) a) ++
  -- app of atoms
  (atoms.flatMap fun f => atoms.map fun a => .app f a) ++
  -- lam with app body
  (atoms.flatMap fun f => atoms.map fun a => .lam .type (.app f a))

private def check_all_mu_bodies (fuel steps : Nat) (bodies : List Expr) : Bool :=
  bodies.all fun body => check_mu_soundness fuel steps .type body

-- All small mu bodies pass the soundness_gen mu case check
example : check_all_mu_bodies 20 8 small_bodies = true := by native_decide

-- Additional: mu with non-trivial annotations
private def check_all_with_anns (fuel steps : Nat) (anns bodies : List Expr) : Bool :=
  anns.all fun ann => bodies.all fun body => check_mu_soundness fuel steps ann body

private def small_anns : List Expr := [.type, .lam .type .type, .lam .type (.bvar 0)]

example : check_all_with_anns 20 8 small_anns small_bodies = true := by native_decide

-- Brute-force results (verified during development):
-- Of 51 test bodies: 14 not well-typed, 26 same evaluator results,
-- 5 different results that pass VCompat, 6 eval failures.
-- The 5 "diff-ok" cases all involve asc where absEval produces .type,
-- so VCompat succeeds via the top disjunct. No counterexample found.

-- Deeper tests: bodies where absEval produces non-type results
-- body = lam type (asc X Y) where Y is a non-trivial function

-- Test 10: different function depths
-- body = lam type (asc (lam type (bvar 0)) (lam type (lam type (bvar 0))))
-- concEvalE: lam type (lam type (bvar 0))
-- absEval: lam type (lam type (lam type (bvar 0)))
example : check_mu_soundness 30 10 .type
    (.lam .type (.asc (.lam .type (.bvar 0)) (.lam .type (.lam .type (.bvar 0))))) = true := by native_decide

-- Test 11: asc with different lambdas, bvar 0 in domain
example : check_mu_soundness 30 10 .type
    (.lam (.bvar 0) (.asc (.lam .type (.bvar 0)) (.lam .type (.lam .type (.bvar 0))))) = true := by native_decide

-- Test 12: nested asc
example : check_mu_soundness 30 10 .type
    (.lam .type (.asc (.asc (.bvar 0) .type) (.lam .type .type))) = true := by native_decide

-- Test 13: asc where lhs and rhs are both lams with different bodies
example : check_mu_soundness 30 10 .type
    (.lam .type (.asc (.lam .type (.bvar 1)) (.lam .type .type))) = true := by native_decide

-- Test 14: mu body containing another mu
example : check_mu_soundness 30 10 .type
    (.mu .type (.asc (.bvar 1) .type)) = true := by native_decide

-- Test 15: complex - lam with asc that has app inside
example : check_mu_soundness 30 10 .type
    (.lam .type (.asc (.app (.bvar 0) (.bvar 1)) .type)) = true := by native_decide

-- CONSTRUCTIVE PROOF: VCompat 3 v τ is FALSE
-- Every disjunct of VCompat fails
theorem adequacy_cex_incompat : ¬VCompat 3 adequacy_cex_v adequacy_cex_τ := by
  unfold VCompat
  intro h
  rcases h with h1 | h2 | ⟨dV, dT, bV, bT, hv, hτ, _⟩ |
                 ⟨aV, aT, bV, bT, hv, hτ, _⟩ |
                 ⟨ann, body, hτ, _⟩ |
                 ⟨ann, body, hv, h_unfold⟩ |
                 ⟨_, _, _, _, hv, _, _, _⟩ |
                 ⟨ctx, ty, h_inf, _⟩
  · cases h1                              -- lam ≠ type
  · cases h2                              -- mu ≠ lam
  · cases hv                              -- mu ≠ lam (v not a lam)
  · cases hτ                              -- lam ≠ mu (τ not a mu)
  · cases hτ                              -- lam ≠ mu (τ not a mu)
  · -- mu-left: v = mu type (app (bvar 0) type), unfold to (app v type)
    cases hv
    -- h_unfold : VCompat 2 ((app (bvar 0) type).subst 0 v) (lam type type)
    -- which is VCompat 2 (app v type) (lam type type)
    -- Note: (app (bvar 0) type).subst 0 (mu type (app (bvar 0) type))
    --      = app (mu type (app (bvar 0) type)) type
    change VCompat 2 ((Expr.app (.bvar 0) .type).subst 0 (Expr.mu .type (.app (.bvar 0) .type))) adequacy_cex_τ at h_unfold
    simp [Expr.subst, Expr.shift] at h_unfold
    -- h_unfold : VCompat 2 (app (mu type (app (bvar 0) type)) type) (lam type type)
    unfold VCompat at h_unfold
    rcases h_unfold with h1 | h2 | ⟨dV, dT, bV, bT, hv', _, _⟩ |
                          ⟨aV, aT, bV, bT, hv', _, _⟩ |
                          ⟨ann', body', hτ', _⟩ |
                          ⟨ann', body', hv', _⟩ |
                          ⟨_, _, _, _, _, hτ', _, _⟩ |
                          ⟨ctx', ty', h_inf', _⟩
    · cases h1                            -- lam ≠ type
    · cases h2                            -- app ≠ lam
    · cases hv'                           -- app ≠ lam
    · cases hv'                           -- app ≠ mu
    · cases hτ'                           -- lam ≠ mu
    · cases hv'                           -- app ≠ mu
    · cases hτ'                           -- lam ≠ app
    · -- inferType of app(mu..., type) = none
      -- inferType ctx' (app (mu ...) type): inferType ctx' (mu ...) = none → none
      have : inferType ctx' (Expr.app (Expr.mu .type (.app (.bvar 0) .type)) .type) = none := by
        simp [inferType]
      rw [this] at h_inf'; cases h_inf'
  · cases hv                              -- mu ≠ app
  · -- inferType of mu = none
    unfold adequacy_cex_v at h_inf
    simp [inferType] at h_inf

-- ============================================================
-- §16 VCompat-equivalence (vEquiv) and mu_body_subst_vcompat tests
-- ============================================================

-- §16.1 mu_body_subst_vcompat: the core lemma for soundness_gen mu case
-- Tests that VCompat on raw evaluator bodies implies VCompat on subst'd bodies.
-- This is mu_body_subst_vcompat's claim.

-- Helper: check mu_body_subst_vcompat for a specific mu expression
-- Returns true iff:
-- 1. Not well-typed (vacuous), OR
-- 2. Eval fails (vacuous), OR
-- 3. VCompat on subst'd bodies holds (given VCompat on raw bodies from IH)
private def check_mu_subst_vcompat (fuel steps : Nat) (ann body : Expr) : Bool :=
  if !(WellTyped fuel [] (.mu ann body)) then true
  else
    let env := Env.extend [] (.mu ann body)
    match concEvalE fuel env body, absEval fuel env body with
    | some bodyV', some bodyT' =>
        -- The IH would give VCompat for raw bodies. Check subst'd bodies too.
        let v := Expr.mu ann bodyV'
        let τ := Expr.mu ann bodyT'
        vcompat_check [[], [.type], [.lam .type .type]] steps
          (bodyV'.subst 0 v) (bodyT'.subst 0 τ)
    | _, _ => true

-- Individual cases with known different evaluator outputs
example : check_mu_subst_vcompat 20 10 .type (.lam .type (.bvar 0)) = true := by native_decide
example : check_mu_subst_vcompat 20 10 .type (.lam (.bvar 0) (.bvar 0)) = true := by native_decide
example : check_mu_subst_vcompat 20 10 .type
    (.asc (.lam (.bvar 0) (.bvar 0)) (.lam .type .type)) = true := by native_decide
example : check_mu_subst_vcompat 20 10 .type
    (.asc (.bvar 0) (.lam .type .type)) = true := by native_decide
example : check_mu_subst_vcompat 20 10 .type
    (.lam .type (.asc (.bvar 1) .type)) = true := by native_decide

-- Brute-force: all small bodies with all annotations
example : (small_anns.all fun ann =>
  small_bodies.all fun body => check_mu_subst_vcompat 20 8 ann body) = true := by native_decide

-- §16.2 closedEvalB: NOT universally true for evaluator outputs
-- The mu-app catch-all can leak raw bvar 0 into outputs. Example:
-- mu type (app (bvar 0) (bvar 0)):
--   concEvalE body = app (app (bvar 0) (bvar 0)) (mu ...)  — has free bvar 0!
--   closedEvalB 0 = false
-- However, the soundness_gen mu sorry STILL holds because:
-- 1. When closedEvalB fails AND evaluators differ, bodyT = type (VCompat top)
-- 2. When closedEvalB fails AND evaluators agree, subst gives equal results
-- 3. When closedEvalB holds, the vEquiv chain works

-- Verify the trichotomy: for all well-typed mus, one of these holds:
-- (a) bodyT' = type, (b) bodyV' = bodyT', (c) closedEvalB 0 for both
private def check_trichotomy (fuel : Nat) (ann body : Expr) : Bool :=
  if !(WellTyped fuel [] (.mu ann body)) then true
  else
    let env := Env.extend [] (.mu ann body)
    match concEvalE fuel env body, absEval fuel env body with
    | some bodyV', some bodyT' =>
        bodyT' == .type ||
        bodyV' == bodyT' ||
        (bodyV'.closedEvalB 0 && bodyT'.closedEvalB 0)
    | _, _ => true

example : (small_anns.all fun ann =>
  small_bodies.all fun body => check_trichotomy 20 ann body) = true := by native_decide

-- §16.3 When closedEvalB holds, vEquiv chain works
-- closedEvalB_subst_vEquiv is FULLY PROVEN — these tests validate it

-- Spot checks on closedEvalB
example : (Expr.lam .type (.bvar 0)).closedEvalB 0 = true := by native_decide
example : ((Expr.lam .type (.bvar 0)).subst 0 (Expr.mu .type (Expr.lam .type (.bvar 0)))).vEquivB
          (Expr.lam .type (.bvar 0)) = true := by native_decide
-- closedEvalB 0 checks body position at depth 1, not domains
-- bvar 0 in domain is NOT checked, only body positions
example : (Expr.lam (.bvar 0) .type).closedEvalB 0 = true := by native_decide
-- bvar 0 in body AT depth 0 fails closedEvalB 0 (but body at depth 1 is fine)
example : (Expr.lam .type (.bvar 0)).closedEvalB 0 = true := by native_decide  -- bvar 0 < 1 ✓

/-! ## §17: Asc-free evaluator equivalence tests

Verifies that evaluator outputs are asc-free and that concEvalE = absEval
on asc-free inputs. This is the key insight for the soundness_gen app case:
after beta-reduction, both evaluators agree. -/

-- Evaluator outputs are asc-free
-- absEval output for identity with ascription inside:
example : (absEval 5 [] (.lam .type (.asc (.bvar 0) .type))).map Expr.ascFreeB
        = some true := by native_decide
-- concEvalE output for identity with ascription inside:
example : (concEvalE 5 [] (.lam .type (.asc (.bvar 0) .type))).map Expr.ascFreeB
        = some true := by native_decide
-- Both evaluators agree on asc-free inputs:
example : concEvalE 5 [] (.lam .type (.bvar 0)) = absEval 5 [] (.lam .type (.bvar 0))
        := by native_decide
example : concEvalE 5 [] (.app (.lam .type (.bvar 0)) .type)
        = absEval 5 [] (.app (.lam .type (.bvar 0)) .type)
        := by native_decide
-- With ascription, they differ:
example : concEvalE 5 [] (.asc (.lam .type (.bvar 0)) .type)
        ≠ absEval 5 [] (.asc (.lam .type (.bvar 0)) .type)
        := by native_decide
-- After beta-reduction of asc-free values, evaluators agree:
-- (lam type (bvar 0)) applied to type → body.subst 0 type = type
-- Both evaluators agree on asc-free substituted body:
example : concEvalE 5 [] (Expr.subst (.bvar 0) 0 .type)
        = absEval 5 [] (Expr.subst (.bvar 0) 0 .type)
        := by native_decide

-- §17.1 UNCONDITIONAL absEval_ascFree/concEvalE_ascFree is FALSE
-- Lambda domains are NOT evaluated, so asc in domains passes through:
example : (absEval 5 [] (.lam (.asc .type .type) (.bvar 0))).map Expr.ascFreeB
        = some false := by native_decide
example : (concEvalE 5 [] (.lam (.asc .type .type) (.bvar 0))).map Expr.ascFreeB
        = some false := by native_decide
-- Mu annotations are NOT evaluated, so asc in annotations passes through:
example : (absEval 5 [] (.mu (.asc .type .type) (.bvar 0))).map Expr.ascFreeB
        = some false := by native_decide
-- mu-app catch-all leaks raw body which can have asc:
example : (absEval 5 [] (.mu .type (.app (.bvar 0) (.asc .type .type)))).map Expr.ascFreeB
        = some false := by native_decide
-- BUT: evaluators still AGREE on these expressions (asc in inactive positions):
example : concEvalE 5 [] (.lam (.asc .type .type) (.bvar 0))
        = absEval 5 [] (.lam (.asc .type .type) (.bvar 0)) := by native_decide
example : concEvalE 5 [] (.mu (.asc .type .type) (.bvar 0))
        = absEval 5 [] (.mu (.asc .type .type) (.bvar 0)) := by native_decide
-- CONDITIONAL version IS true: ascFree input → ascFree output (now proven)

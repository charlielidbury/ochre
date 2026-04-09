import Och.Simple.Macro
import Och.Simple.Subtype
import Och.Simple.Eval
import Och.Simple.Std.Bool
import Och.Simple.Std.Nat

/-!
# Church-encoded Pairs for Simple Och

```
PAIR   = λa:T. λb:T. λr:T. λf:(λx:a. λy:b. r). r
MkPair = λa:T. λb:T. λx:a. λy:b. λr:T. λf:(λx':a. λy':b. r). f x y
FST    = λa:T. λb:T. λp:(PAIR a b). p a (λx:a. λy:b. x)
SND    = λa:T. λb:T. λp:(PAIR a b). p b (λx:a. λy:b. y)
```
-/

set_option autoImplicit false

namespace Och.Simple.Std

open Och.Simple Expr

-- ============================================================
-- Definitions (using soch{} macro)
-- ============================================================

/-- PAIR = λa:T. λb:T. λr:T. λf:(λx:a. λy:b. r). r -/
def PAIR : Expr :=
  soch{ λ(a : ⊤). λ(b : ⊤). λ(r : ⊤). λ(f : λ(x : a). λ(y : b). r). r }

/-- MkPair = λa:T. λb:T. λx:a. λy:b. λr:T. λf:(λx':a. λy':b. r). f x y -/
def MkPair : Expr :=
  soch{ λ(a : ⊤). λ(b : ⊤). λ(x : a). λ(y : b). λ(r : ⊤). λ(f : λ(x' : a). λ(y' : b). r). f x y }

/-- FST = λa:T. λb:T. λp:(PAIR a b). p a (λx:a. λy:b. x) -/
def FST : Expr :=
  soch{ λ(a : ⊤). λ(b : ⊤). λ(p : PAIR a b). p a (λ(x : a). λ(y : b). x) }

/-- SND = λa:T. λb:T. λp:(PAIR a b). p b (λx:a. λy:b. y) -/
def SND : Expr :=
  soch{ λ(a : ⊤). λ(b : ⊤). λ(p : PAIR a b). p b (λ(x : a). λ(y : b). y) }

/-- SWAP = λa:T. λb:T. λp:(PAIR a b). MkPair b a (SND a b p) (FST a b p) -/
def SWAP : Expr :=
  soch{ λ(a : ⊤). λ(b : ⊤). λ(p : PAIR a b). MkPair b a (SND a b p) (FST a b p) }

-- Free variable markers
private def x1 : Expr := .var 1
private def x2 : Expr := .var 2
private def x3 : Expr := .var 3
private def x42 : Expr := .var 42
private def x99 : Expr := .var 99

-- ============================================================
-- Evaluation tests
-- ============================================================

private def ev (e : Expr) : Option Expr := eval 200 e

-- FST T T (MkPair T T x y) -> x
example : ev (.app (.app (.app FST .top) .top) (.app (.app (.app (.app MkPair .top) .top) x42) x99))
  = some x42 := rfl

-- SND T T (MkPair T T x y) -> y
example : ev (.app (.app (.app SND .top) .top) (.app (.app (.app (.app MkPair .top) .top) x42) x99))
  = some x99 := rfl

-- Pair of booleans
private def boolPair : Expr := .app (.app (.app (.app MkPair .top) .top) TRUE) FALSE
example : ev (.app (.app (.app FST .top) .top) boolPair) = some TRUE := rfl
example : ev (.app (.app (.app SND .top) .top) boolPair) = some FALSE := rfl

-- Pair of nats
private def natPair : Expr := .app (.app (.app (.app MkPair .top) .top) ZERO) ONE
example : ev (.app (.app (.app FST .top) .top) natPair) = some ZERO := rfl
example : ev (.app (.app (.app SND .top) .top) natPair) = some ONE := rfl

-- SWAP: swap elements of a pair
private def swapped : Expr := .app (.app (.app SWAP .top) .top) (.app (.app (.app (.app MkPair .top) .top) x42) x99)
example : ev (.app (.app (.app FST .top) .top) swapped) = some x99 := rfl
example : ev (.app (.app (.app SND .top) .top) swapped) = some x42 := rfl

-- Nested pair: PAIR(PAIR(x, y), z)
private def innerPair : Expr := .app (.app (.app (.app MkPair .top) .top) x1) x2
private def nestedPair : Expr := .app (.app (.app (.app MkPair .top) .top) innerPair) x3
-- FST of nested pair returns the inner pair (as unevaluated expression in CBN)
example : (ev (.app (.app (.app FST .top) .top) nestedPair)).isSome = true := rfl
example : ev (.app (.app (.app SND .top) .top) nestedPair) = some x3 := rfl
-- Deep access: FST of FST of nested pair gives x1
example : ev (.app (.app (.app FST .top) .top) (.app (.app (.app FST .top) .top) nestedPair)) = some x1 := rfl

-- ============================================================
-- Subtype derivations
-- ============================================================

-- All pair combinators are subtypes of T
example : Sub [] PAIR .top := Sub.top [] PAIR
example : Sub [] MkPair .top := Sub.top [] MkPair
example : Sub [] FST .top := Sub.top [] FST
example : Sub [] SND .top := Sub.top [] SND
example : Sub [] SWAP .top := Sub.top [] SWAP

-- Self-subtyping (refl)
example : Sub [] PAIR PAIR := Sub.refl [] PAIR
example : Sub [] MkPair MkPair := Sub.refl [] MkPair

end Och.Simple.Std

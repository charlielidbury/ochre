import Och.Macro
import Och.Eval
import Och.SubCheckVal
import Och.Std.Bool

/-!
# Church-encoded Natural Numbers

```
Nat  = λX:Type. λz:X. λs:(X→X). X
zero = λX:Type. λz:X. λs:(X→X). z
succ = λn:Nat.  λX:Type. λz:X. λs:(X→X). s (n X z s)
add  = λn:Nat. λm:Nat. n Nat m succ
```

Standard System F Church encoding of natural numbers.
-/

namespace Std

-- ============================================================
-- Type and constructors
-- ============================================================

def Nat_ := och{ λX:Type. λz:X. λs:(X → X). X }

def zero_ := och{ λX:Type. λz:X. λs:(X → X). z }
def one_  := och{ λX:Type. λz:X. λs:(X → X). s z }
def two_  := och{ λX:Type. λz:X. λs:(X → X). s (s z) }
def three_ := och{ λX:Type. λz:X. λs:(X → X). s (s (s z)) }
def four_ := och{ λX:Type. λz:X. λs:(X → X). s (s (s (s z))) }
def five_ := och{ λX:Type. λz:X. λs:(X → X). s (s (s (s (s z)))) }
def six_ := och{ λX:Type. λz:X. λs:(X → X). s (s (s (s (s (s z))))) }

-- ============================================================
-- Operations
-- ============================================================

def succ_ := och{ λn:Nat_. λX:Type. λz:X. λs:(X → X). s (n X z s) }

-- add = λ(n: Nat). λ(m: Nat). n Nat m succ
def add_ := och{ λn:Nat_. λm:Nat_. n Nat_ m succ_ }

-- isZero = λ(n: Nat). n Bool true (λ(_: Bool). false)
def isZero_ := och{ λn:Nat_. n Std.Bool Std.true_ (Std.Bool → Std.false_) }

-- double = λ(x: Nat). add x x
def double_ := och{ λx:Nat_. add_ x x }

-- Predecessor (uses a local Pair(Nat,Nat) helper)
private def Pair_ := och{ λA:Type. λB:Type. λX:Type. λk:(A → B → X). X }

private def pair_ := och{ λA:Type. λB:Type. λa:A. λb:B. λX:Type. λk:(A → B → X). k a b }

private def PairNN_ := och{ Pair_ Nat_ Nat_ }

-- pred = λn:Nat. fst (n PairNN (pair 0 0) (λp. (snd p, succ (snd p))))
def pred_ := och{
  λn:Nat_.
    n PairNN_ (pair_ Nat_ Nat_ zero_ zero_)
      (λp:PairNN_. pair_ Nat_ Nat_
        (p Nat_ (λfst:Nat_. λsnd:Nat_. snd))
        (succ_ (p Nat_ (λfst:Nat_. λsnd:Nat_. snd))))
      Nat_
      (λa:Nat_. λb:Nat_. a)
}

-- ============================================================
-- Tests
-- ============================================================

section Tests

-- Shorthand
private def NatToNat := och{ Nat_ → Nat_ }

-- ------------------------------------------------------------
-- Computation (positive) — concEval
-- concEval is WHNF so Church numerals (lambdas) can't be directly
-- compared. We use isZero to observe results at ground type.
-- ------------------------------------------------------------

-- isZero 0 = true
example : concEval 200 (och{ isZero_ zero_ }) = some Std.true_ := by native_decide
-- isZero 3 = false
example : concEval 200 (och{ isZero_ three_ }) = some Std.false_ := by native_decide
-- isZero (succ 2) = false (succ 2 is nonzero)
example : concEval 200 (och{ isZero_ (succ_ two_) }) = some Std.false_ := by native_decide
-- isZero (pred 1) = true (pred 1 = 0)
example : concEval 1000 (och{ isZero_ (pred_ one_) }) = some Std.true_ := by native_decide
-- isZero (pred 2) = false (pred 2 ≠ 0)
example : concEval 1000 (och{ isZero_ (pred_ two_) }) = some Std.false_ := by native_decide
-- pred 0 = 0 (observed via isZero)
example : concEval 1000 (och{ isZero_ (pred_ zero_) }) = some Std.true_ := by native_decide

-- ------------------------------------------------------------
-- Computation (positive) — NbE normal-form equality
-- (was `absEvalVal e = .ok ⟨v⟩`; the legacy checker is retired,
--  so now `NbE.nf e = NbE.nf v` — both normalise under binders).
-- ------------------------------------------------------------

-- succ 2 = 3
example : NbE.nf 200 (och{ succ_ two_ }) = NbE.nf 200 three_ := by native_decide
-- add 2 3 = 5
example : NbE.nf 200 (och{ add_ two_ three_ }) = NbE.nf 200 five_ := by native_decide
-- isZero 0 = true
example : NbE.nf 200 (och{ isZero_ zero_ }) = NbE.nf 200 Std.true_ := by native_decide
-- isZero 3 = false
example : NbE.nf 200 (och{ isZero_ three_ }) = NbE.nf 200 Std.false_ := by native_decide
-- double 3 = 6
example : NbE.nf 200 (och{ double_ three_ }) = NbE.nf 200 six_ := by native_decide
-- pred 3 = 2
example : NbE.nf 200 (och{ pred_ three_ }) = NbE.nf 200 two_ := by native_decide
-- pred 0 = 0
example : NbE.nf 200 (och{ pred_ zero_ }) = NbE.nf 200 zero_ := by native_decide
-- pred 1 = 0
example : NbE.nf 200 (och{ pred_ one_ }) = NbE.nf 200 zero_ := by native_decide

-- ------------------------------------------------------------
-- Computation (negative) — NbE
-- ------------------------------------------------------------

-- add 2 3 ≠ 4
example : NbE.nf 200 (och{ add_ two_ three_ }) ≠ NbE.nf 200 four_ := by native_decide
-- succ 2 ≠ 2
example : NbE.nf 200 (och{ succ_ two_ }) ≠ NbE.nf 200 two_ := by native_decide
-- pred 3 ≠ 3
example : NbE.nf 200 (och{ pred_ three_ }) ≠ NbE.nf 200 three_ := by native_decide
-- double 3 ≠ 3
example : NbE.nf 200 (och{ double_ three_ }) ≠ NbE.nf 200 three_ := by native_decide

-- ------------------------------------------------------------
-- Computation (negative) — concEval
-- ------------------------------------------------------------

-- isZero 0 ≠ false
example : concEval 200 (och{ isZero_ zero_ }) ≠ some Std.false_ := by native_decide
-- isZero 3 ≠ true
example : concEval 200 (och{ isZero_ three_ }) ≠ some Std.true_ := by native_decide
-- isZero (succ 0) ≠ true (succ 0 is not zero)
example : concEval 200 (och{ isZero_ (succ_ zero_) }) ≠ some Std.true_ := by native_decide

-- ------------------------------------------------------------
-- Subtype checking (positive)
-- ------------------------------------------------------------

-- Church numerals are subtypes of Nat
example : NbE.subCheck 200 zero_ Nat_ = .ok true := by native_decide
example : NbE.subCheck 200 one_ Nat_ = .ok true := by native_decide
example : NbE.subCheck 200 three_ Nat_ = .ok true := by native_decide
example : NbE.subCheck 200 six_ Nat_ = .ok true := by native_decide

-- succ : Nat → Nat
example : NbE.subCheck 200 succ_ NatToNat = .ok true := by native_decide
-- add : Nat → Nat → Nat
example : NbE.subCheck 200 add_ (och{ Nat_ → NatToNat }) = .ok true := by native_decide
-- isZero : Nat → Bool
example : NbE.subCheck 200 isZero_ (och{ Nat_ → Std.Bool }) = .ok true := by native_decide
-- double : Nat → Nat
example : NbE.subCheck 200 double_ NatToNat = .ok true := by native_decide
-- pred : Nat → Nat
example : NbE.subCheck 1000 pred_ NatToNat = .ok true := by native_decide

-- ------------------------------------------------------------
-- Subtype checking (negative)
-- ------------------------------------------------------------

-- true is not a Nat
example : NbE.subCheck 200 Std.true_ Nat_ = .ok false := by native_decide
-- three is not a subtype of two (different values)
example : NbE.subCheck 200 three_ two_ = .ok false := by native_decide
-- Nat is not a subtype of zero (it's wider)
example : NbE.subCheck 200 Nat_ zero_ = .ok false := by native_decide
-- succ is not a Nat (it's a function)
example : NbE.subCheck 200 succ_ Nat_ = .ok false := by native_decide

end Tests
end Std

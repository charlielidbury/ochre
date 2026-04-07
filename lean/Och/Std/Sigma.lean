import Och.Macro
import Och.Eval
import Och.Std.Nat

/-!
# Church-encoded Sigma (dependent pair)

```
Sigma = λA:Type. λB:(A → Type). λX:Type. λk:(Πa:A. B a → X). X
dpair  = λA:Type. λB:(A → Type). λa:A. λb:B a. λX:Type. λk:(Πa:A. B a → X). k a b
```

Church-encoded dependent pair. The eliminator takes a continuation `k`
that receives both the witness `a : A` and the payload `b : B a`, and
produces a result of type `X`.
-/

namespace Std

def Sigma := och{ λA:Type. λB:(A → Type). λX:Type. λk:(λa:A. B a → X). X }

def dpair := och{ λA:Type. λB:(A → Type). λa:A. λb:(B a). λX:Type. λk:(λa2:A. B a2 → X). k a b }

-- ============================================================
-- Tests
-- ============================================================

section Tests

-- Helper: constant family  λ_:Nat. Nat  (non-dependent case for simplicity)
private def constNat := och{ Nat_ → Nat_ }

-- Build: dpair Nat (λ_.Nat) 1 2
private def pair_1_2 : Expr :=
  och{ dpair Nat_ constNat one_ two_ }

-- fst projection: unpack the pair, return the first component
-- pair X (λa b. a)
private def fst_1_2 : Expr :=
  och{ pair_1_2 Nat_ (λa:Nat_. λ_:Nat_. a) }

-- snd projection: unpack the pair, return the second component
-- pair X (λa b. b)
private def snd_1_2 : Expr :=
  och{ pair_1_2 Nat_ (λ_:Nat_. λb:Nat_. b) }

-- ---- Positive: computation ----

-- fst (dpair Nat (λ_.Nat) 1 2) = 1
example : concEval 100 fst_1_2 = concEval 100 one_ := by native_decide

-- snd (dpair Nat (λ_.Nat) 1 2) = 2
example : concEval 100 snd_1_2 = concEval 100 two_ := by native_decide

-- ---- Positive: subtype checking ----

-- dpair Nat (λ_.Nat) 1 2 : Sigma Nat (λ_.Nat)
example : subCheck 100 pair_1_2 (och{ Sigma Nat_ constNat }) = .ok true := by native_decide

-- dpair : its full type
example : subCheck 100 dpair (och{
  λA:Type. λB:(A → Type). λa:A. λ_:(B a). Sigma A B }) = .ok true := by native_decide

-- ---- Negative: computation ----

-- fst ≠ 2
example : concEval 100 fst_1_2 ≠ concEval 100 two_ := by native_decide

-- snd ≠ 1
example : concEval 100 snd_1_2 ≠ concEval 100 one_ := by native_decide

-- fst ≠ 0
example : concEval 100 fst_1_2 ≠ concEval 100 zero_ := by native_decide

-- ---- Negative: subtype checking ----

-- Sigma Nat (λ_.Nat) is not a Nat (it's a different type)
example : subCheck 100 (och{ Sigma Nat_ constNat }) Nat_ = .ok false := by native_decide

-- dpair is not itself a Sigma type (it's a constructor, not a value of Sigma)
example : subCheck 100 dpair (och{ Sigma Nat_ constNat }) = .ok false := by native_decide

end Tests
end Std

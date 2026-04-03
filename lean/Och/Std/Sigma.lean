import Och.Syntax
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

open Named

namespace Std

def Sigma : Named := .lam "A" .type (.lam "B" (.lam "_" (.var "A") .type) (
  .lam "X" .type (.lam "k" (.lam "a" (.var "A") (.lam "_" (.app (.var "B") (.var "a")) (.var "X"))) (.var "X"))))

def dpair : Named := .lam "A" .type (.lam "B" (.lam "_" (.var "A") .type) (
  .lam "a" (.var "A") (.lam "b" (.app (.var "B") (.var "a")) (
    .lam "X" .type (.lam "k" (.lam "a2" (.var "A") (.lam "_" (.app (.var "B") (.var "a2")) (.var "X")))
      (.app (.app (.var "k") (.var "a")) (.var "b")))))))

-- ============================================================
-- Tests
-- ============================================================

section Tests
open Expr

-- Helper: constant family  λ_:Nat. Nat  (non-dependent case for simplicity)
private def constNat : Named := .lam "_" Nat_ Nat_

-- Build: dpair Nat (λ_.Nat) 1 2
private def pair_1_2 : Named :=
  .app (.app (.app (.app dpair Nat_) constNat) one_) two_

-- fst projection: unpack the pair, return the first component
-- pair X (λa b. a)
private def fst_1_2 : Named :=
  .app (.app pair_1_2 Nat_) (.lam "a" Nat_ (.lam "_" Nat_ (.var "a")))

-- snd projection: unpack the pair, return the second component
-- pair X (λa b. b)
private def snd_1_2 : Named :=
  .app (.app pair_1_2 Nat_) (.lam "_" Nat_ (.lam "b" Nat_ (.var "b")))

-- ---- Positive: computation ----

-- fst (dpair Nat (λ_.Nat) 1 2) = 1
example : concEval 100 (n fst_1_2) = concEval 100 (n one_) := by native_decide

-- snd (dpair Nat (λ_.Nat) 1 2) = 2
example : concEval 100 (n snd_1_2) = concEval 100 (n two_) := by native_decide

-- ---- Positive: subtype checking ----

-- dpair Nat (λ_.Nat) 1 2 : Sigma Nat (λ_.Nat)
example : subCheck 100 (n pair_1_2) (n (.app (.app Sigma Nat_) constNat)) = true := by native_decide

-- dpair : its full type
example : subCheck 100 (n dpair) (n (
  .lam "A" .type (.lam "B" (.lam "_" (.var "A") .type) (
    .lam "a" (.var "A") (.lam "_" (.app (.var "B") (.var "a"))
      (.app (.app Sigma (.var "A")) (.var "B"))))))) = true := by native_decide

-- ---- Negative: computation ----

-- fst ≠ 2
example : concEval 100 (n fst_1_2) ≠ concEval 100 (n two_) := by native_decide

-- snd ≠ 1
example : concEval 100 (n snd_1_2) ≠ concEval 100 (n one_) := by native_decide

-- fst ≠ 0
example : concEval 100 (n fst_1_2) ≠ concEval 100 (n zero_) := by native_decide

-- ---- Negative: subtype checking ----

-- Sigma Nat (λ_.Nat) is not a Nat (it's a different type)
example : subCheck 100 (n (.app (.app Sigma Nat_) constNat)) (n Nat_) = false := by native_decide

-- dpair is not itself a Sigma type (it's a constructor, not a value of Sigma)
example : subCheck 100 (n dpair) (n (.app (.app Sigma Nat_) constNat)) = false := by native_decide

end Tests
end Std

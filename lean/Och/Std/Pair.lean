import Och.Syntax
import Och.Eval
import Och.Std.Bool
import Och.Std.Nat

/-!
# Church-encoded Pairs (Product Type)

```
Pair = λA:Type. λB:Type. λX:Type. λk:(A → B → X). X
pair = λA:Type. λB:Type. λa:A. λb:B. λX:Type. λk:(A → B → X). k a b
fst  = λA:Type. λB:Type. λp:(Pair A B). p A (λa:A. λ_:B. a)
snd  = λA:Type. λB:Type. λp:(Pair A B). p B (λ_:A. λb:B. b)
```

Standard System F Church-encoded product type. The eliminator takes a
continuation that receives both components.
-/

open Named

namespace Std

def Pair : Named := .lam "A" .type (.lam "B" .type (
  .lam "X" .type (.lam "k" (.lam "_" (.var "A") (.lam "_" (.var "B") (.var "X"))) (.var "X"))))

def pair : Named := .lam "A" .type (.lam "B" .type (.lam "a" (.var "A") (.lam "b" (.var "B") (
  .lam "X" .type (.lam "k" (.lam "_" (.var "A") (.lam "_" (.var "B") (.var "X")))
    (.app (.app (.var "k") (.var "a")) (.var "b")))))))

def fst_ : Named := .lam "A" .type (.lam "B" .type (.lam "p" (.app (.app Pair (.var "A")) (.var "B"))
  (.app (.app (.var "p") (.var "A")) (.lam "a" (.var "A") (.lam "_" (.var "B") (.var "a"))))))

def snd_ : Named := .lam "A" .type (.lam "B" .type (.lam "p" (.app (.app Pair (.var "A")) (.var "B"))
  (.app (.app (.var "p") (.var "B")) (.lam "_" (.var "A") (.lam "b" (.var "B") (.var "b"))))))

-- ============================================================
-- Tests
-- ============================================================

section Tests
open Expr

-- Convenience: pair Nat Nat 1 2
private def p12 : Named := .app (.app (.app (.app pair Nat_) Nat_) one_) two_

-- ── Positive computation tests ──────────────────────────────

-- fst (pair Nat Nat 1 2) = 1
example : concEval 100
  (.app (.app (.app (n fst_) (n Nat_)) (n Nat_)) (n p12))
  = concEval 100 (n one_) := by native_decide

-- snd (pair Nat Nat 1 2) = 2
example : concEval 100
  (.app (.app (.app (n snd_) (n Nat_)) (n Nat_)) (n p12))
  = concEval 100 (n two_) := by native_decide

-- ── Positive subtype checks ─────────────────────────────────

-- pair Nat Nat 1 2 : Pair Nat Nat
example : subCheck 100 (n p12) (n (.app (.app Pair Nat_) Nat_)) = true := by native_decide

-- pair : A → B → a → b → Pair A B  (check pair's type at Nat Nat)
example : subCheck 100
  (n (.app (.app pair Nat_) Nat_))
  (n (.lam "_" Nat_ (.lam "_" Nat_ (.app (.app Pair Nat_) Nat_))))
  = true := by native_decide

-- fst_ : Pair Nat Nat → Nat
example : subCheck 100
  (n (.app (.app fst_ Nat_) Nat_))
  (n (.lam "_" (.app (.app Pair Nat_) Nat_) Nat_))
  = true := by native_decide

-- snd_ : Pair Nat Nat → Nat
example : subCheck 100
  (n (.app (.app snd_ Nat_) Nat_))
  (n (.lam "_" (.app (.app Pair Nat_) Nat_) Nat_))
  = true := by native_decide

-- ── Negative computation tests ──────────────────────────────

-- fst ≠ snd value: fst (pair 1 2) ≠ 2
example : concEval 100
  (.app (.app (.app (n fst_) (n Nat_)) (n Nat_)) (n p12))
  ≠ concEval 100 (n two_) := by native_decide

-- snd ≠ fst value: snd (pair 1 2) ≠ 1
example : concEval 100
  (.app (.app (.app (n snd_) (n Nat_)) (n Nat_)) (n p12))
  ≠ concEval 100 (n one_) := by native_decide

-- ── Negative subtype checks ─────────────────────────────────

-- Pair Nat Nat is not a subtype of a specific pair value
example : subCheck 100 (n (.app (.app Pair Nat_) Nat_)) (n p12) = false := by native_decide

-- A pair of Nats is not a Bool
example : subCheck 100 (n p12) (n Bool) = false := by native_decide

-- fst_ (partially applied) is not a Nat
example : subCheck 100 (n (.app (.app fst_ Nat_) Nat_)) (n Nat_) = false := by native_decide

end Tests
end Std

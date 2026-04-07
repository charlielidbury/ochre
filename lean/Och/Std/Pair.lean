import Och.Macro
import Och.Eval
import Och.Std.Bool
import Och.Std.Nat

/-!
# Combined Pairs (Product Type)

```
Pair = λl:Type. λr:Type. λk:(l → r → Type). k l r
fst  = λp:(Pair Type Type). p (λa:Type. λ_:Type. a)
snd  = λp:(Pair Type Type). p (λ_:Type. λb:Type. b)
```

Pair serves as both type and constructor. `Pair Bool Bool` is a type
(pairs of booleans) while `Pair true false` is a value (a specific pair).
Subtyping via app congruence gives `Pair true false <: Pair Bool Bool`.

The result type is hardcoded to `Type` since everything is `<: Type`.
fst and snd use `Pair Type Type` as their domain — since everything is
`<: Type`, any pair `Pair a b` is accepted without needing type arguments.
-/

namespace Std

def Pair := och{ λl:Type. λr:Type. λk:(l → r → Type). k l r }

def fst_ := och{ λp:(Pair Type Type). p (λa:Type. λ_:Type. a) }

def snd_ := och{ λp:(Pair Type Type). p (λ_:Type. λb:Type. b) }

-- ============================================================
-- Tests
-- ============================================================

section Tests

-- Convenience: Pair 1 2 (combined encoding — Pair IS the constructor)
private def p12 := och{ Pair one_ two_ }

-- ── Positive computation tests ──────────────────────────────

-- fst (Pair 1 2) = 1
example : concEval 100
  (och{ fst_ p12 })
  = concEval 100 one_ := by native_decide

-- snd (Pair 1 2) = 2
example : concEval 100
  (och{ snd_ p12 })
  = concEval 100 two_ := by native_decide

-- ── Positive subtype checks ─────────────────────────────────

-- Pair 1 2 : Pair Nat Nat
example : subCheck 100 p12 (och{ Pair Nat_ Nat_ }) = .ok true := by native_decide

-- Pair true false <: Pair Bool Bool  (value subtypes type)
example : subCheck 100
  (och{ Pair true_ false_ })
  (och{ Pair Bool Bool })
  = .ok true := by native_decide

-- fst preserves precise type info: fst (Pair true true) <: true
example : subCheck 100
  (och{ fst_ (Pair true_ true_) })
  true_
  = .ok true := by native_decide

-- fst_ : Pair Type Type → Type
example : subCheck 100
  fst_
  (och{ Pair Nat_ Nat_ → Nat_ })
  = .ok true := by native_decide

-- snd_ : Pair Type Type → Type
example : subCheck 100
  snd_
  (och{ Pair Nat_ Nat_ → Nat_ })
  = .ok true := by native_decide

-- ── Negative computation tests ──────────────────────────────

-- fst ≠ snd value: fst (Pair 1 2) ≠ 2
example : concEval 100
  (och{ fst_ p12 })
  ≠ concEval 100 two_ := by native_decide

-- snd ≠ fst value: snd (Pair 1 2) ≠ 1
example : concEval 100
  (och{ snd_ p12 })
  ≠ concEval 100 one_ := by native_decide

-- ── Negative subtype checks ─────────────────────────────────

-- A pair of Nats is not a Bool
example : subCheck 100 p12 Bool = .ok false := by native_decide

-- fst_ is not a Nat
example : subCheck 100 fst_ Nat_ = .ok false := by native_decide

-- fst does not lose precision: fst (Pair true true) is NOT false
example : subCheck 100
  (och{ fst_ (Pair true_ true_) })
  false_
  = .ok false := by native_decide

end Tests
end Std

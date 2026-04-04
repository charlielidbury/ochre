import Och.Macro
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

namespace Std

def Pair : Expr := och{ λA:Type. λB:Type. λX:Type. λk:(A → B → X). X }

def pair : Expr := och{ λA:Type. λB:Type. λa:A. λb:B. λX:Type. λk:(A → B → X). k a b }

def fst_ : Expr := och{ λA:Type. λB:Type. λp:(Pair A B). p A (λa:A. λ_:B. a) }

def snd_ : Expr := och{ λA:Type. λB:Type. λp:(Pair A B). p B (λ_:A. λb:B. b) }

-- ============================================================
-- Tests
-- ============================================================

section Tests

-- Convenience: pair Nat Nat 1 2
private def p12 : Expr := och{ pair Nat_ Nat_ one_ two_ }

-- ── Positive computation tests ──────────────────────────────

-- fst (pair Nat Nat 1 2) = 1
example : concEval 100
  (och{ fst_ Nat_ Nat_ p12 })
  = concEval 100 one_ := by native_decide

-- snd (pair Nat Nat 1 2) = 2
example : concEval 100
  (och{ snd_ Nat_ Nat_ p12 })
  = concEval 100 two_ := by native_decide

-- ── Positive subtype checks ─────────────────────────────────

-- pair Nat Nat 1 2 : Pair Nat Nat
example : subCheck 100 p12 (och{ Pair Nat_ Nat_ }) = true := by native_decide

-- pair : A → B → a → b → Pair A B  (check pair's type at Nat Nat)
example : subCheck 100
  (och{ pair Nat_ Nat_ })
  (och{ Nat_ → Nat_ → Pair Nat_ Nat_ })
  = true := by native_decide

-- fst_ : Pair Nat Nat → Nat
example : subCheck 100
  (och{ fst_ Nat_ Nat_ })
  (och{ Pair Nat_ Nat_ → Nat_ })
  = true := by native_decide

-- snd_ : Pair Nat Nat → Nat
example : subCheck 100
  (och{ snd_ Nat_ Nat_ })
  (och{ Pair Nat_ Nat_ → Nat_ })
  = true := by native_decide

-- ── Negative computation tests ──────────────────────────────

-- fst ≠ snd value: fst (pair 1 2) ≠ 2
example : concEval 100
  (och{ fst_ Nat_ Nat_ p12 })
  ≠ concEval 100 two_ := by native_decide

-- snd ≠ fst value: snd (pair 1 2) ≠ 1
example : concEval 100
  (och{ snd_ Nat_ Nat_ p12 })
  ≠ concEval 100 one_ := by native_decide

-- ── Negative subtype checks ─────────────────────────────────

-- Pair Nat Nat is not a subtype of a specific pair value
example : subCheck 100 (och{ Pair Nat_ Nat_ }) p12 = false := by native_decide

-- A pair of Nats is not a Bool
example : subCheck 100 p12 Bool = false := by native_decide

-- fst_ (partially applied) is not a Nat
example : subCheck 100 (och{ fst_ Nat_ Nat_ }) Nat_ = false := by native_decide

end Tests
end Std

import Och.Syntax
import Och.Eval
import Och.Std.Nat
import Och.Std.Unit
import Och.Std.Pair

/-!
# Church-encoded Length-Indexed Arrays

```
Array  = λn:Nat. λT:Type. n Type Unit (λacc:Type. Pair T acc)
emptyArray = λT:Type. unit
consArray  = λT:Type. λn:Nat. λx:T. λrest:(Array n T). pair T (Array n T) x rest
headArray  = λT:Type. λn:Nat. λarr:(Array (succ n) T). arr T (λx:T. λ_:(Array n T). x)
tailArray  = λT:Type. λn:Nat. λarr:(Array (succ n) T). arr (Array n T) (λ_:T. λrest:(Array n T). rest)
```

Church-encoded length-indexed arrays. `Array n T` unfolds to nested pairs
via the Church numeral `n`: `Array 0 T = Unit`, `Array 1 T = Pair T Unit`,
`Array 2 T = Pair T (Pair T Unit)`, etc.
-/

open Named

namespace Std

def Array_ : Named := .lam "n" Nat_ (.lam "T" .type (
  .app (.app (.app (.var "n") .type) Unit_) (.lam "acc" .type (
    .app (.app Pair (.var "T")) (.var "acc")))))

def emptyArray : Named := .lam "T" .type unit_

def consArray : Named := .lam "T" .type (.lam "n" Nat_ (.lam "x" (.var "T") (.lam "rest" (.app (.app Array_ (.var "n")) (.var "T")) (
  .app (.app (.app (.app pair (.var "T")) (.app (.app Array_ (.var "n")) (.var "T"))) (.var "x")) (.var "rest")))))

def headArray : Named := .lam "T" .type (.lam "n" Nat_ (.lam "arr" (.app (.app Array_ (.app succ_ (.var "n"))) (.var "T")) (
  .app (.app (.var "arr") (.var "T")) (.lam "x" (.var "T") (.lam "_" (.app (.app Array_ (.var "n")) (.var "T")) (.var "x"))))))

def tailArray : Named := .lam "T" .type (.lam "n" Nat_ (.lam "arr" (.app (.app Array_ (.app succ_ (.var "n"))) (.var "T")) (
  .app (.app (.var "arr") (.app (.app Array_ (.var "n")) (.var "T"))) (.lam "_" (.var "T") (.lam "rest" (.app (.app Array_ (.var "n")) (.var "T")) (.var "rest"))))))

-- ============================================================
-- Tests
-- ============================================================

section Tests
open Expr

-- ── Positive computation tests ─────────────────────────────

-- Array 0 Nat = Unit
example : absEval 1000 [] (.app (.app (n Array_) (n zero_)) (n Nat_)) = .ok (n Unit_) := by native_decide

-- cons 0 into emptyArray, head it back out
-- testArr1 = cons Nat 0 0 (emptyArray Nat)
private def testArr1 : Expr := n (.app (.app (.app (.app consArray Nat_) zero_) zero_) (.app emptyArray Nat_))

-- head testArr1 = 0
example : absEval 1000 [] (.app (.app (.app (n headArray) (n Nat_)) (n zero_)) testArr1) = .ok (n zero_) := by native_decide

-- tail testArr1 = unit
example : absEval 1000 [] (.app (.app (.app (n tailArray) (n Nat_)) (n zero_)) testArr1) = .ok (n unit_) := by native_decide

-- testArr2 = cons Nat 1 1 (cons Nat 0 2 (emptyArray Nat))
private def testArr2 : Expr := n (.app (.app (.app (.app consArray Nat_) one_) one_)
  (.app (.app (.app (.app consArray Nat_) zero_) two_) (.app emptyArray Nat_)))

-- head testArr2 = 1
example : absEval 1000 [] (.app (.app (.app (n headArray) (n Nat_)) (n one_)) testArr2) = .ok (n one_) := by native_decide

-- head (tail testArr2) = 2
example : absEval 1000 [] (.app (.app (.app (n headArray) (n Nat_)) (n zero_))
  (.app (.app (.app (n tailArray) (n Nat_)) (n one_)) testArr2)) = .ok (n two_) := by native_decide

-- ── Positive subtype checks ────────────────────────────────

-- testArr1 ⊑ Array 1 Nat
example : subCheck 1000 testArr1 (.app (.app (n Array_) (n one_)) (n Nat_)) = true := by native_decide

-- testArr2 ⊑ Array 2 Nat
example : subCheck 1000 testArr2 (.app (.app (n Array_) (n two_)) (n Nat_)) = true := by native_decide

-- ── Negative subtype checks ────────────────────────────────

-- emptyArray Nat ⊄ Array 1 Nat (wrong length)
example : subCheck 1000 (.app (n emptyArray) (n Nat_)) (.app (.app (n Array_) (n one_)) (n Nat_)) = false := by native_decide

end Tests
end Std

import Och.Syntax
import Och.Eval
import Och.Std.Nat
import Och.Std.Array
import Och.Std.Sigma

/-!
# Church-encoded Vec (length-indexed vector via Sigma)

```
Vec   = λT:Type. Sigma Nat (λn:Nat. Array n T)
mkVec = λT:Type. λn:Nat. λarr:(Array n T). dpair Nat (λn:Nat. Array n T) n arr
```

A length-indexed vector is a dependent pair (Sigma) of a natural number `n`
and an `Array n T`. The length is existentially quantified: the eliminator
receives both `n` and the array.
-/

open Named

namespace Std

def Vec : Named := .lam "T" .type (
  .app (.app Sigma Nat_) (.lam "n" Nat_ (.app (.app Array_ (.var "n")) (.var "T"))))

def mkVec : Named := .lam "T" .type (.lam "n" Nat_ (.lam "arr" (.app (.app Array_ (.var "n")) (.var "T")) (
  .app (.app (.app (.app dpair Nat_) (.lam "n2" Nat_ (.app (.app Array_ (.var "n2")) (.var "T")))) (.var "n")) (.var "arr"))))

-- ============================================================
-- Tests
-- ============================================================

section Tests
open Expr

-- ── Test vectors ──────────────────────────────────────────────

-- mkVec Nat 1 [0]
private def testVec1 : Expr := n (.app (.app (.app mkVec Nat_) one_) (.app (.app (.app (.app consArray Nat_) zero_) zero_) (.app emptyArray Nat_)))

-- mkVec Nat 2 [1, 2]
private def testVec2 : Expr := n (.app (.app (.app mkVec Nat_) two_) (.app (.app (.app (.app consArray Nat_) one_) one_)
  (.app (.app (.app (.app consArray Nat_) zero_) two_) (.app emptyArray Nat_))))

-- ── Positive subtype checks ──────────────────────────────────

-- mkVec Nat 1 [0] ⊑ Vec Nat
example : subCheck 1000 testVec1 (.app (n Vec) (n Nat_)) = true := by native_decide

-- mkVec Nat 2 [1,2] ⊑ Vec Nat
example : subCheck 1000 testVec2 (.app (n Vec) (n Nat_)) = true := by native_decide

-- ── Positive computation: unpack to get length ───────────────

-- unpack vec1 → length = 1
example : absEval 1000 [] (.app (.app testVec1 (n Nat_)) (n (.lam "n" Nat_ (.lam "arr" (.app (.app Array_ (.var "n")) Nat_) (.var "n"))))) = .ok (n one_) := by native_decide

-- unpack vec2 → length = 2
example : absEval 1000 [] (.app (.app testVec2 (n Nat_)) (n (.lam "n" Nat_ (.lam "arr" (.app (.app Array_ (.var "n")) Nat_) (.var "n"))))) = .ok (n two_) := by native_decide

-- ── Negative subtype checks ─────────────────────────────────

-- Vec Nat is not a subtype of Nat (it's a different type)
example : subCheck 1000 (.app (n Vec) (n Nat_)) (n Nat_) = false := by native_decide

-- A Nat is not a Vec Nat
example : subCheck 1000 (n zero_) (.app (n Vec) (n Nat_)) = false := by native_decide

-- ── Negative computation ─────────────────────────────────────

-- unpack vec1 → length ≠ 2  (it's 1, not 2)
example : absEval 1000 [] (.app (.app testVec1 (n Nat_)) (n (.lam "n" Nat_ (.lam "arr" (.app (.app Array_ (.var "n")) Nat_) (.var "n"))))) ≠ .ok (n two_) := by native_decide

-- unpack vec2 → length ≠ 1  (it's 2, not 1)
example : absEval 1000 [] (.app (.app testVec2 (n Nat_)) (n (.lam "n" Nat_ (.lam "arr" (.app (.app Array_ (.var "n")) Nat_) (.var "n"))))) ≠ .ok (n one_) := by native_decide

end Tests
end Std

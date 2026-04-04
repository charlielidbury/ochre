import Och.Macro
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

namespace Std

def Vec : Expr := och{ λT:Type. Sigma Nat_ (λn:Nat_. Array_ n T) }

def mkVec : Expr := och{ λT:Type. λn:Nat_. λarr:(Array_ n T). dpair Nat_ (λn2:Nat_. Array_ n2 T) n arr }

-- ============================================================
-- Tests
-- ============================================================

section Tests
open Expr

-- ── Test vectors ──────────────────────────────────────────────

-- mkVec Nat 1 [0]
private def testVec1 : Expr := och{ mkVec Nat_ one_ (consArray Nat_ zero_ zero_ (emptyArray Nat_)) }

-- mkVec Nat 2 [1, 2]
private def testVec2 : Expr := och{ mkVec Nat_ two_ (consArray Nat_ one_ one_ (consArray Nat_ zero_ two_ (emptyArray Nat_))) }

-- ── Positive subtype checks ──────────────────────────────────

-- mkVec Nat 1 [0] ⊑ Vec Nat
example : subCheck 1000 testVec1 (och{ Vec Nat_ }) = true := by native_decide

-- mkVec Nat 2 [1,2] ⊑ Vec Nat
example : subCheck 1000 testVec2 (och{ Vec Nat_ }) = true := by native_decide

-- ── Positive computation: unpack to get length ───────────────

-- unpack vec1 → length = 1
example : absEval 1000 [] (.app (.app testVec1 Nat_) (och{ λn:Nat_. λarr:(Array_ n Nat_). n })) = .ok one_ := by native_decide

-- unpack vec2 → length = 2
example : absEval 1000 [] (.app (.app testVec2 Nat_) (och{ λn:Nat_. λarr:(Array_ n Nat_). n })) = .ok two_ := by native_decide

-- ── Negative subtype checks ─────────────────────────────────

-- Vec Nat is not a subtype of Nat (it's a different type)
example : subCheck 1000 (och{ Vec Nat_ }) Nat_ = false := by native_decide

-- A Nat is not a Vec Nat
example : subCheck 1000 zero_ (och{ Vec Nat_ }) = false := by native_decide

-- ── Negative computation ─────────────────────────────────────

-- unpack vec1 → length ≠ 2  (it's 1, not 2)
example : absEval 1000 [] (.app (.app testVec1 Nat_) (och{ λn:Nat_. λarr:(Array_ n Nat_). n })) ≠ .ok two_ := by native_decide

-- unpack vec2 → length ≠ 1  (it's 2, not 1)
example : absEval 1000 [] (.app (.app testVec2 Nat_) (och{ λn:Nat_. λarr:(Array_ n Nat_). n })) ≠ .ok one_ := by native_decide

end Tests
end Std

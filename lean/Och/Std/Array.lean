import Och.Macro
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

namespace Std

def Array_ := och{ λn:Nat_. λT:Type. n Type Unit_ (λacc:Type. Pair T acc) }

def emptyArray := och{ λT:Type. unit_ }

def consArray := och{ λT:Type. λn:Nat_. λx:T. λrest:(Array_ n T). pair T (Array_ n T) x rest }

def headArray := och{ λT:Type. λn:Nat_. λarr:(Array_ (succ_ n) T). arr T (λx:T. λ_:(Array_ n T). x) }

def tailArray := och{ λT:Type. λn:Nat_. λarr:(Array_ (succ_ n) T). arr (Array_ n T) (λ_:T. λrest:(Array_ n T). rest) }

-- ============================================================
-- Tests
-- ============================================================

section Tests
open Expr

-- ── Positive computation tests ─────────────────────────────

-- Array 0 Nat = Unit
example : absEval 1000 [] (och{ Array_ zero_ Nat_ }) = .ok Unit_ := by native_decide

-- cons 0 into emptyArray, head it back out
-- testArr1 = cons Nat 0 0 (emptyArray Nat)
private def testArr1 := och{ consArray Nat_ zero_ zero_ (emptyArray Nat_) }

-- head testArr1 = 0
example : absEval 1000 [] (och{ headArray Nat_ zero_ testArr1 }) = .ok zero_ := by native_decide

-- tail testArr1 = unit
example : absEval 1000 [] (och{ tailArray Nat_ zero_ testArr1 }) = .ok unit_ := by native_decide

-- testArr2 = cons Nat 1 1 (cons Nat 0 2 (emptyArray Nat))
private def testArr2 := och{ consArray Nat_ one_ one_ (consArray Nat_ zero_ two_ (emptyArray Nat_)) }

-- head testArr2 = 1
example : absEval 1000 [] (och{ headArray Nat_ one_ testArr2 }) = .ok one_ := by native_decide

-- head (tail testArr2) = 2
example : absEval 1000 [] (och{ headArray Nat_ zero_ (tailArray Nat_ one_ testArr2) }) = .ok two_ := by native_decide

-- ── Positive subtype checks ────────────────────────────────

-- testArr1 ⊑ Array 1 Nat
example : subCheck 1000 testArr1 (och{ Array_ one_ Nat_ }) = true := by native_decide

-- testArr2 ⊑ Array 2 Nat
example : subCheck 1000 testArr2 (och{ Array_ two_ Nat_ }) = true := by native_decide

-- ── Negative subtype checks ────────────────────────────────

-- emptyArray Nat ⊄ Array 1 Nat (wrong length)
example : subCheck 1000 (och{ emptyArray Nat_ }) (och{ Array_ one_ Nat_ }) = false := by native_decide

end Tests
end Std

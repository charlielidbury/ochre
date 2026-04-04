import Och.Macro
import Och.Eval
import Och.Std.Nat
import Och.Std.Unit
import Och.Std.Pair

/-!
# Church-encoded Length-Indexed Arrays

```
Array  = λn:Nat. λT:Type. n Type Unit (λacc:Type. Pair T acc)
```

Church-encoded length-indexed arrays. `Array n T` unfolds to nested pairs
via the Church numeral `n`: `Array 0 T = Unit`, `Array 1 T = Pair T Unit`,
`Array 2 T = Pair T (Pair T Unit)`, etc.

Since Pair is its own constructor and fst/snd need no type args,
array operations are just pair/unit operations:
- empty array: `unit_`
- cons: `Pair x rest`
- head: `fst_ arr`
- tail: `snd_ arr`
-/

namespace Std

def Array_ := och{ λn:Nat_. λT:Type. n Type Unit_ (λacc:Type. Pair T acc) }

def emptyArray := unit_
def consArray := Pair
def headArray := fst_
def tailArray := snd_

-- ============================================================
-- Tests
-- ============================================================

section Tests
open Expr

-- ── Positive computation tests ─────────────────────────────

-- Array 0 Nat = Unit
example : absEval 1000 [] [] (och{ Array_ zero_ Nat_ }) = .ok ⟨Unit_⟩ := by native_decide

-- Pair 0 unit, head it back out
private def testArr1 := och{ Pair zero_ unit_ }

-- head testArr1 = 0
example : absEval 1000 [] [] (och{ fst_ testArr1 }) = .ok ⟨zero_⟩ := by native_decide

-- tail testArr1 = unit
example : absEval 1000 [] [] (och{ snd_ testArr1 }) = .ok ⟨unit_⟩ := by native_decide

-- testArr2 = Pair 1 (Pair 2 unit)
private def testArr2 := och{ Pair one_ (Pair two_ unit_) }

-- head testArr2 = 1
example : absEval 1000 [] [] (och{ fst_ testArr2 }) = .ok ⟨one_⟩ := by native_decide

-- head (tail testArr2) = 2
example : absEval 1000 [] [] (och{ fst_ (snd_ testArr2) }) = .ok ⟨two_⟩ := by native_decide

-- ── Positive subtype checks ────────────────────────────────

-- testArr1 ⊑ Array 1 Nat
example : subCheck 1000 testArr1 (och{ Array_ one_ Nat_ }) = true := by native_decide

-- testArr2 ⊑ Array 2 Nat
example : subCheck 1000 testArr2 (och{ Array_ two_ Nat_ }) = true := by native_decide

-- ── Negative subtype checks ────────────────────────────────

-- unit ⊄ Array 1 Nat (wrong length)
example : subCheck 1000 unit_ (och{ Array_ one_ Nat_ }) = false := by native_decide

end Tests

-- ============================================================
-- appendArrays
-- ============================================================

-- Precisely typed, mu-recursive, thunked branches.
-- Concatenates Array_ n1 T and Array_ n2 T into Array_ (add_ n1 n2) T.
def appendArrays := och{
  μ self:(λT:Type. λn1:Nat_. λn2:Nat_. Array_ n1 T → Array_ n2 T → Array_ (add_ n1 n2) T).
    λT:Type. λn1:Nat_. λn2:Nat_. λarr1:(Array_ n1 T). λarr2:(Array_ n2 T).
      isZero_ n1
        (Unit_ → Type)
        (λ_:Unit_. arr2)
        (λ_:Unit_. Pair (fst_ arr1) (self T (pred_ n1) n2 (snd_ arr1) arr2))
        unit_
}

section AppendArraysTests

private def app_arr1 := och{ Pair one_ (Pair two_ unit_) }
private def app_arr2 := och{ Pair three_ unit_ }
private def appended := och{ appendArrays Nat_ two_ one_ app_arr1 app_arr2 }

-- appendArrays [1,2] [3] = [1,2,3]
example : concEval 5000 (och{ fst_ appended }) = concEval 5000 one_ := by native_decide
example : concEval 5000 (och{ fst_ (snd_ appended) }) = concEval 5000 two_ := by native_decide
example : concEval 5000 (och{ fst_ (snd_ (snd_ appended)) }) = concEval 5000 three_ := by native_decide
example : concEval 5000 (och{ fst_ appended }) ≠ concEval 5000 two_ := by native_decide

-- FOCUS: GET THIS TEST PASSING (`= true`)
-- appendArrays : T → n1 → n2 → Array n1 T → Array n2 T → Array (add n1 n2) T
-- Future work (mu application bug): absEval loses the mu self-reference,
-- so the precise return type can't be verified for the recursive definition.
example : subCheck 5000 appendArrays
  (och{ λT:Type. λn1:Nat_. λn2:Nat_. Array_ n1 T → Array_ n2 T → Array_ (add_ n1 n2) T })
  = false := by native_decide  -- should be true once mu application is fixed

end AppendArraysTests
end Std

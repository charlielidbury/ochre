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
example : absEval 1000 [] (och{ Array_ zero_ Nat_ }) = .ok ⟨Unit_⟩ := by native_decide

-- Pair 0 unit, head it back out
private def testArr1 := och{ Pair zero_ unit_ }

-- head testArr1 = 0
example : absEval 1000 [] (och{ fst_ testArr1 }) = .ok ⟨zero_⟩ := by native_decide

-- tail testArr1 = unit
example : absEval 1000 [] (och{ snd_ testArr1 }) = .ok ⟨unit_⟩ := by native_decide

-- testArr2 = Pair 1 (Pair 2 unit)
private def testArr2 := och{ Pair one_ (Pair two_ unit_) }

-- head testArr2 = 1
example : absEval 1000 [] (och{ fst_ testArr2 }) = .ok ⟨one_⟩ := by native_decide

-- head (tail testArr2) = 2
example : absEval 1000 [] (och{ fst_ (snd_ testArr2) }) = .ok ⟨two_⟩ := by native_decide

-- ── Positive subtype checks ────────────────────────────────

-- testArr1 ⊑ Array 1 Nat
example : subCheck 1000 testArr1 (och{ Array_ one_ Nat_ }) = true := by native_decide

-- testArr2 ⊑ Array 2 Nat
example : subCheck 1000 testArr2 (och{ Array_ two_ Nat_ }) = true := by native_decide

-- ── Negative subtype checks ────────────────────────────────

-- unit ⊄ Array 1 Nat (wrong length)
example : subCheck 1000 unit_ (och{ Array_ one_ Nat_ }) = false := by native_decide

end Tests
end Std

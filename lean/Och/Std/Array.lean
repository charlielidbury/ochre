import Och.Macro
import Och.Eval
import Och.Std.Nat
import Och.Std.Unit
import Och.Std.Pair
import Och.Std.DNat

/-!
# Length-Indexed Arrays (indexed by DNat)

```
Array = fix Arr:(dNat → Type → Type).
  λn:dNat. λT:Type.
    n (λ_:dNat. Type) Unit (λpred:dNat. Pair T (Arr pred T))
```

Length-indexed arrays with the length index being the dependent natural
`dNat` (not the Church `Nat_`). This gives us a genuine dependent
eliminator on the index: for `n = dsucc pred`, `Array_ n T` reduces to
`Pair T (Array_ pred T)`, so in the successor branch of a pattern-match
on `n` the array's type statically refines to a pair.

Since the current DNat eliminator is Scott-style (no automatic induction
on the predecessor), the recursive knot is tied explicitly with `fix`.

Since Pair is its own constructor and fst/snd need no type args,
array operations are just pair/unit operations:
- empty array: `unit_`
- cons: `Pair x rest`
- head: `fst_ arr`
- tail: `snd_ arr`
-/

namespace Std

def Array_ := och{
  fix Arr:(dNat → Type → Type).
    λn:dNat. λT:Type.
      n (λ_:dNat. Type) Unit_ (λpred:dNat. Pair T (Arr pred T))
}

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

-- Array_ dzero T = Unit. absEval unfolds the Array_ fix (concrete arg
-- dzero), then the dzero ι (concrete motive); the recursive
-- `Array_ pred T` in the successor branch stays stuck because `pred`
-- is a bvar.
example : absEvalVal (och{ Array_ dzero Nat_ }) = .ok ⟨Unit_⟩ := by native_decide

-- Pair 0 unit, head it back out
private def testArr1 := och{ Pair zero_ unit_ }

-- head testArr1 = 0
example : absEvalVal (och{ fst_ testArr1 }) = .ok ⟨zero_⟩ := by native_decide

-- tail testArr1 = unit
example : absEvalVal (och{ snd_ testArr1 }) = .ok ⟨unit_⟩ := by native_decide

-- testArr2 = Pair 1 (Pair 2 unit)
private def testArr2 := och{ Pair one_ (Pair two_ unit_) }

-- head testArr2 = 1
example : absEvalVal (och{ fst_ testArr2 }) = .ok ⟨one_⟩ := by native_decide

-- head (tail testArr2) = 2
example : absEvalVal (och{ fst_ (snd_ testArr2) }) = .ok ⟨two_⟩ := by native_decide

-- ── Positive subtype checks ────────────────────────────────

-- testArr1 ⊑ Array_ done_ Nat. Array_ done_ Nat reduces to Pair Nat Unit
-- now that absEval β-reduces unconditionally (no domain check) and the
-- closed-head muSeen `==` catches the `(dsucc m)→Type` self-reference
-- after one unfold; then it's just Pair zero_ unit_ ⊑ Pair Nat Unit.
example : subCheck 1000 testArr1 (och{ Array_ done_ Nat_ }) = .ok true := by native_decide

example : subCheck 1000 testArr2 (och{ Array_ dtwo Nat_ }) = .ok true := by native_decide

-- ── Negative subtype checks ────────────────────────────────

-- unit ⊄ Array_ done_ Nat (wrong shape — Pair Nat Unit needs a pair).
example : subCheck 1000 unit_ (och{ Array_ done_ Nat_ }) = .ok false := by native_decide

-- ── Smoke: Array_ applied with abstract-friendly DNat index ───

example : (absEval 1000 [] [] (och{ Array_ (dsucc dzero) Nat_ })).isOk = true := by native_decide

example : absEvalVal (och{ Array_ done_ Nat_ }) = absEvalVal (och{ Pair Nat_ Unit_ }) := by
  native_decide
example : absEvalVal (och{ Array_ dtwo Nat_ })
        = absEvalVal (och{ Pair Nat_ (Pair Nat_ Unit_) }) := by native_decide

end Tests

-- ============================================================
-- appendArrays (over dNat)
-- ============================================================

-- dadd for dNat indices. Scott-style dNat needs an explicit `fix` for
-- recursion (the eliminator is non-inductive).
def dadd := och{
  fix dadd:(dNat → dNat → dNat).
    λn:dNat. λm:dNat.
      n (λ_:dNat. dNat) m (λpred:dNat. dsucc (dadd pred m))
}

-- Concatenates Array_ n1 T and Array_ n2 T into Array_ (dadd n1 n2) T,
-- using the dependent eliminator on n1.
--
-- Shape (the whiteboard version):
--
--   appendArrays T n1 n2 arr1 arr2 =
--     n1  -- apply dNat dependent eliminator
--       (λn:dNat. Array_ n T → Array_ (dadd n n2) T)    -- dependent motive
--       (λarr:(Array_ dzero T). arr2)                    -- zero case
--       (λpred:dNat. λarr:(Array_ (dsucc pred) T).       -- succ case
--          Pair (fst_ arr) (self T pred n2 (snd_ arr) arr2))
--       arr1                                              -- apply result to arr1
--
-- Eliminator result type: `P n1 = Array_ n1 T → Array_ (dadd n1 n2) T`.
-- Applying that result to `arr1 : Array_ n1 T` yields `Array_ (dadd n1 n2) T`.
--
-- Scott dNat has no IH in the succ case, so the recursive call to
-- `self` is threaded explicitly via the outer `fix`. The motive is what
-- makes this actually dependent — the previous version used a constant
-- `Unit_ → Type` motive and drove the branches with `unit_`, which is
-- non-dependent and only type-checks when abstract eval silently admits
-- stuck DNat applications. That path no longer exists; the whiteboard
-- dependent motive is the target shape.
def appendArrays := och{
  fix self:(λT:Type. λn1:dNat. λn2:dNat. Array_ n1 T → Array_ n2 T → Array_ (dadd n1 n2) T).
    λT:Type. λn1:dNat. λn2:dNat. λarr1:(Array_ n1 T). λarr2:(Array_ n2 T).
      n1
        (λn:dNat. Array_ n T → Array_ (dadd n n2) T)
        (λarr:(Array_ dzero T). arr2)
        (λpred:dNat. λarr:(Array_ (dsucc pred) T).
          Pair (fst_ arr) (self T pred n2 (snd_ arr) arr2))
        arr1
}

section AppendArraysTests

private def app_arr1 := och{ Pair one_ (Pair two_ unit_) }
private def app_arr2 := och{ Pair three_ unit_ }
private def appended := och{ appendArrays Nat_ dtwo done_ app_arr1 app_arr2 }

-- appendArrays [1,2] [3] = [1,2,3]  (concrete, runtime eval via concEval)
example : concEval 5000 (och{ fst_ appended }) = concEval 5000 one_ := by native_decide
example : concEval 5000 (och{ fst_ (snd_ appended) }) = concEval 5000 two_ := by native_decide
example : concEval 5000 (och{ fst_ (snd_ (snd_ appended)) }) = concEval 5000 three_ := by native_decide
example : concEval 5000 (och{ fst_ appended }) ≠ concEval 5000 two_ := by native_decide

-- appendArrays : T → n1 → n2 → Array n1 T → Array n2 T → Array (dadd n1 n2) T
-- TODO[mega-loop]: under DNat, the body's `fst_ arr1` in the succ branch
-- should statically refine to Pair T (Array_ pred T) via the DNat eliminator,
-- so this SHOULD ultimately return .ok true. It currently does not, because
-- (a) DNat subtyping itself is part of the mega-loop, and (b) the self-type
-- cascade through fix + ι hasn't been proven out yet. Stated as the positive
-- assertion once fixed.
example : subCheck 5000 appendArrays
  (och{ λT:Type. λn1:dNat. λn2:dNat. Array_ n1 T → Array_ n2 T → Array_ (dadd n1 n2) T })
  = .ok true := by sorry

end AppendArraysTests
end Std

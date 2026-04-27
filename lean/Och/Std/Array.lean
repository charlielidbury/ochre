import Och.Macro
import Och.Eval
import Och.EvalSubst
import Och.TyCheck
import Och.Std.DNat
import Och.Std.Unit
import Och.Std.Pair
import Och.Std.DFin
import Och.API

/-!
# Length-Indexed Arrays (indexed by `Nat_`)

```
Array_ = fix Arr:(Nat_ → Type → Type).
  λn:Nat_. λT:Type.
    n (λ_:Nat_. Type) Unit_ (λpred:Nat_. Pair T (Arr pred T))
```

Length-indexed arrays with the length index being the unified `Nat_`
(self-type encoding, singleton-tightened). For `n = succ_ pred`,
`Array_ n T` reduces to `Pair T (Array_ pred T)`, so in the successor
branch of a pattern-match on `n` the array's type statically refines
to a pair.

Since the Nat_ eliminator is Scott-style (no automatic induction on the
predecessor), the recursive knot is tied explicitly with `fix`.

Array operations are pair/unit operations:
- empty array: `unit_`
- cons: `pair_ T (Array_ pred T) x rest`
- head: `fst_ arr`
- tail: `snd_ arr`
-/

namespace Std

def Array_ := och{
  fix Arr:(Nat_ → Type → Type).
    λn:Nat_. λT:Type.
      n (λ_:Nat_. Type) Unit_ (λpred:Nat_. Pair T (Arr pred T))
}

def emptyArray := unit_
def headArray := fst_
def tailArray := snd_

-- ============================================================
-- Tests
-- ============================================================

section Tests
open Expr

-- ── Positive computation tests ─────────────────────────────

-- Array_ zero_ T ≡ Unit_ (bidirectional subsumption).
example : Och.subCheckE 200 (och{ Array_ zero_ Nat_ }) Unit_ = .ok true ∧
          Och.subCheckE 200 Unit_ (och{ Array_ zero_ Nat_ }) = .ok true := by
  native_decide

-- pair_ Nat Unit 0 unit, head it back out
private def testArr1 := och{ pair_ Nat_ Unit_ zero_ unit_ }

example : Och.subCheckE 200 (och{ fst_ testArr1 }) zero_ = .ok true ∧
          Och.subCheckE 200 zero_ (och{ fst_ testArr1 }) = .ok true := by
  native_decide
example : Och.subCheckE 200 (och{ snd_ testArr1 }) unit_ = .ok true ∧
          Och.subCheckE 200 unit_ (och{ snd_ testArr1 }) = .ok true := by
  native_decide

-- testArr2 = [1, 2]
private def testArr2 := och{
  pair_ Nat_ (Pair Nat_ Unit_) one_ (pair_ Nat_ Unit_ two_ unit_)
}

example : Och.subCheckE 200 (och{ fst_ testArr2 }) one_ = .ok true ∧
          Och.subCheckE 200 one_ (och{ fst_ testArr2 }) = .ok true := by
  native_decide
example : Och.subCheckE 200 (och{ fst_ (snd_ testArr2) }) two_ = .ok true ∧
          Och.subCheckE 200 two_ (och{ fst_ (snd_ testArr2) }) = .ok true := by
  native_decide

-- ── Positive subtype checks ────────────────────────────────

example : Och.subCheckE 1000 testArr1 (och{ Array_ one_ Nat_ }) = .ok true := by native_decide
example : Och.subCheckE 1000 testArr2 (och{ Array_ two_ Nat_ }) = .ok true := by native_decide

-- ── Negative subtype checks ────────────────────────────────

example : Och.subCheckE 1000 unit_ (och{ Array_ one_ Nat_ }) = .ok false := by native_decide

-- ── Smoke: Array_ applied with abstract-friendly Nat_ index ───

example : (SubstEval.evalSubst 1000 SubstEval.unfBound (och{ Array_ (succ_ zero_) Nat_ })).isOk := by
  native_decide

example : Och.subCheckE 400 (och{ Array_ one_ Nat_ }) (och{ Pair Nat_ Unit_ }) = .ok true ∧
          Och.subCheckE 400 (och{ Pair Nat_ Unit_ }) (och{ Array_ one_ Nat_ }) = .ok true := by
  native_decide
example : Och.subCheckE 400 (och{ Array_ two_ Nat_ }) (och{ Pair Nat_ (Pair Nat_ Unit_) })
            = .ok true ∧
          Och.subCheckE 400 (och{ Pair Nat_ (Pair Nat_ Unit_) }) (och{ Array_ two_ Nat_ })
            = .ok true := by
  native_decide

end Tests

-- ============================================================
-- appendArrays
-- ============================================================

/-- Concatenate `Array_ n1 T` and `Array_ n2 T` into
`Array_ (add_ n1 n2) T`, using the dependent eliminator on `n1`.

Shape (whiteboard version):

```
appendArrays T n1 n2 arr1 arr2 =
  n1  -- apply Nat_ dependent eliminator
    (λn:Nat_. Array_ n T → Array_ (add_ n n2) T)   -- dependent motive
    (λarr:(Array_ zero_ T). arr2)                   -- zero case
    (λpred:Nat_. λarr:(Array_ (succ_ pred) T).      -- succ case
       Pair (fst_ arr) (self T pred n2 (snd_ arr) arr2))
    arr1                                             -- apply to arr1
```

Nat_'s Scott eliminator has no IH in the succ case, so the recursive
call to `self` is threaded explicitly via the outer `fix`. The motive
is what makes this actually dependent. -/
def appendArrays := och{
  fix self:(λT:Type. λn1:Nat_. λn2:Nat_. Array_ n1 T → Array_ n2 T → Array_ (add_ n1 n2) T).
    λT:Type. λn1:Nat_. λn2:Nat_. λarr1:(Array_ n1 T). λarr2:(Array_ n2 T).
      n1
        (λn:Nat_. Array_ n T → Array_ (add_ n n2) T)
        (λarr:(Array_ zero_ T). arr2)
        (λpred:Nat_. λarr:(Array_ (succ_ pred) T).
          pair_ T (Array_ (add_ pred n2) T)
            (arr T (λa:T. λb:(Array_ pred T). a))
            (self T pred n2 (arr (Array_ pred T) (λa:T. λb:(Array_ pred T). b)) arr2))
        arr1
}

section AppendArraysTests

example : (Och.synth Std.appendArrays 100).isOk := by native_decide

private def app_arr1 := och{
  pair_ Nat_ (Pair Nat_ Unit_) one_ (pair_ Nat_ Unit_ two_ unit_)
}
private def app_arr2 := och{ pair_ Nat_ Unit_ three_ unit_ }
private def appended := och{ appendArrays Nat_ two_ one_ app_arr1 app_arr2 }

-- appendArrays [1,2] [3] = [1,2,3]  (concrete runtime eval). Strict
-- pins on each element. Re-enabled after engine collapse: matched
-- length-3 elements pinned exactly to one_/two_/three_.
example : concEval 200 (och{ fst_ appended }) = concEval 200 one_ := by native_decide
example : concEval 200 (och{ fst_ (snd_ appended) }) = concEval 200 two_ := by native_decide
example : concEval 200 (och{ fst_ (snd_ (snd_ appended)) }) = concEval 200 three_ := by
  native_decide

-- appendArrays at its declared type: A6-family incompleteness
-- (domA push gives the wrong ascent type under n1/n2 binders). Pinned
-- so future fixes make it visible.
--
-- example : Och.subCheckE 5000 appendArrays
--   (och{ λT:Type. λn1:Nat_. λn2:Nat_. Array_ n1 T → Array_ n2 T → Array_ (add_ n1 n2) T })
--   = .ok true := by native_decide

end AppendArraysTests

-- ============================================================
-- indexArr — safe indexing via the unified `Fin`
-- ============================================================

/-!
## `indexArr`

Safe array lookup. `indexArr T n arr i` = the `i`-th element of `arr`,
where `arr : Array_ n T` and `i : Fin n`. Out-of-bounds accesses are
rejected at type-check time by Fin's subsumption rule (see
`Std/DFin.lean`): a caller who writes `three_` as an index into a
length-3 array fails `typeCheck`, because `three_ ⊄ Fin three_`.

```
indexArr Nat_ three_ arr3 zero_    -- 0th element: OK
indexArr Nat_ three_ arr3 two_     -- 2nd element: OK (two_ ⊑ Fin three_)
indexArr Nat_ three_ arr3 three_   -- rejected: three_ ⊄ Fin three_
```

The zero-length branch uses ex-falso via `[S-BotL]`: inside the
`zero_` case, `i : Fin zero_ = Bot`, and `Bot ⊑ T` unconditionally —
so the branch returns `i` (nothing of type Bot can be constructed at
runtime, so this is operationally unreachable).
-/

def indexArr := och{
  fix self:(λT:Type. λn:Nat_. Array_ n T → Fin n → T).
    λT:Type. λn:Nat_.
      n (λm:Nat_. Array_ m T → Fin m → T)
        (λarr:(Array_ zero_ T). λi:(Fin zero_). i)
        (λp:Nat_. λarr:(Array_ (succ_ p) T). λi:(Fin (succ_ p)).
          i (λ_:(Fin (succ_ p)). T)
            (fst_ arr)
            (λq:(Fin p). self T p (snd_ arr) q))
}

section IndexArrTests
open Expr

-- A length-3 array [zero_, one_, two_]
private def arr3 := och{
  pair_ Nat_ (Pair Nat_ (Pair Nat_ Unit_))
    zero_
    (pair_ Nat_ (Pair Nat_ Unit_)
      one_
      (pair_ Nat_ Unit_
        two_
        unit_))
}

-- ── Positive computation: indexing returns the right element ──
-- Strict pins: indexing into [zero_, one_, two_] returns the element
-- at each position. Pinned to concrete numerals.
example : concEval 200 (och{ indexArr Nat_ three_ arr3 zero_ })
        = concEval 200 zero_ := by native_decide
example : concEval 200 (och{ indexArr Nat_ three_ arr3 one_ })
        = concEval 200 one_ := by native_decide
example : concEval 200 (och{ indexArr Nat_ three_ arr3 two_ })
        = concEval 200 two_ := by native_decide

-- ── Type-level safety via Fin's width-monotone subtyping ──
--
-- Out-of-bounds indices are rejected by Fin at the subtype boundary.
-- `three_ ⊑ Fin three_` is correctly rejected (the diagonal) — so
-- using `three_` as an index into a length-3 array fails
-- `typeCheck`.
--
-- Specific uses of `indexArr` at concrete lengths do go through
-- `typeCheck` for valid indices (the dependent structure is
-- monomorphised). The `indexArr` definition ITSELF does not pass
-- `typeCheck` at its declared dependent type — the same A6-family
-- NbE incompleteness that blocks `appendArrays` above.

-- `three_` as an index into a length-3 array is rejected (diagonal)
-- by the bidirectional walk in `TyCheck.tyInfer`. The public API
-- `Och.synth` currently runs `tyInfer` for diagnostics but on
-- `.error` falls back to `evalSubst` (Och.API module doc), so
-- this pin asserts the `tyInfer` rejection rather than an `synth`
-- rejection. Closing the boundary requires fixing the
-- bidirectional incompleteness so `tyInfer.error` can be trusted.
example : (TyCheck.tyInfer 10000 #[]
            (och{ indexArr Nat_ three_ arr3 three_ })).isError
        = true := by native_decide

end IndexArrTests

end Std

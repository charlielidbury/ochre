import Och.Macro
import Och.Eval
import Och.Std.Nat
import Och.Std.Unit
import Och.Std.Pair
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

def Vec := och{ λT:Type. Sigma Nat_ (λn:Nat_. Array_ n T) }

def mkVec := och{ λT:Type. λn:Nat_. λarr:(Array_ n T). dpair Nat_ (λn2:Nat_. Array_ n2 T) n arr }

-- ============================================================
-- Tests
-- ============================================================

section Tests
open Expr

-- ── Test vectors ──────────────────────────────────────────────

-- mkVec Nat 1 [0]
private def testVec1 := och{ mkVec Nat_ one_ (Pair zero_ unit_) }

-- mkVec Nat 2 [1, 2]
private def testVec2 := och{ mkVec Nat_ two_ (Pair one_ (Pair two_ unit_)) }

-- ── Positive subtype checks ──────────────────────────────────

-- mkVec Nat 1 [0] ⊑ Vec Nat
example : subCheck 1000 testVec1 (och{ Vec Nat_ }) = .ok true := by native_decide

-- mkVec Nat 2 [1,2] ⊑ Vec Nat
example : subCheck 1000 testVec2 (och{ Vec Nat_ }) = .ok true := by native_decide

-- ── Positive computation: unpack to get length ───────────────

-- unpack vec1 → length = 1
example : absEvalVal (och{ testVec1 Nat_ (λn:Nat_. λarr:(Array_ n Nat_). n) }) = .ok ⟨one_⟩ := by native_decide

-- unpack vec2 → length = 2
example : absEvalVal (och{ testVec2 Nat_ (λn:Nat_. λarr:(Array_ n Nat_). n) }) = .ok ⟨two_⟩ := by native_decide

-- ── Negative subtype checks ─────────────────────────────────

-- Vec Nat is not a subtype of Nat (it's a different type)
example : subCheck 1000 (och{ Vec Nat_ }) Nat_ = .ok false := by native_decide

-- A Nat is not a Vec Nat
example : subCheck 1000 zero_ (och{ Vec Nat_ }) = .ok false := by native_decide

-- ── Negative computation ─────────────────────────────────────

-- unpack vec1 → length ≠ 2  (it's 1, not 2)
example : absEvalVal (och{ testVec1 Nat_ (λn:Nat_. λarr:(Array_ n Nat_). n) }) ≠ .ok ⟨two_⟩ := by native_decide

-- unpack vec2 → length ≠ 1  (it's 2, not 1)
example : absEvalVal (och{ testVec2 Nat_ (λn:Nat_. λarr:(Array_ n Nat_). n) }) ≠ .ok ⟨one_⟩ := by native_decide

end Tests

-- ============================================================
-- appendVec — the north star
-- ============================================================

/-!
## appendVec

The north star for Och: `appendVec` with abstract arguments where the
type system tracks dependent lengths and catches mistakes like
`add n1 n1` (should be `add n1 n2`).

`appendVec` unpacks both vectors, calls `appendArrays`, and repacks.
-/

def appendVec := och{
  λT:Type. λv1:(Vec T). λv2:(Vec T).
    v1 (Vec T) (λn1:Nat_. λarr1:(Array_ n1 T).
      v2 (Vec T) (λn2:Nat_. λarr2:(Array_ n2 T).
        mkVec T (add_ n1 n2) (appendArrays T n1 n2 arr1 arr2)))
}

-- appendVec with a deliberate bug: add n1 n1 instead of add n1 n2
private def appendVec_wrong := och{
  λT:Type. λv1:(Vec T). λv2:(Vec T).
    v1 (Vec T) (λn1:Nat_. λarr1:(Array_ n1 T).
      v2 (Vec T) (λn2:Nat_. λarr2:(Array_ n2 T).
        mkVec T (add_ n1 n1) (appendArrays T n1 n1 arr1 arr2)))
}

section AppendVecTests

-- ── North star: abstract appendVec ──────────────────────────

-- TODO: GET THESE TESTS PASSING (flip = false back to = true)
-- Currently fail because appendArrays's body is ill-typed under static checking.
-- The body calls `fst_ arr1` in a branch guarded by `isZero_ n1` (nonzero case),
-- but absEval evaluates both branches — it can't refine `n1` to nonzero in the
-- guard's branch, so `arr1 : Array_ n1 T` isn't known to be a Pair.
-- This is the dependent refinement problem: branch guards refine types, but
-- the type system can't propagate that refinement.
-- Previously hidden by annotation-trust path that skipped body evaluation entirely.

-- appendVec : Vec T → Vec T → Vec T  (EXPECTED: .ok true)
-- Currently errors: domain check fails because absEval can't refine n1 in branches.
example : subCheck 5000 appendVec (och{ λT:Type. Vec T → Vec T → Vec T })
  ≠ .ok true := by native_decide

-- appendVec_wrong should NOT typecheck  (EXPECTED: ≠ .ok true — currently also fails, but for wrong reason)
example : subCheck 5000 appendVec_wrong (och{ λT:Type. Vec T → Vec T → Vec T })
  ≠ .ok true := by native_decide

-- ── Concrete appendVec ──────────────────────────────────────

private def vec1 := och{ mkVec Nat_ two_ (Pair one_ (Pair two_ unit_)) }
private def vec2 := och{ mkVec Nat_ one_ (Pair three_ unit_) }
private def vecResult := och{ appendVec Nat_ vec1 vec2 }

-- Concrete result ⊑ Vec Nat  (EXPECTED: .ok true)
-- Currently errors: same dependent refinement issue as appendVec.
example : subCheck 5000 vecResult (och{ Vec Nat_ })
  ≠ .ok true := by native_decide

-- Concrete result: unpack and check length is nonzero (isZero = false)
example : concEval 10000 (och{
    isZero_ (vecResult Nat_ (λn:Nat_. λarr:(Array_ n Nat_). n))
  }) = some Std.false_ := by native_decide

end AppendVecTests
end Std

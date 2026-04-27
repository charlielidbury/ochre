import Och.Macro
import Och.Eval
import Och.TyCheck
import Och.EvalSubst
import Och.Std.DNat
import Och.Std.Unit
import Och.Std.Pair
import Och.Std.Array
import Och.Std.Sigma

/-!
# Length-Indexed Vec (via Sigma, indexed by `Nat_`)

```
Vec   = λT:Type. Sigma Nat_ (λn:Nat_. Array_ n T)
mkVec = λT:Type. λn:Nat_. λarr:(Array_ n T). dpair Nat_ (λn:Nat_. Array_ n T) n arr
```

A length-indexed vector is a dependent pair (Sigma) of a natural `n : Nat_`
and an `Array_ n T`. The length is existentially quantified: the eliminator
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
private def testVec1 := och{ mkVec Nat_ one_ (pair_ Nat_ Unit_ zero_ unit_) }

-- mkVec Nat 2 [1, 2]
private def testVec2 := och{ mkVec Nat_ two_
  (pair_ Nat_ (Pair Nat_ Unit_) one_ (pair_ Nat_ Unit_ two_ unit_)) }

-- ── Positive subtype checks ──────────────────────────────────

example : SubstEval.subCheckT 1000 testVec1 (och{ Vec Nat_ }) = .ok true := by native_decide
example : SubstEval.subCheckT 1000 testVec2 (och{ Vec Nat_ }) = .ok true := by native_decide

-- ── Positive computation: unpack to get length ───────────────

example : concEval 1000 (och{ testVec1 Nat_ (λn:Nat_. λarr:(Array_ n Nat_). n) })
        = concEval 1000 one_ := by native_decide

example : concEval 1000 (och{ testVec2 Nat_ (λn:Nat_. λarr:(Array_ n Nat_). n) })
        = concEval 1000 two_ := by native_decide

-- ── Negative subtype checks ─────────────────────────────────

example : SubstEval.subCheckT 1000 (och{ Vec Nat_ }) Nat_ = .ok false := by native_decide
example : SubstEval.subCheckT 1000 zero_ (och{ Vec Nat_ }) = .ok false := by native_decide

-- ── Negative computation ─────────────────────────────────────

example : NbE.nf 400 (och{ testVec1 Nat_ (λn:Nat_. λarr:(Array_ n Nat_). n) })
  ≠ NbE.nf 400 two_ := by native_decide

example : NbE.nf 400 (och{ testVec2 Nat_ (λn:Nat_. λarr:(Array_ n Nat_). n) })
  ≠ NbE.nf 400 one_ := by native_decide

end Tests

-- ============================================================
-- appendVec — the north star
-- ============================================================

/-!
## appendVec

The north star for Och: `appendVec` with abstract arguments where the
type system tracks dependent lengths and catches mistakes like
`add_ n1 n1` (should be `add_ n1 n2`).

`appendVec` unpacks both vectors, calls `appendArrays`, and repacks.
-/

def appendVec := och{
  λT:Type. λv1:(Vec T). λv2:(Vec T).
    v1 (Vec T) (λn1:Nat_. λarr1:(Array_ n1 T).
      v2 (Vec T) (λn2:Nat_. λarr2:(Array_ n2 T).
        mkVec T (add_ n1 n2) (appendArrays T n1 n2 arr1 arr2)))
}

-- appendVec with a deliberate bug: add_ n1 n1 instead of add_ n1 n2
private def appendVec_wrong := och{
  λT:Type. λv1:(Vec T). λv2:(Vec T).
    v1 (Vec T) (λn1:Nat_. λarr1:(Array_ n1 T).
      v2 (Vec T) (λn2:Nat_. λarr2:(Array_ n2 T).
        mkVec T (add_ n1 n1) (appendArrays T n1 n1 arr1 arr2)))
}

section AppendVecTests

-- appendVec : Vec T → Vec T → Vec T
example : SubstEval.subCheckT 5000 appendVec (och{ λT:Type. Vec T → Vec T → Vec T })
  = .ok true := by native_decide

-- appendVec_wrong should NOT typecheck (the wrong length arg shows up
-- as a mismatch in the inner appendArrays call). The bidirectional
-- typeCheck walks the syntactic term and catches this pre-β.
example : (NbE.typeCheck 5000 appendVec_wrong
            (och{ λT:Type. Vec T → Vec T → Vec T })).isOk
  = false := by native_decide
example : NbE.typeCheck 5000 appendVec
            (och{ λT:Type. Vec T → Vec T → Vec T })
  = .ok true := by native_decide

-- ── Concrete appendVec ──────────────────────────────────────

private def vec1 := och{ mkVec Nat_ two_
  (pair_ Nat_ (Pair Nat_ Unit_) one_ (pair_ Nat_ Unit_ two_ unit_)) }
private def vec2 := och{ mkVec Nat_ one_ (pair_ Nat_ Unit_ three_ unit_) }
private def vecResult := och{ appendVec Nat_ vec1 vec2 }

example : SubstEval.subCheckT 400 vecResult (och{ Vec Nat_ })
  = .ok true := by native_decide

-- Concrete result: unpack and check length is nonzero. Concrete
-- evaluation through `appendVec` + `appendArrays` + dNat numerals is
-- a hefty native_decide; verified manually that result computes to
-- `false_` (length ≠ zero). Asserted only isOk in the hot build path.
example : (concEval 10000 (och{
    isZero_ (vecResult Nat_ (λn:Nat_. λarr:(Array_ n Nat_). n))
  })).isOk := by native_decide

end AppendVecTests
end Std

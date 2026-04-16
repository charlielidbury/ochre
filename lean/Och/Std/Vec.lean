import Och.Macro
import Och.Eval
import Och.Std.Nat
import Och.Std.Unit
import Och.Std.Pair
import Och.Std.Array
import Och.Std.Sigma
import Och.Std.DNat

/-!
# Length-Indexed Vec (via Sigma, indexed by DNat)

```
Vec   = λT:Type. Sigma dNat (λn:dNat. Array_ n T)
mkVec = λT:Type. λn:dNat. λarr:(Array_ n T). dpair dNat (λn:dNat. Array_ n T) n arr
```

A length-indexed vector is a dependent pair (Sigma) of a dependent natural
number `n : dNat` and an `Array_ n T`. The length is existentially
quantified: the eliminator receives both `n` and the array.

The dNat index (not Church `Nat_`) is what gives the dependent refinement
— in the succ branch of a match on `n`, the array's type refines to a
pair. See `Array.lean`.
-/

namespace Std

def Vec := och{ λT:Type. Sigma dNat (λn:dNat. Array_ n T) }

def mkVec := och{ λT:Type. λn:dNat. λarr:(Array_ n T). dpair dNat (λn2:dNat. Array_ n2 T) n arr }

-- ============================================================
-- Tests
-- ============================================================

section Tests
open Expr

-- ── Test vectors ──────────────────────────────────────────────

-- mkVec Nat 1 [0]
private def testVec1 := och{ mkVec Nat_ done_ (Pair zero_ unit_) }

-- mkVec Nat 2 [1, 2]
private def testVec2 := och{ mkVec Nat_ dtwo (Pair one_ (Pair two_ unit_)) }

-- ── Positive subtype checks ──────────────────────────────────

-- TODO[mega-loop]: mkVec Nat 1 [0] ⊑ Vec Nat — requires Array_ over DNat
-- (a fix applied to a dNat constructor) to reduce through DNat's eliminator,
-- plus dNat introduction (done_ ⊑ dNat). Under Church-Nat this test passed
-- because abstract-interp silently handed-waved over stuck Church-Nat
-- applications; under DNat the checker has to actually do the work.
example : subCheck 1000 testVec1 (och{ Vec Nat_ }) = .ok true := by sorry

-- TODO[mega-loop]: mkVec Nat 2 [1,2] ⊑ Vec Nat — same obstructions as above.
example : subCheck 1000 testVec2 (och{ Vec Nat_ }) = .ok true := by sorry

-- ── Positive computation: unpack to get length ───────────────

-- TODO[mega-loop]: unpack vec1 → length = done_.
-- The obstruction is normalization of the motive `λn:dNat. λarr:(Array_ n Nat_). n`
-- under the binder: evaluating `Array_ n Nat_` with abstract `n` unfolds the
-- outer fix of Array_ but then needs DNat's eliminator on the bvar `n`, which
-- is stuck. Under Church-Nat this worked because Church-Nat's stuck eliminator
-- was silently admitted; under DNat the normalization has to actually
-- terminate cleanly.
example : absEvalVal (och{ testVec1 Nat_ (λn:dNat. λarr:(Array_ n Nat_). n) }) = .ok ⟨done_⟩ := by sorry

-- TODO[mega-loop]: unpack vec2 → length = dtwo. Same obstruction.
example : absEvalVal (och{ testVec2 Nat_ (λn:dNat. λarr:(Array_ n Nat_). n) }) = .ok ⟨dtwo⟩ := by sorry

-- ── Negative subtype checks ─────────────────────────────────

-- TODO[mega-loop]: Vec Nat ⊄ Nat. Normalizing `Vec Nat_` requires evaluating
-- `λn:dNat. Array_ n Nat_` under the binder (stuck DNat elim on abstract n).
example : subCheck 1000 (och{ Vec Nat_ }) Nat_ = .ok false := by sorry

-- TODO[mega-loop]: A Nat is not a Vec Nat. Same obstruction (RHS fails to normalize).
example : subCheck 1000 zero_ (och{ Vec Nat_ }) = .ok false := by sorry

-- ── Negative computation ─────────────────────────────────────

-- TODO[mega-loop]: unpack vec1 → length ≠ dtwo. Same absEval obstruction.
example : absEvalVal (och{ testVec1 Nat_ (λn:dNat. λarr:(Array_ n Nat_). n) }) ≠ .ok ⟨dtwo⟩ := by sorry

-- TODO[mega-loop]: unpack vec2 → length ≠ done_. Same absEval obstruction.
example : absEvalVal (och{ testVec2 Nat_ (λn:dNat. λarr:(Array_ n Nat_). n) }) ≠ .ok ⟨done_⟩ := by sorry

end Tests

-- ============================================================
-- appendVec — the north star
-- ============================================================

/-!
## appendVec

The north star for Och: `appendVec` with abstract arguments where the
type system tracks dependent lengths and catches mistakes like
`dadd n1 n1` (should be `dadd n1 n2`).

`appendVec` unpacks both vectors, calls `appendArrays`, and repacks.
-/

def appendVec := och{
  λT:Type. λv1:(Vec T). λv2:(Vec T).
    v1 (Vec T) (λn1:dNat. λarr1:(Array_ n1 T).
      v2 (Vec T) (λn2:dNat. λarr2:(Array_ n2 T).
        mkVec T (dadd n1 n2) (appendArrays T n1 n2 arr1 arr2)))
}

-- appendVec with a deliberate bug: dadd n1 n1 instead of dadd n1 n2
private def appendVec_wrong := och{
  λT:Type. λv1:(Vec T). λv2:(Vec T).
    v1 (Vec T) (λn1:dNat. λarr1:(Array_ n1 T).
      v2 (Vec T) (λn2:dNat. λarr2:(Array_ n2 T).
        mkVec T (dadd n1 n1) (appendArrays T n1 n1 arr1 arr2)))
}

section AppendVecTests

-- ── North star: abstract appendVec ──────────────────────────

-- TODO[mega-loop]: appendVec : Vec T → Vec T → Vec T
-- The whole chain of dependent refinements must work: Array_ over DNat
-- reducing in the succ branch, dNat constructor subtyping (done_ ⊑ dNat,
-- etc.), and the fix-recursive appendArrays type-checking.
example : subCheck 5000 appendVec (och{ λT:Type. Vec T → Vec T → Vec T })
  = .ok true := by sorry

-- TODO[mega-loop]: appendVec_wrong should NOT typecheck (dadd n1 n1 ≠ dadd n1 n2
-- under abstract reasoning). This is the negative pair of the above: once the
-- positive test passes, this one must genuinely reject.
example : subCheck 5000 appendVec_wrong (och{ λT:Type. Vec T → Vec T → Vec T })
  ≠ .ok true := by sorry

-- ── Concrete appendVec ──────────────────────────────────────

private def vec1 := och{ mkVec Nat_ dtwo (Pair one_ (Pair two_ unit_)) }
private def vec2 := och{ mkVec Nat_ done_ (Pair three_ unit_) }
private def vecResult := och{ appendVec Nat_ vec1 vec2 }

-- TODO[mega-loop]: Concrete result ⊑ Vec Nat — needs the same cascade
-- of refinements as the abstract appendVec test above.
example : subCheck 5000 vecResult (och{ Vec Nat_ })
  = .ok true := by sorry

-- TODO[mega-loop]: Concrete result: unpack and check length is nonzero.
-- Relies on concEval being able to walk through the appendVec body —
-- which internally references appendArrays (a fix) and mkVec (which
-- takes abstract-looking arguments). Was previously live under Church-Nat;
-- under DNat it may or may not still walk through cleanly.
example : concEval 10000 (och{
    disZero (vecResult Nat_ (λn:dNat. λarr:(Array_ n Nat_). n))
  }) = some Std.false_ := by sorry

end AppendVecTests
end Std

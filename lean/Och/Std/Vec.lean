import Och.Macro
import Och.Eval
import Och.TyCheck
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
private def testVec1 := och{ mkVec Nat_ done_ (pair_ Nat_ Unit_ zero_ unit_) }

-- mkVec Nat 2 [1, 2]
private def testVec2 := och{ mkVec Nat_ dtwo
  (pair_ Nat_ (Pair Nat_ Unit_) one_ (pair_ Nat_ Unit_ two_ unit_)) }

-- ── Positive subtype checks ──────────────────────────────────

-- mkVec Nat 1 [0] ⊑ Vec Nat. Array_ done_ Nat reduces to Pair Nat Unit
-- now that absEval β-reduces unconditionally and the closed-head muSeen
-- `==` catches the dsucc self-reference; the stuck-recursive-head
-- re-eval rule in subCheckNF then equates the muSeen-cut form with the
-- evaluated ι form so the existential pack typechecks.
example : subCheck 1000 testVec1 (och{ Vec Nat_ }) = .ok true := by native_decide

-- mkVec Nat 2 [1,2] ⊑ Vec Nat — same mechanism as testVec1. Array_ dtwo Nat
-- reduces to Pair Nat (Pair Nat Unit), then testVec2's sigma lines up
-- with Vec's sigma via the stuck-head re-eval rule.
example : subCheck 1000 testVec2 (och{ Vec Nat_ }) = .ok true := by native_decide

-- ── Positive computation: unpack to get length ───────────────

-- unpack vec1 → length = done_. Stated via concEval rather than
-- absEvalVal: the computational fact "unpacking gives back the
-- length we packed" is a runtime property, and concEval (which
-- erases ascriptions) has no muSeen-path-dependence so both sides
-- normalise to the same term. The previous absEvalVal phrasing
-- was testing absEval's NF canonicity, which is the documented
-- representation problem (PROGRESS.md obstacle 2), not the
-- computational fact this section is about. Bidirectional
-- `subCheck` (semantic equality under absEval) also closes for
-- vec1, but hangs for vec2 at fuel 1000, so concEval is used
-- uniformly.
example : concEval 1000 (och{ testVec1 Nat_ (λn:dNat. λarr:(Array_ n Nat_). n) })
        = concEval 1000 done_ := by native_decide

example : concEval 1000 (och{ testVec2 Nat_ (λn:dNat. λarr:(Array_ n Nat_). n) })
        = concEval 1000 dtwo := by native_decide

-- ── Negative subtype checks ─────────────────────────────────

-- Vec Nat ⊄ Nat. Normalising `Vec Nat_` evaluates `λn:dNat. Array_ n Nat_`
-- under the binder; absEval now leaves `Array_ n` (and the inner DNat
-- eliminator on the bvar `n`) as a stuck application instead of
-- diverging, so the comparison terminates.
example : subCheck 1000 (och{ Vec Nat_ }) Nat_ = .ok false := by native_decide

-- A Nat is not a Vec Nat. Same path.
example : subCheck 1000 zero_ (och{ Vec Nat_ }) = .ok false := by native_decide

-- ── Negative computation ─────────────────────────────────────

-- unpack vec1 → length ≠ dtwo.
example : absEvalVal (och{ testVec1 Nat_ (λn:dNat. λarr:(Array_ n Nat_). n) }) ≠ .ok ⟨dtwo⟩ := by
  native_decide

-- unpack vec2 → length ≠ done_. Same mechanism as unpack vec1 ≠ dtwo.
example : absEvalVal (och{ testVec2 Nat_ (λn:dNat. λarr:(Array_ n Nat_). n) }) ≠ .ok ⟨done_⟩ := by native_decide

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

-- appendVec : Vec T → Vec T → Vec T. The full chain works:
-- Array_ over DNat reduces (neutral-head gate leaves `Array_ n` stuck
-- on the abstract `n`), the recursive appendArrays type-checks via
-- the stuck-head re-eval rule, and the existential pack closes.
example : subCheck 5000 appendVec (och{ λT:Type. Vec T → Vec T → Vec T })
  = .ok true := by native_decide

-- appendVec_wrong should NOT typecheck (the inner `appendArrays
-- T n1 n1 arr1 arr2` passes `arr2 : Array_ n2 T` where the 5th
-- parameter — after substituting `n1` for the 3rd — expects
-- `Array_ n1 T`). Neither `subCheckNF` nor `NbE.subCheck` can
-- catch this: both normalise first (β is type-blind) and then
-- compare normal forms, by which point the ill-typed inner
-- application has already β'd through. The bidirectional
-- `NbE.typeCheck` walks the *syntactic* term and runs the domain
-- check at each application, so it sees the bad argument before
-- β erases it. Paired with the positive check below so the pass
-- isn't simply over-rejecting.
example : (NbE.typeCheck 5000 appendVec_wrong
            (och{ λT:Type. Vec T → Vec T → Vec T })).isOk
  = false := by native_decide
example : NbE.typeCheck 5000 appendVec
            (och{ λT:Type. Vec T → Vec T → Vec T })
  = .ok true := by native_decide

-- ── Concrete appendVec ──────────────────────────────────────

private def vec1 := och{ mkVec Nat_ dtwo
  (pair_ Nat_ (Pair Nat_ Unit_) one_ (pair_ Nat_ Unit_ two_ unit_)) }
private def vec2 := och{ mkVec Nat_ done_ (pair_ Nat_ Unit_ three_ unit_) }
private def vecResult := och{ appendVec Nat_ vec1 vec2 }

-- Concrete result ⊑ Vec Nat. subCheckNF fans out here for the
-- same reason as `dtwo/dthree ⊑ dNat` (the result has length
-- dthree). NbE.subCheck handles it at fuel 400.
example : NbE.subCheck 400 vecResult (och{ Vec Nat_ })
  = .ok true := by native_decide

-- Concrete result: unpack and check length is nonzero. concEval walks
-- through appendVec, appendArrays (a fix), mkVec, dadd, and disZero
-- to compute the actual length (dthree), then disZero dthree → false_.
example : concEval 10000 (och{
    disZero (vecResult Nat_ (λn:dNat. λarr:(Array_ n Nat_). n))
  }) = some Std.false_ := by native_decide

end AppendVecTests
end Std

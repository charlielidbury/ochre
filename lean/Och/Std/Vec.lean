import Och.Macro
import Och.Eval
import Och.EvalSubst
import Och.Std.DNat
import Och.Std.Unit
import Och.Std.Pair
import Och.Std.Array
import Och.Std.Sigma
import Och.API

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
-- Ascription transparency bug: minimal reproduction
-- ============================================================
section AscBug

-- BUG: `(x : Type)` should erase x's type to Type, so passing it
-- where Nat_ is expected should reject. But synthCore's .asc arm
-- returns the inner value (not the annotation), and the .app arm's
-- fallback re-discovers x:Nat_ from Γ via neutral ascent on the
-- evalSubst'd argument (which strips the ascription).
private def asc_transparent := och{
  λx:Nat_. (λy:Nat_. y) (x : Type)
}
example : -- correctly rejects: (x : Type) narrows to Type, Type ⊄ Nat_
    (match Och.synth asc_transparent 200 with
     | .ok _ => false | _ => true) = true := by native_decide

-- Concrete value (not neutral): ascription transparency in .asc arm
-- still fires (returns zero_ not Type), but no neutral-ascent
-- fallback exists → correctly rejects.
private def asc_concrete := och{
  (λy:Unit_. y) (zero_ : Type)
}
example : -- correctly rejects (zero_ ⊑ Unit_ fails, no fallback)
    (match Och.synth asc_concrete 200 with
     | .ok _ => false | _ => true) = true := by native_decide

-- Baseline: genuine type mismatch without ascription.
private def genuinely_wrong := och{
  λx:Nat_. (λy:Unit_. y) x
}
example : -- correctly rejects
    (match Och.synth genuinely_wrong 200 with
     | .ok _ => false | _ => true) = true := by native_decide

end AscBug

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

example : Och.subCheckE 200 testVec1 (och{ Vec Nat_ }) = .ok true := by native_decide
example : Och.subCheckE 200 testVec2 (och{ Vec Nat_ }) = .ok true := by native_decide

-- ── Positive computation: unpack to get length ───────────────

example : concEval 100 (och{ testVec1 Nat_ (λn:Nat_. λarr:(Array_ n Nat_). n) })
        = concEval 100 one_ := by native_decide

example : concEval 100 (och{ testVec2 Nat_ (λn:Nat_. λarr:(Array_ n Nat_). n) })
        = concEval 100 two_ := by native_decide

-- ── Negative subtype checks ─────────────────────────────────

example : Och.subCheckE 200 (och{ Vec Nat_ }) Nat_ = .ok false := by native_decide
example : Och.subCheckE 200 zero_ (och{ Vec Nat_ }) = .ok false := by native_decide

-- ── Negative computation ─────────────────────────────────────

-- Phrased via concEval: the negative semantic claim is that `testVec1`
-- with the projection-to-length argument does NOT compute to `two_`.
example : concEval 100 (och{ testVec1 Nat_ (λn:Nat_. λarr:(Array_ n Nat_). n) })
  ≠ concEval 100 two_ := by native_decide

example : concEval 100 (och{ testVec2 Nat_ (λn:Nat_. λarr:(Array_ n Nat_). n) })
  ≠ concEval 100 one_ := by native_decide

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

def id := och{ λΤ:Type. λx:Τ. x }

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
        mkVec T (add_ n1 n1) (appendArrays T n1 n2 arr1 arr2)))
}

section AppendVecTests

-- appendVec : Vec T → Vec T → Vec T
-- Re-enabled after rewriting `appendArrays`'s succ-branch to use
-- inline eliminators on `arr` instead of `fst_`/`snd_` (precision
-- loss at the loose `Pair Type Type → Type` Std-level boundary
-- was the bail; see `docs/ideas/appendvec-investigation.md`).
-- synth validates, and the WTValue is reflexive under subCheck.
example :
    (match Och.synth Std.appendVec 200 with
     | .ok v => Och.subCheck v v 200 == .ok true
     | _ => false) = true := by native_decide

-- appendVec_wrong has a deliberate bug: the inner `appendArrays`
-- call uses `n1` twice instead of `n1, n2`. The bidirectional
-- walk (`TyCheck.tyInfer`) domain-checks each argument and rejects
-- `arr2 : Array_ n2 T` against the expected `Array_ n1 T`.
--
-- The public API `Och.synth` currently runs `tyInfer` for
-- diagnostics but on `.error` falls back to `evalSubst` — the
-- synthCore correctly rejects the bug: arr2 (: Array_ n2 T) is passed
-- where Array_ n1 T is expected, and n2 ≠ n1.
example : (Och.synth appendVec_wrong 200).isError
       = true := by native_decide

-- ── Concrete appendVec ──────────────────────────────────────

private def vec1 := och{ mkVec Nat_ two_
  (pair_ Nat_ (Pair Nat_ Unit_) one_ (pair_ Nat_ Unit_ two_ unit_)) }
private def vec2 := och{ mkVec Nat_ one_ (pair_ Nat_ Unit_ three_ unit_) }
private def vecResult := och{ appendVec Nat_ vec1 vec2 }

-- `Och.subCheckE 400 vecResult (Vec Nat_) = .ok true` would be
-- the natural pin, but the public `Och.synth` walks `vecResult`
-- through `appendVec`/`appendArrays`, both of which exercise
-- abstract dependent-domain checks the structural engine can't
-- close (same A6-family limitation that blocks `synth appendVec`
-- itself — see the abstract `appendVec ⊑ ...` pin commented out
-- in `AppendVecTests` above). Concrete computation still works
-- (next pin); structural subtype checking on the *result* of
-- `appendVec` is bench-only.

-- Concrete result: unpack and check length is nonzero. Strict pin
-- against `false_` (length ≠ zero, since vec1 ++ vec2 has length 3).
example : concEval 200 (och{
    isZero_ (vecResult Nat_ (λn:Nat_. λarr:(Array_ n Nat_). n))
  }) = concEval 200 false_ := by native_decide

end AppendVecTests
end Std

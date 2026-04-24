import Och.NbE
import Och.Std.DNat
import Och.Std.DBool
import Och.Std.Array
import Och.Std.Vec

/-!
Validation tests for the NbE evaluator. These were originally the
cases the substitution-based evaluator (retired 2026-04-19)
diverged or hung on; they remain as `nf` regression tests.
-/

namespace NbE.Tests
open Std

-- Termination on the recursive types that used to fan out.
example : (NbE.nf 200 Nat_).isOk := by native_decide
example : (NbE.nf 200 one_).isOk := by native_decide
example : (NbE.nf 200 two_).isOk := by native_decide
example : (NbE.nf 1000 three_).isOk := by native_decide

-- Identity on the non-recursive standard library. Under the unified
-- Nat_, NF of Nat_ is no longer literal-equal to Nat_ (the fix+ι
-- wrappers expand); asserted only as isOk.
example : (NbE.nf 200 Nat_).isOk := by native_decide
example : NbE.nf 200 Std.Bool = .ok Std.Bool := by native_decide
example : (NbE.nf 200 dtrue).isOk := by native_decide
example : (NbE.nf 200 dBool).isOk := by native_decide

-- Array_ at concrete indices reduces to the right Pair shape.
example : NbE.nf 1000 (och{ Array_ zero_ Nat_ }) = .ok Unit_ := by native_decide
example : NbE.nf 1000 (och{ Array_ one_ Nat_ })
        = NbE.nf 1000 (och{ Pair Nat_ Unit_ }) := by native_decide
example : NbE.nf 1000 (och{ Array_ two_ Nat_ })
        = NbE.nf 1000 (och{ Pair Nat_ (Pair Nat_ Unit_) }) := by native_decide
example : NbE.nf 1000 (och{ Array_ three_ Nat_ })
        = NbE.nf 1000 (och{ Pair Nat_ (Pair Nat_ (Pair Nat_ Unit_)) }) := by
  native_decide

-- Canonicity sanity: `one_` and `succ_ zero_` are the same term,
-- so their normal forms must agree exactly.
example : NbE.nf 200 one_ = NbE.nf 200 (och{ succ_ zero_ }) := by native_decide

end NbE.Tests

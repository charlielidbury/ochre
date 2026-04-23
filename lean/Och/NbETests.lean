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
example : (NbE.nf 200 dNat).isOk := by native_decide
example : (NbE.nf 200 done_).isOk := by native_decide
example : (NbE.nf 200 dtwo).isOk := by native_decide
example : (NbE.nf 1000 dthree).isOk := by native_decide

-- Identity on the non-recursive standard library.
example : NbE.nf 200 Nat_ = .ok Nat_ := by native_decide
example : NbE.nf 200 Std.Bool = .ok Std.Bool := by native_decide
example : (NbE.nf 200 dtrue).isOk := by native_decide
example : (NbE.nf 200 dBool).isOk := by native_decide

-- Array_ at concrete indices reduces to the right Pair shape.
example : NbE.nf 1000 (och{ Array_ dzero Nat_ }) = .ok Unit_ := by native_decide
example : NbE.nf 1000 (och{ Array_ done_ Nat_ })
        = NbE.nf 1000 (och{ Pair Nat_ Unit_ }) := by native_decide
example : NbE.nf 1000 (och{ Array_ dtwo Nat_ })
        = NbE.nf 1000 (och{ Pair Nat_ (Pair Nat_ Unit_) }) := by native_decide
example : NbE.nf 1000 (och{ Array_ dthree Nat_ })
        = NbE.nf 1000 (och{ Pair Nat_ (Pair Nat_ (Pair Nat_ Unit_)) }) := by
  native_decide

-- Canonicity sanity: `done_` and `dsucc dzero` are the same term,
-- so their normal forms must agree exactly.
example : NbE.nf 200 done_ = NbE.nf 200 (och{ dsucc dzero }) := by native_decide

end NbE.Tests

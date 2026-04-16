import Och.NbE
import Och.Std.DNat
import Och.Std.DBool
import Och.Std.Array
import Och.Std.Vec

/-!
Validation tests for the NbE evaluator. These are the cases where
`absEval` either diverges (without the muSeen cutoff), produces
non-canonical normal forms (with it), or hangs at high fuel; NbE
handles them cleanly because substitution is environment extension,
not term copying.
-/

namespace NbE.Tests
open Std

-- Termination on the recursive types that fan out under absEval.
example : (NbE.nf 200 dNat).isSome := by native_decide
example : (NbE.nf 200 done_).isSome := by native_decide
example : (NbE.nf 200 dtwo).isSome := by native_decide
example : (NbE.nf 1000 dthree).isSome := by native_decide

-- Agreement with absEval on the non-recursive standard library.
example : NbE.nf 200 Nat_ = some Nat_ := by native_decide
example : NbE.nf 200 Std.Bool = some Std.Bool := by native_decide
example : (NbE.nf 200 dtrue).isSome := by native_decide
example : (NbE.nf 200 dBool).isSome := by native_decide

-- Array_ at concrete indices reduces to the right Pair shape.
-- Under absEval, `Array_ dthree Nat_` hangs; here it computes.
example : NbE.nf 1000 (och{ Array_ dzero Nat_ }) = some Unit_ := by native_decide
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

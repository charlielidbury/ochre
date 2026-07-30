import Dllbc.Boundary
import Dllbc.Macro
import Dllbc.Std
import Dllbc.PureMacro
import Dllbc.DeclMacro
import Dllbc.StdLemmas
import Dllbc.Tests.S9Diff

/-!
# §25 test suite — the in-place array partition, and the array quicksort

¶6's migration completed: the leaf program ledger G4 says does not transfer, and the
assembly it feeds. `S24Arrays` established that every PIECE works (the carve, the
elementization, the transferred library, `sort2` as the whole stack at width two);
this file is the two programs those pieces were for.
-/

open Dllbc
open Dllbc.StdLemmas (le_refl le_add le_add_l le_add_succ le_trans le_up_r le_pred_l
  leb_true_le leb_false_gt add_succ add_zero id_trans id_congr id_sym znots
  SortedA UbA LbA countA asingle sorted_arrCat count_arrCat ub_permA lb_permA
  nat_rw nat_rw_ty le_zero_eq le_zero_eq_ty sortedA_nil sortedA_nil_ty
  SplitA PartA splitA_nil splitA_nil_ty
  splitA0_lb splitA0_lb_ty splitA_cat_e1 splitA_cat_e1_ty
  splitA_cat_i0 splitA_cat_i0_ty partA_cat_i0 partA_cat_i0_ty
  partA_cat_e0 partA_cat_e0_ty
  bumpN count_acons_congr count_acons_congr_ty bump_comm bump_comm_ty
  count_swapA count_swapA_ty)

namespace Dllbc.Tests.S25ArrSort

/-- Type-check a closed term against a closed type in the pure seed (as §23/§24). -/
def chkL (tm ty : Term) : Bool :=
  match (do let v ← readC 8000 tm; let t ← readC 8000 ty; hasType 8000 v t).run (seedPure [] []) with
  | .ok r _ => r
  | .error _ _ => false

def pv (t : Term) : Val := Val.nfV 4000 (Val.Term.toValPure t)

/-! ## (i) The partition layer's predicates and their nil lemmas -/

example : chkL nat_rw nat_rw_ty = true := by native_decide
example : chkL le_zero_eq le_zero_eq_ty = true := by native_decide
example : chkL sortedA_nil sortedA_nil_ty = true := by native_decide
example : chkL splitA_nil splitA_nil_ty = true := by native_decide

-- The predicates COMPUTE on a run, at every skip count.
-- `SplitA 3 2 [1,2,7]`: first two ≤ 3, last ≥ 3.
example : chkL pure{ Pair(unit, Pair(unit, Pair(unit, unit))) }
               pure{ SplitA 3 2 3 Arr(1, 2, 7) } = true := by native_decide
-- …and it is NOT vacuous: the same array does not split at 1 (element 1 is `2 ≥ 3`? no).
example : chkL pure{ Pair(unit, Pair(unit, Pair(unit, unit))) }
               pure{ SplitA 3 1 3 Arr(1, 2, 7) } = false := by native_decide

-- `PartA 3 2 [1,2,3,7]`: first two ≤ 3, element 2 IS 3, the rest ≥ 3.
example : chkL pure{ Pair(unit, Pair(unit, Pair(Refl, Pair(unit, unit)))) }
               pure{ PartA 3 2 4 Arr(1, 2, 3, 7) } = true := by native_decide
-- The pivot-identity conjunct is load-bearing: element 2 is 4, not 3.
example : chkL pure{ Pair(unit, Pair(unit, Pair(Refl, Pair(unit, unit)))) }
               pure{ PartA 3 2 4 Arr(1, 2, 4, 7) } = false := by native_decide

/-! ### Crossing a concatenation — each an induction on the left array alone -/

example : chkL splitA0_lb splitA0_lb_ty = true := by native_decide
example : chkL splitA_cat_e1 splitA_cat_e1_ty = true := by native_decide
example : chkL splitA_cat_i0 splitA_cat_i0_ty = true := by native_decide
example : chkL partA_cat_i0 partA_cat_i0_ty = true := by native_decide
example : chkL partA_cat_e0 partA_cat_e0_ty = true := by native_decide

/-! ### The count layer for the swap -/

example : chkL count_acons_congr count_acons_congr_ty = true := by native_decide
example : chkL bump_comm bump_comm_ty = true := by native_decide
example : chkL count_swapA count_swapA_ty = true := by native_decide

-- There IS no η at length zero, which is why the nil lemmas exist at all: `SortedA Z`
-- of an opaque payload is a stuck `arrRec`, not `Unit`.
example : (Val.nfV 2000 (Val.Term.toValPure pure{ SortedA Z Arr() }) == .const "Unit")
    = true := by native_decide

end Dllbc.Tests.S25ArrSort

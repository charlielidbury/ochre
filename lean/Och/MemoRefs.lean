import Och.NbE
import Lean.Util.ShareCommon

/-!
# Persistent sharing-state ref for `Closure.open`

A global `ShareCommon.State` maintained across `subCheckVal`
calls. Evaluation results are piped through `State.shareCommon`
so structurally-equal `Val` trees become pointer-equal across
independent recursion paths. Downstream `Val.beqFast` / `ptrEq`
guards then short-circuit on the ptrEq fast-path, restoring the
O(1)-per-guard behavior the checker relied on before Option A.

This file only declares the `initialize`'d `IO.Ref`. The
`@[implemented_by]` wiring lives in `SubCheckVal.lean` (which
defines `Closure.open`), because Lean refuses to evaluate
`[init]` declarations from the same module where `native_decide`
runs.
-/

namespace NbE

/-- Global `ShareCommon.State` ref. Accumulates structural
dedup entries across the whole test suite run; memory is
bounded by the number of distinct `Val` subtrees encountered
(small for Och tests). -/
initialize shareState :
    IO.Ref (ShareCommon.State Lean.ShareCommon.objectFactory) ←
  IO.mkRef (ShareCommon.State.mk _)

end NbE

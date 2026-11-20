import Ochr.Meaning.Strict.Call
import Ochr.Meaning.Strict.Ops

/-!
# A call keeps the invariant (`callOfS`)

The consumed borrow arguments' holders read `⊥`; every position reads its old meaning at the future
with the consumed labels fixed to the callee's final contents, which are members of the parameters'
content types (`ApplyMem.app_mem_finals`), so of the labels' (`BorrowArgsTyped`): a typed future of
the state before. At a returned borrow `k` (fresh), a typed future gives `k` a partly moved member;
where it decodes, the finals are the backward function's (members); where it does not, `callOfLS`
fixes them to `⊥`, a partly moved member of anything.
-/

namespace Ochr.Meaning.Strict
open Ochr.Meaning

/-- **A call keeps the invariant**, and its result's label (a returned borrow's, fresh) records the
result's type. -/
theorem callOfS_sgood {K : RunCtx} {φ : Future} (hMR : MemReads K.dm K.Γ) {fv : Res} {as : List Res}
    {s s' : SState} {r : Res} (hs : SGood K.dm K.Γ φ s) (hf : GoodRes K.dm.read fv)
    (ht : BorrowArgsTyped K.dm.read fv as s) (h : callOfS K.dm.read fv as s = some (r, s')) :
    LabOk K.dm s' r ∧ SGood K.dm K.Γ φ s' := by
  sorry

end Ochr.Meaning.Strict

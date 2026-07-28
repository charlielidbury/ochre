import Dllbc.Tests.SDeclUnified
import Dllbc.Tests.S19Partition

/-!
# The unified-grammar stretch, checked against the REAL S19 corpus

`SDeclUnified.lean` develops the splice-free `partScanEU` / `pivotPlaceHU` against
verbatim transcriptions of the S19 corpus (S19-free, so it builds in seconds).
This file closes the loop: it imports `S19Partition` and asserts the surface Decls
are `alphaEq` (partScanE) / exactly equal (pivotPlaceH) to the ACTUAL corpus
`partScanE` / `pivotPlaceH` — confirming the transcriptions are faithful.

It is the ONLY unified-grammar file importing S19, so it is gated to the final
full build (the ~39-minute S19 re-elaboration this worktree's stale `.lake` trace
forces). The alphaEq assertions themselves are cheap — alphaNorm is a linear
traversal and the compare is structural BEq; no checker runs.
-/

open Dllbc

namespace Dllbc.Tests.SDeclUnifiedS19

-- partScanE: hand ids diverge from pre-order, so alphaEq (not exact).
example : Decl.alphaEq Dllbc.Tests.SDeclUnified.partScanEU Dllbc.Tests.S19Partition.partScanE = true := by
  native_decide

-- pivotPlaceH: ids coincide with pre-order, so exact equality of body/telescope/back.
example : (Dllbc.Tests.SDeclUnified.pivotPlaceHU.body == Dllbc.Tests.S19Partition.pivotPlaceH.body) = true := by
  native_decide
example : (Dllbc.Tests.SDeclUnified.pivotPlaceHU.telescope == Dllbc.Tests.S19Partition.pivotPlaceH.telescope) = true := by
  native_decide
example : (Dllbc.Tests.SDeclUnified.pivotPlaceHU.back == Dllbc.Tests.S19Partition.pivotPlaceH.back) = true := by
  native_decide
example : Decl.alphaEq Dllbc.Tests.SDeclUnified.pivotPlaceHU Dllbc.Tests.S19Partition.pivotPlaceH = true := by
  native_decide

end Dllbc.Tests.SDeclUnifiedS19

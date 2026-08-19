import Dllbc.Syntax
import Dllbc.Value
import Dllbc.Pure
import Dllbc.Machine
import Dllbc.Boundary
import Dllbc.Std
import Dllbc.Uni
import Dllbc.ProgMacro
import Dllbc.StdLemmas
import Dllbc.Program
import Dllbc.ElabCheck
import Dllbc.Tests.KernelFloor
import Dllbc.Tests.Traces
import Dllbc.Tests.Diff
import Dllbc.Tests.Boundaries
import Dllbc.Tests.Arrays
import Dllbc.Tests.Direct
import Dllbc.Tests.ArraySort
import Dllbc.Tests.Functions
import Dllbc.Tests.Programs
import Dllbc.Tests.AuditExemption
import Dllbc.Tests.AuditFold
import Dllbc.Tests.SigmaCopy
import Dllbc.Tests.EagerRec
import Dllbc.Tests.Ledger
import Dllbc.Tests.Sugar
import Dllbc.Tests.OpaqueFill
import Dllbc.Tests.Universe
import Dllbc.Tests.BorrowRefoundGoals
import Dllbc.Tests.SetHmProbe
import Dllbc.Tests.ArrCatIota
import Dllbc.Tests.HashMap
import Dllbc.Tests.HashMapDiff
import Dllbc.Tests.HashMapPin
import Dllbc.Tests.ElabSpans

/-! `Dllbc.Tests.FragmentAgreement` is DELIBERATELY ABSENT from this list, and is
    a REQUIRED merge check rather than a build one — `lake build
    Dllbc.Tests.FragmentAgreement`. It sweeps the reflector over all 1096 `prog{ }`
    blocks in the corpus and costs +65 s on a from-scratch suite (314 s → 379 s,
    +21%). What it guards is drift between `Term.needsRuntime` and `readC`'s
    refusal list, and that list changes when someone deliberately edits the
    fragment boundary — a once-a-milestone event, not a once-an-edit one. Paying
    21% on every build to watch for it puts the cost on the wrong side of the
    frequency. The enforcement point is the merge check; see docs/05 §7. -/

import Ochr.Examples.Registry
import Ochr.Examples.Ledger
import Ochr.Examples.Editor
import Ochr.Examples.«19Uninit»

/-! # The examples: every example file (through the registry) and the asserted ledger

The root of the `OchrExamples` library, which `lake build` builds; with it, the tests of
located errors (`Editor.lean`), and `19Uninit.lean`, a feasibility prototype checked under
switches that are off by default (docs/10, branch uninit-bot; not in the registry). -/

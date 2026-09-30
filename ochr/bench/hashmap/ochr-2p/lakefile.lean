import Lake
open Lake DSL

package «hashmap-ochr-2p» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

-- The Ochr checker, with the examples tour and the arrays library (in the sandbox).
require ochr from "checker"

-- Your solution: the `ochr` blocks of HashMap.lean.
@[default_target]
lean_lib HashMap

-- `lake exe check`: the checker's verdict on every declaration (see Check.lean).
@[default_target]
lean_exe check where
  root := `Check
  supportInterpreter := true

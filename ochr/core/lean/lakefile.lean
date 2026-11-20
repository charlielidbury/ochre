import Lake
open Lake DSL

package «ochr» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

-- The checker: every `Ochr.*` module but the examples. Precompiled to native code, which the
-- elaborator loads, so the `ochr` command checks each block natively when it is elaborated
-- (docs/07).
@[default_target]
lean_lib «Ochr» where
  srcDir := "."
  precompileModules := true

-- The example programs (`Ochr.Examples.*`, declared after `Ochr` so that this library owns
-- them): not precompiled, since they are checked, not run. Its one root, `Ochr/Examples.lean`,
-- imports the registry and the asserted ledger, and with them every example file (not
-- `CaseStudyLedger.lean`, which is run by hand).
@[default_target]
lean_lib OchrExamples where
  srcDir := "."
  roots := #[`Ochr.Examples]

-- `lake exe tests` runs every example program through the checker and prints
-- the verdict table; it exits non-zero if any verdict is not the expected one.
lean_exe tests where
  root := `Tests

-- `lake exe sweep`: DEV TOOLING, not part of the checker or the artefact. Records the checker's
-- states (`Config.recordStates`) over every example and case study and evaluates Bool mirrors of
-- the meaning spine's syntactic `Good` clauses on each (`Sweep.lean`).
lean_exe sweep where
  root := `Sweep

-- The sweep's adversarial programs (`SweepProbes.lean`, `lake exe sweep --probes`): dev tooling,
-- not a default target, and not counted with the suite's verdicts.
lean_lib SweepProbes where
  srcDir := "."
  roots := #[`SweepProbes]

-- `lake exe fuzz`: the differential naturality fuzzer (Ochr/Fuzz/, notes/fuzzer.md).
lean_exe fuzz where
  root := `Fuzz

-- `lake exe heapslice`: the heap-based slice evaluator (`Ochr/Heap/Slice.lean`, not part of the
-- checker) against the real machine, on the suite's data functions (notes/stability.md §8).
lean_exe heapslice where
  root := `HeapSlice

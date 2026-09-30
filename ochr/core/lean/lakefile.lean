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

-- `lake exe fuzz`: the differential naturality fuzzer (Ochr/Fuzz/, notes/fuzzer.md).
lean_exe fuzz where
  root := `Fuzz

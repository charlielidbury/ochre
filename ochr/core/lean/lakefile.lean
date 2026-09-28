import Lake
open Lake DSL

package «ochr» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

@[default_target]
lean_lib «Ochr» where
  srcDir := "."

-- `lake exe tests` runs every example program through the checker and prints
-- the verdict table; it exits non-zero if any verdict is not the expected one.
lean_exe tests where
  root := `Tests

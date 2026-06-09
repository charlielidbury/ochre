import Lake
open Lake DSL

package «pss» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

@[default_target]
lean_lib «Pss» where
  srcDir := "."
  globs := #[.andSubmodules `Pss]

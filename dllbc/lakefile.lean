import Lake
open Lake DSL

package «dllbc» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

@[default_target]
lean_lib «Dllbc» where
  srcDir := "."

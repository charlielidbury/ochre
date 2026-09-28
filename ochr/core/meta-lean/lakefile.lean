import Lake
open Lake DSL

package «OchrMeta» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

@[default_target]
lean_lib «OchrMeta» where
  srcDir := "."

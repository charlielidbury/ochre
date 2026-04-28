import Lake
open Lake DSL

package «pss» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`pp.unicode.fun, true⟩
  ]
  moreServerOptions := #[⟨`linter.unusedVariables, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.16.0"

@[default_target]
lean_lib «Pss» where
  srcDir := "."
  globs := #[.andSubmodules `Pss]

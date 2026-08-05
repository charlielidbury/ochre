import Lake
open Lake DSL

package «dllbc» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

@[default_target]
lean_lib «Dllbc» where
  srcDir := "."
  -- Native-compile the library so the INTERPRETER (every `#eval checkFn …` and
  -- `native_decide` in scratch files and the suite) calls compiled code instead
  -- of interpreting IR — the measured ~30x tax on M22-scale checks.
  precompileModules := true

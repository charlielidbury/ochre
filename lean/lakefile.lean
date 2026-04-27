import Lake
open Lake DSL

package «och» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

@[default_target]
lean_lib «Och» where
  srcDir := "."

lean_exe «eval_bench» where
  root := `Och.EvalBench

lean_exe «fastpath_bench» where
  root := `Och.FastPathBench

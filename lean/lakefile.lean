import Lake
open Lake DSL

package «och» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

@[default_target]
lean_lib «Och» where
  srcDir := "."

lean_exe «beq_bench» where
  root := `Och.BeqBench

lean_exe «eval_bench» where
  root := `Och.EvalBench

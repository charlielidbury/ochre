import Ochr.Examples.Registry

/-! `lake exe tests`: every example program's verdict table, then the counterfactual
ledger. Exits 1 if any verdict is not the expected one. -/

open Ochr Ochr.Test Ochr.Registry

/-- The total number of verdict assertions; a truncated example file changes it. -/
def expectedTotal : Nat := 105

#guard ((reports {}).map Report.count).foldl (· + ·) 0 == expectedTotal
#guard (reports {}).all Report.allAsExpected

def main : IO UInt32 := do
  let rs := reports {}
  for r in rs do
    IO.println r.show
    IO.println ""
  let total := (rs.map Report.count).foldl (· + ·) 0
  let passed := (rs.map Report.passed).foldl (· + ·) 0
  IO.println s!"verdicts as expected: {passed}/{total} (expected total {expectedTotal})"
  IO.println ""
  IO.println "counterfactual ledger (one rule switched off → verdicts that flip):"
  for (n, c) in switches do
    let fs := flips c
    IO.println s!"  {n}: {if fs.isEmpty then "nothing" else ", ".intercalate fs}"
  return if passed == total && total == expectedTotal then 0 else 1

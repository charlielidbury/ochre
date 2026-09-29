import Ochr.Examples.Registry

/-! # The counterfactual ledger, for the case studies (not part of `lake build`)

`lake env lean Ochr/Examples/CaseStudyLedger.lean` switches off one rule at a time, as the
ledger does for the tour (`Ledger.lean`), and prints the case-study declarations that flip,
and those blocked because a declaration they use flipped. The rows are too slow to assert in
every build (each re-checks every case-study block twice); the output is recorded in
`notes/hashmap-case-study.md`. -/

open Ochr Ochr.Registry Ochr.Test

def caseStudyFlips : IO Unit := do
  for (n, c) in switches do
    let (fs, bl) := caseStudies.foldl (fun (fs, bl) (name, b) =>
      let (f, g) := blockFlips name b c 300000
      (fs ++ f, bl ++ g)) ([], [])
    IO.println s!"{n}: {fs.length} flips, {bl.length} blocked"
    unless fs.isEmpty do IO.println s!"  flips: {", ".intercalate fs}"

#eval caseStudyFlips

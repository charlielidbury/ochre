import Ochr.Examples.Registry
open Ochr Ochr.Test Ochr.Registry

/-! Every verdict of the suite with its reason, one tab-separated row per declaration
(`Block.Decl`, `def`/`reject`, verdict and message), for before/after comparisons of a change
that should move no verdict (D79, D80). After a green `lake build` and `lake build Ochr:shared`
(the native checker the run loads):
`lake env lean --load-dynlib=.lake/build/lib/libochr_Ochr.so Scratch/VerdictDump.lean > rows.tsv`
(about a minute), then `diff` two dumps. -/

def rowLine (prog : String) (r : Row) : String :=
  let got := match r.verdict with
    | .accepted => "accepted"
    | .rejected m _ => s!"rejected: {m}"
    | .undecided m => s!"undecided: {m}"
  s!"{prog}.{r.name}\t{if r.expectAccept then "def" else "reject"}\t{got}"

def dumpAll : IO Unit := do
  let reps : List Ochr.Test.Report := Ochr.Registry.reports {} 2000000
  for rep in reps do
    for r in rep.rows do
      IO.println (rowLine rep.program r)

#eval dumpAll

import Ochr.Examples.Registry

/-! # Fuel monotonicity: a decided verdict never changes with more fuel

Running out of fuel, or past a depth limit, means the checker does not know: the verdict is
`undecided`, and nothing below the verdict boundary can catch it (`Ochr/Catch.lean`). So with
less fuel a declaration may become undecided, but it is never decided differently: a
declaration accepted at the default fuel is never rejected at a lower one, and one rejected at
the default fuel is never accepted. Before `notes/catch-census.md`, out of fuel was an error
that one-line handlers turned into defaults ("not a proposition", "not convertible", "no
hint") while refunding the fuel spent, so this did not hold by construction.

The test runs every registered program (`Ochr.Registry`) at five lower fuels, and the case
studies at one (sampled: each run re-checks a case study's whole library, about 30 s at fuel
3,000 and 9 s at 300, against about 1 s for all the programs at five), and compares each declaration's verdict with
its verdict at the default fuel. That verdict is its
expectation (`def`: accepted, `reject def`: rejected), which the `ochr` command asserts when
each block is elaborated, so the default run is not repeated here. Each lower fuel must leave
some declarations undecided and decide others, so the comparison is not vacuous. -/

namespace Ochr.FuelMonotone
open Ochr Ochr.Test Ochr.Registry

/-- The fuels below the default (2,000,000 per declaration) the programs are run at. -/
def fuels : List Nat := [30, 100, 300, 1000, 3000]

/-- What a verdict decides: accepted, rejected, or nothing. -/
def decides : Verdict → Option Bool
  | .accepted => some true
  | .rejected .. => some false
  | .undecided _ => none

/-- One block at each of `fuels`: for each, the decided verdicts that differ from the default
fuel's (the expectation, asserted by the `ochr` command), as messages, and how many
declarations were undecided and decided. -/
def checkBlock (fuels : List Nat) (name : String) (b : Surface.Block) : List (Nat × List String × Nat × Nat) :=
  fuels.map fun f =>
    let rows := (run name b {} f).rows
    let bad := rows.filterMap fun r =>
      match decides r.verdict with
      | none => none
      | some l => if l == r.expectAccept then none
        else some s!"{name}.{r.name}: {if l then "accepted" else "rejected"} at fuel {f}, {if r.expectAccept then "accepted" else "rejected"} at the default"
    let und := (rows.filter fun r => (decides r.verdict).isNone).length
    (f, bad, und, rows.length - und)

/-- Every registered block, at every lower fuel. -/
def results : List (String × List (Nat × List String × Nat × Nat)) :=
  programs.map (fun (n, b) => (n, checkBlock fuels n b)) ++
    caseStudies.map (fun (n, b) => (n, checkBlock [300] n b))

/-- The decided verdicts that changed with fuel (none). -/
def violations : List String :=
  results.flatMap fun (_, rs) => rs.flatMap (·.2.1)

/-- For each lower fuel, how many declarations were undecided and how many decided. -/
def counts : List (Nat × Nat × Nat) :=
  fuels.map fun f =>
    let at_ := results.filterMap fun (_, rs) => rs.find? (·.1 == f)
    (f, (at_.map (·.2.2.1)).foldl (· + ·) 0, (at_.map (·.2.2.2)).foldl (· + ·) 0)

-- no decided verdict changed, and (not vacuous) at every lower fuel some declarations are
-- undecided and some are decided
#eval show IO Unit from do
  IO.println s!"fuel monotonicity: (fuel, undecided, decided) = {counts}"
  unless violations.isEmpty do
    throw (IO.userError s!"decided verdicts changed with fuel:\n{"\n".intercalate violations}")
  unless counts.all fun (_, und, dec) => und > 0 && dec > 0 do
    throw (IO.userError s!"vacuous: some lower fuel decided everything or nothing: {counts}")

end Ochr.FuelMonotone

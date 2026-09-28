import Ochr.Notation

/-!
# Running example programs and asserting their verdicts

Each declaration in an `ochr` program carries an expectation (`def`: accepted,
`reject def`: rejected). `run` checks the program and pairs each expectation with
the verdict. Example files assert `(run P).allAsExpected` and the exact number of
assertions with `#guard`, so a green build means every verdict is as expected and
that no assertion silently disappeared (a truncated file would change the count).
-/

namespace Ochr.Test
open Ochr Ochr.Surface

structure Row where
  name : String
  expectAccept : Bool
  verdict : Verdict
  trace : Array String := #[]

def Row.asExpected (r : Row) : Bool := r.expectAccept == r.verdict.ok

structure Report where
  program : String
  rows : List Row

def Report.allAsExpected (r : Report) : Bool := r.rows.all Row.asExpected
def Report.count (r : Report) : Nat := r.rows.length
def Report.passed (r : Report) : Nat := (r.rows.filter Row.asExpected).length

def run (name : String) (p : Program) (cfg : Config := {}) (fuel : Nat := 2000000) : Report := Id.run do
  -- resolve every declaration; a resolution failure is a rejection of that declaration
  let mut defs : List Item := []
  let mut bad : List (String × String) := []
  for d in p do
    match resolveProgram p d with
    | .ok df => defs := defs ++ [df]
    | .error e => bad := bad ++ [(d.name, e)]
  let verdicts := checkDefs cfg defs fuel
  let rows := p.map fun d =>
    let (v, tr) := match bad.lookup d.name with
      | some e => (Verdict.rejected s!"(surface) {e}", #[])
      | none => (verdicts.lookup d.name).getD (.rejected "not checked", #[])
    { name := d.name, expectAccept := d.expectAccept, verdict := v, trace := tr }
  pure { program := name, rows := rows }

def Row.show (r : Row) : String :=
  let exp := if r.expectAccept then "accept" else "reject"
  let got := match r.verdict with
    | .accepted => "accepted"
    | .rejected m => s!"rejected: {m}"
  let mark := if r.asExpected then "ok  " else "FAIL"
  s!"{mark} {r.name} (expect {exp}) {got}"

def Report.showTrace (r : Report) (name : String) : String :=
  match r.rows.find? (·.name == name) with
  | some row => "\n".intercalate row.trace.toList
  | none => s!"no declaration {name}"

def Report.show (r : Report) : String :=
  s!"== {r.program}: {r.passed}/{r.count} as expected\n" ++
    "\n".intercalate (r.rows.map Row.show)

end Ochr.Test

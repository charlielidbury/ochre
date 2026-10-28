import Ochr.Prelude
import Ochr.Run

/-!
# Running example programs and asserting their verdicts

Each declaration in an `ochr` program carries an expectation (`def`: accepted,
`reject def`: rejected). `run` checks the block (after the declarations the blocks it
`uses` export) and pairs each of its own declarations' expectations with its verdict. The
`ochr` command checks every block this way when it is elaborated (`Ochr.Notation.checkBlock`),
so a green build means every verdict is as expected; `run` is for programmatic runs (the
test runner, the fuzzer, traces).
-/

namespace Ochr.Test
open Ochr Ochr.Surface

/-- What a block exports under `cfg` (`exportsWith`, the library block `Prelude`). -/
def exportsOf (cfg : Config) (fuel : Nat) (b : Block) : Program := exportsWith (some Prelude) cfg fuel b

/-- A block's library under `cfg` (`libWith`): `Prelude`'s exports, then those of the blocks it
uses, transitively. -/
def libOf (cfg : Config) (fuel : Nat) (b : Block) : Program := libWith (some Prelude) cfg fuel b

/-- Each named declaration is rejected with a message that starts as given (the reason, not
only the verdict). -/
def Report.rejectedWith (r : Report) (exp : List (String × String)) : Bool :=
  exp.all fun (n, pre) => match r.rows.find? (·.name == n) with
    | some { verdict := .rejected m _, .. } => pre.isPrefixOf m
    | _ => false

/-- Check a block: its library, then its own declarations (`runWith`). -/
def run (name : String) (b : Block) (cfg : Config := {}) (fuel : Nat := 2000000) : Report :=
  runWith (some Prelude) name b cfg fuel

def Row.show (r : Row) : String :=
  let exp := if r.expectAccept then "accept" else "reject"
  let got := match r.verdict with
    | .accepted => "accepted"
    | .rejected m _ => s!"rejected: {m}"
    | .undecided m => s!"undecided: {m}"
  let mark := if r.asExpected then "ok  " else "FAIL"
  s!"{mark} {r.name} (expect {exp}) {got}"

def Report.showTrace (r : Report) (name : String) : String :=
  match r.rows.find? (·.name == name) with
  | some row => "\n".intercalate (row.trace.toList.filterMap fun | .line s => some s | _ => none)
  | none => s!"no declaration {name}"

def Report.show (r : Report) : String :=
  s!"== {r.program}: {r.passed}/{r.count} as expected\n" ++
    "\n".intercalate (r.rows.map Row.show)

end Ochr.Test

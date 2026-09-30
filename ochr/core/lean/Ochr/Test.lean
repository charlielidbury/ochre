import Ochr.Prelude
import Ochr.Run

/-!
# Running example programs and asserting their verdicts

Each declaration in an `ochr` program carries an expectation (`def`: accepted,
`reject def`: rejected). `run` checks the block (after the declarations the blocks it
`uses` export) and pairs each of its own declarations' expectations with its verdict. The
`ochr` command checks every block this way when it is elaborated (`Ochr.Notation.checkBlock`),
so a green build means every verdict is as expected; `run` is for programmatic runs (the
test runner, the counterfactual ledger, the fuzzer, traces).
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
    | some { verdict := .rejected m, .. } => pre.isPrefixOf m
    | _ => false

/-- Check a block: its library, then its own declarations (`runWith`). -/
def run (name : String) (b : Block) (cfg : Config := {}) (fuel : Nat := 2000000) : Report :=
  runWith (some Prelude) name b cfg fuel

/-- The library declarations of `b` whose visibility under `cfg` differs from the default
(a library declaration flipped by the switched-off rule), as `(name, home block)`. -/
def libChanges (b : Block) (cfg : Config) (fuel : Nat) : List (String × String) :=
  (Prelude :: b.closure.filter (·.name != "Prelude")).flatMap fun u =>
    let e0 := (exportsOf {} fuel u).map (·.name)
    let e1 := (exportsOf cfg fuel u).map (·.name)
    ((e0.filter (!e1.contains ·)) ++ (e1.filter (!e0.contains ·))).map (·, u.name)

/-- Which of `b`'s flipped declarations are blocked by a changed library declaration: those
that mention one, or mention another blocked declaration of `b`. Each is paired with the
library declaration, `Home.decl`, that blocks it. -/
def blockedBy (b : Block) (changed : List (String × String)) (flipped : List String) :
    List (String × String) := Id.run do
  let mut blocked : List (String × String) := []
  let mut progress := true
  while progress do
    progress := false
    for d in b.decls do
      if flipped.contains d.name && (blocked.lookup d.name).isNone then
        let cause := d.mentions.findSome? fun n =>
          match changed.lookup n with
          | some home => some s!"{home}.{n}"
          | none => blocked.lookup n
        if let some c := cause then
          blocked := blocked ++ [(d.name, c)]
          progress := true
  pure blocked

/-- The counterfactual flips of one block under `cfg`: its declarations whose verdict differs
from the default, as `program.name:verdict`, and, separately, those that flip only because a
library declaration they mention flipped, as `program.name blocked by Home.decl`. The library
declaration itself is attributed to its home block (whose own report shows its flip). -/
def blockFlips (name : String) (b : Block) (cfg : Config) (fuel : Nat := 300000) :
    List String × List String := Id.run do
  let base := run name b {} fuel
  let alt := run name b cfg fuel
  let flipped := (base.rows.zip alt.rows).filterMap fun (r, r') =>
    if r.verdict.ok != r'.verdict.ok then some (r.name, r'.verdict.ok) else none
  let bl := if flipped.isEmpty || b.name == "Prelude" then [] else
    blockedBy b (libChanges b cfg fuel) (flipped.map (·.1))
  let mut out := []
  let mut blocked := []
  for (d, ok) in flipped do
    match bl.lookup d with
    | some cause => blocked := blocked ++ [s!"{name}.{d} blocked by {cause}"]
    | none => out := out ++ [s!"{name}.{d}:{if ok then "accepted" else "rejected"}"]
  pure (out, blocked)

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

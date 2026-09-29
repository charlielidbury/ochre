import Ochr.Notation

/-!
# Running example programs and asserting their verdicts

Each declaration in an `ochr` program carries an expectation (`def`: accepted,
`reject def`: rejected). `run` checks the block (after the declarations the blocks it
`uses` export) and pairs each of its own declarations' expectations with its verdict. Example files assert `(run P).allAsExpected` and the exact number of
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

/-- Check a list of declarations as one program: each is resolved against the whole list
(a resolution failure is a rejection of that declaration), then they are checked in order.
The verdict and trace of each, by name. -/
def checkProgram (p : Program) (cfg : Config) (fuel : Nat) : List (String × Verdict × Array String) :=
  Id.run do
  let mut defs : List Item := []
  let mut bad : List (String × String) := []
  for d in p do
    match resolveProgram p d with
    | .ok df => defs := defs ++ [df]
    | .error e => bad := bad ++ [(d.name, e)]
  let verdicts := checkDefs cfg defs fuel
  pure (p.map fun d => match bad.lookup d.name with
    | some e => (d.name, Verdict.rejected s!"(surface) {e}", #[])
    | none => (d.name, (verdicts.lookup d.name).getD (.rejected "not checked", #[])))

mutual
/-- What a block exports under `cfg`: its own declarations that are expected to be accepted
(`def`, not `reject def`) and are accepted, checked after its own library. A rejected or
`reject` declaration is never visible to the block's users. -/
partial def exportsOf (cfg : Config) (fuel : Nat) (b : Block) : Program :=
  let vs := checkProgram (libOf cfg fuel b ++ b.decls) cfg fuel
  b.decls.filter fun d => d.expectAccept && ((vs.lookup d.name).map (·.1.ok)).getD false

/-- A block's library under `cfg`: the exports of every block it uses, transitively, each
once, a block after the blocks it uses. It is checked again, under `cfg`, ahead of the
block's own declarations: nothing is cached, so switching a rule off re-decides the library
too. -/
partial def libOf (cfg : Config) (fuel : Nat) (b : Block) : Program :=
  b.closure.flatMap (exportsOf cfg fuel)
end

/-- Check a block: its library, then its own declarations. The report has a row for each of
its own declarations only; a library declaration is asserted in its home block. -/
def run (name : String) (b : Block) (cfg : Config := {}) (fuel : Nat := 2000000) : Report :=
  let vs := checkProgram (libOf cfg fuel b ++ b.decls) cfg fuel
  let rows := b.decls.map fun d =>
    let (v, tr) := (vs.lookup d.name).getD (.rejected "not checked", #[])
    { name := d.name, expectAccept := d.expectAccept, verdict := v, trace := tr }
  { program := name, rows := rows }

/-- The library declarations of `b` whose visibility under `cfg` differs from the default
(a library declaration flipped by the switched-off rule), as `(name, home block)`. -/
def libChanges (b : Block) (cfg : Config) (fuel : Nat) : List (String × String) :=
  b.closure.flatMap fun u =>
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
  let bl := if b.uses.isEmpty || flipped.isEmpty then [] else
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

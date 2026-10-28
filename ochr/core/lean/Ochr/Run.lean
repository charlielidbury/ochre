import Ochr.Surface

/-!
# Running a block: its library, then its own declarations

A block is checked after the declarations its library exports (`libWith`): the library
block `Prelude` first, then the blocks it `uses`, transitively. This module is imported by
the `ochr` command (`Ochr/Notation.lean`), which checks every block when it is elaborated,
so it cannot name the `Prelude` block (defined by that command, in `Ochr/Prelude.lean`):
the library block is a parameter here. `Ochr.Test` instantiates it with `Prelude`.
-/

namespace Ochr.Test
open Ochr Ochr.Surface

structure Row where
  name : String
  expectAccept : Bool
  verdict : Verdict
  trace : Array LogEntry := #[]     -- the trace (`Config.trace`) and the editor's notes

def Row.asExpected (r : Row) : Bool := r.expectAccept == r.verdict.ok

structure Report where
  program : String
  rows : List Row

def Report.allAsExpected (r : Report) : Bool := r.rows.all Row.asExpected
def Report.count (r : Report) : Nat := r.rows.length
def Report.passed (r : Report) : Nat := (r.rows.filter Row.asExpected).length

/-- Check a list of declarations as one program: each is resolved against the whole list
(a resolution failure is a rejection of that declaration), then they are checked in order.
The verdict and trace of each, by position: the `i`-th entry is the `i`-th declaration's,
so a declaration never reports another's verdict, even one with the same name (which
[Def] and [Ind-decl] reject). The declarations whose positions `located` names are resolved
and checked with their source locations (the editor), so their rejections say where. -/
def checkProgram (p : Program) (cfg : Config) (fuel : Nat) (located : Nat → Bool := fun _ => false) :
    List (String × Verdict × Array LogEntry) := Id.run do
  let mut defs : List Item := []
  let mut locs : Array Locs := #[]                         -- per resolved declaration
  let mut bad : Array (Option (String × Option Loc)) := #[]  -- per declaration: its resolution error
  for (d, i) in p.zipIdx do
    let (r, st) := if located i then resolveLocated p d else (resolveProgram p d, {})
    match r with
    | .ok df =>
      defs := defs ++ [df]
      locs := locs.push st.locs
      bad := bad.push none
    | .error e => bad := bad.push (some (e, st.failAt))
  let mut verdicts := checkDefs cfg defs fuel (fun j => locs[j]?.getD {})
  let mut out := #[]
  for (d, e) in p.zip bad.toList do
    match e with
    | some (e, l) => out := out.push (d.name, Verdict.rejected s!"(surface) {e}" l, #[])
    | none => match verdicts with
      | (_, v, tr) :: rest => out := out.push (d.name, v, tr); verdicts := rest
      | [] => out := out.push (d.name, .rejected "not checked", #[])
  pure out.toList

mutual
/-- What a block exports under `cfg`: its own declarations that are expected to be accepted
(`def`, not `reject def`) and are accepted, checked after its own library. A rejected or
`reject` declaration is never visible to the block's users. -/
partial def exportsWith (pre : Option Block) (cfg : Config) (fuel : Nat) (b : Block) : Program :=
  let lib := libWith pre cfg fuel b
  let vs := (checkProgram (lib ++ b.decls) cfg fuel).drop lib.length
  (b.decls.zip vs).filterMap fun (d, _, v, _) => if d.expectAccept && v.ok then some d else none

/-- A block's library under `cfg`, with `pre` the library block (`Prelude`, v2.1), used by
every block, first: the exports of `pre` and of every block `b` uses, transitively, each
once, a block after the blocks it uses. It is checked again, under `cfg`, ahead of the
block's own declarations: nothing is cached, so switching a rule off re-decides the library
too. `pre` itself has no library. -/
partial def libWith (pre : Option Block) (cfg : Config) (fuel : Nat) (b : Block) : Program :=
  match pre with
  | none => b.closure.flatMap (exportsWith none cfg fuel)
  | some p =>
    if b.name == p.name then [] else
    exportsWith pre cfg fuel p ++
      (b.closure.filter (·.name != p.name)).flatMap (exportsWith pre cfg fuel)
end

/-- Check a block after its library (`libWith pre`). The report has a row for each of its
own declarations only; a library declaration is asserted in its home block. `located`: its
own declarations' rejections say where (the editor). -/
def runWith (pre : Option Block) (name : String) (b : Block) (cfg : Config := {}) (fuel : Nat := 2000000)
    (located : Bool := false) : Report :=
  let lib := libWith pre cfg fuel b
  let vs := (checkProgram (lib ++ b.decls) cfg fuel (fun i => located && lib.length ≤ i)).drop lib.length
  let rows := (b.decls.zip vs).map fun (d, _, v, tr) =>
    { name := d.name, expectAccept := d.expectAccept, verdict := v, trace := tr }
  { program := name, rows := rows }

end Ochr.Test

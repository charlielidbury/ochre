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
The verdict and trace of each, by name. The declarations `located` names are resolved and
checked with their source locations (the editor), so their rejections say where. -/
def checkProgram (p : Program) (cfg : Config) (fuel : Nat) (located : String → Bool := fun _ => false) :
    List (String × Verdict × Array LogEntry) := Id.run do
  let mut defs : List Item := []
  let mut bad : List (String × String × Option Loc) := []
  let mut locs : List (String × Locs) := []
  for d in p do
    let (r, st) := if located d.name then resolveLocated p d else (resolveProgram p d, {})
    match r with
    | .ok df =>
      defs := defs ++ [df]
      if located d.name then locs := (d.name, st.locs) :: locs
    | .error e => bad := bad ++ [(d.name, e, st.failAt)]
  let verdicts := checkDefs cfg defs fuel (fun n => (locs.lookup n).getD {})
  pure (p.map fun d => match bad.lookup d.name with
    | some (e, l) => (d.name, Verdict.rejected s!"(surface) {e}" l, #[])
    | none => (d.name, (verdicts.lookup d.name).getD (.rejected "not checked", #[])))

mutual
/-- What a block exports under `cfg`: its own declarations that are expected to be accepted
(`def`, not `reject def`) and are accepted, checked after its own library. A rejected or
`reject` declaration is never visible to the block's users. -/
partial def exportsWith (pre : Option Block) (cfg : Config) (fuel : Nat) (b : Block) : Program :=
  let vs := checkProgram (libWith pre cfg fuel b ++ b.decls) cfg fuel
  b.decls.filter fun d => d.expectAccept && ((vs.lookup d.name).map (·.1.ok)).getD false

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
  let own := b.decls.map (·.name)
  let vs := checkProgram (libWith pre cfg fuel b ++ b.decls) cfg fuel (fun n => located && own.contains n)
  let rows := b.decls.map fun d =>
    let (v, tr) := (vs.lookup d.name).getD (.rejected "not checked", #[])
    { name := d.name, expectAccept := d.expectAccept, verdict := v, trace := tr }
  { program := name, rows := rows }

end Ochr.Test

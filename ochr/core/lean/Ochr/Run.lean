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

def Row.asExpected (r : Row) : Bool :=
  match r.verdict with
  | .accepted => r.expectAccept
  | .rejected .. => !r.expectAccept
  | .undecided _ => false     -- not knowing is never what a test expects

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
and checked with their source locations (the editor), so their rejections say where.
Resolution is bounded by `fuel` too: a declaration whose resolution runs out of it is
`undecided`, and so is every later one that mentions it (`checkDefs`). -/
def checkProgram (p : Program) (cfg : Config) (fuel : Nat) (located : Nat → Bool := fun _ => false) :
    List (String × Verdict × Array LogEntry) := Id.run do
  let mut defs : List Item := []
  let mut locs : Array Locs := #[]                         -- per resolved declaration
  -- per declaration: its resolution error (a rejection) or exhaustion (undecided)
  let mut bad : Array (Option Verdict) := #[]
  let mut undecided : List String := []                    -- declarations undecided in resolution
  let mut undecidedBefore : Array (List String) := #[]      -- per resolved declaration
  for (d, i) in p.zipIdx do
    let (r, st) := runResolve p d fuel (located i)
    match r with
    | .ok (.ok df) =>
      defs := defs ++ [df]
      locs := locs.push st.locs
      undecidedBefore := undecidedBefore.push undecided
      bad := bad.push none
    | .ok (.error e) => bad := bad.push (some (.rejected s!"(surface) {e}" st.failAt))
    | .error e =>
      undecided := d.name :: undecided
      bad := bad.push (some (.undecided e.msg))
  let mut verdicts := checkDefs cfg defs fuel (fun j => locs[j]?.getD {}) (fun j => undecidedBefore[j]?.getD [])
  let mut out := #[]
  for (d, e) in p.zip bad.toList do
    match e with
    | some v => out := out.push (d.name, v, #[])
    | none => match verdicts with
      | (_, v, tr) :: rest => out := out.push (d.name, v, tr); verdicts := rest
      | [] => out := out.push (d.name, .rejected "not checked", #[])
  pure out.toList

/-- The measure of `exportsWith`/`libWith`: the library block `pre` is checked first and has
no library of its own, so it ranks below every other block. -/
def libRank (pre : Option Block) (b : Block) : Nat :=
  match pre with
  | some p => if b.name == p.name then 0 else 1
  | none => 1

mutual
/-- What a block exports under `cfg`: its own declarations that are expected to be accepted
(`def`, not `reject def`) and are accepted, checked after its own library. A rejected or
`reject` declaration is never visible to the block's users. An undecided one is exported, so
that what its users write about it is undecided too (`checkDefs`), not rejected for a name
that exhaustion removed. -/
def exportsWith (pre : Option Block) (cfg : Config) (fuel : Nat) (b : Block) : Program :=
  let lib := libWith pre cfg fuel b
  let vs := (checkProgram (lib ++ b.decls) cfg fuel).drop lib.length
  (b.decls.zip vs).filterMap fun (d, _, v, _) =>
    if d.expectAccept && (v matches .accepted | .undecided _) then some d else none
termination_by (libRank pre b, sizeOf b, 1)

/-- A block's library under `cfg`, with `pre` the library block (`Prelude`, v2.1), used by
every block, first: the exports of `pre` and of every block `b` uses, transitively, each
once, a block after the blocks it uses. It is checked again ahead of the block's own declarations: nothing is cached. `pre` itself has no library. Terminates: `pre` ranks lowest, and a used block is smaller (`Block.sizeOf_lt_of_mem_closure`). -/
def libWith (pre : Option Block) (cfg : Config) (fuel : Nat) (b : Block) : Program :=
  match pre with
  | none => b.closure.attach.flatMap fun ⟨u, _⟩ => exportsWith none cfg fuel u
  | some p =>
    if hb : b.name == p.name then [] else
    exportsWith (some p) cfg fuel p ++
      (b.closure.filter (·.name != p.name)).attach.flatMap fun ⟨u, _⟩ => exportsWith (some p) cfg fuel u
termination_by (libRank pre b, sizeOf b, 0)
decreasing_by
  all_goals simp_wf
  · apply Prod.Lex.right; apply Prod.Lex.left
    exact Block.sizeOf_lt_of_mem_closure ‹_›
  · apply Prod.Lex.left; simp [libRank, hb]
  · rename_i h
    have hu := List.mem_filter.mp h
    have hun : (u.name == p.name) = false := by simpa using hu.2
    have hr : libRank (some p) u = libRank (some p) b := by simp [libRank, hb, hun]
    rw [hr]; apply Prod.Lex.right; apply Prod.Lex.left
    exact Block.sizeOf_lt_of_mem_closure hu.1
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

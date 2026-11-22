import Ochr.Meaning.Steps.Statements
import Ochr.Examples.Nat

/-!
# The read of a place: pins (lead26, 2026-11-22; docs/31 D181, D182)

**A borrow whose content is partly moved out is read (moved) by the checker** (FINDING; RULED (A), D182: the checker
will reject it, main's D127; until then the named checker fact `Master.BorrowReadWhole` is FALSE, and the pins below
flip when it lands). `MB2`
moves `x`'s first field out through `r` (D53 (h): allowed if the content is whole again when the borrow ends),
then reads `r` whole (`let r2 = r`, a move of the borrow), then makes the content whole through `r2`: ACCEPTED.
`readPlace`'s borrow branch moves a borrow before its `hasHole` check, which every other value meets ("[Read] …
was partly moved out", D53). The reference reads a borrow as its content (`meanV`'s `.borrow` clause), and its
`readPlace` returns nothing for a value that is not whole (`Sem.whole`: a record with a `moved` field is not), so
its run of `MB2`'s body fails at `r`: the typed place step is FALSE as the two stand (by reading the reference,
which is not computable; the checker's verdicts are pinned here). `MB1` (the content restored through `r` itself)
and `MB3` (the borrow ends partly moved: rejected) are the controls.
-/

open Ochr.Test

ochr PlaceMB uses Nats {
  inductive Box := MkBox(n : Nat)
  def MB1 (a : Nat) (b : Nat) : Unit := (let x = (MkBox(a), b); let r = &x; let y = (*r).0; *r := (MkBox(Z), Z); ())
  def MB2 (a : Nat) (b : Nat) : Unit := (let x = (MkBox(a), b); let r = &x; let y = (*r).0; let r2 = r; *r2 := (MkBox(Z), Z); ())
  reject def MB3 (a : Nat) (b : Nat) : Unit := (let x = (MkBox(a), b); let r = &x; let y = (*r).0; let r2 = r; ())
}

-- TODAY: `MB2` is accepted (the pin flips if the checker rejects reading a partly moved borrow, main's D127)
#guard (Ochr.Test.runWith (some Prelude) "PlaceMB" PlaceMB {} (located := false)).allAsExpected

-- the point before `let r2 = r`, as a hole (rejected: with nothing after the hole the borrow ends partly moved; the
-- checker's state at the hole is recorded on the way)
#guard_msgs (drop warning) in
ochr PlaceMBAt uses Nats {
  inductive Box := MkBox(n : Nat)
  reject def MB2At (a : Nat) (b : Nat) : Unit := (let x = (MkBox(a), b); let r = &x; let y = (*r).0; ?)
}

/-! **A copy read of a value holding `⊥`** (D182's table, the copy row): the checker copies a copy-type value without
its `hasHole` test, which the reference's whole test asks. In a typed run the read's [Repack] (before the access)
rejects a dependent value holding `⊥`: a `copy` record whose leaf field a write to its index invalidated is not read
whole (`CP1`, `CP3`); restored first, it is (`CP2`). A non-dependent copy-type value cannot hold `⊥` (its fields are
copied, never moved). -/

ochr PlaceCopyHole uses Nats {
  inductive Bit := B0 | B1
  def Pay2 (b : Bit) : Type := match b { B0 => Bit, B1 => Unit, }
  copy inductive CT := MkCT(b : Bit, x : Pay2(b))
  reject def CP1 (c0 : CT) : CT := (let c = c0; match c { MkCT(b, x) => (b := B1; ()), }; c)
  def CP2 (c0 : CT) : CT := (let c = c0; match c { MkCT(b, x) => (b := B1; x := ()), }; c)
  reject def CP3 (c0 : CT) : Unit := (let c = c0; match c { MkCT(b, x) => (b := B1; ()), }; let d = c; ())
}

#guard (Ochr.Test.runWith (some Prelude) "PlaceCopyHole" PlaceCopyHole {} (located := false)).allAsExpected

namespace Ochr.Meaning.Steps.PlaceGuards
open Ochr Ochr.Meaning Ochr.Meaning.Steps

/-- The checker's whole state at `MB2At`'s hole, before `let r2 = r`: `x ↦ loan_0`, `r ↦ borrow_0 (⊥, σb)`,
`y ↦ MkBox(σa)`; `r` is variable 1. -/
def stMB : MState :=
  let r := Ochr.Test.runWith (some Prelude) "PlaceMBAt" PlaceMBAt { recordStates := true } (located := true)
  match r.rows.find? (·.name == "MB2At") with
  | some row => (row.trace.toList.filterMap fun
      | .state _ false _ st => some st | _ => none).getLast?.getD default
  | none => default

/-- The value the checker's `readPlace` of `r` returns at `MB2At`'s hole, if it succeeds. -/
def readR : Option Value :=
  match (runMachine (Ochr.readPlace 100 (.var 1)) stMB 100000).1 with
  | .ok v _ => some v
  | _ => none

-- TODAY: the read succeeds and returns a borrow whose content holds `⊥` (`BorrowReadWhole` is FALSE); after main's
-- D127 the read fails, and this pin flips
#guard match readR with | some (.borrow _ w) => w.hasHole | _ => false
-- control: the content's second field is whole, its first is not
#guard match readR with | some (.borrow _ (.ind _ _ _ _ [f0, f1])) => Value.exact f0 .bot && !f1.hasHole | _ => false

end Ochr.Meaning.Steps.PlaceGuards

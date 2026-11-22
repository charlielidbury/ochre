import Ochr.Meaning.Steps.Statements
import Ochr.Examples.Nat

/-!
# The read of a place: pins (lead26, 2026-11-22; docs/31 D181, D182)

**A borrow whose content is partly moved out was read (moved) by the checker** (FINDING; RULED (A), D182: the checker
rejects it since main's D127, merged by machine11; the pins below are flipped, and `Master.BorrowReadWhole` reads TRUE
against the new `readPlace`). `MB2`
moves `x`'s first field out through `r` (D53 (h): allowed if the content is whole again when the borrow ends),
then reads `r` whole (`let r2 = r`, a move of the borrow), then makes the content whole through `r2`: ACCEPTED before
D127, REJECTED since. Before D127 `readPlace`'s borrow branch moved a borrow before its `hasHole` check, which every
other value meets ("[Read] … was partly moved out", D53); D127 tests the borrow's content in that branch. The reference reads a borrow as its content (`meanV`'s `.borrow` clause), and its
`readPlace` returns nothing for a value that is not whole (`Sem.whole`: a record with a `moved` field is not), so
its run of `MB2`'s body fails at `r`: the typed place step is FALSE as the two stand (by reading the reference,
which is not computable; the checker's verdicts are pinned here). `MB1` (the content restored through `r` itself)
and `MB3` (the borrow ends partly moved: rejected) are the controls.
-/

open Ochr.Test

ochr PlaceMB uses Nats {
  inductive Box := MkBox(n : Nat)
  def MB1 (a : Nat) (b : Nat) : Unit := (let x = (MkBox(a), b); let r = &x; let y = (*r).0; *r := (MkBox(Z), Z); ())
  reject def MB2 (a : Nat) (b : Nat) : Unit := (let x = (MkBox(a), b); let r = &x; let y = (*r).0; let r2 = r; *r2 := (MkBox(Z), Z); ())
  reject def MB3 (a : Nat) (b : Nat) : Unit := (let x = (MkBox(a), b); let r = &x; let y = (*r).0; let r2 = r; ())
}

-- `MB2` is rejected since main's D127 (it was accepted before: the pin flipped at machine11's merge)
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

-- since main's D127 the read fails (before it, it returned a borrow whose content held `⊥`; the pin flipped at
-- machine11's merge)
#guard readR.isNone
-- control: the state is the one described: `r` holds a borrow whose content's first field is `⊥`, its second whole
#guard match (runMachine (Ochr.content (.var 1)) stMB 100000).1 with
  | .ok (.borrow _ (.ind _ _ _ _ [f0, f1])) _ => Value.exact f0 .bot && !f1.hasHole | _ => false

end Ochr.Meaning.Steps.PlaceGuards

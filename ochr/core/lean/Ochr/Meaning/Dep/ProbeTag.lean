-- Attack probes of the dependent-values lane, run with `lake env lean` against main 5a2106a9 (scratch
-- worktree). Not imported by any library root. Every declaration is `def`: an error is a rejection.
-- Verdicts are recorded in ../HANDOFF.md.
import Ochr.Examples.Nat
import Ochr.Examples.Bool
open Ochr.Test

ochr PTag uses Nats, Bools {
  def Payload (b : Bool) : Type := (match b { false => Nat, true => Unit })
  inductive Tagged := MkT(b : Bool, x : Payload(b))
  -- change tag and payload in place, tag first
  def TagFirst (p : &Tagged) : Unit := match *p { MkT(b, x) => (b := true; x := ()), }
  -- payload first
  def PayloadFirst (p : &Tagged) : Unit := match *p { MkT(b, x) => (x := (); b := true), }
  -- keep the old payload: take it out before the tag changes
  def TakeOld (p : &Tagged) : Nat := match *p { MkT(b, x) => match b { false => (let old = x; b := true; x := (); old), true => 0, }, }
  -- read the old payload after the tag changed
  def ReadAfter (p : &Tagged) : Nat := match *p { MkT(b, x) => match b { false => (b := true; let old = x; x := (); old), true => 0, }, }
  -- the whole value written
  def Whole (p : &Tagged) : Unit := (*p := MkT(true, ()))
  -- a borrow of the payload while the tag is lent
  def LentTag (p : &Tagged) : Unit := match *p { MkT(b, x) => (let r = &b; x := 5; ()), }
  -- a borrow of the payload live across the tag's write
  def LentPayload (p : &Tagged) : Unit := match *p { MkT(b, x) => (let r = &x; b := true; x := ()), }
  def LentPayloadEnded (p : &Tagged) : Unit := match *p { MkT(b, x) => ((let r = &x; ()); b := true; x := ()), }
  -- runs
  def TagFirstRuns : Eq(Bool, (let t = MkT(false, 3); TagFirst(&t); match t { MkT(b, x) => b, }), true) := refl
  def TakeOldRuns : Eq(Nat, (let t = MkT(false, 3); TakeOld(&t)), 3) := refl
}

import Ochr.Examples.E1

/-! # E2: a returned borrow (`TailM`), and proofs about a program that uses it -/

open Ochr.Test

ochr E2 {
  def AddM (x : &Nat) (y : Nat) : Unit :=
    match *x { Z => *x := y | S p => AddM(&p, y) }

  -- a borrow of the final Z node
  def TailM (x : &Nat) : &Nat :=
    match *x { Z => x | S p => TailM(&p) }

  def AddM' (x : &Nat) (y : Nat) : Unit :=
    let t = TailM(x); *t := y

  def AddMEq (x : &Nat) (y : Nat) : Id Unit (AddM(x, y)) (AddM'(x, y)) :=
    match *x { Z => refl | S p => AddMEq(&p, y) }

  def AddMEqOwned (x : Nat) : Id Unit (AddM(&x, 0)) (AddM'(&x, 0)) :=
    AddMEq(&x, 0)

  -- deriver-e2 §8: reading and writing through the returned borrow
  def AddM1 (x : &Nat) : Id Unit (AddM(x, 1)) (let t = TailM(x); *t := S *t) :=
    match *x { Z => refl | S p => AddM1(&p) }

  def TailNoop (x : &Nat) : Id Unit (let t = TailM(x); ()) () :=
    match *x { Z => refl | S p => TailNoop(&p) }
}

#eval IO.println (run "E2" E2).show

-- every verdict as expected, and exactly 7 assertions (a truncated file changes the count)
#guard (run "E2" E2).allAsExpected
#guard (run "E2" E2).count == 7

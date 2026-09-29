import Ochr.Test

/-! # E1: in-place addition, and adding zero has no effect (RULES §7, BRIEF) -/

open Ochr.Test

ochr E1 {
  def AddM (x : &Nat) (y : Nat) : Unit by x :=
    match *x { Z => *x := y, S p => AddM(&p, y) }

  def AddMZero (x : &Nat) : Id Unit (AddM(x, 0)) () by x :=
    match *x { Z => refl, S p => AddMZero(&p) }

  def Add (x : Nat) (y : Nat) : Nat := AddM(&x, y); x

  -- the pure theorem by the in-place lemma on the predecessor field: borrowing x.1
  -- makes the environment do the congruence (v1.2, D25); no cong, no recursion
  def AddZero (x : Nat) : Id Nat (Add(x, 0)) x :=
    match x { Z => refl, S p => AddMZero(&p) }

  def AddZero' (x : Nat) : Id Nat (Add(x, 0)) x := AddMZero(&x)

  -- the paper's §10 excerpt of this file: a type is formed before the body runs
  reject def WriteThenRefl (x : &Nat) : Id Nat (*x) 5 := *x := 5; refl
}

#eval IO.println (run "E1" E1).show

-- every verdict as expected, and exactly 6 assertions (a truncated file changes the count)
#guard (run "E1" E1).allAsExpected
#guard (run "E1" E1).count == 6

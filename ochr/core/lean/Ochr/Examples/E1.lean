import Ochr.Test

/-! # E1: in-place addition, and adding zero has no effect (RULES §7, BRIEF) -/

open Ochr.Test

ochr E1 {
  def AddM (x : &Nat) (y : Nat) : Unit :=
    match *x { Z => *x := y | S p => AddM(&p, y) }

  def AddMZero (x : &Nat) : Id Unit (AddM(x, 0)) () :=
    match *x { Z => refl | S p => AddMZero(&p) }

  def Add (x : Nat) (y : Nat) : Nat := AddM(&x, y); x

  def AddZero (x : Nat) : Id Nat (Add(x, 0)) x :=
    match x { Z => refl | S p => cong S (AddZero(p)) }
}

#eval IO.println (run "E1" E1).show

import Ochr.Examples.E2

/-! # E3: a branch-dependent live borrow (accepted since v1 closes off the stuck match, D15)

`Nat` stands in for `Bool`: `Z` is false, `S _` is true (deriver-e346 E3.0). -/

open Ochr.Test

ochr E3 {
  def AddM (x : &Nat) (y : Nat) : Unit by x :=
    match *x { Z => *x := y | S p => AddM(&p, y) }

  def AddMZero (x : &Nat) : Id Unit (AddM(x, 0)) () by x :=
    match *x { Z => refl | S p => AddMZero(&p) }

  -- the match is not in tail position: its arms are checked, then it is closed off
  def AddToOne (b : Nat) (x1 : &Nat) (x2 : &Nat) (y : Nat) : Unit :=
    let r = match b { Z => x1 | S _ => x2 }; AddM(r, y)

  -- the hand-duplicated version
  def AddToOne' (b : Nat) (x1 : &Nat) (x2 : &Nat) (y : Nat) : Unit :=
    match b { Z => AddM(x1, y) | S _ => AddM(x2, y) }

  -- the same match behind a call
  def Pick (b : Nat) (x1 : &Nat) (x2 : &Nat) : &Nat :=
    match b { Z => x1 | S _ => x2 }

  def AddToOne'' (b : Nat) (x1 : &Nat) (x2 : &Nat) (y : Nat) : Unit :=
    let r = Pick(b, x1, x2); AddM(r, y)

  -- deriver-e346 §E3.3, with the natural proof (Eq A a a ≡ ⊤ removes the refl padding)
  def AddToOneZero (b : Nat) (x1 : &Nat) (x2 : &Nat) : Id Unit (AddToOne'(b, x1, x2, 0)) () :=
    match b { Z => AddMZero(x1) | S _ => AddMZero(x2) }

  def AddToOneZero'' (b : Nat) (x1 : &Nat) (x2 : &Nat) : Id Unit (AddToOne''(b, x1, x2, 0)) () :=
    match b { Z => AddMZero(x1) | S _ => AddMZero(x2) }

  -- the inline version: its stuck match is closed off in the goal too
  def AddToOneZeroInline (b : Nat) (x1 : &Nat) (x2 : &Nat) : Id Unit (AddToOne(b, x1, x2, 0)) () :=
    match b { Z => AddMZero(x1) | S _ => AddMZero(x2) }
}

#eval IO.println (run "E3" E3).show

-- every verdict as expected, and exactly 9 assertions (a truncated file changes the count)
#guard (run "E3" E3).allAsExpected
#guard (run "E3" E3).count == 9

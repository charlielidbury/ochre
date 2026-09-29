import Ochr.Examples.Attacks

/-! # Further probes found while implementing v1 (see notes/lean-checker.md) -/

open Ochr.Test

ochr More {
  def AddM (x : &Nat) (y : Nat) : Unit by x :=
    match *x { Z => *x := y, S p => AddM(&p, y) }

  -- deriver-e346 §E4.3: matching after an opaque call. v1's [Split] covers only σ;
  -- the checker generalises the sealed program to a fresh σ, then splits (C8).
  def MatchAfterOpaque (f : Π(_ : &Nat). Unit) (x : &Nat) : Unit :=
    f(&*x); match *x { Z => (), S _ => () }

  -- lean-checker L2: a later argument ends an earlier argument's borrow. Without the
  -- check the callee receives ⊥ for a borrow parameter; an opaque callee then gets a
  -- sealed call on ⊥, and the concrete run of Dead(g, 0) goes wrong when g writes.
  reject def Dead (f : Π(a : &Nat) (b : Nat). Unit) (x : Nat) : Unit := f(&x, x)
  reject def DeadTwice (f : Π(a : &Nat) (b : &Nat). Unit) (x : Nat) : Unit := f(&x, &x)
  def NotDead (f : Π(a : Nat) (b : &Nat). Unit) (x : Nat) : Unit := f(x, &x)

  -- breaker-frame attack 1: a lemma proved for disjoint borrows, instantiated at
  -- aliased ones. Blocked at argument evaluation: moving z ends the reborrow a (D19).
  def g (x : &Nat) (y : &Nat) : Id Nat (*x := 0; *y := 1; *x) (*x := 0; *y := 1; 0) := refl
  reject def attack (z : &Nat) : Id Nat 1 0 := let a = &*z; g(z, a)
  reject def attack' (z : &Nat) : Id Nat 1 0 := let a = &*z; g(a, z)

  -- a recursive call inside a non-tail match: checked in the arm, then the match is
  -- closed off with the function itself as a value argument
  def NonTailRec (x : &Nat) : Unit by x := (match *x { Z => (), S p => NonTailRec(&p) }); ()

  -- stuck matches in a goal are closed off the same way on both sides
  def StuckGoal (b : Nat) : Id Nat (match b { Z => 0, S _ => 1 }) (match b { Z => 0, S _ => 1 }) := refl
  -- after a split the sealed stuck blocks re-run to the arm values
  def StuckGoalSplit (b : Nat) : Id Nat (match b { Z => 0, S m => S m }) b :=
    match b { Z => refl, S _ => refl }
  reject def StuckGoalWrong (b : Nat) : Id Nat (match b { Z => 0, S _ => 1 }) b :=
    match b { Z => refl, S _ => refl }

  -- the paper's example shape with a let before the match (D5: the footprint
  -- does not depend on unrelated locals)
  def AddMZeroLet (x : &Nat) : Id Unit (let n = 0; AddM(x, n)) () by x :=
    match *x { Z => refl, S p => AddMZeroLet(&p) }
}

#eval IO.println (run "More" More).show

-- every verdict as expected, and exactly 13 assertions (a truncated file changes the count)
#guard (run "More" More).allAsExpected
#guard (run "More" More).count == 13

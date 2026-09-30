import Ochr.Examples.«00Std»
open Ochr Ochr.Test
/-! DropProbe's `Bad2` class, as the fuzzer's Drop family (`--drop N`) finds it: a borrow
returned by a stuck call or a stuck block, whose hole sits in two owners' fills, assigned
into a variable that outlives one of them, then any access to the other owner: a read, a
write, or a borrow. On ochr-core 20a764c3 each function was accepted and its ground call
rejected; under the ghost borrows (a632b90c, reverted) each function was rejected at the
definition. Under amended D65 (d65-lane: a dying local ends the borrowers held in bindings)
each function and each ground call is accepted. The tour's `Drops` block (02Borrows) holds
these. -/
ochr DropVariants uses Fixtures {
  -- a stuck block instead of a stuck call
  def D1 (n : Nat) (b : Nat) (x : &Nat) : Unit := (let a = 0; x := match n { Z => &a, S _ => &b }; let z = b; ())
  def D1Run : Unit := (let y = 7; D1(0, 5, &y))
  -- a write to the other owner
  def D2 (n : Nat) (b : Nat) (x : &Nat) : Unit := (let a = 0; x := Pick(n, &a, &b); b := 0)
  def D2Run : Unit := (let y = 7; D2(0, 5, &y))
  -- a borrow of the other owner
  def D3 (n : Nat) (b : Nat) (x : &Nat) : Unit := (let a = 0; x := Pick(n, &a, &b); let w = &b; ())
  def D3Run : Unit := (let y = 7; D3(0, 5, &y))
  -- the other order of the owners
  def D4 (n : Nat) (b : Nat) (x : &Nat) : Unit := (let a = 0; x := Pick(n, &b, &a); let z = b; ())
  def D4Run : Unit := (let y = 7; D4(1, 5, &y))
}
#eval IO.println (run "DropVariants" DropVariants).show
#guard (run "DropVariants" DropVariants).allAsExpected
#guard (run "DropVariants" DropVariants).count == 8

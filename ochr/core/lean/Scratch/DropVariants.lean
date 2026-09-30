import Ochr.Examples.«00Std»
open Ochr Ochr.Test
/-! DropProbe's `Bad2` class, as the fuzzer's Drop family (`--drop N`) finds it: a borrow
returned by a stuck call or a stuck block, whose hole sits in two owners' fills, assigned
into a variable that outlives one of them, then any access to the other owner: a read, a
write, or a borrow. Each function is accepted, and its ground call is rejected; verdicts as
they stood on ochr-core 20a764c3. Since the ghost-borrow change (a632b90c), each function is
rejected at the definition ("[Drop] a goes out of scope while it is borrowed"), as the `…Run`
defs always were; checked on ochr-core 042a06f7. -/
ochr DropVariants uses Fixtures {
  -- a stuck block instead of a stuck call
  reject def D1 (n : Nat) (b : Nat) (x : &Nat) : Unit := (let a = 0; x := match n { Z => &a, S _ => &b }; let z = b; ())
  reject def D1Run : Unit := (let y = 7; D1(0, 5, &y))
  -- a write to the other owner
  reject def D2 (n : Nat) (b : Nat) (x : &Nat) : Unit := (let a = 0; x := Pick(n, &a, &b); b := 0)
  reject def D2Run : Unit := (let y = 7; D2(0, 5, &y))
  -- a borrow of the other owner
  reject def D3 (n : Nat) (b : Nat) (x : &Nat) : Unit := (let a = 0; x := Pick(n, &a, &b); let w = &b; ())
  reject def D3Run : Unit := (let y = 7; D3(0, 5, &y))
  -- the other order of the owners
  reject def D4 (n : Nat) (b : Nat) (x : &Nat) : Unit := (let a = 0; x := Pick(n, &b, &a); let z = b; ())
  reject def D4Run : Unit := (let y = 7; D4(1, 5, &y))
}
#eval IO.println (run "DropVariants" DropVariants).show

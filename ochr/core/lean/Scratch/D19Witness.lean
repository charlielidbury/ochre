import Ochr.Test
open Ochr Ochr.Test
/-! D19 witnesses that do not go through a `Unit`-returning stuck call (since D59, `BadA1` no
longer depends on D19). Each function is rejected under the default rules. With
`accessInside := false` it is accepted, and its `…Run` (a call on a ground input) is
rejected: an accepted function that goes wrong when run.

`V`, found by the fuzzer (`--diff --switch D19`, seed 1, case 17830), has no call at all. A
stuck block returns a borrow of `n0`, so [Close] leaves `n0` holding a sealed program with
the borrow's loan inside it. Reading `n0` must end that borrow (D19: loans *inside* the
content). Without D19 the later write through `a0` is accepted; at `n0 = 0` the block runs,
the read of `n0` ends `a0`, and the write has no place.

`W` is [Close]'s precondition (a stuck call's arguments hold no loans). `&a` still holds
`r`'s loan inside, [Close] seals it into `out`, and the write through `r` is accepted; at
`n = 1` the call runs and overwrites `a` while `r` borrows inside it. The result goes to
`out`, declared before `r`, so `r` dies first and [Drop] never sees the loan in the sealed
result. Bound after `r`, as in `BadA1`, it is caught by [Drop] even without D19. -/
ochr D19Default {
  def G2 (x : &Nat) (n : Nat) : Nat := (match n { Z => 0, S _ => *x := 0; 0 })
  -- "no such place *a0"
  reject def V (n0 : Nat) : Unit := (let a0 = match n0 { Z => &n0, S _ => &n0 }; *a0 := n0)
  -- "no such place *r"
  reject def W (n : Nat) : Nat := (let a = S Z; let out = 0; (let r = &a.1; out := G2(&a, n); *r := S Z); out)
}
ochr D19Off {
  def G2 (x : &Nat) (n : Nat) : Nat := (match n { Z => 0, S _ => *x := 0; 0 })
  def V (n0 : Nat) : Unit := (let a0 = match n0 { Z => &n0, S _ => &n0 }; *a0 := n0)
  -- "no such place *a0"
  reject def VRun : Unit := V(0)
  def W (n : Nat) : Nat := (let a = S Z; let out = 0; (let r = &a.1; out := G2(&a, n); *r := S Z); out)
  -- "[Drop] the old content of *x is overwritten while borrowed"
  reject def WRun : Nat := W(1)
}
#eval IO.println (run "D19Default (default rules)" D19Default).show
#eval IO.println (run "D19Off (D19 off)" D19Off { accessInside := false }).show

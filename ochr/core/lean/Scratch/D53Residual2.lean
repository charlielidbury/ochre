import Ochr.Test
open Ochr Ochr.Test
/-! D53 acceptance on ochr-core-lean 0b8a68f0 (fuzzer, execution oracle, `--switch +D53`,
10⁶ cases): 10 cases remain (11 findings), of three shapes. Each `F` is accepted and its `FRun`, a call on
a ground input, is rejected. Run with D53 on.
- P (7 of the 10): a borrow whose content was already moved out is passed to a stuck call,
  or to an erased call inside a stuck block's arm. [Close] fills the borrowed place with a
  sealed program, which hides the move; when the call runs, the borrow ends with ⊥ inside.
  The same through a stuck block's arm calling a data function (`PBlockData`) is rejected.
- Q (2): a closure made in a stuck block's arm captures a place (by move) and writes its own
  copy; the block does not count the capture as a move of the place.
- K (1, the fuzzer's case seed 6 28548, delta-debugged by hand): one arm matches the whole
  place `a4` (an in-place read), another moves `a4.2` out; the block captures `a4` whole
  and the move of `a4.2` is lost. Moving versus borrowing or writing in the other arm is
  handled (`KBorrow`, `KWrite`). -/
ochr D53Residual2 {
  inductive B2 := F | T
  inductive L := Nil | Cons(h : Nat, t : L)
  def G1 (x : &Nat) (n : Nat) : Unit := match n { Z => (), S _ => *x := 0 }
  def F5 (x : &Nat) : Prop := *x := 5; ⊤
  -- P: "a borrow ends while its content is partly moved out (⊥)"
  def P1 (x0 : &Nat) : Unit := let a3 = *x0; G1(x0, a3)
  def P1Run : Nat := let c = 0; P1(&c); 0
  def P2 (x1 : &Nat) : Unit := (let a0 = *x1; match a0 { Z => (), S _ => F5(x1); () }); ()
  def P2Run : Nat := let c = 0; P2(&c); 0
  def P3 (x0 : &Nat) (l1 : L) : L := Cons(*x0, match l1 { Nil => l1, Cons(p2, _) => F5(x0); l1 })
  def P3Run : L := let c = 0; P3(&c, Nil)
  reject def PBlockData (x1 : &Nat) : Unit := let a0 = *x1; match a0 { Z => (), S _ => G1(x1, 1) }
  -- Q: "q0.fst was moved out"
  def Q1 (q0 : Nat × Nat) (n1 : Nat) : Nat × Nat := match q0 { Mk(p0, p1) => let a2 = match n1 { Z => λ (y4 : Nat) (y5 : ⊤ ∧ ⊤) : Unit => p0 := y4, S p6 => λ (y8 : Nat) (y9 : ⊤ ∧ ⊤) : Unit => () }; (p0, 0) }
  def Q1Run : Nat × Nat := Q1((0, 0), 0)
  -- K: "a4 was partly moved out"
  def K1 (b0 : B2) : Nat × Nat := let a4 = (0, 0); let t = match b0 { F => match a4 { Mk(p, q) => 0 }, T => let s = a4.2; 0 }; a4
  def K1Run : Nat × Nat := K1(T)
  reject def KBorrow (b0 : B2) : Nat × Nat := let a4 = (0, 0); let t = match b0 { F => G1(&a4.2, 0); 0, T => let s = a4.2; 0 }; a4
  reject def KWrite (b0 : B2) (n : Nat) : Nat := let t = match b0 { F => n := 1; 0, T => let s = n; 0 }; n
}
#eval IO.println (run "D53Residual2" D53Residual2 { d53 := true }).show

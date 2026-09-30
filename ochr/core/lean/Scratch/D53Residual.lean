import Ochr.Test
open Ochr Ochr.Test
/-! D53 acceptance after 10a7861a (fuzzer, execution oracle, `--switch +D53`: 950 cases in
10⁶, from 15,567 before). The fixes for M1/M2/M2b hold for a single stuck block. What
remained on 10a7861a, each `F` accepted and its `FRun`, a call on a ground input, rejected:
- N1, N2: a stuck block inside an arm of another stuck block moves out of a place the outer
  block's refinement did not expose (N2 is M2b one level down).
- N3: a stuck block returns a borrow into an owner while one of its arms moves another part
  of that owner. [Close] replaces the owner by a sealed program holding the returned
  borrow's loan, which hides the partial move.
- N4: an arm moves a sibling field into a sub-place of the block's own scrutinee.
- N5: a block's returned borrow whose content one arm moved out (the same body returned
  from a function, `N5b`, is rejected by the returned-borrow check).
Since ochr-core-lean 0b8a68f0 (a block's moves as effects by place, logged and replayed per
arm, composed through nested blocks; captures by mode per sub-place) each of N1–N5 is
rejected at the definition; the failing calls are kept as comments. Run with D53 on. -/
ochr D53Residual {
  -- the inner block moves (*x0).fst; the outer block splits on n1, not on *x0
  reject def N1 (x0 : &(Nat × Nat)) (n1 : Nat) : Nat := let a = match n1 { Z => match *x0 { Mk(p, _) => p }, S _ => 0 }; a
  -- "a borrow ends while its content is partly moved out ((⊥, 0))"
  -- was: def N1Run : Nat := let c = (0, 0); N1(&c, 0)
  -- M2b one level down: the inner block takes the borrow x0 whole, the outer's other arm moves *x0
  reject def N2 (x0 : &Nat) : Nat := let a = match *x0 { Z => match *x0 { Z => 0, S _ => x0; 0 }, S _ => *x0 }; a
  -- "a borrow ends while its content is partly moved out (⊥)"
  -- was: def N2Run : Nat := let c = 1; N2(&c)
  -- one block (the match on q1 is a refinement, not stuck): it returns a borrow of p2 and its
  -- Z arm moves p1, the other field of q1; q1 is read afterwards
  reject def N3 (q1 : Nat × Nat) : Nat × Nat := let a = match q1 { Mk(p1, p2) => match p2 { Z => p1; &p2, S _ => &p2 } }; q1
  -- "q1 was partly moved out"
  -- was: def N3Run : Nat × Nat := N3((0, 0))
  -- controls: the same block returning data, or returning a borrow of another owner (k), is
  -- rejected at the definition
  reject def N3Data (q1 : Nat × Nat) : Nat × Nat := let a = match q1 { Mk(p1, p2) => match p2 { Z => p1, S _ => 0 } }; q1
  reject def N3Other (q1 : Nat × Nat) (k : Nat) : Nat × Nat := let a = match q1 { Mk(p1, p2) => match p2 { Z => p1; &k, S _ => &k } }; q1
  inductive L := Nil | Cons(h : Nat, t : L)
  def AddM (x : &Nat) (y : Nat) : Unit by x := match *x { Z => *x := y, S p => AddM(&p, y) }
  -- N4: p15 := p9 moves q0.fst into (q0.snd).1; q0 is read afterwards
  reject def N4 (q0 : Nat × Nat) : Nat × Nat := (match q0 { Mk(p9, p10) => match p10 { Z => (), S p15 => p15 := p9 } }; q0)
  -- "q0 was partly moved out"
  -- was: def N4Run : Nat × Nat := N4((0, 1))
  -- N5: the block returns x0 from both arms, and the S arm moves *x0 out first
  reject def N5 (x0 : &Nat) : Unit := (let a0 = match *x0 { Z => x0, S p2 => let a3 = *x0; x0 }; AddM(a0, 0))
  -- "[Match] on *x, which was moved out"
  -- was: def N5Run : Nat := let c = 1; N5(&c); c
  reject def N5b (x0 : &Nat) : &Nat := (match *x0 { Z => x0, S p2 => let a3 = *x0; x0 })
}
#eval IO.println (run "D53Residual" D53Residual {}).show

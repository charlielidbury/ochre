import Ochr.Test
open Ochr Ochr.Test
/-! D53 acceptance: a stuck (closed-off) match hid its arms' moves from the rest of the
function, so the checker accepted functions that read moved data when run (fuzzer, execution
oracle, ochr-core-lean 55977f8e: 15,567 cases in 10⁶). Before 10a7861a each `F` below was
accepted and its call on the ground input in the comment was rejected. Since 10a7861a (a
stuck block's effect on its captures is the direct path's; erasure decided by position),
M1, M2 and M2b are rejected at the definition, like the controls `C1`/`C2`, and M3's
functions are accepted and run. Run with D53 on (it is off by default). -/
ochr D53Blocks {
  -- M1: the arm moves a field its pattern exposed (q0.fst). Was: A1((0, 0)) "q0 was partly moved out"
  reject def A1 (q0 : Nat × Nat) : Nat × Nat := let a = match q0 { Mk(p, _) => p }; q0
  -- was: A2(1) "n0 was partly moved out"
  reject def A2 (n0 : Nat) : Nat := let a = match n0 { Z => 0, S p => p }; n0
  -- M2: the arm moves a whole captured place that is not a variable (*x0). Was: B1(&0, 1)
  -- "a borrow ends while its content is partly moved out"
  reject def B1 (x0 : &Nat) (n1 : Nat) : Nat := let a = match n1 { Z => 0, S _ => *x0 }; a
  reject def B2 (q0 : Nat × Nat) (x1 : &Nat) : Nat := S(match q0 { Mk(_, _) => *x1 })
  reject def B3 (x0 : &Nat) (x1 : &Nat) : &Nat := match *x1 { Z => (), S _ => *x1 := *x0 }; x0
  -- M2b: one arm moves the borrow itself in (a whole read of x0), another moves out through
  -- it. Was: B4(&1) "a borrow ends while its content is partly moved out"
  reject def B4 (x0 : &Nat) : Nat := S((match *x0 { Z => x0; 0, S _ => *x0 }))
  -- M3 (i): the untyped J evaluated its endpoints at runtime depth. Was: J1(1, refl) "n was moved out"
  def J1 (n : Nat) (h : Eq(Nat, n, 1)) : Nat := let m = n; J(Nat, n, 1, λ (z : Nat) : Type => Nat, h, m)
  def J1Run : Nat := J1(1, refl)
  -- M3 (ii): an `Id` side writing a moved place. Was: I1(0) "cannot infer the type of the value ⊥"
  def I1 (n1 : Nat) : Nat := let m = n1; let a0 = Id(Unit, (), n1 := 0); 0
  def I1Run : Nat := I1(0)
  -- control: the same moves outside a stuck block are rejected at the definition
  reject def C1 (q0 : Nat × Nat) : Nat × Nat := match q0 { Mk(p, _) => let a = p; q0 }
  reject def C2 (x0 : &Nat) : Nat := *x0
}
#eval IO.println (run "D53Blocks" D53Blocks {}).show

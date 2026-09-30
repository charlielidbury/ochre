import Ochr.Test
open Ochr Ochr.Test
/-! A probe from the D53 prototype (copy semantics then). Under moves, the only read semantics
since 042a06f7, the double reads `Dbl`/`DblD` and the move out through a borrow `Out` are
rejected; verdicts as on ochr-core 042a06f7. -/
ochr D53Probe {
  -- (1) a double read of a borrowed Nat in one arm
  reject def Dbl (x0 : &Nat) : Nat × Nat := match *x0 { Z => (*x0, S *x0), S p1 => (0, 0) }
  reject def DblZ : Nat × Nat := (let c = 0; Dbl(&c))
  reject def DblD (x0 : &Nat) : Nat × Nat := (*x0, S *x0)
  -- (2) conditional move of an owned n1 by a closed-off block
  def Cond (n0 : Nat) (n1 : Nat) : Id Unit (match n0 { Z => (), S _ => let t = n1; () }) (let t = n1; ()) := refl
  def CondAt : Eq Nat 3 3 := (let r = Cond(0, 3); refl)
  -- (3) a move out through a borrow inside a block, borrow ends with ⊥
  reject def Out (x : &(Nat × Nat)) : Nat × Nat := match *x { Mk(a, b) => *x }
  def OutG (x : &(Nat × Nat)) : Id (Nat × Nat) (match *x { Mk(a, b) => *x }) (match *x { Mk(a, b) => *x }) := refl
  def OutUse : Nat := (let c = (1, 2); let h = OutG(&c); 0)
}
#eval IO.println (run "D53Probe" D53Probe).show

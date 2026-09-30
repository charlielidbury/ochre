import Ochr.Test
open Ochr Ochr.Test
ochr D53Probe2 {
  -- false for x ≠ &(0, 0): rejected
  reject def OutG (x : &(Nat × Nat)) : Id (Nat × Nat) (match *x { Mk(a, b) => *x }) (0, 0) := match *x { Mk(a, b) => refl }
  def OutGen (x : &(Nat × Nat)) : Prop := Id (Nat × Nat) (match *x { Mk(a, b) => *x }) (0, 0)
  def OutSplit (x : &(Nat × Nat)) : Prop := match *x { Mk(a, b) => Id (Nat × Nat) (match *x { Mk(a2, b2) => *x }) (0, 0) }
  def OutAt : Prop := (let c = (1, 2); Id (Nat × Nat) (match c { Mk(a, b) => c }) (0, 0))
  def OutAtB : Prop := (let c = (1, 2); let r = &c; Id (Nat × Nat) (match *r { Mk(a, b) => *r }) (0, 0))
}
#eval IO.println (run "D53Probe2" D53Probe2).show

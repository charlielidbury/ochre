import Ochr.Fuzz.Replay
import Ochr.Test
open Ochr Ochr.Test Ochr.Fuzz
ochr C0 {
  def Stmt (x0 : &Nat) (x1 : &Nat) (n2 : Nat) : Prop :=
    Id(Nat × Nat, (match *x0 { Z => (*x0, S(*x0)), S p1 => (*x1, *x0) }), (0, S(n2)))
}
#eval IO.println (replay C0)

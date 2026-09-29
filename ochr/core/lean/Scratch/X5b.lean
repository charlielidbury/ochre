import Ochr.Test
open Ochr Ochr.Test
ochr CX5b {
  def P1 (h : Π(x : &Nat) (y : &Nat). &Nat) : Prop := Id Nat (let a = Z; let b = Z; (let r = h(&a, &b); ()); a) Z
}
#eval IO.println (run "CX5b" CX5b).show

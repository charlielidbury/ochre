import Ochr.Fuzz.Replay
open Ochr Ochr.Fuzz
ochr CX5 {
  def PickX (x : &Nat) (y : &Nat) : &Nat := x
  def Stmt (h : Π(x : &Nat) (y : &Nat). &Nat) : Prop := Id Nat (let a = 0; let b = 0; (let r = h(&a, &b); ()); a) 0
}
#eval IO.println (replay CX5)

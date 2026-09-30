import Ochr.Examples.«00Std»
open Ochr Ochr.Test
ochr Redecl {
  reject inductive Unit := A | B
  reject inductive Nat := Zero | Succ(p : Nat)
  reject def Z : Nat := 0
  reject inductive And := X
  reject def S (n : Nat) : Nat := n
  reject inductive Prop2 := MkP(n : Nat)
}
#eval IO.println (run "Redecl" Redecl).show

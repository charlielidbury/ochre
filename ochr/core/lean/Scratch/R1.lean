import Ochr.Fuzz.Replay
import Ochr.Test
open Ochr Ochr.Fuzz Ochr.Test

ochr C5624 {
  inductive L := Nil | Cons(h : Nat, t : L)
  def Stmt (l0 : L) : Prop :=
    Id Unit (match l0 { Nil => () | Cons(p5, p6) => match p6 { Nil => () | Cons(p14, _) => p6 := l0 } }) (match l0 { Nil => () | Cons(p37, p38) => match p37 { Z => () | S p40 => l0 := Nil } })
}
#eval IO.println (replay C5624)
#eval IO.println (replay C5624 { genGlobal := true, syntacticClass := true })

ochr C354 {
  def Lie (n : Nat) : Id Nat (let c = 0; let f = match n { Z => (c := 1; λ(y : &Nat) : ⊤ => refl) | S _ => λ(y : &Nat) : ⊤ => refl }; c) 0 := refl
  def Boom : Eq Nat 1 0 := Lie(0)
}
#eval IO.println (run "C354" C354).show

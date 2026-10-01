import Ochr.Fuzz.Replay
import Ochr.Test
open Ochr Ochr.Test Ochr.Fuzz
/-! The escape class E and the vacuous class V of the v2 fuzzer, replayed (notes/fuzzer.md §v2.5). -/
ochr ClassE {
  def Stmt (q2 : Nat × Nat) : Prop :=
    Id(Prop, (let a0 = match q2 { Mk(p5, p6) => λ(y7 : Nat) (y8 : ⊤ ∧ ⊤) : Unit => q2 := q2 }; ⊤), ⊤)
}
ochr ClassV {
  def Stmt (n0 : Nat) (h1 : False) : Prop :=
    Id(Unit, (match n0 { Z => (match h1 {} : Unit), S p21 => () }), (match h1 {} : Unit))
}
#eval IO.println (replay ClassE)
#eval IO.println (replay ClassV)
#eval IO.println (replay ClassV { zeroArmStuck := false })
-- E without a write in the λ: the λ only reads the scrutinee
ochr ClassE2 {
  def Stmt (q2 : Nat × Nat) : Prop :=
    Id(Prop, (let a0 = match q2 { Mk(p5, p6) => λ(y7 : Nat) : Nat => p5 }; ⊤), ⊤)
}
#eval IO.println (replay ClassE2)
-- E through a codomain that reads the captured value
ochr ClassE3 {
  def TN (n : Nat) : Type := match n { Z => Nat, S _ => Nat }
  def Stmt (q2 : Nat × Nat) : Prop :=
    Id(Prop, (let a0 = match q2 { Mk(p5, p6) => λ(y7 : Nat) : TN(p5) => (match p5 { Z => 0, S _ => 1 } : TN(p5)) }; ⊤), ⊤)
}
#eval IO.println (replay ClassE3)
-- E with a real write in the arm (not R2's λ-write)
ochr ClassE4 {
  def Stmt (q2 : Nat × Nat) : Prop :=
    Id(Prop, let a0 = match q2 { Mk(p5, p6) => let f = (λ(y7 : Nat) : Nat => p5); q2 := (1, 1); f }; ⊤, ⊤)
}
#eval IO.println (replay ClassE4)

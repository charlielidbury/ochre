import Ochr.Fuzz.Replay
open Ochr Ochr.Fuzz
/-! The fuzzer's refinement order (seed 10, case 83896 of the 10⁶ baseline at b349bd76).
Substituting `x0 := 0` first unseals the statement's block, whose `Clr(&n2)` then runs while
`n2` is still abstract and is generalised to a fresh σ; substituting `n2 := 0` afterwards
never reached that σ, and the comparison filled it with an arbitrary value (`n2` ends as 1
against the direct run's 0). An oracle artefact: the checker proves such statements in either
split order. `refineValS` now substitutes to a fixpoint; both blocks replay with no finding. -/
ochr RefineOrder {
  def Clr (x : &Nat) : Unit := match *x { Z => (), S p => p := Z }
  def Stmt (x0 : Nat) (n1 : Nat) (n2 : Nat) : Prop :=
    Id Prop (match x0 { Z => Clr(&n2); Id Nat (match n2 { Z => n1, S p4 => 0 }) 0, S p5 => False }) False
}
-- the shrunk case as found: a borrowed scrutinee, `Clr` called through a local alias
ochr RefineOrderAlias {
  def Clr (x : &Nat) : Unit := match *x { Z => (), S p => p := Z }
  def Stmt (x0 : &Nat) (n1 : Nat) (n2 : Nat) : Prop :=
    Id Prop (match *x0 { Z => (let g0 = Clr; g0(&n2)); Id Nat (match n2 { Z => n1, S p4 => 0 }) 0, S p5 => False }) False
}
#eval IO.println (replay RefineOrder)
#eval IO.println (replay RefineOrderAlias)
#guard replayKeys RefineOrder == []
#guard replayKeys RefineOrderAlias == []

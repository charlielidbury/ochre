import Ochr.Fuzz.Replay
import Ochr.Test
open Ochr Ochr.Test Ochr.Fuzz
/-! R1's residual after ef1195ff (1 case in 10⁶, seed 5 case 38531): an `Id` formed in a sealed
program's re-run about a place reached through a returned borrow. Fixed by 06da7a2c (the owner
is typed by what the observation read): `Split` is accepted. -/
ochr R1Residual {
  def R1 (x0 : &Nat) : &Nat := match *x0 { Z => &*x0, S p3 => &p3 }
  def Stmt (x0 : &Nat) (x1 : &Nat) : Prop :=
    Id Prop (match *x0 { Z => let a6 = R1(x1); Id Unit (*x0 := *a6) (), S p7 => ⊤ }) ⊤
  -- a true statement (the two sides differ only in the `S` arm, `⊤` against `⊤ ∧ ⊤`), proved by
  -- splitting: the `Z` arm re-normalises the sealed program, and typing its `Id` failed
  def Split (x0 : &Nat) (x1 : &Nat) : Id Prop (match *x0 { Z => let a6 = R1(x1); Id Unit (*x0 := *a6) (), S p7 => ⊤ }) (match *x0 { Z => let a6 = R1(x1); Id Unit (*x0 := *a6) (), S p7 => ⊤ ∧ ⊤ }) := (
    match *x0 { Z => refl, S _ => refl }
  )
}
#eval IO.println (run "R1Residual" R1Residual).show

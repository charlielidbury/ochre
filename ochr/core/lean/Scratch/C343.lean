import Ochr.Fuzz.Replay
import Ochr.Test
open Ochr Ochr.Test Ochr.Fuzz
ochr C343 {
  def Stmt (q0 : Nat × Nat) : Prop :=
    Id (Nat × Nat) (match q0 { Mk(p0, p1) => match p0 { Z => q0, S p7 => q0 := Mk(p1, p1); q0 } }) (match q0 { Mk(p15, p16) => match p16 { Z => p16 := 0; (1, 0), S _ => q0 } })
  def Split (q0 : Nat × Nat) : Prop :=
    match q0 { Mk(a, b) => Id (Nat × Nat) (match q0 { Mk(p0, p1) => match p0 { Z => q0, S p7 => q0 := Mk(p1, p1); q0 } }) (match q0 { Mk(p15, p16) => match p16 { Z => p16 := 0; (1, 0), S _ => q0 } }) }
  def R1 (q0 : Nat × Nat) : Prop :=
    match q0 { Mk(a, b) => Id (Nat × Nat) q0 (match q0 { Mk(p15, p16) => match p16 { Z => p16 := 0; (1, 0), S _ => q0 } }) }
  def R2 (q0 : Nat × Nat) : Prop :=
    match q0 { Mk(a, b) => Id Nat 0 (match q0 { Mk(p15, p16) => match p16 { Z => p16 := 0; 1, S _ => 0 } }) }
  def R3 (q0 : Nat × Nat) : Prop :=
    match q0 { Mk(a, b) => Id Nat 0 (match b { Z => b := 0; 1, S _ => 0 }) }
  def R4 (q0 : Nat × Nat) : Nat :=
    match q0 { Mk(a, b) => match b { Z => b := 0; 1, S _ => 0 } }
  def R5 (q0 : Nat × Nat) : Nat :=
    match q0 { Mk(a, b) => let r = match b { Z => b := 0; 1, S _ => 0 }; r }
}
#eval IO.println (run "C343" C343).show

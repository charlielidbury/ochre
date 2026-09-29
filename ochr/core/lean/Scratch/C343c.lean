import Ochr.Test
open Ochr Ochr.Test
ochr C343c {
  def Split (q0 : Nat × Nat) : Prop :=
    match q0 { Mk(a, b) => Id (Nat × Nat) (match q0 { Mk(p0, p1) => match p0 { Z => q0, S p7 => q0 := Mk(p1, p1); q0 } }) (match q0 { Mk(p15, p16) => match p16 { Z => p16 := 0; (1, 0), S _ => q0 } }) }
  def S2 (q0 : Nat × Nat) : Prop :=
    match q0 { Mk(a, b) => Id Nat (match a { Z => 0, S p7 => q0 := (b, b); 0 }) (match b { Z => b := 0; 1, S _ => 0 }) }
  def S3 (q0 : Nat × Nat) : Prop :=
    match q0 { Mk(a, b) => Id Nat (match a { Z => 0, S p7 => q0 := (1, 1); 0 }) (match b { Z => 1, S _ => 0 }) }
  def S4 (q0 : Nat × Nat) : Prop :=
    match q0 { Mk(a, b) => Id Nat (match a { Z => 0, S p7 => q0 := (1, 1); 0 }) (match b { Z => b := 0; 1, S _ => 0 }) }
  def S5 (q0 : Nat × Nat) : Prop :=
    match q0 { Mk(a, b) => Id Nat (match a { Z => 0, S p7 => a := 1; 0 }) (match b { Z => b := 0; 1, S _ => 0 }) }
}
#eval IO.println (run "C343c" C343c).show
#eval IO.println ((run "C343c" C343c { trace := true }).showTrace "Split")

import Ochr.Test
open Ochr Ochr.Test
ochr C343b {
  def L1 (q0 : Nat × Nat) : Prop :=
    match q0 { Mk(a, b) => Id (Nat × Nat) (match q0 { Mk(p0, p1) => match p0 { Z => q0, S p7 => q0 := Mk(p1, p1); q0 } }) q0 }
  def L2 (q0 : Nat × Nat) : Nat × Nat :=
    match q0 { Mk(a, b) => let r = match q0 { Mk(p0, p1) => match p0 { Z => q0, S p7 => q0 := Mk(p1, p1); q0 } }; r }
  def L3 (q0 : Nat × Nat) : Nat × Nat :=
    match q0 { Mk(a, b) => let r = match a { Z => q0, S p7 => q0 := Mk(b, b); q0 }; r }
  def L4 (q0 : Nat × Nat) : Nat × Nat :=
    match q0 { Mk(a, b) => let r = match a { Z => 0, S p7 => q0 := Mk(b, b); 0 }; q0 }
  def L5 (a0 : Nat) (b0 : Nat) : Nat × Nat :=
    let q0 = (a0, b0); match q0 { Mk(a, b) => let r = match a { Z => 0, S p7 => q0 := Mk(b, b); 0 }; q0 }
  def L6 (a0 : Nat) (b0 : Nat) : Nat × Nat :=
    let q0 = (a0, b0); let r = match q0.1 { Z => 0, S p7 => q0 := (1, 1); 0 }; q0
}
#eval IO.println (run "C343b" C343b).show
#eval IO.println ((run "C343b" C343b { trace := true }).showTrace "L4")

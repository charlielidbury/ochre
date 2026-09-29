import Ochr.Test
open Ochr Ochr.Test
/-! R6: `Id`'s conjunction lists the observed owners in the order of Ω. Closing off a block
orders them by the block's captures instead, so the same statement computes to conjunctions
in different orders on the two paths. Seen by the fuzzer only with D52 off (with injectivity
the ground equations compute to True/False); on the default rules it is an incompleteness
for open terms. -/
ochr R6Order {
  reject def Direct (n0 : Nat) (x2 : &Nat) : Id Prop (match n0 { Z => Id Unit (*x2 := 1) (n0 := *x2), S p2 => ⊤ })
      (match n0 { Z => Eq Nat 1 *x2 ∧ Eq Nat 0 *x2, S p2 => ⊤ }) := match n0 { Z => refl, S _ => refl }
  def Swapped (n0 : Nat) (x2 : &Nat) : Id Prop (match n0 { Z => Id Unit (*x2 := 1) (n0 := *x2), S p2 => ⊤ })
      (match n0 { Z => Eq Nat 0 *x2 ∧ Eq Nat 1 *x2, S p2 => ⊤ }) := match n0 { Z => refl, S _ => refl }
  def AtZero (x2 : &Nat) : Id Prop (let n0 = 0; Id Unit (*x2 := 1) (n0 := *x2)) (Eq Nat 1 *x2 ∧ Eq Nat 0 *x2) := refl
}
#eval IO.println (run "R6Order" R6Order).show

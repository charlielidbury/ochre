import Ochr.Test
open Ochr Ochr.Test
/-! A match on a scrutinee whose type is a stuck family application (`TG(n)`, neutral at the
generic call) takes its constructors from the patterns, not the type (the scrutTyped rule
covers computed types that evaluate; a stuck one is not checked). `M2` is accepted, and
its call at `n = 1`, where `TG(1) = B2`, fails at runtime: an accepted function that goes
wrong. Found while testing the E family with a dependent codomain (reviewer-6 W10), on
ochr-core 1f07e619 (D53 on). As a proof (`M3`) the shape is rejected, so no `False` from
it here. Verdicts as they stand today: the `def`s are accepted, `M2Run` is rejected. -/
ochr StuckScrutType {
  inductive B2 := F | T
  def TG (n : Nat) : Type := match n { Z => Nat, S _ => B2 }
  def HB (n : Nat) : TG(n) := match n { Z => 0, S _ => F }
  def M2 (n : Nat) (h : Π(n : Nat). TG(n)) : Nat := (let x = h(n); match x { Z => 0, S _ => 1 })
  -- "[Match] on a non-Nat value F"
  reject def M2Run : Nat := M2(1, HB)
  reject def M3 (n : Nat) (h : Π(n : Nat). TG(n)) : Id Nat (let x = h(n); match x { Z => 0, S _ => 1 }) 0 := refl
}
#eval IO.println (run "StuckScrutType" StuckScrutType).show

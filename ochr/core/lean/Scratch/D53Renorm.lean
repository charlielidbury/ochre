import Ochr.Test
open Ochr Ochr.Test
/-! D53 acceptance, class RN: a stuck block formed inside a type (an `Id` side, erased, where
reads copy) closes off to a sealed program; a [Split] re-normalises it as runtime code, where
the same reads move, so a double read errors. True statements proved by splitting are rejected. -/
ochr D53Renorm {
  def Twice (n : Nat) : Prop := Id (Nat × Nat) (match n { Z => (n, n), S p => (p, p) }) (match n { Z => (0, 0), S p => (p, p) })
  -- true (both sides are (0, 0) at Z and (p, p) at S p), proved by splitting n
  def TwiceSplit (n : Nat) : Id (Nat × Nat) (match n { Z => (n, n), S p => (p, p) }) (match n { Z => (0, 0), S p => (p, p) }) := (
    match n { Z => refl, S _ => refl }
  )
  -- the same with the duplication written with clone
  def TwiceClone (n : Nat) : Id (Nat × Nat) (match n { Z => (clone(n), n), S p => (clone(p), p) }) (match n { Z => (0, 0), S p => (p, p) }) := (
    match n { Z => refl, S _ => refl }
  )
}
#eval IO.println (run "D53Renorm" D53Renorm { d53 := true }).show
#eval IO.println (run "D53Renorm" D53Renorm { d53 := true, moves := false }).show

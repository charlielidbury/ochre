import Ochr.Examples.Nat
import Ochr.Examples.Fixtures
open Ochr.Test

/-!
# Probe (docs/30, "After D84"): a counterexample to D84's resource lemma, through [Join]'s grain

`IdP : Id(Nat × Nat, (Z, Z), gp(()))` is proved by `refl`, yet `let v = □; let a = v.0; v.1` is
accepted with `(Z, Z)` and rejected with `gp(())`: a field step is kept only through a declared
type that reads as a one-constructor inductive not computed by a match (`jdGrain`), and `gp`'s
codomain `TP(0)` is computed by a match, so moving `v.0` moves `v` whole.
Run: `lake env lean ../probes/idaudit/R02_DeclGrain.lean` from `ochr/core/lean`, after
`lake build Ochr.Examples.Nat Ochr.Examples.Fixtures`. Expected output on main 7ae8cf00: exactly
three errors, the flipped controls, `FlipIdP` and `FlipPT` ("expected rejection, but accepted")
and `FlipPU` ("[Match] on v, which was moved out"). Any other error means a verdict changed.
-/
-- Resource lemma attack through [Join]'s grain: a field step is kept only through a declared
-- type that reads as a one-constructor inductive not computed by a match (jdGrain).
ochr R02DeclGrain uses Nats {
  def TP (n : Nat) : Type := match n { Z => Nat × Nat, S _ => Nat × Nat }
  def gp (u : Unit) : TP(0) := (Z, Z)
  def IdP : Id(Nat × Nat, (Z, Z), gp(())) := refl
  reject def FlipIdP : Id(Nat × Nat, (Z, Z), gp(())) := refl
  -- the context `let v = □; let a = v.0; v.1`
  def PT (u : Unit) : Nat := (let v = (Z, Z); let a = v.0; v.1)
  reject def PU (u : Unit) : Nat := (let v = gp(()); let a = v.0; v.1)
  reject def FlipPT (u : Unit) : Nat := (let v = (Z, Z); let a = v.0; v.1)
  def FlipPU (u : Unit) : Nat := (let v = gp(()); let a = v.0; v.1)
}

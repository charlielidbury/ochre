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

Since D93 the counterexample is gone: a one-constructor match (the projection `v.0`) has no join,
so `let a = v.0` moves `v.0` and nothing else, whatever `v`'s declared type reads as, and `PU` is
accepted as `PT` is (as Rust accepts `let a = v.0; v.1`). The grain still decides what a match with
several arms drops at its join. Expected output now: exactly three errors, the flipped controls
`FlipIdP`, `FlipPT` and `FlipPU` ("expected rejection, but accepted").
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
  def PU (u : Unit) : Nat := (let v = gp(()); let a = v.0; v.1)
  reject def FlipPT (u : Unit) : Nat := (let v = (Z, Z); let a = v.0; v.1)
  reject def FlipPU (u : Unit) : Nat := (let v = gp(()); let a = v.0; v.1)
}

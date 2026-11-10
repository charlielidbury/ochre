import Ochr.Examples.Nat
import Ochr.Examples.Fixtures
open Ochr.Test
ochr A6 uses Nats {
  inductive NBox (k : Nat) := MkNBox(v : Nat)
  def TyU (A : Type) : Unit := ()
  def TFn (n : Nat) : Type := NBox(n)
  -- a value inside a type argument: does the type-state count it, and does the run move it?
  def T1 (n : Nat) : Id(Unit, TyU(TFn(n)), (let z = n; ())) := refl
  def T1ctx (n : Nat) : Nat := (TyU(TFn(n)); n)
  def T2 (n : Nat) : Id(Unit, TyU(NBox(n)), (let z = n; ())) := refl
  -- a value inside a let annotation and an ascription
  def T3 (n : Nat) : Id(Unit, (let b : NBox(n) = MkNBox[clone(n)](0); ()), (let z = n; ())) := refl
}
#eval (run "A6" A6).rows.forM fun r => IO.println s!"{r.name}: {match r.verdict with | .accepted => "accepted" | .rejected m _ => m | .undecided m => m}"

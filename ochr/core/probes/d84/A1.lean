import Ochr.Examples.Nat
import Ochr.Examples.Fixtures
open Ochr.Test
ochr A1 uses Nats {
  inductive Pr := MkPr(a : Nat, b : Nat)
  def TF (n : Nat) : Type := match n { Z => Pr, S _ => Pr }
  -- G1: a direct projection (no match, no join) of a value of a type a match computes
  def D1 (k : Nat) (x : TF(k)) : Prop := Id(Unit, (let r = &x; let y = x.0; ()), (let r = &x; let z = x; ()))
  def D1Gen (k : Nat) (x : TF(k)) : D1(k, x) := refl
  def D1Z : D1(Z, MkPr(1, 2)) := refl
  reject def D1Boom : False := match D1Gen(Z, MkPr(1, 2)) {}
  -- control: declared Pr
  def D1P (x : Pr) : Prop := Id(Unit, (let r = &x; let y = x.0; ()), (let r = &x; let z = x.0; ()))
  def D1PGen (x : Pr) : D1P(x) := refl
  -- G2: constructor parameters counted as moves by the type-state, not by the run
  inductive NBox (k : Nat) := MkNBox(v : Nat)
  def C1 (n : Nat) : Prop := Id(Unit, (let r = &n; let b = MkNBox[n](0); ()), (let r = &n; let z = n; ()))
  def C1Gen (n : Nat) : C1(n) := refl
  def C1ctxL (n : Nat) : Nat := ((let b = MkNBox[n](0); ()); n)
  -- G3: Obs-ref binding consumed by a block on both sides, different targets
  def O1 (k : Nat) (x : Nat) (z : Nat) (y : &Nat) : Prop := Id(Unit, (y := &x; match k { Z => (let t = y; ()), S _ => () }), (y := &z; match k { Z => (let t = y; ()), S _ => () }))
  def O1Gen (k : Nat) (x : Nat) (z : Nat) (y : &Nat) : O1(k, x, z, y) := refl
  -- G4: no-ending judged on the checking run (Pick ends r early at the generic call)
  def NE2 (n : Nat) (a : Nat) (b : Nat) : Prop := (let r = Pick(n, &a, &b); let w = clone(b); Id(Unit, (let c = clone(a); ()), ()))
  def NE2Gen (n : Nat) (a : Nat) (b : Nat) : NE2(n, a, b) := refl
  def NE2At (a : Nat) (b : Nat) : NE2(Z, a, b) := NE2Gen(Z, a, b)
}
#eval (run "A1" A1).rows.forM fun r => IO.println s!"{r.name}: {match r.verdict with | .accepted => "accepted" | .rejected m _ => m | .undecided m => m}"

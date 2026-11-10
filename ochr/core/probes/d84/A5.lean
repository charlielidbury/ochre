import Ochr.Examples.Nat
import Ochr.Examples.Fixtures
open Ochr.Test
ochr A5 uses Nats {
  inductive Pr := MkPr(a : Nat, b : Nat)
  def TF (n : Nat) : Type := match n { Z => Pr, S _ => Pr }
  def F (n : Nat) : Unit := ()
  -- direct projection on a value of a computed type, both sides alike but read differently afterwards
  def D2 (k : Nat) (x : TF(k)) : Prop := Id(Unit, (let r = &x; let y = x.0; ()), (let r = &x; F(x.0)))
  def D2Gen (k : Nat) (x : TF(k)) : D2(k, x) := refl
  reject def D2Boom : False := match D2Gen(Z, MkPr(1, 2)) {}
  def D2At (x : Pr) : D2(Z, x) := refl
  -- direct move of x.0 on one side, a match-arm move (grain: whole) on the other, both TS {x}?
  def D3 (k : Nat) (x : TF(k)) : Prop := Id(Unit, (let r = &x; match k { Z => F(x.0), S _ => F(x.0) }), (let r = &x; F(x.0)))
  def D3Gen (k : Nat) (x : TF(k)) : D3(k, x) := refl
  -- a side that returns a partly moved value
  def R1 (q : Pr) : Prop := Id(Pr, (let y = q.0; q), (let y = q.0; q))
  def R1Gen (q : Pr) : R1(q) := refl
  reject def R1Boom : False := match R1Gen(MkPr(1, 2)) {}
}
#eval (run "A5" A5).rows.forM fun r => IO.println s!"{r.name}: {match r.verdict with | .accepted => "accepted" | .rejected m _ => m | .undecided m => m}"

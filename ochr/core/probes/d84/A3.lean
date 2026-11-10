import Ochr.Examples.Nat
import Ochr.Examples.Fixtures
open Ochr.Test
ochr A3 uses Nats {
  def Pick (n : Nat) (a : &Nat) (b : &Nat) : &Nat := match n { Z => a, S _ => b }
  def F (n : Nat) : Unit := ()
  -- no-ending on the checking run: r ends at clone(b) symbolically, but not at n = 0
  def NE2 (n : Nat) (a : Nat) (b : Nat) : Prop := (let r = Pick(n, &a, &b); let w = clone(b); Id(Unit, (let c = clone(a); ()), ()))
  def NE2Gen (n : Nat) (a : Nat) (b : Nat) : NE2(n, a, b) := refl
  def NE2At (a : Nat) (b : Nat) : NE2(Z, a, b) := NE2Gen(Z, a, b)
  def NE2AtRefl (a : Nat) (b : Nat) : NE2(Z, a, b) := refl
  -- Obs-ref, then a block consumes the binding on one side only
  reject def O2 (k : Nat) (x : Nat) (y : &Nat) : Id(Unit, (y := &x; match k { Z => (let t = y; ()), S _ => () }), (y := &x; ())) := refl
  -- J's term with a closure capturing x, under a join, against a plain move
  def J1 (k : Nat) (x : Nat) : Prop := Id(Unit, (let r = &x; match k { Z => J(Nat, 0, 0, λ(z : Nat) : Type => Unit, refl, (let f = (λ(u : Unit) : Unit => F(x)); ())), S _ => () }), (let r = &x; let y = x; ()))
  def J1Gen (k : Nat) (x : Nat) : J1(k, x) := refl
  reject def J1Boom : False := match J1Gen(S(Z), Z) {}
  def J1At1 (x : Nat) : J1(S(Z), x) := refl
  -- eq(⊥,⊥) through trans and symm: both sides move x on every path
  def T1 (k : Nat) (x : Nat) (h : Id(Unit, (let r = &x; match k { Z => F(x), S _ => () }), (let r = &x; F(x)))) : Id(Unit, (let r = &x; F(x)), (let r = &x; match k { Z => F(x), S _ => () })) := symm(h)
  def T2 (k : Nat) (x : Nat) : Id(Unit, (let r = &x; match k { Z => F(x), S _ => () }), (let r = &x; F(x))) := refl
  -- the over-counted constructor parameter inside an arm: the join drops n on both paths
  inductive NBox (k : Nat) := MkNBox(v : Nat)
  def P1 (k : Nat) (n : Nat) : Prop := Id(Unit, (let r = &n; match k { Z => (let b = MkNBox[n](0); ()), S _ => () }), (let r = &n; let z = n; ()))
  def P1Gen (k : Nat) (n : Nat) : P1(k, n) := refl
  reject def P1Boom : False := match P1Gen(Z, Z) {}
  def P1At0 (n : Nat) : P1(Z, n) := refl
}
#eval (run "A3" A3).rows.forM fun r => IO.println s!"{r.name}: {match r.verdict with | .accepted => "accepted" | .rejected m _ => m | .undecided m => m}"

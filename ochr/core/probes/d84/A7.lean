import Ochr.Examples.Nat
import Ochr.Examples.Fixtures
open Ochr.Test
ochr A7 uses Nats {
  inductive Pr := MkPr(a : Nat, b : Nat)
  -- left open at a field, through a join, against a direct move of the same field
  def L1 (k : Nat) (y : &Pr) : Prop := Id(Unit, match k { Z => (let a = (*y).0; ()), S _ => () }, (let a = (*y).0; ()))
  def L1Gen (k : Nat) (y : &Pr) : L1(k, y) := refl
  def L1At1 (y : &Pr) : L1(S(Z), y) := refl
  -- flipped: the other field on the right
  reject def L2 (k : Nat) (y : &Pr) : Id(Unit, match k { Z => (let a = (*y).0; ()), S _ => () }, (let a = (*y).1; ())) := refl
  -- left open whole through the join vs a field directly
  reject def L3 (k : Nat) (y : &Pr) : Id(Unit, match k { Z => (let a = *y; ()), S _ => () }, (let a = (*y).0; ())) := refl
}
#eval (run "A7" A7).rows.forM fun r => IO.println s!"{r.name}: {match r.verdict with | .accepted => "accepted" | .rejected m _ => m | .undecided m => m}"

import Ochr.Examples.Nat
import Ochr.Examples.Fixtures
open Ochr.Test
ochr A4 uses Nats {
  def UU (n : Nat) : Type := match n { Z => Unit, S _ => Unit }
  -- Obs-ref through a borrow of Unit: the written σ may be η-normalised to (), hiding the target
  def RU (x1 : Unit) (x2 : Unit) (y : &Unit) : Id(Unit, (y := &x1; ()), (y := &x2; ())) := refl
  def RUL (x1 : Unit) (x2 : Unit) (y : &Unit) : Unit := ((y := &x1; ()); let w = clone(x2); *y := ())
  def RUR (x1 : Unit) (x2 : Unit) (y : &Unit) : Unit := ((y := &x2; ()); let w = clone(x2); *y := ())
  -- the same through a type function reading as Unit
  def RUU (n : Nat) (x1 : UU(n)) (x2 : UU(n)) (y : &UU(n)) : Id(Unit, (y := &x1; ()), (y := &x2; ())) := refl
  -- control: Nat
  reject def RN (x1 : Nat) (x2 : Nat) (y : &Nat) : Id(Unit, (y := &x1; ()), (y := &x2; ())) := refl
}
#eval (run "A4" A4).rows.forM fun r => IO.println s!"{r.name}: {match r.verdict with | .accepted => "accepted" | .rejected m _ => m | .undecided m => m}"

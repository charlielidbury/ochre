import Ochr.Examples.Nat
import Ochr.Examples.Fixtures
open Ochr.Test
ochr A2 uses Nats {
  inductive NBox (k : Nat) := MkNBox(v : Nat)
  -- well formed (both sides "move" n by the type-state) and proved, but only the right side moves n
  def CP (n : Nat) : Id(Unit, (let b = MkNBox[n](0); ()), (let z = n; ())) := refl
  def CL (n : Nat) : Nat := ((let b = MkNBox[n](0); ()); n)
  reject def CR (n : Nat) : Nat := ((let z = n; ()); n)
  -- flipped control: the same Id with n moved on the left too is accepted, its context rejected on both
  def CPok (n : Nat) : Id(Unit, (let b = MkNBox[clone(n)](0); let z = n; ()), (let z = n; ())) := refl
}
#eval (run "A2" A2).rows.forM fun r => IO.println s!"{r.name}: {match r.verdict with | .accepted => "accepted" | .rejected m _ => m | .undecided m => m}"

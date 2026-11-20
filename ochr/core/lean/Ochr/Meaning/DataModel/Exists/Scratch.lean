import Ochr.Examples.Nat
open Ochr.Test
namespace Ochr.Meaning.DataModel.Exists.Scratch
ochr PropNest2 uses Nats {
  inductive PB2 (P : Prop) := MkPB2(x : P)
  inductive D3 (n : Nat) : Prop := D3Z | D3S(w : PB2(D3(n)))
  inductive D4 := D4Z | D4S(w : PB2(Eq(Nat, 0, 0)))
  inductive PBox (P : Prop) : Prop := MkPBox(x : P)
  inductive D5 : Prop := D5Z | D5S(w : PBox(D5))
  inductive D6 := D6Z | D6S(w : PB2(D5))
}
#eval IO.println (run "PropNest2" PropNest2).show
end Ochr.Meaning.DataModel.Exists.Scratch

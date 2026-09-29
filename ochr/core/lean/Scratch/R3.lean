import Ochr.Fuzz.Replay
import Ochr.Test
open Ochr Ochr.Fuzz Ochr.Test

ochr C6232 {
  -- the [Split] path re-normalises the sealed block with the untyped machine, which runs
  -- the ascribed proof's write; the instance evaluates the same match typed, which erases it
  def LieA (n : Nat) : Id Nat (match n { Z => let c = 5; let a : ⊤ = (c := 0; let e = refl; e); c | S _ => 0 }) 0 :=
    match n { Z => refl | S _ => refl }
  def BoomA : Eq Nat 5 0 := LieA(0)
}
#eval IO.println (run "C6232" C6232).show
#eval IO.println (run "C6232+fix" C6232 { proofByValue := true }).show

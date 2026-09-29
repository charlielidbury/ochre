import Ochr.Test
open Ochr Ochr.Test
ochr D53Renorm3 {
  -- a proof: its split re-normalises the goal in erased mode (reads copy): accepted
  def PrfSplit (n : Nat) : Id (Nat × Nat) (match n { Z => (n, n), S p => (p, p) }) (match n { Z => (0, 0), S p => (p, p) }) := (
    match n { Z => refl, S _ => refl }
  )
  -- a data function with the same statement as a hypothesis: its split refines h's stored type
  -- at runtime depth, where the sealed program's double read moves
  def DataSplit (n : Nat) (h : Id (Nat × Nat) (match n { Z => (n, n), S p => (p, p) }) (match n { Z => (0, 0), S p => (p, p) })) : Nat := (
    match n { Z => 0, S _ => 1 }
  )
  def DataSplitNoH (n : Nat) : Nat := match n { Z => 0, S _ => 1 }
}
#eval IO.println (run "D53Renorm3" D53Renorm3).show

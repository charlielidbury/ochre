import Ochr.Examples.«19Uninit»
open Ochr Ochr.Test Ochr.Surface
def flipsUninit (name : String) (b : Block) (base alt : Config) : List String :=
  let r := run name b base
  let r' := run name b alt
  (r.rows.zip r'.rows).filterMap fun (x, y) =>
    if x.verdict.ok != y.verdict.ok then some s!"{name}.{x.name}:{if y.verdict.ok then "accepted" else "rejected"}" else none
#eval flipsUninit "Untagged" Untagged { uninitTypes := true } {}
#eval flipsUninit "LentProofs" LentProofs { uninitTypes := true, lentProofs := true } { uninitTypes := true }
#eval flipsUninit "MoveEmpty" MoveEmpty { uninitTypes := true } { uninitTypes := true, moveEmpty := true }
#eval flipsUninit "UVec" UVec { uninitTypes := true, lentProofs := true } { uninitTypes := true }
#eval flipsUninit "UVec" UVec { uninitTypes := true, lentProofs := true } { uninitTypes := true, lentProofs := true, moveEmpty := true }

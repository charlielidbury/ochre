import Ochr.Examples.Nat
import Ochr.Examples.Fixtures

/-! # Probe helpers for the conversion lane's attacks (`Conv/Attack*.lean`) -/

open Ochr Ochr.Test

namespace Ochr.Meaning.Conv

/-- Each row's name and verdict, for reading a probe's result. -/
def showV (rep : Report) : List String := rep.rows.map fun r =>
  r.name ++ ": " ++ (match r.verdict with
    | .accepted => "ACCEPTED" | .rejected m _ => "rejected: " ++ m | .undecided m => "undecided: " ++ m)

end Ochr.Meaning.Conv

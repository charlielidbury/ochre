import Ochr.Examples.«00Std»
open Ochr Ochr.Test
ochr MinW uses Std {
  def F (x : Word) : Word := x
}
#eval (run "MinW" MinW { uninitTypes := true }).rows.map fun r => (r.name, r.verdict.ok)
#eval (run "Std" Std { uninitTypes := true }).rows.filter (fun r => !r.verdict.ok) |>.map fun r => (r.name, match r.verdict with | .accepted => "" | .rejected m _ => m)

import Ochr.Examples.«19Uninit»
open Ochr Ochr.Test Ochr.Surface
#eval ((run "LentProofs" LentProofs { uninitTypes := true }).rows.filter (·.name == "GetP")).map fun r => match r.verdict with | .accepted => "" | .rejected m _ => m

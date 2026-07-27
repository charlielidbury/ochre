import Dllbc.Tests.S19Partition

open Dllbc
open Dllbc.Tests.S19Partition
open Dllbc.Tests.S17Spec (nthS nth2S swapSN)

@[noinline] def runCheck (_ : Unit) : String :=
  match Dllbc.checkFn [nthS, nth2S, swapSN, partScanRange, quicksort] quicksort with
  | .ok _ => "quicksort OK"
  | .error e => "ERR: " ++ e.take 300

def main : IO Unit := do
  let t0 ← IO.monoMsNow
  let s ← IO.lazyPure (fun _ => runCheck ())
  IO.println s
  let t1 ← IO.monoMsNow
  IO.println s!"elapsed: {t1 - t0} ms"

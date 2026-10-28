import Scratch.TotalProbe.Partial
import Scratch.TotalProbe.Structural

/-! Phase 1b probe: compiled timing of `Partial` against `Structural`. Run it with a temporary
`lean_exe totalprobe where root := `Scratch.TotalProbe.Main` (and a `lean_lib` for the two
modules) in lakefile.lean. -/
open Ochr

def runM' {α} (x : M α) : Except String α :=
  match ((x.run { fuel := 1000000000 }).run.run #[]).1 with
  | .ok (a, _) => .ok a
  | .error (.error m _) => .error m
  | .error _ => .error "stuck"

def bench (name : String) (k : Nat → M Nat) (reps depth : Nat) : IO Unit := do
  let t0 ← IO.monoMsNow
  let mut acc := 0
  for i in [0:reps] do
    match runM' (k (depth + i % 3)) with
    | .ok v => acc := acc + v
    | .error e => throw (IO.userError e)
  let t1 ← IO.monoMsNow
  IO.println s!"{name}: {t1 - t0} ms (acc {acc})"

def main : IO Unit := do
  for _ in [0:3] do
    bench "partial   " (fun n => TotalProbe.Partial.f0 n [1, 2, 3]) 300 10000
    bench "structural" (fun n => TotalProbe.Structural.f0 (n + 1) n [1, 2, 3]) 300 10000

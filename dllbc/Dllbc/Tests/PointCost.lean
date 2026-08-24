import Dllbc
open Dllbc

/-!
A timing harness for point-delta recording (docs/17): times the flagship
checks with recording on and off and reports the delta volume between them.
The array flagship gets the full treatment because recording hangs off
`refineSym`, which fires during array place evaluation, so it is the program
that actually exercises the checker's recording path.

Not in the default build target — nothing imports this module, so `lake
build` does not build it. Run it directly with
`lake build Dllbc.Tests.PointCost` (~30 s, dominated by the checks themselves).
-/

def runN (n : Nat) (pt : Bool) (t : Term) : Nat := Id.run do
  let mut acc := 0
  for _ in [0:n] do
    acc := acc + (match checkProgramHover t none pt with
      | .ok (a, b) => a.length + b.length
      | .error _ => 0)
  return acc
-- `IO.lazyPure` is what FORCES the work inside the timed region. A plain
-- `let r := f ()` is a lazy binding: the earlier version of this harness timed
-- an unevaluated thunk and reported 0ms for work that actually took minutes.
def timeIt (label : String) (f : Unit → Nat) : IO Unit := do
  let t0 ← IO.monoMsNow
  let r ← IO.lazyPure (fun _ => f ())
  let t1 ← IO.monoMsNow
  IO.println s!"{label}: {t1-t0}ms  (sum {r})"
/-- The replay half: what one hover costs. `factsAt` replays the deltas up to a
    point and reads a binder out — the work moved from recording to reading.
    Asked at every statement key in the stream, the worst case a reader can
    produce by hovering everything. -/
def replayAll (paths : List (List PointDelta)) : Nat := Id.run do
  let keys := (paths.flatten.filterMap (fun d => d.stmtKey))
  let mut n := 0
  for k in keys do
    for p in paths do
      for d in p do
        match d.change with
        | .bound x _ | .set x _ => n := n + (factsAt paths k x).length
        | .refine _ _ => pure ()
  return n

-- The array flagship is SEEDED since docs/21's pilot; this harness's walker
-- (`checkProgramHover`) is unseeded, so the list flagship is the remaining
-- closed subject. The seeded chain's hover ledgers ride `modulePathsD` and are
-- exercised (and pinned) in the flagship file's own guarded `show`.
#eval show IO Unit from do
  let l := Tests.S23Direct.flagship
  match checkProgramHover l none true with
  | .ok (_, pts) =>
    let keys := (pts.flatten.filterMap (fun d => d.stmtKey))
    IO.println s!"list: {pts.length} path(s), {pts.flatten.length} deltas, {keys.length} keyed"
    timeIt "list replay: every binder at every key" (fun _ => replayAll pts)
  | .error _ => IO.println "list: rejected"
  timeIt "list     x50 point=false" (fun _ => runN 50 false l)
  timeIt "list     x50 point=true " (fun _ => runN 50 true  l)

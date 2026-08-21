import Dllbc

/-! # The divergence sweep (docs/19 v2, hover simplification's evidence)

    NOT in the build. Claim under test: with the join unconditional, NO point
    in the corpus yields two DISTINCT rendered hover answers — post-seam points
    are one joined path, in-arm points are that arm's single path, and
    shared-prefix points repeat with identical deltas. If this sweep prints a
    divergence, that is a FINDING — stop and record it; do not delete the
    multi-answer rendering. -/

namespace Dllbc.Tests.MatchJoinSweep
open Dllbc

/-- One program's sweep: every (statement key × binder) point, both plain and
    entry readings, plus the letTypes-side disagreement flag. Returns the
    divergent points, rendered. -/
def sweep (name : String) (t : Term) : IO Unit := do
  match checkProgramHover t none true with
  | .error _ => IO.println s!"{name}: REJECTED (not part of the claim)"
  | .ok (lets, pts) =>
    -- the letTypes side: `letIndex`-equivalent disagreement count
    let mut letDiffs := 0
    let mut seen : List (Nat × String × Option Term × Val) := []
    for e in lets do
      match seen.find? (fun q => q.1 == e.binder.id && q.2.1 == e.binder.name) with
      | none => seen := (e.binder.id, e.binder.name, e.ty?, e.val) :: seen
      | some (_, _, ty0, v0) =>
        if !(ty0 == e.ty? && Val.beq v0 e.val) then
          letDiffs := letDiffs + 1
          IO.println s!"{name}: LET-DIVERGENCE at {e.binder.name}#{e.binder.id}"
    -- the point side
    let keys := (pts.flatten.filterMap (·.stmtKey)).foldl (fun acc k =>
      if acc.any (fun k2 => Term.beq k2 k) then acc else k :: acc) []
    let binders := (pts.flatten.filterMap (fun d =>
      match d.change with
      | .bound x _ | .set x _ => some x
      | .refine _ _ => none)).foldl (fun acc x =>
      if acc.any (fun y => y == x) then acc else x :: acc) []
    let mut pointDiffs := 0
    let mut points := 0
    -- One replay per (path, key); every binder read from that state. (The
    -- ENTRY reading is not swept: it is the seeding run's result, which
    -- precedes any split by construction and cannot diverge.)
    for k in keys do
      let sts := pts.filterMap (fun deltas => replayTo deltas k)
      for x in binders do
        let rendered := sts.filterMap (fun st =>
          (st.env.find? (fun kv => kv.1 == x)).map (fun kv =>
            Val.pretty (ProgElab.annotateSyms st.sctx kv.2)))
        if rendered.isEmpty then pure () else do
        points := points + 1
        let distinct := rendered.foldl (fun acc r =>
          if acc.contains r then acc else r :: acc) []
        if distinct.length > 1 then
          pointDiffs := pointDiffs + 1
          let listed := String.intercalate " ⇔ " distinct
          IO.println s!"{name}: POINT-DIVERGENCE at ({k.pretty}, {x.name}#{x.id}): {listed}"
    IO.println s!"{name}: {pts.length} path(s), {points} point(s), {pointDiffs} point-divergence(s), {letDiffs} let-divergence(s)"

#eval show IO Unit from do
  sweep "join seqJoins" Dllbc.Tests.MatchJoin.seqJoins
  sweep "join agreeArms" Dllbc.Tests.MatchJoin.agreeArms
  sweep "join packEvidence" Dllbc.Tests.MatchJoin.packEvidence
  sweep "join borrowWrite" Dllbc.Tests.MatchJoin.borrowWrite
  sweep "join concreteJoin" Dllbc.Tests.MatchJoin.concreteJoin
  sweep "join singleArm" Dllbc.Tests.MatchJoin.singleArm
  sweep "S33Eager overwriteTail" Dllbc.Tests.S33Eager.overwriteTail
  sweep "S33Eager twoBuildsBase" Dllbc.Tests.S33Eager.twoBuildsBase
  sweep "S33Eager twoBuildsTail" Dllbc.Tests.S33Eager.twoBuildsTail
  sweep "flagship (list quicksort)" Dllbc.Tests.S23Direct.flagship
  sweep "hashmap s2CheckedCaller" Dllbc.Tests.HashMap.s2CheckedCaller
  sweep "hashmap s1Chain" Dllbc.Tests.HashMap.s1Chain
  sweep "arrChain (array quicksort)" Dllbc.Tests.S25ArrSort.arrChain

end Dllbc.Tests.MatchJoinSweep

import Ochr.Examples.Registry

/-! `lake exe tests`: every example program's verdict table with per-declaration
check times, a check that every block's recorded exports (`Block.exports`) are what a fresh
check decides, then the counterfactual ledger. Exits 1 if any verdict is not the
expected one (the build already asserts all of this; the runner prints it). -/

open Ochr Ochr.Test Ochr.Surface Ochr.Registry

/-- Check a program declaration by declaration, timing each check. The configuration
is read from a reference after the clock starts, so the (pure) check cannot be
computed ahead of it, and its verdict is stored before the clock stops. -/
def timedRun (cfgRef : IO.Ref Config) (b : Block) : IO (List (String × Bool × Bool × Nat)) := do
  let mut globals : List GDef := []
  let mut inds : List IndDecl := []
  let mut out := #[]
  let sink ← IO.mkRef (0 : Nat)
  -- the block's library (`Prelude`, then what the blocks it `uses` export), checked first
  -- but not timed
  let lib := libOf (← cfgRef.get) defaultFuel b
  let p := lib ++ b.decls
  for (d, i) in p.zipIdx do
    let t0 ← IO.monoNanosNow
    let cfg ← cfgRef.get
    let ok : Bool := match resolveProgram p d with
      | .error _ => false
      | .ok df =>
        let st : MState := { globals := globals, inds := inds, cfg := cfg }
        match (((checkItem df).run st).run.run #[]).1 with
        | .ok _ => true
        | .error _ => false
    sink.modify (· + (if ok then 1 else 0))
    let t1 ← IO.monoNanosNow
    if ok then
      if let .ok df := resolveProgram p d then
        let st : MState := { globals := globals, inds := inds, cfg := cfg }
        if let .ok ((), st') := (((checkItem df).run st).run.run #[]).1 then
          globals := st'.globals
          inds := st'.inds
    if i ≥ lib.length then
      out := out.push (d.name, d.expectAccept, ok, (t1 - t0) / 1000)
  pure out.toList

/-- Median of a non-empty list. -/
def median (xs : List Nat) : Nat :=
  let a := xs.toArray.qsort (· < ·)
  a[a.size / 2]!

def fmtUs (us : Nat) : String :=
  if us < 1000 then s!"{us} µs" else s!"{us / 1000}.{(us % 1000) / 100} ms"

def main : IO UInt32 := do
  let cfgRef ← IO.mkRef ({} : Config)
  let runs := 21
  let mut total := 0
  let mut passed := 0
  let mut totalUs := 0
  IO.println s!"(check times: median of {runs} runs of the compiled checker, per declaration)"
  for (name, p) in programs ++ caseStudies do
    let mut samples : Array (List (String × Bool × Bool × Nat)) := #[]
    for _ in [0:runs] do samples := samples.push (← timedRun cfgRef p)
    let rows := samples[0]!
    let meds := (List.range rows.length).map fun i => median (samples.toList.map fun r => (r[i]!).2.2.2)
    let us := meds.foldl (· + ·) 0
    let ok := (rows.filter fun (_, e, v, _) => e == v).length
    IO.println s!"== {name}: {ok}/{rows.length} as expected, {fmtUs us}"
    for ((n, e, v, _), t) in rows.zip meds do
      let mark := if e == v then "ok  " else "FAIL"
      IO.println s!"{mark} {n}: expect {if e then "accept" else "reject"}, {if v then "accepted" else "rejected"} ({fmtUs t})"
    total := total + rows.length
    passed := passed + ok
    totalUs := totalUs + us
  IO.println ""
  IO.println s!"verdicts as expected: {passed}/{total} (expected total {expectedTotal}); total check time {fmtUs totalUs}"
  IO.println ""
  IO.println "reasons: see the tables printed by `lake build`, or (run name program).show"
  IO.println ""
  -- the exports each block recorded when the `ochr` command checked it (`Block.exports`, read
  -- by its users under the default configuration) against a fresh decision
  let blocks := programs ++ caseStudies
  let stale := blocks.filterMap fun (n, b) => match b.exports with
    | some ns =>
      let fresh := (exportsOf {} defaultFuel (Block.mk b.name b.uses b.decls none)).map (·.name)
      if fresh == ns then none else some n
    | none => some s!"{n} (none recorded)"
  IO.println s!"exports cache: {blocks.length - stale.length}/{blocks.length} blocks agree with a fresh check{if stale.isEmpty then "" else s!"; differ: {", ".intercalate stale}"}"
  IO.println ""
  IO.println "counterfactual ledger (one rule switched off → verdicts that flip):"
  for ((n, c), (k, ws)) in switches.zip rowClass do
    let (fs, bl) := flipsDetail c
    let wit := if ws.isEmpty then "" else s!" (witness: {", ".intercalate ws})"
    let blk := if bl.isEmpty then "" else s!"; {", ".intercalate bl}"
    IO.println s!"  [{k}{wit}] {n}: {if fs.isEmpty then "nothing" else ", ".intercalate fs}{blk}"
  return if passed == total && total == expectedTotal && stale.isEmpty then 0 else 1

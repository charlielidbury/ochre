import Ochr.Fuzz.Make
import Ochr.Fuzz.Shrink

/-!
`lake exe fuzz`: the differential naturality fuzzer (see `ochr/core/notes/fuzzer.md`).

    lake exe fuzz [--seed S] [--count N] [--start I] [--switch NAME]… [--show I] [--quiet]

Case `i` of seed `S` is a pure function of `(S, i)`, so every run is reproducible and
`--show I` re-runs a single case verbosely.
-/

open Ochr Ochr.Fuzz

/-- The rule switches of `Config` (each turns one rule off), by the names used in the
counterfactual ledger. -/
def switchCfg (c : Config) : String → Option Config
  | "D26" | "P2" | "eraseOnCopy" => some { c with eraseOnCopy := false }
  | "D18" | "multiOwner" => some { c with multiOwner := false }
  | "D17" | "recGuard" => some { c with recGuard := false }
  | "D19" | "accessInside" => some { c with accessInside := false }
  | "L1" | "selfHeadOnly" => some { c with selfHeadOnly := false }
  | "L2" | "argNotBot" => some { c with argNotBot := false }
  | "D27" | "proofParamsStar" => some { c with proofParamsStar := false }
  | "L3" | "recNested" => some { c with recNested := false }
  | "D28" | "erasureByDecl" => some { c with erasureByDecl := false }
  | "D29" | "matchEndsInside" => some { c with matchEndsInside := false }
  | "D30" | "closureConv" => some { c with closureConv := 2 }
  | "D31" | "unboundWithoutBy" => some { c with unboundWithoutBy := false }
  | "D32" | "patternWritesVisible" => some { c with patternWritesVisible := false }
  | "G1" | "genConsistent" => some { c with genConsistent := false }
  | "D35" | "classBySyntax" => some { c with classBySyntax := false }
  | "D35/D40" | "blockRule0" => some { c with blockRule := 0 }
  | "D40" | "blockRule1" => some { c with blockRule := 1 }
  | "D35s" | "seqByProof" => some { c with seqByProof := false }
  | "D35r" | "rowByDecl" => some { c with rowByDecl := false }
  | "P1" | "leafRule0" => some { c with leafRule := 0 }
  | "P3" | "leafRule1" => some { c with leafRule := 1 }
  | "D36" | "positivity" => some { c with positivity := false }
  | "D37" | "globalRecords" => some { c with globalRecords := false }
  | "D38" | "obsBorrow" => some { c with obsBorrow := false }
  | "D39" | "headGuardNeutral" => some { c with headGuardNeutral := false }
  | "D41" | "confine" => some { c with confine := false }
  | "D44" | "borrowParam" => some { c with borrowParam := false }
  | "capTypes" | "D51" => some { c with capTypes := false }
  | "D45" | "byType" => some { c with byType := false }
  | "D45s" | "subsingleton" => some { c with subsingleton := false }
  | "D42" | "propValues" => some { c with propValues := false }
  | "D47" | "disjoint" => some { c with disjoint := false }
  | "scrutTyped" => some { c with scrutTyped := false }
  | "D48.1" | "refData" => some { c with refData := false }
  | "D48.2" | "refTop" => some { c with refTop := false }
  | "D48.3" | "piUnder" => some { c with piUnder := false }
  | "D49.3" | "proofDataFields" => some { c with proofDataFields := false }
  | "D50on" | "unitNorm" => some { c with unitNorm := true }          -- switched ON (a counterfactual)
  | "confineBodies" => some { c with confineBodies := true }          -- switched ON (an extension)
  | "C8" | "generalize" => some { c with generalize := false }
  | "C5" | "blockMoves" => some { c with blockMoves := false }
  | _ => none

structure Args where
  seed : Nat := 1
  count : Nat := 100
  start : Nat := 0
  cfg : Config := {}
  base : Config := {}            -- the rules without the switches (a switch named `+X` would apply to both)
  switches : List String := []
  diff : Bool := false
  show? : Option Nat := none
  quiet : Bool := false
  maxShrink : Nat := 2          -- shrink and print this many findings of each kind
  jobs : Nat := 1               -- > 1: run worker processes in parallel (crash-isolated)
  worker : Bool := false
  printOnly : Bool := false
  raw : List String := []       -- the arguments, for re-spawning workers

partial def parseArgs (a : Args) : List String → Except String Args
  | [] => pure a
  | "--seed" :: n :: r => do parseArgs { a with seed := n.toNat! } r
  | "--count" :: n :: r => do parseArgs { a with count := n.toNat! } r
  | "--start" :: n :: r => do parseArgs { a with start := n.toNat! } r
  | "--show" :: n :: r => do parseArgs { a with show? := some n.toNat! } r
  | "--quiet" :: r => do parseArgs { a with quiet := true } r
  | "--shrink" :: n :: r => do parseArgs { a with maxShrink := n.toNat! } r
  | "--diff" :: r => do parseArgs { a with diff := true } r
  | "--jobs" :: n :: r => do parseArgs { a with jobs := n.toNat! } r
  | "--worker" :: r => do parseArgs { a with worker := true } r
  | "--print-only" :: r => do parseArgs { a with printOnly := true } r
  | "--switch" :: s :: r => do
    match switchCfg a.cfg s, switchCfg a.base s with
    | some c, some b =>
      let b := if s.startsWith "+" then b else a.base
      parseArgs { a with cfg := c, base := b, switches := a.switches ++ [s] } r
    | _, _ => throw s!"unknown switch {s}"
  | x :: _ => throw s!"unknown argument {x}"

def bump (xs : List (String × Nat)) (k : String) (d : Nat := 1) : List (String × Nat) :=
  match xs.lookup k with
  | some n => xs.map fun (k', m) => if k' == k then (k', n + d) else (k', m)
  | none => xs ++ [(k, d)]

/-- Run cases `[start, start + count)` in this process. Each case is announced on stdout
(`@BEGIN i`, flushed) so that a supervisor can tell which case crashed the process
(e.g. a stack overflow, as X5 causes); totals are printed as `@` lines at the end. -/
def runRange (a : Args) (o : Opts) : IO Unit := do
  let out ← IO.getStdout
  let mut stats : List (String × Nat) := []
  let mut kinds : List (String × Nat) := []
  let mut first : List (String × Nat) := []
  let mut shrunk : List (String × Nat) := []
  for i in [a.start:a.start + a.count] do
    if a.worker then out.putStrLn s!"@BEGIN {i}"; out.flush
    let (c, r) := mkCase a.seed i o.fuel
    let res := checkCase o c r
    let st := if res.status.startsWith "invalid" then "invalid" else res.status
    stats := bump stats st
    let fs := match o.base with
      | some b =>
        let bk := (checkCase { o with cfg := b, base := none } c r).findings.map (Finding.key)
        res.findings.filter fun (f : Finding) => !bk.contains f.key
      | none => res.findings
    let mut done : List String := []
    for f in fs do
      if done.contains f.key then continue
      done := f.key :: done
      let key := f.key.replace " " "_"
      kinds := bump kinds key
      if first.lookup key |>.isNone then first := first ++ [(key, i)]
      if !a.quiet && (shrunk.lookup key).getD 0 < a.maxShrink then
        shrunk := bump shrunk key
        let (c', f', n) := shrink o r f.key c f
        if !a.quiet then
          out.putStrLn s!"=== case {i}: [{f.key}] (shrunk in {n} checks; `--show {i}` for the original)"
          out.putStrLn (c'.show s!"Fuzz{f.kind.name}{i}")
          out.putStrLn f'.show
          out.putStrLn ""
  for (k, n) in stats do out.putStrLn s!"@STAT {k} {n}"
  for (k, n) in kinds do out.putStrLn s!"@KIND {k} {n}"
  for (k, n) in first do out.putStrLn s!"@FIRST {k} {n}"
  out.putStrLn "@DONE"

/-- Worker arguments: the user's, minus the supervisor's, plus the range. -/
def workerArgs (a : Args) (start count : Nat) : Array String := Id.run do
  let mut out := #[]
  let mut skip := false
  for x in a.raw do
    if skip then skip := false; continue
    if x == "--jobs" || x == "--start" || x == "--count" then skip := true; continue
    out := out.push x
  pure (out ++ #["--worker", "--start", toString start, "--count", toString count])

/-- Run one range in worker processes, restarting after a crash at the case after it. -/
partial def superviseRange (exe : String) (a : Args) (start count : Nat) :
    IO (List String × List (String × Nat) × List (String × Nat) × List (String × Nat) × List Nat) := do
  if count == 0 then return ([], [], [], [], [])
  let r ← IO.Process.output { cmd := exe, args := workerArgs a start count }
  let ls := (r.stdout.splitOn "\n")
  let mut text := #[]
  let mut stats := []
  let mut kinds := []
  let mut first := []
  let mut last := start
  let mut done := false
  for l in ls do
    match l.splitOn " " with
    | ["@BEGIN", i] => last := i.toNat!
    | ["@STAT", k, n] => stats := bump stats k n.toNat!
    | ["@KIND", k, n] => kinds := bump kinds k n.toNat!
    | ["@FIRST", k, n] => first := first ++ [(k, n.toNat!)]
    | ["@DONE"] => done := true
    | _ => if l != "" then text := text.push l
  if done then return (text.toList, stats, kinds, first, [])
  -- the worker died during case `last`
  let p ← IO.Process.output { cmd := exe, args := #["--seed", toString a.seed, "--show", toString last, "--print-only"] }
  let text' := text.push s!"=== case {last}: [crash] the checker crashed (exit {r.exitCode}): {(r.stderr.splitOn "\n").filter (· != "") |>.getLast? |>.getD ""}"
    |>.push p.stdout
  let (t2, s2, k2, f2, c2) ← superviseRange exe a (last + 1) (start + count - last - 1)
  let merge (xs ys : List (String × Nat)) := ys.foldl (fun acc (k, n) => bump acc k n) xs
  pure (text'.toList ++ t2, bump (merge stats s2) "crashed", merge kinds k2,
        first ++ f2.filter (fun (k, _) => (first.lookup k).isNone), last :: c2)

def main (argv : List String) : IO UInt32 := do
  let a ← match parseArgs {} argv with
    | .ok a => pure { a with raw := argv }
    | .error e => IO.eprintln e; return 2
  let o : Opts := { cfg := a.cfg, base := if a.diff then some a.base else none }
  if let some i := a.show? then
    let (c, r) := mkCase a.seed i o.fuel
    IO.println (c.show s!"Case{i}")
    if a.printOnly then return 0
    (← IO.getStdout).flush
    let res := checkCase o c r
    IO.println s!"status: {res.status}; syntactic-only divergences: {res.synOnly}; incomplete: {res.incomplete}"
    for l in debugCase o c do IO.println l
    for f in res.findings do IO.println f.show
    return 0
  if a.worker || a.jobs ≤ 1 && !a.raw.contains "--isolate" then
    let t0 ← IO.monoMsNow
    runRange a o
    if !a.worker then
      IO.println s!"seed {a.seed}, cases {a.start}..{a.start + a.count - 1}, switches {a.switches}, {(← IO.monoMsNow) - t0} ms"
    return 0
  -- supervisor: split the range into `jobs` chunks, one worker process each
  let exe := (← IO.appPath).toString
  let t0 ← IO.monoMsNow
  let j := max 1 a.jobs
  let size := (a.count + j - 1) / j
  let mut tasks := #[]
  for k in [0:j] do
    let s := a.start + k * size
    let n := min size (a.start + a.count - s)
    if s < a.start + a.count then
      tasks := tasks.push (← IO.asTask (superviseRange exe a s n))
  let mut stats := []
  let mut kinds := []
  let mut first : List (String × Nat) := []
  let mut crashes := []
  for t in tasks do
    match ← IO.wait t with
    | .ok (txt, s, k, f, c) =>
      for l in txt do IO.println l
      stats := s.foldl (fun acc (x, n) => bump acc x n) stats
      kinds := k.foldl (fun acc (x, n) => bump acc x n) kinds
      first := first ++ f.filter (fun (x, _) => (first.lookup x).isNone)
      crashes := crashes ++ c
    | .error e => IO.eprintln s!"worker failed: {e}"
  IO.println s!"seed {a.seed}, cases {a.start}..{a.start + a.count - 1}, switches {a.switches}, {j} jobs, {(← IO.monoMsNow) - t0} ms"
  IO.println s!"status: {stats}"
  IO.println s!"findings (kind[: reason]: cases): {kinds}"
  IO.println s!"first case per kind: {first}"
  IO.println s!"crashed cases: {crashes}"
  return 0

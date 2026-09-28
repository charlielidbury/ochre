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
  | "C8" | "generalize" => some { c with generalize := false }
  | "C5" | "blockMoves" => some { c with blockMoves := false }
  | "D27" | "proofParamsStar" => some { c with proofParamsStar := false }
  | "L3" | "recNested" => some { c with recNested := false }
  | "D28" | "erasureByDecl" => some { c with erasureByDecl := false }
  | "D29" | "matchEndsInside" => some { c with matchEndsInside := false }
  | "D30" | "closureConv" => some { c with closureConv := 2 }
  | "D31" | "unboundWithoutBy" => some { c with unboundWithoutBy := false }
  | "D32" | "patternWritesVisible" => some { c with patternWritesVisible := false }
  | "G1" | "genConsistent" => some { c with genConsistent := false }
  | "+D37" | "genGlobal" => some { c with genGlobal := true }   -- emulate v1.8's D37 (not a switch-off)
  | _ => none

structure Args where
  seed : Nat := 1
  count : Nat := 100
  start : Nat := 0
  cfg : Config := {}
  base : Config := {}            -- the rules without the switches (emulations like +D37 apply to both)
  switches : List String := []
  diff : Bool := false
  show? : Option Nat := none
  quiet : Bool := false
  maxShrink : Nat := 2          -- shrink and print this many findings of each kind

partial def parseArgs (a : Args) : List String → Except String Args
  | [] => pure a
  | "--seed" :: n :: r => do parseArgs { a with seed := n.toNat! } r
  | "--count" :: n :: r => do parseArgs { a with count := n.toNat! } r
  | "--start" :: n :: r => do parseArgs { a with start := n.toNat! } r
  | "--show" :: n :: r => do parseArgs { a with show? := some n.toNat! } r
  | "--quiet" :: r => do parseArgs { a with quiet := true } r
  | "--shrink" :: n :: r => do parseArgs { a with maxShrink := n.toNat! } r
  | "--diff" :: r => do parseArgs { a with diff := true } r
  | "--switch" :: s :: r => do
    match switchCfg a.cfg s, switchCfg a.base s with
    | some c, some b =>
      let b := if s.startsWith "+" then b else a.base
      parseArgs { a with cfg := c, base := b, switches := a.switches ++ [s] } r
    | _, _ => throw s!"unknown switch {s}"
  | x :: _ => throw s!"unknown argument {x}"

def main (argv : List String) : IO UInt32 := do
  let a ← match parseArgs {} argv with
    | .ok a => pure a
    | .error e => IO.eprintln e; return 2
  let o : Opts := { cfg := a.cfg, base := if a.diff then some a.base else none }
  if let some i := a.show? then
    let (c, r) := mkCase a.seed i o.fuel
    IO.println (c.show s!"Case{i}")
    let res := checkCase o c r
    IO.println s!"status: {res.status}; syntactic-only divergences: {res.synOnly}; incomplete: {res.incomplete}"
    for l in debugCase o c do IO.println l
    for f in res.findings do IO.println f.show
    return 0
  let mut stats : List (String × Nat) := []
  let mut kinds : List (String × Nat) := []
  let mut first : List (String × Nat) := []
  let mut shrunk : List (String × Nat) := []
  let bump (xs : List (String × Nat)) (k : String) : List (String × Nat) :=
    match xs.lookup k with
    | some n => xs.map fun (k', m) => if k' == k then (k', n + 1) else (k', m)
    | none => xs ++ [(k, 1)]
  let t0 ← IO.monoMsNow
  for i in [a.start:a.start + a.count] do
    let (c, r) := mkCase a.seed i o.fuel
    let res := checkCase o c r
    let st := if res.status.startsWith "invalid" then "invalid" else res.status
    stats := bump stats st
    let fs := match o.base with
      | some b =>
        let bk := (checkCase { o with cfg := b, base := none } c r).findings.map (Finding.kind)
        res.findings.filter fun (f : Finding) => !bk.contains f.kind
      | none => res.findings
    let mut done : List Fuzz.Kind := []
    for f in fs do
      let key := s!"{f.kind.name}/{f.comp}"
      kinds := bump kinds key
      if first.lookup f.kind.name |>.isNone then first := first ++ [(f.kind.name, i)]
      if (shrunk.lookup f.kind.name).getD 0 < a.maxShrink && !done.contains f.kind then
        shrunk := bump shrunk f.kind.name
        done := f.kind :: done
        let (c', f', n) := shrink o r f.kind c f
        if !a.quiet then
          IO.println s!"=== case {i}: [{f.kind.name}] (shrunk in {n} checks; `--show {i}` for the original)"
          IO.println (c'.show s!"Fuzz{f.kind.name}{i}")
          IO.println f'.show
          IO.println ""
  let t1 ← IO.monoMsNow
  IO.println s!"seed {a.seed}, cases {a.start}..{a.start + a.count - 1}, switches {a.switches}, {t1 - t0} ms"
  IO.println s!"status: {stats}"
  IO.println s!"findings (kind/component: cases): {kinds}"
  IO.println s!"first case per kind: {first}"
  return 0

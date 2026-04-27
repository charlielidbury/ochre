import Och.Macro
import Och.TyCheck
import Och.EvalSubst
import Och.Std.DNat
import Och.Std.DBool
import Och.Std.Pair
import Och.Std.Sigma
import Och.Std.DFin

/-!
# Fast-path bench: `subCheckT` (typeCheck → subCheck) vs bare `subCheck` vs bare `typeCheck`

Measures the cost contribution of the bidirectional `typeCheck`
fast-path inside `SubstEval.subCheckT`. For each case, three
configurations are timed:

1. `subCheckT fuel a τ` — current production entry (`typeCheck` then
   fall back to `subCheck`).
2. `subCheck fuel a τ` — what we'd have if we deleted the fast-path.
3. `typeCheck fuel a τ` — the fast-path in isolation (returns
   `.ok true` on positives that it can verify, `.ok false` /
   `.error` otherwise; for negatives it usually `.error`s through
   to the fallback).

Per case we also report whether each config closes (and with what
verdict) and best-effort fuel needed for `subCheck` alone to close.
The `subCheck` fuel re-search is bounded — if a case requires more
than the per-row cap to close, we report it as `did-not-close`.

Run with `nix develop -c lake exe fastpath_bench` from `lean/`.

This file is a worktree-only probe; do not ship as production
infrastructure.
-/

namespace FastPathBench

open Std

/-- Wall-clock the action. The `Nat` argument is a varying offset
    (read from a mutable IO.Ref each call) to defeat CSE / Lean's
    naive memoization across calls. Returns ms and result. -/
def time {α : Type} (act : Nat → α) (fuelRef : IO.Ref Nat) : IO (Nat × α) := do
  let extra ← fuelRef.get
  let t0 ← IO.monoMsNow
  let r := act extra
  let t1 ← IO.monoMsNow
  fuelRef.set (extra + 1)
  return (t1 - t0, r)

/-- Run `act` `n` times with varying offsets; total ms + last result. -/
def timeN {α : Type} [Inhabited α] (n : Nat) (act : Nat → α) (fuelRef : IO.Ref Nat)
    : IO (Nat × α) := do
  let extra ← fuelRef.get
  let t0 ← IO.monoMsNow
  let mut last : α := default
  for i in [:n] do
    last := act (extra + i)
  let t1 ← IO.monoMsNow
  fuelRef.set (extra + n)
  return (t1 - t0, last)

/-- Right-justify a string in a fixed width by prepending spaces. -/
def rjust (n : Nat) (s : String) : String :=
  if s.length >= n then s else "".pushn ' ' (n - s.length) ++ s

/-- Bare `subCheck`-only: no typeCheck fast-path. -/
private def bareSubCheck (fuel : Nat) (a τ : Expr) : Outcome Bool :=
  SubstEval.subCheck fuel a τ

/-- Bare `typeCheck`-only: just the fast-path, no fallback. -/
private def bareTypeCheck (fuel : Nat) (a τ : Expr) : Outcome Bool :=
  NbE.typeCheck fuel a τ

structure Case where
  label    : String
  fuel     : Nat
  a        : Expr
  b        : Expr
  /-- Fuel ladder for finding bare-subCheck closure (asc).
      Capped to keep the bench bounded. -/
  fuelLadder : List Nat := [200, 800, 2000, 8000, 16000]

private def four_ : Expr := och{ succ_ three_ }
private def five_ : Expr := och{ succ_ four_ }
private def p12 : Expr := och{ pair_ Nat_ Nat_ one_ two_ }
private def pBoolBool : Expr := och{ pair_ Bool Bool true_ false_ }
private def pZeroUnit : Expr := och{ Pair zero_ unit_ }

/-- Standard short ladder: try low fuels first to find true minimum. -/
private def shortLadder : List Nat :=
  [5, 10, 20, 50, 100, 200, 400, 800, 2000, 8000, 32000, 128000, 500000]

def cases : List Case :=
  [ -- Critical numerals: historically expensive without fast-path.
    ⟨"01 zero_   ⊑ Nat_                ",   200, zero_,  Nat_, shortLadder ⟩
  , ⟨"02 one_    ⊑ Nat_                ",   200, one_,   Nat_, shortLadder ⟩
  , ⟨"03 two_    ⊑ Nat_                ",   800, two_,   Nat_, shortLadder ⟩
  , ⟨"04 three_  ⊑ Nat_                ",   200, three_, Nat_, shortLadder ⟩
  , ⟨"05 four_   ⊑ Nat_                ",   200, four_,  Nat_, shortLadder ⟩
  , ⟨"06 five_   ⊑ Nat_                ",   200, five_,  Nat_, shortLadder ⟩
    -- DBool dependent positives
  , ⟨"07 dtrue   ⊑ dBool               ",    50, dtrue,  dBool, shortLadder ⟩
  , ⟨"08 dfalse  ⊑ dBool               ",    50, dfalse, dBool, shortLadder ⟩
    -- Pair positives
  , ⟨"09 p12     ⊑ Pair Nat_ Nat_      ",  1000, p12, och{ Pair Nat_ Nat_ }, shortLadder ⟩
  , ⟨"10 pTT     ⊑ Pair Bool Bool      ",   100, pBoolBool, och{ Pair Bool Bool }, shortLadder ⟩
  , ⟨"11 P0u     ⊑ Pair Nat_ Unit_     ",   200, pZeroUnit, och{ Pair Nat_ Unit_ }, shortLadder ⟩
    -- DFin positives
  , ⟨"12 zero_   ⊑ Fin one_            ",  2000, zero_, och{ Fin one_ }, shortLadder ⟩
  , ⟨"13 zero_   ⊑ Fin three_          ",  2000, zero_, och{ Fin three_ }, shortLadder ⟩
  , ⟨"14 one_    ⊑ Fin three_          ",  8000, one_,  och{ Fin three_ }, shortLadder ⟩
  , ⟨"15 two_    ⊑ Fin three_          ", 16000, two_,  och{ Fin three_ }, shortLadder ⟩
  , ⟨"16 Fin one_ ⊑ Fin two_           ",  4000, och{ Fin one_ }, och{ Fin two_ }, shortLadder ⟩
    -- Negatives (rejection should be cheap on subCheck; expensive via typeCheck-then-subCheck?)
  , ⟨"17 dtrue   ⊄ Nat_   (reject)     ",   200, dtrue, Nat_, shortLadder ⟩
  , ⟨"18 Nat_    ⊄ zero_  (reject)     ",   200, Nat_,  zero_, shortLadder ⟩
  , ⟨"19 zero_   ⊄ one_   (reject)     ",   200, zero_, one_, shortLadder ⟩
  , ⟨"20 Bool    ⊄ Nat_   (reject)     ",   200, Bool, Nat_, shortLadder ⟩
  , ⟨"21 unit_   ⊄ Nat_   (reject)     ",   200, unit_, Nat_, shortLadder ⟩
  , ⟨"22 two_    ⊄ Fin two_ (reject)   ", 16000, two_, och{ Fin two_ }, shortLadder ⟩
  , ⟨"23 Fin two_ ⊄ Fin one_ (reject)  ",  2000, och{ Fin two_ }, och{ Fin one_ }, shortLadder ⟩
  ]

/-- Render an `Outcome Bool` very compactly. -/
private def renderOutcome (o : Outcome Bool) : String :=
  match o with
  | .ok true   => "ok-true "
  | .ok false  => "ok-false"
  | .outOfFuel => "outFuel "
  | .error _   => "error   "

/-- Number of repetitions per timing block. Individual calls are
    sub-millisecond; we amplify to get a meaningful signal. -/
private def iters : Nat := 200

/-- Find the smallest fuel from the ladder at which `subCheck` returns
    `.ok _` (closes decisively). Returns the fuel found, the per-call
    cost in microseconds at that fuel (averaged over `iters` reps),
    and the verdict. -/
def findSubCheckFuel (a τ : Expr) (ladder : List Nat) (fuelRef : IO.Ref Nat)
    : IO (Option Nat × Nat × Outcome Bool) := do
  for f in ladder do
    let (_ms, r) ← time (fun n => bareSubCheck (f + n) a τ) fuelRef
    match r with
    | .ok _ =>
        -- Re-time with iters reps for a stable per-call cost.
        let (totMs, r2) ← timeN iters (fun n => bareSubCheck (f + n) a τ) fuelRef
        return (some f, (totMs * 1000) / iters, r2)
    | _ => continue
  return (none, 0, .error "did-not-close")

/-- Run a single case across the three configurations. -/
def runCase (c : Case) (fuelRef : IO.Ref Nat) : IO Unit := do
  -- 1. subCheckT (current). Time `iters` reps for signal.
  let (sct_ms_total, sctR) ← timeN iters (fun n => SubstEval.subCheckT (c.fuel + n) c.a c.b) fuelRef
  -- 2. typeCheck only at the same baseline fuel.
  let (tc_ms_total, tcR) ← timeN iters (fun n => bareTypeCheck (c.fuel + n) c.a c.b) fuelRef
  -- 3. subCheck only at the baseline fuel (single-shot in time, repeated for signal).
  let (sc_ms_total, scR) ← timeN iters (fun n => bareSubCheck (c.fuel + n) c.a c.b) fuelRef
  -- 4. subCheck-fuel-ladder: smallest fuel at which bare subCheck closes,
  --    plus per-call cost AT that minimum fuel.
  let (laddFuel, lad_us_per_call, laddR) ← findSubCheckFuel c.a c.b c.fuelLadder fuelRef
  let laddFuelStr := match laddFuel with
    | some f => toString f
    | none => "DNF"
  -- per-call cost in micro-seconds (avoiding fractional ms).
  let perCall (totMs : Nat) := s!"{(totMs * 1000) / iters}us"
  IO.println s!"{c.label} | subCheckT[f={c.fuel |> toString |> rjust 6}] {(perCall sct_ms_total) |> rjust 7}/call {renderOutcome sctR} | typeCheck[f={c.fuel |> toString |> rjust 6}] {(perCall tc_ms_total) |> rjust 7}/call {renderOutcome tcR} | subCheck[f={c.fuel |> toString |> rjust 6}] {(perCall sc_ms_total) |> rjust 7}/call {renderOutcome scR} | subCheck-min(f={laddFuelStr |> rjust 6}, {(toString lad_us_per_call) |> rjust 5}us/call, {renderOutcome laddR})"

def runAll : IO Unit := do
  let fuelRef ← IO.mkRef (0 : Nat)
  IO.println "=== FastPathBench: subCheckT vs subCheck vs typeCheck ==="
  IO.println s!"Per-call wall-clock averaged over {iters} iterations (varying-fuel offset to defeat CSE)."
  IO.println "Format: case | subCheckT (current) | typeCheck (fast-path alone) | subCheck (no fast-path) | subCheck min-fuel-to-close"
  IO.println ""
  -- Warm-up call to load native_decide pages.
  let _ := SubstEval.subCheckT 200 zero_ Nat_
  for c in cases do
    runCase c fuelRef
  IO.println ""
  IO.println "=== done ==="

end FastPathBench

def main : IO Unit := FastPathBench.runAll

import Och.TypedNbE
import Och.Std.DNat
import Och.Std.Bool
import Och.Std.DBool
import Och.Std.Pair
import Och.Std.Unit
import Och.Std.DFin

/-!
# Tests for the typed-NbE pipeline (`subCheckT` / `subCheckTyped`)

This file mirrors the smoke tests in `Std/*` and `Tests.lean` but
runs them through the *typed* entry point `NbE.subCheckT`. The
goal is twofold:

1. Confirm `subCheckT` is at least as permissive as `subCheck` on
   the existing test corpus.
2. Surface any cases where `subCheckT` succeeds at *lower fuel*
   thanks to the type-fast-path.

Where a test was commented out as "too expensive" in the Std
files, this file tries it under `subCheckT`. Each one that passes
under `subCheckT` is concrete validation of the typed-NbE
performance hypothesis.
-/

namespace NbE.TypedTests

open Std

/-! ## Baseline: simple types -/

example : NbE.subCheckT 50 .type .type = .ok true := by native_decide
example : NbE.subCheckT 50 Nat_ .type = .ok true := by native_decide
example : NbE.subCheckT 50 .type Nat_ = .ok false := by native_decide

/-! ## DBool — tight singleton encoding -/

example : NbE.subCheckT 200 dtrue dBool = .ok true := by native_decide
example : NbE.subCheckT 200 dfalse dBool = .ok true := by native_decide
example : NbE.subCheckT 200 dtrue dfalse = .ok false := by native_decide
example : NbE.subCheckT 200 dBool dtrue = .ok false := by native_decide

/-! ## Church Bool -/

example : NbE.subCheckT 50 true_ Bool = .ok true := by native_decide
example : NbE.subCheckT 50 false_ Bool = .ok true := by native_decide
example : NbE.subCheckT 50 not' (och{ Bool → Bool }) = .ok true := by native_decide
example : NbE.subCheckT 50 Bool true_ = .ok false := by native_decide

/-! ## DNat — the singleton-Nat encoding

The expensive ones from Std/DNat.lean. Under `subCheck`,
`three_ ⊑ Nat_` requires ~50k fuel; the unification exhaustion
investigation closed the door on memoization/filtering wins.
Under `subCheckT`, the fast-path looks up `tyInfer three_` and
checks the *type* against `Nat_`.
-/

example : NbE.subCheckT 200 zero_ Nat_ = .ok true := by native_decide
example : NbE.subCheckT 200 one_ Nat_ = .ok true := by native_decide
example : NbE.subCheckT 800 two_ Nat_ = .ok true := by native_decide
-- The benchmark case: three_ ⊑ Nat_. Pinning at fuel 800 (matching two_)
-- under the typed pipeline; under bare subCheck this needs ~50k.
example : NbE.subCheckT 800 three_ Nat_ = .ok true := by native_decide

-- Negatives still fail correctly.
example : NbE.subCheckT 200 Nat_ zero_ = .ok false := by native_decide
example : NbE.subCheckT 200 zero_ one_ = .ok false := by native_decide

/-! ## DFin — the regressed cases

Several `Fin n` checks were commented out in `Std/DFin.lean`
because `subCheck` couldn't close them at any tractable fuel.
Try them here. Each one that passes is a concrete win. -/

example : NbE.subCheckT 2000 zero_ (och{ Fin one_ })    = .ok true := by native_decide
example : NbE.subCheckT 4000 one_  (och{ Fin two_ })    = .ok true := by native_decide
example : NbE.subCheckT 8000 one_  (och{ Fin three_ })  = .ok true := by native_decide

-- Try the previously-commented-out cases under the typed pipeline.
-- 2026-04-24: timed out (>10 min) at fuel 16000 — left commented.
-- These remain a target for future passes once the typed pipeline
-- iterates further (e.g. tyEval threading the inferred type through
-- application chains so `succ_ two_`'s inferred type carries
-- structurally rather than recomputing).
-- example : NbE.subCheckT 16000 two_ (och{ Fin three_ }) = .ok true := by native_decide
-- example : NbE.subCheckT 16000 two_  (och{ Fin two_ })   = .ok false := by native_decide
-- example : NbE.subCheckT 16000 three_ (och{ Fin two_ }) = .ok false := by native_decide

/-! ## Pair / parametric -/

example : NbE.subCheckT 200 (och{ Pair zero_ unit_ }) (och{ Pair Nat_ Unit_ })
  = .ok true := by native_decide

end NbE.TypedTests

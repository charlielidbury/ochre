import Och.TypedNbE
import Och.EvalSubst
import Och.Std.DNat
import Och.Std.Bool
import Och.Std.DBool
import Och.Std.Pair
import Och.Std.Unit
import Och.Std.DFin

/-!
# Tests for the typed-NbE pipeline (`subCheckT` / `subCheckTyped`)

This file mirrors the smoke tests in `Std/*` and `Tests.lean` but
runs them through the *typed* entry point `SubstEval.subCheckT`. The
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

example : SubstEval.subCheckT 50 .type .type = .ok true := by native_decide
example : SubstEval.subCheckT 50 Nat_ .type = .ok true := by native_decide
example : SubstEval.subCheckT 50 .type Nat_ = .ok false := by native_decide

/-! ## DBool — tight singleton encoding -/

example : SubstEval.subCheckT 200 dtrue dBool = .ok true := by native_decide
example : SubstEval.subCheckT 200 dfalse dBool = .ok true := by native_decide
example : SubstEval.subCheckT 200 dtrue dfalse = .ok false := by native_decide
example : SubstEval.subCheckT 200 dBool dtrue = .ok false := by native_decide

/-! ## Church Bool -/

example : SubstEval.subCheckT 50 true_ Bool = .ok true := by native_decide
example : SubstEval.subCheckT 50 false_ Bool = .ok true := by native_decide
example : SubstEval.subCheckT 50 not' (och{ Bool → Bool }) = .ok true := by native_decide
example : SubstEval.subCheckT 50 Bool true_ = .ok false := by native_decide

/-! ## DNat — the singleton-Nat encoding

The expensive ones from Std/DNat.lean. Under `subCheck`,
`three_ ⊑ Nat_` requires ~50k fuel; the unification exhaustion
investigation closed the door on memoization/filtering wins.
Under `subCheckT`, the fast-path looks up `tyInfer three_` and
checks the *type* against `Nat_`.
-/

example : SubstEval.subCheckT 200 zero_ Nat_ = .ok true := by native_decide
example : SubstEval.subCheckT 200 one_ Nat_ = .ok true := by native_decide
example : SubstEval.subCheckT 800 two_ Nat_ = .ok true := by native_decide
-- The benchmark case: three_ ⊑ Nat_. Pinning at fuel 800 (matching two_)
-- under the typed pipeline; under bare subCheck this needs ~50k.
example : SubstEval.subCheckT 800 three_ Nat_ = .ok true := by native_decide

/-- `five_ ⊑ Nat_` — the perf-regression sentinel from PerfProbe.lean
that does not close under bare `subCheck` at any tested fuel
(commented out at fuel 6400 there, did not close in 10+ minutes).
Under `subCheckT`, the typeCheck-fast-path inlines through 5
applications of `succ_`, each cheap because tyInfer at each layer
returns `Nat_` directly from the fix annotation, so the recursive
domain check on `m` becomes `subCheckVal Nat_ Nat_` = refl.

If this passes at low fuel, that's the headline pass-2 win. -/
def four_local := och{ succ_ three_ }
def five_local := och{ succ_ four_local }
example : SubstEval.subCheckT 800 four_local Nat_ = .ok true := by native_decide
example : SubstEval.subCheckT 800 five_local Nat_ = .ok true := by native_decide

-- Negatives still fail correctly.
example : SubstEval.subCheckT 200 Nat_ zero_ = .ok false := by native_decide
example : SubstEval.subCheckT 200 zero_ one_ = .ok false := by native_decide

/-! ## DFin — the regressed cases

Several `Fin n` checks were commented out in `Std/DFin.lean`
because `subCheck` couldn't close them at any tractable fuel.
Try them here. Each one that passes is a concrete win. -/

example : SubstEval.subCheckT 2000 zero_ (och{ Fin one_ })    = .ok true := by native_decide
example : SubstEval.subCheckT 4000 one_  (och{ Fin two_ })    = .ok true := by native_decide
example : SubstEval.subCheckT 8000 one_  (och{ Fin three_ })  = .ok true := by native_decide

-- Try the previously-commented-out cases under the typed pipeline.
-- 2026-04-24: at fuel 16000 the test runs longer than the 10-min
-- build budget. Reason: even under the typed pipeline, the typeCheck
-- fast-path for `two_ ⊑ Fin three_` rejects (tyInfer's principal
-- type for `two_` is `Nat_`, and `Nat_ ⊑ Fin three_` is false), so
-- we fall back to bare `subCheck two_ (Fin three_)` — the same
-- expensive value-level check as without typed NbE. Pass 3 work
-- (threading inferred types into singleton-aware tyEval) is needed
-- to win this case.
-- example : SubstEval.subCheckT 16000 two_ (och{ Fin three_ }) = .ok true := by native_decide
-- example : SubstEval.subCheckT 16000 two_  (och{ Fin two_ })   = .ok false := by native_decide
-- example : SubstEval.subCheckT 16000 three_ (och{ Fin two_ }) = .ok false := by native_decide

/-! ## Pair / parametric -/

example : SubstEval.subCheckT 200 (och{ Pair zero_ unit_ }) (och{ Pair Nat_ Unit_ })
  = .ok true := by native_decide

end NbE.TypedTests

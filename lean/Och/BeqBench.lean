import Och.Macro
import Och.Eval
import Och.SubCheckVal
import Och.TypedNbE
import Och.Std.DNat
import Och.Std.DFin
import Och.Std.Pair
import Och.Std.Bool
import Och.Std.Unit
import Och.Std.DBool

/-!
# Val.beq ptrEq fast-path benchmark harness

Times `subCheck` / `subCheckT` on a representative panel of cases.
Run twice — once with `Val.beqFast` (the `@[implemented_by]` swap
in `SubCheckVal.lean`) live and once with the attribute commented
out — to measure the fast-path's contribution.

Only used as a one-shot probe; remove or guard once the report is
written. Wall-clock measurements are runtime-only (compiled #eval),
so the `unsafe` `beqFast` body is what actually runs.
-/

namespace NbE.BeqBench

open Std

/-- Run `act` once with a runtime-supplied fuel offset and report
wall-clock ms. The offset is an `IO.Ref Nat` so the optimizer can't
fold the call away; reading from the ref forces the value to be
treated as runtime data. -/
def time {α : Type} [Repr α] (label : String) (fuelRef : IO.Ref Nat)
    (act : Nat → α) : IO Unit := do
  let extra ← fuelRef.get
  let t0 ← IO.monoMsNow
  let r := act extra
  let t1 ← IO.monoMsNow
  IO.println s!"{label}: {t1 - t0} ms  result={repr r}"

/-! ## Benchmark cases

Spread across the spectrum from "no shared substructure / trivial"
to "deeply shared, recursive". Pinned at fuels that previously closed.
-/

-- 1. Trivial: `.type ⊑ .type`. No shared substructure to short-circuit;
--    pure structural BEq on the shape itself (no recursion).
def b_typeRefl  (n : Nat) : Outcome Bool := NbE.subCheck (50 + n) Expr.type Expr.type

-- 2. Tiny singleton: `Unit_ ⊑ Type` and `unit_ ⊑ Unit_`.
def b_unitInType (n : Nat) : Outcome Bool := NbE.subCheck (50 + n) Unit_ Expr.type
def b_unitInUnit (n : Nat) : Outcome Bool := NbE.subCheck (50 + n) unit_ Unit_

-- 3. Singleton-DBool: `dtrue ⊑ dBool` — small ι/fix combo.
def b_dtrueInBool (n : Nat) : Outcome Bool := NbE.subCheck (200 + n) dtrue dBool

-- 4. Church-Bool: `true_ ⊑ Bool`.
def b_trueInBool (n : Nat) : Outcome Bool := NbE.subCheck (50 + n) true_ Bool

-- 5. Singleton-Nat: `zero_ ⊑ Nat_`. Shallow case.
def b_zeroInNat (n : Nat) : Outcome Bool := NbE.subCheck (200 + n) zero_ Nat_

-- 6. Singleton-Nat: `one_ ⊑ Nat_`. One succ_ wrap.
def b_oneInNat (n : Nat) : Outcome Bool := NbE.subCheck (200 + n) one_ Nat_

-- 7. Singleton-Nat: `two_ ⊑ Nat_`. Two succ_ wraps; PerfProbe's
--    pre-fix table reports 10 004 ms here without ptrEq.
def b_twoInNat (n : Nat) : Outcome Bool := NbE.subCheck (800 + n) two_ Nat_

-- 8. Singleton-Nat: `three_ ⊑ Nat_`. Three succ_ wraps; PerfProbe's
--    pre-fix table reports 322 175 ms here without ptrEq (~5min).
def b_threeInNatT (n : Nat) : Outcome Bool := NbE.subCheckT (800 + n) three_ Nat_

-- 8b. Bare `subCheck` on three_ ⊑ Nat_ at the fuel the docs say it
--     needs (~50k after Option A). This is the legacy hot-path where
--     b055339 reported the 1000× speedup on the OLD encoding.
def b_threeInNatBare (n : Nat) : Outcome Bool := NbE.subCheck (50000 + n) three_ Nat_

-- 8c. Bare `subCheck` on two_ ⊑ Nat_ at high fuel — sanity-check that
--     extra fuel above the actual budget doesn't slow Val.beq down.
def b_twoInNatHigh (n : Nat) : Outcome Bool := NbE.subCheck (5000 + n) two_ Nat_

-- 9. Pair: `pair Nat Nat 1 2 ⊑ Pair Nat Nat`.
private def p12 := och{ pair_ Nat_ Nat_ one_ two_ }
def b_pair12 (n : Nat) : Outcome Bool :=
  NbE.subCheckT (1000 + n) p12 (och{ Pair Nat_ Nat_ })

-- 10. Pair-covariance: `Pair zero_ unit_ ⊑ Pair Nat_ Unit_`.
def b_pairCov (n : Nat) : Outcome Bool :=
  NbE.subCheckT (200 + n) (och{ Pair zero_ unit_ }) (och{ Pair Nat_ Unit_ })

-- 11. DFin: `zero_ ⊑ Fin one_` — recursive type, dependent codomain.
def b_zeroInFinOne (n : Nat) : Outcome Bool :=
  NbE.subCheckT (2000 + n) zero_ (och{ Fin one_ })

-- 12. DFin: `one_ ⊑ Fin three_` — deeper Fin, more recursion.
def b_oneInFinThree (n : Nat) : Outcome Bool :=
  NbE.subCheckT (8000 + n) one_ (och{ Fin three_ })

-- 13. DFin width: `Fin one_ ⊑ Fin two_` — typing-ascent on both sides.
def b_finWidth (n : Nat) : Outcome Bool :=
  NbE.subCheckT (4000 + n) (och{ Fin one_ }) (och{ Fin two_ })

-- 14. "no-shared-substructure" reject path: `Nat_ ⊄ zero_`.
def b_natNotInZero (n : Nat) : Outcome Bool := NbE.subCheck (200 + n) Nat_ zero_

-- 15. Distinct-but-structurally-related reject: `unit_ ⊄ Nat_`.
def b_unitNotInNat (n : Nat) : Outcome Bool := NbE.subCheck (200 + n) unit_ Nat_

def runAll : IO Unit := do
  -- Runtime-supplied "extra fuel" prevents constant-folding of the
  -- whole benchmark body. Set to 0 — the named fuels are the
  -- pinned cost contracts.
  let fuelRef ← IO.mkRef (0 : Nat)
  IO.println "=== Val.beq ptrEq fast-path benchmark ==="
  time "01 typeRefl                  (subCheck   50)" fuelRef b_typeRefl
  time "02 Unit_  ⊑ Type             (subCheck   50)" fuelRef b_unitInType
  time "03 unit_  ⊑ Unit_            (subCheck   50)" fuelRef b_unitInUnit
  time "04 dtrue  ⊑ dBool            (subCheck  200)" fuelRef b_dtrueInBool
  time "05 true_  ⊑ Bool             (subCheck   50)" fuelRef b_trueInBool
  time "06 zero_  ⊑ Nat_             (subCheck  200)" fuelRef b_zeroInNat
  time "07 one_   ⊑ Nat_             (subCheck  200)" fuelRef b_oneInNat
  time "08 two_   ⊑ Nat_             (subCheck  800)" fuelRef b_twoInNat
  time "09 three_ ⊑ Nat_  (typed)    (subCheckT 800)" fuelRef b_threeInNatT
  time "09b two_  ⊑ Nat_  (bare hi)  (subCheck  5000)" fuelRef b_twoInNatHigh
  time "09c three_⊑ Nat_  (bare hi)  (subCheck 50000)" fuelRef b_threeInNatBare
  time "10 p12    ⊑ Pair Nat Nat     (subCheckT 1000)" fuelRef b_pair12
  time "11 Pair zero unit ⊑ Pair N U (subCheckT 200)"  fuelRef b_pairCov
  time "12 zero_  ⊑ Fin one_         (subCheckT 2000)" fuelRef b_zeroInFinOne
  time "13 one_   ⊑ Fin three_       (subCheckT 8000)" fuelRef b_oneInFinThree
  time "14 Fin one_ ⊑ Fin two_       (subCheckT 4000)" fuelRef b_finWidth
  time "15 Nat_  ⊄ zero_   (reject)  (subCheck  200)" fuelRef b_natNotInZero
  time "16 unit_ ⊄ Nat_    (reject)  (subCheck  200)" fuelRef b_unitNotInNat
  IO.println "=== done ==="

end NbE.BeqBench

def main : IO Unit := NbE.BeqBench.runAll

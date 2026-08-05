import Dllbc.Migrate
import Dllbc.Tests.S5Bound
import Dllbc.Tests.S6Call
import Dllbc.Tests.S7Group
import Dllbc.Tests.S9Diff
import Dllbc.Tests.S10Ford
import Dllbc.Tests.S11Lib
import Dllbc.Tests.S12Inst
import Dllbc.Tests.S14Bounds
import Dllbc.Tests.S15Elab
import Dllbc.Tests.S16Spec
import Dllbc.Tests.S17Spec
import Dllbc.Tests.S18Rewrite
import Dllbc.Tests.S19Partition
import Dllbc.Tests.S23Direct
import Dllbc.Tests.S24Arrays
import Dllbc.Tests.S25ArrSort
import Dllbc.Tests.SDeclMacro
import Dllbc.Tests.SDeclMacroCrown
import Dllbc.Tests.SDeclUnified

/-!
# §26 (M26-E) — the corpus, down both paths

The migration's bar is **coverage preservation**: everything the declaration path
accepted must be accepted as a program, and every lie twin it refused must be
refused as a program. This file discharges that over the whole corpus — 224
declarations — by running each cohort down BOTH paths and comparing the verdicts.

**Nothing here rewrites a test**, and that is deliberate. A bulk migration's
failure mode is not a wall; it is a quietly-wrong rewrite that still builds. So
the corpus stays exactly as it is, each declaration's callee closure is derived
(`calleeNames`) rather than restated, `progOf` assembles it, and the comparison is
a computation. `Migrate.report` returns counts alongside the disagreement list
precisely so that a migration which quietly stopped covering half the corpus
changes the numbers even while `disagree` stays empty.

**The result: 94 accept on both paths, 56 reject on both, 74 do not migrate, and
NOTHING disagrees.** The 74 are three named classes (§Z below), each a decision
this project has already taken.

## What the comparison found — two real bugs, both mine

Recorded here because the harness's whole justification is that it can say no,
and it did, twice:

  * **`progOf` did not permute a call's arguments to match its callee's hoist.**
    `[k]` is a scrutinee-selection hint and `fnElab` moves that parameter to the
    FRONT (the motive is the sealed Π with the scrutinee peeled off the front), so
    a sealed callee's telescope is not its declaration's telescope. The bug is
    invisible whenever `[k]` is already parameter 0 — which every flagship in this
    corpus happens to satisfy, so §F and §G were green throughout — and passes a
    borrow where a `Nat` is expected otherwise. Surfaced as two S23 cohorts
    reporting decl=accept/prog=reject: `swap_at` (calls `set_at [i]`) and `pick`
    (calls `insert_at [k]`).
  * **The macro silently repaired a non-terminating program.** `recGrow` recurses
    on ITSELF (`recGrow(S(m2))`), is rejected by the declaration path's
    snapshot-subterm guard, and elaborated to a recursor that recurses on the
    predecessor and checked — reported as decl=reject/prog=accept. `ih` is the
    sealed self-view AT THE PREDECESSOR, so `fnElab` now refuses a self-call at
    anything else. Constraint 7 held either way (the kernel accepted a
    well-founded program), but "checks as a different function" is the macro bug
    that constraint tolerates and a reader should not.
-/

open Dllbc

namespace Dllbc.Tests.S26Migrate

open Dllbc.Migrate
open Dllbc.Tests

/-! ## The pools

    One per corpus file: every `Decl` it defines, plus the imported ones its own
    tables use (S19 checks against S17's `nth`/`nth2`/`swapS`). A pool that is
    missing a callee makes both paths reject for the same wrong reason, so
    completeness matters — and the counts are what expose it. -/

def p5 : List Decl := [S5Bound.pushList, S5Bound.vecPush]
def p6 : List Decl := [S6Call.pushList, S6Call.wireCaller, S6Call.zeroAll, S6Call.toNat,
  S6Call.toNatCaller, S6Call.rbCaller]
def p7 : List Decl := [S7Group.choose, S7Group.chooseCaller, S7Group.through, S7Group.throughCaller]
def p9 : List Decl := [S9Diff.through, S9Diff.advance, S9Diff.choose, S9Diff.push]
def p10 : List Decl := [S10Ford.learn, S10Ford.learnObs, S10Ford.learnBorrow,
  S10Ford.rigidStuck, S10Ford.occursFn]
def p11 : List Decl := [S11Lib.retRefl, S11Lib.storeProof, S11Lib.discharge]
def p12 : List Decl := [S12Inst.useRefl, S12Inst.callerRet, S12Inst.symCall, S12Inst.needs,
  S12Inst.callNeeds1, S12Inst.callNeeds3, S12Inst.observe, S12Inst.observeGood,
  S12Inst.observeBad, S12Inst.needsLe22, S12Inst.refineTest, S12Inst.classify]
def p14 : List Decl := [S14Bounds.nth, S14Bounds.nth2, S14Bounds.swap, S14Bounds.cascade,
  S14Bounds.rejectProbe]
def p15 : List Decl := [S15Elab.useTrans, S15Elab.badRefl]
def p16 : List Decl := [S16Spec.swapS01, S16Spec.swapCaller]
def p17 : List Decl := [S17Spec.throughOk, S17Spec.caller, S17Spec.throughLie,
  S17Spec.throughOpaque, S17Spec.nthS, S17Spec.nth2S, S17Spec.swapSN, S17Spec.spcCaller]
def p18 : List Decl := [S18Rewrite.certConsHit, S18Rewrite.certConsHitLie]

def p19 : List Decl := [S17Spec.nthS, S17Spec.nth2S, S17Spec.swapSN,
  S19Partition.certSwapCount, S19Partition.certSwapCountLie, S19Partition.pivotPlace,
  S19Partition.pivotPlaceH, S19Partition.partScan, S19Partition.partScanRange,
  S19Partition.partition, S19Partition.partitionLie, S19Partition.partScanLie,
  S19Partition.nth2Lie, S19Partition.stuckProbe, S19Partition.stuckProbeLie,
  S19Partition.stuckProbeNonExh, S19Partition.partScanE, S19Partition.partitionE,
  S19Partition.partitionQ, S19Partition.partitionRange, S19Partition.quicksort,
  S19Partition.quicksortLie, S19Partition.partScanRangeE, S19Partition.lebProbe,
  S19Partition.qsSpcCaller, S19Partition.exitAccept, S19Partition.exitReject,
  S19Partition.lenPreserve, S19Partition.shareCaller, S19Partition.twoRec,
  S19Partition.swapSE, S19Partition.swapSELie, S19Partition.partitionRangeE,
  S19Partition.partitionRangeELie, S19Partition.quicksortE, S19Partition.quicksortELie,
  S19Partition.quicksortSorted, S19Partition.quicksortSortedLiePerm,
  S19Partition.quicksortSortedLieSorted]

def p23 : List Decl := [S23Direct.pinOne, S23Direct.useIt, S23Direct.usePin, S23Direct.useItLie,
  S23Direct.usePinLie, S23Direct.plainOne, S23Direct.useUnpinned, S23Direct.recGood,
  S23Direct.recBad, S23Direct.recSame, S23Direct.recWrongIdx, S23Direct.recRightIdx,
  S23Direct.recGrow, S23Direct.recMutA, S23Direct.recMutB, S23Direct.recList, S23Direct.recDeep,
  S23Direct.recCursor, S23Direct.recCaller, S23Direct.appendBack, S23Direct.splitOff,
  S23Direct.splitOffLieTake, S23Direct.splitOffLieDrop, S23Direct.splitOffLieSwap,
  S23Direct.splitOffLieHead, S23Direct.setAt, S23Direct.swapAt, S23Direct.setAtLieIdx,
  S23Direct.setAtLieNoop, S23Direct.swapAtLieIdx, S23Direct.swapAtLieNoop, S23Direct.insertAt,
  S23Direct.insertAtLieIdx, S23Direct.insertAtLieNoop, S23Direct.needLe,
  S23Direct.branchKnowledge, S23Direct.branchKnowledgeEq, S23Direct.needGt,
  S23Direct.branchKnowledgeBoth, S23Direct.branchKnowledgeIf, S23Direct.branchEqSwapped,
  S23Direct.needLeSwap, S23Direct.branchEqWrongSpine, S23Direct.wantEqLie,
  S23Direct.branchEqPlainSym, S23Direct.wantRefl, S23Direct.branchEqPlainSymRefl,
  S23Direct.concreteEq, S23Direct.pick, S23Direct.partition, S23Direct.partLieUb,
  S23Direct.partLieLb, S23Direct.partLieCountDrop, S23Direct.partLieCountShift,
  S23Direct.partitionLoses, S23Direct.quicksort, S23Direct.qsLieSorted, S23Direct.qsLieCount,
  S23Direct.qsStaleBound, S23Direct.qsNoSuff]

def p24 : List Decl := [S24Arrays.halves, S24Arrays.noEvidence, S24Arrays.wrongEvidence,
  S24Arrays.rigidLength, S24Arrays.walk, S24Arrays.walkArr, S24Arrays.touch, S24Arrays.callSeg,
  S24Arrays.fill1, S24Arrays.bump, S24Arrays.idxCited, S24Arrays.rng1Cited,
  S24Arrays.idxWeakBound, S24Arrays.threeWayTouch, S24Arrays.splitTwo, S24Arrays.pivotCarve,
  S24Arrays.sigSlice, S24Arrays.useSlice, S24Arrays.sliceTouch, S24Arrays.sigCallerOk,
  S24Arrays.sigCallerWrong, S24Arrays.recSlice, S24Arrays.threeWay, S24Arrays.threeWayNoFirstEv,
  S24Arrays.threeWayUncited, S24Arrays.threeWayWrongEq, S24Arrays.threeWayLyingResidue,
  S24Arrays.sliceTake, S24Arrays.threeWayCall, S24Arrays.setSorted, S24Arrays.setSortedLie,
  S24Arrays.readTwo, S24Arrays.sort2, S24Arrays.sort2LieSorted, S24Arrays.sort2LieCount]

def p25 : List Decl := [S25ArrSort.splitA, S25ArrSort.partitionA, S25ArrSort.quicksortA,
  S25ArrSort.splitALieLen, S25ArrSort.splitALieSp, S25ArrSort.splitALieCount,
  S25ArrSort.splitANoSwap, S25ArrSort.partALieLen, S25ArrSort.partALiePart,
  S25ArrSort.qsALieSorted, S25ArrSort.qsALieCount, S25ArrSort.carveNoEv, S25ArrSort.carveWithEv,
  S25ArrSort.qsANoSuff, S25ArrSort.c6Touch, S25ArrSort.c6PeelCall, S25ArrSort.c6CarveNoCall,
  S25ArrSort.c6Swap, S25ArrSort.c6Rec, S25ArrSort.c6CarveAfterCall, S25ArrSort.twoCursor,
  S25ArrSort.twoCursorRes, S25ArrSort.citedCarve]

def pdm : List Decl := [SDeclMacro.throughOk', SDeclMacro.swapS', SDeclMacro.vecPush',
  SDeclMacro.pushList', SDeclMacro.nth', SDeclMacro.snapBinderDecl, SDeclMacro.snapIgnoreDecl]
def pdc : List Decl := [SDeclMacroCrown.quicksortSig]
def pdu : List Decl := [SDeclUnified.nthU, SDeclUnified.permuted, SDeclUnified.partScanEU,
  SDeclUnified.pivotPlaceHU]

/-! ## §Y. The reports

    One assertion per file, on the whole tuple. `disagree = []` is the property;
    the three counts are what keep the property from holding vacuously. -/

def R (a r d : Nat) : Report := { accepts := a, rejects := r, declined := d, disagree := [] }

example : (report p5  == R 2 0 0) = true := by native_decide
example : (report p6  == R 5 0 1) = true := by native_decide
example : (report p7  == R 4 0 0) = true := by native_decide
example : (report p9  == R 4 0 0) = true := by native_decide
example : (report p10 == R 3 2 0) = true := by native_decide
example : (report p11 == R 3 0 0) = true := by native_decide
example : (report p12 == R 10 2 0) = true := by native_decide
example : (report p14 == R 0 0 5) = true := by native_decide
example : (report p15 == R 1 1 0) = true := by native_decide
example : (report p16 == R 2 0 0) = true := by native_decide
example : (report p17 == R 1 0 7) = true := by native_decide
example : (report p18 == R 1 1 0) = true := by native_decide
example : (report p19 == R 2 2 35) = true := by native_decide
example : (report p23 == R 23 19 18) = true := by native_decide
example : (report p24 == R 20 14 1) = true := by native_decide
example : (report p25 == R 11 12 0) = true := by native_decide
example : (report pdm == R 2 2 3) = true := by native_decide
example : (report pdc == R 0 0 1) = true := by native_decide
example : (report pdu == R 0 1 3) = true := by native_decide

/-- The corpus total, as one number each, so that a file quietly dropping out of
    the survey is visible even if its own assertion was deleted with it. -/
def pools : List (List Decl) :=
  [p5, p6, p7, p9, p10, p11, p12, p14, p15, p16, p17, p18, p19, p23, p24, p25, pdm, pdc, pdu]

example : (pools.foldl (fun (a, r, d) p =>
    let q := report p; (a + q.accepts, r + q.rejects, d + q.declined)) (0, 0, 0)
  == (94, 56, 74)) = true := by native_decide
example : (pools.all (fun p => (report p).disagree.isEmpty)) = true := by native_decide

/-! ## §Z. What did not migrate, and why — three classes, each already decided

    A migration report that could not say "this one did not move" would be the
    quietly-wrong thing, so the declines are classified rather than counted. All
    74 fall into three classes, and each class is a decision this project took
    before this phase started. -/

-- Z1. **A declared `back`** (§6.2) — the mechanism M23 RETIRED. Its corpus
-- declares none, deliberately ("ZERO declared backs" was M23's headline), and the
-- seal has no counterpart because the ensures IS the contract now (§5 point 4).
-- This is the biggest class: it takes S14, S17 and — through the three S17
-- functions their tables import — nearly all of S19, which is the M17-era spec
-- corpus M23 superseded.
example : (match FnMacro.fnElab S17Spec.throughOk with
           | .error e => strContains e "declares a backward spec"
           | .ok _ => false) = true := by native_decide

-- Z2. **`[v]` payload decrease** (§12 decision 8) — no recursor form until §9's
-- borrow-mode eliminator exists; fuel-threading is the blessed interim, and it is
-- a SOURCE change, so a macro may not invent it. `zero_all`, `nth`, `recCursor`,
-- `append_back`, `partition`, `walkArr`. M26-D paid it for `partition` and M26-E
-- for `append_back`; the rest stay as they are (J1 — both worlds alive).
example : (match FnMacro.fnElab S6Call.zeroAll with
           | .error e => strContains e "decision 8"
           | .ok _ => false) = true := by native_decide

-- Z3. **A recursion `natRec` cannot express.** Three shapes: a non-`Nat`
-- scrutinee (`recList` — `listRec` is wired in the KERNEL's `sealRec` but not yet
-- in the macro), a self-call at a non-predecessor (the guard twins `recSame`,
-- `recWrongIdx`, `recGrow`), and — the one that is a genuine expressiveness
-- limit rather than a twin — `recDeep`, which recurses TWO constructors down.
-- `natRec` hands an arm `ih` at the immediate predecessor and nothing below it,
-- so a legal-by-the-guard two-step recursion has no single-`natRec` form.
example : (match FnMacro.fnElab S23Direct.recDeep with
           | .error e => strContains e "not the predecessor"
           | .ok _ => false) = true := by native_decide
example : (match FnMacro.fnElab S23Direct.recList with
           | .error e => strContains e "is not `Nat`"
           | .ok _ => false) = true := by native_decide

/-! ## §W. The two bugs the report found, pinned as regressions

    Both were invisible to every test that existed, and both would have shipped a
    migration that builds. -/

-- W1. THE HOIST PERMUTATION. `swap_at` calls `set_at [i]`, whose decreasing
-- parameter is SECOND, so the sealed callee's telescope is `(i, v, x, hi)` while
-- the call is written `(&mut *v, j, a, p2)`. Before the fix the borrow was checked
-- against `i : Nat` — "hasType: cannot type value borrowₘ". Pinned as the pair it
-- is: the cohort accepts, and its `[k]`-first sibling always did.
example : (match FnMacro.progOf [S23Direct.setAt, S23Direct.swapAt] .unit with
           | .ok t => progOk t
           | .error _ => false) = true := by native_decide
example : (match FnMacro.progOf [S23Direct.insertAt, S23Direct.pick] .unit with
           | .ok t => progOk t
           | .error _ => false) = true := by native_decide

-- W2. THE SILENT REPAIR. `recGrow` recurses on itself and the declaration path
-- rejects it; the macro used to drop the scrutinee argument unexamined and emit an
-- `ih` — a recursor on the PREDECESSOR, which is a different function and checks.
-- Now refused. Kept beside its honest sibling, so the refusal is about the
-- argument and not about the shape.
example : (match FnMacro.fnElab S23Direct.recGrow with
           | .error e => strContains e "not the predecessor"
           | .ok _ => false) = true := by native_decide
example : (match FnMacro.fnElab S23Direct.recGood with
           | .error _ => false
           | .ok _ => true) = true := by native_decide

/-! ## §V. Which blocker is load-bearing — measured, because I had it backwards

    The decline classes above are not independent: `fnElab` reports the FIRST
    reason it finds, and it checks `back` before it checks the decreasing
    parameter. So a function that both declares a backward spec AND decreases
    through a borrow payload is reported as a `back` decline, and reading the
    report at face value says §6.2 blocks S17 and S19 wholesale.

    It does not. Stripping `back` from a pool and re-running the comparison is
    two lines, and it moves 74 declines to **66**: §6.2 is the sole blocker for
    exactly **eight** declarations, and the other 66 are blocked underneath by
    §12 decision 8's `[v]` payload decrease. That reverses the conclusion about
    what stands between here and deleting `Decl` — the road runs through §9's
    borrow-mode eliminator (or fuel-threading six functions by hand, the shape
    M26-D and M26-E have each paid once), not through redesigning what a backward
    spec becomes.

    (A Lean-level gotcha that cost me the first measurement, recorded because it
    fails SILENTLY: `{ d with back := none }` does not strip the field. `back` is
    a reserved token of the `decl{ … }` surface, so the record-update syntax does
    not mean what it reads as, and the stripped pool came back identical. The
    positional `Decl.mk` is the way to write it — which is the same reason
    `DeclMacro.assemble` builds its `Decl` positionally.) -/

def stripBacks (pool : List Decl) : List Decl :=
  pool.map (fun d => Decl.mk d.name d.telescope d.retType d.body none d.dec)

-- The strip is real (the check the first attempt did not make).
example : (p17.any (fun d => d.back.isSome)
        && (stripBacks p17).all (fun d => d.back.isNone)) = true := by native_decide

-- 74 declines become 66, so `back` alone accounts for eight.
example : (pools.foldl (fun a p => a + (report p).declined) 0 == 74) = true := by native_decide
example : (pools.foldl (fun a p => a + (report (stripBacks p)).declined) 0 == 66)
  = true := by native_decide

-- And the comparison still agrees everywhere with the backs gone, so the eight
-- that move are migrations and not accidents.
example : (pools.all (fun p => (report (stripBacks p)).disagree.isEmpty)) = true := by native_decide

-- Per file, so the eight are locatable: S17 loses three (7 → 4), S19 one (35 →
-- 34), and the two `SDecl` pools two more (3 → 1, 1 → 0, 3 → 2).
example : (pools.map (fun p => (report (stripBacks p)).declined)
  == [0, 1, 0, 0, 0, 0, 0, 5, 0, 0, 4, 0, 34, 18, 1, 0, 1, 0, 2]) = true := by native_decide

end Dllbc.Tests.S26Migrate

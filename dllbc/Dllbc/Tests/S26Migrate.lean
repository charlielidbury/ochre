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

**The result: 99 accept on both paths, 57 reject on both, 68 do not migrate, and
NOTHING disagrees.** The 68 are three named classes (§Z below), each a decision
this project has already taken.

(M26-F moved five of these: the corpus's `nth`/`nth2` in S14 and S17 declared
`[v]`, and S26Fuel §C measured that they decrease on their INDEX just as well, so
correcting the hint is one field with no other change. The whole S14 family
migrated — 0/0/5 became 4/1/0 — and the S17/S19 copies still decline, on their
declared `back` rather than on their hint.)

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

    One per corpus file: every `FnDef` it defines, plus the imported ones its own
    tables use (S19 checks against S17's `nth`/`nth2`/`swapS`). A pool that is
    missing a callee makes both paths reject for the same wrong reason, so
    completeness matters — and the counts are what expose it. -/

-- S5Bound is written as PROGRAMS now (M28 ν) and declares no `FnDef` at all, so
-- its pool is gone rather than empty. Neither of its two (`push` by take-and-
-- rebuild, `push` on the Σ-paired vector) was a decliner, so §B's residue is
-- unchanged by the removal — which is the check that the pool carried nothing
-- but inventory.
-- S6Call is written as PROGRAMS now (M28 ι), so it declares one `FnDef`: the
-- `[v]` payload-decrease shape, which is kept as a declaration precisely because
-- `S26Fuel` §A compares it against its fuel-threaded twin. The survey shrinks with
-- the file rather than pretending the declarations are still there.
def p6 : List FnDef := [S6Call.zeroAll]
def p7 : List FnDef := [S7Group.choose, S7Group.chooseCaller, S7Group.through, S7Group.throughCaller]
def p9 : List FnDef := [S9Diff.through, S9Diff.advance, S9Diff.choose, S9Diff.push]
-- S10Ford's declaration half is written as PROGRAMS now (M28 ν) — its library
-- half never had a pool entry, being `hasType` derivations over `Val`s — so `p10`
-- is gone with `p5`. None of its five contributed a decliner either.
def p11 : List FnDef := [S11Lib.retRefl, S11Lib.storeProof, S11Lib.discharge]
def p12 : List FnDef := [S12Inst.useRefl, S12Inst.callerRet, S12Inst.symCall, S12Inst.needs,
  S12Inst.callNeeds1, S12Inst.callNeeds3, S12Inst.observe, S12Inst.observeGood,
  S12Inst.observeBad, S12Inst.needsLe22, S12Inst.refineTest, S12Inst.classify]
def p14 : List FnDef := [S14Bounds.nth, S14Bounds.nth2, S14Bounds.swap, S14Bounds.cascade,
  S14Bounds.rejectProbe]
def p15 : List FnDef := [S15Elab.useTrans, S15Elab.badRefl]
def p16 : List FnDef := [S16Spec.swapS01, S16Spec.swapCaller]
def p17 : List FnDef := [S17Spec.throughOk, S17Spec.caller,
  S17Spec.throughOpaque, S17Spec.nthS, S17Spec.nth2S, S17Spec.swapSN, S17Spec.spcCaller]
def p18 : List FnDef := [S18Rewrite.certConsHit, S18Rewrite.certConsHitLie]

def p19 : List FnDef := [S17Spec.nthS, S17Spec.nth2S, S17Spec.swapSN,
  S19Partition.certSwapCount,
  S19Partition.certSwapCountLie,
  S19Partition.pivotPlace,
  S19Partition.pivotPlaceH,
  S19Partition.partScanE,
  S19Partition.partitionE,
  S19Partition.stuckProbe,
  S19Partition.stuckProbeLie,
  S19Partition.stuckProbeNonExh,
  S19Partition.lebProbe,
  S19Partition.exitReject,
  S19Partition.twoRec]

def p23 : List FnDef := [S23Direct.pinOne, S23Direct.useIt, S23Direct.usePin, S23Direct.useItLie,
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

def p24 : List FnDef := [S24Arrays.halves, S24Arrays.noEvidence, S24Arrays.wrongEvidence,
  S24Arrays.rigidLength, S24Arrays.walk, S24Arrays.walkArr, S24Arrays.touch, S24Arrays.callSeg,
  S24Arrays.fill1, S24Arrays.bump, S24Arrays.idxCited, S24Arrays.rng1Cited,
  S24Arrays.idxWeakBound, S24Arrays.threeWayTouch, S24Arrays.splitTwo, S24Arrays.pivotCarve,
  S24Arrays.sigSlice, S24Arrays.useSlice, S24Arrays.sliceTouch, S24Arrays.sigCallerOk,
  S24Arrays.sigCallerWrong, S24Arrays.recSlice, S24Arrays.threeWay, S24Arrays.threeWayNoFirstEv,
  S24Arrays.threeWayUncited, S24Arrays.threeWayWrongEq, S24Arrays.threeWayLyingResidue,
  S24Arrays.sliceTake, S24Arrays.threeWayCall, S24Arrays.setSorted, S24Arrays.setSortedLie,
  S24Arrays.readTwo, S24Arrays.sort2, S24Arrays.sort2LieSorted, S24Arrays.sort2LieCount]

def p25 : List FnDef := [S25ArrSort.splitA, S25ArrSort.partitionA, S25ArrSort.quicksortA,
  S25ArrSort.splitALieLen, S25ArrSort.splitALieSp, S25ArrSort.splitALieCount,
  S25ArrSort.splitANoSwap, S25ArrSort.partALieLen, S25ArrSort.partALiePart,
  S25ArrSort.qsALieSorted, S25ArrSort.qsALieCount, S25ArrSort.carveNoEv, S25ArrSort.carveWithEv,
  S25ArrSort.qsANoSuff, S25ArrSort.c6Touch, S25ArrSort.c6PeelCall, S25ArrSort.c6CarveNoCall,
  S25ArrSort.c6Swap, S25ArrSort.c6Rec, S25ArrSort.c6CarveAfterCall, S25ArrSort.twoCursor,
  S25ArrSort.twoCursorRes, S25ArrSort.citedCarve]


/-! ## §Y. The reports are gone (M27-δ)

    One assertion per file compared the two paths' verdicts, with three counts
    keeping `disagree = []` from holding vacuously. There is one path now, so
    there is nothing to compare and the harness died with `checkFn`.

    **Its finding is what to keep, and it is recorded in `Migrate.lean` beside
    what replaced it: agreement is not coverage.** `report` never compared a
    DECLINING declaration's declaration-path verdict, so `disagree.isEmpty` was
    true throughout while 27 of the 42 declarations that stopped declining under a
    strip became REJECTS. That is what hid fourteen S19 regressions until a
    deletion exposed them.

    The POOLS below survive: they are the corpus's own inventory, and `S27Dispose`
    reads them. -/

/-- The corpus total, as one number each, so that a file quietly dropping out of
    the survey is visible even if its own assertion was deleted with it. -/
def pools : List (List FnDef) :=
  [p6, p7, p9, p11, p12, p14, p15, p16, p17, p18, p19, p23, p24, p25]

-- (the corpus-total assertion went with `report`; the pools themselves are the
-- inventory, and every declaration in them is asserted in its own file)


/-! ## §Z. What did not migrate, and why — three classes, each already decided

    A migration report that could not say "this one did not move" would be the
    quietly-wrong thing, so the declines are classified rather than counted. All
    68 fall into three classes, and each class is a decision this project took
    before this phase started. -/

-- Z1. **A declared `back`** — RETIRED WITH THE MECHANISM (M27-P2). This class
-- was the biggest of the three: §6.2's backward specs had no seal counterpart,
-- because the ensures IS the contract now (§5 point 4). There is nothing left to
-- assert — no declaration in the corpus declares one, which is the class emptying
-- rather than the test passing. `S27Dispose` §C records where each carrier's
-- claim went.

-- Z3. **A recursion the eliminators cannot express.** Two shapes now that
-- `listRec` is wired: a self-call at a non-predecessor (the guard twins
-- `recSame`, `recWrongIdx`, `recGrow`), and — the one that is a genuine
-- expressiveness limit rather than a twin — `recDeep`, which recurses TWO
-- constructors down. An arm gets `ih` at the immediate predecessor and nothing
-- below it, so a legal-by-the-guard two-step recursion has no single-recursor
-- form.
example : (match FnMacro.fnElab S23Direct.recDeep with
           | .error e => strContains e "not the predecessor"
           | .ok _ => false) = true := by native_decide

-- …and a `List` recursion is no longer one of them: `recList` MIGRATES, which is
-- the only corpus program that exercises the kernel's `listRec` sealing path
-- through the macro rather than by hand.
example : (match FnMacro.fnElab S23Direct.recList with
           | .error _ => false
           | .ok t => progOk (.letIn ⟨900, "recList"⟩ t .unit)) = true := by native_decide
-- The scrutinee-type refusal survives for what neither eliminator serves.
example : (match FnMacro.fnElab { S23Direct.recList with
             telescope := [("l", .const "Bool")], retType := .idT (.const "Nat") (.ctorApp "Z" []) (.ctorApp "Z" []),
             body := .ctorApp "Refl" [] } with
           | .error e => strContains e "neither `Nat` nor `List A`"
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

/-! ## §V. The `back` blocker — RETIRED, and the section with it

    This section measured which of two blockers was load-bearing, and its answer
    ("neither alone; a cohort is a CLOSURE") is the finding worth keeping. Its
    INSTRUMENT is gone: `stripBacks` strips a field no declaration carries, so
    every assertion here would now be a tautology about an empty set.

    What the measurement concluded, preserved because the numbers are the argument
    for what M27 then did: 73 declines as the corpus stood; 68 with the two `[k]`
    hints corrected; 65 with `back` stripped; **20 with both**. Neither fix moved
    the report alone and together they collapsed it, because S17's `nth` had BOTH
    blockers and everything reaching it declined with it. "Fix the biggest class
    first" is exactly the wrong strategy against a closure.

    And the one this file could not see, recorded beside it: **agreement is not
    coverage.** `report` never compares a DECLINING declaration's declaration-path
    verdict to anything — `progVerdict` returns `none` and the comparison skips —
    so `disagree.isEmpty` was true throughout while 27 of the 42 declarations that
    stopped declining under a strip became REJECTS. A comparison harness must also
    measure verdict SURVIVAL, or a declining cohort's regressions are invisible. -/

end Dllbc.Tests.S26Migrate

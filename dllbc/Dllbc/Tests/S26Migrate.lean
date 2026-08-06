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
-- S7Group is written as PROGRAMS now (M28 ν) — its two callers were already
-- hand-built `FnDef`s wrapping a `prog{ }` body, so migrating them was deleting
-- the wrapper. `p7` goes with `p5`/`p10`/`p12`; none of its four was a decliner.
-- S9Diff's callee pool is a `fn` PREFIX now (M28 σ), not four declarations, so it
-- contributes nothing to a survey of declarations. None of the four declined, so
-- §B's residue is unaffected — which is the check that this is a subject leaving
-- and not a verdict changing.
def p9 : List FnDef := []
-- S10Ford's declaration half is written as PROGRAMS now (M28 ν) — its library
-- half never had a pool entry, being `hasType` derivations over `Val`s — so `p10`
-- is gone with `p5`. None of its five contributed a decliner either.
-- S11Lib is written as PROGRAMS now (M28, cluster C) — its three pure-lift
-- subjects were raw `FnDef` records on a keep-rationale that expired with `pure{ }`
-- and juxtaposition application, so `p11` goes with `p5`/`p10`/`p12`. None of the
-- three was a decliner, so §B's residue is unchanged by the removal, which is the
-- check that the pool carried nothing but inventory.
-- S12Inst is written as PROGRAMS now (M28 ν): each of its call cohorts is a `fn`
-- chain, which is the pool this entry used to name, said in the grammar. `p12` is
-- gone with `p5` and `p10`, and none of its twelve was a decliner.
def p14 : List FnDef := [S14Bounds.nth, S14Bounds.nth2, S14Bounds.swap, S14Bounds.cascade,
  S14Bounds.rejectProbe]
def p15 : List FnDef := [S15Elab.useTrans, S15Elab.badRefl]
-- S16Spec is written as PROGRAMS now (M28 ν): `swapS01` is a prefix helper and its
-- caller a spliced tail, so neither is a `FnDef`. `p16` joins p5/p7/p10/p12; neither
-- was a decliner.
-- S17Spec's two nullary CALLER wrappers are programs now (M28 ν) and have left
-- the pool; the five that remain are the callee tables its `tailEnvs`/`runExec`
-- assertions pair one caller body against, and `p19` below reads three of them.
def p17 : List FnDef := [S17Spec.throughOk,
  S17Spec.throughOpaque, S17Spec.nthS, S17Spec.nth2S, S17Spec.swapSN]
def p18 : List FnDef := [S18Rewrite.certConsHit, S18Rewrite.certConsHitLie]

def p19 : List FnDef := [S17Spec.nthS, S17Spec.nth2S, S17Spec.swapSN,
  S19Partition.certSwapCount,
  S19Partition.certSwapCountLie,
  S19Partition.partScanE,
  S19Partition.partitionE,
  S19Partition.lebProbe]
-- (`stuckProbe` and its two twins, and `twoRec`, are programs since M28 ψ and
-- assert themselves in their own file.)

-- S23Direct is migrated in PART (M28 ν): the 26 declarations that nothing outside
-- the file consumed are programs now and have left the pool. What remains is what
-- other files hold as VALUES — the quicksort/partition/splitOff/setAt/swapAt/
-- insertAt families, their record-update lie twins, and the recursion-guard twins
-- `S27Dispose` §B pins by name.
-- The recursion-guard family left the survey in M28 φ: they are `prog{ fn … }`
-- programs now, asserted directly as accepted or rejected in `S23Direct`, so
-- there is no declaration here to survey.
-- (`split_off` and its four twins are programs since M28 D1 — one `soUnder`
-- skeleton, one accept and four rejects, asserted in their own file. None of the
-- five was a decliner, so §B's residue is unchanged by their leaving, which is the
-- check that the pool carried inventory and not a verdict.)
-- (`set_at`/`swap_at` and their four twins are ONE program since M28 D2 — the
-- `setSwapUnder` chain — and left with the same argument. None was a decliner.)
def p23 : List FnDef := [S23Direct.recCursor,
  S23Direct.appendBack,
  S23Direct.partition,
  S23Direct.partitionLoses, S23Direct.quicksort,
  S23Direct.qsLieSorted, S23Direct.qsLieCount, S23Direct.qsStaleBound, S23Direct.qsNoSuff]

-- S24Arrays is written as PROGRAMS now (M28 ν) and declares exactly two `FnDef`s:
-- `walk` and `walkArr`, the same function with the decreasing argument moved,
-- which `S26Fuel` §B compares FIELD BY FIELD and so consumes as values. The pool
-- shrinks to them, and `walkArr` is the entry that matters — it is this file's
-- only contribution to §B's declining residue.
def p24 : List FnDef := [S24Arrays.walk, S24Arrays.walkArr]

-- S25ArrSort is migrated in PART (M28 ν): its self-contained probes are programs,
-- and the array flagship is not. `splitA`/`partitionA`/`quicksortA` are consumed as
-- VALUES — `S26Prog` §(vi) assembles them with `FnMacro.progOf` to run the sort on
-- real inputs, and every lie twin is a record update on one of them
-- (`{ splitA with retType := … }`), which is a `FnDef` operation and not a program
-- one. `citedCarve` stays as the table its two callers and `runsAtAll` share.
def p25 : List FnDef := [S25ArrSort.splitA, S25ArrSort.partitionA, S25ArrSort.quicksortA,
  S25ArrSort.splitALieLen, S25ArrSort.splitALieSp, S25ArrSort.splitALieCount,
  S25ArrSort.splitANoSwap, S25ArrSort.partALieLen, S25ArrSort.partALiePart,
  S25ArrSort.qsALieSorted, S25ArrSort.qsALieCount,
  S25ArrSort.qsANoSuff, S25ArrSort.citedCarve]


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
  [p6, p9, p14, p15, p17, p18, p19, p23, p24, p25]

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
example : progRejects S23Direct.recDeep "not the predecessor" = true := by native_decide

-- …and a `List` recursion is no longer one of them: `recList` MIGRATES, which is
-- the only corpus program that exercises the kernel's `listRec` sealing path
-- through the macro rather than by hand.
example : progOk S23Direct.recList = true := by native_decide
-- The scrutinee-type refusal survives for what neither eliminator serves. Written
-- as the program it describes rather than as a record with three fields replaced.
example : progRejects (prog{ fn recBool [l] (l : Bool) -> Id Nat Z Z { Refl }; () })
  "neither `Nat` nor `List A`" = true := by native_decide

/-! ## §W. The two bugs the report found, pinned as regressions

    Both were invisible to every test that existed, and both would have shipped a
    migration that builds. -/

-- W1. THE HOIST PERMUTATION. `swap_at` calls `set_at [i]`, whose decreasing
-- parameter is SECOND, so the sealed callee's telescope is `(i, v, x, hi)` while
-- the call is written `(&mut *v, j, a, p2)`. Before the fix the borrow was checked
-- against `i : Nat` — "hasType: cannot type value borrowₘ".
--
-- BOTH pins are now `fn` chains in `S23Direct` and assert the same thing there:
-- `swap_at` writes its call in DECLARATION order inside `setSwapUnder` (M28 D2)
-- and `pick` does the same inside `insUnder`'s (M28 χ), and each chain retargets
-- the call into its callee's `[k]`-hoisted telescope. Same bug, same pin, stated
-- as the programs it is about.
example : progOk S23Direct.setSwap = true := by native_decide
example : progOk S23Direct.pick = true := by native_decide

-- W2. THE SILENT REPAIR. `recGrow` recurses on itself and the declaration path
-- rejects it; the macro used to drop the scrutinee argument unexamined and emit an
-- `ih` — a recursor on the PREDECESSOR, which is a different function and checks.
-- Now refused. Kept beside its honest sibling, so the refusal is about the
-- argument and not about the shape.
example : progRejects S23Direct.recGrow "not the predecessor" = true := by native_decide
example : progOk S23Direct.recGood = true := by native_decide

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

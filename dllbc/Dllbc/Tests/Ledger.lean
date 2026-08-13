import Dllbc.Program
import Dllbc.ProgMacro
import Dllbc.Tests.Direct
import Dllbc.Tests.ArraySort
import Dllbc.Tests.Programs

/-!
# The disposition ledger — what every retired mechanism's claims became

**A consolidation bucket** (M28 D10). The suite grew one file per milestone, which
made a test's home a fact about WHEN it was written rather than about what it is
about. These files were merged here, in the order below, with their content moved
VERBATIM — every namespace kept, so every cross-file reference in the tree still
resolves, and each former file is fenced by a comment naming it so the git-log
archaeology survives:

  * `S27Dispose.lean`

Each former file's `open`s are scoped by a `section`, so nothing leaks across the
seams.
-/

-- ┌── was `Dllbc/Tests/S27Dispose.lean` ──────────────────────────────────────────────
section
/-!
# §27 (M27-P1) — a disposition for every declaration the program path declines

The endgame deletes `FnDef`, the `back` machinery and the `[k]` guard. Before any
of that comes off, every declaration that does not have a program form needs a
**written disposition** — ported, paid, or retired with a reason. A decliner that
is merely dropped is a coverage loss disguised as a migration, and the whole point
of M26-E's comparison harness was that such a loss is invisible to a build.

So this file is the ledger, and it is a **computation rather than a list**: the
dispositions below are keyed to the harness's own `refusal`, and §A asserts the
decliner set is exactly the one the dispositions cover. A declaration that starts
or stops declining turns this file red, which is the only way a ledger stays true
after the thing it describes moves.

## The map, and why its headline number changed under us

M26-E measured "eight declarations are blocked by `back` alone" and the endgame was
framed against that eight. M26-F (`0db50c71`) then adopted the corrected `[i]`
hints at the source, which took the *other* blocker off the same declarations —
and the eight became **49**, because `back` is now the only thing standing under
the rest of the corpus.

Nothing about the map was wrong; this is e4222291's closure lesson arriving from
the other side. Neither blocker moved the report alone, so "which one is
load-bearing" was never a property of either one — it was a property of which one
came off last. What the endgame has to dispose of is therefore three different
sizes, and keeping them apart is most of the clarity:

  * **the closure** — declarations that MIGRATE when `back` is stripped, needing
    no disposition at all: they are ordinary programs the moment their cohort's
    leaf stops declining. 49 when this ledger was written; 42 once M27-P2 retired
    the surface-test pools, which is the same fact at a smaller corpus.
  * **21 pool entries** — declarations that actually DECLARE a `back`. The only
    set whose SOURCE has to change (§C). It was 28 before the four surface-test
    files retired with the `back = …` syntax they existed to round-trip.
  * **19** — the residue that survives the deletion, which is the true `[v]`
    payload-decrease class plus the guard twins (§B).

And one distinction the framing does not draw, which shrinks §C a great deal:
**stripping the `back` field is not deleting the declaration.** The back-carrying
functions are callees of the ensures-era stratum — `quicksortE`, `quicksortSorted`,
`partitionRangeE` and their lie twins all reach `partScanRange` or `nth2` — so they
survive as functions minus their backward specs. What retires is the *assertions*
whose subject is the back, not the code under them.
-/

open Dllbc

namespace Dllbc.Tests.S27Dispose

open Dllbc.Tests
open Dllbc.StdLemmas (Ub Lb Len)

/-! ## §A. The instrument, asserted before any conclusion

    §B's residue was computed over the corpus's own declaration pools with the
    harness's `refusal`, so that the ledger and the comparison could not drift
    apart. The strip was asserted to have HAPPENED first — the
    `{ d with back := none }` gotcha (e4222291) produced a "stripped" pool identical
    to the original, and read at face value it said the exact opposite of the
    truth. -/

/-! **EXECUTED (M27-P2), and the assertion cannot be written any more.**

    This section used to count `back`-declaring declarations and assert the count.
    `FnDef.back` no longer exists, so `(·.back.isSome)` does not typecheck — the
    claim "no declaration declares a backward spec" is now a fact about the TYPE
    rather than a property of the corpus, which is the strongest form it can take
    and the form that needs no test. A reappearance would not turn this file red;
    it would fail to compile, everywhere at once.

    What remains assertable is the shape of the corpus after the retirement. -/

/-! **AND THE CENSUS RETIRED WITH IT** (M28 μ). This section also carried the
    corpus totals — 105 accept, 58 reject, 19 decline. `fn` is a statement of the
    program grammar now, so a declaration that becomes a program leaves the pools,
    and the totals moved once per migrated file for a reason that was never a
    verdict changing. A count whose subject is dissolving is bookkeeping, not a
    claim. §B's residue is the part that was load-bearing, and it is below, by
    name. -/

/-! ~~…and the two paths still agree everywhere, which is the property the whole
    comparison exists for.~~ **The second path is gone** (M27-δ), so there is no
    agreement left to assert — and the narrow reading it always needed is the
    thing to carry: **agreement is not coverage.** It said the two paths reached
    the same verdict and said NOTHING about a declining declaration, whose
    declaration-path verdict `report` never compared to anything. That gap hid
    fourteen S19 regressions until a deletion exposed them (§C). What replaces it
    is §B's residue, which cannot skip a decline: a declaration that starts or
    stops declining appears or vanishes there BY NAME. (The corpus tally stood here
    between M27-δ and M28 μ and did the same job by arithmetic; the residue does it
    with identity attached, which is why it is the one that survived.) -/

/-! ## §B. The residue: CLOSED

    This section was the endgame's instrument. Every declaration the program path
    DECLINES needed a written disposition — ported, paid, or retired with a reason —
    because a decliner that is merely dropped is a coverage loss disguised as a
    migration, and M26-E's whole point was that such a loss is invisible to a build.
    So the dispositions were keyed to the harness's own `refusal`, computed over
    `S26Migrate.pools` by `declinedWith`, and asserted NAME FOR NAME: a decliner
    appearing or vanishing turned this file red before it could go unnoticed
    anywhere else.

    It counted down 19 → 11 → 2 → 0, and then the instrument itself dissolved. The
    residue is derived from the POOLS, the pools are the corpus's declarations, and
    the corpus has none: `S26Migrate` is deleted (M28 D8) because every `FnDef` it
    inventoried is a `fn` statement in the file that owns it.

    **An empty ledger and a deleted instrument is exactly what a coverage loss also
    produces, so what replaced each entry is worth stating rather than asserting**,
    since there is nothing left to assert it against:

      * **The `back` class** retired with the mechanism in M27-P2 — no declaration
        can declare one, which is a fact about the TYPE and needs no test.
      * **The guard twins** (`recSame`, `recWrongIdx`, `recGrow`, `recDeep`) became
        programs in M28 φ and are `progRejects … "not the predecessor"` in
        `S23Direct`, which is §B3/§B4 below.
      * **The `[v]` payload-decrease class** — `zero_all`, `recCursor`,
        `append_back`, `partition`, `partitionLoses`, `quicksort` and its twins,
        `walkArr` — was REWRITTEN. Each survivor is a program refused on
        `FnMacro.fnRefusedNeedle`, with "§12 decision 8" in the message and
        `progOk = false` to say the sentinel fires at the BINDING rather than at a
        call; and each has a fuel-threaded twin that CHECKS, in the same file, a few
        lines away. That is strictly more than a name in a computed list.

    A decline is louder written out than counted, and that is why the ledger could
    close rather than merely empty. -/

/-! ### B1. PAID — every one, and where

    The disposition is asserted rather than cited, so that "the disposition exists"
    is a build fact and not a cross-reference a later deletion could falsify. -/

-- `zero_all` (S6) is §7 cost 4's own example: a cursor with no decreasing argument
-- but the payload. Its fuel-threaded twin checks.
example : progOk S26Fuel.zeroAllF = true := by native_decide
-- `walkArr` (S24) is a NEGATIVE control, and its honest twin `walk` was paid in
-- M24 — before decision 8 existed. Nothing to port: the two differ in the HINT
-- alone, and `S24Arrays` asserts both halves adjacently — `walk` accepted,
-- `walkArr` refused at `[a]`-on-a-borrow with the decision in the message.
example : progOk S24Arrays.walk = true := by native_decide
-- `append_back`, `partition` and `quicksort` are paid IN THE SOURCE now: the
-- flagship cohort is one fuel-threaded chain and it CHECKS, which is the strongest
-- form the "paid" claim can take — there is no un-migrated original left for it to
-- be paid against.
example : progOk S23Direct.flagship = true := by native_decide
-- …and the array lane needed no payment at all: it was already fuel-threaded, so
-- decision 8 costs it nothing. Same claim, other container.
example : progOk S25ArrSort.arrChain = true := by native_decide

/-! ### B2. THE GAP THIS LEDGER FOUND — the twins, and where they went

    B1's entries are the HONEST functions. Every one of them is guarded in the
    corpus by lie twins, and **the twins were not migrated with them**: the
    fuel-threaded `partition` was written with no lies at all, and `S26Prog`'s
    battery covered three of `quicksort`'s four. So the paid path was, until this
    file, checking that the honest program is accepted without checking that it
    still refuses anything — which is the half of a differential that can pass
    vacuously. That is a coverage gap rather than a decliner, which is why counting
    declines never surfaced it.

    This section closed it twin for twin, on `FnDef` record updates
    (`{ partitionF with retType := … }`) held to a transform oracle. **All six now
    live beside the functions they guard** (M28 D3): `S23Direct`'s chain takes
    `partition`'s return type, `quicksort`'s, and `quicksort`'s sufficiency
    hypothesis as parameters, so four partition spec lies, two quicksort spec lies
    and the weakened hypothesis are each one varied argument on a shared body, and
    the two BODY twins — `partitionLoses` and `qsStaleBound` — are transcribed
    there for the reason M28 D1 named.

    **The bar this section set survives the move, and it is worth restating because
    it is subtle**: a lie twin that DECLINES teaches nothing — the migration simply
    failed to produce a program — so each twin had to MIGRATE and then be refused,
    which is what `neitherWay` asserted and what a decline-tolerant helper would
    have quietly let through. A `progRejects` on a chain is that bar by
    construction: the chain lowers or the needle is `fnRefusedNeedle`, and the six
    twins are caught on "does not have return type" instead.

    The one thing that does NOT survive the move is the `dropHead` ORACLE — the
    proof that `partitionLoses` really is `partition` with one write changed,
    computed rather than claimed. It was a term-rewriting comparison between two
    `FnDef` bodies, and there are no `FnDef` bodies to compare. What replaces it is
    weaker and honest about being weaker: the differing line carries a comment
    saying it is the lie, and the two bodies are adjacent in one file. -/

/-! ### B3. RETIRE WITH THE GUARD — `recSame`, `recWrongIdx`, `recGrow`

    These three are the guard's own negative controls: a self-call at the same
    argument, at a different one, and at a LARGER one. Their subject is the
    snapshot-subterm check, and the endgame deletes it, so they are tests of a
    deleted feature and retire with it. That is a rationale rather than a loss, and
    the reason it is not a loss is worth pinning rather than asserting:

    **what the guard policed, the macro refuses and scope makes unwritable.** §7's
    `ih` is a binder at the predecessor, so a self-call at anything else has nothing
    to become — `fnElab` says so — and §8's let-chain cannot reference downward, so
    the un-elaborated form resolves to no function at all. Two mechanisms, neither
    of them a decrease check, and both survive the deletion. -/

def guardTwins : List Term := [S23Direct.recSame, S23Direct.recWrongIdx, S23Direct.recGrow]

-- ~~Today: the declaration path rejects each at the guard…~~ The guard is gone
-- (M27-δ), and so is the path that fed it. What is left is the reason that
-- OUTLIVED it, which is what this section was always about:
example : guardTwins.all (fun t => progRejects t "not the predecessor") = true := by native_decide
-- Not vacuous: the honest sibling elaborates, so the three refusals are about the
-- argument and not about the shape.
example : progOk S23Direct.recGood = true := by native_decide

/-! ### B4. `recDeep` — the limit is a MOTIVE the macro does not derive, not a
    recursion the eliminators cannot express

    §12 open 3 files `recDeep` as "§7's genuine expressiveness limit": a recursion
    two constructors down, legal under the guard, with "no single-recursor form,
    because an arm gets `ih` at the *immediate* predecessor and nothing below it".

    The brief asked for a hand-written attempt before retiring it, and the attempt
    succeeds — so the filing is **too strong and is corrected here.** What an arm
    gets is `ih` at the predecessor *of the motive it was given*, and the motive is
    a choice. Two constructions, in increasing generality:

    1. **`recDeep`'s own motive is CONSTANT** (`Π (n : Nat) → Id Nat Z Z` — nothing
       depends on `n`), so `ih : P a` already IS `P b` for every `b`. The direct
       recursor expresses it verbatim, and that is what the program below checks.
    2. **The general two-down shape** — where `P` really does depend on `n` — has
       a described route and NOT a mechanized one, and the distinction is left
       standing rather than blurred: a course-of-values motive `Q m := P m × P (S m)`,
       whose base arm inhabits `P 0` and `P 1` directly and whose step arm at `a`
       with `ih : Q a` returns `Pair(snd ih, fst ih)` — `P (S a)` is `ih`'s second
       component and the two-down call `f a` is its first — then one projection at
       the end. One `natRec`, one stronger motive. Nothing below checks this; it is
       filed as the route, and only construction 1 is a build fact.

    So the limit is real but it is a **macro** limit, not a calculus one: `fnElab`
    derives the motive mechanically from the signature (§7: "the motive is derived
    from the signature — so the macro needs no inference"), and neither of these
    motives is that one. That is the same shape as §9's own survey warning — "the
    eliminator must accept a motive stronger than the signature, plus a weakening
    step" — arriving a second time, from the other end of the language, before §9
    is built. Filed as a macro capability rather than as an expressiveness wall. -/

def deepSealT : Term := prog{ Π (n : Nat) → Id Nat Z Z }
def deepMotT : Term := prog{ λ (n : Nat). Id Nat Z Z }

/-- `recDeep`, hand-written as a sealed recursor. The step arm keeps the corpus's
    own inner `match a` — so the two-constructors-down SHAPE is still there — and
    reaches `ih` from inside it, which is exactly the move the macro refuses to
    make on the author's behalf.

    **The base arm binds the unit binder** (M33b). It was written `Term.lamTel []
    ⟨body⟩` — an empty telescope, which the one-λ fold turns into the body itself —
    and that is now refused: an arm that is not a λ is not a suspension, so it runs
    when the SPINE is formed rather than when ι selects it. The binder the fold ate
    is named here, exactly as `fnElab` names it for a `fn`; `deepBaseArmBare` below
    keeps the old spelling as the rejected twin. -/
def deepBaseArm : Term :=
  Term.lamTel [(unitBinder, .cmpT (.const "Unit"))] (.ctorApp "Refl" [])
def deepBaseArmBare : Term := Term.lamTel [] (.ctorApp "Refl" [])
def deepStepArm : Term :=
  -- `ih`'s domain is the motive at the predecessor, and `deepMotT` is CONSTANT —
  -- which is the whole content of the correction this section records: `ih : P a`
  -- already IS `P b` for every `b` when `P` ignores its index.
  Term.lamTel [(⟨0, "a"⟩, .const "Nat"), (⟨1, "ih"⟩, prog{ Id Nat Z Z })]
    (.matchE ⟨0, "a"⟩ none
      [ .mk "Z" [] (.ctorApp "Refl" [])
      , .mk "S" [⟨2, "b"⟩] (.var ⟨1, "ih"⟩) ])
def deepRec : Term :=
  .app (.app (.app (.const "natRec") deepMotT) deepBaseArm) deepStepArm
def recDeepProg : Term := .letIn ⟨900, "F"⟩ (.seal 0 deepRec deepSealT) .unit

example : progOk recDeepProg = true := by native_decide

/-- …and the same program with the base arm left BARE is refused, naming the
    wrap. The two differ in one binder, which is what makes the accept above about
    the arm's shape rather than about the program. -/
def recDeepBare : Term :=
  .letIn ⟨900, "F"⟩ (.seal 0
    (.app (.app (.app (.const "natRec") deepMotT) deepBaseArmBare) deepStepArm) deepSealT) .unit
example : progRejects recDeepBare "is a bare term, not a λ" = true := by native_decide

/-- **The seal really audits it**, so the acceptance above is not the node waving
    a term through: ascribe the same recursor at a Π that claims `Id Nat Z (S Z)`
    and the arms cannot inhabit it. -/
def deepSealLie : Term := prog{ Π (n : Nat) → Id Nat Z (S Z) }
def recDeepLie : Term :=
  .letIn ⟨900, "F"⟩ (.seal 0 (.app (.app (.app (.const "natRec")
    (prog{ λ (n : Nat). Id Nat Z (S Z) })) deepBaseArm) deepStepArm) deepSealLie) .unit
example : progOk recDeepLie = false := by native_decide

/-- …and the MACRO still declines the declaration, which is the whole content of
    the correction: the form exists, `fnElab` does not reach it. -/
example : progRejects S23Direct.recDeep "not the predecessor" = true := by native_decide

/-! ## §C. The 28 back-declaring entries, and what each one's deletion costs

    §B disposed of the declarations that survive the deletion. This section
    disposes of the ones that CAUSE it — the only set whose source has to change —
    and the classification is asserted rather than described, so that a
    declaration quietly gaining or losing a `back` moves this file. -/

-- `backNames` retired with the field it read.

/-! ### C1. SEVEN SURFACE TESTS — RETIRED in M27-P2, with the syntax they tested

    `SDeclMacro`'s `through'`/`swapS'`/`nth'`, `SDeclMacroCrown`'s `quicksortSig`,
    and `SDeclUnified`'s `nthU`/`permuted`/`pivotPlaceHU` are round-trip tests of
    the `decl{ … }` SURFACE: each asserts that a written `back = …` parses to an
    expected `FnDef` field. When the field goes, the subject goes with it — there is
    no claim underneath to re-express, because the claim WAS the parse. These
    retire, and the rationale is that a test of a deleted syntax is not coverage.

    `quicksortSig` is the one worth naming individually, because it is labelled
    THE CROWN: it is the M22-era quicksort signature — the `hbnd` telescope and
    `back = SortRangeL fuel lo cnt (*v)` — verified against `SInternals`'
    transcription of the corpus. It is the highest-water mark of the declaration
    surface, and it is exactly what Architecture A's retirement retires. -/

/-! ### C2. S17Spec — the mechanism's own file, and where its claims land

    Five entries, three distinct subjects, and only one of them is a coverage
    question:

      * `throughLie` is a **lying-BACK control**: it declares `back = λ r. Cons(1,Nil)`
        for a body that returns its argument, and asserts the callee check catches
        it. It tests the back mechanism itself and retires WITH the mechanism. Not
        a coverage loss — a test of a deleted feature.
      * `throughOk` + `caller` are the **precision payoff**: the caller recovers the
        written `Cons(9,Nil)` in CHECKING mode, against `throughOpaque`'s fresh σ.
        Deleting `back` deletes the precision, BY DESIGN — §5 point 4 is that what
        you keep is what you ascribe, and `Π (b : &mut List Nat) → &mut List Nat`
        ascribes nothing about the payload. `throughOpaque`'s behaviour becomes the
        only behaviour.
      * `nthS`/`nth2S`/`swapSN` are the **composition claim**: backward specs
        compose along a call chain, so a caller of `swapS` recovers the exact
        swapped list.

    **The replacement for the last two is not new work — M23 wrote it.**
    `S23Direct.setAt` is `NthL`-plus-write with the relationship as an ENSURES
    (`Id (List Nat) (*v) (Set i x (old *v))`) rather than as a backward spec, and
    `swapAt` is `swapS` the same way (`Id (List Nat) (*v) (SwapL i j (old *v))`) —
    the same two model functions, `Set` and `SwapL`, moved from the `back` field
    into the return type. What the caller learns is strictly more, not less: a
    propositional equation it can rewrite along, rather than a value the group-end
    happened to compute. Asserted below on both paths, with the lie twins that make
    the acceptance non-vacuous. -/

-- The ensures-style pair checks, as ONE program declaring both — which is also the
-- shape the claim wants, since the point is that a CALLER learns the equation.
example : progOk S23Direct.setSwap = true := by native_decide

-- …and refuses the four lies about exactly the facts the backs used to carry: the
-- index moved, and the update claimed to be a no-op. Asserted where the pair is
-- written (M28 D2, the `setSwapUnder` skeleton): each twin varies one of the
-- chain's two return-type parameters and the other stays honest, so the four
-- rejections are attributable, one per function per lie. This line used to restate
-- them through `neitherWay` on `FnDef` record updates; the restatement is what
-- retires, not the coverage.

-- That the two name the SAME model function (`SwapL` in `swapSN`'s declared back,
-- `SwapL` in `swapAt`'s return type) is a reading of two source lines and is left
-- as one — an equality assertion between a `back` and a `retType` would compare
-- two differently-shaped terms and pass for the wrong reason. What IS asserted is
-- the instrument: the corpus still carries the back this section proposes to
-- delete, so C2 is not describing something already gone.

/-! ### C3. S19's Architecture A stratum — twelve entries that keep their bodies

    `pivotPlace`, `pivotPlaceH`, `partScan`, `partScanRange`, `partition`,
    `partitionQ`, `partitionRange`, `quicksort` and their lie twins are the M22-era
    model-conformance corpus: `back = PartitionL …`, `back = SortRangeL …`, an
    imperative program checked as an implementation of a pure model, correctness
    proved about the model. dllbc-arrows §6.2 calls this "the comparison baseline,
    not the mission", and the endgame retires it to history.

    **They keep existing as functions.** Stripping the field is not deleting the
    declaration, and this is the load-bearing distinction: the ensures-era stratum
    in the same file — `swapSE`, `partitionRangeE`, `quicksortE`, `quicksortSorted`
    and their lie twins — REACHES these through its call graph, so removing them
    outright would take Architecture B's own corpus down with Architecture A's.
    What retires is each one's back-specific assertion; what survives is the
    function, and with it the 35 S19 declarations that migrate the moment the field
    is gone.

    ### C4. `twoRec` — the one clean port

    Its `back = *v` is the IDENTITY and entirely incidental: the subject is
    SEQUENTIAL REBORROW, the quicksort recursion shape, and it checks only because
    `&mut` on a place holding a parked loan demand-ends the prior call's group
    before reborrowing. Dropping the field leaves the subject intact — asserted,
    since "incidental" is exactly the kind of claim that should not be taken on
    trust. -/


-- …and the function still checks. The "and now MIGRATES" half went with the
-- declaration path (M28 ψ): `twoRec` is a `prog{ fn … }` now, so there is no
-- migration to succeed — being writable at all is the stronger form of the same
-- claim. What this line still pins is §C's: dropping the `back` field left the
-- subject intact.
example : progOk S19Partition.twoRec = true := by native_decide

/-! ## §D. INSTRUMENT RETIREMENT — a third disposition class, and the one no
    measurement in this campaign could see

    §B disposed of declarations that survive the deletion and §C of the ones that
    cause it. Both were derived from the corpus's declaration POOLS, and **the pools were the
    TEST corpus**. `Dllbc/Bench.lean` and `Dllbc/BenchQS.lean` are not in any pool,
    declare fifteen more backs between them, and are `checkFn`'s other consumer.

    They are not tests. They are the `lean_exe bench` / `lean_exe benchqs` compiled
    timing harnesses, and their own headers say why they are invisible: they hold
    "verbatim copies of the test-file definitions", kept deliberately out of the
    test imports so the expensive checks run compiled instead of under
    `native_decide`. A harness that exists BY BEING EXCLUDED from the corpus is
    exactly the thing a corpus-derived map cannot report, and no amount of
    re-running the comparison would have found it — the blind spot was in what the
    instrument was pointed at, not in how it was read.

    **Disposition: they retire WITH `checkFn`**, as their own class rather than as
    tests, because the rationale is different. A test that retires loses a claim
    somebody has to decide is expendable; a timing harness for a deleted code path
    has nothing left to time. The `lean_exe` targets in `lakefile.lean` retire with
    them — they are consumers a grep of `Dllbc/*.lean` does not show.

    **What retires with them is a published number**, and that is why the paper's
    SHA pin is a PRECONDITION of the deletion rather than a close-out chore.
    `paper/sections/06-empirics.typ` reports the conformance audit's 465× speedup
    (84,121 ms to 181 ms) "measured on architecture A's program", fenced there as
    one of three non-comparable measurement sets. It is reproducible today by
    running `lake exe bench`; after the deletion it is reproducible only at a SHA,
    so the paper must name that SHA while the instrument still exists.

    Nothing is asserted here, and that is deliberate: these two files are outside
    every pool, so there is no set-equality this ledger could state about them
    without restating their contents and creating the third copy the whole
    arrangement exists to avoid. The census in the deletion commit is the record. -/

/-! ## §E. THE CLAIM-CARRIER AUDIT — where each retired S19 claim went

    The bar for retiring S19's back-dependent stratum was not "the tests go" but
    "each claim names its live carrier, or is recorded superseded-without-
    replacement with the reason". Here it is, and the headline is that **exactly
    one claim has no carrier, and it dies by design rather than by accident.**

    | retired | its claim | live carrier |
    |---|---|---|
    | `partScan`, `partScanRange` | an in-place swap scan CONFORMS to `PartScanL` | the conformance claim IS the retired architecture; the PROGRAM is carried by `S23Direct.partition` (relational `Ub`/`Lb`/count) and `S25ArrSort.partitionA` |
    | `partition`, `partitionQ`, `partitionRange` | conforms to `PartitionL`; returned index = `PartIdxL` | `S23Direct.partition`; `S25ArrSort.partitionA`, which returns an index under its own ensures |
    | `quicksort`, `quicksortLie` | conforms to `SortRangeL` | `S23Direct.quicksort` — `Σ (Sorted (*v)) → Π n. Count`-preservation, zero declared backs. Strictly stronger, and 21 ms against 21.8 s |
    | `exitAccept` | `Id (*v) (SwapL i j (old *v))` | `S23Direct.swapAt` — literally the same statement, asserted in §C2 |
    | `lenPreserve` | `Id (Len *v) (Len (old *v))` across a swap | derivable from `swapAt`'s equation by `LenSwapL` + `IdCongr`; the equation implies the length fact |
    | `shareCaller` | caller-side σ-sharing: a callee's fact about its own exit forwarded as the caller's | the same mechanism at scale in `S23Direct.quicksort`, which forwards `partition`'s count equation into its own postcondition |
    | `swapSE`, `partitionRangeE`, `quicksortE` | count preservation for swap / partition / sort | the count conjunct of `S23Direct.partition` and `S23Direct.quicksort` |
    | `quicksortSorted` | `Σ (SortedR cnt lo (*v)) → Π n. Count`-preservation | `S23Direct.quicksort` — whole-list structural `Sorted` in place of positional `SortedR cnt lo`, same count conjunct |
    | `qsSpc` | a caller recovers the exact sorted list in CHECKING mode | **no carrier — deleted by design.** §5 point 4: what you keep across a boundary is what you ascribe, and an opaque call ascribes nothing about the payload. The BEHAVIOUR is carried by S23Direct's executing differential against Lean's `mergeSort` and by the list-vs-array cross-differential |
    | `nth2Lie`, `partScanLie`, `partitionLie` | a LYING backward spec is caught at the callee check | tests of the deleted mechanism; retire with it |

    **THE TWO-LINE JUSTIFICATION**, which is the sentence the whole S19 question
    reduces to: porting this stratum to ensures-style is not a signature change but
    a PROGRAM rewrite — measured, since `swapS` given the ensures with its cursor
    body is rejected, its exit being a fresh σ minted by `nth2`'s group. **M23
    already performed that rewrite, and its output is already in the corpus and
    already green.**

    **AND THE SOUNDNESS REASON, which arrived after the decision and confirms it.**
    b1's probe found that the `~>`-hatch cursor contract — the form a "successful"
    port would have used — is accepted UNEARNED today: the containments in
    `S27Mixed.lean` are what close it. So a port that had looked like it worked
    would have been green on a promise nothing checked. The naive conversion was
    never sound, which is a stronger reason to retire than the economics alone. -/

end Dllbc.Tests.S27Dispose
end
-- └── end of what was `S27Dispose.lean` ───────────────────────────────────────────────

-- ┌── the M32 R2 binder-convention debt, measured ───────────────────────────────
section
namespace Dllbc.Tests.S32Binders
open Dllbc

/-! # §2.1's migration, sized — and then RUN against the size

    suspensions.md §2.1 makes capitalisation reach EVERY binder: a capital binder
    is comptime, a lowercase one is runtime, and the modeless-pure-binder
    exemption dies. R2 implemented the READING of that rule everywhere it is
    consulted and measured what renaming the corpus would cost. **R3b spends the
    measurement**, and this battery is where the spending shows: the same
    counter, re-run, is the acceptance evidence for the migration's own class.

    **What R2 keyed the fragment on meanwhile**: `Var.bindsSlot`, i.e. whether the
    binder has an Ω slot id at all (`noSlot` is the sentinel). That is the fact
    that is actually true today, and it is exactly what §2.1's migration makes
    derivable from the NAME — which is what R4 needs, since R4 deletes the ids.

    So the residual is the number of binders on which the two keys still
    disagree: comptime by slot, lowercase by name. Counted over the flagship and
    over two stdlib terms, so R4 inherits a number and not an adjective. -/

/-- Comptime binders (no slot) whose name is neither capitalised nor reserved —
    the ones §2.1's migration would rename, and the ones R4 cannot key on a case
    test until it does. -/
partial def lowerComptime : Term → Nat
  | .lam x d b =>
    (if !x.bindsSlot && !isUpperInit x.name && !isReservedName x.name then 1 else 0)
      + lowerComptime d + lowerComptime b
  | .pi _ d b | .sigmaT _ d b | .borrowT _ d b => lowerComptime d + lowerComptime b
  | .app f a | .seq f a | .seal _ f a => lowerComptime f + lowerComptime a
  | .letIn _ r t => lowerComptime r + lowerComptime t
  | .assign p e r => lowerComptime p + lowerComptime e + lowerComptime r
  | .idT a b c => lowerComptime a + lowerComptime b + lowerComptime c
  | .ctorApp _ as | .call _ as => (as.map lowerComptime).foldl (· + ·) 0
  | .matchE _ _ bs => (bs.map (fun br => lowerComptime br.body)).foldl (· + ·) 0
  | .borrow t | .deref t | .cmpT t => lowerComptime t
  | _ => 0

/-- …and the binders that DO bind a slot, for the ratio: these are the ones whose
    case already carries their mode (§6's rule, which M31 Stage A landed). -/
partial def slotBinders : Term → Nat
  | .lam x d b => (if x.bindsSlot then 1 else 0) + slotBinders d + slotBinders b
  | .pi _ d b | .sigmaT _ d b | .borrowT _ d b => slotBinders d + slotBinders b
  | .app f a | .seq f a | .seal _ f a => slotBinders f + slotBinders a
  | .letIn _ r t => slotBinders r + slotBinders t
  | .assign p e r => slotBinders p + slotBinders e + slotBinders r
  | .idT a b c => slotBinders a + slotBinders b + slotBinders c
  | .ctorApp _ as | .call _ as => (as.map slotBinders).foldl (· + ·) 0
  | .matchE _ _ bs => (bs.map (fun br => slotBinders br.body)).foldl (· + ·) 0
  | .borrow t | .deref t | .cmpT t => slotBinders t
  | _ => 0

/-- **The direction that must be ZERO: a runtime binder with nowhere to put its
    argument.** Lowercase says the argument arrives by ⇒ — moved or loan-seeded
    into the store — so a lowercase binder that binds no Ω slot is a binder whose
    argument has no destination. This is the half of R2's `keyDisagree` that is a
    real invariant, and R4 asserts it at 0. -/
partial def keyDisagree : Term → Nat
  | .lam x d b =>
    (if !x.bindsSlot && !(isUpperInit x.name || isReservedName x.name) then 1 else 0)
      + keyDisagree d + keyDisagree b
  | .pi _ d b | .sigmaT _ d b | .borrowT _ d b => keyDisagree d + keyDisagree b
  | .app f a | .seq f a | .seal _ f a => keyDisagree f + keyDisagree a
  | .letIn _ r t => keyDisagree r + keyDisagree t
  | .assign p e r => keyDisagree p + keyDisagree e + keyDisagree r
  | .idT a b c => keyDisagree a + keyDisagree b + keyDisagree c
  | .ctorApp _ as | .call _ as => (as.map keyDisagree).foldl (· + ·) 0
  | .matchE _ _ bs => (bs.map (fun br => keyDisagree br.body)).foldl (· + ·) 0
  | .borrow t | .deref t | .cmpT t => keyDisagree t
  | _ => 0

/-- …and **the other direction, which is the TELESCOPE RULE and is not zero**: a
    CAPITAL binder that binds an Ω slot. Comptime read mode, store location —
    both, and legitimately, because `seedTelescopeV` slots every parameter and
    capital says how the argument is READ, not where it lands. -/
partial def comptimeSlotParams : Term → Nat
  | .lam x d b =>
    (if x.bindsSlot && (isUpperInit x.name || isReservedName x.name) then 1 else 0)
      + comptimeSlotParams d + comptimeSlotParams b
  | .pi _ d b | .sigmaT _ d b | .borrowT _ d b => comptimeSlotParams d + comptimeSlotParams b
  | .app f a | .seq f a | .seal _ f a => comptimeSlotParams f + comptimeSlotParams a
  | .letIn _ r t => comptimeSlotParams r + comptimeSlotParams t
  | .assign p e r => comptimeSlotParams p + comptimeSlotParams e + comptimeSlotParams r
  | .idT a b c => comptimeSlotParams a + comptimeSlotParams b + comptimeSlotParams c
  | .ctorApp _ as | .call _ as => (as.map comptimeSlotParams).foldl (· + ·) 0
  | .matchE _ _ bs => (bs.map (fun br => comptimeSlotParams br.body)).foldl (· + ·) 0
  | .borrow t | .deref t | .cmpT t => comptimeSlotParams t
  | _ => 0

/-- **λ nodes this term classifies IMPERATIVE.** The number the telescope rule
    protects: if the slot test were swapped for a case test, every `fn` whose
    parameters are all capital would leave this count and lose its audit. -/
partial def impLams : Term → Nat
  | .lam x d b =>
    (if Term.lamImperative (.lam x d b) then 1 else 0) + impLams d + impLams b
  | .pi _ d b | .sigmaT _ d b | .borrowT _ d b => impLams d + impLams b
  | .app f a | .seq f a | .seal _ f a => impLams f + impLams a
  | .letIn _ r t => impLams r + impLams t
  | .assign p e r => impLams p + impLams e + impLams r
  | .idT a b c => impLams a + impLams b + impLams c
  | .ctorApp _ as | .call _ as => (as.map impLams).foldl (· + ·) 0
  | .matchE _ _ bs => (bs.map (fun br => impLams br.body)).foldl (· + ·) 0
  | .borrow t | .deref t | .cmpT t => impLams t
  | _ => 0

-- The in-place quicksort — the flagship, the largest program in the corpus, with
-- its specs and library lemmas elaborated in.

example : lowerComptime Dllbc.Tests.S23Direct.flagship = 0 := by native_decide
example : slotBinders Dllbc.Tests.S23Direct.flagship = 22 := by native_decide

-- Two kernel library terms, hand-written rather than elaborated: `len` and the
-- `Le` predicate the carve rule's premises are stated against.
example : lowerComptime Std.lenFnT = 0 := by native_decide
example : lowerComptime Pure.kLeFn = 0 := by native_decide

/-! **THE MIGRATION IS COMPLETE ON THE FLAGSHIP: 10,777 → 0.**

    R2 measured the debt and refused to run it blind; R3b ran it, in two classes
    and against two enumerated differentials. Every comptime binder in the
    largest program in the corpus — its specs, its library lemmas, and the kernel
    functions those unfold to — now SPELLS its mode, which is what §2.1 asks and
    what R4 needs, since R4 deletes the ids this counter's twin reads.

    Where the number went, since two migrations produced it and they are not the
    same kind of thing:

      * **α, `StdLemmas`: 10,777 → 9,545.** Surface syntax, so `binderDom` put
        the `⇝` on each domain and the rename was the whole change. Behaviour
        invisible; this counter was the only assertion in the tree that moved.
      * **β, `Std`/`Pure`'s hand-written terms: 9,545 → 0**, with 33 of that from
        the test files' own spec binders. These are raw `Term`s with no macro
        between them and the datatype, so capitalising a binder means writing its
        `⇝` too (`Term.clam`/`Term.cpi` exist so the two cannot be written apart).
        That IS a mode flip — `Len`, `Count`, `Le`, `Add` and `Sorted` now
        declare their arguments comptime, so a ⇒-application of one snapshot-reads
        where it used to consume — and the corpus measured the flip at ZERO
        changed verdicts, because the library is only ever applied in ⇝ positions.

    **`slotBinders` is UNMOVED at 22, and that is the point, not an oversight**:
    those are the runtime binders, and the migration was never about them. -/

/-! **R4 SPENT THE INHERITANCE, AND THE ANSWER IS A RULE RATHER THAN A SWAP.**

    R2 keyed the fragment on `Var.bindsSlot` and R3b measured what swapping it
    for a case test would cost: **4 binders in the whole flagship**, all one
    construct — a capital telescope parameter binding an Ω slot, because
    `seedTelescopeV` slots every parameter, comptime or not.

    R4 named them: all four are `Hf`, one `fn`'s proof parameter, appearing once
    per copy of that `fn`; capital, `⇝`-domained, slotted. And the swap does not
    happen, because those two keys **answer different questions**:

      * **case** is the READ MODE — ⇝ or ⇒, erased or moved. §2.1's axis.
      * **`bindsSlot`** is the LOCATION — does the argument land in Ω. The
        TELESCOPE rule: a telescope binder binds a slot regardless of case.

    So R2's `keyDisagree` was counting the two axes' disagreement and calling it
    a residue. It splits here into the direction that is an INVARIANT and the
    direction that is the rule:

      * `keyDisagree` — lowercase and NO slot: a runtime binder whose argument
        has nowhere to land. **Zero**, and it is R4's own assertion.
      * `comptimeSlotParams` — capital and slotted: the telescope rule's own
        population. **Four**, and that is content, not debt.

    What R4 did deliver against the plan is narrower and real: `noSlot` is a TAG
    now, beside `declSlot`, and no arithmetic, ordering or window survives
    anywhere in the kernel. The test stayed; E2's machinery around it went. -/
example : keyDisagree Dllbc.Tests.S23Direct.flagship = 0 := by native_decide
example : keyDisagree Std.lenFnT = 0 := by native_decide
example : keyDisagree Pure.kLeFn = 0 := by native_decide

-- The telescope rule's population, named rather than deprecated.
--
-- **M33a: 4 → 6, and the two arrivals are named.** The list is
-- `[Hf, Hf, Hf, Hf, Hfuel, Hfuel]` — R4's four (`Partition`'s and
-- `AppendBack`'s proof parameter, two λ nodes each) plus `Quicksort`'s
-- `hfuel → Hfuel`, at the same two-per-`fn` multiplicity. It flipped because the
-- Class-3 fixpoint reached it: with `partition`'s length conjuncts capital,
-- `let Hf1 = LeTrans … Hl1 Hfuel` must be a capital binding, and a capital
-- argument at a lowercase parameter is a ⇒-move of a capital binding. The
-- telescope rule is unchanged; its population grew.
example : comptimeSlotParams Dllbc.Tests.S23Direct.flagship = 6 := by native_decide

/-! …and **the count the rule protects**. A case test at `Term.lamImperative`
    would take every all-capital-parameter `fn` out of this number and with it
    its §5.4 audit, replacing it with `hasType`. Asserted so that a swap made
    later — by someone reading `bindsSlot`'s name and not its docstring — is loud
    rather than silent.

    It lands on `slotBinders`' own 22, and that is arithmetic rather than
    coincidence: a telescope is nested λs, so a λ node is imperative exactly when
    a slot binder sits at or below it in its own chain, and each slot binder is
    the innermost such node for exactly one prefix. -/
example : impLams Dllbc.Tests.S23Direct.flagship = 22 := by native_decide


/-! ## M33a: the Σ HALF of the migration, and the arm binders that answer it

    `lowerComptime` above counts λ binders and is blind to Σ's — `.sigmaT` is on
    the line that recurses without inspecting the binder — so R3b's 10,777 → 0
    never spoke about the position §2.1's Σ half lives in. These are that
    position, on both sides of it, so the producer/consumer pair is one
    measurement rather than two claims. -/

/-- Σ binders that declare their component COMPTIME (`⇝` on the domain) — the
    producer side. -/
partial def cmpSigmas : Term → Nat
  | .sigmaT _ d b => (if Term.domComptime d then 1 else 0) + cmpSigmas d + cmpSigmas b
  | .lam _ d b | .pi _ d b | .borrowT _ d b => cmpSigmas d + cmpSigmas b
  | .app f a | .seq f a | .seal _ f a => cmpSigmas f + cmpSigmas a
  | .letIn _ r t => cmpSigmas r + cmpSigmas t
  | .assign p e r => cmpSigmas p + cmpSigmas e + cmpSigmas r
  | .idT a b c => cmpSigmas a + cmpSigmas b + cmpSigmas c
  | .ctorApp _ as | .call _ as => (as.map cmpSigmas).foldl (· + ·) 0
  | .matchE _ _ bs => (bs.map (fun br => cmpSigmas br.body)).foldl (· + ·) 0
  | .borrow t | .deref t | .cmpT t => cmpSigmas t
  | _ => 0

/-- Match-arm binders spelled CAPITAL — the consumer side, and the population
    `checkArmModes` refuses to leave lowercase. -/
partial def capArms : Term → Nat
  | .matchE _ _ bs =>
    (bs.map (fun br =>
      (br.binders.filter (fun x => isUpperInit x.name)).length + capArms br.body)).foldl (· + ·) 0
  | .lam _ d b | .pi _ d b | .sigmaT _ d b | .borrowT _ d b => capArms d + capArms b
  | .app f a | .seq f a | .seal _ f a => capArms f + capArms a
  | .letIn _ r t => capArms r + capArms t
  | .assign p e r => capArms p + capArms e + capArms r
  | .idT a b c => capArms a + capArms b + capArms c
  | .ctorApp _ as | .call _ as => (as.map capArms).foldl (· + ·) 0
  | .borrow t | .deref t | .cmpT t => capArms t
  | _ => 0

/-- …and the ones that stay LOWERCASE, which is the other half of the claim: the
    check is bidirectional, so this number is asserted by the same run. -/
partial def lowerArms : Term → Nat
  | .matchE _ _ bs =>
    (bs.map (fun br =>
      (br.binders.filter (fun x => !isUpperInit x.name)).length + lowerArms br.body)).foldl (· + ·) 0
  | .lam _ d b | .pi _ d b | .sigmaT _ d b | .borrowT _ d b => lowerArms d + lowerArms b
  | .app f a | .seq f a | .seal _ f a => lowerArms f + lowerArms a
  | .letIn _ r t => lowerArms r + lowerArms t
  | .assign p e r => lowerArms p + lowerArms e + lowerArms r
  | .idT a b c => lowerArms a + lowerArms b + lowerArms c
  | .ctorApp _ as | .call _ as => (as.map lowerArms).foldl (· + ·) 0
  | .borrow t | .deref t | .cmpT t => lowerArms t
  | _ => 0

example : cmpSigmas Dllbc.Tests.S23Direct.flagship = 91 := by native_decide
example : capArms Dllbc.Tests.S23Direct.flagship = 14 := by native_decide
example : lowerArms Dllbc.Tests.S23Direct.flagship = 22 := by native_decide

/-! **The three numbers, read together.**

      * **91 comptime Σ components.** Most are the library's: `Ub`, `Lb` and
        `Sorted` unfold to Σ chains and R3b's `Term.cpi`/`clam` migration made
        their binders capital, so the flagship's ensures is built out of them.
        Five are the spec's own, written by hand at M33a (`Hub`, `Hlb`, `Hl1`,
        `Hl2`, `Hs`).
      * **14 capital arm binders**, from M33a's 10 and originally 0. Ten are the
        five spec components' consumers: `Partition`'s four in each of its two
        consumer chains, plus `Quicksort`'s `Hs1`/`Hs2`. **The four that arrived
        at M33 are the TAILS** — `Hcnt` (twice), `Hpc`, `Hc1`/`Hc2` across the
        chains — and they are the flip §2.7 predicted this counter would
        register: with the ensures spelled `Σ0`, the tail's `sctx` entry carries
        `⇝` and `checkArmModes` refuses to leave its receiver lowercase.
      * **22 lowercase arm binders**, from 26, and the pair of numbers is the
        whole content: four moved and the other twenty-two did not. They matter
        because the check runs in BOTH directions — each is a component the rule
        positively requires to stay lowercase (the data components: `hi`, `x`,
        `rest`, `lo`). A rule that only pushed one way would let all 36 be
        capital. What is NO LONGER in this number is "every Σ chain's TAIL, which
        has no binder and so has no mode": that was suspensions.md §2.5's
        surviving spelling, visible here as a number, and Σ0 is what took it
        out. -/

end Dllbc.Tests.S32Binders
end
-- └── end of the M32 R2 binder-convention debt ────────────────────────────────

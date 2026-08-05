import Dllbc.Tests.S26Migrate
import Dllbc.Tests.S26Fuel
import Dllbc.Tests.S26Fn
import Dllbc.Tests.S26Prog

/-!
# §27 (M27-P1) — a disposition for every declaration the program path declines

The endgame deletes `Decl`, the `back` machinery and the `[k]` guard. Before any
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

open Dllbc.Migrate Dllbc.Tests
open Dllbc.StdLemmas (Ub Lb len)

/-! ## §A. The instrument, asserted before any conclusion

    Every number below is computed over `S26Migrate.pools` with the harness's own
    `report`/`refusal`, so the ledger and the comparison cannot drift apart. The
    strip is asserted to have HAPPENED first — the `{ d with back := none }` gotcha
    (e4222291) produced a "stripped" pool identical to the original, and read at
    face value it said the exact opposite of the truth. -/

/-! **EXECUTED (M27-P2), and the assertion cannot be written any more.**

    This section used to count `back`-declaring declarations and assert the count.
    `Decl.back` no longer exists, so `(·.back.isSome)` does not typecheck — the
    claim "no declaration declares a backward spec" is now a fact about the TYPE
    rather than a property of the corpus, which is the strongest form it can take
    and the form that needs no test. A reappearance would not turn this file red;
    it would fail to compile, everywhere at once.

    What remains assertable is the shape of the corpus after the retirement. -/

/-- The corpus after the retirement: 110 accept, 58 reject, 19 decline — and the
    19 are exactly §B's residue, the true `[v]` payload-decrease class. Before
    M27-P2 it was 61 declines against 28 back-declaring entries. -/
example : (S26Migrate.pools.foldl (fun (a, r, d) p =>
    let q := report p; (a + q.accepts, r + q.rejects, d + q.declined)) (0, 0, 0)
  == (110, 58, 19)) = true := by native_decide

/-- …and the two paths still agree everywhere, which is the property the whole
    comparison exists for. **Read it narrowly**: agreement is not coverage. This
    says the declaration path and the program path reach the same verdict, and it
    says nothing about a DECLINING declaration, whose declaration-path verdict
    `report` never compares to anything. That gap is what hid the fourteen S19
    regressions until a deletion exposed them (§C). -/
example : (S26Migrate.pools.all (fun p => (report p).disagree.isEmpty))
  = true := by native_decide

/-! ## §B. The residue: 19 declarations, and a disposition for each

    These survive the `back` deletion, so each is a decision about `[k]`, not about
    §6.2. `residue` is derived from the harness rather than written out, and the
    assertion below pins it name-for-name — a decliner appearing or vanishing goes
    red here before it can go unnoticed anywhere else. -/

def residue (p : List Decl) : List String :=
  (declinedWith (S26Fuel.fixAll p)).map (·.1)

/-- The residue, name for name. Several share a `Decl.name` (a lie twin is the
    same function under the same name with a different body), so the multiset —
    not a set — is the claim. -/
example : (S26Migrate.pools.flatMap residue ==
  ["zero_all",
   "recSame", "recWrongIdx", "recGrow", "recDeep", "recCursor", "append_back",
   "partition", "partition", "partition", "partition", "partition",
   "partitionLoses",
   "quicksort", "quicksort", "quicksort", "qsStaleBound", "quicksort",
   "walkArr"]) = true := by native_decide

/-! ### B1. PAID — the fuel twins that already existed

    Five of the nineteen were paid before this phase, one per milestone that met
    them. Asserted here rather than cited, so that "the disposition exists" is a
    build fact and not a cross-reference a later deletion could falsify. -/

-- Both paths accept: the declaration checks AND its elaboration checks as a
-- program. `S26Fuel.bothWays` is where the claim was first made; reused verbatim
-- so the two files cannot drift on what "paid" means.

-- `zero_all` (S6) and `recCursor` (S23) are the same function twice — §7 cost 4's
-- own example, a cursor with no decreasing argument but the payload.
example : S26Fuel.bothWays S26Fuel.zeroAllF = true := by native_decide
-- `append_back` (S23), paid in M26-E, whose CALLER half was decision 8's first
-- real price rise.
example : S26Fuel.bothWays S26Prog.appendBackF = true := by native_decide
-- `partition` (S23), paid in M26-D.
example : S26Fuel.bothWays S26Fn.partitionF = true := by native_decide
-- `quicksort` (S23), the flagship, on the fuel-threaded cohort.
example : S26Fuel.bothWays S26Prog.quicksortP [S26Fn.partitionF, S26Prog.appendBackF]
  = true := by native_decide
-- `walkArr` (S24) is a NEGATIVE control, and its honest twin `walk` was paid in
-- M24 — before decision 8 existed. Nothing to port: the declaration path rejects
-- `walkArr` at the guard and the macro declines it at `[a]`-on-a-borrow, which is
-- one fact from two sides.
example : S26Fuel.bothWays S24Arrays.walk = true := by native_decide

/-! ### B2. THE GAP THIS LEDGER FOUND — six twins with no paid counterpart

    B1's five are the HONEST functions. Every one of them is guarded in the corpus
    by lie twins, and **the twins were not migrated with them**: `partitionF` was
    written with no lies at all, and `S26Prog`'s twin battery covers three of
    `quicksort`'s four. So the paid path was, until this file, checking that the
    honest program is accepted without checking that it still refuses anything —
    which is the half of a differential that can pass vacuously.

    That is a coverage gap rather than a decliner, which is why counting declines
    never surfaced it. Closed below, twin for twin.

    **The bar is sharper than "rejected".** A lie twin that DECLINES teaches
    nothing — the migration simply failed to produce a program. Each twin below
    must MIGRATE and then be refused, on both paths, which is what `neitherWay`
    asserts and what a decline-tolerant helper would have quietly let through. -/

def neitherWay (d : Decl) (deps : List Decl := []) : Bool :=
  (match checkFn (deps ++ [d]) d with | .ok _ => false | .error _ => true)
  && (match FnMacro.progOf (deps ++ [d]) .unit with
      -- A DECLINE is not a rejection: the elaboration has to exist for the
      -- program path's refusal to be about the lie.
      | .error _ => false
      | .ok t => !progOk t)

/-! #### B2a. `partition`'s four SPEC lies, on the fuel-threaded telescope

    Each is one conjunct of the honest ensures made false, and each is written
    exactly as `S23Direct` writes it — a `retType` swap on the honest body, so the
    twin cannot drift from the function it guards. The telescope is `partitionF`'s,
    which is the whole of the migration: a spec lie says nothing about fuel. -/

def partFLie (r : Term) : Decl := { S26Fn.partitionF with retType := r }

-- (1) UPPER BOUND on the wrong snapshot: `Ub p (old *v)` — true of the entry, and
-- the entry is not what the caller gets back.
def partFLieUb : Decl := partFLie (decl{
  fn partFLieUb [fuel] (fuel : Nat, v : &mut List Nat, p : Nat, Hf : Le (len *v) fuel)
    -> Σ (hi : List Nat) → Σ (hub : Ub p (old *v)) → Σ (hlb : Lb p hi)
         → Σ (hl1 : Le (len *v) (len (old *v))) → Σ (hl2 : Le (len hi) (len (old *v)))
         → Π (n : Nat) → Id Nat (add (count n (*v)) (count n hi)) (count n (old *v))
    { () } }).retType

-- (2) LOWER BOUND on the kept part instead of the returned one.
def partFLieLb : Decl := partFLie (decl{
  fn partFLieLb [fuel] (fuel : Nat, v : &mut List Nat, p : Nat, Hf : Le (len *v) fuel)
    -> Σ (hi : List Nat) → Σ (hub : Ub p (*v)) → Σ (hlb : Lb p (*v))
         → Σ (hl1 : Le (len *v) (len (old *v))) → Σ (hl2 : Le (len hi) (len (old *v)))
         → Π (n : Nat) → Id Nat (add (count n (*v)) (count n hi)) (count n (old *v))
    { () } }).retType

-- (3) The returned part DROPPED from the count: "everything stayed in `*v`".
def partFLieCountDrop : Decl := partFLie (decl{
  fn partFLieCountDrop [fuel] (fuel : Nat, v : &mut List Nat, p : Nat, Hf : Le (len *v) fuel)
    -> Σ (hi : List Nat) → Σ (hub : Ub p (*v)) → Σ (hlb : Lb p hi)
         → Σ (hl1 : Le (len *v) (len (old *v))) → Σ (hl2 : Le (len hi) (len (old *v)))
         → Π (n : Nat) → Id Nat (count n (*v)) (count n (old *v))
    { () } }).retType

-- (4) …and the count off by one, which no `Nil`-path argument can reach.
def partFLieCountShift : Decl := partFLie (decl{
  fn partFLieCountShift [fuel] (fuel : Nat, v : &mut List Nat, p : Nat, Hf : Le (len *v) fuel)
    -> Σ (hi : List Nat) → Σ (hub : Ub p (*v)) → Σ (hlb : Lb p hi)
         → Σ (hl1 : Le (len *v) (len (old *v))) → Σ (hl2 : Le (len hi) (len (old *v)))
         → Π (n : Nat) → Id Nat (add (count n (*v)) (count n hi)) (S (count n (old *v)))
    { () } }).retType

def partFLies : List Decl := [partFLieUb, partFLieLb, partFLieCountDrop, partFLieCountShift]

/-- Each lie really is a lie ABOUT THIS FUNCTION: same name, same telescope, same
    body, one different return type. Without this the four could have been four
    unrelated declarations that happen to be rejected. -/
example : partFLies.all (fun d =>
    d.body == S26Fn.partitionF.body
    && d.telescope == S26Fn.partitionF.telescope
    && d.retType != S26Fn.partitionF.retType) = true := by native_decide

example : partFLies.all (fun d => neitherWay d) = true := by native_decide

/-! #### B2b. `partitionLoses` — the BODY twin, derived rather than transcribed

    The four above are spec lies, refutable somewhere the `Nil` path can be blamed
    for. `partitionLoses` is the body twin: the `≤ p` head is DROPPED instead of
    being pushed back onto the kept part, so it is wrong only on the recursive
    `True` path and only in the count conjunct — the bounds still hold of a list
    with one element missing. It is the twin that tests the recursion.

    Transcribing `partitionF` again to change one line would put a 40-line proof
    body in the corpus twice, where the second copy can rot. So the lie is a
    **transform**, and the transform is held to the corpus's own hand-written twin:
    applying it to `partition` must reproduce `partitionLoses` exactly. That makes
    "this is the same lie" a computation instead of a claim about my care — the
    α-oracle pattern M26-D used for the macro, at one function's scale. -/

/-- Drop the head from the one `Cons`-valued write-back. `*v := Nil` and
    `*v := rest` are not `Cons` applications, so the rewrite has exactly one site;
    the oracle below is what proves that rather than the reasoning. -/
partial def dropHead : Term → Term
  | .assign pl (.ctorApp "Cons" [_, tl]) k => .assign pl tl (dropHead k)
  | .letIn x r b => .letIn x (dropHead r) (dropHead b)
  | .assign a b c => .assign (dropHead a) (dropHead b) (dropHead c)
  | .seq a b => .seq (dropHead a) (dropHead b)
  | .ctorApp n as => .ctorApp n (as.map dropHead)
  | .call f as => .call f (as.map dropHead)
  | .callV x as => .callV x (as.map dropHead)
  | .borrow t => .borrow (dropHead t)
  | .deref t => .deref (dropHead t)
  | .matchE sc e bs => .matchE sc e (bs.map (fun b => Branch.mk b.ctor b.binders (dropHead b.body)))
  | t => t

/-- **THE ORACLE.** The corpus wrote `partitionLoses` by hand, before this file
    existed and so not tunable against it. The transform applied to the honest
    `partition` reproduces it — same body, modulo the self-call name each
    declaration owes itself. -/
example : (FnMacro.renameSelf "partition" "partitionLoses"
    (dropHead S23Direct.partition.body) == S23Direct.partitionLoses.body)
  = true := by native_decide
/-- …and the oracle can say NO: without the drop, the two bodies differ. -/
example : (FnMacro.renameSelf "partition" "partitionLoses"
    S23Direct.partition.body == S23Direct.partitionLoses.body) = false := by native_decide

def partitionLosesF : Decl :=
  { S26Fn.partitionF with body := dropHead S26Fn.partitionF.body }

-- The transform really fired on the fuel-threaded body too (it is the same body
-- plus a `match fuel`, but that is a claim worth checking rather than assuming).
example : (partitionLosesF.body != S26Fn.partitionF.body) = true := by native_decide
example : neitherWay partitionLosesF = true := by native_decide

/-! #### B2c. `qsNoSuff` — the sufficiency hypothesis, on the migrated flagship

    The fourth quicksort twin, and the only one `S26Prog`'s battery does not carry.
    It keeps the parameter and weakens it to `Unit`, so the body still elaborates
    and the rejection is about TYPING rather than an unbound name: the `Z` branch's
    `botElim` then has no ⊥ to eliminate and the out-of-fuel path stops being dead.
    This is what makes guard-plus-hypothesis TOTAL correctness rather than partial.

    It needs no new transform: `S26Prog.migrate` retargets callees and leaves the
    telescope alone, which is exactly what its own docstring promised would let it
    carry the lie twins. -/

def qsNoSuffP : Decl := S26Prog.migrate S23Direct.qsNoSuff

-- The weakened hypothesis survived the migration, and it is the only difference
-- from the honest flagship's telescope.
example : (qsNoSuffP.telescope != S26Prog.quicksortP.telescope
        && qsNoSuffP.body == S26Prog.quicksortP.body) = true := by native_decide
example : neitherWay qsNoSuffP [S26Fn.partitionF, S26Prog.appendBackF] = true := by native_decide

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

def guardTwins : List Decl := [S23Direct.recSame, S23Direct.recWrongIdx, S23Direct.recGrow]

-- Today: the declaration path rejects each at the guard…
example : guardTwins.all (fun d => !checkFnOk d [d]) = true := by native_decide
-- …and the macro refuses each for the reason that OUTLIVES the guard.
example : guardTwins.all (fun d =>
    match FnMacro.fnElab d with
    | .error e => strContains e "not the predecessor"
    | .ok _ => false) = true := by native_decide
-- Not vacuous: the honest sibling elaborates, so the three refusals are about the
-- argument and not about the shape.
example : (match FnMacro.fnElab S23Direct.recGood with
           | .error _ => false | .ok _ => true) = true := by native_decide

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

def deepSealT : Term := pure{ Π (n : Nat) → Id Nat Z Z }
def deepMotT : Term := pure{ λ (n : Nat). Id Nat Z Z }

/-- `recDeep`, hand-written as a sealed recursor. The step arm keeps the corpus's
    own inner `match a` — so the two-constructors-down SHAPE is still there — and
    reaches `ih` from inside it, which is exactly the move the macro refuses to
    make on the author's behalf. -/
def deepBaseArm : Term := .lamR [] (.ctorApp "Refl" [])
def deepStepArm : Term :=
  -- `ih`'s domain is the motive at the predecessor, and `deepMotT` is CONSTANT —
  -- which is the whole content of the correction this section records: `ih : P a`
  -- already IS `P b` for every `b` when `P` ignores its index.
  .lamR [(⟨0, "a"⟩, .const "Nat"), (⟨1, "ih"⟩, pure{ Id Nat Z Z })]
    (.matchE ⟨0, "a"⟩ none
      [ .mk "Z" [] (.ctorApp "Refl" [])
      , .mk "S" [⟨2, "b"⟩] (.var ⟨1, "ih"⟩) ])
def deepRec : Term :=
  .app (.app (.app (.const "natRec") deepMotT) deepBaseArm) deepStepArm
def recDeepProg : Term := .letIn ⟨900, "f"⟩ (.seal deepRec deepSealT) .unit

example : progOk recDeepProg = true := by native_decide

/-- **The seal really audits it**, so the acceptance above is not the node waving
    a term through: ascribe the same recursor at a Π that claims `Id Nat Z (S Z)`
    and the arms cannot inhabit it. -/
def deepSealLie : Term := pure{ Π (n : Nat) → Id Nat Z (S Z) }
def recDeepLie : Term :=
  .letIn ⟨900, "f"⟩ (.seal (.app (.app (.app (.const "natRec")
    (pure{ λ (n : Nat). Id Nat Z (S Z) })) deepBaseArm) deepStepArm) deepSealLie) .unit
example : progOk recDeepLie = false := by native_decide

/-- …and the MACRO still declines the declaration, which is the whole content of
    the correction: the form exists, `fnElab` does not reach it. -/
example : (match FnMacro.fnElab S23Direct.recDeep with
           | .error e => strContains e "not the predecessor"
           | .ok _ => false) = true := by native_decide

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
    expected `Decl` field. When the field goes, the subject goes with it — there is
    no claim underneath to re-express, because the claim WAS the parse. These
    retire, and the rationale is that a test of a deleted syntax is not coverage.

    `quicksortSig` is the one worth naming individually, because it is labelled
    THE CROWN: it is the M22-era quicksort signature — the `hbnd` telescope and
    `back = sortRangeL fuel lo cnt (*v)` — verified against `SInternals`'
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
    `S23Direct.setAt` is `nth`-plus-write with the relationship as an ENSURES
    (`Id (List Nat) (*v) (set i x (old *v))`) rather than as a backward spec, and
    `swapAt` is `swapS` the same way (`Id (List Nat) (*v) (swapL i j (old *v))`) —
    the same two model functions, `set` and `swapL`, moved from the `back` field
    into the return type. What the caller learns is strictly more, not less: a
    propositional equation it can rewrite along, rather than a value the group-end
    happened to compute. Asserted below on both paths, with the lie twins that make
    the acceptance non-vacuous. -/

def ensuresReplacements : List Decl := [S23Direct.setAt, S23Direct.swapAt]

-- The ensures-style pair checks as declarations AND as programs.
example : S26Fuel.bothWays S23Direct.setAt = true := by native_decide
example : S26Fuel.bothWays S23Direct.swapAt [S23Direct.setAt] = true := by native_decide

-- …and refuses the four lies about exactly the facts the backs used to carry:
-- the index moved, and the update claimed to be a no-op.
def ensuresLies : List Decl :=
  [S23Direct.setAtLieIdx, S23Direct.setAtLieNoop, S23Direct.swapAtLieIdx, S23Direct.swapAtLieNoop]
example : ensuresLies.all (fun d => neitherWay d [S23Direct.setAt]) = true := by native_decide

-- That the two name the SAME model function (`swapL` in `swapSN`'s declared back,
-- `swapL` in `swapAt`'s return type) is a reading of two source lines and is left
-- as one — an equality assertion between a `back` and a `retType` would compare
-- two differently-shaped terms and pass for the wrong reason. What IS asserted is
-- the instrument: the corpus still carries the back this section proposes to
-- delete, so C2 is not describing something already gone.

/-! ### C3. S19's Architecture A stratum — twelve entries that keep their bodies

    `pivotPlace`, `pivotPlaceH`, `partScan`, `partScanRange`, `partition`,
    `partitionQ`, `partitionRange`, `quicksort` and their lie twins are the M22-era
    model-conformance corpus: `back = partitionL …`, `back = sortRangeL …`, an
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


-- …and the function still checks, and now MIGRATES — which the `[f]`-hinted,
-- back-carrying original could not.
example : S26Fuel.bothWays S19Partition.twoRec = true := by native_decide

/-! ## §D. INSTRUMENT RETIREMENT — a third disposition class, and the one no
    measurement in this campaign could see

    §B disposed of declarations that survive the deletion and §C of the ones that
    cause it. Both were derived from `S26Migrate.pools`, and **the pools are the
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
    | `partScan`, `partScanRange` | an in-place swap scan CONFORMS to `partScanL` | the conformance claim IS the retired architecture; the PROGRAM is carried by `S23Direct.partition` (relational `Ub`/`Lb`/count) and `S25ArrSort.partitionA` |
    | `partition`, `partitionQ`, `partitionRange` | conforms to `partitionL`; returned index = `partIdxL` | `S23Direct.partition`; `S25ArrSort.partitionA`, which returns an index under its own ensures |
    | `quicksort`, `quicksortLie` | conforms to `sortRangeL` | `S23Direct.quicksort` — `Σ (Sorted (*v)) → Π n. count`-preservation, zero declared backs. Strictly stronger, and 21 ms against 21.8 s |
    | `exitAccept` | `Id (*v) (swapL i j (old *v))` | `S23Direct.swapAt` — literally the same statement, asserted in §C2 |
    | `lenPreserve` | `Id (len *v) (len (old *v))` across a swap | derivable from `swapAt`'s equation by `len_swapL` + `id_congr`; the equation implies the length fact |
    | `shareCaller` | caller-side σ-sharing: a callee's fact about its own exit forwarded as the caller's | the same mechanism at scale in `S23Direct.quicksort`, which forwards `partition`'s count equation into its own postcondition |
    | `swapSE`, `partitionRangeE`, `quicksortE` | count preservation for swap / partition / sort | the count conjunct of `S23Direct.partition` and `S23Direct.quicksort` |
    | `quicksortSorted` | `Σ (SortedR cnt lo (*v)) → Π n. count`-preservation | `S23Direct.quicksort` — whole-list structural `Sorted` in place of positional `SortedR cnt lo`, same count conjunct |
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

import Dllbc.Program
import Dllbc.Migrate
import Dllbc.Std
import Dllbc.StdLemmas
import Dllbc.PureMacro
import Dllbc.DeclMacro
import Dllbc.ProgMacro
import Dllbc.FnMacro
import Dllbc.AlphaEq
import Dllbc.Tests.S6Call
import Dllbc.Tests.S24Arrays
import Dllbc.Tests.S14Bounds
import Dllbc.Tests.S23Direct
import Dllbc.Tests.S26Migrate

/-!
# §26 (M26-E) — paying §12 decision 8, shape by shape

The migration report's largest decline class was `[v]` payload decrease: a
recursion that shrinks a borrow's payload has no recursor form until §9's
borrow-mode eliminator exists, and §12 decision 8 blesses fuel-threading as the
interim. M26-D paid it for `partition` and M26-E for `append_back` — both the
LIST-cursor shape.

(§C found that most of that class was never in it, and M26-F adopted the
correction, which leaves the `[v]` class at 19 and a declared `back` as the
largest one. The sections below are as they were measured, each annotated where
the adoption changed what it says.)

This file pays it for the shapes that had not been paid, one per section, so that
"the interim is available" is a measured claim per shape rather than an
extrapolation from one. Each is a TWIN: the `[v]` original stays exactly as it is
(J1 — both worlds alive), and the migration is legible as a diff against it.

**What each section reports is the PRICE**, since that is the only thing still in
doubt. Decision 8 was taken knowing the surface cost; what nobody had measured was
whether the cost is uniform, and the answer so far is that it is not — the list
cursor costs a parameter and a dead branch, and the array cursor costs something
else (§B).
-/

open Dllbc
open Dllbc.StdLemmas (le_refl len Le)

namespace Dllbc.Tests.S26Fuel

/-- The declaration checks, and its elaboration checks as a program. The pair is
    the claim: fuel-threading buys a form the macro accepts, and the two forms
    agree. -/
-- ~~The declaration checks, AND its elaboration checks as a program. The pair is
-- the claim.~~ **Half of it retired with `checkFn`** (M27-δ): there is one path,
-- so what is left is that the fuel-threaded form checks — which was always the
-- half in doubt, since decision 8's question was whether the interim is
-- available at all, not whether two checkers agree about it.
def bothWays (d : FnDef) (deps : List FnDef := []) : Bool :=
  match FnMacro.progOf (deps ++ [d]) .unit with
  | .error _ => false
  | .ok t => progOk t

/-! ## §A. The LIST cursor: `zero_all`

    `zero_all` walks a list through a mutable borrow, zeroing each element, and
    passes the tail's field reborrow to itself. It is the shape §7 cost 4 names as
    having "no easy recursor form" — no counter at all — and the one S6Call and
    S23Direct both carry. -/

def zeroAllF : FnDef :=
  decl{ fn zero_allF [fuel] (fuel : Nat, v : &mut List Nat, Hf : Le (len *v) fuel) -> Unit {
    match v {
      Nil => (),
      -- The dead branch, the same ex-falso the other two migrations carry:
      -- `Hf : Le (S (len *tl)) Z` IS `Bot`.
      Cons(hd, tl) => match fuel {
        Z => botElim Unit Hf,
        S(f2) => { *hd := 0; zero_allF(f2, tl, Hf); () }
      }
    } } }

example : bothWays zeroAllF = true := by native_decide
-- The `[v]` original is untouched and still DECLINES (J1), and the decline is
-- asserted where it is a PROGRAM fact rather than a `fnElab` return value: the
-- same function written as a `fn` statement is `FnStmt.refusedStmt`, rejected on
-- `fnRefusedNeedle` and on "§12 decision 8" by name. `S6Call.zeroAll`'s decline
-- is also what puts "zero_all" in `S27Dispose` §B's residue list, so a decline
-- that stopped happening still reddens the build, with the name attached.
-- (The `fnElab`-return-value assertion that used to sit here went in M28 cluster
-- C, as one of the granular meta-assertions the e2e rule retires.)

/-! ## §B. The ARRAY cursor was already paid, and the corpus says so

    `walkArr [a]` recurses on a carved sub-slice and S24 pins its REJECTION, with
    the finding beside it: "§8's guard compares the actual against the parameter's
    current snapshot by `strictSubterm`… a carve's body split refines the payload
    σ to an `arrCat` SPINE, so from that moment no sub-slice is a structural
    predecessor of its parent… array recursion stays fuel-carried."

    So there is nothing to migrate here, and I nearly wrote the twin before
    checking: `walk` IS `walkArr` with `[fuel]` in place of `[a]` and the same body
    character-for-character. It was written at the time, it checks, and it
    MIGRATES. The array shape's decision-8 price was paid in M24, before decision 8
    existed.

    What the migration report shows for `walkArr` is therefore the two paths
    agreeing about a program neither accepts: the declaration path REJECTS it at
    the guard, the macro DECLINES it at `[a]`-on-a-borrow, and the reasons are the
    same fact seen from two sides. -/

-- **The field-by-field comparison went in M28 cluster C**, with the `.dec`
-- comparison beside it. Two `FnDef` records agreeing on `telescope`/`retType`/
-- `body` (up to `renameSelf`) and differing on `dec` is a structural
-- meta-assertion, and the e2e rule retires those; what it was EVIDENCE for is the
-- sentence above, which the two verdicts below carry between them — one form
-- checks, the other declines, and the source shows they are the same function.
example : bothWays Tests.S24Arrays.walk = true := by native_decide
-- The `[a]` twin: ~~rejected by one path, declined by the other, for the same
-- fact~~ — the rejecting path is gone (M27-δ), and the decline is now asserted
-- where it is a name rather than an `Except` case: "walkArr" is in `S27Dispose`
-- §B's residue list, which is computed by `declinedWith` over the pools, so it
-- says exactly "the macro declines this one" with the identity attached and goes
-- red if it ever stops.

/-! ## §C. THE FINDING: most of the `[v]` class needs no fuel at all

    §7 demotes `[k]` to a **scrutinee-selection hint**, and that changes what a
    mis-chosen one costs. The declaration-era guard was happy with `[v]` whenever
    the payload decreases — which it does — so there was never a reason to name
    anything else, and `nth`/`nth2` name the borrow. But they ALSO decrease on
    their INDEX, which is a `Nat`, and the macro serves that directly.

    **Correcting the hint is free.** No fuel, no signature change, no caller
    change, no dead branch — the same body, the same telescope, the same return
    type, one field of the `FnDef` different. The bound descends definitionally
    exactly as it did (`p : Le (S (S k)) (S (len *tl))` IS `Le (S k) (len *tl)` —
    M14's own bounds-cursor property), which is why nothing else moves.

    With two hints corrected the WHOLE S14 family migrates: four accepted on both
    paths, one rejected on both (its negative control), nothing declined. That was
    five declines a moment ago, and it was the third-largest block in the map.

    This is the same shape as M26-C's `split_off` observation — "it needs NO fuel,
    because it recurses on its index, which is already a `Nat`" — arriving as a
    general fact about the class rather than as a property of one function. What
    genuinely needs fuel is narrower than the report suggested: a cursor with NO
    decreasing argument of its own (§A's `zero_all`, and `recCursor`, which is the
    same function under another name).

    **M26-F ADOPTED this**, so the section reads differently than it did when it was
    written. `nth`/`nth2` in S14Bounds and S17Spec now declare `[i]` at the source,
    and the twins below are no longer twins — each is equal to the corpus
    declaration it was a correction of. The measurements stay because what they
    pin is still a claim: that the hint is the ONLY thing that moved, and that the
    declaration path is as happy with `[i]` as it was with `[v]` (M14's descent
    accepts index decrease either way, so nothing in S14 or S17 needed re-proving).

    The two round-trip mirrors of `nthS` moved with it (`SDeclMacro.nth'`,
    `SDeclUnified.nthU`), and only one of them noticed: `FnDef.alphaEq` compares
    name/telescope/retType/body/back and NOT `dec`, so the `alphaEq` mirror stayed
    green against a stale hint while the exact-`BEq` mirror went red. -/

-- **`nthI`/`nth2I`/`p14fixed` and their equality assertion went in M28 cluster C.**
-- They were `{ S14Bounds.nth with dec := some 1 }` and a copy of `p14` built from
-- them — the corrected hint SIMULATED in the harness — and the assertion beside
-- them said "nothing changed but the hint". M26-F adopted the correction at the
-- source, at which point each alias was `==` to the declaration it aliased, the
-- pool copy was `==` to `S26Migrate.p14`, and both assertions had become
-- structural comparisons of a record with itself. The subjects below are the
-- corpus declarations directly, which is what the aliases had turned into.
example : bothWays Tests.S14Bounds.nth = true := by native_decide
example : bothWays Tests.S14Bounds.nth2 [Tests.S14Bounds.nth] = true := by native_decide

/-- The whole family, hints corrected: 4 accept on both paths, 1 rejects on both
    (`rejectProbe` is S14's own negative control), NOTHING declines. Read off the
    CORPUS pool, not a local copy of it.

    Stated per declaration rather than as three counts (M28 μ, when the corpus-wide
    census retired): a verdict VECTOR says which one rejects, where a tally only says
    that one does — and `none` would be a decline, so "nothing declines" is still
    carried, positionally. Before M26-F's adoption the same five functions declined
    five times (`report p14 == R 0 0 5`, S26Migrate §Y as it then read). -/
example : (Tests.S26Migrate.p14.map (Migrate.progVerdict Tests.S26Migrate.p14)
  == [some true, some true, some true, some true, some false]) = true := by native_decide

/-! ## §D. What is left needing fuel, and one macro gap this section found

    After §B and §C the `[v]` class is: `zero_all` and `recCursor` (the same
    function, twice in the corpus) — a cursor with no decreasing argument but the
    payload — plus S17/S19's `nth`/`nth2`/`swapS`, which since M26-F carry the
    corrected hint (or, for `swapS`, never had one) and are blocked by their
    declared `back` alone. §A pays the first; the second waits on the `back`
    question, which is now the only thing standing under 49 declarations.

    And one thing that LOOKS like a macro gap and is not, recorded because I added
    a refusal for it before thinking it through and then took it out again:
    `fnElab` with no `[k]` emits a plain sealed λ without checking that the body
    has no self-call, so `zero_all` with its hint simply REMOVED elaborates
    happily. The resulting program is still rejected — and by §8's OWN mechanism,
    which is the point: the `let` is not in scope in its own right-hand side, so
    the self-call resolves to nothing and falls through as the forward reference it
    is. M26-C pinned exactly that as why `bad()` is unwritable ("not by a recursion
    rule; the binding is not in scope in its own right-hand side"), and a macro
    refusal would paper over the demonstration. -/

-- `zero_all` with its hint simply REMOVED, written as a program (M28 cluster C —
-- it used to be `fnElab` on a record update, wrapped in a hand-built `letIn`).
-- `FnStmt` §E is the same function WITH the hint, refused at decision 8; the two
-- sit either side of the distinction this paragraph is about.
def noHintStmt : Term := prog{
  fn zero_all (v : &mut List Nat) -> Unit {
    match v { Nil => (), Cons(hd, tl) => { *hd := 0; zero_all(tl); () } } };
  () }
example : progRejects noHintStmt "unknown function" = true := by native_decide
-- Not vacuous: the same body WITH a hint (and the fuel §A threads) is a program
-- that CHECKS, so the rejection above is about the missing recursor and not about
-- the body.
example : bothWays zeroAllF = true := by native_decide

/-! ## §E. The map, re-measured — and the two blockers COMPOSE

    §C's finding is worth a number over the whole corpus rather than over one
    family, and the number is not what either fix predicts on its own. As measured
    before M26-F adopted the hints:

        73 declines as the corpus stood
        68 with the two hints corrected          (−5)
        65 with `back` stripped                  (−8)
        20 WITH BOTH                             (−53)

    The corpus now stands at the second line, so what the assertions below measure
    is 68 and 19 — one better than the 20 predicted, because `S19Partition.nth2Lie`
    is written `{ nth2S with … }` and inherited the corrected hint, which the
    name-matching `fixHints` never reached. That is the one place where adopting a
    fix at the source does more than simulating it in the harness.

    Neither fix alone does much and together they collapse the map, because a
    cohort is a CLOSURE: one un-migratable leaf declines everything above it. S17's
    `nth` has both a declared `back` and a `[v]` hint, so fixing either leaves it
    declining, and everything in S17 and S19 that reaches it declines with it.
    "Fix the biggest class first" is exactly the wrong strategy against a closure —
    the blockers have to come off together or the report barely moves, which is why
    two rounds of measurement made the map look stubborn and the third made it
    small.

    What survives both fixes is 19, and it is the honest residue: 17 in S23 (the
    true `[v]` cursors — `partition`, `append_back`, `recCursor`, `partitionLoses`
    — everything whose closure reaches one of them, the guard twins, and
    `recDeep`), `zero_all` in S6 (paid in §A), and `walkArr` in S24 (a negative
    control, §B). S19's `nth2Lie` was the twentieth and left with the adoption.

    **Stripping `back` is NOT free** — it removes a mechanism a caller relies on,
    which is the design question that goes to the user. Correcting a hint IS free.
    The measurement separates them so the question can be asked about eight
    declarations rather than about the corpus. -/

/-! ### The corpus-wide CENSUS retired here (M28 μ)

    Four assertions counted `S26Migrate.pools` — total declines, total
    accepts/rejects, the per-pool decline vector, and that `fixHints` was a no-op on
    every pool — together with the `fixHints`/`fixAll` harness they were computed
    through. They are gone, and the reason is not that they were failing.

    **A census of `FnDef` pools has no subject once the record form is gone.** `fn`
    is a statement of the program grammar now (M28 θ), the corpus is being rewritten
    onto it, and a declaration that becomes a program leaves the pools — so every
    migrated file moved these numbers for a reason that had nothing to do with any
    verdict changing. Kept through the sweep they would have been ~24 manual
    recomputes and a standing invitation to "fix" a red build by editing a constant.

    What they were FOR survives in two stronger forms, neither of which counts:

      * **The residue by NAME** (`S27Dispose` §B) — the same nineteen declarations
        the decline count summarised, pinned name for name, so one appearing or
        vanishing goes red with its identity attached.
      * **Per-declaration verdicts** — §C above, positional, which is what the
        p14 tally became.

    `fixHints` went with them: it corrected `nth`/`nth2`'s `[k]` hint, M26-F adopted
    the correction at the source, and the assertion that it had become a no-op was
    one of the four. That claim is now structural — there is no `fixHints` to be a
    no-op — and it is checked where it still bites, by `S27Dispose`'s residue list
    (computed without it) not moving. -/

end Dllbc.Tests.S26Fuel

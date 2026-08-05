import Dllbc.Program
import Dllbc.Migrate
import Dllbc.Macro
import Dllbc.Std
import Dllbc.StdLemmas
import Dllbc.PureMacro
import Dllbc.DeclMacro
import Dllbc.ProgMacro
import Dllbc.FnMacro
import Dllbc.Tests.S6Call
import Dllbc.Tests.S24Arrays
import Dllbc.Tests.S14Bounds
import Dllbc.Tests.S23Direct
import Dllbc.Tests.S26Migrate

/-!
# §26 (M26-E) — paying §12 decision 8, shape by shape

The migration report's largest decline class is `[v]` payload decrease: a
recursion that shrinks a borrow's payload has no recursor form until §9's
borrow-mode eliminator exists, and §12 decision 8 blesses fuel-threading as the
interim. M26-D paid it for `partition` and M26-E for `append_back` — both the
LIST-cursor shape.

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
def bothWays (d : Decl) (deps : List Decl := []) : Bool :=
  (match checkFn (deps ++ [d]) d with | .ok _ => true | .error _ => false)
  && (match FnMacro.progOf (deps ++ [d]) .unit with
      | .error _ => false
      | .ok t => progOk t)

/-! ## §A. The LIST cursor: `zero_all`

    `zero_all` walks a list through a mutable borrow, zeroing each element, and
    passes the tail's field reborrow to itself. It is the shape §7 cost 4 names as
    having "no easy recursor form" — no counter at all — and the one S6Call and
    S23Direct both carry. -/

def zeroAllF : Decl :=
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

example : checkFnOk zeroAllF = true := by native_decide
example : bothWays zeroAllF = true := by native_decide
-- The `[v]` original is untouched and still checks (J1), and still declines.
example : checkFnOk Tests.S6Call.zeroAll = true := by native_decide
example : (match FnMacro.fnElab Tests.S6Call.zeroAll with
           | .error e => strContains e "decision 8"
           | .ok _ => false) = true := by native_decide

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

example : (Tests.S24Arrays.walk.telescope == Tests.S24Arrays.walkArr.telescope
        && Tests.S24Arrays.walk.retType == Tests.S24Arrays.walkArr.retType
        -- The bodies differ in one thing, which each declaration owes: the name
        -- its own self-call uses.
        && Tests.S24Arrays.walk.body
             == FnMacro.renameSelf "walkArr" "walk" Tests.S24Arrays.walkArr.body) = true := by
  native_decide
-- …differing in the hint alone, which is the whole of the migration.
example : (Tests.S24Arrays.walk.dec == some 0 && Tests.S24Arrays.walkArr.dec == some 4)
  = true := by native_decide
example : bothWays Tests.S24Arrays.walk = true := by native_decide
-- The `[a]` twin: rejected by one path, declined by the other, for the same fact.
example : (checkFnOk Tests.S24Arrays.walkArr == false
        && (match FnMacro.fnElab Tests.S24Arrays.walkArr with
            | .error e => strContains e "decision 8"
            | .ok _ => false)) = true := by native_decide

/-! ## §C. THE FINDING: most of the `[v]` class needs no fuel at all

    §7 demotes `[k]` to a **scrutinee-selection hint**, and that changes what a
    mis-chosen one costs. The declaration-era guard was happy with `[v]` whenever
    the payload decreases — which it does — so there was never a reason to name
    anything else, and `nth`/`nth2` name the borrow. But they ALSO decrease on
    their INDEX, which is a `Nat`, and the macro serves that directly.

    **Correcting the hint is free.** No fuel, no signature change, no caller
    change, no dead branch — the same body, the same telescope, the same return
    type, one field of the `Decl` different. The bound descends definitionally
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
    same function under another name). -/

def nthI : Decl := { Tests.S14Bounds.nth with dec := some 1 }
def nth2I : Decl := { Tests.S14Bounds.nth2 with dec := some 1 }

/-- Nothing changed but the hint. -/
example : (nthI.body == Tests.S14Bounds.nth.body
        && nthI.telescope == Tests.S14Bounds.nth.telescope
        && nthI.retType == Tests.S14Bounds.nth.retType
        && Tests.S14Bounds.nth.dec == some 0) = true := by native_decide

example : bothWays nthI = true := by native_decide
example : bothWays nth2I [nthI] = true := by native_decide

/-- The whole family, hints corrected: 4 accept on both paths, 1 rejects on both
    (`rejectProbe` is S14's own negative control), NOTHING declines. -/
def p14fixed : List Decl :=
  [nthI, nth2I, Tests.S14Bounds.swap, Tests.S14Bounds.cascade, Tests.S14Bounds.rejectProbe]
example : (Migrate.report p14fixed
  == { accepts := 4, rejects := 1, declined := 0, disagree := [] }) = true := by native_decide
-- …against five declines for the same five functions as the corpus declares them.
example : (Migrate.report Tests.S26Migrate.p14
  == { accepts := 0, rejects := 0, declined := 5, disagree := [] }) = true := by native_decide

/-! ## §D. What is left needing fuel, and one macro gap this section found

    After §B and §C the `[v]` class is: `zero_all` and `recCursor` (the same
    function, twice in the corpus) — a cursor with no decreasing argument but the
    payload — plus S17/S19's `nth`/`nth2`/`swapS`, which have the SAME free fix
    available and are blocked by their declared `back` rather than by their hint.
    §A pays the first; the second waits on the `back` question.

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

example : (match FnMacro.fnElab { Tests.S6Call.zeroAll with dec := none } with
           | .error _ => false
           | .ok t => progRejects (.letIn ⟨900, "zero_all"⟩ t .unit) "unknown function")
  = true := by native_decide
-- Not vacuous: the same body WITH a hint (and the fuel §A threads) is a program
-- that CHECKS, so the rejection above is about the missing recursor and not about
-- the body.
example : bothWays zeroAllF = true := by native_decide

/-! ## §E. The map, re-measured — and the two blockers COMPOSE

    §C's finding is worth a number over the whole corpus rather than over one
    family, and the number is not what either fix predicts on its own.

        73 declines as the corpus stands
        68 with the two hints corrected          (−5)
        65 with `back` stripped                  (−8)
        20 WITH BOTH                             (−53)

    Neither fix alone does much and together they collapse the map, because a
    cohort is a CLOSURE: one un-migratable leaf declines everything above it. S17's
    `nth` has both a declared `back` and a `[v]` hint, so fixing either leaves it
    declining, and everything in S17 and S19 that reaches it declines with it.
    "Fix the biggest class first" is exactly the wrong strategy against a closure —
    the blockers have to come off together or the report barely moves, which is why
    two rounds of measurement made the map look stubborn and the third made it
    small.

    What survives both fixes is 20, and it is the honest residue: 17 in S23 (the
    true `[v]` cursors — `partition`, `append_back`, `recCursor`, `partitionLoses`
    — everything whose closure reaches one of them, the guard twins, and
    `recDeep`), `zero_all` in S6 (paid in §A), `nth2Lie` in S19 (its own `[v]`),
    and `walkArr` in S24 (a negative control, §B).

    **Stripping `back` is NOT free** — it removes a mechanism a caller relies on,
    which is the design question that goes to the user. Correcting a hint IS free.
    The measurement separates them so the question can be asked about eight
    declarations rather than about the corpus. -/

def fixHints (pool : List Decl) : List Decl :=
  pool.map (fun d => if d.name == "nth" || d.name == "nth2" then { d with dec := some 1 } else d)
def fixAll (pool : List Decl) : List Decl := fixHints (Tests.S26Migrate.stripBacks pool)

example : ((Tests.S26Migrate.pools.foldl (fun a p => a + (Migrate.report (fixHints p)).declined) 0 == 68)
        && (Tests.S26Migrate.pools.foldl (fun a p => a + (Migrate.report (fixAll p)).declined) 0 == 20))
  = true := by native_decide

example : (Tests.S26Migrate.pools.foldl (fun (a, r) p =>
    let q := Migrate.report (fixAll p); (a + q.accepts, r + q.rejects)) (0, 0)
  == (118, 86)) = true := by native_decide

-- Still agreeing everywhere under both fixes, so the 53 that move are migrations
-- and not accidents.
example : (Tests.S26Migrate.pools.all (fun p => (Migrate.report (fixAll p)).disagree.isEmpty))
  = true := by native_decide

-- And the residue is where §D says it is.
example : (Tests.S26Migrate.pools.map (fun p => (Migrate.report (fixAll p)).declined)
  == [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 17, 1, 0, 0, 0, 0]) = true := by native_decide

end Dllbc.Tests.S26Fuel

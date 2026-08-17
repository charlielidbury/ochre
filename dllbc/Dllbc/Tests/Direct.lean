import Dllbc.Program
import Dllbc.ProgMacro
import Dllbc.Boundary
import Dllbc.Std
import Dllbc.StdLemmas
import Dllbc.Tests.Diff

/-!
# Direct proving — the list flagship, and the partition stack it was built on

**A consolidation bucket** (M28 D10). The suite grew one file per milestone, which
made a test's home a fact about WHEN it was written rather than about what it is
about. These files were merged here, in the order below, with their content moved
VERBATIM — every namespace kept, so every cross-file reference in the tree still
resolves, and each former file is fenced by a comment naming it so the git-log
archaeology survives:

  * `S23Direct.lean`
  * `S19Partition.lean`

Each former file's `open`s are scoped by a `section`, so nothing leaks across the
seams.
-/

-- ┌── was `Dllbc/Tests/S23Direct.lean` ──────────────────────────────────────────────
section
/-!
# §23 test suite — direct proving with NO declared backward specs

M22 verified an in-place quicksort by *delegating* every mutation to a callee
carrying a declared `back` (a pure model function) and citing lemmas about that
model. That stack stays on main untouched, as the comparison baseline. M23 removes
the `back`s: a callee's ONLY description is its return type — a postcondition over
the exit snapshot (`*v` reads exit, `old *v` reads entry, §5.4) — and a caller sees
an opaque exit plus whatever evidence the callee returned.

## Stage (i): `sigmaRec`, the missing recursor (§9)

The kernel's comptime basis is "one recursor per former", and Σ was the omission:
pure conjunctions could be *built* (`Pair(sortedcert, permcert)`) but never
*projected*. §9 records the cost — the M22 quicksort postcondition's pain diary
traces four separate structural detours to this one gap. With back-less callees the
gap becomes load-bearing rather than merely expensive: a caller's whole knowledge of
its callee's exit is the returned certificate, so it MUST be able to take that
certificate apart.

`sigmaRec A B P f p : P p`, with `ι : sigmaRec A B P f (Pair a b) ↦ f a b` — the
standard dependent Σ eliminator, and non-recursive, so its single arm binds exactly
the two fields and takes no `ih`. Σ's parameters are a type `A` and a *family*
`B : A → Type` (unlike List's uniform parameter), which is why the `elim` sugar
requires the motive's binder type to be written as the Σ itself: `A` and `λ x. B`
are read off it.
-/

open Dllbc
open Dllbc.StdLemmas (LeRefl LeTrans LeUpR Append IdCongr IdTrans IdSym
  Set NthL SwapL LenSet SwapLSet LeRwR InsertL Ub Lb Take LebTrueLe LebFalseGt
  SortedHead SortedTail UbHead UbTail LbBound
  BoundAppend SortedAppendPivot LePredL CountConsL CountConsR Len CountAppend
  CountConsCongr UbPerm LbPerm ListRw)

namespace Dllbc.Tests.S23Direct

/-- Type-check a closed term against a closed type in the pure seed (as in §18/§19). -/
def chk (tm ty : Term) : Bool :=
  match (do let v ← readC 3000 tm; let t ← readC 3000 ty; hasTypeT 3000 v t).run (seedPure [] []) with
  | .ok r _ => r
  | .error _ _ => false

/-! ## (i.a) Non-dependent Σ: the conjunction projections

    The shape every back-less caller needs: a callee returns `Σ (H : P). Q` — a
    conjunction certificate — and the caller projects out the conjunct it wants.
    `B` ignores its binder here, so the motive is constant and both projections are
    ordinary. This is the M22 quicksort postcondition's own shape
    (`Σ (Sortedpart : SortedR …). (Π n. Id …)`), which until now could only be
    assembled, never taken apart. -/

def and_left : Term := prog{
  λ (A : Nat). λ (B : Nat). λ (C : Nat).
    λ (P : Σ (H : Le A B). Le B C).
      elim P return (λ (Q : Σ (H : Le A B). Le B C). Le A B) {
        Pair (X) (Y) => X } }
def and_left_ty : Term := prog{
  Π (A : Nat) → Π (B : Nat) → Π (C : Nat) → (Σ (H : Le A B). Le B C) → Le A B }
example : chk and_left and_left_ty = true := by native_decide

def and_right : Term := prog{
  λ (A : Nat). λ (B : Nat). λ (C : Nat).
    λ (P : Σ (H : Le A B). Le B C).
      elim P return (λ (Q : Σ (H : Le A B). Le B C). Le B C) {
        Pair (X) (Y) => Y } }
def and_right_ty : Term := prog{
  Π (A : Nat) → Π (B : Nat) → Π (C : Nat) → (Σ (H : Le A B). Le B C) → Le B C }
example : chk and_right and_right_ty = true := by native_decide

-- The projections COMPOSE with an ordinary lemma: destructure the conjunction and
-- feed both halves to `LeTrans`. This is exactly what a caller does with a
-- returned certificate — the reason the recursor is a prerequisite for the rest of
-- M23 rather than a nicety.
def and_trans : Term := prog{
  λ (A : Nat). λ (B : Nat). λ (C : Nat).
    λ (P : Σ (H : Le A B). Le B C).
      elim P return (λ (Q : Σ (H : Le A B). Le B C). Le A C) {
        Pair (X) (Y) => LeTrans A B C X Y } }
def and_trans_ty : Term := prog{
  Π (A : Nat) → Π (B : Nat) → Π (C : Nat) → (Σ (H : Le A B). Le B C) → Le A C }
example : chk and_trans and_trans_ty = true := by native_decide

/-! ## (i.b) Dependent Σ: the second projection needs a dependent motive

    When `B` mentions its binder, `snd`'s type mentions `fst p` — so the motive is
    `λ q. Le (S Z) (sfst q)`, and the arm type-checks only because the ι-rule fires
    *inside the type*: `sfst (Pair x y)` reduces to `x`. This is dependent Σ
    elimination proper, not a pair of independent projections. -/

def sfst : Term := prog{
  λ (P : Σ (n : Nat). Le (S Z) n).
    elim P return (λ (Q : Σ (n : Nat). Le (S Z) n). Nat) {
      Pair (X) (Y) => X } }
def sfst_ty : Term := prog{ (Σ (n : Nat). Le (S Z) n) → Nat }
example : chk sfst sfst_ty = true := by native_decide

def ssnd : Term := prog{
  λ (P : Σ (n : Nat). Le (S Z) n).
    elim P return (λ (Q : Σ (n : Nat). Le (S Z) n). Le (S Z) (sfst Q)) {
      Pair (X) (Y) => Y } }
def ssnd_ty : Term := prog{ Π (P : Σ (n : Nat). Le (S Z) n) → Le (S Z) (sfst P) }
example : chk ssnd ssnd_ty = true := by native_decide

/-! ## (i.c) The ι-rule computes -/

-- `sfst (Pair 2 (LeRefl 2)) ⇝ 2`, by ι on a concrete Pair.
def pv (t : Term) : Term := Pure.nf 4000 t
def vnat : Nat → Val | 0 => .ctor "Z" [] | k + 1 => .ctor "S" [vnat k]
def sfstApp : Term := prog{ sfst (Pair (S (S Z)) (LeRefl (S (S Z)))) }
example : (Val.know (pv sfstApp) == vnat 2) = true := by native_decide

-- ι fires under binders on a Pair whose COMPONENTS are neutral — the case that
-- matters, since a caller destructures a certificate about symbolic values, never
-- a closed one: `λ n. λ h. sfst (Pair n h)` normalizes to `λ n. λ h. n`.
example : (pv (prog{ λ (N : Nat). λ (H : Le (S Z) N). sfst (Pair N H) }) ==
           pv (prog{ λ (N : Nat). λ (H : Le (S Z) N). N })) = true := by native_decide

-- The dual: a neutral TARGET has no `Pair` to fire on, so the spine is a legal
-- stuck value rather than an error — which is what lets `ssnd`'s motive above
-- mention `sfst q` for a symbolic `q` and still be judged.

/-! ## (i.d) Negative controls — one per rule branch

    The typing rule has three premises that can fail (`f`, the target, and the
    result convert) plus the ι-rule's shape condition; each gets a test, per the
    M20 lesson (a negative test per RULE BRANCH, not per feature). -/

-- (1) Wrong arm component: `Pair(x)(y) => y` at the FIRST projection's type. The
-- arm must inhabit `P (Pair x y)`, which is `Le a b` — `y : Le b c` does not.
def and_left_lie : Term := prog{
  λ (A : Nat). λ (B : Nat). λ (C : Nat).
    λ (P : Σ (H : Le A B). Le B C).
      elim P return (λ (Q : Σ (H : Le A B). Le B C). Le A B) {
        Pair (X) (Y) => Y } }
example : chk and_left_lie and_left_ty = false := by native_decide

-- (2) Wrong RESULT type: `sfst` returns `Nat`, and the claim is that it returns a
-- proof. `finish` converts the motive-at-target against the ascribed type; this is
-- the branch that catches it.
def sfst_lie_ty : Term := prog{ (Σ (n : Nat). Le (S Z) n) → Le Z Z }
example : chk sfst sfst_lie_ty = false := by native_decide

-- (3) Wrong DEPENDENT motive: the second projection claimed one bigger than the
-- first component. `y : Le (S Z) x`, but `P (Pair x y)` is now `Le (S Z) (S x)` —
-- off by one, and nothing bridges it. This is the branch that would silently pass
-- if the motive were inferred from the arm rather than read off what is written.
def ssnd_lie : Term := prog{
  λ (P : Σ (n : Nat). Le (S Z) n).
    elim P return (λ (Q : Σ (n : Nat). Le (S Z) n). Le (S Z) (S (sfst Q))) {
      Pair (X) (Y) => Y } }
def ssnd_lie_ty : Term := prog{ Π (P : Σ (n : Nat). Le (S Z) n) → Le (S Z) (S (sfst P)) }
example : chk ssnd_lie ssnd_lie_ty = false := by native_decide

-- (4) Wrong TARGET: `sigmaRec` applied to something that is not of the Σ type it
-- declares. Here the target is a bare `Nat`, so the `s : Σ (x : A). B x` premise
-- fails even though the arm is fine.
def sfst_bad_target : Term := prog{ sfst (S Z) }
def sfst_bad_target_ty : Term := prog{ Nat }
example : chk sfst_bad_target sfst_bad_target_ty = false := by native_decide

/-! ## Stage (ii) prelude: DEPENDENT Σ results at a call site

    Building certificates is half of it; the other half is that a *caller* can
    receive one. A back-less callee's returned evidence is pinned to its own
    result — `Σ (r : List Nat). Id (List Nat) r (Drop i (old *v))` is split_off's
    ensures — and until M23 the call rule built a Σ result's tail INDEPENDENTLY of
    its head (`buildResult`'s own comment said so: "a dependent product over the
    first is not supported; no test needs it"). The tail's σ therefore carried a
    DANGLING `pvar` in its sctx type, and the pin was unusable:

        call: argument (σ1) does not have its parameter type (Id σ0 (S Z))

    The fix threads the already-built components into the tail's type (Machine.lean,
    `buildResult`'s `subs`). These three tests are the smallest statement of the
    property: a pinned result is usable, and it is usable *because* of the pin. -/

-- A back-less callee returning a PINNED value, and a consumer whose second
-- parameter's type mentions its first argument.
def pinOne : Term := prog{
  fn PinOne () -> Σ (r : Nat). Id Nat r (S Z) { Pair(S Z, Refl) };
  () }
def useIt : Term := prog{
  fn UseIt (n : Nat, h : Id Nat n (S Z)) -> Unit { () };
  () }
example : progOk pinOne = true := by native_decide
example : progOk useIt = true := by native_decide

-- The caller destructures the returned pair and feeds BOTH halves onward: `h`'s
-- type is `Id σa (S Z)` for the very σa bound to `a`. This is the caller-side
-- shape every back-less callee in the rest of M23 depends on.
def usePin : Term := prog{
  fn PinOne () -> Σ (r : Nat). Id Nat r (S Z) { Pair(S Z, Refl) };
  fn UseIt (n : Nat, h : Id Nat n (S Z)) -> Unit { () };
  fn UsePin () -> Unit
        { let p = PinOne();
          match p { Pair(a, h) => { UseIt(a, h); () } } };
  () }
example : progOk usePin = true := by native_decide

-- Not vacuous (a): the pin says `S Z`; a consumer wanting `S (S Z)` is rejected —
-- so the threaded type is the callee's actual claim, not a rubber stamp.
def useItLie : Term := prog{
  fn UseItLie (n : Nat, h : Id Nat n (S (S Z))) -> Unit { () };
  () }
-- A callee, written into each chain that calls it; the standalone form keeps
-- the verdict `S26Migrate.p23` was computing for it.
example : progOk useItLie = true := by native_decide
def usePinLie : Term := prog{
  fn PinOne () -> Σ (r : Nat). Id Nat r (S Z) { Pair(S Z, Refl) };
  fn UseItLie (n : Nat, h : Id Nat n (S (S Z))) -> Unit { () };
  fn UsePinLie () -> Unit
        { let p = PinOne();
          match p { Pair(a, h) => { UseItLie(a, h); () } } };
  () }
example : progRejects usePinLie "does not have its parameter type" = true := by native_decide

-- Not vacuous (b): drop the pin (a plain `Nat` result) and the caller learns
-- NOTHING about the value it got back — `Refl` cannot inhabit `Id σa (S Z)`. The
-- pin is what carries the knowledge across the boundary, which is the whole
-- premise of removing declared backs.
def plainOne : Term := prog{
  fn PlainOne () -> Nat { S Z };
  () }
-- A callee, written into each chain that calls it; the standalone form keeps
-- the verdict `S26Migrate.p23` was computing for it.
example : progOk plainOne = true := by native_decide
def useUnpinned : Term := prog{
  fn PlainOne () -> Nat { S Z };
  fn UseIt (n : Nat, h : Id Nat n (S Z)) -> Unit { () };
  fn UseUnpinned () -> Unit { let a = PlainOne(); UseIt(a, Refl); () };
  () }
example : progRejects useUnpinned "does not have its parameter type" = true := by native_decide

/-! ## Stage (v): recursion = self-ensures under §8's snapshot-subterm guard

    A call is checked against a signature alone (§5.3) — recursion forces that — so
    a SELF-call is admitted at the function's own declared return type. Through M22
    that return type was `Unit` for every recursive FnDef, and the real content lived
    in the declared `back`, checked by conversion. Remove the backs and the return
    type IS the postcondition, at which point admitting a self-call unconditionally
    is the Hoare rule for recursion with its side condition deleted: every false
    statement proves itself. It did. On main, before this section:

        fn bad () -> Id Nat Z (S Z) { bad() }            -- ACCEPTED
        fn bad2 (n : Nat) -> Id Nat Z (S Z) { bad2(n) }  -- ACCEPTED

    The side condition is §1.2's `[k]`, finally operational: a self-call is admitted
    only when the actual at the declared decreasing position is a STRICT STRUCTURAL
    SUBTERM of that parameter's current snapshot. The checker being a symbolic
    interpreter is what makes this cheap — inside `match n { S(m) => … }` the
    parameter's snapshot has been ⇜-refined to `S σ_m` while the actual is `σ_m`, so
    the comparison is ordinary structural equality on snapshots. The snapshot rides
    `refineSym` with the rest of the σ-bearing state (the M10 invariant), which is
    what makes it readable at the call site at all: owned match has meanwhile
    emptied the parameter's runtime slot.

    A negative test per RULE BRANCH (the M20 lesson), not per feature. -/

-- The honest shape, and the one the rest of M23 rides: structural decrease on a
-- declared fuel argument.
def recGood : Term := prog{
  fn RecGood [n] (n : Nat) -> Id Nat Z Z
        { match n { Z => Refl, S(m) => RecGood(m) } };
  () }
example : progOk recGood = true := by native_decide

-- BRANCH 1 — no `[k]` at all. THE headline control: this exact FnDef was accepted
-- before the guard, and it proves `Z = S Z`.
def recBad : Term := prog{
  fn RecBad () -> Id Nat Z (S Z) { RecBad() };
  () }
-- MIGRATES, AND IS STILL REFUSED — with a different sentence, which is the whole
-- of what the guard's deletion costs. §7 makes a recursive occurrence the `ih`
-- BINDER, and §8 makes scope the let-chain: a self-call resolves to nothing,
-- because a let-chain cannot reference downward. So `Z = S Z` stays unprovable
-- not by a side condition but by the name not existing.
example : progRejects recBad "unknown function" = true := by native_decide

-- BRANCH 2 — `[k]` declared, but the self-call passes the SAME fuel. Equal is not
-- strictly smaller; this is the shape the strictness in `strictSubterm` exists for.
def recSame : Term := prog{ fn RecSame [n] (n : Nat) -> Id Nat Z (S Z) { RecSame(n) }; () }
-- REFUSED AT THE ELABORATION, which is where this branch's content now lives:
-- §7 makes `ih` the sealed self-view AT THE PREDECESSOR, so a self-call at any
-- other argument has nothing to become, and `fnElab` says so rather than emitting
-- a recursor that would be a different function. Asserted on the refusal itself —
-- a twin that merely DECLINED would teach nothing.
example : progRejects recSame "not the predecessor" = true := by native_decide

-- BRANCH 3 — decrease at the WRONG index. The return type here is TRUE, so the
-- audit cannot be what rejects it: `[n]` is declared while `m` is what shrinks.
-- (Without this control the previous two would pass on a guard that merely
-- required *something* to decrease — which is unsound, since alternating branches
-- can each decrease a different coordinate forever.)
def recWrongIdx : Term := prog{
  fn RecWrongIdx [n] (n : Nat, m : Nat) -> Id Nat Z Z
        { match m { Z => Refl, S(m2) => RecWrongIdx(n, m2) } };
  () }
example : progRejects recWrongIdx "not the predecessor" = true := by native_decide

-- …and the same body with the honest index declared is accepted, so branch 3 is
-- about the index, not about the body.
def recRightIdx : Term := prog{
  fn RecRightIdx [m] (n : Nat, m : Nat) -> Id Nat Z Z
        { match m { Z => Refl, S(m2) => RecRightIdx(n, m2) } };
  () }
example : progOk recRightIdx = true := by native_decide

-- BRANCH 4 — an INCREASE reads as "not a subterm", not as a decrease: `S(m2)`
-- against a snapshot of `S m2` is equality one level up, and equality never passes.
def recGrow : Term := prog{
  fn RecGrow [n] (n : Nat) -> Id Nat Z Z
        { match n { Z => Refl, S(m2) => RecGrow(S(m2)) } };
  () }
example : progRejects recGrow "not the predecessor" = true := by native_decide

-- BRANCH 5 — MUTUAL recursion. The guard is per-declaration, so `f → g → f` would
-- let each admit the other's postcondition with nothing decreasing anywhere: the
-- same hole through two doors. Rejected outright (§8's measures are where a general
-- story would live).
def recMutA : Term := prog{
  fn RecMutA () -> Id Nat Z (S Z) { RecMutB() };
  fn RecMutB () -> Id Nat Z (S Z) { RecMutA() };
  () }
-- Same replacement, and §8 predicted exactly this: mutual recursion "becomes
-- unwritable" rather than staying rejected, because `recMutB` is not in scope
-- above `recMutA`. The rejection names the forward reference.
example : progRejects recMutA "unknown function" = true := by
  native_decide

-- The guard is STRUCTURAL, not Nat-specific: a list fuel decreases the same way.
def recList : Term := prog{
  fn RecList [l] (l : List Nat) -> Id Nat Z Z
        { match l { Nil => Refl, Cons(h, t) => RecList(t) } };
  () }
example : progOk recList = true := by native_decide

-- Two constructors down is still a strict subterm (the relation is transitive, not
-- just one-step) — which the quicksort recursion needs, since it peels `Cnt` twice
-- before recursing.
def recDeep : Term := prog{
  fn RecDeep [n] (n : Nat) -> Id Nat Z Z
        { match n { Z => Refl, S(a) => match a { Z => Refl, S(b) => RecDeep(b) } } };
  () }
-- **A MACRO LIMIT, NOT A CALCULUS ONE** (§12 open 3, corrected in M27-P1). The
-- macro declines two-constructors-down because §7 has it derive the motive
-- mechanically from the signature and this shape needs a different one. The FORM
-- exists and checks: `S27Dispose` §D writes `recDeep` as a sealed recursor and
-- accepts it, with a lie twin beside it. So what is asserted here is the macro's
-- refusal, and the carrier of the claim lives there.
example : progRejects recDeep "not the predecessor" = true := by native_decide

/-! ### The one shape the eliminators cannot express: `[v]`, and what it costs

    A BORROW parameter decreases through its PAYLOAD snapshot — §8's guard in its
    most literal form, and the only thing that shrinks in a list cursor with no
    counter. Snapshots are entry-knowledge and are never rewritten by mutation
    (§3.2), so the payload's structural decomposition is a fixed, well-founded
    order, and the declaration path admitted it.

    It has no recursor form. §7 elaborates `[k]` to `natRec`/`listRec` over the
    parameter itself, and a borrow is neither; §9's borrow-mode eliminator is FILED,
    not built. §12 decision 8 accepted the regression and blessed fuel-threading as
    the interim — a source change, since the signature grows a parameter and a bound
    and every caller supplies them, and never something an elaboration invents
    behind its author.

    So this is the whole of the `[v]` class, at program level: the `fn` lowering
    refuses it, and it refuses POINTING AT THE DECISION rather than at a shape.
    Three functions in this file used to be written this way — the list cursor
    below, `append_back` and `partition` — and all three are fuel-threaded in
    stage (vi)'s chain, where the price is one parameter and one dead branch. -/

def borrowDecrease : Term := prog{
  fn ZeroAll [v] (v : &mut List Nat) -> Unit
        { match v { Nil => (), Cons(hd, tl) => { *hd := 0; ZeroAll(tl); () } } };
  () }
-- Refused by the needle no other error can produce…
example : progRejects borrowDecrease FnMacro.fnRefusedNeedle = true := by native_decide
-- …and the refusal's own diagnosis survives into the message, which is what makes
-- it a decision rather than a wall: the programmer is told to thread fuel.
example : progRejects borrowDecrease "§12 decision 8" = true := by native_decide
-- It can never pass green: the sentinel is reached at the BINDING, not at a call,
-- so a refused function that nothing calls still fails.
example : progOk borrowDecrease = false := by native_decide
-- The paid twin — literally this function with a fuel parameter and a bound — is
-- `S26Fuel.zeroAllF`, which checks. The cost is measured, not estimated.

-- A NON-self call to a recursive function is untouched — the guard is about
-- self-calls, and every other call is the ordinary §5.3 signature rule.
def recCaller : Term := prog{
  fn RecGood [n] (n : Nat) -> Id Nat Z Z { match n { Z => Refl, S(m) => RecGood(m) } };
  fn RecCaller () -> Id Nat Z Z { RecGood(S Z) };
  () }
-- The callee is in scope by being written above it — no table (M28 φ).
example : progOk recCaller = true := by native_decide

/-! ## Stage (ii): ownership splitting — `split_off` and `append_back`

    The data plan for a back-less quicksort: recursion over WHOLE lists instead of
    `lo`/`Cnt` range indices. `split_off` takes the tail at depth `i` out of a
    borrowed list and returns it BY VALUE (it cannot come back as a borrow — its
    owner is local); `append_back` walks to the end and replaces the `Nil`. Between
    them the caller owns two independent lists, sorts each, and glues.

    Both are back-less: the ONLY description of either is its return type. And both
    ensures are stated in OBSERVATION functions — `Take`, `Drop`, `Append`, which
    define meaning independently of any implementation — not in a pure function
    mirroring the body's own algorithm, which is what a declared `back` was. That
    is the line: `Id (*v) (Take i (old *v))` IS split_off's spec, not a mirror of it.

    Both check with no declared back anywhere in the call tree, and the two machine
    gaps they forced are recorded at their use sites below. -/

-- `append_back(v, w)`: walk to the end of `*v`, put `w` there. The exit reading is
-- `Append (old *v) w` — the whole postcondition, and the whole description. It is
-- the third `[v]` function, so it is written FUEL-THREADED, in stage (vi)'s chain
-- where its one caller lives.

/-! ### The telescope's own vocabulary

    A `fn`'s parameters are `.var ⟨i, name⟩` at their positional index (§5.2), and a
    return type written outside the header — a skeleton, below — has to name them
    that way. These are those names, once, so that every skeleton in this file
    splices them rather than re-deriving an index. -/

def listNatT : Term := .app (.const "List") (.const "Nat")
def vT : Term := .var ⟨0, "v"⟩
def dvT : Term := .deref vT
def oldvT : Term := .app (.const "old") dvT
def iT : Term := .var ⟨1, "i"⟩
def kT : Term := .var ⟨1, "k"⟩
def xT : Term := .var ⟨2, "x"⟩
def jT : Term := .var ⟨2, "j"⟩
def sucT (t : Term) : Term := .ctorApp "S" [t]

-- `split_off(v, i)`: `*v` keeps the first `i`, the rest comes back by value. The
-- returned tail is Σ-PINNED to `Drop i (old *v)` — the caller's only knowledge of a
-- value it did not compute, which is why stage (ii)'s prelude above had to land
-- first.
--
-- Written as a SKELETON over its return type and its tail (the M28 χ standard):
-- the body is thirty lines and the three spec twins below differ from the honest
-- form in exactly one named argument each, so the body is written ONCE and the
-- difference is by construction rather than by a reader comparing two spellings.
def soUnder (ret tail : Term) : Term := prog{
  fn SplitOff [i] (v : &mut List Nat, i : Nat, hi : Le i (Len *v)) -> %ret
        { match i {
            -- i = Z: Take the whole payload out (§2.4's Take-and-refill, the idiom
            -- Rust rejects with E0507) and leave `Nil`. `Take Z l = Nil` and
            -- `Drop Z l = l` both compute, so both conjuncts are `Refl`.
            Z => { let tail = *v; *v := Nil; Pair(tail, Pair(Refl, Refl)) },
            S(i2) => match v {
              -- `hi : Le (S i2) (Len Nil)` is `Le (S i2) Z`, which IS `Bot`: the
              -- branch is dead and the audit admits an ex-falso at any type (§5.4).
              Nil => botElim Unit hi,
              Cons(hd, tl) => {
                -- `hi` passes down DEFINITIONALLY: `Len (Cons _ t) = S (Len t)`, so
                -- `Le (S i2) (S (Len σ_tl))` already IS `Le i2 (Len σ_tl)`. The M14
                -- bounds-cursor property, still holding.
                let y1 = Take i2 (*tl);
                let p = SplitOff(&m *tl, i2, hi);
                match p { Pair(rr, q) => match q { Pair(H1, h2) => {
                  -- The prefix conjunct needs a congruence under `Cons (*hd)`, and
                  -- reading `*tl` here — AFTER handing `&mut *tl` to the call — is
                  -- the only way to name the callee's exit. That read is what
                  -- forced the ⇝-side demand-end (Machine.lean, `collapseCDerefs`):
                  -- before it, the projection returned the parked `loanₘ` itself and
                  -- a state marker rode silently into this proof term.
                  -- The suffix conjunct needs nothing: `Drop (S i2) (Cons h t)` IS
                  -- `Drop i2 t`, so the callee's `h2` is already the goal.
                  let H0 = *hd;
                  let c1 = IdCongr (List Nat) (List Nat) (λ (A : List Nat). Cons H0 A)
                             (*tl) y1 H1;
                  Pair(rr, Pair(c1, h2)) } } }
              }
            }
        } };
  %tail }

/-- The return type, as a skeleton over its two conjuncts' right-hand sides. Still
    SURFACE syntax — only the two subterms the twins vary are spliced — so what a
    reader compares is `Take i (old *v)` against `Take (S i) (old *v)`, one
    argument apart, and not two hand-built Σ-chains. -/
def soRet (pre suf : Term) : Term := prog{
  Σ (ret : List Nat). Σ (H1 : Id (List Nat) %dvT %pre). Id (List Nat) ret %suf }

def soHonest : Term := soRet (prog{ Take %iT %oldvT }) (prog{ Drop %iT %oldvT })
def splitOff : Term := soUnder soHonest .unit
example : progOk splitOff = true := by native_decide

/-! ### Not vacuous: the spec twins, and the body twin

    Three spec lies (shifting either index, and swapping the two conjuncts) and one
    BODY lie. The spec lies are all caught on the `i = Z` path, so they alone would
    leave the recursive path untested; the body lie breaks the congruence in the
    `Cons` branch and is the control for that path. -/

def splitOffLieTake : Term := soUnder (soRet (prog{ Take (S %iT) %oldvT }) (prog{ Drop %iT %oldvT })) .unit
def splitOffLieDrop : Term := soUnder (soRet (prog{ Take %iT %oldvT }) (prog{ Drop (S %iT) %oldvT })) .unit
def splitOffLieSwap : Term := soUnder (soRet (prog{ Drop %iT %oldvT }) (prog{ Take %iT %oldvT })) .unit
example : progRejects splitOffLieTake "does not have return type" = true := by native_decide
example : progRejects splitOffLieDrop "does not have return type" = true := by native_decide
example : progRejects splitOffLieSwap "does not have return type" = true := by native_decide

-- The BODY lie: the congruence forgets to put `*hd` back on the front (identity
-- instead of `Cons (*hd) ·`), so the prefix conjunct is off by the head element.
-- Rejected on the RECURSIVE path, which no spec twin above reaches.
--
-- **Transcribed rather than sharing `soUnder`'s body, and that is forced.** What
-- varies is a subterm INSIDE the body that names `hd` — a binder the `fn` lowering
-- mints an id for — and a `%` splice is a Lean `Term` written outside the macro,
-- which has no way to say "the `hd` this match will bind". The χ/ψ rules are about
-- when sharing is worth its cost; this is the case where it is not available.
def splitOffLieHead : Term := prog{
  fn SplitOff [i] (v : &mut List Nat, i : Nat, hi : Le i (Len *v)) -> %soHonest
        { match i {
            Z => { let tail = *v; *v := Nil; Pair(tail, Pair(Refl, Refl)) },
            S(i2) => match v {
              Nil => botElim Unit hi,
              Cons(hd, tl) => {
                let y1 = Take i2 (*tl);
                let p = SplitOff(&m *tl, i2, hi);
                match p { Pair(rr, q) => match q { Pair(H1, h2) => {
                  let c1 = IdCongr (List Nat) (List Nat) (λ (A : List Nat). A)
                             (*tl) y1 H1;
                  Pair(rr, Pair(c1, h2)) } } }
              }
            }
        } };
  () }
example : progRejects splitOffLieHead "does not have return type" = true := by native_decide

/-! ### The executing differential — the body really splits

    `progOk` proves the postcondition symbolically; this runs the SAME program on
    concrete lists and confirms `*v` keeps `Take i l` while the returned value is
    `Drop i l`, at the two boundaries and in the middle. The caller rides `soUnder`'s
    own chain as its tail, so what runs is the function declared above it. -/

def tnatT : Nat → Term | 0 => .ctorApp "Z" [] | k + 1 => .ctorApp "S" [tnatT k]
def tlistT : List Nat → Term | [] => .ctorApp "Nil" [] | x :: xs => .ctorApp "Cons" [tnatT x, tlistT xs]
def vnatV : Nat → Val | 0 => .ctor "Z" [] | k + 1 => .ctor "S" [vnatV k]
def vlistV : List Nat → Val | [] => .ctor "Nil" [] | x :: xs => .ctor "Cons" [vnatV x, vlistV xs]
-- SUBJECT: the executing-mode differential's raw Term caller.
def soCallerTail (l : List Nat) (i : Nat) : Term :=
  .letIn ⟨0, "x"⟩ (tlistT l)
    (.letIn ⟨1, "b"⟩ (.borrow (.var ⟨0, "x"⟩))
      (.letIn ⟨2, "p"⟩ (.call "SplitOff" [.var ⟨1, "b"⟩, tnatT i, .unit])
        (.matchE ⟨2, "p"⟩ none [.mk "Pair" [⟨3, "rr"⟩, ⟨4, "q"⟩] (.letIn ⟨5, "y"⟩ (.var ⟨0, "x"⟩) .unit)])))
def runSplit (l : List Nat) (i : Nat) : Bool :=
  match Dllbc.Tests.S9Diff.runExec (soUnder soHonest (soCallerTail l i)) with
  | .ok env => env.lookup "y" == some (vlistV (l.take i)) && env.lookup "rr" == some (vlistV (l.drop i))
  | .error _ => false

example : runSplit [1,2,3,4] 2 = true := by native_decide   -- split in the middle
example : runSplit [1,2,3] 0 = true := by native_decide      -- take nothing, hand the whole list back
example : runSplit [1,2,3] 3 = true := by native_decide      -- take everything, hand back Nil

/-! ## Stage (iii): the swap leaf, relational — and what it says about M22's arc

    M22's central finding was that an in-place leaf mutating through pointer writes
    has an OPAQUE exit, so no value-level postcondition is provable about it, and
    the escape was delegation: mutate through a callee carrying a declared `back`
    and cite a pure lemma about its model. From that, a three-feature arc was filed
    forward — ISSUED-PAYLOAD PINNING, then the `SwapLSet` BRIDGE, then
    AUDIT-REWRITE-ALONG-CITED-BRIDGES — as the route to provable inline leaves.

    That arc is not needed, and the reason is worth stating precisely, because it
    sharpens the M22 finding rather than contradicting it. The opacity is a property
    of borrows ISSUED BY A CALL: `buildResult` mints an issued borrow's payload as a
    fresh σ, because signature-only checking has nothing to say what the payload IS
    at issue time. It is NOT a property of inline mutation. A leaf that does its own
    cursor work through the body's OWN match-field borrows (§3.3) writes into a
    suspension the audit collapses itself, so its exit is a constructor tree over
    known snapshots — fully provable, with nothing minted opaquely anywhere.

    So the whole arc collapses to a program-level choice: walk the list yourself
    instead of calling `nth2`. `set_at` below is the proof of that, and `swap_at`
    shows the second feature evaporating too — the `SwapLSet` bridge M22 proved and
    parked as forward infrastructure "for the audit to cite once pinning lands" is
    just an ordinary lemma applied in the body, needing no audit machinery at all.
    Feature 3 (audit-rewrite) had three convergence points in M22's ledger; this
    removes two of them, and re-scopes pinning to "only if you insist on calling
    a cursor rather than being one". -/

/-! `set_at(v, i, x)` writes `x` at position `i`, in place, through the body's own
    field reborrows; `swap_at(v, i, j)` is two `set_at`s and the M22 bridge. They are
    ONE chain because the second calls the first — the caller is in scope by being
    written below it — and the chain takes BOTH return types as parameters, so each
    of the four twins varies exactly one of them while the two bodies are written
    once.

    **One chain serves both twin families, and that is a refinement of M28 χ's
    forced-duplication note.** χ wrote `insert_at`'s header a second time inside
    `pick`'s program because two `%`-spliced chains collided at `progBase` (an id
    collision M32 R4 retired along with the arithmetic), and read it as the price
    of the guard. The price is only paid when the two functions need
    to be varied through DIFFERENT prefixes. Here they do not: a lying `set_at` is
    refused at its own seal, and a sealed `let` fires its audit at its own node in
    PROGRAM ORDER (§8, and `S26Prog` §B asserts it), so the message a `set_at` twin
    is caught by is `set_at`'s — `swap_at`, which also breaks under it, is never
    reached. Varying the second return type leaves the first honest and the
    attribution is `swap_at`'s for the same reason. -/

def setSwapUnder (sret wret tail : Term) : Term := prog{
  fn SetAt [i] (v : &mut List Nat, i : Nat, x : Nat, hi : Le (S i) (Len *v)) -> %sret
        { match i {
            -- `*hd := x` is a strong update through a match-field reborrow: the
            -- parent suspends, the audit collapses it, and the exit is `Cons x σ_tl`
            -- — which IS `Set Z x (Cons σ_hd σ_tl)`, so the proof is `Refl`.
            Z => match v { Nil => botElim Unit hi, Cons(hd, tl) => { *hd := x; Refl } },
            S(i2) => match v {
              Nil => botElim Unit hi,
              Cons(hd, tl) => {
                let y = Set i2 x (*tl);
                let h = SetAt(&m *tl, i2, x, hi);
                let H0 = *hd;
                IdCongr (List Nat) (List Nat) (λ (A : List Nat). Cons H0 A) (*tl) y h
              }
            }
        } };
  -- `SwapAt(v, i, j)`: two `SetAt`s and the M22 bridge, ensuring the model
  -- function `SwapL` directly. Not recursive itself — the recursion is `SetAt`'s.
  fn SwapAt (v : &mut List Nat, i : Nat, j : Nat, pij : Le (S i) j,
                    p2 : Le (S j) (Len *v), hi : Le (S i) (Len *v)) -> %wret
        { let a = NthL i (*v);
          let b = NthL j (*v);
          -- The M22 bridge, cited as an ordinary lemma in the body. No audit
          -- feature, no pinning: `Set i b (Set j a s)` IS the set-form it relates.
          let bridge = SwapLSet i j (old *v) pij p2;
          let h1 = SetAt(&m *v, j, a, p2);
          -- The bound tax (M21's, unchanged): the second write's bound is stated
          -- over the LIVE `*v`, which the first write replaced with an opaque σ′, so
          -- it transports back through `LenSet` along h1.
          let hlen = IdTrans Nat (Len *v) (Len (Set j a (old *v))) (Len (old *v))
                       (IdCongr (List Nat) Nat Len (*v) (Set j a (old *v)) h1)
                       (LenSet j a (old *v));
          let hi2 = LeRwR (S i) (Len (old *v)) (Len *v)
                      (IdSym Nat (Len *v) (Len (old *v)) hlen) hi;
          -- PAIN DIARY (the recurring idiom, now named). After the second call the
          -- first call's exit σ′ can no longer be NAMED — `*v` reads the newest
          -- value, and nothing binds an older one. So the entire remaining
          -- derivation is staged as a FUNCTION OF THE NEXT EXIT while σ′ is still
          -- readable, and applied afterwards. This is the third appearance of the
          -- shape (M22's proof-linearity dodge, append_back's moved data argument,
          -- and now a superseded intermediate snapshot), and it is the general one:
          -- a body can only ever talk about the CURRENT exit, so any proof spanning
          -- two mutations must be built before the second and applied after it.
          -- The clean fix is a way to bind a snapshot — `let` at comptime, naming an
          -- exit the way `old` names an entry.
          -- **AND §2.4 MAKES THE SNAPSHOT VISIBLE** (M31 Stage A). The paragraph
          -- above ends "the clean fix is a way to bind a snapshot", and this is
          -- what the citation rule turns that into: the λ may no longer CITE a
          -- runtime binding, so every value it was silently freezing at formation
          -- is named first, on the line above, where a reader can see which
          -- moment it belongs to. Nothing is staged differently — the λ closed
          -- over exactly these values before, at exactly this point — the freeze
          -- has simply stopped being implicit. `V0` is the pre-`h2` payload,
          -- which is precisely the superseded intermediate the diary entry is
          -- about, and it now has a name.
          let I0 = i;
          let B0 = b;
          let J0 = j;
          let A0 = a;
          let V0 = *v;
          let OldV0 = old *v;
          let H1 = h1;
          let Bridge0 = bridge;
          let Finish = (λ (E : List Nat). λ (Hh : Id (List Nat) E (Set I0 B0 V0)).
                          IdTrans (List Nat) E (Set I0 B0 V0) (SwapL I0 J0 OldV0)
                            Hh
                            (IdTrans (List Nat) (Set I0 B0 V0) (Set I0 B0 (Set J0 A0 OldV0))
                               (SwapL I0 J0 OldV0)
                               (IdCongr (List Nat) (List Nat) (λ (Z0 : List Nat). Set I0 B0 Z0)
                                 V0 (Set J0 A0 OldV0) H1)
                               Bridge0));
          let h2 = SetAt(&m *v, i, b, hi2);
          Finish (*v) h2 };
  %tail }

/-- Each return type as a skeleton over the model function it cites — still surface
    syntax, one spliced subterm, so the twins below read as the lie they are. -/
def exitIs (rhs : Term) : Term := prog{ Id (List Nat) %dvT %rhs }

def setHonest : Term := exitIs (prog{ Set %iT %xT %oldvT })
def swapHonest : Term := exitIs (prog{ SwapL %iT %jT %oldvT })

/-- The pair, both honest. Also the regression pin M28's survey held separately:
    `swap_at` calls `set_at [i]`, whose decreasing parameter is SECOND, so the sealed
    callee's telescope is `(i, v, x, hi)` while the call is written in DECLARATION
    order — the chain has to permute it (`retarget`), and before it did the borrow
    was checked against `i : Nat`. -/
def setSwap : Term := setSwapUnder setHonest swapHonest .unit
example : progOk setSwap = true := by native_decide

/-! ### Not vacuous -/

-- The index off by one, and the no-op, once per function.
example : progRejects (setSwapUnder (exitIs (prog{ Set (S %iT) %xT %oldvT })) swapHonest .unit)
  "does not have return type" = true := by native_decide
example : progRejects (setSwapUnder (exitIs oldvT) swapHonest .unit)
  "does not have return type" = true := by native_decide
example : progRejects (setSwapUnder setHonest (exitIs (prog{ SwapL (S %iT) %jT %oldvT })) .unit)
  "does not have return type" = true := by native_decide
example : progRejects (setSwapUnder setHonest (exitIs oldvT) .unit)
  "does not have return type" = true := by native_decide

/-! ### The executing differential — the bodies really write and really swap -/

-- SUBJECT: executing-mode raw Term callers (proof arguments are placeholders `()`,
-- which the executing run does not type-check). Each rides the honest chain as its
-- tail, so what runs is the function declared above it.
def setCallerTail (l : List Nat) (i x : Nat) : Term :=
  .letIn ⟨0, "z"⟩ (tlistT l)
    (.letIn ⟨1, "b"⟩ (.borrow (.var ⟨0, "z"⟩))
      (.seq (.call "SetAt" [.var ⟨1, "b"⟩, tnatT i, tnatT x, .unit])
        (.letIn ⟨2, "y"⟩ (.var ⟨0, "z"⟩) .unit)))
def runSetAt (l : List Nat) (i x : Nat) : Bool :=
  match Dllbc.Tests.S9Diff.runExec (setSwapUnder setHonest swapHonest (setCallerTail l i x)) with
  | .ok env => env.lookup "y" == some (vlistV (l.set i x))
  | .error _ => false

example : runSetAt [1,2,3] 0 9 = true := by native_decide
example : runSetAt [1,2,3] 2 9 = true := by native_decide
example : runSetAt [5,5,5,5] 1 7 = true := by native_decide

def swapCallerTail (l : List Nat) (i j : Nat) : Term :=
  .letIn ⟨0, "z"⟩ (tlistT l)
    (.letIn ⟨1, "b"⟩ (.borrow (.var ⟨0, "z"⟩))
      (.seq (.call "SwapAt" [.var ⟨1, "b"⟩, tnatT i, tnatT j, .unit, .unit, .unit])
        (.letIn ⟨2, "y"⟩ (.var ⟨0, "z"⟩) .unit)))
def runSwapAt (l : List Nat) (i j : Nat) : Bool :=
  match Dllbc.Tests.S9Diff.runExec (setSwapUnder setHonest swapHonest (swapCallerTail l i j)) with
  | .ok env =>
    match l.get? i, l.get? j with
    | some a, some b => env.lookup "y" == some (vlistV ((l.set i b).set j a))
    | _, _ => false
  | .error _ => false

example : runSwapAt [1,2,3] 0 2 = true := by native_decide      -- ends
example : runSwapAt [1,2,3,4] 1 2 = true := by native_decide    -- adjacent interior
example : runSwapAt [4,1,3,2,5] 0 4 = true := by native_decide  -- full span

/-! ## Stage (iv) groundwork: `insert_at`, and where a body's knowledge runs out

    The relational partition needs one more mutator and one machine fact, and the
    fact is the milestone's sharpest limitation, so it is established here with its
    own negative control rather than discovered mid-proof.

    `insert_at` is the mutation a LINKED-LIST partition actually performs: relink one
    cell at index `k`. (Lomuto's swap-based scan is an array algorithm; the north
    star's naturalness-first rule says the program stays natural, and `swap_at` above
    remains available for anyone who wants the array shape.) It is `split_off`'s
    idiom again — take-and-refill through the body's own borrows — and checks the
    same way. -/

-- The return type is the ONLY description of this function, so it is written with
-- `exitIs`, the shared mutator skeleton — honest and lies differ in exactly its one
-- argument, provably, rather than by a reader comparing two spellings.
def insLT (k x l : Term) : Term := .app (.app (.app Dllbc.StdLemmas.InsertL k) x) l

/-- The function, once, with its return type and what follows it as parameters. -/
def insUnder (ret tail : Term) : Term := prog{
  fn InsertAt [k] (v : &mut List Nat, k : Nat, x : Nat) -> %ret
        { match k {
            Z => { let t = *v; *v := Cons(x, t); Refl },
            S(k2) => match v {
              -- past the end, `x` lands last: `InsertL (S k) x Nil = Cons x Nil`.
              Nil => { *v := Cons(x, Nil); Refl },
              Cons(hd, tl) => {
                let y = InsertL k2 x (*tl);
                let h = InsertAt(&m *tl, k2, x);
                let H0 = *hd;
                IdCongr (List Nat) (List Nat) (λ (A : List Nat). Cons H0 A) (*tl) y h
              }
            }
        } };
  %tail }

def insHonest : Term := exitIs (insLT kT xT oldvT)
def insertAt : Term := insUnder insHonest .unit
example : progOk insertAt = true := by native_decide

-- The index off by one, and the no-op. Each varies the skeleton's one argument.
example : progRejects (insUnder (exitIs (insLT (sucT kT) xT oldvT)) .unit)
  "does not have return type" = true := by native_decide
example : progRejects (insUnder (exitIs oldvT) .unit)
  "does not have return type" = true := by native_decide

-- `InsertL` computes, including the past-the-end case the `Nil` branch implements.
def insLC (k x : Nat) (l : List Nat) : Term := insLT (tnatT k) (tnatT x) (tlistT l)
example : (Val.know (pv (insLC 0 9 [1,2,3])) == vlistV [9,1,2,3]) = true := by native_decide
example : (Val.know (pv (insLC 2 9 [1,2,3])) == vlistV [1,2,9,3]) = true := by native_decide
example : (Val.know (pv (insLC 3 9 [1,2,3])) == vlistV [1,2,3,9]) = true := by native_decide
example : (Val.know (pv (insLC 5 9 [1,2,3])) == vlistV [1,2,3,9]) = true := by native_decide
example : (Val.know (pv (insLC 0 9 [])) == vlistV [9]) = true := by native_decide

-- SUBJECT: executing-mode raw Term caller.
def insCallerTail (l : List Nat) (k x : Nat) : Term :=
  .letIn ⟨0, "z"⟩ (tlistT l)
    (.letIn ⟨1, "b"⟩ (.borrow (.var ⟨0, "z"⟩))
      (.seq (.call "InsertAt" [.var ⟨1, "b"⟩, tnatT k, tnatT x])
        (.letIn ⟨2, "y"⟩ (.var ⟨0, "z"⟩) .unit)))
def runInsertAt (l : List Nat) (k x : Nat) : Bool :=
  match Dllbc.Tests.S9Diff.runExec (insUnder insHonest (insCallerTail l k x)) with
  | .ok env => env.lookup "y" == some (vlistV (l.take k ++ [x] ++ l.drop k))
  | .error _ => false

example : runInsertAt [1,2,3] 0 9 = true := by native_decide
example : runInsertAt [1,2,3] 2 9 = true := by native_decide
example : runInsertAt [1,2,3] 3 9 = true := by native_decide

/-! ### THE WALL, and the rule that closes it: BRANCH EQUATIONS

    M18's two-layer principle says motive abstraction handles OCCURRENCES and branch
    equations handle KNOWLEDGE. A body-level `match` had only the first layer. When
    the scrutinee is a stuck spine, `generalizeStuck` abstracts it to a fresh σ_b
    across all σ-bearing state and the branch refines σ_b := True — so everything
    that ALREADY mentioned the spine now reads `True`, which is what M19's stuckProbe
    tests. But a body that writes `Leb a b` AFTER the split recomputes the spine, and
    nothing hands back the equation.

    That is exactly backwards for direct proving, where the body must PRODUCE the
    evidence rather than merely have its types agree. `Refl : Id Bool (Leb a b) True`
    does not check inside the `True` branch — kept here as the negative half of the
    pair: -/

def needLe : Term := prog{
  fn NeedLe (a : Nat, b : Nat, h : Le a b) -> Unit { () };
  () }
-- A callee, written into each chain that calls it; the standalone form keeps
-- the verdict `S26Migrate.p23` was computing for it.
example : progOk needLe = true := by native_decide
def branchKnowledge : Term := prog{
  fn NeedLe (a : Nat, b : Nat, h : Le a b) -> Unit { () };
  fn BranchKnowledge (a : Nat, b : Nat) -> Unit
        { let c = Leb a b;
          match c {
            True => { NeedLe(a, b, LebTrueLe a b Refl); () },
            False => ()
          } };
  () }
example : progRejects branchKnowledge "does not have its parameter type" = true := by native_decide

/-! **THE RULE** (M23 phase A). `match h : c { … }` additionally binds, in every
    branch, an equation `h : Id τ ⟨the scrutinee's PRE-SPLIT value⟩ ⟨this branch's
    constructor⟩`. That is the standard dependent-match-with-equations shape — Lean's
    `match h : x with`, Coq's `destruct … eqn:` — and it stays inside §3.2's
    knowledge/state invariant, because the equation IS the branch's match-shape
    knowledge: a fact about the value, true at entry and forever, until now applied
    only as a substitution and here additionally reified as a citable term.

    The pre-split value is where the two layers come apart. At an ordinary split ⇜
    rewrites the scrutinee's value to this constructor everywhere, so the equation's
    two endpoints are already identical and `h` is `Refl` — informative-free, as it
    should be. At a STUCK split `generalizeStuck` ABSTRACTED the spine before the
    refinement, so nothing in the state mentions `Leb a b` any more and a body that
    recomputes it is talking about a term the refinement never saw. There the
    equation is a genuine hypothesis, minted as a fresh σ typed
    `Id Bool (Leb σa σb) True` — the one thing this rule adds.

    The positive twin of `branchKnowledge`: the SAME body, with the equation cited in
    place of `Refl`. The pair is the whole claim — the rule does exactly one new
    thing. -/

def branchKnowledgeEq : Term := prog{
  fn NeedLe (a : Nat, b : Nat, h : Le a b) -> Unit { () };
  fn BranchKnowledgeEq (a : Nat, b : Nat) -> Unit
        { let c = Leb a b;
          match e : c {
            True => { NeedLe(a, b, LebTrueLe a b e); () },
            False => ()
          } };
  () }
example : progOk branchKnowledgeEq = true := by native_decide

-- Both branches, in the direction each can actually prove: `False` gives
-- `Id Bool (Leb a b) False`, hence `Le (S b) a` — so the equation is per-branch,
-- not a single fact smuggled in twice.
def needGt : Term := prog{
  fn NeedGt (a : Nat, b : Nat, h : Le (S b) a) -> Unit { () };
  () }
-- A callee, written into each chain that calls it; the standalone form keeps
-- the verdict `S26Migrate.p23` was computing for it.
example : progOk needGt = true := by native_decide
def branchKnowledgeBoth : Term := prog{
  fn NeedLe (a : Nat, b : Nat, h : Le a b) -> Unit { () };
  fn NeedGt (a : Nat, b : Nat, h : Le (S b) a) -> Unit { () };
  fn BranchKnowledgeBoth (a : Nat, b : Nat) -> Unit
        { let c = Leb a b;
          match e : c {
            True => { NeedLe(a, b, LebTrueLe a b e); () },
            False => { NeedGt(a, b, LebFalseGt a b e); () }
          } };
  () }
example : progOk branchKnowledgeBoth = true := by
  native_decide

-- The `if` sugar carries it too (`if h : c { … } else { … }`), which is the form the
-- partition body wants.
def branchKnowledgeIf : Term := prog{
  fn NeedLe (a : Nat, b : Nat, h : Le a b) -> Unit { () };
  fn NeedGt (a : Nat, b : Nat, h : Le (S b) a) -> Unit { () };
  fn BranchKnowledgeIf (a : Nat, b : Nat) -> Unit
        { if e : Leb a b { NeedLe(a, b, LebTrueLe a b e); () }
          else { NeedGt(a, b, LebFalseGt a b e); () } };
  () }
example : progOk branchKnowledgeIf = true := by
  native_decide

/-! #### Negative controls — one per rule branch

    The rule has exactly three branches that can produce an equation: the stuck
    split (a real hypothesis), the ordinary symbolic split (`Refl`), and the
    concrete split (`Refl`). Each gets a control, plus the two ways the minted
    hypothesis could be a rubber stamp. -/

-- (1) The equation is the branch's OWN constructor, not the other one: citing
-- `LebFalseGt` on the True branch's `e : Id Bool (Leb a b) True` is rejected.
def branchEqSwapped : Term := prog{
  fn NeedLe (a : Nat, b : Nat, h : Le a b) -> Unit { () };
  fn NeedGt (a : Nat, b : Nat, h : Le (S b) a) -> Unit { () };
  fn BranchEqSwapped (a : Nat, b : Nat) -> Unit
        { let c = Leb a b;
          match e : c {
            True => { NeedGt(a, b, LebFalseGt a b e); () },
            False => ()
          } };
  () }
example : progRejects branchEqSwapped "does not have its parameter type" = true := by native_decide

-- (2) The equation is about the SPINE THAT WAS SPLIT ON, not any spine: split on
-- `Leb a b`, then claim the equation is about `Leb b a`. Rejected — so the minted
-- type is read off the abstracted scrutinee, not fabricated per use site.
def needLeSwap : Term := prog{
  fn NeedLeSwap (a : Nat, b : Nat, h : Le b a) -> Unit { () };
  () }
-- A callee, written into each chain that calls it; the standalone form keeps
-- the verdict `S26Migrate.p23` was computing for it.
example : progOk needLeSwap = true := by native_decide
def branchEqWrongSpine : Term := prog{
  fn NeedLeSwap (a : Nat, b : Nat, h : Le b a) -> Unit { () };
  fn BranchEqWrongSpine (a : Nat, b : Nat) -> Unit
        { let c = Leb a b;
          match e : c {
            True => { NeedLeSwap(a, b, LebTrueLe b a e); () },
            False => ()
          } };
  () }
example : progRejects branchEqWrongSpine "does not have its parameter type" = true := by native_decide

-- (3) An ORDINARY symbolic split still yields only `Refl`: `n`'s equation in the
-- `S` branch is `Id Nat (S σm) (S σm)` — ⇜ already rewrote the pre-split value, so
-- both endpoints are the constructor tree and nothing off-diagonal is derivable.
def wantEqLie : Term := prog{
  fn WantEqLie (n : Nat, h : Id Nat (S n) n) -> Unit { () };
  () }
-- A callee, written into each chain that calls it; the standalone form keeps
-- the verdict `S26Migrate.p23` was computing for it.
example : progOk wantEqLie = true := by native_decide
def branchEqPlainSym : Term := prog{
  fn WantEqLie (n : Nat, h : Id Nat (S n) n) -> Unit { () };
  fn BranchEqPlainSym (n : Nat) -> Unit
        { match e : n { Z => (), S(m) => { WantEqLie(m, e); () } } };
  () }
example : progRejects branchEqPlainSym "does not have its parameter type" = true := by native_decide

-- …and the reflexive reading of that same equation IS available: `Id Nat (S m) (S m)`.
def wantRefl : Term := prog{
  fn WantRefl (n : Nat, h : Id Nat (S n) (S n)) -> Unit { () };
  () }
-- A callee, written into each chain that calls it; the standalone form keeps
-- the verdict `S26Migrate.p23` was computing for it.
example : progOk wantRefl = true := by native_decide
def branchEqPlainSymRefl : Term := prog{
  fn WantRefl (n : Nat, h : Id Nat (S n) (S n)) -> Unit { () };
  fn BranchEqPlainSymRefl (n : Nat) -> Unit
        { match e : n { Z => (), S(m) => { WantRefl(m, e); () } } };
  () }
example : progOk branchEqPlainSymRefl = true := by
  native_decide

-- (4) The CONCRETE split (the executing side and any concrete scrutinee) binds the
-- equation too, so a body written with `match h :` runs. The differential below
-- exercises the same path end to end.
def concreteEq : Term := prog{
  fn WantRefl (n : Nat, h : Id Nat (S n) (S n)) -> Unit { () };
  fn ConcreteEq () -> Unit
        { let n = S(Z);
          match e : n { Z => (), S(m) => { WantRefl(m, e); () } } };
  () }
example : progOk concreteEq = true := by native_decide

-- (5) Not vacuous by scoping accident: WITHOUT the binder the same body is
-- unelaboratable (`e` is unbound), and WITH it the branch-free `Refl` of the wall
-- test is still rejected — i.e. binding `e` did not also make `Refl` check. This is
-- `branchKnowledge` above; the pair (it, `branchKnowledgeEq`) is the control.

/-! ### The route around it, verified in both halves

    Rather than add a `destruct-eqn:` to the body's match, keep the body BRANCH-FREE
    and let the pure fragment do the case analysis, where the knowledge is available.

    Half 1 — the body computes its decision as an INDEX with `boolRec` and never
    matches on it. The stuck spine flows through the call and meets the ensures
    definitionally. (This is a better program anyway: index arithmetic, not control
    flow, which is how the mutation was going to be expressed regardless.) -/

-- `insert_at`'s header is repeated here rather than spliced: a `%`-spliced tail
-- could not itself declare functions until M32 R4, because both chains numbered
-- their slots from `progBase` and collided by id. It can now; one chain, both
-- functions, is kept because it is what was written.
def pick : Term := prog{
  fn InsertAt [k] (v : &mut List Nat, k : Nat, x : Nat) -> %insHonest
        { match k {
            Z => { let t = *v; *v := Cons(x, t); Refl },
            S(k2) => match v {
              -- past the end, `x` lands last: `InsertL (S k) x Nil = Cons x Nil`.
              Nil => { *v := Cons(x, Nil); Refl },
              Cons(hd, tl) => {
                let y = InsertL k2 x (*tl);
                let h = InsertAt(&m *tl, k2, x);
                let H0 = *hd;
                IdCongr (List Nat) (List Nat) (λ (A : List Nat). Cons H0 A) (*tl) y h
              }
            }
        } };
  fn Pick (v : &mut List Nat, x : Nat, p : Nat)
        -> Id (List Nat) (*v)
             (InsertL (boolRec (λ (B : Bool). Nat) Z (S Z) (Leb x p)) x (old *v))
        -- (M26-B) `ki`, not `K`. §6 makes capitalisation the binder-mode marker,
        -- and this binder is genuinely RUNTIME: `InsertAt` matches on the index
        -- it is passed. The capital was stylistic — this was the only binder in
        -- the whole corpus whose name contradicted its role, and the fence is
        -- what found it.
        { let ki = boolRec (λ (B : Bool). Nat) Z (S Z) (Leb x p);
          InsertAt(&m *v, ki, x) };
  () }
example : progOk pick = true := by native_decide

/-! Half 2 — the pure lemma, over the SAME stuck index, gets its branch knowledge
    from a CONVOY MOTIVE: the motive carries `Id Bool <spine> b`, so each arm
    receives the equation as an argument and the whole elim is applied to `Refl`.
    This is the idiom M22's `AllLeRExtendFar` already uses; naming it here because
    it is the thing that makes the branch-free route work rather than merely move
    the problem. `ub_pick` is the shape every partition-invariant lemma will take. -/

def ub_pick : Term := prog{
  λ (X : Nat). λ (P : Nat). λ (L : List Nat). λ (H : Ub P L).
    elim (Leb X P) return (λ (B : Bool).
        Id Bool (Leb X P) B →
        Ub P (Take (boolRec (λ (Bb : Bool). Nat) (S Z) Z B)
                (InsertL (boolRec (λ (Bb : Bool). Nat) Z (S Z) B) X L))) {
      True => λ (E : Id Bool (Leb X P) True). Pair(LebTrueLe X P E, unit),
      False => λ (E : Id Bool (Leb X P) False). unit
    } Refl }
def ub_pick_ty : Term := prog{
  Π (X : Nat) → Π (P : Nat) → Π (L : List Nat) → Ub P L →
    Ub P (Take (boolRec (λ (Bb : Bool). Nat) (S Z) Z (Leb X P))
            (InsertL (boolRec (λ (Bb : Bool). Nat) Z (S Z) (Leb X P)) X L)) }
example : chk ub_pick ub_pick_ty = true := by native_decide

-- `Ub`/`Lb` compute, and are Σ-chained (so `sigmaRec` consumes them).
--
-- **The hand-written side's Σ binders are CAPITAL since M32 R3b**, and that is a
-- claim rather than a spelling: `Ub`/`Lb` chain PROOF components, §2.1 makes a
-- proof component's binder capital, and a capital Σ binder now carries `⇝` on its
-- domain — so a lowercase twin here would no longer be the same type. The
-- comparison is by `pv`, which prints the marker, so this is the assertion that
-- the library's own components declare themselves comptime.
example : (pv (prog{ Ub (S (S Z)) (Cons (S Z) (Cons (S (S Z)) Nil)) }) ==
           pv (prog{ Σ (H : Le (S Z) (S (S Z))). Σ (H2 : Le (S (S Z)) (S (S Z))). Unit })) = true := by native_decide
example : (pv (prog{ Lb Z (Cons (S Z) Nil) }) == pv (prog{ Σ (H : Le Z (S Z)). Unit })) = true := by native_decide

/-! ### The unshifted-motive question, settled: LATENT AND UNREACHABLE

    `hasType`'s `natRec`/`listRec` premises use the motive under the step's binders
    WITHOUT shifting it (`.pi "§h" a (.pi "§t" listA (.pi "§ih" (.app p (.pvar "§t"))
    …))`; it was `.pvar 0` and a missing shift when this note was written). Read as
    de Bruijn terms that was a wrong-answer typing rule for an OPEN motive — one
    mentioning an enclosing λ's variable — which is exactly the shape
    `SortedAppendPivot` needs (induction on `a`, motive mentioning `p` and `b`).
    So it looked like a live hazard for the rest of M23 and worth fixing first.

    It is not, and the reason is worth recording because it is not obvious from the
    premise construction: `hasType` INSTANTIATES every λ binder with a fresh σ as it
    descends (the `.lam`-against-`.pi` case). By the time a recursor spine is
    reached, every enclosing binder is a `sym`, so the motive it carries is
    variable-free — and a shift is the identity on a variable-free value. Open
    motives were a de Bruijn artifact of the elaborated term that the typing
    descent never presents. A `.pi` codomain is the only place a bound variable
    survives, and `hasType` returns `Type` there without checking inside.

    Verified rather than argued: these type-check, and they type-checked IDENTICALLY
    with the shifts inserted (I wrote the fix, measured no difference, and reverted
    it — three `shiftPure` calls on an unreachable case is complexity without
    payoff). M30 deleted the shifts along with every other index, so what these now
    pin is the descent discipline itself: if it ever changes, something fails here
    first. -/

def openMotiveL : Term := prog{
  λ (P : Nat). λ (L : List Nat).
    elim L return (λ (Lz : List Nat). Le P P) { Nil => LeRefl P, Cons (H) (T) Ih => Ih } }
def openMotiveL_ty : Term := prog{ Π (P : Nat) → Π (L : List Nat) → Le P P }
example : chk openMotiveL openMotiveL_ty = true := by native_decide

def openMotiveN : Term := prog{
  λ (P : Nat). λ (N : Nat).
    elim N return (λ (Nz : Nat). Le P P) { Z => LeRefl P, S (M) Ih => Ih } }
def openMotiveN_ty : Term := prog{ Π (P : Nat) → Π (N : Nat) → Le P P }
example : chk openMotiveN openMotiveN_ty = true := by native_decide

/-! ### A CHECKER GAP, filed for §9: a `let`-bound value is never type-checked

    `readR`'s `let` reflects its right-hand side and binds it; nothing checks it
    against anything, because nothing demands a type of it until it is CONSUMED.
    So an ill-typed dead proof is silently accepted:

        { let q = <any ill-typed proof term>; () }        -- ACCEPTED

    Path-sensitive laziness is a defensible design — an unconsumed value has no
    obligation — but it means "the body checks" does not imply "everything written in
    the body is well-typed", and that is a real hazard for anyone probing what the
    checker knows. It cost me a false negative result: my first probe of the
    branch-knowledge wall above was `{ let q = LebTrueLe a b Refl; () }`, which was
    ACCEPTED, and I nearly concluded the body DOES get branch equations. The honest
    probe (kept above) routes the proof into a consumer, and is rejected.

    The paired discipline, since `Migrate.progOkOf`/`chk` also collapse "machine error" and
    "typing false" into one `false`: confirm every negative control is an honest
    typing rejection, and confirm every positive one is live by flipping it and
    watching the build go red. Both were done for every test in this file. -/

-- Generic J-transport at `List Nat` — `LeRwR` for arbitrary list predicates. Every
-- certificate a back-less body returns is stated over an exit it knows only
-- PROPOSITIONALLY (from the callee's evidence), so transporting a proof along that
-- evidence is the universal last step; `LeRwR` already covers the `Le`-over-`Nat`
-- case and this is the unrestricted one.
example : chk Dllbc.StdLemmas.ListRw Dllbc.StdLemmas.ListRwTy = true := by native_decide

/-! ### The pivot glue — `Sorted (a ++ p :: b)` from the four partition facts

    A back-less partition hands its caller two WHOLE lists and a pivot, with the four
    facts `Sorted a`, `Ub p a`, `Sorted b`, `Lb p b`; `SortedAppendPivot` is what
    turns those into the sortedness half of quicksort's postcondition. The Σ-chained
    predicates are taken apart with `sigmaRec` (stage (i)) — five projections first,
    then the head-bound transport, then the induction. -/

example : chk SortedHead Dllbc.StdLemmas.SortedHeadTy = true := by native_decide
example : chk SortedTail Dllbc.StdLemmas.SortedTailTy = true := by native_decide
example : chk UbHead Dllbc.StdLemmas.UbHeadTy = true := by native_decide
example : chk UbTail Dllbc.StdLemmas.UbTailTy = true := by native_decide
example : chk LbBound Dllbc.StdLemmas.LbBoundTy = true := by native_decide
example : chk BoundAppend Dllbc.StdLemmas.BoundAppendTy = true := by native_decide
example : chk SortedAppendPivot Dllbc.StdLemmas.SortedAppendPivotTy = true := by native_decide

-- It COMPUTES, end to end: `[1] ++ 2 :: [3]` is sorted, from the four facts about
-- the parts. Every hypothesis at these values is a `⊤`-chain, so the witnesses are
-- `Pair(unit, unit)` — the content is entirely in the lemma.
def sap_app : Term := prog{
  SortedAppendPivot (S (S Z)) (Cons (S Z) Nil) (Cons (S (S (S Z))) Nil)
    Pair(unit, unit) Pair(unit, unit) Pair(unit, unit) Pair(unit, unit) }
def sap_app_ty : Term := prog{
  Sorted (Cons (S Z) (Cons (S (S Z)) (Cons (S (S (S Z))) Nil))) }
example : chk sap_app sap_app_ty = true := by native_decide

/-! Honesty controls. Each flips ONE hypothesis and watches the check fail — the
    two orientation flips (`Ub`/`Lb` swapped for their duals) and one arm lie. -/

-- (1) `Ub p a` weakened to `Lb p a`: `UbHead` now receives `Σ (Le p h). Lb p t`
-- where it wants `Σ (Le h p). Ub p t`. Without a's elements being BELOW the pivot
-- the splice is not sorted, and the check says so.
def sap_lie_ub_ty : Term := prog{
  Π (P : Nat) → Π (A : List Nat) → Π (B : List Nat) →
    Sorted A → Lb P A → Sorted B → Lb P B → Sorted (Append A (Cons P B)) }
example : chk SortedAppendPivot sap_lie_ub_ty = false := by native_decide

-- (2) `Lb p b` weakened to `Ub p b`: `LbBound` is fed the wrong direction, so the
-- pivot no longer bounds b's head.
def sap_lie_lb_ty : Term := prog{
  Π (P : Nat) → Π (A : List Nat) → Π (B : List Nat) →
    Sorted A → Ub P A → Sorted B → Ub P B → Sorted (Append A (Cons P B)) }
example : chk SortedAppendPivot sap_lie_lb_ty = false := by native_decide

-- (3) The `Nil` arm of the transport returning the wrong hypothesis: past the end of
-- `t` the new head is the PIVOT, so only `Le h p` inhabits the goal; handing back the
-- (vacuous) `Bound h Nil` does not.
def bound_append_lie : Term := prog{
  λ (H : Nat). λ (P : Nat). λ (T : List Nat). λ (B : List Nat).
    elim T return (λ (Tz : List Nat).
        Bound H Tz → Le H P → Bound H (Append Tz (Cons P B))) {
      Nil => λ (Hb : Unit). λ (Hp : Le H P). Hb,
      Cons (H2) (T2) Ih => λ (Hb : Le H H2). λ (Hp : Le H P). Hb } }
example : chk bound_append_lie Dllbc.StdLemmas.BoundAppendTy = false := by native_decide

-- (4) Liveness of the `Ub` hypothesis at concrete values: pivot 0 under a left part
-- containing 1 needs `Le 1 0 = ⊥`, which `Pair(unit, unit)` does not inhabit — so the
-- positive computation above passed on its hypotheses, not on a rubber stamp.
def sap_bad_pivot : Term := prog{
  SortedAppendPivot Z (Cons (S Z) Nil) Nil
    Pair(unit, unit) Pair(unit, unit) unit unit }
def sap_bad_pivot_ty : Term := prog{
  Sorted (Cons (S Z) (Cons Z Nil)) }
example : chk sap_bad_pivot sap_bad_pivot_ty = false := by native_decide

/-! ## Stage (vi) prelude: the bound-survival keystone, checked

    A partition-based quicksort needs `Ub p a` for the left part AFTER sorting, while
    the partition bounded it BEFORE — so a bound has to survive a permutation, and
    `Ub`/`Lb` (Σ-chains over the spine) are not natively permutation-invariant. M22
    named the route at the positional encoding: cross to the multiset, where the
    property is `Π x. x > p → Count x l = Z` and permutation-invariance is a
    one-line `IdTrans`. These are the whole-list instances. -/

example : chk Dllbc.StdLemmas.LbHead Dllbc.StdLemmas.LbHeadTy = true := by native_decide
example : chk Dllbc.StdLemmas.LbTail Dllbc.StdLemmas.LbTailTy = true := by native_decide
example : chk Dllbc.StdLemmas.NoAboveOfUb Dllbc.StdLemmas.NoAboveOfUbTy = true := by native_decide
example : chk Dllbc.StdLemmas.UbOfNoAbove Dllbc.StdLemmas.UbOfNoAboveTy = true := by native_decide
example : chk Dllbc.StdLemmas.UbPerm Dllbc.StdLemmas.UbPermTy = true := by native_decide
example : chk Dllbc.StdLemmas.NoBelowOfLb Dllbc.StdLemmas.NoBelowOfLbTy = true := by native_decide
example : chk Dllbc.StdLemmas.LbOfNoBelow Dllbc.StdLemmas.LbOfNoBelowTy = true := by native_decide
example : chk Dllbc.StdLemmas.LbPerm Dllbc.StdLemmas.LbPermTy = true := by native_decide


/-! # Stages (iv) and (vi): THE FLAGSHIP COHORT, as one program

    `partition`, `append_back` and `quicksort` are three sealed `let`s and a tail
    (§8), and they are written here as ONE chain because that is what they are: the
    caller reaches each callee by being written below it, and nothing is passed
    beside anything.

    ## Stage (iv) — the relational partition

    `partition(v, p)`: `*v` keeps the elements `≤ p`, the rest comes back BY VALUE.
    `split_off`'s silhouette, and the shape branch equations make writable — the body
    branches on `Leb x p` and has to PRODUCE `Le x p` from the branch it took, which
    is exactly what M23-iv measured as impossible and phase A closed.

    The ensures is four conjuncts, all in observation vocabulary:

        Σ (hi : List Nat).
      Σ (Hub : Ub p (*v))                       -- the kept part is ≤ p
      → Σ (Hlb : Lb p hi)                         -- the returned part is ≥ p
      → Π n. Id Nat (add (count n (*v)) (count n hi)) (count n (old *v))

    `Ub`/`Lb`/`Count`/`Add` say what a list IS. Nothing here mirrors the body's own
    algorithm — there is no `PartitionL` anywhere in this milestone, which is the
    stage's whole point: every invariant is proven INDUCTIVELY IN THE BODY from the
    recursive call's own ensures.

    The program is §4.1's take-and-rebuild, not Lomuto's array scan (the north star's
    naturalness rule): take the payload, match it OWNED, put the tail back, recurse
    through the parameter borrow, then push the head onto whichever side its
    comparison chose. In-place by this calculus's standards — the only list cell ever
    allocated is the one `Cons` a `Cons` becomes.

    ## Stage (vi) — quicksort

        fn quicksort [fuel] (fuel : Nat, v : &mut List Nat, Hfuel : Le (len *v) fuel)
          -> Σ (Hs : Sorted (*v)). Π n. Id Nat (count n (*v)) (count n (old *v))

    Sorted AND a permutation, over the exit snapshot, and not one `back` in the call
    tree: `partition`, `append_back` and the recursive calls are each described only
    by their return type. The `Sorted` here is the STRUCTURAL Σ-chain, not M22's
    positional `SortedR` — which is what sigmaRec (stage (i)) had to land for.

    THE PROGRAM. Take the payload; the head is the pivot; partition the tail through
    `v`; sort the kept part in place through `v` and the returned part through a
    borrow of the local; glue with `append_back`. The sufficiency hypothesis makes
    the out-of-fuel path ⊥-dischargeable — with the two `Le` conjuncts partition
    returns supplying exactly the two `LeTrans`es that feed the recursive calls
    their own sufficiency.

    THE ONE STRUCTURAL FACT the assembly needs beyond composition is BOUND SURVIVAL:
    `SortedAppendPivot` wants `Ub x` of the SORTED left part, and the partition
    bounded it before the sort. `UbPerm`/`LbPerm` (above) carry both bounds across
    their sorts' count evidence. That is M22's keystone in whole-list form, and it is
    the only place this proof is more than gluing.

    PAIN DIARY — staging is now the dominant cost, and this body is the measurement.
    Four builders (`mkCnt`, `mkUb`, `mkLb`, `fin`) exist for one reason: a proof must
    name values that later statements consume, and the body has no way to say "the
    value `rest` had" or "what `*v` held before that call". Each is applied in stages
    as its arguments become available. Every one of them would disappear under the
    filed `old`-for-consumed-things feature; none of them is doing mathematical work.

    ## ALL THREE ARE FUEL-THREADED, and that is decision 8's price, paid

    M23 wrote `partition` and `append_back` with `[v]` — decreasing through the
    borrow's payload — and `quicksort` with `[fuel]`. The `[v]` shape has no
    recursor form (see `borrowDecrease` in stage (v)), so §12 decision 8 blessed
    fuel-threading as the interim, and this is that source change: each of the two
    grows a `fuel : Nat` parameter and a `Le (Len *v) fuel` bound, each grows a dead
    `Z` branch discharged by `botElim`, and every caller supplies both.

    **The bound needs no lemma, and that is the interesting part.** At each recursive
    call the bound passes down UNCHANGED: `Le (Len (Cons x rest)) (S f2)` IS
    `Le (Len rest) f2` definitionally — the same bounds-cursor descent M14 found. And
    `Hf` is CAPITAL in both callees, which is §6's mode discipline paying for the
    migration: quicksort hands its `hfuel` to `partition` and still needs it twice
    more, and a lowercase proof parameter would have MOVED it (R16).

    `append_back`'s caller side is the one place fuel had to be INVENTED rather than
    forwarded: quicksort calls it AFTER sorting both halves, and a sort returns a
    count equation, not a length bound. What works is the fuel that is exactly
    enough — `Len *v` itself, with `LeRefl` as its bound — staged in a `let` first,
    because a comptime argument mentioning `*v` would demand-collapse the loan it
    was just lent. -/

/-! ### The cohort's telescope vocabulary

    Both fuel-threaded callees put the borrow SECOND (the fuel is `[k]` and `[k]`
    hoists to the front), so a return type written outside a header names it
    `.var ⟨1, "v"⟩`. -/

def vfT : Term := .var ⟨1, "v"⟩
def dvfT : Term := .deref vfT
def oldvfT : Term := .app (.const "old") dvfT
def pT : Term := .var ⟨2, "p"⟩
def fuelT : Term := .var ⟨0, "fuel"⟩

/-! ### The return types

    Written out per twin rather than through a skeleton, which is M28 ψ's rule: for
    a SPEC lie the type IS the readable content, and each of these is one line of a
    six-conjunct chain away from the honest form. Only the two telescope parameters
    a return type cannot name from outside its header are spliced. -/

def partHonest : Term := prog{
  Σ (hi : List Nat). Σ (Hub : Ub %pT (*%vfT)). Σ (Hlb : Lb %pT hi).
    Σ (Hl1 : Le (Len *%vfT) (Len (old *%vfT))). Σ0 (Hl2 : Le (Len hi) (Len (old *%vfT))).
    Π (N : Nat) → Id Nat (Add (Count N (*%vfT)) (Count N hi)) (Count N (old *%vfT)) }

def qsHonest : Term := prog{
  Σ0 (Hs : Sorted (*%vfT)). Π (N : Nat) → Id Nat (Count N (*%vfT)) (Count N (old *%vfT)) }

/-- The sufficiency hypothesis's type — a telescope entry, so it is a parameter of
    the chain too. Its twin is the one that weakens it to `Unit`. -/
def suffHonest : Term := prog{ Le (Len *%vfT) %fuelT }

/-! ### The chain, once

    Three parameters vary — `partition`'s return type, `quicksort`'s, and
    `quicksort`'s sufficiency hypothesis — which is every twin in this cohort except
    the two BODY twins, and those cannot be shared at all (M28 D1's rule: a
    difference inside a body, at a subterm naming a binder the `fn` lowering mints
    an id for, has no splice that can reach it). Both are transcribed below. -/

def qsUnder (pret qret suff tail : Term) : Term := prog{
  fn Partition [fuel] (fuel : Nat, v : &mut List Nat, p : Nat, Hf : Le (Len *v) fuel) -> %pret
      { let l = *v;
        match l {
          -- `Ub p Nil` and `Lb p Nil` are both `Unit`, and the Count goal is
          -- `Add Z Z = Z` — the empty Partition proves itself.
          Nil => { *v := Nil;
                   Pair(Nil, Pair(unit, Pair(unit, Pair(unit, Pair(unit, λ (N : Nat). Refl))))) },
          Cons(x, rest) => match fuel {
            -- Out of fuel with a non-empty list: `Hf : Le (S (Len rest)) Z` IS
            -- `Bot`, so the path is dead and the audit admits an ex-falso at any
            -- return type (§5.4). Guard + sufficiency hypothesis = TOTAL correctness.
            Z => botElim Unit Hf,
            S(f2) => {
            -- PAIN DIARY (staging, and the first where the unnameable thing is an
            -- ENTRY value, not an exit). Both Count steps must name `rest`, the tail
            -- as it was at entry; but `rest` is DATA and `*v := rest` moves it, so
            -- after the very next statement no term in the body denotes it. Dodged
            -- as ever by building the derivation while it is still live and applying
            -- it later. M23-iii stated the rule for exits ("a body can only talk
            -- about the CURRENT exit"); this instance says the same of any consumed
            -- parameter or binder, and it is a filing for `old` on consumed things.
            -- §2.4: `Rest0` and `X0` are the snapshots these two were taking
            -- implicitly. The paragraph above is about exactly this — "a body can
            -- only talk about the CURRENT exit… a filing for `old` on consumed
            -- things" — and the citation rule is what turns the filing into a
            -- binding: the value is frozen HERE, before the call consumes it, and
            -- the name says so.
            let Rest0 = rest;
            let X0 = x;
            let MkL = (λ (A : List Nat). λ (B : List Nat).
                        λ (H : Π (N : Nat) → Id Nat (Add (Count N A) (Count N B)) (Count N Rest0)).
                          λ (N : Nat). CountConsL N X0 A B Rest0 (H N));
            let MkR = (λ (A : List Nat). λ (B : List Nat).
                        λ (H : Π (N : Nat) → Id Nat (Add (Count N A) (Count N B)) (Count N Rest0)).
                          λ (N : Nat). CountConsR N X0 A B Rest0 (H N));
            -- The lengths need no staged lambda: `Len rest` is a NAT, so naming the
            -- computed value once, while `rest` is live, is enough. (The counts
            -- cannot do this — `Count n rest` is a family over `n`, and it is the
            -- LIST the lemma needs, not any one of its counts.)
            let lr = Len rest;
            *v := rest;
            -- The bound goes with the call, UNCHANGED: `Le (Len (Cons x rest)) (S f2)`
            -- already IS `Le (Len rest) f2`.
            let r = Partition(f2, &m *v, p, Hf);
            match r { Pair(hi, q1) => match q1 { Pair(Hub, q2) => match q2 { Pair(Hlb, q3) =>
            match q3 { Pair(Hl1, q4) => match q4 { Pair(Hl2, Hcnt) => {
              -- THE BRANCH EQUATION, in its first real use. `e` is the only reason
              -- either arm can build its bound: the split abstracted `Leb σ_x σ_p`
              -- away, so `LebTrueLe x p Refl` is rejected here (see the wall test)
              -- and `LebTrueLe x p e` is not.
              if e : Leb x p {
                -- x ≤ p: the head belongs to the KEPT part. Derive both proofs
                -- BEFORE the write, which consumes `lo` and `x` (§5.3's ordering
                -- corollary, in its body-local form).
                let lo = *v;
                let Hub2 = Pair(LebTrueLe x p e, Hub);
                let Hl2b = LeUpR (Len hi) lr Hl2;
                let Cnt = MkL lo hi Hcnt;
                *v := Cons(x, lo);
                Pair(hi, Pair(Hub2, Pair(Hlb, Pair(Hl1, Pair(Hl2b, Cnt)))))
              } else {
                -- x > p: the head belongs to the RETURNED part. `*v` is untouched,
                -- so `hub` passes straight through.
                let Hlb2 = Pair(LePredL p x (LebFalseGt x p e), Hlb);
                let Hl1b = LeUpR (Len *v) lr Hl1;
                let Cnt = MkR (*v) hi Hcnt;
                Pair(Cons(x, hi), Pair(Hub, Pair(Hlb2, Pair(Hl1b, Pair(Hl2, Cnt)))))
              }
            } } } } } }
          } }
        } };
  -- `AppendBack(v, w)`: walk to the end of `*v`, put `w` there. The exit reading is
  -- `Append (old *v) w` — the whole postcondition, and the whole description. Its
  -- return type is written INLINE, because nothing lies about it: no twin needs it
  -- spliced, and inside the header `v` and `w` are the names the programmer wrote.
  fn AppendBack [fuel] (fuel : Nat, v : &mut List Nat, w : List Nat, Hf : Le (Len *v) fuel)
      -> Id (List Nat) (*v) (Append (old *v) w)
      { match v {
          Nil => { *v := w; Refl },
          -- PAIN DIARY (staging, the M22 "proof linearity" entry's data twin). The
          -- congruence needs to NAME its right endpoint, `Append (old *tl) w`, but
          -- the recursive call has by then MOVED `w` (it is data, so §2.1 gives no
          -- copy-on-read). Dodged by staging the endpoint as a runtime `let` while
          -- `w` is still live. Same dodge, new cause: M22's was a proof consumed by
          -- a mutation, this is a data argument consumed by the call the proof is
          -- about. The general fix is the same one M22 queued — `old` for consumed
          -- parameters, so a body can name any parameter's ENTRY value without
          -- owning it, which is what M12 already grants the RETURN TYPE and denies
          -- the body.
          Cons(hd, tl) => match fuel {
            Z => botElim Unit Hf,
            S(f2) => {
              let y = Append (*tl) w;
              let h = AppendBack(f2, &m *tl, w, Hf);
              let H0 = *hd;
              IdCongr (List Nat) (List Nat) (λ (A : List Nat). Cons H0 A) (*tl) y h
            }
          }
      } };
  fn Quicksort [fuel] (fuel : Nat, v : &mut List Nat, Hfuel : %suff) -> %qret
      { let l = *v;
        match l {
          Nil => { *v := Nil; Pair(unit, λ (N : Nat). Refl) },
          Cons(x, rest) => match fuel {
            -- Out of fuel with a non-empty list: `hfuel : Le (S (Len rest)) Z` IS
            -- `Bot`, so the path is dead and the audit admits an ex-falso at any
            -- return type (§5.4). Guard + sufficiency hypothesis = TOTAL correctness.
            Z => botElim Unit Hfuel,
            S(f2) => {
              let lr = Len rest;
              -- THE COUNT CHAIN, staged whole while `rest` is still nameable. Its
              -- later arguments are the two parts before sorting (a, b) with the
              -- partition's own Count evidence, then the same two after sorting
              -- (a2, b2) with each sort's evidence, then the glued exit and
              -- `AppendBack`'s evidence. Read it as: rewrite the exit into an
              -- append, split the append's Count, move both parts back across
              -- their sorts, and land on the partition's equation.
              -- §2.4: the citation rule, and the snapshots it makes visible.
              -- `Rest0` is the tail as it is HERE — before `*v := rest` hands it
              -- over — which is the value this builder was freezing implicitly.
              let Rest0 = rest;
              let X0 = x;
              let MkCnt = (λ (A : List Nat). λ (B : List Nat).
                  λ (Hp : Π (N : Nat) → Id Nat (Add (Count N A) (Count N B)) (Count N Rest0)).
                  λ (A2 : List Nat). λ (B2 : List Nat).
                  λ (H1 : Π (N : Nat) → Id Nat (Count N A2) (Count N A)).
                  λ (H2 : Π (N : Nat) → Id Nat (Count N B2) (Count N B)).
                  λ (E : List Nat). λ (Hap : Id (List Nat) E (Append A2 (Cons X0 B2))).
                    λ (N : Nat).
                      IdTrans Nat (Count N E) (Add (Count N A2) (Count N (Cons X0 B2)))
                                   (Count N (Cons X0 Rest0))
                        (IdTrans Nat (Count N E) (Count N (Append A2 (Cons X0 B2)))
                                      (Add (Count N A2) (Count N (Cons X0 B2)))
                           (IdCongr (List Nat) Nat (λ (Z0 : List Nat). Count N Z0)
                              E (Append A2 (Cons X0 B2)) Hap)
                           (CountAppend N A2 (Cons X0 B2)))
                        (IdTrans Nat (Add (Count N A2) (Count N (Cons X0 B2)))
                                      (Add (Count N A) (Count N (Cons X0 B)))
                                      (Count N (Cons X0 Rest0))
                           (IdTrans Nat (Add (Count N A2) (Count N (Cons X0 B2)))
                                         (Add (Count N A) (Count N (Cons X0 B2)))
                                         (Add (Count N A) (Count N (Cons X0 B)))
                              (IdCongr Nat Nat (λ (R : Nat). Add R (Count N (Cons X0 B2)))
                                 (Count N A2) (Count N A) (H1 N))
                              (IdCongr Nat Nat (λ (R : Nat). Add (Count N A) R)
                                 (Count N (Cons X0 B2)) (Count N (Cons X0 B))
                                 (CountConsCongr N X0 B2 B (H2 N))))
                           (CountConsR N X0 A B Rest0 (Hp N))));
              *v := rest;
              -- Decision 8's price at a CALL SITE: the fuel and the bound go with
              -- the call, and the bound is `hfuel` UNCHANGED — after `*v := rest`
              -- the callee wants `Le (Len rest) f2`, which is what it already is.
              -- It SURVIVES the call because `Partition`'s `Hf` is capital.
              let pr = Partition(f2, &m *v, x, Hfuel);
              match pr { Pair(hi, q1) => match q1 { Pair(Hub, q2) => match q2 { Pair(Hlb, q3) =>
              match q3 { Pair(Hl1, q4) => match q4 { Pair(Hl2, Hpc) => {
                -- Both bounds are about to be invalidated as VALUES (the sorts
                -- replace both lists), so their transports are staged now, while the
                -- pre-sort lists are still nameable.
                -- §2.4: the PRE-sort snapshots, named. `V0` and `Hi0` are the two
                -- parts as they are HERE, before either sort replaces them, and that
                -- is exactly what these builders were freezing implicitly. The
                -- comment above already said "while the pre-sort lists are still
                -- nameable"; the rule turns that sentence into two bindings.
                let V0 = *v;
                let Hi0 = hi;
                let Hub0 = Hub;
                let Hlb0 = Hlb;
                let MkUb = (λ (A2 : List Nat).
                    λ (H1 : Π (N : Nat) → Id Nat (Count N A2) (Count N V0)).
                      UbPerm X0 A2 V0 H1 Hub0);
                let MkLb = (λ (B2 : List Nat).
                    λ (H2 : Π (N : Nat) → Id Nat (Count N B2) (Count N Hi0)).
                      LbPerm X0 B2 Hi0 H2 Hlb0);
                let Cnt1 = MkCnt (*v) hi Hpc;
                -- Sort the kept part in place. Its sufficiency is the partition's
                -- length conjunct composed with this frame's.
                let Hf1 = LeTrans (Len *v) lr f2 Hl1 Hfuel;
                let s1 = Quicksort(f2, &m *v, Hf1);
                match s1 { Pair(Hs1, Hc1) => {
                  -- …and the returned part, through a borrow of the local that
                  -- holds it. Nothing about it is in `*v`; it is an ordinary value.
                  let Hf2 = LeTrans (Len hi) lr f2 Hl2 Hfuel;
                  let s2 = Quicksort(f2, &m hi, Hf2);
                  match s2 { Pair(Hs2, Hc2) => {
                    let hub2 = MkUb (*v) Hc1;
                    let hlb2 = MkLb hi Hc2;
                    let Cnt2 = Cnt1 (*v) hi Hc1 Hc2;
                    -- The last staged builder: the glue's evidence arrives only
                    -- from `AppendBack`, by which time both parts are consumed.
                    -- §2.4: and the POST-sort snapshots, which are DIFFERENT values
                    -- from `V0`/`Hi0` above — both sorts wrote in place. The rule
                    -- makes that difference visible instead of leaving the reader to
                    -- date each capture by where it sits.
                    -- M33a: the two SORTEDNESS snapshots that stood here
                    -- (`let Hs1 = hs1`) are gone. They existed only because a
                    -- match arm bound a comptime component at a lowercase name,
                    -- and a runtime binding is not capturable — so `Fin` could
                    -- not cite the proof and a capital `let` had to re-read it.
                    -- With the arm binder spelling its mode, `Fin` cites it.
                    let V1 = *v;
                    let Hi1 = hi;
                    let Hub2 = hub2;
                    let Hlb2 = hlb2;
                    let Fin = (λ (E : List Nat).
                        λ (Hap : Id (List Nat) E (Append V1 (Cons X0 Hi1))).
                          ListRw (λ (Z0 : List Nat). Sorted Z0) (Append V1 (Cons X0 Hi1)) E
                            (IdSym (List Nat) E (Append V1 (Cons X0 Hi1)) Hap)
                            (SortedAppendPivot X0 V1 Hi1 Hs1 Hub2 Hs2 Hlb2));
                    let w = Cons(x, hi);
                    -- The fuel that is exactly enough, staged BEFORE the borrow is
                    -- taken: a comptime argument mentioning `*v` would demand-
                    -- collapse the loan it was just lent.
                    let lv = Len *v;
                    let happ = AppendBack(lv, &m *v, w, LeRefl lv);
                    Pair(Fin (*v) happ, Cnt2 (*v) happ)
                  } }
                } }
              } } } } } }
            }
          }
        } };
  %tail }

/-- THE HEADLINE: M23's in-place quicksort — `Sorted` and the permutation count
    equation over the exit snapshot, no declared `back` anywhere in the call tree —
    checks as ONE program, against no table at all. -/
def flagship : Term := qsUnder partHonest qsHonest suffHonest .unit
example : progOk flagship = true := by native_decide

/-! ### Not vacuous: `partition`'s four spec lies

    The return type is the ONLY description of this function, so each conjunct gets
    a twin that changes exactly it. The body and the telescope are the chain's, so
    the lie is the only variable. -/

-- (1) UPPER BOUND on the wrong snapshot: `Ub p (old *v)` — true of the entry, and
-- the entry is not what the caller gets back.
example : progRejects (qsUnder (prog{
    Σ (hi : List Nat). Σ (Hub : Ub %pT (old *%vfT)). Σ (Hlb : Lb %pT hi).
      Σ (Hl1 : Le (Len *%vfT) (Len (old *%vfT))). Σ0 (Hl2 : Le (Len hi) (Len (old *%vfT))).
      Π (N : Nat) → Id Nat (Add (Count N (*%vfT)) (Count N hi)) (Count N (old *%vfT)) })
    qsHonest suffHonest .unit) "does not have return type" = true := by native_decide

-- (2) LOWER BOUND on the kept part instead of the returned one.
example : progRejects (qsUnder (prog{
    Σ (hi : List Nat). Σ (Hub : Ub %pT (*%vfT)). Σ (Hlb : Lb %pT (*%vfT)).
      Σ (Hl1 : Le (Len *%vfT) (Len (old *%vfT))). Σ0 (Hl2 : Le (Len hi) (Len (old *%vfT))).
      Π (N : Nat) → Id Nat (Add (Count N (*%vfT)) (Count N hi)) (Count N (old *%vfT)) })
    qsHonest suffHonest .unit) "does not have return type" = true := by native_decide

-- (3) The returned part DROPPED from the count: "everything stayed in `*v`".
--
-- **The needle MOVED at M33, and the verdict did not** — the same flip M33a
-- recorded for `quicksortA`'s two spec lies, arriving here for the same reason
-- one layer down. With `Cnt` capital (§2.5's binding, capitalised now that the
-- Σ0 tail ⇝-reads it), the count proof is comptime knowledge and the lie is
-- caught where it is WRITTEN — at this body's own return, by the audit — instead
-- of one call later, where the caller found the argument ill-typed. Was "does not
-- have its parameter type".
example : progRejects (qsUnder (prog{
    Σ (hi : List Nat). Σ (Hub : Ub %pT (*%vfT)). Σ (Hlb : Lb %pT hi).
      Σ (Hl1 : Le (Len *%vfT) (Len (old *%vfT))). Σ0 (Hl2 : Le (Len hi) (Len (old *%vfT))).
      Π (N : Nat) → Id Nat (Count N (*%vfT)) (Count N (old *%vfT)) })
    qsHonest suffHonest .unit) "does not have return type" = true := by native_decide

-- (4) …and the count off by one, which no `Nil`-path argument can reach.
example : progRejects (qsUnder (prog{
    Σ (hi : List Nat). Σ (Hub : Ub %pT (*%vfT)). Σ (Hlb : Lb %pT hi).
      Σ (Hl1 : Le (Len *%vfT) (Len (old *%vfT))). Σ0 (Hl2 : Le (Len hi) (Len (old *%vfT))).
      Π (N : Nat) → Id Nat (Add (Count N (*%vfT)) (Count N hi)) (S (Count N (old *%vfT))) })
    qsHonest suffHonest .unit) "does not have return type" = true := by native_decide

/-! ### Not vacuous: `quicksort`'s two spec lies, and the sufficiency hypothesis

    Every twin here is chosen to survive the `Nil` path and die on the RECURSIVE one
    — the first drafts of (1) and (2) were refuted at `Nil` (verified by reading the
    rejected result term: `Pair unit (λn. Refl)`), which would have left the whole
    assembly untested. -/

-- (1) SORTEDNESS lied onto the wrong subject: the ENTRY is claimed sorted. True at
-- `Nil` (so the base path still passes) and false for any unsorted input, and the
-- body's evidence is about the exit.
example : progRejects (qsUnder partHonest (prog{
    Σ0 (Hs : Sorted (old *%vfT)). Π (N : Nat) → Id Nat (Count N (*%vfT)) (Count N (old *%vfT)) })
    suffHonest .unit) "does not have return type" = true := by native_decide

-- (2) PERMUTATION lied by DIRECTION: the two endpoints swapped. Again `Refl` at
-- `Nil`, and again the body's evidence points the other way once anything moves.
example : progRejects (qsUnder partHonest (prog{
    Σ0 (Hs : Sorted (*%vfT)). Π (N : Nat) → Id Nat (Count N (old *%vfT)) (Count N (*%vfT)) })
    suffHonest .unit) "does not have its parameter type" = true := by native_decide

-- (3) The SUFFICIENCY HYPOTHESIS is load-bearing, not decoration. Keep the
-- parameter (so the body still elaborates and the rejection is about TYPING, not an
-- unbound name) and weaken it to `Unit`: the `Z` branch's `botElim` then has no ⊥
-- to eliminate, and the out-of-fuel path stops being dead. This is what makes the
-- guard-plus-hypothesis pair TOTAL correctness rather than partial.
-- The needle is the MECHANISM, not the generic one: with the hypothesis weakened,
-- the out-of-fuel branch's `botElim` has nothing to eliminate, and the audit says
-- exactly that. The record-update twin this replaces could only assert `!progOk`.
example : progRejects (qsUnder partHonest qsHonest (prog{ Unit }) .unit)
  "botElim result on a non-⊥ argument" = true := by native_decide

/-! ### The two BODY twins, transcribed

    A spec lie is refutable somewhere the `Nil` path can be blamed for; these two are
    wrong only on the RECURSIVE path, which is what makes them the twins that test
    the recursion. Both are written out in full rather than shared through the chain,
    and that is M28 D1's rule rather than a choice: what varies is a subterm INSIDE a
    body naming a binder the `fn` lowering mints an id for, and a `%` splice is a
    Lean `Term` written outside the macro — it has no way to say "the `hub` this
    match will bind". Each carries only what it needs: the count lie needs no
    quicksort at all, and the bound lie needs the whole cohort. -/

/-- `partitionLoses`: the `≤ p` head is DROPPED instead of being pushed back onto the
    kept part — one write changed, `*v := lo` for `*v := Cons(x, lo)`. Wrong only on
    the recursive `True` path and only in the count conjunct; the bounds still hold
    of a list with one element missing. -/
def partitionLoses : Term := prog{
  fn Partition [fuel] (fuel : Nat, v : &mut List Nat, p : Nat, Hf : Le (Len *v) fuel) -> %partHonest
      { let l = *v;
        match l {
          Nil => { *v := Nil;
                   Pair(Nil, Pair(unit, Pair(unit, Pair(unit, Pair(unit, λ (N : Nat). Refl))))) },
          Cons(x, rest) => match fuel {
            Z => botElim Unit Hf,
            S(f2) => {
            -- §2.4: `Rest0` and `X0` are the snapshots these two were taking
            -- implicitly. The paragraph above is about exactly this — "a body can
            -- only talk about the CURRENT exit… a filing for `old` on consumed
            -- things" — and the citation rule is what turns the filing into a
            -- binding: the value is frozen HERE, before the call consumes it, and
            -- the name says so.
            let Rest0 = rest;
            let X0 = x;
            let MkL = (λ (A : List Nat). λ (B : List Nat).
                        λ (H : Π (N : Nat) → Id Nat (Add (Count N A) (Count N B)) (Count N Rest0)).
                          λ (N : Nat). CountConsL N X0 A B Rest0 (H N));
            let MkR = (λ (A : List Nat). λ (B : List Nat).
                        λ (H : Π (N : Nat) → Id Nat (Add (Count N A) (Count N B)) (Count N Rest0)).
                          λ (N : Nat). CountConsR N X0 A B Rest0 (H N));
            let lr = Len rest;
            *v := rest;
            let r = Partition(f2, &m *v, p, Hf);
            match r { Pair(hi, q1) => match q1 { Pair(Hub, q2) => match q2 { Pair(Hlb, q3) =>
            match q3 { Pair(Hl1, q4) => match q4 { Pair(Hl2, Hcnt) => {
              if e : Leb x p {
                let lo = *v;
                let Hub2 = Pair(LebTrueLe x p e, Hub);
                let Hl2b = LeUpR (Len hi) lr Hl2;
                let Cnt = MkL lo hi Hcnt;
                -- THE LIE, and the only line that differs: the head is dropped.
                *v := lo;
                Pair(hi, Pair(Hub2, Pair(Hlb, Pair(Hl1, Pair(Hl2b, Cnt)))))
              } else {
                let Hlb2 = Pair(LePredL p x (LebFalseGt x p e), Hlb);
                let Hl1b = LeUpR (Len *v) lr Hl1;
                let Cnt = MkR (*v) hi Hcnt;
                Pair(Cons(x, hi), Pair(Hub, Pair(Hlb2, Pair(Hl1b, Pair(Hl2, Cnt)))))
              }
            } } } } } }
          } }
        } };
  () }
example : progRejects partitionLoses "does not have return type" = true := by native_decide

/-- `qsStaleBound`: the KEYSTONE is fed the bounds the PARTITION established, on the
    parts as they were BEFORE their recursive sorts, instead of `UbPerm`/`LbPerm`'s
    transports of them — `SortedAppendPivot x (*v) hi Hs1 Hub Hs2 Hlb` for
    `… Hub2 … Hlb2`. Everything else is the chain's `quicksort` verbatim, so what the
    rejection isolates is exactly bound survival. -/
def qsStaleBound : Term := prog{
  fn Partition [fuel] (fuel : Nat, v : &mut List Nat, p : Nat, Hf : Le (Len *v) fuel) -> %partHonest
      { let l = *v;
        match l {
          Nil => { *v := Nil;
                   Pair(Nil, Pair(unit, Pair(unit, Pair(unit, Pair(unit, λ (N : Nat). Refl))))) },
          Cons(x, rest) => match fuel {
            Z => botElim Unit Hf,
            S(f2) => {
            -- §2.4: `Rest0` and `X0` are the snapshots these two were taking
            -- implicitly. The paragraph above is about exactly this — "a body can
            -- only talk about the CURRENT exit… a filing for `old` on consumed
            -- things" — and the citation rule is what turns the filing into a
            -- binding: the value is frozen HERE, before the call consumes it, and
            -- the name says so.
            let Rest0 = rest;
            let X0 = x;
            let MkL = (λ (A : List Nat). λ (B : List Nat).
                        λ (H : Π (N : Nat) → Id Nat (Add (Count N A) (Count N B)) (Count N Rest0)).
                          λ (N : Nat). CountConsL N X0 A B Rest0 (H N));
            let MkR = (λ (A : List Nat). λ (B : List Nat).
                        λ (H : Π (N : Nat) → Id Nat (Add (Count N A) (Count N B)) (Count N Rest0)).
                          λ (N : Nat). CountConsR N X0 A B Rest0 (H N));
            let lr = Len rest;
            *v := rest;
            let r = Partition(f2, &m *v, p, Hf);
            match r { Pair(hi, q1) => match q1 { Pair(Hub, q2) => match q2 { Pair(Hlb, q3) =>
            match q3 { Pair(Hl1, q4) => match q4 { Pair(Hl2, Hcnt) => {
              if e : Leb x p {
                let lo = *v;
                let Hub2 = Pair(LebTrueLe x p e, Hub);
                let Hl2b = LeUpR (Len hi) lr Hl2;
                let Cnt = MkL lo hi Hcnt;
                *v := Cons(x, lo);
                Pair(hi, Pair(Hub2, Pair(Hlb, Pair(Hl1, Pair(Hl2b, Cnt)))))
              } else {
                let Hlb2 = Pair(LePredL p x (LebFalseGt x p e), Hlb);
                let Hl1b = LeUpR (Len *v) lr Hl1;
                let Cnt = MkR (*v) hi Hcnt;
                Pair(Cons(x, hi), Pair(Hub, Pair(Hlb2, Pair(Hl1b, Pair(Hl2, Cnt)))))
              }
            } } } } } }
          } }
        } };
  fn AppendBack [fuel] (fuel : Nat, v : &mut List Nat, w : List Nat, Hf : Le (Len *v) fuel)
      -> Id (List Nat) (*v) (Append (old *v) w)
      { match v {
          Nil => { *v := w; Refl },
          Cons(hd, tl) => match fuel {
            Z => botElim Unit Hf,
            S(f2) => {
              let y = Append (*tl) w;
              let h = AppendBack(f2, &m *tl, w, Hf);
              let H0 = *hd;
              IdCongr (List Nat) (List Nat) (λ (A : List Nat). Cons H0 A) (*tl) y h
            }
          }
      } };
  fn Quicksort [fuel] (fuel : Nat, v : &mut List Nat, Hfuel : %suffHonest) -> %qsHonest
      { let l = *v;
        match l {
          Nil => { *v := Nil; Pair(unit, λ (N : Nat). Refl) },
          Cons(x, rest) => match fuel {
            Z => botElim Unit Hfuel,
            S(f2) => {
              let lr = Len rest;
              -- §2.4: the citation rule, and the snapshots it makes visible.
              -- `Rest0` is the tail as it is HERE — before `*v := rest` hands it
              -- over — which is the value this builder was freezing implicitly.
              let Rest0 = rest;
              let X0 = x;
              let MkCnt = (λ (A : List Nat). λ (B : List Nat).
                  λ (Hp : Π (N : Nat) → Id Nat (Add (Count N A) (Count N B)) (Count N Rest0)).
                  λ (A2 : List Nat). λ (B2 : List Nat).
                  λ (H1 : Π (N : Nat) → Id Nat (Count N A2) (Count N A)).
                  λ (H2 : Π (N : Nat) → Id Nat (Count N B2) (Count N B)).
                  λ (E : List Nat). λ (Hap : Id (List Nat) E (Append A2 (Cons X0 B2))).
                    λ (N : Nat).
                      IdTrans Nat (Count N E) (Add (Count N A2) (Count N (Cons X0 B2)))
                                   (Count N (Cons X0 Rest0))
                        (IdTrans Nat (Count N E) (Count N (Append A2 (Cons X0 B2)))
                                      (Add (Count N A2) (Count N (Cons X0 B2)))
                           (IdCongr (List Nat) Nat (λ (Z0 : List Nat). Count N Z0)
                              E (Append A2 (Cons X0 B2)) Hap)
                           (CountAppend N A2 (Cons X0 B2)))
                        (IdTrans Nat (Add (Count N A2) (Count N (Cons X0 B2)))
                                      (Add (Count N A) (Count N (Cons X0 B)))
                                      (Count N (Cons X0 Rest0))
                           (IdTrans Nat (Add (Count N A2) (Count N (Cons X0 B2)))
                                         (Add (Count N A) (Count N (Cons X0 B2)))
                                         (Add (Count N A) (Count N (Cons X0 B)))
                              (IdCongr Nat Nat (λ (R : Nat). Add R (Count N (Cons X0 B2)))
                                 (Count N A2) (Count N A) (H1 N))
                              (IdCongr Nat Nat (λ (R : Nat). Add (Count N A) R)
                                 (Count N (Cons X0 B2)) (Count N (Cons X0 B))
                                 (CountConsCongr N X0 B2 B (H2 N))))
                           (CountConsR N X0 A B Rest0 (Hp N))));
              *v := rest;
              let pr = Partition(f2, &m *v, x, Hfuel);
              match pr { Pair(hi, q1) => match q1 { Pair(Hub, q2) => match q2 { Pair(Hlb, q3) =>
              match q3 { Pair(Hl1, q4) => match q4 { Pair(Hl2, Hpc) => {
                -- §2.4: the PRE-sort snapshots, named. `V0` and `Hi0` are the two
                -- parts as they are HERE, before either sort replaces them, and that
                -- is exactly what these builders were freezing implicitly. The
                -- comment above already said "while the pre-sort lists are still
                -- nameable"; the rule turns that sentence into two bindings.
                let V0 = *v;
                let Hi0 = hi;
                let Hub0 = Hub;
                let Hlb0 = Hlb;
                let MkUb = (λ (A2 : List Nat).
                    λ (H1 : Π (N : Nat) → Id Nat (Count N A2) (Count N V0)).
                      UbPerm X0 A2 V0 H1 Hub0);
                let MkLb = (λ (B2 : List Nat).
                    λ (H2 : Π (N : Nat) → Id Nat (Count N B2) (Count N Hi0)).
                      LbPerm X0 B2 Hi0 H2 Hlb0);
                let Cnt1 = MkCnt (*v) hi Hpc;
                let Hf1 = LeTrans (Len *v) lr f2 Hl1 Hfuel;
                let s1 = Quicksort(f2, &m *v, Hf1);
                match s1 { Pair(Hs1, Hc1) => {
                  let Hf2 = LeTrans (Len hi) lr f2 Hl2 Hfuel;
                  let s2 = Quicksort(f2, &m hi, Hf2);
                  match s2 { Pair(Hs2, Hc2) => {
                    let hub2 = MkUb (*v) Hc1;
                    let hlb2 = MkLb hi Hc2;
                    let Cnt2 = Cnt1 (*v) hi Hc1 Hc2;
                    -- §2.4: and the POST-sort snapshots, which are DIFFERENT values
                    -- from `V0`/`Hi0` above — both sorts wrote in place. The rule
                    -- makes that difference visible instead of leaving the reader to
                    -- date each capture by where it sits.
                    -- M33a: the two SORTEDNESS snapshots that stood here
                    -- (`let Hs1 = hs1`) are gone. They existed only because a
                    -- match arm bound a comptime component at a lowercase name,
                    -- and a runtime binding is not capturable — so `Fin` could
                    -- not cite the proof and a capital `let` had to re-read it.
                    -- With the arm binder spelling its mode, `Fin` cites it.
                    let V1 = *v;
                    let Hi1 = hi;
                    let Fin = (λ (E : List Nat).
                        λ (Hap : Id (List Nat) E (Append V1 (Cons X0 Hi1))).
                          ListRw (λ (Z0 : List Nat). Sorted Z0) (Append V1 (Cons X0 Hi1)) E
                            (IdSym (List Nat) E (Append V1 (Cons X0 Hi1)) Hap)
                            -- THE LIE, and the only line that differs: the PRE-sort
                            -- bounds (`Hub0`/`Hlb0`), not their transports across the
                            -- sorts (`Hub2`/`Hlb2`). §2.4 sharpens the lie rather than
                            -- hiding it: the two snapshots now have different names.
                            (SortedAppendPivot X0 V1 Hi1 Hs1 Hub0 Hs2 Hlb0));
                    let w = Cons(x, hi);
                    let lv = Len *v;
                    let happ = AppendBack(lv, &m *v, w, LeRefl lv);
                    Pair(Fin (*v) happ, Cnt2 (*v) happ)
                  } }
                } }
              } } } } } }
            }
          }
        } };
  () }
example : progRejects qsStaleBound "does not have return type" = true := by native_decide

/-! ### The executing differentials — the bodies really partition, and really sort

    `progOk` proves the conjuncts symbolically; these run the SAME program on
    concrete inputs. Each rides the honest chain as its tail, so what runs is what
    was checked. `runPart` also exercises phase A's concrete-scrutinee branch end to
    end: `if e : Leb x p` on a closed Bool takes the `ownedSelect` path, where the
    equation is bound to `Refl`. -/

def partCallerTail (l : List Nat) (pvv : Nat) : Term :=
  .letIn ⟨0, "z"⟩ (tlistT l)
    (.letIn ⟨1, "b"⟩ (.borrow (.var ⟨0, "z"⟩))
      (.letIn ⟨2, "r"⟩ (.call "Partition"
          [tnatT l.length, .var ⟨1, "b"⟩, tnatT pvv, .unit])
        (.matchE ⟨2, "r"⟩ none
          [.mk "Pair" [⟨3, "hi"⟩, ⟨4, "q"⟩] (.letIn ⟨5, "y"⟩ (.var ⟨0, "z"⟩) .unit)])))
def runPart (l : List Nat) (pvv : Nat) : Bool :=
  match Dllbc.Tests.S9Diff.runExec (qsUnder partHonest qsHonest suffHonest (partCallerTail l pvv)) with
  | .ok env =>
    env.lookup "y" == some (vlistV (l.filter (fun a => decide (a <= pvv)))) &&
    env.lookup "hi" == some (vlistV (l.filter (fun a => decide (pvv < a))))
  | .error _ => false

example : runPart [3,1,4,1,5] 3 = true := by native_decide   -- both parts non-empty
example : runPart [1,2,3] 5 = true := by native_decide       -- everything stays
example : runPart [7,8,9] 2 = true := by native_decide       -- everything leaves
example : runPart [] 3 = true := by native_decide            -- the Nil path, executing
example : runPart [2,2,2] 2 = true := by native_decide       -- the boundary: x = p stays

/-- The caller the sort's differentials share: own a list, lend it, sort, read it
    back. `Hfuel : Le (Len l) (Len l)` is supplied as `()` — the bound holds by
    COMPUTATION here, which is the ordinary route for a concrete payload. -/
def qsCallerTail (l : List Nat) : Term :=
  .letIn ⟨0, "z"⟩ (tlistT l)
    (.letIn ⟨1, "b"⟩ (.borrow (.var ⟨0, "z"⟩))
      (.seq (.call "Quicksort" [tnatT l.length, .var ⟨1, "b"⟩, .unit])
        (.letIn ⟨2, "y"⟩ (.var ⟨0, "z"⟩) .unit)))
def qsRun (l : List Nat) : Term := qsUnder partHonest qsHonest suffHonest (qsCallerTail l)
def runQs (l : List Nat) : Bool :=
  match Dllbc.Tests.S9Diff.runExec (qsRun l) with
  | .ok env => env.lookup "y" == some (vlistV (l.mergeSort (fun a b => a <= b)))
  | .error _ => false

example : runQs [] = true := by native_decide
example : runQs [1] = true := by native_decide
example : runQs [2,1] = true := by native_decide
example : runQs [3,1,2] = true := by native_decide
example : runQs [1,2,3] = true := by native_decide       -- already sorted: one part always empty
example : runQs [5,5,5] = true := by native_decide       -- all equal
example : runQs [4,1,3,2,5] = true := by native_decide

end Dllbc.Tests.S23Direct
end
-- └── end of what was `S23Direct.lean` ───────────────────────────────────────────────

-- ┌── was `Dllbc/Tests/S19Partition.lean` ──────────────────────────────────────────────
section
/-!
# §19 test suite — partition (model + imperative), built on the M18 stack

This milestone assembles the crystallized architecture into its first real
algorithm: an in-place Lomuto partition through a mutable borrow, whose declared
backward spec is the pure `PartitionL` model, checked by conversion per path.

It opens with the smallest complete instance of the architecture — a `swapS`
caller that recovers the precise `SwapL i j s` (M17) and certifies its count with
`CountSwapL'` (M18) — and gates the imperative body on a machine probe: splitting
the driver on a STUCK Bool spine (`Leb x pivot`, x symbolic), which the current
substitution-based ⇜ cannot do without generalizing the spine first.
-/

open Dllbc
open Dllbc.StdLemmas (SwapL CountSwapL' Set NthL PartScanL PartScanRangeL PartIdxL
  PartIdxRangeL PartGapRangeL PartScanSizeL LenPartitionRangeL LenSortRangeL SortRangeL
  PartitionRangeL PartitionL LeUpR LeAdd LeAddL LeAddSucc LeRwR LeRwL LeAddMonoL
  AddSucc LeTrans LeRefl IdSym IdTrans IdCongr HshiftTrue HshiftFalse LenSwapL AddZero AddAssoc
  CountPartitionRangeL CountSortRangeL SortedR SortedSortRangeL)

namespace Dllbc.Tests.S19Partition

def V (i : Nat) (n : String) : Term := .var ⟨i, n⟩
def natT : Term := .const "Nat"

/-- Type-check a closed term against a closed type in the pure seed (as in §18). -/
def chk (tm ty : Term) : Bool :=
  match (do let v ← readC 3000 tm; let t ← readC 3000 ty; hasTypeT 3000 v t).run (seedPure [] []) with
  | .ok r _ => r
  | .error _ _ => false

/-! ## M19-A: the `CountSwapL'` corollary and its `LeUpR` glue -/

example : chk StdLemmas.LeUpR StdLemmas.LeUpRTy = true := by native_decide
example : chk StdLemmas.CountSwapL' StdLemmas.CountSwapL'Ty = true := by native_decide

-- M20-2 length-equation plumbing: the bound-derivation glue.
example : chk StdLemmas.LeAdd StdLemmas.LeAddTy = true := by native_decide
example : chk StdLemmas.LeAddL StdLemmas.LeAddLTy = true := by native_decide
example : chk StdLemmas.LeAddSucc StdLemmas.LeAddSuccTy = true := by native_decide
example : chk StdLemmas.LeRwR StdLemmas.LeRwRTy = true := by native_decide
example : chk StdLemmas.HshiftTrue StdLemmas.HshiftTrueTy = true := by native_decide
example : chk StdLemmas.HshiftFalse StdLemmas.HshiftFalseTy = true := by native_decide

/-! ### The two telescopes' positional vocabulary

    A return type written outside its own header names parameters as `.var ⟨i, name⟩`
    (§5.2). These are the two that vary. -/

-- SUBJECT: raw Term builders (tS/swapLT) feeding the lying specs below.
def tS (t : Term) : Term := .ctorApp "S" [t]
def swapLT (i j l : Term) : Term := .app (.app (.app StdLemmas.SwapL i) j) l

def sT : Term := .var ⟨0, "s"⟩
def mT : Term := .var ⟨1, "m"⟩
def ciT : Term := .var ⟨2, "i"⟩
def cjT : Term := .var ⟨3, "j"⟩
def evT : Term := .var ⟨0, "v"⟩
def eiT : Term := .var ⟨1, "i"⟩
def ejT : Term := .var ⟨2, "j"⟩

/-! ## THE CHAIN — the cursor family and everything in this file that swaps

    `NthL`, `nth2` and `swapS` are §17's cursor family, and they came here when
    `S17Spec` retired (M28 D7): that file's other half was `through`, whose two
    claims moved to `S7Group`, and this is the only place left that CALLS a cursor.
    They are written once, at the head of one chain, with every subject that needs
    them declared below them — because a callee is in scope by being written above
    its caller (§8). (A `%`-spliced second chain could not declare functions until
    M32 R4 retired the `progBase` collision; it can now, and this shape is kept
    because it is what was written.)

    Two return types are PARAMETERS, because two subjects have lying twins:
    `certSwapCount`'s (the count-preservation certificate) and `exitReject`'s (the
    exit-vs-entry reading). Everything else is written once. A lie is caught at its
    own function's seal — sealed `let`s fire their audits in program order — so the
    rejections below are attributable even though the chain is shared.

    ### `NthL`, `nth2`, `swapS`

    §17 carried these with COMPOSING backward specs — `Set i r s`, then
    `Set i r₁ (Set j r₂ s)` composing it, then `SwapL i j s` composing that. The
    mechanism is gone (M27); what they check now is that the cursor bodies are
    well-typed — the `Le`-bounded descent, the field reborrows, the `botElim` on the
    impossible `Nil` path. The composing-spec claim's ensures-style successor is
    `S23Direct.swapAt`, which states the whole swap as ONE equation over the exit
    snapshot instead of as three specs that compose.

    ### `certSwapCount` — M19-A's opener, the architecture's smallest instance

    A `swapS` caller over a SYMBOLIC list: it borrows `s`, swaps positions `i`/`j`
    in place (imperative mutation), and its result is the count-preservation
    CERTIFICATE `CountSwapL' m i j s pij p2`, computed over the entry snapshot.
    Imperative mutation + pure lemma, end to end.

    ### `pivotPlace` / `pivotPlaceH` — M20-2's conformance base

    The base of partition's recursion, isolated: place the pivot at the boundary `i`
    with a final swap. Cased on `i` because swapS cannot self-swap. `pivotPlace`
    takes its bound directly; `pivotPlaceH` DERIVES it from the length equation the
    recursion carries (`hlen : Len *v = S (Add i g)`), which validates the full
    length-equation → swapS-bound chain the recursive partScan threads.

    ### `partScanE` / `partitionE` — the executing partition

    The full recursive scan and its entry point. The three step cases each derive
    their swapS bound (let-FIRST, per the §5.3 finding) and recurse.

    ### `exitReject` — M22-a, the exit snapshot is not the entry

    A borrow parameter's bare `*v` in the RETURN TYPE reads the EXIT snapshot (the
    collapsed final payload, which the audit already computes); `old *v` names the
    ENTRY one, usable in the type AND the body as a non-consuming reference. After a
    swap they are different, so claiming the exit equals the entry is FALSE.

    The positive half is `Id (*v) (*v)`: both reads see the SAME exit snapshot,
    which is what makes the negative half about the entry rather than about `*v`
    being freshly minted on each occurrence. What it is NOT is
    `Id (*v) (SwapL i j (old *v))` — that is TRUE of this function and `Refl` cannot
    prove it, because `swapS` ensures nothing and the group end hands back an opaque
    σ. Saying it needs the derivation `S23Direct.swapAt` carries, which is where
    §C2's ledger already points.

    ### `lebProbe` — the reborrow-collapse repro

    After an in-place `swapS(&mut *b,…)` the swapped elements sit in the callee's
    element-borrows; this reborrows `&mut *b` and reads `Leb (NthL Z (*v)) pivot` —
    the comptime-deref-through-a-reborrow that read a stale `loanₘ` before the fix.
-/

def certHonest : Term := prog{ Id Nat (Count %mT (SwapL %ciT %cjT %sT)) (Count %mT %sT) }
def certLie : Term := prog{ Id Nat (Count %mT (SwapL %ciT %cjT %sT)) (S (Count %mT %sT)) }
def exitHonest : Term := prog{ Id (List Nat) (*%evT) (*%evT) }
def exitStale : Term := prog{ Id (List Nat) (*%evT) (old *%evT) }

def withCursors (cret eret tail : Term) : Term := prog{
  fn Nth [i] (v : &mut List Nat, i : Nat, p : Le (S i) (Len *v)) -> &mut Nat
        { match v {
            Nil => botElim Unit p,
            Cons(hd, tl) => match i {
              Z => &m *hd,
              S(k) => Nth(&m *tl, k, p)
            }
        } };
  fn Nth2 [i] (v : &mut List Nat, i : Nat, j : Nat,
                 pij : Le (S i) j, p2 : Le (S j) (Len *v)) -> Σ (x : &mut Nat). &mut Nat
        { match v {
            Nil => botElim Unit p2,
            Cons(hd, tl) => match i {
              Z => match j {
                Z => botElim Unit pij,
                S(jjv) => Pair(&m *hd, Nth(&m *tl, jjv, p2))
              },
              S(k) => match j {
                Z => botElim Unit pij,
                S(jj2) => Nth2(&m *tl, k, jj2, pij, p2)
              }
            }
        } };
  fn SwapS (v : &mut List Nat, i : Nat, j : Nat,
                  pij : Le (S i) j, p2 : Le (S j) (Len *v)) -> Unit
        { let pr = Nth2(v, i, j, pij, p2);
          match pr { Pair(ei, ej) => {
            let t = *ei;
            *ei := *ej;
            *ej := t;
            () } } };
  -- s=0, m=1, i=2, j=3, pij=4, p2=5.
  fn CertSwapCount (s : List Nat, m : Nat, i : Nat, j : Nat,
        pij : Le (S i) j, p2 : Le (S j) (Len s)) -> %cret
        { let cert = CountSwapL' m i j s pij p2;
          let b = &m s;
          SwapS(b, i, j, pij, p2);
          cert };
  -- v=0, i=1, pib=2.
  fn PivotPlace (v : &mut List Nat, i : Nat, pib : Le (S i) (Len *v)) -> Unit
        { match i {
            Z => (),
            S(i2) => { SwapS(v, Z, S(i2), (), pib); () }
        } };
  -- v=0, i=1, g=2, hlen=3.
  fn PivotPlaceH (v : &mut List Nat, i : Nat, g : Nat,
        hlen : Id Nat (Len *v) (S (Add i g))) -> Unit
        { match i {
            Z => (),
            -- Derive the bound in a `let` FIRST, while `v` is still live (the `Len *v`
            -- read is comptime/non-consuming); THEN call SwapS (which consumes `v`).
            S(i2) => {
              let p2 = LeRwR (S (S i2)) (S (S (Add i2 g))) (Len *v)
                         (IdSym Nat (Len *v) (S (S (Add i2 g))) hlen)
                         (LeAdd i2 g);
              SwapS(v, Z, S(i2), (), p2);
              ()
            }
        } };
  -- v=0, i=1, j=2, pij=3, p2=4.
  fn ExitReject (v : &mut List Nat, i : Nat, j : Nat, pij : Le (S i) j, p2 : Le (S j) (Len *v))
        -> %eret
        { SwapS(&m *v, i, j, pij, p2); Refl };
  -- v=0, pivot=1.
  fn LebProbe (v : &mut List Nat, pivot : Nat) -> Unit
        { let c = Leb (NthL Z (*v)) pivot;
          match c { True => (), False => () } };
  %tail }

/-- The honest chain: nine functions, one program, no table. -/
def chain : Term := withCursors certHonest exitHonest .unit
example : progOk chain = true := by native_decide

-- Negative control for the opener: claim the count GREW by one across the swap. The
-- certificate proves equality, so the value-returning audit rejects the lying return
-- type — the opener's acceptance is a real check of a real certificate.
example : progRejects (withCursors certLie exitHonest .unit)
  "does not have return type" = true := by native_decide

-- Negative control for M22-a: claim the EXIT reading equals the ENTRY one.
example : progRejects (withCursors certHonest exitStale .unit)
  "does not have return type" = true := by native_decide

/-! ### The executing scan — a second chain, and the reason it is second

    `partScanE`/`partitionE` are the in-place Lomuto partition, mirroring
    `PartitionL` exactly: `partScanE` recurses on the scan counter `k`, reads the
    scan element with the PURE `NthL` on `*v` (a comptime read, the `Leb` condition),
    and branches — the `g = S g'` case swaps in place then recurses, the base places
    the pivot with a final swap (guarded on `i = S i'`, since swapS cannot
    self-swap).

    **Their swapS bounds are placeholders `()`, so they do not type-check**, and
    that is why they cannot ride the chain above: the point of that chain is
    `progOk`. They are RUN, in executing mode, which does not type-check arguments —
    the claim is conformance with the pure model on concrete inputs, which is what
    the checking mode later proved on `S23Direct.partition` with real bounds.

    So the cursor family is written a second time here. That is the honest cost of
    one chain per verdict class, and it is the smaller cost: the alternative is a
    chain the corpus cannot assert `progOk` on, which would make every accepting
    subject in it unasserted. -/

def withScan (tail : Term) : Term := prog{
  fn Nth [i] (v : &mut List Nat, i : Nat, p : Le (S i) (Len *v)) -> &mut Nat
        { match v {
            Nil => botElim Unit p,
            Cons(hd, tl) => match i {
              Z => &m *hd,
              S(k) => Nth(&m *tl, k, p)
            }
        } };
  fn Nth2 [i] (v : &mut List Nat, i : Nat, j : Nat,
                 pij : Le (S i) j, p2 : Le (S j) (Len *v)) -> Σ (x : &mut Nat). &mut Nat
        { match v {
            Nil => botElim Unit p2,
            Cons(hd, tl) => match i {
              Z => match j {
                Z => botElim Unit pij,
                S(jjv) => Pair(&m *hd, Nth(&m *tl, jjv, p2))
              },
              S(k) => match j {
                Z => botElim Unit pij,
                S(jj2) => Nth2(&m *tl, k, jj2, pij, p2)
              }
            }
        } };
  fn SwapS (v : &mut List Nat, i : Nat, j : Nat,
                  pij : Le (S i) j, p2 : Le (S j) (Len *v)) -> Unit
        { let pr = Nth2(v, i, j, pij, p2);
          match pr { Pair(ei, ej) => {
            let t = *ei;
            *ei := *ej;
            *ej := t;
            () } } };
  -- v=0, k=1, i=2, g=3, pivot=4.
  fn PartScanE [k] (v : &mut List Nat, k : Nat, i : Nat, g : Nat, pivot : Nat) -> Unit
        { match k {
            Z => match i {
              Z => (),
              S(i2) => { SwapS(v, Z, S(i2), (), ()); () }
            },
            S(k2) => {
              let c = Leb (NthL (S (Add i g)) (*v)) pivot;
              match c {
                True => match g {
                  Z => PartScanE(v, k2, S(i), Z, pivot),
                  -- `i` and `g2` are read MULTIPLE times here (boundary + scan position
                  -- + the recursion), and §2.1 copy-on-read makes that natural: a
                  -- `S`-constructor arg reads its var by copy (marker-free Nat), so the
                  -- indices are the plain `S i`, `S (Add i (S g2))`, `S g2`.
                  S(g2) => { SwapS(&m *v, S(i), S(Add i (S(g2))), (), ()); PartScanE(v, k2, S(i), S(g2), pivot) }
                },
                False => PartScanE(v, k2, i, S(g), pivot)
              }
            }
        } };
  -- v=0, n=1.
  fn PartitionE (v : &mut List Nat, n : Nat) -> Unit
        { match n {
            Z => (),
            S(n2) => { let pivot = NthL Z (*v); PartScanE(v, n2, Z, Z, pivot) }
        } };
  %tail }

/-! ## M20-2 (the recursive partScan) — partition's scan loop, checked against PartScanL

    The full recursive scan, declared `back = PartScanL pivot k i g (*v)`. Telescope
    carries the length equation `hlen : Len *v = S (Add k (Add i g))` (k-first, so the
    step reduces definitionally). Body mirrors the M19 executing partition; the three
    step cases each derive their swapS bound (let-FIRST, per the §5.3 finding) and
    recurse with an UPDATED hlen (an hshift arithmetic transport — definitional total,
    plus a LenSwapL bridge in the swap case). resolveTree composes the recursive
    call's back-spec with swapS's, exactly as pivotPlace proved for one swap. -/

-- SUBJECT: raw Term builders. `partScanLT`/`dv` (and `tS`/`zt`/`Refl`/`tlist` below)
-- construct the lying-spec inputs and the executing-differential expected values — the
-- raw Term IS the test subject here, not a surface form under test.
def partScanLT (pivot k i g l : Term) : Term := .app (.app (.app (.app (.app StdLemmas.PartScanL pivot) k) i) g) l
def dv : Term := .deref (V 0 "v")

-- v=0, k=1, i=2, g=3, pivot=4, hlen=5; binders k'=6, c/i'=7, g'/hlenX=8, pij=9, p2=10, hlenTSg=11.
/-! ## M21-3 — partScanRange: the subrange scan (partScan shifted by `lo`)

    `partScanRange(v, lo, k, i, g, pivot, hle)` — partScan over the range `[lo, …)`.
    Every position is `Add lo`-shifted; the boundary `i` and gap `g` are RELATIVE
    to `lo`. The bound is now an INEQUALITY `hle : Le (add lo (S (add k (add i g))))
    (len *v)` — a sub-range does not span to the end, so the old equation is false;
    the Le is the honest invariant (the top scan/swap position stays < len). The
    M20 Id-toolkit ports through the new `LeRwL`/`LeAddMonoL`/`AddSucc`
    bridges: swap bounds are `LeTrans` of a `LeAddMonoL` lifted from the entry
    bound, and each recursion threads `hle` via `LeRwL` + `IdCongr` through
    `λx. Add lo (S x)` over the SAME hshift identities partScan uses. -/


/-! ## M21-1 — the partition wrapper (back = PartitionL, the PartScanL composition)

    partition fixes the public interface: pivot placement + the scan, over a
    segment of length `n` (`hlenW : Len *v = n`). Declared `back = PartitionL n
    (*v)` — authored (in StdLemmas) as exactly `n = Z ⇒ *v`, `n = S n' ⇒ PartScanL
    (nth 0 *v) n' 0 0 *v`, the raw composition of partScan's declared back. The
    scan call's hlen is hlenW transported by AddZero (the wrapper's `i = g = 0`,
    so partScan's `S (Add n' (Add 0 0))` is `S (Add n' Z)`, bridged to `S n'`). -/


-- v=0, n=1, hlenW=2; body binders n'=3, pivot=4, hlen=5.
def partitionLieBack : Term := swapLT (.ctorApp "Z" []) (tS (.ctorApp "Z" [])) dv
def partScanLieBack : Term := partScanLT (V 4 "pivot") (V 1 "k") (V 3 "g") (V 2 "i") dv
/-! ## The lying-back sweep — one lie per CALLEE-CHECKED declared-spec branch

    A negative test per rule branch, not per feature (the M20 lesson). The §6.2
    callee convert-check catches a lie only where the declared back is authored as
    the raw suspension TREE (so tree ≡ back definitionally). Two such branches
    beyond the ones already covered:
    - borrow-returning multi-issued  → nth2Lie   (below)
    - borrow-returning single-issued → throughLie (S17Spec — the M8 arc)
    - Unit-returning recursive        → partScanLie (above; caught where an
      untouched argument-borrow path exposes the swapped spec)

    NOT callee-checked, by design: a back that is a higher-level REFORMULATION of
    the raw tree — swapS's `SwapL i j *v` vs its set-based nth2 composition, and
    pivotPlace's SwapL-based `baseBack` — never converts and is validated by the
    DIFFERENTIAL (executing recovery = checking recovery), as M17 established. The
    M20 auditAction extension checks in-place backs authored AS the tree (partScan);
    reformulated backs remain the differential's job. -/

def setL (k v l : Term) : Term := .app (.app (.app StdLemmas.Set k) v) l

-- Borrow-returning multi-issued: nth2 with i and j swapped in the two sets.
-- SUBJECT: a deliberately-wrong back-spec (raw Term, i/j swapped in the two sets) — the lie is the subject.
-- `nth2Lie` — a LYING backward spec (the two indices swapped), asserting that the
-- §6.2 callee check catches it. Retired with the mechanism in M27-P2: a test of a
-- deleted feature is not coverage. It is also the one back this corpus carried as
-- a RECORD UPDATE rather than as surface syntax, which is why the `back = …` sweep
-- did not reach it — M26-F's `with`-closure lesson, arriving from the other side.

/-! ## M19-B (the gate) — splitting the driver on a STUCK Bool spine

    The imperative partition branches on `if Leb x pivot` with `x` symbolic; the
    scrutinee reduces to a stuck spine `Leb σ σp`, NOT a bare σ, and the ⇜ split
    (M3) needs a substitutable variable. The machine now GENERALIZES: on an owned
    stuck spine, `generalizeStuck` NF's it and `abstractInto`s it to a fresh
    `σb : Bool` across all σ-bearing state (the M10 invariant's targets), then the
    ordinary owned-sym split refines σb → True/False per branch.

    The probe: a fn whose RETURN TYPE mentions the same `Leb n 2` spine, with two
    `boolRec` sides that converge ONLY per branch (`Add Z x ≡ x`). Without the
    split the two stuck `boolRec`s differ and neither `Refl` checks; with it, both
    paths reduce and check. Both the spine-in-the-value (the scrutinee) and the
    spine-in-the-type (the pinned return) must refine together — which is exactly
    what generalizing across ALL σ-bearing state delivers. -/

-- SUBJECT: raw Term/Val builders (zt/tnat/lebSp/boolRecNat/Refl) for the stuckProbe
-- lying variants and the pure-model checks — raw Terms are the point here.
def zt : Term := .ctorApp "Z" []
def tnat : Nat → Term | 0 => zt | k + 1 => tS (tnat k)
def lebSp (n : Term) : Term := .app (.app Std.lebFnT n) (tnat 2)
def boolRecNat (t f sp : Term) : Term :=
  .app (.app (.app (.app (.const "boolRec") (.lam "_" (.const "Bool") natT)) t) f) sp
def Refl : Term := .ctorApp "Refl" []

-- n = 0; the `if` binds a fresh scrutinee (id 1).
-- **Written out per twin rather than shared through a skeleton** (M28 ψ). The
-- retSkel form pays when a body is long enough that duplicating it hurts; this body
-- is two lines, so writing each twin in full keeps the honest return type in SURFACE
-- syntax — which for a convergence probe is the whole readable content — at the cost
-- of one repeated `let`. Sharing would have bought nothing and made the honest spec
-- a hand-built `Term`.
def stuckProbe : Term := prog{
  fn StuckProbe (n : Nat) -> Id Nat
        (boolRec (λ (B : Bool). Nat) (S Z) Z (Leb n (S (S Z))))
        (boolRec (λ (B : Bool). Nat) (Add Z (S Z)) (Add Z Z) (Leb n (S (S Z))))
        { let c = Leb n (S (S Z));
          match c { True => Refl, False => Refl } };
  () }
example : progOk stuckProbe = true := by native_decide

-- Not vacuous (a): the True side does NOT converge (`S Z` vs `S (S Z)`). The
-- generalized σb refines to True in that path and the `boolRec` reduces to two
-- distinct values, so `Refl` fails — proving the per-branch refinement is real.
-- SUBJECT: a deliberately-non-converging return type (raw Term) — the lie is the subject.
def stuckProbeLieRet : Term := .idT natT
  (boolRecNat (tS zt) zt (lebSp (V 0 "n"))) (boolRecNat (tS (tS zt)) zt (lebSp (V 0 "n")))
def stuckProbeLie : Term := prog{
  fn StuckProbeLie (n : Nat) -> %stuckProbeLieRet
        { let c = Leb n (S (S Z));
          match c { True => Refl, False => Refl } };
  () }
example : progRejects stuckProbeLie "does not have return type" = true := by native_decide

-- Not vacuous (b): a one-armed match is rejected as non-exhaustive — the
-- generalized σb is genuinely Bool-typed, so exhaustiveness demands True AND False.
-- SUBJECT: a deliberately non-exhaustive body (raw Term, one-armed match) — the defect is the subject.
def stuckProbeNonExhBody : Term := .letIn ⟨1, "c"⟩ (lebSp (V 0 "n")) (.matchE ⟨1, "c"⟩ none [.mk "True" [] Refl])
def stuckProbeNonExh : Term := prog{
  fn StuckProbeNonExh (n : Nat) -> Id Nat
        (boolRec (λ (B : Bool). Nat) (S Z) Z (Leb n (S (S Z))))
        (boolRec (λ (B : Bool). Nat) (Add Z (S Z)) (Add Z Z) (Leb n (S (S Z))))
        { %stuckProbeNonExhBody };
  () }
example : progRejects stuckProbeNonExh "non-exhaustive" = true := by native_decide

/-! ## M19-C (model) — `PartitionL` computes the Lomuto partition

    Concrete validation of the pure model before wiring the imperative body to it:
    first-element pivot, `≤`-elements moved before it, `>`-elements after, pivot
    landing at the boundary. Covers an already-partitioned input (pivot smallest,
    no swaps), a reverse-sorted input (all `≤`, boundary walks to the end), and a
    mixed input that exercises the `g = S g'` swap branch. -/

-- SUBJECT: raw Val/Term builders (pv/vnat/vlist/tlist) — construct the pure-model expected
-- values and the executing-mode inputs; the raw Val/Term IS the subject under test here.
def pv (t : Term) : Term := Pure.nf 4000 t
def vnat : Nat → Val | 0 => .ctor "Z" [] | k + 1 => .ctor "S" [vnat k]
def vlist : List Nat → Val | [] => .ctor "Nil" [] | x :: xs => .ctor "Cons" [vnat x, vlist xs]
def tlist : List Nat → Term | [] => .ctorApp "Nil" [] | x :: xs => .ctorApp "Cons" [tnat x, tlist xs]
def partLT (n : Nat) (l : List Nat) : Term := .app (.app StdLemmas.PartitionL (tnat n)) (tlist l)

example : (Val.know (pv (partLT 3 [3,1,2])) == vlist [2,1,3]) = true := by native_decide
example : (Val.know (pv (partLT 3 [1,2,3])) == vlist [1,2,3]) = true := by native_decide          -- already partitioned
example : (Val.know (pv (partLT 3 [3,2,1])) == vlist [1,2,3]) = true := by native_decide          -- reverse sorted
example : (Val.know (pv (partLT 5 [3,5,1,2,4])) == vlist [2,1,3,5,4]) = true := by native_decide   -- exercises the swap

/-! ## M21-2 — PartIdxL (the boundary index) and SortL (the quicksort model) -/

def idxLT (n : Nat) (l : List Nat) : Term := .app (.app StdLemmas.PartIdxL (tnat n)) (tlist l)
def sortLT (fuel n : Nat) (l : List Nat) : Term := .app (.app (.app StdLemmas.SortL (tnat fuel)) (tnat n)) (tlist l)

-- PartIdxL = the pivot's final position (matches where the partition run lands it):
example : (Val.know (pv (idxLT 3 [3,1,2])) == vnat 2) = true := by native_decide    -- pivot 3 → index 2
example : (Val.know (pv (idxLT 3 [1,2,3])) == vnat 0) = true := by native_decide     -- pivot 1 stays at 0
example : (Val.know (pv (idxLT 3 [3,2,1])) == vnat 2) = true := by native_decide
example : (Val.know (pv (idxLT 5 [3,5,1,2,4])) == vnat 2) = true := by native_decide -- [2,1,3,5,4], pivot at 2

-- SortL sorts (fuel = length). Small cases only — sortL's toValPure inlines the
-- whole partition/scan stack, so pv/nfV on it is heavy; the executing quicksort
-- (M21-3) validates it on the larger input classes far more cheaply.
example : (Val.know (pv (sortLT 2 2 [2,1])) == vlist [1,2]) = true := by native_decide          -- the smallest sort
example : (Val.know (pv (sortLT 1 1 [7])) == vlist [7]) = true := by native_decide              -- singleton
example : (Val.know (pv (sortLT 0 0 [])) == vlist []) = true := by native_decide                -- empty

/-! ## M21-3 — SortRangeL (the index-bounded quicksort spec, plan of record) -/

def sortRangeLT (fuel lo Cnt : Nat) (l : List Nat) : Term :=
  .app (.app (.app (.app StdLemmas.SortRangeL (tnat fuel)) (tnat lo)) (tnat Cnt)) (tlist l)

-- Full-range (lo=0, Cnt=len): SortRangeL 0 (len l) l is a full sort — the top-
-- level shape the imperative quicksort's back carries.
example : (Val.know (pv (sortRangeLT 2 0 2 [2,1])) == vlist [1,2]) = true := by native_decide
example : (Val.know (pv (sortRangeLT 1 0 1 [7])) == vlist [7]) = true := by native_decide
example : (Val.know (pv (sortRangeLT 0 0 0 [])) == vlist []) = true := by native_decide
example : (Val.know (pv (sortRangeLT 3 0 3 [3,2,1])) == vlist [1,2,3]) = true := by native_decide   -- recursion fires
-- Sub-range (lo>0): sort only [lo, lo+Cnt), leaving the rest untouched — the new
-- capability the recursion rides. [5,3,2,9] sorting [3,2] at offset 1 → [5,2,3,9].
example : (Val.know (pv (sortRangeLT 2 1 2 [5,3,2,9])) == vlist [5,2,3,9]) = true := by native_decide
example : (Val.know (pv (sortRangeLT 3 1 3 [9,3,1,2,7])) == vlist [9,1,2,3,7]) = true := by native_decide

/-! ## M19-C (imperative, executing mode) — the body computes `PartitionL`

    The in-place Lomuto partition through a mutable borrow, mirroring `PartitionL`
    exactly. `partScanE` recurses on the scan counter `k`; each step reads the scan
    element with the PURE `NthL` on `*v` (a comptime read, the `Leb` condition), and
    branches: the `g = S g'` case does an in-place `swapS` then recurses; the base
    places the pivot with a final `swapS` (guarded on `i = S i'` — swapS cannot
    self-swap). Run in executing mode (bounds proofs are placeholders `()`, which
    the run does not type-check) to confirm the imperative algorithm agrees with the
    pure model on concrete inputs — the conformance the checking mode will prove. -/

-- The subjects are the chain's `partScanE`/`partitionE` (M28 D7); what follows is
-- the caller that runs them, spliced in as its tail.

-- Executing-mode caller: create a concrete list, borrow, partition in place, recover.
def partCaller (lst : List Nat) (n : Nat) : Term :=
  .letIn ⟨0, "x"⟩ (tlist lst)
    (.letIn ⟨1, "b"⟩ (.borrow (.var ⟨0, "x"⟩))
      (.seq (.call "PartitionE" [.var ⟨1, "b"⟩, tnat n])
        (.letIn ⟨2, "y"⟩ (.var ⟨0, "x"⟩) .unit)))

def runPart (lst : List Nat) (n : Nat) : Bool :=
  match Dllbc.Tests.S9Diff.runExec (withScan (partCaller lst n)) with
  | .ok env => env.lookup "y" == some (Val.know (pv (partLT n lst)))
  | .error _ => false

-- The executing-mode partition agrees with the pure model on every input class:
-- already-partitioned (no swaps), reverse-sorted (all ≤, boundary walks to the
-- end), and mixed inputs that exercise the interior `g = S g'` swap (the reborrow
-- `&mut *v` path). Getting here surfaced and fixed three machine gaps (see the M19
-- report): shiftVars now shifts runtime vars inside pure spines; readR's var-move
-- ends a suspended reborrow in a borrow's payload; and a reused comptime index is
-- authored as a pure `Add` spine so readR delegates to (non-consuming) readC.
example : runPart [3,1,2] 3 = true := by native_decide
example : runPart [1,2,3] 3 = true := by native_decide          -- already partitioned (no swaps)
example : runPart [3,2,1] 3 = true := by native_decide          -- reverse sorted
example : runPart [3,5,1,2,4] 5 = true := by native_decide      -- interior g=S g' swap
example : runPart [5,3,8,1,9,2] 6 = true := by native_decide    -- mixed, multiple interior swaps
example : runPart [2,2,1,3,2] 5 = true := by native_decide      -- duplicates around the pivot

/-! ## M20-3 differential — the CHECKING partScan FnDef, run EXECUTING, = PartScanL

    The load-bearing conformance validator (the callee convert-check reaches the
    back only where it's authored as the tree; the swapS leaf's reformulated back
    is the differential's job). We run the SAME partScan FnDef that Migrate.progOkOf
    accepts — bounds, hlen proofs and all — in EXECUTING mode on concrete lists,
    and confirm its recovered list equals `PartScanL pivot k 0 0 l`. So the body's
    actual effect matches the declared back on every input class: since Migrate.progOkOf
    accepts `back = PartScanL`, executing = PartScanL = the recovered value. -/

-- SUBJECT: the executing-mode differential harness (raw Term caller + raw expected-value
-- needle). Generating the caller Term and the `PartScanL`-computed needle IS the test here.
/-! ## M21-3 — partitionRange: the subrange partition wrapper (Σ-pinned relative index)

    partitions the range [lo, lo+Cnt) in place and returns the pivot's RELATIVE
    offset `i` (absolute = add lo i), Σ-pinned to `PartIdxRangeL lo Cnt *v`. The
    precondition is the range-fits inequality `hbnd : Le (Add lo Cnt) (Len *v)`;
    the partScanRange call's entry bound (i = g = 0) is hbnd bridged by AddZero
    (`Add Cnt2 Z = Cnt2`), mirroring partition's (M21-1) hlenW-via-AddZero. -/


/-! ## M21-3 — quicksort: the imperative in-place quicksort (back = SortRangeL)

    THE NORTH STAR. `quicksort(v, fuel, lo, Cnt, hbnd)` sorts the `Cnt` elements at
    offset `lo` in place. Fuel-structural (mirrors SortRangeL): out of fuel / Cnt ≤
    1 is a no-op; otherwise pick the pivot, compute the pivot's relative index `i`
    and the right-count `g` from the ENTRY list (before mutating), scan-partition
    the range (partScanRange, whose back IS PartitionRangeL lo Cnt *v), then recurse
    on [lo, lo+i) and [lo+i+1, …) — sequential reborrows of the one `*v`. Because
    `i`/`g` are the pure `PartIdxRangeL`/`PartGapRangeL` of the entry list, the
    body's suspension tree (partScanRange's back, then the two quicksort backs
    composed) is DEFINITIONALLY sortRangeL's own unfold — conformance is conversion.

    The two range bounds come from PartScanSizeL (i + g + 1 = Cnt) and the three
    length-preservation lemmas (the partition and each recursive sort keep len *v,
    so the bounds, stated over the live *v, transport back to len entry = hbnd). -/

/-! ## M22-0 — the conformance baseline's validation suite (quicksort)

    Closing the back-specced (simulation) baseline before the direct-proving
    redirect: the lie is rejected, and the SAME checking-mode FnDef run executing on
    every input class (plus a sub-range) recovers exactly `SortRangeL fuel lo Cnt l`
    — so the body's effect is the pure model on concrete data, the conformance the
    §6.2 callee check proves symbolically. -/

-- Not vacuous: identity is the right back only on the no-op paths (fuel Z / Cnt ≤ 1);
-- on the sort path the composed suspension tree is SortRangeL, not *v, so it rejects.
-- SUBJECT: a deliberately-wrong back-spec (raw Term, identity) — the lie is the subject.
def quicksortLieBack : Term := dv
def partScanRangeLT (pivot lo k i g l : Term) : Term :=
  .app (.app (.app (.app (.app (.app StdLemmas.PartScanRangeL pivot) lo) k) i) g) l
-- SUBJECT: the executing-mode differential harness (raw Term caller).
def psrCaller (lst : List Nat) (lo k pivot : Nat) : Term :=
  .letIn ⟨0, "x"⟩ (tlist lst)
    (.letIn ⟨1, "b"⟩ (.borrow (.var ⟨0, "x"⟩))
      (.seq (.call "partScanRangeE" [.var ⟨1, "b"⟩, tnat lo, tnat k, tnat 0, tnat 0, tnat pivot])
        (.letIn ⟨2, "y"⟩ (.var ⟨0, "x"⟩) .unit)))
/-! ## M22 execfix — the executing-mode reborrow-staleness regression + the payoff

    The isolated repro of the pain diary above (`swapS(&mut *b,…)` then a comptime
    deref through a FRESH reborrow), the sequential-swapS positive control (the
    sub-call-read path that always worked, guarding it stays green), and the
    now-unblocked FULL quicksort executing differential. -/

-- The minimal reproducer: after an in-place `swapS(&mut *b,…)` the swapped elements
-- sit in the callee's element-borrows; a probe fn reborrows `&mut *b` and reads
-- `Leb (NthL Z (*v)) pivot` — the exact comptime-deref-through-a-reborrow that read a
-- stale `loanₘ` (stuck) before the fix. `match c` forces the Bool. Post-fix the
-- reborrow fully re-collapses *v, so `NthL Z (*v)` = 1, `Leb 1 5` = True, and the
-- owner `x` recovers the swapped [1,2,3].
-- (`lebProbe` is the chain's, M28 D7; what follows is the caller that runs it.)

-- SUBJECT: raw Term caller for the isolated repro (x=[3,2,1]; b=&mut x; swapS through
-- *b; lebProbe reborrows *b and comptime-reads it; recover y).
def swapLebCaller (lst : List Nat) : Term :=
  .letIn ⟨0,"x"⟩ (tlist lst)
    (.letIn ⟨1,"b"⟩ (.borrow (.var ⟨0,"x"⟩))
      (.seq (.call "SwapS" [.borrow (.deref (.var ⟨1,"b"⟩)), tnat 0, tnat 2, .unit, .unit])
        (.seq (.call "LebProbe" [.borrow (.deref (.var ⟨1,"b"⟩)), tnat 5])
          (.letIn ⟨2,"y"⟩ (.var ⟨0,"x"⟩) .unit))))
def runSwapLebProbe (lst : List Nat) (expect : List Nat) : Bool :=
  match Dllbc.Tests.S9Diff.runExec (withCursors certHonest exitHonest (swapLebCaller lst)) with
  | .ok env => env.lookup "y" == some (vlist expect)
  | .error _ => false
-- Before the fix this errored (leb scrutinee stuck on `loanₘ`); now the reborrow
-- probe reads the collapsed list and the owner recovers the swap.
example : runSwapLebProbe [3,2,1] [1,2,3] = true := by native_decide

-- Positive control: two sequential `swapS(&mut *b,…)` of the same positions compose
-- to the identity ([3,2,1] again). This path always worked (swapS reads *v via its
-- OWN nth2 sub-call, a var-read that already cascades) — it guards that the fix does
-- not disturb the sequential-reborrow path.
def swapTwiceCaller (lst : List Nat) : Term :=
  .letIn ⟨0,"x"⟩ (tlist lst)
    (.letIn ⟨1,"b"⟩ (.borrow (.var ⟨0,"x"⟩))
      (.seq (.call "SwapS" [.borrow (.deref (.var ⟨1,"b"⟩)), tnat 0, tnat 2, .unit, .unit])
        (.seq (.call "SwapS" [.borrow (.deref (.var ⟨1,"b"⟩)), tnat 0, tnat 2, .unit, .unit])
          (.letIn ⟨2,"y"⟩ (.var ⟨0,"x"⟩) .unit))))
def runSwapTwice (lst : List Nat) (expect : List Nat) : Bool :=
  match Dllbc.Tests.S9Diff.runExec (withCursors certHonest exitHonest (swapTwiceCaller lst)) with
  | .ok env => env.lookup "y" == some (vlist expect)
  | .error _ => false
example : runSwapTwice [3,2,1] [3,2,1] = true := by native_decide

-- THE PAYOFF: the FULL quicksort FnDef — bounds, length lemmas and all — run in
-- EXECUTING mode on concrete lists, agreeing with the pure model `SortRangeL`. The
-- body's three sequential `&mut *v` reborrows (partition + two recursive calls) are
-- exactly the reborrow-collapse case the fix unblocks. Full-range callers (lo=0,
-- Cnt=len) so `hbnd = LeRefl (Len x) : Le (Add 0 Cnt) (Len x)`.
/-! ## M22-a — exit-snapshot return types + `old *v` (§5.4, direct-proving enabler)

    A borrow parameter's bare `*v` in the RETURN TYPE reads the EXIT snapshot (the
    collapsed final payload, which the audit already computes); `old *v` names the
    ENTRY snapshot (usable in the type AND the body, a non-consuming reference to
    the entry value). Consumed params stay entry-pinned (M12). These prove the
    reading is genuinely the exit value, not the entry. -/

-- The pair is the chain's `exitReject` (M28 D7): `Id (*v) (*v)` is accepted (both
-- reads see one exit snapshot) and `Id (*v) (old *v)` is rejected (the swap moved
-- things). The reading that is TRUE here and unprovable by `Refl` —
-- `Id (*v) (SwapL i j (old *v))` — is `S23Direct.swapAt`, which carries the
-- derivation; §C2 of the disposition ledger is where that hand-off is recorded.

-- OLD/EXIT MIXED: len is preserved across the swap. *v (exit) = SwapL i j (old *v),
-- so `Len *v = Len (old *v)` is exactly LenSwapL at the entry snapshot — cited
-- directly with `old *v` in the body (no need to save the list, which would move it).
/-- Two self-calls in one arm, with `[f]` the SECOND parameter — so the hoist
    permutation runs on a self-call (`progOf`'s `retarget`), which a surface-minted
    `.callV` would have skipped. `S27Dispose` §C reads its verdict as the
    disposition record for this function's retired `back = *v`. -/
def twoRec : Term := prog{
  fn TwoRec [f] (v : &mut List Nat, f : Nat) -> Unit
        { match f {
            Z => (),
            S(f2) => { TwoRec(&m *v, f2); TwoRec(&m *v, f2); () }
        } };
  () }
example : progOk twoRec = true := by native_decide

/-! ## M22-b — swapSE: count-preservation as a PROVEN postcondition (direct proving)

    The first ensures-form rung. NO back: the return type
    `Π n. Id Nat (Count n (*v)) (Count n (old *v))` is a propositional postcondition
    (swap preserves the multiset), and the body PROVES it from the exit reading —
    the demoted baseline would have declared `back = SwapL i j *v` and leaned on the
    conversion check instead. Here the cert is `CountSwapL'` (SwapL preserves count)
    read directly at the entry snapshot `old *v`.

    WHY DELEGATION, NOT INLINE (the rung's sharpest finding — see the two probes in
    the milestone report). The intended route was to INLINE the swap via `nth2`
    (reborrow `&mut *v`) and ride the §22 bridge, on the expectation that the exit
    reading would be the set/nth form `Set i (NthL j s) (Set j (NthL i s) s)`. It is
    NOT. Through inline `nth2`, the audit reconstructs `*v`-exit from nth2's back
    `Set i r1 (Set j r2 *v)` with r1/r2 the FINAL borrow payloads — and those are
    released as OPAQUE symbols `Set i σ8 (Set j σ7 s)`. The audit never learns
    `σ8 = NthL j s`, `σ7 = NthL i s`: the imperative `*ei := *ej; *ej := t` moved
    values through borrows whose provenance the release does not retain. So the
    bridge (about the nth-form) does not even TYPE against the opaque-form exit —
    a DEEPER gap than set-vs-SwapL. Routing through `swapS` (swapSN) instead makes
    the exit reading the clean model function `SwapL i j (old *v)` (swapSN's back,
    itself a provable postcondition — cf. exitAccept), and `CountSwapL'` matches it
    directly with no bridge.

    PAIN DIARY. Three entries.
    • OPAQUE EXIT READINGS — and the THREE-FEATURE ARC (the campaign's principal
      calculus-design finding). A leaf that mutates via pointer writes (`*ei := *ej`)
      leaves an exit whose written values are opaque existentials, so NO value-level
      postcondition (count/sort/perm) is provable about it. Root cause (one level
      deeper, per team-lead): the opacity is NOT intrinsic to inline mutation — it is
      minted at ONE point, buildResult, which creates an issued borrow's payload as a
      FRESH OPAQUE σ because signature-only checking has nothing saying what the
      payload IS at issue time. Everything downstream preserves information (the
      caller's writes are fully watched; the back spec routes surrendered values
      correctly) — only the issue point discards it. So the fix has a precise name:
      ISSUED-PAYLOAD PINNING, the dual of exit-snapshot — a callee declaring what its
      issued borrow's payload is at issue (`NthL` pinning `*r = NthL i (old *v)`), as
      machinery not a returned proof. The arc: PINNING makes an inline leaf's exit the
      set-form; the §22 BRIDGE (SwapLSet) rewrites set-form to the model function;
      the AUDIT-REWRITE-BY-ID feature cites the bridge at the audit — together they
      make inline leaves PROVABLE. Third convergence point for audit-rewrite (after
      M17 callee-side and the exit-reading side).
    • PROOF LINEARITY vs COUNT. Length preservation is FRICTION-FREE (lenPreserve:
      `LenSwapL` is unconditional), but count preservation needs the bounds — the
      cert wants `pij`/`p2` (CountSwapL' is bounded) AND the swap CONSUMES them.
      Mechanism (per team-lead): proofs MOVE because indexKindV's sctx-type test
      recognizes Nat/Bool/Unit/Id/Π/Type but NOT stuck proposition spines — a σ typed
      `Le (S i) j` whnf's to a stuck natRec application (none of those heads), so it
      fails index-kind and moves. Dodged here by ORDERING alone — the cert is
      let-bound BEFORE the swapS call, reading pij/p2 (non-consuming, ⇝) while live;
      swapS MOVES them after. Fragile: a postcondition citing the proofs AFTER the
      mutation cannot be ordered around. Fix (QUEUED, now RECURRED — the tax was paid
      again at partitionRangeE and quicksortE, the measured-pain threshold): extend
      indexKindTy to erasure-bound stuck types (Le-headed), same §2.1 vacuity
      rationale — proofs-as-copy-on-read. DEFERRED (per team-lead): staging is the
      law of the ladder until a postcondition genuinely can't be staged before its
      mutation, OR the audit-rewrite arc is green-lit. Viability rulings on the fix
      shape: post-readC the Le former has unfolded to an anonymous recursor spine, so
      there is no head to match — a naive "stuck-recursor-to-Type ⇒ copy" is DEAD, not
      just fragile: a σ typed by a stuck `VecF Nat n` is exactly stuck-recursor-to-Type
      yet copying it copies DATA (a vector), the very E0382 class index-kind exists to
      prevent. The sound form is making `Le` a PRIMITIVE former (like Id's `.idT`),
      which also gives audit-rewrite a head to recognize — so it belongs WITH that
      arc, not as a mid-ladder patch.
    • CONVERGENT EVIDENCE. The §22 bridge `SwapLSet` (set-form ≡ SwapL) is proved
      and kept in StdLemmas as forward infrastructure — the transport the audit-rewrite
      feature cites once pinning lands, generalizing to partition's composed set-forms.
      Separately: CountPartitionRangeL / CountSortRangeL are the very pure lemmas the
      PRE-REDIRECT M22 plan wanted — the conformance and direct-proving architectures
      have CONVERGED on the same pure-lemma obligations, differing only in where
      evidence assembly happens. A paper observation. -/
/-! ## M22-b — partitionRangeE: partition's PERMUTATION postcondition (direct proving)

    The partition rung. NO back: the return type `Π n. Id Nat (count n *v)(count n
    (old *v))` says partition permutes the range (preserves the multiset). Same
    delegation discipline as swapSE — the mutation is delegated to `partitionRange`
    (whose back `PartitionRangeL lo Cnt *v` is a CLOSED function of the input, so the
    exit reading is provable, not opaque), and the cert is the pure permutation
    lemma `CountPartitionRangeL` at the entry snapshot. Cert staged before the
    consuming call (reads `hbnd` while live — the proof-linearity dodge again). This
    is the count/Perm half of the eventual `Sorted *v ∧ Perm (old*v) *v` quicksort
    postcondition; sortedness is the other axis, still ahead. -/
/-! ## M22-b — quicksortE: quicksort's PERMUTATION postcondition (direct proving)

    THE NORTH STAR, direct-proving form. NO back: retType `Π n. Id Nat (count n *v)
    (count n (old *v))` says the in-place quicksort PERMUTES its range — a
    propositional postcondition PROVEN in the body (the demoted baseline `quicksort`
    FnDef instead declares `back = SortRangeL fuel lo Cnt *v` and checks conformance
    by conversion). Same delegation discipline as the swap and partition rungs: the
    sort is delegated to `quicksort` (back = SortRangeL, a closed function of the
    input, so the exit reading is provable rather than opaque), and the cert is the
    pure permutation lemma CountSortRangeL at the entry snapshot. Cert staged before
    the consuming call (reads hbnd live). This is the Perm half of the full
    `Sorted *v ∧ Perm (old*v) *v`; sortedness (AllLe/AllGe/sorted-glue) is the
    remaining axis. -/
end Dllbc.Tests.S19Partition
end
-- └── end of what was `S19Partition.lean` ───────────────────────────────────────────────

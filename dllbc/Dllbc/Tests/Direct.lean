import Dllbc.Program
import Dllbc.ProgMacro
import Dllbc.Boundary
import Dllbc.Std
import Dllbc.StdLemmas
import Dllbc.Tests.Diff

/-!
# Direct proving

Tests direct proving over lists: programs whose signatures state functional specs
(via Σ types), with the body discharging the spec directly — Σ projections,
dependent results at call sites, recursion as self-ensures, ownership splitting
(`split_off`/`append_back`), a relational swap, and branch equations. The
checker's symbolic walk together with branch equations can discharge these
proof obligations without a separate proof layer.
-/

section
/-!
## Direct proving with no declared backward specs

A callee's only description is its return type — a postcondition over the exit
snapshot (`*v` reads the exit, `old *v` reads the entry) — and a caller sees an
opaque exit plus whatever evidence the callee returned.

### `sigmaRec`, the missing recursor

Pure conjunctions could be *built* (`Pair(sortedcert, permcert)`) but never
*projected*: Σ needs its own recursor. With back-less callees this becomes
load-bearing rather than merely expensive: a caller's whole knowledge of its
callee's exit is the returned certificate, so it must be able to take that
certificate apart.

`sigmaRec A B P f p : P p`, with `ι : sigmaRec A B P f (Pair a b) ↦ f a b` — the
standard dependent Σ eliminator, non-recursive, so its single arm binds exactly the
two fields and takes no `ih`. Σ's parameters are a type `A` and a *family*
`B : A → Type` (unlike List's uniform parameter), which is why the `elim` sugar
requires the motive's binder type to be written as the Σ itself: `A` and `λ x. B`
are read off it.
-/

open Dllbc
open Dllbc.StdLemmas (LeReflRaw LeTransRaw LeUpRRaw Append IdCongrRaw IdTransRaw IdSymRaw
  Set NthL SwapL LenSetRaw SwapLSetRaw LeRwRRaw Ub Lb Take LebTrueLeRaw LebFalseGtRaw
  SortedHeadRaw SortedTailRaw UbHeadRaw UbTailRaw LbBoundRaw
  BoundAppendRaw SortedAppendPivotRaw LePredLRaw CountConsLRaw CountConsRRaw Len CountAppendRaw
  CountConsCongrRaw UbPermRaw LbPermRaw ListRwRaw)

namespace Dllbc.Tests.S23Direct

/-- Type-check a closed term against a closed type in the pure seed. -/
def chk (tm ty : Term) : Bool :=
  match (do let v ← readC 3000 tm; let t ← readC 3000 ty; hasTypeT 3000 v t).run (seedPure [] []) with
  | .ok r _ => r
  | .error _ _ => false

/-! ## Non-dependent Σ: the conjunction projections

    The shape every back-less caller needs: a callee returns `Σ (H : P). Q` — a
    conjunction certificate — and the caller projects out the conjunct it wants.
    `B` ignores its binder here, so the motive is constant and both projections are
    ordinary. -/

def and_left : Term := prog defer_check {
  λ (A : Nat). λ (B : Nat). λ (C : Nat).
    λ (P : Σ (H : Le A B). Le B C).
      elim P return (λ (Q : Σ (H : Le A B). Le B C). Le A B) {
        Pair (X) (Y) => X } }
def and_left_ty : Term := prog defer_check {
  Π (A : Nat) → Π (B : Nat) → Π (C : Nat) → (Σ (H : Le A B). Le B C) → Le A B }
example : chk and_left and_left_ty = true := by native_decide

def and_right : Term := prog defer_check {
  λ (A : Nat). λ (B : Nat). λ (C : Nat).
    λ (P : Σ (H : Le A B). Le B C).
      elim P return (λ (Q : Σ (H : Le A B). Le B C). Le B C) {
        Pair (X) (Y) => Y } }
def and_right_ty : Term := prog defer_check {
  Π (A : Nat) → Π (B : Nat) → Π (C : Nat) → (Σ (H : Le A B). Le B C) → Le B C }
example : chk and_right and_right_ty = true := by native_decide

-- The projections COMPOSE with an ordinary lemma: destructure the conjunction and
-- feed both halves to `LeTransRaw`. This is exactly what a caller does with a
-- returned certificate.
def and_trans : Term := prog defer_check {
  λ (A : Nat). λ (B : Nat). λ (C : Nat).
    λ (P : Σ (H : Le A B). Le B C).
      elim P return (λ (Q : Σ (H : Le A B). Le B C). Le A C) {
        Pair (X) (Y) => LeTransRaw A B C X Y } }
def and_trans_ty : Term := prog defer_check {
  Π (A : Nat) → Π (B : Nat) → Π (C : Nat) → (Σ (H : Le A B). Le B C) → Le A C }
example : chk and_trans and_trans_ty = true := by native_decide

/-! ## Dependent Σ: the second projection needs a dependent motive

    When `B` mentions its binder, `snd`'s type mentions `fst p` — so the motive is
    `λ q. Le (S Z) (sfst q)`, and the arm type-checks only because the ι-rule fires
    *inside the type*: `sfst (Pair x y)` reduces to `x`. This is dependent Σ
    elimination proper, not a pair of independent projections. -/

def sfst : Term := prog defer_check {
  λ (P : Σ (n : Nat). Le (S Z) n).
    elim P return (λ (Q : Σ (n : Nat). Le (S Z) n). Nat) {
      Pair (X) (Y) => X } }
def sfst_ty : Term := prog defer_check { (Σ (n : Nat). Le (S Z) n) → Nat }
example : chk sfst sfst_ty = true := by native_decide

def ssnd : Term := prog defer_check {
  λ (P : Σ (n : Nat). Le (S Z) n).
    elim P return (λ (Q : Σ (n : Nat). Le (S Z) n). Le (S Z) (sfst Q)) {
      Pair (X) (Y) => Y } }
def ssnd_ty : Term := prog defer_check { Π (P : Σ (n : Nat). Le (S Z) n) → Le (S Z) (sfst P) }
example : chk ssnd ssnd_ty = true := by native_decide

/-! ## The ι-rule computes -/

-- `sfst (Pair 2 (LeReflRaw 2)) ⇝ 2`, by ι on a concrete Pair.
def pv (t : Term) : Term := Pure.nf 4000 t
def vnat : Nat → Val | 0 => .ctor "Z" [] | k + 1 => .ctor "S" [vnat k]
def sfstApp : Term := prog defer_check { sfst (Pair (S (S Z)) (LeReflRaw (S (S Z)))) }
example : (Val.know (pv sfstApp) == vnat 2) = true := by native_decide

-- ι fires under binders on a Pair whose components are neutral — the case that
-- matters, since a caller destructures a certificate about symbolic values, never
-- a closed one: `λ n. λ h. sfst (Pair n h)` normalizes to `λ n. λ h. n`.
example : (pv (prog defer_check { λ (N : Nat). λ (H : Le (S Z) N). sfst (Pair N H) }) ==
           pv (prog defer_check { λ (N : Nat). λ (H : Le (S Z) N). N })) = true := by native_decide

-- The dual: a neutral target has no `Pair` to fire on, so the spine is a legal
-- stuck value rather than an error — which is what lets `ssnd`'s motive above
-- mention `sfst q` for a symbolic `q` and still be judged.

/-! ## Negative controls — one per rule branch

    The typing rule has three premises that can fail (`f`, the target, and the
    result convert) plus the ι-rule's shape condition; each gets a test, one per
    rule branch rather than one per feature. -/

-- (1) Wrong arm component: `Pair(x)(y) => y` at the first projection's type. The
-- arm must inhabit `P (Pair x y)`, which is `Le a b` — `y : Le b c` does not.
def and_left_lie : Term := prog defer_check {
  λ (A : Nat). λ (B : Nat). λ (C : Nat).
    λ (P : Σ (H : Le A B). Le B C).
      elim P return (λ (Q : Σ (H : Le A B). Le B C). Le A B) {
        Pair (X) (Y) => Y } }
example : chk and_left_lie and_left_ty = false := by native_decide

-- (2) Wrong result type: `sfst` returns `Nat`, and the claim is that it returns a
-- proof. `finish` converts the motive-at-target against the ascribed type; this is
-- the branch that catches it.
def sfst_lie_ty : Term := prog defer_check { (Σ (n : Nat). Le (S Z) n) → Le Z Z }
example : chk sfst sfst_lie_ty = false := by native_decide

-- (3) Wrong dependent motive: the second projection claimed one bigger than the
-- first component. `y : Le (S Z) x`, but `P (Pair x y)` is now `Le (S Z) (S x)` —
-- off by one, and nothing bridges it. This is the branch that would silently pass
-- if the motive were inferred from the arm rather than read off what is written.
def ssnd_lie : Term := prog defer_check {
  λ (P : Σ (n : Nat). Le (S Z) n).
    elim P return (λ (Q : Σ (n : Nat). Le (S Z) n). Le (S Z) (S (sfst Q))) {
      Pair (X) (Y) => Y } }
def ssnd_lie_ty : Term := prog defer_check { Π (P : Σ (n : Nat). Le (S Z) n) → Le (S Z) (S (sfst P)) }
example : chk ssnd_lie ssnd_lie_ty = false := by native_decide

-- (4) Wrong target: `sigmaRec` applied to something that is not of the Σ type it
-- declares. Here the target is a bare `Nat`, so the `s : Σ (x : A). B x` premise
-- fails even though the arm is fine.
def sfst_bad_target : Term := prog defer_check { sfst (S Z) }
def sfst_bad_target_ty : Term := prog defer_check { Nat }
example : chk sfst_bad_target sfst_bad_target_ty = false := by native_decide

/-! ## Dependent Σ results at a call site

    Building certificates is half of it; the other half is that a *caller* can
    receive one. A back-less callee's returned evidence is pinned to its own
    result — `Σ (r : List Nat). Id (List Nat) r (Drop i (old *v))` is split_off's
    ensures. Before the call rule built a Σ result's tail independently of its head,
    the tail's σ carried a dangling `pvar` in its sctx type and the pin was unusable:

        call: argument (σ₁) does not have its parameter type (Id σ₀ (S Z))

    The fix threads the already-built components into the tail's type (Machine.lean,
    `buildResult`'s `subs`). These three tests are the smallest statement of the
    property: a pinned result is usable, and it is usable *because* of the pin. -/

-- A back-less callee returning a pinned value, and a consumer whose second
-- parameter's type mentions its first argument.
def pinOne : Term := prog{
  fn PinOne () -> Σ (r : Nat). Id Nat r (S Z) { Pair(S Z, Refl) };
  () }
def useIt : Term := prog{
  fn UseIt (n : Nat, h : Id Nat n (S Z)) -> Unit { () };
  () }
example : progOk pinOne = true := by native_decide
example : progOk useIt = true := by native_decide

-- The caller destructures the returned pair and feeds both halves onward: `h`'s
-- type is `Id σa (S Z)` for the very σa bound to `a`. This is the caller-side
-- shape every back-less callee below depends on.
def usePin : Term := prog{
  fn PinOne () -> Σ (r : Nat). Id Nat r (S Z) { Pair(S Z, Refl) };
  fn UseIt (n : Nat, h : Id Nat n (S Z)) -> Unit { () };
  fn UsePin () -> Unit
        { let Pair(a, h) = PinOne();
          UseIt(a, h); () };
  () }
example : progOk usePin = true := by native_decide

-- Not vacuous (a): the pin says `S Z`; a consumer wanting `S (S Z)` is rejected —
-- so the threaded type is the callee's actual claim, not a rubber stamp.
def useItLie : Term := prog{
  fn UseItLie (n : Nat, h : Id Nat n (S (S Z))) -> Unit { () };
  () }
-- A callee, checked standalone before it is used in the chains below.
example : progOk useItLie = true := by native_decide
def usePinLie : Term := prog defer_check {
  fn PinOne () -> Σ (r : Nat). Id Nat r (S Z) { Pair(S Z, Refl) };
  fn UseItLie (n : Nat, h : Id Nat n (S (S Z))) -> Unit { () };
  fn UsePinLie () -> Unit
        { let Pair(a, h) = PinOne();
          UseItLie(a, h); () };
  () }
example : progRejects usePinLie "does not have its parameter type" = true := by native_decide

-- Not vacuous (b): drop the pin (a plain `Nat` result) and the caller learns
-- NOTHING about the value it got back — `Refl` cannot inhabit `Id σa (S Z)`. The
-- pin is what carries the knowledge across the boundary, which is the whole
-- premise of removing declared backs.
def plainOne : Term := prog{
  fn PlainOne () -> Nat { S Z };
  () }
-- A callee, checked standalone before it is used in the chains below.
example : progOk plainOne = true := by native_decide
def useUnpinned : Term := prog defer_check {
  fn PlainOne () -> Nat { S Z };
  fn UseIt (n : Nat, h : Id Nat n (S Z)) -> Unit { () };
  fn UseUnpinned () -> Unit { let a = PlainOne(); UseIt(a, Refl); () };
  () }
example : progRejects useUnpinned "does not have its parameter type" = true := by native_decide

/-! ## Recursion = self-ensures under a snapshot-subterm guard

    A call is checked against a signature alone — recursion forces that — so a
    self-call is admitted at the function's own declared return type. Once a
    recursive function's return type is a genuine postcondition rather than `Unit`,
    admitting a self-call unconditionally would be the Hoare rule for recursion with
    its side condition deleted: every false statement proves itself:

        fn bad () -> Id Nat Z (S Z) { bad() }            -- would be ACCEPTED
        fn bad2 (n : Nat) -> Id Nat Z (S Z) { bad2(n) }  -- would be ACCEPTED

    The side condition is `[k]`: a self-call is admitted only when the actual at the
    declared decreasing position is a strict structural subterm of that parameter's
    current snapshot. The checker being a symbolic interpreter is what makes this
    cheap — inside `match n { S(m) => … }` the parameter's snapshot has been
    ⇜-refined to `S σ_m` while the actual is `σ_m`, so the comparison is ordinary
    structural equality on snapshots. The snapshot rides `refineSym` with the rest
    of the σ-bearing state, which is what makes it readable at the call site at all:
    owned match has meanwhile emptied the parameter's runtime slot.

    A negative test per rule branch, not per feature. -/

-- The honest shape, and the one the rest of this suite rides: structural decrease
-- on a declared fuel argument.
def recGood : Term := prog{
  fn RecGood [n] (n : Nat) -> Id Nat Z Z
        { match n { Z => Refl, S(m) => RecGood(m) } };
  () }
example : progOk recGood = true := by native_decide

-- BRANCH 1 — no `[k]` at all. This exact FnDef would prove `Z = S Z` if admitted.
def recBad : Term := prog defer_check {
  fn RecBad () -> Id Nat Z (S Z) { RecBad() };
  () }
-- Still refused, but for a different reason: a recursive occurrence is the `ih`
-- binder, and scope is the let-chain, so a self-call resolves to nothing — a
-- let-chain cannot reference downward. So `Z = S Z` stays unprovable not by a
-- side condition but by the name not existing.
example : progRejects recBad "unknown function" = true := by native_decide

-- BRANCH 2 — `[k]` declared, but the self-call passes the same fuel. Equal is not
-- strictly smaller; this is the shape the strictness in `strictSubterm` exists for.
def recSame : Term := prog defer_check { fn RecSame [n] (n : Nat) -> Id Nat Z (S Z) { RecSame(n) }; () }
-- Refused at elaboration: `ih` is the sealed self-view at the predecessor, so a
-- self-call at any other argument has nothing to become, and `fnElab` says so
-- rather than emitting a recursor that would be a different function. Asserted on
-- the refusal itself — a twin that merely declined would teach nothing.
example : progRejects recSame "not the predecessor" = true := by native_decide

-- BRANCH 3 — decrease at the wrong index. The return type here is true, so the
-- audit cannot be what rejects it: `[n]` is declared while `m` is what shrinks.
-- (Without this control the previous two would pass on a guard that merely
-- required *something* to decrease — which is unsound, since alternating branches
-- can each decrease a different coordinate forever.)
def recWrongIdx : Term := prog defer_check {
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

-- BRANCH 4 — an increase reads as "not a subterm", not as a decrease: `S(m2)`
-- against a snapshot of `S m2` is equality one level up, and equality never passes.
def recGrow : Term := prog defer_check {
  fn RecGrow [n] (n : Nat) -> Id Nat Z Z
        { match n { Z => Refl, S(m2) => RecGrow(S(m2)) } };
  () }
example : progRejects recGrow "not the predecessor" = true := by native_decide

-- BRANCH 5 — mutual recursion. The guard is per-declaration, so `f → g → f` would
-- let each admit the other's postcondition with nothing decreasing anywhere: the
-- same hole through two doors. Rejected outright: mutual recursion is unwritable
-- rather than merely rejected, because `recMutB` is not in scope above `recMutA`.
-- The rejection names the forward reference.
def recMutA : Term := prog defer_check {
  fn RecMutA () -> Id Nat Z (S Z) { RecMutB() };
  fn RecMutB () -> Id Nat Z (S Z) { RecMutA() };
  () }
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
def recDeep : Term := prog defer_check {
  fn RecDeep [n] (n : Nat) -> Id Nat Z Z
        { match n { Z => Refl, S(a) => match a { Z => Refl, S(b) => RecDeep(b) } } };
  () }
-- A macro limit, not a calculus one: the macro declines two-constructors-down
-- because it derives the motive mechanically from the signature and this shape
-- needs a different one. The form exists and checks as a sealed recursor written
-- by hand; what is asserted here is only the macro's refusal.
example : progRejects recDeep "not the predecessor" = true := by native_decide

/-! ### The one shape the eliminators cannot express: `[v]`, and what it costs

    A borrow parameter decreases through its payload snapshot — the guard in its
    most literal form, and the only thing that shrinks in a list cursor with no
    counter. Snapshots are entry-knowledge and are never rewritten by mutation, so
    the payload's structural decomposition is a fixed, well-founded order, and the
    declaration path admitted it.

    It has no recursor form: `[k]` elaborates to `natRec`/`listRec` over the
    parameter itself, and a borrow is neither, and no borrow-mode eliminator exists.
    Fuel-threading is the accepted interim — a source change, since the signature
    grows a parameter and a bound and every caller supplies them, rather than
    something an elaboration invents behind its author.

    So this is the whole of the `[v]` class, at program level: the `fn` lowering
    refuses it, pointing at the decision rather than at a shape. Three functions in
    this file are written this way in principle — the list cursor below,
    `append_back` and `partition` — and all three are fuel-threaded in the flagship
    chain below, where the price is one parameter and one dead branch. -/

def borrowDecrease : Term := prog defer_check {
  fn ZeroAll [v] (v : &mut List Nat) -> Unit
        { match v { Nil => (), Cons(hd, tl) => { *hd := 0; ZeroAll(tl); () } } };
  () }
-- Refused by the needle no other error can produce…
example : progRejects borrowDecrease FnMacro.fnRefusedNeedle = true := by native_decide
-- …and the refusal's own diagnosis survives into the message, which is what makes
-- it a decision rather than a dead end: the programmer is told to thread fuel.
example : progRejects borrowDecrease "§12 decision 8" = true := by native_decide
-- It can never pass green: the sentinel is reached at the binding, not at a call,
-- so a refused function that nothing calls still fails.
example : progOk borrowDecrease = false := by native_decide
-- The fuel-threaded twin of this function does check; the cost is measured, not
-- estimated.

-- A non-self call to a recursive function is untouched — the guard is about
-- self-calls, and every other call is the ordinary signature-checking rule.
def recCaller : Term := prog{
  fn RecGood [n] (n : Nat) -> Id Nat Z Z { match n { Z => Refl, S(m) => RecGood(m) } };
  fn RecCaller () -> Id Nat Z Z { RecGood(S Z) };
  () }
-- The callee is in scope by being written above it.
example : progOk recCaller = true := by native_decide

/-! ## Ownership splitting — `split_off` and `append_back`

    The data plan for a back-less quicksort: recursion over whole lists instead of
    range indices. `split_off` takes the tail at depth `i` out of a borrowed list
    and returns it by value (it cannot come back as a borrow — its owner is local);
    `append_back` walks to the end and replaces the `Nil`. Between them the caller
    owns two independent lists, sorts each, and glues.

    Both are back-less: the only description of either is its return type. And both
    ensures are stated in observation functions — `Take`, `Drop`, `Append`, which
    define meaning independently of any implementation — not in a pure function
    mirroring the body's own algorithm. That is the line: `Id (*v) (Take i (old *v))`
    is split_off's spec, not a mirror of it.

    Both check with no declared back anywhere in the call tree. -/

-- `append_back(v, w)`: walk to the end of `*v`, put `w` there. The exit reading is
-- `Append (old *v) w` — the whole postcondition, and the whole description. It has
-- no recursor form for its own decrease, so it is written fuel-threaded, in the
-- flagship chain below where its one caller lives.

/-! ### The telescope's own vocabulary

    A `fn`'s parameters are `.var ⟨i, name⟩` at their positional index, and a return
    type written outside the header — a skeleton, below — has to name them that
    way. These are those names, once, so that every skeleton in this file splices
    them rather than re-deriving an index. -/

def vT : Term := .var ⟨0, "v"⟩
def dvT : Term := .deref vT
def oldvT : Term := .app (.const "old") dvT
def iT : Term := .var ⟨1, "i"⟩
def xT : Term := .var ⟨2, "x"⟩
def jT : Term := .var ⟨2, "j"⟩

-- `split_off(v, i)`: `*v` keeps the first `i`, the rest comes back by value. The
-- returned tail is Σ-pinned to `Drop i (old *v)` — the caller's only knowledge of a
-- value it did not compute.
--
-- Written as a skeleton over its return type and its tail: the body is thirty
-- lines and the three spec twins below differ from the honest form in exactly one
-- named argument each, so the body is written once and the difference is by
-- construction rather than by a reader comparing two spellings.
def soUnder (ret tail : Term) : Term := prog{
  fn SplitOff [i] (v : &mut List Nat, i : Nat, hi : Le i (Len *v)) -> %ret
        { match i {
            -- i = Z: take the whole payload out (take-and-refill, the idiom Rust
            -- rejects with E0507) and leave `Nil`. `Take Z l = Nil` and
            -- `Drop Z l = l` both compute, so both conjuncts are `Refl`.
            Z => { let tail = *v; *v := Nil; Pair(tail, Pair(Refl, Refl)) },
            S(i2) => match v {
              -- `hi : Le (S i2) (Len Nil)` is `Le (S i2) Z`, which is `Bot`: the
              -- branch is dead and the audit admits an ex-falso at any type.
              Nil => botElim Unit hi,
              Cons(hd, tl) => {
                -- `hi` passes down definitionally: `Len (Cons _ t) = S (Len t)`, so
                -- `Le (S i2) (S (Len σ_tl))` already is `Le i2 (Len σ_tl)`.
                let y1 = Take i2 (*tl);
                let Pair(rr, Pair(H1, h2)) = SplitOff(&m *tl, i2, hi);
                -- The prefix conjunct needs a congruence under `Cons (*hd)`, and
                -- reading `*tl` here — after handing `&mut *tl` to the call — is
                -- the only way to name the callee's exit.
                -- The suffix conjunct needs nothing: `Drop (S i2) (Cons h t)` is
                -- `Drop i2 t`, so the callee's `h2` is already the goal.
                let H0 = *hd;
                let c1 = IdCongrRaw (List Nat) (List Nat) (λ (A : List Nat). Cons H0 A)
                           (*tl) y1 H1;
                Pair(rr, Pair(c1, h2))
              }
            }
        } };
  %tail }

/-- The return type, as a skeleton over its two conjuncts' right-hand sides. Still
    surface syntax — only the two subterms the twins vary are spliced — so what a
    reader compares is `Take i (old *v)` against `Take (S i) (old *v)`, one
    argument apart, and not two hand-built Σ-chains. -/
def soRet (pre suf : Term) : Term := prog{
  Σ (ret : List Nat). Σ (H1 : Id (List Nat) %dvT %pre). Id (List Nat) ret %suf }

def soHonest : Term := soRet (prog defer_check { Take %iT %oldvT }) (prog defer_check { Drop %iT %oldvT })
def splitOff : Term := soUnder soHonest .unit
example : progOk splitOff = true := by native_decide

/-! ### Not vacuous: the spec twins, and the body twin

    Three spec lies (shifting either index, and swapping the two conjuncts) and one
    body lie. The spec lies are all caught on the `i = Z` path, so they alone would
    leave the recursive path untested; the body lie breaks the congruence in the
    `Cons` branch and is the control for that path. -/

def splitOffLieTake : Term := soUnder (soRet (prog defer_check { Take (S %iT) %oldvT }) (prog defer_check { Drop %iT %oldvT })) .unit
def splitOffLieDrop : Term := soUnder (soRet (prog defer_check { Take %iT %oldvT }) (prog defer_check { Drop (S %iT) %oldvT })) .unit
def splitOffLieSwap : Term := soUnder (soRet (prog defer_check { Drop %iT %oldvT }) (prog defer_check { Take %iT %oldvT })) .unit
example : progRejects splitOffLieTake "does not have return type" = true := by native_decide
example : progRejects splitOffLieDrop "does not have return type" = true := by native_decide
example : progRejects splitOffLieSwap "does not have return type" = true := by native_decide

-- The body lie: the congruence forgets to put `*hd` back on the front (identity
-- instead of `Cons (*hd) ·`), so the prefix conjunct is off by the head element.
-- Rejected on the recursive path, which no spec twin above reaches.
--
-- Transcribed rather than sharing `soUnder`'s body, and that is forced: what
-- varies is a subterm inside the body that names `hd` — a binder the `fn` lowering
-- mints an id for — and a `%` splice is a Lean `Term` written outside the macro,
-- which has no way to say "the `hd` this match will bind".
def splitOffLieHead : Term := prog defer_check {
  fn SplitOff [i] (v : &mut List Nat, i : Nat, hi : Le i (Len *v)) -> %soHonest
        { match i {
            Z => { let tail = *v; *v := Nil; Pair(tail, Pair(Refl, Refl)) },
            S(i2) => match v {
              Nil => botElim Unit hi,
              Cons(hd, tl) => {
                let y1 = Take i2 (*tl);
                let Pair(rr, Pair(H1, h2)) = SplitOff(&m *tl, i2, hi);
                let c1 = IdCongrRaw (List Nat) (List Nat) (λ (A : List Nat). A)
                           (*tl) y1 H1;
                Pair(rr, Pair(c1, h2))
              }
            }
        } };
  () }
example : progRejects splitOffLieHead "does not have return type" = true := by native_decide

/-! ### The executing differential — the body really splits

    `progOk` proves the postcondition symbolically; this runs the same program on
    concrete lists and confirms `*v` keeps `Take i l` while the returned value is
    `Drop i l`, at the two boundaries and in the middle. The caller rides `soUnder`'s
    own chain as its tail, so what runs is the function declared above it. -/

def vnatV : Nat → Val | 0 => .ctor "Z" [] | k + 1 => .ctor "S" [vnatV k]
def vlistV : List Nat → Val | [] => .ctor "Nil" [] | x :: xs => .ctor "Cons" [vnatV x, vlistV xs]
def soCallerTail (l : List Nat) (i : Nat) : Term := prog defer_check {
  let x = %(Std.ofList (l.map Term.nat));
  let b = &m x;
  let p = SplitOff(b, %(Term.nat i), ());
  match p { Pair(rr, q) => { let y = x; () } } }
def runSplit (l : List Nat) (i : Nat) : Bool :=
  match Dllbc.Tests.S9Diff.runExec (soUnder soHonest (soCallerTail l i)) with
  | .ok env => env.lookup "y" == some (vlistV (l.take i)) && env.lookup "rr" == some (vlistV (l.drop i))
  | .error _ => false

example : runSplit [1,2,3,4] 2 = true := by native_decide   -- split in the middle
example : runSplit [1,2,3] 0 = true := by native_decide      -- take nothing, hand the whole list back
example : runSplit [1,2,3] 3 = true := by native_decide      -- take everything, hand back Nil

/-! ## The swap leaf, relational

    An in-place leaf mutating through pointer writes has an opaque exit, so no
    value-level postcondition is provable about it directly — the escape is
    delegation: mutate through a callee carrying a declared `back` and cite a pure
    lemma about its model. But the opacity is a property of borrows issued by a
    call: `buildResult` mints an issued borrow's payload as a fresh σ, because
    signature-only checking has nothing to say what the payload is at issue time.
    It is not a property of inline mutation. A leaf that does its own cursor work
    through the body's own match-field borrows writes into a suspension the audit
    collapses itself, so its exit is a constructor tree over known snapshots —
    fully provable, with nothing minted opaquely anywhere.

    So the fix is a program-level choice: walk the list yourself instead of calling
    a cursor helper. `set_at` below is the proof of that, and `swap_at` shows a
    bridge lemma between the set-based and relational readings evaporating too —
    it is just an ordinary lemma applied in the body, needing no audit machinery at
    all. -/

/-! `set_at(v, i, x)` writes `x` at position `i`, in place, through the body's own
    field reborrows; `swap_at(v, i, j)` is two `set_at`s and a bridge lemma. They are
    one chain because the second calls the first — the caller is in scope by being
    written below it — and the chain takes both return types as parameters, so each
    of the four twins varies exactly one of them while the two bodies are written
    once.

    One chain serves both twin families: a lying `set_at` is refused at its own
    seal, and a sealed `let` fires its audit at its own node in program order, so
    the message a `set_at` twin is caught by is `set_at`'s — `swap_at`, which also
    breaks under it, is never reached. Varying the second return type leaves the
    first honest and the attribution is `swap_at`'s for the same reason. -/

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
                IdCongrRaw (List Nat) (List Nat) (λ (A : List Nat). Cons H0 A) (*tl) y h
              }
            }
        } };
  -- `SwapAt(v, i, j)`: two `SetAt`s and a bridge lemma, ensuring the model
  -- function `SwapL` directly. Not recursive itself — the recursion is `SetAt`'s.
  fn SwapAt (v : &mut List Nat, i : Nat, j : Nat, pij : Le (S i) j,
                    p2 : Le (S j) (Len *v), hi : Le (S i) (Len *v)) -> %wret
        { let a = NthL i (*v);
          let b = NthL j (*v);
          -- The bridge, cited as an ordinary lemma in the body. No audit feature,
          -- no pinning: `Set i b (Set j a s)` IS the set-form it relates.
          let bridge = SwapLSetRaw i j (old *v) pij p2;
          let h1 = SetAt(&m *v, j, a, p2);
          -- The second write's bound is stated over the LIVE `*v`, which the first
          -- write replaced with an opaque σ′, so it transports back through
          -- `LenSetRaw` along h1.
          let hlen = IdTransRaw Nat (Len *v) (Len (Set j a (old *v))) (Len (old *v))
                       (IdCongrRaw (List Nat) Nat Len (*v) (Set j a (old *v)) h1)
                       (LenSetRaw j a (old *v));
          let hi2 = LeRwRRaw (S i) (Len (old *v)) (Len *v)
                      (IdSymRaw Nat (Len *v) (Len (old *v)) hlen) hi;
          -- A body can only ever talk about the CURRENT exit: after the second call
          -- the first call's exit σ′ can no longer be named, since `*v` reads the
          -- newest value and nothing binds an older one. So the remaining
          -- derivation is staged as a function of the next exit while σ′ is still
          -- readable, and applied afterwards. Every value the closure below needs
          -- is named first, on its own line, so a reader can see which moment each
          -- one belongs to; `V0` is the pre-`h2` payload, the superseded
          -- intermediate this staging is about.
          let I0 = i;
          let B0 = b;
          let J0 = j;
          let A0 = a;
          let V0 = *v;
          let OldV0 = old *v;
          let H1 = h1;
          let Bridge0 = bridge;
          let Finish = (λ (E : List Nat). λ (Hh : Id (List Nat) E (Set I0 B0 V0)).
                          IdTransRaw (List Nat) E (Set I0 B0 V0) (SwapL I0 J0 OldV0)
                            Hh
                            (IdTransRaw (List Nat) (Set I0 B0 V0) (Set I0 B0 (Set J0 A0 OldV0))
                               (SwapL I0 J0 OldV0)
                               (IdCongrRaw (List Nat) (List Nat) (λ (Z0 : List Nat). Set I0 B0 Z0)
                                 V0 (Set J0 A0 OldV0) H1)
                               Bridge0));
          let h2 = SetAt(&m *v, i, b, hi2);
          Finish (*v) h2 };
  %tail }

/-- Each return type as a skeleton over the model function it cites — still surface
    syntax, one spliced subterm, so the twins below read as the lie they are. -/
def exitIs (rhs : Term) : Term := prog{ Id (List Nat) %dvT %rhs }

def setHonest : Term := exitIs (prog defer_check { Set %iT %xT %oldvT })
def swapHonest : Term := exitIs (prog defer_check { SwapL %iT %jT %oldvT })

/-- The pair, both honest. `swap_at` calls `set_at [i]`, whose decreasing parameter
    is second, so the sealed callee's telescope is `(i, v, x, hi)` while the call is
    written in declaration order — the chain has to permute it. -/
def setSwap : Term := setSwapUnder setHonest swapHonest .unit
example : progOk setSwap = true := by native_decide

/-! ### Not vacuous -/

-- The index off by one, and the no-op, once per function.
example : progRejects (setSwapUnder (exitIs (prog defer_check { Set (S %iT) %xT %oldvT })) swapHonest .unit)
  "does not have return type" = true := by native_decide
example : progRejects (setSwapUnder (exitIs oldvT) swapHonest .unit)
  "does not have return type" = true := by native_decide
example : progRejects (setSwapUnder setHonest (exitIs (prog defer_check { SwapL (S %iT) %jT %oldvT })) .unit)
  "does not have return type" = true := by native_decide
example : progRejects (setSwapUnder setHonest (exitIs oldvT) .unit)
  "does not have return type" = true := by native_decide

/-! ### The executing differential — the bodies really write and really swap

    Proof arguments in the callers below are placeholders `()`, since the
    executing run does not type-check. Each rides the honest chain as its tail, so
    what runs is the function declared above it. -/
def setCallerTail (l : List Nat) (i x : Nat) : Term := prog defer_check {
  let z = %(Std.ofList (l.map Term.nat));
  let b = &m z;
  SetAt(b, %(Term.nat i), %(Term.nat x), ());
  let y = z;
  () }
def runSetAt (l : List Nat) (i x : Nat) : Bool :=
  match Dllbc.Tests.S9Diff.runExec (setSwapUnder setHonest swapHonest (setCallerTail l i x)) with
  | .ok env => env.lookup "y" == some (vlistV (l.set i x))
  | .error _ => false

example : runSetAt [1,2,3] 0 9 = true := by native_decide
example : runSetAt [1,2,3] 2 9 = true := by native_decide
example : runSetAt [5,5,5,5] 1 7 = true := by native_decide

def swapCallerTail (l : List Nat) (i j : Nat) : Term := prog defer_check {
  let z = %(Std.ofList (l.map Term.nat));
  let b = &m z;
  SwapAt(b, %(Term.nat i), %(Term.nat j), (), (), ());
  let y = z;
  () }
def runSwapAt (l : List Nat) (i j : Nat) : Bool :=
  match Dllbc.Tests.S9Diff.runExec (setSwapUnder setHonest swapHonest (swapCallerTail l i j)) with
  | .ok env =>
    match l[i]?, l[j]? with
    | some a, some b => env.lookup "y" == some (vlistV ((l.set i b).set j a))
    | _, _ => false
  | .error _ => false

example : runSwapAt [1,2,3] 0 2 = true := by native_decide      -- ends
example : runSwapAt [1,2,3,4] 1 2 = true := by native_decide    -- adjacent interior
example : runSwapAt [4,1,3,2,5] 0 4 = true := by native_decide  -- full span

/-! **The rule.** `match h : c { … }` additionally binds, in every branch, an
    equation `h : Id τ ⟨the scrutinee's pre-split value⟩ ⟨this branch's
    constructor⟩`. That is the standard dependent-match-with-equations shape — Lean's
    `match h : x with`, Coq's `destruct … eqn:` — and the equation IS the branch's
    match-shape knowledge: a fact about the value, true at entry and forever, until
    now applied only as a substitution and here additionally reified as a citable
    term.

    The pre-split value is where the two cases come apart. At an ordinary split ⇜
    rewrites the scrutinee's value to this constructor everywhere, so the equation's
    two endpoints are already identical and `h` is `Refl` — informative-free, as it
    should be. At a stuck split `generalizeStuck` abstracted the spine before the
    refinement, so nothing in the state mentions `Leb a b` any more and a body that
    recomputes it is talking about a term the refinement never saw. There the
    equation is a genuine hypothesis, minted as a fresh σ typed
    `Id Bool (Leb σa σb) True` — the one thing this rule adds.

    Citing this equation is what makes the body below check: without it, a body
    that recomputes `Leb a b` after a stuck split has only `Refl` to offer, and
    `Refl` cannot prove a fact the split never named — the equation is the one new
    thing the rule adds. -/

def branchKnowledgeEq : Term := prog{
  fn NeedLe (a : Nat, b : Nat, h : Le a b) -> Unit { () };
  fn BranchKnowledgeEq (a : Nat, b : Nat) -> Unit
        { let c = Leb a b;
          match e : c {
            True => { NeedLe(a, b, LebTrueLeRaw a b e); () },
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
-- A callee, checked standalone before it is used in the chains below.
example : progOk needGt = true := by native_decide
def branchKnowledgeBoth : Term := prog{
  fn NeedLe (a : Nat, b : Nat, h : Le a b) -> Unit { () };
  fn NeedGt (a : Nat, b : Nat, h : Le (S b) a) -> Unit { () };
  fn BranchKnowledgeBoth (a : Nat, b : Nat) -> Unit
        { let c = Leb a b;
          match e : c {
            True => { NeedLe(a, b, LebTrueLeRaw a b e); () },
            False => { NeedGt(a, b, LebFalseGtRaw a b e); () }
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
        { if e : Leb a b { NeedLe(a, b, LebTrueLeRaw a b e); () }
          else { NeedGt(a, b, LebFalseGtRaw a b e); () } };
  () }
example : progOk branchKnowledgeIf = true := by
  native_decide

/-! #### Negative controls — one per rule branch

    The rule has exactly three branches that can produce an equation: the stuck
    split (a real hypothesis), the ordinary symbolic split (`Refl`), and the
    concrete split (`Refl`). Each gets a control, plus the two ways the minted
    hypothesis could be a rubber stamp. -/

-- (1) The equation is the branch's own constructor, not the other one: citing
-- `LebFalseGtRaw` on the True branch's `e : Id Bool (Leb a b) True` is rejected.
def branchEqSwapped : Term := prog defer_check {
  fn NeedLe (a : Nat, b : Nat, h : Le a b) -> Unit { () };
  fn NeedGt (a : Nat, b : Nat, h : Le (S b) a) -> Unit { () };
  fn BranchEqSwapped (a : Nat, b : Nat) -> Unit
        { let c = Leb a b;
          match e : c {
            True => { NeedGt(a, b, LebFalseGtRaw a b e); () },
            False => ()
          } };
  () }
example : progRejects branchEqSwapped "does not have its parameter type" = true := by native_decide

-- (2) The equation is about the spine that was split on, not any spine: split on
-- `Leb a b`, then claim the equation is about `Leb b a`. Rejected — so the minted
-- type is read off the abstracted scrutinee, not fabricated per use site.
def needLeSwap : Term := prog{
  fn NeedLeSwap (a : Nat, b : Nat, h : Le b a) -> Unit { () };
  () }
-- A callee, checked standalone before it is used in the chains below.
example : progOk needLeSwap = true := by native_decide
def branchEqWrongSpine : Term := prog defer_check {
  fn NeedLeSwap (a : Nat, b : Nat, h : Le b a) -> Unit { () };
  fn BranchEqWrongSpine (a : Nat, b : Nat) -> Unit
        { let c = Leb a b;
          match e : c {
            True => { NeedLeSwap(a, b, LebTrueLeRaw b a e); () },
            False => ()
          } };
  () }
example : progRejects branchEqWrongSpine "does not have its parameter type" = true := by native_decide

-- (3) An ordinary symbolic split still yields only `Refl`: `n`'s equation in the
-- `S` branch is `Id Nat (S σm) (S σm)` — ⇜ already rewrote the pre-split value, so
-- both endpoints are the constructor tree and nothing off-diagonal is derivable.
def wantEqLie : Term := prog{
  fn WantEqLie (n : Nat, h : Id Nat (S n) n) -> Unit { () };
  () }
-- A callee, checked standalone before it is used in the chains below.
example : progOk wantEqLie = true := by native_decide
def branchEqPlainSym : Term := prog defer_check {
  fn WantEqLie (n : Nat, h : Id Nat (S n) n) -> Unit { () };
  fn BranchEqPlainSym (n : Nat) -> Unit
        { match e : n { Z => (), S(m) => { WantEqLie(m, e); () } } };
  () }
example : progRejects branchEqPlainSym "does not have its parameter type" = true := by native_decide

-- …and the reflexive reading of that same equation is available: `Id Nat (S m) (S m)`.
def wantRefl : Term := prog{
  fn WantRefl (n : Nat, h : Id Nat (S n) (S n)) -> Unit { () };
  () }
-- A callee, checked standalone before it is used in the chains below.
example : progOk wantRefl = true := by native_decide
def branchEqPlainSymRefl : Term := prog{
  fn WantRefl (n : Nat, h : Id Nat (S n) (S n)) -> Unit { () };
  fn BranchEqPlainSymRefl (n : Nat) -> Unit
        { match e : n { Z => (), S(m) => { WantRefl(m, e); () } } };
  () }
example : progOk branchEqPlainSymRefl = true := by
  native_decide

-- (4) The concrete split (the executing side and any concrete scrutinee) binds the
-- equation too, so a body written with `match h :` runs. The differential below
-- exercises the same path end to end.
def concreteEq : Term := prog{
  fn WantRefl (n : Nat, h : Id Nat (S n) (S n)) -> Unit { () };
  fn ConcreteEq () -> Unit
        { let n = S(Z);
          match e : n { Z => (), S(m) => { WantRefl(m, e); () } } };
  () }
example : progOk concreteEq = true := by native_decide

-- `Ub`/`Lb` compute, and are Σ-chained (so `sigmaRec` consumes them).
--
-- The hand-written side's Σ binders are capital: `Ub`/`Lb` chain proof
-- components, a proof component's binder is capital, and a capital Σ binder
-- carries `⇝` on its domain — so a lowercase twin here would no longer be the
-- same type. The comparison is by `pv`, which prints the marker, so this is the
-- assertion that the library's own components declare themselves comptime.
example : (pv (prog defer_check { Ub (S (S Z)) (Cons (S Z) (Cons (S (S Z)) Nil)) }) ==
           pv (prog defer_check { Σ (H : Le (S Z) (S (S Z))). Σ (H2 : Le (S (S Z)) (S (S Z))). Unit })) = true := by native_decide
example : (pv (prog defer_check { Lb Z (Cons (S Z) Nil) }) == pv (prog defer_check { Σ (H : Le Z (S Z)). Unit })) = true := by native_decide

-- Generic J-transport at `List Nat` — `LeRwRRaw` for arbitrary list predicates. Every
-- certificate a back-less body returns is stated over an exit it knows only
-- propositionally (from the callee's evidence), so transporting a proof along that
-- evidence is the universal last step; `LeRwRRaw` already covers the `Le`-over-`Nat`
-- case and this is the unrestricted one.
example : chk Dllbc.StdLemmas.ListRwRaw Dllbc.StdLemmas.ListRwTy = true := by native_decide

/-! ### The pivot glue — `Sorted (a ++ p :: b)` from the four partition facts

    A back-less partition hands its caller two whole lists and a pivot, with the four
    facts `Sorted a`, `Ub p a`, `Sorted b`, `Lb p b`; `SortedAppendPivotRaw` is what
    turns those into the sortedness half of quicksort's postcondition. The Σ-chained
    predicates are taken apart with `sigmaRec` — five projections first, then the
    head-bound transport, then the induction. -/

example : chk SortedHeadRaw Dllbc.StdLemmas.SortedHeadTy = true := by native_decide
example : chk SortedTailRaw Dllbc.StdLemmas.SortedTailTy = true := by native_decide
example : chk UbHeadRaw Dllbc.StdLemmas.UbHeadTy = true := by native_decide
example : chk UbTailRaw Dllbc.StdLemmas.UbTailTy = true := by native_decide
example : chk LbBoundRaw Dllbc.StdLemmas.LbBoundTy = true := by native_decide
example : chk BoundAppendRaw Dllbc.StdLemmas.BoundAppendTy = true := by native_decide
example : chk SortedAppendPivotRaw Dllbc.StdLemmas.SortedAppendPivotTy = true := by native_decide

-- It computes, end to end: `[1] ++ 2 :: [3]` is sorted, from the four facts about
-- the parts. Every hypothesis at these values is a `⊤`-chain, so the witnesses are
-- `Pair(unit, unit)` — the content is entirely in the lemma.
def sap_app : Term := prog defer_check {
  SortedAppendPivotRaw (S (S Z)) (Cons (S Z) Nil) (Cons (S (S (S Z))) Nil)
    Pair(unit, unit) Pair(unit, unit) Pair(unit, unit) Pair(unit, unit) }
def sap_app_ty : Term := prog defer_check {
  Sorted (Cons (S Z) (Cons (S (S Z)) (Cons (S (S (S Z))) Nil))) }
example : chk sap_app sap_app_ty = true := by native_decide

/-! Honesty controls. Each flips one hypothesis and watches the check fail — the
    two orientation flips (`Ub`/`Lb` swapped for their duals) and one arm lie. -/

-- (1) `Ub p a` weakened to `Lb p a`: `UbHeadRaw` now receives `Σ (Le p h). Lb p t`
-- where it wants `Σ (Le h p). Ub p t`. Without a's elements being below the pivot
-- the splice is not sorted, and the check says so.
def sap_lie_ub_ty : Term := prog defer_check {
  Π (P : Nat) → Π (A : List Nat) → Π (B : List Nat) →
    Sorted A → Lb P A → Sorted B → Lb P B → Sorted (Append A (Cons P B)) }
example : chk SortedAppendPivotRaw sap_lie_ub_ty = false := by native_decide

-- (2) `Lb p b` weakened to `Ub p b`: `LbBoundRaw` is fed the wrong direction, so the
-- pivot no longer bounds b's head.
def sap_lie_lb_ty : Term := prog defer_check {
  Π (P : Nat) → Π (A : List Nat) → Π (B : List Nat) →
    Sorted A → Ub P A → Sorted B → Ub P B → Sorted (Append A (Cons P B)) }
example : chk SortedAppendPivotRaw sap_lie_lb_ty = false := by native_decide

-- (3) The `Nil` arm of the transport returning the wrong hypothesis: past the end of
-- `t` the new head is the pivot, so only `Le h p` inhabits the goal; handing back the
-- (vacuous) `Bound h Nil` does not.
def bound_append_lie : Term := prog defer_check {
  λ (H : Nat). λ (P : Nat). λ (T : List Nat). λ (B : List Nat).
    elim T return (λ (Tz : List Nat).
        Bound H Tz → Le H P → Bound H (Append Tz (Cons P B))) {
      Nil => λ (Hb : Unit). λ (Hp : Le H P). Hb,
      Cons (H2) (T2) Ih => λ (Hb : Le H H2). λ (Hp : Le H P). Hb } }
example : chk bound_append_lie Dllbc.StdLemmas.BoundAppendTy = false := by native_decide

-- (4) Liveness of the `Ub` hypothesis at concrete values: pivot 0 under a left part
-- containing 1 needs `Le 1 0 = ⊥`, which `Pair(unit, unit)` does not inhabit — so the
-- positive computation above passed on its hypotheses, not on a rubber stamp.
def sap_bad_pivot : Term := prog defer_check {
  SortedAppendPivotRaw Z (Cons (S Z) Nil) Nil
    Pair(unit, unit) Pair(unit, unit) unit unit }
def sap_bad_pivot_ty : Term := prog defer_check {
  Sorted (Cons (S Z) (Cons Z Nil)) }
example : chk sap_bad_pivot sap_bad_pivot_ty = false := by native_decide

/-! ## The bound-survival keystone, checked

    A partition-based quicksort needs `Ub p a` for the left part after sorting, while
    the partition bounded it before — so a bound has to survive a permutation, and
    `Ub`/`Lb` (Σ-chains over the spine) are not natively permutation-invariant. The
    route is to cross to the multiset, where the property is
    `Π x. x > p → Count x l = Z` and permutation-invariance is a one-line `IdTransRaw`.
    These are the whole-list instances. -/

example : chk Dllbc.StdLemmas.LbHeadRaw Dllbc.StdLemmas.LbHeadTy = true := by native_decide
example : chk Dllbc.StdLemmas.LbTailRaw Dllbc.StdLemmas.LbTailTy = true := by native_decide
example : chk Dllbc.StdLemmas.NoAboveOfUbRaw Dllbc.StdLemmas.NoAboveOfUbTy = true := by native_decide
example : chk Dllbc.StdLemmas.UbOfNoAboveRaw Dllbc.StdLemmas.UbOfNoAboveTy = true := by native_decide
example : chk Dllbc.StdLemmas.UbPermRaw Dllbc.StdLemmas.UbPermTy = true := by native_decide
example : chk Dllbc.StdLemmas.NoBelowOfLbRaw Dllbc.StdLemmas.NoBelowOfLbTy = true := by native_decide
example : chk Dllbc.StdLemmas.LbOfNoBelowRaw Dllbc.StdLemmas.LbOfNoBelowTy = true := by native_decide
example : chk Dllbc.StdLemmas.LbPermRaw Dllbc.StdLemmas.LbPermTy = true := by native_decide


/-! # The flagship cohort, as one program

    `partition`, `append_back` and `quicksort` are three sealed `let`s and a tail,
    written here as one chain because that is what they are: the caller reaches
    each callee by being written below it, and nothing is passed beside anything.

    ## The relational partition

    `partition(v, p)`: `*v` keeps the elements `≤ p`, the rest comes back by value.
    `split_off`'s silhouette, and the shape branch equations make writable — the body
    branches on `Leb x p` and has to produce `Le x p` from the branch it took.

    The ensures is four conjuncts, all in observation vocabulary:

        Σ (hi : List Nat).
      Σ (Hub : Ub p (*v))                       -- the kept part is ≤ p
      → Σ (Hlb : Lb p hi)                         -- the returned part is ≥ p
      → Π n. Id Nat (add (count n (*v)) (count n hi)) (count n (old *v))

    `Ub`/`Lb`/`Count`/`Add` say what a list is. Nothing here mirrors the body's own
    algorithm; every invariant is proven inductively in the body from the recursive
    call's own ensures.

    The program is take-and-rebuild, not Lomuto's array scan (the naturalness-first
    rule): take the payload, match it owned, put the tail back, recurse through the
    parameter borrow, then push the head onto whichever side its comparison chose.
    In-place by this calculus's standards — the only list cell ever allocated is
    the one `Cons` a `Cons` becomes.

    ## Quicksort

        fn quicksort [fuel] (fuel : Nat, v : &mut List Nat, Hfuel : Le (len *v) fuel)
          -> Σ (Hs : Sorted (*v)). Π n. Id Nat (count n (*v)) (count n (old *v))

    Sorted and a permutation, over the exit snapshot, and not one `back` in the call
    tree: `partition`, `append_back` and the recursive calls are each described only
    by their return type. The `Sorted` here is the structural Σ-chain, which is what
    `sigmaRec` above had to land for.

    The program: take the payload; the head is the pivot; partition the tail through
    `v`; sort the kept part in place through `v` and the returned part through a
    borrow of the local; glue with `append_back`. The sufficiency hypothesis makes
    the out-of-fuel path ⊥-dischargeable — with the two `Le` conjuncts partition
    returns supplying exactly the two `LeTransRaw`es that feed the recursive calls
    their own sufficiency.

    The one structural fact the assembly needs beyond composition is bound
    survival: `SortedAppendPivotRaw` wants `Ub x` of the sorted left part, and the
    partition bounded it before the sort. `UbPermRaw`/`LbPermRaw` (above) carry both
    bounds across their sorts' count evidence — the only place this proof is more
    than gluing.

    Staging is the dominant remaining cost, and this body is the measurement. Four
    builders (`mkCnt`, `mkUb`, `mkLb`, `fin`) exist for one reason: a proof must
    name values that later statements consume, and the body has no way to say "the
    value `rest` had" or "what `*v` held before that call". Each is applied in stages
    as its arguments become available; none of them is doing mathematical work.

    ## All three are fuel-threaded

    `partition` and `append_back` decrease through the borrow's payload, which has
    no recursor form (see `borrowDecrease` above), so both are fuel-threaded: each
    grows a `fuel : Nat` parameter and a `Le (Len *v) fuel` bound, each grows a dead
    `Z` branch discharged by `botElim`, and every caller supplies both.

    The bound needs no lemma, and that is the interesting part. At each recursive
    call the bound passes down unchanged: `Le (Len (Cons x rest)) (S f2)` is
    `Le (Len rest) f2` definitionally. And `Hf` is capital in both callees: quicksort
    hands its `hfuel` to `partition` and still needs it twice more, and a lowercase
    proof parameter would have moved it.

    `append_back`'s caller side is the one place fuel had to be invented rather than
    forwarded: quicksort calls it after sorting both halves, and a sort returns a
    count equation, not a length bound. What works is the fuel that is exactly
    enough — `Len *v` itself, with `LeReflRaw` as its bound — staged in a `let` first,
    because a comptime argument mentioning `*v` would demand-collapse the loan it
    was just lent. -/

/-! ### The cohort's telescope vocabulary

    Both fuel-threaded callees put the borrow second (the fuel is `[k]` and `[k]`
    hoists to the front), so a return type written outside a header names it
    `.var ⟨1, "v"⟩`. -/

def vfT : Term := .var ⟨1, "v"⟩
def dvfT : Term := .deref vfT
def oldvfT : Term := .app (.const "old") dvfT
def pT : Term := .var ⟨2, "p"⟩
def fuelT : Term := .var ⟨0, "fuel"⟩

/-! ### The return types

    Written out per twin rather than through a skeleton: for a spec lie the type is
    the readable content, and each of these is one line of a six-conjunct chain
    away from the honest form. Only the two telescope parameters a return type
    cannot name from outside its header are spliced. -/

def partHonest : Term := prog defer_check {
  Σ (hi : List Nat). Σ (Hub : Ub %pT (*%vfT)). Σ (Hlb : Lb %pT hi).
    Σ (Hl1 : Le (Len *%vfT) (Len (old *%vfT))). Σ0 (Hl2 : Le (Len hi) (Len (old *%vfT))).
    Π (N : Nat) → Id Nat (Add (Count N (*%vfT)) (Count N hi)) (Count N (old *%vfT)) }

def qsHonest : Term := prog defer_check {
  Σ0 (Hs : Sorted (*%vfT)). Π (N : Nat) → Id Nat (Count N (*%vfT)) (Count N (old *%vfT)) }

/-- The sufficiency hypothesis's type — a telescope entry, so it is a parameter of
    the chain too. Its twin is the one that weakens it to `Unit`. -/
def suffHonest : Term := prog defer_check { Le (Len *%vfT) %fuelT }

/-! ### The chain, once

    Three parameters vary — `partition`'s return type, `quicksort`'s, and
    `quicksort`'s sufficiency hypothesis — which is every twin in this cohort except
    the two body twins, and those cannot be shared at all: a difference inside a
    body, at a subterm naming a binder the `fn` lowering mints an id for, has no
    splice that can reach it. Both are transcribed below. -/

def qsUnder (pret qret suff tail : Term) : Term := prog{
  fn Partition [fuel] (fuel : Nat, v : &mut List Nat, p : Nat, Hf : Le (Len *v) fuel) -> %pret
      { match *v {
          -- `Ub p Nil` and `Lb p Nil` are both `Unit`, and the Count goal is
          -- `Add Z Z = Z` — the empty Partition proves itself.
          Nil => { *v := Nil;
                   Pair(Nil, Pair(unit, Pair(unit, Pair(unit, Pair(unit, λ (N : Nat). Refl))))) },
          Cons(x, rest) => match fuel {
            -- Out of fuel with a non-empty list: `Hf : Le (S (Len rest)) Z` is
            -- `Bot`, so the path is dead and the audit admits an ex-falso at any
            -- return type. Guard + sufficiency hypothesis = total correctness.
            Z => botElim Unit Hf,
            S(f2) => {
            -- Both Count steps must name `rest`, the tail as it was at entry; but
            -- `rest` is data and `*v := rest` moves it, so after the very next
            -- statement no term in the body denotes it. A body can only talk about
            -- the current exit — the same is true of any consumed parameter or
            -- binder — so the derivation is built while `rest`/`x` are still live
            -- and applied later. `Rest0` and `X0` name those snapshots explicitly,
            -- frozen here before the call consumes them.
            let Rest0 = rest;
            let X0 = x;
            let MkL = (λ (A : List Nat). λ (B : List Nat).
                        λ (H : Π (N : Nat) → Id Nat (Add (Count N A) (Count N B)) (Count N Rest0)).
                          λ (N : Nat). CountConsLRaw N X0 A B Rest0 (H N));
            let MkR = (λ (A : List Nat). λ (B : List Nat).
                        λ (H : Π (N : Nat) → Id Nat (Add (Count N A) (Count N B)) (Count N Rest0)).
                          λ (N : Nat). CountConsRRaw N X0 A B Rest0 (H N));
            -- The lengths need no staged lambda: `Len rest` is a Nat, so naming the
            -- computed value once, while `rest` is live, is enough. (The counts
            -- cannot do this — `Count n rest` is a family over `n`, and it is the
            -- list the lemma needs, not any one of its counts.)
            let lr = Len rest;
            *v := rest;
            -- The bound goes with the call, unchanged: `Le (Len (Cons x rest)) (S f2)`
            -- already is `Le (Len rest) f2`.
            let Pair(hi, Pair(Hub, Pair(Hlb, Pair(Hl1, Pair(Hl2, Hcnt))))) = Partition(f2, &m *v, p, Hf);
            -- The branch equation, in its first real use. `e` is the only reason
            -- either arm can build its bound: the split abstracted `Leb σ_x σ_p`
            -- away, so `LebTrueLeRaw x p Refl` is rejected here and `LebTrueLeRaw x p e`
            -- is not.
            if e : Leb x p {
              -- x ≤ p: the head belongs to the kept part. Derive both proofs
              -- before the write, which consumes `lo` and `x`.
              let lo = *v;
              let Hub2 = Pair(LebTrueLeRaw x p e, Hub);
              let Hl2b = LeUpRRaw (Len hi) lr Hl2;
              let Cnt = MkL lo hi Hcnt;
              *v := Cons(x, lo);
              Pair(hi, Pair(Hub2, Pair(Hlb, Pair(Hl1, Pair(Hl2b, Cnt)))))
            } else {
              -- x > p: the head belongs to the returned part. `*v` is untouched,
              -- so `hub` passes straight through.
              let Hlb2 = Pair(LePredLRaw p x (LebFalseGtRaw x p e), Hlb);
              let Hl1b = LeUpRRaw (Len *v) lr Hl1;
              let Cnt = MkR (*v) hi Hcnt;
              Pair(Cons(x, hi), Pair(Hub, Pair(Hlb2, Pair(Hl1b, Pair(Hl2, Cnt)))))
            }
          } }
        } };
  -- `AppendBack(v, w)`: walk to the end of `*v`, put `w` there. The exit reading is
  -- `Append (old *v) w` — the whole postcondition, and the whole description. Its
  -- return type is written inline, because nothing lies about it: no twin needs it
  -- spliced, and inside the header `v` and `w` are the names the programmer wrote.
  fn AppendBack [fuel] (fuel : Nat, v : &mut List Nat, w : List Nat, Hf : Le (Len *v) fuel)
      -> Id (List Nat) (*v) (Append (old *v) w)
      { match v {
          Nil => { *v := w; Refl },
          -- The congruence needs to name its right endpoint, `Append (old *tl) w`,
          -- but the recursive call has by then moved `w` (it is data, so no
          -- copy-on-read). Staging the endpoint as a runtime `let` while `w` is
          -- still live avoids this: a body can name any parameter's entry value
          -- without owning it in the return type, but not yet in the body itself,
          -- so the value has to be captured before it is consumed.
          Cons(hd, tl) => match fuel {
            Z => botElim Unit Hf,
            S(f2) => {
              let y = Append (*tl) w;
              let h = AppendBack(f2, &m *tl, w, Hf);
              let H0 = *hd;
              IdCongrRaw (List Nat) (List Nat) (λ (A : List Nat). Cons H0 A) (*tl) y h
            }
          }
      } };
  fn Quicksort [fuel] (fuel : Nat, v : &mut List Nat, Hfuel : %suff) -> %qret
      { match *v {
          Nil => { *v := Nil; Pair(unit, λ (N : Nat). Refl) },
          Cons(x, rest) => match fuel {
            -- Out of fuel with a non-empty list: `hfuel : Le (S (Len rest)) Z` is
            -- `Bot`, so the path is dead and the audit admits an ex-falso at any
            -- return type. Guard + sufficiency hypothesis = total correctness.
            Z => botElim Unit Hfuel,
            S(f2) => {
              let lr = Len rest;
              -- The count chain, staged whole while `rest` is still nameable. Its
              -- later arguments are the two parts before sorting (a, b) with the
              -- partition's own Count evidence, then the same two after sorting
              -- (a2, b2) with each sort's evidence, then the glued exit and
              -- `AppendBack`'s evidence. Read it as: rewrite the exit into an
              -- append, split the append's Count, move both parts back across
              -- their sorts, and land on the partition's equation.
              -- `Rest0` is the tail as it is here — before `*v := rest` hands it
              -- over — named explicitly so the closure below can cite it.
              let Rest0 = rest;
              let X0 = x;
              let MkCnt = (λ (A : List Nat). λ (B : List Nat).
                  λ (Hp : Π (N : Nat) → Id Nat (Add (Count N A) (Count N B)) (Count N Rest0)).
                  λ (A2 : List Nat). λ (B2 : List Nat).
                  λ (H1 : Π (N : Nat) → Id Nat (Count N A2) (Count N A)).
                  λ (H2 : Π (N : Nat) → Id Nat (Count N B2) (Count N B)).
                  λ (E : List Nat). λ (Hap : Id (List Nat) E (Append A2 (Cons X0 B2))).
                    λ (N : Nat).
                      IdTransRaw Nat (Count N E) (Add (Count N A2) (Count N (Cons X0 B2)))
                                   (Count N (Cons X0 Rest0))
                        (IdTransRaw Nat (Count N E) (Count N (Append A2 (Cons X0 B2)))
                                      (Add (Count N A2) (Count N (Cons X0 B2)))
                           (IdCongrRaw (List Nat) Nat (λ (Z0 : List Nat). Count N Z0)
                              E (Append A2 (Cons X0 B2)) Hap)
                           (CountAppendRaw N A2 (Cons X0 B2)))
                        (IdTransRaw Nat (Add (Count N A2) (Count N (Cons X0 B2)))
                                      (Add (Count N A) (Count N (Cons X0 B)))
                                      (Count N (Cons X0 Rest0))
                           (IdTransRaw Nat (Add (Count N A2) (Count N (Cons X0 B2)))
                                         (Add (Count N A) (Count N (Cons X0 B2)))
                                         (Add (Count N A) (Count N (Cons X0 B)))
                              (IdCongrRaw Nat Nat (λ (R : Nat). Add R (Count N (Cons X0 B2)))
                                 (Count N A2) (Count N A) (H1 N))
                              (IdCongrRaw Nat Nat (λ (R : Nat). Add (Count N A) R)
                                 (Count N (Cons X0 B2)) (Count N (Cons X0 B))
                                 (CountConsCongrRaw N X0 B2 B (H2 N))))
                           (CountConsRRaw N X0 A B Rest0 (Hp N))));
              *v := rest;
              -- The fuel and the bound go with the call, and the bound is `hfuel`
              -- unchanged — after `*v := rest` the callee wants `Le (Len rest) f2`,
              -- which is what it already is. It survives the call because
              -- `Partition`'s `Hf` is capital.
              let Pair(hi, Pair(Hub, Pair(Hlb, Pair(Hl1, Pair(Hl2, Hpc))))) = Partition(f2, &m *v, x, Hfuel);
              -- Both bounds are about to be invalidated as values (the sorts
              -- replace both lists), so their transports are staged now, while the
              -- pre-sort lists are still nameable. `V0` and `Hi0` name the two
              -- parts as they are here, before either sort replaces them.
              let V0 = *v;
              let Hi0 = hi;
              let Hub0 = Hub;
              let Hlb0 = Hlb;
              let MkUb = (λ (A2 : List Nat).
                  λ (H1 : Π (N : Nat) → Id Nat (Count N A2) (Count N V0)).
                    UbPermRaw X0 A2 V0 H1 Hub0);
              let MkLb = (λ (B2 : List Nat).
                  λ (H2 : Π (N : Nat) → Id Nat (Count N B2) (Count N Hi0)).
                    LbPermRaw X0 B2 Hi0 H2 Hlb0);
              let Cnt1 = MkCnt (*v) hi Hpc;
              -- Sort the kept part in place. Its sufficiency is the partition's
              -- length conjunct composed with this frame's.
              let Hf1 = LeTransRaw (Len *v) lr f2 Hl1 Hfuel;
              let Pair(Hs1, Hc1) = Quicksort(f2, &m *v, Hf1);
              -- …and the returned part, through a borrow of the local that
              -- holds it. Nothing about it is in `*v`; it is an ordinary value.
              let Hf2 = LeTransRaw (Len hi) lr f2 Hl2 Hfuel;
              let Pair(Hs2, Hc2) = Quicksort(f2, &m hi, Hf2);
              let hub2 = MkUb (*v) Hc1;
              let hlb2 = MkLb hi Hc2;
              let Cnt2 = Cnt1 (*v) hi Hc1 Hc2;
              -- The last staged builder: the glue's evidence arrives only from
              -- `AppendBack`, by which time both parts are consumed. `V1`/`Hi1`
              -- name the post-sort snapshots explicitly — different values from
              -- `V0`/`Hi0` above, since both sorts wrote in place.
              let V1 = *v;
              let Hi1 = hi;
              let Hub2 = hub2;
              let Hlb2 = hlb2;
              let Fin = (λ (E : List Nat).
                  λ (Hap : Id (List Nat) E (Append V1 (Cons X0 Hi1))).
                    ListRwRaw (λ (Z0 : List Nat). Sorted Z0) (Append V1 (Cons X0 Hi1)) E
                      (IdSymRaw (List Nat) E (Append V1 (Cons X0 Hi1)) Hap)
                      (SortedAppendPivotRaw X0 V1 Hi1 Hs1 Hub2 Hs2 Hlb2));
              let w = Cons(x, hi);
              -- The fuel that is exactly enough, staged BEFORE the borrow is
              -- taken: a comptime argument mentioning `*v` would demand-
              -- collapse the loan it was just lent.
              let lv = Len *v;
              let happ = AppendBack(lv, &m *v, w, LeReflRaw lv);
              Pair(Fin (*v) happ, Cnt2 (*v) happ)
            }
          }
        } };
  %tail }

/-- The in-place quicksort — `Sorted` and the permutation count equation over the
    exit snapshot, no declared `back` anywhere in the call tree — checks as one
    program, against no table at all. -/
def flagship : Term := qsUnder partHonest qsHonest suffHonest .unit
example : progOk flagship = true := by native_decide

/-! ### Not vacuous: `partition`'s four spec lies

    The return type is the only description of this function, so each conjunct gets
    a twin that changes exactly it. The body and the telescope are the chain's, so
    the lie is the only variable. -/

-- (1) Upper bound on the wrong snapshot: `Ub p (old *v)` — true of the entry, and
-- the entry is not what the caller gets back.
example : progRejects (qsUnder (prog defer_check {
    Σ (hi : List Nat). Σ (Hub : Ub %pT (old *%vfT)). Σ (Hlb : Lb %pT hi).
      Σ (Hl1 : Le (Len *%vfT) (Len (old *%vfT))). Σ0 (Hl2 : Le (Len hi) (Len (old *%vfT))).
      Π (N : Nat) → Id Nat (Add (Count N (*%vfT)) (Count N hi)) (Count N (old *%vfT)) })
    qsHonest suffHonest .unit) "does not have return type" = true := by native_decide

-- (2) Lower bound on the kept part instead of the returned one.
example : progRejects (qsUnder (prog defer_check {
    Σ (hi : List Nat). Σ (Hub : Ub %pT (*%vfT)). Σ (Hlb : Lb %pT (*%vfT)).
      Σ (Hl1 : Le (Len *%vfT) (Len (old *%vfT))). Σ0 (Hl2 : Le (Len hi) (Len (old *%vfT))).
      Π (N : Nat) → Id Nat (Add (Count N (*%vfT)) (Count N hi)) (Count N (old *%vfT)) })
    qsHonest suffHonest .unit) "does not have return type" = true := by native_decide

-- (3) The returned part dropped from the count: "everything stayed in `*v`". With
-- `Cnt` capital, the count proof is comptime knowledge and the lie is caught where
-- it is written — at this body's own return, by the audit.
example : progRejects (qsUnder (prog defer_check {
    Σ (hi : List Nat). Σ (Hub : Ub %pT (*%vfT)). Σ (Hlb : Lb %pT hi).
      Σ (Hl1 : Le (Len *%vfT) (Len (old *%vfT))). Σ0 (Hl2 : Le (Len hi) (Len (old *%vfT))).
      Π (N : Nat) → Id Nat (Count N (*%vfT)) (Count N (old *%vfT)) })
    qsHonest suffHonest .unit) "does not have return type" = true := by native_decide

-- (4) …and the count off by one, which no `Nil`-path argument can reach.
example : progRejects (qsUnder (prog defer_check {
    Σ (hi : List Nat). Σ (Hub : Ub %pT (*%vfT)). Σ (Hlb : Lb %pT hi).
      Σ (Hl1 : Le (Len *%vfT) (Len (old *%vfT))). Σ0 (Hl2 : Le (Len hi) (Len (old *%vfT))).
      Π (N : Nat) → Id Nat (Add (Count N (*%vfT)) (Count N hi)) (S (Count N (old *%vfT))) })
    qsHonest suffHonest .unit) "does not have return type" = true := by native_decide

/-! ### Not vacuous: `quicksort`'s two spec lies, and the sufficiency hypothesis

    Every twin here is chosen to survive the `Nil` path and die on the recursive
    one — refuting it only at `Nil` would have left the whole assembly untested. -/

-- (1) Sortedness lied onto the wrong subject: the entry is claimed sorted. True at
-- `Nil` (so the base path still passes) and false for any unsorted input, and the
-- body's evidence is about the exit.
example : progRejects (qsUnder partHonest (prog defer_check {
    Σ0 (Hs : Sorted (old *%vfT)). Π (N : Nat) → Id Nat (Count N (*%vfT)) (Count N (old *%vfT)) })
    suffHonest .unit) "does not have return type" = true := by native_decide

-- (2) Permutation lied by direction: the two endpoints swapped. Again `Refl` at
-- `Nil`, and again the body's evidence points the other way once anything moves.
example : progRejects (qsUnder partHonest (prog defer_check {
    Σ0 (Hs : Sorted (*%vfT)). Π (N : Nat) → Id Nat (Count N (old *%vfT)) (Count N (*%vfT)) })
    suffHonest .unit) "does not have its parameter type" = true := by native_decide

-- (3) The sufficiency hypothesis is load-bearing, not decoration. Keep the
-- parameter (so the body still elaborates and the rejection is about typing, not an
-- unbound name) and weaken it to `Unit`: the `Z` branch's `botElim` then has no ⊥
-- to eliminate, and the out-of-fuel path stops being dead. This is what makes the
-- guard-plus-hypothesis pair total correctness rather than partial.
example : progRejects (qsUnder partHonest qsHonest (prog defer_check { Unit }) .unit)
  "botElim result on a non-⊥ argument" = true := by native_decide

/-! ### The two body twins, transcribed

    A spec lie is refutable somewhere the `Nil` path can be blamed for; these two are
    wrong only on the recursive path, which is what makes them the twins that test
    the recursion. Both are written out in full rather than shared through the chain:
    what varies is a subterm inside a body naming a binder the `fn` lowering mints an
    id for, and a `%` splice is a Lean `Term` written outside the macro — it has no
    way to say "the `hub` this match will bind". Each carries only what it needs: the
    count lie needs no quicksort at all, and the bound lie needs the whole cohort. -/

/-- `partitionLoses`: the `≤ p` head is dropped instead of being pushed back onto the
    kept part — one write changed, `*v := lo` for `*v := Cons(x, lo)`. Wrong only on
    the recursive `True` path and only in the count conjunct; the bounds still hold
    of a list with one element missing. -/
def partitionLoses : Term := prog defer_check {
  fn Partition [fuel] (fuel : Nat, v : &mut List Nat, p : Nat, Hf : Le (Len *v) fuel) -> %partHonest
      { match *v {
          Nil => { *v := Nil;
                   Pair(Nil, Pair(unit, Pair(unit, Pair(unit, Pair(unit, λ (N : Nat). Refl))))) },
          Cons(x, rest) => match fuel {
            Z => botElim Unit Hf,
            S(f2) => {
            -- `Rest0` and `X0` name the snapshots this derivation needs before the
            -- call below consumes them.
            let Rest0 = rest;
            let X0 = x;
            let MkL = (λ (A : List Nat). λ (B : List Nat).
                        λ (H : Π (N : Nat) → Id Nat (Add (Count N A) (Count N B)) (Count N Rest0)).
                          λ (N : Nat). CountConsLRaw N X0 A B Rest0 (H N));
            let MkR = (λ (A : List Nat). λ (B : List Nat).
                        λ (H : Π (N : Nat) → Id Nat (Add (Count N A) (Count N B)) (Count N Rest0)).
                          λ (N : Nat). CountConsRRaw N X0 A B Rest0 (H N));
            let lr = Len rest;
            *v := rest;
            let Pair(hi, Pair(Hub, Pair(Hlb, Pair(Hl1, Pair(Hl2, Hcnt))))) = Partition(f2, &m *v, p, Hf);
            if e : Leb x p {
              let lo = *v;
              let Hub2 = Pair(LebTrueLeRaw x p e, Hub);
              let Hl2b = LeUpRRaw (Len hi) lr Hl2;
              let Cnt = MkL lo hi Hcnt;
              -- The lie, and the only line that differs: the head is dropped.
              *v := lo;
              Pair(hi, Pair(Hub2, Pair(Hlb, Pair(Hl1, Pair(Hl2b, Cnt)))))
            } else {
              let Hlb2 = Pair(LePredLRaw p x (LebFalseGtRaw x p e), Hlb);
              let Hl1b = LeUpRRaw (Len *v) lr Hl1;
              let Cnt = MkR (*v) hi Hcnt;
              Pair(Cons(x, hi), Pair(Hub, Pair(Hlb2, Pair(Hl1b, Pair(Hl2, Cnt)))))
            }
          } }
        } };
  () }
example : progRejects partitionLoses "does not have return type" = true := by native_decide

/-- `qsStaleBound`: the keystone is fed the bounds the partition established, on the
    parts as they were before their recursive sorts, instead of `UbPermRaw`/`LbPermRaw`'s
    transports of them — `SortedAppendPivotRaw x (*v) hi Hs1 Hub Hs2 Hlb` for
    `… Hub2 … Hlb2`. Everything else is the chain's `quicksort` verbatim, so what the
    rejection isolates is exactly bound survival. -/
def qsStaleBound : Term := prog defer_check {
  fn Partition [fuel] (fuel : Nat, v : &mut List Nat, p : Nat, Hf : Le (Len *v) fuel) -> %partHonest
      { match *v {
          Nil => { *v := Nil;
                   Pair(Nil, Pair(unit, Pair(unit, Pair(unit, Pair(unit, λ (N : Nat). Refl))))) },
          Cons(x, rest) => match fuel {
            Z => botElim Unit Hf,
            S(f2) => {
            -- `Rest0` and `X0` name the snapshots this derivation needs before the
            -- call below consumes them.
            let Rest0 = rest;
            let X0 = x;
            let MkL = (λ (A : List Nat). λ (B : List Nat).
                        λ (H : Π (N : Nat) → Id Nat (Add (Count N A) (Count N B)) (Count N Rest0)).
                          λ (N : Nat). CountConsLRaw N X0 A B Rest0 (H N));
            let MkR = (λ (A : List Nat). λ (B : List Nat).
                        λ (H : Π (N : Nat) → Id Nat (Add (Count N A) (Count N B)) (Count N Rest0)).
                          λ (N : Nat). CountConsRRaw N X0 A B Rest0 (H N));
            let lr = Len rest;
            *v := rest;
            let Pair(hi, Pair(Hub, Pair(Hlb, Pair(Hl1, Pair(Hl2, Hcnt))))) = Partition(f2, &m *v, p, Hf);
            if e : Leb x p {
              let lo = *v;
              let Hub2 = Pair(LebTrueLeRaw x p e, Hub);
              let Hl2b = LeUpRRaw (Len hi) lr Hl2;
              let Cnt = MkL lo hi Hcnt;
              *v := Cons(x, lo);
              Pair(hi, Pair(Hub2, Pair(Hlb, Pair(Hl1, Pair(Hl2b, Cnt)))))
            } else {
              let Hlb2 = Pair(LePredLRaw p x (LebFalseGtRaw x p e), Hlb);
              let Hl1b = LeUpRRaw (Len *v) lr Hl1;
              let Cnt = MkR (*v) hi Hcnt;
              Pair(Cons(x, hi), Pair(Hub, Pair(Hlb2, Pair(Hl1b, Pair(Hl2, Cnt)))))
            }
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
              IdCongrRaw (List Nat) (List Nat) (λ (A : List Nat). Cons H0 A) (*tl) y h
            }
          }
      } };
  fn Quicksort [fuel] (fuel : Nat, v : &mut List Nat, Hfuel : %suffHonest) -> %qsHonest
      { match *v {
          Nil => { *v := Nil; Pair(unit, λ (N : Nat). Refl) },
          Cons(x, rest) => match fuel {
            Z => botElim Unit Hfuel,
            S(f2) => {
              let lr = Len rest;
              -- `Rest0` is the tail as it is here — before `*v := rest` hands it
              -- over — named explicitly so the closure below can cite it.
              let Rest0 = rest;
              let X0 = x;
              let MkCnt = (λ (A : List Nat). λ (B : List Nat).
                  λ (Hp : Π (N : Nat) → Id Nat (Add (Count N A) (Count N B)) (Count N Rest0)).
                  λ (A2 : List Nat). λ (B2 : List Nat).
                  λ (H1 : Π (N : Nat) → Id Nat (Count N A2) (Count N A)).
                  λ (H2 : Π (N : Nat) → Id Nat (Count N B2) (Count N B)).
                  λ (E : List Nat). λ (Hap : Id (List Nat) E (Append A2 (Cons X0 B2))).
                    λ (N : Nat).
                      IdTransRaw Nat (Count N E) (Add (Count N A2) (Count N (Cons X0 B2)))
                                   (Count N (Cons X0 Rest0))
                        (IdTransRaw Nat (Count N E) (Count N (Append A2 (Cons X0 B2)))
                                      (Add (Count N A2) (Count N (Cons X0 B2)))
                           (IdCongrRaw (List Nat) Nat (λ (Z0 : List Nat). Count N Z0)
                              E (Append A2 (Cons X0 B2)) Hap)
                           (CountAppendRaw N A2 (Cons X0 B2)))
                        (IdTransRaw Nat (Add (Count N A2) (Count N (Cons X0 B2)))
                                      (Add (Count N A) (Count N (Cons X0 B)))
                                      (Count N (Cons X0 Rest0))
                           (IdTransRaw Nat (Add (Count N A2) (Count N (Cons X0 B2)))
                                         (Add (Count N A) (Count N (Cons X0 B2)))
                                         (Add (Count N A) (Count N (Cons X0 B)))
                              (IdCongrRaw Nat Nat (λ (R : Nat). Add R (Count N (Cons X0 B2)))
                                 (Count N A2) (Count N A) (H1 N))
                              (IdCongrRaw Nat Nat (λ (R : Nat). Add (Count N A) R)
                                 (Count N (Cons X0 B2)) (Count N (Cons X0 B))
                                 (CountConsCongrRaw N X0 B2 B (H2 N))))
                           (CountConsRRaw N X0 A B Rest0 (Hp N))));
              *v := rest;
              let Pair(hi, Pair(Hub, Pair(Hlb, Pair(Hl1, Pair(Hl2, Hpc))))) = Partition(f2, &m *v, x, Hfuel);
              -- `V0`/`Hi0` name the two parts as they are here, before either sort
              -- replaces them.
              let V0 = *v;
              let Hi0 = hi;
              let Hub0 = Hub;
              let Hlb0 = Hlb;
              let MkUb = (λ (A2 : List Nat).
                  λ (H1 : Π (N : Nat) → Id Nat (Count N A2) (Count N V0)).
                    UbPermRaw X0 A2 V0 H1 Hub0);
              let MkLb = (λ (B2 : List Nat).
                  λ (H2 : Π (N : Nat) → Id Nat (Count N B2) (Count N Hi0)).
                    LbPermRaw X0 B2 Hi0 H2 Hlb0);
              let Cnt1 = MkCnt (*v) hi Hpc;
              let Hf1 = LeTransRaw (Len *v) lr f2 Hl1 Hfuel;
              let Pair(Hs1, Hc1) = Quicksort(f2, &m *v, Hf1);
              let Hf2 = LeTransRaw (Len hi) lr f2 Hl2 Hfuel;
              let Pair(Hs2, Hc2) = Quicksort(f2, &m hi, Hf2);
              let hub2 = MkUb (*v) Hc1;
              let hlb2 = MkLb hi Hc2;
              let Cnt2 = Cnt1 (*v) hi Hc1 Hc2;
              -- `V1`/`Hi1` name the post-sort snapshots — different values from
              -- `V0`/`Hi0` above, since both sorts wrote in place.
              let V1 = *v;
              let Hi1 = hi;
              let Fin = (λ (E : List Nat).
                  λ (Hap : Id (List Nat) E (Append V1 (Cons X0 Hi1))).
                    ListRwRaw (λ (Z0 : List Nat). Sorted Z0) (Append V1 (Cons X0 Hi1)) E
                      (IdSymRaw (List Nat) E (Append V1 (Cons X0 Hi1)) Hap)
                      -- The lie, and the only line that differs: the pre-sort
                      -- bounds (`Hub0`/`Hlb0`), not their transports across the
                      -- sorts (`Hub2`/`Hlb2`).
                      (SortedAppendPivotRaw X0 V1 Hi1 Hs1 Hub0 Hs2 Hlb0));
              let w = Cons(x, hi);
              let lv = Len *v;
              let happ = AppendBack(lv, &m *v, w, LeReflRaw lv);
              Pair(Fin (*v) happ, Cnt2 (*v) happ)
            }
          }
        } };
  () }
example : progRejects qsStaleBound "does not have return type" = true := by native_decide

/-! ### The executing differentials — the bodies really partition, and really sort

    `progOk` proves the conjuncts symbolically; these run the same program on
    concrete inputs. Each rides the honest chain as its tail, so what runs is what
    was checked. `runPart` also exercises the concrete-scrutinee branch end to end:
    `if e : Leb x p` on a closed Bool takes the `ownedSelect` path, where the
    equation is bound to `Refl`. -/

def partCallerTail (l : List Nat) (pvv : Nat) : Term := prog defer_check {
  let z = %(Std.ofList (l.map Term.nat));
  let b = &m z;
  let r = Partition(%(Term.nat l.length), b, %(Term.nat pvv), ());
  match r { Pair(hi, q) => { let y = z; () } } }
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
def qsCallerTail (l : List Nat) : Term := prog defer_check {
  let z = %(Std.ofList (l.map Term.nat));
  let b = &m z;
  Quicksort(%(Term.nat l.length), b, ());
  let y = z;
  () }
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

/-- Two self-calls in one arm, with `[f]` the second parameter — so the hoist
    permutation runs on a self-call, which a surface-minted `.callV` would have
    skipped. -/
def twoRec : Term := prog{
  fn TwoRec [f] (v : &mut List Nat, f : Nat) -> Unit
        { match f {
            Z => (),
            S(f2) => { TwoRec(&m *v, f2); TwoRec(&m *v, f2); () }
        } };
  () }
example : progOk twoRec = true := by native_decide

end Dllbc.Tests.S23Direct
end

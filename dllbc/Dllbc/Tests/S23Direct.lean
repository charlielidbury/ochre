import Dllbc.Boundary
import Dllbc.Macro
import Dllbc.Std
import Dllbc.StdLemmas
import Dllbc.PureMacro
import Dllbc.DeclMacro

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
open Dllbc.StdLemmas (le_refl le_trans le_up_r)

namespace Dllbc.Tests.S23Direct

/-- Type-check a closed term against a closed type in the pure seed (as in §18/§19). -/
def chk (tm ty : Term) : Bool :=
  match (do let v ← readC 3000 tm; let t ← readC 3000 ty; hasType 3000 v t).run (seedPure [] []) with
  | .ok r _ => r
  | .error _ _ => false

/-! ## (i.a) Non-dependent Σ: the conjunction projections

    The shape every back-less caller needs: a callee returns `Σ (h : P) → Q` — a
    conjunction certificate — and the caller projects out the conjunct it wants.
    `B` ignores its binder here, so the motive is constant and both projections are
    ordinary. This is the M22 quicksort postcondition's own shape
    (`Σ (sortedpart : SortedR …) → (Π n. Id …)`), which until now could only be
    assembled, never taken apart. -/

def and_left : Term := pure{
  λ (a : Nat). λ (b : Nat). λ (c : Nat).
    λ (p : Σ (h : Le a b) → Le b c).
      elim p return (λ (q : Σ (h : Le a b) → Le b c). Le a b) {
        Pair (x) (y) => x } }
def and_left_ty : Term := pure{
  Π (a : Nat) → Π (b : Nat) → Π (c : Nat) → (Σ (h : Le a b) → Le b c) → Le a b }
example : chk and_left and_left_ty = true := by native_decide

def and_right : Term := pure{
  λ (a : Nat). λ (b : Nat). λ (c : Nat).
    λ (p : Σ (h : Le a b) → Le b c).
      elim p return (λ (q : Σ (h : Le a b) → Le b c). Le b c) {
        Pair (x) (y) => y } }
def and_right_ty : Term := pure{
  Π (a : Nat) → Π (b : Nat) → Π (c : Nat) → (Σ (h : Le a b) → Le b c) → Le b c }
example : chk and_right and_right_ty = true := by native_decide

-- The projections COMPOSE with an ordinary lemma: destructure the conjunction and
-- feed both halves to `le_trans`. This is exactly what a caller does with a
-- returned certificate — the reason the recursor is a prerequisite for the rest of
-- M23 rather than a nicety.
def and_trans : Term := pure{
  λ (a : Nat). λ (b : Nat). λ (c : Nat).
    λ (p : Σ (h : Le a b) → Le b c).
      elim p return (λ (q : Σ (h : Le a b) → Le b c). Le a c) {
        Pair (x) (y) => le_trans a b c x y } }
def and_trans_ty : Term := pure{
  Π (a : Nat) → Π (b : Nat) → Π (c : Nat) → (Σ (h : Le a b) → Le b c) → Le a c }
example : chk and_trans and_trans_ty = true := by native_decide

/-! ## (i.b) Dependent Σ: the second projection needs a dependent motive

    When `B` mentions its binder, `snd`'s type mentions `fst p` — so the motive is
    `λ q. Le (S Z) (sfst q)`, and the arm type-checks only because the ι-rule fires
    *inside the type*: `sfst (Pair x y)` reduces to `x`. This is dependent Σ
    elimination proper, not a pair of independent projections. -/

def sfst : Term := pure{
  λ (p : Σ (n : Nat) → Le (S Z) n).
    elim p return (λ (q : Σ (n : Nat) → Le (S Z) n). Nat) {
      Pair (x) (y) => x } }
def sfst_ty : Term := pure{ (Σ (n : Nat) → Le (S Z) n) → Nat }
example : chk sfst sfst_ty = true := by native_decide

def ssnd : Term := pure{
  λ (p : Σ (n : Nat) → Le (S Z) n).
    elim p return (λ (q : Σ (n : Nat) → Le (S Z) n). Le (S Z) (sfst q)) {
      Pair (x) (y) => y } }
def ssnd_ty : Term := pure{ Π (p : Σ (n : Nat) → Le (S Z) n) → Le (S Z) (sfst p) }
example : chk ssnd ssnd_ty = true := by native_decide

/-! ## (i.c) The ι-rule computes -/

-- `sfst (Pair 2 (le_refl 2)) ⇝ 2`, by ι on a concrete Pair.
def pv (t : Term) : Val := Val.nfV 4000 (Val.Term.toValPure t)
def vnat : Nat → Val | 0 => .ctor "Z" [] | k + 1 => .ctor "S" [vnat k]
def sfstApp : Term := pure{ sfst (Pair (S (S Z)) (le_refl (S (S Z)))) }
example : (pv sfstApp == vnat 2) = true := by native_decide

-- ι fires under binders on a Pair whose COMPONENTS are neutral — the case that
-- matters, since a caller destructures a certificate about symbolic values, never
-- a closed one: `λ n. λ h. sfst (Pair n h)` normalizes to `λ n. λ h. n`.
example : (pv (pure{ λ (n : Nat). λ (h : Le (S Z) n). sfst (Pair n h) }) ==
           pv (pure{ λ (n : Nat). λ (h : Le (S Z) n). n })) = true := by native_decide

-- The dual: a neutral TARGET has no `Pair` to fire on, so the spine is a legal
-- stuck value rather than an error — which is what lets `ssnd`'s motive above
-- mention `sfst q` for a symbolic `q` and still be judged.

/-! ## (i.d) Negative controls — one per rule branch

    The typing rule has three premises that can fail (`f`, the target, and the
    result convert) plus the ι-rule's shape condition; each gets a test, per the
    M20 lesson (a negative test per RULE BRANCH, not per feature). -/

-- (1) Wrong arm component: `Pair(x)(y) => y` at the FIRST projection's type. The
-- arm must inhabit `P (Pair x y)`, which is `Le a b` — `y : Le b c` does not.
def and_left_lie : Term := pure{
  λ (a : Nat). λ (b : Nat). λ (c : Nat).
    λ (p : Σ (h : Le a b) → Le b c).
      elim p return (λ (q : Σ (h : Le a b) → Le b c). Le a b) {
        Pair (x) (y) => y } }
example : chk and_left_lie and_left_ty = false := by native_decide

-- (2) Wrong RESULT type: `sfst` returns `Nat`, and the claim is that it returns a
-- proof. `finish` converts the motive-at-target against the ascribed type; this is
-- the branch that catches it.
def sfst_lie_ty : Term := pure{ (Σ (n : Nat) → Le (S Z) n) → Le Z Z }
example : chk sfst sfst_lie_ty = false := by native_decide

-- (3) Wrong DEPENDENT motive: the second projection claimed one bigger than the
-- first component. `y : Le (S Z) x`, but `P (Pair x y)` is now `Le (S Z) (S x)` —
-- off by one, and nothing bridges it. This is the branch that would silently pass
-- if the motive were inferred from the arm rather than read off what is written.
def ssnd_lie : Term := pure{
  λ (p : Σ (n : Nat) → Le (S Z) n).
    elim p return (λ (q : Σ (n : Nat) → Le (S Z) n). Le (S Z) (S (sfst q))) {
      Pair (x) (y) => y } }
def ssnd_lie_ty : Term := pure{ Π (p : Σ (n : Nat) → Le (S Z) n) → Le (S Z) (S (sfst p)) }
example : chk ssnd_lie ssnd_lie_ty = false := by native_decide

-- (4) Wrong TARGET: `sigmaRec` applied to something that is not of the Σ type it
-- declares. Here the target is a bare `Nat`, so the `s : Σ (x : A) → B x` premise
-- fails even though the arm is fine.
def sfst_bad_target : Term := pure{ sfst (S Z) }
def sfst_bad_target_ty : Term := pure{ Nat }
example : chk sfst_bad_target sfst_bad_target_ty = false := by native_decide

/-! ## Stage (ii) prelude: DEPENDENT Σ results at a call site

    Building certificates is half of it; the other half is that a *caller* can
    receive one. A back-less callee's returned evidence is pinned to its own
    result — `Σ (r : List Nat) → Id (List Nat) r (drop i (old *v))` is split_off's
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
def pinOne : Decl := decl{ fn pinOne () -> Σ (r : Nat) → Id Nat r (S Z) { Pair(S Z, Refl) } }
def useIt : Decl := decl{ fn useIt (n : Nat, h : Id Nat n (S Z)) -> Unit { () } }
example : checkFnOk pinOne = true := by native_decide
example : checkFnOk useIt = true := by native_decide

-- The caller destructures the returned pair and feeds BOTH halves onward: `h`'s
-- type is `Id σa (S Z)` for the very σa bound to `a`. This is the caller-side
-- shape every back-less callee in the rest of M23 depends on.
def usePin : Decl :=
  decl{ fn usePin () -> Unit
        { let p = pinOne();
          match p { Pair(a, h) => { useIt(a, h); () } } } }
example : checkFnOk usePin [pinOne, useIt, usePin] = true := by native_decide

-- Not vacuous (a): the pin says `S Z`; a consumer wanting `S (S Z)` is rejected —
-- so the threaded type is the callee's actual claim, not a rubber stamp.
def useItLie : Decl := decl{ fn useItLie (n : Nat, h : Id Nat n (S (S Z))) -> Unit { () } }
def usePinLie : Decl :=
  decl{ fn usePinLie () -> Unit
        { let p = pinOne();
          match p { Pair(a, h) => { useItLie(a, h); () } } } }
example : checkFnErr usePinLie "does not have its parameter type" [pinOne, useItLie, usePinLie] = true := by native_decide

-- Not vacuous (b): drop the pin (a plain `Nat` result) and the caller learns
-- NOTHING about the value it got back — `Refl` cannot inhabit `Id σa (S Z)`. The
-- pin is what carries the knowledge across the boundary, which is the whole
-- premise of removing declared backs.
def plainOne : Decl := decl{ fn plainOne () -> Nat { S Z } }
def useUnpinned : Decl :=
  decl{ fn useUnpinned () -> Unit { let a = plainOne(); useIt(a, Refl); () } }
example : checkFnErr useUnpinned "does not have its parameter type" [plainOne, useIt, useUnpinned] = true := by native_decide

/-! ## Stage (v): recursion = self-ensures under §8's snapshot-subterm guard

    A call is checked against a signature alone (§5.3) — recursion forces that — so
    a SELF-call is admitted at the function's own declared return type. Through M22
    that return type was `Unit` for every recursive Decl, and the real content lived
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
def recGood : Decl :=
  decl{ fn recGood [n] (n : Nat) -> Id Nat Z Z
        { match n { Z => Refl, S(m) => recGood(m) } } }
example : checkFnOk recGood = true := by native_decide

-- BRANCH 1 — no `[k]` at all. THE headline control: this exact Decl was accepted
-- before the guard, and it proves `Z = S Z`.
def recBad : Decl := decl{ fn recBad () -> Id Nat Z (S Z) { recBad() } }
example : checkFnErr recBad "declares no decreasing argument" = true := by native_decide

-- BRANCH 2 — `[k]` declared, but the self-call passes the SAME fuel. Equal is not
-- strictly smaller; this is the shape the strictness in `strictSubterm` exists for.
def recSame : Decl := decl{ fn recSame [n] (n : Nat) -> Id Nat Z (S Z) { recSame(n) } }
example : checkFnErr recSame "not a strict structural predecessor" = true := by native_decide

-- BRANCH 3 — decrease at the WRONG index. The return type here is TRUE, so the
-- audit cannot be what rejects it: `[n]` is declared while `m` is what shrinks.
-- (Without this control the previous two would pass on a guard that merely
-- required *something* to decrease — which is unsound, since alternating branches
-- can each decrease a different coordinate forever.)
def recWrongIdx : Decl :=
  decl{ fn recWrongIdx [n] (n : Nat, m : Nat) -> Id Nat Z Z
        { match m { Z => Refl, S(m2) => recWrongIdx(n, m2) } } }
example : checkFnErr recWrongIdx "not a strict structural predecessor" = true := by native_decide

-- …and the same body with the honest index declared is accepted, so branch 3 is
-- about the index, not about the body.
def recRightIdx : Decl :=
  decl{ fn recRightIdx [m] (n : Nat, m : Nat) -> Id Nat Z Z
        { match m { Z => Refl, S(m2) => recRightIdx(n, m2) } } }
example : checkFnOk recRightIdx = true := by native_decide

-- BRANCH 4 — an INCREASE reads as "not a subterm", not as a decrease: `S(m2)`
-- against a snapshot of `S m2` is equality one level up, and equality never passes.
def recGrow : Decl :=
  decl{ fn recGrow [n] (n : Nat) -> Id Nat Z Z
        { match n { Z => Refl, S(m2) => recGrow(S(m2)) } } }
example : checkFnErr recGrow "not a strict structural predecessor" = true := by native_decide

-- BRANCH 5 — MUTUAL recursion. The guard is per-declaration, so `f → g → f` would
-- let each admit the other's postcondition with nothing decreasing anywhere: the
-- same hole through two doors. Rejected outright (§8's measures are where a general
-- story would live).
def recMutA : Decl := decl{ fn recMutA () -> Id Nat Z (S Z) { recMutB() } }
def recMutB : Decl := decl{ fn recMutB () -> Id Nat Z (S Z) { recMutA() } }
example : checkFnErr recMutA "mutual recursion" [recMutA, recMutB] = true := by native_decide

-- The guard is STRUCTURAL, not Nat-specific: a list fuel decreases the same way.
def recList : Decl :=
  decl{ fn recList [l] (l : List Nat) -> Id Nat Z Z
        { match l { Nil => Refl, Cons(h, t) => recList(t) } } }
example : checkFnOk recList = true := by native_decide

-- Two constructors down is still a strict subterm (the relation is transitive, not
-- just one-step) — which the quicksort recursion needs, since it peels `cnt` twice
-- before recursing.
def recDeep : Decl :=
  decl{ fn recDeep [n] (n : Nat) -> Id Nat Z Z
        { match n { Z => Refl, S(a) => match a { Z => Refl, S(b) => recDeep(b) } } } }
example : checkFnOk recDeep = true := by native_decide

-- A BORROW parameter decreases through its payload snapshot — §8's guard in its
-- most literal form, and the only thing that shrinks in a list cursor: `zero_all`
-- (S6Call) passes no counter at all, just the tail reborrow. Snapshots are
-- entry-knowledge and are never rewritten by mutation (§3.2), so the payload's
-- structural decomposition is a fixed, well-founded order.
def recCursor : Decl :=
  decl{ fn recCursor [v] (v : &mut List Nat) -> Unit
        { match v { Nil => (), Cons(hd, tl) => { *hd := 0; recCursor(tl); () } } } }
example : checkFnOk recCursor = true := by native_decide

-- A NON-self call to a recursive function is untouched — the guard is about
-- self-calls, and every other call is the ordinary §5.3 signature rule.
def recCaller : Decl := decl{ fn recCaller () -> Id Nat Z Z { recGood(S Z) } }
example : checkFnOk recCaller [recGood, recCaller] = true := by native_decide

end Dllbc.Tests.S23Direct

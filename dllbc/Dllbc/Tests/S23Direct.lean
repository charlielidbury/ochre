import Dllbc.Boundary
import Dllbc.Macro
import Dllbc.Std
import Dllbc.StdLemmas
import Dllbc.PureMacro
import Dllbc.DeclMacro
import Dllbc.Tests.S9Diff

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
open Dllbc.StdLemmas (le_refl le_trans le_up_r append id_congr id_trans id_sym
  set nth swapL len_set swapL_set le_rw_r insertL Ub Lb take leb_true_le leb_false_gt
  sorted_head sorted_tail ub_head ub_tail lb_bound
  bound_append sorted_append_pivot)

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

/-! ## Stage (ii): ownership splitting — `split_off` and `append_back`

    The data plan for a back-less quicksort: recursion over WHOLE lists instead of
    `lo`/`cnt` range indices. `split_off` takes the tail at depth `i` out of a
    borrowed list and returns it BY VALUE (it cannot come back as a borrow — its
    owner is local); `append_back` walks to the end and replaces the `Nil`. Between
    them the caller owns two independent lists, sorts each, and glues.

    Both are back-less: the ONLY description of either is its return type. And both
    ensures are stated in OBSERVATION functions — `take`, `drop`, `append`, which
    define meaning independently of any implementation — not in a pure function
    mirroring the body's own algorithm, which is what a declared `back` was. That
    is the line: `Id (*v) (take i (old *v))` IS split_off's spec, not a mirror of it.

    Both check with no declared back anywhere in the call tree, and the two machine
    gaps they forced are recorded at their use sites below. -/

-- `append_back(v, w)`: walk to the end of `*v`, put `w` there. The exit reading is
-- `append (old *v) w` — the whole postcondition, and the whole description.
def appendBack : Decl :=
  decl{ fn append_back [v] (v : &mut List Nat, w : List Nat)
        -> Id (List Nat) (*v) (append (old *v) w)
        { match v {
            Nil => { *v := w; Refl },
            -- PAIN DIARY (staging, again — the M22 "proof linearity" entry's data
            -- twin). The congruence needs to NAME its right endpoint,
            -- `append (old *tl) w`, but the recursive call has by then MOVED `w`
            -- (it is data, so §2.1 gives no copy-on-read). Dodged by staging the
            -- endpoint as a runtime `let` while `w` is still live. Same dodge, new
            -- cause: M22's was a proof consumed by a mutation, this is a data
            -- argument consumed by the call the proof is about. The general fix is
            -- the same one M22 queued — `old` for consumed parameters, so a body
            -- can name any parameter's ENTRY value without owning it, which is what
            -- M12 already grants the RETURN TYPE and denies the body.
            Cons(hd, tl) => {
              let y = append (*tl) w;
              let h = append_back(&mut *tl, w);
              id_congr (List Nat) (List Nat) (λ (a : List Nat). Cons (*hd) a) (*tl) y h
            }
        } } }
example : checkFnOk appendBack = true := by native_decide

-- `split_off(v, i)`: `*v` keeps the first `i`, the rest comes back by value. The
-- returned tail is Σ-PINNED to `drop i (old *v)` — the caller's only knowledge of a
-- value it did not compute, which is why stage (ii)'s prelude above had to land
-- first.
def splitOff : Decl :=
  decl{ fn split_off [i] (v : &mut List Nat, i : Nat, hi : Le i (len *v))
        -> Σ (ret : List Nat) → Σ (h1 : Id (List Nat) (*v) (take i (old *v)))
             → Id (List Nat) ret (drop i (old *v))
        { match i {
            -- i = Z: take the whole payload out (§2.4's take-and-refill, the idiom
            -- Rust rejects with E0507) and leave `Nil`. `take Z l = Nil` and
            -- `drop Z l = l` both compute, so both conjuncts are `Refl`.
            Z => { let tail = *v; *v := Nil; Pair(tail, Pair(Refl, Refl)) },
            S(i2) => match v {
              -- `hi : Le (S i2) (len Nil)` is `Le (S i2) Z`, which IS `Bot`: the
              -- branch is dead and the audit admits an ex-falso at any type (§5.4).
              Nil => botElim Unit hi,
              Cons(hd, tl) => {
                -- `hi` passes down DEFINITIONALLY: `len (Cons _ t) = S (len t)`, so
                -- `Le (S i2) (S (len σ_tl))` already IS `Le i2 (len σ_tl)`. The M14
                -- bounds-cursor property, still holding.
                let y1 = take i2 (*tl);
                let p = split_off(&mut *tl, i2, hi);
                match p { Pair(rr, q) => match q { Pair(h1, h2) => {
                  -- The prefix conjunct needs a congruence under `Cons (*hd)`, and
                  -- reading `*tl` here — AFTER handing `&mut *tl` to the call — is
                  -- the only way to name the callee's exit. That read is what
                  -- forced the ⇝-side demand-end (Machine.lean, `collapseCDerefs`):
                  -- before it, the projection returned the parked `loanₘ` itself and
                  -- a state marker rode silently into this proof term.
                  -- The suffix conjunct needs nothing: `drop (S i2) (Cons h t)` IS
                  -- `drop i2 t`, so the callee's `h2` is already the goal.
                  let c1 = id_congr (List Nat) (List Nat) (λ (a : List Nat). Cons (*hd) a)
                             (*tl) y1 h1;
                  Pair(rr, Pair(c1, h2)) } } }
              }
            }
        } } }
example : checkFnOk splitOff = true := by native_decide

/-! ### Not vacuous: the spec twins, and the body twin

    Three spec lies (shifting either index, and swapping the two conjuncts) and one
    BODY lie. The spec lies are all caught on the `i = Z` path, so they alone would
    leave the recursive path untested; the body lie breaks the congruence in the
    `Cons` branch and is the control for that path. -/

def dvT : Term := .deref (.var ⟨0, "v"⟩)
def oldvT : Term := .app (.const "old") dvT
def listNatT : Term := .app (.const "List") (.const "Nat")
def iT : Term := .var ⟨1, "i"⟩
def sucT (t : Term) : Term := .ctorApp "S" [t]
-- SUBJECT: deliberately-wrong return types, built as raw Terms — the lie IS the test.
def soTwin (a b : Term) : Decl :=
  { splitOff with retType := .sigmaT listNatT (.sigmaT (.idT listNatT dvT a) (.idT listNatT (.pvar 1) b)) }
def splitOffLieTake : Decl := { soTwin (Std.takeT (sucT iT) oldvT) (Std.dropT iT oldvT) with name := "split_off" }
def splitOffLieDrop : Decl := { soTwin (Std.takeT iT oldvT) (Std.dropT (sucT iT) oldvT) with name := "split_off" }
def splitOffLieSwap : Decl := { soTwin (Std.dropT iT oldvT) (Std.takeT iT oldvT) with name := "split_off" }
example : checkFnErr splitOffLieTake "does not have return type" = true := by native_decide
example : checkFnErr splitOffLieDrop "does not have return type" = true := by native_decide
example : checkFnErr splitOffLieSwap "does not have return type" = true := by native_decide

-- The BODY lie: the congruence forgets to put `*hd` back on the front (identity
-- instead of `Cons (*hd) ·`), so the prefix conjunct is off by the head element.
-- Rejected on the RECURSIVE path, which no spec twin above reaches.
def splitOffLieHead : Decl :=
  decl{ fn split_off [i] (v : &mut List Nat, i : Nat, hi : Le i (len *v))
        -> Σ (ret : List Nat) → Σ (h1 : Id (List Nat) (*v) (take i (old *v)))
             → Id (List Nat) ret (drop i (old *v))
        { match i {
            Z => { let tail = *v; *v := Nil; Pair(tail, Pair(Refl, Refl)) },
            S(i2) => match v {
              Nil => botElim Unit hi,
              Cons(hd, tl) => {
                let y1 = take i2 (*tl);
                let p = split_off(&mut *tl, i2, hi);
                match p { Pair(rr, q) => match q { Pair(h1, h2) => {
                  let c1 = id_congr (List Nat) (List Nat) (λ (a : List Nat). a)
                             (*tl) y1 h1;
                  Pair(rr, Pair(c1, h2)) } } }
              }
            }
        } } }
example : checkFnErr splitOffLieHead "does not have return type" = true := by native_decide

/-! ### The executing differential — the body really splits

    checkFnOk proves the postcondition symbolically; this runs the SAME Decl on
    concrete lists and confirms `*v` keeps `take i l` while the returned value is
    `drop i l`, at the two boundaries and in the middle. -/

def tnatT : Nat → Term | 0 => .ctorApp "Z" [] | k + 1 => .ctorApp "S" [tnatT k]
def tlistT : List Nat → Term | [] => .ctorApp "Nil" [] | x :: xs => .ctorApp "Cons" [tnatT x, tlistT xs]
def vnatV : Nat → Val | 0 => .ctor "Z" [] | k + 1 => .ctor "S" [vnatV k]
def vlistV : List Nat → Val | [] => .ctor "Nil" [] | x :: xs => .ctor "Cons" [vnatV x, vlistV xs]
-- SUBJECT: the executing-mode differential's raw Term caller.
def soCaller (l : List Nat) (i : Nat) : Term :=
  .letIn ⟨0, "x"⟩ (tlistT l)
    (.letIn ⟨1, "b"⟩ (.borrow (.var ⟨0, "x"⟩))
      (.letIn ⟨2, "p"⟩ (.call "split_off" [.var ⟨1, "b"⟩, tnatT i, .unit])
        (.matchE ⟨2, "p"⟩ [.mk "Pair" [⟨3, "rr"⟩, ⟨4, "q"⟩] (.letIn ⟨5, "y"⟩ (.var ⟨0, "x"⟩) .unit)])))
def runSplit (l : List Nat) (i : Nat) : Bool :=
  match Dllbc.Tests.S9Diff.runExec [splitOff] (soCaller l i) with
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
    forward — ISSUED-PAYLOAD PINNING, then the `swapL_set` BRIDGE, then
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
    shows the second feature evaporating too — the `swapL_set` bridge M22 proved and
    parked as forward infrastructure "for the audit to cite once pinning lands" is
    just an ordinary lemma applied in the body, needing no audit machinery at all.
    Feature 3 (audit-rewrite) had three convergence points in M22's ledger; this
    removes two of them, and re-scopes pinning to "only if you insist on calling
    a cursor rather than being one". -/

-- `set_at(v, i, x)`: write `x` at position `i`, in place, through the body's own
-- field reborrows. The exit reading is `set i x (old *v)` — provable, no back.
def setAt : Decl :=
  decl{ fn set_at [i] (v : &mut List Nat, i : Nat, x : Nat, hi : Le (S i) (len *v))
        -> Id (List Nat) (*v) (set i x (old *v))
        { match i {
            -- `*hd := x` is a strong update through a match-field reborrow: the
            -- parent suspends, the audit collapses it, and the exit is `Cons x σ_tl`
            -- — which IS `set Z x (Cons σ_hd σ_tl)`, so the proof is `Refl`.
            Z => match v { Nil => botElim Unit hi, Cons(hd, tl) => { *hd := x; Refl } },
            S(i2) => match v {
              Nil => botElim Unit hi,
              Cons(hd, tl) => {
                let y = set i2 x (*tl);
                let h = set_at(&mut *tl, i2, x, hi);
                id_congr (List Nat) (List Nat) (λ (a : List Nat). Cons (*hd) a) (*tl) y h
              }
            }
        } } }
example : checkFnOk setAt = true := by native_decide

-- `swap_at(v, i, j)`: two `set_at`s and the M22 bridge, ensuring the model function
-- `swapL` directly. Not recursive itself — the recursion is `set_at`'s.
def swapAt : Decl :=
  decl{ fn swap_at (v : &mut List Nat, i : Nat, j : Nat, pij : Le (S i) j,
                    p2 : Le (S j) (len *v), hi : Le (S i) (len *v))
        -> Id (List Nat) (*v) (swapL i j (old *v))
        { let a = nth i (*v);
          let b = nth j (*v);
          -- The M22 bridge, cited as an ordinary lemma in the body. No audit
          -- feature, no pinning: `set i b (set j a s)` IS the set-form it relates.
          let bridge = swapL_set i j (old *v) pij p2;
          let h1 = set_at(&mut *v, j, a, p2);
          -- The bound tax (M21's, unchanged): the second write's bound is stated
          -- over the LIVE `*v`, which the first write replaced with an opaque σ′, so
          -- it transports back through `len_set` along h1.
          let hlen = id_trans Nat (len *v) (len (set j a (old *v))) (len (old *v))
                       (id_congr (List Nat) Nat len (*v) (set j a (old *v)) h1)
                       (len_set j a (old *v));
          let hi2 = le_rw_r (S i) (len (old *v)) (len *v)
                      (id_sym Nat (len *v) (len (old *v)) hlen) hi;
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
          let finish = (λ (e : List Nat). λ (hh : Id (List Nat) e (set i b (*v))).
                          id_trans (List Nat) e (set i b (*v)) (swapL i j (old *v))
                            hh
                            (id_trans (List Nat) (set i b (*v)) (set i b (set j a (old *v)))
                               (swapL i j (old *v))
                               (id_congr (List Nat) (List Nat) (λ (z : List Nat). set i b z)
                                 (*v) (set j a (old *v)) h1)
                               bridge));
          let h2 = set_at(&mut *v, i, b, hi2);
          finish (*v) h2 } }
example : checkFnOk swapAt [setAt, swapAt] = true := by native_decide

/-! ### Not vacuous -/

-- SUBJECT: deliberately-wrong return types (raw Terms) — the lie IS the test.
def setT (k x l : Term) : Term := .app (.app (.app Dllbc.StdLemmas.set k) x) l
def swapT (a b l : Term) : Term := .app (.app (.app Dllbc.StdLemmas.swapL a) b) l
def setAtLieIdx : Decl := { setAt with retType := .idT listNatT dvT (setT (sucT iT) (.var ⟨2, "x"⟩) oldvT) }
def setAtLieNoop : Decl := { setAt with retType := .idT listNatT dvT oldvT }
example : checkFnErr setAtLieIdx "does not have return type" = true := by native_decide
example : checkFnErr setAtLieNoop "does not have return type" = true := by native_decide

def swapAtLieIdx : Decl := { swapAt with retType := .idT listNatT dvT (swapT (sucT iT) (.var ⟨2, "j"⟩) oldvT) }
def swapAtLieNoop : Decl := { swapAt with retType := .idT listNatT dvT oldvT }
example : checkFnErr swapAtLieIdx "does not have return type" [setAt, swapAtLieIdx] = true := by native_decide
example : checkFnErr swapAtLieNoop "does not have return type" [setAt, swapAtLieNoop] = true := by native_decide

/-! ### The executing differential — the bodies really write and really swap -/

-- SUBJECT: executing-mode raw Term callers (proof arguments are placeholders `()`,
-- which the executing run does not type-check).
def setCaller (l : List Nat) (i x : Nat) : Term :=
  .letIn ⟨0, "z"⟩ (tlistT l)
    (.letIn ⟨1, "b"⟩ (.borrow (.var ⟨0, "z"⟩))
      (.seq (.call "set_at" [.var ⟨1, "b"⟩, tnatT i, tnatT x, .unit])
        (.letIn ⟨2, "y"⟩ (.var ⟨0, "z"⟩) .unit)))
def runSetAt (l : List Nat) (i x : Nat) : Bool :=
  match Dllbc.Tests.S9Diff.runExec [setAt] (setCaller l i x) with
  | .ok env => env.lookup "y" == some (vlistV (l.set i x))
  | .error _ => false

example : runSetAt [1,2,3] 0 9 = true := by native_decide
example : runSetAt [1,2,3] 2 9 = true := by native_decide
example : runSetAt [5,5,5,5] 1 7 = true := by native_decide

def swapCaller (l : List Nat) (i j : Nat) : Term :=
  .letIn ⟨0, "z"⟩ (tlistT l)
    (.letIn ⟨1, "b"⟩ (.borrow (.var ⟨0, "z"⟩))
      (.seq (.call "swap_at" [.var ⟨1, "b"⟩, tnatT i, tnatT j, .unit, .unit, .unit])
        (.letIn ⟨2, "y"⟩ (.var ⟨0, "z"⟩) .unit)))
def runSwapAt (l : List Nat) (i j : Nat) : Bool :=
  match Dllbc.Tests.S9Diff.runExec [setAt, swapAt] (swapCaller l i j) with
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

def insertAt : Decl :=
  decl{ fn insert_at [k] (v : &mut List Nat, k : Nat, x : Nat)
        -> Id (List Nat) (*v) (insertL k x (old *v))
        { match k {
            Z => { let t = *v; *v := Cons(x, t); Refl },
            S(k2) => match v {
              -- past the end, `x` lands last: `insertL (S k) x Nil = Cons x Nil`.
              Nil => { *v := Cons(x, Nil); Refl },
              Cons(hd, tl) => {
                let y = insertL k2 x (*tl);
                let h = insert_at(&mut *tl, k2, x);
                id_congr (List Nat) (List Nat) (λ (a : List Nat). Cons (*hd) a) (*tl) y h
              }
            }
        } } }
example : checkFnOk insertAt = true := by native_decide

-- SUBJECT: deliberately-wrong return types (raw Terms).
def insLT (k x l : Term) : Term := .app (.app (.app Dllbc.StdLemmas.insertL k) x) l
def insertAtLieIdx : Decl :=
  { insertAt with retType := .idT listNatT dvT (insLT (sucT (.var ⟨1, "k"⟩)) (.var ⟨2, "x"⟩) oldvT) }
def insertAtLieNoop : Decl := { insertAt with retType := .idT listNatT dvT oldvT }
example : checkFnErr insertAtLieIdx "does not have return type" = true := by native_decide
example : checkFnErr insertAtLieNoop "does not have return type" = true := by native_decide

-- `insertL` computes, including the past-the-end case the `Nil` branch implements.
def insLC (k x : Nat) (l : List Nat) : Term := insLT (tnatT k) (tnatT x) (tlistT l)
example : (pv (insLC 0 9 [1,2,3]) == vlistV [9,1,2,3]) = true := by native_decide
example : (pv (insLC 2 9 [1,2,3]) == vlistV [1,2,9,3]) = true := by native_decide
example : (pv (insLC 3 9 [1,2,3]) == vlistV [1,2,3,9]) = true := by native_decide
example : (pv (insLC 5 9 [1,2,3]) == vlistV [1,2,3,9]) = true := by native_decide
example : (pv (insLC 0 9 []) == vlistV [9]) = true := by native_decide

-- SUBJECT: executing-mode raw Term caller.
def insCaller (l : List Nat) (k x : Nat) : Term :=
  .letIn ⟨0, "z"⟩ (tlistT l)
    (.letIn ⟨1, "b"⟩ (.borrow (.var ⟨0, "z"⟩))
      (.seq (.call "insert_at" [.var ⟨1, "b"⟩, tnatT k, tnatT x])
        (.letIn ⟨2, "y"⟩ (.var ⟨0, "z"⟩) .unit)))
def runInsertAt (l : List Nat) (k x : Nat) : Bool :=
  match Dllbc.Tests.S9Diff.runExec [insertAt] (insCaller l k x) with
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
    tests. But a body that writes `leb a b` AFTER the split recomputes the spine, and
    nothing hands back the equation.

    That is exactly backwards for direct proving, where the body must PRODUCE the
    evidence rather than merely have its types agree. `Refl : Id Bool (leb a b) True`
    does not check inside the `True` branch — kept here as the negative half of the
    pair: -/

def needLe : Decl := decl{ fn needLe (a : Nat, b : Nat, h : Le a b) -> Unit { () } }
def branchKnowledge : Decl :=
  decl{ fn branchKnowledge (a : Nat, b : Nat) -> Unit
        { let c = leb a b;
          match c {
            True => { needLe(a, b, leb_true_le a b Refl); () },
            False => ()
          } } }
example : checkFnErr branchKnowledge "does not have its parameter type"
  [needLe, branchKnowledge] = true := by native_decide

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
    refinement, so nothing in the state mentions `leb a b` any more and a body that
    recomputes it is talking about a term the refinement never saw. There the
    equation is a genuine hypothesis, minted as a fresh σ typed
    `Id Bool (leb σa σb) True` — the one thing this rule adds.

    The positive twin of `branchKnowledge`: the SAME body, with the equation cited in
    place of `Refl`. The pair is the whole claim — the rule does exactly one new
    thing. -/

def branchKnowledgeEq : Decl :=
  decl{ fn branchKnowledgeEq (a : Nat, b : Nat) -> Unit
        { let c = leb a b;
          match e : c {
            True => { needLe(a, b, leb_true_le a b e); () },
            False => ()
          } } }
example : checkFnOk branchKnowledgeEq [needLe, branchKnowledgeEq] = true := by native_decide

-- Both branches, in the direction each can actually prove: `False` gives
-- `Id Bool (leb a b) False`, hence `Le (S b) a` — so the equation is per-branch,
-- not a single fact smuggled in twice.
def needGt : Decl := decl{ fn needGt (a : Nat, b : Nat, h : Le (S b) a) -> Unit { () } }
def branchKnowledgeBoth : Decl :=
  decl{ fn branchKnowledgeBoth (a : Nat, b : Nat) -> Unit
        { let c = leb a b;
          match e : c {
            True => { needLe(a, b, leb_true_le a b e); () },
            False => { needGt(a, b, leb_false_gt a b e); () }
          } } }
example : checkFnOk branchKnowledgeBoth [needLe, needGt, branchKnowledgeBoth] = true := by
  native_decide

-- The `if` sugar carries it too (`if h : c { … } else { … }`), which is the form the
-- partition body wants.
def branchKnowledgeIf : Decl :=
  decl{ fn branchKnowledgeIf (a : Nat, b : Nat) -> Unit
        { if e : leb a b { needLe(a, b, leb_true_le a b e); () }
          else { needGt(a, b, leb_false_gt a b e); () } } }
example : checkFnOk branchKnowledgeIf [needLe, needGt, branchKnowledgeIf] = true := by
  native_decide

/-! #### Negative controls — one per rule branch

    The rule has exactly three branches that can produce an equation: the stuck
    split (a real hypothesis), the ordinary symbolic split (`Refl`), and the
    concrete split (`Refl`). Each gets a control, plus the two ways the minted
    hypothesis could be a rubber stamp. -/

-- (1) The equation is the branch's OWN constructor, not the other one: citing
-- `leb_false_gt` on the True branch's `e : Id Bool (leb a b) True` is rejected.
def branchEqSwapped : Decl :=
  decl{ fn branchEqSwapped (a : Nat, b : Nat) -> Unit
        { let c = leb a b;
          match e : c {
            True => { needGt(a, b, leb_false_gt a b e); () },
            False => ()
          } } }
example : checkFnErr branchEqSwapped "does not have its parameter type"
  [needLe, needGt, branchEqSwapped] = true := by native_decide

-- (2) The equation is about the SPINE THAT WAS SPLIT ON, not any spine: split on
-- `leb a b`, then claim the equation is about `leb b a`. Rejected — so the minted
-- type is read off the abstracted scrutinee, not fabricated per use site.
def needLeSwap : Decl := decl{ fn needLeSwap (a : Nat, b : Nat, h : Le b a) -> Unit { () } }
def branchEqWrongSpine : Decl :=
  decl{ fn branchEqWrongSpine (a : Nat, b : Nat) -> Unit
        { let c = leb a b;
          match e : c {
            True => { needLeSwap(a, b, leb_true_le b a e); () },
            False => ()
          } } }
example : checkFnErr branchEqWrongSpine "does not have its parameter type"
  [needLeSwap, branchEqWrongSpine] = true := by native_decide

-- (3) An ORDINARY symbolic split still yields only `Refl`: `n`'s equation in the
-- `S` branch is `Id Nat (S σm) (S σm)` — ⇜ already rewrote the pre-split value, so
-- both endpoints are the constructor tree and nothing off-diagonal is derivable.
def wantEqLie : Decl :=
  decl{ fn wantEqLie (n : Nat, h : Id Nat (S n) n) -> Unit { () } }
def branchEqPlainSym : Decl :=
  decl{ fn branchEqPlainSym (n : Nat) -> Unit
        { match e : n { Z => (), S(m) => { wantEqLie(m, e); () } } } }
example : checkFnErr branchEqPlainSym "does not have its parameter type"
  [wantEqLie, branchEqPlainSym] = true := by native_decide

-- …and the reflexive reading of that same equation IS available: `Id Nat (S m) (S m)`.
def wantRefl : Decl :=
  decl{ fn wantRefl (n : Nat, h : Id Nat (S n) (S n)) -> Unit { () } }
def branchEqPlainSymRefl : Decl :=
  decl{ fn branchEqPlainSymRefl (n : Nat) -> Unit
        { match e : n { Z => (), S(m) => { wantRefl(m, e); () } } } }
example : checkFnOk branchEqPlainSymRefl [wantRefl, branchEqPlainSymRefl] = true := by
  native_decide

-- (4) The CONCRETE split (the executing side and any concrete scrutinee) binds the
-- equation too, so a body written with `match h :` runs. The differential below
-- exercises the same path end to end.
def concreteEq : Decl :=
  decl{ fn concreteEq () -> Unit
        { let n = S(Z);
          match e : n { Z => (), S(m) => { wantRefl(m, e); () } } } }
example : checkFnOk concreteEq [wantRefl, concreteEq] = true := by native_decide

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

def pick : Decl :=
  decl{ fn pick (v : &mut List Nat, x : Nat, p : Nat)
        -> Id (List Nat) (*v)
             (insertL (boolRec (λ (b : Bool). Nat) Z (S Z) (leb x p)) x (old *v))
        { let K = boolRec (λ (b : Bool). Nat) Z (S Z) (leb x p);
          insert_at(&mut *v, K, x) } }
example : checkFnOk pick [insertAt, pick] = true := by native_decide

/-! Half 2 — the pure lemma, over the SAME stuck index, gets its branch knowledge
    from a CONVOY MOTIVE: the motive carries `Id Bool <spine> b`, so each arm
    receives the equation as an argument and the whole elim is applied to `Refl`.
    This is the idiom M22's `allLeR_extend_far` already uses; naming it here because
    it is the thing that makes the branch-free route work rather than merely move
    the problem. `ub_pick` is the shape every partition-invariant lemma will take. -/

def ub_pick : Term := pure{
  λ (x : Nat). λ (p : Nat). λ (l : List Nat). λ (h : Ub p l).
    elim (leb x p) return (λ (b : Bool).
        Id Bool (leb x p) b →
        Ub p (take (boolRec (λ (bb : Bool). Nat) (S Z) Z b)
                (insertL (boolRec (λ (bb : Bool). Nat) Z (S Z) b) x l))) {
      True => λ (e : Id Bool (leb x p) True). Pair(leb_true_le x p e, unit),
      False => λ (e : Id Bool (leb x p) False). unit
    } Refl }
def ub_pick_ty : Term := pure{
  Π (x : Nat) → Π (p : Nat) → Π (l : List Nat) → Ub p l →
    Ub p (take (boolRec (λ (bb : Bool). Nat) (S Z) Z (leb x p))
            (insertL (boolRec (λ (bb : Bool). Nat) Z (S Z) (leb x p)) x l)) }
example : chk ub_pick ub_pick_ty = true := by native_decide

-- `Ub`/`Lb` compute, and are Σ-chained (so `sigmaRec` consumes them).
example : (pv (pure{ Ub (S (S Z)) (Cons (S Z) (Cons (S (S Z)) Nil)) }) ==
           pv (pure{ Σ (h : Le (S Z) (S (S Z))) → Σ (h2 : Le (S (S Z)) (S (S Z))) → Unit })) = true := by native_decide
example : (pv (pure{ Lb Z (Cons (S Z) Nil) }) == pv (pure{ Σ (h : Le Z (S Z)) → Unit })) = true := by native_decide

/-! ### The unshifted-motive question, settled: LATENT AND UNREACHABLE

    `hasType`'s `natRec`/`listRec` premises use the motive under the step's binders
    WITHOUT shifting it (`.pi a (.pi listA (.pi (.app p (.pvar 0)) …))`). Read as de
    Bruijn terms that is a wrong-answer typing rule for an OPEN motive — one
    mentioning an enclosing λ's variable — which is exactly the shape
    `sorted_append_pivot` needs (induction on `a`, motive mentioning `p` and `b`).
    So it looked like a live hazard for the rest of M23 and worth fixing first.

    It is not, and the reason is worth recording because it is not obvious from the
    premise construction: `hasType` INSTANTIATES every λ binder with a fresh σ as it
    descends (the `.lam`-against-`.pi` case). By the time a recursor spine is
    reached, every enclosing binder is a `sym`, so the motive it carries is
    pvar-free — and `shiftPure` is the identity on pvar-free values. Open motives
    are a de Bruijn artifact of the elaborated term that the typing descent never
    presents. A `.pi` codomain is the only place pvars survive, and `hasType` returns
    `Type` there without checking inside.

    Verified rather than argued: these type-check, and they type-check IDENTICALLY
    with the shifts inserted (I wrote the fix, measured no difference, and reverted
    it — three `shiftPure` calls on an unreachable case is complexity without
    payoff). Kept as positive controls so that if the descent discipline ever
    changes, something fails here first. -/

def openMotiveL : Term := pure{
  λ (p : Nat). λ (l : List Nat).
    elim l return (λ (lz : List Nat). Le p p) { Nil => le_refl p, Cons (h) (t) ih => ih } }
def openMotiveL_ty : Term := pure{ Π (p : Nat) → Π (l : List Nat) → Le p p }
example : chk openMotiveL openMotiveL_ty = true := by native_decide

def openMotiveN : Term := pure{
  λ (p : Nat). λ (n : Nat).
    elim n return (λ (nz : Nat). Le p p) { Z => le_refl p, S (m) ih => ih } }
def openMotiveN_ty : Term := pure{ Π (p : Nat) → Π (n : Nat) → Le p p }
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
    branch-knowledge wall above was `{ let q = leb_true_le a b Refl; () }`, which was
    ACCEPTED, and I nearly concluded the body DOES get branch equations. The honest
    probe (kept above) routes the proof into a consumer, and is rejected.

    The paired discipline, since `checkFnOk`/`chk` also collapse "machine error" and
    "typing false" into one `false`: confirm every negative control is an honest
    typing rejection, and confirm every positive one is live by flipping it and
    watching the build go red. Both were done for every test in this file. -/

-- Generic J-transport at `List Nat` — `le_rw_r` for arbitrary list predicates. Every
-- certificate a back-less body returns is stated over an exit it knows only
-- PROPOSITIONALLY (from the callee's evidence), so transporting a proof along that
-- evidence is the universal last step; `le_rw_r` already covers the `Le`-over-`Nat`
-- case and this is the unrestricted one.
example : chk Dllbc.StdLemmas.list_rw Dllbc.StdLemmas.list_rw_ty = true := by native_decide

/-! ### The pivot glue — `Sorted (a ++ p :: b)` from the four partition facts

    A back-less partition hands its caller two WHOLE lists and a pivot, with the four
    facts `Sorted a`, `Ub p a`, `Sorted b`, `Lb p b`; `sorted_append_pivot` is what
    turns those into the sortedness half of quicksort's postcondition. The Σ-chained
    predicates are taken apart with `sigmaRec` (stage (i)) — five projections first,
    then the head-bound transport, then the induction. -/

example : chk sorted_head Dllbc.StdLemmas.sorted_head_ty = true := by native_decide
example : chk sorted_tail Dllbc.StdLemmas.sorted_tail_ty = true := by native_decide
example : chk ub_head Dllbc.StdLemmas.ub_head_ty = true := by native_decide
example : chk ub_tail Dllbc.StdLemmas.ub_tail_ty = true := by native_decide
example : chk lb_bound Dllbc.StdLemmas.lb_bound_ty = true := by native_decide
example : chk bound_append Dllbc.StdLemmas.bound_append_ty = true := by native_decide
example : chk sorted_append_pivot Dllbc.StdLemmas.sorted_append_pivot_ty = true := by native_decide

-- It COMPUTES, end to end: `[1] ++ 2 :: [3]` is sorted, from the four facts about
-- the parts. Every hypothesis at these values is a `⊤`-chain, so the witnesses are
-- `Pair(unit, unit)` — the content is entirely in the lemma.
def sap_app : Term := pure{
  sorted_append_pivot (S (S Z)) (Cons (S Z) Nil) (Cons (S (S (S Z))) Nil)
    Pair(unit, unit) Pair(unit, unit) Pair(unit, unit) Pair(unit, unit) }
def sap_app_ty : Term := pure{
  Sorted (Cons (S Z) (Cons (S (S Z)) (Cons (S (S (S Z))) Nil))) }
example : chk sap_app sap_app_ty = true := by native_decide

/-! Honesty controls. Each flips ONE hypothesis and watches the check fail — the
    two orientation flips (`Ub`/`Lb` swapped for their duals) and one arm lie. -/

-- (1) `Ub p a` weakened to `Lb p a`: `ub_head` now receives `Σ (Le p h) → Lb p t`
-- where it wants `Σ (Le h p) → Ub p t`. Without a's elements being BELOW the pivot
-- the splice is not sorted, and the check says so.
def sap_lie_ub_ty : Term := pure{
  Π (p : Nat) → Π (a : List Nat) → Π (b : List Nat) →
    Sorted a → Lb p a → Sorted b → Lb p b → Sorted (append a (Cons p b)) }
example : chk sorted_append_pivot sap_lie_ub_ty = false := by native_decide

-- (2) `Lb p b` weakened to `Ub p b`: `lb_bound` is fed the wrong direction, so the
-- pivot no longer bounds b's head.
def sap_lie_lb_ty : Term := pure{
  Π (p : Nat) → Π (a : List Nat) → Π (b : List Nat) →
    Sorted a → Ub p a → Sorted b → Ub p b → Sorted (append a (Cons p b)) }
example : chk sorted_append_pivot sap_lie_lb_ty = false := by native_decide

-- (3) The `Nil` arm of the transport returning the wrong hypothesis: past the end of
-- `t` the new head is the PIVOT, so only `Le h p` inhabits the goal; handing back the
-- (vacuous) `Bound h Nil` does not.
def bound_append_lie : Term := pure{
  λ (h : Nat). λ (p : Nat). λ (t : List Nat). λ (b : List Nat).
    elim t return (λ (tz : List Nat).
        Bound h tz → Le h p → Bound h (append tz (Cons p b))) {
      Nil => λ (hb : Unit). λ (hp : Le h p). hb,
      Cons (h2) (t2) ih => λ (hb : Le h h2). λ (hp : Le h p). hb } }
example : chk bound_append_lie Dllbc.StdLemmas.bound_append_ty = false := by native_decide

-- (4) Liveness of the `Ub` hypothesis at concrete values: pivot 0 under a left part
-- containing 1 needs `Le 1 0 = ⊥`, which `Pair(unit, unit)` does not inhabit — so the
-- positive computation above passed on its hypotheses, not on a rubber stamp.
def sap_bad_pivot : Term := pure{
  sorted_append_pivot Z (Cons (S Z) Nil) Nil
    Pair(unit, unit) Pair(unit, unit) unit unit }
def sap_bad_pivot_ty : Term := pure{
  Sorted (Cons (S Z) (Cons Z Nil)) }
example : chk sap_bad_pivot sap_bad_pivot_ty = false := by native_decide

end Dllbc.Tests.S23Direct

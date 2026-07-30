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

end Dllbc.Tests.S23Direct

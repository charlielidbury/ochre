import Dllbc.Std
import Dllbc.StdLemmas

/-!
# `EagerRec` — the normalizer forces a recursor's recursive result (§4)

`whnfN` used to hand a recursor's step function the recursive call as an
unreduced `Sem` spine and β-bind it by extending an environment. `Sem` has no
host thunks and reduction has no write-back, so every USE of that binder
re-derived it: an arm mentioning `Rec` twice cost twice the whole sub-recursion,
per level, which is exponential in the depth. `Pure.deepForce` fixes it by
forcing the recursive argument to a call-by-value VALUE before the arm is entered
— constructors forced all the way down, closures left closed, neutrals stuck.

The force is asked for only when the arm MAKES the call (`Pure.armUsesRec`), and
that gate is not an optimisation, it is what keeps the change from being a
catastrophe. See the commit: forcing unconditionally costs `binomial(b, a)` on
this very file's `Mod`, because `eqb`'s inner `elim B { Z => False, S (B') Rec =>
RecA B' }` ignores its `Rec` — it is a case split, not a call, and in this
calculus a case split on a `Nat` can only be spelled as a recursion.

## The shape that used to be exponential

`ModT` below is the textbook `mod`: `mod (S a') b = let r = S (mod a' b) in
if r == b then Z else r`. `Rec` occurs in the scrutinee AND in the `False`
branch, which is exactly the doubling. The `hm-probe-mod` lane measured this
shape at **87 s for `Mod 20 32`**, doubling per unit of dividend, and had to
rewrite `Mod` into an accumulator whose step mentions `Rec` once to get a usable
one. That rewrite is no longer required — the textbook spelling computes.

## Measured scaling, divisor 32

Wall clock of one `Pure.nf 4000000` per dividend, `lake env lean` against built
oleans (the harness `hm-probe-mod` used, so the 87 s is the same kind of number):

| dividend |  4 |  8 | 16 | 20 | 32 | 64 | 128 | 256 | 512 | 1056 |
|----------|----|----|----|----|----|----|-----|-----|-----|------|
| ms       |  1 |  2 |  5 |  6 | 15 | 27 |  51 | 100 | 200 |  425 |

Linear — doubling the dividend doubles the time, and the doubling PER UNIT is
gone. `Mod 20 32`: 87 s to 6 ms. `Mod 1056 32` — the Aeneas hashmap's own test
key at its own capacity, which the old normalizer could not finish — 425 ms.

## The cost model this leaves

Eager changes cost, never answers, and `M2` below is the golden for the second
half of that. What it does change: an arm that names its recursive result pays
for it in full even down a branch that discards it, so an early-exit-shaped
recursion costs the whole depth. An arm that does not name it at all pays
nothing, because no call is made.
-/

namespace Dllbc.Tests.EagerRec
open Dllbc

/-! ## M1 — the textbook `mod`, written the way it used to be forbidden -/

/-- `mod a b`, the shape a textbook writes and the old normalizer could not run:
    the recursive result is the scrutinee of the `Eqb` test AND the value the
    `False` branch returns. -/
def ModTFn : Term := prog defer_check {
  λ (A : Nat). λ (B : Nat).
    elim A return (λ (Am : Nat). Nat) {
      Z => Z,
      S (A') Rec => elim (Eqb (S(Rec)) B) return (λ (Bm : Bool). Nat) {
        True => Z,
        False => S(Rec) } } }
def ModTFnT : Dllbc.Term := ModTFn

def pv (t : Term) : Term := Pure.nf 4000000 t

/-- Dividends are SPLICED as `Term.nat`, not written as surface numerals: a
    surface `1056` would be a 1056-deep Lean syntax tree to elaborate. -/
def modOf (a b : Nat) : Term := pv prog{ %ModTFnT %(Term.nat a) %(Term.nat b) }

example : (modOf 7 3).natOf? == some 1 := by native_decide
example : (modOf 6 3).natOf? == some 0 := by native_decide
example : (modOf 5 8).natOf? == some 5 := by native_decide
example : (modOf 0 3).natOf? == some 0 := by native_decide
example : (modOf 20 32).natOf? == some 20 := by native_decide
example : (modOf 999 7).natOf? == some 5 := by native_decide

-- Real sizes: the hashmap's keys at the hashmap's capacity. `Mod 20 32` alone
-- took 87 s before this change, and `Mod 1056 32` was out of reach entirely.
example : (modOf 32 32).natOf? == some 0 := by native_decide
example : (modOf 128 32).natOf? == some 0 := by native_decide
example : (modOf 1024 32).natOf? == some 0 := by native_decide
example : (modOf 1056 32).natOf? == some 0 := by native_decide
example : (modOf 1057 32).natOf? == some 1 := by native_decide

/-! ## M2 — eager changes COST, never ANSWERS

    Three ways an arm can fail to use what it was handed, and the answer is the
    same in all of them. The interesting one is `ZeroOut`: its arm NAMES `Rec`, so
    the call is made and forced, but the branch that runs discards it. -/

/-- The arm ignores `Rec` outright — a case split wearing a recursion's clothes.
    No call is made, so this is `Z` at any depth and costs nothing. -/
def DiscardFn : Term := prog defer_check {
  λ (A : Nat). elim A return (λ (Am : Nat). Nat) { Z => Z, S (A') Rec => Z } }
def DiscardFnT : Dllbc.Term := DiscardFn

/-- The arm ignores `Rec` and answers with the PREDECESSOR instead. -/
def PredFn : Term := prog defer_check {
  λ (A : Nat). elim A return (λ (Am : Nat). Nat) { Z => Z, S (A') Rec => A' } }
def PredFnT : Dllbc.Term := PredFn

/-- The arm names `Rec`, so the recursive call is made and forced to a value —
    and then the branch that runs throws it away. The scrutinee is `Eqb 1 0`,
    which is `False` at every level, so the answer is `Z` however deep it went.
    This is the cost/answer split stated as a term: full depth is paid, and the
    result is what lazy reduction gave. -/
def ZeroOutFn : Term := prog defer_check {
  λ (A : Nat). elim A return (λ (Am : Nat). Nat) {
    Z => Z,
    S (A') Rec => elim (Eqb (S(Z)) Z) return (λ (Bm : Bool). Nat) {
      True => Rec,
      False => Z } } }
def ZeroOutFnT : Dllbc.Term := ZeroOutFn

def app1 (f : Term) (a : Nat) : Term := pv prog{ %f %(Term.nat a) }

example : (app1 DiscardFnT 0).natOf? == some 0 := by native_decide
example : (app1 DiscardFnT 64).natOf? == some 0 := by native_decide
example : (app1 PredFnT 0).natOf? == some 0 := by native_decide
example : (app1 PredFnT 100).natOf? == some 99 := by native_decide
example : (app1 ZeroOutFnT 0).natOf? == some 0 := by native_decide
example : (app1 ZeroOutFnT 64).natOf? == some 0 := by native_decide

/-! ### And it holds over a NEUTRAL, which is where forcing could have gone wrong

    `S (S x)` for a free `x` fires the recursor twice and then gets stuck. The
    discarding arms never look, and `ZeroOut` forces a spine that contains a
    neutral — `deepForce` has to leave that stuck rather than treat it as an
    error or as a value. All three still answer `Z`. -/

def openTwo : Term := prog defer_check { S(S(%(Term.pvar "x"))) }

example : (pv prog defer_check { %DiscardFnT %openTwo }).natOf? == some 0 := by native_decide
example : (pv prog defer_check { %ZeroOutFnT %openTwo }).natOf? == some 0 := by native_decide

/-! ### The two spellings agree

    `ModC` is the accumulator `hm-probe-mod` had to write because the textbook
    shape was unusable — its step names `Rec` once and asks its question of an
    ARGUMENT. It is no longer the only viable spelling, and the point of keeping
    it here is that it must still give `ModT`'s answers. -/

def NextRFn : Term := prog defer_check {
  λ (R : Nat). λ (C : Nat).
    elim C return (λ (Cz : Nat). Nat) { Z => Z, S (C') Rc => S(R) } }
def NextRFnT : Dllbc.Term := NextRFn

def NextCFn : Term := prog defer_check {
  λ (B : Nat). λ (C : Nat).
    elim C return (λ (Cz : Nat). Nat) { Z => B, S (C') Rc => C' } }
def NextCFnT : Dllbc.Term := NextCFn

def ModCFn : Term := prog defer_check {
  λ (A : Nat).
    elim A return (λ (Az : Nat). Π (B : Nat) → Π (R : Nat) → Π (C : Nat) → Nat) {
      Z => λ (B : Nat). λ (R : Nat). λ (C : Nat). R,
      S (A') Rec => λ (B : Nat). λ (R : Nat). λ (C : Nat).
        Rec B (%NextRFnT R C) (%NextCFnT B C) } }
def ModCFnT : Dllbc.Term := ModCFn

/-- `ModC`'s wrapper, matching `hm-probe-mod`'s `Mod`. -/
def modCOf (a b : Nat) : Term := pv prog{
  (λ (A : Nat). λ (B : Nat).
    elim B return (λ (Bz : Nat). Nat) {
      Z => Z,
      S (B') Rb => %ModCFnT A B' Z B' }) %(Term.nat a) %(Term.nat b) }

example : modCOf 7 3 == modOf 7 3 := by native_decide
example : modCOf 20 32 == modOf 20 32 := by native_decide
example : modCOf 1056 32 == modOf 1056 32 := by native_decide
example : modCOf 1057 32 == modOf 1057 32 := by native_decide

end Dllbc.Tests.EagerRec

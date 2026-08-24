import Dllbc.Std
import Dllbc.ElabCheck

/-!
# `EagerRec` — the normalizer forces a recursor's recursive result

This file tests that the normalizer forces a recursor's recursive result to a
value before entering an arm that uses it. Without the force, an arm that
mentions the recursive call twice re-derives the whole sub-recursion each
time it is used, doubling the cost at every level — exponential in the depth.
With the force, the textbook `mod` spelling below computes in linear time
instead.

The force is applied only when an arm actually makes the recursive call,
rather than merely case-splitting on the recursor's argument (which, in this
calculus, can only be spelled as a recursion). Forcing unconditionally would
itself be super-linear on arms that never call `Rec`, so the gate matters as
much as the force does.

Measured effect: `Mod 20 32` fell from 87 s to 6 ms, and time now scales
linearly with the dividend instead of doubling per unit.
-/

namespace Dllbc.Tests.EagerRec
open Dllbc

/-! ## M1 — the textbook `mod` -/

/-- `mod a b`: the recursive result is both the scrutinee of the `Eqb` test and
    the value the `False` branch returns — the shape that doubles cost without
    forcing. -/
def ModTFn : Term := prog_parse {
  λ (A : Nat). λ (B : Nat).
    elim A return (λ (Am : Nat). Nat) {
      Z => Z,
      S (A') Rec => elim (Eqb (S(Rec)) B) return (λ (Bm : Bool). Nat) {
        True => Z,
        False => S(Rec) } } }
def ModTFnT : Dllbc.Term := ModTFn

def pv (t : Term) : Term := Pure.nf 4000000 t

/-- Dividends are spliced in as `Term.nat` because `a` and `b` are Lean
    parameters, not because of cost: a surface numeral is now one syntax node
    (`Surface.buildNat` emits `Term.nat k`), so a literal `1056` elaborates as
    fast as `%(Term.nat 1056)` — it used to be a 1056-deep syntax tree that hit
    `maxRecDepth`. -/
def modOf (a b : Nat) : Term := pv prog{ ModTFnT %(Term.nat a) %(Term.nat b) }

example : (modOf 7 3).natOf? == some 1 := by native_decide
example : (modOf 6 3).natOf? == some 0 := by native_decide
example : (modOf 5 8).natOf? == some 5 := by native_decide
example : (modOf 0 3).natOf? == some 0 := by native_decide
example : (modOf 20 32).natOf? == some 20 := by native_decide
example : (modOf 999 7).natOf? == some 5 := by native_decide

-- Dividends matching the hashmap's real keys and bucket capacity.
example : (modOf 32 32).natOf? == some 0 := by native_decide
example : (modOf 128 32).natOf? == some 0 := by native_decide
example : (modOf 1024 32).natOf? == some 0 := by native_decide
example : (modOf 1056 32).natOf? == some 0 := by native_decide
example : (modOf 1057 32).natOf? == some 1 := by native_decide

/-! ## M2 — eager cost is separate from the answer -/

/-- The arm ignores `Rec`, so no recursive call is made: the result is `Z` at
    any depth, at no cost. -/
def DiscardFn : Term := prog_parse {
  λ (A : Nat). elim A return (λ (Am : Nat). Nat) { Z => Z, S (A') Rec => Z } }
def DiscardFnT : Dllbc.Term := DiscardFn

/-- The arm ignores `Rec` and returns the predecessor `A'` instead. -/
def PredFn : Term := prog_parse {
  λ (A : Nat). elim A return (λ (Am : Nat). Nat) { Z => Z, S (A') Rec => A' } }
def PredFnT : Dllbc.Term := PredFn

/-- The arm names `Rec`, so the call is made and forced to a value, and then the
    branch that runs discards it. The scrutinee `Eqb 1 0` is `False` at every
    level, so the result is `Z` regardless of depth: full cost paid, same
    answer either way. -/
def ZeroOutFn : Term := prog_parse {
  λ (A : Nat). elim A return (λ (Am : Nat). Nat) {
    Z => Z,
    S (A') Rec => elim (Eqb (S(Z)) Z) return (λ (Bm : Bool). Nat) {
      True => Rec,
      False => Z } } }
def ZeroOutFnT : Dllbc.Term := ZeroOutFn

def app1 (f : Term) (a : Nat) : Term := pv prog{ f %(Term.nat a) }

example : (app1 DiscardFnT 0).natOf? == some 0 := by native_decide
example : (app1 DiscardFnT 64).natOf? == some 0 := by native_decide
example : (app1 PredFnT 0).natOf? == some 0 := by native_decide
example : (app1 PredFnT 100).natOf? == some 99 := by native_decide
example : (app1 ZeroOutFnT 0).natOf? == some 0 := by native_decide
example : (app1 ZeroOutFnT 64).natOf? == some 0 := by native_decide

/-! ### Forcing over a stuck neutral -/

-- `S (S x)` for free `x` fires the recursor twice, then gets stuck; `deepForce`
-- must leave the stuck neutral alone rather than treating it as an error.
def openTwo : Term := prog_parse { S(S(x)) }

example : (pv prog_parse { DiscardFnT openTwo }).natOf? == some 0 := by native_decide
example : (pv prog_parse { ZeroOutFnT openTwo }).natOf? == some 0 := by native_decide

/-! ### The two spellings agree -/

-- `ModC` is an accumulator-style alternative to `ModT`: its step names `Rec`
-- once and questions an argument rather than the recursive result. Kept here
-- to check it agrees with `ModT`, not because it is required.
def NextRFn : Term := prog_parse {
  λ (R : Nat). λ (C : Nat).
    elim C return (λ (Cz : Nat). Nat) { Z => Z, S (C') Rc => S(R) } }
def NextRFnT : Dllbc.Term := NextRFn

def NextCFn : Term := prog_parse {
  λ (B : Nat). λ (C : Nat).
    elim C return (λ (Cz : Nat). Nat) { Z => B, S (C') Rc => C' } }
def NextCFnT : Dllbc.Term := NextCFn

def ModCFn : Term := prog_parse {
  λ (A : Nat).
    elim A return (λ (Az : Nat). Π (B : Nat) → Π (R : Nat) → Π (C : Nat) → Nat) {
      Z => λ (B : Nat). λ (R : Nat). λ (C : Nat). R,
      S (A') Rec => λ (B : Nat). λ (R : Nat). λ (C : Nat).
        Rec B (NextRFnT R C) (NextCFnT B C) } }
def ModCFnT : Dllbc.Term := ModCFn

/-- Wrapper for `ModCFn`, mirroring its accumulator-style calling convention. -/
def modCOf (a b : Nat) : Term := pv prog{
  (λ (A : Nat). λ (B : Nat).
    elim B return (λ (Bz : Nat). Nat) {
      Z => Z,
      S (B') Rb => ModCFnT A B' Z B' }) %(Term.nat a) %(Term.nat b) }

example : modCOf 7 3 == modOf 7 3 := by native_decide
example : modCOf 20 32 == modOf 20 32 := by native_decide
example : modCOf 1056 32 == modOf 1056 32 := by native_decide
example : modCOf 1057 32 == modOf 1057 32 := by native_decide

end Dllbc.Tests.EagerRec

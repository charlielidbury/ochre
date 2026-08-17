import Dllbc.Program
import Dllbc.Boundary
import Dllbc.ProgMacro
import Dllbc.Std
import Dllbc.StdLemmas

/-!
# `HmProbeMod` — a viability probe for the hashmap's slot arithmetic

The planned hashmap flagship (mirroring Aeneas' ICFP'22 case study) selects a slot
by `hash % capacity`. DLLBC has no `mod`/`div`. This file finds out what it costs
to add them and to get from a slot index to a WRITABLE cell:

  M1  `Mod`/`Div` as Std-style surface fns, structurally recursive on the dividend.
  M2  the bound lemma `Le (S (Mod a (S b))) (S b)` — a slot index is below capacity.
  M3  the carve-decomposition minting lemma `Le (S i) n → Σ r. Id Nat n (Add i (S r))`.
  M4  a `fn` composing the three into an in-place write at the computed slot.

Nothing here is a kernel change; it is all library.
-/

namespace Dllbc.Tests.HmProbeMod
open Dllbc
open Dllbc.StdLemmas (LeAdd IdCongr IdSym IdTrans LebFalseGt LebTrueLe)

/-! ## M1 — `Mod` and `Div`

    The house structural trick for `mod`: the residue of `S a` is computed from the
    residue of `a` by bumping it and resetting at the divisor. The test for "the
    bump reached the divisor" is written with **`Leb b (S r)`, not `Eqb (S r) b`**,
    and that choice is the whole of M2's proof. Under the invariant `S r ≤ b` the
    two tests agree; but `Leb`'s FALSE branch already has a library lemma turning it
    into the STRICT bound the step needs (`LebFalseGt : Id Bool (Leb a b) False →
    Le (S b) a`), whereas `Eqb`'s false branch gives a disequality that would have
    to be combined with the non-strict bound by a lemma that does not exist yet.

    At `b = Z` this returns `Z` rather than the dividend (`Leb Z _` is always
    `True`). Lean's `%` returns the dividend there; nothing downstream divides by
    zero, and the bound lemma is stated at `S b`. -/

def ModFn : Term := prog{
  λ (A : Nat). λ (B : Nat).
    elim A return (λ (Az : Nat). Nat) {
      Z => Z,
      S (A') Rec => elim (Leb B (S Rec)) return (λ (Cz : Bool). Nat) {
        True => Z,
        False => S(Rec) } } }
def ModFnT : Dllbc.Term := ModFn
abbrev Mod : Term := ModFnT

/-- `Div` on the same recursion: the quotient ticks exactly when the residue
    resets, so its arm re-computes `Mod A' B` and tests the same Boolean. -/
def DivFn : Term := prog{
  λ (A : Nat). λ (B : Nat).
    elim A return (λ (Az : Nat). Nat) {
      Z => Z,
      S (A') Rec => elim (Leb B (S (Mod A' B))) return (λ (Cz : Bool). Nat) {
        True => S(Rec),
        False => Rec } } }
def DivFnT : Dllbc.Term := DivFn
abbrev Div : Term := DivFnT

/-! ### They compute -/

def pv (t : Term) : Term := Pure.nf 200000 t

example : pv prog{ Mod 7 3 } == Term.nat 1 := by native_decide
example : pv prog{ Mod 6 3 } == Term.nat 0 := by native_decide
example : pv prog{ Mod 5 8 } == Term.nat 5 := by native_decide
example : pv prog{ Mod 0 3 } == Term.nat 0 := by native_decide
example : pv prog{ Mod 32 32 } == Term.nat 0 := by native_decide

example : pv prog{ Div 7 3 } == Term.nat 2 := by native_decide
example : pv prog{ Div 6 3 } == Term.nat 2 := by native_decide
example : pv prog{ Div 5 8 } == Term.nat 0 := by native_decide

-- The Aeneas hashmap's own test keys, at its own capacity: 0, 128, 1024, 1056 all
-- land in slot 0 of 32, which is what makes that test exercise the collision list.
example : pv prog{ Mod 128 32 } == Term.nat 0 := by native_decide
example : pv prog{ Mod 1024 32 } == Term.nat 0 := by native_decide
example : pv prog{ Mod 1056 32 } == Term.nat 0 := by native_decide
example : pv prog{ Mod 1057 32 } == Term.nat 1 := by native_decide

/-! ## The lemma harness (as §23/§24: a closed term against a closed type) -/

def chkL (tm ty : Term) : Bool :=
  match (do let v ← readC 8000 tm; let t ← readC 8000 ty; hasTypeT 8000 v t).run (seedPure [] []) with
  | .ok r _ => r
  | .error _ _ => false

/-! ## M2 — the slot index is below the capacity

    `Le (S (Mod a (S b))) (S b)`. The `elim` on `a` is there only to EXPOSE `Mod`'s
    two equations; the induction hypothesis is never consumed, because `Leb`'s false
    branch already carries the strict bound. That is the payoff of writing `Mod`'s
    reset test as `Leb b (S r)`: the step is one `LebFalseGt` and the base is `unit`.

    The Boolean case split is the corpus' remember-the-scrutinee idiom
    (`AllLeRExtendFar`): the motive abstracts the scrutinee AND takes the equation,
    and the whole `elim` is applied to `Refl`. Here the motive's target mentions the
    abstracted Boolean too — the goal is `Le (S (Mod (S a') (S b))) (S b)` and `Mod`
    unfolds to the very `boolRec` being cased — so no `generalize` macro is needed;
    writing the motive by hand covers it. -/

def ModLt : Term := prog{
  λ (A : Nat).
    elim A return (λ (Az : Nat). Π (B : Nat) → Le (S (Mod Az (S B))) (S B)) {
      Z => λ (B : Nat). unit,
      S (A') Ih => λ (B : Nat).
        elim (Leb (S B) (S (Mod A' (S B))))
          return (λ (Cz : Bool).
            Id Bool (Leb (S B) (S (Mod A' (S B)))) Cz →
              Le (S (elim Cz return (λ (Bm : Bool). Nat) {
                       True => Z,
                       False => S(Mod A' (S B)) })) (S B)) {
            True => λ (E : Id Bool (Leb (S B) (S (Mod A' (S B)))) True). unit,
            False => λ (E : Id Bool (Leb (S B) (S (Mod A' (S B)))) False).
              LebFalseGt (S B) (S (Mod A' (S B))) E
          } Refl } }
def ModLtTy : Term := prog{ Π (A : Nat) → Π (B : Nat) → Le (S (Mod A (S B))) (S B) }

example : chkL ModLt ModLtTy = true := by native_decide

/-! ## M3 — minting the carve's decomposition

    `Le (S i) n → Σ r. Id Nat n (Add i (S r))`: "i is strictly below n" is turned into
    the residue `r` and the equation the carve's premise (3) wants CITED. Induction on
    `i`, casing `n` at each level; both `n = Z` arms are `Bot` (the hypothesis says `n`
    is above something), the `i = Z` step reads off `r := n'`, and the successor step
    rebuilds the pair through one `IdCongr S`. -/

def ModDec : Term := prog{
  λ (I : Nat).
    elim I return (λ (Iz : Nat).
        Π (N : Nat) → Le (S Iz) N → Σ (R : Nat) → Id Nat N (Add Iz (S R))) {
      Z => λ (N : Nat).
        elim N return (λ (Nz : Nat). Le (S Z) Nz → Σ (R : Nat) → Id Nat Nz (Add Z (S R))) {
          Z => λ (H : Le (S Z) Z). botElim (Σ (R : Nat) → Id Nat Z (Add Z (S R))) H,
          S (N') Ihn => λ (H : Le (S Z) (S N')). Pair(N', Refl) },
      S (I') Ih => λ (N : Nat).
        elim N return (λ (Nz : Nat).
            Le (S (S I')) Nz → Σ (R : Nat) → Id Nat Nz (Add (S I') (S R))) {
          Z => λ (H : Le (S (S I')) Z). botElim (Σ (R : Nat) → Id Nat Z (Add (S I') (S R))) H,
          S (N') Ihn => λ (H : Le (S (S I')) (S N')).
            elim (Ih N' H) return (λ (Q : Σ (R : Nat) → Id Nat N' (Add I' (S R))).
                Σ (R : Nat) → Id Nat (S N') (Add (S I') (S R))) {
              Pair (X) (Y) =>
                Pair(X, IdCongr Nat Nat (λ (Nn : Nat). S Nn) N' (Add I' (S X)) Y) } } } }
def ModDecTy : Term := prog{
  Π (I : Nat) → Π (N : Nat) → Le (S I) N → Σ (R : Nat) → Id Nat N (Add I (S R)) }

example : chkL ModDec ModDecTy = true := by native_decide

/-! ### …and its two projections, which is what a PROGRAM can consume

    A `fn` body cannot `match` a comptime Σ apart and keep both halves in scope for a
    carve's extent, so the Σ is taken apart by the ordinary dependent pair projections:
    `ModFst` is the residue, `ModSnd` is the equation ABOUT that residue. -/

def ModFst : Term := prog{
  λ (I : Nat). λ (N : Nat). λ (Q : Σ (R : Nat) → Id Nat N (Add I (S R))).
    elim Q return (λ (Q0 : Σ (R : Nat) → Id Nat N (Add I (S R))). Nat) {
      Pair (X) (Y) => X } }
def ModFstTy : Term := prog{
  Π (I : Nat) → Π (N : Nat) → Π (Q : Σ (R : Nat) → Id Nat N (Add I (S R))) → Nat }

example : chkL ModFst ModFstTy = true := by native_decide

def ModSnd : Term := prog{
  λ (I : Nat). λ (N : Nat). λ (Q : Σ (R : Nat) → Id Nat N (Add I (S R))).
    elim Q return (λ (Q0 : Σ (R : Nat) → Id Nat N (Add I (S R))).
        Id Nat N (Add I (S (ModFst I N Q0)))) {
      Pair (X) (Y) => Y } }
def ModSndTy : Term := prog{
  Π (I : Nat) → Π (N : Nat) → Π (Q : Σ (R : Nat) → Id Nat N (Add I (S R))) →
    Id Nat N (Add I (S (ModFst I N Q))) }

example : chkL ModSnd ModSndTy = true := by native_decide

/-! ## M4 — the composition: an in-place write at the computed slot

    `SlotWrite(h, c, v, slots)` writes `v` into slot `h % (c+1)` of a `c+1`-slot
    array. The three-line preamble is the whole story of what mod costs a program:

      * `ModLt h c`         — the index is below the capacity (M2);
      * `ModDec Idx … Hlt`  — mint the residue and the equation (M3);
      * two carves          — the prefix, cited with the minted equation, then the
                              one-slot cell, which needs NO evidence because after
                              the first carve its obligation is `Le 1 (S Res)`.

    The prefix borrow `pre` is never touched. It exists because a carve at a
    symbolic base needs a leaf that STARTS there, and only the first carve can make
    one — the same three-carve shape `partitionA` uses for its swap. -/

def slotWrite : Term := prog{
  fn SlotWrite (h : Nat, c : Nat, v : Nat, slots : &mut (Array (S c) Nat)) -> Unit {
    let Idx = Mod h (S c);
    let Hlt = ModLt h c;
    let Dec = ModDec Idx (S c) Hlt;
    let Res = ModFst Idx (S c) Dec;
    let Hdec = ModSnd Idx (S c) Dec;
    let pre = &m (*slots)[Z ; Idx ; S Res | LeAdd Idx (S Res) | Hdec];
    let cell = &m (*slots)[Idx ; 1 ; Res];
    (*cell)[0] := v;
    ()
  };
  () }

example : progOk slotWrite = true := by native_decide

/-! ### …and it writes the RIGHT slot, executing -/

def natOfV : Nat → Val → Option Nat
  | f, v =>
    match Val.asCtor? v, f with
    | some ("Z", []), _ => some 0
    | some ("S", [w]), f' + 1 => (natOfV f' w).map (· + 1)
    | _, _ => none

def arrOfV : Val → Option (List Nat)
  | v => match Val.asCtor? v with
    | some ("Arr", vs) => vs.mapM (natOfV 4000)
    | _ => none

/-- Four zeroed slots; write `9` at `h % 4`; read the array back. -/
def slotCaller (h : Nat) : Term := prog{
  fn SlotWrite (h : Nat, c : Nat, v : Nat, slots : &mut (Array (S c) Nat)) -> Unit {
    let Idx = Mod h (S c);
    let Hlt = ModLt h c;
    let Dec = ModDec Idx (S c) Hlt;
    let Res = ModFst Idx (S c) Dec;
    let Hdec = ModSnd Idx (S c) Dec;
    let pre = &m (*slots)[Z ; Idx ; S Res | LeAdd Idx (S Res) | Hdec];
    let cell = &m (*slots)[Idx ; 1 ; Res];
    (*cell)[0] := v;
    ()
  };
  let z = Arr(0, 0, 0, 0);
  let b = &m z;
  SlotWrite(%(Term.nat h), 3, 9, b);
  let y = z;
  () }

def runSlot (h : Nat) : Option (List Nat) :=
  match runProgram (slotCaller h) with
  | .ok env => (env.lookup "y").bind arrOfV
  | .error _ => none

#eval runSlot 0
#eval runSlot 1
#eval runSlot 6
#eval runSlot 7

end Dllbc.Tests.HmProbeMod

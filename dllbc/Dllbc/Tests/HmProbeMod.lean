import Dllbc.Program
import Dllbc.Boundary
import Dllbc.ProgMacro
import Dllbc.Std
import Dllbc.StdLemmas

/-!
# `HmProbeMod` — the hashmap's slot arithmetic, probed

The planned hashmap flagship (mirroring Aeneas' ICFP'22 case study) selects a slot
by `hash % capacity`, and DLLBC has no `mod`/`div`. This file is the viability
probe: define them, prove the two lemmas a slot access needs, and compose them
with a carve. Nothing here is a kernel change — it is all library.

Two things were found that a design sketch would not have predicted, and both are
recorded where they were found rather than only in the report:

**(1) `Mod` must be written so its step mentions the recursive result ONCE.** The
textbook shape — `let r = Mod a' b; if S r = b then Z else S r` — is EXPONENTIAL
here, doubling per unit of dividend, so `Mod 20 32` takes 87 s and `Mod 32 32`
would take days. Three spellings of that shape (the branch inline, the branch in a
helper, an accumulator whose two arms each mention `Rec`) measured identically,
which is what says the cost is the normalizer's and not the spelling's: it
substitutes without sharing, so every second occurrence of `Rec` re-derives it.
`ModC` below moves the branch OFF the recursive result and into its ARGUMENTS, so
`Rec` occurs once and the whole thing is linear — `Mod 1056 32` in 73 ms.

**(2) The slot index and the residue must be minted across a FUNCTION BOUNDARY.**
The carve's premise (3) solves its decomposition equation by refining a σ, and
neither `Mod h n` nor a comptime Σ-projection out of `ModDec` is one: both mention
`n`, so `n = add i (S r)` fails the occurs check. `SlotOf` returns them as a Σ, the
caller matches it, and §6.2's opacity re-mints both as fresh binders — the exact
shape `partitionA` already uses for `splitA`'s returned `k`/`r`.
-/

namespace Dllbc.Tests.HmProbeMod
open Dllbc
open Dllbc.StdLemmas (LeRefl LeAdd LeTrans LeRwL AddSucc IdCongr)

/-! ## M1 — `Mod` and `Div`

    The state is `(R, C)`: `R` is the residue so far, `C` is how many more
    increments fit before wrapping, and `R + C = B` is the invariant. Each step asks
    its question of `C` — an ARGUMENT — rather than of the residue, which is what
    keeps `Rec` to a single occurrence. `NextR`/`NextC`/`NextQ` are the three
    non-recursive answers to "what happens to this component at one increment".

    At `B = Z` the wrapper returns `Z` rather than the dividend (Lean's `%` returns
    the dividend). Nothing downstream divides by zero, and every lemma is stated
    over a `Le (S Z) n` hypothesis or an `S b` pattern. -/

def NextRFn : Term := prog{
  λ (R : Nat). λ (C : Nat).
    elim C return (λ (Cz : Nat). Nat) { Z => Z, S (C') Rc => S(R) } }
def NextRFnT : Dllbc.Term := NextRFn
abbrev NextR : Term := NextRFnT

def NextCFn : Term := prog{
  λ (B : Nat). λ (C : Nat).
    elim C return (λ (Cz : Nat). Nat) { Z => B, S (C') Rc => C' } }
def NextCFnT : Dllbc.Term := NextCFn
abbrev NextC : Term := NextCFnT

def NextQFn : Term := prog{
  λ (Q : Nat). λ (C : Nat).
    elim C return (λ (Cz : Nat). Nat) { Z => S(Q), S (C') Rc => Q } }
def NextQFnT : Dllbc.Term := NextQFn
abbrev NextQ : Term := NextQFnT

def ModCFn : Term := prog{
  λ (A : Nat).
    elim A return (λ (Az : Nat). Π (B : Nat) → Π (R : Nat) → Π (C : Nat) → Nat) {
      Z => λ (B : Nat). λ (R : Nat). λ (C : Nat). R,
      S (A') Rec => λ (B : Nat). λ (R : Nat). λ (C : Nat).
        Rec B (NextR R C) (NextC B C) } }
def ModCFnT : Dllbc.Term := ModCFn
abbrev ModC : Term := ModCFnT

def ModFn : Term := prog{
  λ (A : Nat). λ (B : Nat).
    elim B return (λ (Bz : Nat). Nat) { Z => Z, S (B') Rb => ModC A B' Z B' } }
def ModFnT : Dllbc.Term := ModFn
abbrev Mod : Term := ModFnT

/-- `Div` rides the same state with a quotient that ticks exactly when `C` wraps. -/
def DivCFn : Term := prog{
  λ (A : Nat).
    elim A return (λ (Az : Nat).
        Π (B : Nat) → Π (R : Nat) → Π (C : Nat) → Π (Q : Nat) → Nat) {
      Z => λ (B : Nat). λ (R : Nat). λ (C : Nat). λ (Q : Nat). Q,
      S (A') Rec => λ (B : Nat). λ (R : Nat). λ (C : Nat). λ (Q : Nat).
        Rec B (NextR R C) (NextC B C) (NextQ Q C) } }
def DivCFnT : Dllbc.Term := DivCFn
abbrev DivC : Term := DivCFnT

def DivFn : Term := prog{
  λ (A : Nat). λ (B : Nat).
    elim B return (λ (Bz : Nat). Nat) { Z => Z, S (B') Rb => DivC A B' Z B' Z } }
def DivFnT : Dllbc.Term := DivFn
abbrev Div : Term := DivFnT

/-! ### They compute, and they compute at hashmap sizes

    The dividends are SPLICED, not written as surface numerals: `buildNat` expands a
    numeral into that many nested `Term.ctorApp "S"` SYNTAX nodes, so `prog{ Mod 1056
    32 }` would be a 1056-deep Lean term to elaborate. `Term.nat` builds the same
    value from one splice. Worth knowing for the hashmap, whose keys are this size. -/

def pv (t : Term) : Term := Pure.nf 4000000 t
def modOf (a b : Nat) : Term := pv prog{ Mod %(Term.nat a) %(Term.nat b) }
def divOf (a b : Nat) : Term := pv prog{ Div %(Term.nat a) %(Term.nat b) }

example : (modOf 7 3).natOf? == some 1 := by native_decide
example : (modOf 6 3).natOf? == some 0 := by native_decide
example : (modOf 5 8).natOf? == some 5 := by native_decide
example : (modOf 0 3).natOf? == some 0 := by native_decide
example : (modOf 3 0).natOf? == some 0 := by native_decide

example : (divOf 7 3).natOf? == some 2 := by native_decide
example : (divOf 6 3).natOf? == some 2 := by native_decide
example : (divOf 5 8).natOf? == some 0 := by native_decide

-- The Aeneas hashmap's own test keys at its own capacity: `0, 128, 1024, 1056` all
-- land in slot 0 of 32, which is what makes that test exercise the collision list.
example : (modOf 32 32).natOf? == some 0 := by native_decide
example : (modOf 128 32).natOf? == some 0 := by native_decide
example : (modOf 1024 32).natOf? == some 0 := by native_decide
example : (modOf 1056 32).natOf? == some 0 := by native_decide
example : (modOf 1057 32).natOf? == some 1 := by native_decide
example : (divOf 1056 32).natOf? == some 33 := by native_decide

/-! ## The lemma harness (as §23/§24: a closed term against a closed type) -/

def chkL (tm ty : Term) : Bool :=
  match (do let v ← readC 8000 tm; let t ← readC 8000 ty; hasTypeT 8000 v t).run (seedPure [] []) with
  | .ok r _ => r
  | .error _ _ => false

/-! ## M2 — the slot index is below the capacity

    Stated over the state, then specialised. `StepInv` says one increment preserves
    `R + C ≤ B` — its `Z` arm is `LeRefl` (the wrap resets to `(Z, B)`) and its `S`
    arm is one `AddSucc` transport, which is the only place `Add`'s recursion on its
    FIRST argument costs anything. `ModCLt` then never touches the arithmetic again:
    its step is the induction hypothesis at the stepped state, and its base reaches
    `Le R B` from `R + C ≤ B` through `LeAdd` and one `LeTrans`. -/

def StepInv : Term := prog{
  λ (B : Nat). λ (R : Nat). λ (C : Nat).
    elim C return (λ (Cz : Nat). Le (Add R Cz) B → Le (Add (NextR R Cz) (NextC B Cz)) B) {
      Z => λ (H : Le (Add R Z) B). LeRefl B,
      S (C') Rc => λ (H : Le (Add R (S C')) B).
        LeRwL B (Add R (S C')) (S (Add R C')) (AddSucc R C') H } }
def StepInvTy : Term := prog{
  Π (B : Nat) → Π (R : Nat) → Π (C : Nat) →
    Le (Add R C) B → Le (Add (NextR R C) (NextC B C)) B }

example : chkL StepInv StepInvTy = true := by native_decide

def ModCLt : Term := prog{
  λ (A : Nat).
    elim A return (λ (Az : Nat).
        Π (B : Nat) → Π (R : Nat) → Π (C : Nat) →
          Le (Add R C) B → Le (S (ModC Az B R C)) (S B)) {
      Z => λ (B : Nat). λ (R : Nat). λ (C : Nat). λ (H : Le (Add R C) B).
             LeTrans R (Add R C) B (LeAdd R C) H,
      S (A') Ih => λ (B : Nat). λ (R : Nat). λ (C : Nat). λ (H : Le (Add R C) B).
             Ih B (NextR R C) (NextC B C) (StepInv B R C H) } }
def ModCLtTy : Term := prog{
  Π (A : Nat) → Π (B : Nat) → Π (R : Nat) → Π (C : Nat) →
    Le (Add R C) B → Le (S (ModC A B R C)) (S B) }

example : chkL ModCLt ModCLtTy = true := by native_decide

/-- The `S b` form the task asked for. -/
def ModLt : Term := prog{ λ (A : Nat). λ (B : Nat). ModCLt A B Z B (LeRefl B) }
def ModLtTy : Term := prog{ Π (A : Nat) → Π (B : Nat) → Le (S (Mod A (S B))) (S B) }

example : chkL ModLt ModLtTy = true := by native_decide

/-- …and the form a PROGRAM can use. A `fn` cannot take its capacity as the pattern
    `S c` and still let premise (3) refine — `S c` is a constructor applied to a σ,
    which is rigid — so the capacity is an opaque `n` carrying `Le (S Z) n`. -/
def ModLtN : Term := prog{
  λ (A : Nat). λ (N : Nat).
    elim N return (λ (Nz : Nat). Le (S Z) Nz → Le (S (Mod A Nz)) Nz) {
      Z => λ (H : Le (S Z) Z). botElim (Le (S (Mod A Z)) Z) H,
      S (B') Rb => λ (H : Le (S Z) (S B')). ModCLt A B' Z B' (LeRefl B') } }
def ModLtNTy : Term := prog{
  Π (A : Nat) → Π (N : Nat) → Le (S Z) N → Le (S (Mod A N)) N }

example : chkL ModLtN ModLtNTy = true := by native_decide

/-! ## M3 — minting the carve's decomposition

    `Le (S i) n → Σ r. Id Nat n (Add i (S r))`: "i is strictly below n" becomes the
    residue `r` and the equation premise (3) wants CITED. Induction on `i`, casing
    `n` at each level; both `n = Z` arms are `Bot`, the `i = Z` step reads off
    `r := n'`, and the successor step rebuilds the pair through one `IdCongr S`. -/

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

/-! ### The Σ's projections check — and are the WRONG route for a program

    They are here because they are what a comptime consumer would reach for, and
    because their failure is the finding. `ModFst I N Dec` is a term MENTIONING `N`,
    so citing the projected equation makes premise (3) try to solve `n = f(n)` and
    the occurs check refuses it. The Σ has to cross a call instead (M4). -/

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

end Dllbc.Tests.HmProbeMod

import Dllbc.Program
import Dllbc.ProgMacro
import Dllbc.Boundary
import Dllbc.Std
import Dllbc.StdLemmas
import Dllbc.Tests.Diff

/-!
# `Dllbc.Tests.Finite` — bounded machine integers, as a library

DLLBC's `Nat` is unbounded, so the obligations an Aeneas-style extraction spends
most of its proof budget on — "this `usize` addition does not overflow" — simply
do not arise in a DLLBC program. That is a real gap in the comparison, not a
free win: a hashmap written here and a hashmap written in Rust are not solving
the same problem until the DLLBC one has to prove its capacity arithmetic stays
in range.

This file closes it **without touching the kernel**. A bounded integer is a
refinement pack over `Nat`,

    U MAX  :=  Σ0 (n : Nat) → Le n MAX

— a runtime `Nat` paired with a comptime proof that it is at most `MAX` — and
every arithmetic operation is a `fn` whose telescope DEMANDS the bound evidence
for its result. Aeneas' checked arithmetic returns `result`, whose `Fail` case
the caller must discharge downstream; here the same obligation is an evidence
parameter the caller must discharge UPSTREAM, at the call. Same proof, moved to
the other side of the call.

## The unary trade-off, stated once

DLLBC's `Nat` is unary: `S (S (S Z))`. `usize::MAX = 2^64 - 1` is therefore not
a writable numeral, and never will be under this representation — it is 2^64
constructor applications. So:

  * `MAX` is a **symbolic parameter** everywhere a program or a lemma is stated.
    Nothing below ever needs its value; the guard reasoning is `Le`/`Add`/`Mul`
    algebra, which is exactly the shape it has in a real overflow proof.
  * **Executing** tests instantiate `MAX` at small concrete values (16, 255).
    Every proof obligation then reduces to `unit`, because `Le` computes to
    `Unit` on closed arguments — the callers below pass `()` for their bound
    evidence exactly as `ArraySort`'s concrete callers pass `()` for `Le n n`.

The gap between the two is *representation*, not *reasoning*: a binary numeral
kernel would let the same programs and the same lemmas run at `MAX = 2^64 - 1`.
See the recommendation at the foot of this file.
-/

namespace Dllbc.Tests.Finite

open Dllbc
open Dllbc.StdLemmas (LeRefl LeTrans LeUpR LeAdd LeAddL LeAddMonoL LebTrueLe
  LebFalseGt IdTrans IdCongr IdSym AddZero AddSucc AddComm LePredL
  Sub AddSubCancel BoolFT BoolTF LeRwR LeRwL)

/-- Type-check a closed term against a closed type in the pure seed (as §23/§24). -/
def chkL (tm ty : Term) : Bool :=
  match (do let v ← readC 8000 tm; let t ← readC 8000 ty; hasTypeT 8000 v t).run (seedPure [] []) with
  | .ok r _ => r
  | .error _ _ => false

def pv (t : Term) : Term := Pure.nf 4000 t

/-! ## (i) The type

    `U MAX` is a dependent pair whose first component is the RUNTIME value and
    whose second is a COMPTIME proof of the bound — which is what `Σ0` says: the
    binder's case (`n`, lowercase) gives the first component's mode, the `0`
    marks the tail comptime. A value of `U 15` is `Pair(v, h)`; the `h` is not
    data the program can branch on, it is the licence to have built the `v`. -/

/-- `U : Nat → Type` — `U MAX` is the type of naturals no greater than `MAX`. -/
def U : Term := prog{ λ (MAX : Nat). Σ0 (n : Nat) → Le n MAX }

/-- `Val MAX a` — the underlying `Nat`. A `sigmaRec` projection (§9/stage (i)).

    NOTE the motive: the `elim` sugar reads the Σ's domain and family off the
    motive's binder type SYNTACTICALLY, so it cannot be written `U MAX` — the
    pair has to be spelled out at every elimination. -/
def Val : Term := prog{
  λ (MAX : Nat). λ (A : Σ0 (n : Nat) → Le n MAX).
    elim A return (λ (Q : Σ0 (n : Nat) → Le n MAX). Nat) {
      Pair (x) (h) => x } }
def ValTy : Term := prog{ Π (MAX : Nat) → (Σ0 (n : Nat) → Le n MAX) → Nat }

example : chkL Val ValTy = true := by native_decide

/-! ### Construction, and the four ways it is refused

    At a CONCRETE `MAX` the bound proof reduces: `Le 3 15` whnf's to `Unit`, so
    the evidence a caller writes is `unit` and the pack is `Pair(3, unit)`. At an
    out-of-range value `Le 20 15` whnf's to `Bot`, which `unit` does not inhabit
    and nothing else does either — the value is unconstructible, which is the
    whole claim. -/

-- In range: 3 fits in `U 15`.
example : chkL prog{ Pair(3, unit) } prog{ U 15 } = true := by native_decide
-- The boundary is INCLUSIVE, as `usize::MAX` is: 15 fits in `U 15`.
example : chkL prog{ Pair(15, unit) } prog{ U 15 } = true := by native_decide
-- Zero always fits.
example : chkL prog{ Pair(0, unit) } prog{ U 15 } = true := by native_decide

-- REJECTED (1) — out of range by one. `Le 16 15` is `Bot`.
example : chkL prog{ Pair(16, unit) } prog{ U 15 } = false := by native_decide
-- REJECTED (2) — wildly out of range.
example : chkL prog{ Pair(40, unit) } prog{ U 15 } = false := by native_decide
-- REJECTED (3) — no evidence at all: a bare `Nat` is not a `U MAX`. The pack is
-- the type, so "just use the number" is not available.
example : chkL prog{ 3 } prog{ U 15 } = false := by native_decide
-- REJECTED (4) — evidence for the WRONG value. `LeRefl 3 : Le 3 3`, offered as
-- the bound proof of the value 16.
example : chkL prog{ Pair(16, LeRefl 3) } prog{ U 15 } = false := by native_decide

-- The projection computes: `Val 15 (Pair 3 unit) ⇝ 3`.
example : (pv prog{ Val 15 Pair(3, unit) } == pv prog{ 3 }) = true := by native_decide

/-! ### The symbolic pack — what a PROGRAM holds

    Nothing above needs `MAX` concrete. `MkU` is the constructor as a checked
    lemma: given any `n` and any proof that it is in range, the pack exists. It
    is the identity on data; its content is that the two halves travel together. -/

def MkU : Term := prog{
  λ (MAX : Nat). λ (N : Nat). λ (H : Le N MAX). Pair(N, H) }
def MkUTy : Term := prog{
  Π (MAX : Nat) → Π (N : Nat) → Le N MAX → (Σ0 (n : Nat) → Le n MAX) }
example : chkL MkU MkUTy = true := by native_decide

-- `Val` inverts `MkU` DEFINITIONALLY (the ι-rule fires under the binders), so
-- the round-trip is `Refl` rather than an induction.
def ValMkU : Term := prog{
  λ (MAX : Nat). λ (N : Nat). λ (H : Le N MAX). Refl }
def ValMkUTy : Term := prog{
  Π (MAX : Nat) → Π (N : Nat) → Π (H : Le N MAX) → Id Nat (Val MAX (MkU MAX N H)) N }
example : chkL ValMkU ValMkUTy = true := by native_decide

/-- The bound, recovered from a pack — the second projection. Its motive is
    dependent (`Le (Val MAX q) MAX` mentions the first field), so this is
    dependent Σ elimination proper. Every op below uses it to learn its
    arguments' ranges without the caller restating them. -/
def Bnd : Term := prog{
  λ (MAX : Nat). λ (A : Σ0 (n : Nat) → Le n MAX).
    elim A return (λ (Q : Σ0 (n : Nat) → Le n MAX). Le (Val MAX Q) MAX) {
      Pair (x) (h) => h } }
def BndTy : Term := prog{
  Π (MAX : Nat) → Π (A : Σ0 (n : Nat) → Le n MAX) → Le (Val MAX A) MAX }
example : chkL Bnd BndTy = true := by native_decide

/-! ## (ii) The arithmetic the operations are about

    `Add` and `Sub` are already in the library (`Std.addFn`, `StdLemmas.Sub` with
    its `AddSubCancel`); `Mul`, `Div` and `Mod` are not, so they are here.

    `Div`/`Mod` are the **count-up** pair rather than repeated subtraction: both
    recurse structurally on the dividend with the divisor free, incrementing the
    remainder and rolling it over when it reaches the divisor. Structural
    recursion means no fuel parameter and no well-foundedness story, which is
    what makes `DivModId` below a single clean induction. Division by zero
    returns zero (`Eqb (S r) Z` is never `True`, so the remainder just counts up
    and the quotient never increments) — Lean's own convention, and the reason
    `DivU`'s nonzero evidence is about the HARDWARE rather than about totality. -/

def Mul : Term := prog{
  λ (A : Nat). λ (B : Nat).
    elim A return (λ (Az : Nat). Nat) { Z => Z, S (A') Rec => Add B Rec } }
def MulTy : Term := prog{ Π (A : Nat) → Nat → Nat }

def Mod : Term := prog{
  λ (A : Nat). λ (B : Nat).
    elim A return (λ (Az : Nat). Nat) {
      Z => Z,
      S (A') Rec => elim (Eqb (S Rec) B) return (λ (Bz : Bool). Nat) {
        True => Z, False => S Rec } } }
def ModTy : Term := prog{ Π (A : Nat) → Nat → Nat }

def Div : Term := prog{
  λ (A : Nat). λ (B : Nat).
    elim A return (λ (Az : Nat). Nat) {
      Z => Z,
      S (A') Rec => elim (Eqb (S (Mod A' B)) B) return (λ (Bz : Bool). Nat) {
        True => S Rec, False => Rec } } }
def DivTy : Term := prog{ Π (A : Nat) → Nat → Nat }

-- They compute, which is what makes the concrete tests at the foot possible.
example : (pv prog{ Mul 3 4 } == pv prog{ 12 }) = true := by native_decide
example : (pv prog{ Div 7 2 } == pv prog{ 3 }) = true := by native_decide
example : (pv prog{ Mod 7 2 } == pv prog{ 1 }) = true := by native_decide
example : (pv prog{ Div 12 4 } == pv prog{ 3 }) = true := by native_decide
example : (pv prog{ Mod 12 4 } == pv prog{ 0 }) = true := by native_decide
-- Division by zero is zero, and the remainder is the whole dividend.
example : (pv prog{ Div 5 0 } == pv prog{ 0 }) = true := by native_decide
example : (pv prog{ Mod 5 0 } == pv prog{ 5 }) = true := by native_decide

/-! ## (iii) The bound lemmas — what the operations' RESULTS satisfy

    Each op below has to hand back a `U MAX`, which means producing a proof of
    `Le <result> MAX`. Where that proof comes from is the whole design:

      * `AddU`/`MulU` — from the caller. There is no bound to derive; a sum can
        exceed `MAX` and the caller is the only one who knows it does not.
      * `SubU`/`SatSubU`/`DivU` — DERIVED here, from the argument's own bound.
        Truncated subtraction and division only shrink, so `SubLe`/`DivLe` plus
        `LeTrans` discharge the obligation and the caller pays nothing.

    That split is the interesting content: it says exactly which of Rust's
    arithmetic operations can overflow, and it says it as a proof rather than as
    a table someone wrote down. -/

/-- `Eqb`'s true-reflection. The library has the two FALSE directions
    (`EqbGtFalse`, `EqbLtFalse`) and `EqbRefl`, but not this one — `DivModId`'s
    rollover case needs to turn the branch condition back into an equation. -/
def EqbTrueId : Term := prog{
  λ (A : Nat).
    elim A return (λ (Az : Nat). Π (B : Nat) → Id Bool (Eqb Az B) True → Id Nat Az B) {
      Z => λ (B : Nat).
        elim B return (λ (Bz : Nat). Id Bool (Eqb Z Bz) True → Id Nat Z Bz) {
          Z => λ (H : Id Bool (Eqb Z Z) True). Refl,
          S (B') Ihb => λ (H : Id Bool (Eqb Z (S B')) True).
            botElim (Id Nat Z (S B')) (BoolFT H) },
      S (A') Ih => λ (B : Nat).
        elim B return (λ (Bz : Nat). Id Bool (Eqb (S A') Bz) True → Id Nat (S A') Bz) {
          Z => λ (H : Id Bool (Eqb (S A') Z) True).
            botElim (Id Nat (S A') Z) (BoolFT H),
          S (B') Ihb => λ (H : Id Bool (Eqb (S A') (S B')) True).
            IdCongr Nat Nat (λ (N : Nat). S N) A' B' (Ih B' H) } } }
def EqbTrueIdTy : Term := prog{ Π (A : Nat) → Π (B : Nat) → Id Bool (Eqb A B) True → Id Nat A B }
example : chkL EqbTrueId EqbTrueIdTy = true := by native_decide

/-- Truncated subtraction only shrinks: `a - b ≤ a`. This is `SubU`'s whole
    bound argument — the result of a subtraction is in range because the
    MINUEND was. -/
def SubLe : Term := prog{
  λ (A : Nat).
    elim A return (λ (Az : Nat). Π (B : Nat) → Le (Sub Az B) Az) {
      Z => λ (B : Nat). unit,
      S (A') Ih => λ (B : Nat).
        elim B return (λ (Bz : Nat). Le (Sub (S A') Bz) (S A')) {
          Z => LeRefl (S A'),
          S (B') Ihb => LeUpR (Sub A' B') A' (Ih B') } } }
def SubLeTy : Term := prog{ Π (A : Nat) → Π (B : Nat) → Le (Sub A B) A }
example : chkL SubLe SubLeTy = true := by native_decide

/-- Right-multiplication is monotone: `a ≤ b ⟹ a*c ≤ b*c`. The `S`/`S` step is
    one `LeAddMonoL`, because `Mul` recurses on the LEFT factor and both sides
    peel the same `Add c _`. -/
def MulMonoR : Term := prog{
  λ (C : Nat). λ (A : Nat).
    elim A return (λ (Az : Nat). Π (B : Nat) → Le Az B → Le (Mul Az C) (Mul B C)) {
      Z => λ (B : Nat). λ (H : Le Z B). unit,
      S (A') Ih => λ (B : Nat).
        elim B return (λ (Bz : Nat). Le (S A') Bz → Le (Mul (S A') C) (Mul Bz C)) {
          Z => λ (H : Le (S A') Z). botElim (Le (Mul (S A') C) (Mul Z C)) H,
          S (B') Ihb => λ (H : Le (S A') (S B')).
            LeAddMonoL C (Mul A' C) (Mul B' C) (Ih B' H) } } }
def MulMonoRTy : Term := prog{
  Π (C : Nat) → Π (A : Nat) → Π (B : Nat) → Le A B → Le (Mul A C) (Mul B C) }
example : chkL MulMonoR MulMonoRTy = true := by native_decide

/-- Division only shrinks: `a / b ≤ a`, at EVERY divisor including zero. The
    induction cases the same boolean `Div`'s successor arm cases on; the motive
    abstracts the scrutinee so both branches see the quotient they actually
    produce. This is `DivU`'s bound argument. -/
def DivLe : Term := prog{
  λ (A : Nat).
    elim A return (λ (Az : Nat). Π (B : Nat) → Le (Div Az B) Az) {
      Z => λ (B : Nat). unit,
      S (A') Ih => λ (B : Nat).
        elim (Eqb (S (Mod A' B)) B) return (λ (Bz : Bool).
            Le (elim Bz return (λ (Cz : Bool). Nat) {
                  True => S (Div A' B), False => Div A' B }) (S A')) {
          True => Ih B,
          False => LeUpR (Div A' B) A' (Ih B) } } }
def DivLeTy : Term := prog{ Π (A : Nat) → Π (B : Nat) → Le (Div A B) A }
example : chkL DivLe DivLeTy = true := by native_decide

/-- **The division equation**: `a % (b+1) + (a / (b+1)) * (b+1) = a`.

    One induction on the dividend. The successor step cases the SAME boolean
    that `Mod` and `Div` both case on — the rollover test — and the motive
    abstracts it out of both, so the two branches see the pair the definitions
    actually produce. `Refl`-terminated (`… } Refl`) to keep the branch equation
    (the REMEMBER-SCRUTINEE idiom the glue uses): the rollover branch needs
    `Eqb (S r) (S b) = True` back as `r = b`, which is what `EqbTrueId` is for.

    Everything the overflow guard knows about division comes from this one
    lemma. -/
def DivModId : Term := prog{
  λ (B : Nat). λ (A : Nat).
    elim A return (λ (Az : Nat).
        Id Nat (Add (Mod Az (S B)) (Mul (Div Az (S B)) (S B))) Az) {
      Z => Refl,
      S (A') Ih =>
        elim (Eqb (S (Mod A' (S B))) (S B)) return (λ (Bz : Bool).
            Id Bool (Eqb (S (Mod A' (S B))) (S B)) Bz →
            Id Nat (Add (elim Bz return (λ (Cz : Bool). Nat) {
                            True => Z, False => S (Mod A' (S B)) })
                        (Mul (elim Bz return (λ (Cz : Bool). Nat) {
                            True => S (Div A' (S B)), False => Div A' (S B) }) (S B)))
                   (S A')) {
          True => λ (E : Id Bool (Eqb (S (Mod A' (S B))) (S B)) True).
            IdCongr Nat Nat (λ (N : Nat). S N)
              (Add B (Mul (Div A' (S B)) (S B))) A'
              (IdTrans Nat
                (Add B (Mul (Div A' (S B)) (S B)))
                (Add (Mod A' (S B)) (Mul (Div A' (S B)) (S B)))
                A'
                (IdCongr Nat Nat (λ (Z0 : Nat). Add Z0 (Mul (Div A' (S B)) (S B)))
                   B (Mod A' (S B))
                   (IdSym Nat (Mod A' (S B)) B (EqbTrueId (Mod A' (S B)) B E)))
                Ih),
          False => λ (E : Id Bool (Eqb (S (Mod A' (S B))) (S B)) False).
            IdCongr Nat Nat (λ (N : Nat). S N)
              (Add (Mod A' (S B)) (Mul (Div A' (S B)) (S B))) A' Ih
        } Refl } }
def DivModIdTy : Term := prog{
  Π (B : Nat) → Π (A : Nat) → Id Nat (Add (Mod A (S B)) (Mul (Div A (S B)) (S B))) A }
example : chkL DivModId DivModIdTy = true := by native_decide

/-- `(a / (b+1)) * (b+1) ≤ a` — the fact an overflow guard is FOR. Checking
    `x ≤ MAX / k` before computing `x * k` is sound precisely because this holds;
    it is `LeAddL` on the division equation, transported. -/
def DivMulLe : Term := prog{
  λ (B : Nat). λ (A : Nat).
    LeRwR (Mul (Div A (S B)) (S B))
      (Add (Mod A (S B)) (Mul (Div A (S B)) (S B))) A
      (DivModId B A)
      (LeAddL (Mul (Div A (S B)) (S B)) (Mod A (S B))) }
def DivMulLeTy : Term := prog{
  Π (B : Nat) → Π (A : Nat) → Le (Mul (Div A (S B)) (S B)) A }
example : chkL DivMulLe DivMulLeTy = true := by native_decide

end Dllbc.Tests.Finite

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

/-! ## (iv) The operations -/

/-- Why a program was rejected — the message, for the negative twins below. -/
def whyProg (t : Term) : String :=
  match checkProgram t (prog{ Unit }) with | .ok _ => "OK" | .error e => e

/-- **The bounded arithmetic**, as five declarations over a symbolic `MAX`.

    Read the telescopes: every operation whose result CAN leave the range takes
    the bound as an evidence parameter, and every operation whose result cannot
    derives it. That split is the file's main claim, and it is a proof rather
    than a table:

      * `AddU`, `MulU` — `H` is supplied by the CALLER. Nothing about `a ≤ MAX`
        and `b ≤ MAX` implies `a+b ≤ MAX`, so there is no way to derive it here
        and no way to write the call without discharging it.
      * `SubU`, `SatSubU`, `DivU` — derived, from `SubLe`/`DivLe` and the
        argument's own bound (`Bnd MAX a`). The caller pays nothing, because
        subtracting and dividing cannot leave the range.

    This is Aeneas' checked arithmetic with the obligation moved to the other
    side of the call: their `usize_add` returns `result` and the `Fail` case
    propagates until someone discharges it downstream; here it is discharged
    UPSTREAM, at the call, and there is no failure case in the type at all.

    THE UNDERFLOW STORY (`SubU` vs `SatSubU`) — DLLBC's `Sub` is TRUNCATED, so
    `a - b` is in range whatever `b` is and the *bound* obligation is free
    either way. The two differ in what they promise:

      * `SatSubU` takes no evidence and promises only the bound. That is Rust's
        `saturating_sub`, and it is the honest reading of truncation.
      * `SubU` takes `Le (Val b) (Val a)` and promises EXACTNESS —
        `b + (a - b) = a` — as a second, comptime component of its result. The
        evidence is load-bearing there: `AddSubCancel` is exactly the lemma with
        that hypothesis, and without it the equation is false. That is Rust's
        checked `-`, and it is why the evidence parameter is not decoration.

    `DivU`'s `Hnz` is the third kind: the library `Div` is TOTAL (`a / 0 = 0`),
    so the evidence buys nothing about the bound and nothing about the value. It
    is there because a real `div` FAULTS, and the point of the exercise is to
    carry the obligations a machine actually imposes. -/
def uOps (tail : Term) : Term := prog{
  fn AddU (MAX : Nat, a : (Σ0 (n : Nat) → Le n MAX), b : (Σ0 (n : Nat) → Le n MAX),
           H : Le (Add (Val MAX a) (Val MAX b)) MAX)
      -> (Σ0 (n : Nat) → Le n MAX)
      { Pair(Add (Val MAX a) (Val MAX b), H) };
  fn MulU (MAX : Nat, a : (Σ0 (n : Nat) → Le n MAX), b : (Σ0 (n : Nat) → Le n MAX),
           H : Le (Mul (Val MAX a) (Val MAX b)) MAX)
      -> (Σ0 (n : Nat) → Le n MAX)
      { Pair(Mul (Val MAX a) (Val MAX b), H) };
  fn SatSubU (MAX : Nat, a : (Σ0 (n : Nat) → Le n MAX), b : (Σ0 (n : Nat) → Le n MAX))
      -> (Σ0 (n : Nat) → Le n MAX)
      { Pair(Sub (Val MAX a) (Val MAX b),
             LeTrans (Sub (Val MAX a) (Val MAX b)) (Val MAX a) MAX
               (SubLe (Val MAX a) (Val MAX b)) (Bnd MAX a)) };
  fn SubU (MAX : Nat, a : (Σ0 (n : Nat) → Le n MAX), b : (Σ0 (n : Nat) → Le n MAX),
           H : Le (Val MAX b) (Val MAX a))
      -> (Σ0 (r : (Σ0 (n : Nat) → Le n MAX))
            → Id Nat (Add (Val MAX b) (Val MAX r)) (Val MAX a))
      { Pair(Pair(Sub (Val MAX a) (Val MAX b),
                  LeTrans (Sub (Val MAX a) (Val MAX b)) (Val MAX a) MAX
                    (SubLe (Val MAX a) (Val MAX b)) (Bnd MAX a)),
             AddSubCancel (Val MAX a) (Val MAX b) H) };
  fn DivU (MAX : Nat, a : (Σ0 (n : Nat) → Le n MAX), b : (Σ0 (n : Nat) → Le n MAX),
           Hnz : Le (S Z) (Val MAX b))
      -> (Σ0 (n : Nat) → Le n MAX)
      { Pair(Div (Val MAX a) (Val MAX b),
             LeTrans (Div (Val MAX a) (Val MAX b)) (Val MAX a) MAX
               (DivLe (Val MAX a) (Val MAX b)) (Bnd MAX a)) };
  %tail }

example : progOk (uOps prog{ () }) = true := by native_decide

/-! ### Negative twins at the DECLARATION

    One per way the pack can be built dishonestly. These are the interesting
    half: the positive tests say the style is writable, these say it is not
    evadable. -/

-- (1) NO EVIDENCE. Drop `H` from the telescope and there is nothing to put in
-- the pack's proof slot; `unit` does not inhabit `Le (Add σₐ σᵦ) σₘ`.
def addUNoEvidence : Term := prog{
  fn AddUBad (MAX : Nat, a : (Σ0 (n : Nat) → Le n MAX), b : (Σ0 (n : Nat) → Le n MAX))
      -> (Σ0 (n : Nat) → Le n MAX)
      { Pair(Add (Val MAX a) (Val MAX b), unit) };
  () }

-- (2) **THE MONEY TEST** — the evidence is for the wrong ARITHMETIC. The
-- telescope demands `Le (a+b) MAX`; the body multiplies. Both halves are
-- individually fine and the pack is REJECTED, because the pair's second field
-- is checked at `Le (a*b) MAX` and `H` does not have that type. The proof is
-- tied to the operation actually performed, so an op cannot be quietly swapped
-- under a signature that still reads plausibly.
def addUWrongOp : Term := prog{
  fn AddUBad (MAX : Nat, a : (Σ0 (n : Nat) → Le n MAX), b : (Σ0 (n : Nat) → Le n MAX),
              H : Le (Add (Val MAX a) (Val MAX b)) MAX)
      -> (Σ0 (n : Nat) → Le n MAX)
      { Pair(Mul (Val MAX a) (Val MAX b), H) };
  () }

-- (3) The derived bound does not stretch. `SubLe` bounds a DIFFERENCE by the
-- minuend; offered as the bound of a SUM it is simply the wrong lemma.
def satSubUWrongOp : Term := prog{
  fn SatSubUBad (MAX : Nat, a : (Σ0 (n : Nat) → Le n MAX), b : (Σ0 (n : Nat) → Le n MAX))
      -> (Σ0 (n : Nat) → Le n MAX)
      { Pair(Add (Val MAX a) (Val MAX b),
             LeTrans (Sub (Val MAX a) (Val MAX b)) (Val MAX a) MAX
               (SubLe (Val MAX a) (Val MAX b)) (Bnd MAX a)) };
  () }

-- (4) The underflow evidence IS load-bearing. Same body as `SubU`, same
-- exactness postcondition, `H` deleted from the telescope: `b + (a - b) = a`
-- is not definitional (and not true) without it, so `Refl` cannot close it and
-- `AddSubCancel` cannot be applied.
def subUNoUnderflowEv : Term := prog{
  fn SubUBad (MAX : Nat, a : (Σ0 (n : Nat) → Le n MAX), b : (Σ0 (n : Nat) → Le n MAX))
      -> (Σ0 (r : (Σ0 (n : Nat) → Le n MAX))
            → Id Nat (Add (Val MAX b) (Val MAX r)) (Val MAX a))
      { Pair(Pair(Sub (Val MAX a) (Val MAX b),
                  LeTrans (Sub (Val MAX a) (Val MAX b)) (Val MAX a) MAX
                    (SubLe (Val MAX a) (Val MAX b)) (Bnd MAX a)),
             Refl) };
  () }

-- All four fail the same way and it is the right way: the returned PACK is
-- audited against the declared `U MAX`, and its second field does not inhabit
-- the type the first field forces on it.
example : progRejects addUNoEvidence "does not have return type" = true := by native_decide
example : progRejects addUWrongOp "does not have return type" = true := by native_decide
example : progRejects satSubUWrongOp "does not have return type" = true := by native_decide
example : progRejects subUNoUnderflowEv "does not have return type" = true := by native_decide

/-! ### (v) Callers at a concrete `MAX`, checking AND executing

    Everything above is symbolic in `MAX`. These instantiate it — 15, and 255
    for a byte — and that is where the unary trade-off shows itself and where it
    stops mattering: at a closed `MAX` every `Le` obligation whnf's to `Unit`,
    so the evidence a caller writes is `unit`, exactly as `ArraySort`'s concrete
    callers pass `()` for `Le n n`. The proofs did not go away; they were
    discharged by computation. -/

def tn (n : Nat) : Term := Term.nat n

def natOfV : Nat → Dllbc.Val → Option Nat
  | f, v =>
    match v.asCtor?, f with
    | some ("Z", []), _ => some 0
    | some ("S", [w]), f' + 1 => (natOfV f' w).map (· + 1)
    | _, _ => none

/-- Run the program and read the `Nat` its `out` binding holds. -/
def runOut (t : Term) : Option Nat :=
  match runProgram t with
  | .ok env => (env.lookup "out").bind (natOfV 4000)
  | .error _ => none

def addCall (m a b : Nat) : Term := uOps prog{
  let x = Pair(%(tn a), unit);
  let y = Pair(%(tn b), unit);
  let r = AddU(%(tn m), x, y, unit);
  let out = Val %(tn m) r;
  () }

def mulCall (m a b : Nat) : Term := uOps prog{
  let x = Pair(%(tn a), unit);
  let y = Pair(%(tn b), unit);
  let r = MulU(%(tn m), x, y, unit);
  let out = Val %(tn m) r;
  () }

def divCall (m a b : Nat) : Term := uOps prog{
  let x = Pair(%(tn a), unit);
  let y = Pair(%(tn b), unit);
  let r = DivU(%(tn m), x, y, unit);
  let out = Val %(tn m) r;
  () }

def satSubCall (m a b : Nat) : Term := uOps prog{
  let x = Pair(%(tn a), unit);
  let y = Pair(%(tn b), unit);
  let r = SatSubU(%(tn m), x, y);
  let out = Val %(tn m) r;
  () }

-- `SubU` hands back a PAIR — the bounded difference and the exactness
-- certificate — so its caller destructures before reading the value.
def subCall (m a b : Nat) : Term := uOps prog{
  let x = Pair(%(tn a), unit);
  let y = Pair(%(tn b), unit);
  let r = SubU(%(tn m), x, y, unit);
  match r { Pair(q, He) => { let out = Val %(tn m) q; () } } }

/-! #### Accepted, and they RUN to the right numbers -/

-- 7 + 8 = 15 fits exactly in `U 15` — the inclusive boundary, checked and run.
example : progOk (addCall 15 7 8) = true := by native_decide
example : runOut (addCall 15 7 8) == some 15 := by native_decide
/-- `progOk` with the step budget as a parameter — `checkProgram` hardcodes
    `defaultFuel = 1000`, and the unary representation spends that budget in
    proportion to `MAX`. This is the same walk with the constant exposed. -/
def progOkFuel (f : Nat) (t : Term) : Bool :=
  match auditPaths (prog{ Unit })
      ((explore f (atBoundary t) initSt).map
        (fun r => r.bind (fun p =>
          match (endScope f).run p.2 with
          | .ok _ st => .ok (p.1, st)
          | .error e _ => .error e))) with
  | .ok _ => true | .error _ => false

/-! #### THE UNARY BILL, measured

    A concrete `MAX` costs the checking machine `O(MAX)` steps, because `Le a b`
    is `b` nested `natRec` unfoldings. `checkProgram` runs at `defaultFuel =
    1000`, so a whole program's checking shares one budget of 1000 and the
    concrete `MAX` a test may use is capped around **140** — `addCall 140 70 70`
    checks, `addCall 150 75 75` does not.

    That cap is the HARNESS CONSTANT and not the design: the same programs check
    at `MAX = 255` when the walk is given 20000 steps. So the unary bill is a
    linear slowdown with a configurable ceiling, not a wall — and it is a bill on
    EXECUTION and on concrete tests only. Nothing symbolic in `MAX` pays it,
    which is every program and every lemma in this file. -/

example : progOk (addCall 140 70 70) = true := by native_decide
example : progOk (addCall 150 75 75) = false := by native_decide
example : progOkFuel 20000 (addCall 255 200 55) = true := by native_decide
example : progOkFuel 20000 (mulCall 255 16 15) = true := by native_decide
-- 3 * 5 = 15.
example : progOk (mulCall 15 3 5) = true := by native_decide
example : runOut (mulCall 15 3 5) == some 15 := by native_decide
-- 13 / 4 = 3, with the divisor nonzero.
example : progOk (divCall 15 13 4) = true := by native_decide
example : runOut (divCall 15 13 4) == some 3 := by native_decide
-- Checked subtraction, and the exactness certificate travels with it.
example : progOk (subCall 15 12 5) = true := by native_decide
example : runOut (subCall 15 12 5) == some 7 := by native_decide
-- Saturating subtraction takes no evidence and clamps at zero.
example : progOk (satSubCall 15 5 12) = true := by native_decide
example : runOut (satSubCall 15 5 12) == some 0 := by native_decide

/-! #### Rejected — the obligation is literally `Bot`

    Each of these is a call the type checker refuses because the evidence
    argument's parameter type has computed to `Bot`. The message says so:

        call: comptime argument (unit) does not have its parameter type (Bot)

    That is the whole exercise in one line. `10 + 10` in a `U 15` is not a
    runtime panic, not a `Fail` case to be propagated, and not a lint — it is a
    call that does not type-check, at the call. -/

def botNeedle : String := "does not have its parameter type (Bot)"

-- 10 + 10 = 20 > 15. OVERFLOW, refused.
example : progRejects (addCall 15 10 10) botNeedle = true := by native_decide
-- …and one past the boundary, which is where an off-by-one guard would hide.
example : progRejects (addCall 15 8 8) botNeedle = true := by native_decide
-- 200 + 100 in a byte.

-- 4 * 5 = 20 > 15. Multiplication overflow, refused.
example : progRejects (mulCall 15 4 5) botNeedle = true := by native_decide
-- 16 * 16 in a byte.

-- DIVISION BY ZERO, refused — `Hnz : Le 1 0` is `Bot`.
example : progRejects (divCall 15 13 0) botNeedle = true := by native_decide
-- UNDERFLOW, refused — `5 - 12` has no exact answer, and `Le 12 5` is `Bot`.
example : progRejects (subCall 15 5 12) botNeedle = true := by native_decide
-- Off by one at the underflow boundary: `5 - 6`.
example : progRejects (subCall 15 5 6) botNeedle = true := by native_decide
-- …while `5 - 5` is fine, so the boundary is where it should be.
example : progOk (subCall 15 5 5) = true := by native_decide
example : runOut (subCall 15 5 5) == some 0 := by native_decide

-- The pack itself refuses an out-of-range LITERAL, before any operation: a
-- caller cannot smuggle 20 into a `U 15` to begin with.
def badLiteral : Term := uOps prog{
  let x = Pair(20, unit);
  let y = Pair(1, unit);
  let r = AddU(15, x, y, unit);
  let out = Val 15 r;
  () }
-- The needle is different here, and the difference is the point: the whole
-- ARGUMENT is refused, not one comptime field of it. `Pair(20, unit)` never
-- becomes a `U 15` in the first place, so the call fails before any obligation
-- about the addition is reached.
example : progRejects badLiteral "does not have its parameter type" = true := by native_decide

end Dllbc.Tests.Finite

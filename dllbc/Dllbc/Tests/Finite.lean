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
  * **Executing** tests instantiate `MAX` at small concrete values (15 mostly;
    63 and 127 for the composite, 140 and 255 where the ceiling is being
    measured). Every proof obligation then reduces to `unit`, because `Le`
    computes to `Unit` on closed arguments — the callers below pass `()` for
    their bound evidence exactly as `ArraySort`'s concrete callers pass `()` for
    `Le n n`.

One warning is worth reading before the code: **this normalizer has no
sharing**, so a recursive comptime definition that mentions its recursive result
twice is exponential and presents as a build that never finishes. §ii records
what that cost this file and the shape that avoids it.

The gap between the two is *representation*, not *reasoning*: a binary numeral
kernel would let the same programs and the same lemmas run at `MAX = 2^64 - 1`.
See the recommendation at the foot of this file.
-/

namespace Dllbc.Tests.Finite

open Dllbc
open Dllbc.StdLemmas (LeRefl LeTrans LeUpR LeAdd LeAddL LeAddMonoL LebTrueLe
  LebFalseGt IdTrans IdCongr IdSym AddZero AddSucc AddComm LePredL
  Sub AddSubCancel BoolFT BoolTF LeRwR LeRwL AddAssoc)

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

    **`Div`/`Mod` CARRY THEIR STATE, and the textbook spelling of them is a trap.**
    The obvious definition is the count-up pair —

        Mod (S a') b  =  let r = Mod a' b ; if S r == b then Z else S r

    — and it is EXPONENTIAL in this normalizer, which has no sharing: `r` occurs
    twice (once in the test, once in the branch) and the whole recursion is
    re-derived under each occurrence. That is not a guess; the first version of
    this file was written that way and measured, at divisor 5:

        dividend   4    6    8   10   12   14   16    18
        Mod       3ms  3ms 11ms 21ms 85ms 338ms 673ms 2716ms

    — a doubling per unit of dividend. It presents as a build that never
    finishes rather than as an error, and it is why `try_resize` below ran
    instantly at `MAX = 15` and not at all at `MAX = 63`.

    The shape that works carries the would-be-duplicated value as an ARGUMENT
    and asks the question of the argument, so `Rec` occurs exactly once. The
    state is `(R, C)`: `R` is the residue so far, `C` is how many more
    increments fit before it wraps, and `Add R C = B` is the invariant. `NextR`,
    `NextC` and `NextQ` are the three non-recursive answers to "what does this
    component do at one increment". Credit where due: this shape and the
    measurement that motivates it are the `hm-probe-mod` lane's (`ModC` in
    `Dllbc/Tests/HmProbeMod.lean`, and the rule now written down in
    `docs/04-language.md`). If either version reaches `Std`, the other should be
    deleted rather than kept as a second copy.

    Division by zero is zero and so is the remainder — `Mod A Z = Z`, where
    Lean's `%` returns the dividend. Nothing here depends on the choice: every
    lemma below is stated at an `S b` divisor or under a `Le (S Z) d`
    hypothesis, which is why `DivU`'s nonzero evidence is about the HARDWARE
    rather than about totality. -/

def Mul : Term := prog{
  λ (A : Nat). λ (B : Nat).
    elim A return (λ (Az : Nat). Nat) { Z => Z, S (A') Rec => Add B Rec } }
def MulTy : Term := prog{ Π (A : Nat) → Nat → Nat }

def NextR : Term := prog{
  λ (R : Nat). λ (C : Nat).
    elim C return (λ (Cz : Nat). Nat) { Z => Z, S (C') Rc => S(R) } }
def NextC : Term := prog{
  λ (B : Nat). λ (C : Nat).
    elim C return (λ (Cz : Nat). Nat) { Z => B, S (C') Rc => C' } }
def NextQ : Term := prog{
  λ (Q : Nat). λ (C : Nat).
    elim C return (λ (Cz : Nat). Nat) { Z => S(Q), S (C') Rc => Q } }

/-- The residue after `A` increments from state `(R, C)`. One `Rec`, one
    occurrence — which is the whole point. -/
def ModC : Term := prog{
  λ (A : Nat).
    elim A return (λ (Az : Nat). Π (B : Nat) → Π (R : Nat) → Π (C : Nat) → Nat) {
      Z => λ (B : Nat). λ (R : Nat). λ (C : Nat). R,
      S (A') Rec => λ (B : Nat). λ (R : Nat). λ (C : Nat).
        Rec B (NextR R C) (NextC B C) } }
def Mod : Term := prog{
  λ (A : Nat). λ (B : Nat).
    elim B return (λ (Bz : Nat). Nat) { Z => Z, S (B') Rb => ModC A B' Z B' } }
def ModTy : Term := prog{ Π (A : Nat) → Nat → Nat }

/-- The quotient rides the same state, ticking exactly when `C` wraps. -/
def DivC : Term := prog{
  λ (A : Nat).
    elim A return (λ (Az : Nat).
        Π (B : Nat) → Π (R : Nat) → Π (C : Nat) → Π (Q : Nat) → Nat) {
      Z => λ (B : Nat). λ (R : Nat). λ (C : Nat). λ (Q : Nat). Q,
      S (A') Rec => λ (B : Nat). λ (R : Nat). λ (C : Nat). λ (Q : Nat).
        Rec B (NextR R C) (NextC B C) (NextQ Q C) } }
def Div : Term := prog{
  λ (A : Nat). λ (B : Nat).
    elim B return (λ (Bz : Nat). Nat) { Z => Z, S (B') Rb => DivC A B' Z B' Z } }
def DivTy : Term := prog{ Π (A : Nat) → Nat → Nat }

-- They compute, which is what makes the concrete tests at the foot possible.
example : (pv prog{ Mul 3 4 } == pv prog{ 12 }) = true := by native_decide
example : (pv prog{ Div 7 2 } == pv prog{ 3 }) = true := by native_decide
example : (pv prog{ Mod 7 2 } == pv prog{ 1 }) = true := by native_decide
example : (pv prog{ Div 12 4 } == pv prog{ 3 }) = true := by native_decide
example : (pv prog{ Mod 12 4 } == pv prog{ 0 }) = true := by native_decide
example : (pv prog{ Div 63 5 } == pv prog{ 12 }) = true := by native_decide
example : (pv prog{ Mod 63 5 } == pv prog{ 3 }) = true := by native_decide
-- Division by zero is zero, and so is the remainder.
example : (pv prog{ Div 5 0 } == pv prog{ 0 }) = true := by native_decide
example : (pv prog{ Mod 5 0 } == pv prog{ 0 }) = true := by native_decide

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

/-! ### The division equation, over the STATE

    The accumulator shape moves the work into the invariant. `Add R C = B` says
    the state is consistent; `NextInv` says one increment preserves it, and
    `NextStep` says what one increment does to `R + Q*(B+1)` — it adds one, in
    both the wrap and the no-wrap case, for different reasons. Those two are the
    whole content, and `DivModC` is the induction that iterates them. -/

/-- One increment preserves `Add R C = B`. The wrap case does not even need the
    hypothesis (`Add Z B = B` outright); the ordinary case is one `AddSucc`. -/
def NextInv : Term := prog{
  λ (B : Nat). λ (R : Nat). λ (C : Nat).
    elim C return (λ (Cz : Nat).
        Id Nat (Add R Cz) B → Id Nat (Add (NextR R Cz) (NextC B Cz)) B) {
      Z => λ (H : Id Nat (Add R Z) B). Refl,
      S (C') Rc => λ (H : Id Nat (Add R (S C')) B).
        IdTrans Nat (S (Add R C')) (Add R (S C')) B
          (IdSym Nat (Add R (S C')) (S (Add R C')) (AddSucc R C')) H } }
def NextInvTy : Term := prog{
  Π (B : Nat) → Π (R : Nat) → Π (C : Nat) → Id Nat (Add R C) B →
    Id Nat (Add (NextR R C) (NextC B C)) B }
example : chkL NextInv NextInvTy = true := by native_decide

/-- One increment adds one to `R + Q*(B+1)`. No-wrap: `R` becomes `S R` and the
    quotient is untouched, so it is `Refl`. Wrap: `R` drops to `Z` and the
    quotient gains one, which contributes a whole `S B` — and the two balance
    only because the invariant says `R` WAS `B`. That is the one place the
    invariant does real work. -/
def NextStep : Term := prog{
  λ (B : Nat). λ (R : Nat). λ (C : Nat). λ (Q : Nat).
    elim C return (λ (Cz : Nat).
        Id Nat (Add R Cz) B →
        Id Nat (Add (NextR R Cz) (Mul (NextQ Q Cz) (S B)))
               (S (Add R (Mul Q (S B))))) {
      Z => λ (H : Id Nat (Add R Z) B).
        IdCongr Nat Nat (λ (Z0 : Nat). S (Add Z0 (Mul Q (S B)))) B R
          (IdSym Nat R B
            (IdTrans Nat R (Add R Z) B
              (IdSym Nat (Add R Z) R (AddZero R)) H)),
      S (C') Rc => λ (H : Id Nat (Add R (S C')) B). Refl } }
def NextStepTy : Term := prog{
  Π (B : Nat) → Π (R : Nat) → Π (C : Nat) → Π (Q : Nat) → Id Nat (Add R C) B →
    Id Nat (Add (NextR R C) (Mul (NextQ Q C) (S B))) (S (Add R (Mul Q (S B)))) }
example : chkL NextStep NextStepTy = true := by native_decide

/-- **The division equation over the state**: running `A` increments from a
    consistent `(R, C, Q)` leaves `residue + quotient*(B+1)` exactly `A` more
    than it started. One induction on `A`, generalized over the whole state —
    `R`, `C` and `Q` all change at every step, so none of them can be fixed. -/
def DivModC : Term := prog{
  λ (B : Nat). λ (A : Nat).
    elim A return (λ (Az : Nat). Π (R : Nat) → Π (C : Nat) → Π (Q : Nat) →
        Id Nat (Add R C) B →
        Id Nat (Add (ModC Az B R C) (Mul (DivC Az B R C Q) (S B)))
               (Add Az (Add R (Mul Q (S B))))) {
      Z => λ (R : Nat). λ (C : Nat). λ (Q : Nat). λ (Hi : Id Nat (Add R C) B). Refl,
      S (A') Ih => λ (R : Nat). λ (C : Nat). λ (Q : Nat). λ (Hi : Id Nat (Add R C) B).
        IdTrans Nat
          (Add (ModC A' B (NextR R C) (NextC B C))
               (Mul (DivC A' B (NextR R C) (NextC B C) (NextQ Q C)) (S B)))
          (Add A' (Add (NextR R C) (Mul (NextQ Q C) (S B))))
          (S (Add A' (Add R (Mul Q (S B)))))
          (Ih (NextR R C) (NextC B C) (NextQ Q C) (NextInv B R C Hi))
          (IdTrans Nat
            (Add A' (Add (NextR R C) (Mul (NextQ Q C) (S B))))
            (Add A' (S (Add R (Mul Q (S B)))))
            (S (Add A' (Add R (Mul Q (S B)))))
            (IdCongr Nat Nat (λ (Z0 : Nat). Add A' Z0)
              (Add (NextR R C) (Mul (NextQ Q C) (S B)))
              (S (Add R (Mul Q (S B))))
              (NextStep B R C Q Hi))
            (AddSucc A' (Add R (Mul Q (S B))))) } }
def DivModCTy : Term := prog{
  Π (B : Nat) → Π (A : Nat) → Π (R : Nat) → Π (C : Nat) → Π (Q : Nat) →
    Id Nat (Add R C) B →
    Id Nat (Add (ModC A B R C) (Mul (DivC A B R C Q) (S B)))
           (Add A (Add R (Mul Q (S B)))) }
example : chkL DivModC DivModCTy = true := by native_decide

/-- **The division equation**: `a % (b+1) + (a / (b+1)) * (b+1) = a`. The state
    version at its start point `(Z, B, Z)`, whose invariant is `Refl`, plus one
    `AddZero` to clear the `+ 0` the general statement carries.

    Everything the overflow guard knows about division comes from this. -/
def DivModId : Term := prog{
  λ (B : Nat). λ (A : Nat).
    IdTrans Nat (Add (Mod A (S B)) (Mul (Div A (S B)) (S B))) (Add A Z) A
      (DivModC B A Z B Z Refl) (AddZero A) }
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

/-- `q ≤ q * (b+1)` — multiplying by a positive factor does not shrink. -/
def MulLeSelf : Term := prog{
  λ (B : Nat). λ (Q : Nat).
    elim Q return (λ (Qz : Nat). Le Qz (Mul Qz (S B))) {
      Z => unit,
      S (Q') Ih => LeTrans Q' (Mul Q' (S B)) (Add B (Mul Q' (S B)))
                     Ih (LeAddL (Mul Q' (S B)) B) } }
def MulLeSelfTy : Term := prog{ Π (B : Nat) → Π (Q : Nat) → Le Q (Mul Q (S B)) }
example : chkL MulLeSelf MulLeSelfTy = true := by native_decide

/-- Division only shrinks: `a / b ≤ a`, at EVERY divisor including zero — this
    is `DivU`'s bound argument. Under the accumulator definitions it is no
    longer its own induction: case the divisor, and at `S b` the quotient is
    below `quotient * (b+1)` which is below `a`. -/
def DivLe : Term := prog{
  λ (A : Nat). λ (B : Nat).
    elim B return (λ (Bz : Nat). Le (Div A Bz) A) {
      Z => unit,
      S (B') Rb => LeTrans (Div A (S B')) (Mul (Div A (S B')) (S B')) A
                     (MulLeSelf B' (Div A (S B')))
                     (DivMulLe B' A) } }
def DivLeTy : Term := prog{ Π (A : Nat) → Π (B : Nat) → Le (Div A B) A }
example : chkL DivLe DivLeTy = true := by native_decide

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

/-! ## (v) Callers at a concrete `MAX`, checking AND executing

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

/-! ## (vi) Multiplication algebra — the price of the real guard

    The composite below is the Aeneas `try_resize` guard, and its second
    obligation is about `(capacity * 2) * dividend` while the guard gives a fact
    about `capacity * dividend`. Rust's evaluation order and the guard's
    derivation order disagree, so the two have to be reconciled — which means
    commutativity and associativity of `Mul`, which means distributivity, none
    of which the library had. Six lemmas, all standard, all one induction each. -/

def MulZeroR : Term := prog{
  λ (A : Nat). elim A return (λ (Az : Nat). Id Nat (Mul Az Z) Z) {
    Z => Refl,
    S (A') Ih => Ih } }
def MulZeroRTy : Term := prog{ Π (A : Nat) → Id Nat (Mul A Z) Z }
example : chkL MulZeroR MulZeroRTy = true := by native_decide

/-- `a + (b + c) = b + (a + c)` — the shuffle `MulSuccR`'s step needs, out of
    the existing `AddAssoc`/`AddComm`. -/
def AddSwapL : Term := prog{
  λ (A : Nat). λ (B : Nat). λ (C : Nat).
    IdTrans Nat (Add A (Add B C)) (Add (Add A B) C) (Add B (Add A C))
      (IdSym Nat (Add (Add A B) C) (Add A (Add B C)) (AddAssoc A B C))
      (IdTrans Nat (Add (Add A B) C) (Add (Add B A) C) (Add B (Add A C))
        (IdCongr Nat Nat (λ (X : Nat). Add X C) (Add A B) (Add B A) (AddComm A B))
        (AddAssoc B A C)) }
def AddSwapLTy : Term := prog{
  Π (A : Nat) → Π (B : Nat) → Π (C : Nat) → Id Nat (Add A (Add B C)) (Add B (Add A C)) }
example : chkL AddSwapL AddSwapLTy = true := by native_decide

def MulSuccR : Term := prog{
  λ (A : Nat).
    elim A return (λ (Az : Nat). Π (B : Nat) → Id Nat (Mul Az (S B)) (Add Az (Mul Az B))) {
      Z => λ (B : Nat). Refl,
      S (A') Ih => λ (B : Nat).
        IdCongr Nat Nat (λ (N : Nat). S N)
          (Add B (Mul A' (S B))) (Add A' (Add B (Mul A' B)))
          (IdTrans Nat (Add B (Mul A' (S B))) (Add B (Add A' (Mul A' B)))
             (Add A' (Add B (Mul A' B)))
            (IdCongr Nat Nat (λ (X : Nat). Add B X)
              (Mul A' (S B)) (Add A' (Mul A' B)) (Ih B))
            (AddSwapL B A' (Mul A' B))) } }
def MulSuccRTy : Term := prog{
  Π (A : Nat) → Π (B : Nat) → Id Nat (Mul A (S B)) (Add A (Mul A B)) }
example : chkL MulSuccR MulSuccRTy = true := by native_decide

def MulComm : Term := prog{
  λ (A : Nat).
    elim A return (λ (Az : Nat). Π (B : Nat) → Id Nat (Mul Az B) (Mul B Az)) {
      Z => λ (B : Nat). IdSym Nat (Mul B Z) Z (MulZeroR B),
      S (A') Ih => λ (B : Nat).
        IdTrans Nat (Add B (Mul A' B)) (Add B (Mul B A')) (Mul B (S A'))
          (IdCongr Nat Nat (λ (X : Nat). Add B X) (Mul A' B) (Mul B A') (Ih B))
          (IdSym Nat (Mul B (S A')) (Add B (Mul B A')) (MulSuccR B A')) } }
def MulCommTy : Term := prog{ Π (A : Nat) → Π (B : Nat) → Id Nat (Mul A B) (Mul B A) }
example : chkL MulComm MulCommTy = true := by native_decide

def MulDistR : Term := prog{
  λ (A : Nat).
    elim A return (λ (Az : Nat). Π (B : Nat) → Π (C : Nat) →
        Id Nat (Mul (Add Az B) C) (Add (Mul Az C) (Mul B C))) {
      Z => λ (B : Nat). λ (C : Nat). Refl,
      S (A') Ih => λ (B : Nat). λ (C : Nat).
        IdTrans Nat (Add C (Mul (Add A' B) C)) (Add C (Add (Mul A' C) (Mul B C)))
            (Add (Add C (Mul A' C)) (Mul B C))
          (IdCongr Nat Nat (λ (X : Nat). Add C X)
            (Mul (Add A' B) C) (Add (Mul A' C) (Mul B C)) (Ih B C))
          (IdSym Nat (Add (Add C (Mul A' C)) (Mul B C))
            (Add C (Add (Mul A' C) (Mul B C))) (AddAssoc C (Mul A' C) (Mul B C))) } }
def MulDistRTy : Term := prog{
  Π (A : Nat) → Π (B : Nat) → Π (C : Nat) →
    Id Nat (Mul (Add A B) C) (Add (Mul A C) (Mul B C)) }
example : chkL MulDistR MulDistRTy = true := by native_decide

def MulAssoc : Term := prog{
  λ (A : Nat).
    elim A return (λ (Az : Nat). Π (B : Nat) → Π (C : Nat) →
        Id Nat (Mul (Mul Az B) C) (Mul Az (Mul B C))) {
      Z => λ (B : Nat). λ (C : Nat). Refl,
      S (A') Ih => λ (B : Nat). λ (C : Nat).
        IdTrans Nat (Mul (Add B (Mul A' B)) C) (Add (Mul B C) (Mul (Mul A' B) C))
            (Add (Mul B C) (Mul A' (Mul B C)))
          (MulDistR B (Mul A' B) C)
          (IdCongr Nat Nat (λ (X : Nat). Add (Mul B C) X)
            (Mul (Mul A' B) C) (Mul A' (Mul B C)) (Ih B C)) } }
def MulAssocTy : Term := prog{
  Π (A : Nat) → Π (B : Nat) → Π (C : Nat) → Id Nat (Mul (Mul A B) C) (Mul A (Mul B C)) }
example : chkL MulAssoc MulAssocTy = true := by native_decide

/-- `(a*b)*c = (a*c)*b` — the exact reconciliation the guard needs, and the only
    consumer of the four lemmas above. -/
def MulSwapR : Term := prog{
  λ (A : Nat). λ (B : Nat). λ (C : Nat).
    IdTrans Nat (Mul (Mul A B) C) (Mul A (Mul B C)) (Mul (Mul A C) B)
      (MulAssoc A B C)
      (IdTrans Nat (Mul A (Mul B C)) (Mul A (Mul C B)) (Mul (Mul A C) B)
        (IdCongr Nat Nat (λ (X : Nat). Mul A X) (Mul B C) (Mul C B) (MulComm B C))
        (IdSym Nat (Mul (Mul A C) B) (Mul A (Mul C B)) (MulAssoc A C B))) }
def MulSwapRTy : Term := prog{
  Π (A : Nat) → Π (B : Nat) → Π (C : Nat) → Id Nat (Mul (Mul A B) C) (Mul (Mul A C) B) }
example : chkL MulSwapR MulSwapRTy = true := by native_decide

/-- `DivMulLe` with the divisor's nonzero-ness as a HYPOTHESIS rather than as an
    `S` pattern. The guard's dividend is a runtime value carrying a `Le 1 d`
    proof, not a constructor the program may split, so this is the form that is
    actually applicable at a call site. Three lines: case the divisor, kill the
    zero case with the hypothesis. -/
def DivMulLeNz : Term := prog{
  λ (D : Nat).
    elim D return (λ (Dz : Nat). Π (A : Nat) → Le (S Z) Dz → Le (Mul (Div A Dz) Dz) A) {
      Z => λ (A : Nat). λ (H : Le (S Z) Z). botElim (Le (Mul (Div A Z) Z) A) H,
      S (D') Ih => λ (A : Nat). λ (H : Le (S Z) (S D')). DivMulLe D' A } }
def DivMulLeNzTy : Term := prog{
  Π (D : Nat) → Π (A : Nat) → Le (S Z) D → Le (Mul (Div A D) D) A }
example : chkL DivMulLeNz DivMulLeNzTy = true := by native_decide


/-! ## (vii) Ownership — what a `U MAX` costs to USE

    Four probes, run before the composite was written, because the answers
    determine what the composite can look like.

      * a bare `Nat` local may be passed to two calls — Nats COPY;
      * a `U MAX` local may not — the pack is an ordinary owned pair, so a call
        that takes it by value MOVES it, and the second use finds ⊥;
      * `Val MAX p` does NOT consume `p` — a pure projection is a ⇝-read;
      * `Pair(v, H)` where `H` is a comptime BINDER cannot be built mid-body:
        the mode fence refuses to ⇒-move a comptime binder into a runtime pair.
        (Building it in RETURN position is fine — that is what every op does —
        and building it from a literal `unit` is fine, which is what the
        concrete callers do.)

    Together: **a machine integer wants to be `Copy` and a Σ pack is affine.**
    That is the sharpest thing this lane found, and it is a kernel-shaped
    problem — see the recommendation at the foot of the file. The composite
    below is written around it: every pack reaches exactly one consuming call,
    values are staged as bare `Nat`s before the call that consumes their pack,
    and the result is re-minted from the staged parts. -/

def natTwice : Term := prog{
  fn Id2 (n : Nat) -> Nat { n };
  fn Chain (m : Nat) -> Nat { let a = Id2(m); let b = Id2(m); b };
  () }
example : progOk natTwice = true := by native_decide

def packTwice : Term := prog{
  fn Snk (p : (Σ0 (n : Nat) → Le n 15)) -> Nat { Val 15 p };
  fn Chain (p : (Σ0 (n : Nat) → Le n 15)) -> Nat { let a = Snk(p); let b = Snk(p); b };
  () }
example : progRejects packTwice "use-after-move" = true := by native_decide

def projThenMove : Term := prog{
  fn Snk (p : (Σ0 (n : Nat) → Le n 15)) -> Nat { Val 15 p };
  fn Chain (p : (Σ0 (n : Nat) → Le n 15)) -> Nat { let v = Val 15 p; let b = Snk(p); v };
  () }
example : progOk projThenMove = true := by native_decide

def mintMidBody : Term := prog{
  fn Snk (p : (Σ0 (n : Nat) → Le n 15)) -> Nat { Val 15 p };
  fn Chain (H : Le 3 15) -> Nat { let b = Snk(Pair(3, H)); b };
  () }
example : progRejects mintMidBody "COMPTIME binder" = true := by native_decide

/-! ## (viii) THE COMPOSITE — Aeneas' `try_resize` guard

    THE CERTIFIED OPS. A call is OPAQUE (§6.2): the caller's whole knowledge of
    the callee's exit is what the return type says, and `-> U MAX` says only
    "some number in range". So `MulU`'s result cannot appear in the NEXT
    operation's precondition — `Le (Mul (Val MAX nc) d) MAX` is unprovable when
    all you know about `nc` is that it is a `U MAX`.

    That is not a defect of the ops in (iv); it is the price of composing them.
    The fix is one more component in the return type: a certificate saying what
    the value IS. `Refl` proves it (the ι-rule fires on the pack the body just
    built), so it costs one token at the callee and unlocks the whole chain at
    the caller. -/
def uOpsC (tail : Term) : Term := prog{
  fn MulUC (MAX : Nat, a : (Σ0 (n : Nat) → Le n MAX), b : (Σ0 (n : Nat) → Le n MAX),
            H : Le (Mul (Val MAX a) (Val MAX b)) MAX)
      -> (Σ0 (r : (Σ0 (n : Nat) → Le n MAX))
            → Id Nat (Val MAX r) (Mul (Val MAX a) (Val MAX b)))
      { Pair(Pair(Mul (Val MAX a) (Val MAX b), H), Refl) };
  fn DivUC (MAX : Nat, a : (Σ0 (n : Nat) → Le n MAX), b : (Σ0 (n : Nat) → Le n MAX),
            Hnz : Le (S Z) (Val MAX b))
      -> (Σ0 (r : (Σ0 (n : Nat) → Le n MAX))
            → Id Nat (Val MAX r) (Div (Val MAX a) (Val MAX b)))
      { Pair(Pair(Div (Val MAX a) (Val MAX b),
                  LeTrans (Div (Val MAX a) (Val MAX b)) (Val MAX a) MAX
                    (DivLe (Val MAX a) (Val MAX b)) (Bnd MAX a)),
             Refl) };
  %tail }

example : progOk (uOpsC prog{ () }) = true := by native_decide

/-- **`try_resize`**, the Aeneas hashmap's growth guard, in DLLBC.

    Rust (`aeneas/tests/src/hashmap.rs`):

        let n1  = usize::MAX / 2;
        let (divid, divis) = self.max_load_factor;
        let n2  = n1 / divid;
        if capacity <= n2 {
            let ncapacity = capacity * 2;
            self.max_load = ncapacity * divid / divis;
        }

    The guard divides because the thing it is guarding — `capacity * 2 * divid`
    — is exactly what must not be computed if it would overflow. Aeneas proves
    the two multiplications in range from the branch condition; so does this,
    and the proof is the four `let`s below.

    GENERALIZED IN ONE PLACE: the growth factor is a parameter (`growth`, with
    `Hgr : 1 ≤ growth`) rather than the literal 2, because `DivMulLeNz` wants
    the divisor nonzero and not specifically two, and `n1 = MAX / growth` then
    reads as what it is. Instantiate `growth := 2` and this is the Rust.

    THE DERIVATION, and it is entirely from the branch condition:

      (A) `capacity * growth ≤ MAX`
            capacity ≤ n2 ≤ n1                    [branch; DivLe]
            capacity * growth ≤ n1 * growth ≤ MAX [MulMonoR; DivMulLeNz]
      (B) `(capacity * growth) * divid ≤ MAX`
            capacity * divid ≤ n2 * divid ≤ n1    [MulMonoR on the branch;
                                                   DivMulLeNz at divid]
            (capacity * divid) * growth ≤ n1 * growth ≤ MAX
            and `(c*g)*d = (c*d)*g`                [MulSwapR]

    (B) is where the Rust program and the guard disagree about ORDER — the
    program computes `ncapacity * divid` and the guard bounds `capacity *
    divid` — and `MulSwapR` (hence `MulComm`, `MulAssoc`, `MulDistR`) exists
    for that single reconciliation.

    THE OWNERSHIP STAGING, which is the ergonomic cost: `nc` is returned AND fed
    to the second multiplication, and a pack cannot be used twice. So its two
    halves are staged as a copyable `Nat` and a comptime bound before the call
    that consumes it, and the returned pack is re-minted from them. Rust needs
    none of this because `usize` is `Copy`. -/
def tryResize (tail : Term) : Term := uOpsC prog{
  fn TryResize (MAX : Nat,
                capacity : (Σ0 (n : Nat) → Le n MAX),
                growth : (Σ0 (n : Nat) → Le n MAX), Hgr : Le (S Z) (Val MAX growth),
                divid : (Σ0 (n : Nat) → Le n MAX), Hd : Le (S Z) (Val MAX divid),
                divis : (Σ0 (n : Nat) → Le n MAX), Hs : Le (S Z) (Val MAX divis),
                mload : (Σ0 (n : Nat) → Le n MAX))
      -> (Σ (nc : (Σ0 (n : Nat) → Le n MAX)) → (Σ0 (n : Nat) → Le n MAX))
      { if hg : Leb (Val MAX capacity)
                    (Div (Div MAX (Val MAX growth)) (Val MAX divid)) {
          let Hgc = LebTrueLe (Val MAX capacity)
                      (Div (Div MAX (Val MAX growth)) (Val MAX divid)) hg;
          let Hc1 = LeTrans (Val MAX capacity)
                      (Div (Div MAX (Val MAX growth)) (Val MAX divid))
                      (Div MAX (Val MAX growth))
                      Hgc (DivLe (Div MAX (Val MAX growth)) (Val MAX divid));
          let HA = LeTrans (Mul (Val MAX capacity) (Val MAX growth))
                      (Mul (Div MAX (Val MAX growth)) (Val MAX growth)) MAX
                      (MulMonoR (Val MAX growth) (Val MAX capacity)
                        (Div MAX (Val MAX growth)) Hc1)
                      (DivMulLeNz (Val MAX growth) MAX Hgr);
          let Hcd = LeTrans (Mul (Val MAX capacity) (Val MAX divid))
                      (Mul (Div (Div MAX (Val MAX growth)) (Val MAX divid)) (Val MAX divid))
                      (Div MAX (Val MAX growth))
                      (MulMonoR (Val MAX divid) (Val MAX capacity)
                        (Div (Div MAX (Val MAX growth)) (Val MAX divid)) Hgc)
                      (DivMulLeNz (Val MAX divid) (Div MAX (Val MAX growth)) Hd);
          let HB0 = LeTrans (Mul (Mul (Val MAX capacity) (Val MAX divid)) (Val MAX growth))
                      (Mul (Div MAX (Val MAX growth)) (Val MAX growth)) MAX
                      (MulMonoR (Val MAX growth)
                        (Mul (Val MAX capacity) (Val MAX divid))
                        (Div MAX (Val MAX growth)) Hcd)
                      (DivMulLeNz (Val MAX growth) MAX Hgr);
          let HB = LeRwL MAX
                      (Mul (Mul (Val MAX capacity) (Val MAX divid)) (Val MAX growth))
                      (Mul (Mul (Val MAX capacity) (Val MAX growth)) (Val MAX divid))
                      (IdSym Nat
                        (Mul (Mul (Val MAX capacity) (Val MAX growth)) (Val MAX divid))
                        (Mul (Mul (Val MAX capacity) (Val MAX divid)) (Val MAX growth))
                        (MulSwapR (Val MAX capacity) (Val MAX growth) (Val MAX divid)))
                      HB0;
          let cv = Val MAX capacity;
          let gv = Val MAX growth;
          let r1 = MulUC(MAX, capacity, growth, HA);
          match r1 { Pair(nc, Enc) => {
            let ncv = Val MAX nc;
            let Hncb = Bnd MAX nc;
            let HB2 = LeRwL MAX
                        (Mul (Mul cv gv) (Val MAX divid))
                        (Mul (Val MAX nc) (Val MAX divid))
                        (IdCongr Nat Nat (λ (X : Nat). Mul X (Val MAX divid))
                          (Mul cv gv) (Val MAX nc)
                          (IdSym Nat (Val MAX nc) (Mul cv gv) Enc))
                        HB;
            let r2 = MulUC(MAX, nc, divid, HB2);
            match r2 { Pair(nd, End) => {
              let r3 = DivUC(MAX, nd, divis, Hs);
              match r3 { Pair(ml, Eml) => Pair(Pair(ncv, Hncb), ml) } } }
          } }
        } else {
          Pair(capacity, mload)
        } };
  %tail }

example : progOk (tryResize prog{ () }) = true := by native_decide

/-! ### The guard is what makes it check

    Delete the `if` and the same body is REJECTED: with no branch condition
    there is nothing to derive `HA` from, and `capacity * growth ≤ MAX` is
    simply not a consequence of `capacity ≤ MAX` and `growth ≤ MAX`. This is the
    test that says the guard is load-bearing rather than decorative — the same
    thing Aeneas' proof obligation says about the Rust. -/
def tryResizeNoGuard : Term := uOpsC prog{
  fn TryResizeBad (MAX : Nat,
                   capacity : (Σ0 (n : Nat) → Le n MAX),
                   growth : (Σ0 (n : Nat) → Le n MAX))
      -> (Σ0 (n : Nat) → Le n MAX)
      { let r1 = MulUC(MAX, capacity, growth, unit);
        match r1 { Pair(nc, Enc) => nc } };
  () }
example : progRejects tryResizeNoGuard "does not have its parameter type" = true := by
  native_decide

/-! ### It RUNS — `try_resize` on real numbers

    `MAX = 15`, growth 2, load factor 4/5. Then `n1 = 15/2 = 7` and
    `n2 = 7/4 = 1`, so a capacity of 1 resizes (to 2, with max_load
    `2*4/5 = 1`) and a capacity of 2 does not. Both branches, executing. -/

def resizeCall (m cap g dd ds ml : Nat) : Term := tryResize prog{
  let cP = Pair(%(tn cap), unit);
  let gP = Pair(%(tn g), unit);
  let dP = Pair(%(tn dd), unit);
  let sP = Pair(%(tn ds), unit);
  let mP = Pair(%(tn ml), unit);
  let r = TryResize(%(tn m), cP, gP, unit, dP, unit, sP, unit, mP);
  match r { Pair(nc, ld) => { let out = Val %(tn m) nc; let out2 = Val %(tn m) ld; () } } }

def runOut2 (t : Term) : Option (Nat × Nat) :=
  match runProgram t with
  | .ok env =>
    match (env.lookup "out").bind (natOfV 4000), (env.lookup "out2").bind (natOfV 4000) with
    | some a, some b => some (a, b)
    | _, _ => none
  | .error _ => none

-- capacity 1 ≤ n2 = 1: RESIZE. New capacity 2, new max_load `2*4/5 = 1`.
example : progOk (resizeCall 15 1 2 4 5 0) = true := by native_decide
example : runOut2 (resizeCall 15 1 2 4 5 0) == some (2, 1) := by native_decide
-- capacity 2 > n2 = 1: no resize. Capacity and max_load both unchanged.
example : progOk (resizeCall 15 2 2 4 5 9) = true := by native_decide
example : runOut2 (resizeCall 15 2 2 4 5 9) == some (2, 9) := by native_decide

/-! #### THE COST OF DIVIDING, after the rewrite

    An earlier version of this file wrote `Div`/`Mod` in the textbook shape and
    recorded a "quadratic wall" here: `try_resize` ran instantly at `MAX = 15`
    and did not finish in THIRTY MINUTES at `MAX = 63`. That diagnosis was
    wrong. The definitions were EXPONENTIAL (§ii), and with the state-carrying
    ones the same program runs at every size that was out of reach:

        MAX          15     31      63      127
        execute    0.8 s  2.0 s   6.7 s   24.9 s

    (measured through `lake env lean`, which interprets rather than calling the
    precompiled library — in-module it is several times faster, and this whole
    file including both assertions below elaborates in 6.2 s. The RATIO is the
    finding either way.) That is roughly `MAX^1.9` — the quadratic the old note
    claimed and did not have. `MAX = 63` resizes capacity 7 to 14 with max_load 11, and
    `MAX = 127` resizes 15 to 30 with max_load 24; both are asserted below.

    The moral is not about division. It is that a performance claim about a
    normalizer with no sharing has to be MEASURED — the exponential and the
    quadratic present identically (a build that does not finish), and the shape
    of the definition is the only thing that tells them apart. -/

-- MAX = 63: n1 = 31, n2 = 7, so capacity 7 resizes to 14 with max_load 11.
example : runOut2 (resizeCall 63 7 2 4 5 0) == some (14, 11) := by native_decide
-- MAX = 127: n1 = 63, n2 = 15, so capacity 15 resizes to 30 with max_load 24.
example : runOut2 (resizeCall 127 15 2 4 5 0) == some (30, 24) := by native_decide

-- Rejected callers: the load factor's dividend and the growth factor must both
-- be nonzero, and at a concrete MAX those obligations are `Bot`.
example : progRejects (resizeCall 15 1 2 0 5 0) botNeedle = true := by native_decide
example : progRejects (resizeCall 15 1 0 4 5 0) botNeedle = true := by native_decide

/-! ## (ix) Where this leaves things

    WHAT WORKS, WITHOUT A LINE OF KERNEL CHANGE. `U MAX := Σ0 (n : Nat) → Le n MAX`
    is a working bounded integer. It cannot be built out of range; its operations
    demand exactly the obligations a machine imposes; those obligations are
    discharged at the CALL rather than propagated as a failure case; and a real
    overflow guard — Aeneas' `try_resize` — ports across with its evidence
    derived from the branch condition rather than assumed. Every line of it is a
    library over formers the kernel already had (`Σ0`, `sigmaRec`, evidence
    parameters, `Le`).

    WHAT IT COSTS, measured rather than guessed.

      * THE COMPOSITE'S PROOF BUDGET. `TryResize` performs THREE arithmetic
        operations and spends SEVEN proof terms and FOUR staging bindings on
        them. Of the seven: four are mathematical content (the two `Le` chains
        (A) and (B)), one is the mechanical branch reflection (`LebTrueLe`), and
        two are pure transport — one to reconcile `(c*g)*d` with `(c*d)*g`, one
        to move the callee's value certificate into the next precondition. So
        roughly two proof lines per operation, of which a bit over half is
        content. The Rust it replaces is five lines.

      * THE SUPPORTING LIBRARY. Seventeen new lemmas: `NextInv`, `NextStep`,
        `DivModC`, `DivModId`, `DivMulLe`, `DivMulLeNz`, `MulLeSelf`, `DivLe`,
        `SubLe`, `MulMonoR`, `MulZeroR`, `AddSwapL`, `MulSuccR`, `MulComm`,
        `MulDistR`, `MulAssoc`, `MulSwapR`. None of it is specific to bounded
        integers — it is the `Nat` algebra the library was missing, and it stays
        useful after.

      * THE UNARY BILL. `O(MAX)` checking steps for a program whose arithmetic
        is one `Le`; `defaultFuel = 1000` caps those near `MAX = 140`, and that
        cap is the harness constant (the same programs check at `MAX = 255` on
        20000 steps). A program that DIVIDES is quadratic on top of that, so
        `try_resize` executes at `MAX = 127` and would not at `MAX = 1024`. The
        whole bill falls on execution and on concrete tests: symbolic checking
        of the composite — seven proof terms over an opaque `MAX` — never
        computes a numeral, and the entire file elaborates in 6.2 seconds.

      * AND ONE COST THAT IS NOT THE REPRESENTATION'S. The first version of
        `Div`/`Mod` here was EXPONENTIAL, because this normalizer has no sharing
        and the textbook spelling mentions the recursive result twice (§ii). It
        cost half a day and produced a confidently wrong "quadratic" note in
        this very file before it was measured. The rule — use the recursive
        result ONCE, carry the duplicate as an argument — is not specific to
        arithmetic and is now in `docs/04-language.md`.

    DOES ANYTHING HERE WANT KERNEL SUPPORT? Three answers, in the order they
    matter.

    1. **`Copy` for scalars — yes, and it is the only one that really bites.**
       A `Nat` local may be passed to two calls; a `U MAX` local may not, because
       the pack is an ordinary owned pair and a call takes it by value. A machine
       integer is `Copy` in every language that has one, and `try_resize` is the
       proof that real code needs it: `ncapacity` is both returned and multiplied
       again, so its two halves have to be staged as a bare `Nat` and a comptime
       bound before the consuming call and the pack re-minted afterwards. That is
       four of this file's eleven composite bindings, and it scales with the
       number of reuses. The fix is not library-shaped: either a duplicability
       judgment (a pair of `Copy` components is `Copy`) or a kernel refinement
       former whose values are scalars carrying a proof rather than pairs.

    1b. **Sharing in the normalizer — an honourable mention.** Not needed for
       correctness and not what this lane was asked about, but it is the
       difference between `Mod 18` taking 2.7 seconds and `Mod 1024` taking 60
       milliseconds, and the failure mode is a build that never finishes rather
       than an error. Every author has to know the rule; a normalizer that
       shared would mean none of them did.

    2. **Binary numerals — yes for RUNNING, no for reasoning.** Nothing symbolic
       in `MAX` pays the unary bill, which is every program and every lemma
       above; the proofs would be character-for-character the same at
       `MAX = 2^64 - 1`. What is unavailable is the executing differential at a
       realistic width, and a hashmap whose capacity doubling can actually be
       run. If the goal is "the obligations exist and are discharged", unary is
       already enough. If the goal is "run it at `usize`", it is not.

    3. **Wraparound, and the rest — no.** Nothing in this exercise wanted
       wrapping semantics: the verified subset Aeneas targets is the
       panic-free one, which is what an evidence parameter models. Wrapping is a
       different type and would be another library pack (over
       `Mod (op a b) (S MAX)`) with no evidence parameters at all. Truncated
       subtraction already supports both the saturating and the checked reading,
       and signed integers would be a new datatype but still a library one.

    One MACRO-level irritant, worth a line: `elim` reads a Σ's domain and family
    off the motive's binder type syntactically, so a motive can never say
    `U MAX` — every projection respells `Σ0 (n : Nat) → Le n MAX`. Cosmetic, and
    it roughly doubles the width of the vocabulary in (i).

    IS THE LIBRARY ROUTE SUFFICIENT FOR A HASHMAP OVER BOUNDED KEYS? Expressively,
    yes, and this file is the evidence: the capacity arithmetic is the hard part
    of that hashmap and it checks. Keys are cheaper still — they are compared,
    not added, so a `U MAX` key needs `Eqb (Val a) (Val b)` and no evidence at
    all. The obstacle to writing it is ergonomic and it is item 1: a container
    of bounded integers reads its elements constantly, and every read of a pack
    that a call will consume costs a staging pair. -/

end Dllbc.Tests.Finite

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
  LebFalseGt IdTrans IdCongr IdSym AddZero AddSucc AddComm LePredL)

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

end Dllbc.Tests.Finite

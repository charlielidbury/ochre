import Dllbc.ElabCheck
import Dllbc.Std
import Dllbc.ProgMacro

/-!
# `Dllbc.StdLemmas` — the pure lemmas, authored in the §15 surface syntax

The M11 wall — `LeTrans` as a raw de Bruijn term across ~15 binder contexts,
each mis-index failing silently — collapsed by names and explicit motives. Every
lemma here is written in `prog{ … }`: binders are named, motives are written once
and visible, and elaboration resolves names or errors (no silent fallback). The
kernel terms they elaborate to are the same de Bruijn `Term`s hasType already
checks; the surface is authoring sugar only.

`Le`/`Count` are the surface names for the library functions (Term-valued, so a
`prog{ }` application `Le a b` is an ordinary app spine).
-/

namespace Dllbc.StdLemmas
open Dllbc

/-- Surface name for the order type (a `Term`, so `Le a b` is an application). -/
abbrev Le : Term := Std.LeFnT
/-- Surface name for the multiset counter. -/
abbrev Count : Term := Std.countFnT
abbrev Add : Term := Std.addFnT
abbrev Append : Term := Std.appendFnT
abbrev Eqb : Term := Std.eqbFnT
abbrev Take : Term := Std.takeFnT
abbrev Drop : Term := Std.dropFnT
abbrev Leb : Term := Std.lebFnT

/-! ## `LeRefl`, `LeTrans` — the acceptance test -/

def LeRefl : Term := prog defer_check {
  λ (N : Nat). elim N return (λ (M : Nat). Le M M) {
    Z => unit,
    S (K) Ih => Ih } }
def LeReflTy : Term := prog defer_check { Π (N : Nat) → Le N N }

-- The wall. Single outer elim on `a`; the `S` case elims on `b`, whose `S` case
-- elims on `c`, with the IH applied at the peeled proofs — every step
-- definitional through the `Le` equations. Nested, but every binder is NAMED and
-- every motive is written once and visible.
def LeTrans : Term := prog defer_check {
  λ (A : Nat).
    elim A return (λ (A0 : Nat). Π (B : Nat) → Π (C : Nat) → Le A0 B → Le B C → Le A0 C) {
      Z => λ (B : Nat). λ (C : Nat). λ (Hab : Le Z B). λ (Hbc : Le B C). unit,
      S (A') Ih => λ (B : Nat). λ (C : Nat). λ (Hab : Le (S A') B). λ (Hbc : Le B C).
        elim B return (λ (B0 : Nat). Le (S A') B0 → Le B0 C → Le (S A') C) {
          Z => λ (Hab0 : Le (S A') Z). λ (Hbc0 : Le Z C). botElim (Le (S A') C) Hab0,
          S (B') Ihb => λ (Hab0 : Le (S A') (S B')). λ (Hbc0 : Le (S B') C).
            elim C return (λ (C0 : Nat). Le (S B') C0 → Le (S A') C0) {
              Z => λ (Hbc1 : Le (S B') Z). botElim (Le (S A') Z) Hbc1,
              S (C') Ihc => λ (Hbc1 : Le (S B') (S C')). Ih B' C' Hab0 Hbc1
            } Hbc0
        } Hab Hbc
    } }
def LeTransTy : Term := prog defer_check {
  Π (A : Nat) → Π (B : Nat) → Π (C : Nat) → Le A B → Le B C → Le A C }

-- Right-successor monotonicity: `a ≤ b ⟹ a ≤ S b`. Double induction (on `a`,
-- casing `b`): the `Z` head is trivial (`Le Z _ = ⊤`); the `S a'` head cases `b`
-- (`Le (S a') Z = ⊥`, else `Le a' b'` and the IH lifts it to `Le a' (S b')`).
-- The glue `CountSwapL'` needs to bend swapS's `Le (S i) j` into count_swapL's
-- `Le (S i) (Len l)` via one `LeTrans`.
def LeUpR : Term := prog defer_check {
  λ (A : Nat). elim A return (λ (Az : Nat). Π (B : Nat) → Le Az B → Le Az (S B)) {
    Z => λ (B : Nat). λ (H : Le Z B). unit,
    S (A') Ih => λ (B : Nat). λ (H : Le (S A') B).
      elim B return (λ (Bz : Nat). Le (S A') Bz → Le (S A') (S Bz)) {
        Z => λ (H0 : Le (S A') Z). botElim (Le (S A') (S Z)) H0,
        S (B') Ihb => λ (H0 : Le (S A') (S B')). Ih B' H0
      } H } }
def LeUpRTy : Term := prog defer_check { Π (A : Nat) → Π (B : Nat) → Le A B → Le A (S B) }

-- `i ≤ i + g`: the boundary never passes the scan position it feeds. A clean
-- induction on `i` (`Add (S i') g = S (Add i' g)`, so `Le (S i') (Add (S i') g)`
-- reduces to the IH). The partition swaps consume this as their `pij`.
def LeAdd : Term := prog defer_check {
  λ (I : Nat). elim I return (λ (Iz : Nat). Π (G : Nat) → Le Iz (Add Iz G)) {
    Z => λ (G : Nat). unit,
    S (I') Ih => λ (G : Nat). Ih G } }
def LeAddTy : Term := prog defer_check { Π (I : Nat) → Π (G : Nat) → Le I (Add I G) }

-- `b ≤ a + b` — the companion where the summand is on the LEFT (`LeAdd` has it on
-- the right). Induction on `a`: base is `LeRefl` (`Add Z b = b`), step lifts the
-- IH with `LeUpR` (`Add (S a') b = S (Add a' b)`). The scan-position bound uses
-- this because the length equation carries the remaining count `k` on the left.
def LeAddL : Term := prog defer_check {
  λ (B : Nat). λ (A : Nat).
    elim A return (λ (Az : Nat). Le B (Add Az B)) {
      Z => LeRefl B,
      S (A') Ih => LeUpR B (Add A' B) Ih } }
def LeAddLTy : Term := prog defer_check { Π (B : Nat) → Π (A : Nat) → Le B (Add A B) }

-- `S i ≤ i + (S g)` — the swap's `pij`: the boundary `S i` is below the scan
-- position `S (Add i (S g))` whenever the gap is non-empty. Induction on `i`
-- avoids an AddSucc transport (`Add (S i') x = S (Add i' x)` is definitional),
-- so no rewrite is needed here.
def LeAddSucc : Term := prog defer_check {
  λ (I : Nat). elim I return (λ (Iz : Nat). Π (G : Nat) → Le (S Iz) (Add Iz (S G))) {
    Z => λ (G : Nat). unit,
    S (I') Ih => λ (G : Nat). Ih G } }
def LeAddSuccTy : Term := prog defer_check { Π (I : Nat) → Π (G : Nat) → Le (S I) (Add I (S G)) }

-- Transport a `Le` along an `Id` on its SECOND argument: `x = y ⟹ Le a x → Le a
-- y`. The bounds derived over the arithmetic normal form are moved onto `len *v`
-- (and back through `LenSwapL`) with this J-transport — the "LeTrans/le_step
-- glue where descent is not definitional".
def LeRwR : Term := prog defer_check {
  λ (A : Nat). λ (X : Nat). λ (Y : Nat). λ (H : Id Nat X Y). λ (P : Le A X).
    j Nat X (λ (Y' : Nat). λ (Hh : Id Nat X Y'). Le A Y') P Y H }
def LeRwRTy : Term := prog defer_check { Π (A : Nat) → Π (X : Nat) → Π (Y : Nat) → Id Nat X Y → Le A X → Le A Y }

-- Transport a `Le` along an `Id` on its FIRST (smaller) argument: `x = y ⟹ Le x
-- b → Le y b`. The range partition's bound `Le (add lo (S (add k (add i g))))
-- (len *v)` is invariant across the recursion (the sum k+i+g is preserved), but
-- its SYNTACTIC form shifts as k descends and i/g grow; this moves the bound
-- between forms via the hshift identities — the Le mirror of LeRwR, and the one
-- lemma the M20 Id-toolkit lacked for the subrange generalization (§21).
def LeRwL : Term := prog defer_check {
  λ (B : Nat). λ (X : Nat). λ (Y : Nat). λ (H : Id Nat X Y). λ (P : Le X B).
    j Nat X (λ (Y' : Nat). λ (Hh : Id Nat X Y'). Le Y' B) P Y H }
def LeRwLTy : Term := prog defer_check { Π (B : Nat) → Π (X : Nat) → Π (Y : Nat) → Id Nat X Y → Le X B → Le Y B }

-- Left-add monotonicity: `a ≤ b ⟹ lo + a ≤ lo + b`. Induction on `lo`: base is
-- the hypothesis (`Add Z x = x`), step is the IH verbatim (`add (S lo') x =
-- S (add lo' x)` and `Le (S _) (S _) = Le _ _` are both definitional). The range
-- partition's swap bounds shift the entry bound `Le (S i) (S (Add i g))` through
-- `Add lo` to reach `Le (Add lo (S i)) (Add lo (S (Add i g)))` (§21).
def LeAddMonoL : Term := prog defer_check {
  λ (Lo : Nat). λ (A : Nat). λ (B : Nat). λ (H : Le A B).
    elim Lo return (λ (Loz : Nat). Le (Add Loz A) (Add Loz B)) {
      Z => H,
      S (Lo') Ih => Ih } }
def LeAddMonoLTy : Term := prog defer_check { Π (Lo : Nat) → Π (A : Nat) → Π (B : Nat) → Le A B → Le (Add Lo A) (Add Lo B) }

/-! ## `IdTrans`, `IdCongr` — the J warm-ups partition's count-chaining consumes -/

def IdTrans : Term := prog defer_check {
  λ (A : Type). λ (X : A). λ (Y : A). λ (Z0 : A). λ (P : Id A X Y). λ (Q : Id A Y Z0).
    j A X (λ (Y' : A). λ (H : Id A X Y'). Id A Y' Z0 → Id A X Z0) (λ (H : Id A X Z0). H) Y P Q }
def IdTransTy : Term := prog defer_check {
  Π (A : Type) → Π (X : A) → Π (Y : A) → Π (Z0 : A) → Id A X Y → Id A Y Z0 → Id A X Z0 }

def IdCongr : Term := prog defer_check {
  λ (A : Type). λ (B : Type). λ (F : A → B). λ (X : A). λ (Y : A). λ (P : Id A X Y).
    j A X (λ (Y' : A). λ (H : Id A X Y'). Id B (F X) (F Y')) Refl Y P }
def IdCongrTy : Term := prog defer_check {
  Π (A : Type) → Π (B : Type) → Π (F : A → B) → Π (X : A) → Π (Y : A) → Id A X Y → Id B (F X) (F Y) }

def IdSym : Term := prog defer_check {
  λ (A : Type). λ (X : A). λ (Y : A). λ (P : Id A X Y).
    j A X (λ (Y' : A). λ (H : Id A X Y'). Id A Y' X) Refl Y P }
def IdSymTy : Term := prog defer_check { Π (A : Type) → Π (X : A) → Π (Y : A) → Id A X Y → Id A Y X }

/-! ## Arithmetic — the first double-inductions after the wall (§16 calibration) -/

def AddZero : Term := prog defer_check {
  λ (A : Nat). elim A return (λ (X : Nat). Id Nat (Add X Z) X) {
    Z => Refl,
    S (A') Ih => IdCongr Nat Nat (λ (N : Nat). S N) (Add A' Z) A' Ih } }
def AddZeroTy : Term := prog defer_check { Π (A : Nat) → Id Nat (Add A Z) A }

def AddSucc : Term := prog defer_check {
  λ (A : Nat). λ (B : Nat). elim A return (λ (X : Nat). Id Nat (Add X (S B)) (S (Add X B))) {
    Z => Refl,
    S (A') Ih => IdCongr Nat Nat (λ (N : Nat). S N) (Add A' (S B)) (S (Add A' B)) Ih } }
def AddSuccTy : Term := prog defer_check { Π (A : Nat) → Π (B : Nat) → Id Nat (Add A (S B)) (S (Add A B)) }

-- Commutativity: the classic proof, authored in the surface and checked first try.
def AddComm : Term := prog defer_check {
  λ (A : Nat). elim A return (λ (X : Nat). Π (B : Nat) → Id Nat (Add X B) (Add B X)) {
    Z => λ (B : Nat). IdSym Nat (Add B Z) B (AddZero B),
    S (A') Ih => λ (B : Nat).
      IdTrans Nat (S (Add A' B)) (S (Add B A')) (Add B (S A'))
        (IdCongr Nat Nat (λ (N : Nat). S N) (Add A' B) (Add B A') (Ih B))
        (IdSym Nat (Add B (S A')) (S (Add B A')) (AddSucc B A')) } }
def AddCommTy : Term := prog defer_check { Π (A : Nat) → Π (B : Nat) → Id Nat (Add A B) (Add B A) }

def AddAssoc : Term := prog defer_check {
  λ (A : Nat). elim A return (λ (X : Nat). Π (B : Nat) → Π (C : Nat) → Id Nat (Add (Add X B) C) (Add X (Add B C))) {
    Z => λ (B : Nat). λ (C : Nat). Refl,
    S (A') Ih => λ (B : Nat). λ (C : Nat).
      IdCongr Nat Nat (λ (N : Nat). S N) (Add (Add A' B) C) (Add A' (Add B C)) (Ih B C) } }
def AddAssocTy : Term := prog defer_check { Π (A : Nat) → Π (B : Nat) → Π (C : Nat) → Id Nat (Add (Add A B) C) (Add A (Add B C)) }

/-! ## The length-equation shift lemmas — `hlen` updates for the recursive partScan

    The recursion's loop invariant is `Len *v = S (Add k (Add i g))`, and `k+i+g`
    is constant across every step (each moves one successor between the `k`, `i`,
    `g` slots). So each recursive `hlen` update is an arithmetic-identity transport
    of the same total, provable by `AddSucc` (the only non-definitional step, since
    Std `Add` recurses on its first argument). Two shapes cover all three cases:
    boundary advance (True-Z, True-S g') and gap growth (False). -/

def CountAppend : Term := prog defer_check {
  λ (M : Nat). λ (A : List Nat). λ (B : List Nat).
    elim A return (λ (X : List Nat). Id Nat (Count M (Append X B)) (Add (Count M X) (Count M B))) {
      Nil => Refl,
      Cons (H) (T) Ih =>
        elim (Eqb M H) return (λ (Bv : Bool).
          Id Nat (boolRec (λ (W : Bool). Nat) (S (Count M (Append T B))) (Count M (Append T B)) Bv)
                 (Add (boolRec (λ (W : Bool). Nat) (S (Count M T)) (Count M T) Bv) (Count M B))) {
          True => IdCongr Nat Nat (λ (N : Nat). S N) (Count M (Append T B)) (Add (Count M T) (Count M B)) Ih,
          False => Ih
        }
    } }
def CountAppendTy : Term := prog defer_check {
  Π (M : Nat) → Π (A : List Nat) → Π (B : List Nat) →
    Id Nat (Count M (Append A B)) (Add (Count M A) (Count M B)) }

def NthL : Term := prog defer_check {
  λ (K : Nat). elim K return (λ (Z0 : Nat). List Nat → Nat) {
    Z => λ (L : List Nat). elim L return (λ (Z0 : List Nat). Nat) { Nil => Z, Cons (H) (T) Ihl => H },
    S (K') Rec => λ (L : List Nat). elim L return (λ (Z0 : List Nat). Nat) { Nil => Z, Cons (H) (T) Ihl => Rec T } } }

def Set : Term := prog defer_check {
  λ (K : Nat). λ (V : Nat). elim K return (λ (Z0 : Nat). List Nat → List Nat) {
    Z => λ (L : List Nat). elim L return (λ (Z0 : List Nat). List Nat) { Nil => Nil, Cons (H) (T) Ihl => Cons V T },
    S (K') Rec => λ (L : List Nat). elim L return (λ (Z0 : List Nat). List Nat) { Nil => Nil, Cons (H) (T) Ihl => Cons H (Rec T) } } }

def SwapL : Term := prog defer_check {
  λ (I : Nat). elim I return (λ (Z0 : Nat). Nat → List Nat → List Nat) {
    Z => λ (J : Nat). λ (L : List Nat). elim L return (λ (Z0 : List Nat). List Nat) {
      Nil => Nil,
      Cons (X) (Xs) Ihl => elim J return (λ (Z0 : Nat). List Nat) {
        Z => Cons X Xs,
        S (J') Jih => Cons (NthL J' Xs) (Set J' X Xs) } },
    S (I') Reci => λ (J : Nat). λ (L : List Nat). elim L return (λ (Z0 : List Nat). List Nat) {
      Nil => Nil,
      Cons (X) (Xs) Ihl => elim J return (λ (Z0 : Nat). List Nat) {
        Z => Cons X Xs,
        S (J') Jih => Cons X (Reci J' Xs) } } } }

/-! ## Length preservation — the spec `swapS` carries (§16, len variant)

    `LenSet`/`LenSwapL` hold UNCONDITIONALLY — no bounds — because `Set`
    preserves length even off the end (it replaces or no-ops, never resizes) and
    `SwapL` only ever rebuilds the same spine. Unlike count, length needs no
    `Eqb`, so these are clean surface inductions (no rewriting layer required). -/

abbrev Len : Term := Std.lenFnT

def LenSet : Term := prog defer_check {
  λ (K : Nat). λ (V : Nat).
    elim K return (λ (Z0 : Nat). Π (L : List Nat) → Id Nat (Len (Set Z0 V L)) (Len L)) {
      Z => λ (L : List Nat). elim L return (λ (X : List Nat). Id Nat (Len (Set Z V X)) (Len X)) {
        Nil => Refl, Cons (H) (T) Ihl => Refl },
      S (K') Ih => λ (L : List Nat). elim L return (λ (X : List Nat). Id Nat (Len (Set (S K') V X)) (Len X)) {
        Nil => Refl,
        Cons (H) (T) Ihl => IdCongr Nat Nat (λ (N : Nat). S N) (Len (Set K' V T)) (Len T) (Ih T) } } }
def LenSetTy : Term := prog defer_check { Π (K : Nat) → Π (V : Nat) → Π (L : List Nat) → Id Nat (Len (Set K V L)) (Len L) }

def LenSwapL : Term := prog defer_check {
  λ (I : Nat).
    elim I return (λ (Z0 : Nat). Π (J : Nat) → Π (L : List Nat) → Id Nat (Len (SwapL Z0 J L)) (Len L)) {
      Z => λ (J : Nat). λ (L : List Nat).
        elim L return (λ (X : List Nat). Id Nat (Len (SwapL Z J X)) (Len X)) {
          Nil => Refl,
          Cons (Y) (Ys) Ihl => elim J return (λ (W : Nat). Id Nat (Len (SwapL Z W (Cons Y Ys))) (Len (Cons Y Ys))) {
            Z => Refl,
            S (J') Jih => IdCongr Nat Nat (λ (N : Nat). S N) (Len (Set J' Y Ys)) (Len Ys) (LenSet J' Y Ys) } },
      S (I') Ih => λ (J : Nat). λ (L : List Nat).
        elim L return (λ (X : List Nat). Id Nat (Len (SwapL (S I') J X)) (Len X)) {
          Nil => Refl,
          Cons (Y) (Ys) Ihl => elim J return (λ (W : Nat). Id Nat (Len (SwapL (S I') W (Cons Y Ys))) (Len (Cons Y Ys))) {
            Z => Refl,
            S (J') Jih => IdCongr Nat Nat (λ (N : Nat). S N) (Len (SwapL I' J' Ys)) (Len Ys) (Ih J' Ys) } } } }
def LenSwapLTy : Term := prog defer_check { Π (I : Nat) → Π (J : Nat) → Π (L : List Nat) → Id Nat (Len (SwapL I J L)) (Len L) }

/-! ## The bounded `CountSwapL` stack (§18)

    `CountSwapL` — `SwapL i j` preserves the multiset — is FALSE unbounded (off
    the end `NthL` defaults to `Z` and `Set` no-ops, so the head becomes `Z ≠ x`).
    With `Le (S i) (Len l)` and `Le (S j) (Len l)` the indices are in range and the
    swap is a genuine permutation. The proof decomposes into a small stack, each
    node an ordinary Id-algebra fact composed by `IdTrans`/`IdCongr`:

    - `Cons2Comm` — count is invariant under swapping two ADJACENT heads. Proven
      by the §18 nested `generalizing` casing (the report card; the named copy the
      stack consumes). The base case of the head-swap.
    - `CountConsCongr` — `count m l₁ = count m l₂ ⟹ count m (Cons h l₁) =
      count m (Cons h l₂)`. One `IdCongr` whose `f` abstracts `count m ·` out of
      the `boolRec` that `Count (Cons …)` unfolds to (both occurrences at once).
    - `CountHeadswap` — bounded: swapping the head `x` with position `j` of the
      tail preserves count. The meaty double-induction (on `j`, casing `xs`); its
      step is a three-link `IdTrans` chain `Cons2Comm ∘ (CountConsCongr on IH)
      ∘ Cons2Comm`, its `Nil` leaves ⊥-discharged by the range bound.
    - `CountSwapL` — bounded: the top statement, by induction on `i` with `j`/`l`
      casing. Head case delegates to `CountHeadswap`; recursive case is
      `CountConsCongr` on the IH; the degenerate `j = Z` / `i > j` cases are the
      identity, so `Refl`.

    No J-transport (rewrite-by-Id) is needed here: the decomposition localises ALL
    `Eqb`/knowledge reasoning inside `Cons2Comm` (via `generalizing`) and
    `CountConsCongr` (via `IdCongr` on the `boolRec`), leaving the head-swap and
    `SwapL` levels as pure `IdTrans` chains. rewrite-by-Id (S18) remains the tool
    for a subterm STUCK behind an abstract scrutinee, which this stack avoids by
    construction. -/

def CountConsCongr : Term := prog defer_check {
  λ (M : Nat). λ (H : Nat). λ (L1 : List Nat). λ (L2 : List Nat). λ (P : Id Nat (Count M L1) (Count M L2)).
    IdCongr Nat Nat (λ (R : Nat). boolRec (λ (W : Bool). Nat) (S R) R (Eqb M H)) (Count M L1) (Count M L2) P }
def CountConsCongrTy : Term := prog defer_check {
  Π (M : Nat) → Π (H : Nat) → Π (L1 : List Nat) → Π (L2 : List Nat) →
    Id Nat (Count M L1) (Count M L2) → Id Nat (Count M (Cons H L1)) (Count M (Cons H L2)) }

-- The §18 rewrite-by-Id lemma, named: from a RECEIVED equation `Eqb m a = True`,
-- resolve the STUCK `Count m (Cons a l)` to `S (Count m l)`. J transports `Refl`
-- along `IdSym hq`, the motive abstracting the scrutinee `z` out of the `boolRec`
-- that `Count (Cons …)` unfolds to. Abstraction alone cannot do this (the subterm
-- hides behind the scrutinee's own reduction); this is the knowledge half. The
-- imperative tie-in returns THIS applied to its params.
def CountConsHit : Term := prog defer_check {
  λ (M : Nat). λ (A : Nat). λ (L : List Nat). λ (Hq : Id Bool (Eqb M A) True).
    j Bool True
      (λ (Z0 : Bool). λ (H : Id Bool True Z0).
        Id Nat (boolRec (λ (W : Bool). Nat) (S (Count M L)) (Count M L) Z0) (S (Count M L)))
      Refl (Eqb M A) (IdSym Bool (Eqb M A) True Hq) }
def CountConsHitTy : Term := prog defer_check {
  Π (M : Nat) → Π (A : Nat) → Π (L : List Nat) → Id Bool (Eqb M A) True →
    Id Nat (Count M (Cons A L)) (S (Count M L)) }

def SwapLSet : Term := prog defer_check {
  λ (I : Nat).
    elim I return (λ (Iz : Nat). Π (J : Nat) → Π (L : List Nat) → Le (S Iz) J → Le (S J) (Len L) →
        Id (List Nat) (Set Iz (NthL J L) (Set J (NthL Iz L) L)) (SwapL Iz J L)) {
      Z => λ (J : Nat). λ (L : List Nat).
        elim L return (λ (Lz : List Nat). Le (S Z) J → Le (S J) (Len Lz) →
            Id (List Nat) (Set Z (NthL J Lz) (Set J (NthL Z Lz) Lz)) (SwapL Z J Lz)) {
          Nil => λ (Pij : Le (S Z) J). λ (P2 : Le (S J) (Len Nil)).
            botElim (Id (List Nat) (Set Z (NthL J Nil) (Set J (NthL Z Nil) Nil)) (SwapL Z J Nil)) P2,
          Cons (Y) (Ys) Ihl => λ (Pij : Le (S Z) J). λ (P2 : Le (S J) (Len (Cons Y Ys))).
            elim J return (λ (Jz : Nat). Le (S Z) Jz → Le (S Jz) (Len (Cons Y Ys)) →
                Id (List Nat) (Set Z (NthL Jz (Cons Y Ys)) (Set Jz (NthL Z (Cons Y Ys)) (Cons Y Ys))) (SwapL Z Jz (Cons Y Ys))) {
              Z => λ (Pijz : Le (S Z) Z). λ (P2z : Le (S Z) (Len (Cons Y Ys))).
                botElim (Id (List Nat) (Set Z (NthL Z (Cons Y Ys)) (Set Z (NthL Z (Cons Y Ys)) (Cons Y Ys))) (SwapL Z Z (Cons Y Ys))) Pijz,
              S (J') Jih => λ (Pijs : Le (S Z) (S J')). λ (P2s : Le (S (S J')) (Len (Cons Y Ys))). Refl
            } Pij P2 },
      S (I') Ih => λ (J : Nat). λ (L : List Nat).
        elim L return (λ (Lz : List Nat). Le (S (S I')) J → Le (S J) (Len Lz) →
            Id (List Nat) (Set (S I') (NthL J Lz) (Set J (NthL (S I') Lz) Lz)) (SwapL (S I') J Lz)) {
          Nil => λ (Pij : Le (S (S I')) J). λ (P2 : Le (S J) (Len Nil)).
            botElim (Id (List Nat) (Set (S I') (NthL J Nil) (Set J (NthL (S I') Nil) Nil)) (SwapL (S I') J Nil)) P2,
          Cons (Y) (Ys) Ihl => λ (Pij : Le (S (S I')) J). λ (P2 : Le (S J) (Len (Cons Y Ys))).
            elim J return (λ (Jz : Nat). Le (S (S I')) Jz → Le (S Jz) (Len (Cons Y Ys)) →
                Id (List Nat) (Set (S I') (NthL Jz (Cons Y Ys)) (Set Jz (NthL (S I') (Cons Y Ys)) (Cons Y Ys))) (SwapL (S I') Jz (Cons Y Ys))) {
              Z => λ (Pijz : Le (S (S I')) Z). λ (P2z : Le (S Z) (Len (Cons Y Ys))).
                botElim (Id (List Nat) (Set (S I') (NthL Z (Cons Y Ys)) (Set Z (NthL (S I') (Cons Y Ys)) (Cons Y Ys))) (SwapL (S I') Z (Cons Y Ys))) Pijz,
              S (J') Jih => λ (Pijs : Le (S (S I')) (S J')). λ (P2s : Le (S (S J')) (Len (Cons Y Ys))).
                IdCongr (List Nat) (List Nat) (λ (T : List Nat). Cons Y T)
                  (Set I' (NthL J' Ys) (Set J' (NthL I' Ys) Ys)) (SwapL I' J' Ys) (Ih J' Ys Pijs P2s)
            } Pij P2 } } }
def SwapLSetTy : Term := prog defer_check {
  Π (I : Nat) → Π (J : Nat) → Π (L : List Nat) → Le (S I) J → Le (S J) (Len L) →
    Id (List Nat) (Set I (NthL J L) (Set J (NthL I L) L)) (SwapL I J L) }

/-! ## `PartScanL` / `PartitionL` — the pure Lomuto model (§19)

    The EXACT recursion the imperative body performs, so the conformance check
    (convert the body's composed backward tree against this per path) holds. Pivot
    is the FIRST element; the scan carries a boundary `i` (size of the ≤-pivot
    region after the pivot) and a GAP counter `g` (the >-pivot elements found so
    far) — so the scan position is `j = S (Add i g)` and the swap decision is
    STRUCTURAL on `g` (no second stuck-spine split), and the swap is never a
    self-swap (`g = S g'` guarantees `S i < j`). One `Leb` casing per step is the
    only Bool spine, the M19-B gate's job.

    Base (`k = Z`): place the pivot with `SwapL Z i` — cased on `i` because swapS
    cannot self-swap, so `i = Z` is the no-op the imperative body also special-cases.
    Step: `Leb (NthL j l) pivot` — True with `g = Z` advances the boundary (the
    ≤-prefix stays contiguous, no swap); True with `g = S g'` swaps `S i`↔`j`
    (a >-pivot element out, the ≤ element in) keeping the gap; False grows the gap.

    INTERFACE CONTRACT (M21 inheritance): the boundary index `i` at `k = Z` is the
    pivot's final position — the split point the caller recurses on (`[0, i)` and
    `(i, Len)`). partition exposes it as its return value; SortL rides it. -/

def BoolFT : Term := prog defer_check {
  λ (H : Id Bool False True).
    j Bool False (λ (Y' : Bool). λ (Hh : Id Bool False Y'). elim Y' return (λ (Z0 : Bool). Type) { True => Bot, False => Unit })
      unit True H }
def BoolFTTy : Term := prog defer_check { Id Bool False True → Bot }
def BoolTF : Term := prog defer_check {
  λ (H : Id Bool True False).
    j Bool True (λ (Y' : Bool). λ (Hh : Id Bool True Y'). elim Y' return (λ (Z0 : Bool). Type) { True => Unit, False => Bot })
      unit False H }
def BoolTFTy : Term := prog defer_check { Id Bool True False → Bot }

def LebTrueLe : Term := prog defer_check {
  λ (A : Nat).
    elim A return (λ (Az : Nat). Π (B : Nat) → Id Bool (Leb Az B) True → Le Az B) {
      Z => λ (B : Nat). λ (H : Id Bool (Leb Z B) True). unit,
      S (A') Ih => λ (B : Nat).
        elim B return (λ (Bz : Nat). Id Bool (Leb (S A') Bz) True → Le (S A') Bz) {
          Z => λ (H : Id Bool (Leb (S A') Z) True). botElim (Le (S A') Z) (BoolFT H),
          S (B') Ihb => λ (H : Id Bool (Leb (S A') (S B')) True). Ih B' H } } }
def LebTrueLeTy : Term := prog defer_check { Π (A : Nat) → Π (B : Nat) → Id Bool (Leb A B) True → Le A B }

def LebFalseGt : Term := prog defer_check {
  λ (A : Nat).
    elim A return (λ (Az : Nat). Π (B : Nat) → Id Bool (Leb Az B) False → Le (S B) Az) {
      Z => λ (B : Nat). λ (H : Id Bool (Leb Z B) False). botElim (Le (S B) Z) (BoolTF H),
      S (A') Ih => λ (B : Nat).
        elim B return (λ (Bz : Nat). Id Bool (Leb (S A') Bz) False → Le (S Bz) (S A')) {
          Z => λ (H : Id Bool (Leb (S A') Z) False). unit,
          S (B') Ihb => λ (H : Id Bool (Leb (S A') (S B')) False). Ih B' H } } }
def LebFalseGtTy : Term := prog defer_check { Π (A : Nat) → Π (B : Nat) → Id Bool (Leb A B) False → Le (S B) A }

-- Nat antisymmetry (Le a b → Le b a → a = b) — the glue derives its boundary equality
-- (`S k = i` at the last-left/pivot pair) from the two-sided Le bounds a leb-split
-- yields. Double induction; mixed-parity bases are ⊥, equal-parity step is IdCongr S.
def LeAntisym : Term := prog defer_check {
  λ (A : Nat).
    elim A return (λ (Az : Nat). Π (B : Nat) → Le Az B → Le B Az → Id Nat Az B) {
      Z => λ (B : Nat).
        elim B return (λ (Bz : Nat). Le Z Bz → Le Bz Z → Id Nat Z Bz) {
          Z => λ (H1 : Le Z Z). λ (H2 : Le Z Z). Refl,
          S (B') Ihb => λ (H1 : Le Z (S B')). λ (H2 : Le (S B') Z). botElim (Id Nat Z (S B')) H2 },
      S (A') Ih => λ (B : Nat).
        elim B return (λ (Bz : Nat). Le (S A') Bz → Le Bz (S A') → Id Nat (S A') Bz) {
          Z => λ (H1 : Le (S A') Z). λ (H2 : Le Z (S A')). botElim (Id Nat (S A') Z) H1,
          S (B') Ihb => λ (H1 : Le (S A') (S B')). λ (H2 : Le (S B') (S A')).
            IdCongr Nat Nat (λ (N : Nat). S N) A' B' (Ih B' H1 H2) } } }
def LeAntisymTy : Term := prog defer_check { Π (A : Nat) → Π (B : Nat) → Le A B → Le B A → Id Nat A B }

/-! ## AllLeR growth/transport helpers — the region-invariant toolkit (§22, M22-c step 2)

    The partition-invariant proofs thread an AllLeR precondition that GROWS each scan
    step. `AllLeRExtendFar` appends the newly-tested ≤-element at the far end — the
    only place the `m<w` vs `m=w` decision is needed, discharged by leb (remember
    scrutinee) + LebTrueLe/LebFalseGt + LeAntisym. `AllLeRExtendLo` prepends the
    pivot at position lo, absorbing the index-first offset shift `add m (S lo) = add (S
    m) lo` (AddSucc). `AllLeRCong` transports an AllLeR across a pointwise nth-equality
    (fed by the swap-locality lemmas). `AddSwapSucc` bridges index-first `Add a (S b)`
    to `Add b (S a)` — the recurring predicate↔model add-order glue. -/

def Znots : Term := prog defer_check {
  λ (X : Nat). λ (H : Id Nat Z (S X)).
    j Nat Z (λ (Y : Nat). λ (Hy : Id Nat Z Y). elim Y return (λ (Yy : Nat). Type) { Z => Unit, S (K) Ih => Bot })
      unit (S X) H }
def ZnotsTy : Term := prog defer_check { Π (X : Nat) → Id Nat Z (S X) → Bot }

def Pred : Term := prog defer_check { λ (N : Nat). elim N return (λ (Z0 : Nat). Nat) { Z => Z, S (K) Ih => K } }
def SInj : Term := prog defer_check {
  λ (M : Nat). λ (N : Nat). λ (H : Id Nat (S M) (S N)).
    IdCongr Nat Nat Pred (S M) (S N) H }
def SInjTy : Term := prog defer_check { Π (M : Nat) → Π (N : Nat) → Id Nat (S M) (S N) → Id Nat M N }

def Sub : Term := prog defer_check {
  λ (A : Nat).
    elim A return (λ (Az : Nat). Nat → Nat) {
      Z => λ (B : Nat). Z,
      S (A') Rec => λ (B : Nat). elim B return (λ (Bz : Nat). Nat) { Z => S A', S (B') Bih => Rec B' } } }
def SubTy : Term := prog defer_check { Π (A : Nat) → Nat → Nat }
def AddSubCancel : Term := prog defer_check {
  λ (A : Nat).
    elim A return (λ (Az : Nat). Π (B : Nat) → Le B Az → Id Nat (Add B (Sub Az B)) Az) {
      Z => λ (B : Nat).
        elim B return (λ (Bz : Nat). Le Bz Z → Id Nat (Add Bz (Sub Z Bz)) Z) {
          Z => λ (H : Le Z Z). Refl,
          S (B') Bih => λ (H : Le (S B') Z). botElim (Id Nat (Add (S B') (Sub Z (S B'))) Z) H },
      S (A') Ih => λ (B : Nat).
        elim B return (λ (Bz : Nat). Le Bz (S A') → Id Nat (Add Bz (Sub (S A') Bz)) (S A')) {
          Z => λ (H : Le Z (S A')). Refl,
          S (B') Bih => λ (H : Le (S B') (S A')).
            IdCongr Nat Nat (λ (N : Nat). S N) (Add B' (Sub A' B')) A' (Ih B' H) } } }
def AddSubCancelTy : Term := prog defer_check { Π (A : Nat) → Π (B : Nat) → Le B A → Id Nat (Add B (Sub A B)) A }

/-! ## The GLUE — assemble a sorted range from sorted halves (§22, M22-c step 4)

    `Glue`: given the pivot at position `Add i lo`, the left range [lo, lo+i) sorted
    and ≤ pivot, the right range [lo+i+1, …) sorted and > pivot, the WHOLE range
    [lo, lo+i+1+g) is sorted. A nested `Leb`-elim on k vs i (the REMEMBER-SCRUTINEE
    idiom `elim (Leb X) return (λ w. Id Bool (Leb X) w → GOAL) {…} Refl` to recover the
    branch equation) splits the adjacent pair into four cases: both-left (SortedR
    left), left-pivot (k+1=i via LeAntisym; AllLeR + hpiv transport), pivot-right
    (k=i; AllGtR at the first right, after g≥1 from `GapPos`), both-right (k>i;
    reindex the whole-index k into the right segment's `Sub k (S i)` via the
    reindex_* helpers, then SortedR right). Every arithmetic bridge is discharged by
    the add-order toolkit — the positional-predicate ↔ offset-model tax, paid once
    per bound. All kernel-green. -/
def LePredL : Term := prog defer_check {
  λ (A : Nat). λ (B : Nat). λ (H : Le (S A) B).
    LeTrans A (S A) B (LeUpR A A (LeRefl A)) H }
def LePredLTy : Term := prog defer_check { Π (A : Nat) → Π (B : Nat) → Le (S A) B → Le A B }
def EqbGtFalse : Term := prog defer_check {
  λ (H : Nat).
    elim H return (λ (Hz : Nat). Π (X : Nat) → Le (S Hz) X → Id Bool (Eqb X Hz) False) {
      Z => λ (X : Nat).
        elim X return (λ (Xz : Nat). Le (S Z) Xz → Id Bool (Eqb Xz Z) False) {
          Z => λ (Hlt : Le (S Z) Z). botElim (Id Bool (Eqb Z Z) False) Hlt,
          S (X') Xih => λ (Hlt : Le (S Z) (S X')). Refl },
      S (H') Ih => λ (X : Nat).
        elim X return (λ (Xz : Nat). Le (S (S H')) Xz → Id Bool (Eqb Xz (S H')) False) {
          Z => λ (Hlt : Le (S (S H')) Z). botElim (Id Bool (Eqb Z (S H')) False) Hlt,
          S (X') Xih => λ (Hlt : Le (S (S H')) (S X')). Ih X' Hlt } } }
def EqbGtFalseTy : Term := prog defer_check { Π (H : Nat) → Π (X : Nat) → Le (S H) X → Id Bool (Eqb X H) False }

def EqbLtFalse : Term := prog defer_check {
  λ (A : Nat).
    elim A return (λ (Az : Nat). Π (B : Nat) → Le (S Az) B → Id Bool (Eqb Az B) False) {
      Z => λ (B : Nat).
        elim B return (λ (Bz : Nat). Le (S Z) Bz → Id Bool (Eqb Z Bz) False) {
          Z => λ (Hlt : Le (S Z) Z). botElim (Id Bool (Eqb Z Z) False) Hlt,
          S (B') Bih => λ (Hlt : Le (S Z) (S B')). Refl },
      S (A') Ih => λ (B : Nat).
        elim B return (λ (Bz : Nat). Le (S (S A')) Bz → Id Bool (Eqb (S A') Bz) False) {
          Z => λ (Hlt : Le (S (S A')) Z). botElim (Id Bool (Eqb (S A') Z) False) Hlt,
          S (B') Bih => λ (Hlt : Le (S (S A')) (S B')). Ih B' Hlt } } }
def EqbLtFalseTy : Term := prog defer_check { Π (A : Nat) → Π (B : Nat) → Le (S A) B → Id Bool (Eqb A B) False }

def CountConsMiss : Term := prog defer_check {
  λ (M : Nat). λ (H : Nat). λ (T : List Nat). λ (Hq : Id Bool (Eqb M H) False).
    j Bool False
      (λ (Z0 : Bool). λ (Hh : Id Bool False Z0).
        Id Nat (boolRec (λ (W : Bool). Nat) (S (Count M T)) (Count M T) Z0) (Count M T))
      Refl (Eqb M H) (IdSym Bool (Eqb M H) False Hq) }
def CountConsMissTy : Term := prog defer_check {
  Π (M : Nat) → Π (H : Nat) → Π (T : List Nat) → Id Bool (Eqb M H) False →
    Id Nat (Count M (Cons H T)) (Count M T) }

def EqbRefl : Term := prog defer_check {
  λ (N : Nat). elim N return (λ (Nz : Nat). Id Bool (Eqb Nz Nz) True) {
    Z => Refl,
    S (N') Ih => Ih } }
def EqbReflTy : Term := prog defer_check { Π (N : Nat) → Id Bool (Eqb N N) True }

def Ub : Term := prog defer_check {
  λ (P : Nat). λ (L : List Nat).
    elim L return (λ (Lz : List Nat). Type) {
      Nil => Unit,
      Cons (H) (T) Ih => Σ (Hh : Le H P). Ih } }

def Lb : Term := prog defer_check {
  λ (P : Nat). λ (L : List Nat).
    elim L return (λ (Lz : List Nat). Type) {
      Nil => Unit,
      Cons (H) (T) Ih => Σ (Hh : Le P H). Ih } }

def ListRw : Term := prog defer_check {
  λ (P : List Nat → Type). λ (X : List Nat). λ (Y : List Nat).
    λ (H : Id (List Nat) X Y). λ (Px : P X).
      j (List Nat) X (λ (Y2 : List Nat). λ (Hh : Id (List Nat) X Y2). P Y2) Px Y H }
def ListRwTy : Term := prog defer_check {
  Π (P : List Nat → Type) → Π (X : List Nat) → Π (Y : List Nat) →
    Id (List Nat) X Y → P X → P Y }

/-! ## M23 — the pivot glue: `Sorted (a ++ p :: b)` from the four partition facts

    The whole-list counterpart of M22's `sorted_in_*` family. Where the positional
    encoding assembled `SortedR` over a range from four range-scoped facts, the
    back-less partition returns WHOLE lists — a left part, the pivot, a right part —
    and its caller has exactly `Sorted a`, `Ub p a`, `Sorted b`, `Lb p b`. This is
    the lemma that turns those four into the postcondition, and it is the last
    structural step of a back-less quicksort's sortedness half.

    The projections come first. `Sorted`/`Ub` are Σ-chained (Std, M23-iv), so taking
    one apart is a `sigmaRec` — which is exactly why stage (i) had to land before any
    of this could be written. They are stated over `Sorted (Cons h t)` / `Ub p
    (Cons h t)` but the λ domain is written as the UNFOLDED Σ, because the Σ-elim
    sugar reads `A` and `λx. B` off the motive's binder type syntactically. -/

def SortedHead : Term := prog defer_check {
  λ (H : Nat). λ (T : List Nat). λ (S0 : Σ (Hb : Bound H T). Sorted T).
    elim S0 return (λ (Q : Σ (Hb : Bound H T). Sorted T). Bound H T) {
      Pair (X) (Y) => X } }
def SortedHeadTy : Term := prog defer_check {
  Π (H : Nat) → Π (T : List Nat) → Sorted (Cons H T) → Bound H T }

def SortedTail : Term := prog defer_check {
  λ (H : Nat). λ (T : List Nat). λ (S0 : Σ (Hb : Bound H T). Sorted T).
    elim S0 return (λ (Q : Σ (Hb : Bound H T). Sorted T). Sorted T) {
      Pair (X) (Y) => Y } }
def SortedTailTy : Term := prog defer_check {
  Π (H : Nat) → Π (T : List Nat) → Sorted (Cons H T) → Sorted T }

def UbHead : Term := prog defer_check {
  λ (P : Nat). λ (H : Nat). λ (T : List Nat). λ (U : Σ (Hu : Le H P). Ub P T).
    elim U return (λ (Q : Σ (Hu : Le H P). Ub P T). Le H P) {
      Pair (X) (Y) => X } }
def UbHeadTy : Term := prog defer_check {
  Π (P : Nat) → Π (H : Nat) → Π (T : List Nat) → Ub P (Cons H T) → Le H P }

def UbTail : Term := prog defer_check {
  λ (P : Nat). λ (H : Nat). λ (T : List Nat). λ (U : Σ (Hu : Le H P). Ub P T).
    elim U return (λ (Q : Σ (Hu : Le H P). Ub P T). Ub P T) {
      Pair (X) (Y) => Y } }
def UbTailTy : Term := prog defer_check {
  Π (P : Nat) → Π (H : Nat) → Π (T : List Nat) → Ub P (Cons H T) → Ub P T }

/-- `Lb p l ⟹ Bound p l`: a lower bound on EVERY element is in particular a bound on
    the HEAD, which is all `Sorted (Cons p b)` asks of the pivot. The two predicates
    agree definitionally at `Nil` (both `⊤`) and differ at `Cons` only by how much
    they say, so this is a `listRec` whose `Cons` arm is a first projection. -/
def LbBound : Term := prog defer_check {
  λ (P : Nat). λ (L : List Nat).
    elim L return (λ (Lz : List Nat). Lb P Lz → Bound P Lz) {
      Nil => λ (Hn : Unit). Hn,
      Cons (H) (T) Ih => λ (Hl : Σ (Hh : Le P H). Lb P T).
        elim Hl return (λ (Q : Σ (Hh : Le P H). Lb P T). Le P H) {
          Pair (X) (Y) => X } } }
def LbBoundTy : Term := prog defer_check {
  Π (P : Nat) → Π (L : List Nat) → Lb P L → Bound P L }

/-- Head-bound transport across the splice: if `h` bounds the head of `t`, and `h ≤
    p`, then `h` bounds the head of `t ++ p :: b`. The `listRec` on `t` IS the case
    analysis the caller would otherwise have to do inline: at `Nil` the new head is
    the PIVOT (so the bound is `Le h p`, the second hypothesis), at `Cons` the head is
    unchanged by the append (so the bound is the first hypothesis, verbatim). No IH is
    consumed — `Bound` looks exactly one cell deep, so this recursion is a case
    analysis and nothing more. -/
def BoundAppend : Term := prog defer_check {
  λ (H : Nat). λ (P : Nat). λ (T : List Nat). λ (B : List Nat).
    elim T return (λ (Tz : List Nat).
        Bound H Tz → Le H P → Bound H (Append Tz (Cons P B))) {
      Nil => λ (Hb : Unit). λ (Hp : Le H P). Hp,
      Cons (H2) (T2) Ih => λ (Hb : Le H H2). λ (Hp : Le H P). Hb } }
def BoundAppendTy : Term := prog defer_check {
  Π (H : Nat) → Π (P : Nat) → Π (T : List Nat) → Π (B : List Nat) →
    Bound H T → Le H P → Bound H (Append T (Cons P B)) }

/-- The pivot glue. `Sorted a → Ub p a → Sorted b → Lb p b → Sorted (a ++ p :: b)`.

    Induction on `a`, with `b`/`p` and the two right-hand hypotheses fixed outside
    the elim (they do not vary), and `Sorted a`/`Ub p a` INSIDE the motive because
    they do — the `LeTrans` idiom of applying the elim to its own hypotheses at the
    end (`} sa ua`), which is what lets the stated argument order survive an
    induction that needs two of them abstracted.

    The motive is OPEN: it mentions `p` and `b`, which are λ-bound outside the elim
    rather than being parameters of the recursion. That is exactly the shape b86742d4
    settled — `hasType` σ-instantiates λ binders as it descends, so the motive is
    pvar-free by the time the recursor is typed. This lemma is a working positive
    control for it.

    At `Nil` the goal is `Sorted (Cons p b)` = `Bound p b × Sorted b`, built from
    `LbBound` and the fixed `sb`. At `Cons h t` the goal is `Bound h (t ++ p :: b) ×
    Sorted (t ++ p :: b)`: the head bound is `BoundAppend` fed a's own head bound and
    `h ≤ p` from `Ub`, and the tail is the IH at the two tails. Both components are
    definitional — `Append (Cons h t) (Cons p b)` whnf's to `Cons h (append t (Cons p
    b))`, so `Sorted` unfolds straight onto the pair — which is why no `ListRw`
    transport appears anywhere in this proof. -/
def SortedAppendPivot : Term := prog defer_check {
  λ (P : Nat). λ (A : List Nat). λ (B : List Nat).
    λ (Sa : Sorted A). λ (Ua : Ub P A). λ (Sb : Sorted B). λ (Lb0 : Lb P B).
      elim A return (λ (Az : List Nat).
          Sorted Az → Ub P Az → Sorted (Append Az (Cons P B))) {
        Nil => λ (Sn : Unit). λ (Un : Unit). Pair(LbBound P B Lb0, Sb),
        Cons (H) (T) Ih => λ (Sc : Sorted (Cons H T)). λ (Uc : Ub P (Cons H T)).
          Pair(BoundAppend H P T B (SortedHead H T Sc) (UbHead P H T Uc),
               Ih (SortedTail H T Sc) (UbTail P H T Uc))
      } Sa Ua }
def SortedAppendPivotTy : Term := prog defer_check {
  Π (P : Nat) → Π (A : List Nat) → Π (B : List Nat) →
    Sorted A → Ub P A → Sorted B → Lb P B → Sorted (Append A (Cons P B)) }

/-! ## M23 stage (iv) — the two-part vocabulary a relational partition needs

    A partition returns TWO lists whose counts together reconstruct the input's, and
    it decides each element by a `Leb` split. Two facts close the gap between what the
    split hands back and what the postcondition asks for; both are observation-level
    (`Count`, `Add`) and neither mentions partition. The third thing the body wants —
    `Le (S p) x ⟹ Le p x`, to bend `LebFalseGt` into what `Lb p (Cons x _)` asks —
    is already `LePredL` above, from the M22 stack.

    The two-part count step, in its two directions. A partition's invariant is
    `Count n lo + Count n hi = Count n l`, and each recursion step puts the head on
    ONE of the two sides — so the same equation extends by a `Cons` on the left part
    or on the right part, with the whole list gaining that `Cons` either way. Both are
    a `boolRec` on the `Eqb n x` that `Count n (Cons x ·)` unfolds to (the motive
    abstracts the scrutinee out of all three occurrences at once); the arms differ only
    in where the successor has to travel through `Add`. -/

/-- Head onto the LEFT part. `Add (S u) w` is definitionally `S (Add u w)` (`Add`
    recurses on its first argument), so the `True` arm is one `IdCongr`. -/
def CountConsL : Term := prog defer_check {
  λ (N : Nat). λ (X : Nat). λ (A : List Nat). λ (B : List Nat). λ (C : List Nat).
    λ (H : Id Nat (Add (Count N A) (Count N B)) (Count N C)).
      elim (Eqb N X) return (λ (Bv : Bool).
        Id Nat (Add (boolRec (λ (W : Bool). Nat) (S (Count N A)) (Count N A) Bv) (Count N B))
               (boolRec (λ (W : Bool). Nat) (S (Count N C)) (Count N C) Bv)) {
        True => IdCongr Nat Nat (λ (R : Nat). S R)
                  (Add (Count N A) (Count N B)) (Count N C) H,
        False => H } }
def CountConsLTy : Term := prog defer_check {
  Π (N : Nat) → Π (X : Nat) → Π (A : List Nat) → Π (B : List Nat) → Π (C : List Nat) →
    Id Nat (Add (Count N A) (Count N B)) (Count N C) →
    Id Nat (Add (Count N (Cons X A)) (Count N B)) (Count N (Cons X C)) }

/-- Head onto the RIGHT part. Here the successor lands under `Add`'s SECOND argument,
    which is where the asymmetry of a first-argument-recursive `Add` shows up: the
    `True` arm needs `AddSucc` before the `IdCongr`. -/
def CountConsR : Term := prog defer_check {
  λ (N : Nat). λ (X : Nat). λ (A : List Nat). λ (B : List Nat). λ (C : List Nat).
    λ (H : Id Nat (Add (Count N A) (Count N B)) (Count N C)).
      elim (Eqb N X) return (λ (Bv : Bool).
        Id Nat (Add (Count N A) (boolRec (λ (W : Bool). Nat) (S (Count N B)) (Count N B) Bv))
               (boolRec (λ (W : Bool). Nat) (S (Count N C)) (Count N C) Bv)) {
        True => IdTrans Nat (Add (Count N A) (S (Count N B)))
                  (S (Add (Count N A) (Count N B))) (S (Count N C))
                  (AddSucc (Count N A) (Count N B))
                  (IdCongr Nat Nat (λ (R : Nat). S R)
                    (Add (Count N A) (Count N B)) (Count N C) H),
        False => H } }
def CountConsRTy : Term := prog defer_check {
  Π (N : Nat) → Π (X : Nat) → Π (A : List Nat) → Π (B : List Nat) → Π (C : List Nat) →
    Id Nat (Add (Count N A) (Count N B)) (Count N C) →
    Id Nat (Add (Count N A) (Count N (Cons X B))) (Count N (Cons X C)) }

/-! ## M23 stage (vi) — BOUND SURVIVAL, the whole-list keystone

    A partition-based quicksort's sortedness proof needs `Ub p a` where `a` is the
    left part AFTER it has been sorted, while the partition only ever bounded it
    BEFORE. So a bound must survive a permutation, and `Ub`/`Lb` — being Σ-chains over
    the list's spine — are not natively permutation-invariant.

    M22 hit this at the positional encoding and named the route: go through the
    multiset. `noAbove p l := Π x. Le (S p) x → Count x l = Z` ("nothing above p is
    present") is *manifestly* permutation-invariant, because it is a statement about
    counts and nothing else — so `UbPerm` is two conversions with a one-line
    `IdTrans` between them, and all the work sits in the conversions, where it is
    ordinary induction. The `Lb` side mirrors it through `noBelow`.

    The two predicates are written inline as Π-types rather than named: they exist
    only to be crossed. -/

/-- The two `Lb` projections, mirroring `UbHead`/`UbTail`. -/
def LbHead : Term := prog defer_check {
  λ (P : Nat). λ (H : Nat). λ (T : List Nat). λ (U : Σ (Hu : Le P H). Lb P T).
    elim U return (λ (Q : Σ (Hu : Le P H). Lb P T). Le P H) {
      Pair (X) (Y) => X } }
def LbHeadTy : Term := prog defer_check {
  Π (P : Nat) → Π (H : Nat) → Π (T : List Nat) → Lb P (Cons H T) → Le P H }

def LbTail : Term := prog defer_check {
  λ (P : Nat). λ (H : Nat). λ (T : List Nat). λ (U : Σ (Hu : Le P H). Lb P T).
    elim U return (λ (Q : Σ (Hu : Le P H). Lb P T). Lb P T) {
      Pair (X) (Y) => Y } }
def LbTailTy : Term := prog defer_check {
  Π (P : Nat) → Π (H : Nat) → Π (T : List Nat) → Lb P (Cons H T) → Lb P T }

/-- `Ub p l ⟹ nothing above p occurs in l`. At `Cons h t` the head misses every
    `x > p`, because `h ≤ p < x` makes `Eqb x h` False (`EqbGtFalse`), so the count
    steps past the head onto the IH. -/
def NoAboveOfUb : Term := prog defer_check {
  λ (P : Nat). λ (L : List Nat).
    elim L return (λ (Lz : List Nat).
        Ub P Lz → Π (X : Nat) → Le (S P) X → Id Nat (Count X Lz) Z) {
      Nil => λ (U : Unit). λ (X : Nat). λ (Hx : Le (S P) X). Refl,
      Cons (H) (T) Ih => λ (U : Σ (Hh : Le H P). Ub P T). λ (X : Nat). λ (Hx : Le (S P) X).
        IdTrans Nat (Count X (Cons H T)) (Count X T) Z
          (CountConsMiss X H T
            (EqbGtFalse H X (LeTrans (S H) (S P) X (UbHead P H T U) Hx)))
          (Ih (UbTail P H T U) X Hx) } }
def NoAboveOfUbTy : Term := prog defer_check {
  Π (P : Nat) → Π (L : List Nat) → Ub P L →
    Π (X : Nat) → Le (S P) X → Id Nat (Count X L) Z }

/-- …and back. The head bound comes from a `Leb h p` split: if it were False then
    `h > p`, so `Count h l = Z` by hypothesis — but `Count h (Cons h t)` is `S (count
    h t)` (`EqbRefl`), and `Z = S _` is `znots`. The tail hypothesis is the same
    argument run the other way: `Count x (Cons h t) = Z` forces `Count x t = Z`,
    trivially when `Eqb x h` misses and by the same contradiction when it hits. -/
def UbOfNoAbove : Term := prog defer_check {
  λ (P : Nat). λ (L : List Nat).
    elim L return (λ (Lz : List Nat).
        (Π (X : Nat) → Le (S P) X → Id Nat (Count X Lz) Z) → Ub P Lz) {
      Nil => λ (Hn : Π (X : Nat) → Le (S P) X → Id Nat (Count X Nil) Z). unit,
      Cons (H) (T) Ih => λ (Hn : Π (X : Nat) → Le (S P) X → Id Nat (Count X (Cons H T)) Z).
        Pair(
          elim (Leb H P) return (λ (Bv : Bool). Id Bool (Leb H P) Bv → Le H P) {
            True => λ (E : Id Bool (Leb H P) True). LebTrueLe H P E,
            False => λ (E : Id Bool (Leb H P) False).
              botElim (Le H P)
                (Znots (Count H T)
                  (IdTrans Nat Z (Count H (Cons H T)) (S (Count H T))
                    (IdSym Nat (Count H (Cons H T)) Z (Hn H (LebFalseGt H P E)))
                    (CountConsHit H H T (EqbRefl H))))
          } Refl,
          Ih (λ (X : Nat). λ (Hx : Le (S P) X).
                elim (Eqb X H) return (λ (Bv : Bool). Id Bool (Eqb X H) Bv → Id Nat (Count X T) Z) {
                  True => λ (Eq : Id Bool (Eqb X H) True).
                    botElim (Id Nat (Count X T) Z)
                      (Znots (Count X T)
                        (IdTrans Nat Z (Count X (Cons H T)) (S (Count X T))
                          (IdSym Nat (Count X (Cons H T)) Z (Hn X Hx))
                          (CountConsHit X H T Eq))),
                  False => λ (Eq : Id Bool (Eqb X H) False).
                    IdTrans Nat (Count X T) (Count X (Cons H T)) Z
                      (IdSym Nat (Count X (Cons H T)) (Count X T) (CountConsMiss X H T Eq))
                      (Hn X Hx)
                } Refl)) } }
def UbOfNoAboveTy : Term := prog defer_check {
  Π (P : Nat) → Π (L : List Nat) →
    (Π (X : Nat) → Le (S P) X → Id Nat (Count X L) Z) → Ub P L }

/-- THE KEYSTONE. An upper bound survives any count-preserving rearrangement — which
    is exactly what a recursive sort hands back about the part it sorted. -/
def UbPerm : Term := prog defer_check {
  λ (P : Nat). λ (A : List Nat). λ (B : List Nat).
    λ (Hc : Π (N : Nat) → Id Nat (Count N A) (Count N B)). λ (Hb : Ub P B).
      UbOfNoAbove P A (λ (X : Nat). λ (Hx : Le (S P) X).
        IdTrans Nat (Count X A) (Count X B) Z (Hc X) (NoAboveOfUb P B Hb X Hx)) }
def UbPermTy : Term := prog defer_check {
  Π (P : Nat) → Π (A : List Nat) → Π (B : List Nat) →
    (Π (N : Nat) → Id Nat (Count N A) (Count N B)) → Ub P B → Ub P A }

/-- The `Lb` mirror: `Lb p l ⟹ nothing strictly below p occurs`. Here the head misses
    every `x < p ≤ h` by `EqbLtFalse`. -/
def NoBelowOfLb : Term := prog defer_check {
  λ (P : Nat). λ (L : List Nat).
    elim L return (λ (Lz : List Nat).
        Lb P Lz → Π (X : Nat) → Le (S X) P → Id Nat (Count X Lz) Z) {
      Nil => λ (U : Unit). λ (X : Nat). λ (Hx : Le (S X) P). Refl,
      Cons (H) (T) Ih => λ (U : Σ (Hh : Le P H). Lb P T). λ (X : Nat). λ (Hx : Le (S X) P).
        IdTrans Nat (Count X (Cons H T)) (Count X T) Z
          (CountConsMiss X H T
            (EqbLtFalse X H (LeTrans (S X) P H Hx (LbHead P H T U))))
          (Ih (LbTail P H T U) X Hx) } }
def NoBelowOfLbTy : Term := prog defer_check {
  Π (P : Nat) → Π (L : List Nat) → Lb P L →
    Π (X : Nat) → Le (S X) P → Id Nat (Count X L) Z }

def LbOfNoBelow : Term := prog defer_check {
  λ (P : Nat). λ (L : List Nat).
    elim L return (λ (Lz : List Nat).
        (Π (X : Nat) → Le (S X) P → Id Nat (Count X Lz) Z) → Lb P Lz) {
      Nil => λ (Hn : Π (X : Nat) → Le (S X) P → Id Nat (Count X Nil) Z). unit,
      Cons (H) (T) Ih => λ (Hn : Π (X : Nat) → Le (S X) P → Id Nat (Count X (Cons H T)) Z).
        Pair(
          elim (Leb P H) return (λ (Bv : Bool). Id Bool (Leb P H) Bv → Le P H) {
            True => λ (E : Id Bool (Leb P H) True). LebTrueLe P H E,
            False => λ (E : Id Bool (Leb P H) False).
              botElim (Le P H)
                (Znots (Count H T)
                  (IdTrans Nat Z (Count H (Cons H T)) (S (Count H T))
                    (IdSym Nat (Count H (Cons H T)) Z (Hn H (LebFalseGt P H E)))
                    (CountConsHit H H T (EqbRefl H))))
          } Refl,
          Ih (λ (X : Nat). λ (Hx : Le (S X) P).
                elim (Eqb X H) return (λ (Bv : Bool). Id Bool (Eqb X H) Bv → Id Nat (Count X T) Z) {
                  True => λ (Eq : Id Bool (Eqb X H) True).
                    botElim (Id Nat (Count X T) Z)
                      (Znots (Count X T)
                        (IdTrans Nat Z (Count X (Cons H T)) (S (Count X T))
                          (IdSym Nat (Count X (Cons H T)) Z (Hn X Hx))
                          (CountConsHit X H T Eq))),
                  False => λ (Eq : Id Bool (Eqb X H) False).
                    IdTrans Nat (Count X T) (Count X (Cons H T)) Z
                      (IdSym Nat (Count X (Cons H T)) (Count X T) (CountConsMiss X H T Eq))
                      (Hn X Hx)
                } Refl)) } }
def LbOfNoBelowTy : Term := prog defer_check {
  Π (P : Nat) → Π (L : List Nat) →
    (Π (X : Nat) → Le (S X) P → Id Nat (Count X L) Z) → Lb P L }

def LbPerm : Term := prog defer_check {
  λ (P : Nat). λ (A : List Nat). λ (B : List Nat).
    λ (Hc : Π (N : Nat) → Id Nat (Count N A) (Count N B)). λ (Hb : Lb P B).
      LbOfNoBelow P A (λ (X : Nat). λ (Hx : Le (S X) P).
        IdTrans Nat (Count X A) (Count X B) Z (Hc X) (NoBelowOfLb P B Hb X Hx)) }
def LbPermTy : Term := prog defer_check {
  Π (P : Nat) → Π (A : List Nat) → Π (B : List Nat) →
    (Π (N : Nat) → Id Nat (Count N A) (Count N B)) → Lb P B → Lb P A }

/-! ## M24 — the ARRAY layer (¶6's migration ledger, item 3)

    ¶1.3's promise: "Every lemma in the quicksort library — `Count`, `Sorted`, `Bound`,
    the order stack — transfers to arrays by replacing `listRec` with `arrRec` and
    `Cons` with `acons`. Nothing about the migration requires re-deriving that
    mathematics." Here is the transfer, and the promise holds textually: each
    definition below is its list counterpart with `elim` retargeted at the array
    recursor, and each proof is its list proof with the same substitution.

    Two ι-rules make it mechanical rather than merely possible (see `Pure.lean`):
    `arrCat` computes on an `acons`-headed left argument, and `arrRec` fires on the
    cons view. Without them `SortedA (arrCat (acons h t) …)` would not UNFOLD, and every
    step of the glue would want a transport lemma where the list proof needs none. -/

def CountA : Term := prog defer_check {
  λ (X : Nat). λ (N : Nat). λ (A : Array N Nat).
    arrRec Nat (λ (M : Nat). λ (B : Array M Nat). Nat) Z
      (λ (K : Nat). λ (H : Nat). λ (T : Array K Nat). λ (Ih : Nat).
        elim (Eqb X H) return (λ (Bz : Bool). Nat) { True => S Ih, False => Ih })
      N A }

/-- `BoundA p a` — the head of `a` is ≥ `p`. `Bound`'s transfer. -/
def BoundA : Term := prog defer_check {
  λ (P : Nat). λ (N : Nat). λ (A : Array N Nat).
    arrRec Nat (λ (M : Nat). λ (B : Array M Nat). Type) Unit
      (λ (K : Nat). λ (H : Nat). λ (T : Array K Nat). λ (Ih : Type). Le P H) N A }

/-- `SortedA a` — the Σ-chain over the spine. `Sorted`'s transfer. -/
def SortedA : Term := prog defer_check {
  λ (N : Nat). λ (A : Array N Nat).
    arrRec Nat (λ (M : Nat). λ (B : Array M Nat). Type) Unit
      (λ (K : Nat). λ (H : Nat). λ (T : Array K Nat). λ (Ih : Type).
        Σ (Hb : BoundA H K T). Ih) N A }

/-- `UbA p a` — every element of `a` is ≤ `p`. `Ub`'s transfer. -/
def UbA : Term := prog defer_check {
  λ (P : Nat). λ (N : Nat). λ (A : Array N Nat).
    arrRec Nat (λ (M : Nat). λ (B : Array M Nat). Type) Unit
      (λ (K : Nat). λ (H : Nat). λ (T : Array K Nat). λ (Ih : Type).
        Σ (Hh : Le H P). Ih) N A }

/-- `LbA p a` — every element of `a` is ≥ `p`. `Lb`'s transfer. -/
def LbA : Term := prog defer_check {
  λ (P : Nat). λ (N : Nat). λ (A : Array N Nat).
    arrRec Nat (λ (M : Nat). λ (B : Array M Nat). Type) Unit
      (λ (K : Nat). λ (H : Nat). λ (T : Array K Nat). λ (Ih : Type).
        Σ (Hh : Le P H). Ih) N A }

/-- `Asingle x` — the one-element array, `[x]`. ¶6's glue is stated over
    `arrCat (Asingle p) r`, which is the array spelling of `Cons p b`. -/
def Asingle : Term := prog defer_check { λ (X : Nat). acons Z X Arr() }

/-! ### The glue, and the standing claim it tests

    ¶6: "Set `Append ↦ arrCat` and `Cons p b ↦ arrCat (Asingle p) r` and it IS the array
    lemma, hypothesis for hypothesis — not merely the same shape but the same statement
    modulo the container … So the migration INHERITS that proof rather than opening a
    stratum."

    Below is `SortedAppendPivot` and its four helpers with exactly that substitution
    applied and nothing else. The claim is checkable and it checks. Note in particular
    that `arrCat 1 q (Asingle p) b` COMPUTES to `acons q p b` — the array `Cons p b` —
    so the doc's chosen spelling of the pivot splice needs no lemma to relate it to the
    cons view. -/

def SortedHeadA : Term := prog defer_check {
  λ (K : Nat). λ (H : Nat). λ (T : Array K Nat).
    λ (S0 : Σ (Hb : BoundA H K T). SortedA K T).
      elim S0 return (λ (Q : Σ (Hb : BoundA H K T). SortedA K T). BoundA H K T) {
        Pair (X) (Y) => X } }
def SortedHeadATy : Term := prog defer_check {
  Π (K : Nat) → Π (H : Nat) → Π (T : Array K Nat) →
    SortedA (S K) (acons K H T) → BoundA H K T }

def SortedTailA : Term := prog defer_check {
  λ (K : Nat). λ (H : Nat). λ (T : Array K Nat).
    λ (S0 : Σ (Hb : BoundA H K T). SortedA K T).
      elim S0 return (λ (Q : Σ (Hb : BoundA H K T). SortedA K T). SortedA K T) {
        Pair (X) (Y) => Y } }
def SortedTailATy : Term := prog defer_check {
  Π (K : Nat) → Π (H : Nat) → Π (T : Array K Nat) →
    SortedA (S K) (acons K H T) → SortedA K T }

def UbHeadA : Term := prog defer_check {
  λ (P : Nat). λ (K : Nat). λ (H : Nat). λ (T : Array K Nat).
    λ (U : Σ (Hu : Le H P). UbA P K T).
      elim U return (λ (Q : Σ (Hu : Le H P). UbA P K T). Le H P) {
        Pair (X) (Y) => X } }
def UbHeadATy : Term := prog defer_check {
  Π (P : Nat) → Π (K : Nat) → Π (H : Nat) → Π (T : Array K Nat) →
    UbA P (S K) (acons K H T) → Le H P }

def UbTailA : Term := prog defer_check {
  λ (P : Nat). λ (K : Nat). λ (H : Nat). λ (T : Array K Nat).
    λ (U : Σ (Hu : Le H P). UbA P K T).
      elim U return (λ (Q : Σ (Hu : Le H P). UbA P K T). UbA P K T) {
        Pair (X) (Y) => Y } }
def UbTailATy : Term := prog defer_check {
  Π (P : Nat) → Π (K : Nat) → Π (H : Nat) → Π (T : Array K Nat) →
    UbA P (S K) (acons K H T) → UbA P K T }

/-- `LbA p a ⟹ BoundA p a`, `LbBound`'s transfer: a lower bound on every element is in
    particular a bound on the head, which is all `SortedA (acons p b)` asks of the pivot. -/
def LbBoundA : Term := prog defer_check {
  λ (P : Nat). λ (N : Nat). λ (A : Array N Nat).
    arrRec Nat (λ (M : Nat). λ (B : Array M Nat). LbA P M B → BoundA P M B)
      (λ (Hn : Unit). Hn)
      (λ (K : Nat). λ (H : Nat). λ (T : Array K Nat).
        λ (Ih : LbA P K T → BoundA P K T).
          λ (Hl : Σ (Hh : Le P H). LbA P K T).
            elim Hl return (λ (Q : Σ (Hh : Le P H). LbA P K T). Le P H) {
              Pair (X) (Y) => X })
      N A }
def LbBoundATy : Term := prog defer_check {
  Π (P : Nat) → Π (N : Nat) → Π (A : Array N Nat) → LbA P N A → BoundA P N A }

/-- `BoundAppend`'s transfer: the head bound survives the splice. The recursion IS the
    case analysis — at the empty array the new head is the PIVOT, otherwise the head is
    unchanged by the concatenation. No IH is consumed, because `BoundA` looks exactly one
    cell deep. -/
def BoundArrCat : Term := prog defer_check {
  λ (H : Nat). λ (P : Nat). λ (K : Nat). λ (T : Array K Nat).
    λ (Q : Nat). λ (B : Array Q Nat).
      arrRec Nat (λ (M : Nat). λ (Tz : Array M Nat).
          BoundA H M Tz → Le H P →
            BoundA H (Add M (S Q)) (arrCat M (S Q) Tz (arrCat 1 Q (Asingle P) B)))
        (λ (Hb : Unit). λ (Hp : Le H P). Hp)
        (λ (K2 : Nat). λ (H2 : Nat). λ (T2 : Array K2 Nat).
          λ (Ih : BoundA H K2 T2 → Le H P →
              BoundA H (Add K2 (S Q)) (arrCat K2 (S Q) T2 (arrCat 1 Q (Asingle P) B))).
            λ (Hb : Le H H2). λ (Hp : Le H P). Hb)
        K T }
def BoundArrCatTy : Term := prog defer_check {
  Π (H : Nat) → Π (P : Nat) → Π (K : Nat) → Π (T : Array K Nat) →
    Π (Q : Nat) → Π (B : Array Q Nat) →
      BoundA H K T → Le H P →
        BoundA H (Add K (S Q)) (arrCat K (S Q) T (arrCat 1 Q (Asingle P) B)) }

/-- **The quicksort glue** — `SortedAppendPivot` with the container swapped, and
    nothing else changed. This is ¶6's "textbook quicksort correctness statement, in the
    textbook shape", and the standing check on the whole migration: if this were not the
    near-verbatim restatement, something would be off. -/
def SortedArrCat : Term := prog defer_check {
  λ (P : Nat). λ (M : Nat). λ (A : Array M Nat). λ (Q : Nat). λ (B : Array Q Nat).
    λ (Sa : SortedA M A). λ (Ua : UbA P M A). λ (Sb : SortedA Q B). λ (Lb0 : LbA P Q B).
      arrRec Nat (λ (Mz : Nat). λ (Az : Array Mz Nat).
          SortedA Mz Az → UbA P Mz Az →
            SortedA (Add Mz (S Q)) (arrCat Mz (S Q) Az (arrCat 1 Q (Asingle P) B)))
        (λ (Sn : Unit). λ (Un : Unit). Pair(LbBoundA P Q B Lb0, Sb))
        (λ (K : Nat). λ (H : Nat). λ (T : Array K Nat).
          λ (Ih : SortedA K T → UbA P K T →
              SortedA (Add K (S Q)) (arrCat K (S Q) T (arrCat 1 Q (Asingle P) B))).
            λ (Sc : Σ (Hb : BoundA H K T). SortedA K T).
              λ (Uc : Σ (Hu : Le H P). UbA P K T).
                Pair(BoundArrCat H P K T Q B (SortedHeadA K H T Sc) (UbHeadA P K H T Uc),
                     Ih (SortedTailA K H T Sc) (UbTailA P K H T Uc)))
        M A Sa Ua }
def SortedArrCatTy : Term := prog defer_check {
  Π (P : Nat) → Π (M : Nat) → Π (A : Array M Nat) → Π (Q : Nat) → Π (B : Array Q Nat) →
    SortedA M A → UbA P M A → SortedA Q B → LbA P Q B →
      SortedA (Add M (S Q)) (arrCat M (S Q) A (arrCat 1 Q (Asingle P) B)) }

/-- `CountAppend`'s transfer, and ¶6's named survivor: "the one lemma that replaces
    `CountAppend`/`Take`/`Drop` is `CountArrCat : count x (arrCat a b) = add (count x a)
    (count x b)`, which is the same induction." It is the same induction — the `Cons`
    arm's dependent Bool-elim on `Eqb x h` transfers unchanged, because `CountA` unfolds
    on an `acons` exactly as `Count` unfolds on a `Cons`. -/
def CountArrCat : Term := prog defer_check {
  λ (X : Nat). λ (M : Nat). λ (A : Array M Nat). λ (Q : Nat). λ (B : Array Q Nat).
    arrRec Nat (λ (Mz : Nat). λ (Az : Array Mz Nat).
        Id Nat (CountA X (Add Mz Q) (arrCat Mz Q Az B))
               (Add (CountA X Mz Az) (CountA X Q B)))
      Refl
      (λ (K : Nat). λ (H : Nat). λ (T : Array K Nat).
        λ (Ih : Id Nat (CountA X (Add K Q) (arrCat K Q T B))
                       (Add (CountA X K T) (CountA X Q B))).
          elim (Eqb X H) return (λ (Bv : Bool).
            Id Nat (boolRec (λ (W : Bool). Nat)
                     (S (CountA X (Add K Q) (arrCat K Q T B)))
                     (CountA X (Add K Q) (arrCat K Q T B)) Bv)
                   (Add (boolRec (λ (W : Bool). Nat)
                     (S (CountA X K T)) (CountA X K T) Bv) (CountA X Q B))) {
            True => IdCongr Nat Nat (λ (N : Nat). S N)
                      (CountA X (Add K Q) (arrCat K Q T B))
                      (Add (CountA X K T) (CountA X Q B)) Ih,
            False => Ih })
      M A }
def CountArrCatTy : Term := prog defer_check {
  Π (X : Nat) → Π (M : Nat) → Π (A : Array M Nat) → Π (Q : Nat) → Π (B : Array Q Nat) →
    Id Nat (CountA X (Add M Q) (arrCat M Q A B)) (Add (CountA X M A) (CountA X Q B)) }

/-! ### The permutation layer, transferred

    M23's keystone: "`Ub` and `Lb` (Σ-chains over the spine) are not natively
    permutation-invariant. Cross to the multiset, where the property is
    `Π x. x > p → Count x l = Z` and permutation-invariance is a one-line `IdTrans`."
    That crossing transfers with the container like everything else. -/

def CountAconsHit : Term := prog defer_check {
  λ (M : Nat). λ (A : Nat). λ (K : Nat). λ (L : Array K Nat). λ (Hq : Id Bool (Eqb M A) True).
    j Bool True
      (λ (Z0 : Bool). λ (H : Id Bool True Z0).
        Id Nat (boolRec (λ (W : Bool). Nat) (S (CountA M K L)) (CountA M K L) Z0)
               (S (CountA M K L)))
      Refl (Eqb M A) (IdSym Bool (Eqb M A) True Hq) }
def CountAconsHitTy : Term := prog defer_check {
  Π (M : Nat) → Π (A : Nat) → Π (K : Nat) → Π (L : Array K Nat) → Id Bool (Eqb M A) True →
    Id Nat (CountA M (S K) (acons K A L)) (S (CountA M K L)) }

def CountAconsMiss : Term := prog defer_check {
  λ (M : Nat). λ (H : Nat). λ (K : Nat). λ (T : Array K Nat). λ (Hq : Id Bool (Eqb M H) False).
    j Bool False
      (λ (Z0 : Bool). λ (Hh : Id Bool False Z0).
        Id Nat (boolRec (λ (W : Bool). Nat) (S (CountA M K T)) (CountA M K T) Z0)
               (CountA M K T))
      Refl (Eqb M H) (IdSym Bool (Eqb M H) False Hq) }
def CountAconsMissTy : Term := prog defer_check {
  Π (M : Nat) → Π (H : Nat) → Π (K : Nat) → Π (T : Array K Nat) → Id Bool (Eqb M H) False →
    Id Nat (CountA M (S K) (acons K H T)) (CountA M K T) }

def LbHeadA : Term := prog defer_check {
  λ (P : Nat). λ (K : Nat). λ (H : Nat). λ (T : Array K Nat).
    λ (U : Σ (Hh : Le P H). LbA P K T).
      elim U return (λ (Q : Σ (Hh : Le P H). LbA P K T). Le P H) { Pair (X) (Y) => X } }
def LbTailA : Term := prog defer_check {
  λ (P : Nat). λ (K : Nat). λ (H : Nat). λ (T : Array K Nat).
    λ (U : Σ (Hh : Le P H). LbA P K T).
      elim U return (λ (Q : Σ (Hh : Le P H). LbA P K T). LbA P K T) { Pair (X) (Y) => Y } }

def NoAboveOfUbA : Term := prog defer_check {
  λ (P : Nat). λ (N : Nat). λ (A : Array N Nat).
    arrRec Nat (λ (M : Nat). λ (Az : Array M Nat).
        UbA P M Az → Π (X : Nat) → Le (S P) X → Id Nat (CountA X M Az) Z)
      (λ (U : Unit). λ (X : Nat). λ (Hx : Le (S P) X). Refl)
      (λ (K : Nat). λ (H : Nat). λ (T : Array K Nat).
        λ (Ih : UbA P K T → Π (X : Nat) → Le (S P) X → Id Nat (CountA X K T) Z).
          λ (U : Σ (Hh : Le H P). UbA P K T). λ (X : Nat). λ (Hx : Le (S P) X).
            IdTrans Nat (CountA X (S K) (acons K H T)) (CountA X K T) Z
              (CountAconsMiss X H K T
                (EqbGtFalse H X (LeTrans (S H) (S P) X (UbHeadA P K H T U) Hx)))
              (Ih (UbTailA P K H T U) X Hx))
      N A }
def NoAboveOfUbATy : Term := prog defer_check {
  Π (P : Nat) → Π (N : Nat) → Π (A : Array N Nat) → UbA P N A →
    Π (X : Nat) → Le (S P) X → Id Nat (CountA X N A) Z }

def UbOfNoAboveA : Term := prog defer_check {
  λ (P : Nat). λ (N : Nat). λ (A : Array N Nat).
    arrRec Nat (λ (M : Nat). λ (Az : Array M Nat).
        (Π (X : Nat) → Le (S P) X → Id Nat (CountA X M Az) Z) → UbA P M Az)
      (λ (Hn : Π (X : Nat) → Le (S P) X → Id Nat (CountA X Z Arr()) Z). unit)
      (λ (K : Nat). λ (H : Nat). λ (T : Array K Nat).
        λ (Ih : (Π (X : Nat) → Le (S P) X → Id Nat (CountA X K T) Z) → UbA P K T).
          λ (Hn : Π (X : Nat) → Le (S P) X → Id Nat (CountA X (S K) (acons K H T)) Z).
            Pair(
              elim (Leb H P) return (λ (Bv : Bool). Id Bool (Leb H P) Bv → Le H P) {
                True => λ (E : Id Bool (Leb H P) True). LebTrueLe H P E,
                False => λ (E : Id Bool (Leb H P) False).
                  botElim (Le H P)
                    (Znots (CountA H K T)
                      (IdTrans Nat Z (CountA H (S K) (acons K H T)) (S (CountA H K T))
                        (IdSym Nat (CountA H (S K) (acons K H T)) Z (Hn H (LebFalseGt H P E)))
                        (CountAconsHit H H K T (EqbRefl H))))
              } Refl,
              Ih (λ (X : Nat). λ (Hx : Le (S P) X).
                    elim (Eqb X H) return (λ (Bv : Bool).
                        Id Bool (Eqb X H) Bv → Id Nat (CountA X K T) Z) {
                      True => λ (Eq : Id Bool (Eqb X H) True).
                        botElim (Id Nat (CountA X K T) Z)
                          (Znots (CountA X K T)
                            (IdTrans Nat Z (CountA X (S K) (acons K H T)) (S (CountA X K T))
                              (IdSym Nat (CountA X (S K) (acons K H T)) Z (Hn X Hx))
                              (CountAconsHit X H K T Eq))),
                      False => λ (Eq : Id Bool (Eqb X H) False).
                        IdTrans Nat (CountA X K T) (CountA X (S K) (acons K H T)) Z
                          (IdSym Nat (CountA X (S K) (acons K H T)) (CountA X K T)
                            (CountAconsMiss X H K T Eq))
                          (Hn X Hx)
                    } Refl)))
      N A }
def UbOfNoAboveATy : Term := prog defer_check {
  Π (P : Nat) → Π (N : Nat) → Π (A : Array N Nat) →
    (Π (X : Nat) → Le (S P) X → Id Nat (CountA X N A) Z) → UbA P N A }

/-- THE KEYSTONE, transferred: an upper bound survives any count-preserving
    rearrangement — which is exactly what a recursive sort hands back about the part it
    sorted. -/
def UbPermA : Term := prog defer_check {
  λ (P : Nat). λ (M : Nat). λ (A : Array M Nat). λ (Q : Nat). λ (B : Array Q Nat).
    λ (Hc : Π (X : Nat) → Id Nat (CountA X M A) (CountA X Q B)). λ (Hb : UbA P Q B).
      UbOfNoAboveA P M A (λ (X : Nat). λ (Hx : Le (S P) X).
        IdTrans Nat (CountA X M A) (CountA X Q B) Z (Hc X)
          (NoAboveOfUbA P Q B Hb X Hx)) }
def UbPermATy : Term := prog defer_check {
  Π (P : Nat) → Π (M : Nat) → Π (A : Array M Nat) → Π (Q : Nat) → Π (B : Array Q Nat) →
    (Π (X : Nat) → Id Nat (CountA X M A) (CountA X Q B)) → UbA P Q B → UbA P M A }

def NoBelowOfLbA : Term := prog defer_check {
  λ (P : Nat). λ (N : Nat). λ (A : Array N Nat).
    arrRec Nat (λ (M : Nat). λ (Az : Array M Nat).
        LbA P M Az → Π (X : Nat) → Le (S X) P → Id Nat (CountA X M Az) Z)
      (λ (U : Unit). λ (X : Nat). λ (Hx : Le (S X) P). Refl)
      (λ (K : Nat). λ (H : Nat). λ (T : Array K Nat).
        λ (Ih : LbA P K T → Π (X : Nat) → Le (S X) P → Id Nat (CountA X K T) Z).
          λ (U : Σ (Hh : Le P H). LbA P K T). λ (X : Nat). λ (Hx : Le (S X) P).
            IdTrans Nat (CountA X (S K) (acons K H T)) (CountA X K T) Z
              (CountAconsMiss X H K T
                (EqbLtFalse X H (LeTrans (S X) P H Hx (LbHeadA P K H T U))))
              (Ih (LbTailA P K H T U) X Hx))
      N A }
def NoBelowOfLbATy : Term := prog defer_check {
  Π (P : Nat) → Π (N : Nat) → Π (A : Array N Nat) → LbA P N A →
    Π (X : Nat) → Le (S X) P → Id Nat (CountA X N A) Z }

def LbOfNoBelowA : Term := prog defer_check {
  λ (P : Nat). λ (N : Nat). λ (A : Array N Nat).
    arrRec Nat (λ (M : Nat). λ (Az : Array M Nat).
        (Π (X : Nat) → Le (S X) P → Id Nat (CountA X M Az) Z) → LbA P M Az)
      (λ (Hn : Π (X : Nat) → Le (S X) P → Id Nat (CountA X Z Arr()) Z). unit)
      (λ (K : Nat). λ (H : Nat). λ (T : Array K Nat).
        λ (Ih : (Π (X : Nat) → Le (S X) P → Id Nat (CountA X K T) Z) → LbA P K T).
          λ (Hn : Π (X : Nat) → Le (S X) P → Id Nat (CountA X (S K) (acons K H T)) Z).
            Pair(
              elim (Leb P H) return (λ (Bv : Bool). Id Bool (Leb P H) Bv → Le P H) {
                True => λ (E : Id Bool (Leb P H) True). LebTrueLe P H E,
                False => λ (E : Id Bool (Leb P H) False).
                  botElim (Le P H)
                    (Znots (CountA H K T)
                      (IdTrans Nat Z (CountA H (S K) (acons K H T)) (S (CountA H K T))
                        (IdSym Nat (CountA H (S K) (acons K H T)) Z (Hn H (LebFalseGt P H E)))
                        (CountAconsHit H H K T (EqbRefl H))))
              } Refl,
              Ih (λ (X : Nat). λ (Hx : Le (S X) P).
                    elim (Eqb X H) return (λ (Bv : Bool).
                        Id Bool (Eqb X H) Bv → Id Nat (CountA X K T) Z) {
                      True => λ (Eq : Id Bool (Eqb X H) True).
                        botElim (Id Nat (CountA X K T) Z)
                          (Znots (CountA X K T)
                            (IdTrans Nat Z (CountA X (S K) (acons K H T)) (S (CountA X K T))
                              (IdSym Nat (CountA X (S K) (acons K H T)) Z (Hn X Hx))
                              (CountAconsHit X H K T Eq))),
                      False => λ (Eq : Id Bool (Eqb X H) False).
                        IdTrans Nat (CountA X K T) (CountA X (S K) (acons K H T)) Z
                          (IdSym Nat (CountA X (S K) (acons K H T)) (CountA X K T)
                            (CountAconsMiss X H K T Eq))
                          (Hn X Hx)
                    } Refl)))
      N A }
def LbOfNoBelowATy : Term := prog defer_check {
  Π (P : Nat) → Π (N : Nat) → Π (A : Array N Nat) →
    (Π (X : Nat) → Le (S X) P → Id Nat (CountA X N A) Z) → LbA P N A }

def LbPermA : Term := prog defer_check {
  λ (P : Nat). λ (M : Nat). λ (A : Array M Nat). λ (Q : Nat). λ (B : Array Q Nat).
    λ (Hc : Π (X : Nat) → Id Nat (CountA X M A) (CountA X Q B)). λ (Hb : LbA P Q B).
      LbOfNoBelowA P M A (λ (X : Nat). λ (Hx : Le (S X) P).
        IdTrans Nat (CountA X M A) (CountA X Q B) Z (Hc X)
          (NoBelowOfLbA P Q B Hb X Hx)) }
def LbPermATy : Term := prog defer_check {
  Π (P : Nat) → Π (M : Nat) → Π (A : Array M Nat) → Π (Q : Nat) → Π (B : Array Q Nat) →
    (Π (X : Nat) → Id Nat (CountA X M A) (CountA X Q B)) → LbA P Q B → LbA P M A }

/-- Two-element count commutation over arrays — `Cons2Comm`'s transfer at the fixed
    width the miniature sort needs. Double case split on `Eqb`, all four arms `Refl`;
    the `Eqb m a = False` arm needs no inner split because both sides already agree. -/
def CountSwap2 : Term := prog defer_check {
  λ (M : Nat). λ (A : Nat). λ (B : Nat).
    elim (Eqb M A) generalizing (Id Nat (CountA M 2 Arr(B, A)) (CountA M 2 Arr(A, B))) {
      True => elim (Eqb M B) generalizing
        (Id Nat (boolRec (λ (W : Bool). Nat) (S (S Z)) (S Z) (Eqb M B))
                (S (boolRec (λ (W : Bool). Nat) (S Z) Z (Eqb M B)))) {
        True => Refl, False => Refl },
      False => Refl } }
def CountSwap2Ty : Term := prog defer_check {
  Π (M : Nat) → Π (A : Nat) → Π (B : Nat) →
    Id Nat (CountA M 2 Arr(B, A)) (CountA M 2 Arr(A, B)) }

/-! ## The PARTITION layer — the one stratum the array quicksort has to invent

    ¶6's migration ledger counts the partition as surviving the port; ledger G4 records
    that it does not (M23's is a take-and-rebuild over a linked list returning two lists
    BY VALUE; the array one is an in-place scan returning an INDEX). Its *specification*
    has to be invented too, and this is it.

    **Why positional, when ¶6 deletes the positional stratum.** A split point is a
    statement about two parts of one array, and the honest way to name them is to CARVE
    — which is exactly ¶6's claim, and it holds for the SORT, whose sub-slices are its
    own carves. It does not hold across a FUNCTION BOUNDARY. A callee cannot hand a
    segment back: the return type is fixed before the carve exists, `Array n` and
    `Array (Add k r)` convert only after the caller's own carve has refined `n`, and a
    segment cannot be returned by value either, because reading one MOVES it and leaves
    the borrow holding a hole. So the partition's interface is positional and the sort's
    internals are not — one predicate, `PartA`, and the bridge back to ¶1.3's transferred
    library is a single lemma.

    Two predicates, both `arrRec` over the cons view with the skip count threaded as an
    ordinary `Nat` argument (M22's bounded-Π encoding, which the whole-array predicates
    got to drop and these do not):

      `SplitAL p k a`  the first `k` elements are ≤ p, the rest are ≥ p
      `PartA pv k a`  the first `k` are ≤ pv, element `k` **is** pv, the rest are ≥ pv

    `PartA` is shaped so its `kz = 0` case yields `LbA` — the LIBRARY predicate, not a
    third one — which is what makes the bridge to `SortedArrCat` one lemma instead of a
    monotonicity stratum. -/

/-- Transport along a `Nat` identity — `ListRw`'s counterpart, needed to move the
    glue from the pivot VALUE the partition returned to the element sitting in the
    carved pivot slot. -/
def NatRw : Term := prog defer_check {
  λ (P : Nat → Type). λ (X : Nat). λ (Y : Nat). λ (H : Id Nat X Y). λ (Px : P X).
    j Nat X (λ (Y2 : Nat). λ (Hh : Id Nat X Y2). P Y2) Px Y H }
def NatRwTy : Term := prog defer_check {
  Π (P : Nat → Type) → Π (X : Nat) → Π (Y : Nat) → Id Nat X Y → P X → P Y }

/-- `Le n Z ⟹ n = Z`. The array quicksort tests emptiness with `Leb 1 n` rather than
    by matching `n`, because matching refines the length to `S m` and T2's rigid-extent
    restriction then blocks the three-way carve at the returned index. So the False
    branch holds `Le n Z` and has to turn it into the equation the nil lemmas want. -/
def LeZeroEq : Term := prog defer_check {
  λ (N : Nat). elim N return (λ (Z0 : Nat). Le Z0 Z → Id Nat Z0 Z) {
    Z => λ (H : Le Z Z). Refl,
    S (N2) Ih => λ (H : Bot). botElim (Id Nat (S N2) Z) H } }
def LeZeroEqTy : Term := prog defer_check { Π (N : Nat) → Le N Z → Id Nat N Z }

/-- `SortedA` of an array whose LENGTH is zero.

    Not `unit`, and that is the point: there is no η at length zero. `SortedA Z σ` is a
    stuck `arrRec` — the recursor fires on `Arr`, never on the index — so an opaque
    length-zero payload does not compute to `Unit` and the sort's base case cannot be
    discharged by the trivial term. The induction is on the ARRAY with the equation
    carried, and the cons case is dead. -/
def SortedANil : Term := prog defer_check {
  λ (N : Nat). λ (A : Array N Nat).
    arrRec Nat (λ (M : Nat). λ (B : Array M Nat). Id Nat M Z → SortedA M B)
      (λ (H : Id Nat Z Z). unit)
      (λ (K : Nat). λ (Hh : Nat). λ (T : Array K Nat).
        λ (Ih : Id Nat K Z → SortedA K T).
          λ (H : Id Nat (S K) Z).
            botElim (SortedA (S K) (acons K Hh T)) (Znots K (IdSym Nat (S K) Z H)))
      N A }
def SortedANilTy : Term := prog defer_check {
  Π (N : Nat) → Π (A : Array N Nat) → Id Nat N Z → SortedA N A }

/-- `SplitAL p k a` — the first `k` elements are ≤ `p`, the rest are ≥ `p`. -/
def SplitAL : Term := prog defer_check {
  λ (P : Nat). λ (K : Nat). λ (N : Nat). λ (A : Array N Nat).
    arrRec Nat (λ (M : Nat). λ (B : Array M Nat). Π (Kz : Nat) → Type)
      (λ (Kz : Nat). Unit)
      (λ (M : Nat). λ (H : Nat). λ (T : Array M Nat). λ (Ih : Π (Kz : Nat) → Type).
        λ (Kz : Nat).
          elim Kz return (λ (W : Nat). Type) {
            Z => Σ (Hh : Le P H). Ih Z,
            S (K2) Rec => Σ (Hh : Le H P). Ih K2 })
      N A K }

/-- `PartA pv k a` — the first `k` elements are ≤ `pv`, element `k` IS `pv`, and the
    rest are ≥ `pv`. The pivot's presence at the split point is what the sort needs and
    `SplitAL` does not give: without it the element in the carved pivot slot is merely
    ≥ `p`, and `LbA (that element)` of the right half does not follow. -/
def PartA : Term := prog defer_check {
  λ (Pv : Nat). λ (K : Nat). λ (N : Nat). λ (A : Array N Nat).
    arrRec Nat (λ (M : Nat). λ (B : Array M Nat). Π (Kz : Nat) → Type)
      (λ (Kz : Nat). Unit)
      (λ (M : Nat). λ (H : Nat). λ (T : Array M Nat). λ (Ih : Π (Kz : Nat) → Type).
        λ (Kz : Nat).
          elim Kz return (λ (W : Nat). Type) {
            Z => Σ (He : Id Nat H Pv). LbA Pv M T,
            S (K2) Rec => Σ (Hh : Le H Pv). Ih K2 })
      N A K }

/-- `SplitAL` of a length-zero array, at any skip count — `SortedANil`'s twin, and
    needed for the same reason. -/
def SplitANil : Term := prog defer_check {
  λ (P : Nat). λ (Kz : Nat). λ (N : Nat). λ (A : Array N Nat). λ (Hz : Id Nat N Z).
    arrRec Nat (λ (M : Nat). λ (B : Array M Nat).
        Π (K2 : Nat) → Id Nat M Z → SplitAL P K2 M B)
      (λ (K2 : Nat). λ (H : Id Nat Z Z). unit)
      (λ (M : Nat). λ (Hh : Nat). λ (T : Array M Nat).
        λ (Ih : Π (K2 : Nat) → Id Nat M Z → SplitAL P K2 M T).
          λ (K2 : Nat). λ (H : Id Nat (S M) Z).
            botElim (SplitAL P K2 (S M) (acons M Hh T)) (Znots M (IdSym Nat (S M) Z H)))
      N A Kz Hz }
def SplitANilTy : Term := prog defer_check {
  Π (P : Nat) → Π (Kz : Nat) → Π (N : Nat) → Π (A : Array N Nat) →
    Id Nat N Z → SplitAL P Kz N A }

/-! ### Crossing a concatenation

    Every one of these is an induction on the LEFT array and nothing else — the same
    `arrRec` shape as `BoundArrCat` and `SortedArrCat`, which is the evidence that
    this stratum, though new, is not a new KIND of work.

    The spellings are chosen to be the ones the programs actually produce, which is
    R7's lesson arriving in the pure layer: `Add k mm` where the carve decomposes, `S k`
    where a skip count runs one PAST the left part. Stating `SplitACatE1` with the
    generic `Add k t` instead of `S k` would have been more general and unusable, since
    `S k` and `Add k 1` do not convert for symbolic `k` and the program has the former. -/

/-- A zero skip count is a lower bound on the whole array — the crossing from the
    partition layer back into ¶1.3's transferred library. -/
def SplitA0Lb : Term := prog defer_check {
  λ (P : Nat). λ (N : Nat). λ (A : Array N Nat).
    arrRec Nat (λ (M : Nat). λ (B : Array M Nat). SplitAL P Z M B → LbA P M B)
      (λ (H : Unit). unit)
      (λ (K : Nat). λ (Hh : Nat). λ (T : Array K Nat).
        λ (Ih : SplitAL P Z K T → LbA P K T).
          λ (S0 : Σ (H2 : Le P Hh). SplitAL P Z K T).
            elim S0 return (λ (Qz : Σ (H2 : Le P Hh). SplitAL P Z K T). LbA P (S K) (acons K Hh T)) {
              Pair (U) (V) => Pair(U, Ih V) })
      N A }
def SplitA0LbTy : Term := prog defer_check {
  Π (P : Nat) → Π (N : Nat) → Π (A : Array N Nat) → SplitAL P Z N A → LbA P N A }

/-- Split a `SplitAL` whose skip count runs ONE PAST the left part: the left part is
    wholly bounded, and what is left is a `SplitAL` at skip 1 over the right part. This
    is the shape the swap branch needs — it reads off both "the left part is all ≤ p"
    and "the element about to be swapped out is ≤ p" in one step. -/
def SplitACatE1 : Term := prog defer_check {
  λ (P : Nat). λ (K : Nat). λ (Mm : Nat). λ (L : Array K Nat). λ (W : Array Mm Nat).
    arrRec Nat (λ (Kz : Nat). λ (Lz : Array Kz Nat).
        SplitAL P (S Kz) (Add Kz Mm) (arrCat Kz Mm Lz W) →
          Σ (Hu : UbA P Kz Lz). SplitAL P (S Z) Mm W)
      (λ (H : SplitAL P (S Z) Mm W). Pair(unit, H))
      (λ (K2 : Nat). λ (Hh : Nat). λ (T : Array K2 Nat).
        λ (Ih : SplitAL P (S K2) (Add K2 Mm) (arrCat K2 Mm T W) →
                  Σ (Hu : UbA P K2 T). SplitAL P (S Z) Mm W).
          λ (S0 : Σ (H2 : Le Hh P). SplitAL P (S K2) (Add K2 Mm) (arrCat K2 Mm T W)).
            elim S0 return (λ (Qz : Σ (H2 : Le Hh P).
                                SplitAL P (S K2) (Add K2 Mm) (arrCat K2 Mm T W)).
                Σ (Hu : UbA P (S K2) (acons K2 Hh T)). SplitAL P (S Z) Mm W) {
              Pair (U) (V) =>
                elim (Ih V) return (λ (Qz2 : Σ (Hu : UbA P K2 T). SplitAL P (S Z) Mm W).
                    Σ (Hu : UbA P (S K2) (acons K2 Hh T)). SplitAL P (S Z) Mm W) {
                  Pair (A1) (B1) => Pair(Pair(U, A1), B1) } })
      K L }
def SplitACatE1Ty : Term := prog defer_check {
  Π (P : Nat) → Π (K : Nat) → Π (Mm : Nat) → Π (L : Array K Nat) → Π (W : Array Mm Nat) →
    SplitAL P (S K) (Add K Mm) (arrCat K Mm L W) →
      Σ (Hu : UbA P K L). SplitAL P (S Z) Mm W }

/-- The converse at skip exactly `k`: a bounded left part in front of a `SplitAL` at
    skip zero is a `SplitAL` at skip `k`. -/
def SplitACatI0 : Term := prog defer_check {
  λ (P : Nat). λ (K : Nat). λ (Mm : Nat). λ (L : Array K Nat). λ (W : Array Mm Nat).
    arrRec Nat (λ (Kz : Nat). λ (Lz : Array Kz Nat).
        UbA P Kz Lz → SplitAL P Z Mm W → SplitAL P Kz (Add Kz Mm) (arrCat Kz Mm Lz W))
      (λ (U : Unit). λ (H : SplitAL P Z Mm W). H)
      (λ (K2 : Nat). λ (Hh : Nat). λ (T : Array K2 Nat).
        λ (Ih : UbA P K2 T → SplitAL P Z Mm W →
                  SplitAL P K2 (Add K2 Mm) (arrCat K2 Mm T W)).
          λ (U : Σ (H2 : Le Hh P). UbA P K2 T). λ (H : SplitAL P Z Mm W).
            elim U return (λ (Qz : Σ (H2 : Le Hh P). UbA P K2 T).
                SplitAL P (S K2) (Add (S K2) Mm) (arrCat (S K2) Mm (acons K2 Hh T) W)) {
              Pair (A1) (B1) => Pair(A1, Ih B1 H) })
      K L }
def SplitACatI0Ty : Term := prog defer_check {
  Π (P : Nat) → Π (K : Nat) → Π (Mm : Nat) → Π (L : Array K Nat) → Π (W : Array Mm Nat) →
    UbA P K L → SplitAL P Z Mm W → SplitAL P K (Add K Mm) (arrCat K Mm L W) }

/-- `PartA`'s introduction, the partition's last step: a bounded left part in front of
    a `PartA` at skip zero (which is "the head IS the pivot, the tail is ≥ it"). -/
def PartACatI0 : Term := prog defer_check {
  λ (Pv : Nat). λ (K : Nat). λ (Mm : Nat). λ (L : Array K Nat). λ (W : Array Mm Nat).
    arrRec Nat (λ (Kz : Nat). λ (Lz : Array Kz Nat).
        UbA Pv Kz Lz → PartA Pv Z Mm W → PartA Pv Kz (Add Kz Mm) (arrCat Kz Mm Lz W))
      (λ (U : Unit). λ (H : PartA Pv Z Mm W). H)
      (λ (K2 : Nat). λ (Hh : Nat). λ (T : Array K2 Nat).
        λ (Ih : UbA Pv K2 T → PartA Pv Z Mm W →
                  PartA Pv K2 (Add K2 Mm) (arrCat K2 Mm T W)).
          λ (U : Σ (H2 : Le Hh Pv). UbA Pv K2 T). λ (H : PartA Pv Z Mm W).
            elim U return (λ (Qz : Σ (H2 : Le Hh Pv). UbA Pv K2 T).
                PartA Pv (S K2) (Add (S K2) Mm) (arrCat (S K2) Mm (acons K2 Hh T) W)) {
              Pair (A1) (B1) => Pair(A1, Ih B1 H) })
      K L }
def PartACatI0Ty : Term := prog defer_check {
  Π (Pv : Nat) → Π (K : Nat) → Π (Mm : Nat) → Π (L : Array K Nat) → Π (W : Array Mm Nat) →
    UbA Pv K L → PartA Pv Z Mm W → PartA Pv K (Add K Mm) (arrCat K Mm L W) }

/-- **THE BRIDGE.** `PartA`'s elimination at the sort's own carve: the left segment is
    bounded above by the pivot, and what remains is `PartA` at skip zero over the pivot
    slot and the right segment — which unfolds, with no further lemma, to exactly
    `Id Nat (that element) pv` and `LbA pv (right segment)`. Those three facts are
    `SortedArrCat`'s four hypotheses minus the two the recursive calls supply. -/
def PartACatE0 : Term := prog defer_check {
  λ (Pv : Nat). λ (K : Nat). λ (Mm : Nat). λ (L : Array K Nat). λ (W : Array Mm Nat).
    arrRec Nat (λ (Kz : Nat). λ (Lz : Array Kz Nat).
        PartA Pv Kz (Add Kz Mm) (arrCat Kz Mm Lz W) →
          Σ (Hu : UbA Pv Kz Lz). PartA Pv Z Mm W)
      (λ (H : PartA Pv Z Mm W). Pair(unit, H))
      (λ (K2 : Nat). λ (Hh : Nat). λ (T : Array K2 Nat).
        λ (Ih : PartA Pv K2 (Add K2 Mm) (arrCat K2 Mm T W) →
                  Σ (Hu : UbA Pv K2 T). PartA Pv Z Mm W).
          λ (S0 : Σ (H2 : Le Hh Pv). PartA Pv K2 (Add K2 Mm) (arrCat K2 Mm T W)).
            elim S0 return (λ (Qz : Σ (H2 : Le Hh Pv).
                                PartA Pv K2 (Add K2 Mm) (arrCat K2 Mm T W)).
                Σ (Hu : UbA Pv (S K2) (acons K2 Hh T)). PartA Pv Z Mm W) {
              Pair (U) (V) =>
                elim (Ih V) return (λ (Qz2 : Σ (Hu : UbA Pv K2 T). PartA Pv Z Mm W).
                    Σ (Hu : UbA Pv (S K2) (acons K2 Hh T)). PartA Pv Z Mm W) {
                  Pair (A1) (B1) => Pair(Pair(U, A1), B1) } })
      K L }
def PartACatE0Ty : Term := prog defer_check {
  Π (Pv : Nat) → Π (K : Nat) → Π (Mm : Nat) → Π (L : Array K Nat) → Π (W : Array Mm Nat) →
    PartA Pv K (Add K Mm) (arrCat K Mm L W) →
      Σ (Hu : UbA Pv K L). PartA Pv Z Mm W }

/-! ### The same crossings, one conclusion each

    A body cannot conveniently destructure a Σ — a `let`-bound pure value is not
    type-checked (§23's filed checker gap), so the alternative is an inline `elim` whose
    `return` motive is the function's whole return type written out again. Splitting each
    crossing into its two conclusions moves that cost into the pure layer, where writing
    the types is free, and keeps the programs readable. -/

def SplitACatUb : Term := prog defer_check {
  λ (P : Nat). λ (K : Nat). λ (Mm : Nat). λ (L : Array K Nat). λ (W : Array Mm Nat).
    λ (S0 : SplitAL P (S K) (Add K Mm) (arrCat K Mm L W)).
      elim (SplitACatE1 P K Mm L W S0)
        return (λ (Qz : Σ (Hu : UbA P K L). SplitAL P (S Z) Mm W). UbA P K L) {
          Pair (U) (V) => U } }
def SplitACatUbTy : Term := prog defer_check {
  Π (P : Nat) → Π (K : Nat) → Π (Mm : Nat) → Π (L : Array K Nat) → Π (W : Array Mm Nat) →
    SplitAL P (S K) (Add K Mm) (arrCat K Mm L W) → UbA P K L }

def SplitACatRest : Term := prog defer_check {
  λ (P : Nat). λ (K : Nat). λ (Mm : Nat). λ (L : Array K Nat). λ (W : Array Mm Nat).
    λ (S0 : SplitAL P (S K) (Add K Mm) (arrCat K Mm L W)).
      elim (SplitACatE1 P K Mm L W S0)
        return (λ (Qz : Σ (Hu : UbA P K L). SplitAL P (S Z) Mm W). SplitAL P (S Z) Mm W) {
          Pair (U) (V) => V } }
def SplitACatRestTy : Term := prog defer_check {
  Π (P : Nat) → Π (K : Nat) → Π (Mm : Nat) → Π (L : Array K Nat) → Π (W : Array Mm Nat) →
    SplitAL P (S K) (Add K Mm) (arrCat K Mm L W) → SplitAL P (S Z) Mm W }

/-- A skip-1 `SplitAL` over a cons: its head is bounded, and its tail is a skip-0 one.
    Both are definitional unfoldings; naming them keeps the swap branch flat. -/
def SplitA1Head : Term := prog defer_check {
  λ (P : Nat). λ (R : Nat). λ (G : Array R Nat). λ (Yv : Nat).
    λ (S0 : Σ (Hh : Le Yv P). SplitAL P Z R G).
      elim S0 return (λ (Qz : Σ (Hh : Le Yv P). SplitAL P Z R G). Le Yv P) {
        Pair (U) (V) => U } }
def SplitA1HeadTy : Term := prog defer_check {
  Π (P : Nat) → Π (R : Nat) → Π (G : Array R Nat) → Π (Yv : Nat) →
    SplitAL P (S Z) (S R) (acons R Yv G) → Le Yv P }

def SplitA1Tail : Term := prog defer_check {
  λ (P : Nat). λ (R : Nat). λ (G : Array R Nat). λ (Yv : Nat).
    λ (S0 : Σ (Hh : Le Yv P). SplitAL P Z R G).
      elim S0 return (λ (Qz : Σ (Hh : Le Yv P). SplitAL P Z R G). SplitAL P Z R G) {
        Pair (U) (V) => V } }
def SplitA1TailTy : Term := prog defer_check {
  Π (P : Nat) → Π (R : Nat) → Π (G : Array R Nat) → Π (Yv : Nat) →
    SplitAL P (S Z) (S R) (acons R Yv G) → SplitAL P Z R G }

def PartACatUb : Term := prog defer_check {
  λ (Pv : Nat). λ (K : Nat). λ (Mm : Nat). λ (L : Array K Nat). λ (W : Array Mm Nat).
    λ (S0 : PartA Pv K (Add K Mm) (arrCat K Mm L W)).
      elim (PartACatE0 Pv K Mm L W S0)
        return (λ (Qz : Σ (Hu : UbA Pv K L). PartA Pv Z Mm W). UbA Pv K L) {
          Pair (U) (V) => U } }
def PartACatUbTy : Term := prog defer_check {
  Π (Pv : Nat) → Π (K : Nat) → Π (Mm : Nat) → Π (L : Array K Nat) → Π (W : Array Mm Nat) →
    PartA Pv K (Add K Mm) (arrCat K Mm L W) → UbA Pv K L }

def PartACatRest : Term := prog defer_check {
  λ (Pv : Nat). λ (K : Nat). λ (Mm : Nat). λ (L : Array K Nat). λ (W : Array Mm Nat).
    λ (S0 : PartA Pv K (Add K Mm) (arrCat K Mm L W)).
      elim (PartACatE0 Pv K Mm L W S0)
        return (λ (Qz : Σ (Hu : UbA Pv K L). PartA Pv Z Mm W). PartA Pv Z Mm W) {
          Pair (U) (V) => V } }
def PartACatRestTy : Term := prog defer_check {
  Π (Pv : Nat) → Π (K : Nat) → Π (Mm : Nat) → Π (L : Array K Nat) → Π (W : Array Mm Nat) →
    PartA Pv K (Add K Mm) (arrCat K Mm L W) → PartA Pv Z Mm W }

/-- The pivot slot, read off a skip-0 `PartA`: the element there IS the pivot, and
    everything after it is bounded below by the pivot. These two are `SortedArrCat`'s
    remaining hypotheses, and the reason `PartA` records the pivot's identity at all. -/
def PartA0Eq : Term := prog defer_check {
  λ (Pv : Nat). λ (Jj : Nat). λ (G : Array Jj Nat). λ (Ev : Nat).
    λ (S0 : Σ (He : Id Nat Ev Pv). LbA Pv Jj G).
      elim S0 return (λ (Qz : Σ (He : Id Nat Ev Pv). LbA Pv Jj G). Id Nat Ev Pv) {
        Pair (U) (V) => U } }
def PartA0EqTy : Term := prog defer_check {
  Π (Pv : Nat) → Π (Jj : Nat) → Π (G : Array Jj Nat) → Π (Ev : Nat) →
    PartA Pv Z (S Jj) (acons Jj Ev G) → Id Nat Ev Pv }

def PartA0Lb : Term := prog defer_check {
  λ (Pv : Nat). λ (Jj : Nat). λ (G : Array Jj Nat). λ (Ev : Nat).
    λ (S0 : Σ (He : Id Nat Ev Pv). LbA Pv Jj G).
      elim S0 return (λ (Qz : Σ (He : Id Nat Ev Pv). LbA Pv Jj G). LbA Pv Jj G) {
        Pair (U) (V) => V } }
def PartA0LbTy : Term := prog defer_check {
  Π (Pv : Nat) → Π (Jj : Nat) → Π (G : Array Jj Nat) → Π (Ev : Nat) →
    PartA Pv Z (S Jj) (acons Jj Ev G) → LbA Pv Jj G }

/-! ### The count layer for a swap across a carve

    The partition's one mutating step exchanges the array's head with the element at
    the split point, and those two sit in DIFFERENT segments — the whole reason the
    swap is writable at all is that each is at index 0 of its own carve (¶6's "a
    segment with its own zero"). What the permutation conjunct then owes is that the
    exchange does not move any count, over a spine four levels deep. -/

/-- `CountA`'s own step function, named so a congruence can be stated over it: the
    count of a cons is a `bump` of the count of its tail. -/
def BumpN : Term := prog defer_check {
  λ (B : Bool). λ (C : Nat). elim B return (λ (W : Bool). Nat) { True => S C, False => C } }

/-- Congruence for `CountA` under a cons — `CountConsCongr`'s array counterpart. -/
def CountAconsCongr : Term := prog defer_check {
  λ (Q : Nat). λ (H : Nat). λ (K : Nat). λ (T1 : Array K Nat). λ (T2 : Array K Nat).
    λ (Hc : Id Nat (CountA Q K T1) (CountA Q K T2)).
      IdCongr Nat Nat (λ (C : Nat). BumpN (Eqb Q H) C)
        (CountA Q K T1) (CountA Q K T2) Hc }
def CountAconsCongrTy : Term := prog defer_check {
  Π (Q : Nat) → Π (H : Nat) → Π (K : Nat) → Π (T1 : Array K Nat) → Π (T2 : Array K Nat) →
    Id Nat (CountA Q K T1) (CountA Q K T2) →
      Id Nat (CountA Q (S K) (acons K H T1)) (CountA Q (S K) (acons K H T2)) }

/-- The arithmetic core of the swap, over the two `bump`s alone: which of the two
    exchanged elements is being counted does not matter. Four arms; the two mixed ones
    are `AddSucc` and its symmetry, and the two matching ones are `Refl` — `CountSwap2`
    at width two had all four `Refl` because both counts were concrete. -/
def BumpComm : Term := prog defer_check {
  λ (B1 : Bool). λ (B2 : Bool). λ (Cl : Nat). λ (Cg : Nat).
    elim B1 return (λ (W : Bool).
        Id Nat (BumpN B2 (Add Cl (BumpN W Cg))) (BumpN W (Add Cl (BumpN B2 Cg)))) {
      True =>
        elim B2 return (λ (W2 : Bool).
            Id Nat (BumpN W2 (Add Cl (S Cg))) (S (Add Cl (BumpN W2 Cg)))) {
          True => Refl,
          False => AddSucc Cl Cg },
      False =>
        elim B2 return (λ (W2 : Bool).
            Id Nat (BumpN W2 (Add Cl Cg)) (Add Cl (BumpN W2 Cg))) {
          True => IdSym Nat (Add Cl (S Cg)) (S (Add Cl Cg)) (AddSucc Cl Cg),
          False => Refl } } }
def BumpCommTy : Term := prog defer_check {
  Π (B1 : Bool) → Π (B2 : Bool) → Π (Cl : Nat) → Π (Cg : Nat) →
    Id Nat (BumpN B2 (Add Cl (BumpN B1 Cg))) (BumpN B1 (Add Cl (BumpN B2 Cg))) }

/-- **The swap preserves every count**, stated over exactly the spine the partition
    produces: head, left segment, the swapped cell, right segment. Two `CountArrCat`
    rewrites bracket `BumpComm`. -/
def CountSwapA : Term := prog defer_check {
  λ (Q : Nat). λ (X : Nat). λ (Y : Nat). λ (K : Nat). λ (L : Array K Nat).
  λ (R : Nat). λ (G : Array R Nat).
    IdTrans Nat
      (CountA Q (S (Add K (S R))) (acons (Add K (S R)) Y (arrCat K (S R) L (acons R X G))))
      (BumpN (Eqb Q Y) (Add (CountA Q K L) (BumpN (Eqb Q X) (CountA Q R G))))
      (CountA Q (S (Add K (S R))) (acons (Add K (S R)) X (arrCat K (S R) L (acons R Y G))))
      (IdCongr Nat Nat (λ (C : Nat). BumpN (Eqb Q Y) C)
         (CountA Q (Add K (S R)) (arrCat K (S R) L (acons R X G)))
         (Add (CountA Q K L) (CountA Q (S R) (acons R X G)))
         (CountArrCat Q K L (S R) (acons R X G)))
      (IdTrans Nat
        (BumpN (Eqb Q Y) (Add (CountA Q K L) (BumpN (Eqb Q X) (CountA Q R G))))
        (BumpN (Eqb Q X) (Add (CountA Q K L) (BumpN (Eqb Q Y) (CountA Q R G))))
        (CountA Q (S (Add K (S R))) (acons (Add K (S R)) X (arrCat K (S R) L (acons R Y G))))
        (BumpComm (Eqb Q X) (Eqb Q Y) (CountA Q K L) (CountA Q R G))
        (IdSym Nat
          (CountA Q (S (Add K (S R))) (acons (Add K (S R)) X (arrCat K (S R) L (acons R Y G))))
          (BumpN (Eqb Q X) (Add (CountA Q K L) (BumpN (Eqb Q Y) (CountA Q R G))))
          (IdCongr Nat Nat (λ (C : Nat). BumpN (Eqb Q X) C)
             (CountA Q (Add K (S R)) (arrCat K (S R) L (acons R Y G)))
             (Add (CountA Q K L) (CountA Q (S R) (acons R Y G)))
             (CountArrCat Q K L (S R) (acons R Y G))))) }
def CountSwapATy : Term := prog defer_check {
  Π (Q : Nat) → Π (X : Nat) → Π (Y : Nat) → Π (K : Nat) → Π (L : Array K Nat) →
  Π (R : Nat) → Π (G : Array R Nat) →
    Id Nat (CountA Q (S (Add K (S R))) (acons (Add K (S R)) Y (arrCat K (S R) L (acons R X G))))
           (CountA Q (S (Add K (S R))) (acons (Add K (S R)) X (arrCat K (S R) L (acons R Y G)))) }

/-! ## The hashmap flagship's slot arithmetic — ported from branch `hm-probe-mod`
    (commits ad9f0822/a6a549c5), Σ arrows converted to the dot spelling.

    `Mod`/`Div` are written in the ACCUMULATOR form, and that shape is mandatory:
    the textbook `mod` — whose step tests `S (Mod a' b) = b` and then also returns
    `S (Mod a' b)` — mentions its recursive result twice, and the pure normalizer
    substitutes without sharing, so it is silently EXPONENTIAL in the dividend
    (measured on the probe: 87 s at `Mod 20 32`, days at 32). The state here is
    `(R, C)`: `R` the residue so far, `C` how many increments remain before the
    wrap, `R + C = B` the invariant; each step asks its question of `C` — an
    ARGUMENT — so `Rec` occurs exactly once and the whole thing is linear. -/

def NextR : Term := prog defer_check {
  λ (R : Nat). λ (C : Nat).
    elim C return (λ (Cz : Nat). Nat) { Z => Z, S (C2) Rc => S(R) } }
def NextC : Term := prog defer_check {
  λ (B : Nat). λ (C : Nat).
    elim C return (λ (Cz : Nat). Nat) { Z => B, S (C2) Rc => C2 } }
def NextQ : Term := prog defer_check {
  λ (Q : Nat). λ (C : Nat).
    elim C return (λ (Cz : Nat). Nat) { Z => S(Q), S (C2) Rc => Q } }

def ModC : Term := prog defer_check {
  λ (A : Nat).
    elim A return (λ (Az : Nat). Π (B : Nat) → Π (R : Nat) → Π (C : Nat) → Nat) {
      Z => λ (B : Nat). λ (R : Nat). λ (C : Nat). R,
      S (A2) Rec => λ (B : Nat). λ (R : Nat). λ (C : Nat).
        Rec B (NextR R C) (NextC B C) } }

/-- `Mod a b`, with `Mod a Z = Z` (nothing downstream divides by zero; every lemma
    is stated over `Le 1 n`). -/
def Mod : Term := prog defer_check {
  λ (A : Nat). λ (B : Nat).
    elim B return (λ (Bz : Nat). Nat) { Z => Z, S (B2) Rb => ModC A B2 Z B2 } }

def DivC : Term := prog defer_check {
  λ (A : Nat).
    elim A return (λ (Az : Nat).
        Π (B : Nat) → Π (R : Nat) → Π (C : Nat) → Π (Q : Nat) → Nat) {
      Z => λ (B : Nat). λ (R : Nat). λ (C : Nat). λ (Q : Nat). Q,
      S (A2) Rec => λ (B : Nat). λ (R : Nat). λ (C : Nat). λ (Q : Nat).
        Rec B (NextR R C) (NextC B C) (NextQ Q C) } }

def Div : Term := prog defer_check {
  λ (A : Nat). λ (B : Nat).
    elim B return (λ (Bz : Nat). Nat) { Z => Z, S (B2) Rb => DivC A B2 Z B2 Z } }

/-- One increment preserves `R + C ≤ B`: the `Z` arm is the wrap's reset to
    `(Z, B)` and the `S` arm is one `AddSucc` transport. -/
def StepInv : Term := prog defer_check {
  λ (B : Nat). λ (R : Nat). λ (C : Nat).
    elim C return (λ (Cz : Nat). Le (Add R Cz) B → Le (Add (NextR R Cz) (NextC B Cz)) B) {
      Z => λ (H : Le (Add R Z) B). LeRefl B,
      S (C2) Rc => λ (H : Le (Add R (S C2)) B).
        LeRwL B (Add R (S C2)) (S (Add R C2)) (AddSucc R C2) H } }
def StepInvTy : Term := prog defer_check {
  Π (B : Nat) → Π (R : Nat) → Π (C : Nat) →
    Le (Add R C) B → Le (Add (NextR R C) (NextC B C)) B }

def ModCLt : Term := prog defer_check {
  λ (A : Nat).
    elim A return (λ (Az : Nat).
        Π (B : Nat) → Π (R : Nat) → Π (C : Nat) →
          Le (Add R C) B → Le (S (ModC Az B R C)) (S B)) {
      Z => λ (B : Nat). λ (R : Nat). λ (C : Nat). λ (H : Le (Add R C) B).
             LeTrans R (Add R C) B (LeAdd R C) H,
      S (A2) Ih => λ (B : Nat). λ (R : Nat). λ (C : Nat). λ (H : Le (Add R C) B).
             Ih B (NextR R C) (NextC B C) (StepInv B R C H) } }
def ModCLtTy : Term := prog defer_check {
  Π (A : Nat) → Π (B : Nat) → Π (R : Nat) → Π (C : Nat) →
    Le (Add R C) B → Le (S (ModC A B R C)) (S B) }

/-- The slot index is below the capacity — in the form a PROGRAM can use: the
    capacity is an opaque `n` carrying `Le 1 n`, not the pattern `S c`, because
    the carve's premise (3) refines a σ and `S c` is rigid. -/
def ModLtN : Term := prog defer_check {
  λ (A : Nat). λ (N : Nat).
    elim N return (λ (Nz : Nat). Le (S Z) Nz → Le (S (Mod A Nz)) Nz) {
      Z => λ (H : Le (S Z) Z). botElim (Le (S (Mod A Z)) Z) H,
      S (B2) Rb => λ (H : Le (S Z) (S B2)). ModCLt A B2 Z B2 (LeRefl B2) } }
def ModLtNTy : Term := prog defer_check {
  Π (A : Nat) → Π (N : Nat) → Le (S Z) N → Le (S (Mod A N)) N }

/-- Minting the carve's decomposition: `i < n` becomes the residue and the
    equation premise (3) wants CITED. The Σ must cross a CALL boundary to be
    usable (comptime projections mention `n` and fail the occurs check). -/
def ModDec : Term := prog defer_check {
  λ (I : Nat).
    elim I return (λ (Iz : Nat).
        Π (N : Nat) → Le (S Iz) N → Σ (R : Nat). Id Nat N (Add Iz (S R))) {
      Z => λ (N : Nat).
        elim N return (λ (Nz : Nat). Le (S Z) Nz → Σ (R : Nat). Id Nat Nz (Add Z (S R))) {
          Z => λ (H : Le (S Z) Z). botElim (Σ (R : Nat). Id Nat Z (Add Z (S R))) H,
          S (N2) Ihn => λ (H : Le (S Z) (S N2)). Pair(N2, Refl) },
      S (I2) Ih => λ (N : Nat).
        elim N return (λ (Nz : Nat).
            Le (S (S I2)) Nz → Σ (R : Nat). Id Nat Nz (Add (S I2) (S R))) {
          Z => λ (H : Le (S (S I2)) Z). botElim (Σ (R : Nat). Id Nat Z (Add (S I2) (S R))) H,
          S (N2) Ihn => λ (H : Le (S (S I2)) (S N2)).
            elim (Ih N2 H) return (λ (Q : Σ (R : Nat). Id Nat N2 (Add I2 (S R))).
                Σ (R : Nat). Id Nat (S N2) (Add (S I2) (S R))) {
              Pair (X) (Y) =>
                Pair(X, IdCongr Nat Nat (λ (Nn : Nat). S Nn) N2 (Add I2 (S X)) Y) } } } }
def ModDecTy : Term := prog defer_check {
  Π (I : Nat) → Π (N : Nat) → Le (S I) N → Σ (R : Nat). Id Nat N (Add I (S R)) }

/-! ## Multiplication, and the load-ledger arithmetic

    The hashmap's 4/5 load factor is carried Div-free: `n ≤ ⌊4·cap/5⌋` is, for
    integers, exactly `5·n ≤ 4·cap`, and "n exceeds the threshold" is exactly
    `5·n > 4·cap` — so the packed ledger stores `Mul 4 cap` and compares against
    `Mul 5 n`, and no floor-division lemma library is needed. `LedgerGrow` is the
    one fact resize owes: a map at the threshold that takes one more entry fits
    under the DOUBLED capacity's threshold. -/

def Mul : Term := prog defer_check {
  λ (A : Nat). λ (B : Nat). elim A return (λ (Az : Nat). Nat) {
    Z => Z, S (A2) Rec => Add B Rec } }

def AddSwapL : Term := prog defer_check {
  λ (A : Nat). λ (B : Nat). λ (C : Nat).
    elim A return (λ (Az : Nat). Id Nat (Add Az (Add B C)) (Add B (Add Az C))) {
      Z => Refl,
      S (A2) Ih =>
        IdTrans Nat (S (Add A2 (Add B C))) (S (Add B (Add A2 C))) (Add B (S (Add A2 C)))
          (IdCongr Nat Nat (λ (X : Nat). S X) (Add A2 (Add B C)) (Add B (Add A2 C)) Ih)
          (IdSym Nat (Add B (S (Add A2 C))) (S (Add B (Add A2 C))) (AddSucc B (Add A2 C))) } }
def AddSwapLTy : Term := prog defer_check {
  Π (A : Nat) → Π (B : Nat) → Π (C : Nat) →
    Id Nat (Add A (Add B C)) (Add B (Add A C)) }

def AddInterchange : Term := prog defer_check {
  λ (A : Nat). λ (B : Nat). λ (C : Nat). λ (D : Nat).
    IdTrans Nat (Add (Add A B) (Add C D)) (Add A (Add B (Add C D))) (Add (Add A C) (Add B D))
      (AddAssoc A B (Add C D))
      (IdTrans Nat (Add A (Add B (Add C D))) (Add A (Add C (Add B D))) (Add (Add A C) (Add B D))
        (IdCongr Nat Nat (λ (X : Nat). Add A X) (Add B (Add C D)) (Add C (Add B D))
          (AddSwapL B C D))
        (IdSym Nat (Add (Add A C) (Add B D)) (Add A (Add C (Add B D)))
          (AddAssoc A C (Add B D)))) }
def AddInterchangeTy : Term := prog defer_check {
  Π (A : Nat) → Π (B : Nat) → Π (C : Nat) → Π (D : Nat) →
    Id Nat (Add (Add A B) (Add C D)) (Add (Add A C) (Add B D)) }

def MulSucc : Term := prog defer_check {
  λ (A : Nat). λ (B : Nat).
    elim A return (λ (Az : Nat). Id Nat (Mul Az (S B)) (Add Az (Mul Az B))) {
      Z => Refl,
      S (A2) Ih =>
        IdCongr Nat Nat (λ (X : Nat). S X)
          (Add B (Mul A2 (S B))) (Add A2 (Add B (Mul A2 B)))
          (IdTrans Nat (Add B (Mul A2 (S B))) (Add B (Add A2 (Mul A2 B)))
            (Add A2 (Add B (Mul A2 B)))
            (IdCongr Nat Nat (λ (X : Nat). Add B X) (Mul A2 (S B)) (Add A2 (Mul A2 B)) Ih)
            (AddSwapL B A2 (Mul A2 B))) } }
def MulSuccTy : Term := prog defer_check {
  Π (A : Nat) → Π (B : Nat) → Id Nat (Mul A (S B)) (Add A (Mul A B)) }

def MulAddR : Term := prog defer_check {
  λ (A : Nat). λ (B : Nat). λ (C : Nat).
    elim A return (λ (Az : Nat).
        Id Nat (Mul Az (Add B C)) (Add (Mul Az B) (Mul Az C))) {
      Z => Refl,
      S (A2) Ih =>
        IdTrans Nat (Add (Add B C) (Mul A2 (Add B C)))
          (Add (Add B C) (Add (Mul A2 B) (Mul A2 C)))
          (Add (Add B (Mul A2 B)) (Add C (Mul A2 C)))
          (IdCongr Nat Nat (λ (X : Nat). Add (Add B C) X)
            (Mul A2 (Add B C)) (Add (Mul A2 B) (Mul A2 C)) Ih)
          (AddInterchange B C (Mul A2 B) (Mul A2 C)) } }
def MulAddRTy : Term := prog defer_check {
  Π (A : Nat) → Π (B : Nat) → Π (C : Nat) →
    Id Nat (Mul A (Add B C)) (Add (Mul A B) (Mul A C)) }

def MulTwoDouble : Term := prog defer_check {
  λ (A : Nat). λ (C : Nat).
    IdTrans Nat (Mul A (Mul 2 C)) (Mul A (Add C C)) (Add (Mul A C) (Mul A C))
      (IdCongr Nat Nat (λ (X : Nat). Mul A (Add C X)) (Add C Z) C (AddZero C))
      (MulAddR A C C) }
def MulTwoDoubleTy : Term := prog defer_check {
  Π (A : Nat) → Π (C : Nat) → Id Nat (Mul A (Mul 2 C)) (Add (Mul A C) (Mul A C)) }

def LeAddMonoR : Term := prog defer_check {
  λ (A : Nat). λ (B : Nat). λ (K : Nat). λ (H : Le A B).
    LeRwR (Add A K) (Add K B) (Add B K) (AddComm K B)
      (LeRwL (Add K B) (Add K A) (Add A K) (AddComm K A) (LeAddMonoL K A B H)) }
def LeAddMonoRTy : Term := prog defer_check {
  Π (A : Nat) → Π (B : Nat) → Π (K : Nat) → Le A B → Le (Add A K) (Add B K) }

def LeAddMono : Term := prog defer_check {
  λ (A : Nat). λ (B : Nat). λ (C : Nat). λ (D : Nat). λ (H1 : Le A B). λ (H2 : Le C D).
    LeTrans (Add A C) (Add B C) (Add B D) (LeAddMonoR A B C H1) (LeAddMonoL B C D H2) }
def LeAddMonoTy : Term := prog defer_check {
  Π (A : Nat) → Π (B : Nat) → Π (C : Nat) → Π (D : Nat) →
    Le A B → Le C D → Le (Add A C) (Add B D) }

def LeMulR : Term := prog defer_check {
  λ (A : Nat). λ (B : Nat). λ (C : Nat). λ (H : Le B C).
    elim A return (λ (Az : Nat). Le (Mul Az B) (Mul Az C)) {
      Z => unit,
      S (A2) Ih => LeAddMono B C (Mul A2 B) (Mul A2 C) H Ih } }
def LeMulRTy : Term := prog defer_check {
  Π (A : Nat) → Π (B : Nat) → Π (C : Nat) → Le B C → Le (Mul A B) (Mul A C) }

def Le5M4 : Term := prog defer_check {
  λ (C : Nat). λ (H : Le 2 C).
    LeTrans 5 (Mul 4 2) (Mul 4 C) unit (LeMulR 4 2 C H) }
def Le5M4Ty : Term := prog defer_check { Π (C : Nat) → Le 2 C → Le 5 (Mul 4 C) }

/-- Integrality at the one capacity the ≤-chain misses: `5n ≤ 4` forces `n = 0`. -/
def FiveN4Zero : Term := prog defer_check {
  λ (N : Nat). elim N return (λ (Nz : Nat). Le (Mul 5 Nz) 4 → Id Nat Nz Z) {
    Z => λ (H : Le (Mul 5 Z) 4). Refl,
    S (N2) Ih => λ (H : Le (Mul 5 (S N2)) 4).
      botElim (Id Nat (S N2) Z)
        (LeRwL 4 (Mul 5 (S N2)) (Add 5 (Mul 5 N2)) (MulSucc 5 N2) H) } }
def FiveN4ZeroTy : Term := prog defer_check { Π (N : Nat) → Le (Mul 5 N) 4 → Id Nat N Z }

/-- The converse reflection to `LebTrueLe`: an established order closes the test. -/
def LeLebTrue : Term := prog defer_check {
  λ (A : Nat). elim A return (λ (Az : Nat). Π (B : Nat) → Le Az B → Id Bool (Leb Az B) True) {
    Z => λ (B : Nat). λ (H : Le Z B). Refl,
    S (A2) Ih => λ (B : Nat).
      elim B return (λ (Bz : Nat). Le (S A2) Bz → Id Bool (Leb (S A2) Bz) True) {
        Z => λ (H : Le (S A2) Z). botElim (Id Bool (Leb (S A2) Z) True) H,
        S (B2) Ihb => λ (H : Le (S A2) (S B2)). Ih B2 H } } }
def LeLebTrueTy : Term := prog defer_check {
  Π (A : Nat) → Π (B : Nat) → Le A B → Id Bool (Leb A B) True }

/-- `Eqb`'s soundness at symbolic arguments — the lemma every hashmap key test
    converts through. -/
def EqbTrueEq : Term := prog defer_check {
  λ (A : Nat). elim A return (λ (Az : Nat).
      Π (B : Nat) → Id Bool (Eqb Az B) True → Id Nat Az B) {
    Z => λ (B : Nat). elim B return (λ (Bz : Nat). Id Bool (Eqb Z Bz) True → Id Nat Z Bz) {
      Z => λ (H : Id Bool (Eqb Z Z) True). Refl,
      S (B2) Ihb => λ (H : Id Bool (Eqb Z (S B2)) True).
        botElim (Id Nat Z (S B2)) (BoolFT H) },
    S (A2) Ih => λ (B : Nat).
      elim B return (λ (Bz : Nat). Id Bool (Eqb (S A2) Bz) True → Id Nat (S A2) Bz) {
        Z => λ (H : Id Bool (Eqb (S A2) Z) True). botElim (Id Nat (S A2) Z) (BoolFT H),
        S (B2) Ihb => λ (H : Id Bool (Eqb (S A2) (S B2)) True).
          IdCongr Nat Nat (λ (X : Nat). S X) A2 B2 (Ih B2 H) } } }
def EqbTrueEqTy : Term := prog defer_check {
  Π (A : Nat) → Π (B : Nat) → Id Bool (Eqb A B) True → Id Nat A B }

def EqbSym : Term := prog defer_check {
  λ (A : Nat). elim A return (λ (Az : Nat). Π (B : Nat) → Id Bool (Eqb Az B) (Eqb B Az)) {
    Z => λ (B : Nat). elim B return (λ (Bz : Nat). Id Bool (Eqb Z Bz) (Eqb Bz Z)) {
      Z => Refl, S (B2) Ihb => Refl },
    S (A2) Ih => λ (B : Nat).
      elim B return (λ (Bz : Nat). Id Bool (Eqb (S A2) Bz) (Eqb Bz (S A2))) {
        Z => Refl, S (B2) Ihb => Ih B2 } } }
def EqbSymTy : Term := prog defer_check {
  Π (A : Nat) → Π (B : Nat) → Id Bool (Eqb A B) (Eqb B A) }

/-- The pure fragment's `if e : …`: case on a stuck Bool, each branch receiving
    the equation it teaches. The workhorse of every pointwise-Find proof. -/
def IfDec : Term := prog defer_check {
  λ (B : Bool). λ (T : Type).
    λ (F : Id Bool B True → T). λ (G : Id Bool B False → T).
      boolRec (λ (Bm : Bool). (Id Bool Bm True → T) → ((Id Bool Bm False → T) → T))
        (λ (F2 : Id Bool True True → T). λ (G2 : Id Bool True False → T). F2 Refl)
        (λ (F2 : Id Bool False True → T). λ (G2 : Id Bool False False → T). G2 Refl)
        B F G }
def IfDecTy : Term := prog defer_check {
  Π (B : Bool) → Π (T : Type) →
    (Id Bool B True → T) → (Id Bool B False → T) → T }

/-- THE RESIZE LEDGER FACT: at the threshold, one more entry fits under the
    doubled capacity. The `Leb 2 C` split exists because the ≤-chain
    `4c + 5 ≤ 8c` needs `c ≥ 2`, and `c = 1` closes by integrality instead
    (`5n ≤ 4` forces `n = 0`, and `5 ≤ 8` computes). -/
def LedgerGrow : Term := prog defer_check {
  λ (C : Nat). λ (N : Nat). λ (H1 : Le (S Z) C). λ (Hle : Le (Mul 5 N) (Mul 4 C)).
    IfDec (Leb 2 C) (Le (Mul 5 (S N)) (Mul 4 (Mul 2 C)))
      (λ (E : Id Bool (Leb 2 C) True).
        LeRwL (Mul 4 (Mul 2 C)) (Add 5 (Mul 5 N)) (Mul 5 (S N))
          (IdSym Nat (Mul 5 (S N)) (Add 5 (Mul 5 N)) (MulSucc 5 N))
          (LeRwR (Add 5 (Mul 5 N)) (Add (Mul 4 C) (Mul 4 C)) (Mul 4 (Mul 2 C))
            (IdSym Nat (Mul 4 (Mul 2 C)) (Add (Mul 4 C) (Mul 4 C)) (MulTwoDouble 4 C))
            (LeAddMono 5 (Mul 4 C) (Mul 5 N) (Mul 4 C)
              (Le5M4 C (LebTrueLe 2 C E)) Hle)))
      (λ (E : Id Bool (Leb 2 C) False).
        NatRw (λ (Cz : Nat). Le (Mul 5 N) (Mul 4 Cz) → Le (Mul 5 (S N)) (Mul 4 (Mul 2 Cz)))
          (S Z) C
          (IdSym Nat C (S Z) (LeAntisym C (S Z) (LebFalseGt 2 C E) H1))
          (λ (Hle1 : Le (Mul 5 N) (Mul 4 (S Z))).
            NatRw (λ (Nz : Nat). Le (Mul 5 (S Nz)) (Mul 4 (Mul 2 (S Z)))) Z N
              (IdSym Nat N Z (FiveN4Zero N Hle1)) unit)
          Hle) }
def LedgerGrowTy : Term := prog defer_check {
  Π (C : Nat) → Π (N : Nat) → Le (S Z) C → Le (Mul 5 N) (Mul 4 C) →
    Le (Mul 5 (S N)) (Mul 4 (Mul 2 C)) }


/-! ## The library typechecks

    Every entry above that states a type (X paired with XTy) is checked here
    against that type. These definitions are raw terms (defer_check), so Lean
    compiling them proves nothing; programs cite them by their stated types,
    and this battery is what makes that trust sound. -/

/-- Type-check a closed term against a closed type in the pure seed. -/
def chkLib (tm ty : Term) : Bool :=
  match (do let v ← readC 8000 tm; let t ← readC 8000 ty; hasTypeT 8000 v t).run (seedPure [] []) with
  | .ok r _ => r
  | .error _ _ => false

example : chkLib AddAssoc AddAssocTy = true := by native_decide
example : chkLib AddComm AddCommTy = true := by native_decide
example : chkLib AddInterchange AddInterchangeTy = true := by native_decide
example : chkLib AddSubCancel AddSubCancelTy = true := by native_decide
example : chkLib AddSucc AddSuccTy = true := by native_decide
example : chkLib AddSwapL AddSwapLTy = true := by native_decide
example : chkLib AddZero AddZeroTy = true := by native_decide
example : chkLib BoolFT BoolFTTy = true := by native_decide
example : chkLib BoolTF BoolTFTy = true := by native_decide
example : chkLib BoundAppend BoundAppendTy = true := by native_decide
example : chkLib BoundArrCat BoundArrCatTy = true := by native_decide
example : chkLib BumpComm BumpCommTy = true := by native_decide
example : chkLib CountAconsCongr CountAconsCongrTy = true := by native_decide
example : chkLib CountAconsHit CountAconsHitTy = true := by native_decide
example : chkLib CountAconsMiss CountAconsMissTy = true := by native_decide
example : chkLib CountAppend CountAppendTy = true := by native_decide
example : chkLib CountArrCat CountArrCatTy = true := by native_decide
example : chkLib CountConsCongr CountConsCongrTy = true := by native_decide
example : chkLib CountConsHit CountConsHitTy = true := by native_decide
example : chkLib CountConsL CountConsLTy = true := by native_decide
example : chkLib CountConsMiss CountConsMissTy = true := by native_decide
example : chkLib CountConsR CountConsRTy = true := by native_decide
example : chkLib CountSwap2 CountSwap2Ty = true := by native_decide
example : chkLib CountSwapA CountSwapATy = true := by native_decide
example : chkLib EqbGtFalse EqbGtFalseTy = true := by native_decide
example : chkLib EqbLtFalse EqbLtFalseTy = true := by native_decide
example : chkLib EqbRefl EqbReflTy = true := by native_decide
example : chkLib EqbSym EqbSymTy = true := by native_decide
example : chkLib EqbTrueEq EqbTrueEqTy = true := by native_decide
example : chkLib FiveN4Zero FiveN4ZeroTy = true := by native_decide
example : chkLib IdCongr IdCongrTy = true := by native_decide
example : chkLib IdSym IdSymTy = true := by native_decide
example : chkLib IdTrans IdTransTy = true := by native_decide
example : chkLib IfDec IfDecTy = true := by native_decide
example : chkLib LbBound LbBoundTy = true := by native_decide
example : chkLib LbBoundA LbBoundATy = true := by native_decide
example : chkLib LbHead LbHeadTy = true := by native_decide
example : chkLib LbOfNoBelow LbOfNoBelowTy = true := by native_decide
example : chkLib LbOfNoBelowA LbOfNoBelowATy = true := by native_decide
example : chkLib LbPerm LbPermTy = true := by native_decide
example : chkLib LbPermA LbPermATy = true := by native_decide
example : chkLib LbTail LbTailTy = true := by native_decide
example : chkLib Le5M4 Le5M4Ty = true := by native_decide
example : chkLib LeAdd LeAddTy = true := by native_decide
example : chkLib LeAddL LeAddLTy = true := by native_decide
example : chkLib LeAddMono LeAddMonoTy = true := by native_decide
example : chkLib LeAddMonoL LeAddMonoLTy = true := by native_decide
example : chkLib LeAddMonoR LeAddMonoRTy = true := by native_decide
example : chkLib LeAddSucc LeAddSuccTy = true := by native_decide
example : chkLib LeAntisym LeAntisymTy = true := by native_decide
example : chkLib LeLebTrue LeLebTrueTy = true := by native_decide
example : chkLib LeMulR LeMulRTy = true := by native_decide
example : chkLib LePredL LePredLTy = true := by native_decide
example : chkLib LeRefl LeReflTy = true := by native_decide
example : chkLib LeRwL LeRwLTy = true := by native_decide
example : chkLib LeRwR LeRwRTy = true := by native_decide
example : chkLib LeTrans LeTransTy = true := by native_decide
example : chkLib LeUpR LeUpRTy = true := by native_decide
example : chkLib LeZeroEq LeZeroEqTy = true := by native_decide
example : chkLib LebFalseGt LebFalseGtTy = true := by native_decide
example : chkLib LebTrueLe LebTrueLeTy = true := by native_decide
example : chkLib LedgerGrow LedgerGrowTy = true := by native_decide
example : chkLib LenSet LenSetTy = true := by native_decide
example : chkLib LenSwapL LenSwapLTy = true := by native_decide
example : chkLib ListRw ListRwTy = true := by native_decide
example : chkLib ModCLt ModCLtTy = true := by native_decide
example : chkLib ModDec ModDecTy = true := by native_decide
example : chkLib ModLtN ModLtNTy = true := by native_decide
example : chkLib MulAddR MulAddRTy = true := by native_decide
example : chkLib MulSucc MulSuccTy = true := by native_decide
example : chkLib MulTwoDouble MulTwoDoubleTy = true := by native_decide
example : chkLib NatRw NatRwTy = true := by native_decide
example : chkLib NoAboveOfUb NoAboveOfUbTy = true := by native_decide
example : chkLib NoAboveOfUbA NoAboveOfUbATy = true := by native_decide
example : chkLib NoBelowOfLb NoBelowOfLbTy = true := by native_decide
example : chkLib NoBelowOfLbA NoBelowOfLbATy = true := by native_decide
example : chkLib PartA0Eq PartA0EqTy = true := by native_decide
example : chkLib PartA0Lb PartA0LbTy = true := by native_decide
example : chkLib PartACatE0 PartACatE0Ty = true := by native_decide
example : chkLib PartACatI0 PartACatI0Ty = true := by native_decide
example : chkLib PartACatRest PartACatRestTy = true := by native_decide
example : chkLib PartACatUb PartACatUbTy = true := by native_decide
example : chkLib SInj SInjTy = true := by native_decide
example : chkLib SortedANil SortedANilTy = true := by native_decide
example : chkLib SortedAppendPivot SortedAppendPivotTy = true := by native_decide
example : chkLib SortedArrCat SortedArrCatTy = true := by native_decide
example : chkLib SortedHead SortedHeadTy = true := by native_decide
example : chkLib SortedHeadA SortedHeadATy = true := by native_decide
example : chkLib SortedTail SortedTailTy = true := by native_decide
example : chkLib SortedTailA SortedTailATy = true := by native_decide
example : chkLib SplitA0Lb SplitA0LbTy = true := by native_decide
example : chkLib SplitA1Head SplitA1HeadTy = true := by native_decide
example : chkLib SplitA1Tail SplitA1TailTy = true := by native_decide
example : chkLib SplitACatE1 SplitACatE1Ty = true := by native_decide
example : chkLib SplitACatI0 SplitACatI0Ty = true := by native_decide
example : chkLib SplitACatRest SplitACatRestTy = true := by native_decide
example : chkLib SplitACatUb SplitACatUbTy = true := by native_decide
example : chkLib SplitANil SplitANilTy = true := by native_decide
example : chkLib StepInv StepInvTy = true := by native_decide
example : chkLib Sub SubTy = true := by native_decide
example : chkLib SwapLSet SwapLSetTy = true := by native_decide
example : chkLib UbHead UbHeadTy = true := by native_decide
example : chkLib UbHeadA UbHeadATy = true := by native_decide
example : chkLib UbOfNoAbove UbOfNoAboveTy = true := by native_decide
example : chkLib UbOfNoAboveA UbOfNoAboveATy = true := by native_decide
example : chkLib UbPerm UbPermTy = true := by native_decide
example : chkLib UbPermA UbPermATy = true := by native_decide
example : chkLib UbTail UbTailTy = true := by native_decide
example : chkLib UbTailA UbTailATy = true := by native_decide
example : chkLib Znots ZnotsTy = true := by native_decide

end Dllbc.StdLemmas

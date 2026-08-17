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

def LeRefl : Term := prog{
  λ (N : Nat). elim N return (λ (M : Nat). Le M M) {
    Z => unit,
    S (K) Ih => Ih } }
def LeReflTy : Term := prog{ Π (N : Nat) → Le N N }

-- The wall. Single outer elim on `a`; the `S` case elims on `b`, whose `S` case
-- elims on `c`, with the IH applied at the peeled proofs — every step
-- definitional through the `Le` equations. Nested, but every binder is NAMED and
-- every motive is written once and visible.
def LeTrans : Term := prog{
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
def LeTransTy : Term := prog{
  Π (A : Nat) → Π (B : Nat) → Π (C : Nat) → Le A B → Le B C → Le A C }

-- Right-successor monotonicity: `a ≤ b ⟹ a ≤ S b`. Double induction (on `a`,
-- casing `b`): the `Z` head is trivial (`Le Z _ = ⊤`); the `S a'` head cases `b`
-- (`Le (S a') Z = ⊥`, else `Le a' b'` and the IH lifts it to `Le a' (S b')`).
-- The glue `CountSwapL'` needs to bend swapS's `Le (S i) j` into count_swapL's
-- `Le (S i) (Len l)` via one `LeTrans`.
def LeUpR : Term := prog{
  λ (A : Nat). elim A return (λ (Az : Nat). Π (B : Nat) → Le Az B → Le Az (S B)) {
    Z => λ (B : Nat). λ (H : Le Z B). unit,
    S (A') Ih => λ (B : Nat). λ (H : Le (S A') B).
      elim B return (λ (Bz : Nat). Le (S A') Bz → Le (S A') (S Bz)) {
        Z => λ (H0 : Le (S A') Z). botElim (Le (S A') (S Z)) H0,
        S (B') Ihb => λ (H0 : Le (S A') (S B')). Ih B' H0
      } H } }
def LeUpRTy : Term := prog{ Π (A : Nat) → Π (B : Nat) → Le A B → Le A (S B) }

-- `i ≤ i + g`: the boundary never passes the scan position it feeds. A clean
-- induction on `i` (`Add (S i') g = S (Add i' g)`, so `Le (S i') (Add (S i') g)`
-- reduces to the IH). The partition swaps consume this as their `pij`.
def LeAdd : Term := prog{
  λ (I : Nat). elim I return (λ (Iz : Nat). Π (G : Nat) → Le Iz (Add Iz G)) {
    Z => λ (G : Nat). unit,
    S (I') Ih => λ (G : Nat). Ih G } }
def LeAddTy : Term := prog{ Π (I : Nat) → Π (G : Nat) → Le I (Add I G) }

-- `b ≤ a + b` — the companion where the summand is on the LEFT (`LeAdd` has it on
-- the right). Induction on `a`: base is `LeRefl` (`Add Z b = b`), step lifts the
-- IH with `LeUpR` (`Add (S a') b = S (Add a' b)`). The scan-position bound uses
-- this because the length equation carries the remaining count `k` on the left.
def LeAddL : Term := prog{
  λ (B : Nat). λ (A : Nat).
    elim A return (λ (Az : Nat). Le B (Add Az B)) {
      Z => LeRefl B,
      S (A') Ih => LeUpR B (Add A' B) Ih } }
def LeAddLTy : Term := prog{ Π (B : Nat) → Π (A : Nat) → Le B (Add A B) }

-- `S i ≤ i + (S g)` — the swap's `pij`: the boundary `S i` is below the scan
-- position `S (Add i (S g))` whenever the gap is non-empty. Induction on `i`
-- avoids an AddSucc transport (`Add (S i') x = S (Add i' x)` is definitional),
-- so no rewrite is needed here.
def LeAddSucc : Term := prog{
  λ (I : Nat). elim I return (λ (Iz : Nat). Π (G : Nat) → Le (S Iz) (Add Iz (S G))) {
    Z => λ (G : Nat). unit,
    S (I') Ih => λ (G : Nat). Ih G } }
def LeAddSuccTy : Term := prog{ Π (I : Nat) → Π (G : Nat) → Le (S I) (Add I (S G)) }

-- Transport a `Le` along an `Id` on its SECOND argument: `x = y ⟹ Le a x → Le a
-- y`. The bounds derived over the arithmetic normal form are moved onto `len *v`
-- (and back through `LenSwapL`) with this J-transport — the "LeTrans/le_step
-- glue where descent is not definitional".
def LeRwR : Term := prog{
  λ (A : Nat). λ (X : Nat). λ (Y : Nat). λ (H : Id Nat X Y). λ (P : Le A X).
    j Nat X (λ (Y' : Nat). λ (Hh : Id Nat X Y'). Le A Y') P Y H }
def LeRwRTy : Term := prog{ Π (A : Nat) → Π (X : Nat) → Π (Y : Nat) → Id Nat X Y → Le A X → Le A Y }

-- Transport a `Le` along an `Id` on its FIRST (smaller) argument: `x = y ⟹ Le x
-- b → Le y b`. The range partition's bound `Le (add lo (S (add k (add i g))))
-- (len *v)` is invariant across the recursion (the sum k+i+g is preserved), but
-- its SYNTACTIC form shifts as k descends and i/g grow; this moves the bound
-- between forms via the hshift identities — the Le mirror of LeRwR, and the one
-- lemma the M20 Id-toolkit lacked for the subrange generalization (§21).
def LeRwL : Term := prog{
  λ (B : Nat). λ (X : Nat). λ (Y : Nat). λ (H : Id Nat X Y). λ (P : Le X B).
    j Nat X (λ (Y' : Nat). λ (Hh : Id Nat X Y'). Le Y' B) P Y H }
def LeRwLTy : Term := prog{ Π (B : Nat) → Π (X : Nat) → Π (Y : Nat) → Id Nat X Y → Le X B → Le Y B }

-- Left-add monotonicity: `a ≤ b ⟹ lo + a ≤ lo + b`. Induction on `lo`: base is
-- the hypothesis (`Add Z x = x`), step is the IH verbatim (`add (S lo') x =
-- S (add lo' x)` and `Le (S _) (S _) = Le _ _` are both definitional). The range
-- partition's swap bounds shift the entry bound `Le (S i) (S (Add i g))` through
-- `Add lo` to reach `Le (Add lo (S i)) (Add lo (S (Add i g)))` (§21).
def LeAddMonoL : Term := prog{
  λ (Lo : Nat). λ (A : Nat). λ (B : Nat). λ (H : Le A B).
    elim Lo return (λ (Loz : Nat). Le (Add Loz A) (Add Loz B)) {
      Z => H,
      S (Lo') Ih => Ih } }
def LeAddMonoLTy : Term := prog{ Π (Lo : Nat) → Π (A : Nat) → Π (B : Nat) → Le A B → Le (Add Lo A) (Add Lo B) }

/-! ## `IdTrans`, `IdCongr` — the J warm-ups partition's count-chaining consumes -/

def IdTrans : Term := prog{
  λ (A : Type). λ (X : A). λ (Y : A). λ (Z0 : A). λ (P : Id A X Y). λ (Q : Id A Y Z0).
    j A X (λ (Y' : A). λ (H : Id A X Y'). Id A Y' Z0 → Id A X Z0) (λ (H : Id A X Z0). H) Y P Q }
def IdTransTy : Term := prog{
  Π (A : Type) → Π (X : A) → Π (Y : A) → Π (Z0 : A) → Id A X Y → Id A Y Z0 → Id A X Z0 }

def IdCongr : Term := prog{
  λ (A : Type). λ (B : Type). λ (F : A → B). λ (X : A). λ (Y : A). λ (P : Id A X Y).
    j A X (λ (Y' : A). λ (H : Id A X Y'). Id B (F X) (F Y')) Refl Y P }
def IdCongrTy : Term := prog{
  Π (A : Type) → Π (B : Type) → Π (F : A → B) → Π (X : A) → Π (Y : A) → Id A X Y → Id B (F X) (F Y) }

def IdSym : Term := prog{
  λ (A : Type). λ (X : A). λ (Y : A). λ (P : Id A X Y).
    j A X (λ (Y' : A). λ (H : Id A X Y'). Id A Y' X) Refl Y P }
def IdSymTy : Term := prog{ Π (A : Type) → Π (X : A) → Π (Y : A) → Id A X Y → Id A Y X }

/-! ## Arithmetic — the first double-inductions after the wall (§16 calibration) -/

def AddZero : Term := prog{
  λ (A : Nat). elim A return (λ (X : Nat). Id Nat (Add X Z) X) {
    Z => Refl,
    S (A') Ih => IdCongr Nat Nat (λ (N : Nat). S N) (Add A' Z) A' Ih } }
def AddZeroTy : Term := prog{ Π (A : Nat) → Id Nat (Add A Z) A }

def AddSucc : Term := prog{
  λ (A : Nat). λ (B : Nat). elim A return (λ (X : Nat). Id Nat (Add X (S B)) (S (Add X B))) {
    Z => Refl,
    S (A') Ih => IdCongr Nat Nat (λ (N : Nat). S N) (Add A' (S B)) (S (Add A' B)) Ih } }
def AddSuccTy : Term := prog{ Π (A : Nat) → Π (B : Nat) → Id Nat (Add A (S B)) (S (Add A B)) }

-- Commutativity: the classic proof, authored in the surface and checked first try.
def AddComm : Term := prog{
  λ (A : Nat). elim A return (λ (X : Nat). Π (B : Nat) → Id Nat (Add X B) (Add B X)) {
    Z => λ (B : Nat). IdSym Nat (Add B Z) B (AddZero B),
    S (A') Ih => λ (B : Nat).
      IdTrans Nat (S (Add A' B)) (S (Add B A')) (Add B (S A'))
        (IdCongr Nat Nat (λ (N : Nat). S N) (Add A' B) (Add B A') (Ih B))
        (IdSym Nat (Add B (S A')) (S (Add B A')) (AddSucc B A')) } }
def AddCommTy : Term := prog{ Π (A : Nat) → Π (B : Nat) → Id Nat (Add A B) (Add B A) }

def AddAssoc : Term := prog{
  λ (A : Nat). elim A return (λ (X : Nat). Π (B : Nat) → Π (C : Nat) → Id Nat (Add (Add X B) C) (Add X (Add B C))) {
    Z => λ (B : Nat). λ (C : Nat). Refl,
    S (A') Ih => λ (B : Nat). λ (C : Nat).
      IdCongr Nat Nat (λ (N : Nat). S N) (Add (Add A' B) C) (Add A' (Add B C)) (Ih B C) } }
def AddAssocTy : Term := prog{ Π (A : Nat) → Π (B : Nat) → Π (C : Nat) → Id Nat (Add (Add A B) C) (Add A (Add B C)) }

/-! ## The length-equation shift lemmas — `hlen` updates for the recursive partScan

    The recursion's loop invariant is `Len *v = S (Add k (Add i g))`, and `k+i+g`
    is constant across every step (each moves one successor between the `k`, `i`,
    `g` slots). So each recursive `hlen` update is an arithmetic-identity transport
    of the same total, provable by `AddSucc` (the only non-definitional step, since
    Std `Add` recurses on its first argument). Two shapes cover all three cases:
    boundary advance (True-Z, True-S g') and gap growth (False). -/

-- Boundary advance: `Add (S k) (Add i g) = Add k (Add (S i) g)` (move a successor
-- from k to i). `Add (S i) g = S (Add i g)` is definitional, so only the `add k
-- (S ·)` step needs AddSucc.
def HshiftTrue : Term := prog{
  λ (K : Nat). λ (I : Nat). λ (G : Nat).
    IdSym Nat (Add K (S (Add I G))) (S (Add K (Add I G))) (AddSucc K (Add I G)) }
def HshiftTrueTy : Term := prog{ Π (K : Nat) → Π (I : Nat) → Π (G : Nat) →
  Id Nat (Add (S K) (Add I G)) (Add K (Add (S I) G)) }

-- Gap growth: `Add (S k) (Add i g) = Add k (Add i (S g))` (move a successor from k
-- to g). `Add i (S g)` is stuck (add recurses on i), so this needs AddSucc TWICE
-- — once under `Add k` to grow the gap, once to pull the successor out front.
def HshiftFalse : Term := prog{
  λ (K : Nat). λ (I : Nat). λ (G : Nat).
    IdSym Nat (Add K (Add I (S G))) (S (Add K (Add I G)))
      (IdTrans Nat (Add K (Add I (S G))) (Add K (S (Add I G))) (S (Add K (Add I G)))
        (IdCongr Nat Nat (λ (X : Nat). Add K X) (Add I (S G)) (S (Add I G)) (AddSucc I G))
        (AddSucc K (Add I G))) }
def HshiftFalseTy : Term := prog{ Π (K : Nat) → Π (I : Nat) → Π (G : Nat) →
  Id Nat (Add (S K) (Add I G)) (Add K (Add I (S G))) }

-- `Count`'s Cons-unfolding equation as an Id — definitional, a `Refl` after whnf.
def CountCons : Term := prog{ λ (M : Nat). λ (H : Nat). λ (T : List Nat). Refl }
def CountConsTy : Term := prog{
  Π (M : Nat) → Π (H : Nat) → Π (T : List Nat) →
    Id Nat (Count M (Cons H T)) (boolRec (λ (B : Bool). Nat) (S (Count M T)) (Count M T) (Eqb M H)) }

/-! ## The `Count`/`Append`/`Take`/`Drop` lemmas (§16-2)

    `CountAppend` — count distributes over `Append` — needs a dependent Bool-elim
    on `Eqb m h` in the `Cons` case (the motive abstracts the `boolRec` that
    `Count (Cons …)` unfolds to). `TakeDropId` reassembles a list from its
    prefix and suffix. Both are the building blocks the swap-count lemma consumes. -/

def CountAppend : Term := prog{
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
def CountAppendTy : Term := prog{
  Π (M : Nat) → Π (A : List Nat) → Π (B : List Nat) →
    Id Nat (Count M (Append A B)) (Add (Count M A) (Count M B)) }

def TakeDropId : Term := prog{
  λ (I : Nat). elim I return (λ (K : Nat). Π (L : List Nat) → Id (List Nat) (Append (Take K L) (Drop K L)) L) {
    Z => λ (L : List Nat). Refl,
    S (I') Ih => λ (L : List Nat).
      elim L return (λ (X : List Nat). Id (List Nat) (Append (Take (S I') X) (Drop (S I') X)) X) {
        Nil => Refl,
        Cons (H) (T) Ihl =>
          IdCongr (List Nat) (List Nat) (λ (R : List Nat). Cons H R)
            (Append (Take I' T) (Drop I' T)) T (Ih T)
      } } }
def TakeDropIdTy : Term := prog{
  Π (I : Nat) → Π (L : List Nat) → Id (List Nat) (Append (Take I L) (Drop I L)) L }

/-! ## `NthL`, `Set`, `SwapL` — the pure specification of swap (§16-2)

    Authored in the surface (dogfooding §15 — a first raw-de-Bruijn `Set` had a
    `pvar 4`-vs-`pvar 3` slip; the surface version cannot slip). `SwapL` mirrors
    the cursor walk: recurse past the prefix, then at `i = 0` exchange the head
    with position `j` of the tail (`Cons (NthL j' xs) (Set j' x xs)`). Reduces:
    `SwapL 0 2 [1,2,3] = [3,2,1]`. `CountSwapL` is the pending node — see the
    milestone report: it requires a BOUND (`SwapL` off the end defaults `NthL` to
    `Z`, breaking count preservation), so it decomposes into a bounded stack. -/

def NthL : Term := prog{
  λ (K : Nat). elim K return (λ (Z0 : Nat). List Nat → Nat) {
    Z => λ (L : List Nat). elim L return (λ (Z0 : List Nat). Nat) { Nil => Z, Cons (H) (T) Ihl => H },
    S (K') Rec => λ (L : List Nat). elim L return (λ (Z0 : List Nat). Nat) { Nil => Z, Cons (H) (T) Ihl => Rec T } } }

def Set : Term := prog{
  λ (K : Nat). λ (V : Nat). elim K return (λ (Z0 : Nat). List Nat → List Nat) {
    Z => λ (L : List Nat). elim L return (λ (Z0 : List Nat). List Nat) { Nil => Nil, Cons (H) (T) Ihl => Cons V T },
    S (K') Rec => λ (L : List Nat). elim L return (λ (Z0 : List Nat). List Nat) { Nil => Nil, Cons (H) (T) Ihl => Cons H (Rec T) } } }

def SwapL : Term := prog{
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

def LenSet : Term := prog{
  λ (K : Nat). λ (V : Nat).
    elim K return (λ (Z0 : Nat). Π (L : List Nat) → Id Nat (Len (Set Z0 V L)) (Len L)) {
      Z => λ (L : List Nat). elim L return (λ (X : List Nat). Id Nat (Len (Set Z V X)) (Len X)) {
        Nil => Refl, Cons (H) (T) Ihl => Refl },
      S (K') Ih => λ (L : List Nat). elim L return (λ (X : List Nat). Id Nat (Len (Set (S K') V X)) (Len X)) {
        Nil => Refl,
        Cons (H) (T) Ihl => IdCongr Nat Nat (λ (N : Nat). S N) (Len (Set K' V T)) (Len T) (Ih T) } } }
def LenSetTy : Term := prog{ Π (K : Nat) → Π (V : Nat) → Π (L : List Nat) → Id Nat (Len (Set K V L)) (Len L) }

def LenSwapL : Term := prog{
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
def LenSwapLTy : Term := prog{ Π (I : Nat) → Π (J : Nat) → Π (L : List Nat) → Id Nat (Len (SwapL I J L)) (Len L) }

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

def Cons2Comm : Term := prog{
  λ (M : Nat). λ (A : Nat). λ (B : Nat). λ (L : List Nat).
    elim (Eqb M A) generalizing (Id Nat (Count M (Cons A (Cons B L))) (Count M (Cons B (Cons A L)))) {
      True => elim (Eqb M B) generalizing
        (Id Nat (S (Count M (Cons B L)))
                (boolRec (λ (W : Bool). Nat) (S (S (Count M L))) (S (Count M L)) (Eqb M B))) {
        True => Refl, False => Refl },
      False => Refl } }
def Cons2CommTy : Term := prog{
  Π (M : Nat) → Π (A : Nat) → Π (B : Nat) → Π (L : List Nat) →
    Id Nat (Count M (Cons A (Cons B L))) (Count M (Cons B (Cons A L))) }

-- Congruence of `Count` under `Cons`: the `f` abstracts `Count m ·` out of BOTH
-- occurrences in the `boolRec` that `Count m (Cons h ·)` whnf's to, so a single
-- `IdCongr` transports the tail equation through the head.
def CountConsCongr : Term := prog{
  λ (M : Nat). λ (H : Nat). λ (L1 : List Nat). λ (L2 : List Nat). λ (P : Id Nat (Count M L1) (Count M L2)).
    IdCongr Nat Nat (λ (R : Nat). boolRec (λ (W : Bool). Nat) (S R) R (Eqb M H)) (Count M L1) (Count M L2) P }
def CountConsCongrTy : Term := prog{
  Π (M : Nat) → Π (H : Nat) → Π (L1 : List Nat) → Π (L2 : List Nat) →
    Id Nat (Count M L1) (Count M L2) → Id Nat (Count M (Cons H L1)) (Count M (Cons H L2)) }

-- The §18 rewrite-by-Id lemma, named: from a RECEIVED equation `Eqb m a = True`,
-- resolve the STUCK `Count m (Cons a l)` to `S (Count m l)`. J transports `Refl`
-- along `IdSym hq`, the motive abstracting the scrutinee `z` out of the `boolRec`
-- that `Count (Cons …)` unfolds to. Abstraction alone cannot do this (the subterm
-- hides behind the scrutinee's own reduction); this is the knowledge half. The
-- imperative tie-in returns THIS applied to its params.
def CountConsHit : Term := prog{
  λ (M : Nat). λ (A : Nat). λ (L : List Nat). λ (Hq : Id Bool (Eqb M A) True).
    j Bool True
      (λ (Z0 : Bool). λ (H : Id Bool True Z0).
        Id Nat (boolRec (λ (W : Bool). Nat) (S (Count M L)) (Count M L) Z0) (S (Count M L)))
      Refl (Eqb M A) (IdSym Bool (Eqb M A) True Hq) }
def CountConsHitTy : Term := prog{
  Π (M : Nat) → Π (A : Nat) → Π (L : List Nat) → Id Bool (Eqb M A) True →
    Id Nat (Count M (Cons A L)) (S (Count M L)) }

-- Bounded head-swap: exchanging the head `x` with position `j` of the tail `xs`
-- preserves count, PROVIDED `j` is in range (`Le (S j) (Len xs)`). Induction on
-- `j`, casing `xs`; the `Nil` leaves are ⊥-discharged by the bound (`Le (S _) Z`).
-- Base (`j = Z`): the swap is `Cons y (Cons x ys) ↔ Cons x (Cons y ys)`, exactly
-- `Cons2Comm`. Step (`j = S j'`): a three-link `IdTrans` chain — float the
-- swapped-in element past the head with `Cons2Comm`, apply the IH under the head
-- via `CountConsCongr`, then `Cons2Comm` back.
def CountHeadswap : Term := prog{
  λ (M : Nat). λ (X : Nat). λ (J : Nat).
    elim J return (λ (Jz : Nat).
        Π (Xs : List Nat) → Le (S Jz) (Len Xs) →
          Id Nat (Count M (Cons (NthL Jz Xs) (Set Jz X Xs))) (Count M (Cons X Xs))) {
      Z => λ (Xs : List Nat).
        elim Xs return (λ (Xz : List Nat).
            Le (S Z) (Len Xz) →
              Id Nat (Count M (Cons (NthL Z Xz) (Set Z X Xz))) (Count M (Cons X Xz))) {
          Nil => λ (Bnd0 : Le (S Z) (Len Nil)).
            botElim (Id Nat (Count M (Cons (NthL Z Nil) (Set Z X Nil))) (Count M (Cons X Nil))) Bnd0,
          Cons (Y) (Ys) Ihx => λ (Bnd0 : Le (S Z) (Len (Cons Y Ys))).
            Cons2Comm M Y X Ys },
      S (J') Ih => λ (Xs : List Nat).
        elim Xs return (λ (Xz : List Nat).
            Le (S (S J')) (Len Xz) →
              Id Nat (Count M (Cons (NthL (S J') Xz) (Set (S J') X Xz))) (Count M (Cons X Xz))) {
          Nil => λ (Bnd0 : Le (S (S J')) (Len Nil)).
            botElim (Id Nat (Count M (Cons (NthL (S J') Nil) (Set (S J') X Nil))) (Count M (Cons X Nil))) Bnd0,
          Cons (Y) (Ys) Ihx => λ (Bnd0 : Le (S (S J')) (Len (Cons Y Ys))).
            IdTrans Nat
              (Count M (Cons (NthL J' Ys) (Cons Y (Set J' X Ys))))
              (Count M (Cons Y (Cons (NthL J' Ys) (Set J' X Ys))))
              (Count M (Cons X (Cons Y Ys)))
              (Cons2Comm M (NthL J' Ys) Y (Set J' X Ys))
              (IdTrans Nat
                (Count M (Cons Y (Cons (NthL J' Ys) (Set J' X Ys))))
                (Count M (Cons Y (Cons X Ys)))
                (Count M (Cons X (Cons Y Ys)))
                (CountConsCongr M Y (Cons (NthL J' Ys) (Set J' X Ys)) (Cons X Ys) (Ih Ys Bnd0))
                (Cons2Comm M Y X Ys)) } } }
def CountHeadswapTy : Term := prog{
  Π (M : Nat) → Π (X : Nat) → Π (J : Nat) → Π (Xs : List Nat) → Le (S J) (Len Xs) →
    Id Nat (Count M (Cons (NthL J Xs) (Set J X Xs))) (Count M (Cons X Xs)) }

-- The top: `SwapL i j` preserves count when both indices are in range. Induction
-- on `i`, casing `l` then `j`. The head case (`i = Z`, `j = S j'`) is exactly a
-- `CountHeadswap` (`SwapL Z (S j') (Cons y ys) = Cons (NthL j' ys) (Set j' y ys)`);
-- the recursive case (`i = S i'`, `j = S j'`) rebuilds `Cons y (SwapL i' j' ys)`,
-- discharged by `CountConsCongr` on the IH; the degenerate `j = Z` / `i > j`
-- cases are the identity swap (`Refl`); `Nil` is ⊥-discharged by `Le (S i) …`.
def CountSwapL : Term := prog{
  λ (M : Nat). λ (I : Nat).
    elim I return (λ (Iz : Nat).
        Π (J : Nat) → Π (L : List Nat) → Le (S Iz) (Len L) → Le (S J) (Len L) →
          Id Nat (Count M (SwapL Iz J L)) (Count M L)) {
      Z => λ (J : Nat). λ (L : List Nat).
        elim L return (λ (Lz : List Nat).
            Le (S Z) (Len Lz) → Le (S J) (Len Lz) → Id Nat (Count M (SwapL Z J Lz)) (Count M Lz)) {
          Nil => λ (Bi0 : Le (S Z) (Len Nil)). λ (Bj0 : Le (S J) (Len Nil)).
            botElim (Id Nat (Count M (SwapL Z J Nil)) (Count M Nil)) Bi0,
          Cons (Y) (Ys) Ihl => λ (Bi0 : Le (S Z) (Len (Cons Y Ys))). λ (Bj0 : Le (S J) (Len (Cons Y Ys))).
            elim J return (λ (Jz : Nat).
                Le (S Jz) (Len (Cons Y Ys)) →
                  Id Nat (Count M (SwapL Z Jz (Cons Y Ys))) (Count M (Cons Y Ys))) {
              Z => λ (Bj1 : Le (S Z) (Len (Cons Y Ys))). Refl,
              S (J') Jih => λ (Bj1 : Le (S (S J')) (Len (Cons Y Ys))).
                CountHeadswap M Y J' Ys Bj1
            } Bj0 },
      S (I') Ih => λ (J : Nat). λ (L : List Nat).
        elim L return (λ (Lz : List Nat).
            Le (S (S I')) (Len Lz) → Le (S J) (Len Lz) → Id Nat (Count M (SwapL (S I') J Lz)) (Count M Lz)) {
          Nil => λ (Bi0 : Le (S (S I')) (Len Nil)). λ (Bj0 : Le (S J) (Len Nil)).
            botElim (Id Nat (Count M (SwapL (S I') J Nil)) (Count M Nil)) Bi0,
          Cons (Y) (Ys) Ihl => λ (Bi0 : Le (S (S I')) (Len (Cons Y Ys))). λ (Bj0 : Le (S J) (Len (Cons Y Ys))).
            elim J return (λ (Jz : Nat).
                Le (S Jz) (Len (Cons Y Ys)) →
                  Id Nat (Count M (SwapL (S I') Jz (Cons Y Ys))) (Count M (Cons Y Ys))) {
              Z => λ (Bj1 : Le (S Z) (Len (Cons Y Ys))). Refl,
              S (J') Jih => λ (Bj1 : Le (S (S J')) (Len (Cons Y Ys))).
                CountConsCongr M Y (SwapL I' J' Ys) Ys (Ih J' Ys Bi0 Bj1)
            } Bj0 } } }
def CountSwapLTy : Term := prog{
  Π (M : Nat) → Π (I : Nat) → Π (J : Nat) → Π (L : List Nat) →
    Le (S I) (Len L) → Le (S J) (Len L) → Id Nat (Count M (SwapL I J L)) (Count M L) }

-- The friction-free corollary: CountSwapL with swapS's telescope-mirrored
-- premises (`Le (S i) j`, `Le (S j) (Len l)` — exactly the `pij`/`p2` a swapS
-- caller holds). The general CountSwapL is the mathematically right statement
-- (independent bounds, no `i ≤ j` needed); this derives the caller's hand-off from
-- it. `Le (S i) (Len l)` comes by `LeTrans (S i) (S j) (Len l)`: `LeUpR` lifts
-- `pij : Le (S i) j` to `Le (S i) (S j)`, then chain with `p2`.
def CountSwapL' : Term := prog{
  λ (M : Nat). λ (I : Nat). λ (J : Nat). λ (L : List Nat).
    λ (Pij : Le (S I) J). λ (P2 : Le (S J) (Len L)).
      CountSwapL M I J L (LeTrans (S I) (S J) (Len L) (LeUpR (S I) J Pij) P2) P2 }
def CountSwapL'Ty : Term := prog{
  Π (M : Nat) → Π (I : Nat) → Π (J : Nat) → Π (L : List Nat) →
    Le (S I) J → Le (S J) (Len L) → Id Nat (Count M (SwapL I J L)) (Count M L) }

/-! ## The BRIDGE — set/nth exit form ≡ `SwapL` (§22, direct proving)

    In direct-proving mode a swap FnDef's return type reads the EXIT snapshot, and
    the exit reading of `swapS`'s body is the set/nth composition its two crossed
    writes leave behind — `Set i (NthL j l) (Set j (NthL i l) l)` — NOT the `SwapL`
    model. This bridges the two so every `SwapL`-based lemma (CountSwapL',
    LenSwapL, …) transports to the surface form rather than being re-proved per
    composition (which would be a per-form count-algebra tax forever).

    Carries swapS's telescope bounds `Le (S i) j`, `Le (S j) (Len l)` (the `pij`/`p2`
    a swapS caller holds). Both are load-bearing IN THE PROOF, each killing one
    impossible leaf: `pij` discharges the `j = Z` slot (where set-form and SwapL
    disagree once `i > 0`), `p2` discharges the `l = Nil` slot (where the inner
    `Set j v Nil` is otherwise STUCK on the free `j` — semantically Nil but not
    definitionally without casing `j`). Note the SEMANTIC content needs only
    `Le (S i) j`: verified computationally the two forms agree for all `i < j` even
    off the end. `p2` is proof-theoretic scaffolding, not semantic necessity — it
    lets the Nil leaf be a `botElim` rather than a `set_nil` rewrite, giving the
    exact M18/CountSwapL shape. Induction mirrors `SwapL`: `i = Z` is definitional
    (both sides reduce to `Cons (NthL j' ys) (Set j' y ys)`), the `i = S i'` step is
    the IH under `Cons y ·`. -/
def SwapLSet : Term := prog{
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
def SwapLSetTy : Term := prog{
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

def PartScanL : Term := prog{
  λ (Pivot : Nat). λ (K : Nat).
    elim K return (λ (Kz : Nat). Π (I : Nat) → Π (G : Nat) → List Nat → List Nat) {
      Z => λ (I : Nat). λ (G : Nat). λ (L : List Nat).
        elim I return (λ (Iz : Nat). List Nat) {
          Z => L,
          S (I') Iih => SwapL Z (S I') L },
      S (K') Rec => λ (I : Nat). λ (G : Nat). λ (L : List Nat).
        elim (Leb (NthL (S (Add I G)) L) Pivot) return (λ (W : Bool). List Nat) {
          True => elim G return (λ (Gz : Nat). List Nat) {
            Z => Rec (S I) Z L,
            S (G') Gih => Rec (S I) (S G') (SwapL (S I) (S (Add I G)) L) },
          False => Rec I (S G) L } } }

def PartitionL : Term := prog{
  λ (N : Nat). λ (L : List Nat).
    elim N return (λ (Nz : Nat). List Nat) {
      Z => L,
      S (N') Rec => PartScanL (NthL Z L) N' Z Z L } }
def PartitionLTy : Term := prog{ Π (N : Nat) → List Nat → List Nat }

/-! ## `PartScanIdxL` / `PartIdxL` — the boundary INDEX the scan produces (§21)

    Mirror of partScanL's recursion but returning the boundary `i` (the pivot's
    final position) at `k = Z` instead of the placed list. This is the index the
    imperative partition returns transparently (a Σ pinning it to `PartIdxL`), and
    the split point sortL's two recursive calls ride. Same casings/arithmetic as
    PartScanL, so the two stay in lockstep. -/

def PartScanIdxL : Term := prog{
  λ (Pivot : Nat). λ (K : Nat).
    elim K return (λ (Kz : Nat). Π (I : Nat) → Π (G : Nat) → List Nat → Nat) {
      Z => λ (I : Nat). λ (G : Nat). λ (L : List Nat). I,
      S (K') Rec => λ (I : Nat). λ (G : Nat). λ (L : List Nat).
        elim (Leb (NthL (S (Add I G)) L) Pivot) return (λ (W : Bool). Nat) {
          True => elim G return (λ (Gz : Nat). Nat) {
            Z => Rec (S I) Z L,
            S (G') Gih => Rec (S I) (S G') (SwapL (S I) (S (Add I G)) L) },
          False => Rec I (S G) L } } }

def PartIdxL : Term := prog{
  λ (N : Nat). λ (L : List Nat).
    elim N return (λ (Nz : Nat). Nat) {
      Z => Z,
      S (N') Rec => PartScanIdxL (NthL Z L) N' Z Z L } }
def PartIdxLTy : Term := prog{ Π (N : Nat) → List Nat → Nat }

/-! ## `SortL` — the pure quicksort model (§21)

    Fuel-structural (natRec on `fuel`; the caller passes `fuel = n` at the top).
    Base: out of fuel, or a segment of length ≤ 1 (already sorted) → identity. Step
    (n ≥ 2): partition the segment (`p = PartitionL n l`, pivot lands at `i =
    PartIdxL n l`), then recursively sort the two Sub-slices — the prefix `take i p`
    (length `i`) and the suffix `Drop (S i) p` (length `Len (Drop (S i) p)`, which
    avoids Nat subtraction) — reassembling `sortedPrefix ++ [pivot] ++ sortedSuffix`.
    The imperative quicksort mirrors this exactly (partition returns the transparent
    `i`, both recursions ride it), so the conformance is conversion. -/

def SortL : Term := prog{
  λ (Fuel : Nat).
    elim Fuel return (λ (Fz : Nat). Π (N : Nat) → List Nat → List Nat) {
      Z => λ (N : Nat). λ (L : List Nat). L,
      S (F') Rec => λ (N : Nat). λ (L : List Nat).
        elim N return (λ (Nz : Nat). List Nat) {
          Z => L,
          S (N') Nih => elim N' return (λ (Mz : Nat). List Nat) {
            Z => L,
            S (N'') N2ih =>
              let p = PartitionL N L;
              let i = PartIdxL N L;
              Append (Rec i (Take i p)) (Cons (NthL i p) (Rec (Len (Drop (S i) p)) (Drop (S i) p)))
          } } } }
def SortLTy : Term := prog{ Π (Fuel : Nat) → Π (N : Nat) → List Nat → List Nat }

/-! ## Range-aware models — the index-bounded quicksort spec (§21, plan of record)

    SUGGESTIONS.md's north star: "suffix sub-slices are tail reborrows; PREFIX
    RECURSION RIDES THE BOUND, not a prefix borrow." So the imperative quicksort
    is CLRS-form `quicksort(v, lo, cnt)` — reborrow the whole *v, sort the `cnt`
    elements at offset `lo` by index swaps, recurse on the two sub-ranges. These
    models are `PartScanL`/`PartIdxL`/`SortL` with every position shifted by `lo`
    (the pivot sits at `lo`, scan positions are `lo + 1 + i + g`), the boundary
    `i` tracked RELATIVE to `lo`. Two facts make the recursion subtraction-free:
    the relative boundary `i` at `k = Z` IS the left sub-count (elements ≤ pivot),
    and the gap `g` at `k = Z` IS the right sub-count (elements > pivot) — the scan
    maintains `i + g = k`, so no `hi - lo` ever appears. -/

def PartScanRangeL : Term := prog{
  λ (Pivot : Nat). λ (Lo : Nat). λ (K : Nat).
    elim K return (λ (Kz : Nat). Π (I : Nat) → Π (G : Nat) → List Nat → List Nat) {
      Z => λ (I : Nat). λ (G : Nat). λ (L : List Nat).
        elim I return (λ (Iz : Nat). List Nat) {
          Z => L,
          S (I') Iih => SwapL Lo (Add Lo (S I')) L },
      S (K') Rec => λ (I : Nat). λ (G : Nat). λ (L : List Nat).
        elim (Leb (NthL (Add Lo (S (Add I G))) L) Pivot) return (λ (W : Bool). List Nat) {
          True => elim G return (λ (Gz : Nat). List Nat) {
            Z => Rec (S I) Z L,
            S (G') Gih => Rec (S I) (S G') (SwapL (Add Lo (S I)) (Add Lo (S (Add I G))) L) },
          False => Rec I (S G) L } } }

def PartitionRangeL : Term := prog{
  λ (Lo : Nat). λ (Cnt : Nat). λ (L : List Nat).
    elim Cnt return (λ (Cz : Nat). List Nat) {
      Z => L,
      S (Cnt') Rec => PartScanRangeL (NthL Lo L) Lo Cnt' Z Z L } }

def PartScanIdxRangeL : Term := prog{
  λ (Pivot : Nat). λ (Lo : Nat). λ (K : Nat).
    elim K return (λ (Kz : Nat). Π (I : Nat) → Π (G : Nat) → List Nat → Nat) {
      Z => λ (I : Nat). λ (G : Nat). λ (L : List Nat). I,
      S (K') Rec => λ (I : Nat). λ (G : Nat). λ (L : List Nat).
        elim (Leb (NthL (Add Lo (S (Add I G))) L) Pivot) return (λ (W : Bool). Nat) {
          True => elim G return (λ (Gz : Nat). Nat) {
            Z => Rec (S I) Z L,
            S (G') Gih => Rec (S I) (S G') (SwapL (Add Lo (S I)) (Add Lo (S (Add I G))) L) },
          False => Rec I (S G) L } } }

def PartIdxRangeL : Term := prog{
  λ (Lo : Nat). λ (Cnt : Nat). λ (L : List Nat).
    elim Cnt return (λ (Cz : Nat). Nat) {
      Z => Z,
      S (Cnt') Rec => PartScanIdxRangeL (NthL Lo L) Lo Cnt' Z Z L } }

def PartScanGapRangeL : Term := prog{
  λ (Pivot : Nat). λ (Lo : Nat). λ (K : Nat).
    elim K return (λ (Kz : Nat). Π (I : Nat) → Π (G : Nat) → List Nat → Nat) {
      Z => λ (I : Nat). λ (G : Nat). λ (L : List Nat). G,
      S (K') Rec => λ (I : Nat). λ (G : Nat). λ (L : List Nat).
        elim (Leb (NthL (Add Lo (S (Add I G))) L) Pivot) return (λ (W : Bool). Nat) {
          True => elim G return (λ (Gz : Nat). Nat) {
            Z => Rec (S I) Z L,
            S (G') Gih => Rec (S I) (S G') (SwapL (Add Lo (S I)) (Add Lo (S (Add I G))) L) },
          False => Rec I (S G) L } } }

def PartGapRangeL : Term := prog{
  λ (Lo : Nat). λ (Cnt : Nat). λ (L : List Nat).
    elim Cnt return (λ (Cz : Nat). Nat) {
      Z => Z,
      S (Cnt') Rec => PartScanGapRangeL (NthL Lo L) Lo Cnt' Z Z L } }

-- The scan's size invariant: the boundary `idx` plus the gap `gap` always sum to
-- `k + i + g` — the scan neither creates nor destroys total budget, it only shifts
-- successors between the `k`/`i`/`g` slots (the same move the `hshift` lemmas
-- encode). Induction on `k` with `i`,`g`,`l` quantified AFTER `k` in the motive, so
-- the IH is usable at the shifted arguments each recursive step takes. The `S k`
-- step cases on the SAME `Leb` scrutinee that both `PartScanIdxRangeL` and
-- `PartScanGapRangeL` branch on, abstracting that `Bool` uniformly across the idx
-- and gap elims; each leaf is one `hshift` transport (`IdSym`/`IdTrans`).
def PartScanSizeL : Term := prog{
  λ (Pivot : Nat). λ (Lo : Nat). λ (K : Nat).
    elim K return (λ (Kz : Nat). Π (I : Nat) → Π (G : Nat) → Π (L : List Nat) →
        Id Nat (Add (PartScanIdxRangeL Pivot Lo Kz I G L) (PartScanGapRangeL Pivot Lo Kz I G L)) (Add Kz (Add I G))) {
      Z => λ (I : Nat). λ (G : Nat). λ (L : List Nat). Refl,
      S (K') Ih => λ (I : Nat). λ (G : Nat). λ (L : List Nat).
        elim (Leb (NthL (Add Lo (S (Add I G))) L) Pivot)
          return (λ (W : Bool). Id Nat
            (Add (elim W return (λ (Ww : Bool). Nat) {
                    True => elim G return (λ (Gz : Nat). Nat) {
                      Z => PartScanIdxRangeL Pivot Lo K' (S I) Z L,
                      S (G') Gih => PartScanIdxRangeL Pivot Lo K' (S I) (S G') (SwapL (Add Lo (S I)) (Add Lo (S (Add I G))) L) },
                    False => PartScanIdxRangeL Pivot Lo K' I (S G) L })
                 (elim W return (λ (Ww : Bool). Nat) {
                    True => elim G return (λ (Gz : Nat). Nat) {
                      Z => PartScanGapRangeL Pivot Lo K' (S I) Z L,
                      S (G') Gih => PartScanGapRangeL Pivot Lo K' (S I) (S G') (SwapL (Add Lo (S I)) (Add Lo (S (Add I G))) L) },
                    False => PartScanGapRangeL Pivot Lo K' I (S G) L }))
            (Add (S K') (Add I G))) {
          True => elim G return (λ (Gz : Nat). Id Nat
                    (Add (elim Gz return (λ (Gy : Nat). Nat) {
                            Z => PartScanIdxRangeL Pivot Lo K' (S I) Z L,
                            S (G') Gih => PartScanIdxRangeL Pivot Lo K' (S I) (S G') (SwapL (Add Lo (S I)) (Add Lo (S (Add I G))) L) })
                         (elim Gz return (λ (Gy : Nat). Nat) {
                            Z => PartScanGapRangeL Pivot Lo K' (S I) Z L,
                            S (G') Gih => PartScanGapRangeL Pivot Lo K' (S I) (S G') (SwapL (Add Lo (S I)) (Add Lo (S (Add I G))) L) }))
                    (Add (S K') (Add I Gz))) {
            Z => IdTrans Nat
                   (Add (PartScanIdxRangeL Pivot Lo K' (S I) Z L) (PartScanGapRangeL Pivot Lo K' (S I) Z L))
                   (Add K' (Add (S I) Z))
                   (Add (S K') (Add I Z))
                   (Ih (S I) Z L)
                   (IdSym Nat (Add (S K') (Add I Z)) (Add K' (Add (S I) Z)) (HshiftTrue K' I Z)),
            S (G') Gih => IdTrans Nat
                   (Add (PartScanIdxRangeL Pivot Lo K' (S I) (S G') (SwapL (Add Lo (S I)) (Add Lo (S (Add I G))) L)) (PartScanGapRangeL Pivot Lo K' (S I) (S G') (SwapL (Add Lo (S I)) (Add Lo (S (Add I G))) L)))
                   (Add K' (Add (S I) (S G')))
                   (Add (S K') (Add I (S G')))
                   (Ih (S I) (S G') (SwapL (Add Lo (S I)) (Add Lo (S (Add I G))) L))
                   (IdSym Nat (Add (S K') (Add I (S G'))) (Add K' (Add (S I) (S G'))) (HshiftTrue K' I (S G')))
          },
          False => IdTrans Nat
                     (Add (PartScanIdxRangeL Pivot Lo K' I (S G) L) (PartScanGapRangeL Pivot Lo K' I (S G) L))
                     (Add K' (Add I (S G)))
                     (Add (S K') (Add I G))
                     (Ih I (S G) L)
                     (IdSym Nat (Add (S K') (Add I G)) (Add K' (Add I (S G))) (HshiftFalse K' I G))
        }
    } }
def PartScanSizeLTy : Term := prog{ Π (Pivot : Nat) → Π (Lo : Nat) → Π (K : Nat) → Π (I : Nat) → Π (G : Nat) → Π (L : List Nat) →
  Id Nat (Add (PartScanIdxRangeL Pivot Lo K I G L) (PartScanGapRangeL Pivot Lo K I G L)) (Add K (Add I G)) }

-- The range scan preserves length — it only ever rebuilds the same spine (SwapL,
-- which LenSwapL knows preserves length) or leaves it. Same induction shape as
-- PartScanSizeL (on k, elim the leb Bool, elim g in True), but the leaves are
-- simpler: each recursive step is the IH, and the two SwapL cases (Z-base pivot
-- placement, True/S-g swap) bridge through LenSwapL. The quicksort recursion
-- needs this because partitionRange MUTATES *v, and the two recursive-call range
-- bounds refer to len (*v-after-partition) — this moves them back onto len (entry).
def LenPartScanRangeL : Term := prog{
  λ (Pivot : Nat). λ (Lo : Nat). λ (K : Nat).
    elim K return (λ (Kz : Nat). Π (I : Nat) → Π (G : Nat) → Π (L : List Nat) →
        Id Nat (Len (PartScanRangeL Pivot Lo Kz I G L)) (Len L)) {
      Z => λ (I : Nat). λ (G : Nat). λ (L : List Nat).
        elim I return (λ (Iz : Nat). Id Nat
            (Len (elim Iz return (λ (Iy : Nat). List Nat) { Z => L, S (I') Iih => SwapL Lo (Add Lo (S I')) L }))
            (Len L)) {
          Z => Refl,
          S (I') Iih => LenSwapL Lo (Add Lo (S I')) L },
      S (K') Ih => λ (I : Nat). λ (G : Nat). λ (L : List Nat).
        elim (Leb (NthL (Add Lo (S (Add I G))) L) Pivot)
          return (λ (W : Bool). Id Nat
            (Len (elim W return (λ (Ww : Bool). List Nat) {
                    True => elim G return (λ (Gz : Nat). List Nat) {
                      Z => PartScanRangeL Pivot Lo K' (S I) Z L,
                      S (G') Gih => PartScanRangeL Pivot Lo K' (S I) (S G') (SwapL (Add Lo (S I)) (Add Lo (S (Add I G))) L) },
                    False => PartScanRangeL Pivot Lo K' I (S G) L }))
            (Len L)) {
          True => elim G return (λ (Gz : Nat). Id Nat
                    (Len (elim Gz return (λ (Gy : Nat). List Nat) {
                            Z => PartScanRangeL Pivot Lo K' (S I) Z L,
                            S (G') Gih => PartScanRangeL Pivot Lo K' (S I) (S G') (SwapL (Add Lo (S I)) (Add Lo (S (Add I G))) L) }))
                    (Len L)) {
            Z => Ih (S I) Z L,
            S (G') Gih => IdTrans Nat
                   (Len (PartScanRangeL Pivot Lo K' (S I) (S G') (SwapL (Add Lo (S I)) (Add Lo (S (Add I G))) L)))
                   (Len (SwapL (Add Lo (S I)) (Add Lo (S (Add I G))) L))
                   (Len L)
                   (Ih (S I) (S G') (SwapL (Add Lo (S I)) (Add Lo (S (Add I G))) L))
                   (LenSwapL (Add Lo (S I)) (Add Lo (S (Add I G))) L)
          },
          False => Ih I (S G) L
        }
    } }
def LenPartScanRangeLTy : Term := prog{ Π (Pivot : Nat) → Π (Lo : Nat) → Π (K : Nat) → Π (I : Nat) → Π (G : Nat) → Π (L : List Nat) →
  Id Nat (Len (PartScanRangeL Pivot Lo K I G L)) (Len L) }

-- The wrapper form the quicksort recursion consumes: PartitionRangeL is
-- PartScanRangeL after picking the pivot, so its length preservation is the scan's
-- (Z base is Refl, S cnt' is LenPartScanRangeL at the entry offsets).
def LenPartitionRangeL : Term := prog{
  λ (Lo : Nat). λ (Cnt : Nat). λ (L : List Nat).
    elim Cnt return (λ (Cz : Nat). Id Nat
        (Len (elim Cz return (λ (Cy : Nat). List Nat) { Z => L, S (Cnt') Rec => PartScanRangeL (NthL Lo L) Lo Cnt' Z Z L }))
        (Len L)) {
      Z => Refl,
      S (Cnt') Rec => LenPartScanRangeL (NthL Lo L) Lo Cnt' Z Z L } }
def LenPartitionRangeLTy : Term := prog{ Π (Lo : Nat) → Π (Cnt : Nat) → Π (L : List Nat) → Id Nat (Len (PartitionRangeL Lo Cnt L)) (Len L) }

/-! ## Count preservation of the range scan/partition (§22, the partition rung)

    The permutation half of partition's postcondition: the range scan preserves the
    multiset. Same induction shape as LenPartScanRangeL (on k, elim the leb Bool,
    elim g in True), but where LenSwapL is UNCONDITIONAL, CountSwapL' is BOUNDED —
    so unlike the len versions these THREAD the range bound `Le (add lo (S (add k
    (add i g)))) (len l)` (the honest invariant partScanRange already carries) and
    reconstruct the two per-swap `CountSwapL'` premises from it at each swap leaf,
    exactly the LeTrans/LeRwL/LeAddMonoL bound algebra partScanRange's body
    proves. This is the proof-linearity-vs-count asymmetry made concrete: length is
    friction-free, count pays the bound tax at every swap. -/
def CountPartScanRangeL : Term := prog{
  λ (Pivot : Nat). λ (Lo : Nat). λ (M : Nat). λ (K : Nat).
    elim K return (λ (Kz : Nat). Π (I : Nat) → Π (G : Nat) → Π (L : List Nat) →
        Le (Add Lo (S (Add Kz (Add I G)))) (Len L) →
        Id Nat (Count M (PartScanRangeL Pivot Lo Kz I G L)) (Count M L)) {
      Z => λ (I : Nat). λ (G : Nat). λ (L : List Nat).
        elim I return (λ (Iz : Nat).
            Le (Add Lo (S (Add Z (Add Iz G)))) (Len L) →
            Id Nat (Count M (elim Iz return (λ (Iy : Nat). List Nat) {
                Z => L, S (I') Iih => SwapL Lo (Add Lo (S I')) L })) (Count M L)) {
          Z => λ (Hle : Le (Add Lo (S (Add Z (Add Z G)))) (Len L)). Refl,
          S (I') Iih => λ (Hle : Le (Add Lo (S (Add Z (Add (S I') G)))) (Len L)).
            CountSwapL' M Lo (Add Lo (S I')) L (LeAddSucc Lo I')
              (LeTrans (S (Add Lo (S I'))) (Add Lo (S (S (Add I' G)))) (Len L)
                (LeRwL (Add Lo (S (S (Add I' G)))) (Add Lo (S (S I'))) (S (Add Lo (S I')))
                  (AddSucc Lo (S I'))
                  (LeAddMonoL Lo (S (S I')) (S (S (Add I' G))) (LeAdd I' G)))
                Hle)
        },
      S (K') Ih => λ (I : Nat). λ (G : Nat). λ (L : List Nat).
        λ (Hle : Le (Add Lo (S (Add (S K') (Add I G)))) (Len L)).
        elim (Leb (NthL (Add Lo (S (Add I G))) L) Pivot)
          return (λ (W : Bool). Id Nat
            (Count M (elim W return (λ (Ww : Bool). List Nat) {
                True => elim G return (λ (Gz : Nat). List Nat) {
                  Z => PartScanRangeL Pivot Lo K' (S I) Z L,
                  S (G') Gih => PartScanRangeL Pivot Lo K' (S I) (S G') (SwapL (Add Lo (S I)) (Add Lo (S (Add I G))) L) },
                False => PartScanRangeL Pivot Lo K' I (S G) L }))
            (Count M L)) {
          True =>
            (elim G return (λ (Gz : Nat).
                Le (Add Lo (S (Add (S K') (Add I Gz)))) (Len L) →
                Id Nat (Count M (elim Gz return (λ (Gy : Nat). List Nat) {
                    Z => PartScanRangeL Pivot Lo K' (S I) Z L,
                    S (G') Gih => PartScanRangeL Pivot Lo K' (S I) (S G') (SwapL (Add Lo (S I)) (Add Lo (S (Add I Gz))) L) })) (Count M L)) {
              Z => λ (HleZ : Le (Add Lo (S (Add (S K') (Add I Z)))) (Len L)).
                Ih (S I) Z L
                  (LeRwL (Len L)
                    (Add Lo (S (Add (S K') (Add I Z))))
                    (Add Lo (S (Add K' (Add (S I) Z))))
                    (IdCongr Nat Nat (λ (A : Nat). Add Lo (S A))
                      (Add (S K') (Add I Z)) (Add K' (Add (S I) Z)) (HshiftTrue K' I Z))
                    HleZ),
              S (G') Gih => λ (HleS : Le (Add Lo (S (Add (S K') (Add I (S G'))))) (Len L)).
                IdTrans Nat
                  (Count M (PartScanRangeL Pivot Lo K' (S I) (S G') (SwapL (Add Lo (S I)) (Add Lo (S (Add I (S G')))) L)))
                  (Count M (SwapL (Add Lo (S I)) (Add Lo (S (Add I (S G')))) L))
                  (Count M L)
                  (Ih (S I) (S G') (SwapL (Add Lo (S I)) (Add Lo (S (Add I (S G')))) L)
                    (LeRwR (Add Lo (S (Add K' (Add (S I) (S G'))))) (Len L)
                       (Len (SwapL (Add Lo (S I)) (Add Lo (S (Add I (S G')))) L))
                       (IdSym Nat (Len (SwapL (Add Lo (S I)) (Add Lo (S (Add I (S G')))) L)) (Len L)
                         (LenSwapL (Add Lo (S I)) (Add Lo (S (Add I (S G')))) L))
                       (LeRwL (Len L)
                         (Add Lo (S (Add (S K') (Add I (S G')))))
                         (Add Lo (S (Add K' (Add (S I) (S G')))))
                         (IdCongr Nat Nat (λ (A : Nat). Add Lo (S A))
                           (Add (S K') (Add I (S G'))) (Add K' (Add (S I) (S G'))) (HshiftTrue K' I (S G')))
                         HleS)))
                  (CountSwapL' M (Add Lo (S I)) (Add Lo (S (Add I (S G')))) L
                    (LeRwL (Add Lo (S (Add I (S G')))) (Add Lo (S (S I))) (S (Add Lo (S I)))
                      (AddSucc Lo (S I))
                      (LeAddMonoL Lo (S (S I)) (S (Add I (S G'))) (LeAddSucc I G')))
                    (LeTrans (S (Add Lo (S (Add I (S G'))))) (Add Lo (S (S (Add K' (Add I (S G')))))) (Len L)
                      (LeRwL (Add Lo (S (S (Add K' (Add I (S G'))))))
                        (Add Lo (S (S (Add I (S G'))))) (S (Add Lo (S (Add I (S G')))))
                        (AddSucc Lo (S (Add I (S G'))))
                        (LeAddMonoL Lo (S (S (Add I (S G')))) (S (S (Add K' (Add I (S G')))))
                          (LeAddL (Add I (S G')) K')))
                      HleS))
            }) Hle,
          False =>
            Ih I (S G) L
              (LeRwL (Len L)
                (Add Lo (S (Add (S K') (Add I G))))
                (Add Lo (S (Add K' (Add I (S G)))))
                (IdCongr Nat Nat (λ (A : Nat). Add Lo (S A))
                  (Add (S K') (Add I G)) (Add K' (Add I (S G))) (HshiftFalse K' I G))
                Hle)
        }
    } }
def CountPartScanRangeLTy : Term := prog{
  Π (Pivot : Nat) → Π (Lo : Nat) → Π (M : Nat) → Π (K : Nat) → Π (I : Nat) → Π (G : Nat) → Π (L : List Nat) →
    Le (Add Lo (S (Add K (Add I G)))) (Len L) →
    Id Nat (Count M (PartScanRangeL Pivot Lo K I G L)) (Count M L) }

-- Wrapper: PartitionRangeL is PartScanRangeL after picking the pivot, so count
-- preservation is the scan's (Z base Refl, S cnt' is the scan at entry offsets).
-- The top range bound `Le (Add lo cnt) (Len l)` supplies the scan's bound; at
-- cnt = S cnt' it needs an AddZero nudge (`Add cnt' (Add Z Z) = Add cnt' Z`, and
-- `Add` recurses on its FIRST arg so `Add cnt' Z` is stuck at a free cnt').
def CountPartitionRangeL : Term := prog{
  λ (Lo : Nat). λ (M : Nat). λ (Cnt : Nat). λ (L : List Nat).
    elim Cnt return (λ (Cz : Nat).
        Le (Add Lo Cz) (Len L) →
        Id Nat (Count M (elim Cz return (λ (Cy : Nat). List Nat) {
            Z => L, S (Cnt') Rec => PartScanRangeL (NthL Lo L) Lo Cnt' Z Z L })) (Count M L)) {
      Z => λ (Hb : Le (Add Lo Z) (Len L)). Refl,
      S (Cnt') Rec => λ (Hb : Le (Add Lo (S Cnt')) (Len L)).
        CountPartScanRangeL (NthL Lo L) Lo M Cnt' Z Z L
          (LeRwL (Len L) (Add Lo (S Cnt')) (Add Lo (S (Add Cnt' Z)))
            (IdCongr Nat Nat (λ (A : Nat). Add Lo (S A)) Cnt' (Add Cnt' Z)
              (IdSym Nat (Add Cnt' Z) Cnt' (AddZero Cnt')))
            Hb) } }
def CountPartitionRangeLTy : Term := prog{
  Π (Lo : Nat) → Π (M : Nat) → Π (Cnt : Nat) → Π (L : List Nat) →
    Le (Add Lo Cnt) (Len L) → Id Nat (Count M (PartitionRangeL Lo Cnt L)) (Count M L) }

/-- `SortRangeL fuel lo cnt l` — sort the `cnt` elements of `l` at offset `lo` in
    place. Fuel-structural; base = out of fuel or `cnt ≤ 1`; step partitions the
    range, then sorts the left sub-range `[lo, lo+i)` (count `i`) and the right
    `[lo+i+1, …)` (count `g`), the right on the result of the left — the raw
    composition the imperative body implements. `partitionQ` is the `lo = 0` slice. -/
def SortRangeL : Term := prog{
  λ (Fuel : Nat).
    elim Fuel return (λ (Fz : Nat). Π (Lo : Nat) → Π (Cnt : Nat) → List Nat → List Nat) {
      Z => λ (Lo : Nat). λ (Cnt : Nat). λ (L : List Nat). L,
      S (F') Rec => λ (Lo : Nat). λ (Cnt : Nat). λ (L : List Nat).
        elim Cnt return (λ (Cz : Nat). List Nat) {
          Z => L,
          S (Cnt') Nih => elim Cnt' return (λ (Mz : Nat). List Nat) {
            Z => L,
            S (Cnt'') N2ih =>
              let p = PartitionRangeL Lo Cnt L;
              let i = PartIdxRangeL Lo Cnt L;
              let g = PartGapRangeL Lo Cnt L;
              Rec (S (Add Lo i)) g (Rec Lo i p)
          } } } }
def SortRangeLTy : Term := prog{ Π (Fuel : Nat) → Π (Lo : Nat) → Π (Cnt : Nat) → List Nat → List Nat }

-- SortRangeL is a permutation, so it preserves length. Fuel-structural induction
-- mirroring sortRangeL's own shape (base fuel Z / cnt ≤ 1 are Refl); the step is
-- the IH applied to each of the two recursive sorts, chained onto
-- LenPartitionRangeL for the partition underneath. The quicksort recursion needs
-- this for its SECOND range bound: the second recursive call runs after the first
-- has permuted *v, so the bound (over len *v-after-first) moves back through this.
def LenSortRangeL : Term := prog{
  λ (Fuel : Nat).
    elim Fuel return (λ (Fz : Nat). Π (Lo : Nat) → Π (Cnt : Nat) → Π (L : List Nat) → Id Nat (Len (SortRangeL Fz Lo Cnt L)) (Len L)) {
      Z => λ (Lo : Nat). λ (Cnt : Nat). λ (L : List Nat). Refl,
      S (F') Ih => λ (Lo : Nat). λ (Cnt : Nat). λ (L : List Nat).
        elim Cnt return (λ (Cz : Nat). Id Nat (Len (elim Cz return (λ (Cy : Nat). List Nat) {
              Z => L,
              S (Cnt') Nih => elim Cnt' return (λ (My : Nat). List Nat) {
                Z => L,
                S (Cnt'') N2ih => SortRangeL F' (S (Add Lo (PartIdxRangeL Lo Cnt L))) (PartGapRangeL Lo Cnt L) (SortRangeL F' Lo (PartIdxRangeL Lo Cnt L) (PartitionRangeL Lo Cnt L)) } })) (Len L)) {
          Z => Refl,
          S (Cnt') Nih => elim Cnt' return (λ (My : Nat). Id Nat (Len (elim My return (λ (Myy : Nat). List Nat) {
                Z => L,
                S (Cnt'') N2ih => SortRangeL F' (S (Add Lo (PartIdxRangeL Lo Cnt L))) (PartGapRangeL Lo Cnt L) (SortRangeL F' Lo (PartIdxRangeL Lo Cnt L) (PartitionRangeL Lo Cnt L)) })) (Len L)) {
            Z => Refl,
            S (Cnt'') N2ih =>
              IdTrans Nat
                (Len (SortRangeL F' (S (Add Lo (PartIdxRangeL Lo Cnt L))) (PartGapRangeL Lo Cnt L) (SortRangeL F' Lo (PartIdxRangeL Lo Cnt L) (PartitionRangeL Lo Cnt L))))
                (Len (SortRangeL F' Lo (PartIdxRangeL Lo Cnt L) (PartitionRangeL Lo Cnt L)))
                (Len L)
                (Ih (S (Add Lo (PartIdxRangeL Lo Cnt L))) (PartGapRangeL Lo Cnt L) (SortRangeL F' Lo (PartIdxRangeL Lo Cnt L) (PartitionRangeL Lo Cnt L)))
                (IdTrans Nat
                  (Len (SortRangeL F' Lo (PartIdxRangeL Lo Cnt L) (PartitionRangeL Lo Cnt L)))
                  (Len (PartitionRangeL Lo Cnt L))
                  (Len L)
                  (Ih Lo (PartIdxRangeL Lo Cnt L) (PartitionRangeL Lo Cnt L))
                  (LenPartitionRangeL Lo Cnt L))
          } } } }
def LenSortRangeLTy : Term := prog{ Π (Fuel : Nat) → Π (Lo : Nat) → Π (Cnt : Nat) → Π (L : List Nat) → Id Nat (Len (SortRangeL Fuel Lo Cnt L)) (Len L) }

/-! ## Count preservation of the full sort (§22, the quicksort rung)

    The permutation half of quicksort's postcondition. Fuel-structural induction
    mirroring SortRangeL (base fuel Z / cnt ≤ 1 are Refl); the step chains the IH
    over the two recursive sorts onto CountPartitionRangeL for the partition
    underneath — `count m (sort right (sort left (partition l))) = count m (sort
    left (partition l)) = count m (partition l) = count m l`. Like the len version
    but count is BOUNDED, so it threads the range bound `Le (Add lo cnt) (Len l)`
    and each recursive call gets its sub-range bound from `SortRangeBL`/`SortRangeBR`
    below (the two range bounds the imperative quicksort's body already derives from
    PartScanSizeL + the len lemmas). NOTE the elim S-arms carry their (unused) IH
    binders `nih`/`n2ih` — the natRec recursion runs through the fuel `ih`, not the
    cnt elims, but the binder is syntactically required. -/

-- Left sub-range bound: `Le (Add lo i) (Len (partition …))`, i = the pivot index.
-- Lifted verbatim from the quicksort FnDef's `bl` (PartScanSizeL gives i+g = cnt-1,
-- LenPartitionRangeL moves the entry bound onto the partitioned list).
def SortRangeBL : Term := prog{
  λ (Lo : Nat). λ (Cnt'' : Nat). λ (L : List Nat). λ (Hb : Le (Add Lo (S (S Cnt''))) (Len L)).
    LeRwR (Add Lo (PartIdxRangeL Lo (S (S Cnt'')) L)) (Len L) (Len (PartitionRangeL Lo (S (S Cnt'')) L))
      (IdSym Nat (Len (PartitionRangeL Lo (S (S Cnt'')) L)) (Len L)
        (LenPartitionRangeL Lo (S (S Cnt'')) L))
      (LeTrans (Add Lo (PartIdxRangeL Lo (S (S Cnt'')) L)) (Add Lo (S (S Cnt''))) (Len L)
        (LeRwR (Add Lo (PartIdxRangeL Lo (S (S Cnt'')) L))
          (Add Lo (S (Add (PartIdxRangeL Lo (S (S Cnt'')) L) (PartGapRangeL Lo (S (S Cnt'')) L))))
          (Add Lo (S (S Cnt'')))
          (IdCongr Nat Nat (λ (A : Nat). Add Lo A)
            (S (Add (PartIdxRangeL Lo (S (S Cnt'')) L) (PartGapRangeL Lo (S (S Cnt'')) L))) (S (S Cnt''))
            (IdCongr Nat Nat (λ (A : Nat). S A)
              (Add (PartIdxRangeL Lo (S (S Cnt'')) L) (PartGapRangeL Lo (S (S Cnt'')) L)) (S Cnt'')
              (IdTrans Nat (Add (PartIdxRangeL Lo (S (S Cnt'')) L) (PartGapRangeL Lo (S (S Cnt'')) L))
                (S (Add Cnt'' Z)) (S Cnt'')
                (PartScanSizeL (NthL Lo L) Lo (S Cnt'') Z Z L)
                (IdCongr Nat Nat (λ (A : Nat). S A) (Add Cnt'' Z) Cnt'' (AddZero Cnt'')))))
          (LeAddMonoL Lo (PartIdxRangeL Lo (S (S Cnt'')) L)
            (S (Add (PartIdxRangeL Lo (S (S Cnt'')) L) (PartGapRangeL Lo (S (S Cnt'')) L)))
            (LeUpR (PartIdxRangeL Lo (S (S Cnt'')) L)
              (Add (PartIdxRangeL Lo (S (S Cnt'')) L) (PartGapRangeL Lo (S (S Cnt'')) L))
              (LeAdd (PartIdxRangeL Lo (S (S Cnt'')) L) (PartGapRangeL Lo (S (S Cnt'')) L)))))
        Hb) }
def SortRangeBLTy : Term := prog{
  Π (Lo : Nat) → Π (Cnt'' : Nat) → Π (L : List Nat) → Le (Add Lo (S (S Cnt''))) (Len L) →
    Le (Add Lo (PartIdxRangeL Lo (S (S Cnt'')) L)) (Len (PartitionRangeL Lo (S (S Cnt'')) L)) }

-- Right sub-range bound: `Le (Add (S (Add lo i)) g) (Len (sort left (partition …)))`.
-- Lifted verbatim from the quicksort FnDef's `br` (LenSortRangeL then
-- LenPartitionRangeL move the bound back over both mutations; the arithmetic
-- `Add (S (Add lo i)) g = Add lo (S (i+g)) = Add lo cnt` uses AddAssoc/AddSucc).
def SortRangeBR : Term := prog{
  λ (F' : Nat). λ (Lo : Nat). λ (Cnt'' : Nat). λ (L : List Nat). λ (Hb : Le (Add Lo (S (S Cnt''))) (Len L)).
    LeRwR (Add (S (Add Lo (PartIdxRangeL Lo (S (S Cnt'')) L))) (PartGapRangeL Lo (S (S Cnt'')) L)) (Len L)
      (Len (SortRangeL F' Lo (PartIdxRangeL Lo (S (S Cnt'')) L) (PartitionRangeL Lo (S (S Cnt'')) L)))
      (IdSym Nat (Len (SortRangeL F' Lo (PartIdxRangeL Lo (S (S Cnt'')) L) (PartitionRangeL Lo (S (S Cnt'')) L))) (Len L)
        (IdTrans Nat (Len (SortRangeL F' Lo (PartIdxRangeL Lo (S (S Cnt'')) L) (PartitionRangeL Lo (S (S Cnt'')) L)))
          (Len (PartitionRangeL Lo (S (S Cnt'')) L)) (Len L)
          (LenSortRangeL F' Lo (PartIdxRangeL Lo (S (S Cnt'')) L) (PartitionRangeL Lo (S (S Cnt'')) L))
          (LenPartitionRangeL Lo (S (S Cnt'')) L)))
      (LeRwL (Len L) (Add Lo (S (S Cnt'')))
        (Add (S (Add Lo (PartIdxRangeL Lo (S (S Cnt'')) L))) (PartGapRangeL Lo (S (S Cnt'')) L))
        (IdSym Nat (Add (S (Add Lo (PartIdxRangeL Lo (S (S Cnt'')) L))) (PartGapRangeL Lo (S (S Cnt'')) L)) (Add Lo (S (S Cnt'')))
          (IdTrans Nat (Add (S (Add Lo (PartIdxRangeL Lo (S (S Cnt'')) L))) (PartGapRangeL Lo (S (S Cnt'')) L))
            (S (Add Lo (Add (PartIdxRangeL Lo (S (S Cnt'')) L) (PartGapRangeL Lo (S (S Cnt'')) L)))) (Add Lo (S (S Cnt'')))
            (IdCongr Nat Nat (λ (A : Nat). S A)
              (Add (Add Lo (PartIdxRangeL Lo (S (S Cnt'')) L)) (PartGapRangeL Lo (S (S Cnt'')) L))
              (Add Lo (Add (PartIdxRangeL Lo (S (S Cnt'')) L) (PartGapRangeL Lo (S (S Cnt'')) L)))
              (AddAssoc Lo (PartIdxRangeL Lo (S (S Cnt'')) L) (PartGapRangeL Lo (S (S Cnt'')) L)))
            (IdTrans Nat (S (Add Lo (Add (PartIdxRangeL Lo (S (S Cnt'')) L) (PartGapRangeL Lo (S (S Cnt'')) L))))
              (Add Lo (S (Add (PartIdxRangeL Lo (S (S Cnt'')) L) (PartGapRangeL Lo (S (S Cnt'')) L)))) (Add Lo (S (S Cnt'')))
              (IdSym Nat (Add Lo (S (Add (PartIdxRangeL Lo (S (S Cnt'')) L) (PartGapRangeL Lo (S (S Cnt'')) L))))
                (S (Add Lo (Add (PartIdxRangeL Lo (S (S Cnt'')) L) (PartGapRangeL Lo (S (S Cnt'')) L))))
                (AddSucc Lo (Add (PartIdxRangeL Lo (S (S Cnt'')) L) (PartGapRangeL Lo (S (S Cnt'')) L))))
              (IdCongr Nat Nat (λ (A : Nat). Add Lo A)
                (S (Add (PartIdxRangeL Lo (S (S Cnt'')) L) (PartGapRangeL Lo (S (S Cnt'')) L))) (S (S Cnt''))
                (IdCongr Nat Nat (λ (A : Nat). S A)
                  (Add (PartIdxRangeL Lo (S (S Cnt'')) L) (PartGapRangeL Lo (S (S Cnt'')) L)) (S Cnt'')
                  (IdTrans Nat (Add (PartIdxRangeL Lo (S (S Cnt'')) L) (PartGapRangeL Lo (S (S Cnt'')) L))
                    (S (Add Cnt'' Z)) (S Cnt'')
                    (PartScanSizeL (NthL Lo L) Lo (S Cnt'') Z Z L)
                    (IdCongr Nat Nat (λ (A : Nat). S A) (Add Cnt'' Z) Cnt'' (AddZero Cnt''))))))))
        Hb) }
def SortRangeBRTy : Term := prog{
  Π (F' : Nat) → Π (Lo : Nat) → Π (Cnt'' : Nat) → Π (L : List Nat) → Le (Add Lo (S (S Cnt''))) (Len L) →
    Le (Add (S (Add Lo (PartIdxRangeL Lo (S (S Cnt'')) L))) (PartGapRangeL Lo (S (S Cnt'')) L))
       (Len (SortRangeL F' Lo (PartIdxRangeL Lo (S (S Cnt'')) L) (PartitionRangeL Lo (S (S Cnt'')) L))) }

def CountSortRangeL : Term := prog{
  λ (M : Nat). λ (Fuel : Nat).
    elim Fuel return (λ (Fz : Nat). Π (Lo : Nat) → Π (Cnt : Nat) → Π (L : List Nat) →
        Le (Add Lo Cnt) (Len L) → Id Nat (Count M (SortRangeL Fz Lo Cnt L)) (Count M L)) {
      Z => λ (Lo : Nat). λ (Cnt : Nat). λ (L : List Nat). λ (Hb : Le (Add Lo Cnt) (Len L)). Refl,
      S (F') Ih => λ (Lo : Nat). λ (Cnt : Nat). λ (L : List Nat).
        elim Cnt return (λ (Cz : Nat). Le (Add Lo Cz) (Len L) →
            Id Nat (Count M (SortRangeL (S F') Lo Cz L)) (Count M L)) {
          Z => λ (Hb : Le (Add Lo Z) (Len L)). Refl,
          S (Cnt') Nih => elim Cnt' return (λ (Cz' : Nat). Le (Add Lo (S Cz')) (Len L) →
              Id Nat (Count M (SortRangeL (S F') Lo (S Cz') L)) (Count M L)) {
            Z => λ (Hb : Le (Add Lo (S Z)) (Len L)). Refl,
            S (Cnt'') N2ih => λ (Hb : Le (Add Lo (S (S Cnt''))) (Len L)).
              IdTrans Nat
                (Count M (SortRangeL F' (S (Add Lo (PartIdxRangeL Lo (S (S Cnt'')) L))) (PartGapRangeL Lo (S (S Cnt'')) L)
                          (SortRangeL F' Lo (PartIdxRangeL Lo (S (S Cnt'')) L) (PartitionRangeL Lo (S (S Cnt'')) L))))
                (Count M (SortRangeL F' Lo (PartIdxRangeL Lo (S (S Cnt'')) L) (PartitionRangeL Lo (S (S Cnt'')) L)))
                (Count M L)
                (Ih (S (Add Lo (PartIdxRangeL Lo (S (S Cnt'')) L))) (PartGapRangeL Lo (S (S Cnt'')) L)
                    (SortRangeL F' Lo (PartIdxRangeL Lo (S (S Cnt'')) L) (PartitionRangeL Lo (S (S Cnt'')) L))
                    (SortRangeBR F' Lo Cnt'' L Hb))
                (IdTrans Nat
                  (Count M (SortRangeL F' Lo (PartIdxRangeL Lo (S (S Cnt'')) L) (PartitionRangeL Lo (S (S Cnt'')) L)))
                  (Count M (PartitionRangeL Lo (S (S Cnt'')) L))
                  (Count M L)
                  (Ih Lo (PartIdxRangeL Lo (S (S Cnt'')) L) (PartitionRangeL Lo (S (S Cnt'')) L)
                      (SortRangeBL Lo Cnt'' L Hb))
                  (CountPartitionRangeL Lo M (S (S Cnt'')) L Hb))
          }
        }
    } }
def CountSortRangeLTy : Term := prog{
  Π (M : Nat) → Π (Fuel : Nat) → Π (Lo : Nat) → Π (Cnt : Nat) → Π (L : List Nat) →
    Le (Add Lo Cnt) (Len L) → Id Nat (Count M (SortRangeL Fuel Lo Cnt L)) (Count M L) }

/-! ## Range-order predicates — the sortedness axis (§22, M22-c)

    AllLeR/AllGtR: the `w` positions [lo, lo+w) of `l` are all ≤ p (resp. > p). The
    ordering-relation-to-pivot the count models are blind to.

    ENCODING = bounded-Π, NOT a Σ-chain. Comptime Σ types can be CONSTRUCTED (Pair)
    but NOT ELIMINATED in a pure proof — `match` is runtime-only, and `elim` supports
    only the Nat/Bool/List recursors, so a conjunction-as-Σ can never be projected in
    a lemma. `Π (k : Nat) → Le (S k) w → Le (NthL (Add k lo) l) p` sidesteps that:
    eliminate by APPLICATION (`h k hk`), construct by LAMBDA. `Add k lo` (k first, not
    `Add lo k`) so the k=0 head reduces to `NthL lo l` definitionally (add Z lo = lo),
    avoiding an AddZero transport at every head extraction.

    NB the predicate FAMILY is not directly `chk`-able against `Π … → Type` (the M5
    limitation: hasType defers λ/neutral typing, so it can't type `Unit`/a neutral
    under the family's binders). This is not a defect in the predicate — it is only
    APPLIED forms that appear in lemma statements, and those reduce and check fine
    (exercised by AllLeRHead / AllLeREmpty below, both kernel-green). -/
def AllLeR : Term := prog{
  λ (W : Nat). λ (Lo : Nat). λ (P : Nat). λ (L : List Nat).
    Π (K : Nat) → Le (S K) W → Le (NthL (Add K Lo) L) P }
def AllGtR : Term := prog{
  λ (W : Nat). λ (Lo : Nat). λ (P : Nat). λ (L : List Nat).
    Π (K : Nat) → Le (S K) W → Le (S P) (NthL (Add K Lo) L) }

-- Head extraction: a width-(S w) AllLeR gives the bound at position lo (apply at
-- k=Z; Le (S Z)(S w) whnf's to ⊤, discharged by `unit`; add Z lo = lo).
def AllLeRHead : Term := prog{
  λ (W : Nat). λ (Lo : Nat). λ (P : Nat). λ (L : List Nat). λ (H : AllLeR (S W) Lo P L).
    H Z unit }
def AllLeRHeadTy : Term := prog{
  Π (W : Nat) → Π (Lo : Nat) → Π (P : Nat) → Π (L : List Nat) →
    AllLeR (S W) Lo P L → Le (NthL Lo L) P }
def AllGtRHead : Term := prog{
  λ (W : Nat). λ (Lo : Nat). λ (P : Nat). λ (L : List Nat). λ (H : AllGtR (S W) Lo P L).
    H Z unit }
def AllGtRHeadTy : Term := prog{
  Π (W : Nat) → Π (Lo : Nat) → Π (P : Nat) → Π (L : List Nat) →
    AllGtR (S W) Lo P L → Le (S P) (NthL Lo L) }

-- The empty range is vacuously bounded (Le (S k) Z = ⊥ ⇒ botElim).
def AllLeREmpty : Term := prog{
  λ (Lo : Nat). λ (P : Nat). λ (L : List Nat).
    λ (K : Nat). λ (Hk : Le (S K) Z). botElim (Le (NthL (Add K Lo) L) P) Hk }
def AllLeREmptyTy : Term := prog{
  Π (Lo : Nat) → Π (P : Nat) → Π (L : List Nat) → AllLeR Z Lo P L }
def AllGtREmpty : Term := prog{
  λ (Lo : Nat). λ (P : Nat). λ (L : List Nat).
    λ (K : Nat). λ (Hk : Le (S K) Z). botElim (Le (S P) (NthL (Add K Lo) L)) Hk }
def AllGtREmptyTy : Term := prog{
  Π (Lo : Nat) → Π (P : Nat) → Π (L : List Nat) → AllGtR Z Lo P L }

/-! ## Segment count — the multiset vehicle for perm-survival (§22, M22-c step 3)

    `SegCount x lo w l` = occurrences of x in positions [lo, lo+w) of l, as the count
    over the take/drop segment (reuses count/take/drop; preservation cribs count_* +
    CountAppend + TakeDropId). This is the perm-invariant twin the positional
    AllLeR is bridged to: the sort permutes the segment (SegCount preserved), so a
    positional bound over the segment survives the sort. Its preservation-under-the-
    model-functions and the model-function LOCALITY lemmas are the mechanical stratum. -/
def SegCount : Term := prog{
  λ (X : Nat). λ (Lo : Nat). λ (W : Nat). λ (L : List Nat).
    Count X (Take W (Drop Lo L)) }
def SegCountTy : Term := prog{ Π (X : Nat) → Π (Lo : Nat) → Π (W : Nat) → Π (L : List Nat) → Nat }

/-! ## Range sortedness (§22, M22-c step 4)

    SortedR w lo l: positions [lo, lo+w) are non-decreasing — for every adjacent pair
    (k, k+1) both inside the range (S(S k) ≤ w), nth(lo+k) ≤ nth(lo+k+1). Bounded-Π,
    same encoding as AllLeR/AllGtR (eliminate by application, construct by lambda;
    `Add k lo` / `Add (S k) lo` so k=0 reduces to nth lo / nth (S lo)). Width ≤ 1 is
    vacuously sorted. The glue lemma (SortedR left ∧ AllLeR left≤pivot ∧ AllGtR right>pivot
    ∧ SortedR right ⟹ SortedR whole) assembles on these; then SortedSortRangeL. -/
def SortedR : Term := prog{
  λ (W : Nat). λ (Lo : Nat). λ (L : List Nat).
    Π (K : Nat) → Le (S (S K)) W → Le (NthL (Add K Lo) L) (NthL (Add (S K) Lo) L) }

-- Head adjacent-bound from a width-(S (S w)) SortedR (apply at k=Z).
def SortedRHead : Term := prog{
  λ (W : Nat). λ (Lo : Nat). λ (L : List Nat). λ (H : SortedR (S (S W)) Lo L).
    H Z unit }
def SortedRHeadTy : Term := prog{
  Π (W : Nat) → Π (Lo : Nat) → Π (L : List Nat) →
    SortedR (S (S W)) Lo L → Le (NthL Lo L) (NthL (S Lo) L) }

-- Width 0 and width 1 are vacuously sorted (Le (S (S k)) (Z / S Z) = ⊥ ⇒ botElim).
def SortedRZero : Term := prog{
  λ (Lo : Nat). λ (L : List Nat).
    λ (K : Nat). λ (Hk : Le (S (S K)) Z). botElim (Le (NthL (Add K Lo) L) (NthL (Add (S K) Lo) L)) Hk }
def SortedRZeroTy : Term := prog{
  Π (Lo : Nat) → Π (L : List Nat) → SortedR Z Lo L }
def SortedROne : Term := prog{
  λ (Lo : Nat). λ (L : List Nat).
    λ (K : Nat). λ (Hk : Le (S (S K)) (S Z)). botElim (Le (NthL (Add K Lo) L) (NthL (Add (S K) Lo) L)) Hk }
def SortedROneTy : Term := prog{
  Π (Lo : Nat) → Π (L : List Nat) → SortedR (S Z) Lo L }

/-! ## leb ↔ Le bridges (§22, M22-c) — the Bool-comparison / order-proposition link

    The model functions branch on `Leb` (a Bool); the predicates carry `Le` (a
    proposition). These bridge the two — needed both for the partition INVARIANT
    (the scan's leb tests become AllLeR/AllGtR facts) and the GLUE (its k-vs-i
    trichotomy is a leb case-split whose branches yield the Le adjacency facts).
    `Leb` and `Le` share the same double recursion, so each bridge is a double
    induction with a Bool-DISCRIMINATE at the mismatched base (BoolFT/BoolTF:
    False ≠ True, by transporting `unit` along the false equation to `⊥`). -/
def BoolFT : Term := prog{
  λ (H : Id Bool False True).
    j Bool False (λ (Y' : Bool). λ (Hh : Id Bool False Y'). elim Y' return (λ (Z0 : Bool). Type) { True => Bot, False => Unit })
      unit True H }
def BoolFTTy : Term := prog{ Id Bool False True → Bot }
def BoolTF : Term := prog{
  λ (H : Id Bool True False).
    j Bool True (λ (Y' : Bool). λ (Hh : Id Bool True Y'). elim Y' return (λ (Z0 : Bool). Type) { True => Unit, False => Bot })
      unit False H }
def BoolTFTy : Term := prog{ Id Bool True False → Bot }

def LebTrueLe : Term := prog{
  λ (A : Nat).
    elim A return (λ (Az : Nat). Π (B : Nat) → Id Bool (Leb Az B) True → Le Az B) {
      Z => λ (B : Nat). λ (H : Id Bool (Leb Z B) True). unit,
      S (A') Ih => λ (B : Nat).
        elim B return (λ (Bz : Nat). Id Bool (Leb (S A') Bz) True → Le (S A') Bz) {
          Z => λ (H : Id Bool (Leb (S A') Z) True). botElim (Le (S A') Z) (BoolFT H),
          S (B') Ihb => λ (H : Id Bool (Leb (S A') (S B')) True). Ih B' H } } }
def LebTrueLeTy : Term := prog{ Π (A : Nat) → Π (B : Nat) → Id Bool (Leb A B) True → Le A B }

def LebFalseGt : Term := prog{
  λ (A : Nat).
    elim A return (λ (Az : Nat). Π (B : Nat) → Id Bool (Leb Az B) False → Le (S B) Az) {
      Z => λ (B : Nat). λ (H : Id Bool (Leb Z B) False). botElim (Le (S B) Z) (BoolTF H),
      S (A') Ih => λ (B : Nat).
        elim B return (λ (Bz : Nat). Id Bool (Leb (S A') Bz) False → Le (S Bz) (S A')) {
          Z => λ (H : Id Bool (Leb (S A') Z) False). unit,
          S (B') Ihb => λ (H : Id Bool (Leb (S A') (S B')) False). Ih B' H } } }
def LebFalseGtTy : Term := prog{ Π (A : Nat) → Π (B : Nat) → Id Bool (Leb A B) False → Le (S B) A }

-- Nat antisymmetry (Le a b → Le b a → a = b) — the glue derives its boundary equality
-- (`S k = i` at the last-left/pivot pair) from the two-sided Le bounds a leb-split
-- yields. Double induction; mixed-parity bases are ⊥, equal-parity step is IdCongr S.
def LeAntisym : Term := prog{
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
def LeAntisymTy : Term := prog{ Π (A : Nat) → Π (B : Nat) → Le A B → Le B A → Id Nat A B }

/-! ## AllLeR growth/transport helpers — the region-invariant toolkit (§22, M22-c step 2)

    The partition-invariant proofs thread an AllLeR precondition that GROWS each scan
    step. `AllLeRExtendFar` appends the newly-tested ≤-element at the far end — the
    only place the `m<w` vs `m=w` decision is needed, discharged by leb (remember
    scrutinee) + LebTrueLe/LebFalseGt + LeAntisym. `AllLeRExtendLo` prepends the
    pivot at position lo, absorbing the index-first offset shift `add m (S lo) = add (S
    m) lo` (AddSucc). `AllLeRCong` transports an AllLeR across a pointwise nth-equality
    (fed by the swap-locality lemmas). `AddSwapSucc` bridges index-first `Add a (S b)`
    to `Add b (S a)` — the recurring predicate↔model add-order glue. -/

def AllLeRExtendFar : Term := prog{
  λ (W : Nat). λ (Lo : Nat). λ (P : Nat). λ (L : List Nat).
    λ (H : AllLeR W Lo P L). λ (Hnew : Le (NthL (Add W Lo) L) P).
    λ (M : Nat).
      elim (Leb (S M) W) return (λ (B : Bool). Id Bool (Leb (S M) W) B → Le (S M) (S W) → Le (NthL (Add M Lo) L) P) {
        True => λ (E : Id Bool (Leb (S M) W) True). λ (Hm : Le (S M) (S W)). H M (LebTrueLe (S M) W E),
        False => λ (E : Id Bool (Leb (S M) W) False). λ (Hm : Le (S M) (S W)).
          LeRwL P (NthL (Add W Lo) L) (NthL (Add M Lo) L)
            (IdCongr Nat Nat (λ (Q : Nat). NthL Q L) (Add W Lo) (Add M Lo)
              (IdCongr Nat Nat (λ (Z0 : Nat). Add Z0 Lo) W M (IdSym Nat M W (LeAntisym M W Hm (LebFalseGt (S M) W E)))))
            Hnew
      } Refl }
def AllLeRExtendFarTy : Term := prog{
  Π (W : Nat) → Π (Lo : Nat) → Π (P : Nat) → Π (L : List Nat) →
    AllLeR W Lo P L → Le (NthL (Add W Lo) L) P → AllLeR (S W) Lo P L }

def AllLeRExtendLo : Term := prog{
  λ (W : Nat). λ (Lo : Nat). λ (P : Nat). λ (L : List Nat).
    λ (H0 : Le (NthL Lo L) P). λ (H : AllLeR W (S Lo) P L).
    λ (M : Nat).
      elim M return (λ (Mz : Nat). Le (S Mz) (S W) → Le (NthL (Add Mz Lo) L) P) {
        Z => λ (Hm : Le (S Z) (S W)). H0,
        S (M') Mih => λ (Hm : Le (S (S M')) (S W)).
          LeRwL P (NthL (Add M' (S Lo)) L) (NthL (Add (S M') Lo) L)
            (IdCongr Nat Nat (λ (Q : Nat). NthL Q L) (Add M' (S Lo)) (Add (S M') Lo) (AddSucc M' Lo))
            (H M' Hm) } }
def AllLeRExtendLoTy : Term := prog{
  Π (W : Nat) → Π (Lo : Nat) → Π (P : Nat) → Π (L : List Nat) →
    Le (NthL Lo L) P → AllLeR W (S Lo) P L → AllLeR (S W) Lo P L }

def AllLeRCong : Term := prog{
  λ (W : Nat). λ (Off : Nat). λ (P : Nat). λ (L : List Nat). λ (L' : List Nat).
    λ (Heq : Π (M : Nat) → Le (S M) W → Id Nat (NthL (Add M Off) L') (NthL (Add M Off) L)).
    λ (H : AllLeR W Off P L).
    λ (M : Nat). λ (Hm : Le (S M) W).
      LeRwL P (NthL (Add M Off) L) (NthL (Add M Off) L')
        (IdSym Nat (NthL (Add M Off) L') (NthL (Add M Off) L) (Heq M Hm))
        (H M Hm) }
def AllLeRCongTy : Term := prog{
  Π (W : Nat) → Π (Off : Nat) → Π (P : Nat) → Π (L : List Nat) → Π (L' : List Nat) →
    (Π (M : Nat) → Le (S M) W → Id Nat (NthL (Add M Off) L') (NthL (Add M Off) L)) →
    AllLeR W Off P L → AllLeR W Off P L' }

def AddSwapSucc : Term := prog{
  λ (A : Nat). λ (B : Nat).
    IdTrans Nat (Add A (S B)) (S (Add A B)) (Add B (S A))
      (AddSucc A B)
      (IdTrans Nat (S (Add A B)) (S (Add B A)) (Add B (S A))
        (IdCongr Nat Nat (λ (Z0 : Nat). S Z0) (Add A B) (Add B A) (AddComm A B))
        (IdSym Nat (Add B (S A)) (S (Add B A)) (AddSucc B A))) }
def AddSwapSuccTy : Term := prog{ Π (A : Nat) → Π (B : Nat) → Id Nat (Add A (S B)) (Add B (S A)) }

-- Left cancellation (Le (add a b)(add a c) → Le b c) — the glue's pivot-right case
-- derives g ≥ 1 (Le (S Z) g) from the range bound Le (S i)(add i g) by cancelling i
-- (after bridging S i = add i (S Z) via AddSucc/AddZero). Induction on a.
def LeAddCancelL : Term := prog{
  λ (A : Nat).
    elim A return (λ (Az : Nat). Π (B : Nat) → Π (C : Nat) → Le (Add Az B) (Add Az C) → Le B C) {
      Z => λ (B : Nat). λ (C : Nat). λ (H : Le (Add Z B) (Add Z C)). H,
      S (A') Ih => λ (B : Nat). λ (C : Nat). λ (H : Le (Add (S A') B) (Add (S A') C)). Ih B C H } }
def LeAddCancelLTy : Term := prog{
  Π (A : Nat) → Π (B : Nat) → Π (C : Nat) → Le (Add A B) (Add A C) → Le B C }
/-! ## `NthL`-under-`SwapL` locality — the positional stratum (§22, M22-c)

    Where `CountSwapL` says the swap preserves the MULTISET, these say WHERE each
    position lands, which the SegCount/locality argument (and the sortedness half)
    reads directly. `SwapL i j` (with the smaller index first) touches ONLY
    positions `i` and `j`: position `i` receives old `j` (`NthSwapLLo`), position
    `j` receives old `i` (`NthSwapLHi`), and every position `k` OUTSIDE `{i,j}` is
    unchanged. The "outside" atom is split into the two directions the range scan's
    locality actually needs — `k < i` (`NthSwapLLt`, below both indices since
    `i ≤ j`) and `k > j` (`NthSwapLGt`, above both) — each stated with a SINGLE
    honest `Le` bound, so a caller reasoning about a below-range or above-range
    position cites exactly one of them. The middle band `i < k < j` is also
    untouched but is not needed downstream, so it is left unstated (it would need
    the two-sided bound `Le (S i) k → Le (S k) j`).

    BOUNDS (verified computationally, minimal):
    - `NthSwapLLt` needs ONLY `Le (S k) i` (the `l = Nil` and `j = Z` leaves are
      `Refl`, not bound-discharged — off the end both sides degrade to the same
      stuck `NthL k Nil`).
    - `NthSwapLGt` needs ONLY `Le (S j) k` (below-`j` positions in the set-branch
      are handled by `NthSetGt`).
    - `NthSwapLLo` needs ONLY `Le (S i) j` — NO length bound: off the end the swap
      writes `NthL j l = Z` at `i`, so both sides read `Z` consistently. The `Nil`
      leaves case `j` (so the stuck `NthL j Nil` reduces to `Z` on both sides).
    - `NthSwapLHi` needs BOTH `Le (S i) j` and `Le (S j) (Len l)` — the base case
      reads `NthL j (Set j x xs) = x` (`NthSetSame`), which is FALSE off the end, so
      the length bound is load-bearing (discharges the `Nil` leaf as `botElim` and
      feeds `NthSetSame`).

    Two `Set` helpers underneath: `NthSetGt` (`NthL` past the written index is
    unchanged, bound `Le (S j) k`) and `NthSetSame` (`NthL k (Set k v l) = v` in
    range, bound `Le (S k) (Len l)`). -/

-- `NthL k (Set j v l) = NthL k l` for k strictly above the written index j.
def NthSetGt : Term := prog{
  λ (V : Nat). λ (J : Nat).
    elim J return (λ (Jz : Nat). Π (K : Nat) → Π (L : List Nat) → Le (S Jz) K → Id Nat (NthL K (Set Jz V L)) (NthL K L)) {
      Z => λ (K : Nat). λ (L : List Nat). λ (H : Le (S Z) K).
        elim K return (λ (Kz : Nat). Le (S Z) Kz → Id Nat (NthL Kz (Set Z V L)) (NthL Kz L)) {
          Z => λ (H0 : Le (S Z) Z). botElim (Id Nat (NthL Z (Set Z V L)) (NthL Z L)) H0,
          S (K') Kih => λ (H0 : Le (S Z) (S K')).
            elim L return (λ (Lz : List Nat). Id Nat (NthL (S K') (Set Z V Lz)) (NthL (S K') Lz)) {
              Nil => Refl,
              Cons (Hh) (Tt) Ihl => Refl } } H,
      S (J') Ih => λ (K : Nat). λ (L : List Nat). λ (H : Le (S (S J')) K).
        elim K return (λ (Kz : Nat). Le (S (S J')) Kz → Id Nat (NthL Kz (Set (S J') V L)) (NthL Kz L)) {
          Z => λ (H0 : Le (S (S J')) Z). botElim (Id Nat (NthL Z (Set (S J') V L)) (NthL Z L)) H0,
          S (K') Kih => λ (H0 : Le (S (S J')) (S K')).
            elim L return (λ (Lz : List Nat). Id Nat (NthL (S K') (Set (S J') V Lz)) (NthL (S K') Lz)) {
              Nil => Refl,
              Cons (Hh) (Tt) Ihl => Ih K' Tt H0 } } H } }
def NthSetGtTy : Term := prog{
  Π (V : Nat) → Π (J : Nat) → Π (K : Nat) → Π (L : List Nat) →
    Le (S J) K → Id Nat (NthL K (Set J V L)) (NthL K L) }

-- `NthL k (Set k v l) = v` when k is in range (off the end set no-ops, giving Z ≠ v).
def NthSetSame : Term := prog{
  λ (V : Nat). λ (K : Nat).
    elim K return (λ (Kz : Nat). Π (L : List Nat) → Le (S Kz) (Len L) → Id Nat (NthL Kz (Set Kz V L)) V) {
      Z => λ (L : List Nat).
        elim L return (λ (Lz : List Nat). Le (S Z) (Len Lz) → Id Nat (NthL Z (Set Z V Lz)) V) {
          Nil => λ (H : Le (S Z) (Len Nil)). botElim (Id Nat (NthL Z (Set Z V Nil)) V) H,
          Cons (Hh) (Tt) Ihl => λ (H : Le (S Z) (Len (Cons Hh Tt))). Refl },
      S (K') Ih => λ (L : List Nat).
        elim L return (λ (Lz : List Nat). Le (S (S K')) (Len Lz) → Id Nat (NthL (S K') (Set (S K') V Lz)) V) {
          Nil => λ (H : Le (S (S K')) (Len Nil)). botElim (Id Nat (NthL (S K') (Set (S K') V Nil)) V) H,
          Cons (Hh) (Tt) Ihl => λ (H : Le (S (S K')) (Len (Cons Hh Tt))). Ih Tt H } } }
def NthSetSameTy : Term := prog{
  Π (V : Nat) → Π (K : Nat) → Π (L : List Nat) →
    Le (S K) (Len L) → Id Nat (NthL K (Set K V L)) V }

-- Locality below the swap: positions `k < i` are untouched by `SwapL i j`. Induct
-- on i (mirroring SwapL); i = Z is vacuous (Le (S k) Z = ⊥); the recursive leaf is
-- the IH under `Cons x ·`, the j = Z / head leaves are Refl.
def NthSwapLLt : Term := prog{
  λ (I : Nat).
    elim I return (λ (Iz : Nat). Π (J : Nat) → Π (K : Nat) → Π (L : List Nat) → Le (S K) Iz → Id Nat (NthL K (SwapL Iz J L)) (NthL K L)) {
      Z => λ (J : Nat). λ (K : Nat). λ (L : List Nat). λ (H : Le (S K) Z).
        botElim (Id Nat (NthL K (SwapL Z J L)) (NthL K L)) H,
      S (I') Ih => λ (J : Nat). λ (K : Nat). λ (L : List Nat). λ (H : Le (S K) (S I')).
        elim L return (λ (Lz : List Nat). Id Nat (NthL K (SwapL (S I') J Lz)) (NthL K Lz)) {
          Nil => Refl,
          Cons (X) (Xs) Ihl =>
            elim J return (λ (Jz : Nat). Id Nat (NthL K (SwapL (S I') Jz (Cons X Xs))) (NthL K (Cons X Xs))) {
              Z => Refl,
              S (J') Jih =>
                elim K return (λ (Kz : Nat). Le (S Kz) (S I') → Id Nat (NthL Kz (Cons X (SwapL I' J' Xs))) (NthL Kz (Cons X Xs))) {
                  Z => λ (H0 : Le (S Z) (S I')). Refl,
                  S (K') Kih => λ (H0 : Le (S (S K')) (S I')). Ih J' K' Xs H0 } H } } } }
def NthSwapLLtTy : Term := prog{
  Π (I : Nat) → Π (J : Nat) → Π (K : Nat) → Π (L : List Nat) →
    Le (S K) I → Id Nat (NthL K (SwapL I J L)) (NthL K L) }

-- Locality above the swap: positions `k > j` are untouched by `SwapL i j`. Induct
-- on i; the i = Z / j = S j' leaf floats through the set-branch via `NthSetGt`,
-- the i = S i' / j = S j' leaf is the IH, the j = Z / Nil leaves are Refl.
def NthSwapLGt : Term := prog{
  λ (I : Nat).
    elim I return (λ (Iz : Nat). Π (J : Nat) → Π (K : Nat) → Π (L : List Nat) → Le (S J) K → Id Nat (NthL K (SwapL Iz J L)) (NthL K L)) {
      Z => λ (J : Nat). λ (K : Nat). λ (L : List Nat). λ (H : Le (S J) K).
        elim L return (λ (Lz : List Nat). Id Nat (NthL K (SwapL Z J Lz)) (NthL K Lz)) {
          Nil => Refl,
          Cons (X) (Xs) Ihl =>
            elim J return (λ (Jz : Nat). Le (S Jz) K → Id Nat (NthL K (SwapL Z Jz (Cons X Xs))) (NthL K (Cons X Xs))) {
              Z => λ (H0 : Le (S Z) K). Refl,
              S (J') Jih => λ (H0 : Le (S (S J')) K).
                elim K return (λ (Kz : Nat). Le (S (S J')) Kz → Id Nat (NthL Kz (Cons (NthL J' Xs) (Set J' X Xs))) (NthL Kz (Cons X Xs))) {
                  Z => λ (H1 : Le (S (S J')) Z). botElim (Id Nat (NthL Z (Cons (NthL J' Xs) (Set J' X Xs))) (NthL Z (Cons X Xs))) H1,
                  S (K') Kih => λ (H1 : Le (S (S J')) (S K')). NthSetGt X J' K' Xs H1 } H0 } H },
      S (I') Ih => λ (J : Nat). λ (K : Nat). λ (L : List Nat). λ (H : Le (S J) K).
        elim L return (λ (Lz : List Nat). Id Nat (NthL K (SwapL (S I') J Lz)) (NthL K Lz)) {
          Nil => Refl,
          Cons (X) (Xs) Ihl =>
            elim J return (λ (Jz : Nat). Le (S Jz) K → Id Nat (NthL K (SwapL (S I') Jz (Cons X Xs))) (NthL K (Cons X Xs))) {
              Z => λ (H0 : Le (S Z) K). Refl,
              S (J') Jih => λ (H0 : Le (S (S J')) K).
                elim K return (λ (Kz : Nat). Le (S (S J')) Kz → Id Nat (NthL Kz (Cons X (SwapL I' J' Xs))) (NthL Kz (Cons X Xs))) {
                  Z => λ (H1 : Le (S (S J')) Z). botElim (Id Nat (NthL Z (Cons X (SwapL I' J' Xs))) (NthL Z (Cons X Xs))) H1,
                  S (K') Kih => λ (H1 : Le (S (S J')) (S K')). Ih J' K' Xs H1 } H0 } H } } }
def NthSwapLGtTy : Term := prog{
  Π (I : Nat) → Π (J : Nat) → Π (K : Nat) → Π (L : List Nat) →
    Le (S J) K → Id Nat (NthL K (SwapL I J L)) (NthL K L) }

-- The lower endpoint: position i of `SwapL i j l` reads old position j. Induct on
-- i; the recursive leaf is the IH under `Cons x ·`. NO length bound — off the end
-- the swap writes `NthL j l = Z` at i, so both sides read Z consistently; the Nil
-- leaves case j so the stuck `NthL j Nil` reduces to Z on both sides, and the j = Z
-- leaf (impossible with i ≥ 1) is the sole botElim, discharged by `Le (S i) j`.
def NthSwapLLo : Term := prog{
  λ (I : Nat).
    elim I return (λ (Iz : Nat). Π (J : Nat) → Π (L : List Nat) → Le (S Iz) J → Id Nat (NthL Iz (SwapL Iz J L)) (NthL J L)) {
      Z => λ (J : Nat). λ (L : List Nat). λ (H : Le (S Z) J).
        elim L return (λ (Lz : List Nat). Id Nat (NthL Z (SwapL Z J Lz)) (NthL J Lz)) {
          Nil => elim J return (λ (Jz : Nat). Id Nat (NthL Z (SwapL Z Jz Nil)) (NthL Jz Nil)) {
            Z => Refl, S (J') Jih => Refl },
          Cons (X) (Xs) Ihl =>
            elim J return (λ (Jz : Nat). Le (S Z) Jz → Id Nat (NthL Z (SwapL Z Jz (Cons X Xs))) (NthL Jz (Cons X Xs))) {
              Z => λ (H0 : Le (S Z) Z). botElim (Id Nat (NthL Z (SwapL Z Z (Cons X Xs))) (NthL Z (Cons X Xs))) H0,
              S (J') Jih => λ (H0 : Le (S Z) (S J')). Refl } H },
      S (I') Ih => λ (J : Nat). λ (L : List Nat). λ (H : Le (S (S I')) J).
        elim L return (λ (Lz : List Nat). Id Nat (NthL (S I') (SwapL (S I') J Lz)) (NthL J Lz)) {
          Nil => elim J return (λ (Jz : Nat). Id Nat (NthL (S I') (SwapL (S I') Jz Nil)) (NthL Jz Nil)) {
            Z => Refl, S (J') Jih => Refl },
          Cons (X) (Xs) Ihl =>
            elim J return (λ (Jz : Nat). Le (S (S I')) Jz → Id Nat (NthL (S I') (SwapL (S I') Jz (Cons X Xs))) (NthL Jz (Cons X Xs))) {
              Z => λ (H0 : Le (S (S I')) Z). botElim (Id Nat (NthL (S I') (SwapL (S I') Z (Cons X Xs))) (NthL Z (Cons X Xs))) H0,
              S (J') Jih => λ (H0 : Le (S (S I')) (S J')). Ih J' Xs H0 } H } } }
def NthSwapLLoTy : Term := prog{
  Π (I : Nat) → Π (J : Nat) → Π (L : List Nat) →
    Le (S I) J → Id Nat (NthL I (SwapL I J L)) (NthL J L) }

-- The upper endpoint: position j of `SwapL i j l` reads old position i. Induct on
-- i; the base (i = Z) reads `NthL j (Set j x xs) = x` via `NthSetSame`, so the
-- length bound `Le (S j) (Len l)` is load-bearing here (botElims the Nil leaf and
-- feeds NthSetSame) — UNLIKE _lo. The recursive leaf is the IH under `Cons x ·`,
-- threading both bounds; the j = Z leaf is botElim by `Le (S i) j`.
def NthSwapLHi : Term := prog{
  λ (I : Nat).
    elim I return (λ (Iz : Nat). Π (J : Nat) → Π (L : List Nat) → Le (S Iz) J → Le (S J) (Len L) → Id Nat (NthL J (SwapL Iz J L)) (NthL Iz L)) {
      Z => λ (J : Nat). λ (L : List Nat). λ (H1 : Le (S Z) J). λ (H2 : Le (S J) (Len L)).
        elim L return (λ (Lz : List Nat). Le (S J) (Len Lz) → Id Nat (NthL J (SwapL Z J Lz)) (NthL Z Lz)) {
          Nil => λ (A2 : Le (S J) (Len Nil)).
            botElim (Id Nat (NthL J (SwapL Z J Nil)) (NthL Z Nil)) A2,
          Cons (X) (Xs) Ihl => λ (A2 : Le (S J) (Len (Cons X Xs))).
            elim J return (λ (Jz : Nat). Le (S Z) Jz → Le (S Jz) (Len (Cons X Xs)) → Id Nat (NthL Jz (SwapL Z Jz (Cons X Xs))) (NthL Z (Cons X Xs))) {
              Z => λ (B1 : Le (S Z) Z). λ (B2 : Le (S Z) (Len (Cons X Xs))).
                botElim (Id Nat (NthL Z (SwapL Z Z (Cons X Xs))) (NthL Z (Cons X Xs))) B1,
              S (J') Jih => λ (B1 : Le (S Z) (S J')). λ (B2 : Le (S (S J')) (Len (Cons X Xs))).
                NthSetSame X J' Xs B2 } H1 A2 } H2,
      S (I') Ih => λ (J : Nat). λ (L : List Nat). λ (H1 : Le (S (S I')) J). λ (H2 : Le (S J) (Len L)).
        elim L return (λ (Lz : List Nat). Le (S J) (Len Lz) → Id Nat (NthL J (SwapL (S I') J Lz)) (NthL (S I') Lz)) {
          Nil => λ (A2 : Le (S J) (Len Nil)).
            botElim (Id Nat (NthL J (SwapL (S I') J Nil)) (NthL (S I') Nil)) A2,
          Cons (X) (Xs) Ihl => λ (A2 : Le (S J) (Len (Cons X Xs))).
            elim J return (λ (Jz : Nat). Le (S (S I')) Jz → Le (S Jz) (Len (Cons X Xs)) → Id Nat (NthL Jz (SwapL (S I') Jz (Cons X Xs))) (NthL (S I') (Cons X Xs))) {
              Z => λ (B1 : Le (S (S I')) Z). λ (B2 : Le (S Z) (Len (Cons X Xs))).
                botElim (Id Nat (NthL Z (SwapL (S I') Z (Cons X Xs))) (NthL (S I') (Cons X Xs))) B1,
              S (J') Jih => λ (B1 : Le (S (S I')) (S J')). λ (B2 : Le (S (S J')) (Len (Cons X Xs))).
                Ih J' Xs B1 B2 } H1 A2 } H2 } }
def NthSwapLHiTy : Term := prog{
  Π (I : Nat) → Π (J : Nat) → Π (L : List Nat) →
    Le (S I) J → Le (S J) (Len L) → Id Nat (NthL J (SwapL I J L)) (NthL I L) }

-- `NthL k (Set j v l) = NthL k l` for k strictly BELOW the written index j (mirror of
-- NthSetGt). The below-index companion the partition-invariant base case needs.
def NthSetLt : Term := prog{
  λ (V : Nat). λ (J : Nat).
    elim J return (λ (Jz : Nat). Π (K : Nat) → Π (L : List Nat) → Le (S K) Jz → Id Nat (NthL K (Set Jz V L)) (NthL K L)) {
      Z => λ (K : Nat). λ (L : List Nat). λ (H : Le (S K) Z). botElim (Id Nat (NthL K (Set Z V L)) (NthL K L)) H,
      S (J') Ih => λ (K : Nat). λ (L : List Nat). λ (H : Le (S K) (S J')).
        elim K return (λ (Kz : Nat). Le (S Kz) (S J') → Id Nat (NthL Kz (Set (S J') V L)) (NthL Kz L)) {
          Z => λ (H0 : Le (S Z) (S J')).
            elim L return (λ (Lz : List Nat). Id Nat (NthL Z (Set (S J') V Lz)) (NthL Z Lz)) {
              Nil => Refl,
              Cons (Hh) (Tt) Ihl => Refl },
          S (K') Kih => λ (H0 : Le (S (S K')) (S J')).
            elim L return (λ (Lz : List Nat). Id Nat (NthL (S K') (Set (S J') V Lz)) (NthL (S K') Lz)) {
              Nil => Refl,
              Cons (Hh) (Tt) Ihl => Ih K' Tt H0 } } H } }
def NthSetLtTy : Term := prog{
  Π (V : Nat) → Π (J : Nat) → Π (K : Nat) → Π (L : List Nat) →
    Le (S K) J → Id Nat (NthL K (Set J V L)) (NthL K L) }

-- The MIDDLE band left unstated in Step A: positions strictly between i and j are
-- untouched by `SwapL i j` (two-sided bound). Induction on i mirroring SwapL; the
-- i=Z base floats through the set-branch via NthSetLt, the recursive leaf is the IH.
def NthSwapLMid : Term := prog{
  λ (I : Nat).
    elim I return (λ (Iz : Nat). Π (J : Nat) → Π (K : Nat) → Π (L : List Nat) → Le (S Iz) K → Le (S K) J → Id Nat (NthL K (SwapL Iz J L)) (NthL K L)) {
      Z => λ (J : Nat). λ (K : Nat). λ (L : List Nat). λ (Hik : Le (S Z) K). λ (Hkj : Le (S K) J).
        elim L return (λ (Lz : List Nat). Id Nat (NthL K (SwapL Z J Lz)) (NthL K Lz)) {
          Nil => Refl,
          Cons (X) (Xs) Ihl =>
            elim J return (λ (Jz : Nat). Le (S K) Jz → Id Nat (NthL K (SwapL Z Jz (Cons X Xs))) (NthL K (Cons X Xs))) {
              Z => λ (Hkj0 : Le (S K) Z). botElim (Id Nat (NthL K (SwapL Z Z (Cons X Xs))) (NthL K (Cons X Xs))) Hkj0,
              S (J') Jih => λ (Hkj0 : Le (S K) (S J')).
                elim K return (λ (Kz : Nat). Le (S Z) Kz → Le (S Kz) (S J') → Id Nat (NthL Kz (Cons (NthL J' Xs) (Set J' X Xs))) (NthL Kz (Cons X Xs))) {
                  Z => λ (Hik1 : Le (S Z) Z). λ (Hkj1 : Le (S Z) (S J')). botElim (Id Nat (NthL Z (Cons (NthL J' Xs) (Set J' X Xs))) (NthL Z (Cons X Xs))) Hik1,
                  S (K') Kih => λ (Hik1 : Le (S Z) (S K')). λ (Hkj1 : Le (S (S K')) (S J')).
                    NthSetLt X J' K' Xs Hkj1 } Hik Hkj0 } Hkj },
      S (I') Ih => λ (J : Nat). λ (K : Nat). λ (L : List Nat). λ (Hik : Le (S (S I')) K). λ (Hkj : Le (S K) J).
        elim L return (λ (Lz : List Nat). Id Nat (NthL K (SwapL (S I') J Lz)) (NthL K Lz)) {
          Nil => Refl,
          Cons (X) (Xs) Ihl =>
            elim J return (λ (Jz : Nat). Le (S K) Jz → Id Nat (NthL K (SwapL (S I') Jz (Cons X Xs))) (NthL K (Cons X Xs))) {
              Z => λ (Hkj0 : Le (S K) Z). botElim (Id Nat (NthL K (SwapL (S I') Z (Cons X Xs))) (NthL K (Cons X Xs))) Hkj0,
              S (J') Jih => λ (Hkj0 : Le (S K) (S J')).
                elim K return (λ (Kz : Nat). Le (S (S I')) Kz → Le (S Kz) (S J') → Id Nat (NthL Kz (Cons X (SwapL I' J' Xs))) (NthL Kz (Cons X Xs))) {
                  Z => λ (Hik1 : Le (S (S I')) Z). λ (Hkj1 : Le (S Z) (S J')). botElim (Id Nat (NthL Z (Cons X (SwapL I' J' Xs))) (NthL Z (Cons X Xs))) Hik1,
                  S (K') Kih => λ (Hik1 : Le (S (S I')) (S K')). λ (Hkj1 : Le (S (S K')) (S J')).
                    Ih J' K' Xs Hik1 Hkj1 } Hik Hkj0 } Hkj } } }
def NthSwapLMidTy : Term := prog{
  Π (I : Nat) → Π (J : Nat) → Π (K : Nat) → Π (L : List Nat) →
    Le (S I) K → Le (S K) J → Id Nat (NthL K (SwapL I J L)) (NthL K L) }

/-! ## `NthL`-under-scan/partition LOCALITY — positions outside the range unchanged (§22)

    The range scan `PartScanRangeL pivot lo k i g` only ever swaps positions inside
    `[lo, lo + (k+i+g)]` (base places the pivot at `SwapL lo (lo+i)`; each step swaps
    at `lo+1+i` ↔ `lo+1+i+g`, all ≥ lo, ≤ the top). So a query position OUTSIDE that
    band is untouched, split (as with the swap crux) into the two directions the
    quicksort recursion consumes:

    - `_lt` : positions `j < lo` (below the range). Bound `Le (S j) lo`, INVARIANT
      across the recursion (bound outside the k-elim, no transport) — each scan swap
      is discharged by `NthSwapLLt` since j < lo ≤ every swap's smaller index.
    - `_ge` : positions `q ≥ lo+1+(k+i+g)` (at/above the scanned top). Bound
      `Le (Add lo (S (Add k (Add i g)))) q` — the SAME shifting invariant
      `CountPartScanRangeL` threads, but on a POSITION `q` instead of `Len l`, so it
      transports by the identical `hshift` congruences and, crucially, needs NO
      `LenSwapL` step (q is list-independent). Each swap discharged by `NthSwapLGt`.

    The `PartitionRangeL` wrappers pick the pivot then defer to the scan (the `_ge`
    bound becomes the clean `Le (Add lo cnt) q`, one `AddZero` nudge as in
    `CountPartitionRangeL`). Together `_lt` (j < lo) and `_ge` (q ≥ lo+cnt) cover
    everything OUTSIDE the operated range `[lo, lo+cnt)`. -/

-- Below-lo locality of the range scan. Bound `Le (S j) lo` is invariant (bound
-- outside the k-elim); each swap discharged by NthSwapLLt (j < lo ≤ swap index).
def NthPartScanRangeLLt : Term := prog{
  λ (Pivot : Nat). λ (Lo : Nat). λ (J : Nat). λ (Hlt : Le (S J) Lo). λ (K : Nat).
    elim K return (λ (Kz : Nat). Π (I : Nat) → Π (G : Nat) → Π (L : List Nat) → Id Nat (NthL J (PartScanRangeL Pivot Lo Kz I G L)) (NthL J L)) {
      Z => λ (I : Nat). λ (G : Nat). λ (L : List Nat).
        elim I return (λ (Iz : Nat). Id Nat (NthL J (elim Iz return (λ (Iy : Nat). List Nat) { Z => L, S (I') Iih => SwapL Lo (Add Lo (S I')) L })) (NthL J L)) {
          Z => Refl,
          S (I') Iih => NthSwapLLt Lo (Add Lo (S I')) J L Hlt },
      S (K') Ih => λ (I : Nat). λ (G : Nat). λ (L : List Nat).
        elim (Leb (NthL (Add Lo (S (Add I G))) L) Pivot)
          return (λ (W : Bool). Id Nat (NthL J (elim W return (λ (Ww : Bool). List Nat) {
              True => elim G return (λ (Gz : Nat). List Nat) {
                Z => PartScanRangeL Pivot Lo K' (S I) Z L,
                S (G') Gih => PartScanRangeL Pivot Lo K' (S I) (S G') (SwapL (Add Lo (S I)) (Add Lo (S (Add I G))) L) },
              False => PartScanRangeL Pivot Lo K' I (S G) L })) (NthL J L)) {
          True => elim G return (λ (Gz : Nat). Id Nat (NthL J (elim Gz return (λ (Gy : Nat). List Nat) {
                    Z => PartScanRangeL Pivot Lo K' (S I) Z L,
                    S (G') Gih => PartScanRangeL Pivot Lo K' (S I) (S G') (SwapL (Add Lo (S I)) (Add Lo (S (Add I G))) L) })) (NthL J L)) {
            Z => Ih (S I) Z L,
            S (G') Gih => IdTrans Nat
                   (NthL J (PartScanRangeL Pivot Lo K' (S I) (S G') (SwapL (Add Lo (S I)) (Add Lo (S (Add I G))) L)))
                   (NthL J (SwapL (Add Lo (S I)) (Add Lo (S (Add I G))) L))
                   (NthL J L)
                   (Ih (S I) (S G') (SwapL (Add Lo (S I)) (Add Lo (S (Add I G))) L))
                   (NthSwapLLt (Add Lo (S I)) (Add Lo (S (Add I G))) J L
                     (LeTrans (S J) Lo (Add Lo (S I)) Hlt (LeAdd Lo (S I))))
          },
          False => Ih I (S G) L
        }
    } }
def NthPartScanRangeLLtTy : Term := prog{
  Π (Pivot : Nat) → Π (Lo : Nat) → Π (J : Nat) → Le (S J) Lo → Π (K : Nat) → Π (I : Nat) → Π (G : Nat) → Π (L : List Nat) →
    Id Nat (NthL J (PartScanRangeL Pivot Lo K I G L)) (NthL J L) }

-- At/above-top locality of the range scan. Same threaded invariant as
-- CountPartScanRangeL but on position q, so hshift transports apply and NO
-- LenSwapL is needed; each swap discharged by NthSwapLGt.
def NthPartScanRangeLGe : Term := prog{
  λ (Pivot : Nat). λ (Lo : Nat). λ (Q : Nat). λ (K : Nat).
    elim K return (λ (Kz : Nat). Π (I : Nat) → Π (G : Nat) → Π (L : List Nat) →
        Le (Add Lo (S (Add Kz (Add I G)))) Q →
        Id Nat (NthL Q (PartScanRangeL Pivot Lo Kz I G L)) (NthL Q L)) {
      Z => λ (I : Nat). λ (G : Nat). λ (L : List Nat).
        elim I return (λ (Iz : Nat).
            Le (Add Lo (S (Add Z (Add Iz G)))) Q →
            Id Nat (NthL Q (elim Iz return (λ (Iy : Nat). List Nat) {
                Z => L, S (I') Iih => SwapL Lo (Add Lo (S I')) L })) (NthL Q L)) {
          Z => λ (Hle : Le (Add Lo (S (Add Z (Add Z G)))) Q). Refl,
          S (I') Iih => λ (Hle : Le (Add Lo (S (Add Z (Add (S I') G)))) Q).
            NthSwapLGt Lo (Add Lo (S I')) Q L
              (LeTrans (S (Add Lo (S I'))) (Add Lo (S (S (Add I' G)))) Q
                (LeRwL (Add Lo (S (S (Add I' G)))) (Add Lo (S (S I'))) (S (Add Lo (S I')))
                  (AddSucc Lo (S I'))
                  (LeAddMonoL Lo (S (S I')) (S (S (Add I' G))) (LeAdd I' G)))
                Hle)
        },
      S (K') Ih => λ (I : Nat). λ (G : Nat). λ (L : List Nat).
        λ (Hle : Le (Add Lo (S (Add (S K') (Add I G)))) Q).
        elim (Leb (NthL (Add Lo (S (Add I G))) L) Pivot)
          return (λ (W : Bool). Id Nat
            (NthL Q (elim W return (λ (Ww : Bool). List Nat) {
                True => elim G return (λ (Gz : Nat). List Nat) {
                  Z => PartScanRangeL Pivot Lo K' (S I) Z L,
                  S (G') Gih => PartScanRangeL Pivot Lo K' (S I) (S G') (SwapL (Add Lo (S I)) (Add Lo (S (Add I G))) L) },
                False => PartScanRangeL Pivot Lo K' I (S G) L }))
            (NthL Q L)) {
          True =>
            (elim G return (λ (Gz : Nat).
                Le (Add Lo (S (Add (S K') (Add I Gz)))) Q →
                Id Nat (NthL Q (elim Gz return (λ (Gy : Nat). List Nat) {
                    Z => PartScanRangeL Pivot Lo K' (S I) Z L,
                    S (G') Gih => PartScanRangeL Pivot Lo K' (S I) (S G') (SwapL (Add Lo (S I)) (Add Lo (S (Add I Gz))) L) })) (NthL Q L)) {
              Z => λ (HleZ : Le (Add Lo (S (Add (S K') (Add I Z)))) Q).
                Ih (S I) Z L
                  (LeRwL Q
                    (Add Lo (S (Add (S K') (Add I Z))))
                    (Add Lo (S (Add K' (Add (S I) Z))))
                    (IdCongr Nat Nat (λ (A : Nat). Add Lo (S A))
                      (Add (S K') (Add I Z)) (Add K' (Add (S I) Z)) (HshiftTrue K' I Z))
                    HleZ),
              S (G') Gih => λ (HleS : Le (Add Lo (S (Add (S K') (Add I (S G'))))) Q).
                IdTrans Nat
                  (NthL Q (PartScanRangeL Pivot Lo K' (S I) (S G') (SwapL (Add Lo (S I)) (Add Lo (S (Add I (S G')))) L)))
                  (NthL Q (SwapL (Add Lo (S I)) (Add Lo (S (Add I (S G')))) L))
                  (NthL Q L)
                  (Ih (S I) (S G') (SwapL (Add Lo (S I)) (Add Lo (S (Add I (S G')))) L)
                    (LeRwL Q
                      (Add Lo (S (Add (S K') (Add I (S G')))))
                      (Add Lo (S (Add K' (Add (S I) (S G')))))
                      (IdCongr Nat Nat (λ (A : Nat). Add Lo (S A))
                        (Add (S K') (Add I (S G'))) (Add K' (Add (S I) (S G'))) (HshiftTrue K' I (S G')))
                      HleS))
                  (NthSwapLGt (Add Lo (S I)) (Add Lo (S (Add I (S G')))) Q L
                    (LeTrans (S (Add Lo (S (Add I (S G'))))) (Add Lo (S (S (Add K' (Add I (S G')))))) Q
                      (LeRwL (Add Lo (S (S (Add K' (Add I (S G'))))))
                        (Add Lo (S (S (Add I (S G'))))) (S (Add Lo (S (Add I (S G')))))
                        (AddSucc Lo (S (Add I (S G'))))
                        (LeAddMonoL Lo (S (S (Add I (S G')))) (S (S (Add K' (Add I (S G')))))
                          (LeAddL (Add I (S G')) K')))
                      HleS))
            }) Hle,
          False =>
            Ih I (S G) L
              (LeRwL Q
                (Add Lo (S (Add (S K') (Add I G))))
                (Add Lo (S (Add K' (Add I (S G)))))
                (IdCongr Nat Nat (λ (A : Nat). Add Lo (S A))
                  (Add (S K') (Add I G)) (Add K' (Add I (S G))) (HshiftFalse K' I G))
                Hle)
        }
    } }
def NthPartScanRangeLGeTy : Term := prog{
  Π (Pivot : Nat) → Π (Lo : Nat) → Π (Q : Nat) → Π (K : Nat) → Π (I : Nat) → Π (G : Nat) → Π (L : List Nat) →
    Le (Add Lo (S (Add K (Add I G)))) Q →
    Id Nat (NthL Q (PartScanRangeL Pivot Lo K I G L)) (NthL Q L) }

-- Below-lo locality wrapper (partition = scan after pivot pick), mirroring LenPartitionRangeL.
def NthPartitionRangeLLt : Term := prog{
  λ (Lo : Nat). λ (J : Nat). λ (Hlt : Le (S J) Lo). λ (Cnt : Nat). λ (L : List Nat).
    elim Cnt return (λ (Cz : Nat). Id Nat
        (NthL J (elim Cz return (λ (Cy : Nat). List Nat) { Z => L, S (Cnt') Rec => PartScanRangeL (NthL Lo L) Lo Cnt' Z Z L }))
        (NthL J L)) {
      Z => Refl,
      S (Cnt') Rec => NthPartScanRangeLLt (NthL Lo L) Lo J Hlt Cnt' Z Z L } }
def NthPartitionRangeLLtTy : Term := prog{
  Π (Lo : Nat) → Π (J : Nat) → Le (S J) Lo → Π (Cnt : Nat) → Π (L : List Nat) →
    Id Nat (NthL J (PartitionRangeL Lo Cnt L)) (NthL J L) }

-- At/above-(lo+cnt) locality wrapper. The top bound Le (add lo cnt) q supplies the
-- scan's Le (add lo (S (add cnt' Z))) q via one AddZero nudge (cf CountPartitionRangeL).
def NthPartitionRangeLGe : Term := prog{
  λ (Lo : Nat). λ (Q : Nat). λ (Cnt : Nat). λ (L : List Nat).
    elim Cnt return (λ (Cz : Nat).
        Le (Add Lo Cz) Q →
        Id Nat (NthL Q (elim Cz return (λ (Cy : Nat). List Nat) { Z => L, S (Cnt') Rec => PartScanRangeL (NthL Lo L) Lo Cnt' Z Z L })) (NthL Q L)) {
      Z => λ (Hb : Le (Add Lo Z) Q). Refl,
      S (Cnt') Rec => λ (Hb : Le (Add Lo (S Cnt')) Q).
        NthPartScanRangeLGe (NthL Lo L) Lo Q Cnt' Z Z L
          (LeRwL Q (Add Lo (S Cnt')) (Add Lo (S (Add Cnt' Z)))
            (IdCongr Nat Nat (λ (A : Nat). Add Lo (S A)) Cnt' (Add Cnt' Z)
              (IdSym Nat (Add Cnt' Z) Cnt' (AddZero Cnt')))
            Hb) } }
def NthPartitionRangeLGeTy : Term := prog{
  Π (Lo : Nat) → Π (Q : Nat) → Π (Cnt : Nat) → Π (L : List Nat) →
    Le (Add Lo Cnt) Q → Id Nat (NthL Q (PartitionRangeL Lo Cnt L)) (NthL Q L) }

/-! ## `NthL`-under-sort LOCALITY — positions outside the sorted range unchanged (§22)

    The full quicksort's locality, the fuel-structural culmination of Step B. The
    two sub-slices SortRangeL recurses on — the prefix `[lo, lo+i)` and the suffix
    `[lo+i+1, …)` — both sit inside `[lo, lo+cnt)`, so a position outside the whole
    range stays outside both. `_lt` (j < lo) composes the two recursive-sort
    localities with `NthPartitionRangeLLt` (bound threaded through the fuel elim,
    the right recursion's `lo' = S(lo+i)` reached via one `LeUpR`); `_ge`
    (q ≥ lo+cnt) is the CountSortRangeL structure with position bounds
    `SortRangeGeBL`/`SortRangeGeBR` in place of SortRangeBL/BR — these are the
    len-relative sub-range bounds STRIPPED of their LenPartitionRangeL/LenSortRangeL
    layer (a position bound is list-independent), leaving just the PartScanSizeL
    size fact (`PartSizeCnt`: i+g = cnt-1) and add-arithmetic. -/

-- Below-lo locality of the full sort. Fuel induction (mirror LenSortRangeL);
-- step composes right-sort, left-sort, partition localities via NthPartitionRangeLLt.
def NthSortRangeLLt : Term := prog{
  λ (Fuel : Nat). λ (J : Nat).
    elim Fuel return (λ (Fz : Nat). Π (Lo : Nat) → Π (Cnt : Nat) → Π (L : List Nat) → Le (S J) Lo → Id Nat (NthL J (SortRangeL Fz Lo Cnt L)) (NthL J L)) {
      Z => λ (Lo : Nat). λ (Cnt : Nat). λ (L : List Nat). λ (Hlt : Le (S J) Lo). Refl,
      S (F') Ih => λ (Lo : Nat). λ (Cnt : Nat). λ (L : List Nat). λ (Hlt : Le (S J) Lo).
        elim Cnt return (λ (Cz : Nat). Id Nat (NthL J (elim Cz return (λ (Cy : Nat). List Nat) {
              Z => L,
              S (Cnt') Nih => elim Cnt' return (λ (My : Nat). List Nat) {
                Z => L,
                S (Cnt'') N2ih => SortRangeL F' (S (Add Lo (PartIdxRangeL Lo Cnt L))) (PartGapRangeL Lo Cnt L) (SortRangeL F' Lo (PartIdxRangeL Lo Cnt L) (PartitionRangeL Lo Cnt L)) } })) (NthL J L)) {
          Z => Refl,
          S (Cnt') Nih => elim Cnt' return (λ (My : Nat). Id Nat (NthL J (elim My return (λ (Myy : Nat). List Nat) {
                Z => L,
                S (Cnt'') N2ih => SortRangeL F' (S (Add Lo (PartIdxRangeL Lo Cnt L))) (PartGapRangeL Lo Cnt L) (SortRangeL F' Lo (PartIdxRangeL Lo Cnt L) (PartitionRangeL Lo Cnt L)) })) (NthL J L)) {
            Z => Refl,
            S (Cnt'') N2ih =>
              IdTrans Nat
                (NthL J (SortRangeL F' (S (Add Lo (PartIdxRangeL Lo Cnt L))) (PartGapRangeL Lo Cnt L) (SortRangeL F' Lo (PartIdxRangeL Lo Cnt L) (PartitionRangeL Lo Cnt L))))
                (NthL J (SortRangeL F' Lo (PartIdxRangeL Lo Cnt L) (PartitionRangeL Lo Cnt L)))
                (NthL J L)
                (Ih (S (Add Lo (PartIdxRangeL Lo Cnt L))) (PartGapRangeL Lo Cnt L) (SortRangeL F' Lo (PartIdxRangeL Lo Cnt L) (PartitionRangeL Lo Cnt L))
                    (LeTrans (S J) Lo (S (Add Lo (PartIdxRangeL Lo Cnt L))) Hlt
                      (LeUpR Lo (Add Lo (PartIdxRangeL Lo Cnt L)) (LeAdd Lo (PartIdxRangeL Lo Cnt L)))))
                (IdTrans Nat
                  (NthL J (SortRangeL F' Lo (PartIdxRangeL Lo Cnt L) (PartitionRangeL Lo Cnt L)))
                  (NthL J (PartitionRangeL Lo Cnt L))
                  (NthL J L)
                  (Ih Lo (PartIdxRangeL Lo Cnt L) (PartitionRangeL Lo Cnt L) Hlt)
                  (NthPartitionRangeLLt Lo J Hlt Cnt L))
          } } } }
def NthSortRangeLLtTy : Term := prog{
  Π (Fuel : Nat) → Π (J : Nat) → Π (Lo : Nat) → Π (Cnt : Nat) → Π (L : List Nat) →
    Le (S J) Lo → Id Nat (NthL J (SortRangeL Fuel Lo Cnt L)) (NthL J L) }

-- The pivot index plus the gap equals cnt-1 (= S cnt'' for cnt = S(S cnt'')).
-- Lifted from sortRangeBL's inner IdTrans (PartScanSizeL then AddZero).
def PartSizeCnt : Term := prog{
  λ (Lo : Nat). λ (Cnt'' : Nat). λ (L : List Nat).
    IdTrans Nat
      (Add (PartIdxRangeL Lo (S (S Cnt'')) L) (PartGapRangeL Lo (S (S Cnt'')) L))
      (S (Add Cnt'' Z))
      (S Cnt'')
      (PartScanSizeL (NthL Lo L) Lo (S Cnt'') Z Z L)
      (IdCongr Nat Nat (λ (A : Nat). S A) (Add Cnt'' Z) Cnt'' (AddZero Cnt'')) }
def PartSizeCntTy : Term := prog{
  Π (Lo : Nat) → Π (Cnt'' : Nat) → Π (L : List Nat) →
    Id Nat (Add (PartIdxRangeL Lo (S (S Cnt'')) L) (PartGapRangeL Lo (S (S Cnt'')) L)) (S Cnt'') }

-- Left sub-range position bound: Le (add lo i) q from Le (add lo cnt) q (i ≤ cnt-1 < cnt).
def SortRangeGeBL : Term := prog{
  λ (Lo : Nat). λ (Cnt'' : Nat). λ (Q : Nat). λ (L : List Nat). λ (Hb : Le (Add Lo (S (S Cnt''))) Q).
    LeTrans (Add Lo (PartIdxRangeL Lo (S (S Cnt'')) L)) (Add Lo (S (S Cnt''))) Q
      (LeAddMonoL Lo (PartIdxRangeL Lo (S (S Cnt'')) L) (S (S Cnt''))
        (LeUpR (PartIdxRangeL Lo (S (S Cnt'')) L) (S Cnt'')
          (LeRwR (PartIdxRangeL Lo (S (S Cnt'')) L)
            (Add (PartIdxRangeL Lo (S (S Cnt'')) L) (PartGapRangeL Lo (S (S Cnt'')) L))
            (S Cnt'')
            (PartSizeCnt Lo Cnt'' L)
            (LeAdd (PartIdxRangeL Lo (S (S Cnt'')) L) (PartGapRangeL Lo (S (S Cnt'')) L)))))
      Hb }
def SortRangeGeBLTy : Term := prog{
  Π (Lo : Nat) → Π (Cnt'' : Nat) → Π (Q : Nat) → Π (L : List Nat) → Le (Add Lo (S (S Cnt''))) Q →
    Le (Add Lo (PartIdxRangeL Lo (S (S Cnt'')) L)) Q }

-- Right sub-range position bound: Le (add (S (add lo i)) g) q from Le (add lo cnt) q,
-- using add (S (add lo i)) g = add lo (S (add i g)) = add lo cnt (PartSizeCnt).
def SortRangeGeBR : Term := prog{
  λ (Lo : Nat). λ (Cnt'' : Nat). λ (Q : Nat). λ (L : List Nat). λ (Hb : Le (Add Lo (S (S Cnt''))) Q).
    LeRwL Q (Add Lo (S (S Cnt''))) (Add (S (Add Lo (PartIdxRangeL Lo (S (S Cnt'')) L))) (PartGapRangeL Lo (S (S Cnt'')) L))
      (IdSym Nat
        (Add (S (Add Lo (PartIdxRangeL Lo (S (S Cnt'')) L))) (PartGapRangeL Lo (S (S Cnt'')) L))
        (Add Lo (S (S Cnt'')))
        (IdTrans Nat
          (Add (S (Add Lo (PartIdxRangeL Lo (S (S Cnt'')) L))) (PartGapRangeL Lo (S (S Cnt'')) L))
          (Add Lo (S (Add (PartIdxRangeL Lo (S (S Cnt'')) L) (PartGapRangeL Lo (S (S Cnt'')) L))))
          (Add Lo (S (S Cnt'')))
          (IdTrans Nat
            (Add (S (Add Lo (PartIdxRangeL Lo (S (S Cnt'')) L))) (PartGapRangeL Lo (S (S Cnt'')) L))
            (S (Add Lo (Add (PartIdxRangeL Lo (S (S Cnt'')) L) (PartGapRangeL Lo (S (S Cnt'')) L))))
            (Add Lo (S (Add (PartIdxRangeL Lo (S (S Cnt'')) L) (PartGapRangeL Lo (S (S Cnt'')) L))))
            (IdCongr Nat Nat (λ (A : Nat). S A)
              (Add (Add Lo (PartIdxRangeL Lo (S (S Cnt'')) L)) (PartGapRangeL Lo (S (S Cnt'')) L))
              (Add Lo (Add (PartIdxRangeL Lo (S (S Cnt'')) L) (PartGapRangeL Lo (S (S Cnt'')) L)))
              (AddAssoc Lo (PartIdxRangeL Lo (S (S Cnt'')) L) (PartGapRangeL Lo (S (S Cnt'')) L)))
            (IdSym Nat
              (Add Lo (S (Add (PartIdxRangeL Lo (S (S Cnt'')) L) (PartGapRangeL Lo (S (S Cnt'')) L))))
              (S (Add Lo (Add (PartIdxRangeL Lo (S (S Cnt'')) L) (PartGapRangeL Lo (S (S Cnt'')) L))))
              (AddSucc Lo (Add (PartIdxRangeL Lo (S (S Cnt'')) L) (PartGapRangeL Lo (S (S Cnt'')) L)))))
          (IdCongr Nat Nat (λ (A : Nat). Add Lo (S A))
            (Add (PartIdxRangeL Lo (S (S Cnt'')) L) (PartGapRangeL Lo (S (S Cnt'')) L)) (S Cnt'')
            (PartSizeCnt Lo Cnt'' L))))
      Hb }
def SortRangeGeBRTy : Term := prog{
  Π (Lo : Nat) → Π (Cnt'' : Nat) → Π (Q : Nat) → Π (L : List Nat) → Le (Add Lo (S (S Cnt''))) Q →
    Le (Add (S (Add Lo (PartIdxRangeL Lo (S (S Cnt'')) L))) (PartGapRangeL Lo (S (S Cnt'')) L)) Q }

-- At/above-(lo+cnt) locality of the full sort. CountSortRangeL structure with
-- position bounds SortRangeGeBL/BR feeding the two recursive-sort IHs.
def NthSortRangeLGe : Term := prog{
  λ (Fuel : Nat). λ (Q : Nat).
    elim Fuel return (λ (Fz : Nat). Π (Lo : Nat) → Π (Cnt : Nat) → Π (L : List Nat) →
        Le (Add Lo Cnt) Q → Id Nat (NthL Q (SortRangeL Fz Lo Cnt L)) (NthL Q L)) {
      Z => λ (Lo : Nat). λ (Cnt : Nat). λ (L : List Nat). λ (Hb : Le (Add Lo Cnt) Q). Refl,
      S (F') Ih => λ (Lo : Nat). λ (Cnt : Nat). λ (L : List Nat).
        elim Cnt return (λ (Cz : Nat). Le (Add Lo Cz) Q →
            Id Nat (NthL Q (SortRangeL (S F') Lo Cz L)) (NthL Q L)) {
          Z => λ (Hb : Le (Add Lo Z) Q). Refl,
          S (Cnt') Nih => elim Cnt' return (λ (Cz' : Nat). Le (Add Lo (S Cz')) Q →
              Id Nat (NthL Q (SortRangeL (S F') Lo (S Cz') L)) (NthL Q L)) {
            Z => λ (Hb : Le (Add Lo (S Z)) Q). Refl,
            S (Cnt'') N2ih => λ (Hb : Le (Add Lo (S (S Cnt''))) Q).
              IdTrans Nat
                (NthL Q (SortRangeL F' (S (Add Lo (PartIdxRangeL Lo (S (S Cnt'')) L))) (PartGapRangeL Lo (S (S Cnt'')) L)
                          (SortRangeL F' Lo (PartIdxRangeL Lo (S (S Cnt'')) L) (PartitionRangeL Lo (S (S Cnt'')) L))))
                (NthL Q (SortRangeL F' Lo (PartIdxRangeL Lo (S (S Cnt'')) L) (PartitionRangeL Lo (S (S Cnt'')) L)))
                (NthL Q L)
                (Ih (S (Add Lo (PartIdxRangeL Lo (S (S Cnt'')) L))) (PartGapRangeL Lo (S (S Cnt'')) L)
                    (SortRangeL F' Lo (PartIdxRangeL Lo (S (S Cnt'')) L) (PartitionRangeL Lo (S (S Cnt'')) L))
                    (SortRangeGeBR Lo Cnt'' Q L Hb))
                (IdTrans Nat
                  (NthL Q (SortRangeL F' Lo (PartIdxRangeL Lo (S (S Cnt'')) L) (PartitionRangeL Lo (S (S Cnt'')) L)))
                  (NthL Q (PartitionRangeL Lo (S (S Cnt'')) L))
                  (NthL Q L)
                  (Ih Lo (PartIdxRangeL Lo (S (S Cnt'')) L) (PartitionRangeL Lo (S (S Cnt'')) L)
                      (SortRangeGeBL Lo Cnt'' Q L Hb))
                  (NthPartitionRangeLGe Lo Q (S (S Cnt'')) L Hb))
          }
        }
    } }
def NthSortRangeLGeTy : Term := prog{
  Π (Fuel : Nat) → Π (Q : Nat) → Π (Lo : Nat) → Π (Cnt : Nat) → Π (L : List Nat) →
    Le (Add Lo Cnt) Q → Id Nat (NthL Q (SortRangeL Fuel Lo Cnt L)) (NthL Q L) }

/-! ## Reusable bridges — cancellation, no-confusion, list/take/drop extensionality (§22)

    The general-purpose stratum Step C's SegCount preservation stands on. Two are
    the classical Nat "no confusion + cancellation" primitives; the rest bridge the
    positional (nth) view to the segment (take/drop) view.

    - `Znots` : `Z ≠ S` via a LARGE elimination into `Type` (`elim y {Z => Unit, S =>
      Bot}`), transported by `j`. This is the discriminator list-extensionality needs
      to kill Nil-vs-Cons length mismatches — and it type-checks (the M5 λ/neutral
      deferral does not bite an APPLIED large elim).
    - `SInj` : `S` injective, one `IdCongr` with `Pred`.
    - `AddCancelL` : left cancellation, induction on `a` peeling `SInj`.
    - `NthDrop` : `NthL k (Drop b l) = NthL (Add b k) l` (the positional reading of drop).
    - `ListExt` : equal length + equal `NthL` everywhere ⟹ equal lists (needs znots + SInj).
    - `TakeExtBounded` : `Take w a = Take w b` from equal length + `NthL` agreeing
      BELOW w — the bounded form fed directly by `nth_*_lt` (no case split on k).
    - `LenDropCong` : dropping preserves a length equality.
    - `CountSplit` : `Count x l = Count x (Take w l) + Count x (Drop w l)` (CountAppend ∘ TakeDropId). -/

def Znots : Term := prog{
  λ (X : Nat). λ (H : Id Nat Z (S X)).
    j Nat Z (λ (Y : Nat). λ (Hy : Id Nat Z Y). elim Y return (λ (Yy : Nat). Type) { Z => Unit, S (K) Ih => Bot })
      unit (S X) H }
def ZnotsTy : Term := prog{ Π (X : Nat) → Id Nat Z (S X) → Bot }

def Pred : Term := prog{ λ (N : Nat). elim N return (λ (Z0 : Nat). Nat) { Z => Z, S (K) Ih => K } }
def SInj : Term := prog{
  λ (M : Nat). λ (N : Nat). λ (H : Id Nat (S M) (S N)).
    IdCongr Nat Nat Pred (S M) (S N) H }
def SInjTy : Term := prog{ Π (M : Nat) → Π (N : Nat) → Id Nat (S M) (S N) → Id Nat M N }

def AddCancelL : Term := prog{
  λ (A : Nat).
    elim A return (λ (Az : Nat). Π (X : Nat) → Π (Y : Nat) → Id Nat (Add Az X) (Add Az Y) → Id Nat X Y) {
      Z => λ (X : Nat). λ (Y : Nat). λ (H : Id Nat (Add Z X) (Add Z Y)). H,
      S (A') Ih => λ (X : Nat). λ (Y : Nat). λ (H : Id Nat (Add (S A') X) (Add (S A') Y)).
        Ih X Y (SInj (Add A' X) (Add A' Y) H) } }
def AddCancelLTy : Term := prog{
  Π (A : Nat) → Π (X : Nat) → Π (Y : Nat) → Id Nat (Add A X) (Add A Y) → Id Nat X Y }

def NthDrop : Term := prog{
  λ (B : Nat).
    elim B return (λ (Bz : Nat). Π (K : Nat) → Π (L : List Nat) → Id Nat (NthL K (Drop Bz L)) (NthL (Add Bz K) L)) {
      Z => λ (K : Nat). λ (L : List Nat). Refl,
      S (B') Ih => λ (K : Nat). λ (L : List Nat).
        elim L return (λ (Lz : List Nat). Id Nat (NthL K (Drop (S B') Lz)) (NthL (Add (S B') K) Lz)) {
          Nil => elim K return (λ (Kz : Nat). Id Nat (NthL Kz (Drop (S B') Nil)) (NthL (Add (S B') Kz) Nil)) {
            Z => Refl, S (K') Kih => Refl },
          Cons (H) (T) Ihl => Ih K T } } }
def NthDropTy : Term := prog{
  Π (B : Nat) → Π (K : Nat) → Π (L : List Nat) → Id Nat (NthL K (Drop B L)) (NthL (Add B K) L) }

def ListExt : Term := prog{
  λ (A : List Nat).
    elim A return (λ (Az : List Nat). Π (B : List Nat) → Id Nat (Len Az) (Len B) → (Π (K : Nat) → Id Nat (NthL K Az) (NthL K B)) → Id (List Nat) Az B) {
      Nil => λ (B : List Nat).
        elim B return (λ (Bz : List Nat). Id Nat (Len Nil) (Len Bz) → (Π (K : Nat) → Id Nat (NthL K Nil) (NthL K Bz)) → Id (List Nat) Nil Bz) {
          Nil => λ (Hlen : Id Nat (Len Nil) (Len Nil)). λ (Hnth : Π (K : Nat) → Id Nat (NthL K Nil) (NthL K Nil)). Refl,
          Cons (Hb) (Tb) Ihb => λ (Hlen : Id Nat (Len Nil) (Len (Cons Hb Tb))). λ (Hnth : Π (K : Nat) → Id Nat (NthL K Nil) (NthL K (Cons Hb Tb))).
            botElim (Id (List Nat) Nil (Cons Hb Tb)) (Znots (Len Tb) Hlen) },
      Cons (Ha) (Ta) Iha => λ (B : List Nat).
        elim B return (λ (Bz : List Nat). Id Nat (Len (Cons Ha Ta)) (Len Bz) → (Π (K : Nat) → Id Nat (NthL K (Cons Ha Ta)) (NthL K Bz)) → Id (List Nat) (Cons Ha Ta) Bz) {
          Nil => λ (Hlen : Id Nat (Len (Cons Ha Ta)) (Len Nil)). λ (Hnth : Π (K : Nat) → Id Nat (NthL K (Cons Ha Ta)) (NthL K Nil)).
            botElim (Id (List Nat) (Cons Ha Ta) Nil) (Znots (Len Ta) (IdSym Nat (Len (Cons Ha Ta)) (Len Nil) Hlen)),
          Cons (Hb) (Tb) Ihb => λ (Hlen : Id Nat (Len (Cons Ha Ta)) (Len (Cons Hb Tb))). λ (Hnth : Π (K : Nat) → Id Nat (NthL K (Cons Ha Ta)) (NthL K (Cons Hb Tb))).
            IdTrans (List Nat) (Cons Ha Ta) (Cons Hb Ta) (Cons Hb Tb)
              (IdCongr Nat (List Nat) (λ (Hh : Nat). Cons Hh Ta) Ha Hb (Hnth Z))
              (IdCongr (List Nat) (List Nat) (λ (Tt : List Nat). Cons Hb Tt) Ta Tb
                (Iha Tb (SInj (Len Ta) (Len Tb) Hlen) (λ (K : Nat). Hnth (S K)))) } } }
def ListExtTy : Term := prog{
  Π (A : List Nat) → Π (B : List Nat) → Id Nat (Len A) (Len B) →
    (Π (K : Nat) → Id Nat (NthL K A) (NthL K B)) → Id (List Nat) A B }

def TakeExtBounded : Term := prog{
  λ (W : Nat).
    elim W return (λ (Wz : Nat). Π (A : List Nat) → Π (B : List Nat) → Id Nat (Len A) (Len B) → (Π (K : Nat) → Le (S K) Wz → Id Nat (NthL K A) (NthL K B)) → Id (List Nat) (Take Wz A) (Take Wz B)) {
      Z => λ (A : List Nat). λ (B : List Nat). λ (Hlen : Id Nat (Len A) (Len B)). λ (Hnth : Π (K : Nat) → Le (S K) Z → Id Nat (NthL K A) (NthL K B)). Refl,
      S (W') Ih => λ (A : List Nat). λ (B : List Nat). λ (Hlen : Id Nat (Len A) (Len B)). λ (Hnth : Π (K : Nat) → Le (S K) (S W') → Id Nat (NthL K A) (NthL K B)).
        elim A return (λ (Az : List Nat). Id Nat (Len Az) (Len B) → (Π (K : Nat) → Le (S K) (S W') → Id Nat (NthL K Az) (NthL K B)) → Id (List Nat) (Take (S W') Az) (Take (S W') B)) {
          Nil => λ (HlenA : Id Nat (Len Nil) (Len B)). λ (HnthA : Π (K : Nat) → Le (S K) (S W') → Id Nat (NthL K Nil) (NthL K B)).
            elim B return (λ (Bz : List Nat). Id Nat (Len Nil) (Len Bz) → Id (List Nat) (Take (S W') Nil) (Take (S W') Bz)) {
              Nil => λ (Hl : Id Nat (Len Nil) (Len Nil)). Refl,
              Cons (Hb) (Tb) Ihb => λ (Hl : Id Nat (Len Nil) (Len (Cons Hb Tb))).
                botElim (Id (List Nat) (Take (S W') Nil) (Take (S W') (Cons Hb Tb))) (Znots (Len Tb) Hl) } HlenA,
          Cons (Ha) (Ta) Iha => λ (HlenA : Id Nat (Len (Cons Ha Ta)) (Len B)). λ (HnthA : Π (K : Nat) → Le (S K) (S W') → Id Nat (NthL K (Cons Ha Ta)) (NthL K B)).
            elim B return (λ (Bz : List Nat). Id Nat (Len (Cons Ha Ta)) (Len Bz) → (Π (K : Nat) → Le (S K) (S W') → Id Nat (NthL K (Cons Ha Ta)) (NthL K Bz)) → Id (List Nat) (Take (S W') (Cons Ha Ta)) (Take (S W') Bz)) {
              Nil => λ (Hl : Id Nat (Len (Cons Ha Ta)) (Len Nil)). λ (Hn : Π (K : Nat) → Le (S K) (S W') → Id Nat (NthL K (Cons Ha Ta)) (NthL K Nil)).
                botElim (Id (List Nat) (Take (S W') (Cons Ha Ta)) (Take (S W') Nil)) (Znots (Len Ta) (IdSym Nat (Len (Cons Ha Ta)) (Len Nil) Hl)),
              Cons (Hb) (Tb) Ihb => λ (Hl : Id Nat (Len (Cons Ha Ta)) (Len (Cons Hb Tb))). λ (Hn : Π (K : Nat) → Le (S K) (S W') → Id Nat (NthL K (Cons Ha Ta)) (NthL K (Cons Hb Tb))).
                IdTrans (List Nat) (Cons Ha (Take W' Ta)) (Cons Hb (Take W' Ta)) (Cons Hb (Take W' Tb))
                  (IdCongr Nat (List Nat) (λ (Hh : Nat). Cons Hh (Take W' Ta)) Ha Hb (Hn Z unit))
                  (IdCongr (List Nat) (List Nat) (λ (Tt : List Nat). Cons Hb Tt) (Take W' Ta) (Take W' Tb)
                    (Ih Ta Tb (SInj (Len Ta) (Len Tb) Hl) (λ (K : Nat). λ (Hk : Le (S K) W'). Hn (S K) Hk)))
            } HlenA HnthA
        } Hlen Hnth
    } }
def TakeExtBoundedTy : Term := prog{
  Π (W : Nat) → Π (A : List Nat) → Π (B : List Nat) → Id Nat (Len A) (Len B) →
    (Π (K : Nat) → Le (S K) W → Id Nat (NthL K A) (NthL K B)) → Id (List Nat) (Take W A) (Take W B) }

def LenDropCong : Term := prog{
  λ (W : Nat).
    elim W return (λ (Wz : Nat). Π (A : List Nat) → Π (B : List Nat) → Id Nat (Len A) (Len B) → Id Nat (Len (Drop Wz A)) (Len (Drop Wz B))) {
      Z => λ (A : List Nat). λ (B : List Nat). λ (Hlen : Id Nat (Len A) (Len B)). Hlen,
      S (W') Ih => λ (A : List Nat). λ (B : List Nat). λ (Hlen : Id Nat (Len A) (Len B)).
        elim A return (λ (Az : List Nat). Id Nat (Len Az) (Len B) → Id Nat (Len (Drop (S W') Az)) (Len (Drop (S W') B))) {
          Nil => λ (Hl : Id Nat (Len Nil) (Len B)).
            elim B return (λ (Bz : List Nat). Id Nat (Len Nil) (Len Bz) → Id Nat (Len (Drop (S W') Nil)) (Len (Drop (S W') Bz))) {
              Nil => λ (H : Id Nat (Len Nil) (Len Nil)). Refl,
              Cons (Hb) (Tb) Ihb => λ (H : Id Nat (Len Nil) (Len (Cons Hb Tb))).
                botElim (Id Nat (Len (Drop (S W') Nil)) (Len (Drop (S W') (Cons Hb Tb)))) (Znots (Len Tb) H) } Hl,
          Cons (Ha) (Ta) Iha => λ (Hl : Id Nat (Len (Cons Ha Ta)) (Len B)).
            elim B return (λ (Bz : List Nat). Id Nat (Len (Cons Ha Ta)) (Len Bz) → Id Nat (Len (Drop (S W') (Cons Ha Ta))) (Len (Drop (S W') Bz))) {
              Nil => λ (H : Id Nat (Len (Cons Ha Ta)) (Len Nil)).
                botElim (Id Nat (Len (Drop (S W') (Cons Ha Ta))) (Len (Drop (S W') Nil))) (Znots (Len Ta) (IdSym Nat (Len (Cons Ha Ta)) (Len Nil) H)),
              Cons (Hb) (Tb) Ihb => λ (H : Id Nat (Len (Cons Ha Ta)) (Len (Cons Hb Tb))).
                Ih Ta Tb (SInj (Len Ta) (Len Tb) H) } Hl } Hlen } }
def LenDropCongTy : Term := prog{
  Π (W : Nat) → Π (A : List Nat) → Π (B : List Nat) → Id Nat (Len A) (Len B) →
    Id Nat (Len (Drop W A)) (Len (Drop W B)) }

def CountSplit : Term := prog{
  λ (X : Nat). λ (W : Nat). λ (L : List Nat).
    IdTrans Nat (Count X L) (Count X (Append (Take W L) (Drop W L))) (Add (Count X (Take W L)) (Count X (Drop W L)))
      (IdCongr (List Nat) Nat (λ (Ll : List Nat). Count X Ll) L (Append (Take W L) (Drop W L))
        (IdSym (List Nat) (Append (Take W L) (Drop W L)) L (TakeDropId W L)))
      (CountAppend X (Take W L) (Drop W L)) }
def CountSplitTy : Term := prog{
  Π (X : Nat) → Π (W : Nat) → Π (L : List Nat) →
    Id Nat (Count X L) (Add (Count X (Take W L)) (Count X (Drop W L))) }

/-! ## Segment-count preservation — the perm-survival vehicle (§22, M22-c step 3)

    The multiset half's payoff: sorting/partitioning a range preserves the multiset
    OF THAT SEGMENT (SegCount), so a positional bound over the segment survives the
    permutation. The argument is pure cancellation: whole count is preserved
    (CountSortRangeL / CountPartitionRangeL), the prefix `Take lo` and suffix
    `Drop cnt (Drop lo)` are IDENTICAL lists (Step B locality lifted to list equality
    via TakeExtBounded / ListExt + NthDrop), and

        count x whole = count x prefix + (segment + suffix)

    so with prefix and suffix counts equal on both sides, AddCancelL twice (once
    each side, AddComm to expose the operand) leaves segment counts equal — no
    subtraction. `CountRestPreserved` / `CountSegPreserved` are the two directions
    of that cancellation; `SegGlue` composes them; `take_lo_*` / `drop_suffix_*`
    supply the list equalities from Step B. -/

def CountRestPreserved : Term := prog{
  λ (X : Nat). λ (W : Nat). λ (S0 : List Nat). λ (L : List Nat).
    λ (Hcount : Id Nat (Count X S0) (Count X L)).
    λ (Hpre : Id Nat (Count X (Take W S0)) (Count X (Take W L))).
      AddCancelL (Count X (Take W L)) (Count X (Drop W S0)) (Count X (Drop W L))
        (IdTrans Nat
          (Add (Count X (Take W L)) (Count X (Drop W S0)))
          (Count X L)
          (Add (Count X (Take W L)) (Count X (Drop W L)))
          (IdTrans Nat
            (Add (Count X (Take W L)) (Count X (Drop W S0)))
            (Count X S0)
            (Count X L)
            (IdSym Nat (Count X S0) (Add (Count X (Take W L)) (Count X (Drop W S0)))
              (IdTrans Nat
                (Count X S0)
                (Add (Count X (Take W S0)) (Count X (Drop W S0)))
                (Add (Count X (Take W L)) (Count X (Drop W S0)))
                (CountSplit X W S0)
                (IdCongr Nat Nat (λ (N : Nat). Add N (Count X (Drop W S0)))
                  (Count X (Take W S0)) (Count X (Take W L)) Hpre)))
            Hcount)
          (CountSplit X W L)) }
def CountRestPreservedTy : Term := prog{
  Π (X : Nat) → Π (W : Nat) → Π (S0 : List Nat) → Π (L : List Nat) →
    Id Nat (Count X S0) (Count X L) →
    Id Nat (Count X (Take W S0)) (Count X (Take W L)) →
    Id Nat (Count X (Drop W S0)) (Count X (Drop W L)) }

def CountSegPreserved : Term := prog{
  λ (X : Nat). λ (W : Nat). λ (S0 : List Nat). λ (L : List Nat).
    λ (Hcount : Id Nat (Count X S0) (Count X L)).
    λ (Hdrop : Id Nat (Count X (Drop W S0)) (Count X (Drop W L))).
      AddCancelL (Count X (Drop W L)) (Count X (Take W S0)) (Count X (Take W L))
        (IdTrans Nat
          (Add (Count X (Drop W L)) (Count X (Take W S0)))
          (Count X L)
          (Add (Count X (Drop W L)) (Count X (Take W L)))
          (IdTrans Nat
            (Add (Count X (Drop W L)) (Count X (Take W S0)))
            (Count X S0)
            (Count X L)
            (IdSym Nat (Count X S0) (Add (Count X (Drop W L)) (Count X (Take W S0)))
              (IdTrans Nat
                (Count X S0)
                (Add (Count X (Take W S0)) (Count X (Drop W S0)))
                (Add (Count X (Drop W L)) (Count X (Take W S0)))
                (CountSplit X W S0)
                (IdTrans Nat
                  (Add (Count X (Take W S0)) (Count X (Drop W S0)))
                  (Add (Count X (Take W S0)) (Count X (Drop W L)))
                  (Add (Count X (Drop W L)) (Count X (Take W S0)))
                  (IdCongr Nat Nat (λ (N : Nat). Add (Count X (Take W S0)) N)
                    (Count X (Drop W S0)) (Count X (Drop W L)) Hdrop)
                  (AddComm (Count X (Take W S0)) (Count X (Drop W L))))))
            Hcount)
          (IdTrans Nat
            (Count X L)
            (Add (Count X (Take W L)) (Count X (Drop W L)))
            (Add (Count X (Drop W L)) (Count X (Take W L)))
            (CountSplit X W L)
            (AddComm (Count X (Take W L)) (Count X (Drop W L))))) }
def CountSegPreservedTy : Term := prog{
  Π (X : Nat) → Π (W : Nat) → Π (S0 : List Nat) → Π (L : List Nat) →
    Id Nat (Count X S0) (Count X L) →
    Id Nat (Count X (Drop W S0)) (Count X (Drop W L)) →
    Id Nat (Count X (Take W S0)) (Count X (Take W L)) }

def SegGlue : Term := prog{
  λ (X : Nat). λ (Lo : Nat). λ (Cnt : Nat). λ (S0 : List Nat). λ (L : List Nat).
    λ (Hcount : Id Nat (Count X S0) (Count X L)).
    λ (Hpre : Id (List Nat) (Take Lo S0) (Take Lo L)).
    λ (Hsuf : Id (List Nat) (Drop Cnt (Drop Lo S0)) (Drop Cnt (Drop Lo L))).
      CountSegPreserved X Cnt (Drop Lo S0) (Drop Lo L)
        (CountRestPreserved X Lo S0 L Hcount
          (IdCongr (List Nat) Nat (λ (Ll : List Nat). Count X Ll) (Take Lo S0) (Take Lo L) Hpre))
        (IdCongr (List Nat) Nat (λ (Ll : List Nat). Count X Ll) (Drop Cnt (Drop Lo S0)) (Drop Cnt (Drop Lo L)) Hsuf) }
def SegGlueTy : Term := prog{
  Π (X : Nat) → Π (Lo : Nat) → Π (Cnt : Nat) → Π (S0 : List Nat) → Π (L : List Nat) →
    Id Nat (Count X S0) (Count X L) →
    Id (List Nat) (Take Lo S0) (Take Lo L) →
    Id (List Nat) (Drop Cnt (Drop Lo S0)) (Drop Cnt (Drop Lo L)) →
    Id Nat (Count X (Take Cnt (Drop Lo S0))) (Count X (Take Cnt (Drop Lo L))) }

-- Prefix/suffix of the SORT are identical (Step B locality → list equality).
def TakeLoSort : Term := prog{
  λ (Fuel : Nat). λ (Lo : Nat). λ (Cnt : Nat). λ (L : List Nat).
    TakeExtBounded Lo (SortRangeL Fuel Lo Cnt L) L
      (LenSortRangeL Fuel Lo Cnt L)
      (λ (K : Nat). λ (Hk : Le (S K) Lo). NthSortRangeLLt Fuel K Lo Cnt L Hk) }
def TakeLoSortTy : Term := prog{
  Π (Fuel : Nat) → Π (Lo : Nat) → Π (Cnt : Nat) → Π (L : List Nat) →
    Id (List Nat) (Take Lo (SortRangeL Fuel Lo Cnt L)) (Take Lo L) }

def DropSuffixSort : Term := prog{
  λ (Fuel : Nat). λ (Lo : Nat). λ (Cnt : Nat). λ (L : List Nat).
    ListExt (Drop Cnt (Drop Lo (SortRangeL Fuel Lo Cnt L))) (Drop Cnt (Drop Lo L))
      (LenDropCong Cnt (Drop Lo (SortRangeL Fuel Lo Cnt L)) (Drop Lo L)
        (LenDropCong Lo (SortRangeL Fuel Lo Cnt L) L (LenSortRangeL Fuel Lo Cnt L)))
      (λ (K : Nat).
        IdTrans Nat
          (NthL K (Drop Cnt (Drop Lo (SortRangeL Fuel Lo Cnt L))))
          (NthL (Add Lo (Add Cnt K)) (SortRangeL Fuel Lo Cnt L))
          (NthL K (Drop Cnt (Drop Lo L)))
          (IdTrans Nat
            (NthL K (Drop Cnt (Drop Lo (SortRangeL Fuel Lo Cnt L))))
            (NthL (Add Cnt K) (Drop Lo (SortRangeL Fuel Lo Cnt L)))
            (NthL (Add Lo (Add Cnt K)) (SortRangeL Fuel Lo Cnt L))
            (NthDrop Cnt K (Drop Lo (SortRangeL Fuel Lo Cnt L)))
            (NthDrop Lo (Add Cnt K) (SortRangeL Fuel Lo Cnt L)))
          (IdTrans Nat
            (NthL (Add Lo (Add Cnt K)) (SortRangeL Fuel Lo Cnt L))
            (NthL (Add Lo (Add Cnt K)) L)
            (NthL K (Drop Cnt (Drop Lo L)))
            (NthSortRangeLGe Fuel (Add Lo (Add Cnt K)) Lo Cnt L
              (LeAddMonoL Lo Cnt (Add Cnt K) (LeAdd Cnt K)))
            (IdTrans Nat
              (NthL (Add Lo (Add Cnt K)) L)
              (NthL (Add Cnt K) (Drop Lo L))
              (NthL K (Drop Cnt (Drop Lo L)))
              (IdSym Nat (NthL (Add Cnt K) (Drop Lo L)) (NthL (Add Lo (Add Cnt K)) L) (NthDrop Lo (Add Cnt K) L))
              (IdSym Nat (NthL K (Drop Cnt (Drop Lo L))) (NthL (Add Cnt K) (Drop Lo L)) (NthDrop Cnt K (Drop Lo L)))))) }
def DropSuffixSortTy : Term := prog{
  Π (Fuel : Nat) → Π (Lo : Nat) → Π (Cnt : Nat) → Π (L : List Nat) →
    Id (List Nat) (Drop Cnt (Drop Lo (SortRangeL Fuel Lo Cnt L))) (Drop Cnt (Drop Lo L)) }

-- Prefix/suffix of PARTITION are identical (same shape).
def TakeLoPartition : Term := prog{
  λ (Lo : Nat). λ (Cnt : Nat). λ (L : List Nat).
    TakeExtBounded Lo (PartitionRangeL Lo Cnt L) L
      (LenPartitionRangeL Lo Cnt L)
      (λ (K : Nat). λ (Hk : Le (S K) Lo). NthPartitionRangeLLt Lo K Hk Cnt L) }
def TakeLoPartitionTy : Term := prog{
  Π (Lo : Nat) → Π (Cnt : Nat) → Π (L : List Nat) →
    Id (List Nat) (Take Lo (PartitionRangeL Lo Cnt L)) (Take Lo L) }

def DropSuffixPartition : Term := prog{
  λ (Lo : Nat). λ (Cnt : Nat). λ (L : List Nat).
    ListExt (Drop Cnt (Drop Lo (PartitionRangeL Lo Cnt L))) (Drop Cnt (Drop Lo L))
      (LenDropCong Cnt (Drop Lo (PartitionRangeL Lo Cnt L)) (Drop Lo L)
        (LenDropCong Lo (PartitionRangeL Lo Cnt L) L (LenPartitionRangeL Lo Cnt L)))
      (λ (K : Nat).
        IdTrans Nat
          (NthL K (Drop Cnt (Drop Lo (PartitionRangeL Lo Cnt L))))
          (NthL (Add Lo (Add Cnt K)) (PartitionRangeL Lo Cnt L))
          (NthL K (Drop Cnt (Drop Lo L)))
          (IdTrans Nat
            (NthL K (Drop Cnt (Drop Lo (PartitionRangeL Lo Cnt L))))
            (NthL (Add Cnt K) (Drop Lo (PartitionRangeL Lo Cnt L)))
            (NthL (Add Lo (Add Cnt K)) (PartitionRangeL Lo Cnt L))
            (NthDrop Cnt K (Drop Lo (PartitionRangeL Lo Cnt L)))
            (NthDrop Lo (Add Cnt K) (PartitionRangeL Lo Cnt L)))
          (IdTrans Nat
            (NthL (Add Lo (Add Cnt K)) (PartitionRangeL Lo Cnt L))
            (NthL (Add Lo (Add Cnt K)) L)
            (NthL K (Drop Cnt (Drop Lo L)))
            (NthPartitionRangeLGe Lo (Add Lo (Add Cnt K)) Cnt L
              (LeAddMonoL Lo Cnt (Add Cnt K) (LeAdd Cnt K)))
            (IdTrans Nat
              (NthL (Add Lo (Add Cnt K)) L)
              (NthL (Add Cnt K) (Drop Lo L))
              (NthL K (Drop Cnt (Drop Lo L)))
              (IdSym Nat (NthL (Add Cnt K) (Drop Lo L)) (NthL (Add Lo (Add Cnt K)) L) (NthDrop Lo (Add Cnt K) L))
              (IdSym Nat (NthL K (Drop Cnt (Drop Lo L))) (NthL (Add Cnt K) (Drop Lo L)) (NthDrop Cnt K (Drop Lo L)))))) }
def DropSuffixPartitionTy : Term := prog{
  Π (Lo : Nat) → Π (Cnt : Nat) → Π (L : List Nat) →
    Id (List Nat) (Drop Cnt (Drop Lo (PartitionRangeL Lo Cnt L))) (Drop Cnt (Drop Lo L)) }

-- THE GOALS: the segment multiset survives the range sort and partition.
def SegCountSortRangeL : Term := prog{
  λ (X : Nat). λ (Fuel : Nat). λ (Lo : Nat). λ (Cnt : Nat). λ (L : List Nat).
    λ (Hb : Le (Add Lo Cnt) (Len L)).
      SegGlue X Lo Cnt (SortRangeL Fuel Lo Cnt L) L
        (CountSortRangeL X Fuel Lo Cnt L Hb)
        (TakeLoSort Fuel Lo Cnt L)
        (DropSuffixSort Fuel Lo Cnt L) }
def SegCountSortRangeLTy : Term := prog{
  Π (X : Nat) → Π (Fuel : Nat) → Π (Lo : Nat) → Π (Cnt : Nat) → Π (L : List Nat) →
    Le (Add Lo Cnt) (Len L) →
    Id Nat (SegCount X Lo Cnt (SortRangeL Fuel Lo Cnt L)) (SegCount X Lo Cnt L) }

def SegCountPartitionRangeL : Term := prog{
  λ (X : Nat). λ (Lo : Nat). λ (Cnt : Nat). λ (L : List Nat).
    λ (Hb : Le (Add Lo Cnt) (Len L)).
      SegGlue X Lo Cnt (PartitionRangeL Lo Cnt L) L
        (CountPartitionRangeL Lo X Cnt L Hb)
        (TakeLoPartition Lo Cnt L)
        (DropSuffixPartition Lo Cnt L) }
def SegCountPartitionRangeLTy : Term := prog{
  Π (X : Nat) → Π (Lo : Nat) → Π (Cnt : Nat) → Π (L : List Nat) →
    Le (Add Lo Cnt) (Len L) →
    Id Nat (SegCount X Lo Cnt (PartitionRangeL Lo Cnt L)) (SegCount X Lo Cnt L) }

/-! ## The partition invariant — STATEMENTS (§22, M22-c step 2; proofs dispatched)

    PartScanRangeL establishes the Lomuto invariant: the ≤-segment is ≤ pivot, the
    gap is > pivot, the pivot lands at the boundary index. Verified computationally
    (final forms on 5 inputs incl. a sub-range) and elaboration-checked. The 3-way
    conjunction CANNOT be Σ-bundled (comptime Σ can't be projected), so it is THREE
    separate lemmas — and they ARE separable: AllLeR-maintenance needs only the ≤-side
    precondition + the leb test (the swapped-in element tested ≤ pivot); AllGtR only
    the gap-side; pivot only that lo is untouched. STRENGTHENED scan-level forms carry
    the region preconditions (≤-region offset `S lo`, gap offset `Add (S i) lo`,
    index-first to match the predicates); the PartitionRangeL WRAPPERS drop out at
    i=g=0 (vacuous preconditions). ADD-ORDER: predicates index-first (`Add k lo`),
    PartScanRangeL offset-first (`Add lo X`) — the proofs bridge with AddComm. Proofs
    owned by dllbc-seg (positional induction mirroring CountPartScanRangeL, swaps
    discharged via NthSwapLLt/gt). -/
-- PosBridgeSs : add lo (S (S m)) = S (add m (S lo))  (both lo+m+2) — the mid upper bound.
def PosBridgeSs : Term := prog{
  λ (Lo : Nat). λ (M : Nat).
    IdTrans Nat (Add Lo (S (S M))) (S (S (Add Lo M))) (S (Add M (S Lo)))
      (IdTrans Nat (Add Lo (S (S M))) (S (Add Lo (S M))) (S (S (Add Lo M)))
        (AddSucc Lo (S M))
        (IdCongr Nat Nat (λ (Z0 : Nat). S Z0) (Add Lo (S M)) (S (Add Lo M)) (AddSucc Lo M)))
      (IdSym Nat (S (Add M (S Lo))) (S (S (Add Lo M)))
        (IdTrans Nat (S (Add M (S Lo))) (S (S (Add M Lo))) (S (S (Add Lo M)))
          (IdCongr Nat Nat (λ (Z0 : Nat). S Z0) (Add M (S Lo)) (S (Add M Lo)) (AddSucc M Lo))
          (IdCongr Nat Nat (λ (Z0 : Nat). S Z0) (S (Add M Lo)) (S (Add Lo M))
            (IdCongr Nat Nat (λ (Z0 : Nat). S Z0) (Add M Lo) (Add Lo M) (AddComm M Lo))))) }
def PosBridgeSsTy : Term := prog{ Π (Lo : Nat) → Π (M : Nat) → Id Nat (Add Lo (S (S M))) (S (Add M (S Lo))) }

-- BndSl : the scan swap's smaller index < larger index (S(lo+1+i) ≤ lo+1+i+(S g')).
def BndSl : Term := prog{
  λ (Lo : Nat). λ (I : Nat). λ (G' : Nat).
    LeRwL (Add Lo (S (Add I (S G')))) (Add Lo (S (S I))) (S (Add Lo (S I)))
      (AddSucc Lo (S I))
      (LeAddMonoL Lo (S (S I)) (S (Add I (S G')))
        (LeRwR (S I) (S (Add I G')) (Add I (S G'))
          (IdSym Nat (Add I (S G')) (S (Add I G')) (AddSucc I G'))
          (LeAdd I G'))) }
def BndSlTy : Term := prog{ Π (Lo : Nat) → Π (I : Nat) → Π (G' : Nat) → Le (S (Add Lo (S I))) (Add Lo (S (Add I (S G')))) }

-- AllLeRBaseSwap : the pivot-placement swap at the base (i = S i') keeps [lo, lo+S i')
-- all ≤ pivot. Position lo gets the far ≤-element (NthSwapLLo + hL at i'), the interior
-- is unchanged (AllLeRCong via NthSwapLMid), assembled by AllLeRExtendLo.
def AllLeRBaseSwap : Term := prog{
  λ (Pivot : Nat). λ (Lo : Nat). λ (I' : Nat). λ (L : List Nat).
    λ (HL : AllLeR (S I') (S Lo) Pivot L).
      AllLeRExtendLo I' Lo Pivot (SwapL Lo (Add Lo (S I')) L)
        (LeRwL Pivot (NthL (Add Lo (S I')) L) (NthL Lo (SwapL Lo (Add Lo (S I')) L))
          (IdSym Nat (NthL Lo (SwapL Lo (Add Lo (S I')) L)) (NthL (Add Lo (S I')) L)
            (NthSwapLLo Lo (Add Lo (S I')) L (LeAddSucc Lo I')))
          (LeRwL Pivot (NthL (Add I' (S Lo)) L) (NthL (Add Lo (S I')) L)
            (IdCongr Nat Nat (λ (Q : Nat). NthL Q L) (Add I' (S Lo)) (Add Lo (S I')) (AddSwapSucc I' Lo))
            (HL I' (LeRefl (S I')))))
        (AllLeRCong I' (S Lo) Pivot L (SwapL Lo (Add Lo (S I')) L)
          (λ (M : Nat). λ (Hm : Le (S M) I').
            NthSwapLMid Lo (Add Lo (S I')) (Add M (S Lo)) L
              (LeAddL (S Lo) M)
              (LeRwL (Add Lo (S I')) (Add Lo (S (S M))) (S (Add M (S Lo)))
                (PosBridgeSs Lo M)
                (LeAddMonoL Lo (S (S M)) (S I') Hm)))
          (λ (M : Nat). λ (Hm : Le (S M) I'). HL M (LeUpR (S M) I' Hm))) }
def AllLeRBaseSwapTy : Term := prog{
  Π (Pivot : Nat) → Π (Lo : Nat) → Π (I' : Nat) → Π (L : List Nat) →
    AllLeR (S I') (S Lo) Pivot L → AllLeR (S I') Lo Pivot (SwapL Lo (Add Lo (S I')) L) }

-- AllLeRStepTZ : True/g=0 step — the scan element (tested ≤ pivot) extends the ≤-region.
def AllLeRStepTZ : Term := prog{
  λ (Pivot : Nat). λ (Lo : Nat). λ (I : Nat). λ (L : List Nat).
    λ (E : Id Bool (Leb (NthL (Add Lo (S (Add I Z))) L) Pivot) True). λ (HL : AllLeR I (S Lo) Pivot L).
      AllLeRExtendFar I (S Lo) Pivot L HL
        (LeRwL Pivot (NthL (Add Lo (S (Add I Z))) L) (NthL (Add I (S Lo)) L)
          (IdCongr Nat Nat (λ (Q : Nat). NthL Q L) (Add Lo (S (Add I Z))) (Add I (S Lo))
            (IdTrans Nat (Add Lo (S (Add I Z))) (Add Lo (S I)) (Add I (S Lo))
              (IdCongr Nat Nat (λ (Z0 : Nat). Add Lo (S Z0)) (Add I Z) I (AddZero I))
              (IdSym Nat (Add I (S Lo)) (Add Lo (S I)) (AddSwapSucc I Lo))))
          (LebTrueLe (NthL (Add Lo (S (Add I Z))) L) Pivot E)) }
def AllLeRStepTZTy : Term := prog{
  Π (Pivot : Nat) → Π (Lo : Nat) → Π (I : Nat) → Π (L : List Nat) →
    Id Bool (Leb (NthL (Add Lo (S (Add I Z))) L) Pivot) True → AllLeR I (S Lo) Pivot L → AllLeR (S I) (S Lo) Pivot L }

-- AllLeRStepSwap : True/g=S g' step — the scan swap moves the tested ≤-element to the
-- new boundary; interior unchanged (NthSwapLLt), new far element = old scan (NthSwapLLo).
def AllLeRStepSwap : Term := prog{
  λ (Pivot : Nat). λ (Lo : Nat). λ (I : Nat). λ (G' : Nat). λ (L : List Nat).
    λ (E : Id Bool (Leb (NthL (Add Lo (S (Add I (S G')))) L) Pivot) True). λ (HL : AllLeR I (S Lo) Pivot L).
      AllLeRExtendFar I (S Lo) Pivot (SwapL (Add Lo (S I)) (Add Lo (S (Add I (S G')))) L)
        (AllLeRCong I (S Lo) Pivot L (SwapL (Add Lo (S I)) (Add Lo (S (Add I (S G')))) L)
          (λ (M : Nat). λ (Hm : Le (S M) I).
            NthSwapLLt (Add Lo (S I)) (Add Lo (S (Add I (S G')))) (Add M (S Lo)) L
              (LeRwL (Add Lo (S I)) (Add Lo (S (S M))) (S (Add M (S Lo)))
                (PosBridgeSs Lo M)
                (LeAddMonoL Lo (S (S M)) (S I) Hm)))
          HL)
        (LeRwL Pivot (NthL (Add Lo (S (Add I (S G')))) L) (NthL (Add I (S Lo)) (SwapL (Add Lo (S I)) (Add Lo (S (Add I (S G')))) L))
          (IdTrans Nat
            (NthL (Add Lo (S (Add I (S G')))) L)
            (NthL (Add Lo (S I)) (SwapL (Add Lo (S I)) (Add Lo (S (Add I (S G')))) L))
            (NthL (Add I (S Lo)) (SwapL (Add Lo (S I)) (Add Lo (S (Add I (S G')))) L))
            (IdSym Nat (NthL (Add Lo (S I)) (SwapL (Add Lo (S I)) (Add Lo (S (Add I (S G')))) L)) (NthL (Add Lo (S (Add I (S G')))) L)
              (NthSwapLLo (Add Lo (S I)) (Add Lo (S (Add I (S G')))) L (BndSl Lo I G')))
            (IdCongr Nat Nat (λ (Q : Nat). NthL Q (SwapL (Add Lo (S I)) (Add Lo (S (Add I (S G')))) L)) (Add Lo (S I)) (Add I (S Lo))
              (IdSym Nat (Add I (S Lo)) (Add Lo (S I)) (AddSwapSucc I Lo))))
          (LebTrueLe (NthL (Add Lo (S (Add I (S G')))) L) Pivot E)) }
def AllLeRStepSwapTy : Term := prog{
  Π (Pivot : Nat) → Π (Lo : Nat) → Π (I : Nat) → Π (G' : Nat) → Π (L : List Nat) →
    Id Bool (Leb (NthL (Add Lo (S (Add I (S G')))) L) Pivot) True → AllLeR I (S Lo) Pivot L →
    AllLeR (S I) (S Lo) Pivot (SwapL (Add Lo (S I)) (Add Lo (S (Add I (S G')))) L) }

-- PartScanRangeLAllLeR : the scanned ≤-region [lo, lo+finalI) is all ≤ pivot. Induction
-- on k mirroring count_partScanRangeL's bound threading; the AllLeR precondition grows via
-- the step helpers (leb fact from remember-scrutinee, threaded through the g-elim); the base
-- converts to offset lo via AllLeRBaseSwap / AllLeREmpty.
def PartScanRangeLAllLeR : Term := prog{
  λ (Pivot : Nat). λ (Lo : Nat). λ (K : Nat).
    elim K return (λ (Kz : Nat). Π (I : Nat) → Π (G : Nat) → Π (L : List Nat) →
        Le (Add Lo (S (Add Kz (Add I G)))) (Len L) →
        Id Nat (NthL Lo L) Pivot →
        AllLeR I (S Lo) Pivot L →
        AllLeR (PartScanIdxRangeL Pivot Lo Kz I G L) Lo Pivot (PartScanRangeL Pivot Lo Kz I G L)) {
      Z => λ (I : Nat). λ (G : Nat). λ (L : List Nat).
        λ (Hle : Le (Add Lo (S (Add Z (Add I G)))) (Len L)). λ (Hpv : Id Nat (NthL Lo L) Pivot). λ (HL : AllLeR I (S Lo) Pivot L).
        elim I return (λ (Iz : Nat).
            Le (Add Lo (S (Add Z (Add Iz G)))) (Len L) → Id Nat (NthL Lo L) Pivot → AllLeR Iz (S Lo) Pivot L →
            AllLeR Iz Lo Pivot (elim Iz return (λ (Iy : Nat). List Nat) { Z => L, S (I') Iih => SwapL Lo (Add Lo (S I')) L })) {
          Z => λ (Hle0 : Le (Add Lo (S (Add Z (Add Z G)))) (Len L)). λ (Hpv0 : Id Nat (NthL Lo L) Pivot). λ (HL0 : AllLeR Z (S Lo) Pivot L).
            AllLeREmpty Lo Pivot L,
          S (I') Iih => λ (Hle0 : Le (Add Lo (S (Add Z (Add (S I') G)))) (Len L)). λ (Hpv0 : Id Nat (NthL Lo L) Pivot). λ (HL0 : AllLeR (S I') (S Lo) Pivot L).
            AllLeRBaseSwap Pivot Lo I' L HL0
        } Hle Hpv HL,
      S (K') Ih => λ (I : Nat). λ (G : Nat). λ (L : List Nat).
        λ (Hle : Le (Add Lo (S (Add (S K') (Add I G)))) (Len L)). λ (Hpv : Id Nat (NthL Lo L) Pivot). λ (HL : AllLeR I (S Lo) Pivot L).
        elim (Leb (NthL (Add Lo (S (Add I G))) L) Pivot)
          return (λ (B : Bool). Id Bool (Leb (NthL (Add Lo (S (Add I G))) L) Pivot) B →
            AllLeR (elim B return (λ (Bw : Bool). Nat) {
                True => elim G return (λ (Gz : Nat). Nat) {
                  Z => PartScanIdxRangeL Pivot Lo K' (S I) Z L,
                  S (G') Gih => PartScanIdxRangeL Pivot Lo K' (S I) (S G') (SwapL (Add Lo (S I)) (Add Lo (S (Add I G))) L) },
                False => PartScanIdxRangeL Pivot Lo K' I (S G) L }) Lo Pivot
              (elim B return (λ (Bw : Bool). List Nat) {
                True => elim G return (λ (Gz : Nat). List Nat) {
                  Z => PartScanRangeL Pivot Lo K' (S I) Z L,
                  S (G') Gih => PartScanRangeL Pivot Lo K' (S I) (S G') (SwapL (Add Lo (S I)) (Add Lo (S (Add I G))) L) },
                False => PartScanRangeL Pivot Lo K' I (S G) L })) {
          True => λ (E : Id Bool (Leb (NthL (Add Lo (S (Add I G))) L) Pivot) True).
            (elim G return (λ (Gz : Nat).
                Id Bool (Leb (NthL (Add Lo (S (Add I Gz))) L) Pivot) True →
                Le (Add Lo (S (Add (S K') (Add I Gz)))) (Len L) →
                AllLeR (elim Gz return (λ (Gy : Nat). Nat) {
                    Z => PartScanIdxRangeL Pivot Lo K' (S I) Z L,
                    S (G') Gih => PartScanIdxRangeL Pivot Lo K' (S I) (S G') (SwapL (Add Lo (S I)) (Add Lo (S (Add I Gz))) L) }) Lo Pivot
                  (elim Gz return (λ (Gy : Nat). List Nat) {
                    Z => PartScanRangeL Pivot Lo K' (S I) Z L,
                    S (G') Gih => PartScanRangeL Pivot Lo K' (S I) (S G') (SwapL (Add Lo (S I)) (Add Lo (S (Add I Gz))) L) })) {
              Z => λ (E0 : Id Bool (Leb (NthL (Add Lo (S (Add I Z))) L) Pivot) True). λ (HleZ : Le (Add Lo (S (Add (S K') (Add I Z)))) (Len L)).
                Ih (S I) Z L
                  (LeRwL (Len L) (Add Lo (S (Add (S K') (Add I Z)))) (Add Lo (S (Add K' (Add (S I) Z))))
                    (IdCongr Nat Nat (λ (A : Nat). Add Lo (S A)) (Add (S K') (Add I Z)) (Add K' (Add (S I) Z)) (HshiftTrue K' I Z))
                    HleZ)
                  Hpv
                  (AllLeRStepTZ Pivot Lo I L E0 HL),
              S (G') Gih => λ (E0 : Id Bool (Leb (NthL (Add Lo (S (Add I (S G')))) L) Pivot) True). λ (HleS : Le (Add Lo (S (Add (S K') (Add I (S G'))))) (Len L)).
                Ih (S I) (S G') (SwapL (Add Lo (S I)) (Add Lo (S (Add I (S G')))) L)
                  (LeRwR (Add Lo (S (Add K' (Add (S I) (S G'))))) (Len L)
                     (Len (SwapL (Add Lo (S I)) (Add Lo (S (Add I (S G')))) L))
                     (IdSym Nat (Len (SwapL (Add Lo (S I)) (Add Lo (S (Add I (S G')))) L)) (Len L)
                       (LenSwapL (Add Lo (S I)) (Add Lo (S (Add I (S G')))) L))
                     (LeRwL (Len L) (Add Lo (S (Add (S K') (Add I (S G'))))) (Add Lo (S (Add K' (Add (S I) (S G')))))
                       (IdCongr Nat Nat (λ (A : Nat). Add Lo (S A)) (Add (S K') (Add I (S G'))) (Add K' (Add (S I) (S G'))) (HshiftTrue K' I (S G')))
                       HleS))
                  (IdTrans Nat (NthL Lo (SwapL (Add Lo (S I)) (Add Lo (S (Add I (S G')))) L)) (NthL Lo L) Pivot
                    (NthSwapLLt (Add Lo (S I)) (Add Lo (S (Add I (S G')))) Lo L (LeAddSucc Lo I))
                    Hpv)
                  (AllLeRStepSwap Pivot Lo I G' L E0 HL)
            }) E Hle,
          False => λ (Efalse : Id Bool (Leb (NthL (Add Lo (S (Add I G))) L) Pivot) False).
            Ih I (S G) L
              (LeRwL (Len L) (Add Lo (S (Add (S K') (Add I G)))) (Add Lo (S (Add K' (Add I (S G)))))
                (IdCongr Nat Nat (λ (A : Nat). Add Lo (S A)) (Add (S K') (Add I G)) (Add K' (Add I (S G))) (HshiftFalse K' I G))
                Hle)
              Hpv
              HL
        } Refl
    } }
def PartScanRangeLAllLeRTy : Term := prog{
  Π (Pivot : Nat) → Π (Lo : Nat) → Π (K : Nat) → Π (I : Nat) → Π (G : Nat) → Π (L : List Nat) →
    Le (Add Lo (S (Add K (Add I G)))) (Len L) →
    Id Nat (NthL Lo L) Pivot →
    AllLeR I (S Lo) Pivot L →
    AllLeR (PartScanIdxRangeL Pivot Lo K I G L) Lo Pivot (PartScanRangeL Pivot Lo K I G L) }
/-! ## AllGtR (gap-side) region invariant — the mirror of the ≤-region (§22, M22-c step 2)

    The gap's OFFSET shifts each step (`Add (S i) lo` → `Add (S (S i)) lo`), unlike the
    ≤-region's fixed `S lo`, and the asymmetry flips: the gap GROWS in the False branch
    (scan element > pivot, `AllGtRStepFalse` via LebFalseGt + extend_far), the True/Sg'
    swap ROTATES the old boundary (first gap element) to the gap's far end
    (`AllGtRStepSwap` via NthSwapLHi, needing a len bound), and True/g=0 is the empty
    gap (`AllGtREmpty`). `OffBridge` / `PosBridgeScan` / `BndGapUpper` carry the
    (messier) offset arithmetic. -/

def AllGtRExtendFar : Term := prog{
  λ (W : Nat). λ (Lo : Nat). λ (P : Nat). λ (L : List Nat).
    λ (H : AllGtR W Lo P L). λ (Hnew : Le (S P) (NthL (Add W Lo) L)).
    λ (M : Nat).
      elim (Leb (S M) W) return (λ (B : Bool). Id Bool (Leb (S M) W) B → Le (S M) (S W) → Le (S P) (NthL (Add M Lo) L)) {
        True => λ (E : Id Bool (Leb (S M) W) True). λ (Hm : Le (S M) (S W)). H M (LebTrueLe (S M) W E),
        False => λ (E : Id Bool (Leb (S M) W) False). λ (Hm : Le (S M) (S W)).
          LeRwR (S P) (NthL (Add W Lo) L) (NthL (Add M Lo) L)
            (IdCongr Nat Nat (λ (Q : Nat). NthL Q L) (Add W Lo) (Add M Lo)
              (IdCongr Nat Nat (λ (Z0 : Nat). Add Z0 Lo) W M (IdSym Nat M W (LeAntisym M W Hm (LebFalseGt (S M) W E)))))
            Hnew
      } Refl }
def AllGtRExtendFarTy : Term := prog{
  Π (W : Nat) → Π (Lo : Nat) → Π (P : Nat) → Π (L : List Nat) →
    AllGtR W Lo P L → Le (S P) (NthL (Add W Lo) L) → AllGtR (S W) Lo P L }

def AllGtRCong : Term := prog{
  λ (W : Nat). λ (Off : Nat). λ (P : Nat). λ (L : List Nat). λ (L' : List Nat).
    λ (Heq : Π (M : Nat) → Le (S M) W → Id Nat (NthL (Add M Off) L') (NthL (Add M Off) L)).
    λ (H : AllGtR W Off P L).
    λ (M : Nat). λ (Hm : Le (S M) W).
      LeRwR (S P) (NthL (Add M Off) L) (NthL (Add M Off) L')
        (IdSym Nat (NthL (Add M Off) L') (NthL (Add M Off) L) (Heq M Hm))
        (H M Hm) }
def AllGtRCongTy : Term := prog{
  Π (W : Nat) → Π (Off : Nat) → Π (P : Nat) → Π (L : List Nat) → Π (L' : List Nat) →
    (Π (M : Nat) → Le (S M) W → Id Nat (NthL (Add M Off) L') (NthL (Add M Off) L)) →
    AllGtR W Off P L → AllGtR W Off P L' }

def OffBridge : Term := prog{
  λ (Lo : Nat). λ (I' : Nat).
    IdCongr Nat Nat (λ (Z0 : Nat). S Z0) (S (Add I' Lo)) (Add Lo (S I'))
      (IdTrans Nat (S (Add I' Lo)) (S (Add Lo I')) (Add Lo (S I'))
        (IdCongr Nat Nat (λ (Z0 : Nat). S Z0) (Add I' Lo) (Add Lo I') (AddComm I' Lo))
        (IdSym Nat (Add Lo (S I')) (S (Add Lo I')) (AddSucc Lo I'))) }
def OffBridgeTy : Term := prog{ Π (Lo : Nat) → Π (I' : Nat) → Id Nat (Add (S (S I')) Lo) (S (Add Lo (S I'))) }

def AllGtRBaseSwap : Term := prog{
  λ (Pivot : Nat). λ (Lo : Nat). λ (I' : Nat). λ (G : Nat). λ (L : List Nat).
    λ (HG : AllGtR G (Add (S (S I')) Lo) Pivot L).
      AllGtRCong G (Add (S (S I')) Lo) Pivot L (SwapL Lo (Add Lo (S I')) L)
        (λ (M : Nat). λ (Hm : Le (S M) G).
          NthSwapLGt Lo (Add Lo (S I')) (Add M (Add (S (S I')) Lo)) L
            (LeRwL (Add M (Add (S (S I')) Lo)) (Add (S (S I')) Lo) (S (Add Lo (S I')))
              (OffBridge Lo I')
              (LeAddL (Add (S (S I')) Lo) M)))
        HG }
def AllGtRBaseSwapTy : Term := prog{
  Π (Pivot : Nat) → Π (Lo : Nat) → Π (I' : Nat) → Π (G : Nat) → Π (L : List Nat) →
    AllGtR G (Add (S (S I')) Lo) Pivot L → AllGtR G (Add (S (S I')) Lo) Pivot (SwapL Lo (Add Lo (S I')) L) }

def PosBridgeScan : Term := prog{
  λ (Lo : Nat). λ (I : Nat). λ (G : Nat).
    IdTrans Nat (Add Lo (S (Add I G))) (S (Add Lo (Add I G))) (Add G (Add (S I) Lo))
      (AddSucc Lo (Add I G))
      (IdTrans Nat (S (Add Lo (Add I G))) (S (Add G (Add I Lo))) (Add G (Add (S I) Lo))
        (IdCongr Nat Nat (λ (Z0 : Nat). S Z0) (Add Lo (Add I G)) (Add G (Add I Lo))
          (IdTrans Nat (Add Lo (Add I G)) (Add (Add Lo I) G) (Add G (Add I Lo))
            (IdSym Nat (Add (Add Lo I) G) (Add Lo (Add I G)) (AddAssoc Lo I G))
            (IdTrans Nat (Add (Add Lo I) G) (Add G (Add Lo I)) (Add G (Add I Lo))
              (AddComm (Add Lo I) G)
              (IdCongr Nat Nat (λ (Z0 : Nat). Add G Z0) (Add Lo I) (Add I Lo) (AddComm Lo I)))))
        (IdSym Nat (Add G (Add (S I) Lo)) (S (Add G (Add I Lo))) (AddSucc G (Add I Lo)))) }
def PosBridgeScanTy : Term := prog{ Π (Lo : Nat) → Π (I : Nat) → Π (G : Nat) → Id Nat (Add Lo (S (Add I G))) (Add G (Add (S I) Lo)) }

def AllGtRStepFalse : Term := prog{
  λ (Pivot : Nat). λ (Lo : Nat). λ (I : Nat). λ (G : Nat). λ (L : List Nat).
    λ (Efalse : Id Bool (Leb (NthL (Add Lo (S (Add I G))) L) Pivot) False). λ (HG : AllGtR G (Add (S I) Lo) Pivot L).
      AllGtRExtendFar G (Add (S I) Lo) Pivot L HG
        (LeRwR (S Pivot) (NthL (Add Lo (S (Add I G))) L) (NthL (Add G (Add (S I) Lo)) L)
          (IdCongr Nat Nat (λ (Q : Nat). NthL Q L) (Add Lo (S (Add I G))) (Add G (Add (S I) Lo)) (PosBridgeScan Lo I G))
          (LebFalseGt (NthL (Add Lo (S (Add I G))) L) Pivot Efalse)) }
def AllGtRStepFalseTy : Term := prog{
  Π (Pivot : Nat) → Π (Lo : Nat) → Π (I : Nat) → Π (G : Nat) → Π (L : List Nat) →
    Id Bool (Leb (NthL (Add Lo (S (Add I G))) L) Pivot) False → AllGtR G (Add (S I) Lo) Pivot L →
    AllGtR (S G) (Add (S I) Lo) Pivot L }

def BndGapUpper : Term := prog{
  λ (Lo : Nat). λ (I : Nat). λ (G' : Nat). λ (M : Nat). λ (Hm : Le (S M) G').
    LeRwR (S (Add M (Add (S (S I)) Lo))) (Add Lo (S (S (Add I G')))) (Add Lo (S (Add I (S G'))))
      (IdCongr Nat Nat (λ (Z0 : Nat). Add Lo (S Z0)) (S (Add I G')) (Add I (S G')) (IdSym Nat (Add I (S G')) (S (Add I G')) (AddSucc I G')))
      (LeRwL (Add Lo (S (S (Add I G')))) (Add Lo (S (S (S (Add I M))))) (S (Add M (Add (S (S I)) Lo)))
        (IdTrans Nat (Add Lo (S (S (S (Add I M))))) (S (Add Lo (S (S (Add I M))))) (S (Add M (Add (S (S I)) Lo)))
          (AddSucc Lo (S (S (Add I M))))
          (IdCongr Nat Nat (λ (Z0 : Nat). S Z0) (Add Lo (S (S (Add I M)))) (Add M (Add (S (S I)) Lo)) (PosBridgeScan Lo (S I) M)))
        (LeAddMonoL Lo (S (S (S (Add I M)))) (S (S (Add I G')))
          (LeRwL (Add I G') (Add I (S M)) (S (Add I M)) (AddSucc I M) (LeAddMonoL I (S M) G' Hm)))) }
def BndGapUpperTy : Term := prog{
  Π (Lo : Nat) → Π (I : Nat) → Π (G' : Nat) → Π (M : Nat) → Le (S M) G' →
    Le (S (Add M (Add (S (S I)) Lo))) (Add Lo (S (Add I (S G')))) }

def AllGtRStepSwap : Term := prog{
  λ (Pivot : Nat). λ (Lo : Nat). λ (I : Nat). λ (G' : Nat). λ (L : List Nat).
    λ (Hlen : Le (S (Add Lo (S (Add I (S G'))))) (Len L)).
    λ (E : Id Bool (Leb (NthL (Add Lo (S (Add I (S G')))) L) Pivot) True). λ (HG : AllGtR (S G') (Add (S I) Lo) Pivot L).
      AllGtRExtendFar G' (Add (S (S I)) Lo) Pivot (SwapL (Add Lo (S I)) (Add Lo (S (Add I (S G')))) L)
        (AllGtRCong G' (Add (S (S I)) Lo) Pivot L (SwapL (Add Lo (S I)) (Add Lo (S (Add I (S G')))) L)
          (λ (M : Nat). λ (Hm : Le (S M) G').
            NthSwapLMid (Add Lo (S I)) (Add Lo (S (Add I (S G')))) (Add M (Add (S (S I)) Lo)) L
              (LeRwL (Add M (Add (S (S I)) Lo)) (Add (S (S I)) Lo) (S (Add Lo (S I)))
                (OffBridge Lo I)
                (LeAddL (Add (S (S I)) Lo) M))
              (BndGapUpper Lo I G' M Hm))
          (λ (M : Nat). λ (Hm : Le (S M) G').
            LeRwR (S Pivot) (NthL (Add (S M) (Add (S I) Lo)) L) (NthL (Add M (Add (S (S I)) Lo)) L)
              (IdCongr Nat Nat (λ (Q : Nat). NthL Q L) (Add (S M) (Add (S I) Lo)) (Add M (Add (S (S I)) Lo))
                (IdSym Nat (Add M (Add (S (S I)) Lo)) (Add (S M) (Add (S I) Lo)) (AddSucc M (S (Add I Lo)))))
              (HG (S M) Hm)))
        (LeRwR (S Pivot) (NthL (Add Lo (S I)) L) (NthL (Add G' (Add (S (S I)) Lo)) (SwapL (Add Lo (S I)) (Add Lo (S (Add I (S G')))) L))
          (IdTrans Nat
            (NthL (Add Lo (S I)) L)
            (NthL (Add Lo (S (Add I (S G')))) (SwapL (Add Lo (S I)) (Add Lo (S (Add I (S G')))) L))
            (NthL (Add G' (Add (S (S I)) Lo)) (SwapL (Add Lo (S I)) (Add Lo (S (Add I (S G')))) L))
            (IdSym Nat (NthL (Add Lo (S (Add I (S G')))) (SwapL (Add Lo (S I)) (Add Lo (S (Add I (S G')))) L)) (NthL (Add Lo (S I)) L)
              (NthSwapLHi (Add Lo (S I)) (Add Lo (S (Add I (S G')))) L (BndSl Lo I G') Hlen))
            (IdCongr Nat Nat (λ (Q : Nat). NthL Q (SwapL (Add Lo (S I)) (Add Lo (S (Add I (S G')))) L)) (Add Lo (S (Add I (S G')))) (Add G' (Add (S (S I)) Lo))
              (IdTrans Nat (Add Lo (S (Add I (S G')))) (Add Lo (S (S (Add I G')))) (Add G' (Add (S (S I)) Lo))
                (IdCongr Nat Nat (λ (Z0 : Nat). Add Lo (S Z0)) (Add I (S G')) (S (Add I G')) (AddSucc I G'))
                (PosBridgeScan Lo (S I) G'))))
          (LeRwR (S Pivot) (NthL (Add (S I) Lo) L) (NthL (Add Lo (S I)) L)
            (IdCongr Nat Nat (λ (Q : Nat). NthL Q L) (Add (S I) Lo) (Add Lo (S I)) (AddComm (S I) Lo))
            (AllGtRHead G' (Add (S I) Lo) Pivot L HG))) }
def AllGtRStepSwapTy : Term := prog{
  Π (Pivot : Nat) → Π (Lo : Nat) → Π (I : Nat) → Π (G' : Nat) → Π (L : List Nat) →
    Le (S (Add Lo (S (Add I (S G'))))) (Len L) →
    Id Bool (Leb (NthL (Add Lo (S (Add I (S G')))) L) Pivot) True → AllGtR (S G') (Add (S I) Lo) Pivot L →
    AllGtR (S G') (Add (S (S I)) Lo) Pivot (SwapL (Add Lo (S I)) (Add Lo (S (Add I (S G')))) L) }

-- PartScanRangeLAllGtR : the scanned gap [lo+1+finalI, …) is all > pivot. Mirror of allLeR;
-- the conclusion OFFSET also depends on leb (motive carries three elim b). NOTE the True arm
-- threads hG through the g-elim (the precondition is indexed by g, refined to S g' in the swap
-- branch) — unlike allLeR whose precondition was indexed by i.
def PartScanRangeLAllGtR : Term := prog{
  λ (Pivot : Nat). λ (Lo : Nat). λ (K : Nat).
    elim K return (λ (Kz : Nat). Π (I : Nat) → Π (G : Nat) → Π (L : List Nat) →
        Le (Add Lo (S (Add Kz (Add I G)))) (Len L) →
        Id Nat (NthL Lo L) Pivot →
        AllGtR G (Add (S I) Lo) Pivot L →
        AllGtR (PartScanGapRangeL Pivot Lo Kz I G L) (Add (S (PartScanIdxRangeL Pivot Lo Kz I G L)) Lo) Pivot (PartScanRangeL Pivot Lo Kz I G L)) {
      Z => λ (I : Nat). λ (G : Nat). λ (L : List Nat).
        λ (Hle : Le (Add Lo (S (Add Z (Add I G)))) (Len L)). λ (Hpv : Id Nat (NthL Lo L) Pivot). λ (HG : AllGtR G (Add (S I) Lo) Pivot L).
        elim I return (λ (Iz : Nat).
            Le (Add Lo (S (Add Z (Add Iz G)))) (Len L) → Id Nat (NthL Lo L) Pivot → AllGtR G (Add (S Iz) Lo) Pivot L →
            AllGtR G (Add (S Iz) Lo) Pivot (elim Iz return (λ (Iy : Nat). List Nat) { Z => L, S (I') Iih => SwapL Lo (Add Lo (S I')) L })) {
          Z => λ (Hle0 : Le (Add Lo (S (Add Z (Add Z G)))) (Len L)). λ (Hpv0 : Id Nat (NthL Lo L) Pivot). λ (HG0 : AllGtR G (Add (S Z) Lo) Pivot L).
            HG0,
          S (I') Iih => λ (Hle0 : Le (Add Lo (S (Add Z (Add (S I') G)))) (Len L)). λ (Hpv0 : Id Nat (NthL Lo L) Pivot). λ (HG0 : AllGtR G (Add (S (S I')) Lo) Pivot L).
            AllGtRBaseSwap Pivot Lo I' G L HG0
        } Hle Hpv HG,
      S (K') Ih => λ (I : Nat). λ (G : Nat). λ (L : List Nat).
        λ (Hle : Le (Add Lo (S (Add (S K') (Add I G)))) (Len L)). λ (Hpv : Id Nat (NthL Lo L) Pivot). λ (HG : AllGtR G (Add (S I) Lo) Pivot L).
        elim (Leb (NthL (Add Lo (S (Add I G))) L) Pivot)
          return (λ (B : Bool). Id Bool (Leb (NthL (Add Lo (S (Add I G))) L) Pivot) B →
            AllGtR (elim B return (λ (Bw : Bool). Nat) {
                True => elim G return (λ (Gz : Nat). Nat) {
                  Z => PartScanGapRangeL Pivot Lo K' (S I) Z L,
                  S (G') Gih => PartScanGapRangeL Pivot Lo K' (S I) (S G') (SwapL (Add Lo (S I)) (Add Lo (S (Add I G))) L) },
                False => PartScanGapRangeL Pivot Lo K' I (S G) L })
              (Add (S (elim B return (λ (Bw : Bool). Nat) {
                True => elim G return (λ (Gz : Nat). Nat) {
                  Z => PartScanIdxRangeL Pivot Lo K' (S I) Z L,
                  S (G') Gih => PartScanIdxRangeL Pivot Lo K' (S I) (S G') (SwapL (Add Lo (S I)) (Add Lo (S (Add I G))) L) },
                False => PartScanIdxRangeL Pivot Lo K' I (S G) L })) Lo) Pivot
              (elim B return (λ (Bw : Bool). List Nat) {
                True => elim G return (λ (Gz : Nat). List Nat) {
                  Z => PartScanRangeL Pivot Lo K' (S I) Z L,
                  S (G') Gih => PartScanRangeL Pivot Lo K' (S I) (S G') (SwapL (Add Lo (S I)) (Add Lo (S (Add I G))) L) },
                False => PartScanRangeL Pivot Lo K' I (S G) L })) {
          True => λ (E : Id Bool (Leb (NthL (Add Lo (S (Add I G))) L) Pivot) True).
            (elim G return (λ (Gz : Nat).
                Id Bool (Leb (NthL (Add Lo (S (Add I Gz))) L) Pivot) True →
                Le (Add Lo (S (Add (S K') (Add I Gz)))) (Len L) →
                AllGtR Gz (Add (S I) Lo) Pivot L →
                AllGtR (elim Gz return (λ (Gy : Nat). Nat) {
                    Z => PartScanGapRangeL Pivot Lo K' (S I) Z L,
                    S (G') Gih => PartScanGapRangeL Pivot Lo K' (S I) (S G') (SwapL (Add Lo (S I)) (Add Lo (S (Add I Gz))) L) })
                  (Add (S (elim Gz return (λ (Gy : Nat). Nat) {
                    Z => PartScanIdxRangeL Pivot Lo K' (S I) Z L,
                    S (G') Gih => PartScanIdxRangeL Pivot Lo K' (S I) (S G') (SwapL (Add Lo (S I)) (Add Lo (S (Add I Gz))) L) })) Lo) Pivot
                  (elim Gz return (λ (Gy : Nat). List Nat) {
                    Z => PartScanRangeL Pivot Lo K' (S I) Z L,
                    S (G') Gih => PartScanRangeL Pivot Lo K' (S I) (S G') (SwapL (Add Lo (S I)) (Add Lo (S (Add I Gz))) L) })) {
              Z => λ (E0 : Id Bool (Leb (NthL (Add Lo (S (Add I Z))) L) Pivot) True). λ (HleZ : Le (Add Lo (S (Add (S K') (Add I Z)))) (Len L)). λ (HG0 : AllGtR Z (Add (S I) Lo) Pivot L).
                Ih (S I) Z L
                  (LeRwL (Len L) (Add Lo (S (Add (S K') (Add I Z)))) (Add Lo (S (Add K' (Add (S I) Z))))
                    (IdCongr Nat Nat (λ (A : Nat). Add Lo (S A)) (Add (S K') (Add I Z)) (Add K' (Add (S I) Z)) (HshiftTrue K' I Z))
                    HleZ)
                  Hpv
                  (AllGtREmpty (Add (S (S I)) Lo) Pivot L),
              S (G') Gih => λ (E0 : Id Bool (Leb (NthL (Add Lo (S (Add I (S G')))) L) Pivot) True). λ (HleS : Le (Add Lo (S (Add (S K') (Add I (S G'))))) (Len L)). λ (HG0 : AllGtR (S G') (Add (S I) Lo) Pivot L).
                Ih (S I) (S G') (SwapL (Add Lo (S I)) (Add Lo (S (Add I (S G')))) L)
                  (LeRwR (Add Lo (S (Add K' (Add (S I) (S G'))))) (Len L)
                     (Len (SwapL (Add Lo (S I)) (Add Lo (S (Add I (S G')))) L))
                     (IdSym Nat (Len (SwapL (Add Lo (S I)) (Add Lo (S (Add I (S G')))) L)) (Len L)
                       (LenSwapL (Add Lo (S I)) (Add Lo (S (Add I (S G')))) L))
                     (LeRwL (Len L) (Add Lo (S (Add (S K') (Add I (S G'))))) (Add Lo (S (Add K' (Add (S I) (S G')))))
                       (IdCongr Nat Nat (λ (A : Nat). Add Lo (S A)) (Add (S K') (Add I (S G'))) (Add K' (Add (S I) (S G'))) (HshiftTrue K' I (S G')))
                       HleS))
                  (IdTrans Nat (NthL Lo (SwapL (Add Lo (S I)) (Add Lo (S (Add I (S G')))) L)) (NthL Lo L) Pivot
                    (NthSwapLLt (Add Lo (S I)) (Add Lo (S (Add I (S G')))) Lo L (LeAddSucc Lo I))
                    Hpv)
                  (AllGtRStepSwap Pivot Lo I G' L
                    (LeTrans (S (Add Lo (S (Add I (S G'))))) (Add Lo (S (S (Add K' (Add I (S G')))))) (Len L)
                      (LeRwL (Add Lo (S (S (Add K' (Add I (S G'))))))
                        (Add Lo (S (S (Add I (S G'))))) (S (Add Lo (S (Add I (S G')))))
                        (AddSucc Lo (S (Add I (S G'))))
                        (LeAddMonoL Lo (S (S (Add I (S G')))) (S (S (Add K' (Add I (S G')))))
                          (LeAddL (Add I (S G')) K')))
                      HleS)
                    E0 HG0)
            }) E Hle HG,
          False => λ (Efalse : Id Bool (Leb (NthL (Add Lo (S (Add I G))) L) Pivot) False).
            Ih I (S G) L
              (LeRwL (Len L) (Add Lo (S (Add (S K') (Add I G)))) (Add Lo (S (Add K' (Add I (S G)))))
                (IdCongr Nat Nat (λ (A : Nat). Add Lo (S A)) (Add (S K') (Add I G)) (Add K' (Add I (S G))) (HshiftFalse K' I G))
                Hle)
              Hpv
              (AllGtRStepFalse Pivot Lo I G L Efalse HG)
        } Refl
    } }
def PartScanRangeLAllGtRTy : Term := prog{
  Π (Pivot : Nat) → Π (Lo : Nat) → Π (K : Nat) → Π (I : Nat) → Π (G : Nat) → Π (L : List Nat) →
    Le (Add Lo (S (Add K (Add I G)))) (Len L) →
    Id Nat (NthL Lo L) Pivot →
    AllGtR G (Add (S I) Lo) Pivot L →
    AllGtR (PartScanGapRangeL Pivot Lo K I G L) (Add (S (PartScanIdxRangeL Pivot Lo K I G L)) Lo) Pivot (PartScanRangeL Pivot Lo K I G L) }
-- The pivot ends at position `Add finalI lo`. Induction on k mirroring
-- count_partScanRangeL's bound threading, PLUS threading the pivot-fact
-- `Id (NthL lo l) pivot` (updated across the step swap via NthSwapLLt — lo is below
-- both swap indices). Base (k=Z) places the pivot: i=Z is the pivot-fact directly;
-- i=S i' swaps lo↔lo+i, so NthSwapLHi reads old-lo (=pivot) at the boundary, bridged
-- from index-first `Add (S i') lo` to offset-first `Add lo (S i')` by AddComm.
def PartScanRangeLPivot : Term := prog{
  λ (Pivot : Nat). λ (Lo : Nat). λ (K : Nat).
    elim K return (λ (Kz : Nat). Π (I : Nat) → Π (G : Nat) → Π (L : List Nat) →
        Le (Add Lo (S (Add Kz (Add I G)))) (Len L) →
        Id Nat (NthL Lo L) Pivot →
        Id Nat (NthL (Add (PartScanIdxRangeL Pivot Lo Kz I G L) Lo) (PartScanRangeL Pivot Lo Kz I G L)) Pivot) {
      Z => λ (I : Nat). λ (G : Nat). λ (L : List Nat).
        λ (Hle : Le (Add Lo (S (Add Z (Add I G)))) (Len L)). λ (Hpv : Id Nat (NthL Lo L) Pivot).
        elim I return (λ (Iz : Nat).
            Le (Add Lo (S (Add Z (Add Iz G)))) (Len L) →
            Id Nat (NthL (Add Iz Lo) (elim Iz return (λ (Iy : Nat). List Nat) { Z => L, S (I') Iih => SwapL Lo (Add Lo (S I')) L })) Pivot) {
          Z => λ (Hle0 : Le (Add Lo (S (Add Z (Add Z G)))) (Len L)). Hpv,
          S (I') Iih => λ (Hle0 : Le (Add Lo (S (Add Z (Add (S I') G)))) (Len L)).
            IdTrans Nat
              (NthL (Add (S I') Lo) (SwapL Lo (Add Lo (S I')) L))
              (NthL (Add Lo (S I')) (SwapL Lo (Add Lo (S I')) L))
              Pivot
              (IdCongr Nat Nat (λ (P : Nat). NthL P (SwapL Lo (Add Lo (S I')) L)) (Add (S I') Lo) (Add Lo (S I')) (AddComm (S I') Lo))
              (IdTrans Nat
                (NthL (Add Lo (S I')) (SwapL Lo (Add Lo (S I')) L))
                (NthL Lo L)
                Pivot
                (NthSwapLHi Lo (Add Lo (S I')) L (LeAddSucc Lo I')
                  (LeTrans (S (Add Lo (S I'))) (Add Lo (S (S (Add I' G)))) (Len L)
                    (LeRwL (Add Lo (S (S (Add I' G)))) (Add Lo (S (S I'))) (S (Add Lo (S I')))
                      (AddSucc Lo (S I'))
                      (LeAddMonoL Lo (S (S I')) (S (S (Add I' G))) (LeAdd I' G)))
                    Hle0))
                Hpv)
        } Hle,
      S (K') Ih => λ (I : Nat). λ (G : Nat). λ (L : List Nat).
        λ (Hle : Le (Add Lo (S (Add (S K') (Add I G)))) (Len L)). λ (Hpv : Id Nat (NthL Lo L) Pivot).
        elim (Leb (NthL (Add Lo (S (Add I G))) L) Pivot)
          return (λ (W : Bool). Id Nat
            (NthL (Add (elim W return (λ (Ww : Bool). Nat) {
                True => elim G return (λ (Gz : Nat). Nat) {
                  Z => PartScanIdxRangeL Pivot Lo K' (S I) Z L,
                  S (G') Gih => PartScanIdxRangeL Pivot Lo K' (S I) (S G') (SwapL (Add Lo (S I)) (Add Lo (S (Add I G))) L) },
                False => PartScanIdxRangeL Pivot Lo K' I (S G) L }) Lo)
              (elim W return (λ (Ww : Bool). List Nat) {
                True => elim G return (λ (Gz : Nat). List Nat) {
                  Z => PartScanRangeL Pivot Lo K' (S I) Z L,
                  S (G') Gih => PartScanRangeL Pivot Lo K' (S I) (S G') (SwapL (Add Lo (S I)) (Add Lo (S (Add I G))) L) },
                False => PartScanRangeL Pivot Lo K' I (S G) L }))
            Pivot) {
          True =>
            (elim G return (λ (Gz : Nat).
                Le (Add Lo (S (Add (S K') (Add I Gz)))) (Len L) →
                Id Nat (NthL (Add (elim Gz return (λ (Gy : Nat). Nat) {
                    Z => PartScanIdxRangeL Pivot Lo K' (S I) Z L,
                    S (G') Gih => PartScanIdxRangeL Pivot Lo K' (S I) (S G') (SwapL (Add Lo (S I)) (Add Lo (S (Add I Gz))) L) }) Lo)
                  (elim Gz return (λ (Gy : Nat). List Nat) {
                    Z => PartScanRangeL Pivot Lo K' (S I) Z L,
                    S (G') Gih => PartScanRangeL Pivot Lo K' (S I) (S G') (SwapL (Add Lo (S I)) (Add Lo (S (Add I Gz))) L) })) Pivot) {
              Z => λ (HleZ : Le (Add Lo (S (Add (S K') (Add I Z)))) (Len L)).
                Ih (S I) Z L
                  (LeRwL (Len L)
                    (Add Lo (S (Add (S K') (Add I Z))))
                    (Add Lo (S (Add K' (Add (S I) Z))))
                    (IdCongr Nat Nat (λ (A : Nat). Add Lo (S A))
                      (Add (S K') (Add I Z)) (Add K' (Add (S I) Z)) (HshiftTrue K' I Z))
                    HleZ)
                  Hpv,
              S (G') Gih => λ (HleS : Le (Add Lo (S (Add (S K') (Add I (S G'))))) (Len L)).
                Ih (S I) (S G') (SwapL (Add Lo (S I)) (Add Lo (S (Add I (S G')))) L)
                  (LeRwR (Add Lo (S (Add K' (Add (S I) (S G'))))) (Len L)
                     (Len (SwapL (Add Lo (S I)) (Add Lo (S (Add I (S G')))) L))
                     (IdSym Nat (Len (SwapL (Add Lo (S I)) (Add Lo (S (Add I (S G')))) L)) (Len L)
                       (LenSwapL (Add Lo (S I)) (Add Lo (S (Add I (S G')))) L))
                     (LeRwL (Len L)
                       (Add Lo (S (Add (S K') (Add I (S G')))))
                       (Add Lo (S (Add K' (Add (S I) (S G')))))
                       (IdCongr Nat Nat (λ (A : Nat). Add Lo (S A))
                         (Add (S K') (Add I (S G'))) (Add K' (Add (S I) (S G'))) (HshiftTrue K' I (S G')))
                       HleS))
                  (IdTrans Nat (NthL Lo (SwapL (Add Lo (S I)) (Add Lo (S (Add I (S G')))) L)) (NthL Lo L) Pivot
                    (NthSwapLLt (Add Lo (S I)) (Add Lo (S (Add I (S G')))) Lo L (LeAddSucc Lo I))
                    Hpv)
            }) Hle,
          False =>
            Ih I (S G) L
              (LeRwL (Len L)
                (Add Lo (S (Add (S K') (Add I G))))
                (Add Lo (S (Add K' (Add I (S G)))))
                (IdCongr Nat Nat (λ (A : Nat). Add Lo (S A))
                  (Add (S K') (Add I G)) (Add K' (Add I (S G))) (HshiftFalse K' I G))
                Hle)
              Hpv
        }
    } }
def PartScanRangeLPivotTy : Term := prog{
  Π (Pivot : Nat) → Π (Lo : Nat) → Π (K : Nat) → Π (I : Nat) → Π (G : Nat) → Π (L : List Nat) →
    Le (Add Lo (S (Add K (Add I G)))) (Len L) →
    Id Nat (NthL Lo L) Pivot →
    Id Nat (NthL (Add (PartScanIdxRangeL Pivot Lo K I G L) Lo) (PartScanRangeL Pivot Lo K I G L)) Pivot }
-- PartitionPivot : wrapper of PartScanRangeLPivot at i=g=0 (preconditions vacuous;
-- pivot-fact is Refl since the pivot is nth lo l; one AddZero nudge on the bound).
def PartitionPivot : Term := prog{
  λ (Lo : Nat). λ (Cnt : Nat). λ (L : List Nat).
    elim Cnt return (λ (Cz : Nat).
        Le (Add Lo Cz) (Len L) →
        Id Nat (NthL (Add (elim Cz return (λ (Cy : Nat). Nat) { Z => Z, S (Cnt') Rec => PartScanIdxRangeL (NthL Lo L) Lo Cnt' Z Z L }) Lo)
                    (elim Cz return (λ (Cy : Nat). List Nat) { Z => L, S (Cnt') Rec => PartScanRangeL (NthL Lo L) Lo Cnt' Z Z L })) (NthL Lo L)) {
      Z => λ (Hb : Le (Add Lo Z) (Len L)). Refl,
      S (Cnt') Rec => λ (Hb : Le (Add Lo (S Cnt')) (Len L)).
        PartScanRangeLPivot (NthL Lo L) Lo Cnt' Z Z L
          (LeRwL (Len L) (Add Lo (S Cnt')) (Add Lo (S (Add Cnt' Z)))
            (IdCongr Nat Nat (λ (A : Nat). Add Lo (S A)) Cnt' (Add Cnt' Z)
              (IdSym Nat (Add Cnt' Z) Cnt' (AddZero Cnt')))
            Hb)
          Refl } }

-- PartitionAllLeR : wrapper of PartScanRangeLAllLeR at i=g=0 (AllLeR Z precondition vacuous).
def PartitionAllLeR : Term := prog{
  λ (Lo : Nat). λ (Cnt : Nat). λ (L : List Nat).
    elim Cnt return (λ (Cz : Nat).
        Le (Add Lo Cz) (Len L) →
        AllLeR (elim Cz return (λ (Cy : Nat). Nat) { Z => Z, S (Cnt') Rec => PartScanIdxRangeL (NthL Lo L) Lo Cnt' Z Z L }) Lo (NthL Lo L)
               (elim Cz return (λ (Cy : Nat). List Nat) { Z => L, S (Cnt') Rec => PartScanRangeL (NthL Lo L) Lo Cnt' Z Z L })) {
      Z => λ (Hb : Le (Add Lo Z) (Len L)). AllLeREmpty Lo (NthL Lo L) L,
      S (Cnt') Rec => λ (Hb : Le (Add Lo (S Cnt')) (Len L)).
        PartScanRangeLAllLeR (NthL Lo L) Lo Cnt' Z Z L
          (LeRwL (Len L) (Add Lo (S Cnt')) (Add Lo (S (Add Cnt' Z)))
            (IdCongr Nat Nat (λ (A : Nat). Add Lo (S A)) Cnt' (Add Cnt' Z)
              (IdSym Nat (Add Cnt' Z) Cnt' (AddZero Cnt')))
            Hb)
          Refl
          (AllLeREmpty (S Lo) (NthL Lo L) L) } }

def PartitionAllLeRTy : Term := prog{
  Π (Lo : Nat) → Π (Cnt : Nat) → Π (L : List Nat) → Le (Add Lo Cnt) (Len L) →
    AllLeR (PartIdxRangeL Lo Cnt L) Lo (NthL Lo L) (PartitionRangeL Lo Cnt L) }
-- PartitionAllGtR : wrapper of PartScanRangeLAllGtR at i=g=0 (AllGtR Z precondition vacuous).
def PartitionAllGtR : Term := prog{
  λ (Lo : Nat). λ (Cnt : Nat). λ (L : List Nat).
    elim Cnt return (λ (Cz : Nat).
        Le (Add Lo Cz) (Len L) →
        AllGtR (elim Cz return (λ (Cy : Nat). Nat) { Z => Z, S (Cnt') Rec => PartScanGapRangeL (NthL Lo L) Lo Cnt' Z Z L })
               (Add (S (elim Cz return (λ (Cy : Nat). Nat) { Z => Z, S (Cnt') Rec => PartScanIdxRangeL (NthL Lo L) Lo Cnt' Z Z L })) Lo) (NthL Lo L)
               (elim Cz return (λ (Cy : Nat). List Nat) { Z => L, S (Cnt') Rec => PartScanRangeL (NthL Lo L) Lo Cnt' Z Z L })) {
      Z => λ (Hb : Le (Add Lo Z) (Len L)). AllGtREmpty (Add (S Z) Lo) (NthL Lo L) L,
      S (Cnt') Rec => λ (Hb : Le (Add Lo (S Cnt')) (Len L)).
        PartScanRangeLAllGtR (NthL Lo L) Lo Cnt' Z Z L
          (LeRwL (Len L) (Add Lo (S Cnt')) (Add Lo (S (Add Cnt' Z)))
            (IdCongr Nat Nat (λ (A : Nat). Add Lo (S A)) Cnt' (Add Cnt' Z)
              (IdSym Nat (Add Cnt' Z) Cnt' (AddZero Cnt')))
            Hb)
          Refl
          (AllGtREmpty (Add (S Z) Lo) (NthL Lo L) L) } }

def PartitionAllGtRTy : Term := prog{
  Π (Lo : Nat) → Π (Cnt : Nat) → Π (L : List Nat) → Le (Add Lo Cnt) (Len L) →
    AllGtR (PartGapRangeL Lo Cnt L) (Add (S (PartIdxRangeL Lo Cnt L)) Lo) (NthL Lo L) (PartitionRangeL Lo Cnt L) }
def PartitionPivotTy : Term := prog{
  Π (Lo : Nat) → Π (Cnt : Nat) → Π (L : List Nat) → Le (Add Lo Cnt) (Len L) →
    Id Nat (NthL (Add (PartIdxRangeL Lo Cnt L) Lo) (PartitionRangeL Lo Cnt L)) (NthL Lo L) }

-- Truncated subtraction + its reindex identity — the glue's both-right case maps a
-- whole-range index k>i into the right-segment index `Sub k (S i)`, then transports
-- the position `Add (Sub k (S i)) (Add (S i) lo)` back to `Add k lo` via AddAssoc +
-- `Add (Sub k (S i)) (S i) = k` (AddComm of AddSubCancel). sub recurses on the
-- minuend so `Sub (S a)(S b) = Sub a b`; AddSubCancel is a clean double induction.
def Sub : Term := prog{
  λ (A : Nat).
    elim A return (λ (Az : Nat). Nat → Nat) {
      Z => λ (B : Nat). Z,
      S (A') Rec => λ (B : Nat). elim B return (λ (Bz : Nat). Nat) { Z => S A', S (B') Bih => Rec B' } } }
def SubTy : Term := prog{ Π (A : Nat) → Nat → Nat }
def AddSubCancel : Term := prog{
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
def AddSubCancelTy : Term := prog{ Π (A : Nat) → Π (B : Nat) → Le B A → Id Nat (Add B (Sub A B)) A }

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
def LePredL : Term := prog{
  λ (A : Nat). λ (B : Nat). λ (H : Le (S A) B).
    LeTrans A (S A) B (LeUpR A A (LeRefl A)) H }
def LePredLTy : Term := prog{ Π (A : Nat) → Π (B : Nat) → Le (S A) B → Le A B }
def GapPos : Term := prog{
  λ (I : Nat). λ (G : Nat). λ (H : Le (S I) (Add I G)).
    LeAddCancelL I (S Z) G
      (LeRwL (Add I G) (S I) (Add I (S Z))
        (IdSym Nat (Add I (S Z)) (S I)
          (IdTrans Nat (Add I (S Z)) (S (Add I Z)) (S I)
            (AddSucc I Z)
            (IdCongr Nat Nat (λ (N : Nat). S N) (Add I Z) I (AddZero I))))
        H) }
def GapPosTy : Term := prog{ Π (I : Nat) → Π (G : Nat) → Le (S I) (Add I G) → Le (S Z) G }
def ReindexPos : Term := prog{
  λ (I : Nat). λ (K : Nat). λ (Lo : Nat). λ (Hik : Le (S I) K).
    IdTrans Nat
      (Add (Sub K (S I)) (S (Add I Lo)))
      (Add (Add (Sub K (S I)) (S I)) Lo)
      (Add K Lo)
      (IdSym Nat (Add (Add (Sub K (S I)) (S I)) Lo) (Add (Sub K (S I)) (S (Add I Lo)))
        (AddAssoc (Sub K (S I)) (S I) Lo))
      (IdCongr Nat Nat (λ (X : Nat). Add X Lo) (Add (Sub K (S I)) (S I)) K
        (IdTrans Nat (Add (Sub K (S I)) (S I)) (Add (S I) (Sub K (S I))) K
          (AddComm (Sub K (S I)) (S I))
          (AddSubCancel K (S I) Hik))) }
def ReindexPosTy : Term := prog{
  Π (I : Nat) → Π (K : Nat) → Π (Lo : Nat) → Le (S I) K →
    Id Nat (Add (Sub K (S I)) (S (Add I Lo))) (Add K Lo) }
def ReindexPosS : Term := prog{
  λ (I : Nat). λ (K : Nat). λ (Lo : Nat). λ (Hik : Le (S I) K).
    IdTrans Nat
      (Add (S (Sub K (S I))) (S (Add I Lo)))
      (Add (Add (S (Sub K (S I))) (S I)) Lo)
      (Add (S K) Lo)
      (IdSym Nat (Add (Add (S (Sub K (S I))) (S I)) Lo) (Add (S (Sub K (S I))) (S (Add I Lo)))
        (AddAssoc (S (Sub K (S I))) (S I) Lo))
      (IdCongr Nat Nat (λ (X : Nat). Add X Lo) (Add (S (Sub K (S I))) (S I)) (S K)
        (IdCongr Nat Nat (λ (N : Nat). S N) (Add (Sub K (S I)) (S I)) K
          (IdTrans Nat (Add (Sub K (S I)) (S I)) (Add (S I) (Sub K (S I))) K
            (AddComm (Sub K (S I)) (S I))
            (AddSubCancel K (S I) Hik)))) }
def ReindexPosSTy : Term := prog{
  Π (I : Nat) → Π (K : Nat) → Π (Lo : Nat) → Le (S I) K →
    Id Nat (Add (S (Sub K (S I))) (S (Add I Lo))) (Add (S K) Lo) }
def ReindexBnd : Term := prog{
  λ (I : Nat). λ (G : Nat). λ (K : Nat). λ (Hik : Le (S I) K). λ (Hk : Le (S K) (Add I G)).
    LeAddCancelL I (S (S (Sub K (S I)))) G
      (LeRwL (Add I G)
        (S (S (Add I (Sub K (S I)))))
        (Add I (S (S (Sub K (S I)))))
        (IdSym Nat (Add I (S (S (Sub K (S I))))) (S (S (Add I (Sub K (S I)))))
          (IdTrans Nat (Add I (S (S (Sub K (S I))))) (S (Add I (S (Sub K (S I))))) (S (S (Add I (Sub K (S I)))))
            (AddSucc I (S (Sub K (S I))))
            (IdCongr Nat Nat (λ (N : Nat). S N) (Add I (S (Sub K (S I)))) (S (Add I (Sub K (S I))))
              (AddSucc I (Sub K (S I))))))
        (LeRwL (Add I G) (S K) (S (S (Add I (Sub K (S I)))))
          (IdCongr Nat Nat (λ (N : Nat). S N) K (S (Add I (Sub K (S I))))
            (IdSym Nat (S (Add I (Sub K (S I)))) K (AddSubCancel K (S I) Hik)))
          Hk)) }
def ReindexBndTy : Term := prog{
  Π (I : Nat) → Π (G : Nat) → Π (K : Nat) → Le (S I) K → Le (S K) (Add I G) →
    Le (S (S (Sub K (S I)))) G }
def GlueLeftPivot : Term := prog{
  λ (I : Nat). λ (K : Nat). λ (Lo : Nat). λ (Pivot : Nat). λ (R : List Nat).
    λ (E1 : Id Bool (Leb (S K) I) True).
    λ (E2 : Id Bool (Leb (S (S K)) I) False).
    λ (Hpiv : Id Nat Pivot (NthL (Add I Lo) R)).
    λ (Al : AllLeR I Lo Pivot R).
      LeRwR (NthL (Add K Lo) R) Pivot (NthL (Add (S K) Lo) R)
        (IdTrans Nat Pivot (NthL (Add I Lo) R) (NthL (Add (S K) Lo) R)
          Hpiv
          (IdCongr Nat Nat (λ (X : Nat). NthL (Add X Lo) R) I (S K)
            (LeAntisym I (S K) (LebFalseGt (S (S K)) I E2) (LebTrueLe (S K) I E1))))
        (Al K (LebTrueLe (S K) I E1)) }
def GlueLeftPivotTy : Term := prog{
  Π (I : Nat) → Π (K : Nat) → Π (Lo : Nat) → Π (Pivot : Nat) → Π (R : List Nat) →
    Id Bool (Leb (S K) I) True → Id Bool (Leb (S (S K)) I) False →
    Id Nat Pivot (NthL (Add I Lo) R) → AllLeR I Lo Pivot R →
    Le (NthL (Add K Lo) R) (NthL (Add (S K) Lo) R) }
def GluePivotRight : Term := prog{
  λ (I : Nat). λ (G : Nat). λ (K : Nat). λ (Lo : Nat). λ (Pivot : Nat). λ (R : List Nat).
    λ (E1 : Id Bool (Leb (S K) I) False).
    λ (E2 : Id Bool (Leb (S I) K) False).
    λ (Hk : Le (S (S K)) (S (Add I G))).
    λ (Hpiv : Id Nat Pivot (NthL (Add I Lo) R)).
    λ (Ag : AllGtR G (S (Add I Lo)) Pivot R).
      LeRwL (NthL (Add (S K) Lo) R) Pivot (NthL (Add K Lo) R)
        (IdSym Nat (NthL (Add K Lo) R) Pivot
          (IdTrans Nat (NthL (Add K Lo) R) (NthL (Add I Lo) R) Pivot
            (IdCongr Nat Nat (λ (X : Nat). NthL (Add X Lo) R) K I
              (LeAntisym K I (LebFalseGt (S I) K E2) (LebFalseGt (S K) I E1)))
            (IdSym Nat Pivot (NthL (Add I Lo) R) Hpiv)))
        (LeRwR Pivot (NthL (S (Add I Lo)) R) (NthL (Add (S K) Lo) R)
          (IdCongr Nat Nat (λ (X : Nat). NthL (S (Add X Lo)) R) I K
            (IdSym Nat K I (LeAntisym K I (LebFalseGt (S I) K E2) (LebFalseGt (S K) I E1))))
          (LePredL Pivot (NthL (S (Add I Lo)) R)
            (Ag Z (GapPos I G
              (LeRwL (Add I G) (S K) (S I)
                (IdCongr Nat Nat (λ (N : Nat). S N) K I
                  (LeAntisym K I (LebFalseGt (S I) K E2) (LebFalseGt (S K) I E1)))
                Hk))))) }
def GluePivotRightTy : Term := prog{
  Π (I : Nat) → Π (G : Nat) → Π (K : Nat) → Π (Lo : Nat) → Π (Pivot : Nat) → Π (R : List Nat) →
    Id Bool (Leb (S K) I) False → Id Bool (Leb (S I) K) False →
    Le (S (S K)) (S (Add I G)) → Id Nat Pivot (NthL (Add I Lo) R) →
    AllGtR G (S (Add I Lo)) Pivot R →
    Le (NthL (Add K Lo) R) (NthL (Add (S K) Lo) R) }
def GlueBothRight : Term := prog{
  λ (I : Nat). λ (G : Nat). λ (K : Nat). λ (Lo : Nat). λ (Pivot : Nat). λ (R : List Nat).
    λ (E2 : Id Bool (Leb (S I) K) True).
    λ (Hk : Le (S (S K)) (S (Add I G))).
    λ (Sr : SortedR G (S (Add I Lo)) R).
      LeRwL (NthL (Add (S K) Lo) R)
        (NthL (Add (Sub K (S I)) (S (Add I Lo))) R)
        (NthL (Add K Lo) R)
        (IdCongr Nat Nat (λ (P : Nat). NthL P R) (Add (Sub K (S I)) (S (Add I Lo))) (Add K Lo)
          (ReindexPos I K Lo (LebTrueLe (S I) K E2)))
        (LeRwR (NthL (Add (Sub K (S I)) (S (Add I Lo))) R)
          (NthL (Add (S (Sub K (S I))) (S (Add I Lo))) R)
          (NthL (Add (S K) Lo) R)
          (IdCongr Nat Nat (λ (P : Nat). NthL P R) (Add (S (Sub K (S I))) (S (Add I Lo))) (Add (S K) Lo)
            (ReindexPosS I K Lo (LebTrueLe (S I) K E2)))
          (Sr (Sub K (S I)) (ReindexBnd I G K (LebTrueLe (S I) K E2) Hk))) }
def GlueBothRightTy : Term := prog{
  Π (I : Nat) → Π (G : Nat) → Π (K : Nat) → Π (Lo : Nat) → Π (Pivot : Nat) → Π (R : List Nat) →
    Id Bool (Leb (S I) K) True → Le (S (S K)) (S (Add I G)) →
    SortedR G (S (Add I Lo)) R →
    Le (NthL (Add K Lo) R) (NthL (Add (S K) Lo) R) }
def Glue : Term := prog{
  λ (I : Nat). λ (G : Nat). λ (Lo : Nat). λ (Pivot : Nat). λ (R : List Nat).
    λ (Hpiv : Id Nat Pivot (NthL (Add I Lo) R)).
    λ (Sl : SortedR I Lo R).
    λ (Al : AllLeR I Lo Pivot R).
    λ (Ag : AllGtR G (S (Add I Lo)) Pivot R).
    λ (Sr : SortedR G (S (Add I Lo)) R).
    λ (K : Nat). λ (Hk : Le (S (S K)) (S (Add I G))).
      (elim (Leb (S K) I) return (λ (W : Bool).
          Id Bool (Leb (S K) I) W → Le (NthL (Add K Lo) R) (NthL (Add (S K) Lo) R)) {
        True => λ (E1 : Id Bool (Leb (S K) I) True).
          (elim (Leb (S (S K)) I) return (λ (W2 : Bool).
              Id Bool (Leb (S (S K)) I) W2 → Le (NthL (Add K Lo) R) (NthL (Add (S K) Lo) R)) {
            True => λ (E2 : Id Bool (Leb (S (S K)) I) True). Sl K (LebTrueLe (S (S K)) I E2),
            False => λ (E2 : Id Bool (Leb (S (S K)) I) False). GlueLeftPivot I K Lo Pivot R E1 E2 Hpiv Al
          }) Refl,
        False => λ (E1 : Id Bool (Leb (S K) I) False).
          (elim (Leb (S I) K) return (λ (W2 : Bool).
              Id Bool (Leb (S I) K) W2 → Le (NthL (Add K Lo) R) (NthL (Add (S K) Lo) R)) {
            True => λ (E2 : Id Bool (Leb (S I) K) True). GlueBothRight I G K Lo Pivot R E2 Hk Sr,
            False => λ (E2 : Id Bool (Leb (S I) K) False). GluePivotRight I G K Lo Pivot R E1 E2 Hk Hpiv Ag
          }) Refl
      }) Refl }
def GlueTy : Term := prog{
  Π (I : Nat) → Π (G : Nat) → Π (Lo : Nat) → Π (Pivot : Nat) → Π (R : List Nat) →
    Id Nat Pivot (NthL (Add I Lo) R) →
    SortedR I Lo R →
    AllLeR I Lo Pivot R →
    AllGtR G (S (Add I Lo)) Pivot R →
    SortedR G (S (Add I Lo)) R →
    SortedR (S (Add I G)) Lo R }

/-! ## The KEYSTONE — range bounds survive sorting (§22, M22-c step 3; bridges dispatched)

    `AllLeRSortRange` / `AllGtRSortRange`: sorting the range [lo, lo+w) preserves the
    ≤-bound / >-bound over that range. This is what lets SortedSortRangeL carry the
    partition invariant's bounds through the two recursive sorts. Positional AllLeR is
    NOT natively perm-invariant, so it routes through the multiset: `noAbove p =
    Π x. Le (S p) x → SegCount x = Z` (no element > p in the segment) IS perm-invariant
    (SegCountSortRangeL, on main). Composition (MINE): AllLeRSortRange =
    NoAboveToAllLeR ∘ (IdTrans with SegCountSortRangeL) ∘ AllLeRToNoAbove. The
    three bridges + the shared membership helper (NthSegCountPos) are MECHANICAL
    count/segment inductions — PROOFS DISPATCHED to dllbc-seg (reusing NthDrop /
    CountSplit / CountSegPreserved / CountCons on main). Statements elaboration-
    verified. AllGtR mirrors with noBelow = Π x. Le x p → SegCount x = Z. -/
-- Keystone bridge helpers: eqb comparison, the count "miss" step, count-zero-by-extension,
-- and take-vs-nth/len facts. All mechanical count/segment inductions.
def EqbGtFalse : Term := prog{
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
def EqbGtFalseTy : Term := prog{ Π (H : Nat) → Π (X : Nat) → Le (S H) X → Id Bool (Eqb X H) False }

def EqbLtFalse : Term := prog{
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
def EqbLtFalseTy : Term := prog{ Π (A : Nat) → Π (B : Nat) → Le (S A) B → Id Bool (Eqb A B) False }

def CountConsMiss : Term := prog{
  λ (M : Nat). λ (H : Nat). λ (T : List Nat). λ (Hq : Id Bool (Eqb M H) False).
    j Bool False
      (λ (Z0 : Bool). λ (Hh : Id Bool False Z0).
        Id Nat (boolRec (λ (W : Bool). Nat) (S (Count M T)) (Count M T) Z0) (Count M T))
      Refl (Eqb M H) (IdSym Bool (Eqb M H) False Hq) }
def CountConsMissTy : Term := prog{
  Π (M : Nat) → Π (H : Nat) → Π (T : List Nat) → Id Bool (Eqb M H) False →
    Id Nat (Count M (Cons H T)) (Count M T) }

def CountZeroExt : Term := prog{
  λ (X : Nat). λ (S0 : List Nat).
    elim S0 return (λ (Sz : List Nat). (Π (J : Nat) → Le (S J) (Len Sz) → Id Bool (Eqb X (NthL J Sz)) False) → Id Nat (Count X Sz) Z) {
      Nil => λ (Heq : Π (J : Nat) → Le (S J) (Len Nil) → Id Bool (Eqb X (NthL J Nil)) False). Refl,
      Cons (H) (T) Ih => λ (Heq : Π (J : Nat) → Le (S J) (Len (Cons H T)) → Id Bool (Eqb X (NthL J (Cons H T))) False).
        IdTrans Nat (Count X (Cons H T)) (Count X T) Z
          (CountConsMiss X H T (Heq Z unit))
          (Ih (λ (J : Nat). λ (Hj : Le (S J) (Len T)). Heq (S J) Hj)) } }
def CountZeroExtTy : Term := prog{
  Π (X : Nat) → Π (S0 : List Nat) →
    (Π (J : Nat) → Le (S J) (Len S0) → Id Bool (Eqb X (NthL J S0)) False) → Id Nat (Count X S0) Z }

def NthTake : Term := prog{
  λ (W : Nat).
    elim W return (λ (Wz : Nat). Π (J : Nat) → Π (S0 : List Nat) → Le (S J) Wz → Id Nat (NthL J (Take Wz S0)) (NthL J S0)) {
      Z => λ (J : Nat). λ (S0 : List Nat). λ (Hlt : Le (S J) Z). botElim (Id Nat (NthL J (Take Z S0)) (NthL J S0)) Hlt,
      S (W') Ih => λ (J : Nat). λ (S0 : List Nat).
        elim J return (λ (Jz : Nat). Le (S Jz) (S W') → Id Nat (NthL Jz (Take (S W') S0)) (NthL Jz S0)) {
          Z => λ (Hlt : Le (S Z) (S W')).
            elim S0 return (λ (Sz : List Nat). Id Nat (NthL Z (Take (S W') Sz)) (NthL Z Sz)) {
              Nil => Refl, Cons (H) (T) Sih => Refl },
          S (J') Jih => λ (Hlt : Le (S (S J')) (S W')).
            elim S0 return (λ (Sz : List Nat). Id Nat (NthL (S J') (Take (S W') Sz)) (NthL (S J') Sz)) {
              Nil => Refl,
              Cons (H) (T) Sih => Ih J' T Hlt } } } }
def NthTakeTy : Term := prog{
  Π (W : Nat) → Π (J : Nat) → Π (S0 : List Nat) → Le (S J) W → Id Nat (NthL J (Take W S0)) (NthL J S0) }

def LenTakeLe : Term := prog{
  λ (W : Nat).
    elim W return (λ (Wz : Nat). Π (S0 : List Nat) → Le (Len (Take Wz S0)) Wz) {
      Z => λ (S0 : List Nat). unit,
      S (W') Ih => λ (S0 : List Nat).
        elim S0 return (λ (Sz : List Nat). Le (Len (Take (S W') Sz)) (S W')) {
          Nil => unit,
          Cons (H) (T) Sih => Ih T } } }
def LenTakeLeTy : Term := prog{ Π (W : Nat) → Π (S0 : List Nat) → Le (Len (Take W S0)) W }

-- #2 AllLeRToNoAbove : every segment element ≤ p, so an x>p occurs 0× (CountZeroExt,
-- with each element bridged nth j (take w (drop lo l)) → nth (add j lo) l via NthTake/NthDrop).
def AllLeRToNoAbove : Term := prog{
  λ (W : Nat). λ (Lo : Nat). λ (P : Nat). λ (L : List Nat).
    λ (HAll : AllLeR W Lo P L). λ (X : Nat). λ (Hpx : Le (S P) X).
      CountZeroExt X (Take W (Drop Lo L))
        (λ (J : Nat). λ (Hj : Le (S J) (Len (Take W (Drop Lo L)))).
          EqbGtFalse (NthL J (Take W (Drop Lo L))) X
            (LeTrans (S (NthL J (Take W (Drop Lo L)))) (S P) X
              (LeRwL P (NthL (Add J Lo) L) (NthL J (Take W (Drop Lo L)))
                (IdSym Nat (NthL J (Take W (Drop Lo L))) (NthL (Add J Lo) L)
                  (IdTrans Nat (NthL J (Take W (Drop Lo L))) (NthL J (Drop Lo L)) (NthL (Add J Lo) L)
                    (NthTake W J (Drop Lo L) (LeTrans (S J) (Len (Take W (Drop Lo L))) W Hj (LenTakeLe W (Drop Lo L))))
                    (IdTrans Nat (NthL J (Drop Lo L)) (NthL (Add Lo J) L) (NthL (Add J Lo) L)
                      (NthDrop Lo J L)
                      (IdCongr Nat Nat (λ (Q : Nat). NthL Q L) (Add Lo J) (Add J Lo) (AddComm Lo J)))))
                (HAll J (LeTrans (S J) (Len (Take W (Drop Lo L))) W Hj (LenTakeLe W (Drop Lo L)))))
              Hpx)) }

-- #4 AllGtRToNoBelow : every segment element > p, so an x≤p occurs 0× (mirror of #2).
def AllGtRToNoBelow : Term := prog{
  λ (W : Nat). λ (Lo : Nat). λ (P : Nat). λ (L : List Nat).
    λ (HAll : AllGtR W Lo P L). λ (X : Nat). λ (Hxp : Le X P).
      CountZeroExt X (Take W (Drop Lo L))
        (λ (J : Nat). λ (Hj : Le (S J) (Len (Take W (Drop Lo L)))).
          EqbLtFalse X (NthL J (Take W (Drop Lo L)))
            (LeTrans (S X) (S P) (NthL J (Take W (Drop Lo L)))
              Hxp
              (LeRwR (S P) (NthL (Add J Lo) L) (NthL J (Take W (Drop Lo L)))
                (IdSym Nat (NthL J (Take W (Drop Lo L))) (NthL (Add J Lo) L)
                  (IdTrans Nat (NthL J (Take W (Drop Lo L))) (NthL J (Drop Lo L)) (NthL (Add J Lo) L)
                    (NthTake W J (Drop Lo L) (LeTrans (S J) (Len (Take W (Drop Lo L))) W Hj (LenTakeLe W (Drop Lo L))))
                    (IdTrans Nat (NthL J (Drop Lo L)) (NthL (Add Lo J) L) (NthL (Add J Lo) L)
                      (NthDrop Lo J L)
                      (IdCongr Nat Nat (λ (Q : Nat). NthL Q L) (Add Lo J) (Add J Lo) (AddComm Lo J)))))
                (HAll J (LeTrans (S J) (Len (Take W (Drop Lo L))) W Hj (LenTakeLe W (Drop Lo L))))))) }

-- Membership side (#1/#3/#5): the range-fits bound makes the element genuinely present.
def EqbRefl : Term := prog{
  λ (N : Nat). elim N return (λ (Nz : Nat). Id Bool (Eqb Nz Nz) True) {
    Z => Refl,
    S (N') Ih => Ih } }
def EqbReflTy : Term := prog{ Π (N : Nat) → Id Bool (Eqb N N) True }

def LenDropBound : Term := prog{
  λ (Lo : Nat).
    elim Lo return (λ (Loz : Nat). Π (K : Nat) → Π (L : List Nat) → Le (Add Loz K) (Len L) → Le K (Len (Drop Loz L))) {
      Z => λ (K : Nat). λ (L : List Nat). λ (Hb : Le (Add Z K) (Len L)). Hb,
      S (Lo') Ih => λ (K : Nat). λ (L : List Nat).
        elim L return (λ (Lz : List Nat). Le (Add (S Lo') K) (Len Lz) → Le K (Len (Drop (S Lo') Lz))) {
          Nil => λ (Hb : Le (Add (S Lo') K) (Len Nil)). botElim (Le K (Len (Drop (S Lo') Nil))) Hb,
          Cons (H) (T) Lih => λ (Hb : Le (Add (S Lo') K) (Len (Cons H T))). Ih K T Hb } } }
def LenDropBoundTy : Term := prog{
  Π (Lo : Nat) → Π (K : Nat) → Π (L : List Nat) → Le (Add Lo K) (Len L) → Le K (Len (Drop Lo L)) }

def CountTakeNthPos : Term := prog{
  λ (W : Nat).
    elim W return (λ (Wz : Nat). Π (M : Nat) → Π (S0 : List Nat) → Le (S M) Wz → Le (S M) (Len S0) → Le (S Z) (Count (NthL M S0) (Take Wz S0))) {
      Z => λ (M : Nat). λ (S0 : List Nat). λ (Hw : Le (S M) Z). λ (Hs : Le (S M) (Len S0)). botElim (Le (S Z) (Count (NthL M S0) (Take Z S0))) Hw,
      S (W') Ih => λ (M : Nat). λ (S0 : List Nat). λ (Hw : Le (S M) (S W')). λ (Hs : Le (S M) (Len S0)).
        elim S0 return (λ (Sz : List Nat). Le (S M) (Len Sz) → Le (S Z) (Count (NthL M Sz) (Take (S W') Sz))) {
          Nil => λ (Hs0 : Le (S M) (Len Nil)). botElim (Le (S Z) (Count (NthL M Nil) (Take (S W') Nil))) Hs0,
          Cons (H) (T) Sih => λ (Hs0 : Le (S M) (Len (Cons H T))).
            elim M return (λ (Mz : Nat). Le (S Mz) (S W') → Le (S Mz) (Len (Cons H T)) → Le (S Z) (Count (NthL Mz (Cons H T)) (Take (S W') (Cons H T)))) {
              Z => λ (Hw1 : Le (S Z) (S W')). λ (Hs1 : Le (S Z) (Len (Cons H T))).
                LeRwR (S Z) (S (Count H (Take W' T))) (Count H (Cons H (Take W' T)))
                  (IdSym Nat (Count H (Cons H (Take W' T))) (S (Count H (Take W' T)))
                    (CountConsHit H H (Take W' T) (EqbRefl H)))
                  unit,
              S (M') Mih => λ (Hw1 : Le (S (S M')) (S W')). λ (Hs1 : Le (S (S M')) (Len (Cons H T))).
                elim (Eqb (NthL M' T) H) return (λ (B : Bool). Le (S Z) (boolRec (λ (Bw : Bool). Nat) (S (Count (NthL M' T) (Take W' T))) (Count (NthL M' T) (Take W' T)) B)) {
                  True => unit,
                  False => Ih M' T Hw1 Hs1 }
            } Hw Hs0 } Hs } }
def CountTakeNthPosTy : Term := prog{
  Π (W : Nat) → Π (M : Nat) → Π (S0 : List Nat) → Le (S M) W → Le (S M) (Len S0) →
    Le (S Z) (Count (NthL M S0) (Take W S0)) }

-- #1 NthSegCountPos : element at range position lo+m occurs ≥1× in the segment (needs range-fits).
def NthSegCountPos : Term := prog{
  λ (M : Nat). λ (W : Nat). λ (Lo : Nat). λ (L : List Nat).
    λ (Hmw : Le (S M) W). λ (Hrange : Le (Add Lo W) (Len L)).
      LeRwR (S Z) (Count (NthL M (Drop Lo L)) (Take W (Drop Lo L))) (Count (NthL (Add M Lo) L) (Take W (Drop Lo L)))
        (IdCongr Nat Nat (λ (Q : Nat). Count Q (Take W (Drop Lo L))) (NthL M (Drop Lo L)) (NthL (Add M Lo) L)
          (IdTrans Nat (NthL M (Drop Lo L)) (NthL (Add Lo M) L) (NthL (Add M Lo) L)
            (NthDrop Lo M L)
            (IdCongr Nat Nat (λ (Q : Nat). NthL Q L) (Add Lo M) (Add M Lo) (AddComm Lo M))))
        (CountTakeNthPos W M (Drop Lo L) Hmw
          (LenDropBound Lo (S M) L
            (LeTrans (Add Lo (S M)) (Add Lo W) (Len L) (LeAddMonoL Lo (S M) W Hmw) Hrange))) }

-- #3 NoAboveToAllLeR : no element > p in the segment ⟹ range ≤ p (leb + contradiction via #1).
def NoAboveToAllLeR : Term := prog{
  λ (W : Nat). λ (Lo : Nat). λ (P : Nat). λ (L : List Nat).
    λ (Hrange : Le (Add Lo W) (Len L)). λ (HnoAbove : Π (X : Nat) → Le (S P) X → Id Nat (SegCount X Lo W L) Z).
    λ (M : Nat). λ (Hm : Le (S M) W).
      elim (Leb (NthL (Add M Lo) L) P) return (λ (B : Bool). Id Bool (Leb (NthL (Add M Lo) L) P) B → Le (NthL (Add M Lo) L) P) {
        True => λ (E : Id Bool (Leb (NthL (Add M Lo) L) P) True). LebTrueLe (NthL (Add M Lo) L) P E,
        False => λ (E : Id Bool (Leb (NthL (Add M Lo) L) P) False).
          botElim (Le (NthL (Add M Lo) L) P)
            (LeRwR (S Z) (SegCount (NthL (Add M Lo) L) Lo W L) Z
              (HnoAbove (NthL (Add M Lo) L) (LebFalseGt (NthL (Add M Lo) L) P E))
              (NthSegCountPos M W Lo L Hm Hrange))
      } Refl }

-- #5 NoBelowToAllGtR : mirror of #3.
def NoBelowToAllGtR : Term := prog{
  λ (W : Nat). λ (Lo : Nat). λ (P : Nat). λ (L : List Nat).
    λ (Hrange : Le (Add Lo W) (Len L)). λ (HnoBelow : Π (X : Nat) → Le X P → Id Nat (SegCount X Lo W L) Z).
    λ (M : Nat). λ (Hm : Le (S M) W).
      elim (Leb (NthL (Add M Lo) L) P) return (λ (B : Bool). Id Bool (Leb (NthL (Add M Lo) L) P) B → Le (S P) (NthL (Add M Lo) L)) {
        True => λ (E : Id Bool (Leb (NthL (Add M Lo) L) P) True).
          botElim (Le (S P) (NthL (Add M Lo) L))
            (LeRwR (S Z) (SegCount (NthL (Add M Lo) L) Lo W L) Z
              (HnoBelow (NthL (Add M Lo) L) (LebTrueLe (NthL (Add M Lo) L) P E))
              (NthSegCountPos M W Lo L Hm Hrange)),
        False => λ (E : Id Bool (Leb (NthL (Add M Lo) L) P) False). LebFalseGt (NthL (Add M Lo) L) P E
      } Refl }

def AllLeRToNoAboveTy : Term := prog{
  Π (W : Nat) → Π (Lo : Nat) → Π (P : Nat) → Π (L : List Nat) →
    AllLeR W Lo P L → Π (X : Nat) → Le (S P) X → Id Nat (SegCount X Lo W L) Z }
def NoAboveToAllLeRTy : Term := prog{
  Π (W : Nat) → Π (Lo : Nat) → Π (P : Nat) → Π (L : List Nat) → Le (Add Lo W) (Len L) →
    (Π (X : Nat) → Le (S P) X → Id Nat (SegCount X Lo W L) Z) → AllLeR W Lo P L }
def AllGtRToNoBelowTy : Term := prog{
  Π (W : Nat) → Π (Lo : Nat) → Π (P : Nat) → Π (L : List Nat) →
    AllGtR W Lo P L → Π (X : Nat) → Le X P → Id Nat (SegCount X Lo W L) Z }
def NoBelowToAllGtRTy : Term := prog{
  Π (W : Nat) → Π (Lo : Nat) → Π (P : Nat) → Π (L : List Nat) → Le (Add Lo W) (Len L) →
    (Π (X : Nat) → Le X P → Id Nat (SegCount X Lo W L) Z) → AllGtR W Lo P L }
-- #1/#3/#5 carry the range-fits bound `Le (Add lo w) (Len l)`: without it an off-the-end
-- position reads Z, which need not occur in the segment, so #1 (present ≥1×) and #5
-- (AllGtR needs nth>p at every m<w, but off-end nth=Z isn't) are FALSE (dllbc-seg's
-- gate finding, computationally checked). #2/#4 iterate the ACTUAL segment so need no
-- bound. The keystone already carries this bound and len is sort-invariant, so the
-- composition feeds #3/#5 the bound over the sorted list.
def NthSegCountPosTy : Term := prog{
  Π (M : Nat) → Π (W : Nat) → Π (Lo : Nat) → Π (L : List Nat) →
    Le (S M) W → Le (Add Lo W) (Len L) → Le (S Z) (SegCount (NthL (Add M Lo) L) Lo W L) }
def AllLeRSortRangeTy : Term := prog{
  Π (Fuel : Nat) → Π (Lo : Nat) → Π (W : Nat) → Π (P : Nat) → Π (L : List Nat) →
    Le (Add Lo W) (Len L) → AllLeR W Lo P L → AllLeR W Lo P (SortRangeL Fuel Lo W L) }
def AllGtRSortRangeTy : Term := prog{
  Π (Fuel : Nat) → Π (Lo : Nat) → Π (W : Nat) → Π (P : Nat) → Π (L : List Nat) →
    Le (Add Lo W) (Len L) → AllGtR W Lo P L → AllGtR W Lo P (SortRangeL Fuel Lo W L) }

-- KEYSTONE composition (mine): route the positional bound through the perm-invariant
-- noAbove/noBelow (SegCount preserved by SegCountSortRangeL), feeding the range bound
-- over the sorted list (len sort-invariant, LeRwR over LenSortRangeL).
def AllLeRSortRange : Term := prog{
  λ (Fuel : Nat). λ (Lo : Nat). λ (W : Nat). λ (P : Nat). λ (L : List Nat).
    λ (Bound0 : Le (Add Lo W) (Len L)). λ (H : AllLeR W Lo P L).
      NoAboveToAllLeR W Lo P (SortRangeL Fuel Lo W L)
        (LeRwR (Add Lo W) (Len L) (Len (SortRangeL Fuel Lo W L))
          (IdSym Nat (Len (SortRangeL Fuel Lo W L)) (Len L) (LenSortRangeL Fuel Lo W L))
          Bound0)
        (λ (X : Nat). λ (Hx : Le (S P) X).
          IdTrans Nat (SegCount X Lo W (SortRangeL Fuel Lo W L)) (SegCount X Lo W L) Z
            (SegCountSortRangeL X Fuel Lo W L Bound0)
            (AllLeRToNoAbove W Lo P L H X Hx)) }
def AllGtRSortRange : Term := prog{
  λ (Fuel : Nat). λ (Lo : Nat). λ (W : Nat). λ (P : Nat). λ (L : List Nat).
    λ (Bound0 : Le (Add Lo W) (Len L)). λ (H : AllGtR W Lo P L).
      NoBelowToAllGtR W Lo P (SortRangeL Fuel Lo W L)
        (LeRwR (Add Lo W) (Len L) (Len (SortRangeL Fuel Lo W L))
          (IdSym Nat (Len (SortRangeL Fuel Lo W L)) (Len L) (LenSortRangeL Fuel Lo W L))
          Bound0)
        (λ (X : Nat). λ (Hx : Le X P).
          IdTrans Nat (SegCount X Lo W (SortRangeL Fuel Lo W L)) (SegCount X Lo W L) Z
            (SegCountSortRangeL X Fuel Lo W L Bound0)
            (AllGtRToNoBelow W Lo P L H X Hx)) }

/-! ## SortedSortRangeL — the full sort is sorted (§22, M22-c step 5; proof dispatched)

    The model half of the North Star's sortedness. Fuel-structural induction mirroring
    CountSortRangeL. FUEL-SUFFICIENCY: sortedness (unlike count/len) is NOT preserved by
    the out-of-fuel identity, so it carries `Le cnt fuel` (the recursion depth ≤ cnt). The
    step (cnt ≥ 2) applies the GLUE to the two recursively-sorted sub-ranges, feeding it:
    the pivot placement (PartitionPivot + locality — the sorts don't touch position
    lo+i), the two sub-range SortedRs (the two IHs + locality), and AllLeR-left/AllGtR-right
    SURVIVING both sorts (PartitionAllLeR/allGtR = invariant, then allLeR/AllGtRSortRange
    = keystone, then locality for the OTHER sort). The glue's width S(add i g) = cnt via
    PartScanSizeL (i+g = cnt-1). Sub-range bounds/fuel from PartScanSizeL + the len lemmas.
    Assembly over now-proven pieces (glue, keystone, invariant, locality all on main) —
    proof owned by dllbc-seg per skeleton+prove; statement mine. -/
def SortedSortRangeLTy : Term := prog{
  Π (Fuel : Nat) → Π (Lo : Nat) → Π (Cnt : Nat) → Π (L : List Nat) →
    Le Cnt Fuel → Le (Add Lo Cnt) (Len L) →
    SortedR Cnt Lo (SortRangeL Fuel Lo Cnt L) }

-- SortedR transport kit for SortedSortRangeL (spine takeover): move a SortedR across
-- a fixed region (SortedRCong, le_rw both endpoints), a width rewrite (SortedRWidthCong,
-- j on the width — for the glue's S(add i g) → cnt), or an offset rewrite (SortedROffCong,
-- j on the offset — for the AddComm S(add lo i) ↔ S(add i lo) bridge).
def SortedRCong : Term := prog{
  λ (W : Nat). λ (Lo : Nat). λ (L : List Nat). λ (L' : List Nat).
    λ (S0 : SortedR W Lo L).
    λ (Agree : Π (Q : Nat) → Le (S Q) W → Id Nat (NthL (Add Q Lo) L') (NthL (Add Q Lo) L)).
      λ (K : Nat). λ (Hk : Le (S (S K)) W).
        LeRwR (NthL (Add K Lo) L') (NthL (Add (S K) Lo) L) (NthL (Add (S K) Lo) L')
          (IdSym Nat (NthL (Add (S K) Lo) L') (NthL (Add (S K) Lo) L) (Agree (S K) Hk))
          (LeRwL (NthL (Add (S K) Lo) L) (NthL (Add K Lo) L) (NthL (Add K Lo) L')
            (IdSym Nat (NthL (Add K Lo) L') (NthL (Add K Lo) L) (Agree K (LePredL (S K) W Hk)))
            (S0 K Hk)) }
def SortedRCongTy : Term := prog{
  Π (W : Nat) → Π (Lo : Nat) → Π (L : List Nat) → Π (L' : List Nat) →
    SortedR W Lo L →
    (Π (Q : Nat) → Le (S Q) W → Id Nat (NthL (Add Q Lo) L') (NthL (Add Q Lo) L)) →
    SortedR W Lo L' }
def SortedRWidthCong : Term := prog{
  λ (W : Nat). λ (W' : Nat). λ (Lo : Nat). λ (L : List Nat).
    λ (E : Id Nat W W'). λ (S0 : SortedR W Lo L).
      j Nat W (λ (W2 : Nat). λ (H : Id Nat W W2). SortedR W2 Lo L) S0 W' E }
def SortedRWidthCongTy : Term := prog{
  Π (W : Nat) → Π (W' : Nat) → Π (Lo : Nat) → Π (L : List Nat) →
    Id Nat W W' → SortedR W Lo L → SortedR W' Lo L }
def SortedROffCong : Term := prog{
  λ (W : Nat). λ (Lo : Nat). λ (Lo' : Nat). λ (L : List Nat).
    λ (E : Id Nat Lo Lo'). λ (S0 : SortedR W Lo L).
      j Nat Lo (λ (Lo2 : Nat). λ (H : Id Nat Lo Lo2). SortedR W Lo2 L) S0 Lo' E }
def SortedROffCongTy : Term := prog{
  Π (W : Nat) → Π (Lo : Nat) → Π (Lo' : Nat) → Π (L : List Nat) →
    Id Nat Lo Lo' → SortedR W Lo L → SortedR W Lo' L }

/-! ## sorted_sortRangeL's 5 glue inputs (spine takeover) — each survives BOTH sub-sorts.
    Setup: L = SortRangeL f' lo i p (left sort), result = SortRangeL f' (S(add lo i)) g L
    (right sort). SL/AL: left region [lo,lo+i) is BELOW the right sort (NthSortRangeLLt);
    AG: gap is ABOVE the left sort (NthSortRangeLGe). Keystone (allLeR/AllGtRSortRange)
    carries bounds across the OWN sort; cong across the fixed region. AddComm bridges the
    positional-predicate offset (add i lo) ↔ model offset (add lo i). -/
def PosLtBound : Term := prog{
  λ (Q : Nat). λ (I : Nat). λ (Lo : Nat). λ (Hq : Le (S Q) I).
    LeRwL (Add Lo I) (Add Lo Q) (Add Q Lo) (AddComm Lo Q)
      (LeAddMonoL Lo Q I (LePredL Q I Hq)) }
def PosLtBoundTy : Term := prog{
  Π (Q : Nat) → Π (I : Nat) → Π (Lo : Nat) → Le (S Q) I → Le (S (Add Q Lo)) (S (Add Lo I)) }
def AllGtROffCong : Term := prog{
  λ (W : Nat). λ (Off : Nat). λ (Off' : Nat). λ (P : Nat). λ (L : List Nat).
    λ (E : Id Nat Off Off'). λ (S0 : AllGtR W Off P L).
      j Nat Off (λ (O2 : Nat). λ (H : Id Nat Off O2). AllGtR W O2 P L) S0 Off' E }
def AllGtROffCongTy : Term := prog{
  Π (W : Nat) → Π (Off : Nat) → Π (Off' : Nat) → Π (P : Nat) → Π (L : List Nat) →
    Id Nat Off Off' → AllGtR W Off P L → AllGtR W Off' P L }
def GapGeBound : Term := prog{
  λ (M : Nat). λ (I : Nat). λ (Lo : Nat).
    LeRwL (Add M (S (Add I Lo))) (Add I Lo) (Add Lo I) (AddComm I Lo)
      (LeTrans (Add I Lo) (S (Add I Lo)) (Add M (S (Add I Lo)))
        (LeUpR (Add I Lo) (Add I Lo) (LeRefl (Add I Lo)))
        (LeAddL (S (Add I Lo)) M)) }
def GapGeBoundTy : Term := prog{
  Π (M : Nat) → Π (I : Nat) → Π (Lo : Nat) → Le (Add Lo I) (Add M (S (Add I Lo))) }
def SortedInSL : Term := prog{
  λ (I : Nat). λ (G : Nat). λ (Lo : Nat). λ (P : List Nat). λ (F' : Nat).
    λ (IhL : SortedR I Lo (SortRangeL F' Lo I P)).
      SortedRCong I Lo (SortRangeL F' Lo I P) (SortRangeL F' (S (Add Lo I)) G (SortRangeL F' Lo I P))
        IhL
        (λ (Q : Nat). λ (Hq : Le (S Q) I).
          NthSortRangeLLt F' (Add Q Lo) (S (Add Lo I)) G (SortRangeL F' Lo I P) (PosLtBound Q I Lo Hq)) }
def SortedInSLTy : Term := prog{
  Π (I : Nat) → Π (G : Nat) → Π (Lo : Nat) → Π (P : List Nat) → Π (F' : Nat) →
    SortedR I Lo (SortRangeL F' Lo I P) →
    SortedR I Lo (SortRangeL F' (S (Add Lo I)) G (SortRangeL F' Lo I P)) }
def SortedInSR : Term := prog{
  λ (I : Nat). λ (G : Nat). λ (Lo : Nat). λ (P : List Nat). λ (F' : Nat).
    λ (IhR : SortedR G (S (Add Lo I)) (SortRangeL F' (S (Add Lo I)) G (SortRangeL F' Lo I P))).
      SortedROffCong G (S (Add Lo I)) (S (Add I Lo)) (SortRangeL F' (S (Add Lo I)) G (SortRangeL F' Lo I P))
        (IdCongr Nat Nat (λ (N : Nat). S N) (Add Lo I) (Add I Lo) (AddComm Lo I))
        IhR }
def SortedInSRTy : Term := prog{
  Π (I : Nat) → Π (G : Nat) → Π (Lo : Nat) → Π (P : List Nat) → Π (F' : Nat) →
    SortedR G (S (Add Lo I)) (SortRangeL F' (S (Add Lo I)) G (SortRangeL F' Lo I P)) →
    SortedR G (S (Add I Lo)) (SortRangeL F' (S (Add Lo I)) G (SortRangeL F' Lo I P)) }
def SortedInHPIV : Term := prog{
  λ (I : Nat). λ (G : Nat). λ (Lo : Nat). λ (Pivot : Nat). λ (P : List Nat). λ (F' : Nat).
    λ (Ppiv : Id Nat (NthL (Add I Lo) P) Pivot).
      IdSym Nat (NthL (Add I Lo) (SortRangeL F' (S (Add Lo I)) G (SortRangeL F' Lo I P))) Pivot
        (IdTrans Nat
          (NthL (Add I Lo) (SortRangeL F' (S (Add Lo I)) G (SortRangeL F' Lo I P)))
          (NthL (Add I Lo) (SortRangeL F' Lo I P))
          Pivot
          (NthSortRangeLLt F' (Add I Lo) (S (Add Lo I)) G (SortRangeL F' Lo I P)
            (LeRwR (Add I Lo) (Add I Lo) (Add Lo I) (AddComm I Lo) (LeRefl (Add I Lo))))
          (IdTrans Nat (NthL (Add I Lo) (SortRangeL F' Lo I P)) (NthL (Add I Lo) P) Pivot
            (NthSortRangeLGe F' (Add I Lo) Lo I P
              (LeRwL (Add I Lo) (Add I Lo) (Add Lo I) (AddComm I Lo) (LeRefl (Add I Lo))))
            Ppiv)) }
def SortedInHPIVTy : Term := prog{
  Π (I : Nat) → Π (G : Nat) → Π (Lo : Nat) → Π (Pivot : Nat) → Π (P : List Nat) → Π (F' : Nat) →
    Id Nat (NthL (Add I Lo) P) Pivot →
    Id Nat Pivot (NthL (Add I Lo) (SortRangeL F' (S (Add Lo I)) G (SortRangeL F' Lo I P))) }
def SortedInAL : Term := prog{
  λ (I : Nat). λ (G : Nat). λ (Lo : Nat). λ (Pivot : Nat). λ (P : List Nat). λ (F' : Nat).
    λ (PAL : AllLeR I Lo Pivot P). λ (Bl : Le (Add Lo I) (Len P)).
      AllLeRCong I Lo Pivot (SortRangeL F' Lo I P) (SortRangeL F' (S (Add Lo I)) G (SortRangeL F' Lo I P))
        (λ (Q : Nat). λ (Hq : Le (S Q) I).
          NthSortRangeLLt F' (Add Q Lo) (S (Add Lo I)) G (SortRangeL F' Lo I P) (PosLtBound Q I Lo Hq))
        (AllLeRSortRange F' Lo I Pivot P Bl PAL) }
def SortedInALTy : Term := prog{
  Π (I : Nat) → Π (G : Nat) → Π (Lo : Nat) → Π (Pivot : Nat) → Π (P : List Nat) → Π (F' : Nat) →
    AllLeR I Lo Pivot P → Le (Add Lo I) (Len P) →
    AllLeR I Lo Pivot (SortRangeL F' (S (Add Lo I)) G (SortRangeL F' Lo I P)) }
def SortedInAG : Term := prog{
  λ (I : Nat). λ (G : Nat). λ (Lo : Nat). λ (Pivot : Nat). λ (P : List Nat). λ (F' : Nat).
    λ (PAG : AllGtR G (S (Add I Lo)) Pivot P).
    λ (Br : Le (Add (S (Add Lo I)) G) (Len (SortRangeL F' Lo I P))).
      AllGtROffCong G (S (Add Lo I)) (S (Add I Lo)) Pivot (SortRangeL F' (S (Add Lo I)) G (SortRangeL F' Lo I P))
        (IdCongr Nat Nat (λ (N : Nat). S N) (Add Lo I) (Add I Lo) (AddComm Lo I))
        (AllGtRSortRange F' (S (Add Lo I)) G Pivot (SortRangeL F' Lo I P) Br
          (AllGtROffCong G (S (Add I Lo)) (S (Add Lo I)) Pivot (SortRangeL F' Lo I P)
            (IdCongr Nat Nat (λ (N : Nat). S N) (Add I Lo) (Add Lo I) (AddComm I Lo))
            (AllGtRCong G (S (Add I Lo)) Pivot P (SortRangeL F' Lo I P)
              (λ (M : Nat). λ (Hm : Le (S M) G).
                NthSortRangeLGe F' (Add M (S (Add I Lo))) Lo I P (GapGeBound M I Lo))
              PAG))) }
def SortedInAGTy : Term := prog{
  Π (I : Nat) → Π (G : Nat) → Π (Lo : Nat) → Π (Pivot : Nat) → Π (P : List Nat) → Π (F' : Nat) →
    AllGtR G (S (Add I Lo)) Pivot P → Le (Add (S (Add Lo I)) G) (Len (SortRangeL F' Lo I P)) →
    AllGtR G (S (Add I Lo)) Pivot (SortRangeL F' (S (Add Lo I)) G (SortRangeL F' Lo I P)) }

-- i+g = cnt-1 for the top partition (PartScanSizeL + AddZero); reused by the size
-- transport and both fuel-sufficiency derivations in SortedSortRangeL.
def PartSize : Term := prog{
  λ (Lo : Nat). λ (Cnt'' : Nat). λ (L : List Nat).
    IdTrans Nat
      (Add (PartIdxRangeL Lo (S (S Cnt'')) L) (PartGapRangeL Lo (S (S Cnt'')) L))
      (S (Add Cnt'' Z)) (S Cnt'')
      (PartScanSizeL (NthL Lo L) Lo (S Cnt'') Z Z L)
      (IdCongr Nat Nat (λ (N : Nat). S N) (Add Cnt'' Z) Cnt'' (AddZero Cnt'')) }
def PartSizeTy : Term := prog{
  Π (Lo : Nat) → Π (Cnt'' : Nat) → Π (L : List Nat) →
    Id Nat (Add (PartIdxRangeL Lo (S (S Cnt'')) L) (PartGapRangeL Lo (S (S Cnt'')) L)) (S Cnt'') }


def SortedSortRangeL : Term := prog{
  λ (Fuel : Nat).
    elim Fuel return (λ (Fz : Nat). Π (Lo : Nat) → Π (Cnt : Nat) → Π (L : List Nat) →
        Le Cnt Fz → Le (Add Lo Cnt) (Len L) → SortedR Cnt Lo (SortRangeL Fz Lo Cnt L)) {
      Z => λ (Lo : Nat). λ (Cnt : Nat). λ (L : List Nat).
        elim Cnt return (λ (Cz : Nat). Le Cz Z → Le (Add Lo Cz) (Len L) → SortedR Cz Lo L) {
          Z => λ (Hf : Le Z Z). λ (Hb : Le (Add Lo Z) (Len L)). SortedRZero Lo L,
          S (C) Cih => λ (Hf : Le (S C) Z). λ (Hb : Le (Add Lo (S C)) (Len L)). botElim (SortedR (S C) Lo L) Hf },
      S (F') Ih => λ (Lo : Nat). λ (Cnt : Nat). λ (L : List Nat).
        elim Cnt return (λ (Cz : Nat). Le Cz (S F') → Le (Add Lo Cz) (Len L) → SortedR Cz Lo (SortRangeL (S F') Lo Cz L)) {
          Z => λ (Hf : Le Z (S F')). λ (Hb : Le (Add Lo Z) (Len L)). SortedRZero Lo L,
          S (Cnt') Nih => elim Cnt' return (λ (Cz' : Nat). Le (S Cz') (S F') → Le (Add Lo (S Cz')) (Len L) → SortedR (S Cz') Lo (SortRangeL (S F') Lo (S Cz') L)) {
            Z => λ (Hf : Le (S Z) (S F')). λ (Hb : Le (Add Lo (S Z)) (Len L)). SortedROne Lo L,
            S (Cnt'') N2ih => λ (Hf : Le (S (S Cnt'')) (S F')). λ (Hb : Le (Add Lo (S (S Cnt''))) (Len L)).
              SortedRWidthCong
                (S (Add (PartIdxRangeL Lo (S (S Cnt'')) L) (PartGapRangeL Lo (S (S Cnt'')) L)))
                (S (S Cnt'')) Lo
                (SortRangeL F' (S (Add Lo (PartIdxRangeL Lo (S (S Cnt'')) L))) (PartGapRangeL Lo (S (S Cnt'')) L)
                  (SortRangeL F' Lo (PartIdxRangeL Lo (S (S Cnt'')) L) (PartitionRangeL Lo (S (S Cnt'')) L)))
                (IdCongr Nat Nat (λ (N : Nat). S N)
                  (Add (PartIdxRangeL Lo (S (S Cnt'')) L) (PartGapRangeL Lo (S (S Cnt'')) L)) (S Cnt'')
                  (PartSize Lo Cnt'' L))
                (Glue (PartIdxRangeL Lo (S (S Cnt'')) L) (PartGapRangeL Lo (S (S Cnt'')) L) Lo (NthL Lo L)
                  (SortRangeL F' (S (Add Lo (PartIdxRangeL Lo (S (S Cnt'')) L))) (PartGapRangeL Lo (S (S Cnt'')) L)
                    (SortRangeL F' Lo (PartIdxRangeL Lo (S (S Cnt'')) L) (PartitionRangeL Lo (S (S Cnt'')) L)))
                  (SortedInHPIV (PartIdxRangeL Lo (S (S Cnt'')) L) (PartGapRangeL Lo (S (S Cnt'')) L) Lo (NthL Lo L)
                    (PartitionRangeL Lo (S (S Cnt'')) L) F' (PartitionPivot Lo (S (S Cnt'')) L Hb))
                  (SortedInSL (PartIdxRangeL Lo (S (S Cnt'')) L) (PartGapRangeL Lo (S (S Cnt'')) L) Lo
                    (PartitionRangeL Lo (S (S Cnt'')) L) F'
                    (Ih Lo (PartIdxRangeL Lo (S (S Cnt'')) L) (PartitionRangeL Lo (S (S Cnt'')) L)
                      (LeTrans (PartIdxRangeL Lo (S (S Cnt'')) L) (S Cnt'') F'
                        (LeRwR (PartIdxRangeL Lo (S (S Cnt'')) L)
                          (Add (PartIdxRangeL Lo (S (S Cnt'')) L) (PartGapRangeL Lo (S (S Cnt'')) L)) (S Cnt'')
                          (PartSize Lo Cnt'' L)
                          (LeAdd (PartIdxRangeL Lo (S (S Cnt'')) L) (PartGapRangeL Lo (S (S Cnt'')) L)))
                        Hf)
                      (SortRangeBL Lo Cnt'' L Hb)))
                  (SortedInAL (PartIdxRangeL Lo (S (S Cnt'')) L) (PartGapRangeL Lo (S (S Cnt'')) L) Lo (NthL Lo L)
                    (PartitionRangeL Lo (S (S Cnt'')) L) F'
                    (PartitionAllLeR Lo (S (S Cnt'')) L Hb) (SortRangeBL Lo Cnt'' L Hb))
                  (SortedInAG (PartIdxRangeL Lo (S (S Cnt'')) L) (PartGapRangeL Lo (S (S Cnt'')) L) Lo (NthL Lo L)
                    (PartitionRangeL Lo (S (S Cnt'')) L) F'
                    (PartitionAllGtR Lo (S (S Cnt'')) L Hb) (SortRangeBR F' Lo Cnt'' L Hb))
                  (SortedInSR (PartIdxRangeL Lo (S (S Cnt'')) L) (PartGapRangeL Lo (S (S Cnt'')) L) Lo
                    (PartitionRangeL Lo (S (S Cnt'')) L) F'
                    (Ih (S (Add Lo (PartIdxRangeL Lo (S (S Cnt'')) L))) (PartGapRangeL Lo (S (S Cnt'')) L)
                      (SortRangeL F' Lo (PartIdxRangeL Lo (S (S Cnt'')) L) (PartitionRangeL Lo (S (S Cnt'')) L))
                      (LeTrans (PartGapRangeL Lo (S (S Cnt'')) L) (S Cnt'') F'
                        (LeRwR (PartGapRangeL Lo (S (S Cnt'')) L)
                          (Add (PartIdxRangeL Lo (S (S Cnt'')) L) (PartGapRangeL Lo (S (S Cnt'')) L)) (S Cnt'')
                          (PartSize Lo Cnt'' L)
                          (LeAddL (PartGapRangeL Lo (S (S Cnt'')) L) (PartIdxRangeL Lo (S (S Cnt'')) L)))
                        Hf)
                      (SortRangeBR F' Lo Cnt'' L Hb))))
          }
        }
    } }

/-! ## M23 (§23) — the whole-list vocabulary

    Direct proving over WHOLE lists (no `lo`/`cnt` range indices) needs three
    definitions M22's positional encoding had no use for. All three are OBSERVATION
    functions — they say what a list IS, not what any body DOES — which is the line
    a back-less ensures has to stay on.

    `Ub p l` / `Lb p l`: every element of `l` is ≤ p (resp. ≥ p). Σ-chained exactly
    as `Sorted`/`Bound` are (Std), so they are consumed by `sigmaRec` and built by
    `Pair` — which is why the Σ recursor had to land before any of this.

    `InsertL k x l`: `x` spliced in at index `k` (past the end it lands last). This
    is the shape a linked-list partition actually mutates by: relinking one cell,
    never sliding a range. Lomuto's swap-based scan is an ARRAY algorithm, and the
    naturalness-first rule (the north star's) says the program stays natural. -/

def Ub : Term := prog{
  λ (P : Nat). λ (L : List Nat).
    elim L return (λ (Lz : List Nat). Type) {
      Nil => Unit,
      Cons (H) (T) Ih => Σ (Hh : Le H P). Ih } }

def Lb : Term := prog{
  λ (P : Nat). λ (L : List Nat).
    elim L return (λ (Lz : List Nat). Type) {
      Nil => Unit,
      Cons (H) (T) Ih => Σ (Hh : Le P H). Ih } }

def InsertL : Term := prog{
  λ (K : Nat).
    elim K return (λ (Kz : Nat). Nat → List Nat → List Nat) {
      Z => λ (X : Nat). λ (L : List Nat). Cons X L,
      S (K2) Ih => λ (X : Nat). λ (L : List Nat).
        elim L return (λ (Lz : List Nat). List Nat) {
          Nil => Cons X Nil,
          Cons (H) (T) Iht => Cons H (Ih X T) } } }

/-- Generic J-transport at `List Nat`: `x = y ⟹ P x → P y`. `LeRwR`/`LeRwL` are
    this at `Le`-shaped `P` over `Nat`; a back-less body needs the unrestricted form,
    because every certificate it returns is stated over an exit snapshot it only
    knows PROPOSITIONALLY (the callee's evidence), never definitionally. -/
def ListRw : Term := prog{
  λ (P : List Nat → Type). λ (X : List Nat). λ (Y : List Nat).
    λ (H : Id (List Nat) X Y). λ (Px : P X).
      j (List Nat) X (λ (Y2 : List Nat). λ (Hh : Id (List Nat) X Y2). P Y2) Px Y H }
def ListRwTy : Term := prog{
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

def SortedHead : Term := prog{
  λ (H : Nat). λ (T : List Nat). λ (S0 : Σ (Hb : Bound H T). Sorted T).
    elim S0 return (λ (Q : Σ (Hb : Bound H T). Sorted T). Bound H T) {
      Pair (X) (Y) => X } }
def SortedHeadTy : Term := prog{
  Π (H : Nat) → Π (T : List Nat) → Sorted (Cons H T) → Bound H T }

def SortedTail : Term := prog{
  λ (H : Nat). λ (T : List Nat). λ (S0 : Σ (Hb : Bound H T). Sorted T).
    elim S0 return (λ (Q : Σ (Hb : Bound H T). Sorted T). Sorted T) {
      Pair (X) (Y) => Y } }
def SortedTailTy : Term := prog{
  Π (H : Nat) → Π (T : List Nat) → Sorted (Cons H T) → Sorted T }

def UbHead : Term := prog{
  λ (P : Nat). λ (H : Nat). λ (T : List Nat). λ (U : Σ (Hu : Le H P). Ub P T).
    elim U return (λ (Q : Σ (Hu : Le H P). Ub P T). Le H P) {
      Pair (X) (Y) => X } }
def UbHeadTy : Term := prog{
  Π (P : Nat) → Π (H : Nat) → Π (T : List Nat) → Ub P (Cons H T) → Le H P }

def UbTail : Term := prog{
  λ (P : Nat). λ (H : Nat). λ (T : List Nat). λ (U : Σ (Hu : Le H P). Ub P T).
    elim U return (λ (Q : Σ (Hu : Le H P). Ub P T). Ub P T) {
      Pair (X) (Y) => Y } }
def UbTailTy : Term := prog{
  Π (P : Nat) → Π (H : Nat) → Π (T : List Nat) → Ub P (Cons H T) → Ub P T }

/-- `Lb p l ⟹ Bound p l`: a lower bound on EVERY element is in particular a bound on
    the HEAD, which is all `Sorted (Cons p b)` asks of the pivot. The two predicates
    agree definitionally at `Nil` (both `⊤`) and differ at `Cons` only by how much
    they say, so this is a `listRec` whose `Cons` arm is a first projection. -/
def LbBound : Term := prog{
  λ (P : Nat). λ (L : List Nat).
    elim L return (λ (Lz : List Nat). Lb P Lz → Bound P Lz) {
      Nil => λ (Hn : Unit). Hn,
      Cons (H) (T) Ih => λ (Hl : Σ (Hh : Le P H). Lb P T).
        elim Hl return (λ (Q : Σ (Hh : Le P H). Lb P T). Le P H) {
          Pair (X) (Y) => X } } }
def LbBoundTy : Term := prog{
  Π (P : Nat) → Π (L : List Nat) → Lb P L → Bound P L }

/-- Head-bound transport across the splice: if `h` bounds the head of `t`, and `h ≤
    p`, then `h` bounds the head of `t ++ p :: b`. The `listRec` on `t` IS the case
    analysis the caller would otherwise have to do inline: at `Nil` the new head is
    the PIVOT (so the bound is `Le h p`, the second hypothesis), at `Cons` the head is
    unchanged by the append (so the bound is the first hypothesis, verbatim). No IH is
    consumed — `Bound` looks exactly one cell deep, so this recursion is a case
    analysis and nothing more. -/
def BoundAppend : Term := prog{
  λ (H : Nat). λ (P : Nat). λ (T : List Nat). λ (B : List Nat).
    elim T return (λ (Tz : List Nat).
        Bound H Tz → Le H P → Bound H (Append Tz (Cons P B))) {
      Nil => λ (Hb : Unit). λ (Hp : Le H P). Hp,
      Cons (H2) (T2) Ih => λ (Hb : Le H H2). λ (Hp : Le H P). Hb } }
def BoundAppendTy : Term := prog{
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
def SortedAppendPivot : Term := prog{
  λ (P : Nat). λ (A : List Nat). λ (B : List Nat).
    λ (Sa : Sorted A). λ (Ua : Ub P A). λ (Sb : Sorted B). λ (Lb0 : Lb P B).
      elim A return (λ (Az : List Nat).
          Sorted Az → Ub P Az → Sorted (Append Az (Cons P B))) {
        Nil => λ (Sn : Unit). λ (Un : Unit). Pair(LbBound P B Lb0, Sb),
        Cons (H) (T) Ih => λ (Sc : Sorted (Cons H T)). λ (Uc : Ub P (Cons H T)).
          Pair(BoundAppend H P T B (SortedHead H T Sc) (UbHead P H T Uc),
               Ih (SortedTail H T Sc) (UbTail P H T Uc))
      } Sa Ua }
def SortedAppendPivotTy : Term := prog{
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
def CountConsL : Term := prog{
  λ (N : Nat). λ (X : Nat). λ (A : List Nat). λ (B : List Nat). λ (C : List Nat).
    λ (H : Id Nat (Add (Count N A) (Count N B)) (Count N C)).
      elim (Eqb N X) return (λ (Bv : Bool).
        Id Nat (Add (boolRec (λ (W : Bool). Nat) (S (Count N A)) (Count N A) Bv) (Count N B))
               (boolRec (λ (W : Bool). Nat) (S (Count N C)) (Count N C) Bv)) {
        True => IdCongr Nat Nat (λ (R : Nat). S R)
                  (Add (Count N A) (Count N B)) (Count N C) H,
        False => H } }
def CountConsLTy : Term := prog{
  Π (N : Nat) → Π (X : Nat) → Π (A : List Nat) → Π (B : List Nat) → Π (C : List Nat) →
    Id Nat (Add (Count N A) (Count N B)) (Count N C) →
    Id Nat (Add (Count N (Cons X A)) (Count N B)) (Count N (Cons X C)) }

/-- Head onto the RIGHT part. Here the successor lands under `Add`'s SECOND argument,
    which is where the asymmetry of a first-argument-recursive `Add` shows up: the
    `True` arm needs `AddSucc` before the `IdCongr`. -/
def CountConsR : Term := prog{
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
def CountConsRTy : Term := prog{
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
def LbHead : Term := prog{
  λ (P : Nat). λ (H : Nat). λ (T : List Nat). λ (U : Σ (Hu : Le P H). Lb P T).
    elim U return (λ (Q : Σ (Hu : Le P H). Lb P T). Le P H) {
      Pair (X) (Y) => X } }
def LbHeadTy : Term := prog{
  Π (P : Nat) → Π (H : Nat) → Π (T : List Nat) → Lb P (Cons H T) → Le P H }

def LbTail : Term := prog{
  λ (P : Nat). λ (H : Nat). λ (T : List Nat). λ (U : Σ (Hu : Le P H). Lb P T).
    elim U return (λ (Q : Σ (Hu : Le P H). Lb P T). Lb P T) {
      Pair (X) (Y) => Y } }
def LbTailTy : Term := prog{
  Π (P : Nat) → Π (H : Nat) → Π (T : List Nat) → Lb P (Cons H T) → Lb P T }

/-- `Ub p l ⟹ nothing above p occurs in l`. At `Cons h t` the head misses every
    `x > p`, because `h ≤ p < x` makes `Eqb x h` False (`EqbGtFalse`), so the count
    steps past the head onto the IH. -/
def NoAboveOfUb : Term := prog{
  λ (P : Nat). λ (L : List Nat).
    elim L return (λ (Lz : List Nat).
        Ub P Lz → Π (X : Nat) → Le (S P) X → Id Nat (Count X Lz) Z) {
      Nil => λ (U : Unit). λ (X : Nat). λ (Hx : Le (S P) X). Refl,
      Cons (H) (T) Ih => λ (U : Σ (Hh : Le H P). Ub P T). λ (X : Nat). λ (Hx : Le (S P) X).
        IdTrans Nat (Count X (Cons H T)) (Count X T) Z
          (CountConsMiss X H T
            (EqbGtFalse H X (LeTrans (S H) (S P) X (UbHead P H T U) Hx)))
          (Ih (UbTail P H T U) X Hx) } }
def NoAboveOfUbTy : Term := prog{
  Π (P : Nat) → Π (L : List Nat) → Ub P L →
    Π (X : Nat) → Le (S P) X → Id Nat (Count X L) Z }

/-- …and back. The head bound comes from a `Leb h p` split: if it were False then
    `h > p`, so `Count h l = Z` by hypothesis — but `Count h (Cons h t)` is `S (count
    h t)` (`EqbRefl`), and `Z = S _` is `znots`. The tail hypothesis is the same
    argument run the other way: `Count x (Cons h t) = Z` forces `Count x t = Z`,
    trivially when `Eqb x h` misses and by the same contradiction when it hits. -/
def UbOfNoAbove : Term := prog{
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
def UbOfNoAboveTy : Term := prog{
  Π (P : Nat) → Π (L : List Nat) →
    (Π (X : Nat) → Le (S P) X → Id Nat (Count X L) Z) → Ub P L }

/-- THE KEYSTONE. An upper bound survives any count-preserving rearrangement — which
    is exactly what a recursive sort hands back about the part it sorted. -/
def UbPerm : Term := prog{
  λ (P : Nat). λ (A : List Nat). λ (B : List Nat).
    λ (Hc : Π (N : Nat) → Id Nat (Count N A) (Count N B)). λ (Hb : Ub P B).
      UbOfNoAbove P A (λ (X : Nat). λ (Hx : Le (S P) X).
        IdTrans Nat (Count X A) (Count X B) Z (Hc X) (NoAboveOfUb P B Hb X Hx)) }
def UbPermTy : Term := prog{
  Π (P : Nat) → Π (A : List Nat) → Π (B : List Nat) →
    (Π (N : Nat) → Id Nat (Count N A) (Count N B)) → Ub P B → Ub P A }

/-- The `Lb` mirror: `Lb p l ⟹ nothing strictly below p occurs`. Here the head misses
    every `x < p ≤ h` by `EqbLtFalse`. -/
def NoBelowOfLb : Term := prog{
  λ (P : Nat). λ (L : List Nat).
    elim L return (λ (Lz : List Nat).
        Lb P Lz → Π (X : Nat) → Le (S X) P → Id Nat (Count X Lz) Z) {
      Nil => λ (U : Unit). λ (X : Nat). λ (Hx : Le (S X) P). Refl,
      Cons (H) (T) Ih => λ (U : Σ (Hh : Le P H). Lb P T). λ (X : Nat). λ (Hx : Le (S X) P).
        IdTrans Nat (Count X (Cons H T)) (Count X T) Z
          (CountConsMiss X H T
            (EqbLtFalse X H (LeTrans (S X) P H Hx (LbHead P H T U))))
          (Ih (LbTail P H T U) X Hx) } }
def NoBelowOfLbTy : Term := prog{
  Π (P : Nat) → Π (L : List Nat) → Lb P L →
    Π (X : Nat) → Le (S X) P → Id Nat (Count X L) Z }

def LbOfNoBelow : Term := prog{
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
def LbOfNoBelowTy : Term := prog{
  Π (P : Nat) → Π (L : List Nat) →
    (Π (X : Nat) → Le (S X) P → Id Nat (Count X L) Z) → Lb P L }

def LbPerm : Term := prog{
  λ (P : Nat). λ (A : List Nat). λ (B : List Nat).
    λ (Hc : Π (N : Nat) → Id Nat (Count N A) (Count N B)). λ (Hb : Lb P B).
      LbOfNoBelow P A (λ (X : Nat). λ (Hx : Le (S X) P).
        IdTrans Nat (Count X A) (Count X B) Z (Hc X) (NoBelowOfLb P B Hb X Hx)) }
def LbPermTy : Term := prog{
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

/-- The empty array. -/
def Anil : Term := prog{ Arr() }

/-- `CountA x a` — the multiset counter, `Count`'s transfer. -/
def CountA : Term := prog{
  λ (X : Nat). λ (N : Nat). λ (A : Array N Nat).
    arrRec Nat (λ (M : Nat). λ (B : Array M Nat). Nat) Z
      (λ (K : Nat). λ (H : Nat). λ (T : Array K Nat). λ (Ih : Nat).
        elim (Eqb X H) return (λ (Bz : Bool). Nat) { True => S Ih, False => Ih })
      N A }

/-- `BoundA p a` — the head of `a` is ≥ `p`. `Bound`'s transfer. -/
def BoundA : Term := prog{
  λ (P : Nat). λ (N : Nat). λ (A : Array N Nat).
    arrRec Nat (λ (M : Nat). λ (B : Array M Nat). Type) Unit
      (λ (K : Nat). λ (H : Nat). λ (T : Array K Nat). λ (Ih : Type). Le P H) N A }

/-- `SortedA a` — the Σ-chain over the spine. `Sorted`'s transfer. -/
def SortedA : Term := prog{
  λ (N : Nat). λ (A : Array N Nat).
    arrRec Nat (λ (M : Nat). λ (B : Array M Nat). Type) Unit
      (λ (K : Nat). λ (H : Nat). λ (T : Array K Nat). λ (Ih : Type).
        Σ (Hb : BoundA H K T). Ih) N A }

/-- `UbA p a` — every element of `a` is ≤ `p`. `Ub`'s transfer. -/
def UbA : Term := prog{
  λ (P : Nat). λ (N : Nat). λ (A : Array N Nat).
    arrRec Nat (λ (M : Nat). λ (B : Array M Nat). Type) Unit
      (λ (K : Nat). λ (H : Nat). λ (T : Array K Nat). λ (Ih : Type).
        Σ (Hh : Le H P). Ih) N A }

/-- `LbA p a` — every element of `a` is ≥ `p`. `Lb`'s transfer. -/
def LbA : Term := prog{
  λ (P : Nat). λ (N : Nat). λ (A : Array N Nat).
    arrRec Nat (λ (M : Nat). λ (B : Array M Nat). Type) Unit
      (λ (K : Nat). λ (H : Nat). λ (T : Array K Nat). λ (Ih : Type).
        Σ (Hh : Le P H). Ih) N A }

/-- `Asingle x` — the one-element array, `[x]`. ¶6's glue is stated over
    `arrCat (Asingle p) r`, which is the array spelling of `Cons p b`. -/
def Asingle : Term := prog{ λ (X : Nat). acons Z X Arr() }

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

def SortedHeadA : Term := prog{
  λ (K : Nat). λ (H : Nat). λ (T : Array K Nat).
    λ (S0 : Σ (Hb : BoundA H K T). SortedA K T).
      elim S0 return (λ (Q : Σ (Hb : BoundA H K T). SortedA K T). BoundA H K T) {
        Pair (X) (Y) => X } }
def SortedHeadATy : Term := prog{
  Π (K : Nat) → Π (H : Nat) → Π (T : Array K Nat) →
    SortedA (S K) (acons K H T) → BoundA H K T }

def SortedTailA : Term := prog{
  λ (K : Nat). λ (H : Nat). λ (T : Array K Nat).
    λ (S0 : Σ (Hb : BoundA H K T). SortedA K T).
      elim S0 return (λ (Q : Σ (Hb : BoundA H K T). SortedA K T). SortedA K T) {
        Pair (X) (Y) => Y } }
def SortedTailATy : Term := prog{
  Π (K : Nat) → Π (H : Nat) → Π (T : Array K Nat) →
    SortedA (S K) (acons K H T) → SortedA K T }

def UbHeadA : Term := prog{
  λ (P : Nat). λ (K : Nat). λ (H : Nat). λ (T : Array K Nat).
    λ (U : Σ (Hu : Le H P). UbA P K T).
      elim U return (λ (Q : Σ (Hu : Le H P). UbA P K T). Le H P) {
        Pair (X) (Y) => X } }
def UbHeadATy : Term := prog{
  Π (P : Nat) → Π (K : Nat) → Π (H : Nat) → Π (T : Array K Nat) →
    UbA P (S K) (acons K H T) → Le H P }

def UbTailA : Term := prog{
  λ (P : Nat). λ (K : Nat). λ (H : Nat). λ (T : Array K Nat).
    λ (U : Σ (Hu : Le H P). UbA P K T).
      elim U return (λ (Q : Σ (Hu : Le H P). UbA P K T). UbA P K T) {
        Pair (X) (Y) => Y } }
def UbTailATy : Term := prog{
  Π (P : Nat) → Π (K : Nat) → Π (H : Nat) → Π (T : Array K Nat) →
    UbA P (S K) (acons K H T) → UbA P K T }

/-- `LbA p a ⟹ BoundA p a`, `LbBound`'s transfer: a lower bound on every element is in
    particular a bound on the head, which is all `SortedA (acons p b)` asks of the pivot. -/
def LbBoundA : Term := prog{
  λ (P : Nat). λ (N : Nat). λ (A : Array N Nat).
    arrRec Nat (λ (M : Nat). λ (B : Array M Nat). LbA P M B → BoundA P M B)
      (λ (Hn : Unit). Hn)
      (λ (K : Nat). λ (H : Nat). λ (T : Array K Nat).
        λ (Ih : LbA P K T → BoundA P K T).
          λ (Hl : Σ (Hh : Le P H). LbA P K T).
            elim Hl return (λ (Q : Σ (Hh : Le P H). LbA P K T). Le P H) {
              Pair (X) (Y) => X })
      N A }
def LbBoundATy : Term := prog{
  Π (P : Nat) → Π (N : Nat) → Π (A : Array N Nat) → LbA P N A → BoundA P N A }

/-- `BoundAppend`'s transfer: the head bound survives the splice. The recursion IS the
    case analysis — at the empty array the new head is the PIVOT, otherwise the head is
    unchanged by the concatenation. No IH is consumed, because `BoundA` looks exactly one
    cell deep. -/
def BoundArrCat : Term := prog{
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
def BoundArrCatTy : Term := prog{
  Π (H : Nat) → Π (P : Nat) → Π (K : Nat) → Π (T : Array K Nat) →
    Π (Q : Nat) → Π (B : Array Q Nat) →
      BoundA H K T → Le H P →
        BoundA H (Add K (S Q)) (arrCat K (S Q) T (arrCat 1 Q (Asingle P) B)) }

/-- **The quicksort glue** — `SortedAppendPivot` with the container swapped, and
    nothing else changed. This is ¶6's "textbook quicksort correctness statement, in the
    textbook shape", and the standing check on the whole migration: if this were not the
    near-verbatim restatement, something would be off. -/
def SortedArrCat : Term := prog{
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
def SortedArrCatTy : Term := prog{
  Π (P : Nat) → Π (M : Nat) → Π (A : Array M Nat) → Π (Q : Nat) → Π (B : Array Q Nat) →
    SortedA M A → UbA P M A → SortedA Q B → LbA P Q B →
      SortedA (Add M (S Q)) (arrCat M (S Q) A (arrCat 1 Q (Asingle P) B)) }

/-- `CountAppend`'s transfer, and ¶6's named survivor: "the one lemma that replaces
    `CountAppend`/`Take`/`Drop` is `CountArrCat : count x (arrCat a b) = add (count x a)
    (count x b)`, which is the same induction." It is the same induction — the `Cons`
    arm's dependent Bool-elim on `Eqb x h` transfers unchanged, because `CountA` unfolds
    on an `acons` exactly as `Count` unfolds on a `Cons`. -/
def CountArrCat : Term := prog{
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
def CountArrCatTy : Term := prog{
  Π (X : Nat) → Π (M : Nat) → Π (A : Array M Nat) → Π (Q : Nat) → Π (B : Array Q Nat) →
    Id Nat (CountA X (Add M Q) (arrCat M Q A B)) (Add (CountA X M A) (CountA X Q B)) }

/-! ### The permutation layer, transferred

    M23's keystone: "`Ub` and `Lb` (Σ-chains over the spine) are not natively
    permutation-invariant. Cross to the multiset, where the property is
    `Π x. x > p → Count x l = Z` and permutation-invariance is a one-line `IdTrans`."
    That crossing transfers with the container like everything else. -/

def CountAconsHit : Term := prog{
  λ (M : Nat). λ (A : Nat). λ (K : Nat). λ (L : Array K Nat). λ (Hq : Id Bool (Eqb M A) True).
    j Bool True
      (λ (Z0 : Bool). λ (H : Id Bool True Z0).
        Id Nat (boolRec (λ (W : Bool). Nat) (S (CountA M K L)) (CountA M K L) Z0)
               (S (CountA M K L)))
      Refl (Eqb M A) (IdSym Bool (Eqb M A) True Hq) }
def CountAconsHitTy : Term := prog{
  Π (M : Nat) → Π (A : Nat) → Π (K : Nat) → Π (L : Array K Nat) → Id Bool (Eqb M A) True →
    Id Nat (CountA M (S K) (acons K A L)) (S (CountA M K L)) }

def CountAconsMiss : Term := prog{
  λ (M : Nat). λ (H : Nat). λ (K : Nat). λ (T : Array K Nat). λ (Hq : Id Bool (Eqb M H) False).
    j Bool False
      (λ (Z0 : Bool). λ (Hh : Id Bool False Z0).
        Id Nat (boolRec (λ (W : Bool). Nat) (S (CountA M K T)) (CountA M K T) Z0)
               (CountA M K T))
      Refl (Eqb M H) (IdSym Bool (Eqb M H) False Hq) }
def CountAconsMissTy : Term := prog{
  Π (M : Nat) → Π (H : Nat) → Π (K : Nat) → Π (T : Array K Nat) → Id Bool (Eqb M H) False →
    Id Nat (CountA M (S K) (acons K H T)) (CountA M K T) }

def LbHeadA : Term := prog{
  λ (P : Nat). λ (K : Nat). λ (H : Nat). λ (T : Array K Nat).
    λ (U : Σ (Hh : Le P H). LbA P K T).
      elim U return (λ (Q : Σ (Hh : Le P H). LbA P K T). Le P H) { Pair (X) (Y) => X } }
def LbTailA : Term := prog{
  λ (P : Nat). λ (K : Nat). λ (H : Nat). λ (T : Array K Nat).
    λ (U : Σ (Hh : Le P H). LbA P K T).
      elim U return (λ (Q : Σ (Hh : Le P H). LbA P K T). LbA P K T) { Pair (X) (Y) => Y } }

def NoAboveOfUbA : Term := prog{
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
def NoAboveOfUbATy : Term := prog{
  Π (P : Nat) → Π (N : Nat) → Π (A : Array N Nat) → UbA P N A →
    Π (X : Nat) → Le (S P) X → Id Nat (CountA X N A) Z }

def UbOfNoAboveA : Term := prog{
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
def UbOfNoAboveATy : Term := prog{
  Π (P : Nat) → Π (N : Nat) → Π (A : Array N Nat) →
    (Π (X : Nat) → Le (S P) X → Id Nat (CountA X N A) Z) → UbA P N A }

/-- THE KEYSTONE, transferred: an upper bound survives any count-preserving
    rearrangement — which is exactly what a recursive sort hands back about the part it
    sorted. -/
def UbPermA : Term := prog{
  λ (P : Nat). λ (M : Nat). λ (A : Array M Nat). λ (Q : Nat). λ (B : Array Q Nat).
    λ (Hc : Π (X : Nat) → Id Nat (CountA X M A) (CountA X Q B)). λ (Hb : UbA P Q B).
      UbOfNoAboveA P M A (λ (X : Nat). λ (Hx : Le (S P) X).
        IdTrans Nat (CountA X M A) (CountA X Q B) Z (Hc X)
          (NoAboveOfUbA P Q B Hb X Hx)) }
def UbPermATy : Term := prog{
  Π (P : Nat) → Π (M : Nat) → Π (A : Array M Nat) → Π (Q : Nat) → Π (B : Array Q Nat) →
    (Π (X : Nat) → Id Nat (CountA X M A) (CountA X Q B)) → UbA P Q B → UbA P M A }

def NoBelowOfLbA : Term := prog{
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
def NoBelowOfLbATy : Term := prog{
  Π (P : Nat) → Π (N : Nat) → Π (A : Array N Nat) → LbA P N A →
    Π (X : Nat) → Le (S X) P → Id Nat (CountA X N A) Z }

def LbOfNoBelowA : Term := prog{
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
def LbOfNoBelowATy : Term := prog{
  Π (P : Nat) → Π (N : Nat) → Π (A : Array N Nat) →
    (Π (X : Nat) → Le (S X) P → Id Nat (CountA X N A) Z) → LbA P N A }

def LbPermA : Term := prog{
  λ (P : Nat). λ (M : Nat). λ (A : Array M Nat). λ (Q : Nat). λ (B : Array Q Nat).
    λ (Hc : Π (X : Nat) → Id Nat (CountA X M A) (CountA X Q B)). λ (Hb : LbA P Q B).
      LbOfNoBelowA P M A (λ (X : Nat). λ (Hx : Le (S X) P).
        IdTrans Nat (CountA X M A) (CountA X Q B) Z (Hc X)
          (NoBelowOfLbA P Q B Hb X Hx)) }
def LbPermATy : Term := prog{
  Π (P : Nat) → Π (M : Nat) → Π (A : Array M Nat) → Π (Q : Nat) → Π (B : Array Q Nat) →
    (Π (X : Nat) → Id Nat (CountA X M A) (CountA X Q B)) → LbA P Q B → LbA P M A }

/-- Two-element count commutation over arrays — `Cons2Comm`'s transfer at the fixed
    width the miniature sort needs. Double case split on `Eqb`, all four arms `Refl`;
    the `Eqb m a = False` arm needs no inner split because both sides already agree. -/
def CountSwap2 : Term := prog{
  λ (M : Nat). λ (A : Nat). λ (B : Nat).
    elim (Eqb M A) generalizing (Id Nat (CountA M 2 Arr(B, A)) (CountA M 2 Arr(A, B))) {
      True => elim (Eqb M B) generalizing
        (Id Nat (boolRec (λ (W : Bool). Nat) (S (S Z)) (S Z) (Eqb M B))
                (S (boolRec (λ (W : Bool). Nat) (S Z) Z (Eqb M B)))) {
        True => Refl, False => Refl },
      False => Refl } }
def CountSwap2Ty : Term := prog{
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
def NatRw : Term := prog{
  λ (P : Nat → Type). λ (X : Nat). λ (Y : Nat). λ (H : Id Nat X Y). λ (Px : P X).
    j Nat X (λ (Y2 : Nat). λ (Hh : Id Nat X Y2). P Y2) Px Y H }
def NatRwTy : Term := prog{
  Π (P : Nat → Type) → Π (X : Nat) → Π (Y : Nat) → Id Nat X Y → P X → P Y }

/-- `Le n Z ⟹ n = Z`. The array quicksort tests emptiness with `Leb 1 n` rather than
    by matching `n`, because matching refines the length to `S m` and T2's rigid-extent
    restriction then blocks the three-way carve at the returned index. So the False
    branch holds `Le n Z` and has to turn it into the equation the nil lemmas want. -/
def LeZeroEq : Term := prog{
  λ (N : Nat). elim N return (λ (Z0 : Nat). Le Z0 Z → Id Nat Z0 Z) {
    Z => λ (H : Le Z Z). Refl,
    S (N2) Ih => λ (H : Bot). botElim (Id Nat (S N2) Z) H } }
def LeZeroEqTy : Term := prog{ Π (N : Nat) → Le N Z → Id Nat N Z }

/-- `SortedA` of an array whose LENGTH is zero.

    Not `unit`, and that is the point: there is no η at length zero. `SortedA Z σ` is a
    stuck `arrRec` — the recursor fires on `Arr`, never on the index — so an opaque
    length-zero payload does not compute to `Unit` and the sort's base case cannot be
    discharged by the trivial term. The induction is on the ARRAY with the equation
    carried, and the cons case is dead. -/
def SortedANil : Term := prog{
  λ (N : Nat). λ (A : Array N Nat).
    arrRec Nat (λ (M : Nat). λ (B : Array M Nat). Id Nat M Z → SortedA M B)
      (λ (H : Id Nat Z Z). unit)
      (λ (K : Nat). λ (Hh : Nat). λ (T : Array K Nat).
        λ (Ih : Id Nat K Z → SortedA K T).
          λ (H : Id Nat (S K) Z).
            botElim (SortedA (S K) (acons K Hh T)) (Znots K (IdSym Nat (S K) Z H)))
      N A }
def SortedANilTy : Term := prog{
  Π (N : Nat) → Π (A : Array N Nat) → Id Nat N Z → SortedA N A }

/-- `SplitAL p k a` — the first `k` elements are ≤ `p`, the rest are ≥ `p`. -/
def SplitAL : Term := prog{
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
def PartA : Term := prog{
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
def SplitANil : Term := prog{
  λ (P : Nat). λ (Kz : Nat). λ (N : Nat). λ (A : Array N Nat). λ (Hz : Id Nat N Z).
    arrRec Nat (λ (M : Nat). λ (B : Array M Nat).
        Π (K2 : Nat) → Id Nat M Z → SplitAL P K2 M B)
      (λ (K2 : Nat). λ (H : Id Nat Z Z). unit)
      (λ (M : Nat). λ (Hh : Nat). λ (T : Array M Nat).
        λ (Ih : Π (K2 : Nat) → Id Nat M Z → SplitAL P K2 M T).
          λ (K2 : Nat). λ (H : Id Nat (S M) Z).
            botElim (SplitAL P K2 (S M) (acons M Hh T)) (Znots M (IdSym Nat (S M) Z H)))
      N A Kz Hz }
def SplitANilTy : Term := prog{
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
def SplitA0Lb : Term := prog{
  λ (P : Nat). λ (N : Nat). λ (A : Array N Nat).
    arrRec Nat (λ (M : Nat). λ (B : Array M Nat). SplitAL P Z M B → LbA P M B)
      (λ (H : Unit). unit)
      (λ (K : Nat). λ (Hh : Nat). λ (T : Array K Nat).
        λ (Ih : SplitAL P Z K T → LbA P K T).
          λ (S0 : Σ (H2 : Le P Hh). SplitAL P Z K T).
            elim S0 return (λ (Qz : Σ (H2 : Le P Hh). SplitAL P Z K T). LbA P (S K) (acons K Hh T)) {
              Pair (U) (V) => Pair(U, Ih V) })
      N A }
def SplitA0LbTy : Term := prog{
  Π (P : Nat) → Π (N : Nat) → Π (A : Array N Nat) → SplitAL P Z N A → LbA P N A }

/-- Split a `SplitAL` whose skip count runs ONE PAST the left part: the left part is
    wholly bounded, and what is left is a `SplitAL` at skip 1 over the right part. This
    is the shape the swap branch needs — it reads off both "the left part is all ≤ p"
    and "the element about to be swapped out is ≤ p" in one step. -/
def SplitACatE1 : Term := prog{
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
def SplitACatE1Ty : Term := prog{
  Π (P : Nat) → Π (K : Nat) → Π (Mm : Nat) → Π (L : Array K Nat) → Π (W : Array Mm Nat) →
    SplitAL P (S K) (Add K Mm) (arrCat K Mm L W) →
      Σ (Hu : UbA P K L). SplitAL P (S Z) Mm W }

/-- The converse at skip exactly `k`: a bounded left part in front of a `SplitAL` at
    skip zero is a `SplitAL` at skip `k`. -/
def SplitACatI0 : Term := prog{
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
def SplitACatI0Ty : Term := prog{
  Π (P : Nat) → Π (K : Nat) → Π (Mm : Nat) → Π (L : Array K Nat) → Π (W : Array Mm Nat) →
    UbA P K L → SplitAL P Z Mm W → SplitAL P K (Add K Mm) (arrCat K Mm L W) }

/-- `PartA`'s introduction, the partition's last step: a bounded left part in front of
    a `PartA` at skip zero (which is "the head IS the pivot, the tail is ≥ it"). -/
def PartACatI0 : Term := prog{
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
def PartACatI0Ty : Term := prog{
  Π (Pv : Nat) → Π (K : Nat) → Π (Mm : Nat) → Π (L : Array K Nat) → Π (W : Array Mm Nat) →
    UbA Pv K L → PartA Pv Z Mm W → PartA Pv K (Add K Mm) (arrCat K Mm L W) }

/-- **THE BRIDGE.** `PartA`'s elimination at the sort's own carve: the left segment is
    bounded above by the pivot, and what remains is `PartA` at skip zero over the pivot
    slot and the right segment — which unfolds, with no further lemma, to exactly
    `Id Nat (that element) pv` and `LbA pv (right segment)`. Those three facts are
    `SortedArrCat`'s four hypotheses minus the two the recursive calls supply. -/
def PartACatE0 : Term := prog{
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
def PartACatE0Ty : Term := prog{
  Π (Pv : Nat) → Π (K : Nat) → Π (Mm : Nat) → Π (L : Array K Nat) → Π (W : Array Mm Nat) →
    PartA Pv K (Add K Mm) (arrCat K Mm L W) →
      Σ (Hu : UbA Pv K L). PartA Pv Z Mm W }

/-! ### The same crossings, one conclusion each

    A body cannot conveniently destructure a Σ — a `let`-bound pure value is not
    type-checked (§23's filed checker gap), so the alternative is an inline `elim` whose
    `return` motive is the function's whole return type written out again. Splitting each
    crossing into its two conclusions moves that cost into the pure layer, where writing
    the types is free, and keeps the programs readable. -/

def SplitACatUb : Term := prog{
  λ (P : Nat). λ (K : Nat). λ (Mm : Nat). λ (L : Array K Nat). λ (W : Array Mm Nat).
    λ (S0 : SplitAL P (S K) (Add K Mm) (arrCat K Mm L W)).
      elim (SplitACatE1 P K Mm L W S0)
        return (λ (Qz : Σ (Hu : UbA P K L). SplitAL P (S Z) Mm W). UbA P K L) {
          Pair (U) (V) => U } }
def SplitACatUbTy : Term := prog{
  Π (P : Nat) → Π (K : Nat) → Π (Mm : Nat) → Π (L : Array K Nat) → Π (W : Array Mm Nat) →
    SplitAL P (S K) (Add K Mm) (arrCat K Mm L W) → UbA P K L }

def SplitACatRest : Term := prog{
  λ (P : Nat). λ (K : Nat). λ (Mm : Nat). λ (L : Array K Nat). λ (W : Array Mm Nat).
    λ (S0 : SplitAL P (S K) (Add K Mm) (arrCat K Mm L W)).
      elim (SplitACatE1 P K Mm L W S0)
        return (λ (Qz : Σ (Hu : UbA P K L). SplitAL P (S Z) Mm W). SplitAL P (S Z) Mm W) {
          Pair (U) (V) => V } }
def SplitACatRestTy : Term := prog{
  Π (P : Nat) → Π (K : Nat) → Π (Mm : Nat) → Π (L : Array K Nat) → Π (W : Array Mm Nat) →
    SplitAL P (S K) (Add K Mm) (arrCat K Mm L W) → SplitAL P (S Z) Mm W }

/-- A skip-1 `SplitAL` over a cons: its head is bounded, and its tail is a skip-0 one.
    Both are definitional unfoldings; naming them keeps the swap branch flat. -/
def SplitA1Head : Term := prog{
  λ (P : Nat). λ (R : Nat). λ (G : Array R Nat). λ (Yv : Nat).
    λ (S0 : Σ (Hh : Le Yv P). SplitAL P Z R G).
      elim S0 return (λ (Qz : Σ (Hh : Le Yv P). SplitAL P Z R G). Le Yv P) {
        Pair (U) (V) => U } }
def SplitA1HeadTy : Term := prog{
  Π (P : Nat) → Π (R : Nat) → Π (G : Array R Nat) → Π (Yv : Nat) →
    SplitAL P (S Z) (S R) (acons R Yv G) → Le Yv P }

def SplitA1Tail : Term := prog{
  λ (P : Nat). λ (R : Nat). λ (G : Array R Nat). λ (Yv : Nat).
    λ (S0 : Σ (Hh : Le Yv P). SplitAL P Z R G).
      elim S0 return (λ (Qz : Σ (Hh : Le Yv P). SplitAL P Z R G). SplitAL P Z R G) {
        Pair (U) (V) => V } }
def SplitA1TailTy : Term := prog{
  Π (P : Nat) → Π (R : Nat) → Π (G : Array R Nat) → Π (Yv : Nat) →
    SplitAL P (S Z) (S R) (acons R Yv G) → SplitAL P Z R G }

def PartACatUb : Term := prog{
  λ (Pv : Nat). λ (K : Nat). λ (Mm : Nat). λ (L : Array K Nat). λ (W : Array Mm Nat).
    λ (S0 : PartA Pv K (Add K Mm) (arrCat K Mm L W)).
      elim (PartACatE0 Pv K Mm L W S0)
        return (λ (Qz : Σ (Hu : UbA Pv K L). PartA Pv Z Mm W). UbA Pv K L) {
          Pair (U) (V) => U } }
def PartACatUbTy : Term := prog{
  Π (Pv : Nat) → Π (K : Nat) → Π (Mm : Nat) → Π (L : Array K Nat) → Π (W : Array Mm Nat) →
    PartA Pv K (Add K Mm) (arrCat K Mm L W) → UbA Pv K L }

def PartACatRest : Term := prog{
  λ (Pv : Nat). λ (K : Nat). λ (Mm : Nat). λ (L : Array K Nat). λ (W : Array Mm Nat).
    λ (S0 : PartA Pv K (Add K Mm) (arrCat K Mm L W)).
      elim (PartACatE0 Pv K Mm L W S0)
        return (λ (Qz : Σ (Hu : UbA Pv K L). PartA Pv Z Mm W). PartA Pv Z Mm W) {
          Pair (U) (V) => V } }
def PartACatRestTy : Term := prog{
  Π (Pv : Nat) → Π (K : Nat) → Π (Mm : Nat) → Π (L : Array K Nat) → Π (W : Array Mm Nat) →
    PartA Pv K (Add K Mm) (arrCat K Mm L W) → PartA Pv Z Mm W }

/-- The pivot slot, read off a skip-0 `PartA`: the element there IS the pivot, and
    everything after it is bounded below by the pivot. These two are `SortedArrCat`'s
    remaining hypotheses, and the reason `PartA` records the pivot's identity at all. -/
def PartA0Eq : Term := prog{
  λ (Pv : Nat). λ (Jj : Nat). λ (G : Array Jj Nat). λ (Ev : Nat).
    λ (S0 : Σ (He : Id Nat Ev Pv). LbA Pv Jj G).
      elim S0 return (λ (Qz : Σ (He : Id Nat Ev Pv). LbA Pv Jj G). Id Nat Ev Pv) {
        Pair (U) (V) => U } }
def PartA0EqTy : Term := prog{
  Π (Pv : Nat) → Π (Jj : Nat) → Π (G : Array Jj Nat) → Π (Ev : Nat) →
    PartA Pv Z (S Jj) (acons Jj Ev G) → Id Nat Ev Pv }

def PartA0Lb : Term := prog{
  λ (Pv : Nat). λ (Jj : Nat). λ (G : Array Jj Nat). λ (Ev : Nat).
    λ (S0 : Σ (He : Id Nat Ev Pv). LbA Pv Jj G).
      elim S0 return (λ (Qz : Σ (He : Id Nat Ev Pv). LbA Pv Jj G). LbA Pv Jj G) {
        Pair (U) (V) => V } }
def PartA0LbTy : Term := prog{
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
def BumpN : Term := prog{
  λ (B : Bool). λ (C : Nat). elim B return (λ (W : Bool). Nat) { True => S C, False => C } }

/-- Congruence for `CountA` under a cons — `CountConsCongr`'s array counterpart. -/
def CountAconsCongr : Term := prog{
  λ (Q : Nat). λ (H : Nat). λ (K : Nat). λ (T1 : Array K Nat). λ (T2 : Array K Nat).
    λ (Hc : Id Nat (CountA Q K T1) (CountA Q K T2)).
      IdCongr Nat Nat (λ (C : Nat). BumpN (Eqb Q H) C)
        (CountA Q K T1) (CountA Q K T2) Hc }
def CountAconsCongrTy : Term := prog{
  Π (Q : Nat) → Π (H : Nat) → Π (K : Nat) → Π (T1 : Array K Nat) → Π (T2 : Array K Nat) →
    Id Nat (CountA Q K T1) (CountA Q K T2) →
      Id Nat (CountA Q (S K) (acons K H T1)) (CountA Q (S K) (acons K H T2)) }

/-- The arithmetic core of the swap, over the two `bump`s alone: which of the two
    exchanged elements is being counted does not matter. Four arms; the two mixed ones
    are `AddSucc` and its symmetry, and the two matching ones are `Refl` — `CountSwap2`
    at width two had all four `Refl` because both counts were concrete. -/
def BumpComm : Term := prog{
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
def BumpCommTy : Term := prog{
  Π (B1 : Bool) → Π (B2 : Bool) → Π (Cl : Nat) → Π (Cg : Nat) →
    Id Nat (BumpN B2 (Add Cl (BumpN B1 Cg))) (BumpN B1 (Add Cl (BumpN B2 Cg))) }

/-- **The swap preserves every count**, stated over exactly the spine the partition
    produces: head, left segment, the swapped cell, right segment. Two `CountArrCat`
    rewrites bracket `BumpComm`. -/
def CountSwapA : Term := prog{
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
def CountSwapATy : Term := prog{
  Π (Q : Nat) → Π (X : Nat) → Π (Y : Nat) → Π (K : Nat) → Π (L : Array K Nat) →
  Π (R : Nat) → Π (G : Array R Nat) →
    Id Nat (CountA Q (S (Add K (S R))) (acons (Add K (S R)) Y (arrCat K (S R) L (acons R X G))))
           (CountA Q (S (Add K (S R))) (acons (Add K (S R)) X (arrCat K (S R) L (acons R Y G)))) }

/-! ## `Mod`, `Div`, `Mul` — the hashmap's slot arithmetic (ported from `hm-probe-mod`,
    2026-08-17, verbatim — commit a6a549c5)

    `Mod`/`Div` ride one accumulator state `(R, C)`: `R` is the residue so far, `C` is
    how many increments remain before wrapping, and `R + C = B` is the invariant. Each
    step asks its question of `C` — an ARGUMENT — never of the recursive result, which
    is the shape the probe found mandatory: the textbook `mod` mentions its recursive
    result TWICE (once in the guard, once in the return) and was measured exponential
    under the no-sharing normalizer of that date. `NextR`/`NextC`/`NextQ` are the three
    non-recursive answers to "what happens to this component at one increment". At
    `B = Z` the wrapper returns `Z` (Lean's `%` would return the dividend); nothing
    downstream divides by zero, and every lemma is stated over `Le (S Z) n`. -/

def NextR : Term := prog{
  λ (R : Nat). λ (C : Nat).
    elim C return (λ (Cz : Nat). Nat) { Z => Z, S (C') Rc => S(R) } }

def NextC : Term := prog{
  λ (B : Nat). λ (C : Nat).
    elim C return (λ (Cz : Nat). Nat) { Z => B, S (C') Rc => C' } }

def NextQ : Term := prog{
  λ (Q : Nat). λ (C : Nat).
    elim C return (λ (Cz : Nat). Nat) { Z => S(Q), S (C') Rc => Q } }

def ModC : Term := prog{
  λ (A : Nat).
    elim A return (λ (Az : Nat). Π (B : Nat) → Π (R : Nat) → Π (C : Nat) → Nat) {
      Z => λ (B : Nat). λ (R : Nat). λ (C : Nat). R,
      S (A') Rec => λ (B : Nat). λ (R : Nat). λ (C : Nat).
        Rec B (NextR R C) (NextC B C) } }

def Mod : Term := prog{
  λ (A : Nat). λ (B : Nat).
    elim B return (λ (Bz : Nat). Nat) { Z => Z, S (B') Rb => ModC A B' Z B' } }

/-- `Div` rides the same state with a quotient that ticks exactly when `C` wraps. -/
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

/-- `Mul a b` by recursion on `b`, mentioning its recursive result exactly once
    (`Add A Rec`) — the same single-occurrence discipline `ModC`'s accumulator uses. -/
def Mul : Term := prog{
  λ (A : Nat). λ (B : Nat). elim B return (λ (Bm : Nat). Nat) {
    Z => Z, S (B') Rec => Add A Rec } }

/-! ### M2 — the slot index is below the capacity -/

def StepInv : Term := prog{
  λ (B : Nat). λ (R : Nat). λ (C : Nat).
    elim C return (λ (Cz : Nat). Le (Add R Cz) B → Le (Add (NextR R Cz) (NextC B Cz)) B) {
      Z => λ (H : Le (Add R Z) B). LeRefl B,
      S (C') Rc => λ (H : Le (Add R (S C')) B).
        LeRwL B (Add R (S C')) (S (Add R C')) (AddSucc R C') H } }
def StepInvTy : Term := prog{
  Π (B : Nat) → Π (R : Nat) → Π (C : Nat) →
    Le (Add R C) B → Le (Add (NextR R C) (NextC B C)) B }

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

/-- The form a PROGRAM can use: the capacity is an opaque `n` carrying `Le (S Z) n`,
    never the pattern `S c` — a `fn`'s premise (3) may not refine `S c`, since it is a
    constructor applied to a σ, which is rigid. -/
def ModLtN : Term := prog{
  λ (A : Nat). λ (N : Nat).
    elim N return (λ (Nz : Nat). Le (S Z) Nz → Le (S (Mod A Nz)) Nz) {
      Z => λ (H : Le (S Z) Z). botElim (Le (S (Mod A Z)) Z) H,
      S (B') Rb => λ (H : Le (S Z) (S B')). ModCLt A B' Z B' (LeRefl B') } }
def ModLtNTy : Term := prog{
  Π (A : Nat) → Π (N : Nat) → Le (S Z) N → Le (S (Mod A N)) N }

/-! ### M3 — minting the carve's decomposition

    `Le (S i) n → Σ r. Id Nat n (Add i (S r))`: "i is strictly below n" becomes the
    residue `r` and the equation premise (3) wants CITED. The Σ's own projections
    check but are the WRONG route for a program: `ModFst I N Dec` mentions `N`, so
    citing the projected equation makes premise (3) try to solve `n = f(n)` and the
    occurs check refuses it — the Σ has to cross a CALL instead (`SlotOf` below),
    the same shape `partitionA` already uses for `splitA`'s returned `k`/`r`. -/

def ModDec : Term := prog{
  λ (I : Nat).
    elim I return (λ (Iz : Nat).
        Π (N : Nat) → Le (S Iz) N → Σ (R : Nat). Id Nat N (Add Iz (S R))) {
      Z => λ (N : Nat).
        elim N return (λ (Nz : Nat). Le (S Z) Nz → Σ (R : Nat). Id Nat Nz (Add Z (S R))) {
          Z => λ (H : Le (S Z) Z). botElim (Σ (R : Nat). Id Nat Z (Add Z (S R))) H,
          S (N') Ihn => λ (H : Le (S Z) (S N')). Pair(N', Refl) },
      S (I') Ih => λ (N : Nat).
        elim N return (λ (Nz : Nat).
            Le (S (S I')) Nz → Σ (R : Nat). Id Nat Nz (Add (S I') (S R))) {
          Z => λ (H : Le (S (S I')) Z). botElim (Σ (R : Nat). Id Nat Z (Add (S I') (S R))) H,
          S (N') Ihn => λ (H : Le (S (S I')) (S N')).
            elim (Ih N' H) return (λ (Q : Σ (R : Nat). Id Nat N' (Add I' (S R))).
                Σ (R : Nat). Id Nat (S N') (Add (S I') (S R))) {
              Pair (X) (Y) =>
                Pair(X, IdCongr Nat Nat (λ (Nn : Nat). S Nn) N' (Add I' (S X)) Y) } } } }
def ModDecTy : Term := prog{
  Π (I : Nat) → Π (N : Nat) → Le (S I) N → Σ (R : Nat). Id Nat N (Add I (S R)) }

/-! ## The hashmap flagship (`docs/13-hashmap-flagship.md`) — vocabulary

    **Option** — the `Σ (Bool)` encoding, ported from `hm-probe-opt` (verbatim, modulo
    the Σ-dot migration and specialising the payload to `Nat`, since values are `Nat`
    in v1). `OptP` is a `boolRec` into `Type`; `Opt T` pairs a runtime tag with an
    erased-or-not payload of that type (the tag is lowercase, so the match on it is a
    genuine runtime branch). `OptElim` is the eliminator every `Opt`-typed PURE
    function below is built from — a return-type-generic fold, Lean's `Option.elim`,
    needed because a pure function may not use the imperative `match`. -/

def OptP : Term := prog{
  λ (B : Bool). λ (T : Type). elim B return (λ (Bm : Bool). Type) {
    True => T, False => Unit } }

def Opt : Term := prog{ λ (T : Type). Σ (b : Bool). OptP b T }

/-- `Some : Nat → Opt Nat`. -/
def Some : Term := prog{ λ (V : Nat). Pair(True, V) }
/-- `None : Opt Nat`. -/
def None : Term := prog{ Pair(False, unit) }

def OptElim : Term := prog{
  λ (O : Σ (b : Bool). OptP b Nat). λ (R : Type). λ (Dn : R). λ (Ds : Nat → R).
    elim O return (λ (Oz : Σ (b : Bool). OptP b Nat). R) {
      Pair (B) (P) => elim B return (λ (Bz : Bool). OptP Bz Nat → R) {
        True => λ (V : Nat). Ds V,
        False => λ (U : Unit). Dn
      } P
    } }

/-! ## Entries and buckets — `List (Σ k. Nat)`, the Aeneas hashmap's own shape

    `LenE`/`FindL` are hand-built `listRec` spines rather than the `elim` sugar,
    because `Uni.elabUElim`'s Nil/Cons branch hard-codes the element type as `Nat`
    (`hm-probe-opt` §"the cause") — the kernel's `listRec` is fully generic in the
    element type; only the surface sugar is monomorphic. -/

def Entry : Term := prog{ Σ (k : Nat). Nat }
def Bucket : Term := prog{ List Entry }

/-- `LenE b` — the bucket's entry count. `Std.lenFn`'s transfer at this payload. -/
def LenE : Term := prog{
  λ (L : Bucket).
    listRec Entry (λ (Lm : Bucket). Nat) Z
      (λ (H : Entry). λ (T : Bucket). λ (Ih : Nat). S(Ih))
      L }

/-- `FindL q b` — the first entry in `b` whose key is `q`, `None` if there is none.
    Head-to-tail scan, matching `insert_in_list`'s own walk order (and therefore
    `SetL`'s, §next section): the FIRST occurrence wins, which is also the only one
    that can exist once `SetL`'s own no-duplicate-key invariant is established. -/
def FindL : Term := prog{
  λ (Q : Nat). λ (B : Bucket).
    listRec Entry (λ (Bm : Bucket). Σ (b : Bool). OptP b Nat) None
      (λ (E : Entry). λ (T : Bucket). λ (Rec : Σ (b : Bool). OptP b Nat).
        elim E return (λ (Em : Σ (k : Nat). Nat). Σ (b : Bool). OptP b Nat) {
          Pair (K2) (V2) =>
            elim (Eqb Q K2) return (λ (Bz : Bool). Σ (b : Bool). OptP b Nat) {
              True => Some V2, False => Rec } })
      B }

/-! ## The slot array — well-hashedness, entry counting, and the whole-map lookup

    `AllHashedA`/`TotalLenA` are `SortedA`'s shape (`hm-probe-arrays`'s `AllShortA`,
    generalised from a length bound to a per-slot hash equation): an `arrRec` fold into
    `Type`/`Nat` over the cons view, with the running absolute slot index threaded as an
    explicit `Nat` argument — `SplitAL`'s "M22 bounded-Π" idiom, since the predicate
    needs a POSITION and `arrRec`'s own peeling only ever hands back a REMAINING-LENGTH
    co-index. -/

/-- `AllKeysEq cap i b` — every entry in bucket `b` hashes to slot `i`. -/
def AllKeysEq : Term := prog{
  λ (Cap : Nat). λ (I : Nat). λ (B : Bucket).
    listRec Entry (λ (Bm : Bucket). Type) Unit
      (λ (E : Entry). λ (T : Bucket). λ (Ih : Type).
        elim E return (λ (Em : Σ (k : Nat). Nat). Type) {
          Pair (K2) (V2) => Σ (Heq : Id Nat (Mod K2 Cap) I). Ih
        })
      B }

/-- `AllHashedA cap n a i0` — every bucket of the `n`-slot sub-array `a` is well-hashed,
    reading `a`'s own zeroth slot as ABSOLUTE index `i0` of the full `cap`-array. Used
    at `i0 = Z, n = cap` for the packed invariant, and at an arbitrary `i0` for the
    carve-crossing lemmas below (the `SplitACatI0`/`SplitACatE1` shape). -/
def AllHashedA : Term := prog{
  λ (Cap : Nat). λ (N : Nat). λ (A : Array N Bucket). λ (I0 : Nat).
    arrRec Bucket (λ (M : Nat). λ (Bz : Array M Bucket). Π (I : Nat) → Type)
      (λ (I : Nat). Unit)
      (λ (K : Nat). λ (H : Bucket). λ (T : Array K Bucket). λ (Ih : Π (I : Nat) → Type).
        λ (I : Nat). Σ (Hh : AllKeysEq Cap I H). Ih (S I))
      N A I0 }

/-- `TotalLenA n a` — the entry count across every bucket of `a`. `CountA`'s shape,
    with `Eqb`-branching replaced by an unconditional `Add`. -/
def TotalLenA : Term := prog{
  λ (N : Nat). λ (A : Array N Bucket).
    arrRec Bucket (λ (M : Nat). λ (Bz : Array M Bucket). Nat) Z
      (λ (K : Nat). λ (H : Bucket). λ (T : Array K Bucket). λ (Ih : Nat). Add (LenE H) Ih)
      N A }

/-- `TotalLenA` distributes over `arrCat` — `CountArrCat`'s shape, simpler since there
    is no `Eqb` branch to carry across the induction (every bucket contributes
    unconditionally, so the step is one `AddAssoc` rather than a `boolRec` congruence). -/
def TotalLenACat : Term := prog{
  λ (M : Nat). λ (A : Array M Bucket). λ (Kk : Nat). λ (B : Array Kk Bucket).
    arrRec Bucket (λ (Mz : Nat). λ (Az : Array Mz Bucket).
        Id Nat (TotalLenA (Add Mz Kk) (arrCat Mz Kk Az B)) (Add (TotalLenA Mz Az) (TotalLenA Kk B)))
      Refl
      (λ (K2 : Nat). λ (H : Bucket). λ (T : Array K2 Bucket).
        λ (Ih : Id Nat (TotalLenA (Add K2 Kk) (arrCat K2 Kk T B))
                       (Add (TotalLenA K2 T) (TotalLenA Kk B))).
          IdTrans Nat
            (Add (LenE H) (TotalLenA (Add K2 Kk) (arrCat K2 Kk T B)))
            (Add (LenE H) (Add (TotalLenA K2 T) (TotalLenA Kk B)))
            (Add (Add (LenE H) (TotalLenA K2 T)) (TotalLenA Kk B))
            (IdCongr Nat Nat (λ (X : Nat). Add (LenE H) X)
              (TotalLenA (Add K2 Kk) (arrCat K2 Kk T B))
              (Add (TotalLenA K2 T) (TotalLenA Kk B)) Ih)
            (IdSym Nat (Add (Add (LenE H) (TotalLenA K2 T)) (TotalLenA Kk B))
              (Add (LenE H) (Add (TotalLenA K2 T) (TotalLenA Kk B)))
              (AddAssoc (LenE H) (TotalLenA K2 T) (TotalLenA Kk B))))
      M A }

/-- Associativity of the "first hit wins" combine, at the ONE instantiation the
    whole-map fold needs (`F = Some`). Both leaves close by `Refl` once `O1`'s tag is
    concrete — `CountArrCat`'s `boolRec`-phantom trick, one level deeper: fixing the
    Bool tag alone is enough to compute both sides to the SAME term, regardless of what
    `O2`/`D` are, so neither is ever cased on. -/
def OptElimAssoc : Term := prog{
  λ (O1 : Opt Nat). λ (O2 : Opt Nat). λ (D : Opt Nat).
    elim O1 return (λ (Oz : Σ (b : Bool). OptP b Nat).
        Id (Opt Nat) (OptElim Oz (Opt Nat) (OptElim O2 (Opt Nat) D Some) Some)
                     (OptElim (OptElim Oz (Opt Nat) O2 Some) (Opt Nat) D Some)) {
      Pair (B1) (P1) =>
        elim B1 return (λ (Bz : Bool). Π (Pz : OptP Bz Nat) →
            Id (Opt Nat) (OptElim Pair(Bz, Pz) (Opt Nat) (OptElim O2 (Opt Nat) D Some) Some)
                         (OptElim (OptElim Pair(Bz, Pz) (Opt Nat) O2 Some) (Opt Nat) D Some)) {
          True => λ (V : Nat). Refl,
          False => λ (U : Unit). Refl
        } P1
    } }

/-- `FindArrA q n a` — scan every bucket of `a` head-to-tail, first hit wins. Provably
    the same answer as looking only in slot `Mod q cap` GIVEN well-hashedness (every
    other bucket misses by construction), but stated as a fold because a fold is what
    crosses `arrCat` for free (`CountArrCat`'s pattern) — `aget` at a SYMBOLIC index
    does not reduce at all (`Pure.lean`'s `aget` rule requires a CONCRETE index), so an
    `aget`-based spelling would need a carve-crossing lemma family this fold sidesteps
    entirely. -/
def FindArrA : Term := prog{
  λ (Q : Nat). λ (N : Nat). λ (A : Array N Bucket).
    arrRec Bucket (λ (M : Nat). λ (Bz : Array M Bucket). Σ (b : Bool). OptP b Nat) None
      (λ (K : Nat). λ (H : Bucket). λ (T : Array K Bucket). λ (Ih : Σ (b : Bool). OptP b Nat).
        OptElim (FindL Q H) (Opt Nat) Ih Some)
      N A }

/-- `FindArrA` crosses `arrCat`: `CountArrCat`'s shape exactly, with the `Eqb`-keyed
    congruence swapped for `OptElimAssoc`. -/
def FindArrACat : Term := prog{
  λ (Q : Nat). λ (M : Nat). λ (A : Array M Bucket). λ (Kk : Nat). λ (B : Array Kk Bucket).
    arrRec Bucket (λ (Mz : Nat). λ (Az : Array Mz Bucket).
        Id (Opt Nat) (FindArrA Q (Add Mz Kk) (arrCat Mz Kk Az B))
                     (OptElim (FindArrA Q Mz Az) (Opt Nat) (FindArrA Q Kk B) Some))
      Refl
      (λ (K2 : Nat). λ (H : Bucket). λ (T : Array K2 Bucket).
        λ (Ih : Id (Opt Nat) (FindArrA Q (Add K2 Kk) (arrCat K2 Kk T B))
                             (OptElim (FindArrA Q K2 T) (Opt Nat) (FindArrA Q Kk B) Some)).
          IdTrans (Opt Nat)
            (OptElim (FindL Q H) (Opt Nat) (FindArrA Q (Add K2 Kk) (arrCat K2 Kk T B)) Some)
            (OptElim (FindL Q H) (Opt Nat) (OptElim (FindArrA Q K2 T) (Opt Nat) (FindArrA Q Kk B) Some) Some)
            (OptElim (OptElim (FindL Q H) (Opt Nat) (FindArrA Q K2 T) Some) (Opt Nat) (FindArrA Q Kk B) Some)
            (IdCongr (Opt Nat) (Opt Nat) (λ (X : Σ (b : Bool). OptP b Nat).
                OptElim (FindL Q H) (Opt Nat) X Some)
              (FindArrA Q (Add K2 Kk) (arrCat K2 Kk T B))
              (OptElim (FindArrA Q K2 T) (Opt Nat) (FindArrA Q Kk B) Some) Ih)
            (OptElimAssoc (FindL Q H) (FindArrA Q K2 T) (FindArrA Q Kk B)))
      M A }

/-! ## The packed `HashMap` and its spec functions

    `docs/13-hashmap-flagship.md`'s fixed container: `cap`/`load`/`n` are runtime
    `Nat`s (Copy, so a lowercase binder is the honest one — they are small the way a
    `usize` field is), `slots` is the real array, and `HMInv` rides along erased —
    `Σ0` marks the TAIL of the last pair comptime, so a `HashMap` value cannot exist
    broken. The four clauses: `Le 1 cap`; every slot's bucket is well-hashed
    (`AllHashedA`); `n` is the total entry count (`TotalLenA`), which is how a caller
    bounds any ONE bucket's length without reaching into buckets (any addend is ≤ the
    sum, `LeAdd`/`LeAddL`); `load` is the 4/5 threshold ledger for `cap`. -/

def HMInv : Term := prog{
  λ (Cap : Nat). λ (Load : Nat). λ (N : Nat). λ (Slots : Array Cap Bucket).
    Le (S Z) Cap × AllHashedA Cap Cap Slots Z × Id Nat N (TotalLenA Cap Slots) ×
      Id Nat Load (Div (Mul Cap 4) 5) }

def HashMapT : Term := prog{
  Σ (cap : Nat). Σ (load : Nat). Σ (n : Nat). Σ0 (slots : Array cap Bucket).
    HMInv cap load n slots }

/-- `FindHM q hm` — the pointwise spec of "what does the map say `q` maps to".
    Formulated as the WHOLE-MAP fold `FindArrA`, not an `aget`-at-`Mod q cap` direct
    index: see `FindArrA`'s own note — an `aget`-based spelling would need a carve
    crossing lemma family this fold sidesteps, and the two are provably the same
    answer given `HMInv`'s well-hashedness (at most one bucket can ever match). -/
def FindHM : Term := prog{
  λ (Q : Nat). λ (Hm : Σ (cap : Nat). Σ (load : Nat). Σ (n : Nat).
      Σ0 (slots : Array cap Bucket). HMInv cap load n slots).
    elim Hm return (λ (H0 : Σ (cap : Nat). Σ (load : Nat). Σ (n : Nat).
        Σ0 (slots : Array cap Bucket). HMInv cap load n slots). Σ (b : Bool). OptP b Nat) {
      Pair (Cap) (Rest1) =>
        elim Rest1 return (λ (R1 : Σ (load : Nat). Σ (n : Nat). Σ0 (slots : Array Cap Bucket).
            HMInv Cap load n slots). Σ (b : Bool). OptP b Nat) {
          Pair (Load) (Rest2) =>
            elim Rest2 return (λ (R2 : Σ (n : Nat). Σ0 (slots : Array Cap Bucket).
                HMInv Cap Load n slots). Σ (b : Bool). OptP b Nat) {
              Pair (N0) (Rest3) =>
                elim Rest3 return (λ (R3 : Σ0 (slots : Array Cap Bucket). HMInv Cap Load N0 slots).
                    Σ (b : Bool). OptP b Nat) {
                  Pair (Slots) (Hinv) => FindArrA Q Cap Slots
                }
            }
        }
    } }

/-- `SizeHM hm` — the entry count. The invariant makes this a plain projection: `n`
    already IS the total count (`HMInv`'s counting clause), so there is nothing to
    compute — the packed representation's whole point, arriving at the first spec
    function that gets to cash it in. -/
def SizeHM : Term := prog{
  λ (Hm : Σ (cap : Nat). Σ (load : Nat). Σ (n : Nat). Σ0 (slots : Array cap Bucket).
      HMInv cap load n slots).
    elim Hm return (λ (H0 : Σ (cap : Nat). Σ (load : Nat). Σ (n : Nat).
        Σ0 (slots : Array cap Bucket). HMInv cap load n slots). Nat) {
      Pair (Cap) (Rest1) =>
        elim Rest1 return (λ (R1 : Σ (load : Nat). Σ (n : Nat). Σ0 (slots : Array Cap Bucket).
            HMInv Cap load n slots). Nat) {
          Pair (Load) (Rest2) =>
            elim Rest2 return (λ (R2 : Σ (n : Nat). Σ0 (slots : Array Cap Bucket).
                HMInv Cap Load n slots). Nat) {
              Pair (N0) (Rest3) => N0
            }
        }
    } }

/-- `FindIns q key v hm` — the model update Insert's find-equation is checked against:
    `Some v` at `key`, the old answer everywhere else. -/
def FindIns : Term := prog{
  λ (Q : Nat). λ (Key : Nat). λ (V : Nat). λ (Hm : Σ (cap : Nat). Σ (load : Nat). Σ (n : Nat).
      Σ0 (slots : Array cap Bucket). HMInv cap load n slots).
    elim (Eqb Q Key) return (λ (Bz : Bool). Σ (b : Bool). OptP b Nat) {
      True => Some V, False => FindHM Q Hm } }

/-- `FindRem q key hm` — Remove's model update: `None` at `key`, the old answer
    everywhere else. -/
def FindRem : Term := prog{
  λ (Q : Nat). λ (Key : Nat). λ (Hm : Σ (cap : Nat). Σ (load : Nat). Σ (n : Nat).
      Σ0 (slots : Array cap Bucket). HMInv cap load n slots).
    elim (Eqb Q Key) return (λ (Bz : Bool). Σ (b : Bool). OptP b Nat) {
      True => None, False => FindHM Q Hm } }

/-! ## `New` — filling a fresh slot array, and what it trivially satisfies

    `MkFillFn` is `hm-probe-opt`'s `MkSlotsFn`, generalised to the `Bucket` payload —
    an `acons` spine, working equally as a comptime builder and (below) inside a `fn`.
    Its three companion lemmas are each an induction MATCHING `MkFillFn`'s own
    recursion: at every step the goal and the induction hypothesis turn out to be
    DEFINITIONALLY the same statement (`Nil` is vacuously well-hashed at any index,
    contributes `Z` to `TotalLenA`, and misses every `FindL` query), so each step's
    proof is the induction hypothesis ITSELF — no transport, no congruence lemma. -/

def MkFillFn : Term := prog{
  λ (N : Nat). elim N return (λ (Nm : Nat). Array Nm Bucket) {
    Z => Arr(), S (M) Rec => acons M Nil Rec } }

def MkFillAllHashed : Term := prog{
  λ (Cap : Nat). λ (N : Nat).
    elim N return (λ (Nz : Nat). Π (I : Nat) → AllHashedA Cap Nz (MkFillFn Nz) I) {
      Z => λ (I : Nat). unit,
      S (N') Ih => λ (I : Nat). Pair(unit, Ih (S I))
    } }

def MkFillTotalLen : Term := prog{
  λ (N : Nat).
    elim N return (λ (Nz : Nat). Id Nat Z (TotalLenA Nz (MkFillFn Nz))) {
      Z => Refl, S (N') Ih => Ih
    } }

def MkFillFind : Term := prog{
  λ (N : Nat).
    elim N return (λ (Nz : Nat). Π (Q : Nat) → Id (Opt Nat) (FindArrA Q Nz (MkFillFn Nz)) None) {
      Z => λ (Q : Nat). Refl,
      S (N') Ih => λ (Q : Nat). Ih Q
    } }

/-! ## `insert_in_list` — the bucket-level walk, and the arithmetic it needs

    `EqbTrueEq`/`EqbSymm` are decidable-equality soundness and symmetry, by the
    `Znots`-style discrimination and a plain double induction respectively; neither
    exists yet (`EqbRefl` — reflexivity — already does). `FindInsL`/`CondBump` are the
    bucket-level model update and the "bump the count iff absent" ledger the size
    conjunct is stated against; `CondBumpSucc` is the one fact gluing a bucket's own
    accounting to its caller's (`S` commutes with `CondBump` in its SECOND argument,
    regardless of the first) — `OptElimAssoc`'s trick again: both cases close once the
    `Opt`'s tag alone is fixed. -/

def FalseNotTrue : Term := prog{
  λ (H : Id Bool False True).
    j Bool False (λ (Y : Bool). λ (Hy : Id Bool False Y).
        elim Y return (λ (Yy : Bool). Type) { True => Bot, False => Unit })
      unit True H }
def FalseNotTrueTy : Term := prog{ Id Bool False True → Bot }

def EqbTrueEq : Term := prog{
  λ (A : Nat).
    elim A return (λ (Az : Nat). Π (B : Nat) → Id Bool (Eqb Az B) True → Id Nat Az B) {
      Z => λ (B : Nat).
        elim B return (λ (Bz : Nat). Id Bool (Eqb Z Bz) True → Id Nat Z Bz) {
          Z => λ (H : Id Bool True True). Refl,
          S (B') Rb => λ (H : Id Bool False True). botElim (Id Nat Z (S B')) (FalseNotTrue H)
        },
      S (A') Ih => λ (B : Nat).
        elim B return (λ (Bz : Nat). Id Bool (Eqb (S A') Bz) True → Id Nat (S A') Bz) {
          Z => λ (H : Id Bool False True). botElim (Id Nat (S A') Z) (FalseNotTrue H),
          S (B') Rb => λ (H : Id Bool (Eqb A' B') True).
            IdCongr Nat Nat (λ (X : Nat). S X) A' B' (Ih B' H)
        }
    } }
def EqbTrueEqTy : Term := prog{ Π (A : Nat) → Π (B : Nat) → Id Bool (Eqb A B) True → Id Nat A B }

def EqbSymm : Term := prog{
  λ (A : Nat).
    elim A return (λ (Az : Nat). Π (B : Nat) → Id Bool (Eqb Az B) (Eqb B Az)) {
      Z => λ (B : Nat).
        elim B return (λ (Bz : Nat). Id Bool (Eqb Z Bz) (Eqb Bz Z)) { Z => Refl, S (B') Rb => Refl },
      S (A') Ih => λ (B : Nat).
        elim B return (λ (Bz : Nat). Id Bool (Eqb (S A') Bz) (Eqb Bz (S A'))) {
          Z => Refl, S (B') Rb => Ih B'
        }
    } }
def EqbSymmTy : Term := prog{ Π (A : Nat) → Π (B : Nat) → Id Bool (Eqb A B) (Eqb B A) }

/-- `FindInsL q key v b` — the bucket-level model update: `Some v` at `key`, the old
    answer everywhere else. `InsertInList`'s own pointwise return equation is checked
    against this. -/
def FindInsL : Term := prog{
  λ (Q : Nat). λ (Key : Nat). λ (V : Nat). λ (B : Bucket).
    elim (Eqb Q Key) return (λ (Bz : Bool). Σ (b : Bool). OptP b Nat) {
      True => Some V, False => FindL Q B } }

/-- `CondBump o n` — `n` bumped iff `o` (the OLD lookup) was `None`. -/
def CondBump : Term := prog{
  λ (O : Opt Nat). λ (N : Nat). OptElim O Nat (S N) (λ (V : Nat). N) }

def CondBumpSucc : Term := prog{
  λ (O : Opt Nat). λ (N : Nat).
    elim O return (λ (Oz : Σ (b : Bool). OptP b Nat).
        Id Nat (S (CondBump Oz N)) (CondBump Oz (S N))) {
      Pair (B1) (P1) =>
        elim B1 return (λ (Bz : Bool). Π (Pz : OptP Bz Nat) →
            Id Nat (S (CondBump Pair(Bz, Pz) N)) (CondBump Pair(Bz, Pz) (S N))) {
          True => λ (V : Nat). Refl,
          False => λ (U : Unit). Refl
        } P1
    } }
def CondBumpSuccTy : Term := prog{
  Π (O : Opt Nat) → Π (N : Nat) → Id Nat (S (CondBump O N)) (CondBump O (S N)) }

/-! ## `BoolRw` and the `boolRec`-collapse pair

    `BoolRw` is `NatRw` at `Bool` (the `j`-based rewrite, same shape, different type
    index) — needed because `InsertInList`'s own proof (next) has to REWRITE a STUCK
    `Eqb`-headed `boolRec` using a hypothesis about that Bool, not just case-split on
    it fresh. `BoolRecTrue`/`BoolRecFalse` specialise it to the ONE shape every such
    rewrite in this file needs: collapsing `boolRec (Opt-motive) T F X` once `X`'s
    value is known. -/

def BoolRw : Term := prog{
  λ (P : Bool → Type). λ (X : Bool). λ (Y : Bool). λ (H : Id Bool X Y). λ (Px : P X).
    j Bool X (λ (Y' : Bool). λ (Hy : Id Bool X Y'). P Y') Px Y H }
def BoolRwTy : Term := prog{
  Π (P : Bool → Type) → Π (X : Bool) → Π (Y : Bool) → Id Bool X Y → P X → P Y }

def BoolRecTrue : Term := prog{
  λ (T : Opt Nat). λ (F : Opt Nat). λ (X : Bool). λ (H : Id Bool X True).
    BoolRw (λ (Bz : Bool). Id (Opt Nat) (boolRec (λ (W : Bool). Σ (b : Bool). OptP b Nat) T F Bz) T)
      True X (IdSym Bool X True H) Refl }
def BoolRecTrueTy : Term := prog{
  Π (T : Opt Nat) → Π (F : Opt Nat) → Π (X : Bool) → Id Bool X True →
    Id (Opt Nat) (boolRec (λ (W : Bool). Σ (b : Bool). OptP b Nat) T F X) T }

def BoolRecFalse : Term := prog{
  λ (T : Opt Nat). λ (F : Opt Nat). λ (X : Bool). λ (H : Id Bool X False).
    BoolRw (λ (Bz : Bool). Id (Opt Nat) (boolRec (λ (W : Bool). Σ (b : Bool). OptP b Nat) T F Bz) F)
      False X (IdSym Bool X False H) Refl }
def BoolRecFalseTy : Term := prog{
  Π (T : Opt Nat) → Π (F : Opt Nat) → Π (X : Bool) → Id Bool X False →
    Id (Opt Nat) (boolRec (λ (W : Bool). Σ (b : Bool). OptP b Nat) T F X) F }

/-! ## `AllKeysEq` head/tail — `SortedHeadA`/`SortedTailA`'s shape

    A COMPTIME (capital) value cannot be the scrutinee of an imperative destructuring
    `let`/`match` (§6: erased, never scrutinised at runtime) — `InsertInList`'s own
    proof needs to split its `HallKeys : AllKeysEq Cap I (*b)` parameter into "this
    entry's own hash fact" and "the tail's own witness" WHILE ALSO performing real
    mutations in the same branch, which a pure `elim`'s arm cannot do either. These
    two projectors sidestep both: ordinary function calls, callable from anywhere. -/

def AllKeysEqHead : Term := prog{
  λ (Cap : Nat). λ (I : Nat). λ (K : Nat). λ (T : Bucket).
    λ (S0 : Σ (Heq : Id Nat (Mod K Cap) I). AllKeysEq Cap I T).
      elim S0 return (λ (Q : Σ (Heq : Id Nat (Mod K Cap) I). AllKeysEq Cap I T).
          Id Nat (Mod K Cap) I) {
        Pair (X) (Y) => X } }
def AllKeysEqHeadTy : Term := prog{
  Π (Cap : Nat) → Π (I : Nat) → Π (K : Nat) → Π (T : Bucket) →
    (Σ (Heq : Id Nat (Mod K Cap) I). AllKeysEq Cap I T) → Id Nat (Mod K Cap) I }

def AllKeysEqTail : Term := prog{
  λ (Cap : Nat). λ (I : Nat). λ (K : Nat). λ (T : Bucket).
    λ (S0 : Σ (Heq : Id Nat (Mod K Cap) I). AllKeysEq Cap I T).
      elim S0 return (λ (Q : Σ (Heq : Id Nat (Mod K Cap) I). AllKeysEq Cap I T).
          AllKeysEq Cap I T) {
        Pair (X) (Y) => Y } }
def AllKeysEqTailTy : Term := prog{
  Π (Cap : Nat) → Π (I : Nat) → Π (K : Nat) → Π (T : Bucket) →
    (Σ (Heq : Id Nat (Mod K Cap) I). AllKeysEq Cap I T) → AllKeysEq Cap I T }

/-- Generic `Σ0` projectors — needed once a `let Pair(_, Pair(_, _)) = call;` pattern
    goes two levels deep through nested `Σ0`s: the surface's nested-pattern desugaring
    mis-cases its own auto-generated intermediate binder there (measured — the SAME
    failure survives swapping `×` for a second `Σ0`, so it is about the NESTING depth,
    not the connective), and a comptime-bound name cannot itself be re-matched (§6).
    An ordinary function call sidesteps both. -/
def Sig0PairFst : Term := prog{
  λ (A : Type). λ (B : Type). λ (S0 : Σ0 (x : A). B).
    elim S0 return (λ (Q : Σ0 (x : A). B). A) { Pair (X) (Y) => X } }
def Sig0PairFstTy : Term := prog{
  Π (A : Type) → Π (B : Type) → (Σ0 (x : A). B) → A }

def Sig0PairSnd : Term := prog{
  λ (A : Type). λ (B : Type). λ (S0 : Σ0 (x : A). B).
    elim S0 return (λ (Q : Σ0 (x : A). B). B) { Pair (X) (Y) => Y } }
def Sig0PairSndTy : Term := prog{
  Π (A : Type) → Π (B : Type) → (Σ0 (x : A). B) → B }

/-- `AllHashedA` crosses `arrCat` — `SplitACatI0`'s shape (induction on the LEFT
    array, peeling its own `AllHashedA` hypothesis via the SAME `arrRec`), simpler
    since there is no pivot/`UbA` side-condition, just the absolute index shifting by
    one per cons step. `I0` is generalised INSIDE the `arrRec` motive (the M22
    bounded-Pi idiom `AllHashedA` itself uses for its own index) because the
    recursive step needs it instantiated at `S I0`, not the caller's original `I0`. -/
def AllHashedACat : Term := prog{
  λ (Cap : Nat). λ (K : Nat). λ (L : Array K Bucket). λ (M : Nat). λ (W : Array M Bucket).
    arrRec Bucket (λ (Kz : Nat). λ (Lz : Array Kz Bucket). Π (I0 : Nat) →
        AllHashedA Cap Kz Lz I0 → AllHashedA Cap M W (Add I0 Kz) →
          AllHashedA Cap (Add Kz M) (arrCat Kz M Lz W) I0)
      (λ (I0 : Nat). λ (Hl : Unit). λ (Hw : AllHashedA Cap M W (Add I0 Z)).
        NatRw (λ (X : Nat). AllHashedA Cap M W X) (Add I0 Z) I0 (AddZero I0) Hw)
      (λ (K2 : Nat). λ (Hh : Bucket). λ (T : Array K2 Bucket).
        λ (Ih : Π (I0 : Nat) → AllHashedA Cap K2 T I0 → AllHashedA Cap M W (Add I0 K2) →
                  AllHashedA Cap (Add K2 M) (arrCat K2 M T W) I0).
        λ (I0 : Nat).
        λ (Hl : Σ (Hk : AllKeysEq Cap I0 Hh). AllHashedA Cap K2 T (S I0)).
        λ (Hw : AllHashedA Cap M W (Add I0 (S K2))).
          elim Hl return (λ (Q : Σ (Hk : AllKeysEq Cap I0 Hh). AllHashedA Cap K2 T (S I0)).
              Σ (Hk2 : AllKeysEq Cap I0 Hh). AllHashedA Cap (Add K2 M) (arrCat K2 M T W) (S I0)) {
            Pair (HkVal) (HtVal) =>
              Pair(HkVal, Ih (S I0) HtVal (NatRw (λ (X : Nat). AllHashedA Cap M W X)
                (Add I0 (S K2)) (Add (S I0) K2) (AddSucc I0 K2) Hw))
          })
      K L }
def AllHashedACatTy : Term := prog{
  Π (Cap : Nat) → Π (K : Nat) → Π (L : Array K Bucket) → Π (M : Nat) → Π (W : Array M Bucket) →
  Π (I0 : Nat) →
    AllHashedA Cap K L I0 → AllHashedA Cap M W (Add I0 K) →
      AllHashedA Cap (Add K M) (arrCat K M L W) I0 }

/-! ## `HMInv`'s four projectors

    `HMInv` is a non-dependent `×`-chain (`Le 1 cap × AllHashedA … × Id … × Id …`); the
    array-level `Insert` needs to pull ONE clause out of a `HashMap`'s packed (hence
    comptime, hence un-`match`able) invariant witness at a time. Each is one or two
    `elim`s peeling the chain from the front. -/

def HMInvCapPos : Term := prog{
  λ (Cap : Nat). λ (Load : Nat). λ (N : Nat). λ (Slots : Array Cap Bucket).
  λ (H : Le (S Z) Cap × AllHashedA Cap Cap Slots Z × Id Nat N (TotalLenA Cap Slots) ×
         Id Nat Load (Div (Mul Cap 4) 5)).
    elim H return (λ (Q : Σ (J : Le (S Z) Cap). AllHashedA Cap Cap Slots Z ×
        Id Nat N (TotalLenA Cap Slots) × Id Nat Load (Div (Mul Cap 4) 5)). Le (S Z) Cap) {
      Pair (X) (Y) => X } }
def HMInvCapPosTy : Term := prog{
  Π (Cap : Nat) → Π (Load : Nat) → Π (N : Nat) → Π (Slots : Array Cap Bucket) →
    HMInv Cap Load N Slots → Le (S Z) Cap }

def HMInvHashed : Term := prog{
  λ (Cap : Nat). λ (Load : Nat). λ (N : Nat). λ (Slots : Array Cap Bucket).
  λ (H : Le (S Z) Cap × AllHashedA Cap Cap Slots Z × Id Nat N (TotalLenA Cap Slots) ×
         Id Nat Load (Div (Mul Cap 4) 5)).
    elim H return (λ (Q : Σ (J : Le (S Z) Cap). AllHashedA Cap Cap Slots Z ×
        Id Nat N (TotalLenA Cap Slots) × Id Nat Load (Div (Mul Cap 4) 5)).
        AllHashedA Cap Cap Slots Z) {
      Pair (X) (Y) =>
        elim Y return (λ (Q2 : Σ (J2 : AllHashedA Cap Cap Slots Z). Id Nat N (TotalLenA Cap Slots) ×
            Id Nat Load (Div (Mul Cap 4) 5)). AllHashedA Cap Cap Slots Z) {
          Pair (X2) (Y2) => X2 } } }
def HMInvHashedTy : Term := prog{
  Π (Cap : Nat) → Π (Load : Nat) → Π (N : Nat) → Π (Slots : Array Cap Bucket) →
    HMInv Cap Load N Slots → AllHashedA Cap Cap Slots Z }

def HMInvCount : Term := prog{
  λ (Cap : Nat). λ (Load : Nat). λ (N : Nat). λ (Slots : Array Cap Bucket).
  λ (H : Le (S Z) Cap × AllHashedA Cap Cap Slots Z × Id Nat N (TotalLenA Cap Slots) ×
         Id Nat Load (Div (Mul Cap 4) 5)).
    elim H return (λ (Q : Σ (J : Le (S Z) Cap). AllHashedA Cap Cap Slots Z ×
        Id Nat N (TotalLenA Cap Slots) × Id Nat Load (Div (Mul Cap 4) 5)).
        Id Nat N (TotalLenA Cap Slots)) {
      Pair (X) (Y) =>
        elim Y return (λ (Q2 : Σ (J2 : AllHashedA Cap Cap Slots Z). Id Nat N (TotalLenA Cap Slots) ×
            Id Nat Load (Div (Mul Cap 4) 5)). Id Nat N (TotalLenA Cap Slots)) {
          Pair (X2) (Y2) =>
            elim Y2 return (λ (Q3 : Σ (J3 : Id Nat N (TotalLenA Cap Slots)).
                Id Nat Load (Div (Mul Cap 4) 5)). Id Nat N (TotalLenA Cap Slots)) {
              Pair (X3) (Y3) => X3 } } } }
def HMInvCountTy : Term := prog{
  Π (Cap : Nat) → Π (Load : Nat) → Π (N : Nat) → Π (Slots : Array Cap Bucket) →
    HMInv Cap Load N Slots → Id Nat N (TotalLenA Cap Slots) }

def HMInvLoad : Term := prog{
  λ (Cap : Nat). λ (Load : Nat). λ (N : Nat). λ (Slots : Array Cap Bucket).
  λ (H : Le (S Z) Cap × AllHashedA Cap Cap Slots Z × Id Nat N (TotalLenA Cap Slots) ×
         Id Nat Load (Div (Mul Cap 4) 5)).
    elim H return (λ (Q : Σ (J : Le (S Z) Cap). AllHashedA Cap Cap Slots Z ×
        Id Nat N (TotalLenA Cap Slots) × Id Nat Load (Div (Mul Cap 4) 5)).
        Id Nat Load (Div (Mul Cap 4) 5)) {
      Pair (X) (Y) =>
        elim Y return (λ (Q2 : Σ (J2 : AllHashedA Cap Cap Slots Z). Id Nat N (TotalLenA Cap Slots) ×
            Id Nat Load (Div (Mul Cap 4) 5)). Id Nat Load (Div (Mul Cap 4) 5)) {
          Pair (X2) (Y2) =>
            elim Y2 return (λ (Q3 : Σ (J3 : Id Nat N (TotalLenA Cap Slots)).
                Id Nat Load (Div (Mul Cap 4) 5)). Id Nat Load (Div (Mul Cap 4) 5)) {
              Pair (X3) (Y3) => Y3 } } } }
def HMInvLoadTy : Term := prog{
  Π (Cap : Nat) → Π (Load : Nat) → Π (N : Nat) → Π (Slots : Array Cap Bucket) →
    HMInv Cap Load N Slots → Id Nat Load (Div (Mul Cap 4) 5) }

/-- The converse of `AllHashedACat` — `SplitACatE1`'s shape (induction on the LEFT
    array, peeling the WHOLE-ARRAY hypothesis at each cons step): given the WHOLE
    carved-and-rebuilt array is well-hashed, recover well-hashedness of the untouched
    prefix and suffix separately. The array-level `Insert` needs this to justify that
    `lo`/`hi` (never written) still satisfy `AllHashedA` after the carve, before it
    replaces the cell in between and re-`AllHashedACat`s the three pieces back
    together. -/
def AllHashedACatSplit : Term := prog{
  λ (Cap : Nat). λ (K : Nat). λ (L : Array K Bucket). λ (M : Nat). λ (W : Array M Bucket).
    arrRec Bucket (λ (Kz : Nat). λ (Lz : Array Kz Bucket). Π (I0 : Nat) →
        AllHashedA Cap (Add Kz M) (arrCat Kz M Lz W) I0 →
          Σ (Hl : AllHashedA Cap Kz Lz I0). AllHashedA Cap M W (Add I0 Kz))
      (λ (I0 : Nat). λ (H : AllHashedA Cap M W I0).
        Pair(unit, NatRw (λ (X : Nat). AllHashedA Cap M W X) I0 (Add I0 Z)
          (IdSym Nat (Add I0 Z) I0 (AddZero I0)) H))
      (λ (K2 : Nat). λ (Hh : Bucket). λ (T : Array K2 Bucket).
        λ (Ih : Π (I0 : Nat) → AllHashedA Cap (Add K2 M) (arrCat K2 M T W) I0 →
                  Σ (Hl : AllHashedA Cap K2 T I0). AllHashedA Cap M W (Add I0 K2)).
        λ (I0 : Nat).
        λ (Hyp : Σ (Hk : AllKeysEq Cap I0 Hh). AllHashedA Cap (Add K2 M) (arrCat K2 M T W) (S I0)).
          elim Hyp return (λ (Q : Σ (Hk : AllKeysEq Cap I0 Hh).
              AllHashedA Cap (Add K2 M) (arrCat K2 M T W) (S I0)).
              Σ (Hl : Σ (Hk2 : AllKeysEq Cap I0 Hh). AllHashedA Cap K2 T (S I0)).
                AllHashedA Cap M W (Add I0 (S K2))) {
            Pair (HkVal) (HRest) =>
              elim (Ih (S I0) HRest) return (λ (Q2 : Σ (Hl2 : AllHashedA Cap K2 T (S I0)).
                  AllHashedA Cap M W (Add (S I0) K2)).
                  Σ (Hl : Σ (Hk2 : AllKeysEq Cap I0 Hh). AllHashedA Cap K2 T (S I0)).
                    AllHashedA Cap M W (Add I0 (S K2))) {
                Pair (Hl2Val) (HW2) =>
                  Pair(Pair(HkVal, Hl2Val),
                    NatRw (λ (X : Nat). AllHashedA Cap M W X) (Add (S I0) K2) (Add I0 (S K2))
                      (IdSym Nat (Add I0 (S K2)) (Add (S I0) K2) (AddSucc I0 K2)) HW2)
              }
          })
      K L }
def AllHashedACatSplitTy : Term := prog{
  Π (Cap : Nat) → Π (K : Nat) → Π (L : Array K Bucket) → Π (M : Nat) → Π (W : Array M Bucket) →
  Π (I0 : Nat) →
    AllHashedA Cap (Add K M) (arrCat K M L W) I0 →
      Σ (Hl : AllHashedA Cap K L I0). AllHashedA Cap M W (Add I0 K) }

end Dllbc.StdLemmas

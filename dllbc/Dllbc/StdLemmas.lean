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
  λ (n : Nat). elim n return (λ (m : Nat). Le m m) {
    Z => unit,
    S (k) ih => ih } }
def LeReflTy : Term := prog{ Π (n : Nat) → Le n n }

-- The wall. Single outer elim on `a`; the `S` case elims on `b`, whose `S` case
-- elims on `c`, with the IH applied at the peeled proofs — every step
-- definitional through the `Le` equations. Nested, but every binder is NAMED and
-- every motive is written once and visible.
def LeTrans : Term := prog{
  λ (a : Nat).
    elim a return (λ (a0 : Nat). Π (b : Nat) → Π (c : Nat) → Le a0 b → Le b c → Le a0 c) {
      Z => λ (b : Nat). λ (c : Nat). λ (hab : Le Z b). λ (hbc : Le b c). unit,
      S (a') ih => λ (b : Nat). λ (c : Nat). λ (hab : Le (S a') b). λ (hbc : Le b c).
        elim b return (λ (b0 : Nat). Le (S a') b0 → Le b0 c → Le (S a') c) {
          Z => λ (hab0 : Le (S a') Z). λ (hbc0 : Le Z c). botElim (Le (S a') c) hab0,
          S (b') ihb => λ (hab0 : Le (S a') (S b')). λ (hbc0 : Le (S b') c).
            elim c return (λ (c0 : Nat). Le (S b') c0 → Le (S a') c0) {
              Z => λ (hbc1 : Le (S b') Z). botElim (Le (S a') Z) hbc1,
              S (c') ihc => λ (hbc1 : Le (S b') (S c')). ih b' c' hab0 hbc1
            } hbc0
        } hab hbc
    } }
def LeTransTy : Term := prog{
  Π (a : Nat) → Π (b : Nat) → Π (c : Nat) → Le a b → Le b c → Le a c }

-- Right-successor monotonicity: `a ≤ b ⟹ a ≤ S b`. Double induction (on `a`,
-- casing `b`): the `Z` head is trivial (`Le Z _ = ⊤`); the `S a'` head cases `b`
-- (`Le (S a') Z = ⊥`, else `Le a' b'` and the IH lifts it to `Le a' (S b')`).
-- The glue `CountSwapL'` needs to bend swapS's `Le (S i) j` into count_swapL's
-- `Le (S i) (Len l)` via one `LeTrans`.
def LeUpR : Term := prog{
  λ (a : Nat). elim a return (λ (az : Nat). Π (b : Nat) → Le az b → Le az (S b)) {
    Z => λ (b : Nat). λ (h : Le Z b). unit,
    S (a') ih => λ (b : Nat). λ (h : Le (S a') b).
      elim b return (λ (bz : Nat). Le (S a') bz → Le (S a') (S bz)) {
        Z => λ (h0 : Le (S a') Z). botElim (Le (S a') (S Z)) h0,
        S (b') ihb => λ (h0 : Le (S a') (S b')). ih b' h0
      } h } }
def LeUpRTy : Term := prog{ Π (a : Nat) → Π (b : Nat) → Le a b → Le a (S b) }

-- `i ≤ i + g`: the boundary never passes the scan position it feeds. A clean
-- induction on `i` (`Add (S i') g = S (Add i' g)`, so `Le (S i') (Add (S i') g)`
-- reduces to the IH). The partition swaps consume this as their `pij`.
def LeAdd : Term := prog{
  λ (i : Nat). elim i return (λ (iz : Nat). Π (g : Nat) → Le iz (Add iz g)) {
    Z => λ (g : Nat). unit,
    S (i') ih => λ (g : Nat). ih g } }
def LeAddTy : Term := prog{ Π (i : Nat) → Π (g : Nat) → Le i (Add i g) }

-- `b ≤ a + b` — the companion where the summand is on the LEFT (`LeAdd` has it on
-- the right). Induction on `a`: base is `LeRefl` (`Add Z b = b`), step lifts the
-- IH with `LeUpR` (`Add (S a') b = S (Add a' b)`). The scan-position bound uses
-- this because the length equation carries the remaining count `k` on the left.
def LeAddL : Term := prog{
  λ (b : Nat). λ (a : Nat).
    elim a return (λ (az : Nat). Le b (Add az b)) {
      Z => LeRefl b,
      S (a') ih => LeUpR b (Add a' b) ih } }
def LeAddLTy : Term := prog{ Π (b : Nat) → Π (a : Nat) → Le b (Add a b) }

-- `S i ≤ i + (S g)` — the swap's `pij`: the boundary `S i` is below the scan
-- position `S (Add i (S g))` whenever the gap is non-empty. Induction on `i`
-- avoids an AddSucc transport (`Add (S i') x = S (Add i' x)` is definitional),
-- so no rewrite is needed here.
def LeAddSucc : Term := prog{
  λ (i : Nat). elim i return (λ (iz : Nat). Π (g : Nat) → Le (S iz) (Add iz (S g))) {
    Z => λ (g : Nat). unit,
    S (i') ih => λ (g : Nat). ih g } }
def LeAddSuccTy : Term := prog{ Π (i : Nat) → Π (g : Nat) → Le (S i) (Add i (S g)) }

-- Transport a `Le` along an `Id` on its SECOND argument: `x = y ⟹ Le a x → Le a
-- y`. The bounds derived over the arithmetic normal form are moved onto `len *v`
-- (and back through `LenSwapL`) with this J-transport — the "LeTrans/le_step
-- glue where descent is not definitional".
def LeRwR : Term := prog{
  λ (a : Nat). λ (x : Nat). λ (y : Nat). λ (h : Id Nat x y). λ (p : Le a x).
    j Nat x (λ (y' : Nat). λ (hh : Id Nat x y'). Le a y') p y h }
def LeRwRTy : Term := prog{ Π (a : Nat) → Π (x : Nat) → Π (y : Nat) → Id Nat x y → Le a x → Le a y }

-- Transport a `Le` along an `Id` on its FIRST (smaller) argument: `x = y ⟹ Le x
-- b → Le y b`. The range partition's bound `Le (add lo (S (add k (add i g))))
-- (len *v)` is invariant across the recursion (the sum k+i+g is preserved), but
-- its SYNTACTIC form shifts as k descends and i/g grow; this moves the bound
-- between forms via the hshift identities — the Le mirror of LeRwR, and the one
-- lemma the M20 Id-toolkit lacked for the subrange generalization (§21).
def LeRwL : Term := prog{
  λ (b : Nat). λ (x : Nat). λ (y : Nat). λ (h : Id Nat x y). λ (p : Le x b).
    j Nat x (λ (y' : Nat). λ (hh : Id Nat x y'). Le y' b) p y h }
def LeRwLTy : Term := prog{ Π (b : Nat) → Π (x : Nat) → Π (y : Nat) → Id Nat x y → Le x b → Le y b }

-- Left-add monotonicity: `a ≤ b ⟹ lo + a ≤ lo + b`. Induction on `lo`: base is
-- the hypothesis (`Add Z x = x`), step is the IH verbatim (`add (S lo') x =
-- S (add lo' x)` and `Le (S _) (S _) = Le _ _` are both definitional). The range
-- partition's swap bounds shift the entry bound `Le (S i) (S (Add i g))` through
-- `Add lo` to reach `Le (Add lo (S i)) (Add lo (S (Add i g)))` (§21).
def LeAddMonoL : Term := prog{
  λ (lo : Nat). λ (a : Nat). λ (b : Nat). λ (h : Le a b).
    elim lo return (λ (loz : Nat). Le (Add loz a) (Add loz b)) {
      Z => h,
      S (lo') ih => ih } }
def LeAddMonoLTy : Term := prog{ Π (lo : Nat) → Π (a : Nat) → Π (b : Nat) → Le a b → Le (Add lo a) (Add lo b) }

/-! ## `IdTrans`, `IdCongr` — the J warm-ups partition's count-chaining consumes -/

def IdTrans : Term := prog{
  λ (A : Type). λ (x : A). λ (y : A). λ (z : A). λ (p : Id A x y). λ (q : Id A y z).
    j A x (λ (y' : A). λ (h : Id A x y'). Id A y' z → Id A x z) (λ (h : Id A x z). h) y p q }
def IdTransTy : Term := prog{
  Π (A : Type) → Π (x : A) → Π (y : A) → Π (z : A) → Id A x y → Id A y z → Id A x z }

def IdCongr : Term := prog{
  λ (A : Type). λ (B : Type). λ (f : A → B). λ (x : A). λ (y : A). λ (p : Id A x y).
    j A x (λ (y' : A). λ (h : Id A x y'). Id B (f x) (f y')) Refl y p }
def IdCongrTy : Term := prog{
  Π (A : Type) → Π (B : Type) → Π (f : A → B) → Π (x : A) → Π (y : A) → Id A x y → Id B (f x) (f y) }

def IdSym : Term := prog{
  λ (A : Type). λ (x : A). λ (y : A). λ (p : Id A x y).
    j A x (λ (y' : A). λ (h : Id A x y'). Id A y' x) Refl y p }
def IdSymTy : Term := prog{ Π (A : Type) → Π (x : A) → Π (y : A) → Id A x y → Id A y x }

/-! ## Arithmetic — the first double-inductions after the wall (§16 calibration) -/

def AddZero : Term := prog{
  λ (a : Nat). elim a return (λ (x : Nat). Id Nat (Add x Z) x) {
    Z => Refl,
    S (a') ih => IdCongr Nat Nat (λ (n : Nat). S n) (Add a' Z) a' ih } }
def AddZeroTy : Term := prog{ Π (a : Nat) → Id Nat (Add a Z) a }

def AddSucc : Term := prog{
  λ (a : Nat). λ (b : Nat). elim a return (λ (x : Nat). Id Nat (Add x (S b)) (S (Add x b))) {
    Z => Refl,
    S (a') ih => IdCongr Nat Nat (λ (n : Nat). S n) (Add a' (S b)) (S (Add a' b)) ih } }
def AddSuccTy : Term := prog{ Π (a : Nat) → Π (b : Nat) → Id Nat (Add a (S b)) (S (Add a b)) }

-- Commutativity: the classic proof, authored in the surface and checked first try.
def AddComm : Term := prog{
  λ (a : Nat). elim a return (λ (x : Nat). Π (b : Nat) → Id Nat (Add x b) (Add b x)) {
    Z => λ (b : Nat). IdSym Nat (Add b Z) b (AddZero b),
    S (a') ih => λ (b : Nat).
      IdTrans Nat (S (Add a' b)) (S (Add b a')) (Add b (S a'))
        (IdCongr Nat Nat (λ (n : Nat). S n) (Add a' b) (Add b a') (ih b))
        (IdSym Nat (Add b (S a')) (S (Add b a')) (AddSucc b a')) } }
def AddCommTy : Term := prog{ Π (a : Nat) → Π (b : Nat) → Id Nat (Add a b) (Add b a) }

def AddAssoc : Term := prog{
  λ (a : Nat). elim a return (λ (x : Nat). Π (b : Nat) → Π (c : Nat) → Id Nat (Add (Add x b) c) (Add x (Add b c))) {
    Z => λ (b : Nat). λ (c : Nat). Refl,
    S (a') ih => λ (b : Nat). λ (c : Nat).
      IdCongr Nat Nat (λ (n : Nat). S n) (Add (Add a' b) c) (Add a' (Add b c)) (ih b c) } }
def AddAssocTy : Term := prog{ Π (a : Nat) → Π (b : Nat) → Π (c : Nat) → Id Nat (Add (Add a b) c) (Add a (Add b c)) }

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
  λ (k : Nat). λ (i : Nat). λ (g : Nat).
    IdSym Nat (Add k (S (Add i g))) (S (Add k (Add i g))) (AddSucc k (Add i g)) }
def HshiftTrueTy : Term := prog{ Π (k : Nat) → Π (i : Nat) → Π (g : Nat) →
  Id Nat (Add (S k) (Add i g)) (Add k (Add (S i) g)) }

-- Gap growth: `Add (S k) (Add i g) = Add k (Add i (S g))` (move a successor from k
-- to g). `Add i (S g)` is stuck (add recurses on i), so this needs AddSucc TWICE
-- — once under `Add k` to grow the gap, once to pull the successor out front.
def HshiftFalse : Term := prog{
  λ (k : Nat). λ (i : Nat). λ (g : Nat).
    IdSym Nat (Add k (Add i (S g))) (S (Add k (Add i g)))
      (IdTrans Nat (Add k (Add i (S g))) (Add k (S (Add i g))) (S (Add k (Add i g)))
        (IdCongr Nat Nat (λ (x : Nat). Add k x) (Add i (S g)) (S (Add i g)) (AddSucc i g))
        (AddSucc k (Add i g))) }
def HshiftFalseTy : Term := prog{ Π (k : Nat) → Π (i : Nat) → Π (g : Nat) →
  Id Nat (Add (S k) (Add i g)) (Add k (Add i (S g))) }

-- `Count`'s Cons-unfolding equation as an Id — definitional, a `Refl` after whnf.
def CountCons : Term := prog{ λ (m : Nat). λ (h : Nat). λ (t : List Nat). Refl }
def CountConsTy : Term := prog{
  Π (m : Nat) → Π (h : Nat) → Π (t : List Nat) →
    Id Nat (Count m (Cons h t)) (boolRec (λ (b : Bool). Nat) (S (Count m t)) (Count m t) (Eqb m h)) }

/-! ## The `Count`/`Append`/`Take`/`Drop` lemmas (§16-2)

    `CountAppend` — count distributes over `Append` — needs a dependent Bool-elim
    on `Eqb m h` in the `Cons` case (the motive abstracts the `boolRec` that
    `Count (Cons …)` unfolds to). `TakeDropId` reassembles a list from its
    prefix and suffix. Both are the building blocks the swap-count lemma consumes. -/

def CountAppend : Term := prog{
  λ (m : Nat). λ (a : List Nat). λ (b : List Nat).
    elim a return (λ (x : List Nat). Id Nat (Count m (Append x b)) (Add (Count m x) (Count m b))) {
      Nil => Refl,
      Cons (h) (t) ih =>
        elim (Eqb m h) return (λ (bv : Bool).
          Id Nat (boolRec (λ (w : Bool). Nat) (S (Count m (Append t b))) (Count m (Append t b)) bv)
                 (Add (boolRec (λ (w : Bool). Nat) (S (Count m t)) (Count m t) bv) (Count m b))) {
          True => IdCongr Nat Nat (λ (n : Nat). S n) (Count m (Append t b)) (Add (Count m t) (Count m b)) ih,
          False => ih
        }
    } }
def CountAppendTy : Term := prog{
  Π (m : Nat) → Π (a : List Nat) → Π (b : List Nat) →
    Id Nat (Count m (Append a b)) (Add (Count m a) (Count m b)) }

def TakeDropId : Term := prog{
  λ (i : Nat). elim i return (λ (k : Nat). Π (l : List Nat) → Id (List Nat) (Append (Take k l) (Drop k l)) l) {
    Z => λ (l : List Nat). Refl,
    S (i') ih => λ (l : List Nat).
      elim l return (λ (x : List Nat). Id (List Nat) (Append (Take (S i') x) (Drop (S i') x)) x) {
        Nil => Refl,
        Cons (h) (t) ihl =>
          IdCongr (List Nat) (List Nat) (λ (r : List Nat). Cons h r)
            (Append (Take i' t) (Drop i' t)) t (ih t)
      } } }
def TakeDropIdTy : Term := prog{
  Π (i : Nat) → Π (l : List Nat) → Id (List Nat) (Append (Take i l) (Drop i l)) l }

/-! ## `NthL`, `Set`, `SwapL` — the pure specification of swap (§16-2)

    Authored in the surface (dogfooding §15 — a first raw-de-Bruijn `Set` had a
    `pvar 4`-vs-`pvar 3` slip; the surface version cannot slip). `SwapL` mirrors
    the cursor walk: recurse past the prefix, then at `i = 0` exchange the head
    with position `j` of the tail (`Cons (NthL j' xs) (Set j' x xs)`). Reduces:
    `SwapL 0 2 [1,2,3] = [3,2,1]`. `CountSwapL` is the pending node — see the
    milestone report: it requires a BOUND (`SwapL` off the end defaults `NthL` to
    `Z`, breaking count preservation), so it decomposes into a bounded stack. -/

def NthL : Term := prog{
  λ (k : Nat). elim k return (λ (z : Nat). List Nat → Nat) {
    Z => λ (l : List Nat). elim l return (λ (z : List Nat). Nat) { Nil => Z, Cons (h) (t) ihl => h },
    S (k') rec => λ (l : List Nat). elim l return (λ (z : List Nat). Nat) { Nil => Z, Cons (h) (t) ihl => rec t } } }

def Set : Term := prog{
  λ (k : Nat). λ (v : Nat). elim k return (λ (z : Nat). List Nat → List Nat) {
    Z => λ (l : List Nat). elim l return (λ (z : List Nat). List Nat) { Nil => Nil, Cons (h) (t) ihl => Cons v t },
    S (k') rec => λ (l : List Nat). elim l return (λ (z : List Nat). List Nat) { Nil => Nil, Cons (h) (t) ihl => Cons h (rec t) } } }

def SwapL : Term := prog{
  λ (i : Nat). elim i return (λ (z : Nat). Nat → List Nat → List Nat) {
    Z => λ (j : Nat). λ (l : List Nat). elim l return (λ (z : List Nat). List Nat) {
      Nil => Nil,
      Cons (x) (xs) ihl => elim j return (λ (z : Nat). List Nat) {
        Z => Cons x xs,
        S (j') jih => Cons (NthL j' xs) (Set j' x xs) } },
    S (i') reci => λ (j : Nat). λ (l : List Nat). elim l return (λ (z : List Nat). List Nat) {
      Nil => Nil,
      Cons (x) (xs) ihl => elim j return (λ (z : Nat). List Nat) {
        Z => Cons x xs,
        S (j') jih => Cons x (reci j' xs) } } } }

/-! ## Length preservation — the spec `swapS` carries (§16, len variant)

    `LenSet`/`LenSwapL` hold UNCONDITIONALLY — no bounds — because `Set`
    preserves length even off the end (it replaces or no-ops, never resizes) and
    `SwapL` only ever rebuilds the same spine. Unlike count, length needs no
    `Eqb`, so these are clean surface inductions (no rewriting layer required). -/

abbrev Len : Term := Std.lenFnT

def LenSet : Term := prog{
  λ (k : Nat). λ (v : Nat).
    elim k return (λ (z : Nat). Π (l : List Nat) → Id Nat (Len (Set z v l)) (Len l)) {
      Z => λ (l : List Nat). elim l return (λ (x : List Nat). Id Nat (Len (Set Z v x)) (Len x)) {
        Nil => Refl, Cons (h) (t) ihl => Refl },
      S (k') ih => λ (l : List Nat). elim l return (λ (x : List Nat). Id Nat (Len (Set (S k') v x)) (Len x)) {
        Nil => Refl,
        Cons (h) (t) ihl => IdCongr Nat Nat (λ (n : Nat). S n) (Len (Set k' v t)) (Len t) (ih t) } } }
def LenSetTy : Term := prog{ Π (k : Nat) → Π (v : Nat) → Π (l : List Nat) → Id Nat (Len (Set k v l)) (Len l) }

def LenSwapL : Term := prog{
  λ (i : Nat).
    elim i return (λ (z : Nat). Π (j : Nat) → Π (l : List Nat) → Id Nat (Len (SwapL z j l)) (Len l)) {
      Z => λ (j : Nat). λ (l : List Nat).
        elim l return (λ (x : List Nat). Id Nat (Len (SwapL Z j x)) (Len x)) {
          Nil => Refl,
          Cons (y) (ys) ihl => elim j return (λ (w : Nat). Id Nat (Len (SwapL Z w (Cons y ys))) (Len (Cons y ys))) {
            Z => Refl,
            S (j') jih => IdCongr Nat Nat (λ (n : Nat). S n) (Len (Set j' y ys)) (Len ys) (LenSet j' y ys) } },
      S (i') ih => λ (j : Nat). λ (l : List Nat).
        elim l return (λ (x : List Nat). Id Nat (Len (SwapL (S i') j x)) (Len x)) {
          Nil => Refl,
          Cons (y) (ys) ihl => elim j return (λ (w : Nat). Id Nat (Len (SwapL (S i') w (Cons y ys))) (Len (Cons y ys))) {
            Z => Refl,
            S (j') jih => IdCongr Nat Nat (λ (n : Nat). S n) (Len (SwapL i' j' ys)) (Len ys) (ih j' ys) } } } }
def LenSwapLTy : Term := prog{ Π (i : Nat) → Π (j : Nat) → Π (l : List Nat) → Id Nat (Len (SwapL i j l)) (Len l) }

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
  λ (m : Nat). λ (a : Nat). λ (b : Nat). λ (l : List Nat).
    elim (Eqb m a) generalizing (Id Nat (Count m (Cons a (Cons b l))) (Count m (Cons b (Cons a l)))) {
      True => elim (Eqb m b) generalizing
        (Id Nat (S (Count m (Cons b l)))
                (boolRec (λ (w : Bool). Nat) (S (S (Count m l))) (S (Count m l)) (Eqb m b))) {
        True => Refl, False => Refl },
      False => Refl } }
def Cons2CommTy : Term := prog{
  Π (m : Nat) → Π (a : Nat) → Π (b : Nat) → Π (l : List Nat) →
    Id Nat (Count m (Cons a (Cons b l))) (Count m (Cons b (Cons a l))) }

-- Congruence of `Count` under `Cons`: the `f` abstracts `Count m ·` out of BOTH
-- occurrences in the `boolRec` that `Count m (Cons h ·)` whnf's to, so a single
-- `IdCongr` transports the tail equation through the head.
def CountConsCongr : Term := prog{
  λ (m : Nat). λ (h : Nat). λ (l1 : List Nat). λ (l2 : List Nat). λ (p : Id Nat (Count m l1) (Count m l2)).
    IdCongr Nat Nat (λ (r : Nat). boolRec (λ (w : Bool). Nat) (S r) r (Eqb m h)) (Count m l1) (Count m l2) p }
def CountConsCongrTy : Term := prog{
  Π (m : Nat) → Π (h : Nat) → Π (l1 : List Nat) → Π (l2 : List Nat) →
    Id Nat (Count m l1) (Count m l2) → Id Nat (Count m (Cons h l1)) (Count m (Cons h l2)) }

-- The §18 rewrite-by-Id lemma, named: from a RECEIVED equation `Eqb m a = True`,
-- resolve the STUCK `Count m (Cons a l)` to `S (Count m l)`. J transports `Refl`
-- along `IdSym hq`, the motive abstracting the scrutinee `z` out of the `boolRec`
-- that `Count (Cons …)` unfolds to. Abstraction alone cannot do this (the subterm
-- hides behind the scrutinee's own reduction); this is the knowledge half. The
-- imperative tie-in returns THIS applied to its params.
def CountConsHit : Term := prog{
  λ (m : Nat). λ (a : Nat). λ (l : List Nat). λ (hq : Id Bool (Eqb m a) True).
    j Bool True
      (λ (z : Bool). λ (h : Id Bool True z).
        Id Nat (boolRec (λ (w : Bool). Nat) (S (Count m l)) (Count m l) z) (S (Count m l)))
      Refl (Eqb m a) (IdSym Bool (Eqb m a) True hq) }
def CountConsHitTy : Term := prog{
  Π (m : Nat) → Π (a : Nat) → Π (l : List Nat) → Id Bool (Eqb m a) True →
    Id Nat (Count m (Cons a l)) (S (Count m l)) }

-- Bounded head-swap: exchanging the head `x` with position `j` of the tail `xs`
-- preserves count, PROVIDED `j` is in range (`Le (S j) (Len xs)`). Induction on
-- `j`, casing `xs`; the `Nil` leaves are ⊥-discharged by the bound (`Le (S _) Z`).
-- Base (`j = Z`): the swap is `Cons y (Cons x ys) ↔ Cons x (Cons y ys)`, exactly
-- `Cons2Comm`. Step (`j = S j'`): a three-link `IdTrans` chain — float the
-- swapped-in element past the head with `Cons2Comm`, apply the IH under the head
-- via `CountConsCongr`, then `Cons2Comm` back.
def CountHeadswap : Term := prog{
  λ (m : Nat). λ (x : Nat). λ (j : Nat).
    elim j return (λ (jz : Nat).
        Π (xs : List Nat) → Le (S jz) (Len xs) →
          Id Nat (Count m (Cons (NthL jz xs) (Set jz x xs))) (Count m (Cons x xs))) {
      Z => λ (xs : List Nat).
        elim xs return (λ (xz : List Nat).
            Le (S Z) (Len xz) →
              Id Nat (Count m (Cons (NthL Z xz) (Set Z x xz))) (Count m (Cons x xz))) {
          Nil => λ (bnd0 : Le (S Z) (Len Nil)).
            botElim (Id Nat (Count m (Cons (NthL Z Nil) (Set Z x Nil))) (Count m (Cons x Nil))) bnd0,
          Cons (y) (ys) ihx => λ (bnd0 : Le (S Z) (Len (Cons y ys))).
            Cons2Comm m y x ys },
      S (j') ih => λ (xs : List Nat).
        elim xs return (λ (xz : List Nat).
            Le (S (S j')) (Len xz) →
              Id Nat (Count m (Cons (NthL (S j') xz) (Set (S j') x xz))) (Count m (Cons x xz))) {
          Nil => λ (bnd0 : Le (S (S j')) (Len Nil)).
            botElim (Id Nat (Count m (Cons (NthL (S j') Nil) (Set (S j') x Nil))) (Count m (Cons x Nil))) bnd0,
          Cons (y) (ys) ihx => λ (bnd0 : Le (S (S j')) (Len (Cons y ys))).
            IdTrans Nat
              (Count m (Cons (NthL j' ys) (Cons y (Set j' x ys))))
              (Count m (Cons y (Cons (NthL j' ys) (Set j' x ys))))
              (Count m (Cons x (Cons y ys)))
              (Cons2Comm m (NthL j' ys) y (Set j' x ys))
              (IdTrans Nat
                (Count m (Cons y (Cons (NthL j' ys) (Set j' x ys))))
                (Count m (Cons y (Cons x ys)))
                (Count m (Cons x (Cons y ys)))
                (CountConsCongr m y (Cons (NthL j' ys) (Set j' x ys)) (Cons x ys) (ih ys bnd0))
                (Cons2Comm m y x ys)) } } }
def CountHeadswapTy : Term := prog{
  Π (m : Nat) → Π (x : Nat) → Π (j : Nat) → Π (xs : List Nat) → Le (S j) (Len xs) →
    Id Nat (Count m (Cons (NthL j xs) (Set j x xs))) (Count m (Cons x xs)) }

-- The top: `SwapL i j` preserves count when both indices are in range. Induction
-- on `i`, casing `l` then `j`. The head case (`i = Z`, `j = S j'`) is exactly a
-- `CountHeadswap` (`SwapL Z (S j') (Cons y ys) = Cons (NthL j' ys) (Set j' y ys)`);
-- the recursive case (`i = S i'`, `j = S j'`) rebuilds `Cons y (SwapL i' j' ys)`,
-- discharged by `CountConsCongr` on the IH; the degenerate `j = Z` / `i > j`
-- cases are the identity swap (`Refl`); `Nil` is ⊥-discharged by `Le (S i) …`.
def CountSwapL : Term := prog{
  λ (m : Nat). λ (i : Nat).
    elim i return (λ (iz : Nat).
        Π (j : Nat) → Π (l : List Nat) → Le (S iz) (Len l) → Le (S j) (Len l) →
          Id Nat (Count m (SwapL iz j l)) (Count m l)) {
      Z => λ (j : Nat). λ (l : List Nat).
        elim l return (λ (lz : List Nat).
            Le (S Z) (Len lz) → Le (S j) (Len lz) → Id Nat (Count m (SwapL Z j lz)) (Count m lz)) {
          Nil => λ (bi0 : Le (S Z) (Len Nil)). λ (bj0 : Le (S j) (Len Nil)).
            botElim (Id Nat (Count m (SwapL Z j Nil)) (Count m Nil)) bi0,
          Cons (y) (ys) ihl => λ (bi0 : Le (S Z) (Len (Cons y ys))). λ (bj0 : Le (S j) (Len (Cons y ys))).
            elim j return (λ (jz : Nat).
                Le (S jz) (Len (Cons y ys)) →
                  Id Nat (Count m (SwapL Z jz (Cons y ys))) (Count m (Cons y ys))) {
              Z => λ (bj1 : Le (S Z) (Len (Cons y ys))). Refl,
              S (j') jih => λ (bj1 : Le (S (S j')) (Len (Cons y ys))).
                CountHeadswap m y j' ys bj1
            } bj0 },
      S (i') ih => λ (j : Nat). λ (l : List Nat).
        elim l return (λ (lz : List Nat).
            Le (S (S i')) (Len lz) → Le (S j) (Len lz) → Id Nat (Count m (SwapL (S i') j lz)) (Count m lz)) {
          Nil => λ (bi0 : Le (S (S i')) (Len Nil)). λ (bj0 : Le (S j) (Len Nil)).
            botElim (Id Nat (Count m (SwapL (S i') j Nil)) (Count m Nil)) bi0,
          Cons (y) (ys) ihl => λ (bi0 : Le (S (S i')) (Len (Cons y ys))). λ (bj0 : Le (S j) (Len (Cons y ys))).
            elim j return (λ (jz : Nat).
                Le (S jz) (Len (Cons y ys)) →
                  Id Nat (Count m (SwapL (S i') jz (Cons y ys))) (Count m (Cons y ys))) {
              Z => λ (bj1 : Le (S Z) (Len (Cons y ys))). Refl,
              S (j') jih => λ (bj1 : Le (S (S j')) (Len (Cons y ys))).
                CountConsCongr m y (SwapL i' j' ys) ys (ih j' ys bi0 bj1)
            } bj0 } } }
def CountSwapLTy : Term := prog{
  Π (m : Nat) → Π (i : Nat) → Π (j : Nat) → Π (l : List Nat) →
    Le (S i) (Len l) → Le (S j) (Len l) → Id Nat (Count m (SwapL i j l)) (Count m l) }

-- The friction-free corollary: CountSwapL with swapS's telescope-mirrored
-- premises (`Le (S i) j`, `Le (S j) (Len l)` — exactly the `pij`/`p2` a swapS
-- caller holds). The general CountSwapL is the mathematically right statement
-- (independent bounds, no `i ≤ j` needed); this derives the caller's hand-off from
-- it. `Le (S i) (Len l)` comes by `LeTrans (S i) (S j) (Len l)`: `LeUpR` lifts
-- `pij : Le (S i) j` to `Le (S i) (S j)`, then chain with `p2`.
def CountSwapL' : Term := prog{
  λ (m : Nat). λ (i : Nat). λ (j : Nat). λ (l : List Nat).
    λ (pij : Le (S i) j). λ (p2 : Le (S j) (Len l)).
      CountSwapL m i j l (LeTrans (S i) (S j) (Len l) (LeUpR (S i) j pij) p2) p2 }
def CountSwapL'Ty : Term := prog{
  Π (m : Nat) → Π (i : Nat) → Π (j : Nat) → Π (l : List Nat) →
    Le (S i) j → Le (S j) (Len l) → Id Nat (Count m (SwapL i j l)) (Count m l) }

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
  λ (i : Nat).
    elim i return (λ (iz : Nat). Π (j : Nat) → Π (l : List Nat) → Le (S iz) j → Le (S j) (Len l) →
        Id (List Nat) (Set iz (NthL j l) (Set j (NthL iz l) l)) (SwapL iz j l)) {
      Z => λ (j : Nat). λ (l : List Nat).
        elim l return (λ (lz : List Nat). Le (S Z) j → Le (S j) (Len lz) →
            Id (List Nat) (Set Z (NthL j lz) (Set j (NthL Z lz) lz)) (SwapL Z j lz)) {
          Nil => λ (pij : Le (S Z) j). λ (p2 : Le (S j) (Len Nil)).
            botElim (Id (List Nat) (Set Z (NthL j Nil) (Set j (NthL Z Nil) Nil)) (SwapL Z j Nil)) p2,
          Cons (y) (ys) ihl => λ (pij : Le (S Z) j). λ (p2 : Le (S j) (Len (Cons y ys))).
            elim j return (λ (jz : Nat). Le (S Z) jz → Le (S jz) (Len (Cons y ys)) →
                Id (List Nat) (Set Z (NthL jz (Cons y ys)) (Set jz (NthL Z (Cons y ys)) (Cons y ys))) (SwapL Z jz (Cons y ys))) {
              Z => λ (pijz : Le (S Z) Z). λ (p2z : Le (S Z) (Len (Cons y ys))).
                botElim (Id (List Nat) (Set Z (NthL Z (Cons y ys)) (Set Z (NthL Z (Cons y ys)) (Cons y ys))) (SwapL Z Z (Cons y ys))) pijz,
              S (j') jih => λ (pijs : Le (S Z) (S j')). λ (p2s : Le (S (S j')) (Len (Cons y ys))). Refl
            } pij p2 },
      S (i') ih => λ (j : Nat). λ (l : List Nat).
        elim l return (λ (lz : List Nat). Le (S (S i')) j → Le (S j) (Len lz) →
            Id (List Nat) (Set (S i') (NthL j lz) (Set j (NthL (S i') lz) lz)) (SwapL (S i') j lz)) {
          Nil => λ (pij : Le (S (S i')) j). λ (p2 : Le (S j) (Len Nil)).
            botElim (Id (List Nat) (Set (S i') (NthL j Nil) (Set j (NthL (S i') Nil) Nil)) (SwapL (S i') j Nil)) p2,
          Cons (y) (ys) ihl => λ (pij : Le (S (S i')) j). λ (p2 : Le (S j) (Len (Cons y ys))).
            elim j return (λ (jz : Nat). Le (S (S i')) jz → Le (S jz) (Len (Cons y ys)) →
                Id (List Nat) (Set (S i') (NthL jz (Cons y ys)) (Set jz (NthL (S i') (Cons y ys)) (Cons y ys))) (SwapL (S i') jz (Cons y ys))) {
              Z => λ (pijz : Le (S (S i')) Z). λ (p2z : Le (S Z) (Len (Cons y ys))).
                botElim (Id (List Nat) (Set (S i') (NthL Z (Cons y ys)) (Set Z (NthL (S i') (Cons y ys)) (Cons y ys))) (SwapL (S i') Z (Cons y ys))) pijz,
              S (j') jih => λ (pijs : Le (S (S i')) (S j')). λ (p2s : Le (S (S j')) (Len (Cons y ys))).
                IdCongr (List Nat) (List Nat) (λ (t : List Nat). Cons y t)
                  (Set i' (NthL j' ys) (Set j' (NthL i' ys) ys)) (SwapL i' j' ys) (ih j' ys pijs p2s)
            } pij p2 } } }
def SwapLSetTy : Term := prog{
  Π (i : Nat) → Π (j : Nat) → Π (l : List Nat) → Le (S i) j → Le (S j) (Len l) →
    Id (List Nat) (Set i (NthL j l) (Set j (NthL i l) l)) (SwapL i j l) }

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
  λ (pivot : Nat). λ (k : Nat).
    elim k return (λ (kz : Nat). Π (i : Nat) → Π (g : Nat) → List Nat → List Nat) {
      Z => λ (i : Nat). λ (g : Nat). λ (l : List Nat).
        elim i return (λ (iz : Nat). List Nat) {
          Z => l,
          S (i') iih => SwapL Z (S i') l },
      S (k') rec => λ (i : Nat). λ (g : Nat). λ (l : List Nat).
        elim (Leb (NthL (S (Add i g)) l) pivot) return (λ (w : Bool). List Nat) {
          True => elim g return (λ (gz : Nat). List Nat) {
            Z => rec (S i) Z l,
            S (g') gih => rec (S i) (S g') (SwapL (S i) (S (Add i g)) l) },
          False => rec i (S g) l } } }

def PartitionL : Term := prog{
  λ (n : Nat). λ (l : List Nat).
    elim n return (λ (nz : Nat). List Nat) {
      Z => l,
      S (n') rec => PartScanL (NthL Z l) n' Z Z l } }
def PartitionLTy : Term := prog{ Π (n : Nat) → List Nat → List Nat }

/-! ## `PartScanIdxL` / `PartIdxL` — the boundary INDEX the scan produces (§21)

    Mirror of partScanL's recursion but returning the boundary `i` (the pivot's
    final position) at `k = Z` instead of the placed list. This is the index the
    imperative partition returns transparently (a Σ pinning it to `PartIdxL`), and
    the split point sortL's two recursive calls ride. Same casings/arithmetic as
    PartScanL, so the two stay in lockstep. -/

def PartScanIdxL : Term := prog{
  λ (pivot : Nat). λ (k : Nat).
    elim k return (λ (kz : Nat). Π (i : Nat) → Π (g : Nat) → List Nat → Nat) {
      Z => λ (i : Nat). λ (g : Nat). λ (l : List Nat). i,
      S (k') rec => λ (i : Nat). λ (g : Nat). λ (l : List Nat).
        elim (Leb (NthL (S (Add i g)) l) pivot) return (λ (w : Bool). Nat) {
          True => elim g return (λ (gz : Nat). Nat) {
            Z => rec (S i) Z l,
            S (g') gih => rec (S i) (S g') (SwapL (S i) (S (Add i g)) l) },
          False => rec i (S g) l } } }

def PartIdxL : Term := prog{
  λ (n : Nat). λ (l : List Nat).
    elim n return (λ (nz : Nat). Nat) {
      Z => Z,
      S (n') rec => PartScanIdxL (NthL Z l) n' Z Z l } }
def PartIdxLTy : Term := prog{ Π (n : Nat) → List Nat → Nat }

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
  λ (fuel : Nat).
    elim fuel return (λ (fz : Nat). Π (n : Nat) → List Nat → List Nat) {
      Z => λ (n : Nat). λ (l : List Nat). l,
      S (f') rec => λ (n : Nat). λ (l : List Nat).
        elim n return (λ (nz : Nat). List Nat) {
          Z => l,
          S (n') nih => elim n' return (λ (mz : Nat). List Nat) {
            Z => l,
            S (n'') n2ih =>
              let p = PartitionL n l;
              let i = PartIdxL n l;
              Append (rec i (Take i p)) (Cons (NthL i p) (rec (Len (Drop (S i) p)) (Drop (S i) p)))
          } } } }
def SortLTy : Term := prog{ Π (fuel : Nat) → Π (n : Nat) → List Nat → List Nat }

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
  λ (pivot : Nat). λ (lo : Nat). λ (k : Nat).
    elim k return (λ (kz : Nat). Π (i : Nat) → Π (g : Nat) → List Nat → List Nat) {
      Z => λ (i : Nat). λ (g : Nat). λ (l : List Nat).
        elim i return (λ (iz : Nat). List Nat) {
          Z => l,
          S (i') iih => SwapL lo (Add lo (S i')) l },
      S (k') rec => λ (i : Nat). λ (g : Nat). λ (l : List Nat).
        elim (Leb (NthL (Add lo (S (Add i g))) l) pivot) return (λ (w : Bool). List Nat) {
          True => elim g return (λ (gz : Nat). List Nat) {
            Z => rec (S i) Z l,
            S (g') gih => rec (S i) (S g') (SwapL (Add lo (S i)) (Add lo (S (Add i g))) l) },
          False => rec i (S g) l } } }

def PartitionRangeL : Term := prog{
  λ (lo : Nat). λ (cnt : Nat). λ (l : List Nat).
    elim cnt return (λ (cz : Nat). List Nat) {
      Z => l,
      S (cnt') rec => PartScanRangeL (NthL lo l) lo cnt' Z Z l } }

def PartScanIdxRangeL : Term := prog{
  λ (pivot : Nat). λ (lo : Nat). λ (k : Nat).
    elim k return (λ (kz : Nat). Π (i : Nat) → Π (g : Nat) → List Nat → Nat) {
      Z => λ (i : Nat). λ (g : Nat). λ (l : List Nat). i,
      S (k') rec => λ (i : Nat). λ (g : Nat). λ (l : List Nat).
        elim (Leb (NthL (Add lo (S (Add i g))) l) pivot) return (λ (w : Bool). Nat) {
          True => elim g return (λ (gz : Nat). Nat) {
            Z => rec (S i) Z l,
            S (g') gih => rec (S i) (S g') (SwapL (Add lo (S i)) (Add lo (S (Add i g))) l) },
          False => rec i (S g) l } } }

def PartIdxRangeL : Term := prog{
  λ (lo : Nat). λ (cnt : Nat). λ (l : List Nat).
    elim cnt return (λ (cz : Nat). Nat) {
      Z => Z,
      S (cnt') rec => PartScanIdxRangeL (NthL lo l) lo cnt' Z Z l } }

def PartScanGapRangeL : Term := prog{
  λ (pivot : Nat). λ (lo : Nat). λ (k : Nat).
    elim k return (λ (kz : Nat). Π (i : Nat) → Π (g : Nat) → List Nat → Nat) {
      Z => λ (i : Nat). λ (g : Nat). λ (l : List Nat). g,
      S (k') rec => λ (i : Nat). λ (g : Nat). λ (l : List Nat).
        elim (Leb (NthL (Add lo (S (Add i g))) l) pivot) return (λ (w : Bool). Nat) {
          True => elim g return (λ (gz : Nat). Nat) {
            Z => rec (S i) Z l,
            S (g') gih => rec (S i) (S g') (SwapL (Add lo (S i)) (Add lo (S (Add i g))) l) },
          False => rec i (S g) l } } }

def PartGapRangeL : Term := prog{
  λ (lo : Nat). λ (cnt : Nat). λ (l : List Nat).
    elim cnt return (λ (cz : Nat). Nat) {
      Z => Z,
      S (cnt') rec => PartScanGapRangeL (NthL lo l) lo cnt' Z Z l } }

-- The scan's size invariant: the boundary `idx` plus the gap `gap` always sum to
-- `k + i + g` — the scan neither creates nor destroys total budget, it only shifts
-- successors between the `k`/`i`/`g` slots (the same move the `hshift` lemmas
-- encode). Induction on `k` with `i`,`g`,`l` quantified AFTER `k` in the motive, so
-- the IH is usable at the shifted arguments each recursive step takes. The `S k`
-- step cases on the SAME `Leb` scrutinee that both `PartScanIdxRangeL` and
-- `PartScanGapRangeL` branch on, abstracting that `Bool` uniformly across the idx
-- and gap elims; each leaf is one `hshift` transport (`IdSym`/`IdTrans`).
def PartScanSizeL : Term := prog{
  λ (pivot : Nat). λ (lo : Nat). λ (k : Nat).
    elim k return (λ (kz : Nat). Π (i : Nat) → Π (g : Nat) → Π (l : List Nat) →
        Id Nat (Add (PartScanIdxRangeL pivot lo kz i g l) (PartScanGapRangeL pivot lo kz i g l)) (Add kz (Add i g))) {
      Z => λ (i : Nat). λ (g : Nat). λ (l : List Nat). Refl,
      S (k') ih => λ (i : Nat). λ (g : Nat). λ (l : List Nat).
        elim (Leb (NthL (Add lo (S (Add i g))) l) pivot)
          return (λ (w : Bool). Id Nat
            (Add (elim w return (λ (ww : Bool). Nat) {
                    True => elim g return (λ (gz : Nat). Nat) {
                      Z => PartScanIdxRangeL pivot lo k' (S i) Z l,
                      S (g') gih => PartScanIdxRangeL pivot lo k' (S i) (S g') (SwapL (Add lo (S i)) (Add lo (S (Add i g))) l) },
                    False => PartScanIdxRangeL pivot lo k' i (S g) l })
                 (elim w return (λ (ww : Bool). Nat) {
                    True => elim g return (λ (gz : Nat). Nat) {
                      Z => PartScanGapRangeL pivot lo k' (S i) Z l,
                      S (g') gih => PartScanGapRangeL pivot lo k' (S i) (S g') (SwapL (Add lo (S i)) (Add lo (S (Add i g))) l) },
                    False => PartScanGapRangeL pivot lo k' i (S g) l }))
            (Add (S k') (Add i g))) {
          True => elim g return (λ (gz : Nat). Id Nat
                    (Add (elim gz return (λ (gy : Nat). Nat) {
                            Z => PartScanIdxRangeL pivot lo k' (S i) Z l,
                            S (g') gih => PartScanIdxRangeL pivot lo k' (S i) (S g') (SwapL (Add lo (S i)) (Add lo (S (Add i g))) l) })
                         (elim gz return (λ (gy : Nat). Nat) {
                            Z => PartScanGapRangeL pivot lo k' (S i) Z l,
                            S (g') gih => PartScanGapRangeL pivot lo k' (S i) (S g') (SwapL (Add lo (S i)) (Add lo (S (Add i g))) l) }))
                    (Add (S k') (Add i gz))) {
            Z => IdTrans Nat
                   (Add (PartScanIdxRangeL pivot lo k' (S i) Z l) (PartScanGapRangeL pivot lo k' (S i) Z l))
                   (Add k' (Add (S i) Z))
                   (Add (S k') (Add i Z))
                   (ih (S i) Z l)
                   (IdSym Nat (Add (S k') (Add i Z)) (Add k' (Add (S i) Z)) (HshiftTrue k' i Z)),
            S (g') gih => IdTrans Nat
                   (Add (PartScanIdxRangeL pivot lo k' (S i) (S g') (SwapL (Add lo (S i)) (Add lo (S (Add i g))) l)) (PartScanGapRangeL pivot lo k' (S i) (S g') (SwapL (Add lo (S i)) (Add lo (S (Add i g))) l)))
                   (Add k' (Add (S i) (S g')))
                   (Add (S k') (Add i (S g')))
                   (ih (S i) (S g') (SwapL (Add lo (S i)) (Add lo (S (Add i g))) l))
                   (IdSym Nat (Add (S k') (Add i (S g'))) (Add k' (Add (S i) (S g'))) (HshiftTrue k' i (S g')))
          },
          False => IdTrans Nat
                     (Add (PartScanIdxRangeL pivot lo k' i (S g) l) (PartScanGapRangeL pivot lo k' i (S g) l))
                     (Add k' (Add i (S g)))
                     (Add (S k') (Add i g))
                     (ih i (S g) l)
                     (IdSym Nat (Add (S k') (Add i g)) (Add k' (Add i (S g))) (HshiftFalse k' i g))
        }
    } }
def PartScanSizeLTy : Term := prog{ Π (pivot : Nat) → Π (lo : Nat) → Π (k : Nat) → Π (i : Nat) → Π (g : Nat) → Π (l : List Nat) →
  Id Nat (Add (PartScanIdxRangeL pivot lo k i g l) (PartScanGapRangeL pivot lo k i g l)) (Add k (Add i g)) }

-- The range scan preserves length — it only ever rebuilds the same spine (SwapL,
-- which LenSwapL knows preserves length) or leaves it. Same induction shape as
-- PartScanSizeL (on k, elim the leb Bool, elim g in True), but the leaves are
-- simpler: each recursive step is the IH, and the two SwapL cases (Z-base pivot
-- placement, True/S-g swap) bridge through LenSwapL. The quicksort recursion
-- needs this because partitionRange MUTATES *v, and the two recursive-call range
-- bounds refer to len (*v-after-partition) — this moves them back onto len (entry).
def LenPartScanRangeL : Term := prog{
  λ (pivot : Nat). λ (lo : Nat). λ (k : Nat).
    elim k return (λ (kz : Nat). Π (i : Nat) → Π (g : Nat) → Π (l : List Nat) →
        Id Nat (Len (PartScanRangeL pivot lo kz i g l)) (Len l)) {
      Z => λ (i : Nat). λ (g : Nat). λ (l : List Nat).
        elim i return (λ (iz : Nat). Id Nat
            (Len (elim iz return (λ (iy : Nat). List Nat) { Z => l, S (i') iih => SwapL lo (Add lo (S i')) l }))
            (Len l)) {
          Z => Refl,
          S (i') iih => LenSwapL lo (Add lo (S i')) l },
      S (k') ih => λ (i : Nat). λ (g : Nat). λ (l : List Nat).
        elim (Leb (NthL (Add lo (S (Add i g))) l) pivot)
          return (λ (w : Bool). Id Nat
            (Len (elim w return (λ (ww : Bool). List Nat) {
                    True => elim g return (λ (gz : Nat). List Nat) {
                      Z => PartScanRangeL pivot lo k' (S i) Z l,
                      S (g') gih => PartScanRangeL pivot lo k' (S i) (S g') (SwapL (Add lo (S i)) (Add lo (S (Add i g))) l) },
                    False => PartScanRangeL pivot lo k' i (S g) l }))
            (Len l)) {
          True => elim g return (λ (gz : Nat). Id Nat
                    (Len (elim gz return (λ (gy : Nat). List Nat) {
                            Z => PartScanRangeL pivot lo k' (S i) Z l,
                            S (g') gih => PartScanRangeL pivot lo k' (S i) (S g') (SwapL (Add lo (S i)) (Add lo (S (Add i g))) l) }))
                    (Len l)) {
            Z => ih (S i) Z l,
            S (g') gih => IdTrans Nat
                   (Len (PartScanRangeL pivot lo k' (S i) (S g') (SwapL (Add lo (S i)) (Add lo (S (Add i g))) l)))
                   (Len (SwapL (Add lo (S i)) (Add lo (S (Add i g))) l))
                   (Len l)
                   (ih (S i) (S g') (SwapL (Add lo (S i)) (Add lo (S (Add i g))) l))
                   (LenSwapL (Add lo (S i)) (Add lo (S (Add i g))) l)
          },
          False => ih i (S g) l
        }
    } }
def LenPartScanRangeLTy : Term := prog{ Π (pivot : Nat) → Π (lo : Nat) → Π (k : Nat) → Π (i : Nat) → Π (g : Nat) → Π (l : List Nat) →
  Id Nat (Len (PartScanRangeL pivot lo k i g l)) (Len l) }

-- The wrapper form the quicksort recursion consumes: PartitionRangeL is
-- PartScanRangeL after picking the pivot, so its length preservation is the scan's
-- (Z base is Refl, S cnt' is LenPartScanRangeL at the entry offsets).
def LenPartitionRangeL : Term := prog{
  λ (lo : Nat). λ (cnt : Nat). λ (l : List Nat).
    elim cnt return (λ (cz : Nat). Id Nat
        (Len (elim cz return (λ (cy : Nat). List Nat) { Z => l, S (cnt') rec => PartScanRangeL (NthL lo l) lo cnt' Z Z l }))
        (Len l)) {
      Z => Refl,
      S (cnt') rec => LenPartScanRangeL (NthL lo l) lo cnt' Z Z l } }
def LenPartitionRangeLTy : Term := prog{ Π (lo : Nat) → Π (cnt : Nat) → Π (l : List Nat) → Id Nat (Len (PartitionRangeL lo cnt l)) (Len l) }

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
  λ (pivot : Nat). λ (lo : Nat). λ (m : Nat). λ (k : Nat).
    elim k return (λ (kz : Nat). Π (i : Nat) → Π (g : Nat) → Π (l : List Nat) →
        Le (Add lo (S (Add kz (Add i g)))) (Len l) →
        Id Nat (Count m (PartScanRangeL pivot lo kz i g l)) (Count m l)) {
      Z => λ (i : Nat). λ (g : Nat). λ (l : List Nat).
        elim i return (λ (iz : Nat).
            Le (Add lo (S (Add Z (Add iz g)))) (Len l) →
            Id Nat (Count m (elim iz return (λ (iy : Nat). List Nat) {
                Z => l, S (i') iih => SwapL lo (Add lo (S i')) l })) (Count m l)) {
          Z => λ (hle : Le (Add lo (S (Add Z (Add Z g)))) (Len l)). Refl,
          S (i') iih => λ (hle : Le (Add lo (S (Add Z (Add (S i') g)))) (Len l)).
            CountSwapL' m lo (Add lo (S i')) l (LeAddSucc lo i')
              (LeTrans (S (Add lo (S i'))) (Add lo (S (S (Add i' g)))) (Len l)
                (LeRwL (Add lo (S (S (Add i' g)))) (Add lo (S (S i'))) (S (Add lo (S i')))
                  (AddSucc lo (S i'))
                  (LeAddMonoL lo (S (S i')) (S (S (Add i' g))) (LeAdd i' g)))
                hle)
        },
      S (k') ih => λ (i : Nat). λ (g : Nat). λ (l : List Nat).
        λ (hle : Le (Add lo (S (Add (S k') (Add i g)))) (Len l)).
        elim (Leb (NthL (Add lo (S (Add i g))) l) pivot)
          return (λ (w : Bool). Id Nat
            (Count m (elim w return (λ (ww : Bool). List Nat) {
                True => elim g return (λ (gz : Nat). List Nat) {
                  Z => PartScanRangeL pivot lo k' (S i) Z l,
                  S (g') gih => PartScanRangeL pivot lo k' (S i) (S g') (SwapL (Add lo (S i)) (Add lo (S (Add i g))) l) },
                False => PartScanRangeL pivot lo k' i (S g) l }))
            (Count m l)) {
          True =>
            (elim g return (λ (gz : Nat).
                Le (Add lo (S (Add (S k') (Add i gz)))) (Len l) →
                Id Nat (Count m (elim gz return (λ (gy : Nat). List Nat) {
                    Z => PartScanRangeL pivot lo k' (S i) Z l,
                    S (g') gih => PartScanRangeL pivot lo k' (S i) (S g') (SwapL (Add lo (S i)) (Add lo (S (Add i gz))) l) })) (Count m l)) {
              Z => λ (hleZ : Le (Add lo (S (Add (S k') (Add i Z)))) (Len l)).
                ih (S i) Z l
                  (LeRwL (Len l)
                    (Add lo (S (Add (S k') (Add i Z))))
                    (Add lo (S (Add k' (Add (S i) Z))))
                    (IdCongr Nat Nat (λ (a : Nat). Add lo (S a))
                      (Add (S k') (Add i Z)) (Add k' (Add (S i) Z)) (HshiftTrue k' i Z))
                    hleZ),
              S (g') gih => λ (hleS : Le (Add lo (S (Add (S k') (Add i (S g'))))) (Len l)).
                IdTrans Nat
                  (Count m (PartScanRangeL pivot lo k' (S i) (S g') (SwapL (Add lo (S i)) (Add lo (S (Add i (S g')))) l)))
                  (Count m (SwapL (Add lo (S i)) (Add lo (S (Add i (S g')))) l))
                  (Count m l)
                  (ih (S i) (S g') (SwapL (Add lo (S i)) (Add lo (S (Add i (S g')))) l)
                    (LeRwR (Add lo (S (Add k' (Add (S i) (S g'))))) (Len l)
                       (Len (SwapL (Add lo (S i)) (Add lo (S (Add i (S g')))) l))
                       (IdSym Nat (Len (SwapL (Add lo (S i)) (Add lo (S (Add i (S g')))) l)) (Len l)
                         (LenSwapL (Add lo (S i)) (Add lo (S (Add i (S g')))) l))
                       (LeRwL (Len l)
                         (Add lo (S (Add (S k') (Add i (S g')))))
                         (Add lo (S (Add k' (Add (S i) (S g')))))
                         (IdCongr Nat Nat (λ (a : Nat). Add lo (S a))
                           (Add (S k') (Add i (S g'))) (Add k' (Add (S i) (S g'))) (HshiftTrue k' i (S g')))
                         hleS)))
                  (CountSwapL' m (Add lo (S i)) (Add lo (S (Add i (S g')))) l
                    (LeRwL (Add lo (S (Add i (S g')))) (Add lo (S (S i))) (S (Add lo (S i)))
                      (AddSucc lo (S i))
                      (LeAddMonoL lo (S (S i)) (S (Add i (S g'))) (LeAddSucc i g')))
                    (LeTrans (S (Add lo (S (Add i (S g'))))) (Add lo (S (S (Add k' (Add i (S g')))))) (Len l)
                      (LeRwL (Add lo (S (S (Add k' (Add i (S g'))))))
                        (Add lo (S (S (Add i (S g'))))) (S (Add lo (S (Add i (S g')))))
                        (AddSucc lo (S (Add i (S g'))))
                        (LeAddMonoL lo (S (S (Add i (S g')))) (S (S (Add k' (Add i (S g')))))
                          (LeAddL (Add i (S g')) k')))
                      hleS))
            }) hle,
          False =>
            ih i (S g) l
              (LeRwL (Len l)
                (Add lo (S (Add (S k') (Add i g))))
                (Add lo (S (Add k' (Add i (S g)))))
                (IdCongr Nat Nat (λ (a : Nat). Add lo (S a))
                  (Add (S k') (Add i g)) (Add k' (Add i (S g))) (HshiftFalse k' i g))
                hle)
        }
    } }
def CountPartScanRangeLTy : Term := prog{
  Π (pivot : Nat) → Π (lo : Nat) → Π (m : Nat) → Π (k : Nat) → Π (i : Nat) → Π (g : Nat) → Π (l : List Nat) →
    Le (Add lo (S (Add k (Add i g)))) (Len l) →
    Id Nat (Count m (PartScanRangeL pivot lo k i g l)) (Count m l) }

-- Wrapper: PartitionRangeL is PartScanRangeL after picking the pivot, so count
-- preservation is the scan's (Z base Refl, S cnt' is the scan at entry offsets).
-- The top range bound `Le (Add lo cnt) (Len l)` supplies the scan's bound; at
-- cnt = S cnt' it needs an AddZero nudge (`Add cnt' (Add Z Z) = Add cnt' Z`, and
-- `Add` recurses on its FIRST arg so `Add cnt' Z` is stuck at a free cnt').
def CountPartitionRangeL : Term := prog{
  λ (lo : Nat). λ (m : Nat). λ (cnt : Nat). λ (l : List Nat).
    elim cnt return (λ (cz : Nat).
        Le (Add lo cz) (Len l) →
        Id Nat (Count m (elim cz return (λ (cy : Nat). List Nat) {
            Z => l, S (cnt') rec => PartScanRangeL (NthL lo l) lo cnt' Z Z l })) (Count m l)) {
      Z => λ (hb : Le (Add lo Z) (Len l)). Refl,
      S (cnt') rec => λ (hb : Le (Add lo (S cnt')) (Len l)).
        CountPartScanRangeL (NthL lo l) lo m cnt' Z Z l
          (LeRwL (Len l) (Add lo (S cnt')) (Add lo (S (Add cnt' Z)))
            (IdCongr Nat Nat (λ (a : Nat). Add lo (S a)) cnt' (Add cnt' Z)
              (IdSym Nat (Add cnt' Z) cnt' (AddZero cnt')))
            hb) } }
def CountPartitionRangeLTy : Term := prog{
  Π (lo : Nat) → Π (m : Nat) → Π (cnt : Nat) → Π (l : List Nat) →
    Le (Add lo cnt) (Len l) → Id Nat (Count m (PartitionRangeL lo cnt l)) (Count m l) }

/-- `SortRangeL fuel lo cnt l` — sort the `cnt` elements of `l` at offset `lo` in
    place. Fuel-structural; base = out of fuel or `cnt ≤ 1`; step partitions the
    range, then sorts the left sub-range `[lo, lo+i)` (count `i`) and the right
    `[lo+i+1, …)` (count `g`), the right on the result of the left — the raw
    composition the imperative body implements. `partitionQ` is the `lo = 0` slice. -/
def SortRangeL : Term := prog{
  λ (fuel : Nat).
    elim fuel return (λ (fz : Nat). Π (lo : Nat) → Π (cnt : Nat) → List Nat → List Nat) {
      Z => λ (lo : Nat). λ (cnt : Nat). λ (l : List Nat). l,
      S (f') rec => λ (lo : Nat). λ (cnt : Nat). λ (l : List Nat).
        elim cnt return (λ (cz : Nat). List Nat) {
          Z => l,
          S (cnt') nih => elim cnt' return (λ (mz : Nat). List Nat) {
            Z => l,
            S (cnt'') n2ih =>
              let p = PartitionRangeL lo cnt l;
              let i = PartIdxRangeL lo cnt l;
              let g = PartGapRangeL lo cnt l;
              rec (S (Add lo i)) g (rec lo i p)
          } } } }
def SortRangeLTy : Term := prog{ Π (fuel : Nat) → Π (lo : Nat) → Π (cnt : Nat) → List Nat → List Nat }

-- SortRangeL is a permutation, so it preserves length. Fuel-structural induction
-- mirroring sortRangeL's own shape (base fuel Z / cnt ≤ 1 are Refl); the step is
-- the IH applied to each of the two recursive sorts, chained onto
-- LenPartitionRangeL for the partition underneath. The quicksort recursion needs
-- this for its SECOND range bound: the second recursive call runs after the first
-- has permuted *v, so the bound (over len *v-after-first) moves back through this.
def LenSortRangeL : Term := prog{
  λ (fuel : Nat).
    elim fuel return (λ (fz : Nat). Π (lo : Nat) → Π (cnt : Nat) → Π (l : List Nat) → Id Nat (Len (SortRangeL fz lo cnt l)) (Len l)) {
      Z => λ (lo : Nat). λ (cnt : Nat). λ (l : List Nat). Refl,
      S (f') ih => λ (lo : Nat). λ (cnt : Nat). λ (l : List Nat).
        elim cnt return (λ (cz : Nat). Id Nat (Len (elim cz return (λ (cy : Nat). List Nat) {
              Z => l,
              S (cnt') nih => elim cnt' return (λ (my : Nat). List Nat) {
                Z => l,
                S (cnt'') n2ih => SortRangeL f' (S (Add lo (PartIdxRangeL lo cnt l))) (PartGapRangeL lo cnt l) (SortRangeL f' lo (PartIdxRangeL lo cnt l) (PartitionRangeL lo cnt l)) } })) (Len l)) {
          Z => Refl,
          S (cnt') nih => elim cnt' return (λ (my : Nat). Id Nat (Len (elim my return (λ (myy : Nat). List Nat) {
                Z => l,
                S (cnt'') n2ih => SortRangeL f' (S (Add lo (PartIdxRangeL lo cnt l))) (PartGapRangeL lo cnt l) (SortRangeL f' lo (PartIdxRangeL lo cnt l) (PartitionRangeL lo cnt l)) })) (Len l)) {
            Z => Refl,
            S (cnt'') n2ih =>
              IdTrans Nat
                (Len (SortRangeL f' (S (Add lo (PartIdxRangeL lo cnt l))) (PartGapRangeL lo cnt l) (SortRangeL f' lo (PartIdxRangeL lo cnt l) (PartitionRangeL lo cnt l))))
                (Len (SortRangeL f' lo (PartIdxRangeL lo cnt l) (PartitionRangeL lo cnt l)))
                (Len l)
                (ih (S (Add lo (PartIdxRangeL lo cnt l))) (PartGapRangeL lo cnt l) (SortRangeL f' lo (PartIdxRangeL lo cnt l) (PartitionRangeL lo cnt l)))
                (IdTrans Nat
                  (Len (SortRangeL f' lo (PartIdxRangeL lo cnt l) (PartitionRangeL lo cnt l)))
                  (Len (PartitionRangeL lo cnt l))
                  (Len l)
                  (ih lo (PartIdxRangeL lo cnt l) (PartitionRangeL lo cnt l))
                  (LenPartitionRangeL lo cnt l))
          } } } }
def LenSortRangeLTy : Term := prog{ Π (fuel : Nat) → Π (lo : Nat) → Π (cnt : Nat) → Π (l : List Nat) → Id Nat (Len (SortRangeL fuel lo cnt l)) (Len l) }

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
  λ (lo : Nat). λ (cnt'' : Nat). λ (l : List Nat). λ (hb : Le (Add lo (S (S cnt''))) (Len l)).
    LeRwR (Add lo (PartIdxRangeL lo (S (S cnt'')) l)) (Len l) (Len (PartitionRangeL lo (S (S cnt'')) l))
      (IdSym Nat (Len (PartitionRangeL lo (S (S cnt'')) l)) (Len l)
        (LenPartitionRangeL lo (S (S cnt'')) l))
      (LeTrans (Add lo (PartIdxRangeL lo (S (S cnt'')) l)) (Add lo (S (S cnt''))) (Len l)
        (LeRwR (Add lo (PartIdxRangeL lo (S (S cnt'')) l))
          (Add lo (S (Add (PartIdxRangeL lo (S (S cnt'')) l) (PartGapRangeL lo (S (S cnt'')) l))))
          (Add lo (S (S cnt'')))
          (IdCongr Nat Nat (λ (a : Nat). Add lo a)
            (S (Add (PartIdxRangeL lo (S (S cnt'')) l) (PartGapRangeL lo (S (S cnt'')) l))) (S (S cnt''))
            (IdCongr Nat Nat (λ (a : Nat). S a)
              (Add (PartIdxRangeL lo (S (S cnt'')) l) (PartGapRangeL lo (S (S cnt'')) l)) (S cnt'')
              (IdTrans Nat (Add (PartIdxRangeL lo (S (S cnt'')) l) (PartGapRangeL lo (S (S cnt'')) l))
                (S (Add cnt'' Z)) (S cnt'')
                (PartScanSizeL (NthL lo l) lo (S cnt'') Z Z l)
                (IdCongr Nat Nat (λ (a : Nat). S a) (Add cnt'' Z) cnt'' (AddZero cnt'')))))
          (LeAddMonoL lo (PartIdxRangeL lo (S (S cnt'')) l)
            (S (Add (PartIdxRangeL lo (S (S cnt'')) l) (PartGapRangeL lo (S (S cnt'')) l)))
            (LeUpR (PartIdxRangeL lo (S (S cnt'')) l)
              (Add (PartIdxRangeL lo (S (S cnt'')) l) (PartGapRangeL lo (S (S cnt'')) l))
              (LeAdd (PartIdxRangeL lo (S (S cnt'')) l) (PartGapRangeL lo (S (S cnt'')) l)))))
        hb) }
def SortRangeBLTy : Term := prog{
  Π (lo : Nat) → Π (cnt'' : Nat) → Π (l : List Nat) → Le (Add lo (S (S cnt''))) (Len l) →
    Le (Add lo (PartIdxRangeL lo (S (S cnt'')) l)) (Len (PartitionRangeL lo (S (S cnt'')) l)) }

-- Right sub-range bound: `Le (Add (S (Add lo i)) g) (Len (sort left (partition …)))`.
-- Lifted verbatim from the quicksort FnDef's `br` (LenSortRangeL then
-- LenPartitionRangeL move the bound back over both mutations; the arithmetic
-- `Add (S (Add lo i)) g = Add lo (S (i+g)) = Add lo cnt` uses AddAssoc/AddSucc).
def SortRangeBR : Term := prog{
  λ (f' : Nat). λ (lo : Nat). λ (cnt'' : Nat). λ (l : List Nat). λ (hb : Le (Add lo (S (S cnt''))) (Len l)).
    LeRwR (Add (S (Add lo (PartIdxRangeL lo (S (S cnt'')) l))) (PartGapRangeL lo (S (S cnt'')) l)) (Len l)
      (Len (SortRangeL f' lo (PartIdxRangeL lo (S (S cnt'')) l) (PartitionRangeL lo (S (S cnt'')) l)))
      (IdSym Nat (Len (SortRangeL f' lo (PartIdxRangeL lo (S (S cnt'')) l) (PartitionRangeL lo (S (S cnt'')) l))) (Len l)
        (IdTrans Nat (Len (SortRangeL f' lo (PartIdxRangeL lo (S (S cnt'')) l) (PartitionRangeL lo (S (S cnt'')) l)))
          (Len (PartitionRangeL lo (S (S cnt'')) l)) (Len l)
          (LenSortRangeL f' lo (PartIdxRangeL lo (S (S cnt'')) l) (PartitionRangeL lo (S (S cnt'')) l))
          (LenPartitionRangeL lo (S (S cnt'')) l)))
      (LeRwL (Len l) (Add lo (S (S cnt'')))
        (Add (S (Add lo (PartIdxRangeL lo (S (S cnt'')) l))) (PartGapRangeL lo (S (S cnt'')) l))
        (IdSym Nat (Add (S (Add lo (PartIdxRangeL lo (S (S cnt'')) l))) (PartGapRangeL lo (S (S cnt'')) l)) (Add lo (S (S cnt'')))
          (IdTrans Nat (Add (S (Add lo (PartIdxRangeL lo (S (S cnt'')) l))) (PartGapRangeL lo (S (S cnt'')) l))
            (S (Add lo (Add (PartIdxRangeL lo (S (S cnt'')) l) (PartGapRangeL lo (S (S cnt'')) l)))) (Add lo (S (S cnt'')))
            (IdCongr Nat Nat (λ (a : Nat). S a)
              (Add (Add lo (PartIdxRangeL lo (S (S cnt'')) l)) (PartGapRangeL lo (S (S cnt'')) l))
              (Add lo (Add (PartIdxRangeL lo (S (S cnt'')) l) (PartGapRangeL lo (S (S cnt'')) l)))
              (AddAssoc lo (PartIdxRangeL lo (S (S cnt'')) l) (PartGapRangeL lo (S (S cnt'')) l)))
            (IdTrans Nat (S (Add lo (Add (PartIdxRangeL lo (S (S cnt'')) l) (PartGapRangeL lo (S (S cnt'')) l))))
              (Add lo (S (Add (PartIdxRangeL lo (S (S cnt'')) l) (PartGapRangeL lo (S (S cnt'')) l)))) (Add lo (S (S cnt'')))
              (IdSym Nat (Add lo (S (Add (PartIdxRangeL lo (S (S cnt'')) l) (PartGapRangeL lo (S (S cnt'')) l))))
                (S (Add lo (Add (PartIdxRangeL lo (S (S cnt'')) l) (PartGapRangeL lo (S (S cnt'')) l))))
                (AddSucc lo (Add (PartIdxRangeL lo (S (S cnt'')) l) (PartGapRangeL lo (S (S cnt'')) l))))
              (IdCongr Nat Nat (λ (a : Nat). Add lo a)
                (S (Add (PartIdxRangeL lo (S (S cnt'')) l) (PartGapRangeL lo (S (S cnt'')) l))) (S (S cnt''))
                (IdCongr Nat Nat (λ (a : Nat). S a)
                  (Add (PartIdxRangeL lo (S (S cnt'')) l) (PartGapRangeL lo (S (S cnt'')) l)) (S cnt'')
                  (IdTrans Nat (Add (PartIdxRangeL lo (S (S cnt'')) l) (PartGapRangeL lo (S (S cnt'')) l))
                    (S (Add cnt'' Z)) (S cnt'')
                    (PartScanSizeL (NthL lo l) lo (S cnt'') Z Z l)
                    (IdCongr Nat Nat (λ (a : Nat). S a) (Add cnt'' Z) cnt'' (AddZero cnt''))))))))
        hb) }
def SortRangeBRTy : Term := prog{
  Π (f' : Nat) → Π (lo : Nat) → Π (cnt'' : Nat) → Π (l : List Nat) → Le (Add lo (S (S cnt''))) (Len l) →
    Le (Add (S (Add lo (PartIdxRangeL lo (S (S cnt'')) l))) (PartGapRangeL lo (S (S cnt'')) l))
       (Len (SortRangeL f' lo (PartIdxRangeL lo (S (S cnt'')) l) (PartitionRangeL lo (S (S cnt'')) l))) }

def CountSortRangeL : Term := prog{
  λ (m : Nat). λ (fuel : Nat).
    elim fuel return (λ (fz : Nat). Π (lo : Nat) → Π (cnt : Nat) → Π (l : List Nat) →
        Le (Add lo cnt) (Len l) → Id Nat (Count m (SortRangeL fz lo cnt l)) (Count m l)) {
      Z => λ (lo : Nat). λ (cnt : Nat). λ (l : List Nat). λ (hb : Le (Add lo cnt) (Len l)). Refl,
      S (f') ih => λ (lo : Nat). λ (cnt : Nat). λ (l : List Nat).
        elim cnt return (λ (cz : Nat). Le (Add lo cz) (Len l) →
            Id Nat (Count m (SortRangeL (S f') lo cz l)) (Count m l)) {
          Z => λ (hb : Le (Add lo Z) (Len l)). Refl,
          S (cnt') nih => elim cnt' return (λ (cz' : Nat). Le (Add lo (S cz')) (Len l) →
              Id Nat (Count m (SortRangeL (S f') lo (S cz') l)) (Count m l)) {
            Z => λ (hb : Le (Add lo (S Z)) (Len l)). Refl,
            S (cnt'') n2ih => λ (hb : Le (Add lo (S (S cnt''))) (Len l)).
              IdTrans Nat
                (Count m (SortRangeL f' (S (Add lo (PartIdxRangeL lo (S (S cnt'')) l))) (PartGapRangeL lo (S (S cnt'')) l)
                          (SortRangeL f' lo (PartIdxRangeL lo (S (S cnt'')) l) (PartitionRangeL lo (S (S cnt'')) l))))
                (Count m (SortRangeL f' lo (PartIdxRangeL lo (S (S cnt'')) l) (PartitionRangeL lo (S (S cnt'')) l)))
                (Count m l)
                (ih (S (Add lo (PartIdxRangeL lo (S (S cnt'')) l))) (PartGapRangeL lo (S (S cnt'')) l)
                    (SortRangeL f' lo (PartIdxRangeL lo (S (S cnt'')) l) (PartitionRangeL lo (S (S cnt'')) l))
                    (SortRangeBR f' lo cnt'' l hb))
                (IdTrans Nat
                  (Count m (SortRangeL f' lo (PartIdxRangeL lo (S (S cnt'')) l) (PartitionRangeL lo (S (S cnt'')) l)))
                  (Count m (PartitionRangeL lo (S (S cnt'')) l))
                  (Count m l)
                  (ih lo (PartIdxRangeL lo (S (S cnt'')) l) (PartitionRangeL lo (S (S cnt'')) l)
                      (SortRangeBL lo cnt'' l hb))
                  (CountPartitionRangeL lo m (S (S cnt'')) l hb))
          }
        }
    } }
def CountSortRangeLTy : Term := prog{
  Π (m : Nat) → Π (fuel : Nat) → Π (lo : Nat) → Π (cnt : Nat) → Π (l : List Nat) →
    Le (Add lo cnt) (Len l) → Id Nat (Count m (SortRangeL fuel lo cnt l)) (Count m l) }

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
  λ (w : Nat). λ (lo : Nat). λ (p : Nat). λ (l : List Nat).
    Π (k : Nat) → Le (S k) w → Le (NthL (Add k lo) l) p }
def AllGtR : Term := prog{
  λ (w : Nat). λ (lo : Nat). λ (p : Nat). λ (l : List Nat).
    Π (k : Nat) → Le (S k) w → Le (S p) (NthL (Add k lo) l) }

-- Head extraction: a width-(S w) AllLeR gives the bound at position lo (apply at
-- k=Z; Le (S Z)(S w) whnf's to ⊤, discharged by `unit`; add Z lo = lo).
def AllLeRHead : Term := prog{
  λ (w : Nat). λ (lo : Nat). λ (p : Nat). λ (l : List Nat). λ (h : AllLeR (S w) lo p l).
    h Z unit }
def AllLeRHeadTy : Term := prog{
  Π (w : Nat) → Π (lo : Nat) → Π (p : Nat) → Π (l : List Nat) →
    AllLeR (S w) lo p l → Le (NthL lo l) p }
def AllGtRHead : Term := prog{
  λ (w : Nat). λ (lo : Nat). λ (p : Nat). λ (l : List Nat). λ (h : AllGtR (S w) lo p l).
    h Z unit }
def AllGtRHeadTy : Term := prog{
  Π (w : Nat) → Π (lo : Nat) → Π (p : Nat) → Π (l : List Nat) →
    AllGtR (S w) lo p l → Le (S p) (NthL lo l) }

-- The empty range is vacuously bounded (Le (S k) Z = ⊥ ⇒ botElim).
def AllLeREmpty : Term := prog{
  λ (lo : Nat). λ (p : Nat). λ (l : List Nat).
    λ (k : Nat). λ (hk : Le (S k) Z). botElim (Le (NthL (Add k lo) l) p) hk }
def AllLeREmptyTy : Term := prog{
  Π (lo : Nat) → Π (p : Nat) → Π (l : List Nat) → AllLeR Z lo p l }
def AllGtREmpty : Term := prog{
  λ (lo : Nat). λ (p : Nat). λ (l : List Nat).
    λ (k : Nat). λ (hk : Le (S k) Z). botElim (Le (S p) (NthL (Add k lo) l)) hk }
def AllGtREmptyTy : Term := prog{
  Π (lo : Nat) → Π (p : Nat) → Π (l : List Nat) → AllGtR Z lo p l }

/-! ## Segment count — the multiset vehicle for perm-survival (§22, M22-c step 3)

    `SegCount x lo w l` = occurrences of x in positions [lo, lo+w) of l, as the count
    over the take/drop segment (reuses count/take/drop; preservation cribs count_* +
    CountAppend + TakeDropId). This is the perm-invariant twin the positional
    AllLeR is bridged to: the sort permutes the segment (SegCount preserved), so a
    positional bound over the segment survives the sort. Its preservation-under-the-
    model-functions and the model-function LOCALITY lemmas are the mechanical stratum. -/
def SegCount : Term := prog{
  λ (x : Nat). λ (lo : Nat). λ (w : Nat). λ (l : List Nat).
    Count x (Take w (Drop lo l)) }
def SegCountTy : Term := prog{ Π (x : Nat) → Π (lo : Nat) → Π (w : Nat) → Π (l : List Nat) → Nat }

/-! ## Range sortedness (§22, M22-c step 4)

    SortedR w lo l: positions [lo, lo+w) are non-decreasing — for every adjacent pair
    (k, k+1) both inside the range (S(S k) ≤ w), nth(lo+k) ≤ nth(lo+k+1). Bounded-Π,
    same encoding as AllLeR/AllGtR (eliminate by application, construct by lambda;
    `Add k lo` / `Add (S k) lo` so k=0 reduces to nth lo / nth (S lo)). Width ≤ 1 is
    vacuously sorted. The glue lemma (SortedR left ∧ AllLeR left≤pivot ∧ AllGtR right>pivot
    ∧ SortedR right ⟹ SortedR whole) assembles on these; then SortedSortRangeL. -/
def SortedR : Term := prog{
  λ (w : Nat). λ (lo : Nat). λ (l : List Nat).
    Π (k : Nat) → Le (S (S k)) w → Le (NthL (Add k lo) l) (NthL (Add (S k) lo) l) }

-- Head adjacent-bound from a width-(S (S w)) SortedR (apply at k=Z).
def SortedRHead : Term := prog{
  λ (w : Nat). λ (lo : Nat). λ (l : List Nat). λ (h : SortedR (S (S w)) lo l).
    h Z unit }
def SortedRHeadTy : Term := prog{
  Π (w : Nat) → Π (lo : Nat) → Π (l : List Nat) →
    SortedR (S (S w)) lo l → Le (NthL lo l) (NthL (S lo) l) }

-- Width 0 and width 1 are vacuously sorted (Le (S (S k)) (Z / S Z) = ⊥ ⇒ botElim).
def SortedRZero : Term := prog{
  λ (lo : Nat). λ (l : List Nat).
    λ (k : Nat). λ (hk : Le (S (S k)) Z). botElim (Le (NthL (Add k lo) l) (NthL (Add (S k) lo) l)) hk }
def SortedRZeroTy : Term := prog{
  Π (lo : Nat) → Π (l : List Nat) → SortedR Z lo l }
def SortedROne : Term := prog{
  λ (lo : Nat). λ (l : List Nat).
    λ (k : Nat). λ (hk : Le (S (S k)) (S Z)). botElim (Le (NthL (Add k lo) l) (NthL (Add (S k) lo) l)) hk }
def SortedROneTy : Term := prog{
  Π (lo : Nat) → Π (l : List Nat) → SortedR (S Z) lo l }

/-! ## leb ↔ Le bridges (§22, M22-c) — the Bool-comparison / order-proposition link

    The model functions branch on `Leb` (a Bool); the predicates carry `Le` (a
    proposition). These bridge the two — needed both for the partition INVARIANT
    (the scan's leb tests become AllLeR/AllGtR facts) and the GLUE (its k-vs-i
    trichotomy is a leb case-split whose branches yield the Le adjacency facts).
    `Leb` and `Le` share the same double recursion, so each bridge is a double
    induction with a Bool-DISCRIMINATE at the mismatched base (BoolFT/BoolTF:
    False ≠ True, by transporting `unit` along the false equation to `⊥`). -/
def BoolFT : Term := prog{
  λ (h : Id Bool False True).
    j Bool False (λ (y' : Bool). λ (hh : Id Bool False y'). elim y' return (λ (z : Bool). Type) { True => Bot, False => Unit })
      unit True h }
def BoolFTTy : Term := prog{ Id Bool False True → Bot }
def BoolTF : Term := prog{
  λ (h : Id Bool True False).
    j Bool True (λ (y' : Bool). λ (hh : Id Bool True y'). elim y' return (λ (z : Bool). Type) { True => Unit, False => Bot })
      unit False h }
def BoolTFTy : Term := prog{ Id Bool True False → Bot }

def LebTrueLe : Term := prog{
  λ (a : Nat).
    elim a return (λ (az : Nat). Π (b : Nat) → Id Bool (Leb az b) True → Le az b) {
      Z => λ (b : Nat). λ (h : Id Bool (Leb Z b) True). unit,
      S (a') ih => λ (b : Nat).
        elim b return (λ (bz : Nat). Id Bool (Leb (S a') bz) True → Le (S a') bz) {
          Z => λ (h : Id Bool (Leb (S a') Z) True). botElim (Le (S a') Z) (BoolFT h),
          S (b') ihb => λ (h : Id Bool (Leb (S a') (S b')) True). ih b' h } } }
def LebTrueLeTy : Term := prog{ Π (a : Nat) → Π (b : Nat) → Id Bool (Leb a b) True → Le a b }

def LebFalseGt : Term := prog{
  λ (a : Nat).
    elim a return (λ (az : Nat). Π (b : Nat) → Id Bool (Leb az b) False → Le (S b) az) {
      Z => λ (b : Nat). λ (h : Id Bool (Leb Z b) False). botElim (Le (S b) Z) (BoolTF h),
      S (a') ih => λ (b : Nat).
        elim b return (λ (bz : Nat). Id Bool (Leb (S a') bz) False → Le (S bz) (S a')) {
          Z => λ (h : Id Bool (Leb (S a') Z) False). unit,
          S (b') ihb => λ (h : Id Bool (Leb (S a') (S b')) False). ih b' h } } }
def LebFalseGtTy : Term := prog{ Π (a : Nat) → Π (b : Nat) → Id Bool (Leb a b) False → Le (S b) a }

-- Nat antisymmetry (Le a b → Le b a → a = b) — the glue derives its boundary equality
-- (`S k = i` at the last-left/pivot pair) from the two-sided Le bounds a leb-split
-- yields. Double induction; mixed-parity bases are ⊥, equal-parity step is IdCongr S.
def LeAntisym : Term := prog{
  λ (a : Nat).
    elim a return (λ (az : Nat). Π (b : Nat) → Le az b → Le b az → Id Nat az b) {
      Z => λ (b : Nat).
        elim b return (λ (bz : Nat). Le Z bz → Le bz Z → Id Nat Z bz) {
          Z => λ (h1 : Le Z Z). λ (h2 : Le Z Z). Refl,
          S (b') ihb => λ (h1 : Le Z (S b')). λ (h2 : Le (S b') Z). botElim (Id Nat Z (S b')) h2 },
      S (a') ih => λ (b : Nat).
        elim b return (λ (bz : Nat). Le (S a') bz → Le bz (S a') → Id Nat (S a') bz) {
          Z => λ (h1 : Le (S a') Z). λ (h2 : Le Z (S a')). botElim (Id Nat (S a') Z) h1,
          S (b') ihb => λ (h1 : Le (S a') (S b')). λ (h2 : Le (S b') (S a')).
            IdCongr Nat Nat (λ (n : Nat). S n) a' b' (ih b' h1 h2) } } }
def LeAntisymTy : Term := prog{ Π (a : Nat) → Π (b : Nat) → Le a b → Le b a → Id Nat a b }

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
  λ (w : Nat). λ (lo : Nat). λ (p : Nat). λ (l : List Nat).
    λ (h : AllLeR w lo p l). λ (hnew : Le (NthL (Add w lo) l) p).
    λ (m : Nat).
      elim (Leb (S m) w) return (λ (b : Bool). Id Bool (Leb (S m) w) b → Le (S m) (S w) → Le (NthL (Add m lo) l) p) {
        True => λ (e : Id Bool (Leb (S m) w) True). λ (hm : Le (S m) (S w)). h m (LebTrueLe (S m) w e),
        False => λ (e : Id Bool (Leb (S m) w) False). λ (hm : Le (S m) (S w)).
          LeRwL p (NthL (Add w lo) l) (NthL (Add m lo) l)
            (IdCongr Nat Nat (λ (q : Nat). NthL q l) (Add w lo) (Add m lo)
              (IdCongr Nat Nat (λ (z : Nat). Add z lo) w m (IdSym Nat m w (LeAntisym m w hm (LebFalseGt (S m) w e)))))
            hnew
      } Refl }
def AllLeRExtendFarTy : Term := prog{
  Π (w : Nat) → Π (lo : Nat) → Π (p : Nat) → Π (l : List Nat) →
    AllLeR w lo p l → Le (NthL (Add w lo) l) p → AllLeR (S w) lo p l }

def AllLeRExtendLo : Term := prog{
  λ (w : Nat). λ (lo : Nat). λ (p : Nat). λ (l : List Nat).
    λ (h0 : Le (NthL lo l) p). λ (h : AllLeR w (S lo) p l).
    λ (m : Nat).
      elim m return (λ (mz : Nat). Le (S mz) (S w) → Le (NthL (Add mz lo) l) p) {
        Z => λ (hm : Le (S Z) (S w)). h0,
        S (m') mih => λ (hm : Le (S (S m')) (S w)).
          LeRwL p (NthL (Add m' (S lo)) l) (NthL (Add (S m') lo) l)
            (IdCongr Nat Nat (λ (q : Nat). NthL q l) (Add m' (S lo)) (Add (S m') lo) (AddSucc m' lo))
            (h m' hm) } }
def AllLeRExtendLoTy : Term := prog{
  Π (w : Nat) → Π (lo : Nat) → Π (p : Nat) → Π (l : List Nat) →
    Le (NthL lo l) p → AllLeR w (S lo) p l → AllLeR (S w) lo p l }

def AllLeRCong : Term := prog{
  λ (w : Nat). λ (off : Nat). λ (p : Nat). λ (l : List Nat). λ (l' : List Nat).
    λ (heq : Π (m : Nat) → Le (S m) w → Id Nat (NthL (Add m off) l') (NthL (Add m off) l)).
    λ (h : AllLeR w off p l).
    λ (m : Nat). λ (hm : Le (S m) w).
      LeRwL p (NthL (Add m off) l) (NthL (Add m off) l')
        (IdSym Nat (NthL (Add m off) l') (NthL (Add m off) l) (heq m hm))
        (h m hm) }
def AllLeRCongTy : Term := prog{
  Π (w : Nat) → Π (off : Nat) → Π (p : Nat) → Π (l : List Nat) → Π (l' : List Nat) →
    (Π (m : Nat) → Le (S m) w → Id Nat (NthL (Add m off) l') (NthL (Add m off) l)) →
    AllLeR w off p l → AllLeR w off p l' }

def AddSwapSucc : Term := prog{
  λ (a : Nat). λ (b : Nat).
    IdTrans Nat (Add a (S b)) (S (Add a b)) (Add b (S a))
      (AddSucc a b)
      (IdTrans Nat (S (Add a b)) (S (Add b a)) (Add b (S a))
        (IdCongr Nat Nat (λ (z : Nat). S z) (Add a b) (Add b a) (AddComm a b))
        (IdSym Nat (Add b (S a)) (S (Add b a)) (AddSucc b a))) }
def AddSwapSuccTy : Term := prog{ Π (a : Nat) → Π (b : Nat) → Id Nat (Add a (S b)) (Add b (S a)) }

-- Left cancellation (Le (add a b)(add a c) → Le b c) — the glue's pivot-right case
-- derives g ≥ 1 (Le (S Z) g) from the range bound Le (S i)(add i g) by cancelling i
-- (after bridging S i = add i (S Z) via AddSucc/AddZero). Induction on a.
def LeAddCancelL : Term := prog{
  λ (a : Nat).
    elim a return (λ (az : Nat). Π (b : Nat) → Π (c : Nat) → Le (Add az b) (Add az c) → Le b c) {
      Z => λ (b : Nat). λ (c : Nat). λ (h : Le (Add Z b) (Add Z c)). h,
      S (a') ih => λ (b : Nat). λ (c : Nat). λ (h : Le (Add (S a') b) (Add (S a') c)). ih b c h } }
def LeAddCancelLTy : Term := prog{
  Π (a : Nat) → Π (b : Nat) → Π (c : Nat) → Le (Add a b) (Add a c) → Le b c }
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
  λ (v : Nat). λ (j : Nat).
    elim j return (λ (jz : Nat). Π (k : Nat) → Π (l : List Nat) → Le (S jz) k → Id Nat (NthL k (Set jz v l)) (NthL k l)) {
      Z => λ (k : Nat). λ (l : List Nat). λ (h : Le (S Z) k).
        elim k return (λ (kz : Nat). Le (S Z) kz → Id Nat (NthL kz (Set Z v l)) (NthL kz l)) {
          Z => λ (h0 : Le (S Z) Z). botElim (Id Nat (NthL Z (Set Z v l)) (NthL Z l)) h0,
          S (k') kih => λ (h0 : Le (S Z) (S k')).
            elim l return (λ (lz : List Nat). Id Nat (NthL (S k') (Set Z v lz)) (NthL (S k') lz)) {
              Nil => Refl,
              Cons (hh) (tt) ihl => Refl } } h,
      S (j') ih => λ (k : Nat). λ (l : List Nat). λ (h : Le (S (S j')) k).
        elim k return (λ (kz : Nat). Le (S (S j')) kz → Id Nat (NthL kz (Set (S j') v l)) (NthL kz l)) {
          Z => λ (h0 : Le (S (S j')) Z). botElim (Id Nat (NthL Z (Set (S j') v l)) (NthL Z l)) h0,
          S (k') kih => λ (h0 : Le (S (S j')) (S k')).
            elim l return (λ (lz : List Nat). Id Nat (NthL (S k') (Set (S j') v lz)) (NthL (S k') lz)) {
              Nil => Refl,
              Cons (hh) (tt) ihl => ih k' tt h0 } } h } }
def NthSetGtTy : Term := prog{
  Π (v : Nat) → Π (j : Nat) → Π (k : Nat) → Π (l : List Nat) →
    Le (S j) k → Id Nat (NthL k (Set j v l)) (NthL k l) }

-- `NthL k (Set k v l) = v` when k is in range (off the end set no-ops, giving Z ≠ v).
def NthSetSame : Term := prog{
  λ (v : Nat). λ (k : Nat).
    elim k return (λ (kz : Nat). Π (l : List Nat) → Le (S kz) (Len l) → Id Nat (NthL kz (Set kz v l)) v) {
      Z => λ (l : List Nat).
        elim l return (λ (lz : List Nat). Le (S Z) (Len lz) → Id Nat (NthL Z (Set Z v lz)) v) {
          Nil => λ (h : Le (S Z) (Len Nil)). botElim (Id Nat (NthL Z (Set Z v Nil)) v) h,
          Cons (hh) (tt) ihl => λ (h : Le (S Z) (Len (Cons hh tt))). Refl },
      S (k') ih => λ (l : List Nat).
        elim l return (λ (lz : List Nat). Le (S (S k')) (Len lz) → Id Nat (NthL (S k') (Set (S k') v lz)) v) {
          Nil => λ (h : Le (S (S k')) (Len Nil)). botElim (Id Nat (NthL (S k') (Set (S k') v Nil)) v) h,
          Cons (hh) (tt) ihl => λ (h : Le (S (S k')) (Len (Cons hh tt))). ih tt h } } }
def NthSetSameTy : Term := prog{
  Π (v : Nat) → Π (k : Nat) → Π (l : List Nat) →
    Le (S k) (Len l) → Id Nat (NthL k (Set k v l)) v }

-- Locality below the swap: positions `k < i` are untouched by `SwapL i j`. Induct
-- on i (mirroring SwapL); i = Z is vacuous (Le (S k) Z = ⊥); the recursive leaf is
-- the IH under `Cons x ·`, the j = Z / head leaves are Refl.
def NthSwapLLt : Term := prog{
  λ (i : Nat).
    elim i return (λ (iz : Nat). Π (j : Nat) → Π (k : Nat) → Π (l : List Nat) → Le (S k) iz → Id Nat (NthL k (SwapL iz j l)) (NthL k l)) {
      Z => λ (j : Nat). λ (k : Nat). λ (l : List Nat). λ (h : Le (S k) Z).
        botElim (Id Nat (NthL k (SwapL Z j l)) (NthL k l)) h,
      S (i') ih => λ (j : Nat). λ (k : Nat). λ (l : List Nat). λ (h : Le (S k) (S i')).
        elim l return (λ (lz : List Nat). Id Nat (NthL k (SwapL (S i') j lz)) (NthL k lz)) {
          Nil => Refl,
          Cons (x) (xs) ihl =>
            elim j return (λ (jz : Nat). Id Nat (NthL k (SwapL (S i') jz (Cons x xs))) (NthL k (Cons x xs))) {
              Z => Refl,
              S (j') jih =>
                elim k return (λ (kz : Nat). Le (S kz) (S i') → Id Nat (NthL kz (Cons x (SwapL i' j' xs))) (NthL kz (Cons x xs))) {
                  Z => λ (h0 : Le (S Z) (S i')). Refl,
                  S (k') kih => λ (h0 : Le (S (S k')) (S i')). ih j' k' xs h0 } h } } } }
def NthSwapLLtTy : Term := prog{
  Π (i : Nat) → Π (j : Nat) → Π (k : Nat) → Π (l : List Nat) →
    Le (S k) i → Id Nat (NthL k (SwapL i j l)) (NthL k l) }

-- Locality above the swap: positions `k > j` are untouched by `SwapL i j`. Induct
-- on i; the i = Z / j = S j' leaf floats through the set-branch via `NthSetGt`,
-- the i = S i' / j = S j' leaf is the IH, the j = Z / Nil leaves are Refl.
def NthSwapLGt : Term := prog{
  λ (i : Nat).
    elim i return (λ (iz : Nat). Π (j : Nat) → Π (k : Nat) → Π (l : List Nat) → Le (S j) k → Id Nat (NthL k (SwapL iz j l)) (NthL k l)) {
      Z => λ (j : Nat). λ (k : Nat). λ (l : List Nat). λ (h : Le (S j) k).
        elim l return (λ (lz : List Nat). Id Nat (NthL k (SwapL Z j lz)) (NthL k lz)) {
          Nil => Refl,
          Cons (x) (xs) ihl =>
            elim j return (λ (jz : Nat). Le (S jz) k → Id Nat (NthL k (SwapL Z jz (Cons x xs))) (NthL k (Cons x xs))) {
              Z => λ (h0 : Le (S Z) k). Refl,
              S (j') jih => λ (h0 : Le (S (S j')) k).
                elim k return (λ (kz : Nat). Le (S (S j')) kz → Id Nat (NthL kz (Cons (NthL j' xs) (Set j' x xs))) (NthL kz (Cons x xs))) {
                  Z => λ (h1 : Le (S (S j')) Z). botElim (Id Nat (NthL Z (Cons (NthL j' xs) (Set j' x xs))) (NthL Z (Cons x xs))) h1,
                  S (k') kih => λ (h1 : Le (S (S j')) (S k')). NthSetGt x j' k' xs h1 } h0 } h },
      S (i') ih => λ (j : Nat). λ (k : Nat). λ (l : List Nat). λ (h : Le (S j) k).
        elim l return (λ (lz : List Nat). Id Nat (NthL k (SwapL (S i') j lz)) (NthL k lz)) {
          Nil => Refl,
          Cons (x) (xs) ihl =>
            elim j return (λ (jz : Nat). Le (S jz) k → Id Nat (NthL k (SwapL (S i') jz (Cons x xs))) (NthL k (Cons x xs))) {
              Z => λ (h0 : Le (S Z) k). Refl,
              S (j') jih => λ (h0 : Le (S (S j')) k).
                elim k return (λ (kz : Nat). Le (S (S j')) kz → Id Nat (NthL kz (Cons x (SwapL i' j' xs))) (NthL kz (Cons x xs))) {
                  Z => λ (h1 : Le (S (S j')) Z). botElim (Id Nat (NthL Z (Cons x (SwapL i' j' xs))) (NthL Z (Cons x xs))) h1,
                  S (k') kih => λ (h1 : Le (S (S j')) (S k')). ih j' k' xs h1 } h0 } h } } }
def NthSwapLGtTy : Term := prog{
  Π (i : Nat) → Π (j : Nat) → Π (k : Nat) → Π (l : List Nat) →
    Le (S j) k → Id Nat (NthL k (SwapL i j l)) (NthL k l) }

-- The lower endpoint: position i of `SwapL i j l` reads old position j. Induct on
-- i; the recursive leaf is the IH under `Cons x ·`. NO length bound — off the end
-- the swap writes `NthL j l = Z` at i, so both sides read Z consistently; the Nil
-- leaves case j so the stuck `NthL j Nil` reduces to Z on both sides, and the j = Z
-- leaf (impossible with i ≥ 1) is the sole botElim, discharged by `Le (S i) j`.
def NthSwapLLo : Term := prog{
  λ (i : Nat).
    elim i return (λ (iz : Nat). Π (j : Nat) → Π (l : List Nat) → Le (S iz) j → Id Nat (NthL iz (SwapL iz j l)) (NthL j l)) {
      Z => λ (j : Nat). λ (l : List Nat). λ (h : Le (S Z) j).
        elim l return (λ (lz : List Nat). Id Nat (NthL Z (SwapL Z j lz)) (NthL j lz)) {
          Nil => elim j return (λ (jz : Nat). Id Nat (NthL Z (SwapL Z jz Nil)) (NthL jz Nil)) {
            Z => Refl, S (j') jih => Refl },
          Cons (x) (xs) ihl =>
            elim j return (λ (jz : Nat). Le (S Z) jz → Id Nat (NthL Z (SwapL Z jz (Cons x xs))) (NthL jz (Cons x xs))) {
              Z => λ (h0 : Le (S Z) Z). botElim (Id Nat (NthL Z (SwapL Z Z (Cons x xs))) (NthL Z (Cons x xs))) h0,
              S (j') jih => λ (h0 : Le (S Z) (S j')). Refl } h },
      S (i') ih => λ (j : Nat). λ (l : List Nat). λ (h : Le (S (S i')) j).
        elim l return (λ (lz : List Nat). Id Nat (NthL (S i') (SwapL (S i') j lz)) (NthL j lz)) {
          Nil => elim j return (λ (jz : Nat). Id Nat (NthL (S i') (SwapL (S i') jz Nil)) (NthL jz Nil)) {
            Z => Refl, S (j') jih => Refl },
          Cons (x) (xs) ihl =>
            elim j return (λ (jz : Nat). Le (S (S i')) jz → Id Nat (NthL (S i') (SwapL (S i') jz (Cons x xs))) (NthL jz (Cons x xs))) {
              Z => λ (h0 : Le (S (S i')) Z). botElim (Id Nat (NthL (S i') (SwapL (S i') Z (Cons x xs))) (NthL Z (Cons x xs))) h0,
              S (j') jih => λ (h0 : Le (S (S i')) (S j')). ih j' xs h0 } h } } }
def NthSwapLLoTy : Term := prog{
  Π (i : Nat) → Π (j : Nat) → Π (l : List Nat) →
    Le (S i) j → Id Nat (NthL i (SwapL i j l)) (NthL j l) }

-- The upper endpoint: position j of `SwapL i j l` reads old position i. Induct on
-- i; the base (i = Z) reads `NthL j (Set j x xs) = x` via `NthSetSame`, so the
-- length bound `Le (S j) (Len l)` is load-bearing here (botElims the Nil leaf and
-- feeds NthSetSame) — UNLIKE _lo. The recursive leaf is the IH under `Cons x ·`,
-- threading both bounds; the j = Z leaf is botElim by `Le (S i) j`.
def NthSwapLHi : Term := prog{
  λ (i : Nat).
    elim i return (λ (iz : Nat). Π (j : Nat) → Π (l : List Nat) → Le (S iz) j → Le (S j) (Len l) → Id Nat (NthL j (SwapL iz j l)) (NthL iz l)) {
      Z => λ (j : Nat). λ (l : List Nat). λ (h1 : Le (S Z) j). λ (h2 : Le (S j) (Len l)).
        elim l return (λ (lz : List Nat). Le (S j) (Len lz) → Id Nat (NthL j (SwapL Z j lz)) (NthL Z lz)) {
          Nil => λ (a2 : Le (S j) (Len Nil)).
            botElim (Id Nat (NthL j (SwapL Z j Nil)) (NthL Z Nil)) a2,
          Cons (x) (xs) ihl => λ (a2 : Le (S j) (Len (Cons x xs))).
            elim j return (λ (jz : Nat). Le (S Z) jz → Le (S jz) (Len (Cons x xs)) → Id Nat (NthL jz (SwapL Z jz (Cons x xs))) (NthL Z (Cons x xs))) {
              Z => λ (b1 : Le (S Z) Z). λ (b2 : Le (S Z) (Len (Cons x xs))).
                botElim (Id Nat (NthL Z (SwapL Z Z (Cons x xs))) (NthL Z (Cons x xs))) b1,
              S (j') jih => λ (b1 : Le (S Z) (S j')). λ (b2 : Le (S (S j')) (Len (Cons x xs))).
                NthSetSame x j' xs b2 } h1 a2 } h2,
      S (i') ih => λ (j : Nat). λ (l : List Nat). λ (h1 : Le (S (S i')) j). λ (h2 : Le (S j) (Len l)).
        elim l return (λ (lz : List Nat). Le (S j) (Len lz) → Id Nat (NthL j (SwapL (S i') j lz)) (NthL (S i') lz)) {
          Nil => λ (a2 : Le (S j) (Len Nil)).
            botElim (Id Nat (NthL j (SwapL (S i') j Nil)) (NthL (S i') Nil)) a2,
          Cons (x) (xs) ihl => λ (a2 : Le (S j) (Len (Cons x xs))).
            elim j return (λ (jz : Nat). Le (S (S i')) jz → Le (S jz) (Len (Cons x xs)) → Id Nat (NthL jz (SwapL (S i') jz (Cons x xs))) (NthL (S i') (Cons x xs))) {
              Z => λ (b1 : Le (S (S i')) Z). λ (b2 : Le (S Z) (Len (Cons x xs))).
                botElim (Id Nat (NthL Z (SwapL (S i') Z (Cons x xs))) (NthL (S i') (Cons x xs))) b1,
              S (j') jih => λ (b1 : Le (S (S i')) (S j')). λ (b2 : Le (S (S j')) (Len (Cons x xs))).
                ih j' xs b1 b2 } h1 a2 } h2 } }
def NthSwapLHiTy : Term := prog{
  Π (i : Nat) → Π (j : Nat) → Π (l : List Nat) →
    Le (S i) j → Le (S j) (Len l) → Id Nat (NthL j (SwapL i j l)) (NthL i l) }

-- `NthL k (Set j v l) = NthL k l` for k strictly BELOW the written index j (mirror of
-- NthSetGt). The below-index companion the partition-invariant base case needs.
def NthSetLt : Term := prog{
  λ (v : Nat). λ (j : Nat).
    elim j return (λ (jz : Nat). Π (k : Nat) → Π (l : List Nat) → Le (S k) jz → Id Nat (NthL k (Set jz v l)) (NthL k l)) {
      Z => λ (k : Nat). λ (l : List Nat). λ (h : Le (S k) Z). botElim (Id Nat (NthL k (Set Z v l)) (NthL k l)) h,
      S (j') ih => λ (k : Nat). λ (l : List Nat). λ (h : Le (S k) (S j')).
        elim k return (λ (kz : Nat). Le (S kz) (S j') → Id Nat (NthL kz (Set (S j') v l)) (NthL kz l)) {
          Z => λ (h0 : Le (S Z) (S j')).
            elim l return (λ (lz : List Nat). Id Nat (NthL Z (Set (S j') v lz)) (NthL Z lz)) {
              Nil => Refl,
              Cons (hh) (tt) ihl => Refl },
          S (k') kih => λ (h0 : Le (S (S k')) (S j')).
            elim l return (λ (lz : List Nat). Id Nat (NthL (S k') (Set (S j') v lz)) (NthL (S k') lz)) {
              Nil => Refl,
              Cons (hh) (tt) ihl => ih k' tt h0 } } h } }
def NthSetLtTy : Term := prog{
  Π (v : Nat) → Π (j : Nat) → Π (k : Nat) → Π (l : List Nat) →
    Le (S k) j → Id Nat (NthL k (Set j v l)) (NthL k l) }

-- The MIDDLE band left unstated in Step A: positions strictly between i and j are
-- untouched by `SwapL i j` (two-sided bound). Induction on i mirroring SwapL; the
-- i=Z base floats through the set-branch via NthSetLt, the recursive leaf is the IH.
def NthSwapLMid : Term := prog{
  λ (i : Nat).
    elim i return (λ (iz : Nat). Π (j : Nat) → Π (k : Nat) → Π (l : List Nat) → Le (S iz) k → Le (S k) j → Id Nat (NthL k (SwapL iz j l)) (NthL k l)) {
      Z => λ (j : Nat). λ (k : Nat). λ (l : List Nat). λ (hik : Le (S Z) k). λ (hkj : Le (S k) j).
        elim l return (λ (lz : List Nat). Id Nat (NthL k (SwapL Z j lz)) (NthL k lz)) {
          Nil => Refl,
          Cons (x) (xs) ihl =>
            elim j return (λ (jz : Nat). Le (S k) jz → Id Nat (NthL k (SwapL Z jz (Cons x xs))) (NthL k (Cons x xs))) {
              Z => λ (hkj0 : Le (S k) Z). botElim (Id Nat (NthL k (SwapL Z Z (Cons x xs))) (NthL k (Cons x xs))) hkj0,
              S (j') jih => λ (hkj0 : Le (S k) (S j')).
                elim k return (λ (kz : Nat). Le (S Z) kz → Le (S kz) (S j') → Id Nat (NthL kz (Cons (NthL j' xs) (Set j' x xs))) (NthL kz (Cons x xs))) {
                  Z => λ (hik1 : Le (S Z) Z). λ (hkj1 : Le (S Z) (S j')). botElim (Id Nat (NthL Z (Cons (NthL j' xs) (Set j' x xs))) (NthL Z (Cons x xs))) hik1,
                  S (k') kih => λ (hik1 : Le (S Z) (S k')). λ (hkj1 : Le (S (S k')) (S j')).
                    NthSetLt x j' k' xs hkj1 } hik hkj0 } hkj },
      S (i') ih => λ (j : Nat). λ (k : Nat). λ (l : List Nat). λ (hik : Le (S (S i')) k). λ (hkj : Le (S k) j).
        elim l return (λ (lz : List Nat). Id Nat (NthL k (SwapL (S i') j lz)) (NthL k lz)) {
          Nil => Refl,
          Cons (x) (xs) ihl =>
            elim j return (λ (jz : Nat). Le (S k) jz → Id Nat (NthL k (SwapL (S i') jz (Cons x xs))) (NthL k (Cons x xs))) {
              Z => λ (hkj0 : Le (S k) Z). botElim (Id Nat (NthL k (SwapL (S i') Z (Cons x xs))) (NthL k (Cons x xs))) hkj0,
              S (j') jih => λ (hkj0 : Le (S k) (S j')).
                elim k return (λ (kz : Nat). Le (S (S i')) kz → Le (S kz) (S j') → Id Nat (NthL kz (Cons x (SwapL i' j' xs))) (NthL kz (Cons x xs))) {
                  Z => λ (hik1 : Le (S (S i')) Z). λ (hkj1 : Le (S Z) (S j')). botElim (Id Nat (NthL Z (Cons x (SwapL i' j' xs))) (NthL Z (Cons x xs))) hik1,
                  S (k') kih => λ (hik1 : Le (S (S i')) (S k')). λ (hkj1 : Le (S (S k')) (S j')).
                    ih j' k' xs hik1 hkj1 } hik hkj0 } hkj } } }
def NthSwapLMidTy : Term := prog{
  Π (i : Nat) → Π (j : Nat) → Π (k : Nat) → Π (l : List Nat) →
    Le (S i) k → Le (S k) j → Id Nat (NthL k (SwapL i j l)) (NthL k l) }

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
  λ (pivot : Nat). λ (lo : Nat). λ (j : Nat). λ (hlt : Le (S j) lo). λ (k : Nat).
    elim k return (λ (kz : Nat). Π (i : Nat) → Π (g : Nat) → Π (l : List Nat) → Id Nat (NthL j (PartScanRangeL pivot lo kz i g l)) (NthL j l)) {
      Z => λ (i : Nat). λ (g : Nat). λ (l : List Nat).
        elim i return (λ (iz : Nat). Id Nat (NthL j (elim iz return (λ (iy : Nat). List Nat) { Z => l, S (i') iih => SwapL lo (Add lo (S i')) l })) (NthL j l)) {
          Z => Refl,
          S (i') iih => NthSwapLLt lo (Add lo (S i')) j l hlt },
      S (k') ih => λ (i : Nat). λ (g : Nat). λ (l : List Nat).
        elim (Leb (NthL (Add lo (S (Add i g))) l) pivot)
          return (λ (w : Bool). Id Nat (NthL j (elim w return (λ (ww : Bool). List Nat) {
              True => elim g return (λ (gz : Nat). List Nat) {
                Z => PartScanRangeL pivot lo k' (S i) Z l,
                S (g') gih => PartScanRangeL pivot lo k' (S i) (S g') (SwapL (Add lo (S i)) (Add lo (S (Add i g))) l) },
              False => PartScanRangeL pivot lo k' i (S g) l })) (NthL j l)) {
          True => elim g return (λ (gz : Nat). Id Nat (NthL j (elim gz return (λ (gy : Nat). List Nat) {
                    Z => PartScanRangeL pivot lo k' (S i) Z l,
                    S (g') gih => PartScanRangeL pivot lo k' (S i) (S g') (SwapL (Add lo (S i)) (Add lo (S (Add i g))) l) })) (NthL j l)) {
            Z => ih (S i) Z l,
            S (g') gih => IdTrans Nat
                   (NthL j (PartScanRangeL pivot lo k' (S i) (S g') (SwapL (Add lo (S i)) (Add lo (S (Add i g))) l)))
                   (NthL j (SwapL (Add lo (S i)) (Add lo (S (Add i g))) l))
                   (NthL j l)
                   (ih (S i) (S g') (SwapL (Add lo (S i)) (Add lo (S (Add i g))) l))
                   (NthSwapLLt (Add lo (S i)) (Add lo (S (Add i g))) j l
                     (LeTrans (S j) lo (Add lo (S i)) hlt (LeAdd lo (S i))))
          },
          False => ih i (S g) l
        }
    } }
def NthPartScanRangeLLtTy : Term := prog{
  Π (pivot : Nat) → Π (lo : Nat) → Π (j : Nat) → Le (S j) lo → Π (k : Nat) → Π (i : Nat) → Π (g : Nat) → Π (l : List Nat) →
    Id Nat (NthL j (PartScanRangeL pivot lo k i g l)) (NthL j l) }

-- At/above-top locality of the range scan. Same threaded invariant as
-- CountPartScanRangeL but on position q, so hshift transports apply and NO
-- LenSwapL is needed; each swap discharged by NthSwapLGt.
def NthPartScanRangeLGe : Term := prog{
  λ (pivot : Nat). λ (lo : Nat). λ (q : Nat). λ (k : Nat).
    elim k return (λ (kz : Nat). Π (i : Nat) → Π (g : Nat) → Π (l : List Nat) →
        Le (Add lo (S (Add kz (Add i g)))) q →
        Id Nat (NthL q (PartScanRangeL pivot lo kz i g l)) (NthL q l)) {
      Z => λ (i : Nat). λ (g : Nat). λ (l : List Nat).
        elim i return (λ (iz : Nat).
            Le (Add lo (S (Add Z (Add iz g)))) q →
            Id Nat (NthL q (elim iz return (λ (iy : Nat). List Nat) {
                Z => l, S (i') iih => SwapL lo (Add lo (S i')) l })) (NthL q l)) {
          Z => λ (hle : Le (Add lo (S (Add Z (Add Z g)))) q). Refl,
          S (i') iih => λ (hle : Le (Add lo (S (Add Z (Add (S i') g)))) q).
            NthSwapLGt lo (Add lo (S i')) q l
              (LeTrans (S (Add lo (S i'))) (Add lo (S (S (Add i' g)))) q
                (LeRwL (Add lo (S (S (Add i' g)))) (Add lo (S (S i'))) (S (Add lo (S i')))
                  (AddSucc lo (S i'))
                  (LeAddMonoL lo (S (S i')) (S (S (Add i' g))) (LeAdd i' g)))
                hle)
        },
      S (k') ih => λ (i : Nat). λ (g : Nat). λ (l : List Nat).
        λ (hle : Le (Add lo (S (Add (S k') (Add i g)))) q).
        elim (Leb (NthL (Add lo (S (Add i g))) l) pivot)
          return (λ (w : Bool). Id Nat
            (NthL q (elim w return (λ (ww : Bool). List Nat) {
                True => elim g return (λ (gz : Nat). List Nat) {
                  Z => PartScanRangeL pivot lo k' (S i) Z l,
                  S (g') gih => PartScanRangeL pivot lo k' (S i) (S g') (SwapL (Add lo (S i)) (Add lo (S (Add i g))) l) },
                False => PartScanRangeL pivot lo k' i (S g) l }))
            (NthL q l)) {
          True =>
            (elim g return (λ (gz : Nat).
                Le (Add lo (S (Add (S k') (Add i gz)))) q →
                Id Nat (NthL q (elim gz return (λ (gy : Nat). List Nat) {
                    Z => PartScanRangeL pivot lo k' (S i) Z l,
                    S (g') gih => PartScanRangeL pivot lo k' (S i) (S g') (SwapL (Add lo (S i)) (Add lo (S (Add i gz))) l) })) (NthL q l)) {
              Z => λ (hleZ : Le (Add lo (S (Add (S k') (Add i Z)))) q).
                ih (S i) Z l
                  (LeRwL q
                    (Add lo (S (Add (S k') (Add i Z))))
                    (Add lo (S (Add k' (Add (S i) Z))))
                    (IdCongr Nat Nat (λ (a : Nat). Add lo (S a))
                      (Add (S k') (Add i Z)) (Add k' (Add (S i) Z)) (HshiftTrue k' i Z))
                    hleZ),
              S (g') gih => λ (hleS : Le (Add lo (S (Add (S k') (Add i (S g'))))) q).
                IdTrans Nat
                  (NthL q (PartScanRangeL pivot lo k' (S i) (S g') (SwapL (Add lo (S i)) (Add lo (S (Add i (S g')))) l)))
                  (NthL q (SwapL (Add lo (S i)) (Add lo (S (Add i (S g')))) l))
                  (NthL q l)
                  (ih (S i) (S g') (SwapL (Add lo (S i)) (Add lo (S (Add i (S g')))) l)
                    (LeRwL q
                      (Add lo (S (Add (S k') (Add i (S g')))))
                      (Add lo (S (Add k' (Add (S i) (S g')))))
                      (IdCongr Nat Nat (λ (a : Nat). Add lo (S a))
                        (Add (S k') (Add i (S g'))) (Add k' (Add (S i) (S g'))) (HshiftTrue k' i (S g')))
                      hleS))
                  (NthSwapLGt (Add lo (S i)) (Add lo (S (Add i (S g')))) q l
                    (LeTrans (S (Add lo (S (Add i (S g'))))) (Add lo (S (S (Add k' (Add i (S g')))))) q
                      (LeRwL (Add lo (S (S (Add k' (Add i (S g'))))))
                        (Add lo (S (S (Add i (S g'))))) (S (Add lo (S (Add i (S g')))))
                        (AddSucc lo (S (Add i (S g'))))
                        (LeAddMonoL lo (S (S (Add i (S g')))) (S (S (Add k' (Add i (S g')))))
                          (LeAddL (Add i (S g')) k')))
                      hleS))
            }) hle,
          False =>
            ih i (S g) l
              (LeRwL q
                (Add lo (S (Add (S k') (Add i g))))
                (Add lo (S (Add k' (Add i (S g)))))
                (IdCongr Nat Nat (λ (a : Nat). Add lo (S a))
                  (Add (S k') (Add i g)) (Add k' (Add i (S g))) (HshiftFalse k' i g))
                hle)
        }
    } }
def NthPartScanRangeLGeTy : Term := prog{
  Π (pivot : Nat) → Π (lo : Nat) → Π (q : Nat) → Π (k : Nat) → Π (i : Nat) → Π (g : Nat) → Π (l : List Nat) →
    Le (Add lo (S (Add k (Add i g)))) q →
    Id Nat (NthL q (PartScanRangeL pivot lo k i g l)) (NthL q l) }

-- Below-lo locality wrapper (partition = scan after pivot pick), mirroring LenPartitionRangeL.
def NthPartitionRangeLLt : Term := prog{
  λ (lo : Nat). λ (j : Nat). λ (hlt : Le (S j) lo). λ (cnt : Nat). λ (l : List Nat).
    elim cnt return (λ (cz : Nat). Id Nat
        (NthL j (elim cz return (λ (cy : Nat). List Nat) { Z => l, S (cnt') rec => PartScanRangeL (NthL lo l) lo cnt' Z Z l }))
        (NthL j l)) {
      Z => Refl,
      S (cnt') rec => NthPartScanRangeLLt (NthL lo l) lo j hlt cnt' Z Z l } }
def NthPartitionRangeLLtTy : Term := prog{
  Π (lo : Nat) → Π (j : Nat) → Le (S j) lo → Π (cnt : Nat) → Π (l : List Nat) →
    Id Nat (NthL j (PartitionRangeL lo cnt l)) (NthL j l) }

-- At/above-(lo+cnt) locality wrapper. The top bound Le (add lo cnt) q supplies the
-- scan's Le (add lo (S (add cnt' Z))) q via one AddZero nudge (cf CountPartitionRangeL).
def NthPartitionRangeLGe : Term := prog{
  λ (lo : Nat). λ (q : Nat). λ (cnt : Nat). λ (l : List Nat).
    elim cnt return (λ (cz : Nat).
        Le (Add lo cz) q →
        Id Nat (NthL q (elim cz return (λ (cy : Nat). List Nat) { Z => l, S (cnt') rec => PartScanRangeL (NthL lo l) lo cnt' Z Z l })) (NthL q l)) {
      Z => λ (hb : Le (Add lo Z) q). Refl,
      S (cnt') rec => λ (hb : Le (Add lo (S cnt')) q).
        NthPartScanRangeLGe (NthL lo l) lo q cnt' Z Z l
          (LeRwL q (Add lo (S cnt')) (Add lo (S (Add cnt' Z)))
            (IdCongr Nat Nat (λ (a : Nat). Add lo (S a)) cnt' (Add cnt' Z)
              (IdSym Nat (Add cnt' Z) cnt' (AddZero cnt')))
            hb) } }
def NthPartitionRangeLGeTy : Term := prog{
  Π (lo : Nat) → Π (q : Nat) → Π (cnt : Nat) → Π (l : List Nat) →
    Le (Add lo cnt) q → Id Nat (NthL q (PartitionRangeL lo cnt l)) (NthL q l) }

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
  λ (fuel : Nat). λ (j : Nat).
    elim fuel return (λ (fz : Nat). Π (lo : Nat) → Π (cnt : Nat) → Π (l : List Nat) → Le (S j) lo → Id Nat (NthL j (SortRangeL fz lo cnt l)) (NthL j l)) {
      Z => λ (lo : Nat). λ (cnt : Nat). λ (l : List Nat). λ (hlt : Le (S j) lo). Refl,
      S (f') ih => λ (lo : Nat). λ (cnt : Nat). λ (l : List Nat). λ (hlt : Le (S j) lo).
        elim cnt return (λ (cz : Nat). Id Nat (NthL j (elim cz return (λ (cy : Nat). List Nat) {
              Z => l,
              S (cnt') nih => elim cnt' return (λ (my : Nat). List Nat) {
                Z => l,
                S (cnt'') n2ih => SortRangeL f' (S (Add lo (PartIdxRangeL lo cnt l))) (PartGapRangeL lo cnt l) (SortRangeL f' lo (PartIdxRangeL lo cnt l) (PartitionRangeL lo cnt l)) } })) (NthL j l)) {
          Z => Refl,
          S (cnt') nih => elim cnt' return (λ (my : Nat). Id Nat (NthL j (elim my return (λ (myy : Nat). List Nat) {
                Z => l,
                S (cnt'') n2ih => SortRangeL f' (S (Add lo (PartIdxRangeL lo cnt l))) (PartGapRangeL lo cnt l) (SortRangeL f' lo (PartIdxRangeL lo cnt l) (PartitionRangeL lo cnt l)) })) (NthL j l)) {
            Z => Refl,
            S (cnt'') n2ih =>
              IdTrans Nat
                (NthL j (SortRangeL f' (S (Add lo (PartIdxRangeL lo cnt l))) (PartGapRangeL lo cnt l) (SortRangeL f' lo (PartIdxRangeL lo cnt l) (PartitionRangeL lo cnt l))))
                (NthL j (SortRangeL f' lo (PartIdxRangeL lo cnt l) (PartitionRangeL lo cnt l)))
                (NthL j l)
                (ih (S (Add lo (PartIdxRangeL lo cnt l))) (PartGapRangeL lo cnt l) (SortRangeL f' lo (PartIdxRangeL lo cnt l) (PartitionRangeL lo cnt l))
                    (LeTrans (S j) lo (S (Add lo (PartIdxRangeL lo cnt l))) hlt
                      (LeUpR lo (Add lo (PartIdxRangeL lo cnt l)) (LeAdd lo (PartIdxRangeL lo cnt l)))))
                (IdTrans Nat
                  (NthL j (SortRangeL f' lo (PartIdxRangeL lo cnt l) (PartitionRangeL lo cnt l)))
                  (NthL j (PartitionRangeL lo cnt l))
                  (NthL j l)
                  (ih lo (PartIdxRangeL lo cnt l) (PartitionRangeL lo cnt l) hlt)
                  (NthPartitionRangeLLt lo j hlt cnt l))
          } } } }
def NthSortRangeLLtTy : Term := prog{
  Π (fuel : Nat) → Π (j : Nat) → Π (lo : Nat) → Π (cnt : Nat) → Π (l : List Nat) →
    Le (S j) lo → Id Nat (NthL j (SortRangeL fuel lo cnt l)) (NthL j l) }

-- The pivot index plus the gap equals cnt-1 (= S cnt'' for cnt = S(S cnt'')).
-- Lifted from sortRangeBL's inner IdTrans (PartScanSizeL then AddZero).
def PartSizeCnt : Term := prog{
  λ (lo : Nat). λ (cnt'' : Nat). λ (l : List Nat).
    IdTrans Nat
      (Add (PartIdxRangeL lo (S (S cnt'')) l) (PartGapRangeL lo (S (S cnt'')) l))
      (S (Add cnt'' Z))
      (S cnt'')
      (PartScanSizeL (NthL lo l) lo (S cnt'') Z Z l)
      (IdCongr Nat Nat (λ (a : Nat). S a) (Add cnt'' Z) cnt'' (AddZero cnt'')) }
def PartSizeCntTy : Term := prog{
  Π (lo : Nat) → Π (cnt'' : Nat) → Π (l : List Nat) →
    Id Nat (Add (PartIdxRangeL lo (S (S cnt'')) l) (PartGapRangeL lo (S (S cnt'')) l)) (S cnt'') }

-- Left sub-range position bound: Le (add lo i) q from Le (add lo cnt) q (i ≤ cnt-1 < cnt).
def SortRangeGeBL : Term := prog{
  λ (lo : Nat). λ (cnt'' : Nat). λ (q : Nat). λ (l : List Nat). λ (hb : Le (Add lo (S (S cnt''))) q).
    LeTrans (Add lo (PartIdxRangeL lo (S (S cnt'')) l)) (Add lo (S (S cnt''))) q
      (LeAddMonoL lo (PartIdxRangeL lo (S (S cnt'')) l) (S (S cnt''))
        (LeUpR (PartIdxRangeL lo (S (S cnt'')) l) (S cnt'')
          (LeRwR (PartIdxRangeL lo (S (S cnt'')) l)
            (Add (PartIdxRangeL lo (S (S cnt'')) l) (PartGapRangeL lo (S (S cnt'')) l))
            (S cnt'')
            (PartSizeCnt lo cnt'' l)
            (LeAdd (PartIdxRangeL lo (S (S cnt'')) l) (PartGapRangeL lo (S (S cnt'')) l)))))
      hb }
def SortRangeGeBLTy : Term := prog{
  Π (lo : Nat) → Π (cnt'' : Nat) → Π (q : Nat) → Π (l : List Nat) → Le (Add lo (S (S cnt''))) q →
    Le (Add lo (PartIdxRangeL lo (S (S cnt'')) l)) q }

-- Right sub-range position bound: Le (add (S (add lo i)) g) q from Le (add lo cnt) q,
-- using add (S (add lo i)) g = add lo (S (add i g)) = add lo cnt (PartSizeCnt).
def SortRangeGeBR : Term := prog{
  λ (lo : Nat). λ (cnt'' : Nat). λ (q : Nat). λ (l : List Nat). λ (hb : Le (Add lo (S (S cnt''))) q).
    LeRwL q (Add lo (S (S cnt''))) (Add (S (Add lo (PartIdxRangeL lo (S (S cnt'')) l))) (PartGapRangeL lo (S (S cnt'')) l))
      (IdSym Nat
        (Add (S (Add lo (PartIdxRangeL lo (S (S cnt'')) l))) (PartGapRangeL lo (S (S cnt'')) l))
        (Add lo (S (S cnt'')))
        (IdTrans Nat
          (Add (S (Add lo (PartIdxRangeL lo (S (S cnt'')) l))) (PartGapRangeL lo (S (S cnt'')) l))
          (Add lo (S (Add (PartIdxRangeL lo (S (S cnt'')) l) (PartGapRangeL lo (S (S cnt'')) l))))
          (Add lo (S (S cnt'')))
          (IdTrans Nat
            (Add (S (Add lo (PartIdxRangeL lo (S (S cnt'')) l))) (PartGapRangeL lo (S (S cnt'')) l))
            (S (Add lo (Add (PartIdxRangeL lo (S (S cnt'')) l) (PartGapRangeL lo (S (S cnt'')) l))))
            (Add lo (S (Add (PartIdxRangeL lo (S (S cnt'')) l) (PartGapRangeL lo (S (S cnt'')) l))))
            (IdCongr Nat Nat (λ (a : Nat). S a)
              (Add (Add lo (PartIdxRangeL lo (S (S cnt'')) l)) (PartGapRangeL lo (S (S cnt'')) l))
              (Add lo (Add (PartIdxRangeL lo (S (S cnt'')) l) (PartGapRangeL lo (S (S cnt'')) l)))
              (AddAssoc lo (PartIdxRangeL lo (S (S cnt'')) l) (PartGapRangeL lo (S (S cnt'')) l)))
            (IdSym Nat
              (Add lo (S (Add (PartIdxRangeL lo (S (S cnt'')) l) (PartGapRangeL lo (S (S cnt'')) l))))
              (S (Add lo (Add (PartIdxRangeL lo (S (S cnt'')) l) (PartGapRangeL lo (S (S cnt'')) l))))
              (AddSucc lo (Add (PartIdxRangeL lo (S (S cnt'')) l) (PartGapRangeL lo (S (S cnt'')) l)))))
          (IdCongr Nat Nat (λ (a : Nat). Add lo (S a))
            (Add (PartIdxRangeL lo (S (S cnt'')) l) (PartGapRangeL lo (S (S cnt'')) l)) (S cnt'')
            (PartSizeCnt lo cnt'' l))))
      hb }
def SortRangeGeBRTy : Term := prog{
  Π (lo : Nat) → Π (cnt'' : Nat) → Π (q : Nat) → Π (l : List Nat) → Le (Add lo (S (S cnt''))) q →
    Le (Add (S (Add lo (PartIdxRangeL lo (S (S cnt'')) l))) (PartGapRangeL lo (S (S cnt'')) l)) q }

-- At/above-(lo+cnt) locality of the full sort. CountSortRangeL structure with
-- position bounds SortRangeGeBL/BR feeding the two recursive-sort IHs.
def NthSortRangeLGe : Term := prog{
  λ (fuel : Nat). λ (q : Nat).
    elim fuel return (λ (fz : Nat). Π (lo : Nat) → Π (cnt : Nat) → Π (l : List Nat) →
        Le (Add lo cnt) q → Id Nat (NthL q (SortRangeL fz lo cnt l)) (NthL q l)) {
      Z => λ (lo : Nat). λ (cnt : Nat). λ (l : List Nat). λ (hb : Le (Add lo cnt) q). Refl,
      S (f') ih => λ (lo : Nat). λ (cnt : Nat). λ (l : List Nat).
        elim cnt return (λ (cz : Nat). Le (Add lo cz) q →
            Id Nat (NthL q (SortRangeL (S f') lo cz l)) (NthL q l)) {
          Z => λ (hb : Le (Add lo Z) q). Refl,
          S (cnt') nih => elim cnt' return (λ (cz' : Nat). Le (Add lo (S cz')) q →
              Id Nat (NthL q (SortRangeL (S f') lo (S cz') l)) (NthL q l)) {
            Z => λ (hb : Le (Add lo (S Z)) q). Refl,
            S (cnt'') n2ih => λ (hb : Le (Add lo (S (S cnt''))) q).
              IdTrans Nat
                (NthL q (SortRangeL f' (S (Add lo (PartIdxRangeL lo (S (S cnt'')) l))) (PartGapRangeL lo (S (S cnt'')) l)
                          (SortRangeL f' lo (PartIdxRangeL lo (S (S cnt'')) l) (PartitionRangeL lo (S (S cnt'')) l))))
                (NthL q (SortRangeL f' lo (PartIdxRangeL lo (S (S cnt'')) l) (PartitionRangeL lo (S (S cnt'')) l)))
                (NthL q l)
                (ih (S (Add lo (PartIdxRangeL lo (S (S cnt'')) l))) (PartGapRangeL lo (S (S cnt'')) l)
                    (SortRangeL f' lo (PartIdxRangeL lo (S (S cnt'')) l) (PartitionRangeL lo (S (S cnt'')) l))
                    (SortRangeGeBR lo cnt'' q l hb))
                (IdTrans Nat
                  (NthL q (SortRangeL f' lo (PartIdxRangeL lo (S (S cnt'')) l) (PartitionRangeL lo (S (S cnt'')) l)))
                  (NthL q (PartitionRangeL lo (S (S cnt'')) l))
                  (NthL q l)
                  (ih lo (PartIdxRangeL lo (S (S cnt'')) l) (PartitionRangeL lo (S (S cnt'')) l)
                      (SortRangeGeBL lo cnt'' q l hb))
                  (NthPartitionRangeLGe lo q (S (S cnt'')) l hb))
          }
        }
    } }
def NthSortRangeLGeTy : Term := prog{
  Π (fuel : Nat) → Π (q : Nat) → Π (lo : Nat) → Π (cnt : Nat) → Π (l : List Nat) →
    Le (Add lo cnt) q → Id Nat (NthL q (SortRangeL fuel lo cnt l)) (NthL q l) }

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
  λ (x : Nat). λ (h : Id Nat Z (S x)).
    j Nat Z (λ (y : Nat). λ (hy : Id Nat Z y). elim y return (λ (yy : Nat). Type) { Z => Unit, S (k) ih => Bot })
      unit (S x) h }
def ZnotsTy : Term := prog{ Π (x : Nat) → Id Nat Z (S x) → Bot }

def Pred : Term := prog{ λ (n : Nat). elim n return (λ (z : Nat). Nat) { Z => Z, S (k) ih => k } }
def SInj : Term := prog{
  λ (m : Nat). λ (n : Nat). λ (h : Id Nat (S m) (S n)).
    IdCongr Nat Nat Pred (S m) (S n) h }
def SInjTy : Term := prog{ Π (m : Nat) → Π (n : Nat) → Id Nat (S m) (S n) → Id Nat m n }

def AddCancelL : Term := prog{
  λ (a : Nat).
    elim a return (λ (az : Nat). Π (x : Nat) → Π (y : Nat) → Id Nat (Add az x) (Add az y) → Id Nat x y) {
      Z => λ (x : Nat). λ (y : Nat). λ (h : Id Nat (Add Z x) (Add Z y)). h,
      S (a') ih => λ (x : Nat). λ (y : Nat). λ (h : Id Nat (Add (S a') x) (Add (S a') y)).
        ih x y (SInj (Add a' x) (Add a' y) h) } }
def AddCancelLTy : Term := prog{
  Π (a : Nat) → Π (x : Nat) → Π (y : Nat) → Id Nat (Add a x) (Add a y) → Id Nat x y }

def NthDrop : Term := prog{
  λ (b : Nat).
    elim b return (λ (bz : Nat). Π (k : Nat) → Π (l : List Nat) → Id Nat (NthL k (Drop bz l)) (NthL (Add bz k) l)) {
      Z => λ (k : Nat). λ (l : List Nat). Refl,
      S (b') ih => λ (k : Nat). λ (l : List Nat).
        elim l return (λ (lz : List Nat). Id Nat (NthL k (Drop (S b') lz)) (NthL (Add (S b') k) lz)) {
          Nil => elim k return (λ (kz : Nat). Id Nat (NthL kz (Drop (S b') Nil)) (NthL (Add (S b') kz) Nil)) {
            Z => Refl, S (k') kih => Refl },
          Cons (h) (t) ihl => ih k t } } }
def NthDropTy : Term := prog{
  Π (b : Nat) → Π (k : Nat) → Π (l : List Nat) → Id Nat (NthL k (Drop b l)) (NthL (Add b k) l) }

def ListExt : Term := prog{
  λ (a : List Nat).
    elim a return (λ (az : List Nat). Π (b : List Nat) → Id Nat (Len az) (Len b) → (Π (k : Nat) → Id Nat (NthL k az) (NthL k b)) → Id (List Nat) az b) {
      Nil => λ (b : List Nat).
        elim b return (λ (bz : List Nat). Id Nat (Len Nil) (Len bz) → (Π (k : Nat) → Id Nat (NthL k Nil) (NthL k bz)) → Id (List Nat) Nil bz) {
          Nil => λ (hlen : Id Nat (Len Nil) (Len Nil)). λ (hnth : Π (k : Nat) → Id Nat (NthL k Nil) (NthL k Nil)). Refl,
          Cons (hb) (tb) ihb => λ (hlen : Id Nat (Len Nil) (Len (Cons hb tb))). λ (hnth : Π (k : Nat) → Id Nat (NthL k Nil) (NthL k (Cons hb tb))).
            botElim (Id (List Nat) Nil (Cons hb tb)) (Znots (Len tb) hlen) },
      Cons (ha) (ta) iha => λ (b : List Nat).
        elim b return (λ (bz : List Nat). Id Nat (Len (Cons ha ta)) (Len bz) → (Π (k : Nat) → Id Nat (NthL k (Cons ha ta)) (NthL k bz)) → Id (List Nat) (Cons ha ta) bz) {
          Nil => λ (hlen : Id Nat (Len (Cons ha ta)) (Len Nil)). λ (hnth : Π (k : Nat) → Id Nat (NthL k (Cons ha ta)) (NthL k Nil)).
            botElim (Id (List Nat) (Cons ha ta) Nil) (Znots (Len ta) (IdSym Nat (Len (Cons ha ta)) (Len Nil) hlen)),
          Cons (hb) (tb) ihb => λ (hlen : Id Nat (Len (Cons ha ta)) (Len (Cons hb tb))). λ (hnth : Π (k : Nat) → Id Nat (NthL k (Cons ha ta)) (NthL k (Cons hb tb))).
            IdTrans (List Nat) (Cons ha ta) (Cons hb ta) (Cons hb tb)
              (IdCongr Nat (List Nat) (λ (hh : Nat). Cons hh ta) ha hb (hnth Z))
              (IdCongr (List Nat) (List Nat) (λ (tt : List Nat). Cons hb tt) ta tb
                (iha tb (SInj (Len ta) (Len tb) hlen) (λ (k : Nat). hnth (S k)))) } } }
def ListExtTy : Term := prog{
  Π (a : List Nat) → Π (b : List Nat) → Id Nat (Len a) (Len b) →
    (Π (k : Nat) → Id Nat (NthL k a) (NthL k b)) → Id (List Nat) a b }

def TakeExtBounded : Term := prog{
  λ (w : Nat).
    elim w return (λ (wz : Nat). Π (a : List Nat) → Π (b : List Nat) → Id Nat (Len a) (Len b) → (Π (k : Nat) → Le (S k) wz → Id Nat (NthL k a) (NthL k b)) → Id (List Nat) (Take wz a) (Take wz b)) {
      Z => λ (a : List Nat). λ (b : List Nat). λ (hlen : Id Nat (Len a) (Len b)). λ (hnth : Π (k : Nat) → Le (S k) Z → Id Nat (NthL k a) (NthL k b)). Refl,
      S (w') ih => λ (a : List Nat). λ (b : List Nat). λ (hlen : Id Nat (Len a) (Len b)). λ (hnth : Π (k : Nat) → Le (S k) (S w') → Id Nat (NthL k a) (NthL k b)).
        elim a return (λ (az : List Nat). Id Nat (Len az) (Len b) → (Π (k : Nat) → Le (S k) (S w') → Id Nat (NthL k az) (NthL k b)) → Id (List Nat) (Take (S w') az) (Take (S w') b)) {
          Nil => λ (hlenA : Id Nat (Len Nil) (Len b)). λ (hnthA : Π (k : Nat) → Le (S k) (S w') → Id Nat (NthL k Nil) (NthL k b)).
            elim b return (λ (bz : List Nat). Id Nat (Len Nil) (Len bz) → Id (List Nat) (Take (S w') Nil) (Take (S w') bz)) {
              Nil => λ (hl : Id Nat (Len Nil) (Len Nil)). Refl,
              Cons (hb) (tb) ihb => λ (hl : Id Nat (Len Nil) (Len (Cons hb tb))).
                botElim (Id (List Nat) (Take (S w') Nil) (Take (S w') (Cons hb tb))) (Znots (Len tb) hl) } hlenA,
          Cons (ha) (ta) iha => λ (hlenA : Id Nat (Len (Cons ha ta)) (Len b)). λ (hnthA : Π (k : Nat) → Le (S k) (S w') → Id Nat (NthL k (Cons ha ta)) (NthL k b)).
            elim b return (λ (bz : List Nat). Id Nat (Len (Cons ha ta)) (Len bz) → (Π (k : Nat) → Le (S k) (S w') → Id Nat (NthL k (Cons ha ta)) (NthL k bz)) → Id (List Nat) (Take (S w') (Cons ha ta)) (Take (S w') bz)) {
              Nil => λ (hl : Id Nat (Len (Cons ha ta)) (Len Nil)). λ (hn : Π (k : Nat) → Le (S k) (S w') → Id Nat (NthL k (Cons ha ta)) (NthL k Nil)).
                botElim (Id (List Nat) (Take (S w') (Cons ha ta)) (Take (S w') Nil)) (Znots (Len ta) (IdSym Nat (Len (Cons ha ta)) (Len Nil) hl)),
              Cons (hb) (tb) ihb => λ (hl : Id Nat (Len (Cons ha ta)) (Len (Cons hb tb))). λ (hn : Π (k : Nat) → Le (S k) (S w') → Id Nat (NthL k (Cons ha ta)) (NthL k (Cons hb tb))).
                IdTrans (List Nat) (Cons ha (Take w' ta)) (Cons hb (Take w' ta)) (Cons hb (Take w' tb))
                  (IdCongr Nat (List Nat) (λ (hh : Nat). Cons hh (Take w' ta)) ha hb (hn Z unit))
                  (IdCongr (List Nat) (List Nat) (λ (tt : List Nat). Cons hb tt) (Take w' ta) (Take w' tb)
                    (ih ta tb (SInj (Len ta) (Len tb) hl) (λ (k : Nat). λ (hk : Le (S k) w'). hn (S k) hk)))
            } hlenA hnthA
        } hlen hnth
    } }
def TakeExtBoundedTy : Term := prog{
  Π (w : Nat) → Π (a : List Nat) → Π (b : List Nat) → Id Nat (Len a) (Len b) →
    (Π (k : Nat) → Le (S k) w → Id Nat (NthL k a) (NthL k b)) → Id (List Nat) (Take w a) (Take w b) }

def LenDropCong : Term := prog{
  λ (w : Nat).
    elim w return (λ (wz : Nat). Π (a : List Nat) → Π (b : List Nat) → Id Nat (Len a) (Len b) → Id Nat (Len (Drop wz a)) (Len (Drop wz b))) {
      Z => λ (a : List Nat). λ (b : List Nat). λ (hlen : Id Nat (Len a) (Len b)). hlen,
      S (w') ih => λ (a : List Nat). λ (b : List Nat). λ (hlen : Id Nat (Len a) (Len b)).
        elim a return (λ (az : List Nat). Id Nat (Len az) (Len b) → Id Nat (Len (Drop (S w') az)) (Len (Drop (S w') b))) {
          Nil => λ (hl : Id Nat (Len Nil) (Len b)).
            elim b return (λ (bz : List Nat). Id Nat (Len Nil) (Len bz) → Id Nat (Len (Drop (S w') Nil)) (Len (Drop (S w') bz))) {
              Nil => λ (h : Id Nat (Len Nil) (Len Nil)). Refl,
              Cons (hb) (tb) ihb => λ (h : Id Nat (Len Nil) (Len (Cons hb tb))).
                botElim (Id Nat (Len (Drop (S w') Nil)) (Len (Drop (S w') (Cons hb tb)))) (Znots (Len tb) h) } hl,
          Cons (ha) (ta) iha => λ (hl : Id Nat (Len (Cons ha ta)) (Len b)).
            elim b return (λ (bz : List Nat). Id Nat (Len (Cons ha ta)) (Len bz) → Id Nat (Len (Drop (S w') (Cons ha ta))) (Len (Drop (S w') bz))) {
              Nil => λ (h : Id Nat (Len (Cons ha ta)) (Len Nil)).
                botElim (Id Nat (Len (Drop (S w') (Cons ha ta))) (Len (Drop (S w') Nil))) (Znots (Len ta) (IdSym Nat (Len (Cons ha ta)) (Len Nil) h)),
              Cons (hb) (tb) ihb => λ (h : Id Nat (Len (Cons ha ta)) (Len (Cons hb tb))).
                ih ta tb (SInj (Len ta) (Len tb) h) } hl } hlen } }
def LenDropCongTy : Term := prog{
  Π (w : Nat) → Π (a : List Nat) → Π (b : List Nat) → Id Nat (Len a) (Len b) →
    Id Nat (Len (Drop w a)) (Len (Drop w b)) }

def CountSplit : Term := prog{
  λ (x : Nat). λ (w : Nat). λ (l : List Nat).
    IdTrans Nat (Count x l) (Count x (Append (Take w l) (Drop w l))) (Add (Count x (Take w l)) (Count x (Drop w l)))
      (IdCongr (List Nat) Nat (λ (ll : List Nat). Count x ll) l (Append (Take w l) (Drop w l))
        (IdSym (List Nat) (Append (Take w l) (Drop w l)) l (TakeDropId w l)))
      (CountAppend x (Take w l) (Drop w l)) }
def CountSplitTy : Term := prog{
  Π (x : Nat) → Π (w : Nat) → Π (l : List Nat) →
    Id Nat (Count x l) (Add (Count x (Take w l)) (Count x (Drop w l))) }

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
  λ (x : Nat). λ (w : Nat). λ (s : List Nat). λ (l : List Nat).
    λ (hcount : Id Nat (Count x s) (Count x l)).
    λ (hpre : Id Nat (Count x (Take w s)) (Count x (Take w l))).
      AddCancelL (Count x (Take w l)) (Count x (Drop w s)) (Count x (Drop w l))
        (IdTrans Nat
          (Add (Count x (Take w l)) (Count x (Drop w s)))
          (Count x l)
          (Add (Count x (Take w l)) (Count x (Drop w l)))
          (IdTrans Nat
            (Add (Count x (Take w l)) (Count x (Drop w s)))
            (Count x s)
            (Count x l)
            (IdSym Nat (Count x s) (Add (Count x (Take w l)) (Count x (Drop w s)))
              (IdTrans Nat
                (Count x s)
                (Add (Count x (Take w s)) (Count x (Drop w s)))
                (Add (Count x (Take w l)) (Count x (Drop w s)))
                (CountSplit x w s)
                (IdCongr Nat Nat (λ (n : Nat). Add n (Count x (Drop w s)))
                  (Count x (Take w s)) (Count x (Take w l)) hpre)))
            hcount)
          (CountSplit x w l)) }
def CountRestPreservedTy : Term := prog{
  Π (x : Nat) → Π (w : Nat) → Π (s : List Nat) → Π (l : List Nat) →
    Id Nat (Count x s) (Count x l) →
    Id Nat (Count x (Take w s)) (Count x (Take w l)) →
    Id Nat (Count x (Drop w s)) (Count x (Drop w l)) }

def CountSegPreserved : Term := prog{
  λ (x : Nat). λ (w : Nat). λ (s : List Nat). λ (l : List Nat).
    λ (hcount : Id Nat (Count x s) (Count x l)).
    λ (hdrop : Id Nat (Count x (Drop w s)) (Count x (Drop w l))).
      AddCancelL (Count x (Drop w l)) (Count x (Take w s)) (Count x (Take w l))
        (IdTrans Nat
          (Add (Count x (Drop w l)) (Count x (Take w s)))
          (Count x l)
          (Add (Count x (Drop w l)) (Count x (Take w l)))
          (IdTrans Nat
            (Add (Count x (Drop w l)) (Count x (Take w s)))
            (Count x s)
            (Count x l)
            (IdSym Nat (Count x s) (Add (Count x (Drop w l)) (Count x (Take w s)))
              (IdTrans Nat
                (Count x s)
                (Add (Count x (Take w s)) (Count x (Drop w s)))
                (Add (Count x (Drop w l)) (Count x (Take w s)))
                (CountSplit x w s)
                (IdTrans Nat
                  (Add (Count x (Take w s)) (Count x (Drop w s)))
                  (Add (Count x (Take w s)) (Count x (Drop w l)))
                  (Add (Count x (Drop w l)) (Count x (Take w s)))
                  (IdCongr Nat Nat (λ (n : Nat). Add (Count x (Take w s)) n)
                    (Count x (Drop w s)) (Count x (Drop w l)) hdrop)
                  (AddComm (Count x (Take w s)) (Count x (Drop w l))))))
            hcount)
          (IdTrans Nat
            (Count x l)
            (Add (Count x (Take w l)) (Count x (Drop w l)))
            (Add (Count x (Drop w l)) (Count x (Take w l)))
            (CountSplit x w l)
            (AddComm (Count x (Take w l)) (Count x (Drop w l))))) }
def CountSegPreservedTy : Term := prog{
  Π (x : Nat) → Π (w : Nat) → Π (s : List Nat) → Π (l : List Nat) →
    Id Nat (Count x s) (Count x l) →
    Id Nat (Count x (Drop w s)) (Count x (Drop w l)) →
    Id Nat (Count x (Take w s)) (Count x (Take w l)) }

def SegGlue : Term := prog{
  λ (x : Nat). λ (lo : Nat). λ (cnt : Nat). λ (s : List Nat). λ (l : List Nat).
    λ (hcount : Id Nat (Count x s) (Count x l)).
    λ (hpre : Id (List Nat) (Take lo s) (Take lo l)).
    λ (hsuf : Id (List Nat) (Drop cnt (Drop lo s)) (Drop cnt (Drop lo l))).
      CountSegPreserved x cnt (Drop lo s) (Drop lo l)
        (CountRestPreserved x lo s l hcount
          (IdCongr (List Nat) Nat (λ (ll : List Nat). Count x ll) (Take lo s) (Take lo l) hpre))
        (IdCongr (List Nat) Nat (λ (ll : List Nat). Count x ll) (Drop cnt (Drop lo s)) (Drop cnt (Drop lo l)) hsuf) }
def SegGlueTy : Term := prog{
  Π (x : Nat) → Π (lo : Nat) → Π (cnt : Nat) → Π (s : List Nat) → Π (l : List Nat) →
    Id Nat (Count x s) (Count x l) →
    Id (List Nat) (Take lo s) (Take lo l) →
    Id (List Nat) (Drop cnt (Drop lo s)) (Drop cnt (Drop lo l)) →
    Id Nat (Count x (Take cnt (Drop lo s))) (Count x (Take cnt (Drop lo l))) }

-- Prefix/suffix of the SORT are identical (Step B locality → list equality).
def TakeLoSort : Term := prog{
  λ (fuel : Nat). λ (lo : Nat). λ (cnt : Nat). λ (l : List Nat).
    TakeExtBounded lo (SortRangeL fuel lo cnt l) l
      (LenSortRangeL fuel lo cnt l)
      (λ (k : Nat). λ (hk : Le (S k) lo). NthSortRangeLLt fuel k lo cnt l hk) }
def TakeLoSortTy : Term := prog{
  Π (fuel : Nat) → Π (lo : Nat) → Π (cnt : Nat) → Π (l : List Nat) →
    Id (List Nat) (Take lo (SortRangeL fuel lo cnt l)) (Take lo l) }

def DropSuffixSort : Term := prog{
  λ (fuel : Nat). λ (lo : Nat). λ (cnt : Nat). λ (l : List Nat).
    ListExt (Drop cnt (Drop lo (SortRangeL fuel lo cnt l))) (Drop cnt (Drop lo l))
      (LenDropCong cnt (Drop lo (SortRangeL fuel lo cnt l)) (Drop lo l)
        (LenDropCong lo (SortRangeL fuel lo cnt l) l (LenSortRangeL fuel lo cnt l)))
      (λ (k : Nat).
        IdTrans Nat
          (NthL k (Drop cnt (Drop lo (SortRangeL fuel lo cnt l))))
          (NthL (Add lo (Add cnt k)) (SortRangeL fuel lo cnt l))
          (NthL k (Drop cnt (Drop lo l)))
          (IdTrans Nat
            (NthL k (Drop cnt (Drop lo (SortRangeL fuel lo cnt l))))
            (NthL (Add cnt k) (Drop lo (SortRangeL fuel lo cnt l)))
            (NthL (Add lo (Add cnt k)) (SortRangeL fuel lo cnt l))
            (NthDrop cnt k (Drop lo (SortRangeL fuel lo cnt l)))
            (NthDrop lo (Add cnt k) (SortRangeL fuel lo cnt l)))
          (IdTrans Nat
            (NthL (Add lo (Add cnt k)) (SortRangeL fuel lo cnt l))
            (NthL (Add lo (Add cnt k)) l)
            (NthL k (Drop cnt (Drop lo l)))
            (NthSortRangeLGe fuel (Add lo (Add cnt k)) lo cnt l
              (LeAddMonoL lo cnt (Add cnt k) (LeAdd cnt k)))
            (IdTrans Nat
              (NthL (Add lo (Add cnt k)) l)
              (NthL (Add cnt k) (Drop lo l))
              (NthL k (Drop cnt (Drop lo l)))
              (IdSym Nat (NthL (Add cnt k) (Drop lo l)) (NthL (Add lo (Add cnt k)) l) (NthDrop lo (Add cnt k) l))
              (IdSym Nat (NthL k (Drop cnt (Drop lo l))) (NthL (Add cnt k) (Drop lo l)) (NthDrop cnt k (Drop lo l)))))) }
def DropSuffixSortTy : Term := prog{
  Π (fuel : Nat) → Π (lo : Nat) → Π (cnt : Nat) → Π (l : List Nat) →
    Id (List Nat) (Drop cnt (Drop lo (SortRangeL fuel lo cnt l))) (Drop cnt (Drop lo l)) }

-- Prefix/suffix of PARTITION are identical (same shape).
def TakeLoPartition : Term := prog{
  λ (lo : Nat). λ (cnt : Nat). λ (l : List Nat).
    TakeExtBounded lo (PartitionRangeL lo cnt l) l
      (LenPartitionRangeL lo cnt l)
      (λ (k : Nat). λ (hk : Le (S k) lo). NthPartitionRangeLLt lo k hk cnt l) }
def TakeLoPartitionTy : Term := prog{
  Π (lo : Nat) → Π (cnt : Nat) → Π (l : List Nat) →
    Id (List Nat) (Take lo (PartitionRangeL lo cnt l)) (Take lo l) }

def DropSuffixPartition : Term := prog{
  λ (lo : Nat). λ (cnt : Nat). λ (l : List Nat).
    ListExt (Drop cnt (Drop lo (PartitionRangeL lo cnt l))) (Drop cnt (Drop lo l))
      (LenDropCong cnt (Drop lo (PartitionRangeL lo cnt l)) (Drop lo l)
        (LenDropCong lo (PartitionRangeL lo cnt l) l (LenPartitionRangeL lo cnt l)))
      (λ (k : Nat).
        IdTrans Nat
          (NthL k (Drop cnt (Drop lo (PartitionRangeL lo cnt l))))
          (NthL (Add lo (Add cnt k)) (PartitionRangeL lo cnt l))
          (NthL k (Drop cnt (Drop lo l)))
          (IdTrans Nat
            (NthL k (Drop cnt (Drop lo (PartitionRangeL lo cnt l))))
            (NthL (Add cnt k) (Drop lo (PartitionRangeL lo cnt l)))
            (NthL (Add lo (Add cnt k)) (PartitionRangeL lo cnt l))
            (NthDrop cnt k (Drop lo (PartitionRangeL lo cnt l)))
            (NthDrop lo (Add cnt k) (PartitionRangeL lo cnt l)))
          (IdTrans Nat
            (NthL (Add lo (Add cnt k)) (PartitionRangeL lo cnt l))
            (NthL (Add lo (Add cnt k)) l)
            (NthL k (Drop cnt (Drop lo l)))
            (NthPartitionRangeLGe lo (Add lo (Add cnt k)) cnt l
              (LeAddMonoL lo cnt (Add cnt k) (LeAdd cnt k)))
            (IdTrans Nat
              (NthL (Add lo (Add cnt k)) l)
              (NthL (Add cnt k) (Drop lo l))
              (NthL k (Drop cnt (Drop lo l)))
              (IdSym Nat (NthL (Add cnt k) (Drop lo l)) (NthL (Add lo (Add cnt k)) l) (NthDrop lo (Add cnt k) l))
              (IdSym Nat (NthL k (Drop cnt (Drop lo l))) (NthL (Add cnt k) (Drop lo l)) (NthDrop cnt k (Drop lo l)))))) }
def DropSuffixPartitionTy : Term := prog{
  Π (lo : Nat) → Π (cnt : Nat) → Π (l : List Nat) →
    Id (List Nat) (Drop cnt (Drop lo (PartitionRangeL lo cnt l))) (Drop cnt (Drop lo l)) }

-- THE GOALS: the segment multiset survives the range sort and partition.
def SegCountSortRangeL : Term := prog{
  λ (x : Nat). λ (fuel : Nat). λ (lo : Nat). λ (cnt : Nat). λ (l : List Nat).
    λ (hb : Le (Add lo cnt) (Len l)).
      SegGlue x lo cnt (SortRangeL fuel lo cnt l) l
        (CountSortRangeL x fuel lo cnt l hb)
        (TakeLoSort fuel lo cnt l)
        (DropSuffixSort fuel lo cnt l) }
def SegCountSortRangeLTy : Term := prog{
  Π (x : Nat) → Π (fuel : Nat) → Π (lo : Nat) → Π (cnt : Nat) → Π (l : List Nat) →
    Le (Add lo cnt) (Len l) →
    Id Nat (SegCount x lo cnt (SortRangeL fuel lo cnt l)) (SegCount x lo cnt l) }

def SegCountPartitionRangeL : Term := prog{
  λ (x : Nat). λ (lo : Nat). λ (cnt : Nat). λ (l : List Nat).
    λ (hb : Le (Add lo cnt) (Len l)).
      SegGlue x lo cnt (PartitionRangeL lo cnt l) l
        (CountPartitionRangeL lo x cnt l hb)
        (TakeLoPartition lo cnt l)
        (DropSuffixPartition lo cnt l) }
def SegCountPartitionRangeLTy : Term := prog{
  Π (x : Nat) → Π (lo : Nat) → Π (cnt : Nat) → Π (l : List Nat) →
    Le (Add lo cnt) (Len l) →
    Id Nat (SegCount x lo cnt (PartitionRangeL lo cnt l)) (SegCount x lo cnt l) }

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
  λ (lo : Nat). λ (m : Nat).
    IdTrans Nat (Add lo (S (S m))) (S (S (Add lo m))) (S (Add m (S lo)))
      (IdTrans Nat (Add lo (S (S m))) (S (Add lo (S m))) (S (S (Add lo m)))
        (AddSucc lo (S m))
        (IdCongr Nat Nat (λ (z : Nat). S z) (Add lo (S m)) (S (Add lo m)) (AddSucc lo m)))
      (IdSym Nat (S (Add m (S lo))) (S (S (Add lo m)))
        (IdTrans Nat (S (Add m (S lo))) (S (S (Add m lo))) (S (S (Add lo m)))
          (IdCongr Nat Nat (λ (z : Nat). S z) (Add m (S lo)) (S (Add m lo)) (AddSucc m lo))
          (IdCongr Nat Nat (λ (z : Nat). S z) (S (Add m lo)) (S (Add lo m))
            (IdCongr Nat Nat (λ (z : Nat). S z) (Add m lo) (Add lo m) (AddComm m lo))))) }
def PosBridgeSsTy : Term := prog{ Π (lo : Nat) → Π (m : Nat) → Id Nat (Add lo (S (S m))) (S (Add m (S lo))) }

-- BndSl : the scan swap's smaller index < larger index (S(lo+1+i) ≤ lo+1+i+(S g')).
def BndSl : Term := prog{
  λ (lo : Nat). λ (i : Nat). λ (g' : Nat).
    LeRwL (Add lo (S (Add i (S g')))) (Add lo (S (S i))) (S (Add lo (S i)))
      (AddSucc lo (S i))
      (LeAddMonoL lo (S (S i)) (S (Add i (S g')))
        (LeRwR (S i) (S (Add i g')) (Add i (S g'))
          (IdSym Nat (Add i (S g')) (S (Add i g')) (AddSucc i g'))
          (LeAdd i g'))) }
def BndSlTy : Term := prog{ Π (lo : Nat) → Π (i : Nat) → Π (g' : Nat) → Le (S (Add lo (S i))) (Add lo (S (Add i (S g')))) }

-- AllLeRBaseSwap : the pivot-placement swap at the base (i = S i') keeps [lo, lo+S i')
-- all ≤ pivot. Position lo gets the far ≤-element (NthSwapLLo + hL at i'), the interior
-- is unchanged (AllLeRCong via NthSwapLMid), assembled by AllLeRExtendLo.
def AllLeRBaseSwap : Term := prog{
  λ (pivot : Nat). λ (lo : Nat). λ (i' : Nat). λ (l : List Nat).
    λ (hL : AllLeR (S i') (S lo) pivot l).
      AllLeRExtendLo i' lo pivot (SwapL lo (Add lo (S i')) l)
        (LeRwL pivot (NthL (Add lo (S i')) l) (NthL lo (SwapL lo (Add lo (S i')) l))
          (IdSym Nat (NthL lo (SwapL lo (Add lo (S i')) l)) (NthL (Add lo (S i')) l)
            (NthSwapLLo lo (Add lo (S i')) l (LeAddSucc lo i')))
          (LeRwL pivot (NthL (Add i' (S lo)) l) (NthL (Add lo (S i')) l)
            (IdCongr Nat Nat (λ (q : Nat). NthL q l) (Add i' (S lo)) (Add lo (S i')) (AddSwapSucc i' lo))
            (hL i' (LeRefl (S i')))))
        (AllLeRCong i' (S lo) pivot l (SwapL lo (Add lo (S i')) l)
          (λ (m : Nat). λ (hm : Le (S m) i').
            NthSwapLMid lo (Add lo (S i')) (Add m (S lo)) l
              (LeAddL (S lo) m)
              (LeRwL (Add lo (S i')) (Add lo (S (S m))) (S (Add m (S lo)))
                (PosBridgeSs lo m)
                (LeAddMonoL lo (S (S m)) (S i') hm)))
          (λ (m : Nat). λ (hm : Le (S m) i'). hL m (LeUpR (S m) i' hm))) }
def AllLeRBaseSwapTy : Term := prog{
  Π (pivot : Nat) → Π (lo : Nat) → Π (i' : Nat) → Π (l : List Nat) →
    AllLeR (S i') (S lo) pivot l → AllLeR (S i') lo pivot (SwapL lo (Add lo (S i')) l) }

-- AllLeRStepTZ : True/g=0 step — the scan element (tested ≤ pivot) extends the ≤-region.
def AllLeRStepTZ : Term := prog{
  λ (pivot : Nat). λ (lo : Nat). λ (i : Nat). λ (l : List Nat).
    λ (e : Id Bool (Leb (NthL (Add lo (S (Add i Z))) l) pivot) True). λ (hL : AllLeR i (S lo) pivot l).
      AllLeRExtendFar i (S lo) pivot l hL
        (LeRwL pivot (NthL (Add lo (S (Add i Z))) l) (NthL (Add i (S lo)) l)
          (IdCongr Nat Nat (λ (q : Nat). NthL q l) (Add lo (S (Add i Z))) (Add i (S lo))
            (IdTrans Nat (Add lo (S (Add i Z))) (Add lo (S i)) (Add i (S lo))
              (IdCongr Nat Nat (λ (z : Nat). Add lo (S z)) (Add i Z) i (AddZero i))
              (IdSym Nat (Add i (S lo)) (Add lo (S i)) (AddSwapSucc i lo))))
          (LebTrueLe (NthL (Add lo (S (Add i Z))) l) pivot e)) }
def AllLeRStepTZTy : Term := prog{
  Π (pivot : Nat) → Π (lo : Nat) → Π (i : Nat) → Π (l : List Nat) →
    Id Bool (Leb (NthL (Add lo (S (Add i Z))) l) pivot) True → AllLeR i (S lo) pivot l → AllLeR (S i) (S lo) pivot l }

-- AllLeRStepSwap : True/g=S g' step — the scan swap moves the tested ≤-element to the
-- new boundary; interior unchanged (NthSwapLLt), new far element = old scan (NthSwapLLo).
def AllLeRStepSwap : Term := prog{
  λ (pivot : Nat). λ (lo : Nat). λ (i : Nat). λ (g' : Nat). λ (l : List Nat).
    λ (e : Id Bool (Leb (NthL (Add lo (S (Add i (S g')))) l) pivot) True). λ (hL : AllLeR i (S lo) pivot l).
      AllLeRExtendFar i (S lo) pivot (SwapL (Add lo (S i)) (Add lo (S (Add i (S g')))) l)
        (AllLeRCong i (S lo) pivot l (SwapL (Add lo (S i)) (Add lo (S (Add i (S g')))) l)
          (λ (m : Nat). λ (hm : Le (S m) i).
            NthSwapLLt (Add lo (S i)) (Add lo (S (Add i (S g')))) (Add m (S lo)) l
              (LeRwL (Add lo (S i)) (Add lo (S (S m))) (S (Add m (S lo)))
                (PosBridgeSs lo m)
                (LeAddMonoL lo (S (S m)) (S i) hm)))
          hL)
        (LeRwL pivot (NthL (Add lo (S (Add i (S g')))) l) (NthL (Add i (S lo)) (SwapL (Add lo (S i)) (Add lo (S (Add i (S g')))) l))
          (IdTrans Nat
            (NthL (Add lo (S (Add i (S g')))) l)
            (NthL (Add lo (S i)) (SwapL (Add lo (S i)) (Add lo (S (Add i (S g')))) l))
            (NthL (Add i (S lo)) (SwapL (Add lo (S i)) (Add lo (S (Add i (S g')))) l))
            (IdSym Nat (NthL (Add lo (S i)) (SwapL (Add lo (S i)) (Add lo (S (Add i (S g')))) l)) (NthL (Add lo (S (Add i (S g')))) l)
              (NthSwapLLo (Add lo (S i)) (Add lo (S (Add i (S g')))) l (BndSl lo i g')))
            (IdCongr Nat Nat (λ (q : Nat). NthL q (SwapL (Add lo (S i)) (Add lo (S (Add i (S g')))) l)) (Add lo (S i)) (Add i (S lo))
              (IdSym Nat (Add i (S lo)) (Add lo (S i)) (AddSwapSucc i lo))))
          (LebTrueLe (NthL (Add lo (S (Add i (S g')))) l) pivot e)) }
def AllLeRStepSwapTy : Term := prog{
  Π (pivot : Nat) → Π (lo : Nat) → Π (i : Nat) → Π (g' : Nat) → Π (l : List Nat) →
    Id Bool (Leb (NthL (Add lo (S (Add i (S g')))) l) pivot) True → AllLeR i (S lo) pivot l →
    AllLeR (S i) (S lo) pivot (SwapL (Add lo (S i)) (Add lo (S (Add i (S g')))) l) }

-- PartScanRangeLAllLeR : the scanned ≤-region [lo, lo+finalI) is all ≤ pivot. Induction
-- on k mirroring count_partScanRangeL's bound threading; the AllLeR precondition grows via
-- the step helpers (leb fact from remember-scrutinee, threaded through the g-elim); the base
-- converts to offset lo via AllLeRBaseSwap / AllLeREmpty.
def PartScanRangeLAllLeR : Term := prog{
  λ (pivot : Nat). λ (lo : Nat). λ (k : Nat).
    elim k return (λ (kz : Nat). Π (i : Nat) → Π (g : Nat) → Π (l : List Nat) →
        Le (Add lo (S (Add kz (Add i g)))) (Len l) →
        Id Nat (NthL lo l) pivot →
        AllLeR i (S lo) pivot l →
        AllLeR (PartScanIdxRangeL pivot lo kz i g l) lo pivot (PartScanRangeL pivot lo kz i g l)) {
      Z => λ (i : Nat). λ (g : Nat). λ (l : List Nat).
        λ (hle : Le (Add lo (S (Add Z (Add i g)))) (Len l)). λ (hpv : Id Nat (NthL lo l) pivot). λ (hL : AllLeR i (S lo) pivot l).
        elim i return (λ (iz : Nat).
            Le (Add lo (S (Add Z (Add iz g)))) (Len l) → Id Nat (NthL lo l) pivot → AllLeR iz (S lo) pivot l →
            AllLeR iz lo pivot (elim iz return (λ (iy : Nat). List Nat) { Z => l, S (i') iih => SwapL lo (Add lo (S i')) l })) {
          Z => λ (hle0 : Le (Add lo (S (Add Z (Add Z g)))) (Len l)). λ (hpv0 : Id Nat (NthL lo l) pivot). λ (hL0 : AllLeR Z (S lo) pivot l).
            AllLeREmpty lo pivot l,
          S (i') iih => λ (hle0 : Le (Add lo (S (Add Z (Add (S i') g)))) (Len l)). λ (hpv0 : Id Nat (NthL lo l) pivot). λ (hL0 : AllLeR (S i') (S lo) pivot l).
            AllLeRBaseSwap pivot lo i' l hL0
        } hle hpv hL,
      S (k') ih => λ (i : Nat). λ (g : Nat). λ (l : List Nat).
        λ (hle : Le (Add lo (S (Add (S k') (Add i g)))) (Len l)). λ (hpv : Id Nat (NthL lo l) pivot). λ (hL : AllLeR i (S lo) pivot l).
        elim (Leb (NthL (Add lo (S (Add i g))) l) pivot)
          return (λ (b : Bool). Id Bool (Leb (NthL (Add lo (S (Add i g))) l) pivot) b →
            AllLeR (elim b return (λ (bw : Bool). Nat) {
                True => elim g return (λ (gz : Nat). Nat) {
                  Z => PartScanIdxRangeL pivot lo k' (S i) Z l,
                  S (g') gih => PartScanIdxRangeL pivot lo k' (S i) (S g') (SwapL (Add lo (S i)) (Add lo (S (Add i g))) l) },
                False => PartScanIdxRangeL pivot lo k' i (S g) l }) lo pivot
              (elim b return (λ (bw : Bool). List Nat) {
                True => elim g return (λ (gz : Nat). List Nat) {
                  Z => PartScanRangeL pivot lo k' (S i) Z l,
                  S (g') gih => PartScanRangeL pivot lo k' (S i) (S g') (SwapL (Add lo (S i)) (Add lo (S (Add i g))) l) },
                False => PartScanRangeL pivot lo k' i (S g) l })) {
          True => λ (e : Id Bool (Leb (NthL (Add lo (S (Add i g))) l) pivot) True).
            (elim g return (λ (gz : Nat).
                Id Bool (Leb (NthL (Add lo (S (Add i gz))) l) pivot) True →
                Le (Add lo (S (Add (S k') (Add i gz)))) (Len l) →
                AllLeR (elim gz return (λ (gy : Nat). Nat) {
                    Z => PartScanIdxRangeL pivot lo k' (S i) Z l,
                    S (g') gih => PartScanIdxRangeL pivot lo k' (S i) (S g') (SwapL (Add lo (S i)) (Add lo (S (Add i gz))) l) }) lo pivot
                  (elim gz return (λ (gy : Nat). List Nat) {
                    Z => PartScanRangeL pivot lo k' (S i) Z l,
                    S (g') gih => PartScanRangeL pivot lo k' (S i) (S g') (SwapL (Add lo (S i)) (Add lo (S (Add i gz))) l) })) {
              Z => λ (e0 : Id Bool (Leb (NthL (Add lo (S (Add i Z))) l) pivot) True). λ (hleZ : Le (Add lo (S (Add (S k') (Add i Z)))) (Len l)).
                ih (S i) Z l
                  (LeRwL (Len l) (Add lo (S (Add (S k') (Add i Z)))) (Add lo (S (Add k' (Add (S i) Z))))
                    (IdCongr Nat Nat (λ (a : Nat). Add lo (S a)) (Add (S k') (Add i Z)) (Add k' (Add (S i) Z)) (HshiftTrue k' i Z))
                    hleZ)
                  hpv
                  (AllLeRStepTZ pivot lo i l e0 hL),
              S (g') gih => λ (e0 : Id Bool (Leb (NthL (Add lo (S (Add i (S g')))) l) pivot) True). λ (hleS : Le (Add lo (S (Add (S k') (Add i (S g'))))) (Len l)).
                ih (S i) (S g') (SwapL (Add lo (S i)) (Add lo (S (Add i (S g')))) l)
                  (LeRwR (Add lo (S (Add k' (Add (S i) (S g'))))) (Len l)
                     (Len (SwapL (Add lo (S i)) (Add lo (S (Add i (S g')))) l))
                     (IdSym Nat (Len (SwapL (Add lo (S i)) (Add lo (S (Add i (S g')))) l)) (Len l)
                       (LenSwapL (Add lo (S i)) (Add lo (S (Add i (S g')))) l))
                     (LeRwL (Len l) (Add lo (S (Add (S k') (Add i (S g'))))) (Add lo (S (Add k' (Add (S i) (S g')))))
                       (IdCongr Nat Nat (λ (a : Nat). Add lo (S a)) (Add (S k') (Add i (S g'))) (Add k' (Add (S i) (S g'))) (HshiftTrue k' i (S g')))
                       hleS))
                  (IdTrans Nat (NthL lo (SwapL (Add lo (S i)) (Add lo (S (Add i (S g')))) l)) (NthL lo l) pivot
                    (NthSwapLLt (Add lo (S i)) (Add lo (S (Add i (S g')))) lo l (LeAddSucc lo i))
                    hpv)
                  (AllLeRStepSwap pivot lo i g' l e0 hL)
            }) e hle,
          False => λ (efalse : Id Bool (Leb (NthL (Add lo (S (Add i g))) l) pivot) False).
            ih i (S g) l
              (LeRwL (Len l) (Add lo (S (Add (S k') (Add i g)))) (Add lo (S (Add k' (Add i (S g)))))
                (IdCongr Nat Nat (λ (a : Nat). Add lo (S a)) (Add (S k') (Add i g)) (Add k' (Add i (S g))) (HshiftFalse k' i g))
                hle)
              hpv
              hL
        } Refl
    } }
def PartScanRangeLAllLeRTy : Term := prog{
  Π (pivot : Nat) → Π (lo : Nat) → Π (k : Nat) → Π (i : Nat) → Π (g : Nat) → Π (l : List Nat) →
    Le (Add lo (S (Add k (Add i g)))) (Len l) →
    Id Nat (NthL lo l) pivot →
    AllLeR i (S lo) pivot l →
    AllLeR (PartScanIdxRangeL pivot lo k i g l) lo pivot (PartScanRangeL pivot lo k i g l) }
/-! ## AllGtR (gap-side) region invariant — the mirror of the ≤-region (§22, M22-c step 2)

    The gap's OFFSET shifts each step (`Add (S i) lo` → `Add (S (S i)) lo`), unlike the
    ≤-region's fixed `S lo`, and the asymmetry flips: the gap GROWS in the False branch
    (scan element > pivot, `AllGtRStepFalse` via LebFalseGt + extend_far), the True/Sg'
    swap ROTATES the old boundary (first gap element) to the gap's far end
    (`AllGtRStepSwap` via NthSwapLHi, needing a len bound), and True/g=0 is the empty
    gap (`AllGtREmpty`). `OffBridge` / `PosBridgeScan` / `BndGapUpper` carry the
    (messier) offset arithmetic. -/

def AllGtRExtendFar : Term := prog{
  λ (w : Nat). λ (lo : Nat). λ (p : Nat). λ (l : List Nat).
    λ (h : AllGtR w lo p l). λ (hnew : Le (S p) (NthL (Add w lo) l)).
    λ (m : Nat).
      elim (Leb (S m) w) return (λ (b : Bool). Id Bool (Leb (S m) w) b → Le (S m) (S w) → Le (S p) (NthL (Add m lo) l)) {
        True => λ (e : Id Bool (Leb (S m) w) True). λ (hm : Le (S m) (S w)). h m (LebTrueLe (S m) w e),
        False => λ (e : Id Bool (Leb (S m) w) False). λ (hm : Le (S m) (S w)).
          LeRwR (S p) (NthL (Add w lo) l) (NthL (Add m lo) l)
            (IdCongr Nat Nat (λ (q : Nat). NthL q l) (Add w lo) (Add m lo)
              (IdCongr Nat Nat (λ (z : Nat). Add z lo) w m (IdSym Nat m w (LeAntisym m w hm (LebFalseGt (S m) w e)))))
            hnew
      } Refl }
def AllGtRExtendFarTy : Term := prog{
  Π (w : Nat) → Π (lo : Nat) → Π (p : Nat) → Π (l : List Nat) →
    AllGtR w lo p l → Le (S p) (NthL (Add w lo) l) → AllGtR (S w) lo p l }

def AllGtRCong : Term := prog{
  λ (w : Nat). λ (off : Nat). λ (p : Nat). λ (l : List Nat). λ (l' : List Nat).
    λ (heq : Π (m : Nat) → Le (S m) w → Id Nat (NthL (Add m off) l') (NthL (Add m off) l)).
    λ (h : AllGtR w off p l).
    λ (m : Nat). λ (hm : Le (S m) w).
      LeRwR (S p) (NthL (Add m off) l) (NthL (Add m off) l')
        (IdSym Nat (NthL (Add m off) l') (NthL (Add m off) l) (heq m hm))
        (h m hm) }
def AllGtRCongTy : Term := prog{
  Π (w : Nat) → Π (off : Nat) → Π (p : Nat) → Π (l : List Nat) → Π (l' : List Nat) →
    (Π (m : Nat) → Le (S m) w → Id Nat (NthL (Add m off) l') (NthL (Add m off) l)) →
    AllGtR w off p l → AllGtR w off p l' }

def OffBridge : Term := prog{
  λ (lo : Nat). λ (i' : Nat).
    IdCongr Nat Nat (λ (z : Nat). S z) (S (Add i' lo)) (Add lo (S i'))
      (IdTrans Nat (S (Add i' lo)) (S (Add lo i')) (Add lo (S i'))
        (IdCongr Nat Nat (λ (z : Nat). S z) (Add i' lo) (Add lo i') (AddComm i' lo))
        (IdSym Nat (Add lo (S i')) (S (Add lo i')) (AddSucc lo i'))) }
def OffBridgeTy : Term := prog{ Π (lo : Nat) → Π (i' : Nat) → Id Nat (Add (S (S i')) lo) (S (Add lo (S i'))) }

def AllGtRBaseSwap : Term := prog{
  λ (pivot : Nat). λ (lo : Nat). λ (i' : Nat). λ (g : Nat). λ (l : List Nat).
    λ (hG : AllGtR g (Add (S (S i')) lo) pivot l).
      AllGtRCong g (Add (S (S i')) lo) pivot l (SwapL lo (Add lo (S i')) l)
        (λ (m : Nat). λ (hm : Le (S m) g).
          NthSwapLGt lo (Add lo (S i')) (Add m (Add (S (S i')) lo)) l
            (LeRwL (Add m (Add (S (S i')) lo)) (Add (S (S i')) lo) (S (Add lo (S i')))
              (OffBridge lo i')
              (LeAddL (Add (S (S i')) lo) m)))
        hG }
def AllGtRBaseSwapTy : Term := prog{
  Π (pivot : Nat) → Π (lo : Nat) → Π (i' : Nat) → Π (g : Nat) → Π (l : List Nat) →
    AllGtR g (Add (S (S i')) lo) pivot l → AllGtR g (Add (S (S i')) lo) pivot (SwapL lo (Add lo (S i')) l) }

def PosBridgeScan : Term := prog{
  λ (lo : Nat). λ (i : Nat). λ (g : Nat).
    IdTrans Nat (Add lo (S (Add i g))) (S (Add lo (Add i g))) (Add g (Add (S i) lo))
      (AddSucc lo (Add i g))
      (IdTrans Nat (S (Add lo (Add i g))) (S (Add g (Add i lo))) (Add g (Add (S i) lo))
        (IdCongr Nat Nat (λ (z : Nat). S z) (Add lo (Add i g)) (Add g (Add i lo))
          (IdTrans Nat (Add lo (Add i g)) (Add (Add lo i) g) (Add g (Add i lo))
            (IdSym Nat (Add (Add lo i) g) (Add lo (Add i g)) (AddAssoc lo i g))
            (IdTrans Nat (Add (Add lo i) g) (Add g (Add lo i)) (Add g (Add i lo))
              (AddComm (Add lo i) g)
              (IdCongr Nat Nat (λ (z : Nat). Add g z) (Add lo i) (Add i lo) (AddComm lo i)))))
        (IdSym Nat (Add g (Add (S i) lo)) (S (Add g (Add i lo))) (AddSucc g (Add i lo)))) }
def PosBridgeScanTy : Term := prog{ Π (lo : Nat) → Π (i : Nat) → Π (g : Nat) → Id Nat (Add lo (S (Add i g))) (Add g (Add (S i) lo)) }

def AllGtRStepFalse : Term := prog{
  λ (pivot : Nat). λ (lo : Nat). λ (i : Nat). λ (g : Nat). λ (l : List Nat).
    λ (efalse : Id Bool (Leb (NthL (Add lo (S (Add i g))) l) pivot) False). λ (hG : AllGtR g (Add (S i) lo) pivot l).
      AllGtRExtendFar g (Add (S i) lo) pivot l hG
        (LeRwR (S pivot) (NthL (Add lo (S (Add i g))) l) (NthL (Add g (Add (S i) lo)) l)
          (IdCongr Nat Nat (λ (q : Nat). NthL q l) (Add lo (S (Add i g))) (Add g (Add (S i) lo)) (PosBridgeScan lo i g))
          (LebFalseGt (NthL (Add lo (S (Add i g))) l) pivot efalse)) }
def AllGtRStepFalseTy : Term := prog{
  Π (pivot : Nat) → Π (lo : Nat) → Π (i : Nat) → Π (g : Nat) → Π (l : List Nat) →
    Id Bool (Leb (NthL (Add lo (S (Add i g))) l) pivot) False → AllGtR g (Add (S i) lo) pivot l →
    AllGtR (S g) (Add (S i) lo) pivot l }

def BndGapUpper : Term := prog{
  λ (lo : Nat). λ (i : Nat). λ (g' : Nat). λ (m : Nat). λ (hm : Le (S m) g').
    LeRwR (S (Add m (Add (S (S i)) lo))) (Add lo (S (S (Add i g')))) (Add lo (S (Add i (S g'))))
      (IdCongr Nat Nat (λ (z : Nat). Add lo (S z)) (S (Add i g')) (Add i (S g')) (IdSym Nat (Add i (S g')) (S (Add i g')) (AddSucc i g')))
      (LeRwL (Add lo (S (S (Add i g')))) (Add lo (S (S (S (Add i m))))) (S (Add m (Add (S (S i)) lo)))
        (IdTrans Nat (Add lo (S (S (S (Add i m))))) (S (Add lo (S (S (Add i m))))) (S (Add m (Add (S (S i)) lo)))
          (AddSucc lo (S (S (Add i m))))
          (IdCongr Nat Nat (λ (z : Nat). S z) (Add lo (S (S (Add i m)))) (Add m (Add (S (S i)) lo)) (PosBridgeScan lo (S i) m)))
        (LeAddMonoL lo (S (S (S (Add i m)))) (S (S (Add i g')))
          (LeRwL (Add i g') (Add i (S m)) (S (Add i m)) (AddSucc i m) (LeAddMonoL i (S m) g' hm)))) }
def BndGapUpperTy : Term := prog{
  Π (lo : Nat) → Π (i : Nat) → Π (g' : Nat) → Π (m : Nat) → Le (S m) g' →
    Le (S (Add m (Add (S (S i)) lo))) (Add lo (S (Add i (S g')))) }

def AllGtRStepSwap : Term := prog{
  λ (pivot : Nat). λ (lo : Nat). λ (i : Nat). λ (g' : Nat). λ (l : List Nat).
    λ (hlen : Le (S (Add lo (S (Add i (S g'))))) (Len l)).
    λ (e : Id Bool (Leb (NthL (Add lo (S (Add i (S g')))) l) pivot) True). λ (hG : AllGtR (S g') (Add (S i) lo) pivot l).
      AllGtRExtendFar g' (Add (S (S i)) lo) pivot (SwapL (Add lo (S i)) (Add lo (S (Add i (S g')))) l)
        (AllGtRCong g' (Add (S (S i)) lo) pivot l (SwapL (Add lo (S i)) (Add lo (S (Add i (S g')))) l)
          (λ (m : Nat). λ (hm : Le (S m) g').
            NthSwapLMid (Add lo (S i)) (Add lo (S (Add i (S g')))) (Add m (Add (S (S i)) lo)) l
              (LeRwL (Add m (Add (S (S i)) lo)) (Add (S (S i)) lo) (S (Add lo (S i)))
                (OffBridge lo i)
                (LeAddL (Add (S (S i)) lo) m))
              (BndGapUpper lo i g' m hm))
          (λ (m : Nat). λ (hm : Le (S m) g').
            LeRwR (S pivot) (NthL (Add (S m) (Add (S i) lo)) l) (NthL (Add m (Add (S (S i)) lo)) l)
              (IdCongr Nat Nat (λ (q : Nat). NthL q l) (Add (S m) (Add (S i) lo)) (Add m (Add (S (S i)) lo))
                (IdSym Nat (Add m (Add (S (S i)) lo)) (Add (S m) (Add (S i) lo)) (AddSucc m (S (Add i lo)))))
              (hG (S m) hm)))
        (LeRwR (S pivot) (NthL (Add lo (S i)) l) (NthL (Add g' (Add (S (S i)) lo)) (SwapL (Add lo (S i)) (Add lo (S (Add i (S g')))) l))
          (IdTrans Nat
            (NthL (Add lo (S i)) l)
            (NthL (Add lo (S (Add i (S g')))) (SwapL (Add lo (S i)) (Add lo (S (Add i (S g')))) l))
            (NthL (Add g' (Add (S (S i)) lo)) (SwapL (Add lo (S i)) (Add lo (S (Add i (S g')))) l))
            (IdSym Nat (NthL (Add lo (S (Add i (S g')))) (SwapL (Add lo (S i)) (Add lo (S (Add i (S g')))) l)) (NthL (Add lo (S i)) l)
              (NthSwapLHi (Add lo (S i)) (Add lo (S (Add i (S g')))) l (BndSl lo i g') hlen))
            (IdCongr Nat Nat (λ (q : Nat). NthL q (SwapL (Add lo (S i)) (Add lo (S (Add i (S g')))) l)) (Add lo (S (Add i (S g')))) (Add g' (Add (S (S i)) lo))
              (IdTrans Nat (Add lo (S (Add i (S g')))) (Add lo (S (S (Add i g')))) (Add g' (Add (S (S i)) lo))
                (IdCongr Nat Nat (λ (z : Nat). Add lo (S z)) (Add i (S g')) (S (Add i g')) (AddSucc i g'))
                (PosBridgeScan lo (S i) g'))))
          (LeRwR (S pivot) (NthL (Add (S i) lo) l) (NthL (Add lo (S i)) l)
            (IdCongr Nat Nat (λ (q : Nat). NthL q l) (Add (S i) lo) (Add lo (S i)) (AddComm (S i) lo))
            (AllGtRHead g' (Add (S i) lo) pivot l hG))) }
def AllGtRStepSwapTy : Term := prog{
  Π (pivot : Nat) → Π (lo : Nat) → Π (i : Nat) → Π (g' : Nat) → Π (l : List Nat) →
    Le (S (Add lo (S (Add i (S g'))))) (Len l) →
    Id Bool (Leb (NthL (Add lo (S (Add i (S g')))) l) pivot) True → AllGtR (S g') (Add (S i) lo) pivot l →
    AllGtR (S g') (Add (S (S i)) lo) pivot (SwapL (Add lo (S i)) (Add lo (S (Add i (S g')))) l) }

-- PartScanRangeLAllGtR : the scanned gap [lo+1+finalI, …) is all > pivot. Mirror of allLeR;
-- the conclusion OFFSET also depends on leb (motive carries three elim b). NOTE the True arm
-- threads hG through the g-elim (the precondition is indexed by g, refined to S g' in the swap
-- branch) — unlike allLeR whose precondition was indexed by i.
def PartScanRangeLAllGtR : Term := prog{
  λ (pivot : Nat). λ (lo : Nat). λ (k : Nat).
    elim k return (λ (kz : Nat). Π (i : Nat) → Π (g : Nat) → Π (l : List Nat) →
        Le (Add lo (S (Add kz (Add i g)))) (Len l) →
        Id Nat (NthL lo l) pivot →
        AllGtR g (Add (S i) lo) pivot l →
        AllGtR (PartScanGapRangeL pivot lo kz i g l) (Add (S (PartScanIdxRangeL pivot lo kz i g l)) lo) pivot (PartScanRangeL pivot lo kz i g l)) {
      Z => λ (i : Nat). λ (g : Nat). λ (l : List Nat).
        λ (hle : Le (Add lo (S (Add Z (Add i g)))) (Len l)). λ (hpv : Id Nat (NthL lo l) pivot). λ (hG : AllGtR g (Add (S i) lo) pivot l).
        elim i return (λ (iz : Nat).
            Le (Add lo (S (Add Z (Add iz g)))) (Len l) → Id Nat (NthL lo l) pivot → AllGtR g (Add (S iz) lo) pivot l →
            AllGtR g (Add (S iz) lo) pivot (elim iz return (λ (iy : Nat). List Nat) { Z => l, S (i') iih => SwapL lo (Add lo (S i')) l })) {
          Z => λ (hle0 : Le (Add lo (S (Add Z (Add Z g)))) (Len l)). λ (hpv0 : Id Nat (NthL lo l) pivot). λ (hG0 : AllGtR g (Add (S Z) lo) pivot l).
            hG0,
          S (i') iih => λ (hle0 : Le (Add lo (S (Add Z (Add (S i') g)))) (Len l)). λ (hpv0 : Id Nat (NthL lo l) pivot). λ (hG0 : AllGtR g (Add (S (S i')) lo) pivot l).
            AllGtRBaseSwap pivot lo i' g l hG0
        } hle hpv hG,
      S (k') ih => λ (i : Nat). λ (g : Nat). λ (l : List Nat).
        λ (hle : Le (Add lo (S (Add (S k') (Add i g)))) (Len l)). λ (hpv : Id Nat (NthL lo l) pivot). λ (hG : AllGtR g (Add (S i) lo) pivot l).
        elim (Leb (NthL (Add lo (S (Add i g))) l) pivot)
          return (λ (b : Bool). Id Bool (Leb (NthL (Add lo (S (Add i g))) l) pivot) b →
            AllGtR (elim b return (λ (bw : Bool). Nat) {
                True => elim g return (λ (gz : Nat). Nat) {
                  Z => PartScanGapRangeL pivot lo k' (S i) Z l,
                  S (g') gih => PartScanGapRangeL pivot lo k' (S i) (S g') (SwapL (Add lo (S i)) (Add lo (S (Add i g))) l) },
                False => PartScanGapRangeL pivot lo k' i (S g) l })
              (Add (S (elim b return (λ (bw : Bool). Nat) {
                True => elim g return (λ (gz : Nat). Nat) {
                  Z => PartScanIdxRangeL pivot lo k' (S i) Z l,
                  S (g') gih => PartScanIdxRangeL pivot lo k' (S i) (S g') (SwapL (Add lo (S i)) (Add lo (S (Add i g))) l) },
                False => PartScanIdxRangeL pivot lo k' i (S g) l })) lo) pivot
              (elim b return (λ (bw : Bool). List Nat) {
                True => elim g return (λ (gz : Nat). List Nat) {
                  Z => PartScanRangeL pivot lo k' (S i) Z l,
                  S (g') gih => PartScanRangeL pivot lo k' (S i) (S g') (SwapL (Add lo (S i)) (Add lo (S (Add i g))) l) },
                False => PartScanRangeL pivot lo k' i (S g) l })) {
          True => λ (e : Id Bool (Leb (NthL (Add lo (S (Add i g))) l) pivot) True).
            (elim g return (λ (gz : Nat).
                Id Bool (Leb (NthL (Add lo (S (Add i gz))) l) pivot) True →
                Le (Add lo (S (Add (S k') (Add i gz)))) (Len l) →
                AllGtR gz (Add (S i) lo) pivot l →
                AllGtR (elim gz return (λ (gy : Nat). Nat) {
                    Z => PartScanGapRangeL pivot lo k' (S i) Z l,
                    S (g') gih => PartScanGapRangeL pivot lo k' (S i) (S g') (SwapL (Add lo (S i)) (Add lo (S (Add i gz))) l) })
                  (Add (S (elim gz return (λ (gy : Nat). Nat) {
                    Z => PartScanIdxRangeL pivot lo k' (S i) Z l,
                    S (g') gih => PartScanIdxRangeL pivot lo k' (S i) (S g') (SwapL (Add lo (S i)) (Add lo (S (Add i gz))) l) })) lo) pivot
                  (elim gz return (λ (gy : Nat). List Nat) {
                    Z => PartScanRangeL pivot lo k' (S i) Z l,
                    S (g') gih => PartScanRangeL pivot lo k' (S i) (S g') (SwapL (Add lo (S i)) (Add lo (S (Add i gz))) l) })) {
              Z => λ (e0 : Id Bool (Leb (NthL (Add lo (S (Add i Z))) l) pivot) True). λ (hleZ : Le (Add lo (S (Add (S k') (Add i Z)))) (Len l)). λ (hG0 : AllGtR Z (Add (S i) lo) pivot l).
                ih (S i) Z l
                  (LeRwL (Len l) (Add lo (S (Add (S k') (Add i Z)))) (Add lo (S (Add k' (Add (S i) Z))))
                    (IdCongr Nat Nat (λ (a : Nat). Add lo (S a)) (Add (S k') (Add i Z)) (Add k' (Add (S i) Z)) (HshiftTrue k' i Z))
                    hleZ)
                  hpv
                  (AllGtREmpty (Add (S (S i)) lo) pivot l),
              S (g') gih => λ (e0 : Id Bool (Leb (NthL (Add lo (S (Add i (S g')))) l) pivot) True). λ (hleS : Le (Add lo (S (Add (S k') (Add i (S g'))))) (Len l)). λ (hG0 : AllGtR (S g') (Add (S i) lo) pivot l).
                ih (S i) (S g') (SwapL (Add lo (S i)) (Add lo (S (Add i (S g')))) l)
                  (LeRwR (Add lo (S (Add k' (Add (S i) (S g'))))) (Len l)
                     (Len (SwapL (Add lo (S i)) (Add lo (S (Add i (S g')))) l))
                     (IdSym Nat (Len (SwapL (Add lo (S i)) (Add lo (S (Add i (S g')))) l)) (Len l)
                       (LenSwapL (Add lo (S i)) (Add lo (S (Add i (S g')))) l))
                     (LeRwL (Len l) (Add lo (S (Add (S k') (Add i (S g'))))) (Add lo (S (Add k' (Add (S i) (S g')))))
                       (IdCongr Nat Nat (λ (a : Nat). Add lo (S a)) (Add (S k') (Add i (S g'))) (Add k' (Add (S i) (S g'))) (HshiftTrue k' i (S g')))
                       hleS))
                  (IdTrans Nat (NthL lo (SwapL (Add lo (S i)) (Add lo (S (Add i (S g')))) l)) (NthL lo l) pivot
                    (NthSwapLLt (Add lo (S i)) (Add lo (S (Add i (S g')))) lo l (LeAddSucc lo i))
                    hpv)
                  (AllGtRStepSwap pivot lo i g' l
                    (LeTrans (S (Add lo (S (Add i (S g'))))) (Add lo (S (S (Add k' (Add i (S g')))))) (Len l)
                      (LeRwL (Add lo (S (S (Add k' (Add i (S g'))))))
                        (Add lo (S (S (Add i (S g'))))) (S (Add lo (S (Add i (S g')))))
                        (AddSucc lo (S (Add i (S g'))))
                        (LeAddMonoL lo (S (S (Add i (S g')))) (S (S (Add k' (Add i (S g')))))
                          (LeAddL (Add i (S g')) k')))
                      hleS)
                    e0 hG0)
            }) e hle hG,
          False => λ (efalse : Id Bool (Leb (NthL (Add lo (S (Add i g))) l) pivot) False).
            ih i (S g) l
              (LeRwL (Len l) (Add lo (S (Add (S k') (Add i g)))) (Add lo (S (Add k' (Add i (S g)))))
                (IdCongr Nat Nat (λ (a : Nat). Add lo (S a)) (Add (S k') (Add i g)) (Add k' (Add i (S g))) (HshiftFalse k' i g))
                hle)
              hpv
              (AllGtRStepFalse pivot lo i g l efalse hG)
        } Refl
    } }
def PartScanRangeLAllGtRTy : Term := prog{
  Π (pivot : Nat) → Π (lo : Nat) → Π (k : Nat) → Π (i : Nat) → Π (g : Nat) → Π (l : List Nat) →
    Le (Add lo (S (Add k (Add i g)))) (Len l) →
    Id Nat (NthL lo l) pivot →
    AllGtR g (Add (S i) lo) pivot l →
    AllGtR (PartScanGapRangeL pivot lo k i g l) (Add (S (PartScanIdxRangeL pivot lo k i g l)) lo) pivot (PartScanRangeL pivot lo k i g l) }
-- The pivot ends at position `Add finalI lo`. Induction on k mirroring
-- count_partScanRangeL's bound threading, PLUS threading the pivot-fact
-- `Id (NthL lo l) pivot` (updated across the step swap via NthSwapLLt — lo is below
-- both swap indices). Base (k=Z) places the pivot: i=Z is the pivot-fact directly;
-- i=S i' swaps lo↔lo+i, so NthSwapLHi reads old-lo (=pivot) at the boundary, bridged
-- from index-first `Add (S i') lo` to offset-first `Add lo (S i')` by AddComm.
def PartScanRangeLPivot : Term := prog{
  λ (pivot : Nat). λ (lo : Nat). λ (k : Nat).
    elim k return (λ (kz : Nat). Π (i : Nat) → Π (g : Nat) → Π (l : List Nat) →
        Le (Add lo (S (Add kz (Add i g)))) (Len l) →
        Id Nat (NthL lo l) pivot →
        Id Nat (NthL (Add (PartScanIdxRangeL pivot lo kz i g l) lo) (PartScanRangeL pivot lo kz i g l)) pivot) {
      Z => λ (i : Nat). λ (g : Nat). λ (l : List Nat).
        λ (hle : Le (Add lo (S (Add Z (Add i g)))) (Len l)). λ (hpv : Id Nat (NthL lo l) pivot).
        elim i return (λ (iz : Nat).
            Le (Add lo (S (Add Z (Add iz g)))) (Len l) →
            Id Nat (NthL (Add iz lo) (elim iz return (λ (iy : Nat). List Nat) { Z => l, S (i') iih => SwapL lo (Add lo (S i')) l })) pivot) {
          Z => λ (hle0 : Le (Add lo (S (Add Z (Add Z g)))) (Len l)). hpv,
          S (i') iih => λ (hle0 : Le (Add lo (S (Add Z (Add (S i') g)))) (Len l)).
            IdTrans Nat
              (NthL (Add (S i') lo) (SwapL lo (Add lo (S i')) l))
              (NthL (Add lo (S i')) (SwapL lo (Add lo (S i')) l))
              pivot
              (IdCongr Nat Nat (λ (p : Nat). NthL p (SwapL lo (Add lo (S i')) l)) (Add (S i') lo) (Add lo (S i')) (AddComm (S i') lo))
              (IdTrans Nat
                (NthL (Add lo (S i')) (SwapL lo (Add lo (S i')) l))
                (NthL lo l)
                pivot
                (NthSwapLHi lo (Add lo (S i')) l (LeAddSucc lo i')
                  (LeTrans (S (Add lo (S i'))) (Add lo (S (S (Add i' g)))) (Len l)
                    (LeRwL (Add lo (S (S (Add i' g)))) (Add lo (S (S i'))) (S (Add lo (S i')))
                      (AddSucc lo (S i'))
                      (LeAddMonoL lo (S (S i')) (S (S (Add i' g))) (LeAdd i' g)))
                    hle0))
                hpv)
        } hle,
      S (k') ih => λ (i : Nat). λ (g : Nat). λ (l : List Nat).
        λ (hle : Le (Add lo (S (Add (S k') (Add i g)))) (Len l)). λ (hpv : Id Nat (NthL lo l) pivot).
        elim (Leb (NthL (Add lo (S (Add i g))) l) pivot)
          return (λ (w : Bool). Id Nat
            (NthL (Add (elim w return (λ (ww : Bool). Nat) {
                True => elim g return (λ (gz : Nat). Nat) {
                  Z => PartScanIdxRangeL pivot lo k' (S i) Z l,
                  S (g') gih => PartScanIdxRangeL pivot lo k' (S i) (S g') (SwapL (Add lo (S i)) (Add lo (S (Add i g))) l) },
                False => PartScanIdxRangeL pivot lo k' i (S g) l }) lo)
              (elim w return (λ (ww : Bool). List Nat) {
                True => elim g return (λ (gz : Nat). List Nat) {
                  Z => PartScanRangeL pivot lo k' (S i) Z l,
                  S (g') gih => PartScanRangeL pivot lo k' (S i) (S g') (SwapL (Add lo (S i)) (Add lo (S (Add i g))) l) },
                False => PartScanRangeL pivot lo k' i (S g) l }))
            pivot) {
          True =>
            (elim g return (λ (gz : Nat).
                Le (Add lo (S (Add (S k') (Add i gz)))) (Len l) →
                Id Nat (NthL (Add (elim gz return (λ (gy : Nat). Nat) {
                    Z => PartScanIdxRangeL pivot lo k' (S i) Z l,
                    S (g') gih => PartScanIdxRangeL pivot lo k' (S i) (S g') (SwapL (Add lo (S i)) (Add lo (S (Add i gz))) l) }) lo)
                  (elim gz return (λ (gy : Nat). List Nat) {
                    Z => PartScanRangeL pivot lo k' (S i) Z l,
                    S (g') gih => PartScanRangeL pivot lo k' (S i) (S g') (SwapL (Add lo (S i)) (Add lo (S (Add i gz))) l) })) pivot) {
              Z => λ (hleZ : Le (Add lo (S (Add (S k') (Add i Z)))) (Len l)).
                ih (S i) Z l
                  (LeRwL (Len l)
                    (Add lo (S (Add (S k') (Add i Z))))
                    (Add lo (S (Add k' (Add (S i) Z))))
                    (IdCongr Nat Nat (λ (a : Nat). Add lo (S a))
                      (Add (S k') (Add i Z)) (Add k' (Add (S i) Z)) (HshiftTrue k' i Z))
                    hleZ)
                  hpv,
              S (g') gih => λ (hleS : Le (Add lo (S (Add (S k') (Add i (S g'))))) (Len l)).
                ih (S i) (S g') (SwapL (Add lo (S i)) (Add lo (S (Add i (S g')))) l)
                  (LeRwR (Add lo (S (Add k' (Add (S i) (S g'))))) (Len l)
                     (Len (SwapL (Add lo (S i)) (Add lo (S (Add i (S g')))) l))
                     (IdSym Nat (Len (SwapL (Add lo (S i)) (Add lo (S (Add i (S g')))) l)) (Len l)
                       (LenSwapL (Add lo (S i)) (Add lo (S (Add i (S g')))) l))
                     (LeRwL (Len l)
                       (Add lo (S (Add (S k') (Add i (S g')))))
                       (Add lo (S (Add k' (Add (S i) (S g')))))
                       (IdCongr Nat Nat (λ (a : Nat). Add lo (S a))
                         (Add (S k') (Add i (S g'))) (Add k' (Add (S i) (S g'))) (HshiftTrue k' i (S g')))
                       hleS))
                  (IdTrans Nat (NthL lo (SwapL (Add lo (S i)) (Add lo (S (Add i (S g')))) l)) (NthL lo l) pivot
                    (NthSwapLLt (Add lo (S i)) (Add lo (S (Add i (S g')))) lo l (LeAddSucc lo i))
                    hpv)
            }) hle,
          False =>
            ih i (S g) l
              (LeRwL (Len l)
                (Add lo (S (Add (S k') (Add i g))))
                (Add lo (S (Add k' (Add i (S g)))))
                (IdCongr Nat Nat (λ (a : Nat). Add lo (S a))
                  (Add (S k') (Add i g)) (Add k' (Add i (S g))) (HshiftFalse k' i g))
                hle)
              hpv
        }
    } }
def PartScanRangeLPivotTy : Term := prog{
  Π (pivot : Nat) → Π (lo : Nat) → Π (k : Nat) → Π (i : Nat) → Π (g : Nat) → Π (l : List Nat) →
    Le (Add lo (S (Add k (Add i g)))) (Len l) →
    Id Nat (NthL lo l) pivot →
    Id Nat (NthL (Add (PartScanIdxRangeL pivot lo k i g l) lo) (PartScanRangeL pivot lo k i g l)) pivot }
-- PartitionPivot : wrapper of PartScanRangeLPivot at i=g=0 (preconditions vacuous;
-- pivot-fact is Refl since the pivot is nth lo l; one AddZero nudge on the bound).
def PartitionPivot : Term := prog{
  λ (lo : Nat). λ (cnt : Nat). λ (l : List Nat).
    elim cnt return (λ (cz : Nat).
        Le (Add lo cz) (Len l) →
        Id Nat (NthL (Add (elim cz return (λ (cy : Nat). Nat) { Z => Z, S (cnt') rec => PartScanIdxRangeL (NthL lo l) lo cnt' Z Z l }) lo)
                    (elim cz return (λ (cy : Nat). List Nat) { Z => l, S (cnt') rec => PartScanRangeL (NthL lo l) lo cnt' Z Z l })) (NthL lo l)) {
      Z => λ (hb : Le (Add lo Z) (Len l)). Refl,
      S (cnt') rec => λ (hb : Le (Add lo (S cnt')) (Len l)).
        PartScanRangeLPivot (NthL lo l) lo cnt' Z Z l
          (LeRwL (Len l) (Add lo (S cnt')) (Add lo (S (Add cnt' Z)))
            (IdCongr Nat Nat (λ (a : Nat). Add lo (S a)) cnt' (Add cnt' Z)
              (IdSym Nat (Add cnt' Z) cnt' (AddZero cnt')))
            hb)
          Refl } }

-- PartitionAllLeR : wrapper of PartScanRangeLAllLeR at i=g=0 (AllLeR Z precondition vacuous).
def PartitionAllLeR : Term := prog{
  λ (lo : Nat). λ (cnt : Nat). λ (l : List Nat).
    elim cnt return (λ (cz : Nat).
        Le (Add lo cz) (Len l) →
        AllLeR (elim cz return (λ (cy : Nat). Nat) { Z => Z, S (cnt') rec => PartScanIdxRangeL (NthL lo l) lo cnt' Z Z l }) lo (NthL lo l)
               (elim cz return (λ (cy : Nat). List Nat) { Z => l, S (cnt') rec => PartScanRangeL (NthL lo l) lo cnt' Z Z l })) {
      Z => λ (hb : Le (Add lo Z) (Len l)). AllLeREmpty lo (NthL lo l) l,
      S (cnt') rec => λ (hb : Le (Add lo (S cnt')) (Len l)).
        PartScanRangeLAllLeR (NthL lo l) lo cnt' Z Z l
          (LeRwL (Len l) (Add lo (S cnt')) (Add lo (S (Add cnt' Z)))
            (IdCongr Nat Nat (λ (a : Nat). Add lo (S a)) cnt' (Add cnt' Z)
              (IdSym Nat (Add cnt' Z) cnt' (AddZero cnt')))
            hb)
          Refl
          (AllLeREmpty (S lo) (NthL lo l) l) } }

def PartitionAllLeRTy : Term := prog{
  Π (lo : Nat) → Π (cnt : Nat) → Π (l : List Nat) → Le (Add lo cnt) (Len l) →
    AllLeR (PartIdxRangeL lo cnt l) lo (NthL lo l) (PartitionRangeL lo cnt l) }
-- PartitionAllGtR : wrapper of PartScanRangeLAllGtR at i=g=0 (AllGtR Z precondition vacuous).
def PartitionAllGtR : Term := prog{
  λ (lo : Nat). λ (cnt : Nat). λ (l : List Nat).
    elim cnt return (λ (cz : Nat).
        Le (Add lo cz) (Len l) →
        AllGtR (elim cz return (λ (cy : Nat). Nat) { Z => Z, S (cnt') rec => PartScanGapRangeL (NthL lo l) lo cnt' Z Z l })
               (Add (S (elim cz return (λ (cy : Nat). Nat) { Z => Z, S (cnt') rec => PartScanIdxRangeL (NthL lo l) lo cnt' Z Z l })) lo) (NthL lo l)
               (elim cz return (λ (cy : Nat). List Nat) { Z => l, S (cnt') rec => PartScanRangeL (NthL lo l) lo cnt' Z Z l })) {
      Z => λ (hb : Le (Add lo Z) (Len l)). AllGtREmpty (Add (S Z) lo) (NthL lo l) l,
      S (cnt') rec => λ (hb : Le (Add lo (S cnt')) (Len l)).
        PartScanRangeLAllGtR (NthL lo l) lo cnt' Z Z l
          (LeRwL (Len l) (Add lo (S cnt')) (Add lo (S (Add cnt' Z)))
            (IdCongr Nat Nat (λ (a : Nat). Add lo (S a)) cnt' (Add cnt' Z)
              (IdSym Nat (Add cnt' Z) cnt' (AddZero cnt')))
            hb)
          Refl
          (AllGtREmpty (Add (S Z) lo) (NthL lo l) l) } }

def PartitionAllGtRTy : Term := prog{
  Π (lo : Nat) → Π (cnt : Nat) → Π (l : List Nat) → Le (Add lo cnt) (Len l) →
    AllGtR (PartGapRangeL lo cnt l) (Add (S (PartIdxRangeL lo cnt l)) lo) (NthL lo l) (PartitionRangeL lo cnt l) }
def PartitionPivotTy : Term := prog{
  Π (lo : Nat) → Π (cnt : Nat) → Π (l : List Nat) → Le (Add lo cnt) (Len l) →
    Id Nat (NthL (Add (PartIdxRangeL lo cnt l) lo) (PartitionRangeL lo cnt l)) (NthL lo l) }

-- Truncated subtraction + its reindex identity — the glue's both-right case maps a
-- whole-range index k>i into the right-segment index `Sub k (S i)`, then transports
-- the position `Add (Sub k (S i)) (Add (S i) lo)` back to `Add k lo` via AddAssoc +
-- `Add (Sub k (S i)) (S i) = k` (AddComm of AddSubCancel). sub recurses on the
-- minuend so `Sub (S a)(S b) = Sub a b`; AddSubCancel is a clean double induction.
def Sub : Term := prog{
  λ (a : Nat).
    elim a return (λ (az : Nat). Nat → Nat) {
      Z => λ (b : Nat). Z,
      S (a') rec => λ (b : Nat). elim b return (λ (bz : Nat). Nat) { Z => S a', S (b') bih => rec b' } } }
def SubTy : Term := prog{ Π (a : Nat) → Nat → Nat }
def AddSubCancel : Term := prog{
  λ (a : Nat).
    elim a return (λ (az : Nat). Π (b : Nat) → Le b az → Id Nat (Add b (Sub az b)) az) {
      Z => λ (b : Nat).
        elim b return (λ (bz : Nat). Le bz Z → Id Nat (Add bz (Sub Z bz)) Z) {
          Z => λ (h : Le Z Z). Refl,
          S (b') bih => λ (h : Le (S b') Z). botElim (Id Nat (Add (S b') (Sub Z (S b'))) Z) h },
      S (a') ih => λ (b : Nat).
        elim b return (λ (bz : Nat). Le bz (S a') → Id Nat (Add bz (Sub (S a') bz)) (S a')) {
          Z => λ (h : Le Z (S a')). Refl,
          S (b') bih => λ (h : Le (S b') (S a')).
            IdCongr Nat Nat (λ (n : Nat). S n) (Add b' (Sub a' b')) a' (ih b' h) } } }
def AddSubCancelTy : Term := prog{ Π (a : Nat) → Π (b : Nat) → Le b a → Id Nat (Add b (Sub a b)) a }

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
  λ (a : Nat). λ (b : Nat). λ (h : Le (S a) b).
    LeTrans a (S a) b (LeUpR a a (LeRefl a)) h }
def LePredLTy : Term := prog{ Π (a : Nat) → Π (b : Nat) → Le (S a) b → Le a b }
def GapPos : Term := prog{
  λ (i : Nat). λ (g : Nat). λ (h : Le (S i) (Add i g)).
    LeAddCancelL i (S Z) g
      (LeRwL (Add i g) (S i) (Add i (S Z))
        (IdSym Nat (Add i (S Z)) (S i)
          (IdTrans Nat (Add i (S Z)) (S (Add i Z)) (S i)
            (AddSucc i Z)
            (IdCongr Nat Nat (λ (n : Nat). S n) (Add i Z) i (AddZero i))))
        h) }
def GapPosTy : Term := prog{ Π (i : Nat) → Π (g : Nat) → Le (S i) (Add i g) → Le (S Z) g }
def ReindexPos : Term := prog{
  λ (i : Nat). λ (k : Nat). λ (lo : Nat). λ (hik : Le (S i) k).
    IdTrans Nat
      (Add (Sub k (S i)) (S (Add i lo)))
      (Add (Add (Sub k (S i)) (S i)) lo)
      (Add k lo)
      (IdSym Nat (Add (Add (Sub k (S i)) (S i)) lo) (Add (Sub k (S i)) (S (Add i lo)))
        (AddAssoc (Sub k (S i)) (S i) lo))
      (IdCongr Nat Nat (λ (x : Nat). Add x lo) (Add (Sub k (S i)) (S i)) k
        (IdTrans Nat (Add (Sub k (S i)) (S i)) (Add (S i) (Sub k (S i))) k
          (AddComm (Sub k (S i)) (S i))
          (AddSubCancel k (S i) hik))) }
def ReindexPosTy : Term := prog{
  Π (i : Nat) → Π (k : Nat) → Π (lo : Nat) → Le (S i) k →
    Id Nat (Add (Sub k (S i)) (S (Add i lo))) (Add k lo) }
def ReindexPosS : Term := prog{
  λ (i : Nat). λ (k : Nat). λ (lo : Nat). λ (hik : Le (S i) k).
    IdTrans Nat
      (Add (S (Sub k (S i))) (S (Add i lo)))
      (Add (Add (S (Sub k (S i))) (S i)) lo)
      (Add (S k) lo)
      (IdSym Nat (Add (Add (S (Sub k (S i))) (S i)) lo) (Add (S (Sub k (S i))) (S (Add i lo)))
        (AddAssoc (S (Sub k (S i))) (S i) lo))
      (IdCongr Nat Nat (λ (x : Nat). Add x lo) (Add (S (Sub k (S i))) (S i)) (S k)
        (IdCongr Nat Nat (λ (n : Nat). S n) (Add (Sub k (S i)) (S i)) k
          (IdTrans Nat (Add (Sub k (S i)) (S i)) (Add (S i) (Sub k (S i))) k
            (AddComm (Sub k (S i)) (S i))
            (AddSubCancel k (S i) hik)))) }
def ReindexPosSTy : Term := prog{
  Π (i : Nat) → Π (k : Nat) → Π (lo : Nat) → Le (S i) k →
    Id Nat (Add (S (Sub k (S i))) (S (Add i lo))) (Add (S k) lo) }
def ReindexBnd : Term := prog{
  λ (i : Nat). λ (g : Nat). λ (k : Nat). λ (hik : Le (S i) k). λ (hk : Le (S k) (Add i g)).
    LeAddCancelL i (S (S (Sub k (S i)))) g
      (LeRwL (Add i g)
        (S (S (Add i (Sub k (S i)))))
        (Add i (S (S (Sub k (S i)))))
        (IdSym Nat (Add i (S (S (Sub k (S i))))) (S (S (Add i (Sub k (S i)))))
          (IdTrans Nat (Add i (S (S (Sub k (S i))))) (S (Add i (S (Sub k (S i))))) (S (S (Add i (Sub k (S i)))))
            (AddSucc i (S (Sub k (S i))))
            (IdCongr Nat Nat (λ (n : Nat). S n) (Add i (S (Sub k (S i)))) (S (Add i (Sub k (S i))))
              (AddSucc i (Sub k (S i))))))
        (LeRwL (Add i g) (S k) (S (S (Add i (Sub k (S i)))))
          (IdCongr Nat Nat (λ (n : Nat). S n) k (S (Add i (Sub k (S i))))
            (IdSym Nat (S (Add i (Sub k (S i)))) k (AddSubCancel k (S i) hik)))
          hk)) }
def ReindexBndTy : Term := prog{
  Π (i : Nat) → Π (g : Nat) → Π (k : Nat) → Le (S i) k → Le (S k) (Add i g) →
    Le (S (S (Sub k (S i)))) g }
def GlueLeftPivot : Term := prog{
  λ (i : Nat). λ (k : Nat). λ (lo : Nat). λ (pivot : Nat). λ (R : List Nat).
    λ (e1 : Id Bool (Leb (S k) i) True).
    λ (e2 : Id Bool (Leb (S (S k)) i) False).
    λ (hpiv : Id Nat pivot (NthL (Add i lo) R)).
    λ (al : AllLeR i lo pivot R).
      LeRwR (NthL (Add k lo) R) pivot (NthL (Add (S k) lo) R)
        (IdTrans Nat pivot (NthL (Add i lo) R) (NthL (Add (S k) lo) R)
          hpiv
          (IdCongr Nat Nat (λ (x : Nat). NthL (Add x lo) R) i (S k)
            (LeAntisym i (S k) (LebFalseGt (S (S k)) i e2) (LebTrueLe (S k) i e1))))
        (al k (LebTrueLe (S k) i e1)) }
def GlueLeftPivotTy : Term := prog{
  Π (i : Nat) → Π (k : Nat) → Π (lo : Nat) → Π (pivot : Nat) → Π (R : List Nat) →
    Id Bool (Leb (S k) i) True → Id Bool (Leb (S (S k)) i) False →
    Id Nat pivot (NthL (Add i lo) R) → AllLeR i lo pivot R →
    Le (NthL (Add k lo) R) (NthL (Add (S k) lo) R) }
def GluePivotRight : Term := prog{
  λ (i : Nat). λ (g : Nat). λ (k : Nat). λ (lo : Nat). λ (pivot : Nat). λ (R : List Nat).
    λ (e1 : Id Bool (Leb (S k) i) False).
    λ (e2 : Id Bool (Leb (S i) k) False).
    λ (hk : Le (S (S k)) (S (Add i g))).
    λ (hpiv : Id Nat pivot (NthL (Add i lo) R)).
    λ (ag : AllGtR g (S (Add i lo)) pivot R).
      LeRwL (NthL (Add (S k) lo) R) pivot (NthL (Add k lo) R)
        (IdSym Nat (NthL (Add k lo) R) pivot
          (IdTrans Nat (NthL (Add k lo) R) (NthL (Add i lo) R) pivot
            (IdCongr Nat Nat (λ (x : Nat). NthL (Add x lo) R) k i
              (LeAntisym k i (LebFalseGt (S i) k e2) (LebFalseGt (S k) i e1)))
            (IdSym Nat pivot (NthL (Add i lo) R) hpiv)))
        (LeRwR pivot (NthL (S (Add i lo)) R) (NthL (Add (S k) lo) R)
          (IdCongr Nat Nat (λ (x : Nat). NthL (S (Add x lo)) R) i k
            (IdSym Nat k i (LeAntisym k i (LebFalseGt (S i) k e2) (LebFalseGt (S k) i e1))))
          (LePredL pivot (NthL (S (Add i lo)) R)
            (ag Z (GapPos i g
              (LeRwL (Add i g) (S k) (S i)
                (IdCongr Nat Nat (λ (n : Nat). S n) k i
                  (LeAntisym k i (LebFalseGt (S i) k e2) (LebFalseGt (S k) i e1)))
                hk))))) }
def GluePivotRightTy : Term := prog{
  Π (i : Nat) → Π (g : Nat) → Π (k : Nat) → Π (lo : Nat) → Π (pivot : Nat) → Π (R : List Nat) →
    Id Bool (Leb (S k) i) False → Id Bool (Leb (S i) k) False →
    Le (S (S k)) (S (Add i g)) → Id Nat pivot (NthL (Add i lo) R) →
    AllGtR g (S (Add i lo)) pivot R →
    Le (NthL (Add k lo) R) (NthL (Add (S k) lo) R) }
def GlueBothRight : Term := prog{
  λ (i : Nat). λ (g : Nat). λ (k : Nat). λ (lo : Nat). λ (pivot : Nat). λ (R : List Nat).
    λ (e2 : Id Bool (Leb (S i) k) True).
    λ (hk : Le (S (S k)) (S (Add i g))).
    λ (sr : SortedR g (S (Add i lo)) R).
      LeRwL (NthL (Add (S k) lo) R)
        (NthL (Add (Sub k (S i)) (S (Add i lo))) R)
        (NthL (Add k lo) R)
        (IdCongr Nat Nat (λ (p : Nat). NthL p R) (Add (Sub k (S i)) (S (Add i lo))) (Add k lo)
          (ReindexPos i k lo (LebTrueLe (S i) k e2)))
        (LeRwR (NthL (Add (Sub k (S i)) (S (Add i lo))) R)
          (NthL (Add (S (Sub k (S i))) (S (Add i lo))) R)
          (NthL (Add (S k) lo) R)
          (IdCongr Nat Nat (λ (p : Nat). NthL p R) (Add (S (Sub k (S i))) (S (Add i lo))) (Add (S k) lo)
            (ReindexPosS i k lo (LebTrueLe (S i) k e2)))
          (sr (Sub k (S i)) (ReindexBnd i g k (LebTrueLe (S i) k e2) hk))) }
def GlueBothRightTy : Term := prog{
  Π (i : Nat) → Π (g : Nat) → Π (k : Nat) → Π (lo : Nat) → Π (pivot : Nat) → Π (R : List Nat) →
    Id Bool (Leb (S i) k) True → Le (S (S k)) (S (Add i g)) →
    SortedR g (S (Add i lo)) R →
    Le (NthL (Add k lo) R) (NthL (Add (S k) lo) R) }
def Glue : Term := prog{
  λ (i : Nat). λ (g : Nat). λ (lo : Nat). λ (pivot : Nat). λ (R : List Nat).
    λ (hpiv : Id Nat pivot (NthL (Add i lo) R)).
    λ (sl : SortedR i lo R).
    λ (al : AllLeR i lo pivot R).
    λ (ag : AllGtR g (S (Add i lo)) pivot R).
    λ (sr : SortedR g (S (Add i lo)) R).
    λ (k : Nat). λ (hk : Le (S (S k)) (S (Add i g))).
      (elim (Leb (S k) i) return (λ (w : Bool).
          Id Bool (Leb (S k) i) w → Le (NthL (Add k lo) R) (NthL (Add (S k) lo) R)) {
        True => λ (e1 : Id Bool (Leb (S k) i) True).
          (elim (Leb (S (S k)) i) return (λ (w2 : Bool).
              Id Bool (Leb (S (S k)) i) w2 → Le (NthL (Add k lo) R) (NthL (Add (S k) lo) R)) {
            True => λ (e2 : Id Bool (Leb (S (S k)) i) True). sl k (LebTrueLe (S (S k)) i e2),
            False => λ (e2 : Id Bool (Leb (S (S k)) i) False). GlueLeftPivot i k lo pivot R e1 e2 hpiv al
          }) Refl,
        False => λ (e1 : Id Bool (Leb (S k) i) False).
          (elim (Leb (S i) k) return (λ (w2 : Bool).
              Id Bool (Leb (S i) k) w2 → Le (NthL (Add k lo) R) (NthL (Add (S k) lo) R)) {
            True => λ (e2 : Id Bool (Leb (S i) k) True). GlueBothRight i g k lo pivot R e2 hk sr,
            False => λ (e2 : Id Bool (Leb (S i) k) False). GluePivotRight i g k lo pivot R e1 e2 hk hpiv ag
          }) Refl
      }) Refl }
def GlueTy : Term := prog{
  Π (i : Nat) → Π (g : Nat) → Π (lo : Nat) → Π (pivot : Nat) → Π (R : List Nat) →
    Id Nat pivot (NthL (Add i lo) R) →
    SortedR i lo R →
    AllLeR i lo pivot R →
    AllGtR g (S (Add i lo)) pivot R →
    SortedR g (S (Add i lo)) R →
    SortedR (S (Add i g)) lo R }

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
  λ (h : Nat).
    elim h return (λ (hz : Nat). Π (x : Nat) → Le (S hz) x → Id Bool (Eqb x hz) False) {
      Z => λ (x : Nat).
        elim x return (λ (xz : Nat). Le (S Z) xz → Id Bool (Eqb xz Z) False) {
          Z => λ (hlt : Le (S Z) Z). botElim (Id Bool (Eqb Z Z) False) hlt,
          S (x') xih => λ (hlt : Le (S Z) (S x')). Refl },
      S (h') ih => λ (x : Nat).
        elim x return (λ (xz : Nat). Le (S (S h')) xz → Id Bool (Eqb xz (S h')) False) {
          Z => λ (hlt : Le (S (S h')) Z). botElim (Id Bool (Eqb Z (S h')) False) hlt,
          S (x') xih => λ (hlt : Le (S (S h')) (S x')). ih x' hlt } } }
def EqbGtFalseTy : Term := prog{ Π (h : Nat) → Π (x : Nat) → Le (S h) x → Id Bool (Eqb x h) False }

def EqbLtFalse : Term := prog{
  λ (a : Nat).
    elim a return (λ (az : Nat). Π (b : Nat) → Le (S az) b → Id Bool (Eqb az b) False) {
      Z => λ (b : Nat).
        elim b return (λ (bz : Nat). Le (S Z) bz → Id Bool (Eqb Z bz) False) {
          Z => λ (hlt : Le (S Z) Z). botElim (Id Bool (Eqb Z Z) False) hlt,
          S (b') bih => λ (hlt : Le (S Z) (S b')). Refl },
      S (a') ih => λ (b : Nat).
        elim b return (λ (bz : Nat). Le (S (S a')) bz → Id Bool (Eqb (S a') bz) False) {
          Z => λ (hlt : Le (S (S a')) Z). botElim (Id Bool (Eqb (S a') Z) False) hlt,
          S (b') bih => λ (hlt : Le (S (S a')) (S b')). ih b' hlt } } }
def EqbLtFalseTy : Term := prog{ Π (a : Nat) → Π (b : Nat) → Le (S a) b → Id Bool (Eqb a b) False }

def CountConsMiss : Term := prog{
  λ (m : Nat). λ (h : Nat). λ (t : List Nat). λ (hq : Id Bool (Eqb m h) False).
    j Bool False
      (λ (z : Bool). λ (hh : Id Bool False z).
        Id Nat (boolRec (λ (w : Bool). Nat) (S (Count m t)) (Count m t) z) (Count m t))
      Refl (Eqb m h) (IdSym Bool (Eqb m h) False hq) }
def CountConsMissTy : Term := prog{
  Π (m : Nat) → Π (h : Nat) → Π (t : List Nat) → Id Bool (Eqb m h) False →
    Id Nat (Count m (Cons h t)) (Count m t) }

def CountZeroExt : Term := prog{
  λ (x : Nat). λ (s : List Nat).
    elim s return (λ (sz : List Nat). (Π (j : Nat) → Le (S j) (Len sz) → Id Bool (Eqb x (NthL j sz)) False) → Id Nat (Count x sz) Z) {
      Nil => λ (heq : Π (j : Nat) → Le (S j) (Len Nil) → Id Bool (Eqb x (NthL j Nil)) False). Refl,
      Cons (h) (t) ih => λ (heq : Π (j : Nat) → Le (S j) (Len (Cons h t)) → Id Bool (Eqb x (NthL j (Cons h t))) False).
        IdTrans Nat (Count x (Cons h t)) (Count x t) Z
          (CountConsMiss x h t (heq Z unit))
          (ih (λ (j : Nat). λ (hj : Le (S j) (Len t)). heq (S j) hj)) } }
def CountZeroExtTy : Term := prog{
  Π (x : Nat) → Π (s : List Nat) →
    (Π (j : Nat) → Le (S j) (Len s) → Id Bool (Eqb x (NthL j s)) False) → Id Nat (Count x s) Z }

def NthTake : Term := prog{
  λ (w : Nat).
    elim w return (λ (wz : Nat). Π (j : Nat) → Π (s : List Nat) → Le (S j) wz → Id Nat (NthL j (Take wz s)) (NthL j s)) {
      Z => λ (j : Nat). λ (s : List Nat). λ (hlt : Le (S j) Z). botElim (Id Nat (NthL j (Take Z s)) (NthL j s)) hlt,
      S (w') ih => λ (j : Nat). λ (s : List Nat).
        elim j return (λ (jz : Nat). Le (S jz) (S w') → Id Nat (NthL jz (Take (S w') s)) (NthL jz s)) {
          Z => λ (hlt : Le (S Z) (S w')).
            elim s return (λ (sz : List Nat). Id Nat (NthL Z (Take (S w') sz)) (NthL Z sz)) {
              Nil => Refl, Cons (h) (t) sih => Refl },
          S (j') jih => λ (hlt : Le (S (S j')) (S w')).
            elim s return (λ (sz : List Nat). Id Nat (NthL (S j') (Take (S w') sz)) (NthL (S j') sz)) {
              Nil => Refl,
              Cons (h) (t) sih => ih j' t hlt } } } }
def NthTakeTy : Term := prog{
  Π (w : Nat) → Π (j : Nat) → Π (s : List Nat) → Le (S j) w → Id Nat (NthL j (Take w s)) (NthL j s) }

def LenTakeLe : Term := prog{
  λ (w : Nat).
    elim w return (λ (wz : Nat). Π (s : List Nat) → Le (Len (Take wz s)) wz) {
      Z => λ (s : List Nat). unit,
      S (w') ih => λ (s : List Nat).
        elim s return (λ (sz : List Nat). Le (Len (Take (S w') sz)) (S w')) {
          Nil => unit,
          Cons (h) (t) sih => ih t } } }
def LenTakeLeTy : Term := prog{ Π (w : Nat) → Π (s : List Nat) → Le (Len (Take w s)) w }

-- #2 AllLeRToNoAbove : every segment element ≤ p, so an x>p occurs 0× (CountZeroExt,
-- with each element bridged nth j (take w (drop lo l)) → nth (add j lo) l via NthTake/NthDrop).
def AllLeRToNoAbove : Term := prog{
  λ (w : Nat). λ (lo : Nat). λ (p : Nat). λ (l : List Nat).
    λ (hAll : AllLeR w lo p l). λ (x : Nat). λ (hpx : Le (S p) x).
      CountZeroExt x (Take w (Drop lo l))
        (λ (j : Nat). λ (hj : Le (S j) (Len (Take w (Drop lo l)))).
          EqbGtFalse (NthL j (Take w (Drop lo l))) x
            (LeTrans (S (NthL j (Take w (Drop lo l)))) (S p) x
              (LeRwL p (NthL (Add j lo) l) (NthL j (Take w (Drop lo l)))
                (IdSym Nat (NthL j (Take w (Drop lo l))) (NthL (Add j lo) l)
                  (IdTrans Nat (NthL j (Take w (Drop lo l))) (NthL j (Drop lo l)) (NthL (Add j lo) l)
                    (NthTake w j (Drop lo l) (LeTrans (S j) (Len (Take w (Drop lo l))) w hj (LenTakeLe w (Drop lo l))))
                    (IdTrans Nat (NthL j (Drop lo l)) (NthL (Add lo j) l) (NthL (Add j lo) l)
                      (NthDrop lo j l)
                      (IdCongr Nat Nat (λ (q : Nat). NthL q l) (Add lo j) (Add j lo) (AddComm lo j)))))
                (hAll j (LeTrans (S j) (Len (Take w (Drop lo l))) w hj (LenTakeLe w (Drop lo l)))))
              hpx)) }

-- #4 AllGtRToNoBelow : every segment element > p, so an x≤p occurs 0× (mirror of #2).
def AllGtRToNoBelow : Term := prog{
  λ (w : Nat). λ (lo : Nat). λ (p : Nat). λ (l : List Nat).
    λ (hAll : AllGtR w lo p l). λ (x : Nat). λ (hxp : Le x p).
      CountZeroExt x (Take w (Drop lo l))
        (λ (j : Nat). λ (hj : Le (S j) (Len (Take w (Drop lo l)))).
          EqbLtFalse x (NthL j (Take w (Drop lo l)))
            (LeTrans (S x) (S p) (NthL j (Take w (Drop lo l)))
              hxp
              (LeRwR (S p) (NthL (Add j lo) l) (NthL j (Take w (Drop lo l)))
                (IdSym Nat (NthL j (Take w (Drop lo l))) (NthL (Add j lo) l)
                  (IdTrans Nat (NthL j (Take w (Drop lo l))) (NthL j (Drop lo l)) (NthL (Add j lo) l)
                    (NthTake w j (Drop lo l) (LeTrans (S j) (Len (Take w (Drop lo l))) w hj (LenTakeLe w (Drop lo l))))
                    (IdTrans Nat (NthL j (Drop lo l)) (NthL (Add lo j) l) (NthL (Add j lo) l)
                      (NthDrop lo j l)
                      (IdCongr Nat Nat (λ (q : Nat). NthL q l) (Add lo j) (Add j lo) (AddComm lo j)))))
                (hAll j (LeTrans (S j) (Len (Take w (Drop lo l))) w hj (LenTakeLe w (Drop lo l))))))) }

-- Membership side (#1/#3/#5): the range-fits bound makes the element genuinely present.
def EqbRefl : Term := prog{
  λ (n : Nat). elim n return (λ (nz : Nat). Id Bool (Eqb nz nz) True) {
    Z => Refl,
    S (n') ih => ih } }
def EqbReflTy : Term := prog{ Π (n : Nat) → Id Bool (Eqb n n) True }

def LenDropBound : Term := prog{
  λ (lo : Nat).
    elim lo return (λ (loz : Nat). Π (k : Nat) → Π (l : List Nat) → Le (Add loz k) (Len l) → Le k (Len (Drop loz l))) {
      Z => λ (k : Nat). λ (l : List Nat). λ (hb : Le (Add Z k) (Len l)). hb,
      S (lo') ih => λ (k : Nat). λ (l : List Nat).
        elim l return (λ (lz : List Nat). Le (Add (S lo') k) (Len lz) → Le k (Len (Drop (S lo') lz))) {
          Nil => λ (hb : Le (Add (S lo') k) (Len Nil)). botElim (Le k (Len (Drop (S lo') Nil))) hb,
          Cons (h) (t) lih => λ (hb : Le (Add (S lo') k) (Len (Cons h t))). ih k t hb } } }
def LenDropBoundTy : Term := prog{
  Π (lo : Nat) → Π (k : Nat) → Π (l : List Nat) → Le (Add lo k) (Len l) → Le k (Len (Drop lo l)) }

def CountTakeNthPos : Term := prog{
  λ (w : Nat).
    elim w return (λ (wz : Nat). Π (m : Nat) → Π (s : List Nat) → Le (S m) wz → Le (S m) (Len s) → Le (S Z) (Count (NthL m s) (Take wz s))) {
      Z => λ (m : Nat). λ (s : List Nat). λ (hw : Le (S m) Z). λ (hs : Le (S m) (Len s)). botElim (Le (S Z) (Count (NthL m s) (Take Z s))) hw,
      S (w') ih => λ (m : Nat). λ (s : List Nat). λ (hw : Le (S m) (S w')). λ (hs : Le (S m) (Len s)).
        elim s return (λ (sz : List Nat). Le (S m) (Len sz) → Le (S Z) (Count (NthL m sz) (Take (S w') sz))) {
          Nil => λ (hs0 : Le (S m) (Len Nil)). botElim (Le (S Z) (Count (NthL m Nil) (Take (S w') Nil))) hs0,
          Cons (h) (t) sih => λ (hs0 : Le (S m) (Len (Cons h t))).
            elim m return (λ (mz : Nat). Le (S mz) (S w') → Le (S mz) (Len (Cons h t)) → Le (S Z) (Count (NthL mz (Cons h t)) (Take (S w') (Cons h t)))) {
              Z => λ (hw1 : Le (S Z) (S w')). λ (hs1 : Le (S Z) (Len (Cons h t))).
                LeRwR (S Z) (S (Count h (Take w' t))) (Count h (Cons h (Take w' t)))
                  (IdSym Nat (Count h (Cons h (Take w' t))) (S (Count h (Take w' t)))
                    (CountConsHit h h (Take w' t) (EqbRefl h)))
                  unit,
              S (m') mih => λ (hw1 : Le (S (S m')) (S w')). λ (hs1 : Le (S (S m')) (Len (Cons h t))).
                elim (Eqb (NthL m' t) h) return (λ (b : Bool). Le (S Z) (boolRec (λ (bw : Bool). Nat) (S (Count (NthL m' t) (Take w' t))) (Count (NthL m' t) (Take w' t)) b)) {
                  True => unit,
                  False => ih m' t hw1 hs1 }
            } hw hs0 } hs } }
def CountTakeNthPosTy : Term := prog{
  Π (w : Nat) → Π (m : Nat) → Π (s : List Nat) → Le (S m) w → Le (S m) (Len s) →
    Le (S Z) (Count (NthL m s) (Take w s)) }

-- #1 NthSegCountPos : element at range position lo+m occurs ≥1× in the segment (needs range-fits).
def NthSegCountPos : Term := prog{
  λ (m : Nat). λ (w : Nat). λ (lo : Nat). λ (l : List Nat).
    λ (hmw : Le (S m) w). λ (hrange : Le (Add lo w) (Len l)).
      LeRwR (S Z) (Count (NthL m (Drop lo l)) (Take w (Drop lo l))) (Count (NthL (Add m lo) l) (Take w (Drop lo l)))
        (IdCongr Nat Nat (λ (q : Nat). Count q (Take w (Drop lo l))) (NthL m (Drop lo l)) (NthL (Add m lo) l)
          (IdTrans Nat (NthL m (Drop lo l)) (NthL (Add lo m) l) (NthL (Add m lo) l)
            (NthDrop lo m l)
            (IdCongr Nat Nat (λ (q : Nat). NthL q l) (Add lo m) (Add m lo) (AddComm lo m))))
        (CountTakeNthPos w m (Drop lo l) hmw
          (LenDropBound lo (S m) l
            (LeTrans (Add lo (S m)) (Add lo w) (Len l) (LeAddMonoL lo (S m) w hmw) hrange))) }

-- #3 NoAboveToAllLeR : no element > p in the segment ⟹ range ≤ p (leb + contradiction via #1).
def NoAboveToAllLeR : Term := prog{
  λ (w : Nat). λ (lo : Nat). λ (p : Nat). λ (l : List Nat).
    λ (hrange : Le (Add lo w) (Len l)). λ (hnoAbove : Π (x : Nat) → Le (S p) x → Id Nat (SegCount x lo w l) Z).
    λ (m : Nat). λ (hm : Le (S m) w).
      elim (Leb (NthL (Add m lo) l) p) return (λ (b : Bool). Id Bool (Leb (NthL (Add m lo) l) p) b → Le (NthL (Add m lo) l) p) {
        True => λ (e : Id Bool (Leb (NthL (Add m lo) l) p) True). LebTrueLe (NthL (Add m lo) l) p e,
        False => λ (e : Id Bool (Leb (NthL (Add m lo) l) p) False).
          botElim (Le (NthL (Add m lo) l) p)
            (LeRwR (S Z) (SegCount (NthL (Add m lo) l) lo w l) Z
              (hnoAbove (NthL (Add m lo) l) (LebFalseGt (NthL (Add m lo) l) p e))
              (NthSegCountPos m w lo l hm hrange))
      } Refl }

-- #5 NoBelowToAllGtR : mirror of #3.
def NoBelowToAllGtR : Term := prog{
  λ (w : Nat). λ (lo : Nat). λ (p : Nat). λ (l : List Nat).
    λ (hrange : Le (Add lo w) (Len l)). λ (hnoBelow : Π (x : Nat) → Le x p → Id Nat (SegCount x lo w l) Z).
    λ (m : Nat). λ (hm : Le (S m) w).
      elim (Leb (NthL (Add m lo) l) p) return (λ (b : Bool). Id Bool (Leb (NthL (Add m lo) l) p) b → Le (S p) (NthL (Add m lo) l)) {
        True => λ (e : Id Bool (Leb (NthL (Add m lo) l) p) True).
          botElim (Le (S p) (NthL (Add m lo) l))
            (LeRwR (S Z) (SegCount (NthL (Add m lo) l) lo w l) Z
              (hnoBelow (NthL (Add m lo) l) (LebTrueLe (NthL (Add m lo) l) p e))
              (NthSegCountPos m w lo l hm hrange)),
        False => λ (e : Id Bool (Leb (NthL (Add m lo) l) p) False). LebFalseGt (NthL (Add m lo) l) p e
      } Refl }

def AllLeRToNoAboveTy : Term := prog{
  Π (w : Nat) → Π (lo : Nat) → Π (p : Nat) → Π (l : List Nat) →
    AllLeR w lo p l → Π (x : Nat) → Le (S p) x → Id Nat (SegCount x lo w l) Z }
def NoAboveToAllLeRTy : Term := prog{
  Π (w : Nat) → Π (lo : Nat) → Π (p : Nat) → Π (l : List Nat) → Le (Add lo w) (Len l) →
    (Π (x : Nat) → Le (S p) x → Id Nat (SegCount x lo w l) Z) → AllLeR w lo p l }
def AllGtRToNoBelowTy : Term := prog{
  Π (w : Nat) → Π (lo : Nat) → Π (p : Nat) → Π (l : List Nat) →
    AllGtR w lo p l → Π (x : Nat) → Le x p → Id Nat (SegCount x lo w l) Z }
def NoBelowToAllGtRTy : Term := prog{
  Π (w : Nat) → Π (lo : Nat) → Π (p : Nat) → Π (l : List Nat) → Le (Add lo w) (Len l) →
    (Π (x : Nat) → Le x p → Id Nat (SegCount x lo w l) Z) → AllGtR w lo p l }
-- #1/#3/#5 carry the range-fits bound `Le (Add lo w) (Len l)`: without it an off-the-end
-- position reads Z, which need not occur in the segment, so #1 (present ≥1×) and #5
-- (AllGtR needs nth>p at every m<w, but off-end nth=Z isn't) are FALSE (dllbc-seg's
-- gate finding, computationally checked). #2/#4 iterate the ACTUAL segment so need no
-- bound. The keystone already carries this bound and len is sort-invariant, so the
-- composition feeds #3/#5 the bound over the sorted list.
def NthSegCountPosTy : Term := prog{
  Π (m : Nat) → Π (w : Nat) → Π (lo : Nat) → Π (l : List Nat) →
    Le (S m) w → Le (Add lo w) (Len l) → Le (S Z) (SegCount (NthL (Add m lo) l) lo w l) }
def AllLeRSortRangeTy : Term := prog{
  Π (fuel : Nat) → Π (lo : Nat) → Π (w : Nat) → Π (p : Nat) → Π (l : List Nat) →
    Le (Add lo w) (Len l) → AllLeR w lo p l → AllLeR w lo p (SortRangeL fuel lo w l) }
def AllGtRSortRangeTy : Term := prog{
  Π (fuel : Nat) → Π (lo : Nat) → Π (w : Nat) → Π (p : Nat) → Π (l : List Nat) →
    Le (Add lo w) (Len l) → AllGtR w lo p l → AllGtR w lo p (SortRangeL fuel lo w l) }

-- KEYSTONE composition (mine): route the positional bound through the perm-invariant
-- noAbove/noBelow (SegCount preserved by SegCountSortRangeL), feeding the range bound
-- over the sorted list (len sort-invariant, LeRwR over LenSortRangeL).
def AllLeRSortRange : Term := prog{
  λ (fuel : Nat). λ (lo : Nat). λ (w : Nat). λ (p : Nat). λ (l : List Nat).
    λ (bound : Le (Add lo w) (Len l)). λ (h : AllLeR w lo p l).
      NoAboveToAllLeR w lo p (SortRangeL fuel lo w l)
        (LeRwR (Add lo w) (Len l) (Len (SortRangeL fuel lo w l))
          (IdSym Nat (Len (SortRangeL fuel lo w l)) (Len l) (LenSortRangeL fuel lo w l))
          bound)
        (λ (x : Nat). λ (hx : Le (S p) x).
          IdTrans Nat (SegCount x lo w (SortRangeL fuel lo w l)) (SegCount x lo w l) Z
            (SegCountSortRangeL x fuel lo w l bound)
            (AllLeRToNoAbove w lo p l h x hx)) }
def AllGtRSortRange : Term := prog{
  λ (fuel : Nat). λ (lo : Nat). λ (w : Nat). λ (p : Nat). λ (l : List Nat).
    λ (bound : Le (Add lo w) (Len l)). λ (h : AllGtR w lo p l).
      NoBelowToAllGtR w lo p (SortRangeL fuel lo w l)
        (LeRwR (Add lo w) (Len l) (Len (SortRangeL fuel lo w l))
          (IdSym Nat (Len (SortRangeL fuel lo w l)) (Len l) (LenSortRangeL fuel lo w l))
          bound)
        (λ (x : Nat). λ (hx : Le x p).
          IdTrans Nat (SegCount x lo w (SortRangeL fuel lo w l)) (SegCount x lo w l) Z
            (SegCountSortRangeL x fuel lo w l bound)
            (AllGtRToNoBelow w lo p l h x hx)) }

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
  Π (fuel : Nat) → Π (lo : Nat) → Π (cnt : Nat) → Π (l : List Nat) →
    Le cnt fuel → Le (Add lo cnt) (Len l) →
    SortedR cnt lo (SortRangeL fuel lo cnt l) }

-- SortedR transport kit for SortedSortRangeL (spine takeover): move a SortedR across
-- a fixed region (SortedRCong, le_rw both endpoints), a width rewrite (SortedRWidthCong,
-- j on the width — for the glue's S(add i g) → cnt), or an offset rewrite (SortedROffCong,
-- j on the offset — for the AddComm S(add lo i) ↔ S(add i lo) bridge).
def SortedRCong : Term := prog{
  λ (w : Nat). λ (lo : Nat). λ (l : List Nat). λ (l' : List Nat).
    λ (s : SortedR w lo l).
    λ (agree : Π (q : Nat) → Le (S q) w → Id Nat (NthL (Add q lo) l') (NthL (Add q lo) l)).
      λ (k : Nat). λ (hk : Le (S (S k)) w).
        LeRwR (NthL (Add k lo) l') (NthL (Add (S k) lo) l) (NthL (Add (S k) lo) l')
          (IdSym Nat (NthL (Add (S k) lo) l') (NthL (Add (S k) lo) l) (agree (S k) hk))
          (LeRwL (NthL (Add (S k) lo) l) (NthL (Add k lo) l) (NthL (Add k lo) l')
            (IdSym Nat (NthL (Add k lo) l') (NthL (Add k lo) l) (agree k (LePredL (S k) w hk)))
            (s k hk)) }
def SortedRCongTy : Term := prog{
  Π (w : Nat) → Π (lo : Nat) → Π (l : List Nat) → Π (l' : List Nat) →
    SortedR w lo l →
    (Π (q : Nat) → Le (S q) w → Id Nat (NthL (Add q lo) l') (NthL (Add q lo) l)) →
    SortedR w lo l' }
def SortedRWidthCong : Term := prog{
  λ (w : Nat). λ (w' : Nat). λ (lo : Nat). λ (l : List Nat).
    λ (e : Id Nat w w'). λ (s : SortedR w lo l).
      j Nat w (λ (w2 : Nat). λ (h : Id Nat w w2). SortedR w2 lo l) s w' e }
def SortedRWidthCongTy : Term := prog{
  Π (w : Nat) → Π (w' : Nat) → Π (lo : Nat) → Π (l : List Nat) →
    Id Nat w w' → SortedR w lo l → SortedR w' lo l }
def SortedROffCong : Term := prog{
  λ (w : Nat). λ (lo : Nat). λ (lo' : Nat). λ (l : List Nat).
    λ (e : Id Nat lo lo'). λ (s : SortedR w lo l).
      j Nat lo (λ (lo2 : Nat). λ (h : Id Nat lo lo2). SortedR w lo2 l) s lo' e }
def SortedROffCongTy : Term := prog{
  Π (w : Nat) → Π (lo : Nat) → Π (lo' : Nat) → Π (l : List Nat) →
    Id Nat lo lo' → SortedR w lo l → SortedR w lo' l }

/-! ## sorted_sortRangeL's 5 glue inputs (spine takeover) — each survives BOTH sub-sorts.
    Setup: L = SortRangeL f' lo i p (left sort), result = SortRangeL f' (S(add lo i)) g L
    (right sort). SL/AL: left region [lo,lo+i) is BELOW the right sort (NthSortRangeLLt);
    AG: gap is ABOVE the left sort (NthSortRangeLGe). Keystone (allLeR/AllGtRSortRange)
    carries bounds across the OWN sort; cong across the fixed region. AddComm bridges the
    positional-predicate offset (add i lo) ↔ model offset (add lo i). -/
def PosLtBound : Term := prog{
  λ (q : Nat). λ (i : Nat). λ (lo : Nat). λ (hq : Le (S q) i).
    LeRwL (Add lo i) (Add lo q) (Add q lo) (AddComm lo q)
      (LeAddMonoL lo q i (LePredL q i hq)) }
def PosLtBoundTy : Term := prog{
  Π (q : Nat) → Π (i : Nat) → Π (lo : Nat) → Le (S q) i → Le (S (Add q lo)) (S (Add lo i)) }
def AllGtROffCong : Term := prog{
  λ (w : Nat). λ (off : Nat). λ (off' : Nat). λ (p : Nat). λ (l : List Nat).
    λ (e : Id Nat off off'). λ (s : AllGtR w off p l).
      j Nat off (λ (o2 : Nat). λ (h : Id Nat off o2). AllGtR w o2 p l) s off' e }
def AllGtROffCongTy : Term := prog{
  Π (w : Nat) → Π (off : Nat) → Π (off' : Nat) → Π (p : Nat) → Π (l : List Nat) →
    Id Nat off off' → AllGtR w off p l → AllGtR w off' p l }
def GapGeBound : Term := prog{
  λ (m : Nat). λ (i : Nat). λ (lo : Nat).
    LeRwL (Add m (S (Add i lo))) (Add i lo) (Add lo i) (AddComm i lo)
      (LeTrans (Add i lo) (S (Add i lo)) (Add m (S (Add i lo)))
        (LeUpR (Add i lo) (Add i lo) (LeRefl (Add i lo)))
        (LeAddL (S (Add i lo)) m)) }
def GapGeBoundTy : Term := prog{
  Π (m : Nat) → Π (i : Nat) → Π (lo : Nat) → Le (Add lo i) (Add m (S (Add i lo))) }
def SortedInSL : Term := prog{
  λ (i : Nat). λ (g : Nat). λ (lo : Nat). λ (p : List Nat). λ (f' : Nat).
    λ (ihL : SortedR i lo (SortRangeL f' lo i p)).
      SortedRCong i lo (SortRangeL f' lo i p) (SortRangeL f' (S (Add lo i)) g (SortRangeL f' lo i p))
        ihL
        (λ (q : Nat). λ (hq : Le (S q) i).
          NthSortRangeLLt f' (Add q lo) (S (Add lo i)) g (SortRangeL f' lo i p) (PosLtBound q i lo hq)) }
def SortedInSLTy : Term := prog{
  Π (i : Nat) → Π (g : Nat) → Π (lo : Nat) → Π (p : List Nat) → Π (f' : Nat) →
    SortedR i lo (SortRangeL f' lo i p) →
    SortedR i lo (SortRangeL f' (S (Add lo i)) g (SortRangeL f' lo i p)) }
def SortedInSR : Term := prog{
  λ (i : Nat). λ (g : Nat). λ (lo : Nat). λ (p : List Nat). λ (f' : Nat).
    λ (ihR : SortedR g (S (Add lo i)) (SortRangeL f' (S (Add lo i)) g (SortRangeL f' lo i p))).
      SortedROffCong g (S (Add lo i)) (S (Add i lo)) (SortRangeL f' (S (Add lo i)) g (SortRangeL f' lo i p))
        (IdCongr Nat Nat (λ (n : Nat). S n) (Add lo i) (Add i lo) (AddComm lo i))
        ihR }
def SortedInSRTy : Term := prog{
  Π (i : Nat) → Π (g : Nat) → Π (lo : Nat) → Π (p : List Nat) → Π (f' : Nat) →
    SortedR g (S (Add lo i)) (SortRangeL f' (S (Add lo i)) g (SortRangeL f' lo i p)) →
    SortedR g (S (Add i lo)) (SortRangeL f' (S (Add lo i)) g (SortRangeL f' lo i p)) }
def SortedInHPIV : Term := prog{
  λ (i : Nat). λ (g : Nat). λ (lo : Nat). λ (pivot : Nat). λ (p : List Nat). λ (f' : Nat).
    λ (ppiv : Id Nat (NthL (Add i lo) p) pivot).
      IdSym Nat (NthL (Add i lo) (SortRangeL f' (S (Add lo i)) g (SortRangeL f' lo i p))) pivot
        (IdTrans Nat
          (NthL (Add i lo) (SortRangeL f' (S (Add lo i)) g (SortRangeL f' lo i p)))
          (NthL (Add i lo) (SortRangeL f' lo i p))
          pivot
          (NthSortRangeLLt f' (Add i lo) (S (Add lo i)) g (SortRangeL f' lo i p)
            (LeRwR (Add i lo) (Add i lo) (Add lo i) (AddComm i lo) (LeRefl (Add i lo))))
          (IdTrans Nat (NthL (Add i lo) (SortRangeL f' lo i p)) (NthL (Add i lo) p) pivot
            (NthSortRangeLGe f' (Add i lo) lo i p
              (LeRwL (Add i lo) (Add i lo) (Add lo i) (AddComm i lo) (LeRefl (Add i lo))))
            ppiv)) }
def SortedInHPIVTy : Term := prog{
  Π (i : Nat) → Π (g : Nat) → Π (lo : Nat) → Π (pivot : Nat) → Π (p : List Nat) → Π (f' : Nat) →
    Id Nat (NthL (Add i lo) p) pivot →
    Id Nat pivot (NthL (Add i lo) (SortRangeL f' (S (Add lo i)) g (SortRangeL f' lo i p))) }
def SortedInAL : Term := prog{
  λ (i : Nat). λ (g : Nat). λ (lo : Nat). λ (pivot : Nat). λ (p : List Nat). λ (f' : Nat).
    λ (pAL : AllLeR i lo pivot p). λ (bl : Le (Add lo i) (Len p)).
      AllLeRCong i lo pivot (SortRangeL f' lo i p) (SortRangeL f' (S (Add lo i)) g (SortRangeL f' lo i p))
        (λ (q : Nat). λ (hq : Le (S q) i).
          NthSortRangeLLt f' (Add q lo) (S (Add lo i)) g (SortRangeL f' lo i p) (PosLtBound q i lo hq))
        (AllLeRSortRange f' lo i pivot p bl pAL) }
def SortedInALTy : Term := prog{
  Π (i : Nat) → Π (g : Nat) → Π (lo : Nat) → Π (pivot : Nat) → Π (p : List Nat) → Π (f' : Nat) →
    AllLeR i lo pivot p → Le (Add lo i) (Len p) →
    AllLeR i lo pivot (SortRangeL f' (S (Add lo i)) g (SortRangeL f' lo i p)) }
def SortedInAG : Term := prog{
  λ (i : Nat). λ (g : Nat). λ (lo : Nat). λ (pivot : Nat). λ (p : List Nat). λ (f' : Nat).
    λ (pAG : AllGtR g (S (Add i lo)) pivot p).
    λ (br : Le (Add (S (Add lo i)) g) (Len (SortRangeL f' lo i p))).
      AllGtROffCong g (S (Add lo i)) (S (Add i lo)) pivot (SortRangeL f' (S (Add lo i)) g (SortRangeL f' lo i p))
        (IdCongr Nat Nat (λ (n : Nat). S n) (Add lo i) (Add i lo) (AddComm lo i))
        (AllGtRSortRange f' (S (Add lo i)) g pivot (SortRangeL f' lo i p) br
          (AllGtROffCong g (S (Add i lo)) (S (Add lo i)) pivot (SortRangeL f' lo i p)
            (IdCongr Nat Nat (λ (n : Nat). S n) (Add i lo) (Add lo i) (AddComm i lo))
            (AllGtRCong g (S (Add i lo)) pivot p (SortRangeL f' lo i p)
              (λ (m : Nat). λ (hm : Le (S m) g).
                NthSortRangeLGe f' (Add m (S (Add i lo))) lo i p (GapGeBound m i lo))
              pAG))) }
def SortedInAGTy : Term := prog{
  Π (i : Nat) → Π (g : Nat) → Π (lo : Nat) → Π (pivot : Nat) → Π (p : List Nat) → Π (f' : Nat) →
    AllGtR g (S (Add i lo)) pivot p → Le (Add (S (Add lo i)) g) (Len (SortRangeL f' lo i p)) →
    AllGtR g (S (Add i lo)) pivot (SortRangeL f' (S (Add lo i)) g (SortRangeL f' lo i p)) }

-- i+g = cnt-1 for the top partition (PartScanSizeL + AddZero); reused by the size
-- transport and both fuel-sufficiency derivations in SortedSortRangeL.
def PartSize : Term := prog{
  λ (lo : Nat). λ (cnt'' : Nat). λ (l : List Nat).
    IdTrans Nat
      (Add (PartIdxRangeL lo (S (S cnt'')) l) (PartGapRangeL lo (S (S cnt'')) l))
      (S (Add cnt'' Z)) (S cnt'')
      (PartScanSizeL (NthL lo l) lo (S cnt'') Z Z l)
      (IdCongr Nat Nat (λ (n : Nat). S n) (Add cnt'' Z) cnt'' (AddZero cnt'')) }
def PartSizeTy : Term := prog{
  Π (lo : Nat) → Π (cnt'' : Nat) → Π (l : List Nat) →
    Id Nat (Add (PartIdxRangeL lo (S (S cnt'')) l) (PartGapRangeL lo (S (S cnt'')) l)) (S cnt'') }


def SortedSortRangeL : Term := prog{
  λ (fuel : Nat).
    elim fuel return (λ (fz : Nat). Π (lo : Nat) → Π (cnt : Nat) → Π (l : List Nat) →
        Le cnt fz → Le (Add lo cnt) (Len l) → SortedR cnt lo (SortRangeL fz lo cnt l)) {
      Z => λ (lo : Nat). λ (cnt : Nat). λ (l : List Nat).
        elim cnt return (λ (cz : Nat). Le cz Z → Le (Add lo cz) (Len l) → SortedR cz lo l) {
          Z => λ (hf : Le Z Z). λ (hb : Le (Add lo Z) (Len l)). SortedRZero lo l,
          S (c) cih => λ (hf : Le (S c) Z). λ (hb : Le (Add lo (S c)) (Len l)). botElim (SortedR (S c) lo l) hf },
      S (f') ih => λ (lo : Nat). λ (cnt : Nat). λ (l : List Nat).
        elim cnt return (λ (cz : Nat). Le cz (S f') → Le (Add lo cz) (Len l) → SortedR cz lo (SortRangeL (S f') lo cz l)) {
          Z => λ (hf : Le Z (S f')). λ (hb : Le (Add lo Z) (Len l)). SortedRZero lo l,
          S (cnt') nih => elim cnt' return (λ (cz' : Nat). Le (S cz') (S f') → Le (Add lo (S cz')) (Len l) → SortedR (S cz') lo (SortRangeL (S f') lo (S cz') l)) {
            Z => λ (hf : Le (S Z) (S f')). λ (hb : Le (Add lo (S Z)) (Len l)). SortedROne lo l,
            S (cnt'') n2ih => λ (hf : Le (S (S cnt'')) (S f')). λ (hb : Le (Add lo (S (S cnt''))) (Len l)).
              SortedRWidthCong
                (S (Add (PartIdxRangeL lo (S (S cnt'')) l) (PartGapRangeL lo (S (S cnt'')) l)))
                (S (S cnt'')) lo
                (SortRangeL f' (S (Add lo (PartIdxRangeL lo (S (S cnt'')) l))) (PartGapRangeL lo (S (S cnt'')) l)
                  (SortRangeL f' lo (PartIdxRangeL lo (S (S cnt'')) l) (PartitionRangeL lo (S (S cnt'')) l)))
                (IdCongr Nat Nat (λ (n : Nat). S n)
                  (Add (PartIdxRangeL lo (S (S cnt'')) l) (PartGapRangeL lo (S (S cnt'')) l)) (S cnt'')
                  (PartSize lo cnt'' l))
                (Glue (PartIdxRangeL lo (S (S cnt'')) l) (PartGapRangeL lo (S (S cnt'')) l) lo (NthL lo l)
                  (SortRangeL f' (S (Add lo (PartIdxRangeL lo (S (S cnt'')) l))) (PartGapRangeL lo (S (S cnt'')) l)
                    (SortRangeL f' lo (PartIdxRangeL lo (S (S cnt'')) l) (PartitionRangeL lo (S (S cnt'')) l)))
                  (SortedInHPIV (PartIdxRangeL lo (S (S cnt'')) l) (PartGapRangeL lo (S (S cnt'')) l) lo (NthL lo l)
                    (PartitionRangeL lo (S (S cnt'')) l) f' (PartitionPivot lo (S (S cnt'')) l hb))
                  (SortedInSL (PartIdxRangeL lo (S (S cnt'')) l) (PartGapRangeL lo (S (S cnt'')) l) lo
                    (PartitionRangeL lo (S (S cnt'')) l) f'
                    (ih lo (PartIdxRangeL lo (S (S cnt'')) l) (PartitionRangeL lo (S (S cnt'')) l)
                      (LeTrans (PartIdxRangeL lo (S (S cnt'')) l) (S cnt'') f'
                        (LeRwR (PartIdxRangeL lo (S (S cnt'')) l)
                          (Add (PartIdxRangeL lo (S (S cnt'')) l) (PartGapRangeL lo (S (S cnt'')) l)) (S cnt'')
                          (PartSize lo cnt'' l)
                          (LeAdd (PartIdxRangeL lo (S (S cnt'')) l) (PartGapRangeL lo (S (S cnt'')) l)))
                        hf)
                      (SortRangeBL lo cnt'' l hb)))
                  (SortedInAL (PartIdxRangeL lo (S (S cnt'')) l) (PartGapRangeL lo (S (S cnt'')) l) lo (NthL lo l)
                    (PartitionRangeL lo (S (S cnt'')) l) f'
                    (PartitionAllLeR lo (S (S cnt'')) l hb) (SortRangeBL lo cnt'' l hb))
                  (SortedInAG (PartIdxRangeL lo (S (S cnt'')) l) (PartGapRangeL lo (S (S cnt'')) l) lo (NthL lo l)
                    (PartitionRangeL lo (S (S cnt'')) l) f'
                    (PartitionAllGtR lo (S (S cnt'')) l hb) (SortRangeBR f' lo cnt'' l hb))
                  (SortedInSR (PartIdxRangeL lo (S (S cnt'')) l) (PartGapRangeL lo (S (S cnt'')) l) lo
                    (PartitionRangeL lo (S (S cnt'')) l) f'
                    (ih (S (Add lo (PartIdxRangeL lo (S (S cnt'')) l))) (PartGapRangeL lo (S (S cnt'')) l)
                      (SortRangeL f' lo (PartIdxRangeL lo (S (S cnt'')) l) (PartitionRangeL lo (S (S cnt'')) l))
                      (LeTrans (PartGapRangeL lo (S (S cnt'')) l) (S cnt'') f'
                        (LeRwR (PartGapRangeL lo (S (S cnt'')) l)
                          (Add (PartIdxRangeL lo (S (S cnt'')) l) (PartGapRangeL lo (S (S cnt'')) l)) (S cnt'')
                          (PartSize lo cnt'' l)
                          (LeAddL (PartGapRangeL lo (S (S cnt'')) l) (PartIdxRangeL lo (S (S cnt'')) l)))
                        hf)
                      (SortRangeBR f' lo cnt'' l hb))))
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
  λ (p : Nat). λ (l : List Nat).
    elim l return (λ (lz : List Nat). Type) {
      Nil => Unit,
      Cons (h) (t) ih => Σ (hh : Le h p) → ih } }

def Lb : Term := prog{
  λ (p : Nat). λ (l : List Nat).
    elim l return (λ (lz : List Nat). Type) {
      Nil => Unit,
      Cons (h) (t) ih => Σ (hh : Le p h) → ih } }

def InsertL : Term := prog{
  λ (k : Nat).
    elim k return (λ (kz : Nat). Nat → List Nat → List Nat) {
      Z => λ (x : Nat). λ (l : List Nat). Cons x l,
      S (k2) ih => λ (x : Nat). λ (l : List Nat).
        elim l return (λ (lz : List Nat). List Nat) {
          Nil => Cons x Nil,
          Cons (h) (t) iht => Cons h (ih x t) } } }

/-- Generic J-transport at `List Nat`: `x = y ⟹ P x → P y`. `LeRwR`/`LeRwL` are
    this at `Le`-shaped `P` over `Nat`; a back-less body needs the unrestricted form,
    because every certificate it returns is stated over an exit snapshot it only
    knows PROPOSITIONALLY (the callee's evidence), never definitionally. -/
def ListRw : Term := prog{
  λ (P : List Nat → Type). λ (x : List Nat). λ (y : List Nat).
    λ (h : Id (List Nat) x y). λ (px : P x).
      j (List Nat) x (λ (y2 : List Nat). λ (hh : Id (List Nat) x y2). P y2) px y h }
def ListRwTy : Term := prog{
  Π (P : List Nat → Type) → Π (x : List Nat) → Π (y : List Nat) →
    Id (List Nat) x y → P x → P y }

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
  λ (h : Nat). λ (t : List Nat). λ (s : Σ (hb : Bound h t) → Sorted t).
    elim s return (λ (q : Σ (hb : Bound h t) → Sorted t). Bound h t) {
      Pair (x) (y) => x } }
def SortedHeadTy : Term := prog{
  Π (h : Nat) → Π (t : List Nat) → Sorted (Cons h t) → Bound h t }

def SortedTail : Term := prog{
  λ (h : Nat). λ (t : List Nat). λ (s : Σ (hb : Bound h t) → Sorted t).
    elim s return (λ (q : Σ (hb : Bound h t) → Sorted t). Sorted t) {
      Pair (x) (y) => y } }
def SortedTailTy : Term := prog{
  Π (h : Nat) → Π (t : List Nat) → Sorted (Cons h t) → Sorted t }

def UbHead : Term := prog{
  λ (p : Nat). λ (h : Nat). λ (t : List Nat). λ (u : Σ (hu : Le h p) → Ub p t).
    elim u return (λ (q : Σ (hu : Le h p) → Ub p t). Le h p) {
      Pair (x) (y) => x } }
def UbHeadTy : Term := prog{
  Π (p : Nat) → Π (h : Nat) → Π (t : List Nat) → Ub p (Cons h t) → Le h p }

def UbTail : Term := prog{
  λ (p : Nat). λ (h : Nat). λ (t : List Nat). λ (u : Σ (hu : Le h p) → Ub p t).
    elim u return (λ (q : Σ (hu : Le h p) → Ub p t). Ub p t) {
      Pair (x) (y) => y } }
def UbTailTy : Term := prog{
  Π (p : Nat) → Π (h : Nat) → Π (t : List Nat) → Ub p (Cons h t) → Ub p t }

/-- `Lb p l ⟹ Bound p l`: a lower bound on EVERY element is in particular a bound on
    the HEAD, which is all `Sorted (Cons p b)` asks of the pivot. The two predicates
    agree definitionally at `Nil` (both `⊤`) and differ at `Cons` only by how much
    they say, so this is a `listRec` whose `Cons` arm is a first projection. -/
def LbBound : Term := prog{
  λ (p : Nat). λ (l : List Nat).
    elim l return (λ (lz : List Nat). Lb p lz → Bound p lz) {
      Nil => λ (hn : Unit). hn,
      Cons (h) (t) ih => λ (hl : Σ (hh : Le p h) → Lb p t).
        elim hl return (λ (q : Σ (hh : Le p h) → Lb p t). Le p h) {
          Pair (x) (y) => x } } }
def LbBoundTy : Term := prog{
  Π (p : Nat) → Π (l : List Nat) → Lb p l → Bound p l }

/-- Head-bound transport across the splice: if `h` bounds the head of `t`, and `h ≤
    p`, then `h` bounds the head of `t ++ p :: b`. The `listRec` on `t` IS the case
    analysis the caller would otherwise have to do inline: at `Nil` the new head is
    the PIVOT (so the bound is `Le h p`, the second hypothesis), at `Cons` the head is
    unchanged by the append (so the bound is the first hypothesis, verbatim). No IH is
    consumed — `Bound` looks exactly one cell deep, so this recursion is a case
    analysis and nothing more. -/
def BoundAppend : Term := prog{
  λ (h : Nat). λ (p : Nat). λ (t : List Nat). λ (b : List Nat).
    elim t return (λ (tz : List Nat).
        Bound h tz → Le h p → Bound h (Append tz (Cons p b))) {
      Nil => λ (hb : Unit). λ (hp : Le h p). hp,
      Cons (h2) (t2) ih => λ (hb : Le h h2). λ (hp : Le h p). hb } }
def BoundAppendTy : Term := prog{
  Π (h : Nat) → Π (p : Nat) → Π (t : List Nat) → Π (b : List Nat) →
    Bound h t → Le h p → Bound h (Append t (Cons p b)) }

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
  λ (p : Nat). λ (a : List Nat). λ (b : List Nat).
    λ (sa : Sorted a). λ (ua : Ub p a). λ (sb : Sorted b). λ (lb : Lb p b).
      elim a return (λ (az : List Nat).
          Sorted az → Ub p az → Sorted (Append az (Cons p b))) {
        Nil => λ (sn : Unit). λ (un : Unit). Pair(LbBound p b lb, sb),
        Cons (h) (t) ih => λ (sc : Sorted (Cons h t)). λ (uc : Ub p (Cons h t)).
          Pair(BoundAppend h p t b (SortedHead h t sc) (UbHead p h t uc),
               ih (SortedTail h t sc) (UbTail p h t uc))
      } sa ua }
def SortedAppendPivotTy : Term := prog{
  Π (p : Nat) → Π (a : List Nat) → Π (b : List Nat) →
    Sorted a → Ub p a → Sorted b → Lb p b → Sorted (Append a (Cons p b)) }

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
  λ (n : Nat). λ (x : Nat). λ (a : List Nat). λ (b : List Nat). λ (c : List Nat).
    λ (h : Id Nat (Add (Count n a) (Count n b)) (Count n c)).
      elim (Eqb n x) return (λ (bv : Bool).
        Id Nat (Add (boolRec (λ (w : Bool). Nat) (S (Count n a)) (Count n a) bv) (Count n b))
               (boolRec (λ (w : Bool). Nat) (S (Count n c)) (Count n c) bv)) {
        True => IdCongr Nat Nat (λ (r : Nat). S r)
                  (Add (Count n a) (Count n b)) (Count n c) h,
        False => h } }
def CountConsLTy : Term := prog{
  Π (n : Nat) → Π (x : Nat) → Π (a : List Nat) → Π (b : List Nat) → Π (c : List Nat) →
    Id Nat (Add (Count n a) (Count n b)) (Count n c) →
    Id Nat (Add (Count n (Cons x a)) (Count n b)) (Count n (Cons x c)) }

/-- Head onto the RIGHT part. Here the successor lands under `Add`'s SECOND argument,
    which is where the asymmetry of a first-argument-recursive `Add` shows up: the
    `True` arm needs `AddSucc` before the `IdCongr`. -/
def CountConsR : Term := prog{
  λ (n : Nat). λ (x : Nat). λ (a : List Nat). λ (b : List Nat). λ (c : List Nat).
    λ (h : Id Nat (Add (Count n a) (Count n b)) (Count n c)).
      elim (Eqb n x) return (λ (bv : Bool).
        Id Nat (Add (Count n a) (boolRec (λ (w : Bool). Nat) (S (Count n b)) (Count n b) bv))
               (boolRec (λ (w : Bool). Nat) (S (Count n c)) (Count n c) bv)) {
        True => IdTrans Nat (Add (Count n a) (S (Count n b)))
                  (S (Add (Count n a) (Count n b))) (S (Count n c))
                  (AddSucc (Count n a) (Count n b))
                  (IdCongr Nat Nat (λ (r : Nat). S r)
                    (Add (Count n a) (Count n b)) (Count n c) h),
        False => h } }
def CountConsRTy : Term := prog{
  Π (n : Nat) → Π (x : Nat) → Π (a : List Nat) → Π (b : List Nat) → Π (c : List Nat) →
    Id Nat (Add (Count n a) (Count n b)) (Count n c) →
    Id Nat (Add (Count n a) (Count n (Cons x b))) (Count n (Cons x c)) }

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
  λ (p : Nat). λ (h : Nat). λ (t : List Nat). λ (u : Σ (hu : Le p h) → Lb p t).
    elim u return (λ (q : Σ (hu : Le p h) → Lb p t). Le p h) {
      Pair (x) (y) => x } }
def LbHeadTy : Term := prog{
  Π (p : Nat) → Π (h : Nat) → Π (t : List Nat) → Lb p (Cons h t) → Le p h }

def LbTail : Term := prog{
  λ (p : Nat). λ (h : Nat). λ (t : List Nat). λ (u : Σ (hu : Le p h) → Lb p t).
    elim u return (λ (q : Σ (hu : Le p h) → Lb p t). Lb p t) {
      Pair (x) (y) => y } }
def LbTailTy : Term := prog{
  Π (p : Nat) → Π (h : Nat) → Π (t : List Nat) → Lb p (Cons h t) → Lb p t }

/-- `Ub p l ⟹ nothing above p occurs in l`. At `Cons h t` the head misses every
    `x > p`, because `h ≤ p < x` makes `Eqb x h` False (`EqbGtFalse`), so the count
    steps past the head onto the IH. -/
def NoAboveOfUb : Term := prog{
  λ (p : Nat). λ (l : List Nat).
    elim l return (λ (lz : List Nat).
        Ub p lz → Π (x : Nat) → Le (S p) x → Id Nat (Count x lz) Z) {
      Nil => λ (u : Unit). λ (x : Nat). λ (hx : Le (S p) x). Refl,
      Cons (h) (t) ih => λ (u : Σ (hh : Le h p) → Ub p t). λ (x : Nat). λ (hx : Le (S p) x).
        IdTrans Nat (Count x (Cons h t)) (Count x t) Z
          (CountConsMiss x h t
            (EqbGtFalse h x (LeTrans (S h) (S p) x (UbHead p h t u) hx)))
          (ih (UbTail p h t u) x hx) } }
def NoAboveOfUbTy : Term := prog{
  Π (p : Nat) → Π (l : List Nat) → Ub p l →
    Π (x : Nat) → Le (S p) x → Id Nat (Count x l) Z }

/-- …and back. The head bound comes from a `Leb h p` split: if it were False then
    `h > p`, so `Count h l = Z` by hypothesis — but `Count h (Cons h t)` is `S (count
    h t)` (`EqbRefl`), and `Z = S _` is `znots`. The tail hypothesis is the same
    argument run the other way: `Count x (Cons h t) = Z` forces `Count x t = Z`,
    trivially when `Eqb x h` misses and by the same contradiction when it hits. -/
def UbOfNoAbove : Term := prog{
  λ (p : Nat). λ (l : List Nat).
    elim l return (λ (lz : List Nat).
        (Π (x : Nat) → Le (S p) x → Id Nat (Count x lz) Z) → Ub p lz) {
      Nil => λ (hn : Π (x : Nat) → Le (S p) x → Id Nat (Count x Nil) Z). unit,
      Cons (h) (t) ih => λ (hn : Π (x : Nat) → Le (S p) x → Id Nat (Count x (Cons h t)) Z).
        Pair(
          elim (Leb h p) return (λ (bv : Bool). Id Bool (Leb h p) bv → Le h p) {
            True => λ (e : Id Bool (Leb h p) True). LebTrueLe h p e,
            False => λ (e : Id Bool (Leb h p) False).
              botElim (Le h p)
                (Znots (Count h t)
                  (IdTrans Nat Z (Count h (Cons h t)) (S (Count h t))
                    (IdSym Nat (Count h (Cons h t)) Z (hn h (LebFalseGt h p e)))
                    (CountConsHit h h t (EqbRefl h))))
          } Refl,
          ih (λ (x : Nat). λ (hx : Le (S p) x).
                elim (Eqb x h) return (λ (bv : Bool). Id Bool (Eqb x h) bv → Id Nat (Count x t) Z) {
                  True => λ (eq : Id Bool (Eqb x h) True).
                    botElim (Id Nat (Count x t) Z)
                      (Znots (Count x t)
                        (IdTrans Nat Z (Count x (Cons h t)) (S (Count x t))
                          (IdSym Nat (Count x (Cons h t)) Z (hn x hx))
                          (CountConsHit x h t eq))),
                  False => λ (eq : Id Bool (Eqb x h) False).
                    IdTrans Nat (Count x t) (Count x (Cons h t)) Z
                      (IdSym Nat (Count x (Cons h t)) (Count x t) (CountConsMiss x h t eq))
                      (hn x hx)
                } Refl)) } }
def UbOfNoAboveTy : Term := prog{
  Π (p : Nat) → Π (l : List Nat) →
    (Π (x : Nat) → Le (S p) x → Id Nat (Count x l) Z) → Ub p l }

/-- THE KEYSTONE. An upper bound survives any count-preserving rearrangement — which
    is exactly what a recursive sort hands back about the part it sorted. -/
def UbPerm : Term := prog{
  λ (p : Nat). λ (a : List Nat). λ (b : List Nat).
    λ (hc : Π (n : Nat) → Id Nat (Count n a) (Count n b)). λ (hb : Ub p b).
      UbOfNoAbove p a (λ (x : Nat). λ (hx : Le (S p) x).
        IdTrans Nat (Count x a) (Count x b) Z (hc x) (NoAboveOfUb p b hb x hx)) }
def UbPermTy : Term := prog{
  Π (p : Nat) → Π (a : List Nat) → Π (b : List Nat) →
    (Π (n : Nat) → Id Nat (Count n a) (Count n b)) → Ub p b → Ub p a }

/-- The `Lb` mirror: `Lb p l ⟹ nothing strictly below p occurs`. Here the head misses
    every `x < p ≤ h` by `EqbLtFalse`. -/
def NoBelowOfLb : Term := prog{
  λ (p : Nat). λ (l : List Nat).
    elim l return (λ (lz : List Nat).
        Lb p lz → Π (x : Nat) → Le (S x) p → Id Nat (Count x lz) Z) {
      Nil => λ (u : Unit). λ (x : Nat). λ (hx : Le (S x) p). Refl,
      Cons (h) (t) ih => λ (u : Σ (hh : Le p h) → Lb p t). λ (x : Nat). λ (hx : Le (S x) p).
        IdTrans Nat (Count x (Cons h t)) (Count x t) Z
          (CountConsMiss x h t
            (EqbLtFalse x h (LeTrans (S x) p h hx (LbHead p h t u))))
          (ih (LbTail p h t u) x hx) } }
def NoBelowOfLbTy : Term := prog{
  Π (p : Nat) → Π (l : List Nat) → Lb p l →
    Π (x : Nat) → Le (S x) p → Id Nat (Count x l) Z }

def LbOfNoBelow : Term := prog{
  λ (p : Nat). λ (l : List Nat).
    elim l return (λ (lz : List Nat).
        (Π (x : Nat) → Le (S x) p → Id Nat (Count x lz) Z) → Lb p lz) {
      Nil => λ (hn : Π (x : Nat) → Le (S x) p → Id Nat (Count x Nil) Z). unit,
      Cons (h) (t) ih => λ (hn : Π (x : Nat) → Le (S x) p → Id Nat (Count x (Cons h t)) Z).
        Pair(
          elim (Leb p h) return (λ (bv : Bool). Id Bool (Leb p h) bv → Le p h) {
            True => λ (e : Id Bool (Leb p h) True). LebTrueLe p h e,
            False => λ (e : Id Bool (Leb p h) False).
              botElim (Le p h)
                (Znots (Count h t)
                  (IdTrans Nat Z (Count h (Cons h t)) (S (Count h t))
                    (IdSym Nat (Count h (Cons h t)) Z (hn h (LebFalseGt p h e)))
                    (CountConsHit h h t (EqbRefl h))))
          } Refl,
          ih (λ (x : Nat). λ (hx : Le (S x) p).
                elim (Eqb x h) return (λ (bv : Bool). Id Bool (Eqb x h) bv → Id Nat (Count x t) Z) {
                  True => λ (eq : Id Bool (Eqb x h) True).
                    botElim (Id Nat (Count x t) Z)
                      (Znots (Count x t)
                        (IdTrans Nat Z (Count x (Cons h t)) (S (Count x t))
                          (IdSym Nat (Count x (Cons h t)) Z (hn x hx))
                          (CountConsHit x h t eq))),
                  False => λ (eq : Id Bool (Eqb x h) False).
                    IdTrans Nat (Count x t) (Count x (Cons h t)) Z
                      (IdSym Nat (Count x (Cons h t)) (Count x t) (CountConsMiss x h t eq))
                      (hn x hx)
                } Refl)) } }
def LbOfNoBelowTy : Term := prog{
  Π (p : Nat) → Π (l : List Nat) →
    (Π (x : Nat) → Le (S x) p → Id Nat (Count x l) Z) → Lb p l }

def LbPerm : Term := prog{
  λ (p : Nat). λ (a : List Nat). λ (b : List Nat).
    λ (hc : Π (n : Nat) → Id Nat (Count n a) (Count n b)). λ (hb : Lb p b).
      LbOfNoBelow p a (λ (x : Nat). λ (hx : Le (S x) p).
        IdTrans Nat (Count x a) (Count x b) Z (hc x) (NoBelowOfLb p b hb x hx)) }
def LbPermTy : Term := prog{
  Π (p : Nat) → Π (a : List Nat) → Π (b : List Nat) →
    (Π (n : Nat) → Id Nat (Count n a) (Count n b)) → Lb p b → Lb p a }

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
  λ (x : Nat). λ (n : Nat). λ (a : Array n Nat).
    arrRec Nat (λ (m : Nat). λ (b : Array m Nat). Nat) Z
      (λ (k : Nat). λ (h : Nat). λ (t : Array k Nat). λ (ih : Nat).
        elim (Eqb x h) return (λ (bz : Bool). Nat) { True => S ih, False => ih })
      n a }

/-- `BoundA p a` — the head of `a` is ≥ `p`. `Bound`'s transfer. -/
def BoundA : Term := prog{
  λ (p : Nat). λ (n : Nat). λ (a : Array n Nat).
    arrRec Nat (λ (m : Nat). λ (b : Array m Nat). Type) Unit
      (λ (k : Nat). λ (h : Nat). λ (t : Array k Nat). λ (ih : Type). Le p h) n a }

/-- `SortedA a` — the Σ-chain over the spine. `Sorted`'s transfer. -/
def SortedA : Term := prog{
  λ (n : Nat). λ (a : Array n Nat).
    arrRec Nat (λ (m : Nat). λ (b : Array m Nat). Type) Unit
      (λ (k : Nat). λ (h : Nat). λ (t : Array k Nat). λ (ih : Type).
        Σ (hb : BoundA h k t) → ih) n a }

/-- `UbA p a` — every element of `a` is ≤ `p`. `Ub`'s transfer. -/
def UbA : Term := prog{
  λ (p : Nat). λ (n : Nat). λ (a : Array n Nat).
    arrRec Nat (λ (m : Nat). λ (b : Array m Nat). Type) Unit
      (λ (k : Nat). λ (h : Nat). λ (t : Array k Nat). λ (ih : Type).
        Σ (hh : Le h p) → ih) n a }

/-- `LbA p a` — every element of `a` is ≥ `p`. `Lb`'s transfer. -/
def LbA : Term := prog{
  λ (p : Nat). λ (n : Nat). λ (a : Array n Nat).
    arrRec Nat (λ (m : Nat). λ (b : Array m Nat). Type) Unit
      (λ (k : Nat). λ (h : Nat). λ (t : Array k Nat). λ (ih : Type).
        Σ (hh : Le p h) → ih) n a }

/-- `Asingle x` — the one-element array, `[x]`. ¶6's glue is stated over
    `arrCat (Asingle p) r`, which is the array spelling of `Cons p b`. -/
def Asingle : Term := prog{ λ (x : Nat). acons Z x Arr() }

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
  λ (k : Nat). λ (h : Nat). λ (t : Array k Nat).
    λ (s : Σ (hb : BoundA h k t) → SortedA k t).
      elim s return (λ (q : Σ (hb : BoundA h k t) → SortedA k t). BoundA h k t) {
        Pair (x) (y) => x } }
def SortedHeadATy : Term := prog{
  Π (k : Nat) → Π (h : Nat) → Π (t : Array k Nat) →
    SortedA (S k) (acons k h t) → BoundA h k t }

def SortedTailA : Term := prog{
  λ (k : Nat). λ (h : Nat). λ (t : Array k Nat).
    λ (s : Σ (hb : BoundA h k t) → SortedA k t).
      elim s return (λ (q : Σ (hb : BoundA h k t) → SortedA k t). SortedA k t) {
        Pair (x) (y) => y } }
def SortedTailATy : Term := prog{
  Π (k : Nat) → Π (h : Nat) → Π (t : Array k Nat) →
    SortedA (S k) (acons k h t) → SortedA k t }

def UbHeadA : Term := prog{
  λ (p : Nat). λ (k : Nat). λ (h : Nat). λ (t : Array k Nat).
    λ (u : Σ (hu : Le h p) → UbA p k t).
      elim u return (λ (q : Σ (hu : Le h p) → UbA p k t). Le h p) {
        Pair (x) (y) => x } }
def UbHeadATy : Term := prog{
  Π (p : Nat) → Π (k : Nat) → Π (h : Nat) → Π (t : Array k Nat) →
    UbA p (S k) (acons k h t) → Le h p }

def UbTailA : Term := prog{
  λ (p : Nat). λ (k : Nat). λ (h : Nat). λ (t : Array k Nat).
    λ (u : Σ (hu : Le h p) → UbA p k t).
      elim u return (λ (q : Σ (hu : Le h p) → UbA p k t). UbA p k t) {
        Pair (x) (y) => y } }
def UbTailATy : Term := prog{
  Π (p : Nat) → Π (k : Nat) → Π (h : Nat) → Π (t : Array k Nat) →
    UbA p (S k) (acons k h t) → UbA p k t }

/-- `LbA p a ⟹ BoundA p a`, `LbBound`'s transfer: a lower bound on every element is in
    particular a bound on the head, which is all `SortedA (acons p b)` asks of the pivot. -/
def LbBoundA : Term := prog{
  λ (p : Nat). λ (n : Nat). λ (a : Array n Nat).
    arrRec Nat (λ (m : Nat). λ (b : Array m Nat). LbA p m b → BoundA p m b)
      (λ (hn : Unit). hn)
      (λ (k : Nat). λ (h : Nat). λ (t : Array k Nat).
        λ (ih : LbA p k t → BoundA p k t).
          λ (hl : Σ (hh : Le p h) → LbA p k t).
            elim hl return (λ (q : Σ (hh : Le p h) → LbA p k t). Le p h) {
              Pair (x) (y) => x })
      n a }
def LbBoundATy : Term := prog{
  Π (p : Nat) → Π (n : Nat) → Π (a : Array n Nat) → LbA p n a → BoundA p n a }

/-- `BoundAppend`'s transfer: the head bound survives the splice. The recursion IS the
    case analysis — at the empty array the new head is the PIVOT, otherwise the head is
    unchanged by the concatenation. No IH is consumed, because `BoundA` looks exactly one
    cell deep. -/
def BoundArrCat : Term := prog{
  λ (h : Nat). λ (p : Nat). λ (k : Nat). λ (t : Array k Nat).
    λ (q : Nat). λ (b : Array q Nat).
      arrRec Nat (λ (m : Nat). λ (tz : Array m Nat).
          BoundA h m tz → Le h p →
            BoundA h (Add m (S q)) (arrCat m (S q) tz (arrCat 1 q (Asingle p) b)))
        (λ (hb : Unit). λ (hp : Le h p). hp)
        (λ (k2 : Nat). λ (h2 : Nat). λ (t2 : Array k2 Nat).
          λ (ih : BoundA h k2 t2 → Le h p →
              BoundA h (Add k2 (S q)) (arrCat k2 (S q) t2 (arrCat 1 q (Asingle p) b))).
            λ (hb : Le h h2). λ (hp : Le h p). hb)
        k t }
def BoundArrCatTy : Term := prog{
  Π (h : Nat) → Π (p : Nat) → Π (k : Nat) → Π (t : Array k Nat) →
    Π (q : Nat) → Π (b : Array q Nat) →
      BoundA h k t → Le h p →
        BoundA h (Add k (S q)) (arrCat k (S q) t (arrCat 1 q (Asingle p) b)) }

/-- **The quicksort glue** — `SortedAppendPivot` with the container swapped, and
    nothing else changed. This is ¶6's "textbook quicksort correctness statement, in the
    textbook shape", and the standing check on the whole migration: if this were not the
    near-verbatim restatement, something would be off. -/
def SortedArrCat : Term := prog{
  λ (p : Nat). λ (m : Nat). λ (a : Array m Nat). λ (q : Nat). λ (b : Array q Nat).
    λ (sa : SortedA m a). λ (ua : UbA p m a). λ (sb : SortedA q b). λ (lb : LbA p q b).
      arrRec Nat (λ (mz : Nat). λ (az : Array mz Nat).
          SortedA mz az → UbA p mz az →
            SortedA (Add mz (S q)) (arrCat mz (S q) az (arrCat 1 q (Asingle p) b)))
        (λ (sn : Unit). λ (un : Unit). Pair(LbBoundA p q b lb, sb))
        (λ (k : Nat). λ (h : Nat). λ (t : Array k Nat).
          λ (ih : SortedA k t → UbA p k t →
              SortedA (Add k (S q)) (arrCat k (S q) t (arrCat 1 q (Asingle p) b))).
            λ (sc : Σ (hb : BoundA h k t) → SortedA k t).
              λ (uc : Σ (hu : Le h p) → UbA p k t).
                Pair(BoundArrCat h p k t q b (SortedHeadA k h t sc) (UbHeadA p k h t uc),
                     ih (SortedTailA k h t sc) (UbTailA p k h t uc)))
        m a sa ua }
def SortedArrCatTy : Term := prog{
  Π (p : Nat) → Π (m : Nat) → Π (a : Array m Nat) → Π (q : Nat) → Π (b : Array q Nat) →
    SortedA m a → UbA p m a → SortedA q b → LbA p q b →
      SortedA (Add m (S q)) (arrCat m (S q) a (arrCat 1 q (Asingle p) b)) }

/-- `CountAppend`'s transfer, and ¶6's named survivor: "the one lemma that replaces
    `CountAppend`/`Take`/`Drop` is `CountArrCat : count x (arrCat a b) = add (count x a)
    (count x b)`, which is the same induction." It is the same induction — the `Cons`
    arm's dependent Bool-elim on `Eqb x h` transfers unchanged, because `CountA` unfolds
    on an `acons` exactly as `Count` unfolds on a `Cons`. -/
def CountArrCat : Term := prog{
  λ (x : Nat). λ (m : Nat). λ (a : Array m Nat). λ (q : Nat). λ (b : Array q Nat).
    arrRec Nat (λ (mz : Nat). λ (az : Array mz Nat).
        Id Nat (CountA x (Add mz q) (arrCat mz q az b))
               (Add (CountA x mz az) (CountA x q b)))
      Refl
      (λ (k : Nat). λ (h : Nat). λ (t : Array k Nat).
        λ (ih : Id Nat (CountA x (Add k q) (arrCat k q t b))
                       (Add (CountA x k t) (CountA x q b))).
          elim (Eqb x h) return (λ (bv : Bool).
            Id Nat (boolRec (λ (w : Bool). Nat)
                     (S (CountA x (Add k q) (arrCat k q t b)))
                     (CountA x (Add k q) (arrCat k q t b)) bv)
                   (Add (boolRec (λ (w : Bool). Nat)
                     (S (CountA x k t)) (CountA x k t) bv) (CountA x q b))) {
            True => IdCongr Nat Nat (λ (n : Nat). S n)
                      (CountA x (Add k q) (arrCat k q t b))
                      (Add (CountA x k t) (CountA x q b)) ih,
            False => ih })
      m a }
def CountArrCatTy : Term := prog{
  Π (x : Nat) → Π (m : Nat) → Π (a : Array m Nat) → Π (q : Nat) → Π (b : Array q Nat) →
    Id Nat (CountA x (Add m q) (arrCat m q a b)) (Add (CountA x m a) (CountA x q b)) }

/-! ### The permutation layer, transferred

    M23's keystone: "`Ub` and `Lb` (Σ-chains over the spine) are not natively
    permutation-invariant. Cross to the multiset, where the property is
    `Π x. x > p → Count x l = Z` and permutation-invariance is a one-line `IdTrans`."
    That crossing transfers with the container like everything else. -/

def CountAconsHit : Term := prog{
  λ (m : Nat). λ (a : Nat). λ (k : Nat). λ (l : Array k Nat). λ (hq : Id Bool (Eqb m a) True).
    j Bool True
      (λ (z : Bool). λ (h : Id Bool True z).
        Id Nat (boolRec (λ (w : Bool). Nat) (S (CountA m k l)) (CountA m k l) z)
               (S (CountA m k l)))
      Refl (Eqb m a) (IdSym Bool (Eqb m a) True hq) }
def CountAconsHitTy : Term := prog{
  Π (m : Nat) → Π (a : Nat) → Π (k : Nat) → Π (l : Array k Nat) → Id Bool (Eqb m a) True →
    Id Nat (CountA m (S k) (acons k a l)) (S (CountA m k l)) }

def CountAconsMiss : Term := prog{
  λ (m : Nat). λ (h : Nat). λ (k : Nat). λ (t : Array k Nat). λ (hq : Id Bool (Eqb m h) False).
    j Bool False
      (λ (z : Bool). λ (hh : Id Bool False z).
        Id Nat (boolRec (λ (w : Bool). Nat) (S (CountA m k t)) (CountA m k t) z)
               (CountA m k t))
      Refl (Eqb m h) (IdSym Bool (Eqb m h) False hq) }
def CountAconsMissTy : Term := prog{
  Π (m : Nat) → Π (h : Nat) → Π (k : Nat) → Π (t : Array k Nat) → Id Bool (Eqb m h) False →
    Id Nat (CountA m (S k) (acons k h t)) (CountA m k t) }

def LbHeadA : Term := prog{
  λ (p : Nat). λ (k : Nat). λ (h : Nat). λ (t : Array k Nat).
    λ (u : Σ (hh : Le p h) → LbA p k t).
      elim u return (λ (q : Σ (hh : Le p h) → LbA p k t). Le p h) { Pair (x) (y) => x } }
def LbTailA : Term := prog{
  λ (p : Nat). λ (k : Nat). λ (h : Nat). λ (t : Array k Nat).
    λ (u : Σ (hh : Le p h) → LbA p k t).
      elim u return (λ (q : Σ (hh : Le p h) → LbA p k t). LbA p k t) { Pair (x) (y) => y } }

def NoAboveOfUbA : Term := prog{
  λ (p : Nat). λ (n : Nat). λ (a : Array n Nat).
    arrRec Nat (λ (m : Nat). λ (az : Array m Nat).
        UbA p m az → Π (x : Nat) → Le (S p) x → Id Nat (CountA x m az) Z)
      (λ (u : Unit). λ (x : Nat). λ (hx : Le (S p) x). Refl)
      (λ (k : Nat). λ (h : Nat). λ (t : Array k Nat).
        λ (ih : UbA p k t → Π (x : Nat) → Le (S p) x → Id Nat (CountA x k t) Z).
          λ (u : Σ (hh : Le h p) → UbA p k t). λ (x : Nat). λ (hx : Le (S p) x).
            IdTrans Nat (CountA x (S k) (acons k h t)) (CountA x k t) Z
              (CountAconsMiss x h k t
                (EqbGtFalse h x (LeTrans (S h) (S p) x (UbHeadA p k h t u) hx)))
              (ih (UbTailA p k h t u) x hx))
      n a }
def NoAboveOfUbATy : Term := prog{
  Π (p : Nat) → Π (n : Nat) → Π (a : Array n Nat) → UbA p n a →
    Π (x : Nat) → Le (S p) x → Id Nat (CountA x n a) Z }

def UbOfNoAboveA : Term := prog{
  λ (p : Nat). λ (n : Nat). λ (a : Array n Nat).
    arrRec Nat (λ (m : Nat). λ (az : Array m Nat).
        (Π (x : Nat) → Le (S p) x → Id Nat (CountA x m az) Z) → UbA p m az)
      (λ (hn : Π (x : Nat) → Le (S p) x → Id Nat (CountA x Z Arr()) Z). unit)
      (λ (k : Nat). λ (h : Nat). λ (t : Array k Nat).
        λ (ih : (Π (x : Nat) → Le (S p) x → Id Nat (CountA x k t) Z) → UbA p k t).
          λ (hn : Π (x : Nat) → Le (S p) x → Id Nat (CountA x (S k) (acons k h t)) Z).
            Pair(
              elim (Leb h p) return (λ (bv : Bool). Id Bool (Leb h p) bv → Le h p) {
                True => λ (e : Id Bool (Leb h p) True). LebTrueLe h p e,
                False => λ (e : Id Bool (Leb h p) False).
                  botElim (Le h p)
                    (Znots (CountA h k t)
                      (IdTrans Nat Z (CountA h (S k) (acons k h t)) (S (CountA h k t))
                        (IdSym Nat (CountA h (S k) (acons k h t)) Z (hn h (LebFalseGt h p e)))
                        (CountAconsHit h h k t (EqbRefl h))))
              } Refl,
              ih (λ (x : Nat). λ (hx : Le (S p) x).
                    elim (Eqb x h) return (λ (bv : Bool).
                        Id Bool (Eqb x h) bv → Id Nat (CountA x k t) Z) {
                      True => λ (eq : Id Bool (Eqb x h) True).
                        botElim (Id Nat (CountA x k t) Z)
                          (Znots (CountA x k t)
                            (IdTrans Nat Z (CountA x (S k) (acons k h t)) (S (CountA x k t))
                              (IdSym Nat (CountA x (S k) (acons k h t)) Z (hn x hx))
                              (CountAconsHit x h k t eq))),
                      False => λ (eq : Id Bool (Eqb x h) False).
                        IdTrans Nat (CountA x k t) (CountA x (S k) (acons k h t)) Z
                          (IdSym Nat (CountA x (S k) (acons k h t)) (CountA x k t)
                            (CountAconsMiss x h k t eq))
                          (hn x hx)
                    } Refl)))
      n a }
def UbOfNoAboveATy : Term := prog{
  Π (p : Nat) → Π (n : Nat) → Π (a : Array n Nat) →
    (Π (x : Nat) → Le (S p) x → Id Nat (CountA x n a) Z) → UbA p n a }

/-- THE KEYSTONE, transferred: an upper bound survives any count-preserving
    rearrangement — which is exactly what a recursive sort hands back about the part it
    sorted. -/
def UbPermA : Term := prog{
  λ (p : Nat). λ (m : Nat). λ (a : Array m Nat). λ (q : Nat). λ (b : Array q Nat).
    λ (hc : Π (x : Nat) → Id Nat (CountA x m a) (CountA x q b)). λ (hb : UbA p q b).
      UbOfNoAboveA p m a (λ (x : Nat). λ (hx : Le (S p) x).
        IdTrans Nat (CountA x m a) (CountA x q b) Z (hc x)
          (NoAboveOfUbA p q b hb x hx)) }
def UbPermATy : Term := prog{
  Π (p : Nat) → Π (m : Nat) → Π (a : Array m Nat) → Π (q : Nat) → Π (b : Array q Nat) →
    (Π (x : Nat) → Id Nat (CountA x m a) (CountA x q b)) → UbA p q b → UbA p m a }

def NoBelowOfLbA : Term := prog{
  λ (p : Nat). λ (n : Nat). λ (a : Array n Nat).
    arrRec Nat (λ (m : Nat). λ (az : Array m Nat).
        LbA p m az → Π (x : Nat) → Le (S x) p → Id Nat (CountA x m az) Z)
      (λ (u : Unit). λ (x : Nat). λ (hx : Le (S x) p). Refl)
      (λ (k : Nat). λ (h : Nat). λ (t : Array k Nat).
        λ (ih : LbA p k t → Π (x : Nat) → Le (S x) p → Id Nat (CountA x k t) Z).
          λ (u : Σ (hh : Le p h) → LbA p k t). λ (x : Nat). λ (hx : Le (S x) p).
            IdTrans Nat (CountA x (S k) (acons k h t)) (CountA x k t) Z
              (CountAconsMiss x h k t
                (EqbLtFalse x h (LeTrans (S x) p h hx (LbHeadA p k h t u))))
              (ih (LbTailA p k h t u) x hx))
      n a }
def NoBelowOfLbATy : Term := prog{
  Π (p : Nat) → Π (n : Nat) → Π (a : Array n Nat) → LbA p n a →
    Π (x : Nat) → Le (S x) p → Id Nat (CountA x n a) Z }

def LbOfNoBelowA : Term := prog{
  λ (p : Nat). λ (n : Nat). λ (a : Array n Nat).
    arrRec Nat (λ (m : Nat). λ (az : Array m Nat).
        (Π (x : Nat) → Le (S x) p → Id Nat (CountA x m az) Z) → LbA p m az)
      (λ (hn : Π (x : Nat) → Le (S x) p → Id Nat (CountA x Z Arr()) Z). unit)
      (λ (k : Nat). λ (h : Nat). λ (t : Array k Nat).
        λ (ih : (Π (x : Nat) → Le (S x) p → Id Nat (CountA x k t) Z) → LbA p k t).
          λ (hn : Π (x : Nat) → Le (S x) p → Id Nat (CountA x (S k) (acons k h t)) Z).
            Pair(
              elim (Leb p h) return (λ (bv : Bool). Id Bool (Leb p h) bv → Le p h) {
                True => λ (e : Id Bool (Leb p h) True). LebTrueLe p h e,
                False => λ (e : Id Bool (Leb p h) False).
                  botElim (Le p h)
                    (Znots (CountA h k t)
                      (IdTrans Nat Z (CountA h (S k) (acons k h t)) (S (CountA h k t))
                        (IdSym Nat (CountA h (S k) (acons k h t)) Z (hn h (LebFalseGt p h e)))
                        (CountAconsHit h h k t (EqbRefl h))))
              } Refl,
              ih (λ (x : Nat). λ (hx : Le (S x) p).
                    elim (Eqb x h) return (λ (bv : Bool).
                        Id Bool (Eqb x h) bv → Id Nat (CountA x k t) Z) {
                      True => λ (eq : Id Bool (Eqb x h) True).
                        botElim (Id Nat (CountA x k t) Z)
                          (Znots (CountA x k t)
                            (IdTrans Nat Z (CountA x (S k) (acons k h t)) (S (CountA x k t))
                              (IdSym Nat (CountA x (S k) (acons k h t)) Z (hn x hx))
                              (CountAconsHit x h k t eq))),
                      False => λ (eq : Id Bool (Eqb x h) False).
                        IdTrans Nat (CountA x k t) (CountA x (S k) (acons k h t)) Z
                          (IdSym Nat (CountA x (S k) (acons k h t)) (CountA x k t)
                            (CountAconsMiss x h k t eq))
                          (hn x hx)
                    } Refl)))
      n a }
def LbOfNoBelowATy : Term := prog{
  Π (p : Nat) → Π (n : Nat) → Π (a : Array n Nat) →
    (Π (x : Nat) → Le (S x) p → Id Nat (CountA x n a) Z) → LbA p n a }

def LbPermA : Term := prog{
  λ (p : Nat). λ (m : Nat). λ (a : Array m Nat). λ (q : Nat). λ (b : Array q Nat).
    λ (hc : Π (x : Nat) → Id Nat (CountA x m a) (CountA x q b)). λ (hb : LbA p q b).
      LbOfNoBelowA p m a (λ (x : Nat). λ (hx : Le (S x) p).
        IdTrans Nat (CountA x m a) (CountA x q b) Z (hc x)
          (NoBelowOfLbA p q b hb x hx)) }
def LbPermATy : Term := prog{
  Π (p : Nat) → Π (m : Nat) → Π (a : Array m Nat) → Π (q : Nat) → Π (b : Array q Nat) →
    (Π (x : Nat) → Id Nat (CountA x m a) (CountA x q b)) → LbA p q b → LbA p m a }

/-- Two-element count commutation over arrays — `Cons2Comm`'s transfer at the fixed
    width the miniature sort needs. Double case split on `Eqb`, all four arms `Refl`;
    the `Eqb m a = False` arm needs no inner split because both sides already agree. -/
def CountSwap2 : Term := prog{
  λ (m : Nat). λ (a : Nat). λ (b : Nat).
    elim (Eqb m a) generalizing (Id Nat (CountA m 2 Arr(b, a)) (CountA m 2 Arr(a, b))) {
      True => elim (Eqb m b) generalizing
        (Id Nat (boolRec (λ (w : Bool). Nat) (S (S Z)) (S Z) (Eqb m b))
                (S (boolRec (λ (w : Bool). Nat) (S Z) Z (Eqb m b)))) {
        True => Refl, False => Refl },
      False => Refl } }
def CountSwap2Ty : Term := prog{
  Π (m : Nat) → Π (a : Nat) → Π (b : Nat) →
    Id Nat (CountA m 2 Arr(b, a)) (CountA m 2 Arr(a, b)) }

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
  λ (P : Nat → Type). λ (x : Nat). λ (y : Nat). λ (h : Id Nat x y). λ (px : P x).
    j Nat x (λ (y2 : Nat). λ (hh : Id Nat x y2). P y2) px y h }
def NatRwTy : Term := prog{
  Π (P : Nat → Type) → Π (x : Nat) → Π (y : Nat) → Id Nat x y → P x → P y }

/-- `Le n Z ⟹ n = Z`. The array quicksort tests emptiness with `Leb 1 n` rather than
    by matching `n`, because matching refines the length to `S m` and T2's rigid-extent
    restriction then blocks the three-way carve at the returned index. So the False
    branch holds `Le n Z` and has to turn it into the equation the nil lemmas want. -/
def LeZeroEq : Term := prog{
  λ (n : Nat). elim n return (λ (z : Nat). Le z Z → Id Nat z Z) {
    Z => λ (h : Le Z Z). Refl,
    S (n2) ih => λ (h : Bot). botElim (Id Nat (S n2) Z) h } }
def LeZeroEqTy : Term := prog{ Π (n : Nat) → Le n Z → Id Nat n Z }

/-- `SortedA` of an array whose LENGTH is zero.

    Not `unit`, and that is the point: there is no η at length zero. `SortedA Z σ` is a
    stuck `arrRec` — the recursor fires on `Arr`, never on the index — so an opaque
    length-zero payload does not compute to `Unit` and the sort's base case cannot be
    discharged by the trivial term. The induction is on the ARRAY with the equation
    carried, and the cons case is dead. -/
def SortedANil : Term := prog{
  λ (n : Nat). λ (a : Array n Nat).
    arrRec Nat (λ (m : Nat). λ (b : Array m Nat). Id Nat m Z → SortedA m b)
      (λ (h : Id Nat Z Z). unit)
      (λ (k : Nat). λ (hh : Nat). λ (t : Array k Nat).
        λ (ih : Id Nat k Z → SortedA k t).
          λ (h : Id Nat (S k) Z).
            botElim (SortedA (S k) (acons k hh t)) (Znots k (IdSym Nat (S k) Z h)))
      n a }
def SortedANilTy : Term := prog{
  Π (n : Nat) → Π (a : Array n Nat) → Id Nat n Z → SortedA n a }

/-- `SplitAL p k a` — the first `k` elements are ≤ `p`, the rest are ≥ `p`. -/
def SplitAL : Term := prog{
  λ (p : Nat). λ (k : Nat). λ (n : Nat). λ (a : Array n Nat).
    arrRec Nat (λ (m : Nat). λ (b : Array m Nat). Π (kz : Nat) → Type)
      (λ (kz : Nat). Unit)
      (λ (m : Nat). λ (h : Nat). λ (t : Array m Nat). λ (ih : Π (kz : Nat) → Type).
        λ (kz : Nat).
          elim kz return (λ (w : Nat). Type) {
            Z => Σ (hh : Le p h) → ih Z,
            S (k2) rec => Σ (hh : Le h p) → ih k2 })
      n a k }

/-- `PartA pv k a` — the first `k` elements are ≤ `pv`, element `k` IS `pv`, and the
    rest are ≥ `pv`. The pivot's presence at the split point is what the sort needs and
    `SplitAL` does not give: without it the element in the carved pivot slot is merely
    ≥ `p`, and `LbA (that element)` of the right half does not follow. -/
def PartA : Term := prog{
  λ (pv : Nat). λ (k : Nat). λ (n : Nat). λ (a : Array n Nat).
    arrRec Nat (λ (m : Nat). λ (b : Array m Nat). Π (kz : Nat) → Type)
      (λ (kz : Nat). Unit)
      (λ (m : Nat). λ (h : Nat). λ (t : Array m Nat). λ (ih : Π (kz : Nat) → Type).
        λ (kz : Nat).
          elim kz return (λ (w : Nat). Type) {
            Z => Σ (he : Id Nat h pv) → LbA pv m t,
            S (k2) rec => Σ (hh : Le h pv) → ih k2 })
      n a k }

/-- `SplitAL` of a length-zero array, at any skip count — `SortedANil`'s twin, and
    needed for the same reason. -/
def SplitANil : Term := prog{
  λ (p : Nat). λ (kz : Nat). λ (n : Nat). λ (a : Array n Nat). λ (hz : Id Nat n Z).
    arrRec Nat (λ (m : Nat). λ (b : Array m Nat).
        Π (k2 : Nat) → Id Nat m Z → SplitAL p k2 m b)
      (λ (k2 : Nat). λ (h : Id Nat Z Z). unit)
      (λ (m : Nat). λ (hh : Nat). λ (t : Array m Nat).
        λ (ih : Π (k2 : Nat) → Id Nat m Z → SplitAL p k2 m t).
          λ (k2 : Nat). λ (h : Id Nat (S m) Z).
            botElim (SplitAL p k2 (S m) (acons m hh t)) (Znots m (IdSym Nat (S m) Z h)))
      n a kz hz }
def SplitANilTy : Term := prog{
  Π (p : Nat) → Π (kz : Nat) → Π (n : Nat) → Π (a : Array n Nat) →
    Id Nat n Z → SplitAL p kz n a }

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
  λ (p : Nat). λ (n : Nat). λ (a : Array n Nat).
    arrRec Nat (λ (m : Nat). λ (b : Array m Nat). SplitAL p Z m b → LbA p m b)
      (λ (h : Unit). unit)
      (λ (k : Nat). λ (hh : Nat). λ (t : Array k Nat).
        λ (ih : SplitAL p Z k t → LbA p k t).
          λ (s : Σ (h2 : Le p hh) → SplitAL p Z k t).
            elim s return (λ (qz : Σ (h2 : Le p hh) → SplitAL p Z k t). LbA p (S k) (acons k hh t)) {
              Pair (u) (v) => Pair(u, ih v) })
      n a }
def SplitA0LbTy : Term := prog{
  Π (p : Nat) → Π (n : Nat) → Π (a : Array n Nat) → SplitAL p Z n a → LbA p n a }

/-- Split a `SplitAL` whose skip count runs ONE PAST the left part: the left part is
    wholly bounded, and what is left is a `SplitAL` at skip 1 over the right part. This
    is the shape the swap branch needs — it reads off both "the left part is all ≤ p"
    and "the element about to be swapped out is ≤ p" in one step. -/
def SplitACatE1 : Term := prog{
  λ (p : Nat). λ (k : Nat). λ (mm : Nat). λ (l : Array k Nat). λ (w : Array mm Nat).
    arrRec Nat (λ (kz : Nat). λ (lz : Array kz Nat).
        SplitAL p (S kz) (Add kz mm) (arrCat kz mm lz w) →
          Σ (hu : UbA p kz lz) → SplitAL p (S Z) mm w)
      (λ (h : SplitAL p (S Z) mm w). Pair(unit, h))
      (λ (k2 : Nat). λ (hh : Nat). λ (t : Array k2 Nat).
        λ (ih : SplitAL p (S k2) (Add k2 mm) (arrCat k2 mm t w) →
                  Σ (hu : UbA p k2 t) → SplitAL p (S Z) mm w).
          λ (s : Σ (h2 : Le hh p) → SplitAL p (S k2) (Add k2 mm) (arrCat k2 mm t w)).
            elim s return (λ (qz : Σ (h2 : Le hh p) →
                                SplitAL p (S k2) (Add k2 mm) (arrCat k2 mm t w)).
                Σ (hu : UbA p (S k2) (acons k2 hh t)) → SplitAL p (S Z) mm w) {
              Pair (u) (v) =>
                elim (ih v) return (λ (qz2 : Σ (hu : UbA p k2 t) → SplitAL p (S Z) mm w).
                    Σ (hu : UbA p (S k2) (acons k2 hh t)) → SplitAL p (S Z) mm w) {
                  Pair (a1) (b1) => Pair(Pair(u, a1), b1) } })
      k l }
def SplitACatE1Ty : Term := prog{
  Π (p : Nat) → Π (k : Nat) → Π (mm : Nat) → Π (l : Array k Nat) → Π (w : Array mm Nat) →
    SplitAL p (S k) (Add k mm) (arrCat k mm l w) →
      Σ (hu : UbA p k l) → SplitAL p (S Z) mm w }

/-- The converse at skip exactly `k`: a bounded left part in front of a `SplitAL` at
    skip zero is a `SplitAL` at skip `k`. -/
def SplitACatI0 : Term := prog{
  λ (p : Nat). λ (k : Nat). λ (mm : Nat). λ (l : Array k Nat). λ (w : Array mm Nat).
    arrRec Nat (λ (kz : Nat). λ (lz : Array kz Nat).
        UbA p kz lz → SplitAL p Z mm w → SplitAL p kz (Add kz mm) (arrCat kz mm lz w))
      (λ (u : Unit). λ (h : SplitAL p Z mm w). h)
      (λ (k2 : Nat). λ (hh : Nat). λ (t : Array k2 Nat).
        λ (ih : UbA p k2 t → SplitAL p Z mm w →
                  SplitAL p k2 (Add k2 mm) (arrCat k2 mm t w)).
          λ (u : Σ (h2 : Le hh p) → UbA p k2 t). λ (h : SplitAL p Z mm w).
            elim u return (λ (qz : Σ (h2 : Le hh p) → UbA p k2 t).
                SplitAL p (S k2) (Add (S k2) mm) (arrCat (S k2) mm (acons k2 hh t) w)) {
              Pair (a1) (b1) => Pair(a1, ih b1 h) })
      k l }
def SplitACatI0Ty : Term := prog{
  Π (p : Nat) → Π (k : Nat) → Π (mm : Nat) → Π (l : Array k Nat) → Π (w : Array mm Nat) →
    UbA p k l → SplitAL p Z mm w → SplitAL p k (Add k mm) (arrCat k mm l w) }

/-- `PartA`'s introduction, the partition's last step: a bounded left part in front of
    a `PartA` at skip zero (which is "the head IS the pivot, the tail is ≥ it"). -/
def PartACatI0 : Term := prog{
  λ (pv : Nat). λ (k : Nat). λ (mm : Nat). λ (l : Array k Nat). λ (w : Array mm Nat).
    arrRec Nat (λ (kz : Nat). λ (lz : Array kz Nat).
        UbA pv kz lz → PartA pv Z mm w → PartA pv kz (Add kz mm) (arrCat kz mm lz w))
      (λ (u : Unit). λ (h : PartA pv Z mm w). h)
      (λ (k2 : Nat). λ (hh : Nat). λ (t : Array k2 Nat).
        λ (ih : UbA pv k2 t → PartA pv Z mm w →
                  PartA pv k2 (Add k2 mm) (arrCat k2 mm t w)).
          λ (u : Σ (h2 : Le hh pv) → UbA pv k2 t). λ (h : PartA pv Z mm w).
            elim u return (λ (qz : Σ (h2 : Le hh pv) → UbA pv k2 t).
                PartA pv (S k2) (Add (S k2) mm) (arrCat (S k2) mm (acons k2 hh t) w)) {
              Pair (a1) (b1) => Pair(a1, ih b1 h) })
      k l }
def PartACatI0Ty : Term := prog{
  Π (pv : Nat) → Π (k : Nat) → Π (mm : Nat) → Π (l : Array k Nat) → Π (w : Array mm Nat) →
    UbA pv k l → PartA pv Z mm w → PartA pv k (Add k mm) (arrCat k mm l w) }

/-- **THE BRIDGE.** `PartA`'s elimination at the sort's own carve: the left segment is
    bounded above by the pivot, and what remains is `PartA` at skip zero over the pivot
    slot and the right segment — which unfolds, with no further lemma, to exactly
    `Id Nat (that element) pv` and `LbA pv (right segment)`. Those three facts are
    `SortedArrCat`'s four hypotheses minus the two the recursive calls supply. -/
def PartACatE0 : Term := prog{
  λ (pv : Nat). λ (k : Nat). λ (mm : Nat). λ (l : Array k Nat). λ (w : Array mm Nat).
    arrRec Nat (λ (kz : Nat). λ (lz : Array kz Nat).
        PartA pv kz (Add kz mm) (arrCat kz mm lz w) →
          Σ (hu : UbA pv kz lz) → PartA pv Z mm w)
      (λ (h : PartA pv Z mm w). Pair(unit, h))
      (λ (k2 : Nat). λ (hh : Nat). λ (t : Array k2 Nat).
        λ (ih : PartA pv k2 (Add k2 mm) (arrCat k2 mm t w) →
                  Σ (hu : UbA pv k2 t) → PartA pv Z mm w).
          λ (s : Σ (h2 : Le hh pv) → PartA pv k2 (Add k2 mm) (arrCat k2 mm t w)).
            elim s return (λ (qz : Σ (h2 : Le hh pv) →
                                PartA pv k2 (Add k2 mm) (arrCat k2 mm t w)).
                Σ (hu : UbA pv (S k2) (acons k2 hh t)) → PartA pv Z mm w) {
              Pair (u) (v) =>
                elim (ih v) return (λ (qz2 : Σ (hu : UbA pv k2 t) → PartA pv Z mm w).
                    Σ (hu : UbA pv (S k2) (acons k2 hh t)) → PartA pv Z mm w) {
                  Pair (a1) (b1) => Pair(Pair(u, a1), b1) } })
      k l }
def PartACatE0Ty : Term := prog{
  Π (pv : Nat) → Π (k : Nat) → Π (mm : Nat) → Π (l : Array k Nat) → Π (w : Array mm Nat) →
    PartA pv k (Add k mm) (arrCat k mm l w) →
      Σ (hu : UbA pv k l) → PartA pv Z mm w }

/-! ### The same crossings, one conclusion each

    A body cannot conveniently destructure a Σ — a `let`-bound pure value is not
    type-checked (§23's filed checker gap), so the alternative is an inline `elim` whose
    `return` motive is the function's whole return type written out again. Splitting each
    crossing into its two conclusions moves that cost into the pure layer, where writing
    the types is free, and keeps the programs readable. -/

def SplitACatUb : Term := prog{
  λ (p : Nat). λ (k : Nat). λ (mm : Nat). λ (l : Array k Nat). λ (w : Array mm Nat).
    λ (s : SplitAL p (S k) (Add k mm) (arrCat k mm l w)).
      elim (SplitACatE1 p k mm l w s)
        return (λ (qz : Σ (hu : UbA p k l) → SplitAL p (S Z) mm w). UbA p k l) {
          Pair (u) (v) => u } }
def SplitACatUbTy : Term := prog{
  Π (p : Nat) → Π (k : Nat) → Π (mm : Nat) → Π (l : Array k Nat) → Π (w : Array mm Nat) →
    SplitAL p (S k) (Add k mm) (arrCat k mm l w) → UbA p k l }

def SplitACatRest : Term := prog{
  λ (p : Nat). λ (k : Nat). λ (mm : Nat). λ (l : Array k Nat). λ (w : Array mm Nat).
    λ (s : SplitAL p (S k) (Add k mm) (arrCat k mm l w)).
      elim (SplitACatE1 p k mm l w s)
        return (λ (qz : Σ (hu : UbA p k l) → SplitAL p (S Z) mm w). SplitAL p (S Z) mm w) {
          Pair (u) (v) => v } }
def SplitACatRestTy : Term := prog{
  Π (p : Nat) → Π (k : Nat) → Π (mm : Nat) → Π (l : Array k Nat) → Π (w : Array mm Nat) →
    SplitAL p (S k) (Add k mm) (arrCat k mm l w) → SplitAL p (S Z) mm w }

/-- A skip-1 `SplitAL` over a cons: its head is bounded, and its tail is a skip-0 one.
    Both are definitional unfoldings; naming them keeps the swap branch flat. -/
def SplitA1Head : Term := prog{
  λ (p : Nat). λ (r : Nat). λ (g : Array r Nat). λ (yv : Nat).
    λ (s : Σ (hh : Le yv p) → SplitAL p Z r g).
      elim s return (λ (qz : Σ (hh : Le yv p) → SplitAL p Z r g). Le yv p) {
        Pair (u) (v) => u } }
def SplitA1HeadTy : Term := prog{
  Π (p : Nat) → Π (r : Nat) → Π (g : Array r Nat) → Π (yv : Nat) →
    SplitAL p (S Z) (S r) (acons r yv g) → Le yv p }

def SplitA1Tail : Term := prog{
  λ (p : Nat). λ (r : Nat). λ (g : Array r Nat). λ (yv : Nat).
    λ (s : Σ (hh : Le yv p) → SplitAL p Z r g).
      elim s return (λ (qz : Σ (hh : Le yv p) → SplitAL p Z r g). SplitAL p Z r g) {
        Pair (u) (v) => v } }
def SplitA1TailTy : Term := prog{
  Π (p : Nat) → Π (r : Nat) → Π (g : Array r Nat) → Π (yv : Nat) →
    SplitAL p (S Z) (S r) (acons r yv g) → SplitAL p Z r g }

def PartACatUb : Term := prog{
  λ (pv : Nat). λ (k : Nat). λ (mm : Nat). λ (l : Array k Nat). λ (w : Array mm Nat).
    λ (s : PartA pv k (Add k mm) (arrCat k mm l w)).
      elim (PartACatE0 pv k mm l w s)
        return (λ (qz : Σ (hu : UbA pv k l) → PartA pv Z mm w). UbA pv k l) {
          Pair (u) (v) => u } }
def PartACatUbTy : Term := prog{
  Π (pv : Nat) → Π (k : Nat) → Π (mm : Nat) → Π (l : Array k Nat) → Π (w : Array mm Nat) →
    PartA pv k (Add k mm) (arrCat k mm l w) → UbA pv k l }

def PartACatRest : Term := prog{
  λ (pv : Nat). λ (k : Nat). λ (mm : Nat). λ (l : Array k Nat). λ (w : Array mm Nat).
    λ (s : PartA pv k (Add k mm) (arrCat k mm l w)).
      elim (PartACatE0 pv k mm l w s)
        return (λ (qz : Σ (hu : UbA pv k l) → PartA pv Z mm w). PartA pv Z mm w) {
          Pair (u) (v) => v } }
def PartACatRestTy : Term := prog{
  Π (pv : Nat) → Π (k : Nat) → Π (mm : Nat) → Π (l : Array k Nat) → Π (w : Array mm Nat) →
    PartA pv k (Add k mm) (arrCat k mm l w) → PartA pv Z mm w }

/-- The pivot slot, read off a skip-0 `PartA`: the element there IS the pivot, and
    everything after it is bounded below by the pivot. These two are `SortedArrCat`'s
    remaining hypotheses, and the reason `PartA` records the pivot's identity at all. -/
def PartA0Eq : Term := prog{
  λ (pv : Nat). λ (jj : Nat). λ (g : Array jj Nat). λ (ev : Nat).
    λ (s : Σ (he : Id Nat ev pv) → LbA pv jj g).
      elim s return (λ (qz : Σ (he : Id Nat ev pv) → LbA pv jj g). Id Nat ev pv) {
        Pair (u) (v) => u } }
def PartA0EqTy : Term := prog{
  Π (pv : Nat) → Π (jj : Nat) → Π (g : Array jj Nat) → Π (ev : Nat) →
    PartA pv Z (S jj) (acons jj ev g) → Id Nat ev pv }

def PartA0Lb : Term := prog{
  λ (pv : Nat). λ (jj : Nat). λ (g : Array jj Nat). λ (ev : Nat).
    λ (s : Σ (he : Id Nat ev pv) → LbA pv jj g).
      elim s return (λ (qz : Σ (he : Id Nat ev pv) → LbA pv jj g). LbA pv jj g) {
        Pair (u) (v) => v } }
def PartA0LbTy : Term := prog{
  Π (pv : Nat) → Π (jj : Nat) → Π (g : Array jj Nat) → Π (ev : Nat) →
    PartA pv Z (S jj) (acons jj ev g) → LbA pv jj g }

/-! ### The count layer for a swap across a carve

    The partition's one mutating step exchanges the array's head with the element at
    the split point, and those two sit in DIFFERENT segments — the whole reason the
    swap is writable at all is that each is at index 0 of its own carve (¶6's "a
    segment with its own zero"). What the permutation conjunct then owes is that the
    exchange does not move any count, over a spine four levels deep. -/

/-- `CountA`'s own step function, named so a congruence can be stated over it: the
    count of a cons is a `bump` of the count of its tail. -/
def BumpN : Term := prog{
  λ (b : Bool). λ (c : Nat). elim b return (λ (w : Bool). Nat) { True => S c, False => c } }

/-- Congruence for `CountA` under a cons — `CountConsCongr`'s array counterpart. -/
def CountAconsCongr : Term := prog{
  λ (q : Nat). λ (h : Nat). λ (k : Nat). λ (t1 : Array k Nat). λ (t2 : Array k Nat).
    λ (hc : Id Nat (CountA q k t1) (CountA q k t2)).
      IdCongr Nat Nat (λ (c : Nat). BumpN (Eqb q h) c)
        (CountA q k t1) (CountA q k t2) hc }
def CountAconsCongrTy : Term := prog{
  Π (q : Nat) → Π (h : Nat) → Π (k : Nat) → Π (t1 : Array k Nat) → Π (t2 : Array k Nat) →
    Id Nat (CountA q k t1) (CountA q k t2) →
      Id Nat (CountA q (S k) (acons k h t1)) (CountA q (S k) (acons k h t2)) }

/-- The arithmetic core of the swap, over the two `bump`s alone: which of the two
    exchanged elements is being counted does not matter. Four arms; the two mixed ones
    are `AddSucc` and its symmetry, and the two matching ones are `Refl` — `CountSwap2`
    at width two had all four `Refl` because both counts were concrete. -/
def BumpComm : Term := prog{
  λ (b1 : Bool). λ (b2 : Bool). λ (cl : Nat). λ (cg : Nat).
    elim b1 return (λ (w : Bool).
        Id Nat (BumpN b2 (Add cl (BumpN w cg))) (BumpN w (Add cl (BumpN b2 cg)))) {
      True =>
        elim b2 return (λ (w2 : Bool).
            Id Nat (BumpN w2 (Add cl (S cg))) (S (Add cl (BumpN w2 cg)))) {
          True => Refl,
          False => AddSucc cl cg },
      False =>
        elim b2 return (λ (w2 : Bool).
            Id Nat (BumpN w2 (Add cl cg)) (Add cl (BumpN w2 cg))) {
          True => IdSym Nat (Add cl (S cg)) (S (Add cl cg)) (AddSucc cl cg),
          False => Refl } } }
def BumpCommTy : Term := prog{
  Π (b1 : Bool) → Π (b2 : Bool) → Π (cl : Nat) → Π (cg : Nat) →
    Id Nat (BumpN b2 (Add cl (BumpN b1 cg))) (BumpN b1 (Add cl (BumpN b2 cg))) }

/-- **The swap preserves every count**, stated over exactly the spine the partition
    produces: head, left segment, the swapped cell, right segment. Two `CountArrCat`
    rewrites bracket `BumpComm`. -/
def CountSwapA : Term := prog{
  λ (q : Nat). λ (x : Nat). λ (y : Nat). λ (k : Nat). λ (l : Array k Nat).
  λ (r : Nat). λ (g : Array r Nat).
    IdTrans Nat
      (CountA q (S (Add k (S r))) (acons (Add k (S r)) y (arrCat k (S r) l (acons r x g))))
      (BumpN (Eqb q y) (Add (CountA q k l) (BumpN (Eqb q x) (CountA q r g))))
      (CountA q (S (Add k (S r))) (acons (Add k (S r)) x (arrCat k (S r) l (acons r y g))))
      (IdCongr Nat Nat (λ (c : Nat). BumpN (Eqb q y) c)
         (CountA q (Add k (S r)) (arrCat k (S r) l (acons r x g)))
         (Add (CountA q k l) (CountA q (S r) (acons r x g)))
         (CountArrCat q k l (S r) (acons r x g)))
      (IdTrans Nat
        (BumpN (Eqb q y) (Add (CountA q k l) (BumpN (Eqb q x) (CountA q r g))))
        (BumpN (Eqb q x) (Add (CountA q k l) (BumpN (Eqb q y) (CountA q r g))))
        (CountA q (S (Add k (S r))) (acons (Add k (S r)) x (arrCat k (S r) l (acons r y g))))
        (BumpComm (Eqb q x) (Eqb q y) (CountA q k l) (CountA q r g))
        (IdSym Nat
          (CountA q (S (Add k (S r))) (acons (Add k (S r)) x (arrCat k (S r) l (acons r y g))))
          (BumpN (Eqb q x) (Add (CountA q k l) (BumpN (Eqb q y) (CountA q r g))))
          (IdCongr Nat Nat (λ (c : Nat). BumpN (Eqb q x) c)
             (CountA q (Add k (S r)) (arrCat k (S r) l (acons r y g)))
             (Add (CountA q k l) (CountA q (S r) (acons r y g)))
             (CountArrCat q k l (S r) (acons r y g))))) }
def CountSwapATy : Term := prog{
  Π (q : Nat) → Π (x : Nat) → Π (y : Nat) → Π (k : Nat) → Π (l : Array k Nat) →
  Π (r : Nat) → Π (g : Array r Nat) →
    Id Nat (CountA q (S (Add k (S r))) (acons (Add k (S r)) y (arrCat k (S r) l (acons r x g))))
           (CountA q (S (Add k (S r))) (acons (Add k (S r)) x (arrCat k (S r) l (acons r y g)))) }

end Dllbc.StdLemmas

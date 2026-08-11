import Dllbc.Std
import Dllbc.ProgMacro

/-!
# `Dllbc.StdLemmas` — the pure lemmas, authored in the §15 surface syntax

The M11 wall — `le_trans` as a raw de Bruijn term across ~15 binder contexts,
each mis-index failing silently — collapsed by names and explicit motives. Every
lemma here is written in `prog{ … }`: binders are named, motives are written once
and visible, and elaboration resolves names or errors (no silent fallback). The
kernel terms they elaborate to are the same de Bruijn `Term`s hasType already
checks; the surface is authoring sugar only.

`Le`/`count` are the surface names for the library functions (Term-valued, so a
`prog{ }` application `Le a b` is an ordinary app spine).
-/

namespace Dllbc.StdLemmas
open Dllbc

/-- Surface name for the order type (a `Term`, so `Le a b` is an application). -/
abbrev Le : Term := Std.LeFnT
/-- Surface name for the multiset counter. -/
abbrev count : Term := Std.countFnT
abbrev add : Term := Std.addFnT
abbrev append : Term := Std.appendFnT
abbrev eqb : Term := Std.eqbFnT
abbrev take : Term := Std.takeFnT
abbrev drop : Term := Std.dropFnT
abbrev leb : Term := Std.lebFnT

/-! ## `le_refl`, `le_trans` — the acceptance test -/

def le_refl : Term := prog{
  λ (n : Nat). elim n return (λ (m : Nat). Le m m) {
    Z => unit,
    S (k) ih => ih } }
def le_refl_ty : Term := prog{ Π (n : Nat) → Le n n }

-- The wall. Single outer elim on `a`; the `S` case elims on `b`, whose `S` case
-- elims on `c`, with the IH applied at the peeled proofs — every step
-- definitional through the `Le` equations. Nested, but every binder is NAMED and
-- every motive is written once and visible.
def le_trans : Term := prog{
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
def le_trans_ty : Term := prog{
  Π (a : Nat) → Π (b : Nat) → Π (c : Nat) → Le a b → Le b c → Le a c }

-- Right-successor monotonicity: `a ≤ b ⟹ a ≤ S b`. Double induction (on `a`,
-- casing `b`): the `Z` head is trivial (`Le Z _ = ⊤`); the `S a'` head cases `b`
-- (`Le (S a') Z = ⊥`, else `Le a' b'` and the IH lifts it to `Le a' (S b')`).
-- The glue `count_swapL'` needs to bend swapS's `Le (S i) j` into count_swapL's
-- `Le (S i) (len l)` via one `le_trans`.
def le_up_r : Term := prog{
  λ (a : Nat). elim a return (λ (az : Nat). Π (b : Nat) → Le az b → Le az (S b)) {
    Z => λ (b : Nat). λ (h : Le Z b). unit,
    S (a') ih => λ (b : Nat). λ (h : Le (S a') b).
      elim b return (λ (bz : Nat). Le (S a') bz → Le (S a') (S bz)) {
        Z => λ (h0 : Le (S a') Z). botElim (Le (S a') (S Z)) h0,
        S (b') ihb => λ (h0 : Le (S a') (S b')). ih b' h0
      } h } }
def le_up_r_ty : Term := prog{ Π (a : Nat) → Π (b : Nat) → Le a b → Le a (S b) }

-- `i ≤ i + g`: the boundary never passes the scan position it feeds. A clean
-- induction on `i` (`add (S i') g = S (add i' g)`, so `Le (S i') (add (S i') g)`
-- reduces to the IH). The partition swaps consume this as their `pij`.
def le_add : Term := prog{
  λ (i : Nat). elim i return (λ (iz : Nat). Π (g : Nat) → Le iz (Add iz g)) {
    Z => λ (g : Nat). unit,
    S (i') ih => λ (g : Nat). ih g } }
def le_add_ty : Term := prog{ Π (i : Nat) → Π (g : Nat) → Le i (Add i g) }

-- `b ≤ a + b` — the companion where the summand is on the LEFT (`le_add` has it on
-- the right). Induction on `a`: base is `le_refl` (`add Z b = b`), step lifts the
-- IH with `le_up_r` (`add (S a') b = S (add a' b)`). The scan-position bound uses
-- this because the length equation carries the remaining count `k` on the left.
def le_add_l : Term := prog{
  λ (b : Nat). λ (a : Nat).
    elim a return (λ (az : Nat). Le b (Add az b)) {
      Z => le_refl b,
      S (a') ih => le_up_r b (Add a' b) ih } }
def le_add_l_ty : Term := prog{ Π (b : Nat) → Π (a : Nat) → Le b (Add a b) }

-- `S i ≤ i + (S g)` — the swap's `pij`: the boundary `S i` is below the scan
-- position `S (add i (S g))` whenever the gap is non-empty. Induction on `i`
-- avoids an add_succ transport (`add (S i') x = S (add i' x)` is definitional),
-- so no rewrite is needed here.
def le_add_succ : Term := prog{
  λ (i : Nat). elim i return (λ (iz : Nat). Π (g : Nat) → Le (S iz) (Add iz (S g))) {
    Z => λ (g : Nat). unit,
    S (i') ih => λ (g : Nat). ih g } }
def le_add_succ_ty : Term := prog{ Π (i : Nat) → Π (g : Nat) → Le (S i) (Add i (S g)) }

-- Transport a `Le` along an `Id` on its SECOND argument: `x = y ⟹ Le a x → Le a
-- y`. The bounds derived over the arithmetic normal form are moved onto `len *v`
-- (and back through `len_swapL`) with this J-transport — the "le_trans/le_step
-- glue where descent is not definitional".
def le_rw_r : Term := prog{
  λ (a : Nat). λ (x : Nat). λ (y : Nat). λ (h : Id Nat x y). λ (p : Le a x).
    j Nat x (λ (y' : Nat). λ (hh : Id Nat x y'). Le a y') p y h }
def le_rw_r_ty : Term := prog{ Π (a : Nat) → Π (x : Nat) → Π (y : Nat) → Id Nat x y → Le a x → Le a y }

-- Transport a `Le` along an `Id` on its FIRST (smaller) argument: `x = y ⟹ Le x
-- b → Le y b`. The range partition's bound `Le (add lo (S (add k (add i g))))
-- (len *v)` is invariant across the recursion (the sum k+i+g is preserved), but
-- its SYNTACTIC form shifts as k descends and i/g grow; this moves the bound
-- between forms via the hshift identities — the Le mirror of le_rw_r, and the one
-- lemma the M20 Id-toolkit lacked for the subrange generalization (§21).
def le_rw_l : Term := prog{
  λ (b : Nat). λ (x : Nat). λ (y : Nat). λ (h : Id Nat x y). λ (p : Le x b).
    j Nat x (λ (y' : Nat). λ (hh : Id Nat x y'). Le y' b) p y h }
def le_rw_l_ty : Term := prog{ Π (b : Nat) → Π (x : Nat) → Π (y : Nat) → Id Nat x y → Le x b → Le y b }

-- Left-add monotonicity: `a ≤ b ⟹ lo + a ≤ lo + b`. Induction on `lo`: base is
-- the hypothesis (`add Z x = x`), step is the IH verbatim (`add (S lo') x =
-- S (add lo' x)` and `Le (S _) (S _) = Le _ _` are both definitional). The range
-- partition's swap bounds shift the entry bound `Le (S i) (S (add i g))` through
-- `add lo` to reach `Le (add lo (S i)) (add lo (S (add i g)))` (§21).
def le_add_mono_l : Term := prog{
  λ (lo : Nat). λ (a : Nat). λ (b : Nat). λ (h : Le a b).
    elim lo return (λ (loz : Nat). Le (Add loz a) (Add loz b)) {
      Z => h,
      S (lo') ih => ih } }
def le_add_mono_l_ty : Term := prog{ Π (lo : Nat) → Π (a : Nat) → Π (b : Nat) → Le a b → Le (Add lo a) (Add lo b) }

/-! ## `id_trans`, `id_congr` — the J warm-ups partition's count-chaining consumes -/

def id_trans : Term := prog{
  λ (A : Type). λ (x : A). λ (y : A). λ (z : A). λ (p : Id A x y). λ (q : Id A y z).
    j A x (λ (y' : A). λ (h : Id A x y'). Id A y' z → Id A x z) (λ (h : Id A x z). h) y p q }
def id_trans_ty : Term := prog{
  Π (A : Type) → Π (x : A) → Π (y : A) → Π (z : A) → Id A x y → Id A y z → Id A x z }

def id_congr : Term := prog{
  λ (A : Type). λ (B : Type). λ (f : A → B). λ (x : A). λ (y : A). λ (p : Id A x y).
    j A x (λ (y' : A). λ (h : Id A x y'). Id B (f x) (f y')) Refl y p }
def id_congr_ty : Term := prog{
  Π (A : Type) → Π (B : Type) → Π (f : A → B) → Π (x : A) → Π (y : A) → Id A x y → Id B (f x) (f y) }

def id_sym : Term := prog{
  λ (A : Type). λ (x : A). λ (y : A). λ (p : Id A x y).
    j A x (λ (y' : A). λ (h : Id A x y'). Id A y' x) Refl y p }
def id_sym_ty : Term := prog{ Π (A : Type) → Π (x : A) → Π (y : A) → Id A x y → Id A y x }

/-! ## Arithmetic — the first double-inductions after the wall (§16 calibration) -/

def add_zero : Term := prog{
  λ (a : Nat). elim a return (λ (x : Nat). Id Nat (Add x Z) x) {
    Z => Refl,
    S (a') ih => id_congr Nat Nat (λ (n : Nat). S n) (Add a' Z) a' ih } }
def add_zero_ty : Term := prog{ Π (a : Nat) → Id Nat (Add a Z) a }

def add_succ : Term := prog{
  λ (a : Nat). λ (b : Nat). elim a return (λ (x : Nat). Id Nat (Add x (S b)) (S (Add x b))) {
    Z => Refl,
    S (a') ih => id_congr Nat Nat (λ (n : Nat). S n) (Add a' (S b)) (S (Add a' b)) ih } }
def add_succ_ty : Term := prog{ Π (a : Nat) → Π (b : Nat) → Id Nat (Add a (S b)) (S (Add a b)) }

-- Commutativity: the classic proof, authored in the surface and checked first try.
def add_comm : Term := prog{
  λ (a : Nat). elim a return (λ (x : Nat). Π (b : Nat) → Id Nat (Add x b) (Add b x)) {
    Z => λ (b : Nat). id_sym Nat (Add b Z) b (add_zero b),
    S (a') ih => λ (b : Nat).
      id_trans Nat (S (Add a' b)) (S (Add b a')) (Add b (S a'))
        (id_congr Nat Nat (λ (n : Nat). S n) (Add a' b) (Add b a') (ih b))
        (id_sym Nat (Add b (S a')) (S (Add b a')) (add_succ b a')) } }
def add_comm_ty : Term := prog{ Π (a : Nat) → Π (b : Nat) → Id Nat (Add a b) (Add b a) }

def add_assoc : Term := prog{
  λ (a : Nat). elim a return (λ (x : Nat). Π (b : Nat) → Π (c : Nat) → Id Nat (Add (Add x b) c) (Add x (Add b c))) {
    Z => λ (b : Nat). λ (c : Nat). Refl,
    S (a') ih => λ (b : Nat). λ (c : Nat).
      id_congr Nat Nat (λ (n : Nat). S n) (Add (Add a' b) c) (Add a' (Add b c)) (ih b c) } }
def add_assoc_ty : Term := prog{ Π (a : Nat) → Π (b : Nat) → Π (c : Nat) → Id Nat (Add (Add a b) c) (Add a (Add b c)) }

/-! ## The length-equation shift lemmas — `hlen` updates for the recursive partScan

    The recursion's loop invariant is `len *v = S (add k (add i g))`, and `k+i+g`
    is constant across every step (each moves one successor between the `k`, `i`,
    `g` slots). So each recursive `hlen` update is an arithmetic-identity transport
    of the same total, provable by `add_succ` (the only non-definitional step, since
    Std `add` recurses on its first argument). Two shapes cover all three cases:
    boundary advance (True-Z, True-S g') and gap growth (False). -/

-- Boundary advance: `add (S k) (add i g) = add k (add (S i) g)` (move a successor
-- from k to i). `add (S i) g = S (add i g)` is definitional, so only the `add k
-- (S ·)` step needs add_succ.
def hshift_true : Term := prog{
  λ (k : Nat). λ (i : Nat). λ (g : Nat).
    id_sym Nat (Add k (S (Add i g))) (S (Add k (Add i g))) (add_succ k (Add i g)) }
def hshift_true_ty : Term := prog{ Π (k : Nat) → Π (i : Nat) → Π (g : Nat) →
  Id Nat (Add (S k) (Add i g)) (Add k (Add (S i) g)) }

-- Gap growth: `add (S k) (add i g) = add k (add i (S g))` (move a successor from k
-- to g). `add i (S g)` is stuck (add recurses on i), so this needs add_succ TWICE
-- — once under `add k` to grow the gap, once to pull the successor out front.
def hshift_false : Term := prog{
  λ (k : Nat). λ (i : Nat). λ (g : Nat).
    id_sym Nat (Add k (Add i (S g))) (S (Add k (Add i g)))
      (id_trans Nat (Add k (Add i (S g))) (Add k (S (Add i g))) (S (Add k (Add i g)))
        (id_congr Nat Nat (λ (x : Nat). Add k x) (Add i (S g)) (S (Add i g)) (add_succ i g))
        (add_succ k (Add i g))) }
def hshift_false_ty : Term := prog{ Π (k : Nat) → Π (i : Nat) → Π (g : Nat) →
  Id Nat (Add (S k) (Add i g)) (Add k (Add i (S g))) }

-- `count`'s Cons-unfolding equation as an Id — definitional, a `Refl` after whnf.
def count_cons : Term := prog{ λ (m : Nat). λ (h : Nat). λ (t : List Nat). Refl }
def count_cons_ty : Term := prog{
  Π (m : Nat) → Π (h : Nat) → Π (t : List Nat) →
    Id Nat (Count m (Cons h t)) (boolRec (λ (b : Bool). Nat) (S (Count m t)) (Count m t) (Eqb m h)) }

/-! ## The `count`/`append`/`take`/`drop` lemmas (§16-2)

    `count_append` — count distributes over `append` — needs a dependent Bool-elim
    on `eqb m h` in the `Cons` case (the motive abstracts the `boolRec` that
    `count (Cons …)` unfolds to). `take_drop_id` reassembles a list from its
    prefix and suffix. Both are the building blocks the swap-count lemma consumes. -/

def count_append : Term := prog{
  λ (m : Nat). λ (a : List Nat). λ (b : List Nat).
    elim a return (λ (x : List Nat). Id Nat (Count m (append x b)) (Add (Count m x) (Count m b))) {
      Nil => Refl,
      Cons (h) (t) ih =>
        elim (Eqb m h) return (λ (bv : Bool).
          Id Nat (boolRec (λ (w : Bool). Nat) (S (Count m (append t b))) (Count m (append t b)) bv)
                 (Add (boolRec (λ (w : Bool). Nat) (S (Count m t)) (Count m t) bv) (Count m b))) {
          True => id_congr Nat Nat (λ (n : Nat). S n) (Count m (append t b)) (Add (Count m t) (Count m b)) ih,
          False => ih
        }
    } }
def count_append_ty : Term := prog{
  Π (m : Nat) → Π (a : List Nat) → Π (b : List Nat) →
    Id Nat (Count m (append a b)) (Add (Count m a) (Count m b)) }

def take_drop_id : Term := prog{
  λ (i : Nat). elim i return (λ (k : Nat). Π (l : List Nat) → Id (List Nat) (append (Take k l) (Drop k l)) l) {
    Z => λ (l : List Nat). Refl,
    S (i') ih => λ (l : List Nat).
      elim l return (λ (x : List Nat). Id (List Nat) (append (Take (S i') x) (Drop (S i') x)) x) {
        Nil => Refl,
        Cons (h) (t) ihl =>
          id_congr (List Nat) (List Nat) (λ (r : List Nat). Cons h r)
            (append (Take i' t) (Drop i' t)) t (ih t)
      } } }
def take_drop_id_ty : Term := prog{
  Π (i : Nat) → Π (l : List Nat) → Id (List Nat) (append (Take i l) (Drop i l)) l }

/-! ## `nth`, `set`, `swapL` — the pure specification of swap (§16-2)

    Authored in the surface (dogfooding §15 — a first raw-de-Bruijn `set` had a
    `pvar 4`-vs-`pvar 3` slip; the surface version cannot slip). `swapL` mirrors
    the cursor walk: recurse past the prefix, then at `i = 0` exchange the head
    with position `j` of the tail (`Cons (nth j' xs) (set j' x xs)`). Reduces:
    `swapL 0 2 [1,2,3] = [3,2,1]`. `count_swapL` is the pending node — see the
    milestone report: it requires a BOUND (`swapL` off the end defaults `nth` to
    `Z`, breaking count preservation), so it decomposes into a bounded stack. -/

def nth : Term := prog{
  λ (k : Nat). elim k return (λ (z : Nat). List Nat → Nat) {
    Z => λ (l : List Nat). elim l return (λ (z : List Nat). Nat) { Nil => Z, Cons (h) (t) ihl => h },
    S (k') rec => λ (l : List Nat). elim l return (λ (z : List Nat). Nat) { Nil => Z, Cons (h) (t) ihl => rec t } } }

def set : Term := prog{
  λ (k : Nat). λ (v : Nat). elim k return (λ (z : Nat). List Nat → List Nat) {
    Z => λ (l : List Nat). elim l return (λ (z : List Nat). List Nat) { Nil => Nil, Cons (h) (t) ihl => Cons v t },
    S (k') rec => λ (l : List Nat). elim l return (λ (z : List Nat). List Nat) { Nil => Nil, Cons (h) (t) ihl => Cons h (rec t) } } }

def swapL : Term := prog{
  λ (i : Nat). elim i return (λ (z : Nat). Nat → List Nat → List Nat) {
    Z => λ (j : Nat). λ (l : List Nat). elim l return (λ (z : List Nat). List Nat) {
      Nil => Nil,
      Cons (x) (xs) ihl => elim j return (λ (z : Nat). List Nat) {
        Z => Cons x xs,
        S (j') jih => Cons (nth j' xs) (set j' x xs) } },
    S (i') reci => λ (j : Nat). λ (l : List Nat). elim l return (λ (z : List Nat). List Nat) {
      Nil => Nil,
      Cons (x) (xs) ihl => elim j return (λ (z : Nat). List Nat) {
        Z => Cons x xs,
        S (j') jih => Cons x (reci j' xs) } } } }

/-! ## Length preservation — the spec `swapS` carries (§16, len variant)

    `len_set`/`len_swapL` hold UNCONDITIONALLY — no bounds — because `set`
    preserves length even off the end (it replaces or no-ops, never resizes) and
    `swapL` only ever rebuilds the same spine. Unlike count, length needs no
    `eqb`, so these are clean surface inductions (no rewriting layer required). -/

abbrev len : Term := Std.lenFnT

def len_set : Term := prog{
  λ (k : Nat). λ (v : Nat).
    elim k return (λ (z : Nat). Π (l : List Nat) → Id Nat (Len (set z v l)) (Len l)) {
      Z => λ (l : List Nat). elim l return (λ (x : List Nat). Id Nat (Len (set Z v x)) (Len x)) {
        Nil => Refl, Cons (h) (t) ihl => Refl },
      S (k') ih => λ (l : List Nat). elim l return (λ (x : List Nat). Id Nat (Len (set (S k') v x)) (Len x)) {
        Nil => Refl,
        Cons (h) (t) ihl => id_congr Nat Nat (λ (n : Nat). S n) (Len (set k' v t)) (Len t) (ih t) } } }
def len_set_ty : Term := prog{ Π (k : Nat) → Π (v : Nat) → Π (l : List Nat) → Id Nat (Len (set k v l)) (Len l) }

def len_swapL : Term := prog{
  λ (i : Nat).
    elim i return (λ (z : Nat). Π (j : Nat) → Π (l : List Nat) → Id Nat (Len (swapL z j l)) (Len l)) {
      Z => λ (j : Nat). λ (l : List Nat).
        elim l return (λ (x : List Nat). Id Nat (Len (swapL Z j x)) (Len x)) {
          Nil => Refl,
          Cons (y) (ys) ihl => elim j return (λ (w : Nat). Id Nat (Len (swapL Z w (Cons y ys))) (Len (Cons y ys))) {
            Z => Refl,
            S (j') jih => id_congr Nat Nat (λ (n : Nat). S n) (Len (set j' y ys)) (Len ys) (len_set j' y ys) } },
      S (i') ih => λ (j : Nat). λ (l : List Nat).
        elim l return (λ (x : List Nat). Id Nat (Len (swapL (S i') j x)) (Len x)) {
          Nil => Refl,
          Cons (y) (ys) ihl => elim j return (λ (w : Nat). Id Nat (Len (swapL (S i') w (Cons y ys))) (Len (Cons y ys))) {
            Z => Refl,
            S (j') jih => id_congr Nat Nat (λ (n : Nat). S n) (Len (swapL i' j' ys)) (Len ys) (ih j' ys) } } } }
def len_swapL_ty : Term := prog{ Π (i : Nat) → Π (j : Nat) → Π (l : List Nat) → Id Nat (Len (swapL i j l)) (Len l) }

/-! ## The bounded `count_swapL` stack (§18)

    `count_swapL` — `swapL i j` preserves the multiset — is FALSE unbounded (off
    the end `nth` defaults to `Z` and `set` no-ops, so the head becomes `Z ≠ x`).
    With `Le (S i) (len l)` and `Le (S j) (len l)` the indices are in range and the
    swap is a genuine permutation. The proof decomposes into a small stack, each
    node an ordinary Id-algebra fact composed by `id_trans`/`id_congr`:

    - `cons2_comm` — count is invariant under swapping two ADJACENT heads. Proven
      by the §18 nested `generalizing` casing (the report card; the named copy the
      stack consumes). The base case of the head-swap.
    - `count_cons_congr` — `count m l₁ = count m l₂ ⟹ count m (Cons h l₁) =
      count m (Cons h l₂)`. One `id_congr` whose `f` abstracts `count m ·` out of
      the `boolRec` that `count (Cons …)` unfolds to (both occurrences at once).
    - `count_headswap` — bounded: swapping the head `x` with position `j` of the
      tail preserves count. The meaty double-induction (on `j`, casing `xs`); its
      step is a three-link `id_trans` chain `cons2_comm ∘ (count_cons_congr on IH)
      ∘ cons2_comm`, its `Nil` leaves ⊥-discharged by the range bound.
    - `count_swapL` — bounded: the top statement, by induction on `i` with `j`/`l`
      casing. Head case delegates to `count_headswap`; recursive case is
      `count_cons_congr` on the IH; the degenerate `j = Z` / `i > j` cases are the
      identity, so `Refl`.

    No J-transport (rewrite-by-Id) is needed here: the decomposition localises ALL
    `eqb`/knowledge reasoning inside `cons2_comm` (via `generalizing`) and
    `count_cons_congr` (via `id_congr` on the `boolRec`), leaving the head-swap and
    `swapL` levels as pure `id_trans` chains. rewrite-by-Id (S18) remains the tool
    for a subterm STUCK behind an abstract scrutinee, which this stack avoids by
    construction. -/

def cons2_comm : Term := prog{
  λ (m : Nat). λ (a : Nat). λ (b : Nat). λ (l : List Nat).
    elim (Eqb m a) generalizing (Id Nat (Count m (Cons a (Cons b l))) (Count m (Cons b (Cons a l)))) {
      True => elim (Eqb m b) generalizing
        (Id Nat (S (Count m (Cons b l)))
                (boolRec (λ (w : Bool). Nat) (S (S (Count m l))) (S (Count m l)) (Eqb m b))) {
        True => Refl, False => Refl },
      False => Refl } }
def cons2_comm_ty : Term := prog{
  Π (m : Nat) → Π (a : Nat) → Π (b : Nat) → Π (l : List Nat) →
    Id Nat (Count m (Cons a (Cons b l))) (Count m (Cons b (Cons a l))) }

-- Congruence of `count` under `Cons`: the `f` abstracts `count m ·` out of BOTH
-- occurrences in the `boolRec` that `count m (Cons h ·)` whnf's to, so a single
-- `id_congr` transports the tail equation through the head.
def count_cons_congr : Term := prog{
  λ (m : Nat). λ (h : Nat). λ (l1 : List Nat). λ (l2 : List Nat). λ (p : Id Nat (Count m l1) (Count m l2)).
    id_congr Nat Nat (λ (r : Nat). boolRec (λ (w : Bool). Nat) (S r) r (Eqb m h)) (Count m l1) (Count m l2) p }
def count_cons_congr_ty : Term := prog{
  Π (m : Nat) → Π (h : Nat) → Π (l1 : List Nat) → Π (l2 : List Nat) →
    Id Nat (Count m l1) (Count m l2) → Id Nat (Count m (Cons h l1)) (Count m (Cons h l2)) }

-- The §18 rewrite-by-Id lemma, named: from a RECEIVED equation `eqb m a = True`,
-- resolve the STUCK `count m (Cons a l)` to `S (count m l)`. J transports `Refl`
-- along `id_sym hq`, the motive abstracting the scrutinee `z` out of the `boolRec`
-- that `count (Cons …)` unfolds to. Abstraction alone cannot do this (the subterm
-- hides behind the scrutinee's own reduction); this is the knowledge half. The
-- imperative tie-in returns THIS applied to its params.
def count_cons_hit : Term := prog{
  λ (m : Nat). λ (a : Nat). λ (l : List Nat). λ (hq : Id Bool (Eqb m a) True).
    j Bool True
      (λ (z : Bool). λ (h : Id Bool True z).
        Id Nat (boolRec (λ (w : Bool). Nat) (S (Count m l)) (Count m l) z) (S (Count m l)))
      Refl (Eqb m a) (id_sym Bool (Eqb m a) True hq) }
def count_cons_hit_ty : Term := prog{
  Π (m : Nat) → Π (a : Nat) → Π (l : List Nat) → Id Bool (Eqb m a) True →
    Id Nat (Count m (Cons a l)) (S (Count m l)) }

-- Bounded head-swap: exchanging the head `x` with position `j` of the tail `xs`
-- preserves count, PROVIDED `j` is in range (`Le (S j) (len xs)`). Induction on
-- `j`, casing `xs`; the `Nil` leaves are ⊥-discharged by the bound (`Le (S _) Z`).
-- Base (`j = Z`): the swap is `Cons y (Cons x ys) ↔ Cons x (Cons y ys)`, exactly
-- `cons2_comm`. Step (`j = S j'`): a three-link `id_trans` chain — float the
-- swapped-in element past the head with `cons2_comm`, apply the IH under the head
-- via `count_cons_congr`, then `cons2_comm` back.
def count_headswap : Term := prog{
  λ (m : Nat). λ (x : Nat). λ (j : Nat).
    elim j return (λ (jz : Nat).
        Π (xs : List Nat) → Le (S jz) (Len xs) →
          Id Nat (Count m (Cons (nth jz xs) (set jz x xs))) (Count m (Cons x xs))) {
      Z => λ (xs : List Nat).
        elim xs return (λ (xz : List Nat).
            Le (S Z) (Len xz) →
              Id Nat (Count m (Cons (nth Z xz) (set Z x xz))) (Count m (Cons x xz))) {
          Nil => λ (bnd0 : Le (S Z) (Len Nil)).
            botElim (Id Nat (Count m (Cons (nth Z Nil) (set Z x Nil))) (Count m (Cons x Nil))) bnd0,
          Cons (y) (ys) ihx => λ (bnd0 : Le (S Z) (Len (Cons y ys))).
            cons2_comm m y x ys },
      S (j') ih => λ (xs : List Nat).
        elim xs return (λ (xz : List Nat).
            Le (S (S j')) (Len xz) →
              Id Nat (Count m (Cons (nth (S j') xz) (set (S j') x xz))) (Count m (Cons x xz))) {
          Nil => λ (bnd0 : Le (S (S j')) (Len Nil)).
            botElim (Id Nat (Count m (Cons (nth (S j') Nil) (set (S j') x Nil))) (Count m (Cons x Nil))) bnd0,
          Cons (y) (ys) ihx => λ (bnd0 : Le (S (S j')) (Len (Cons y ys))).
            id_trans Nat
              (Count m (Cons (nth j' ys) (Cons y (set j' x ys))))
              (Count m (Cons y (Cons (nth j' ys) (set j' x ys))))
              (Count m (Cons x (Cons y ys)))
              (cons2_comm m (nth j' ys) y (set j' x ys))
              (id_trans Nat
                (Count m (Cons y (Cons (nth j' ys) (set j' x ys))))
                (Count m (Cons y (Cons x ys)))
                (Count m (Cons x (Cons y ys)))
                (count_cons_congr m y (Cons (nth j' ys) (set j' x ys)) (Cons x ys) (ih ys bnd0))
                (cons2_comm m y x ys)) } } }
def count_headswap_ty : Term := prog{
  Π (m : Nat) → Π (x : Nat) → Π (j : Nat) → Π (xs : List Nat) → Le (S j) (Len xs) →
    Id Nat (Count m (Cons (nth j xs) (set j x xs))) (Count m (Cons x xs)) }

-- The top: `swapL i j` preserves count when both indices are in range. Induction
-- on `i`, casing `l` then `j`. The head case (`i = Z`, `j = S j'`) is exactly a
-- `count_headswap` (`swapL Z (S j') (Cons y ys) = Cons (nth j' ys) (set j' y ys)`);
-- the recursive case (`i = S i'`, `j = S j'`) rebuilds `Cons y (swapL i' j' ys)`,
-- discharged by `count_cons_congr` on the IH; the degenerate `j = Z` / `i > j`
-- cases are the identity swap (`Refl`); `Nil` is ⊥-discharged by `Le (S i) …`.
def count_swapL : Term := prog{
  λ (m : Nat). λ (i : Nat).
    elim i return (λ (iz : Nat).
        Π (j : Nat) → Π (l : List Nat) → Le (S iz) (Len l) → Le (S j) (Len l) →
          Id Nat (Count m (swapL iz j l)) (Count m l)) {
      Z => λ (j : Nat). λ (l : List Nat).
        elim l return (λ (lz : List Nat).
            Le (S Z) (Len lz) → Le (S j) (Len lz) → Id Nat (Count m (swapL Z j lz)) (Count m lz)) {
          Nil => λ (bi0 : Le (S Z) (Len Nil)). λ (bj0 : Le (S j) (Len Nil)).
            botElim (Id Nat (Count m (swapL Z j Nil)) (Count m Nil)) bi0,
          Cons (y) (ys) ihl => λ (bi0 : Le (S Z) (Len (Cons y ys))). λ (bj0 : Le (S j) (Len (Cons y ys))).
            elim j return (λ (jz : Nat).
                Le (S jz) (Len (Cons y ys)) →
                  Id Nat (Count m (swapL Z jz (Cons y ys))) (Count m (Cons y ys))) {
              Z => λ (bj1 : Le (S Z) (Len (Cons y ys))). Refl,
              S (j') jih => λ (bj1 : Le (S (S j')) (Len (Cons y ys))).
                count_headswap m y j' ys bj1
            } bj0 },
      S (i') ih => λ (j : Nat). λ (l : List Nat).
        elim l return (λ (lz : List Nat).
            Le (S (S i')) (Len lz) → Le (S j) (Len lz) → Id Nat (Count m (swapL (S i') j lz)) (Count m lz)) {
          Nil => λ (bi0 : Le (S (S i')) (Len Nil)). λ (bj0 : Le (S j) (Len Nil)).
            botElim (Id Nat (Count m (swapL (S i') j Nil)) (Count m Nil)) bi0,
          Cons (y) (ys) ihl => λ (bi0 : Le (S (S i')) (Len (Cons y ys))). λ (bj0 : Le (S j) (Len (Cons y ys))).
            elim j return (λ (jz : Nat).
                Le (S jz) (Len (Cons y ys)) →
                  Id Nat (Count m (swapL (S i') jz (Cons y ys))) (Count m (Cons y ys))) {
              Z => λ (bj1 : Le (S Z) (Len (Cons y ys))). Refl,
              S (j') jih => λ (bj1 : Le (S (S j')) (Len (Cons y ys))).
                count_cons_congr m y (swapL i' j' ys) ys (ih j' ys bi0 bj1)
            } bj0 } } }
def count_swapL_ty : Term := prog{
  Π (m : Nat) → Π (i : Nat) → Π (j : Nat) → Π (l : List Nat) →
    Le (S i) (Len l) → Le (S j) (Len l) → Id Nat (Count m (swapL i j l)) (Count m l) }

-- The friction-free corollary: count_swapL with swapS's telescope-mirrored
-- premises (`Le (S i) j`, `Le (S j) (len l)` — exactly the `pij`/`p2` a swapS
-- caller holds). The general count_swapL is the mathematically right statement
-- (independent bounds, no `i ≤ j` needed); this derives the caller's hand-off from
-- it. `Le (S i) (len l)` comes by `le_trans (S i) (S j) (len l)`: `le_up_r` lifts
-- `pij : Le (S i) j` to `Le (S i) (S j)`, then chain with `p2`.
def count_swapL' : Term := prog{
  λ (m : Nat). λ (i : Nat). λ (j : Nat). λ (l : List Nat).
    λ (pij : Le (S i) j). λ (p2 : Le (S j) (Len l)).
      count_swapL m i j l (le_trans (S i) (S j) (Len l) (le_up_r (S i) j pij) p2) p2 }
def count_swapL'_ty : Term := prog{
  Π (m : Nat) → Π (i : Nat) → Π (j : Nat) → Π (l : List Nat) →
    Le (S i) j → Le (S j) (Len l) → Id Nat (Count m (swapL i j l)) (Count m l) }

/-! ## The BRIDGE — set/nth exit form ≡ `swapL` (§22, direct proving)

    In direct-proving mode a swap FnDef's return type reads the EXIT snapshot, and
    the exit reading of `swapS`'s body is the set/nth composition its two crossed
    writes leave behind — `set i (nth j l) (set j (nth i l) l)` — NOT the `swapL`
    model. This bridges the two so every `swapL`-based lemma (count_swapL',
    len_swapL, …) transports to the surface form rather than being re-proved per
    composition (which would be a per-form count-algebra tax forever).

    Carries swapS's telescope bounds `Le (S i) j`, `Le (S j) (len l)` (the `pij`/`p2`
    a swapS caller holds). Both are load-bearing IN THE PROOF, each killing one
    impossible leaf: `pij` discharges the `j = Z` slot (where set-form and swapL
    disagree once `i > 0`), `p2` discharges the `l = Nil` slot (where the inner
    `set j v Nil` is otherwise STUCK on the free `j` — semantically Nil but not
    definitionally without casing `j`). Note the SEMANTIC content needs only
    `Le (S i) j`: verified computationally the two forms agree for all `i < j` even
    off the end. `p2` is proof-theoretic scaffolding, not semantic necessity — it
    lets the Nil leaf be a `botElim` rather than a `set_nil` rewrite, giving the
    exact M18/count_swapL shape. Induction mirrors `swapL`: `i = Z` is definitional
    (both sides reduce to `Cons (nth j' ys) (set j' y ys)`), the `i = S i'` step is
    the IH under `Cons y ·`. -/
def swapL_set : Term := prog{
  λ (i : Nat).
    elim i return (λ (iz : Nat). Π (j : Nat) → Π (l : List Nat) → Le (S iz) j → Le (S j) (Len l) →
        Id (List Nat) (set iz (nth j l) (set j (nth iz l) l)) (swapL iz j l)) {
      Z => λ (j : Nat). λ (l : List Nat).
        elim l return (λ (lz : List Nat). Le (S Z) j → Le (S j) (Len lz) →
            Id (List Nat) (set Z (nth j lz) (set j (nth Z lz) lz)) (swapL Z j lz)) {
          Nil => λ (pij : Le (S Z) j). λ (p2 : Le (S j) (Len Nil)).
            botElim (Id (List Nat) (set Z (nth j Nil) (set j (nth Z Nil) Nil)) (swapL Z j Nil)) p2,
          Cons (y) (ys) ihl => λ (pij : Le (S Z) j). λ (p2 : Le (S j) (Len (Cons y ys))).
            elim j return (λ (jz : Nat). Le (S Z) jz → Le (S jz) (Len (Cons y ys)) →
                Id (List Nat) (set Z (nth jz (Cons y ys)) (set jz (nth Z (Cons y ys)) (Cons y ys))) (swapL Z jz (Cons y ys))) {
              Z => λ (pijz : Le (S Z) Z). λ (p2z : Le (S Z) (Len (Cons y ys))).
                botElim (Id (List Nat) (set Z (nth Z (Cons y ys)) (set Z (nth Z (Cons y ys)) (Cons y ys))) (swapL Z Z (Cons y ys))) pijz,
              S (j') jih => λ (pijs : Le (S Z) (S j')). λ (p2s : Le (S (S j')) (Len (Cons y ys))). Refl
            } pij p2 },
      S (i') ih => λ (j : Nat). λ (l : List Nat).
        elim l return (λ (lz : List Nat). Le (S (S i')) j → Le (S j) (Len lz) →
            Id (List Nat) (set (S i') (nth j lz) (set j (nth (S i') lz) lz)) (swapL (S i') j lz)) {
          Nil => λ (pij : Le (S (S i')) j). λ (p2 : Le (S j) (Len Nil)).
            botElim (Id (List Nat) (set (S i') (nth j Nil) (set j (nth (S i') Nil) Nil)) (swapL (S i') j Nil)) p2,
          Cons (y) (ys) ihl => λ (pij : Le (S (S i')) j). λ (p2 : Le (S j) (Len (Cons y ys))).
            elim j return (λ (jz : Nat). Le (S (S i')) jz → Le (S jz) (Len (Cons y ys)) →
                Id (List Nat) (set (S i') (nth jz (Cons y ys)) (set jz (nth (S i') (Cons y ys)) (Cons y ys))) (swapL (S i') jz (Cons y ys))) {
              Z => λ (pijz : Le (S (S i')) Z). λ (p2z : Le (S Z) (Len (Cons y ys))).
                botElim (Id (List Nat) (set (S i') (nth Z (Cons y ys)) (set Z (nth (S i') (Cons y ys)) (Cons y ys))) (swapL (S i') Z (Cons y ys))) pijz,
              S (j') jih => λ (pijs : Le (S (S i')) (S j')). λ (p2s : Le (S (S j')) (Len (Cons y ys))).
                id_congr (List Nat) (List Nat) (λ (t : List Nat). Cons y t)
                  (set i' (nth j' ys) (set j' (nth i' ys) ys)) (swapL i' j' ys) (ih j' ys pijs p2s)
            } pij p2 } } }
def swapL_set_ty : Term := prog{
  Π (i : Nat) → Π (j : Nat) → Π (l : List Nat) → Le (S i) j → Le (S j) (Len l) →
    Id (List Nat) (set i (nth j l) (set j (nth i l) l)) (swapL i j l) }

/-! ## `partScanL` / `partitionL` — the pure Lomuto model (§19)

    The EXACT recursion the imperative body performs, so the conformance check
    (convert the body's composed backward tree against this per path) holds. Pivot
    is the FIRST element; the scan carries a boundary `i` (size of the ≤-pivot
    region after the pivot) and a GAP counter `g` (the >-pivot elements found so
    far) — so the scan position is `j = S (add i g)` and the swap decision is
    STRUCTURAL on `g` (no second stuck-spine split), and the swap is never a
    self-swap (`g = S g'` guarantees `S i < j`). One `leb` casing per step is the
    only Bool spine, the M19-B gate's job.

    Base (`k = Z`): place the pivot with `swapL Z i` — cased on `i` because swapS
    cannot self-swap, so `i = Z` is the no-op the imperative body also special-cases.
    Step: `leb (nth j l) pivot` — True with `g = Z` advances the boundary (the
    ≤-prefix stays contiguous, no swap); True with `g = S g'` swaps `S i`↔`j`
    (a >-pivot element out, the ≤ element in) keeping the gap; False grows the gap.

    INTERFACE CONTRACT (M21 inheritance): the boundary index `i` at `k = Z` is the
    pivot's final position — the split point the caller recurses on (`[0, i)` and
    `(i, len)`). partition exposes it as its return value; sortL rides it. -/

def partScanL : Term := prog{
  λ (pivot : Nat). λ (k : Nat).
    elim k return (λ (kz : Nat). Π (i : Nat) → Π (g : Nat) → List Nat → List Nat) {
      Z => λ (i : Nat). λ (g : Nat). λ (l : List Nat).
        elim i return (λ (iz : Nat). List Nat) {
          Z => l,
          S (i') iih => swapL Z (S i') l },
      S (k') rec => λ (i : Nat). λ (g : Nat). λ (l : List Nat).
        elim (Leb (nth (S (Add i g)) l) pivot) return (λ (w : Bool). List Nat) {
          True => elim g return (λ (gz : Nat). List Nat) {
            Z => rec (S i) Z l,
            S (g') gih => rec (S i) (S g') (swapL (S i) (S (Add i g)) l) },
          False => rec i (S g) l } } }

def partitionL : Term := prog{
  λ (n : Nat). λ (l : List Nat).
    elim n return (λ (nz : Nat). List Nat) {
      Z => l,
      S (n') rec => partScanL (nth Z l) n' Z Z l } }
def partitionL_ty : Term := prog{ Π (n : Nat) → List Nat → List Nat }

/-! ## `partScanIdxL` / `partIdxL` — the boundary INDEX the scan produces (§21)

    Mirror of partScanL's recursion but returning the boundary `i` (the pivot's
    final position) at `k = Z` instead of the placed list. This is the index the
    imperative partition returns transparently (a Σ pinning it to `partIdxL`), and
    the split point sortL's two recursive calls ride. Same casings/arithmetic as
    partScanL, so the two stay in lockstep. -/

def partScanIdxL : Term := prog{
  λ (pivot : Nat). λ (k : Nat).
    elim k return (λ (kz : Nat). Π (i : Nat) → Π (g : Nat) → List Nat → Nat) {
      Z => λ (i : Nat). λ (g : Nat). λ (l : List Nat). i,
      S (k') rec => λ (i : Nat). λ (g : Nat). λ (l : List Nat).
        elim (Leb (nth (S (Add i g)) l) pivot) return (λ (w : Bool). Nat) {
          True => elim g return (λ (gz : Nat). Nat) {
            Z => rec (S i) Z l,
            S (g') gih => rec (S i) (S g') (swapL (S i) (S (Add i g)) l) },
          False => rec i (S g) l } } }

def partIdxL : Term := prog{
  λ (n : Nat). λ (l : List Nat).
    elim n return (λ (nz : Nat). Nat) {
      Z => Z,
      S (n') rec => partScanIdxL (nth Z l) n' Z Z l } }
def partIdxL_ty : Term := prog{ Π (n : Nat) → List Nat → Nat }

/-! ## `sortL` — the pure quicksort model (§21)

    Fuel-structural (natRec on `fuel`; the caller passes `fuel = n` at the top).
    Base: out of fuel, or a segment of length ≤ 1 (already sorted) → identity. Step
    (n ≥ 2): partition the segment (`p = partitionL n l`, pivot lands at `i =
    partIdxL n l`), then recursively sort the two sub-slices — the prefix `take i p`
    (length `i`) and the suffix `drop (S i) p` (length `len (drop (S i) p)`, which
    avoids Nat subtraction) — reassembling `sortedPrefix ++ [pivot] ++ sortedSuffix`.
    The imperative quicksort mirrors this exactly (partition returns the transparent
    `i`, both recursions ride it), so the conformance is conversion. -/

def sortL : Term := prog{
  λ (fuel : Nat).
    elim fuel return (λ (fz : Nat). Π (n : Nat) → List Nat → List Nat) {
      Z => λ (n : Nat). λ (l : List Nat). l,
      S (f') rec => λ (n : Nat). λ (l : List Nat).
        elim n return (λ (nz : Nat). List Nat) {
          Z => l,
          S (n') nih => elim n' return (λ (mz : Nat). List Nat) {
            Z => l,
            S (n'') n2ih =>
              let p = partitionL n l;
              let i = partIdxL n l;
              append (rec i (Take i p)) (Cons (nth i p) (rec (Len (Drop (S i) p)) (Drop (S i) p)))
          } } } }
def sortL_ty : Term := prog{ Π (fuel : Nat) → Π (n : Nat) → List Nat → List Nat }

/-! ## Range-aware models — the index-bounded quicksort spec (§21, plan of record)

    SUGGESTIONS.md's north star: "suffix sub-slices are tail reborrows; PREFIX
    RECURSION RIDES THE BOUND, not a prefix borrow." So the imperative quicksort
    is CLRS-form `quicksort(v, lo, cnt)` — reborrow the whole *v, sort the `cnt`
    elements at offset `lo` by index swaps, recurse on the two sub-ranges. These
    models are `partScanL`/`partIdxL`/`sortL` with every position shifted by `lo`
    (the pivot sits at `lo`, scan positions are `lo + 1 + i + g`), the boundary
    `i` tracked RELATIVE to `lo`. Two facts make the recursion subtraction-free:
    the relative boundary `i` at `k = Z` IS the left sub-count (elements ≤ pivot),
    and the gap `g` at `k = Z` IS the right sub-count (elements > pivot) — the scan
    maintains `i + g = k`, so no `hi - lo` ever appears. -/

def partScanRangeL : Term := prog{
  λ (pivot : Nat). λ (lo : Nat). λ (k : Nat).
    elim k return (λ (kz : Nat). Π (i : Nat) → Π (g : Nat) → List Nat → List Nat) {
      Z => λ (i : Nat). λ (g : Nat). λ (l : List Nat).
        elim i return (λ (iz : Nat). List Nat) {
          Z => l,
          S (i') iih => swapL lo (Add lo (S i')) l },
      S (k') rec => λ (i : Nat). λ (g : Nat). λ (l : List Nat).
        elim (Leb (nth (Add lo (S (Add i g))) l) pivot) return (λ (w : Bool). List Nat) {
          True => elim g return (λ (gz : Nat). List Nat) {
            Z => rec (S i) Z l,
            S (g') gih => rec (S i) (S g') (swapL (Add lo (S i)) (Add lo (S (Add i g))) l) },
          False => rec i (S g) l } } }

def partitionRangeL : Term := prog{
  λ (lo : Nat). λ (cnt : Nat). λ (l : List Nat).
    elim cnt return (λ (cz : Nat). List Nat) {
      Z => l,
      S (cnt') rec => partScanRangeL (nth lo l) lo cnt' Z Z l } }

def partScanIdxRangeL : Term := prog{
  λ (pivot : Nat). λ (lo : Nat). λ (k : Nat).
    elim k return (λ (kz : Nat). Π (i : Nat) → Π (g : Nat) → List Nat → Nat) {
      Z => λ (i : Nat). λ (g : Nat). λ (l : List Nat). i,
      S (k') rec => λ (i : Nat). λ (g : Nat). λ (l : List Nat).
        elim (Leb (nth (Add lo (S (Add i g))) l) pivot) return (λ (w : Bool). Nat) {
          True => elim g return (λ (gz : Nat). Nat) {
            Z => rec (S i) Z l,
            S (g') gih => rec (S i) (S g') (swapL (Add lo (S i)) (Add lo (S (Add i g))) l) },
          False => rec i (S g) l } } }

def partIdxRangeL : Term := prog{
  λ (lo : Nat). λ (cnt : Nat). λ (l : List Nat).
    elim cnt return (λ (cz : Nat). Nat) {
      Z => Z,
      S (cnt') rec => partScanIdxRangeL (nth lo l) lo cnt' Z Z l } }

def partScanGapRangeL : Term := prog{
  λ (pivot : Nat). λ (lo : Nat). λ (k : Nat).
    elim k return (λ (kz : Nat). Π (i : Nat) → Π (g : Nat) → List Nat → Nat) {
      Z => λ (i : Nat). λ (g : Nat). λ (l : List Nat). g,
      S (k') rec => λ (i : Nat). λ (g : Nat). λ (l : List Nat).
        elim (Leb (nth (Add lo (S (Add i g))) l) pivot) return (λ (w : Bool). Nat) {
          True => elim g return (λ (gz : Nat). Nat) {
            Z => rec (S i) Z l,
            S (g') gih => rec (S i) (S g') (swapL (Add lo (S i)) (Add lo (S (Add i g))) l) },
          False => rec i (S g) l } } }

def partGapRangeL : Term := prog{
  λ (lo : Nat). λ (cnt : Nat). λ (l : List Nat).
    elim cnt return (λ (cz : Nat). Nat) {
      Z => Z,
      S (cnt') rec => partScanGapRangeL (nth lo l) lo cnt' Z Z l } }

-- The scan's size invariant: the boundary `idx` plus the gap `gap` always sum to
-- `k + i + g` — the scan neither creates nor destroys total budget, it only shifts
-- successors between the `k`/`i`/`g` slots (the same move the `hshift` lemmas
-- encode). Induction on `k` with `i`,`g`,`l` quantified AFTER `k` in the motive, so
-- the IH is usable at the shifted arguments each recursive step takes. The `S k`
-- step cases on the SAME `leb` scrutinee that both `partScanIdxRangeL` and
-- `partScanGapRangeL` branch on, abstracting that `Bool` uniformly across the idx
-- and gap elims; each leaf is one `hshift` transport (`id_sym`/`id_trans`).
def partScanSizeL : Term := prog{
  λ (pivot : Nat). λ (lo : Nat). λ (k : Nat).
    elim k return (λ (kz : Nat). Π (i : Nat) → Π (g : Nat) → Π (l : List Nat) →
        Id Nat (Add (partScanIdxRangeL pivot lo kz i g l) (partScanGapRangeL pivot lo kz i g l)) (Add kz (Add i g))) {
      Z => λ (i : Nat). λ (g : Nat). λ (l : List Nat). Refl,
      S (k') ih => λ (i : Nat). λ (g : Nat). λ (l : List Nat).
        elim (Leb (nth (Add lo (S (Add i g))) l) pivot)
          return (λ (w : Bool). Id Nat
            (Add (elim w return (λ (ww : Bool). Nat) {
                    True => elim g return (λ (gz : Nat). Nat) {
                      Z => partScanIdxRangeL pivot lo k' (S i) Z l,
                      S (g') gih => partScanIdxRangeL pivot lo k' (S i) (S g') (swapL (Add lo (S i)) (Add lo (S (Add i g))) l) },
                    False => partScanIdxRangeL pivot lo k' i (S g) l })
                 (elim w return (λ (ww : Bool). Nat) {
                    True => elim g return (λ (gz : Nat). Nat) {
                      Z => partScanGapRangeL pivot lo k' (S i) Z l,
                      S (g') gih => partScanGapRangeL pivot lo k' (S i) (S g') (swapL (Add lo (S i)) (Add lo (S (Add i g))) l) },
                    False => partScanGapRangeL pivot lo k' i (S g) l }))
            (Add (S k') (Add i g))) {
          True => elim g return (λ (gz : Nat). Id Nat
                    (Add (elim gz return (λ (gy : Nat). Nat) {
                            Z => partScanIdxRangeL pivot lo k' (S i) Z l,
                            S (g') gih => partScanIdxRangeL pivot lo k' (S i) (S g') (swapL (Add lo (S i)) (Add lo (S (Add i g))) l) })
                         (elim gz return (λ (gy : Nat). Nat) {
                            Z => partScanGapRangeL pivot lo k' (S i) Z l,
                            S (g') gih => partScanGapRangeL pivot lo k' (S i) (S g') (swapL (Add lo (S i)) (Add lo (S (Add i g))) l) }))
                    (Add (S k') (Add i gz))) {
            Z => id_trans Nat
                   (Add (partScanIdxRangeL pivot lo k' (S i) Z l) (partScanGapRangeL pivot lo k' (S i) Z l))
                   (Add k' (Add (S i) Z))
                   (Add (S k') (Add i Z))
                   (ih (S i) Z l)
                   (id_sym Nat (Add (S k') (Add i Z)) (Add k' (Add (S i) Z)) (hshift_true k' i Z)),
            S (g') gih => id_trans Nat
                   (Add (partScanIdxRangeL pivot lo k' (S i) (S g') (swapL (Add lo (S i)) (Add lo (S (Add i g))) l)) (partScanGapRangeL pivot lo k' (S i) (S g') (swapL (Add lo (S i)) (Add lo (S (Add i g))) l)))
                   (Add k' (Add (S i) (S g')))
                   (Add (S k') (Add i (S g')))
                   (ih (S i) (S g') (swapL (Add lo (S i)) (Add lo (S (Add i g))) l))
                   (id_sym Nat (Add (S k') (Add i (S g'))) (Add k' (Add (S i) (S g'))) (hshift_true k' i (S g')))
          },
          False => id_trans Nat
                     (Add (partScanIdxRangeL pivot lo k' i (S g) l) (partScanGapRangeL pivot lo k' i (S g) l))
                     (Add k' (Add i (S g)))
                     (Add (S k') (Add i g))
                     (ih i (S g) l)
                     (id_sym Nat (Add (S k') (Add i g)) (Add k' (Add i (S g))) (hshift_false k' i g))
        }
    } }
def partScanSizeL_ty : Term := prog{ Π (pivot : Nat) → Π (lo : Nat) → Π (k : Nat) → Π (i : Nat) → Π (g : Nat) → Π (l : List Nat) →
  Id Nat (Add (partScanIdxRangeL pivot lo k i g l) (partScanGapRangeL pivot lo k i g l)) (Add k (Add i g)) }

-- The range scan preserves length — it only ever rebuilds the same spine (swapL,
-- which len_swapL knows preserves length) or leaves it. Same induction shape as
-- partScanSizeL (on k, elim the leb Bool, elim g in True), but the leaves are
-- simpler: each recursive step is the IH, and the two swapL cases (Z-base pivot
-- placement, True/S-g swap) bridge through len_swapL. The quicksort recursion
-- needs this because partitionRange MUTATES *v, and the two recursive-call range
-- bounds refer to len (*v-after-partition) — this moves them back onto len (entry).
def len_partScanRangeL : Term := prog{
  λ (pivot : Nat). λ (lo : Nat). λ (k : Nat).
    elim k return (λ (kz : Nat). Π (i : Nat) → Π (g : Nat) → Π (l : List Nat) →
        Id Nat (Len (partScanRangeL pivot lo kz i g l)) (Len l)) {
      Z => λ (i : Nat). λ (g : Nat). λ (l : List Nat).
        elim i return (λ (iz : Nat). Id Nat
            (Len (elim iz return (λ (iy : Nat). List Nat) { Z => l, S (i') iih => swapL lo (Add lo (S i')) l }))
            (Len l)) {
          Z => Refl,
          S (i') iih => len_swapL lo (Add lo (S i')) l },
      S (k') ih => λ (i : Nat). λ (g : Nat). λ (l : List Nat).
        elim (Leb (nth (Add lo (S (Add i g))) l) pivot)
          return (λ (w : Bool). Id Nat
            (Len (elim w return (λ (ww : Bool). List Nat) {
                    True => elim g return (λ (gz : Nat). List Nat) {
                      Z => partScanRangeL pivot lo k' (S i) Z l,
                      S (g') gih => partScanRangeL pivot lo k' (S i) (S g') (swapL (Add lo (S i)) (Add lo (S (Add i g))) l) },
                    False => partScanRangeL pivot lo k' i (S g) l }))
            (Len l)) {
          True => elim g return (λ (gz : Nat). Id Nat
                    (Len (elim gz return (λ (gy : Nat). List Nat) {
                            Z => partScanRangeL pivot lo k' (S i) Z l,
                            S (g') gih => partScanRangeL pivot lo k' (S i) (S g') (swapL (Add lo (S i)) (Add lo (S (Add i g))) l) }))
                    (Len l)) {
            Z => ih (S i) Z l,
            S (g') gih => id_trans Nat
                   (Len (partScanRangeL pivot lo k' (S i) (S g') (swapL (Add lo (S i)) (Add lo (S (Add i g))) l)))
                   (Len (swapL (Add lo (S i)) (Add lo (S (Add i g))) l))
                   (Len l)
                   (ih (S i) (S g') (swapL (Add lo (S i)) (Add lo (S (Add i g))) l))
                   (len_swapL (Add lo (S i)) (Add lo (S (Add i g))) l)
          },
          False => ih i (S g) l
        }
    } }
def len_partScanRangeL_ty : Term := prog{ Π (pivot : Nat) → Π (lo : Nat) → Π (k : Nat) → Π (i : Nat) → Π (g : Nat) → Π (l : List Nat) →
  Id Nat (Len (partScanRangeL pivot lo k i g l)) (Len l) }

-- The wrapper form the quicksort recursion consumes: partitionRangeL is
-- partScanRangeL after picking the pivot, so its length preservation is the scan's
-- (Z base is Refl, S cnt' is len_partScanRangeL at the entry offsets).
def len_partitionRangeL : Term := prog{
  λ (lo : Nat). λ (cnt : Nat). λ (l : List Nat).
    elim cnt return (λ (cz : Nat). Id Nat
        (Len (elim cz return (λ (cy : Nat). List Nat) { Z => l, S (cnt') rec => partScanRangeL (nth lo l) lo cnt' Z Z l }))
        (Len l)) {
      Z => Refl,
      S (cnt') rec => len_partScanRangeL (nth lo l) lo cnt' Z Z l } }
def len_partitionRangeL_ty : Term := prog{ Π (lo : Nat) → Π (cnt : Nat) → Π (l : List Nat) → Id Nat (Len (partitionRangeL lo cnt l)) (Len l) }

/-! ## Count preservation of the range scan/partition (§22, the partition rung)

    The permutation half of partition's postcondition: the range scan preserves the
    multiset. Same induction shape as len_partScanRangeL (on k, elim the leb Bool,
    elim g in True), but where len_swapL is UNCONDITIONAL, count_swapL' is BOUNDED —
    so unlike the len versions these THREAD the range bound `Le (add lo (S (add k
    (add i g)))) (len l)` (the honest invariant partScanRange already carries) and
    reconstruct the two per-swap `count_swapL'` premises from it at each swap leaf,
    exactly the le_trans/le_rw_l/le_add_mono_l bound algebra partScanRange's body
    proves. This is the proof-linearity-vs-count asymmetry made concrete: length is
    friction-free, count pays the bound tax at every swap. -/
def count_partScanRangeL : Term := prog{
  λ (pivot : Nat). λ (lo : Nat). λ (m : Nat). λ (k : Nat).
    elim k return (λ (kz : Nat). Π (i : Nat) → Π (g : Nat) → Π (l : List Nat) →
        Le (Add lo (S (Add kz (Add i g)))) (Len l) →
        Id Nat (Count m (partScanRangeL pivot lo kz i g l)) (Count m l)) {
      Z => λ (i : Nat). λ (g : Nat). λ (l : List Nat).
        elim i return (λ (iz : Nat).
            Le (Add lo (S (Add Z (Add iz g)))) (Len l) →
            Id Nat (Count m (elim iz return (λ (iy : Nat). List Nat) {
                Z => l, S (i') iih => swapL lo (Add lo (S i')) l })) (Count m l)) {
          Z => λ (hle : Le (Add lo (S (Add Z (Add Z g)))) (Len l)). Refl,
          S (i') iih => λ (hle : Le (Add lo (S (Add Z (Add (S i') g)))) (Len l)).
            count_swapL' m lo (Add lo (S i')) l (le_add_succ lo i')
              (le_trans (S (Add lo (S i'))) (Add lo (S (S (Add i' g)))) (Len l)
                (le_rw_l (Add lo (S (S (Add i' g)))) (Add lo (S (S i'))) (S (Add lo (S i')))
                  (add_succ lo (S i'))
                  (le_add_mono_l lo (S (S i')) (S (S (Add i' g))) (le_add i' g)))
                hle)
        },
      S (k') ih => λ (i : Nat). λ (g : Nat). λ (l : List Nat).
        λ (hle : Le (Add lo (S (Add (S k') (Add i g)))) (Len l)).
        elim (Leb (nth (Add lo (S (Add i g))) l) pivot)
          return (λ (w : Bool). Id Nat
            (Count m (elim w return (λ (ww : Bool). List Nat) {
                True => elim g return (λ (gz : Nat). List Nat) {
                  Z => partScanRangeL pivot lo k' (S i) Z l,
                  S (g') gih => partScanRangeL pivot lo k' (S i) (S g') (swapL (Add lo (S i)) (Add lo (S (Add i g))) l) },
                False => partScanRangeL pivot lo k' i (S g) l }))
            (Count m l)) {
          True =>
            (elim g return (λ (gz : Nat).
                Le (Add lo (S (Add (S k') (Add i gz)))) (Len l) →
                Id Nat (Count m (elim gz return (λ (gy : Nat). List Nat) {
                    Z => partScanRangeL pivot lo k' (S i) Z l,
                    S (g') gih => partScanRangeL pivot lo k' (S i) (S g') (swapL (Add lo (S i)) (Add lo (S (Add i gz))) l) })) (Count m l)) {
              Z => λ (hleZ : Le (Add lo (S (Add (S k') (Add i Z)))) (Len l)).
                ih (S i) Z l
                  (le_rw_l (Len l)
                    (Add lo (S (Add (S k') (Add i Z))))
                    (Add lo (S (Add k' (Add (S i) Z))))
                    (id_congr Nat Nat (λ (a : Nat). Add lo (S a))
                      (Add (S k') (Add i Z)) (Add k' (Add (S i) Z)) (hshift_true k' i Z))
                    hleZ),
              S (g') gih => λ (hleS : Le (Add lo (S (Add (S k') (Add i (S g'))))) (Len l)).
                id_trans Nat
                  (Count m (partScanRangeL pivot lo k' (S i) (S g') (swapL (Add lo (S i)) (Add lo (S (Add i (S g')))) l)))
                  (Count m (swapL (Add lo (S i)) (Add lo (S (Add i (S g')))) l))
                  (Count m l)
                  (ih (S i) (S g') (swapL (Add lo (S i)) (Add lo (S (Add i (S g')))) l)
                    (le_rw_r (Add lo (S (Add k' (Add (S i) (S g'))))) (Len l)
                       (Len (swapL (Add lo (S i)) (Add lo (S (Add i (S g')))) l))
                       (id_sym Nat (Len (swapL (Add lo (S i)) (Add lo (S (Add i (S g')))) l)) (Len l)
                         (len_swapL (Add lo (S i)) (Add lo (S (Add i (S g')))) l))
                       (le_rw_l (Len l)
                         (Add lo (S (Add (S k') (Add i (S g')))))
                         (Add lo (S (Add k' (Add (S i) (S g')))))
                         (id_congr Nat Nat (λ (a : Nat). Add lo (S a))
                           (Add (S k') (Add i (S g'))) (Add k' (Add (S i) (S g'))) (hshift_true k' i (S g')))
                         hleS)))
                  (count_swapL' m (Add lo (S i)) (Add lo (S (Add i (S g')))) l
                    (le_rw_l (Add lo (S (Add i (S g')))) (Add lo (S (S i))) (S (Add lo (S i)))
                      (add_succ lo (S i))
                      (le_add_mono_l lo (S (S i)) (S (Add i (S g'))) (le_add_succ i g')))
                    (le_trans (S (Add lo (S (Add i (S g'))))) (Add lo (S (S (Add k' (Add i (S g')))))) (Len l)
                      (le_rw_l (Add lo (S (S (Add k' (Add i (S g'))))))
                        (Add lo (S (S (Add i (S g'))))) (S (Add lo (S (Add i (S g')))))
                        (add_succ lo (S (Add i (S g'))))
                        (le_add_mono_l lo (S (S (Add i (S g')))) (S (S (Add k' (Add i (S g')))))
                          (le_add_l (Add i (S g')) k')))
                      hleS))
            }) hle,
          False =>
            ih i (S g) l
              (le_rw_l (Len l)
                (Add lo (S (Add (S k') (Add i g))))
                (Add lo (S (Add k' (Add i (S g)))))
                (id_congr Nat Nat (λ (a : Nat). Add lo (S a))
                  (Add (S k') (Add i g)) (Add k' (Add i (S g))) (hshift_false k' i g))
                hle)
        }
    } }
def count_partScanRangeL_ty : Term := prog{
  Π (pivot : Nat) → Π (lo : Nat) → Π (m : Nat) → Π (k : Nat) → Π (i : Nat) → Π (g : Nat) → Π (l : List Nat) →
    Le (Add lo (S (Add k (Add i g)))) (Len l) →
    Id Nat (Count m (partScanRangeL pivot lo k i g l)) (Count m l) }

-- Wrapper: partitionRangeL is partScanRangeL after picking the pivot, so count
-- preservation is the scan's (Z base Refl, S cnt' is the scan at entry offsets).
-- The top range bound `Le (add lo cnt) (len l)` supplies the scan's bound; at
-- cnt = S cnt' it needs an add_zero nudge (`add cnt' (add Z Z) = add cnt' Z`, and
-- `add` recurses on its FIRST arg so `add cnt' Z` is stuck at a free cnt').
def count_partitionRangeL : Term := prog{
  λ (lo : Nat). λ (m : Nat). λ (cnt : Nat). λ (l : List Nat).
    elim cnt return (λ (cz : Nat).
        Le (Add lo cz) (Len l) →
        Id Nat (Count m (elim cz return (λ (cy : Nat). List Nat) {
            Z => l, S (cnt') rec => partScanRangeL (nth lo l) lo cnt' Z Z l })) (Count m l)) {
      Z => λ (hb : Le (Add lo Z) (Len l)). Refl,
      S (cnt') rec => λ (hb : Le (Add lo (S cnt')) (Len l)).
        count_partScanRangeL (nth lo l) lo m cnt' Z Z l
          (le_rw_l (Len l) (Add lo (S cnt')) (Add lo (S (Add cnt' Z)))
            (id_congr Nat Nat (λ (a : Nat). Add lo (S a)) cnt' (Add cnt' Z)
              (id_sym Nat (Add cnt' Z) cnt' (add_zero cnt')))
            hb) } }
def count_partitionRangeL_ty : Term := prog{
  Π (lo : Nat) → Π (m : Nat) → Π (cnt : Nat) → Π (l : List Nat) →
    Le (Add lo cnt) (Len l) → Id Nat (Count m (partitionRangeL lo cnt l)) (Count m l) }

/-- `sortRangeL fuel lo cnt l` — sort the `cnt` elements of `l` at offset `lo` in
    place. Fuel-structural; base = out of fuel or `cnt ≤ 1`; step partitions the
    range, then sorts the left sub-range `[lo, lo+i)` (count `i`) and the right
    `[lo+i+1, …)` (count `g`), the right on the result of the left — the raw
    composition the imperative body implements. `partitionQ` is the `lo = 0` slice. -/
def sortRangeL : Term := prog{
  λ (fuel : Nat).
    elim fuel return (λ (fz : Nat). Π (lo : Nat) → Π (cnt : Nat) → List Nat → List Nat) {
      Z => λ (lo : Nat). λ (cnt : Nat). λ (l : List Nat). l,
      S (f') rec => λ (lo : Nat). λ (cnt : Nat). λ (l : List Nat).
        elim cnt return (λ (cz : Nat). List Nat) {
          Z => l,
          S (cnt') nih => elim cnt' return (λ (mz : Nat). List Nat) {
            Z => l,
            S (cnt'') n2ih =>
              let p = partitionRangeL lo cnt l;
              let i = partIdxRangeL lo cnt l;
              let g = partGapRangeL lo cnt l;
              rec (S (Add lo i)) g (rec lo i p)
          } } } }
def sortRangeL_ty : Term := prog{ Π (fuel : Nat) → Π (lo : Nat) → Π (cnt : Nat) → List Nat → List Nat }

-- sortRangeL is a permutation, so it preserves length. Fuel-structural induction
-- mirroring sortRangeL's own shape (base fuel Z / cnt ≤ 1 are Refl); the step is
-- the IH applied to each of the two recursive sorts, chained onto
-- len_partitionRangeL for the partition underneath. The quicksort recursion needs
-- this for its SECOND range bound: the second recursive call runs after the first
-- has permuted *v, so the bound (over len *v-after-first) moves back through this.
def len_sortRangeL : Term := prog{
  λ (fuel : Nat).
    elim fuel return (λ (fz : Nat). Π (lo : Nat) → Π (cnt : Nat) → Π (l : List Nat) → Id Nat (Len (sortRangeL fz lo cnt l)) (Len l)) {
      Z => λ (lo : Nat). λ (cnt : Nat). λ (l : List Nat). Refl,
      S (f') ih => λ (lo : Nat). λ (cnt : Nat). λ (l : List Nat).
        elim cnt return (λ (cz : Nat). Id Nat (Len (elim cz return (λ (cy : Nat). List Nat) {
              Z => l,
              S (cnt') nih => elim cnt' return (λ (my : Nat). List Nat) {
                Z => l,
                S (cnt'') n2ih => sortRangeL f' (S (Add lo (partIdxRangeL lo cnt l))) (partGapRangeL lo cnt l) (sortRangeL f' lo (partIdxRangeL lo cnt l) (partitionRangeL lo cnt l)) } })) (Len l)) {
          Z => Refl,
          S (cnt') nih => elim cnt' return (λ (my : Nat). Id Nat (Len (elim my return (λ (myy : Nat). List Nat) {
                Z => l,
                S (cnt'') n2ih => sortRangeL f' (S (Add lo (partIdxRangeL lo cnt l))) (partGapRangeL lo cnt l) (sortRangeL f' lo (partIdxRangeL lo cnt l) (partitionRangeL lo cnt l)) })) (Len l)) {
            Z => Refl,
            S (cnt'') n2ih =>
              id_trans Nat
                (Len (sortRangeL f' (S (Add lo (partIdxRangeL lo cnt l))) (partGapRangeL lo cnt l) (sortRangeL f' lo (partIdxRangeL lo cnt l) (partitionRangeL lo cnt l))))
                (Len (sortRangeL f' lo (partIdxRangeL lo cnt l) (partitionRangeL lo cnt l)))
                (Len l)
                (ih (S (Add lo (partIdxRangeL lo cnt l))) (partGapRangeL lo cnt l) (sortRangeL f' lo (partIdxRangeL lo cnt l) (partitionRangeL lo cnt l)))
                (id_trans Nat
                  (Len (sortRangeL f' lo (partIdxRangeL lo cnt l) (partitionRangeL lo cnt l)))
                  (Len (partitionRangeL lo cnt l))
                  (Len l)
                  (ih lo (partIdxRangeL lo cnt l) (partitionRangeL lo cnt l))
                  (len_partitionRangeL lo cnt l))
          } } } }
def len_sortRangeL_ty : Term := prog{ Π (fuel : Nat) → Π (lo : Nat) → Π (cnt : Nat) → Π (l : List Nat) → Id Nat (Len (sortRangeL fuel lo cnt l)) (Len l) }

/-! ## Count preservation of the full sort (§22, the quicksort rung)

    The permutation half of quicksort's postcondition. Fuel-structural induction
    mirroring sortRangeL (base fuel Z / cnt ≤ 1 are Refl); the step chains the IH
    over the two recursive sorts onto count_partitionRangeL for the partition
    underneath — `count m (sort right (sort left (partition l))) = count m (sort
    left (partition l)) = count m (partition l) = count m l`. Like the len version
    but count is BOUNDED, so it threads the range bound `Le (add lo cnt) (len l)`
    and each recursive call gets its sub-range bound from `sortRangeBL`/`sortRangeBR`
    below (the two range bounds the imperative quicksort's body already derives from
    partScanSizeL + the len lemmas). NOTE the elim S-arms carry their (unused) IH
    binders `nih`/`n2ih` — the natRec recursion runs through the fuel `ih`, not the
    cnt elims, but the binder is syntactically required. -/

-- Left sub-range bound: `Le (add lo i) (len (partition …))`, i = the pivot index.
-- Lifted verbatim from the quicksort FnDef's `bl` (partScanSizeL gives i+g = cnt-1,
-- len_partitionRangeL moves the entry bound onto the partitioned list).
def sortRangeBL : Term := prog{
  λ (lo : Nat). λ (cnt'' : Nat). λ (l : List Nat). λ (hb : Le (Add lo (S (S cnt''))) (Len l)).
    le_rw_r (Add lo (partIdxRangeL lo (S (S cnt'')) l)) (Len l) (Len (partitionRangeL lo (S (S cnt'')) l))
      (id_sym Nat (Len (partitionRangeL lo (S (S cnt'')) l)) (Len l)
        (len_partitionRangeL lo (S (S cnt'')) l))
      (le_trans (Add lo (partIdxRangeL lo (S (S cnt'')) l)) (Add lo (S (S cnt''))) (Len l)
        (le_rw_r (Add lo (partIdxRangeL lo (S (S cnt'')) l))
          (Add lo (S (Add (partIdxRangeL lo (S (S cnt'')) l) (partGapRangeL lo (S (S cnt'')) l))))
          (Add lo (S (S cnt'')))
          (id_congr Nat Nat (λ (a : Nat). Add lo a)
            (S (Add (partIdxRangeL lo (S (S cnt'')) l) (partGapRangeL lo (S (S cnt'')) l))) (S (S cnt''))
            (id_congr Nat Nat (λ (a : Nat). S a)
              (Add (partIdxRangeL lo (S (S cnt'')) l) (partGapRangeL lo (S (S cnt'')) l)) (S cnt'')
              (id_trans Nat (Add (partIdxRangeL lo (S (S cnt'')) l) (partGapRangeL lo (S (S cnt'')) l))
                (S (Add cnt'' Z)) (S cnt'')
                (partScanSizeL (nth lo l) lo (S cnt'') Z Z l)
                (id_congr Nat Nat (λ (a : Nat). S a) (Add cnt'' Z) cnt'' (add_zero cnt'')))))
          (le_add_mono_l lo (partIdxRangeL lo (S (S cnt'')) l)
            (S (Add (partIdxRangeL lo (S (S cnt'')) l) (partGapRangeL lo (S (S cnt'')) l)))
            (le_up_r (partIdxRangeL lo (S (S cnt'')) l)
              (Add (partIdxRangeL lo (S (S cnt'')) l) (partGapRangeL lo (S (S cnt'')) l))
              (le_add (partIdxRangeL lo (S (S cnt'')) l) (partGapRangeL lo (S (S cnt'')) l)))))
        hb) }
def sortRangeBL_ty : Term := prog{
  Π (lo : Nat) → Π (cnt'' : Nat) → Π (l : List Nat) → Le (Add lo (S (S cnt''))) (Len l) →
    Le (Add lo (partIdxRangeL lo (S (S cnt'')) l)) (Len (partitionRangeL lo (S (S cnt'')) l)) }

-- Right sub-range bound: `Le (add (S (add lo i)) g) (len (sort left (partition …)))`.
-- Lifted verbatim from the quicksort FnDef's `br` (len_sortRangeL then
-- len_partitionRangeL move the bound back over both mutations; the arithmetic
-- `add (S (add lo i)) g = add lo (S (i+g)) = add lo cnt` uses add_assoc/add_succ).
def sortRangeBR : Term := prog{
  λ (f' : Nat). λ (lo : Nat). λ (cnt'' : Nat). λ (l : List Nat). λ (hb : Le (Add lo (S (S cnt''))) (Len l)).
    le_rw_r (Add (S (Add lo (partIdxRangeL lo (S (S cnt'')) l))) (partGapRangeL lo (S (S cnt'')) l)) (Len l)
      (Len (sortRangeL f' lo (partIdxRangeL lo (S (S cnt'')) l) (partitionRangeL lo (S (S cnt'')) l)))
      (id_sym Nat (Len (sortRangeL f' lo (partIdxRangeL lo (S (S cnt'')) l) (partitionRangeL lo (S (S cnt'')) l))) (Len l)
        (id_trans Nat (Len (sortRangeL f' lo (partIdxRangeL lo (S (S cnt'')) l) (partitionRangeL lo (S (S cnt'')) l)))
          (Len (partitionRangeL lo (S (S cnt'')) l)) (Len l)
          (len_sortRangeL f' lo (partIdxRangeL lo (S (S cnt'')) l) (partitionRangeL lo (S (S cnt'')) l))
          (len_partitionRangeL lo (S (S cnt'')) l)))
      (le_rw_l (Len l) (Add lo (S (S cnt'')))
        (Add (S (Add lo (partIdxRangeL lo (S (S cnt'')) l))) (partGapRangeL lo (S (S cnt'')) l))
        (id_sym Nat (Add (S (Add lo (partIdxRangeL lo (S (S cnt'')) l))) (partGapRangeL lo (S (S cnt'')) l)) (Add lo (S (S cnt'')))
          (id_trans Nat (Add (S (Add lo (partIdxRangeL lo (S (S cnt'')) l))) (partGapRangeL lo (S (S cnt'')) l))
            (S (Add lo (Add (partIdxRangeL lo (S (S cnt'')) l) (partGapRangeL lo (S (S cnt'')) l)))) (Add lo (S (S cnt'')))
            (id_congr Nat Nat (λ (a : Nat). S a)
              (Add (Add lo (partIdxRangeL lo (S (S cnt'')) l)) (partGapRangeL lo (S (S cnt'')) l))
              (Add lo (Add (partIdxRangeL lo (S (S cnt'')) l) (partGapRangeL lo (S (S cnt'')) l)))
              (add_assoc lo (partIdxRangeL lo (S (S cnt'')) l) (partGapRangeL lo (S (S cnt'')) l)))
            (id_trans Nat (S (Add lo (Add (partIdxRangeL lo (S (S cnt'')) l) (partGapRangeL lo (S (S cnt'')) l))))
              (Add lo (S (Add (partIdxRangeL lo (S (S cnt'')) l) (partGapRangeL lo (S (S cnt'')) l)))) (Add lo (S (S cnt'')))
              (id_sym Nat (Add lo (S (Add (partIdxRangeL lo (S (S cnt'')) l) (partGapRangeL lo (S (S cnt'')) l))))
                (S (Add lo (Add (partIdxRangeL lo (S (S cnt'')) l) (partGapRangeL lo (S (S cnt'')) l))))
                (add_succ lo (Add (partIdxRangeL lo (S (S cnt'')) l) (partGapRangeL lo (S (S cnt'')) l))))
              (id_congr Nat Nat (λ (a : Nat). Add lo a)
                (S (Add (partIdxRangeL lo (S (S cnt'')) l) (partGapRangeL lo (S (S cnt'')) l))) (S (S cnt''))
                (id_congr Nat Nat (λ (a : Nat). S a)
                  (Add (partIdxRangeL lo (S (S cnt'')) l) (partGapRangeL lo (S (S cnt'')) l)) (S cnt'')
                  (id_trans Nat (Add (partIdxRangeL lo (S (S cnt'')) l) (partGapRangeL lo (S (S cnt'')) l))
                    (S (Add cnt'' Z)) (S cnt'')
                    (partScanSizeL (nth lo l) lo (S cnt'') Z Z l)
                    (id_congr Nat Nat (λ (a : Nat). S a) (Add cnt'' Z) cnt'' (add_zero cnt''))))))))
        hb) }
def sortRangeBR_ty : Term := prog{
  Π (f' : Nat) → Π (lo : Nat) → Π (cnt'' : Nat) → Π (l : List Nat) → Le (Add lo (S (S cnt''))) (Len l) →
    Le (Add (S (Add lo (partIdxRangeL lo (S (S cnt'')) l))) (partGapRangeL lo (S (S cnt'')) l))
       (Len (sortRangeL f' lo (partIdxRangeL lo (S (S cnt'')) l) (partitionRangeL lo (S (S cnt'')) l))) }

def count_sortRangeL : Term := prog{
  λ (m : Nat). λ (fuel : Nat).
    elim fuel return (λ (fz : Nat). Π (lo : Nat) → Π (cnt : Nat) → Π (l : List Nat) →
        Le (Add lo cnt) (Len l) → Id Nat (Count m (sortRangeL fz lo cnt l)) (Count m l)) {
      Z => λ (lo : Nat). λ (cnt : Nat). λ (l : List Nat). λ (hb : Le (Add lo cnt) (Len l)). Refl,
      S (f') ih => λ (lo : Nat). λ (cnt : Nat). λ (l : List Nat).
        elim cnt return (λ (cz : Nat). Le (Add lo cz) (Len l) →
            Id Nat (Count m (sortRangeL (S f') lo cz l)) (Count m l)) {
          Z => λ (hb : Le (Add lo Z) (Len l)). Refl,
          S (cnt') nih => elim cnt' return (λ (cz' : Nat). Le (Add lo (S cz')) (Len l) →
              Id Nat (Count m (sortRangeL (S f') lo (S cz') l)) (Count m l)) {
            Z => λ (hb : Le (Add lo (S Z)) (Len l)). Refl,
            S (cnt'') n2ih => λ (hb : Le (Add lo (S (S cnt''))) (Len l)).
              id_trans Nat
                (Count m (sortRangeL f' (S (Add lo (partIdxRangeL lo (S (S cnt'')) l))) (partGapRangeL lo (S (S cnt'')) l)
                          (sortRangeL f' lo (partIdxRangeL lo (S (S cnt'')) l) (partitionRangeL lo (S (S cnt'')) l))))
                (Count m (sortRangeL f' lo (partIdxRangeL lo (S (S cnt'')) l) (partitionRangeL lo (S (S cnt'')) l)))
                (Count m l)
                (ih (S (Add lo (partIdxRangeL lo (S (S cnt'')) l))) (partGapRangeL lo (S (S cnt'')) l)
                    (sortRangeL f' lo (partIdxRangeL lo (S (S cnt'')) l) (partitionRangeL lo (S (S cnt'')) l))
                    (sortRangeBR f' lo cnt'' l hb))
                (id_trans Nat
                  (Count m (sortRangeL f' lo (partIdxRangeL lo (S (S cnt'')) l) (partitionRangeL lo (S (S cnt'')) l)))
                  (Count m (partitionRangeL lo (S (S cnt'')) l))
                  (Count m l)
                  (ih lo (partIdxRangeL lo (S (S cnt'')) l) (partitionRangeL lo (S (S cnt'')) l)
                      (sortRangeBL lo cnt'' l hb))
                  (count_partitionRangeL lo m (S (S cnt'')) l hb))
          }
        }
    } }
def count_sortRangeL_ty : Term := prog{
  Π (m : Nat) → Π (fuel : Nat) → Π (lo : Nat) → Π (cnt : Nat) → Π (l : List Nat) →
    Le (Add lo cnt) (Len l) → Id Nat (Count m (sortRangeL fuel lo cnt l)) (Count m l) }

/-! ## Range-order predicates — the sortedness axis (§22, M22-c)

    AllLeR/AllGtR: the `w` positions [lo, lo+w) of `l` are all ≤ p (resp. > p). The
    ordering-relation-to-pivot the count models are blind to.

    ENCODING = bounded-Π, NOT a Σ-chain. Comptime Σ types can be CONSTRUCTED (Pair)
    but NOT ELIMINATED in a pure proof — `match` is runtime-only, and `elim` supports
    only the Nat/Bool/List recursors, so a conjunction-as-Σ can never be projected in
    a lemma. `Π (k : Nat) → Le (S k) w → Le (nth (add k lo) l) p` sidesteps that:
    eliminate by APPLICATION (`h k hk`), construct by LAMBDA. `add k lo` (k first, not
    `add lo k`) so the k=0 head reduces to `nth lo l` definitionally (add Z lo = lo),
    avoiding an add_zero transport at every head extraction.

    NB the predicate FAMILY is not directly `chk`-able against `Π … → Type` (the M5
    limitation: hasType defers λ/neutral typing, so it can't type `Unit`/a neutral
    under the family's binders). This is not a defect in the predicate — it is only
    APPLIED forms that appear in lemma statements, and those reduce and check fine
    (exercised by allLeR_head / allLeR_empty below, both kernel-green). -/
def AllLeR : Term := prog{
  λ (w : Nat). λ (lo : Nat). λ (p : Nat). λ (l : List Nat).
    Π (k : Nat) → Le (S k) w → Le (nth (Add k lo) l) p }
def AllGtR : Term := prog{
  λ (w : Nat). λ (lo : Nat). λ (p : Nat). λ (l : List Nat).
    Π (k : Nat) → Le (S k) w → Le (S p) (nth (Add k lo) l) }

-- Head extraction: a width-(S w) AllLeR gives the bound at position lo (apply at
-- k=Z; Le (S Z)(S w) whnf's to ⊤, discharged by `unit`; add Z lo = lo).
def allLeR_head : Term := prog{
  λ (w : Nat). λ (lo : Nat). λ (p : Nat). λ (l : List Nat). λ (h : AllLeR (S w) lo p l).
    h Z unit }
def allLeR_head_ty : Term := prog{
  Π (w : Nat) → Π (lo : Nat) → Π (p : Nat) → Π (l : List Nat) →
    AllLeR (S w) lo p l → Le (nth lo l) p }
def allGtR_head : Term := prog{
  λ (w : Nat). λ (lo : Nat). λ (p : Nat). λ (l : List Nat). λ (h : AllGtR (S w) lo p l).
    h Z unit }
def allGtR_head_ty : Term := prog{
  Π (w : Nat) → Π (lo : Nat) → Π (p : Nat) → Π (l : List Nat) →
    AllGtR (S w) lo p l → Le (S p) (nth lo l) }

-- The empty range is vacuously bounded (Le (S k) Z = ⊥ ⇒ botElim).
def allLeR_empty : Term := prog{
  λ (lo : Nat). λ (p : Nat). λ (l : List Nat).
    λ (k : Nat). λ (hk : Le (S k) Z). botElim (Le (nth (Add k lo) l) p) hk }
def allLeR_empty_ty : Term := prog{
  Π (lo : Nat) → Π (p : Nat) → Π (l : List Nat) → AllLeR Z lo p l }
def allGtR_empty : Term := prog{
  λ (lo : Nat). λ (p : Nat). λ (l : List Nat).
    λ (k : Nat). λ (hk : Le (S k) Z). botElim (Le (S p) (nth (Add k lo) l)) hk }
def allGtR_empty_ty : Term := prog{
  Π (lo : Nat) → Π (p : Nat) → Π (l : List Nat) → AllGtR Z lo p l }

/-! ## Segment count — the multiset vehicle for perm-survival (§22, M22-c step 3)

    `segCount x lo w l` = occurrences of x in positions [lo, lo+w) of l, as the count
    over the take/drop segment (reuses count/take/drop; preservation cribs count_* +
    count_append + take_drop_id). This is the perm-invariant twin the positional
    AllLeR is bridged to: the sort permutes the segment (segCount preserved), so a
    positional bound over the segment survives the sort. Its preservation-under-the-
    model-functions and the model-function LOCALITY lemmas are the mechanical stratum. -/
def segCount : Term := prog{
  λ (x : Nat). λ (lo : Nat). λ (w : Nat). λ (l : List Nat).
    Count x (Take w (Drop lo l)) }
def segCount_ty : Term := prog{ Π (x : Nat) → Π (lo : Nat) → Π (w : Nat) → Π (l : List Nat) → Nat }

/-! ## Range sortedness (§22, M22-c step 4)

    SortedR w lo l: positions [lo, lo+w) are non-decreasing — for every adjacent pair
    (k, k+1) both inside the range (S(S k) ≤ w), nth(lo+k) ≤ nth(lo+k+1). Bounded-Π,
    same encoding as AllLeR/AllGtR (eliminate by application, construct by lambda;
    `add k lo` / `add (S k) lo` so k=0 reduces to nth lo / nth (S lo)). Width ≤ 1 is
    vacuously sorted. The glue lemma (SortedR left ∧ AllLeR left≤pivot ∧ AllGtR right>pivot
    ∧ SortedR right ⟹ SortedR whole) assembles on these; then sorted_sortRangeL. -/
def SortedR : Term := prog{
  λ (w : Nat). λ (lo : Nat). λ (l : List Nat).
    Π (k : Nat) → Le (S (S k)) w → Le (nth (Add k lo) l) (nth (Add (S k) lo) l) }

-- Head adjacent-bound from a width-(S (S w)) SortedR (apply at k=Z).
def sortedR_head : Term := prog{
  λ (w : Nat). λ (lo : Nat). λ (l : List Nat). λ (h : SortedR (S (S w)) lo l).
    h Z unit }
def sortedR_head_ty : Term := prog{
  Π (w : Nat) → Π (lo : Nat) → Π (l : List Nat) →
    SortedR (S (S w)) lo l → Le (nth lo l) (nth (S lo) l) }

-- Width 0 and width 1 are vacuously sorted (Le (S (S k)) (Z / S Z) = ⊥ ⇒ botElim).
def sortedR_zero : Term := prog{
  λ (lo : Nat). λ (l : List Nat).
    λ (k : Nat). λ (hk : Le (S (S k)) Z). botElim (Le (nth (Add k lo) l) (nth (Add (S k) lo) l)) hk }
def sortedR_zero_ty : Term := prog{
  Π (lo : Nat) → Π (l : List Nat) → SortedR Z lo l }
def sortedR_one : Term := prog{
  λ (lo : Nat). λ (l : List Nat).
    λ (k : Nat). λ (hk : Le (S (S k)) (S Z)). botElim (Le (nth (Add k lo) l) (nth (Add (S k) lo) l)) hk }
def sortedR_one_ty : Term := prog{
  Π (lo : Nat) → Π (l : List Nat) → SortedR (S Z) lo l }

/-! ## leb ↔ Le bridges (§22, M22-c) — the Bool-comparison / order-proposition link

    The model functions branch on `leb` (a Bool); the predicates carry `Le` (a
    proposition). These bridge the two — needed both for the partition INVARIANT
    (the scan's leb tests become AllLeR/AllGtR facts) and the GLUE (its k-vs-i
    trichotomy is a leb case-split whose branches yield the Le adjacency facts).
    `leb` and `Le` share the same double recursion, so each bridge is a double
    induction with a Bool-DISCRIMINATE at the mismatched base (boolFT/boolTF:
    False ≠ True, by transporting `unit` along the false equation to `⊥`). -/
def boolFT : Term := prog{
  λ (h : Id Bool False True).
    j Bool False (λ (y' : Bool). λ (hh : Id Bool False y'). elim y' return (λ (z : Bool). Type) { True => Bot, False => Unit })
      unit True h }
def boolFT_ty : Term := prog{ Id Bool False True → Bot }
def boolTF : Term := prog{
  λ (h : Id Bool True False).
    j Bool True (λ (y' : Bool). λ (hh : Id Bool True y'). elim y' return (λ (z : Bool). Type) { True => Unit, False => Bot })
      unit False h }
def boolTF_ty : Term := prog{ Id Bool True False → Bot }

def leb_true_le : Term := prog{
  λ (a : Nat).
    elim a return (λ (az : Nat). Π (b : Nat) → Id Bool (Leb az b) True → Le az b) {
      Z => λ (b : Nat). λ (h : Id Bool (Leb Z b) True). unit,
      S (a') ih => λ (b : Nat).
        elim b return (λ (bz : Nat). Id Bool (Leb (S a') bz) True → Le (S a') bz) {
          Z => λ (h : Id Bool (Leb (S a') Z) True). botElim (Le (S a') Z) (boolFT h),
          S (b') ihb => λ (h : Id Bool (Leb (S a') (S b')) True). ih b' h } } }
def leb_true_le_ty : Term := prog{ Π (a : Nat) → Π (b : Nat) → Id Bool (Leb a b) True → Le a b }

def leb_false_gt : Term := prog{
  λ (a : Nat).
    elim a return (λ (az : Nat). Π (b : Nat) → Id Bool (Leb az b) False → Le (S b) az) {
      Z => λ (b : Nat). λ (h : Id Bool (Leb Z b) False). botElim (Le (S b) Z) (boolTF h),
      S (a') ih => λ (b : Nat).
        elim b return (λ (bz : Nat). Id Bool (Leb (S a') bz) False → Le (S bz) (S a')) {
          Z => λ (h : Id Bool (Leb (S a') Z) False). unit,
          S (b') ihb => λ (h : Id Bool (Leb (S a') (S b')) False). ih b' h } } }
def leb_false_gt_ty : Term := prog{ Π (a : Nat) → Π (b : Nat) → Id Bool (Leb a b) False → Le (S b) a }

-- Nat antisymmetry (Le a b → Le b a → a = b) — the glue derives its boundary equality
-- (`S k = i` at the last-left/pivot pair) from the two-sided Le bounds a leb-split
-- yields. Double induction; mixed-parity bases are ⊥, equal-parity step is id_congr S.
def le_antisym : Term := prog{
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
            id_congr Nat Nat (λ (n : Nat). S n) a' b' (ih b' h1 h2) } } }
def le_antisym_ty : Term := prog{ Π (a : Nat) → Π (b : Nat) → Le a b → Le b a → Id Nat a b }

/-! ## AllLeR growth/transport helpers — the region-invariant toolkit (§22, M22-c step 2)

    The partition-invariant proofs thread an AllLeR precondition that GROWS each scan
    step. `allLeR_extend_far` appends the newly-tested ≤-element at the far end — the
    only place the `m<w` vs `m=w` decision is needed, discharged by leb (remember
    scrutinee) + leb_true_le/leb_false_gt + le_antisym. `allLeR_extend_lo` prepends the
    pivot at position lo, absorbing the index-first offset shift `add m (S lo) = add (S
    m) lo` (add_succ). `allLeR_cong` transports an AllLeR across a pointwise nth-equality
    (fed by the swap-locality lemmas). `add_swap_succ` bridges index-first `add a (S b)`
    to `add b (S a)` — the recurring predicate↔model add-order glue. -/

def allLeR_extend_far : Term := prog{
  λ (w : Nat). λ (lo : Nat). λ (p : Nat). λ (l : List Nat).
    λ (h : AllLeR w lo p l). λ (hnew : Le (nth (Add w lo) l) p).
    λ (m : Nat).
      elim (Leb (S m) w) return (λ (b : Bool). Id Bool (Leb (S m) w) b → Le (S m) (S w) → Le (nth (Add m lo) l) p) {
        True => λ (e : Id Bool (Leb (S m) w) True). λ (hm : Le (S m) (S w)). h m (leb_true_le (S m) w e),
        False => λ (e : Id Bool (Leb (S m) w) False). λ (hm : Le (S m) (S w)).
          le_rw_l p (nth (Add w lo) l) (nth (Add m lo) l)
            (id_congr Nat Nat (λ (q : Nat). nth q l) (Add w lo) (Add m lo)
              (id_congr Nat Nat (λ (z : Nat). Add z lo) w m (id_sym Nat m w (le_antisym m w hm (leb_false_gt (S m) w e)))))
            hnew
      } Refl }
def allLeR_extend_far_ty : Term := prog{
  Π (w : Nat) → Π (lo : Nat) → Π (p : Nat) → Π (l : List Nat) →
    AllLeR w lo p l → Le (nth (Add w lo) l) p → AllLeR (S w) lo p l }

def allLeR_extend_lo : Term := prog{
  λ (w : Nat). λ (lo : Nat). λ (p : Nat). λ (l : List Nat).
    λ (h0 : Le (nth lo l) p). λ (h : AllLeR w (S lo) p l).
    λ (m : Nat).
      elim m return (λ (mz : Nat). Le (S mz) (S w) → Le (nth (Add mz lo) l) p) {
        Z => λ (hm : Le (S Z) (S w)). h0,
        S (m') mih => λ (hm : Le (S (S m')) (S w)).
          le_rw_l p (nth (Add m' (S lo)) l) (nth (Add (S m') lo) l)
            (id_congr Nat Nat (λ (q : Nat). nth q l) (Add m' (S lo)) (Add (S m') lo) (add_succ m' lo))
            (h m' hm) } }
def allLeR_extend_lo_ty : Term := prog{
  Π (w : Nat) → Π (lo : Nat) → Π (p : Nat) → Π (l : List Nat) →
    Le (nth lo l) p → AllLeR w (S lo) p l → AllLeR (S w) lo p l }

def allLeR_cong : Term := prog{
  λ (w : Nat). λ (off : Nat). λ (p : Nat). λ (l : List Nat). λ (l' : List Nat).
    λ (heq : Π (m : Nat) → Le (S m) w → Id Nat (nth (Add m off) l') (nth (Add m off) l)).
    λ (h : AllLeR w off p l).
    λ (m : Nat). λ (hm : Le (S m) w).
      le_rw_l p (nth (Add m off) l) (nth (Add m off) l')
        (id_sym Nat (nth (Add m off) l') (nth (Add m off) l) (heq m hm))
        (h m hm) }
def allLeR_cong_ty : Term := prog{
  Π (w : Nat) → Π (off : Nat) → Π (p : Nat) → Π (l : List Nat) → Π (l' : List Nat) →
    (Π (m : Nat) → Le (S m) w → Id Nat (nth (Add m off) l') (nth (Add m off) l)) →
    AllLeR w off p l → AllLeR w off p l' }

def add_swap_succ : Term := prog{
  λ (a : Nat). λ (b : Nat).
    id_trans Nat (Add a (S b)) (S (Add a b)) (Add b (S a))
      (add_succ a b)
      (id_trans Nat (S (Add a b)) (S (Add b a)) (Add b (S a))
        (id_congr Nat Nat (λ (z : Nat). S z) (Add a b) (Add b a) (add_comm a b))
        (id_sym Nat (Add b (S a)) (S (Add b a)) (add_succ b a))) }
def add_swap_succ_ty : Term := prog{ Π (a : Nat) → Π (b : Nat) → Id Nat (Add a (S b)) (Add b (S a)) }

-- Left cancellation (Le (add a b)(add a c) → Le b c) — the glue's pivot-right case
-- derives g ≥ 1 (Le (S Z) g) from the range bound Le (S i)(add i g) by cancelling i
-- (after bridging S i = add i (S Z) via add_succ/add_zero). Induction on a.
def le_add_cancel_l : Term := prog{
  λ (a : Nat).
    elim a return (λ (az : Nat). Π (b : Nat) → Π (c : Nat) → Le (Add az b) (Add az c) → Le b c) {
      Z => λ (b : Nat). λ (c : Nat). λ (h : Le (Add Z b) (Add Z c)). h,
      S (a') ih => λ (b : Nat). λ (c : Nat). λ (h : Le (Add (S a') b) (Add (S a') c)). ih b c h } }
def le_add_cancel_l_ty : Term := prog{
  Π (a : Nat) → Π (b : Nat) → Π (c : Nat) → Le (Add a b) (Add a c) → Le b c }
/-! ## `nth`-under-`swapL` locality — the positional stratum (§22, M22-c)

    Where `count_swapL` says the swap preserves the MULTISET, these say WHERE each
    position lands, which the segCount/locality argument (and the sortedness half)
    reads directly. `swapL i j` (with the smaller index first) touches ONLY
    positions `i` and `j`: position `i` receives old `j` (`nth_swapL_lo`), position
    `j` receives old `i` (`nth_swapL_hi`), and every position `k` OUTSIDE `{i,j}` is
    unchanged. The "outside" atom is split into the two directions the range scan's
    locality actually needs — `k < i` (`nth_swapL_lt`, below both indices since
    `i ≤ j`) and `k > j` (`nth_swapL_gt`, above both) — each stated with a SINGLE
    honest `Le` bound, so a caller reasoning about a below-range or above-range
    position cites exactly one of them. The middle band `i < k < j` is also
    untouched but is not needed downstream, so it is left unstated (it would need
    the two-sided bound `Le (S i) k → Le (S k) j`).

    BOUNDS (verified computationally, minimal):
    - `nth_swapL_lt` needs ONLY `Le (S k) i` (the `l = Nil` and `j = Z` leaves are
      `Refl`, not bound-discharged — off the end both sides degrade to the same
      stuck `nth k Nil`).
    - `nth_swapL_gt` needs ONLY `Le (S j) k` (below-`j` positions in the set-branch
      are handled by `nth_set_gt`).
    - `nth_swapL_lo` needs ONLY `Le (S i) j` — NO length bound: off the end the swap
      writes `nth j l = Z` at `i`, so both sides read `Z` consistently. The `Nil`
      leaves case `j` (so the stuck `nth j Nil` reduces to `Z` on both sides).
    - `nth_swapL_hi` needs BOTH `Le (S i) j` and `Le (S j) (len l)` — the base case
      reads `nth j (set j x xs) = x` (`nth_set_same`), which is FALSE off the end, so
      the length bound is load-bearing (discharges the `Nil` leaf as `botElim` and
      feeds `nth_set_same`).

    Two `set` helpers underneath: `nth_set_gt` (`nth` past the written index is
    unchanged, bound `Le (S j) k`) and `nth_set_same` (`nth k (set k v l) = v` in
    range, bound `Le (S k) (len l)`). -/

-- `nth k (set j v l) = nth k l` for k strictly above the written index j.
def nth_set_gt : Term := prog{
  λ (v : Nat). λ (j : Nat).
    elim j return (λ (jz : Nat). Π (k : Nat) → Π (l : List Nat) → Le (S jz) k → Id Nat (nth k (set jz v l)) (nth k l)) {
      Z => λ (k : Nat). λ (l : List Nat). λ (h : Le (S Z) k).
        elim k return (λ (kz : Nat). Le (S Z) kz → Id Nat (nth kz (set Z v l)) (nth kz l)) {
          Z => λ (h0 : Le (S Z) Z). botElim (Id Nat (nth Z (set Z v l)) (nth Z l)) h0,
          S (k') kih => λ (h0 : Le (S Z) (S k')).
            elim l return (λ (lz : List Nat). Id Nat (nth (S k') (set Z v lz)) (nth (S k') lz)) {
              Nil => Refl,
              Cons (hh) (tt) ihl => Refl } } h,
      S (j') ih => λ (k : Nat). λ (l : List Nat). λ (h : Le (S (S j')) k).
        elim k return (λ (kz : Nat). Le (S (S j')) kz → Id Nat (nth kz (set (S j') v l)) (nth kz l)) {
          Z => λ (h0 : Le (S (S j')) Z). botElim (Id Nat (nth Z (set (S j') v l)) (nth Z l)) h0,
          S (k') kih => λ (h0 : Le (S (S j')) (S k')).
            elim l return (λ (lz : List Nat). Id Nat (nth (S k') (set (S j') v lz)) (nth (S k') lz)) {
              Nil => Refl,
              Cons (hh) (tt) ihl => ih k' tt h0 } } h } }
def nth_set_gt_ty : Term := prog{
  Π (v : Nat) → Π (j : Nat) → Π (k : Nat) → Π (l : List Nat) →
    Le (S j) k → Id Nat (nth k (set j v l)) (nth k l) }

-- `nth k (set k v l) = v` when k is in range (off the end set no-ops, giving Z ≠ v).
def nth_set_same : Term := prog{
  λ (v : Nat). λ (k : Nat).
    elim k return (λ (kz : Nat). Π (l : List Nat) → Le (S kz) (Len l) → Id Nat (nth kz (set kz v l)) v) {
      Z => λ (l : List Nat).
        elim l return (λ (lz : List Nat). Le (S Z) (Len lz) → Id Nat (nth Z (set Z v lz)) v) {
          Nil => λ (h : Le (S Z) (Len Nil)). botElim (Id Nat (nth Z (set Z v Nil)) v) h,
          Cons (hh) (tt) ihl => λ (h : Le (S Z) (Len (Cons hh tt))). Refl },
      S (k') ih => λ (l : List Nat).
        elim l return (λ (lz : List Nat). Le (S (S k')) (Len lz) → Id Nat (nth (S k') (set (S k') v lz)) v) {
          Nil => λ (h : Le (S (S k')) (Len Nil)). botElim (Id Nat (nth (S k') (set (S k') v Nil)) v) h,
          Cons (hh) (tt) ihl => λ (h : Le (S (S k')) (Len (Cons hh tt))). ih tt h } } }
def nth_set_same_ty : Term := prog{
  Π (v : Nat) → Π (k : Nat) → Π (l : List Nat) →
    Le (S k) (Len l) → Id Nat (nth k (set k v l)) v }

-- Locality below the swap: positions `k < i` are untouched by `swapL i j`. Induct
-- on i (mirroring swapL); i = Z is vacuous (Le (S k) Z = ⊥); the recursive leaf is
-- the IH under `Cons x ·`, the j = Z / head leaves are Refl.
def nth_swapL_lt : Term := prog{
  λ (i : Nat).
    elim i return (λ (iz : Nat). Π (j : Nat) → Π (k : Nat) → Π (l : List Nat) → Le (S k) iz → Id Nat (nth k (swapL iz j l)) (nth k l)) {
      Z => λ (j : Nat). λ (k : Nat). λ (l : List Nat). λ (h : Le (S k) Z).
        botElim (Id Nat (nth k (swapL Z j l)) (nth k l)) h,
      S (i') ih => λ (j : Nat). λ (k : Nat). λ (l : List Nat). λ (h : Le (S k) (S i')).
        elim l return (λ (lz : List Nat). Id Nat (nth k (swapL (S i') j lz)) (nth k lz)) {
          Nil => Refl,
          Cons (x) (xs) ihl =>
            elim j return (λ (jz : Nat). Id Nat (nth k (swapL (S i') jz (Cons x xs))) (nth k (Cons x xs))) {
              Z => Refl,
              S (j') jih =>
                elim k return (λ (kz : Nat). Le (S kz) (S i') → Id Nat (nth kz (Cons x (swapL i' j' xs))) (nth kz (Cons x xs))) {
                  Z => λ (h0 : Le (S Z) (S i')). Refl,
                  S (k') kih => λ (h0 : Le (S (S k')) (S i')). ih j' k' xs h0 } h } } } }
def nth_swapL_lt_ty : Term := prog{
  Π (i : Nat) → Π (j : Nat) → Π (k : Nat) → Π (l : List Nat) →
    Le (S k) i → Id Nat (nth k (swapL i j l)) (nth k l) }

-- Locality above the swap: positions `k > j` are untouched by `swapL i j`. Induct
-- on i; the i = Z / j = S j' leaf floats through the set-branch via `nth_set_gt`,
-- the i = S i' / j = S j' leaf is the IH, the j = Z / Nil leaves are Refl.
def nth_swapL_gt : Term := prog{
  λ (i : Nat).
    elim i return (λ (iz : Nat). Π (j : Nat) → Π (k : Nat) → Π (l : List Nat) → Le (S j) k → Id Nat (nth k (swapL iz j l)) (nth k l)) {
      Z => λ (j : Nat). λ (k : Nat). λ (l : List Nat). λ (h : Le (S j) k).
        elim l return (λ (lz : List Nat). Id Nat (nth k (swapL Z j lz)) (nth k lz)) {
          Nil => Refl,
          Cons (x) (xs) ihl =>
            elim j return (λ (jz : Nat). Le (S jz) k → Id Nat (nth k (swapL Z jz (Cons x xs))) (nth k (Cons x xs))) {
              Z => λ (h0 : Le (S Z) k). Refl,
              S (j') jih => λ (h0 : Le (S (S j')) k).
                elim k return (λ (kz : Nat). Le (S (S j')) kz → Id Nat (nth kz (Cons (nth j' xs) (set j' x xs))) (nth kz (Cons x xs))) {
                  Z => λ (h1 : Le (S (S j')) Z). botElim (Id Nat (nth Z (Cons (nth j' xs) (set j' x xs))) (nth Z (Cons x xs))) h1,
                  S (k') kih => λ (h1 : Le (S (S j')) (S k')). nth_set_gt x j' k' xs h1 } h0 } h },
      S (i') ih => λ (j : Nat). λ (k : Nat). λ (l : List Nat). λ (h : Le (S j) k).
        elim l return (λ (lz : List Nat). Id Nat (nth k (swapL (S i') j lz)) (nth k lz)) {
          Nil => Refl,
          Cons (x) (xs) ihl =>
            elim j return (λ (jz : Nat). Le (S jz) k → Id Nat (nth k (swapL (S i') jz (Cons x xs))) (nth k (Cons x xs))) {
              Z => λ (h0 : Le (S Z) k). Refl,
              S (j') jih => λ (h0 : Le (S (S j')) k).
                elim k return (λ (kz : Nat). Le (S (S j')) kz → Id Nat (nth kz (Cons x (swapL i' j' xs))) (nth kz (Cons x xs))) {
                  Z => λ (h1 : Le (S (S j')) Z). botElim (Id Nat (nth Z (Cons x (swapL i' j' xs))) (nth Z (Cons x xs))) h1,
                  S (k') kih => λ (h1 : Le (S (S j')) (S k')). ih j' k' xs h1 } h0 } h } } }
def nth_swapL_gt_ty : Term := prog{
  Π (i : Nat) → Π (j : Nat) → Π (k : Nat) → Π (l : List Nat) →
    Le (S j) k → Id Nat (nth k (swapL i j l)) (nth k l) }

-- The lower endpoint: position i of `swapL i j l` reads old position j. Induct on
-- i; the recursive leaf is the IH under `Cons x ·`. NO length bound — off the end
-- the swap writes `nth j l = Z` at i, so both sides read Z consistently; the Nil
-- leaves case j so the stuck `nth j Nil` reduces to Z on both sides, and the j = Z
-- leaf (impossible with i ≥ 1) is the sole botElim, discharged by `Le (S i) j`.
def nth_swapL_lo : Term := prog{
  λ (i : Nat).
    elim i return (λ (iz : Nat). Π (j : Nat) → Π (l : List Nat) → Le (S iz) j → Id Nat (nth iz (swapL iz j l)) (nth j l)) {
      Z => λ (j : Nat). λ (l : List Nat). λ (h : Le (S Z) j).
        elim l return (λ (lz : List Nat). Id Nat (nth Z (swapL Z j lz)) (nth j lz)) {
          Nil => elim j return (λ (jz : Nat). Id Nat (nth Z (swapL Z jz Nil)) (nth jz Nil)) {
            Z => Refl, S (j') jih => Refl },
          Cons (x) (xs) ihl =>
            elim j return (λ (jz : Nat). Le (S Z) jz → Id Nat (nth Z (swapL Z jz (Cons x xs))) (nth jz (Cons x xs))) {
              Z => λ (h0 : Le (S Z) Z). botElim (Id Nat (nth Z (swapL Z Z (Cons x xs))) (nth Z (Cons x xs))) h0,
              S (j') jih => λ (h0 : Le (S Z) (S j')). Refl } h },
      S (i') ih => λ (j : Nat). λ (l : List Nat). λ (h : Le (S (S i')) j).
        elim l return (λ (lz : List Nat). Id Nat (nth (S i') (swapL (S i') j lz)) (nth j lz)) {
          Nil => elim j return (λ (jz : Nat). Id Nat (nth (S i') (swapL (S i') jz Nil)) (nth jz Nil)) {
            Z => Refl, S (j') jih => Refl },
          Cons (x) (xs) ihl =>
            elim j return (λ (jz : Nat). Le (S (S i')) jz → Id Nat (nth (S i') (swapL (S i') jz (Cons x xs))) (nth jz (Cons x xs))) {
              Z => λ (h0 : Le (S (S i')) Z). botElim (Id Nat (nth (S i') (swapL (S i') Z (Cons x xs))) (nth Z (Cons x xs))) h0,
              S (j') jih => λ (h0 : Le (S (S i')) (S j')). ih j' xs h0 } h } } }
def nth_swapL_lo_ty : Term := prog{
  Π (i : Nat) → Π (j : Nat) → Π (l : List Nat) →
    Le (S i) j → Id Nat (nth i (swapL i j l)) (nth j l) }

-- The upper endpoint: position j of `swapL i j l` reads old position i. Induct on
-- i; the base (i = Z) reads `nth j (set j x xs) = x` via `nth_set_same`, so the
-- length bound `Le (S j) (len l)` is load-bearing here (botElims the Nil leaf and
-- feeds nth_set_same) — UNLIKE _lo. The recursive leaf is the IH under `Cons x ·`,
-- threading both bounds; the j = Z leaf is botElim by `Le (S i) j`.
def nth_swapL_hi : Term := prog{
  λ (i : Nat).
    elim i return (λ (iz : Nat). Π (j : Nat) → Π (l : List Nat) → Le (S iz) j → Le (S j) (Len l) → Id Nat (nth j (swapL iz j l)) (nth iz l)) {
      Z => λ (j : Nat). λ (l : List Nat). λ (h1 : Le (S Z) j). λ (h2 : Le (S j) (Len l)).
        elim l return (λ (lz : List Nat). Le (S j) (Len lz) → Id Nat (nth j (swapL Z j lz)) (nth Z lz)) {
          Nil => λ (a2 : Le (S j) (Len Nil)).
            botElim (Id Nat (nth j (swapL Z j Nil)) (nth Z Nil)) a2,
          Cons (x) (xs) ihl => λ (a2 : Le (S j) (Len (Cons x xs))).
            elim j return (λ (jz : Nat). Le (S Z) jz → Le (S jz) (Len (Cons x xs)) → Id Nat (nth jz (swapL Z jz (Cons x xs))) (nth Z (Cons x xs))) {
              Z => λ (b1 : Le (S Z) Z). λ (b2 : Le (S Z) (Len (Cons x xs))).
                botElim (Id Nat (nth Z (swapL Z Z (Cons x xs))) (nth Z (Cons x xs))) b1,
              S (j') jih => λ (b1 : Le (S Z) (S j')). λ (b2 : Le (S (S j')) (Len (Cons x xs))).
                nth_set_same x j' xs b2 } h1 a2 } h2,
      S (i') ih => λ (j : Nat). λ (l : List Nat). λ (h1 : Le (S (S i')) j). λ (h2 : Le (S j) (Len l)).
        elim l return (λ (lz : List Nat). Le (S j) (Len lz) → Id Nat (nth j (swapL (S i') j lz)) (nth (S i') lz)) {
          Nil => λ (a2 : Le (S j) (Len Nil)).
            botElim (Id Nat (nth j (swapL (S i') j Nil)) (nth (S i') Nil)) a2,
          Cons (x) (xs) ihl => λ (a2 : Le (S j) (Len (Cons x xs))).
            elim j return (λ (jz : Nat). Le (S (S i')) jz → Le (S jz) (Len (Cons x xs)) → Id Nat (nth jz (swapL (S i') jz (Cons x xs))) (nth (S i') (Cons x xs))) {
              Z => λ (b1 : Le (S (S i')) Z). λ (b2 : Le (S Z) (Len (Cons x xs))).
                botElim (Id Nat (nth Z (swapL (S i') Z (Cons x xs))) (nth (S i') (Cons x xs))) b1,
              S (j') jih => λ (b1 : Le (S (S i')) (S j')). λ (b2 : Le (S (S j')) (Len (Cons x xs))).
                ih j' xs b1 b2 } h1 a2 } h2 } }
def nth_swapL_hi_ty : Term := prog{
  Π (i : Nat) → Π (j : Nat) → Π (l : List Nat) →
    Le (S i) j → Le (S j) (Len l) → Id Nat (nth j (swapL i j l)) (nth i l) }

-- `nth k (set j v l) = nth k l` for k strictly BELOW the written index j (mirror of
-- nth_set_gt). The below-index companion the partition-invariant base case needs.
def nth_set_lt : Term := prog{
  λ (v : Nat). λ (j : Nat).
    elim j return (λ (jz : Nat). Π (k : Nat) → Π (l : List Nat) → Le (S k) jz → Id Nat (nth k (set jz v l)) (nth k l)) {
      Z => λ (k : Nat). λ (l : List Nat). λ (h : Le (S k) Z). botElim (Id Nat (nth k (set Z v l)) (nth k l)) h,
      S (j') ih => λ (k : Nat). λ (l : List Nat). λ (h : Le (S k) (S j')).
        elim k return (λ (kz : Nat). Le (S kz) (S j') → Id Nat (nth kz (set (S j') v l)) (nth kz l)) {
          Z => λ (h0 : Le (S Z) (S j')).
            elim l return (λ (lz : List Nat). Id Nat (nth Z (set (S j') v lz)) (nth Z lz)) {
              Nil => Refl,
              Cons (hh) (tt) ihl => Refl },
          S (k') kih => λ (h0 : Le (S (S k')) (S j')).
            elim l return (λ (lz : List Nat). Id Nat (nth (S k') (set (S j') v lz)) (nth (S k') lz)) {
              Nil => Refl,
              Cons (hh) (tt) ihl => ih k' tt h0 } } h } }
def nth_set_lt_ty : Term := prog{
  Π (v : Nat) → Π (j : Nat) → Π (k : Nat) → Π (l : List Nat) →
    Le (S k) j → Id Nat (nth k (set j v l)) (nth k l) }

-- The MIDDLE band left unstated in Step A: positions strictly between i and j are
-- untouched by `swapL i j` (two-sided bound). Induction on i mirroring swapL; the
-- i=Z base floats through the set-branch via nth_set_lt, the recursive leaf is the IH.
def nth_swapL_mid : Term := prog{
  λ (i : Nat).
    elim i return (λ (iz : Nat). Π (j : Nat) → Π (k : Nat) → Π (l : List Nat) → Le (S iz) k → Le (S k) j → Id Nat (nth k (swapL iz j l)) (nth k l)) {
      Z => λ (j : Nat). λ (k : Nat). λ (l : List Nat). λ (hik : Le (S Z) k). λ (hkj : Le (S k) j).
        elim l return (λ (lz : List Nat). Id Nat (nth k (swapL Z j lz)) (nth k lz)) {
          Nil => Refl,
          Cons (x) (xs) ihl =>
            elim j return (λ (jz : Nat). Le (S k) jz → Id Nat (nth k (swapL Z jz (Cons x xs))) (nth k (Cons x xs))) {
              Z => λ (hkj0 : Le (S k) Z). botElim (Id Nat (nth k (swapL Z Z (Cons x xs))) (nth k (Cons x xs))) hkj0,
              S (j') jih => λ (hkj0 : Le (S k) (S j')).
                elim k return (λ (kz : Nat). Le (S Z) kz → Le (S kz) (S j') → Id Nat (nth kz (Cons (nth j' xs) (set j' x xs))) (nth kz (Cons x xs))) {
                  Z => λ (hik1 : Le (S Z) Z). λ (hkj1 : Le (S Z) (S j')). botElim (Id Nat (nth Z (Cons (nth j' xs) (set j' x xs))) (nth Z (Cons x xs))) hik1,
                  S (k') kih => λ (hik1 : Le (S Z) (S k')). λ (hkj1 : Le (S (S k')) (S j')).
                    nth_set_lt x j' k' xs hkj1 } hik hkj0 } hkj },
      S (i') ih => λ (j : Nat). λ (k : Nat). λ (l : List Nat). λ (hik : Le (S (S i')) k). λ (hkj : Le (S k) j).
        elim l return (λ (lz : List Nat). Id Nat (nth k (swapL (S i') j lz)) (nth k lz)) {
          Nil => Refl,
          Cons (x) (xs) ihl =>
            elim j return (λ (jz : Nat). Le (S k) jz → Id Nat (nth k (swapL (S i') jz (Cons x xs))) (nth k (Cons x xs))) {
              Z => λ (hkj0 : Le (S k) Z). botElim (Id Nat (nth k (swapL (S i') Z (Cons x xs))) (nth k (Cons x xs))) hkj0,
              S (j') jih => λ (hkj0 : Le (S k) (S j')).
                elim k return (λ (kz : Nat). Le (S (S i')) kz → Le (S kz) (S j') → Id Nat (nth kz (Cons x (swapL i' j' xs))) (nth kz (Cons x xs))) {
                  Z => λ (hik1 : Le (S (S i')) Z). λ (hkj1 : Le (S Z) (S j')). botElim (Id Nat (nth Z (Cons x (swapL i' j' xs))) (nth Z (Cons x xs))) hik1,
                  S (k') kih => λ (hik1 : Le (S (S i')) (S k')). λ (hkj1 : Le (S (S k')) (S j')).
                    ih j' k' xs hik1 hkj1 } hik hkj0 } hkj } } }
def nth_swapL_mid_ty : Term := prog{
  Π (i : Nat) → Π (j : Nat) → Π (k : Nat) → Π (l : List Nat) →
    Le (S i) k → Le (S k) j → Id Nat (nth k (swapL i j l)) (nth k l) }

/-! ## `nth`-under-scan/partition LOCALITY — positions outside the range unchanged (§22)

    The range scan `partScanRangeL pivot lo k i g` only ever swaps positions inside
    `[lo, lo + (k+i+g)]` (base places the pivot at `swapL lo (lo+i)`; each step swaps
    at `lo+1+i` ↔ `lo+1+i+g`, all ≥ lo, ≤ the top). So a query position OUTSIDE that
    band is untouched, split (as with the swap crux) into the two directions the
    quicksort recursion consumes:

    - `_lt` : positions `j < lo` (below the range). Bound `Le (S j) lo`, INVARIANT
      across the recursion (bound outside the k-elim, no transport) — each scan swap
      is discharged by `nth_swapL_lt` since j < lo ≤ every swap's smaller index.
    - `_ge` : positions `q ≥ lo+1+(k+i+g)` (at/above the scanned top). Bound
      `Le (add lo (S (add k (add i g)))) q` — the SAME shifting invariant
      `count_partScanRangeL` threads, but on a POSITION `q` instead of `len l`, so it
      transports by the identical `hshift` congruences and, crucially, needs NO
      `len_swapL` step (q is list-independent). Each swap discharged by `nth_swapL_gt`.

    The `partitionRangeL` wrappers pick the pivot then defer to the scan (the `_ge`
    bound becomes the clean `Le (add lo cnt) q`, one `add_zero` nudge as in
    `count_partitionRangeL`). Together `_lt` (j < lo) and `_ge` (q ≥ lo+cnt) cover
    everything OUTSIDE the operated range `[lo, lo+cnt)`. -/

-- Below-lo locality of the range scan. Bound `Le (S j) lo` is invariant (bound
-- outside the k-elim); each swap discharged by nth_swapL_lt (j < lo ≤ swap index).
def nth_partScanRangeL_lt : Term := prog{
  λ (pivot : Nat). λ (lo : Nat). λ (j : Nat). λ (hlt : Le (S j) lo). λ (k : Nat).
    elim k return (λ (kz : Nat). Π (i : Nat) → Π (g : Nat) → Π (l : List Nat) → Id Nat (nth j (partScanRangeL pivot lo kz i g l)) (nth j l)) {
      Z => λ (i : Nat). λ (g : Nat). λ (l : List Nat).
        elim i return (λ (iz : Nat). Id Nat (nth j (elim iz return (λ (iy : Nat). List Nat) { Z => l, S (i') iih => swapL lo (Add lo (S i')) l })) (nth j l)) {
          Z => Refl,
          S (i') iih => nth_swapL_lt lo (Add lo (S i')) j l hlt },
      S (k') ih => λ (i : Nat). λ (g : Nat). λ (l : List Nat).
        elim (Leb (nth (Add lo (S (Add i g))) l) pivot)
          return (λ (w : Bool). Id Nat (nth j (elim w return (λ (ww : Bool). List Nat) {
              True => elim g return (λ (gz : Nat). List Nat) {
                Z => partScanRangeL pivot lo k' (S i) Z l,
                S (g') gih => partScanRangeL pivot lo k' (S i) (S g') (swapL (Add lo (S i)) (Add lo (S (Add i g))) l) },
              False => partScanRangeL pivot lo k' i (S g) l })) (nth j l)) {
          True => elim g return (λ (gz : Nat). Id Nat (nth j (elim gz return (λ (gy : Nat). List Nat) {
                    Z => partScanRangeL pivot lo k' (S i) Z l,
                    S (g') gih => partScanRangeL pivot lo k' (S i) (S g') (swapL (Add lo (S i)) (Add lo (S (Add i g))) l) })) (nth j l)) {
            Z => ih (S i) Z l,
            S (g') gih => id_trans Nat
                   (nth j (partScanRangeL pivot lo k' (S i) (S g') (swapL (Add lo (S i)) (Add lo (S (Add i g))) l)))
                   (nth j (swapL (Add lo (S i)) (Add lo (S (Add i g))) l))
                   (nth j l)
                   (ih (S i) (S g') (swapL (Add lo (S i)) (Add lo (S (Add i g))) l))
                   (nth_swapL_lt (Add lo (S i)) (Add lo (S (Add i g))) j l
                     (le_trans (S j) lo (Add lo (S i)) hlt (le_add lo (S i))))
          },
          False => ih i (S g) l
        }
    } }
def nth_partScanRangeL_lt_ty : Term := prog{
  Π (pivot : Nat) → Π (lo : Nat) → Π (j : Nat) → Le (S j) lo → Π (k : Nat) → Π (i : Nat) → Π (g : Nat) → Π (l : List Nat) →
    Id Nat (nth j (partScanRangeL pivot lo k i g l)) (nth j l) }

-- At/above-top locality of the range scan. Same threaded invariant as
-- count_partScanRangeL but on position q, so hshift transports apply and NO
-- len_swapL is needed; each swap discharged by nth_swapL_gt.
def nth_partScanRangeL_ge : Term := prog{
  λ (pivot : Nat). λ (lo : Nat). λ (q : Nat). λ (k : Nat).
    elim k return (λ (kz : Nat). Π (i : Nat) → Π (g : Nat) → Π (l : List Nat) →
        Le (Add lo (S (Add kz (Add i g)))) q →
        Id Nat (nth q (partScanRangeL pivot lo kz i g l)) (nth q l)) {
      Z => λ (i : Nat). λ (g : Nat). λ (l : List Nat).
        elim i return (λ (iz : Nat).
            Le (Add lo (S (Add Z (Add iz g)))) q →
            Id Nat (nth q (elim iz return (λ (iy : Nat). List Nat) {
                Z => l, S (i') iih => swapL lo (Add lo (S i')) l })) (nth q l)) {
          Z => λ (hle : Le (Add lo (S (Add Z (Add Z g)))) q). Refl,
          S (i') iih => λ (hle : Le (Add lo (S (Add Z (Add (S i') g)))) q).
            nth_swapL_gt lo (Add lo (S i')) q l
              (le_trans (S (Add lo (S i'))) (Add lo (S (S (Add i' g)))) q
                (le_rw_l (Add lo (S (S (Add i' g)))) (Add lo (S (S i'))) (S (Add lo (S i')))
                  (add_succ lo (S i'))
                  (le_add_mono_l lo (S (S i')) (S (S (Add i' g))) (le_add i' g)))
                hle)
        },
      S (k') ih => λ (i : Nat). λ (g : Nat). λ (l : List Nat).
        λ (hle : Le (Add lo (S (Add (S k') (Add i g)))) q).
        elim (Leb (nth (Add lo (S (Add i g))) l) pivot)
          return (λ (w : Bool). Id Nat
            (nth q (elim w return (λ (ww : Bool). List Nat) {
                True => elim g return (λ (gz : Nat). List Nat) {
                  Z => partScanRangeL pivot lo k' (S i) Z l,
                  S (g') gih => partScanRangeL pivot lo k' (S i) (S g') (swapL (Add lo (S i)) (Add lo (S (Add i g))) l) },
                False => partScanRangeL pivot lo k' i (S g) l }))
            (nth q l)) {
          True =>
            (elim g return (λ (gz : Nat).
                Le (Add lo (S (Add (S k') (Add i gz)))) q →
                Id Nat (nth q (elim gz return (λ (gy : Nat). List Nat) {
                    Z => partScanRangeL pivot lo k' (S i) Z l,
                    S (g') gih => partScanRangeL pivot lo k' (S i) (S g') (swapL (Add lo (S i)) (Add lo (S (Add i gz))) l) })) (nth q l)) {
              Z => λ (hleZ : Le (Add lo (S (Add (S k') (Add i Z)))) q).
                ih (S i) Z l
                  (le_rw_l q
                    (Add lo (S (Add (S k') (Add i Z))))
                    (Add lo (S (Add k' (Add (S i) Z))))
                    (id_congr Nat Nat (λ (a : Nat). Add lo (S a))
                      (Add (S k') (Add i Z)) (Add k' (Add (S i) Z)) (hshift_true k' i Z))
                    hleZ),
              S (g') gih => λ (hleS : Le (Add lo (S (Add (S k') (Add i (S g'))))) q).
                id_trans Nat
                  (nth q (partScanRangeL pivot lo k' (S i) (S g') (swapL (Add lo (S i)) (Add lo (S (Add i (S g')))) l)))
                  (nth q (swapL (Add lo (S i)) (Add lo (S (Add i (S g')))) l))
                  (nth q l)
                  (ih (S i) (S g') (swapL (Add lo (S i)) (Add lo (S (Add i (S g')))) l)
                    (le_rw_l q
                      (Add lo (S (Add (S k') (Add i (S g')))))
                      (Add lo (S (Add k' (Add (S i) (S g')))))
                      (id_congr Nat Nat (λ (a : Nat). Add lo (S a))
                        (Add (S k') (Add i (S g'))) (Add k' (Add (S i) (S g'))) (hshift_true k' i (S g')))
                      hleS))
                  (nth_swapL_gt (Add lo (S i)) (Add lo (S (Add i (S g')))) q l
                    (le_trans (S (Add lo (S (Add i (S g'))))) (Add lo (S (S (Add k' (Add i (S g')))))) q
                      (le_rw_l (Add lo (S (S (Add k' (Add i (S g'))))))
                        (Add lo (S (S (Add i (S g'))))) (S (Add lo (S (Add i (S g')))))
                        (add_succ lo (S (Add i (S g'))))
                        (le_add_mono_l lo (S (S (Add i (S g')))) (S (S (Add k' (Add i (S g')))))
                          (le_add_l (Add i (S g')) k')))
                      hleS))
            }) hle,
          False =>
            ih i (S g) l
              (le_rw_l q
                (Add lo (S (Add (S k') (Add i g))))
                (Add lo (S (Add k' (Add i (S g)))))
                (id_congr Nat Nat (λ (a : Nat). Add lo (S a))
                  (Add (S k') (Add i g)) (Add k' (Add i (S g))) (hshift_false k' i g))
                hle)
        }
    } }
def nth_partScanRangeL_ge_ty : Term := prog{
  Π (pivot : Nat) → Π (lo : Nat) → Π (q : Nat) → Π (k : Nat) → Π (i : Nat) → Π (g : Nat) → Π (l : List Nat) →
    Le (Add lo (S (Add k (Add i g)))) q →
    Id Nat (nth q (partScanRangeL pivot lo k i g l)) (nth q l) }

-- Below-lo locality wrapper (partition = scan after pivot pick), mirroring len_partitionRangeL.
def nth_partitionRangeL_lt : Term := prog{
  λ (lo : Nat). λ (j : Nat). λ (hlt : Le (S j) lo). λ (cnt : Nat). λ (l : List Nat).
    elim cnt return (λ (cz : Nat). Id Nat
        (nth j (elim cz return (λ (cy : Nat). List Nat) { Z => l, S (cnt') rec => partScanRangeL (nth lo l) lo cnt' Z Z l }))
        (nth j l)) {
      Z => Refl,
      S (cnt') rec => nth_partScanRangeL_lt (nth lo l) lo j hlt cnt' Z Z l } }
def nth_partitionRangeL_lt_ty : Term := prog{
  Π (lo : Nat) → Π (j : Nat) → Le (S j) lo → Π (cnt : Nat) → Π (l : List Nat) →
    Id Nat (nth j (partitionRangeL lo cnt l)) (nth j l) }

-- At/above-(lo+cnt) locality wrapper. The top bound Le (add lo cnt) q supplies the
-- scan's Le (add lo (S (add cnt' Z))) q via one add_zero nudge (cf count_partitionRangeL).
def nth_partitionRangeL_ge : Term := prog{
  λ (lo : Nat). λ (q : Nat). λ (cnt : Nat). λ (l : List Nat).
    elim cnt return (λ (cz : Nat).
        Le (Add lo cz) q →
        Id Nat (nth q (elim cz return (λ (cy : Nat). List Nat) { Z => l, S (cnt') rec => partScanRangeL (nth lo l) lo cnt' Z Z l })) (nth q l)) {
      Z => λ (hb : Le (Add lo Z) q). Refl,
      S (cnt') rec => λ (hb : Le (Add lo (S cnt')) q).
        nth_partScanRangeL_ge (nth lo l) lo q cnt' Z Z l
          (le_rw_l q (Add lo (S cnt')) (Add lo (S (Add cnt' Z)))
            (id_congr Nat Nat (λ (a : Nat). Add lo (S a)) cnt' (Add cnt' Z)
              (id_sym Nat (Add cnt' Z) cnt' (add_zero cnt')))
            hb) } }
def nth_partitionRangeL_ge_ty : Term := prog{
  Π (lo : Nat) → Π (q : Nat) → Π (cnt : Nat) → Π (l : List Nat) →
    Le (Add lo cnt) q → Id Nat (nth q (partitionRangeL lo cnt l)) (nth q l) }

/-! ## `nth`-under-sort LOCALITY — positions outside the sorted range unchanged (§22)

    The full quicksort's locality, the fuel-structural culmination of Step B. The
    two sub-slices sortRangeL recurses on — the prefix `[lo, lo+i)` and the suffix
    `[lo+i+1, …)` — both sit inside `[lo, lo+cnt)`, so a position outside the whole
    range stays outside both. `_lt` (j < lo) composes the two recursive-sort
    localities with `nth_partitionRangeL_lt` (bound threaded through the fuel elim,
    the right recursion's `lo' = S(lo+i)` reached via one `le_up_r`); `_ge`
    (q ≥ lo+cnt) is the count_sortRangeL structure with position bounds
    `sortRangeGeBL`/`sortRangeGeBR` in place of sortRangeBL/BR — these are the
    len-relative sub-range bounds STRIPPED of their len_partitionRangeL/len_sortRangeL
    layer (a position bound is list-independent), leaving just the partScanSizeL
    size fact (`partSizeCnt`: i+g = cnt-1) and add-arithmetic. -/

-- Below-lo locality of the full sort. Fuel induction (mirror len_sortRangeL);
-- step composes right-sort, left-sort, partition localities via nth_partitionRangeL_lt.
def nth_sortRangeL_lt : Term := prog{
  λ (fuel : Nat). λ (j : Nat).
    elim fuel return (λ (fz : Nat). Π (lo : Nat) → Π (cnt : Nat) → Π (l : List Nat) → Le (S j) lo → Id Nat (nth j (sortRangeL fz lo cnt l)) (nth j l)) {
      Z => λ (lo : Nat). λ (cnt : Nat). λ (l : List Nat). λ (hlt : Le (S j) lo). Refl,
      S (f') ih => λ (lo : Nat). λ (cnt : Nat). λ (l : List Nat). λ (hlt : Le (S j) lo).
        elim cnt return (λ (cz : Nat). Id Nat (nth j (elim cz return (λ (cy : Nat). List Nat) {
              Z => l,
              S (cnt') nih => elim cnt' return (λ (my : Nat). List Nat) {
                Z => l,
                S (cnt'') n2ih => sortRangeL f' (S (Add lo (partIdxRangeL lo cnt l))) (partGapRangeL lo cnt l) (sortRangeL f' lo (partIdxRangeL lo cnt l) (partitionRangeL lo cnt l)) } })) (nth j l)) {
          Z => Refl,
          S (cnt') nih => elim cnt' return (λ (my : Nat). Id Nat (nth j (elim my return (λ (myy : Nat). List Nat) {
                Z => l,
                S (cnt'') n2ih => sortRangeL f' (S (Add lo (partIdxRangeL lo cnt l))) (partGapRangeL lo cnt l) (sortRangeL f' lo (partIdxRangeL lo cnt l) (partitionRangeL lo cnt l)) })) (nth j l)) {
            Z => Refl,
            S (cnt'') n2ih =>
              id_trans Nat
                (nth j (sortRangeL f' (S (Add lo (partIdxRangeL lo cnt l))) (partGapRangeL lo cnt l) (sortRangeL f' lo (partIdxRangeL lo cnt l) (partitionRangeL lo cnt l))))
                (nth j (sortRangeL f' lo (partIdxRangeL lo cnt l) (partitionRangeL lo cnt l)))
                (nth j l)
                (ih (S (Add lo (partIdxRangeL lo cnt l))) (partGapRangeL lo cnt l) (sortRangeL f' lo (partIdxRangeL lo cnt l) (partitionRangeL lo cnt l))
                    (le_trans (S j) lo (S (Add lo (partIdxRangeL lo cnt l))) hlt
                      (le_up_r lo (Add lo (partIdxRangeL lo cnt l)) (le_add lo (partIdxRangeL lo cnt l)))))
                (id_trans Nat
                  (nth j (sortRangeL f' lo (partIdxRangeL lo cnt l) (partitionRangeL lo cnt l)))
                  (nth j (partitionRangeL lo cnt l))
                  (nth j l)
                  (ih lo (partIdxRangeL lo cnt l) (partitionRangeL lo cnt l) hlt)
                  (nth_partitionRangeL_lt lo j hlt cnt l))
          } } } }
def nth_sortRangeL_lt_ty : Term := prog{
  Π (fuel : Nat) → Π (j : Nat) → Π (lo : Nat) → Π (cnt : Nat) → Π (l : List Nat) →
    Le (S j) lo → Id Nat (nth j (sortRangeL fuel lo cnt l)) (nth j l) }

-- The pivot index plus the gap equals cnt-1 (= S cnt'' for cnt = S(S cnt'')).
-- Lifted from sortRangeBL's inner id_trans (partScanSizeL then add_zero).
def partSizeCnt : Term := prog{
  λ (lo : Nat). λ (cnt'' : Nat). λ (l : List Nat).
    id_trans Nat
      (Add (partIdxRangeL lo (S (S cnt'')) l) (partGapRangeL lo (S (S cnt'')) l))
      (S (Add cnt'' Z))
      (S cnt'')
      (partScanSizeL (nth lo l) lo (S cnt'') Z Z l)
      (id_congr Nat Nat (λ (a : Nat). S a) (Add cnt'' Z) cnt'' (add_zero cnt'')) }
def partSizeCnt_ty : Term := prog{
  Π (lo : Nat) → Π (cnt'' : Nat) → Π (l : List Nat) →
    Id Nat (Add (partIdxRangeL lo (S (S cnt'')) l) (partGapRangeL lo (S (S cnt'')) l)) (S cnt'') }

-- Left sub-range position bound: Le (add lo i) q from Le (add lo cnt) q (i ≤ cnt-1 < cnt).
def sortRangeGeBL : Term := prog{
  λ (lo : Nat). λ (cnt'' : Nat). λ (q : Nat). λ (l : List Nat). λ (hb : Le (Add lo (S (S cnt''))) q).
    le_trans (Add lo (partIdxRangeL lo (S (S cnt'')) l)) (Add lo (S (S cnt''))) q
      (le_add_mono_l lo (partIdxRangeL lo (S (S cnt'')) l) (S (S cnt''))
        (le_up_r (partIdxRangeL lo (S (S cnt'')) l) (S cnt'')
          (le_rw_r (partIdxRangeL lo (S (S cnt'')) l)
            (Add (partIdxRangeL lo (S (S cnt'')) l) (partGapRangeL lo (S (S cnt'')) l))
            (S cnt'')
            (partSizeCnt lo cnt'' l)
            (le_add (partIdxRangeL lo (S (S cnt'')) l) (partGapRangeL lo (S (S cnt'')) l)))))
      hb }
def sortRangeGeBL_ty : Term := prog{
  Π (lo : Nat) → Π (cnt'' : Nat) → Π (q : Nat) → Π (l : List Nat) → Le (Add lo (S (S cnt''))) q →
    Le (Add lo (partIdxRangeL lo (S (S cnt'')) l)) q }

-- Right sub-range position bound: Le (add (S (add lo i)) g) q from Le (add lo cnt) q,
-- using add (S (add lo i)) g = add lo (S (add i g)) = add lo cnt (partSizeCnt).
def sortRangeGeBR : Term := prog{
  λ (lo : Nat). λ (cnt'' : Nat). λ (q : Nat). λ (l : List Nat). λ (hb : Le (Add lo (S (S cnt''))) q).
    le_rw_l q (Add lo (S (S cnt''))) (Add (S (Add lo (partIdxRangeL lo (S (S cnt'')) l))) (partGapRangeL lo (S (S cnt'')) l))
      (id_sym Nat
        (Add (S (Add lo (partIdxRangeL lo (S (S cnt'')) l))) (partGapRangeL lo (S (S cnt'')) l))
        (Add lo (S (S cnt'')))
        (id_trans Nat
          (Add (S (Add lo (partIdxRangeL lo (S (S cnt'')) l))) (partGapRangeL lo (S (S cnt'')) l))
          (Add lo (S (Add (partIdxRangeL lo (S (S cnt'')) l) (partGapRangeL lo (S (S cnt'')) l))))
          (Add lo (S (S cnt'')))
          (id_trans Nat
            (Add (S (Add lo (partIdxRangeL lo (S (S cnt'')) l))) (partGapRangeL lo (S (S cnt'')) l))
            (S (Add lo (Add (partIdxRangeL lo (S (S cnt'')) l) (partGapRangeL lo (S (S cnt'')) l))))
            (Add lo (S (Add (partIdxRangeL lo (S (S cnt'')) l) (partGapRangeL lo (S (S cnt'')) l))))
            (id_congr Nat Nat (λ (a : Nat). S a)
              (Add (Add lo (partIdxRangeL lo (S (S cnt'')) l)) (partGapRangeL lo (S (S cnt'')) l))
              (Add lo (Add (partIdxRangeL lo (S (S cnt'')) l) (partGapRangeL lo (S (S cnt'')) l)))
              (add_assoc lo (partIdxRangeL lo (S (S cnt'')) l) (partGapRangeL lo (S (S cnt'')) l)))
            (id_sym Nat
              (Add lo (S (Add (partIdxRangeL lo (S (S cnt'')) l) (partGapRangeL lo (S (S cnt'')) l))))
              (S (Add lo (Add (partIdxRangeL lo (S (S cnt'')) l) (partGapRangeL lo (S (S cnt'')) l))))
              (add_succ lo (Add (partIdxRangeL lo (S (S cnt'')) l) (partGapRangeL lo (S (S cnt'')) l)))))
          (id_congr Nat Nat (λ (a : Nat). Add lo (S a))
            (Add (partIdxRangeL lo (S (S cnt'')) l) (partGapRangeL lo (S (S cnt'')) l)) (S cnt'')
            (partSizeCnt lo cnt'' l))))
      hb }
def sortRangeGeBR_ty : Term := prog{
  Π (lo : Nat) → Π (cnt'' : Nat) → Π (q : Nat) → Π (l : List Nat) → Le (Add lo (S (S cnt''))) q →
    Le (Add (S (Add lo (partIdxRangeL lo (S (S cnt'')) l))) (partGapRangeL lo (S (S cnt'')) l)) q }

-- At/above-(lo+cnt) locality of the full sort. count_sortRangeL structure with
-- position bounds sortRangeGeBL/BR feeding the two recursive-sort IHs.
def nth_sortRangeL_ge : Term := prog{
  λ (fuel : Nat). λ (q : Nat).
    elim fuel return (λ (fz : Nat). Π (lo : Nat) → Π (cnt : Nat) → Π (l : List Nat) →
        Le (Add lo cnt) q → Id Nat (nth q (sortRangeL fz lo cnt l)) (nth q l)) {
      Z => λ (lo : Nat). λ (cnt : Nat). λ (l : List Nat). λ (hb : Le (Add lo cnt) q). Refl,
      S (f') ih => λ (lo : Nat). λ (cnt : Nat). λ (l : List Nat).
        elim cnt return (λ (cz : Nat). Le (Add lo cz) q →
            Id Nat (nth q (sortRangeL (S f') lo cz l)) (nth q l)) {
          Z => λ (hb : Le (Add lo Z) q). Refl,
          S (cnt') nih => elim cnt' return (λ (cz' : Nat). Le (Add lo (S cz')) q →
              Id Nat (nth q (sortRangeL (S f') lo (S cz') l)) (nth q l)) {
            Z => λ (hb : Le (Add lo (S Z)) q). Refl,
            S (cnt'') n2ih => λ (hb : Le (Add lo (S (S cnt''))) q).
              id_trans Nat
                (nth q (sortRangeL f' (S (Add lo (partIdxRangeL lo (S (S cnt'')) l))) (partGapRangeL lo (S (S cnt'')) l)
                          (sortRangeL f' lo (partIdxRangeL lo (S (S cnt'')) l) (partitionRangeL lo (S (S cnt'')) l))))
                (nth q (sortRangeL f' lo (partIdxRangeL lo (S (S cnt'')) l) (partitionRangeL lo (S (S cnt'')) l)))
                (nth q l)
                (ih (S (Add lo (partIdxRangeL lo (S (S cnt'')) l))) (partGapRangeL lo (S (S cnt'')) l)
                    (sortRangeL f' lo (partIdxRangeL lo (S (S cnt'')) l) (partitionRangeL lo (S (S cnt'')) l))
                    (sortRangeGeBR lo cnt'' q l hb))
                (id_trans Nat
                  (nth q (sortRangeL f' lo (partIdxRangeL lo (S (S cnt'')) l) (partitionRangeL lo (S (S cnt'')) l)))
                  (nth q (partitionRangeL lo (S (S cnt'')) l))
                  (nth q l)
                  (ih lo (partIdxRangeL lo (S (S cnt'')) l) (partitionRangeL lo (S (S cnt'')) l)
                      (sortRangeGeBL lo cnt'' q l hb))
                  (nth_partitionRangeL_ge lo q (S (S cnt'')) l hb))
          }
        }
    } }
def nth_sortRangeL_ge_ty : Term := prog{
  Π (fuel : Nat) → Π (q : Nat) → Π (lo : Nat) → Π (cnt : Nat) → Π (l : List Nat) →
    Le (Add lo cnt) q → Id Nat (nth q (sortRangeL fuel lo cnt l)) (nth q l) }

/-! ## Reusable bridges — cancellation, no-confusion, list/take/drop extensionality (§22)

    The general-purpose stratum Step C's segCount preservation stands on. Two are
    the classical Nat "no confusion + cancellation" primitives; the rest bridge the
    positional (nth) view to the segment (take/drop) view.

    - `znots` : `Z ≠ S` via a LARGE elimination into `Type` (`elim y {Z => Unit, S =>
      Bot}`), transported by `j`. This is the discriminator list-extensionality needs
      to kill Nil-vs-Cons length mismatches — and it type-checks (the M5 λ/neutral
      deferral does not bite an APPLIED large elim).
    - `s_inj` : `S` injective, one `id_congr` with `pred`.
    - `add_cancel_l` : left cancellation, induction on `a` peeling `s_inj`.
    - `nth_drop` : `nth k (drop b l) = nth (add b k) l` (the positional reading of drop).
    - `list_ext` : equal length + equal `nth` everywhere ⟹ equal lists (needs znots + s_inj).
    - `take_ext_bounded` : `take w a = take w b` from equal length + `nth` agreeing
      BELOW w — the bounded form fed directly by `nth_*_lt` (no case split on k).
    - `len_drop_cong` : dropping preserves a length equality.
    - `count_split` : `count x l = count x (take w l) + count x (drop w l)` (count_append ∘ take_drop_id). -/

def znots : Term := prog{
  λ (x : Nat). λ (h : Id Nat Z (S x)).
    j Nat Z (λ (y : Nat). λ (hy : Id Nat Z y). elim y return (λ (yy : Nat). Type) { Z => Unit, S (k) ih => Bot })
      unit (S x) h }
def znots_ty : Term := prog{ Π (x : Nat) → Id Nat Z (S x) → Bot }

def pred : Term := prog{ λ (n : Nat). elim n return (λ (z : Nat). Nat) { Z => Z, S (k) ih => k } }
def s_inj : Term := prog{
  λ (m : Nat). λ (n : Nat). λ (h : Id Nat (S m) (S n)).
    id_congr Nat Nat pred (S m) (S n) h }
def s_inj_ty : Term := prog{ Π (m : Nat) → Π (n : Nat) → Id Nat (S m) (S n) → Id Nat m n }

def add_cancel_l : Term := prog{
  λ (a : Nat).
    elim a return (λ (az : Nat). Π (x : Nat) → Π (y : Nat) → Id Nat (Add az x) (Add az y) → Id Nat x y) {
      Z => λ (x : Nat). λ (y : Nat). λ (h : Id Nat (Add Z x) (Add Z y)). h,
      S (a') ih => λ (x : Nat). λ (y : Nat). λ (h : Id Nat (Add (S a') x) (Add (S a') y)).
        ih x y (s_inj (Add a' x) (Add a' y) h) } }
def add_cancel_l_ty : Term := prog{
  Π (a : Nat) → Π (x : Nat) → Π (y : Nat) → Id Nat (Add a x) (Add a y) → Id Nat x y }

def nth_drop : Term := prog{
  λ (b : Nat).
    elim b return (λ (bz : Nat). Π (k : Nat) → Π (l : List Nat) → Id Nat (nth k (Drop bz l)) (nth (Add bz k) l)) {
      Z => λ (k : Nat). λ (l : List Nat). Refl,
      S (b') ih => λ (k : Nat). λ (l : List Nat).
        elim l return (λ (lz : List Nat). Id Nat (nth k (Drop (S b') lz)) (nth (Add (S b') k) lz)) {
          Nil => elim k return (λ (kz : Nat). Id Nat (nth kz (Drop (S b') Nil)) (nth (Add (S b') kz) Nil)) {
            Z => Refl, S (k') kih => Refl },
          Cons (h) (t) ihl => ih k t } } }
def nth_drop_ty : Term := prog{
  Π (b : Nat) → Π (k : Nat) → Π (l : List Nat) → Id Nat (nth k (Drop b l)) (nth (Add b k) l) }

def list_ext : Term := prog{
  λ (a : List Nat).
    elim a return (λ (az : List Nat). Π (b : List Nat) → Id Nat (Len az) (Len b) → (Π (k : Nat) → Id Nat (nth k az) (nth k b)) → Id (List Nat) az b) {
      Nil => λ (b : List Nat).
        elim b return (λ (bz : List Nat). Id Nat (Len Nil) (Len bz) → (Π (k : Nat) → Id Nat (nth k Nil) (nth k bz)) → Id (List Nat) Nil bz) {
          Nil => λ (hlen : Id Nat (Len Nil) (Len Nil)). λ (hnth : Π (k : Nat) → Id Nat (nth k Nil) (nth k Nil)). Refl,
          Cons (hb) (tb) ihb => λ (hlen : Id Nat (Len Nil) (Len (Cons hb tb))). λ (hnth : Π (k : Nat) → Id Nat (nth k Nil) (nth k (Cons hb tb))).
            botElim (Id (List Nat) Nil (Cons hb tb)) (znots (Len tb) hlen) },
      Cons (ha) (ta) iha => λ (b : List Nat).
        elim b return (λ (bz : List Nat). Id Nat (Len (Cons ha ta)) (Len bz) → (Π (k : Nat) → Id Nat (nth k (Cons ha ta)) (nth k bz)) → Id (List Nat) (Cons ha ta) bz) {
          Nil => λ (hlen : Id Nat (Len (Cons ha ta)) (Len Nil)). λ (hnth : Π (k : Nat) → Id Nat (nth k (Cons ha ta)) (nth k Nil)).
            botElim (Id (List Nat) (Cons ha ta) Nil) (znots (Len ta) (id_sym Nat (Len (Cons ha ta)) (Len Nil) hlen)),
          Cons (hb) (tb) ihb => λ (hlen : Id Nat (Len (Cons ha ta)) (Len (Cons hb tb))). λ (hnth : Π (k : Nat) → Id Nat (nth k (Cons ha ta)) (nth k (Cons hb tb))).
            id_trans (List Nat) (Cons ha ta) (Cons hb ta) (Cons hb tb)
              (id_congr Nat (List Nat) (λ (hh : Nat). Cons hh ta) ha hb (hnth Z))
              (id_congr (List Nat) (List Nat) (λ (tt : List Nat). Cons hb tt) ta tb
                (iha tb (s_inj (Len ta) (Len tb) hlen) (λ (k : Nat). hnth (S k)))) } } }
def list_ext_ty : Term := prog{
  Π (a : List Nat) → Π (b : List Nat) → Id Nat (Len a) (Len b) →
    (Π (k : Nat) → Id Nat (nth k a) (nth k b)) → Id (List Nat) a b }

def take_ext_bounded : Term := prog{
  λ (w : Nat).
    elim w return (λ (wz : Nat). Π (a : List Nat) → Π (b : List Nat) → Id Nat (Len a) (Len b) → (Π (k : Nat) → Le (S k) wz → Id Nat (nth k a) (nth k b)) → Id (List Nat) (Take wz a) (Take wz b)) {
      Z => λ (a : List Nat). λ (b : List Nat). λ (hlen : Id Nat (Len a) (Len b)). λ (hnth : Π (k : Nat) → Le (S k) Z → Id Nat (nth k a) (nth k b)). Refl,
      S (w') ih => λ (a : List Nat). λ (b : List Nat). λ (hlen : Id Nat (Len a) (Len b)). λ (hnth : Π (k : Nat) → Le (S k) (S w') → Id Nat (nth k a) (nth k b)).
        elim a return (λ (az : List Nat). Id Nat (Len az) (Len b) → (Π (k : Nat) → Le (S k) (S w') → Id Nat (nth k az) (nth k b)) → Id (List Nat) (Take (S w') az) (Take (S w') b)) {
          Nil => λ (hlenA : Id Nat (Len Nil) (Len b)). λ (hnthA : Π (k : Nat) → Le (S k) (S w') → Id Nat (nth k Nil) (nth k b)).
            elim b return (λ (bz : List Nat). Id Nat (Len Nil) (Len bz) → Id (List Nat) (Take (S w') Nil) (Take (S w') bz)) {
              Nil => λ (hl : Id Nat (Len Nil) (Len Nil)). Refl,
              Cons (hb) (tb) ihb => λ (hl : Id Nat (Len Nil) (Len (Cons hb tb))).
                botElim (Id (List Nat) (Take (S w') Nil) (Take (S w') (Cons hb tb))) (znots (Len tb) hl) } hlenA,
          Cons (ha) (ta) iha => λ (hlenA : Id Nat (Len (Cons ha ta)) (Len b)). λ (hnthA : Π (k : Nat) → Le (S k) (S w') → Id Nat (nth k (Cons ha ta)) (nth k b)).
            elim b return (λ (bz : List Nat). Id Nat (Len (Cons ha ta)) (Len bz) → (Π (k : Nat) → Le (S k) (S w') → Id Nat (nth k (Cons ha ta)) (nth k bz)) → Id (List Nat) (Take (S w') (Cons ha ta)) (Take (S w') bz)) {
              Nil => λ (hl : Id Nat (Len (Cons ha ta)) (Len Nil)). λ (hn : Π (k : Nat) → Le (S k) (S w') → Id Nat (nth k (Cons ha ta)) (nth k Nil)).
                botElim (Id (List Nat) (Take (S w') (Cons ha ta)) (Take (S w') Nil)) (znots (Len ta) (id_sym Nat (Len (Cons ha ta)) (Len Nil) hl)),
              Cons (hb) (tb) ihb => λ (hl : Id Nat (Len (Cons ha ta)) (Len (Cons hb tb))). λ (hn : Π (k : Nat) → Le (S k) (S w') → Id Nat (nth k (Cons ha ta)) (nth k (Cons hb tb))).
                id_trans (List Nat) (Cons ha (Take w' ta)) (Cons hb (Take w' ta)) (Cons hb (Take w' tb))
                  (id_congr Nat (List Nat) (λ (hh : Nat). Cons hh (Take w' ta)) ha hb (hn Z unit))
                  (id_congr (List Nat) (List Nat) (λ (tt : List Nat). Cons hb tt) (Take w' ta) (Take w' tb)
                    (ih ta tb (s_inj (Len ta) (Len tb) hl) (λ (k : Nat). λ (hk : Le (S k) w'). hn (S k) hk)))
            } hlenA hnthA
        } hlen hnth
    } }
def take_ext_bounded_ty : Term := prog{
  Π (w : Nat) → Π (a : List Nat) → Π (b : List Nat) → Id Nat (Len a) (Len b) →
    (Π (k : Nat) → Le (S k) w → Id Nat (nth k a) (nth k b)) → Id (List Nat) (Take w a) (Take w b) }

def len_drop_cong : Term := prog{
  λ (w : Nat).
    elim w return (λ (wz : Nat). Π (a : List Nat) → Π (b : List Nat) → Id Nat (Len a) (Len b) → Id Nat (Len (Drop wz a)) (Len (Drop wz b))) {
      Z => λ (a : List Nat). λ (b : List Nat). λ (hlen : Id Nat (Len a) (Len b)). hlen,
      S (w') ih => λ (a : List Nat). λ (b : List Nat). λ (hlen : Id Nat (Len a) (Len b)).
        elim a return (λ (az : List Nat). Id Nat (Len az) (Len b) → Id Nat (Len (Drop (S w') az)) (Len (Drop (S w') b))) {
          Nil => λ (hl : Id Nat (Len Nil) (Len b)).
            elim b return (λ (bz : List Nat). Id Nat (Len Nil) (Len bz) → Id Nat (Len (Drop (S w') Nil)) (Len (Drop (S w') bz))) {
              Nil => λ (h : Id Nat (Len Nil) (Len Nil)). Refl,
              Cons (hb) (tb) ihb => λ (h : Id Nat (Len Nil) (Len (Cons hb tb))).
                botElim (Id Nat (Len (Drop (S w') Nil)) (Len (Drop (S w') (Cons hb tb)))) (znots (Len tb) h) } hl,
          Cons (ha) (ta) iha => λ (hl : Id Nat (Len (Cons ha ta)) (Len b)).
            elim b return (λ (bz : List Nat). Id Nat (Len (Cons ha ta)) (Len bz) → Id Nat (Len (Drop (S w') (Cons ha ta))) (Len (Drop (S w') bz))) {
              Nil => λ (h : Id Nat (Len (Cons ha ta)) (Len Nil)).
                botElim (Id Nat (Len (Drop (S w') (Cons ha ta))) (Len (Drop (S w') Nil))) (znots (Len ta) (id_sym Nat (Len (Cons ha ta)) (Len Nil) h)),
              Cons (hb) (tb) ihb => λ (h : Id Nat (Len (Cons ha ta)) (Len (Cons hb tb))).
                ih ta tb (s_inj (Len ta) (Len tb) h) } hl } hlen } }
def len_drop_cong_ty : Term := prog{
  Π (w : Nat) → Π (a : List Nat) → Π (b : List Nat) → Id Nat (Len a) (Len b) →
    Id Nat (Len (Drop w a)) (Len (Drop w b)) }

def count_split : Term := prog{
  λ (x : Nat). λ (w : Nat). λ (l : List Nat).
    id_trans Nat (Count x l) (Count x (append (Take w l) (Drop w l))) (Add (Count x (Take w l)) (Count x (Drop w l)))
      (id_congr (List Nat) Nat (λ (ll : List Nat). Count x ll) l (append (Take w l) (Drop w l))
        (id_sym (List Nat) (append (Take w l) (Drop w l)) l (take_drop_id w l)))
      (count_append x (Take w l) (Drop w l)) }
def count_split_ty : Term := prog{
  Π (x : Nat) → Π (w : Nat) → Π (l : List Nat) →
    Id Nat (Count x l) (Add (Count x (Take w l)) (Count x (Drop w l))) }

/-! ## Segment-count preservation — the perm-survival vehicle (§22, M22-c step 3)

    The multiset half's payoff: sorting/partitioning a range preserves the multiset
    OF THAT SEGMENT (segCount), so a positional bound over the segment survives the
    permutation. The argument is pure cancellation: whole count is preserved
    (count_sortRangeL / count_partitionRangeL), the prefix `take lo` and suffix
    `drop cnt (drop lo)` are IDENTICAL lists (Step B locality lifted to list equality
    via take_ext_bounded / list_ext + nth_drop), and

        count x whole = count x prefix + (segment + suffix)

    so with prefix and suffix counts equal on both sides, add_cancel_l twice (once
    each side, add_comm to expose the operand) leaves segment counts equal — no
    subtraction. `count_rest_preserved` / `count_seg_preserved` are the two directions
    of that cancellation; `seg_glue` composes them; `take_lo_*` / `drop_suffix_*`
    supply the list equalities from Step B. -/

def count_rest_preserved : Term := prog{
  λ (x : Nat). λ (w : Nat). λ (s : List Nat). λ (l : List Nat).
    λ (hcount : Id Nat (Count x s) (Count x l)).
    λ (hpre : Id Nat (Count x (Take w s)) (Count x (Take w l))).
      add_cancel_l (Count x (Take w l)) (Count x (Drop w s)) (Count x (Drop w l))
        (id_trans Nat
          (Add (Count x (Take w l)) (Count x (Drop w s)))
          (Count x l)
          (Add (Count x (Take w l)) (Count x (Drop w l)))
          (id_trans Nat
            (Add (Count x (Take w l)) (Count x (Drop w s)))
            (Count x s)
            (Count x l)
            (id_sym Nat (Count x s) (Add (Count x (Take w l)) (Count x (Drop w s)))
              (id_trans Nat
                (Count x s)
                (Add (Count x (Take w s)) (Count x (Drop w s)))
                (Add (Count x (Take w l)) (Count x (Drop w s)))
                (count_split x w s)
                (id_congr Nat Nat (λ (n : Nat). Add n (Count x (Drop w s)))
                  (Count x (Take w s)) (Count x (Take w l)) hpre)))
            hcount)
          (count_split x w l)) }
def count_rest_preserved_ty : Term := prog{
  Π (x : Nat) → Π (w : Nat) → Π (s : List Nat) → Π (l : List Nat) →
    Id Nat (Count x s) (Count x l) →
    Id Nat (Count x (Take w s)) (Count x (Take w l)) →
    Id Nat (Count x (Drop w s)) (Count x (Drop w l)) }

def count_seg_preserved : Term := prog{
  λ (x : Nat). λ (w : Nat). λ (s : List Nat). λ (l : List Nat).
    λ (hcount : Id Nat (Count x s) (Count x l)).
    λ (hdrop : Id Nat (Count x (Drop w s)) (Count x (Drop w l))).
      add_cancel_l (Count x (Drop w l)) (Count x (Take w s)) (Count x (Take w l))
        (id_trans Nat
          (Add (Count x (Drop w l)) (Count x (Take w s)))
          (Count x l)
          (Add (Count x (Drop w l)) (Count x (Take w l)))
          (id_trans Nat
            (Add (Count x (Drop w l)) (Count x (Take w s)))
            (Count x s)
            (Count x l)
            (id_sym Nat (Count x s) (Add (Count x (Drop w l)) (Count x (Take w s)))
              (id_trans Nat
                (Count x s)
                (Add (Count x (Take w s)) (Count x (Drop w s)))
                (Add (Count x (Drop w l)) (Count x (Take w s)))
                (count_split x w s)
                (id_trans Nat
                  (Add (Count x (Take w s)) (Count x (Drop w s)))
                  (Add (Count x (Take w s)) (Count x (Drop w l)))
                  (Add (Count x (Drop w l)) (Count x (Take w s)))
                  (id_congr Nat Nat (λ (n : Nat). Add (Count x (Take w s)) n)
                    (Count x (Drop w s)) (Count x (Drop w l)) hdrop)
                  (add_comm (Count x (Take w s)) (Count x (Drop w l))))))
            hcount)
          (id_trans Nat
            (Count x l)
            (Add (Count x (Take w l)) (Count x (Drop w l)))
            (Add (Count x (Drop w l)) (Count x (Take w l)))
            (count_split x w l)
            (add_comm (Count x (Take w l)) (Count x (Drop w l))))) }
def count_seg_preserved_ty : Term := prog{
  Π (x : Nat) → Π (w : Nat) → Π (s : List Nat) → Π (l : List Nat) →
    Id Nat (Count x s) (Count x l) →
    Id Nat (Count x (Drop w s)) (Count x (Drop w l)) →
    Id Nat (Count x (Take w s)) (Count x (Take w l)) }

def seg_glue : Term := prog{
  λ (x : Nat). λ (lo : Nat). λ (cnt : Nat). λ (s : List Nat). λ (l : List Nat).
    λ (hcount : Id Nat (Count x s) (Count x l)).
    λ (hpre : Id (List Nat) (Take lo s) (Take lo l)).
    λ (hsuf : Id (List Nat) (Drop cnt (Drop lo s)) (Drop cnt (Drop lo l))).
      count_seg_preserved x cnt (Drop lo s) (Drop lo l)
        (count_rest_preserved x lo s l hcount
          (id_congr (List Nat) Nat (λ (ll : List Nat). Count x ll) (Take lo s) (Take lo l) hpre))
        (id_congr (List Nat) Nat (λ (ll : List Nat). Count x ll) (Drop cnt (Drop lo s)) (Drop cnt (Drop lo l)) hsuf) }
def seg_glue_ty : Term := prog{
  Π (x : Nat) → Π (lo : Nat) → Π (cnt : Nat) → Π (s : List Nat) → Π (l : List Nat) →
    Id Nat (Count x s) (Count x l) →
    Id (List Nat) (Take lo s) (Take lo l) →
    Id (List Nat) (Drop cnt (Drop lo s)) (Drop cnt (Drop lo l)) →
    Id Nat (Count x (Take cnt (Drop lo s))) (Count x (Take cnt (Drop lo l))) }

-- Prefix/suffix of the SORT are identical (Step B locality → list equality).
def take_lo_sort : Term := prog{
  λ (fuel : Nat). λ (lo : Nat). λ (cnt : Nat). λ (l : List Nat).
    take_ext_bounded lo (sortRangeL fuel lo cnt l) l
      (len_sortRangeL fuel lo cnt l)
      (λ (k : Nat). λ (hk : Le (S k) lo). nth_sortRangeL_lt fuel k lo cnt l hk) }
def take_lo_sort_ty : Term := prog{
  Π (fuel : Nat) → Π (lo : Nat) → Π (cnt : Nat) → Π (l : List Nat) →
    Id (List Nat) (Take lo (sortRangeL fuel lo cnt l)) (Take lo l) }

def drop_suffix_sort : Term := prog{
  λ (fuel : Nat). λ (lo : Nat). λ (cnt : Nat). λ (l : List Nat).
    list_ext (Drop cnt (Drop lo (sortRangeL fuel lo cnt l))) (Drop cnt (Drop lo l))
      (len_drop_cong cnt (Drop lo (sortRangeL fuel lo cnt l)) (Drop lo l)
        (len_drop_cong lo (sortRangeL fuel lo cnt l) l (len_sortRangeL fuel lo cnt l)))
      (λ (k : Nat).
        id_trans Nat
          (nth k (Drop cnt (Drop lo (sortRangeL fuel lo cnt l))))
          (nth (Add lo (Add cnt k)) (sortRangeL fuel lo cnt l))
          (nth k (Drop cnt (Drop lo l)))
          (id_trans Nat
            (nth k (Drop cnt (Drop lo (sortRangeL fuel lo cnt l))))
            (nth (Add cnt k) (Drop lo (sortRangeL fuel lo cnt l)))
            (nth (Add lo (Add cnt k)) (sortRangeL fuel lo cnt l))
            (nth_drop cnt k (Drop lo (sortRangeL fuel lo cnt l)))
            (nth_drop lo (Add cnt k) (sortRangeL fuel lo cnt l)))
          (id_trans Nat
            (nth (Add lo (Add cnt k)) (sortRangeL fuel lo cnt l))
            (nth (Add lo (Add cnt k)) l)
            (nth k (Drop cnt (Drop lo l)))
            (nth_sortRangeL_ge fuel (Add lo (Add cnt k)) lo cnt l
              (le_add_mono_l lo cnt (Add cnt k) (le_add cnt k)))
            (id_trans Nat
              (nth (Add lo (Add cnt k)) l)
              (nth (Add cnt k) (Drop lo l))
              (nth k (Drop cnt (Drop lo l)))
              (id_sym Nat (nth (Add cnt k) (Drop lo l)) (nth (Add lo (Add cnt k)) l) (nth_drop lo (Add cnt k) l))
              (id_sym Nat (nth k (Drop cnt (Drop lo l))) (nth (Add cnt k) (Drop lo l)) (nth_drop cnt k (Drop lo l)))))) }
def drop_suffix_sort_ty : Term := prog{
  Π (fuel : Nat) → Π (lo : Nat) → Π (cnt : Nat) → Π (l : List Nat) →
    Id (List Nat) (Drop cnt (Drop lo (sortRangeL fuel lo cnt l))) (Drop cnt (Drop lo l)) }

-- Prefix/suffix of PARTITION are identical (same shape).
def take_lo_partition : Term := prog{
  λ (lo : Nat). λ (cnt : Nat). λ (l : List Nat).
    take_ext_bounded lo (partitionRangeL lo cnt l) l
      (len_partitionRangeL lo cnt l)
      (λ (k : Nat). λ (hk : Le (S k) lo). nth_partitionRangeL_lt lo k hk cnt l) }
def take_lo_partition_ty : Term := prog{
  Π (lo : Nat) → Π (cnt : Nat) → Π (l : List Nat) →
    Id (List Nat) (Take lo (partitionRangeL lo cnt l)) (Take lo l) }

def drop_suffix_partition : Term := prog{
  λ (lo : Nat). λ (cnt : Nat). λ (l : List Nat).
    list_ext (Drop cnt (Drop lo (partitionRangeL lo cnt l))) (Drop cnt (Drop lo l))
      (len_drop_cong cnt (Drop lo (partitionRangeL lo cnt l)) (Drop lo l)
        (len_drop_cong lo (partitionRangeL lo cnt l) l (len_partitionRangeL lo cnt l)))
      (λ (k : Nat).
        id_trans Nat
          (nth k (Drop cnt (Drop lo (partitionRangeL lo cnt l))))
          (nth (Add lo (Add cnt k)) (partitionRangeL lo cnt l))
          (nth k (Drop cnt (Drop lo l)))
          (id_trans Nat
            (nth k (Drop cnt (Drop lo (partitionRangeL lo cnt l))))
            (nth (Add cnt k) (Drop lo (partitionRangeL lo cnt l)))
            (nth (Add lo (Add cnt k)) (partitionRangeL lo cnt l))
            (nth_drop cnt k (Drop lo (partitionRangeL lo cnt l)))
            (nth_drop lo (Add cnt k) (partitionRangeL lo cnt l)))
          (id_trans Nat
            (nth (Add lo (Add cnt k)) (partitionRangeL lo cnt l))
            (nth (Add lo (Add cnt k)) l)
            (nth k (Drop cnt (Drop lo l)))
            (nth_partitionRangeL_ge lo (Add lo (Add cnt k)) cnt l
              (le_add_mono_l lo cnt (Add cnt k) (le_add cnt k)))
            (id_trans Nat
              (nth (Add lo (Add cnt k)) l)
              (nth (Add cnt k) (Drop lo l))
              (nth k (Drop cnt (Drop lo l)))
              (id_sym Nat (nth (Add cnt k) (Drop lo l)) (nth (Add lo (Add cnt k)) l) (nth_drop lo (Add cnt k) l))
              (id_sym Nat (nth k (Drop cnt (Drop lo l))) (nth (Add cnt k) (Drop lo l)) (nth_drop cnt k (Drop lo l)))))) }
def drop_suffix_partition_ty : Term := prog{
  Π (lo : Nat) → Π (cnt : Nat) → Π (l : List Nat) →
    Id (List Nat) (Drop cnt (Drop lo (partitionRangeL lo cnt l))) (Drop cnt (Drop lo l)) }

-- THE GOALS: the segment multiset survives the range sort and partition.
def segCount_sortRangeL : Term := prog{
  λ (x : Nat). λ (fuel : Nat). λ (lo : Nat). λ (cnt : Nat). λ (l : List Nat).
    λ (hb : Le (Add lo cnt) (Len l)).
      seg_glue x lo cnt (sortRangeL fuel lo cnt l) l
        (count_sortRangeL x fuel lo cnt l hb)
        (take_lo_sort fuel lo cnt l)
        (drop_suffix_sort fuel lo cnt l) }
def segCount_sortRangeL_ty : Term := prog{
  Π (x : Nat) → Π (fuel : Nat) → Π (lo : Nat) → Π (cnt : Nat) → Π (l : List Nat) →
    Le (Add lo cnt) (Len l) →
    Id Nat (segCount x lo cnt (sortRangeL fuel lo cnt l)) (segCount x lo cnt l) }

def segCount_partitionRangeL : Term := prog{
  λ (x : Nat). λ (lo : Nat). λ (cnt : Nat). λ (l : List Nat).
    λ (hb : Le (Add lo cnt) (Len l)).
      seg_glue x lo cnt (partitionRangeL lo cnt l) l
        (count_partitionRangeL lo x cnt l hb)
        (take_lo_partition lo cnt l)
        (drop_suffix_partition lo cnt l) }
def segCount_partitionRangeL_ty : Term := prog{
  Π (x : Nat) → Π (lo : Nat) → Π (cnt : Nat) → Π (l : List Nat) →
    Le (Add lo cnt) (Len l) →
    Id Nat (segCount x lo cnt (partitionRangeL lo cnt l)) (segCount x lo cnt l) }

/-! ## The partition invariant — STATEMENTS (§22, M22-c step 2; proofs dispatched)

    partScanRangeL establishes the Lomuto invariant: the ≤-segment is ≤ pivot, the
    gap is > pivot, the pivot lands at the boundary index. Verified computationally
    (final forms on 5 inputs incl. a sub-range) and elaboration-checked. The 3-way
    conjunction CANNOT be Σ-bundled (comptime Σ can't be projected), so it is THREE
    separate lemmas — and they ARE separable: AllLeR-maintenance needs only the ≤-side
    precondition + the leb test (the swapped-in element tested ≤ pivot); AllGtR only
    the gap-side; pivot only that lo is untouched. STRENGTHENED scan-level forms carry
    the region preconditions (≤-region offset `S lo`, gap offset `add (S i) lo`,
    index-first to match the predicates); the partitionRangeL WRAPPERS drop out at
    i=g=0 (vacuous preconditions). ADD-ORDER: predicates index-first (`add k lo`),
    partScanRangeL offset-first (`add lo X`) — the proofs bridge with add_comm. Proofs
    owned by dllbc-seg (positional induction mirroring count_partScanRangeL, swaps
    discharged via nth_swapL_lt/gt). -/
-- pos_bridge_ss : add lo (S (S m)) = S (add m (S lo))  (both lo+m+2) — the mid upper bound.
def pos_bridge_ss : Term := prog{
  λ (lo : Nat). λ (m : Nat).
    id_trans Nat (Add lo (S (S m))) (S (S (Add lo m))) (S (Add m (S lo)))
      (id_trans Nat (Add lo (S (S m))) (S (Add lo (S m))) (S (S (Add lo m)))
        (add_succ lo (S m))
        (id_congr Nat Nat (λ (z : Nat). S z) (Add lo (S m)) (S (Add lo m)) (add_succ lo m)))
      (id_sym Nat (S (Add m (S lo))) (S (S (Add lo m)))
        (id_trans Nat (S (Add m (S lo))) (S (S (Add m lo))) (S (S (Add lo m)))
          (id_congr Nat Nat (λ (z : Nat). S z) (Add m (S lo)) (S (Add m lo)) (add_succ m lo))
          (id_congr Nat Nat (λ (z : Nat). S z) (S (Add m lo)) (S (Add lo m))
            (id_congr Nat Nat (λ (z : Nat). S z) (Add m lo) (Add lo m) (add_comm m lo))))) }
def pos_bridge_ss_ty : Term := prog{ Π (lo : Nat) → Π (m : Nat) → Id Nat (Add lo (S (S m))) (S (Add m (S lo))) }

-- bnd_sl : the scan swap's smaller index < larger index (S(lo+1+i) ≤ lo+1+i+(S g')).
def bnd_sl : Term := prog{
  λ (lo : Nat). λ (i : Nat). λ (g' : Nat).
    le_rw_l (Add lo (S (Add i (S g')))) (Add lo (S (S i))) (S (Add lo (S i)))
      (add_succ lo (S i))
      (le_add_mono_l lo (S (S i)) (S (Add i (S g')))
        (le_rw_r (S i) (S (Add i g')) (Add i (S g'))
          (id_sym Nat (Add i (S g')) (S (Add i g')) (add_succ i g'))
          (le_add i g'))) }
def bnd_sl_ty : Term := prog{ Π (lo : Nat) → Π (i : Nat) → Π (g' : Nat) → Le (S (Add lo (S i))) (Add lo (S (Add i (S g')))) }

-- allLeR_base_swap : the pivot-placement swap at the base (i = S i') keeps [lo, lo+S i')
-- all ≤ pivot. Position lo gets the far ≤-element (nth_swapL_lo + hL at i'), the interior
-- is unchanged (allLeR_cong via nth_swapL_mid), assembled by allLeR_extend_lo.
def allLeR_base_swap : Term := prog{
  λ (pivot : Nat). λ (lo : Nat). λ (i' : Nat). λ (l : List Nat).
    λ (hL : AllLeR (S i') (S lo) pivot l).
      allLeR_extend_lo i' lo pivot (swapL lo (Add lo (S i')) l)
        (le_rw_l pivot (nth (Add lo (S i')) l) (nth lo (swapL lo (Add lo (S i')) l))
          (id_sym Nat (nth lo (swapL lo (Add lo (S i')) l)) (nth (Add lo (S i')) l)
            (nth_swapL_lo lo (Add lo (S i')) l (le_add_succ lo i')))
          (le_rw_l pivot (nth (Add i' (S lo)) l) (nth (Add lo (S i')) l)
            (id_congr Nat Nat (λ (q : Nat). nth q l) (Add i' (S lo)) (Add lo (S i')) (add_swap_succ i' lo))
            (hL i' (le_refl (S i')))))
        (allLeR_cong i' (S lo) pivot l (swapL lo (Add lo (S i')) l)
          (λ (m : Nat). λ (hm : Le (S m) i').
            nth_swapL_mid lo (Add lo (S i')) (Add m (S lo)) l
              (le_add_l (S lo) m)
              (le_rw_l (Add lo (S i')) (Add lo (S (S m))) (S (Add m (S lo)))
                (pos_bridge_ss lo m)
                (le_add_mono_l lo (S (S m)) (S i') hm)))
          (λ (m : Nat). λ (hm : Le (S m) i'). hL m (le_up_r (S m) i' hm))) }
def allLeR_base_swap_ty : Term := prog{
  Π (pivot : Nat) → Π (lo : Nat) → Π (i' : Nat) → Π (l : List Nat) →
    AllLeR (S i') (S lo) pivot l → AllLeR (S i') lo pivot (swapL lo (Add lo (S i')) l) }

-- allLeR_step_TZ : True/g=0 step — the scan element (tested ≤ pivot) extends the ≤-region.
def allLeR_step_TZ : Term := prog{
  λ (pivot : Nat). λ (lo : Nat). λ (i : Nat). λ (l : List Nat).
    λ (e : Id Bool (Leb (nth (Add lo (S (Add i Z))) l) pivot) True). λ (hL : AllLeR i (S lo) pivot l).
      allLeR_extend_far i (S lo) pivot l hL
        (le_rw_l pivot (nth (Add lo (S (Add i Z))) l) (nth (Add i (S lo)) l)
          (id_congr Nat Nat (λ (q : Nat). nth q l) (Add lo (S (Add i Z))) (Add i (S lo))
            (id_trans Nat (Add lo (S (Add i Z))) (Add lo (S i)) (Add i (S lo))
              (id_congr Nat Nat (λ (z : Nat). Add lo (S z)) (Add i Z) i (add_zero i))
              (id_sym Nat (Add i (S lo)) (Add lo (S i)) (add_swap_succ i lo))))
          (leb_true_le (nth (Add lo (S (Add i Z))) l) pivot e)) }
def allLeR_step_TZ_ty : Term := prog{
  Π (pivot : Nat) → Π (lo : Nat) → Π (i : Nat) → Π (l : List Nat) →
    Id Bool (Leb (nth (Add lo (S (Add i Z))) l) pivot) True → AllLeR i (S lo) pivot l → AllLeR (S i) (S lo) pivot l }

-- allLeR_step_swap : True/g=S g' step — the scan swap moves the tested ≤-element to the
-- new boundary; interior unchanged (nth_swapL_lt), new far element = old scan (nth_swapL_lo).
def allLeR_step_swap : Term := prog{
  λ (pivot : Nat). λ (lo : Nat). λ (i : Nat). λ (g' : Nat). λ (l : List Nat).
    λ (e : Id Bool (Leb (nth (Add lo (S (Add i (S g')))) l) pivot) True). λ (hL : AllLeR i (S lo) pivot l).
      allLeR_extend_far i (S lo) pivot (swapL (Add lo (S i)) (Add lo (S (Add i (S g')))) l)
        (allLeR_cong i (S lo) pivot l (swapL (Add lo (S i)) (Add lo (S (Add i (S g')))) l)
          (λ (m : Nat). λ (hm : Le (S m) i).
            nth_swapL_lt (Add lo (S i)) (Add lo (S (Add i (S g')))) (Add m (S lo)) l
              (le_rw_l (Add lo (S i)) (Add lo (S (S m))) (S (Add m (S lo)))
                (pos_bridge_ss lo m)
                (le_add_mono_l lo (S (S m)) (S i) hm)))
          hL)
        (le_rw_l pivot (nth (Add lo (S (Add i (S g')))) l) (nth (Add i (S lo)) (swapL (Add lo (S i)) (Add lo (S (Add i (S g')))) l))
          (id_trans Nat
            (nth (Add lo (S (Add i (S g')))) l)
            (nth (Add lo (S i)) (swapL (Add lo (S i)) (Add lo (S (Add i (S g')))) l))
            (nth (Add i (S lo)) (swapL (Add lo (S i)) (Add lo (S (Add i (S g')))) l))
            (id_sym Nat (nth (Add lo (S i)) (swapL (Add lo (S i)) (Add lo (S (Add i (S g')))) l)) (nth (Add lo (S (Add i (S g')))) l)
              (nth_swapL_lo (Add lo (S i)) (Add lo (S (Add i (S g')))) l (bnd_sl lo i g')))
            (id_congr Nat Nat (λ (q : Nat). nth q (swapL (Add lo (S i)) (Add lo (S (Add i (S g')))) l)) (Add lo (S i)) (Add i (S lo))
              (id_sym Nat (Add i (S lo)) (Add lo (S i)) (add_swap_succ i lo))))
          (leb_true_le (nth (Add lo (S (Add i (S g')))) l) pivot e)) }
def allLeR_step_swap_ty : Term := prog{
  Π (pivot : Nat) → Π (lo : Nat) → Π (i : Nat) → Π (g' : Nat) → Π (l : List Nat) →
    Id Bool (Leb (nth (Add lo (S (Add i (S g')))) l) pivot) True → AllLeR i (S lo) pivot l →
    AllLeR (S i) (S lo) pivot (swapL (Add lo (S i)) (Add lo (S (Add i (S g')))) l) }

-- partScanRangeL_allLeR : the scanned ≤-region [lo, lo+finalI) is all ≤ pivot. Induction
-- on k mirroring count_partScanRangeL's bound threading; the AllLeR precondition grows via
-- the step helpers (leb fact from remember-scrutinee, threaded through the g-elim); the base
-- converts to offset lo via allLeR_base_swap / allLeR_empty.
def partScanRangeL_allLeR : Term := prog{
  λ (pivot : Nat). λ (lo : Nat). λ (k : Nat).
    elim k return (λ (kz : Nat). Π (i : Nat) → Π (g : Nat) → Π (l : List Nat) →
        Le (Add lo (S (Add kz (Add i g)))) (Len l) →
        Id Nat (nth lo l) pivot →
        AllLeR i (S lo) pivot l →
        AllLeR (partScanIdxRangeL pivot lo kz i g l) lo pivot (partScanRangeL pivot lo kz i g l)) {
      Z => λ (i : Nat). λ (g : Nat). λ (l : List Nat).
        λ (hle : Le (Add lo (S (Add Z (Add i g)))) (Len l)). λ (hpv : Id Nat (nth lo l) pivot). λ (hL : AllLeR i (S lo) pivot l).
        elim i return (λ (iz : Nat).
            Le (Add lo (S (Add Z (Add iz g)))) (Len l) → Id Nat (nth lo l) pivot → AllLeR iz (S lo) pivot l →
            AllLeR iz lo pivot (elim iz return (λ (iy : Nat). List Nat) { Z => l, S (i') iih => swapL lo (Add lo (S i')) l })) {
          Z => λ (hle0 : Le (Add lo (S (Add Z (Add Z g)))) (Len l)). λ (hpv0 : Id Nat (nth lo l) pivot). λ (hL0 : AllLeR Z (S lo) pivot l).
            allLeR_empty lo pivot l,
          S (i') iih => λ (hle0 : Le (Add lo (S (Add Z (Add (S i') g)))) (Len l)). λ (hpv0 : Id Nat (nth lo l) pivot). λ (hL0 : AllLeR (S i') (S lo) pivot l).
            allLeR_base_swap pivot lo i' l hL0
        } hle hpv hL,
      S (k') ih => λ (i : Nat). λ (g : Nat). λ (l : List Nat).
        λ (hle : Le (Add lo (S (Add (S k') (Add i g)))) (Len l)). λ (hpv : Id Nat (nth lo l) pivot). λ (hL : AllLeR i (S lo) pivot l).
        elim (Leb (nth (Add lo (S (Add i g))) l) pivot)
          return (λ (b : Bool). Id Bool (Leb (nth (Add lo (S (Add i g))) l) pivot) b →
            AllLeR (elim b return (λ (bw : Bool). Nat) {
                True => elim g return (λ (gz : Nat). Nat) {
                  Z => partScanIdxRangeL pivot lo k' (S i) Z l,
                  S (g') gih => partScanIdxRangeL pivot lo k' (S i) (S g') (swapL (Add lo (S i)) (Add lo (S (Add i g))) l) },
                False => partScanIdxRangeL pivot lo k' i (S g) l }) lo pivot
              (elim b return (λ (bw : Bool). List Nat) {
                True => elim g return (λ (gz : Nat). List Nat) {
                  Z => partScanRangeL pivot lo k' (S i) Z l,
                  S (g') gih => partScanRangeL pivot lo k' (S i) (S g') (swapL (Add lo (S i)) (Add lo (S (Add i g))) l) },
                False => partScanRangeL pivot lo k' i (S g) l })) {
          True => λ (e : Id Bool (Leb (nth (Add lo (S (Add i g))) l) pivot) True).
            (elim g return (λ (gz : Nat).
                Id Bool (Leb (nth (Add lo (S (Add i gz))) l) pivot) True →
                Le (Add lo (S (Add (S k') (Add i gz)))) (Len l) →
                AllLeR (elim gz return (λ (gy : Nat). Nat) {
                    Z => partScanIdxRangeL pivot lo k' (S i) Z l,
                    S (g') gih => partScanIdxRangeL pivot lo k' (S i) (S g') (swapL (Add lo (S i)) (Add lo (S (Add i gz))) l) }) lo pivot
                  (elim gz return (λ (gy : Nat). List Nat) {
                    Z => partScanRangeL pivot lo k' (S i) Z l,
                    S (g') gih => partScanRangeL pivot lo k' (S i) (S g') (swapL (Add lo (S i)) (Add lo (S (Add i gz))) l) })) {
              Z => λ (e0 : Id Bool (Leb (nth (Add lo (S (Add i Z))) l) pivot) True). λ (hleZ : Le (Add lo (S (Add (S k') (Add i Z)))) (Len l)).
                ih (S i) Z l
                  (le_rw_l (Len l) (Add lo (S (Add (S k') (Add i Z)))) (Add lo (S (Add k' (Add (S i) Z))))
                    (id_congr Nat Nat (λ (a : Nat). Add lo (S a)) (Add (S k') (Add i Z)) (Add k' (Add (S i) Z)) (hshift_true k' i Z))
                    hleZ)
                  hpv
                  (allLeR_step_TZ pivot lo i l e0 hL),
              S (g') gih => λ (e0 : Id Bool (Leb (nth (Add lo (S (Add i (S g')))) l) pivot) True). λ (hleS : Le (Add lo (S (Add (S k') (Add i (S g'))))) (Len l)).
                ih (S i) (S g') (swapL (Add lo (S i)) (Add lo (S (Add i (S g')))) l)
                  (le_rw_r (Add lo (S (Add k' (Add (S i) (S g'))))) (Len l)
                     (Len (swapL (Add lo (S i)) (Add lo (S (Add i (S g')))) l))
                     (id_sym Nat (Len (swapL (Add lo (S i)) (Add lo (S (Add i (S g')))) l)) (Len l)
                       (len_swapL (Add lo (S i)) (Add lo (S (Add i (S g')))) l))
                     (le_rw_l (Len l) (Add lo (S (Add (S k') (Add i (S g'))))) (Add lo (S (Add k' (Add (S i) (S g')))))
                       (id_congr Nat Nat (λ (a : Nat). Add lo (S a)) (Add (S k') (Add i (S g'))) (Add k' (Add (S i) (S g'))) (hshift_true k' i (S g')))
                       hleS))
                  (id_trans Nat (nth lo (swapL (Add lo (S i)) (Add lo (S (Add i (S g')))) l)) (nth lo l) pivot
                    (nth_swapL_lt (Add lo (S i)) (Add lo (S (Add i (S g')))) lo l (le_add_succ lo i))
                    hpv)
                  (allLeR_step_swap pivot lo i g' l e0 hL)
            }) e hle,
          False => λ (efalse : Id Bool (Leb (nth (Add lo (S (Add i g))) l) pivot) False).
            ih i (S g) l
              (le_rw_l (Len l) (Add lo (S (Add (S k') (Add i g)))) (Add lo (S (Add k' (Add i (S g)))))
                (id_congr Nat Nat (λ (a : Nat). Add lo (S a)) (Add (S k') (Add i g)) (Add k' (Add i (S g))) (hshift_false k' i g))
                hle)
              hpv
              hL
        } Refl
    } }
def partScanRangeL_allLeR_ty : Term := prog{
  Π (pivot : Nat) → Π (lo : Nat) → Π (k : Nat) → Π (i : Nat) → Π (g : Nat) → Π (l : List Nat) →
    Le (Add lo (S (Add k (Add i g)))) (Len l) →
    Id Nat (nth lo l) pivot →
    AllLeR i (S lo) pivot l →
    AllLeR (partScanIdxRangeL pivot lo k i g l) lo pivot (partScanRangeL pivot lo k i g l) }
/-! ## AllGtR (gap-side) region invariant — the mirror of the ≤-region (§22, M22-c step 2)

    The gap's OFFSET shifts each step (`add (S i) lo` → `add (S (S i)) lo`), unlike the
    ≤-region's fixed `S lo`, and the asymmetry flips: the gap GROWS in the False branch
    (scan element > pivot, `allGtR_step_false` via leb_false_gt + extend_far), the True/Sg'
    swap ROTATES the old boundary (first gap element) to the gap's far end
    (`allGtR_step_swap` via nth_swapL_hi, needing a len bound), and True/g=0 is the empty
    gap (`allGtR_empty`). `off_bridge` / `pos_bridge_scan` / `bnd_gap_upper` carry the
    (messier) offset arithmetic. -/

def allGtR_extend_far : Term := prog{
  λ (w : Nat). λ (lo : Nat). λ (p : Nat). λ (l : List Nat).
    λ (h : AllGtR w lo p l). λ (hnew : Le (S p) (nth (Add w lo) l)).
    λ (m : Nat).
      elim (Leb (S m) w) return (λ (b : Bool). Id Bool (Leb (S m) w) b → Le (S m) (S w) → Le (S p) (nth (Add m lo) l)) {
        True => λ (e : Id Bool (Leb (S m) w) True). λ (hm : Le (S m) (S w)). h m (leb_true_le (S m) w e),
        False => λ (e : Id Bool (Leb (S m) w) False). λ (hm : Le (S m) (S w)).
          le_rw_r (S p) (nth (Add w lo) l) (nth (Add m lo) l)
            (id_congr Nat Nat (λ (q : Nat). nth q l) (Add w lo) (Add m lo)
              (id_congr Nat Nat (λ (z : Nat). Add z lo) w m (id_sym Nat m w (le_antisym m w hm (leb_false_gt (S m) w e)))))
            hnew
      } Refl }
def allGtR_extend_far_ty : Term := prog{
  Π (w : Nat) → Π (lo : Nat) → Π (p : Nat) → Π (l : List Nat) →
    AllGtR w lo p l → Le (S p) (nth (Add w lo) l) → AllGtR (S w) lo p l }

def allGtR_cong : Term := prog{
  λ (w : Nat). λ (off : Nat). λ (p : Nat). λ (l : List Nat). λ (l' : List Nat).
    λ (heq : Π (m : Nat) → Le (S m) w → Id Nat (nth (Add m off) l') (nth (Add m off) l)).
    λ (h : AllGtR w off p l).
    λ (m : Nat). λ (hm : Le (S m) w).
      le_rw_r (S p) (nth (Add m off) l) (nth (Add m off) l')
        (id_sym Nat (nth (Add m off) l') (nth (Add m off) l) (heq m hm))
        (h m hm) }
def allGtR_cong_ty : Term := prog{
  Π (w : Nat) → Π (off : Nat) → Π (p : Nat) → Π (l : List Nat) → Π (l' : List Nat) →
    (Π (m : Nat) → Le (S m) w → Id Nat (nth (Add m off) l') (nth (Add m off) l)) →
    AllGtR w off p l → AllGtR w off p l' }

def off_bridge : Term := prog{
  λ (lo : Nat). λ (i' : Nat).
    id_congr Nat Nat (λ (z : Nat). S z) (S (Add i' lo)) (Add lo (S i'))
      (id_trans Nat (S (Add i' lo)) (S (Add lo i')) (Add lo (S i'))
        (id_congr Nat Nat (λ (z : Nat). S z) (Add i' lo) (Add lo i') (add_comm i' lo))
        (id_sym Nat (Add lo (S i')) (S (Add lo i')) (add_succ lo i'))) }
def off_bridge_ty : Term := prog{ Π (lo : Nat) → Π (i' : Nat) → Id Nat (Add (S (S i')) lo) (S (Add lo (S i'))) }

def allGtR_base_swap : Term := prog{
  λ (pivot : Nat). λ (lo : Nat). λ (i' : Nat). λ (g : Nat). λ (l : List Nat).
    λ (hG : AllGtR g (Add (S (S i')) lo) pivot l).
      allGtR_cong g (Add (S (S i')) lo) pivot l (swapL lo (Add lo (S i')) l)
        (λ (m : Nat). λ (hm : Le (S m) g).
          nth_swapL_gt lo (Add lo (S i')) (Add m (Add (S (S i')) lo)) l
            (le_rw_l (Add m (Add (S (S i')) lo)) (Add (S (S i')) lo) (S (Add lo (S i')))
              (off_bridge lo i')
              (le_add_l (Add (S (S i')) lo) m)))
        hG }
def allGtR_base_swap_ty : Term := prog{
  Π (pivot : Nat) → Π (lo : Nat) → Π (i' : Nat) → Π (g : Nat) → Π (l : List Nat) →
    AllGtR g (Add (S (S i')) lo) pivot l → AllGtR g (Add (S (S i')) lo) pivot (swapL lo (Add lo (S i')) l) }

def pos_bridge_scan : Term := prog{
  λ (lo : Nat). λ (i : Nat). λ (g : Nat).
    id_trans Nat (Add lo (S (Add i g))) (S (Add lo (Add i g))) (Add g (Add (S i) lo))
      (add_succ lo (Add i g))
      (id_trans Nat (S (Add lo (Add i g))) (S (Add g (Add i lo))) (Add g (Add (S i) lo))
        (id_congr Nat Nat (λ (z : Nat). S z) (Add lo (Add i g)) (Add g (Add i lo))
          (id_trans Nat (Add lo (Add i g)) (Add (Add lo i) g) (Add g (Add i lo))
            (id_sym Nat (Add (Add lo i) g) (Add lo (Add i g)) (add_assoc lo i g))
            (id_trans Nat (Add (Add lo i) g) (Add g (Add lo i)) (Add g (Add i lo))
              (add_comm (Add lo i) g)
              (id_congr Nat Nat (λ (z : Nat). Add g z) (Add lo i) (Add i lo) (add_comm lo i)))))
        (id_sym Nat (Add g (Add (S i) lo)) (S (Add g (Add i lo))) (add_succ g (Add i lo)))) }
def pos_bridge_scan_ty : Term := prog{ Π (lo : Nat) → Π (i : Nat) → Π (g : Nat) → Id Nat (Add lo (S (Add i g))) (Add g (Add (S i) lo)) }

def allGtR_step_false : Term := prog{
  λ (pivot : Nat). λ (lo : Nat). λ (i : Nat). λ (g : Nat). λ (l : List Nat).
    λ (efalse : Id Bool (Leb (nth (Add lo (S (Add i g))) l) pivot) False). λ (hG : AllGtR g (Add (S i) lo) pivot l).
      allGtR_extend_far g (Add (S i) lo) pivot l hG
        (le_rw_r (S pivot) (nth (Add lo (S (Add i g))) l) (nth (Add g (Add (S i) lo)) l)
          (id_congr Nat Nat (λ (q : Nat). nth q l) (Add lo (S (Add i g))) (Add g (Add (S i) lo)) (pos_bridge_scan lo i g))
          (leb_false_gt (nth (Add lo (S (Add i g))) l) pivot efalse)) }
def allGtR_step_false_ty : Term := prog{
  Π (pivot : Nat) → Π (lo : Nat) → Π (i : Nat) → Π (g : Nat) → Π (l : List Nat) →
    Id Bool (Leb (nth (Add lo (S (Add i g))) l) pivot) False → AllGtR g (Add (S i) lo) pivot l →
    AllGtR (S g) (Add (S i) lo) pivot l }

def bnd_gap_upper : Term := prog{
  λ (lo : Nat). λ (i : Nat). λ (g' : Nat). λ (m : Nat). λ (hm : Le (S m) g').
    le_rw_r (S (Add m (Add (S (S i)) lo))) (Add lo (S (S (Add i g')))) (Add lo (S (Add i (S g'))))
      (id_congr Nat Nat (λ (z : Nat). Add lo (S z)) (S (Add i g')) (Add i (S g')) (id_sym Nat (Add i (S g')) (S (Add i g')) (add_succ i g')))
      (le_rw_l (Add lo (S (S (Add i g')))) (Add lo (S (S (S (Add i m))))) (S (Add m (Add (S (S i)) lo)))
        (id_trans Nat (Add lo (S (S (S (Add i m))))) (S (Add lo (S (S (Add i m))))) (S (Add m (Add (S (S i)) lo)))
          (add_succ lo (S (S (Add i m))))
          (id_congr Nat Nat (λ (z : Nat). S z) (Add lo (S (S (Add i m)))) (Add m (Add (S (S i)) lo)) (pos_bridge_scan lo (S i) m)))
        (le_add_mono_l lo (S (S (S (Add i m)))) (S (S (Add i g')))
          (le_rw_l (Add i g') (Add i (S m)) (S (Add i m)) (add_succ i m) (le_add_mono_l i (S m) g' hm)))) }
def bnd_gap_upper_ty : Term := prog{
  Π (lo : Nat) → Π (i : Nat) → Π (g' : Nat) → Π (m : Nat) → Le (S m) g' →
    Le (S (Add m (Add (S (S i)) lo))) (Add lo (S (Add i (S g')))) }

def allGtR_step_swap : Term := prog{
  λ (pivot : Nat). λ (lo : Nat). λ (i : Nat). λ (g' : Nat). λ (l : List Nat).
    λ (hlen : Le (S (Add lo (S (Add i (S g'))))) (Len l)).
    λ (e : Id Bool (Leb (nth (Add lo (S (Add i (S g')))) l) pivot) True). λ (hG : AllGtR (S g') (Add (S i) lo) pivot l).
      allGtR_extend_far g' (Add (S (S i)) lo) pivot (swapL (Add lo (S i)) (Add lo (S (Add i (S g')))) l)
        (allGtR_cong g' (Add (S (S i)) lo) pivot l (swapL (Add lo (S i)) (Add lo (S (Add i (S g')))) l)
          (λ (m : Nat). λ (hm : Le (S m) g').
            nth_swapL_mid (Add lo (S i)) (Add lo (S (Add i (S g')))) (Add m (Add (S (S i)) lo)) l
              (le_rw_l (Add m (Add (S (S i)) lo)) (Add (S (S i)) lo) (S (Add lo (S i)))
                (off_bridge lo i)
                (le_add_l (Add (S (S i)) lo) m))
              (bnd_gap_upper lo i g' m hm))
          (λ (m : Nat). λ (hm : Le (S m) g').
            le_rw_r (S pivot) (nth (Add (S m) (Add (S i) lo)) l) (nth (Add m (Add (S (S i)) lo)) l)
              (id_congr Nat Nat (λ (q : Nat). nth q l) (Add (S m) (Add (S i) lo)) (Add m (Add (S (S i)) lo))
                (id_sym Nat (Add m (Add (S (S i)) lo)) (Add (S m) (Add (S i) lo)) (add_succ m (S (Add i lo)))))
              (hG (S m) hm)))
        (le_rw_r (S pivot) (nth (Add lo (S i)) l) (nth (Add g' (Add (S (S i)) lo)) (swapL (Add lo (S i)) (Add lo (S (Add i (S g')))) l))
          (id_trans Nat
            (nth (Add lo (S i)) l)
            (nth (Add lo (S (Add i (S g')))) (swapL (Add lo (S i)) (Add lo (S (Add i (S g')))) l))
            (nth (Add g' (Add (S (S i)) lo)) (swapL (Add lo (S i)) (Add lo (S (Add i (S g')))) l))
            (id_sym Nat (nth (Add lo (S (Add i (S g')))) (swapL (Add lo (S i)) (Add lo (S (Add i (S g')))) l)) (nth (Add lo (S i)) l)
              (nth_swapL_hi (Add lo (S i)) (Add lo (S (Add i (S g')))) l (bnd_sl lo i g') hlen))
            (id_congr Nat Nat (λ (q : Nat). nth q (swapL (Add lo (S i)) (Add lo (S (Add i (S g')))) l)) (Add lo (S (Add i (S g')))) (Add g' (Add (S (S i)) lo))
              (id_trans Nat (Add lo (S (Add i (S g')))) (Add lo (S (S (Add i g')))) (Add g' (Add (S (S i)) lo))
                (id_congr Nat Nat (λ (z : Nat). Add lo (S z)) (Add i (S g')) (S (Add i g')) (add_succ i g'))
                (pos_bridge_scan lo (S i) g'))))
          (le_rw_r (S pivot) (nth (Add (S i) lo) l) (nth (Add lo (S i)) l)
            (id_congr Nat Nat (λ (q : Nat). nth q l) (Add (S i) lo) (Add lo (S i)) (add_comm (S i) lo))
            (allGtR_head g' (Add (S i) lo) pivot l hG))) }
def allGtR_step_swap_ty : Term := prog{
  Π (pivot : Nat) → Π (lo : Nat) → Π (i : Nat) → Π (g' : Nat) → Π (l : List Nat) →
    Le (S (Add lo (S (Add i (S g'))))) (Len l) →
    Id Bool (Leb (nth (Add lo (S (Add i (S g')))) l) pivot) True → AllGtR (S g') (Add (S i) lo) pivot l →
    AllGtR (S g') (Add (S (S i)) lo) pivot (swapL (Add lo (S i)) (Add lo (S (Add i (S g')))) l) }

-- partScanRangeL_allGtR : the scanned gap [lo+1+finalI, …) is all > pivot. Mirror of allLeR;
-- the conclusion OFFSET also depends on leb (motive carries three elim b). NOTE the True arm
-- threads hG through the g-elim (the precondition is indexed by g, refined to S g' in the swap
-- branch) — unlike allLeR whose precondition was indexed by i.
def partScanRangeL_allGtR : Term := prog{
  λ (pivot : Nat). λ (lo : Nat). λ (k : Nat).
    elim k return (λ (kz : Nat). Π (i : Nat) → Π (g : Nat) → Π (l : List Nat) →
        Le (Add lo (S (Add kz (Add i g)))) (Len l) →
        Id Nat (nth lo l) pivot →
        AllGtR g (Add (S i) lo) pivot l →
        AllGtR (partScanGapRangeL pivot lo kz i g l) (Add (S (partScanIdxRangeL pivot lo kz i g l)) lo) pivot (partScanRangeL pivot lo kz i g l)) {
      Z => λ (i : Nat). λ (g : Nat). λ (l : List Nat).
        λ (hle : Le (Add lo (S (Add Z (Add i g)))) (Len l)). λ (hpv : Id Nat (nth lo l) pivot). λ (hG : AllGtR g (Add (S i) lo) pivot l).
        elim i return (λ (iz : Nat).
            Le (Add lo (S (Add Z (Add iz g)))) (Len l) → Id Nat (nth lo l) pivot → AllGtR g (Add (S iz) lo) pivot l →
            AllGtR g (Add (S iz) lo) pivot (elim iz return (λ (iy : Nat). List Nat) { Z => l, S (i') iih => swapL lo (Add lo (S i')) l })) {
          Z => λ (hle0 : Le (Add lo (S (Add Z (Add Z g)))) (Len l)). λ (hpv0 : Id Nat (nth lo l) pivot). λ (hG0 : AllGtR g (Add (S Z) lo) pivot l).
            hG0,
          S (i') iih => λ (hle0 : Le (Add lo (S (Add Z (Add (S i') g)))) (Len l)). λ (hpv0 : Id Nat (nth lo l) pivot). λ (hG0 : AllGtR g (Add (S (S i')) lo) pivot l).
            allGtR_base_swap pivot lo i' g l hG0
        } hle hpv hG,
      S (k') ih => λ (i : Nat). λ (g : Nat). λ (l : List Nat).
        λ (hle : Le (Add lo (S (Add (S k') (Add i g)))) (Len l)). λ (hpv : Id Nat (nth lo l) pivot). λ (hG : AllGtR g (Add (S i) lo) pivot l).
        elim (Leb (nth (Add lo (S (Add i g))) l) pivot)
          return (λ (b : Bool). Id Bool (Leb (nth (Add lo (S (Add i g))) l) pivot) b →
            AllGtR (elim b return (λ (bw : Bool). Nat) {
                True => elim g return (λ (gz : Nat). Nat) {
                  Z => partScanGapRangeL pivot lo k' (S i) Z l,
                  S (g') gih => partScanGapRangeL pivot lo k' (S i) (S g') (swapL (Add lo (S i)) (Add lo (S (Add i g))) l) },
                False => partScanGapRangeL pivot lo k' i (S g) l })
              (Add (S (elim b return (λ (bw : Bool). Nat) {
                True => elim g return (λ (gz : Nat). Nat) {
                  Z => partScanIdxRangeL pivot lo k' (S i) Z l,
                  S (g') gih => partScanIdxRangeL pivot lo k' (S i) (S g') (swapL (Add lo (S i)) (Add lo (S (Add i g))) l) },
                False => partScanIdxRangeL pivot lo k' i (S g) l })) lo) pivot
              (elim b return (λ (bw : Bool). List Nat) {
                True => elim g return (λ (gz : Nat). List Nat) {
                  Z => partScanRangeL pivot lo k' (S i) Z l,
                  S (g') gih => partScanRangeL pivot lo k' (S i) (S g') (swapL (Add lo (S i)) (Add lo (S (Add i g))) l) },
                False => partScanRangeL pivot lo k' i (S g) l })) {
          True => λ (e : Id Bool (Leb (nth (Add lo (S (Add i g))) l) pivot) True).
            (elim g return (λ (gz : Nat).
                Id Bool (Leb (nth (Add lo (S (Add i gz))) l) pivot) True →
                Le (Add lo (S (Add (S k') (Add i gz)))) (Len l) →
                AllGtR gz (Add (S i) lo) pivot l →
                AllGtR (elim gz return (λ (gy : Nat). Nat) {
                    Z => partScanGapRangeL pivot lo k' (S i) Z l,
                    S (g') gih => partScanGapRangeL pivot lo k' (S i) (S g') (swapL (Add lo (S i)) (Add lo (S (Add i gz))) l) })
                  (Add (S (elim gz return (λ (gy : Nat). Nat) {
                    Z => partScanIdxRangeL pivot lo k' (S i) Z l,
                    S (g') gih => partScanIdxRangeL pivot lo k' (S i) (S g') (swapL (Add lo (S i)) (Add lo (S (Add i gz))) l) })) lo) pivot
                  (elim gz return (λ (gy : Nat). List Nat) {
                    Z => partScanRangeL pivot lo k' (S i) Z l,
                    S (g') gih => partScanRangeL pivot lo k' (S i) (S g') (swapL (Add lo (S i)) (Add lo (S (Add i gz))) l) })) {
              Z => λ (e0 : Id Bool (Leb (nth (Add lo (S (Add i Z))) l) pivot) True). λ (hleZ : Le (Add lo (S (Add (S k') (Add i Z)))) (Len l)). λ (hG0 : AllGtR Z (Add (S i) lo) pivot l).
                ih (S i) Z l
                  (le_rw_l (Len l) (Add lo (S (Add (S k') (Add i Z)))) (Add lo (S (Add k' (Add (S i) Z))))
                    (id_congr Nat Nat (λ (a : Nat). Add lo (S a)) (Add (S k') (Add i Z)) (Add k' (Add (S i) Z)) (hshift_true k' i Z))
                    hleZ)
                  hpv
                  (allGtR_empty (Add (S (S i)) lo) pivot l),
              S (g') gih => λ (e0 : Id Bool (Leb (nth (Add lo (S (Add i (S g')))) l) pivot) True). λ (hleS : Le (Add lo (S (Add (S k') (Add i (S g'))))) (Len l)). λ (hG0 : AllGtR (S g') (Add (S i) lo) pivot l).
                ih (S i) (S g') (swapL (Add lo (S i)) (Add lo (S (Add i (S g')))) l)
                  (le_rw_r (Add lo (S (Add k' (Add (S i) (S g'))))) (Len l)
                     (Len (swapL (Add lo (S i)) (Add lo (S (Add i (S g')))) l))
                     (id_sym Nat (Len (swapL (Add lo (S i)) (Add lo (S (Add i (S g')))) l)) (Len l)
                       (len_swapL (Add lo (S i)) (Add lo (S (Add i (S g')))) l))
                     (le_rw_l (Len l) (Add lo (S (Add (S k') (Add i (S g'))))) (Add lo (S (Add k' (Add (S i) (S g')))))
                       (id_congr Nat Nat (λ (a : Nat). Add lo (S a)) (Add (S k') (Add i (S g'))) (Add k' (Add (S i) (S g'))) (hshift_true k' i (S g')))
                       hleS))
                  (id_trans Nat (nth lo (swapL (Add lo (S i)) (Add lo (S (Add i (S g')))) l)) (nth lo l) pivot
                    (nth_swapL_lt (Add lo (S i)) (Add lo (S (Add i (S g')))) lo l (le_add_succ lo i))
                    hpv)
                  (allGtR_step_swap pivot lo i g' l
                    (le_trans (S (Add lo (S (Add i (S g'))))) (Add lo (S (S (Add k' (Add i (S g')))))) (Len l)
                      (le_rw_l (Add lo (S (S (Add k' (Add i (S g'))))))
                        (Add lo (S (S (Add i (S g'))))) (S (Add lo (S (Add i (S g')))))
                        (add_succ lo (S (Add i (S g'))))
                        (le_add_mono_l lo (S (S (Add i (S g')))) (S (S (Add k' (Add i (S g')))))
                          (le_add_l (Add i (S g')) k')))
                      hleS)
                    e0 hG0)
            }) e hle hG,
          False => λ (efalse : Id Bool (Leb (nth (Add lo (S (Add i g))) l) pivot) False).
            ih i (S g) l
              (le_rw_l (Len l) (Add lo (S (Add (S k') (Add i g)))) (Add lo (S (Add k' (Add i (S g)))))
                (id_congr Nat Nat (λ (a : Nat). Add lo (S a)) (Add (S k') (Add i g)) (Add k' (Add i (S g))) (hshift_false k' i g))
                hle)
              hpv
              (allGtR_step_false pivot lo i g l efalse hG)
        } Refl
    } }
def partScanRangeL_allGtR_ty : Term := prog{
  Π (pivot : Nat) → Π (lo : Nat) → Π (k : Nat) → Π (i : Nat) → Π (g : Nat) → Π (l : List Nat) →
    Le (Add lo (S (Add k (Add i g)))) (Len l) →
    Id Nat (nth lo l) pivot →
    AllGtR g (Add (S i) lo) pivot l →
    AllGtR (partScanGapRangeL pivot lo k i g l) (Add (S (partScanIdxRangeL pivot lo k i g l)) lo) pivot (partScanRangeL pivot lo k i g l) }
-- The pivot ends at position `add finalI lo`. Induction on k mirroring
-- count_partScanRangeL's bound threading, PLUS threading the pivot-fact
-- `Id (nth lo l) pivot` (updated across the step swap via nth_swapL_lt — lo is below
-- both swap indices). Base (k=Z) places the pivot: i=Z is the pivot-fact directly;
-- i=S i' swaps lo↔lo+i, so nth_swapL_hi reads old-lo (=pivot) at the boundary, bridged
-- from index-first `add (S i') lo` to offset-first `add lo (S i')` by add_comm.
def partScanRangeL_pivot : Term := prog{
  λ (pivot : Nat). λ (lo : Nat). λ (k : Nat).
    elim k return (λ (kz : Nat). Π (i : Nat) → Π (g : Nat) → Π (l : List Nat) →
        Le (Add lo (S (Add kz (Add i g)))) (Len l) →
        Id Nat (nth lo l) pivot →
        Id Nat (nth (Add (partScanIdxRangeL pivot lo kz i g l) lo) (partScanRangeL pivot lo kz i g l)) pivot) {
      Z => λ (i : Nat). λ (g : Nat). λ (l : List Nat).
        λ (hle : Le (Add lo (S (Add Z (Add i g)))) (Len l)). λ (hpv : Id Nat (nth lo l) pivot).
        elim i return (λ (iz : Nat).
            Le (Add lo (S (Add Z (Add iz g)))) (Len l) →
            Id Nat (nth (Add iz lo) (elim iz return (λ (iy : Nat). List Nat) { Z => l, S (i') iih => swapL lo (Add lo (S i')) l })) pivot) {
          Z => λ (hle0 : Le (Add lo (S (Add Z (Add Z g)))) (Len l)). hpv,
          S (i') iih => λ (hle0 : Le (Add lo (S (Add Z (Add (S i') g)))) (Len l)).
            id_trans Nat
              (nth (Add (S i') lo) (swapL lo (Add lo (S i')) l))
              (nth (Add lo (S i')) (swapL lo (Add lo (S i')) l))
              pivot
              (id_congr Nat Nat (λ (p : Nat). nth p (swapL lo (Add lo (S i')) l)) (Add (S i') lo) (Add lo (S i')) (add_comm (S i') lo))
              (id_trans Nat
                (nth (Add lo (S i')) (swapL lo (Add lo (S i')) l))
                (nth lo l)
                pivot
                (nth_swapL_hi lo (Add lo (S i')) l (le_add_succ lo i')
                  (le_trans (S (Add lo (S i'))) (Add lo (S (S (Add i' g)))) (Len l)
                    (le_rw_l (Add lo (S (S (Add i' g)))) (Add lo (S (S i'))) (S (Add lo (S i')))
                      (add_succ lo (S i'))
                      (le_add_mono_l lo (S (S i')) (S (S (Add i' g))) (le_add i' g)))
                    hle0))
                hpv)
        } hle,
      S (k') ih => λ (i : Nat). λ (g : Nat). λ (l : List Nat).
        λ (hle : Le (Add lo (S (Add (S k') (Add i g)))) (Len l)). λ (hpv : Id Nat (nth lo l) pivot).
        elim (Leb (nth (Add lo (S (Add i g))) l) pivot)
          return (λ (w : Bool). Id Nat
            (nth (Add (elim w return (λ (ww : Bool). Nat) {
                True => elim g return (λ (gz : Nat). Nat) {
                  Z => partScanIdxRangeL pivot lo k' (S i) Z l,
                  S (g') gih => partScanIdxRangeL pivot lo k' (S i) (S g') (swapL (Add lo (S i)) (Add lo (S (Add i g))) l) },
                False => partScanIdxRangeL pivot lo k' i (S g) l }) lo)
              (elim w return (λ (ww : Bool). List Nat) {
                True => elim g return (λ (gz : Nat). List Nat) {
                  Z => partScanRangeL pivot lo k' (S i) Z l,
                  S (g') gih => partScanRangeL pivot lo k' (S i) (S g') (swapL (Add lo (S i)) (Add lo (S (Add i g))) l) },
                False => partScanRangeL pivot lo k' i (S g) l }))
            pivot) {
          True =>
            (elim g return (λ (gz : Nat).
                Le (Add lo (S (Add (S k') (Add i gz)))) (Len l) →
                Id Nat (nth (Add (elim gz return (λ (gy : Nat). Nat) {
                    Z => partScanIdxRangeL pivot lo k' (S i) Z l,
                    S (g') gih => partScanIdxRangeL pivot lo k' (S i) (S g') (swapL (Add lo (S i)) (Add lo (S (Add i gz))) l) }) lo)
                  (elim gz return (λ (gy : Nat). List Nat) {
                    Z => partScanRangeL pivot lo k' (S i) Z l,
                    S (g') gih => partScanRangeL pivot lo k' (S i) (S g') (swapL (Add lo (S i)) (Add lo (S (Add i gz))) l) })) pivot) {
              Z => λ (hleZ : Le (Add lo (S (Add (S k') (Add i Z)))) (Len l)).
                ih (S i) Z l
                  (le_rw_l (Len l)
                    (Add lo (S (Add (S k') (Add i Z))))
                    (Add lo (S (Add k' (Add (S i) Z))))
                    (id_congr Nat Nat (λ (a : Nat). Add lo (S a))
                      (Add (S k') (Add i Z)) (Add k' (Add (S i) Z)) (hshift_true k' i Z))
                    hleZ)
                  hpv,
              S (g') gih => λ (hleS : Le (Add lo (S (Add (S k') (Add i (S g'))))) (Len l)).
                ih (S i) (S g') (swapL (Add lo (S i)) (Add lo (S (Add i (S g')))) l)
                  (le_rw_r (Add lo (S (Add k' (Add (S i) (S g'))))) (Len l)
                     (Len (swapL (Add lo (S i)) (Add lo (S (Add i (S g')))) l))
                     (id_sym Nat (Len (swapL (Add lo (S i)) (Add lo (S (Add i (S g')))) l)) (Len l)
                       (len_swapL (Add lo (S i)) (Add lo (S (Add i (S g')))) l))
                     (le_rw_l (Len l)
                       (Add lo (S (Add (S k') (Add i (S g')))))
                       (Add lo (S (Add k' (Add (S i) (S g')))))
                       (id_congr Nat Nat (λ (a : Nat). Add lo (S a))
                         (Add (S k') (Add i (S g'))) (Add k' (Add (S i) (S g'))) (hshift_true k' i (S g')))
                       hleS))
                  (id_trans Nat (nth lo (swapL (Add lo (S i)) (Add lo (S (Add i (S g')))) l)) (nth lo l) pivot
                    (nth_swapL_lt (Add lo (S i)) (Add lo (S (Add i (S g')))) lo l (le_add_succ lo i))
                    hpv)
            }) hle,
          False =>
            ih i (S g) l
              (le_rw_l (Len l)
                (Add lo (S (Add (S k') (Add i g))))
                (Add lo (S (Add k' (Add i (S g)))))
                (id_congr Nat Nat (λ (a : Nat). Add lo (S a))
                  (Add (S k') (Add i g)) (Add k' (Add i (S g))) (hshift_false k' i g))
                hle)
              hpv
        }
    } }
def partScanRangeL_pivot_ty : Term := prog{
  Π (pivot : Nat) → Π (lo : Nat) → Π (k : Nat) → Π (i : Nat) → Π (g : Nat) → Π (l : List Nat) →
    Le (Add lo (S (Add k (Add i g)))) (Len l) →
    Id Nat (nth lo l) pivot →
    Id Nat (nth (Add (partScanIdxRangeL pivot lo k i g l) lo) (partScanRangeL pivot lo k i g l)) pivot }
-- partition_pivot : wrapper of partScanRangeL_pivot at i=g=0 (preconditions vacuous;
-- pivot-fact is Refl since the pivot is nth lo l; one add_zero nudge on the bound).
def partition_pivot : Term := prog{
  λ (lo : Nat). λ (cnt : Nat). λ (l : List Nat).
    elim cnt return (λ (cz : Nat).
        Le (Add lo cz) (Len l) →
        Id Nat (nth (Add (elim cz return (λ (cy : Nat). Nat) { Z => Z, S (cnt') rec => partScanIdxRangeL (nth lo l) lo cnt' Z Z l }) lo)
                    (elim cz return (λ (cy : Nat). List Nat) { Z => l, S (cnt') rec => partScanRangeL (nth lo l) lo cnt' Z Z l })) (nth lo l)) {
      Z => λ (hb : Le (Add lo Z) (Len l)). Refl,
      S (cnt') rec => λ (hb : Le (Add lo (S cnt')) (Len l)).
        partScanRangeL_pivot (nth lo l) lo cnt' Z Z l
          (le_rw_l (Len l) (Add lo (S cnt')) (Add lo (S (Add cnt' Z)))
            (id_congr Nat Nat (λ (a : Nat). Add lo (S a)) cnt' (Add cnt' Z)
              (id_sym Nat (Add cnt' Z) cnt' (add_zero cnt')))
            hb)
          Refl } }

-- partition_allLeR : wrapper of partScanRangeL_allLeR at i=g=0 (AllLeR Z precondition vacuous).
def partition_allLeR : Term := prog{
  λ (lo : Nat). λ (cnt : Nat). λ (l : List Nat).
    elim cnt return (λ (cz : Nat).
        Le (Add lo cz) (Len l) →
        AllLeR (elim cz return (λ (cy : Nat). Nat) { Z => Z, S (cnt') rec => partScanIdxRangeL (nth lo l) lo cnt' Z Z l }) lo (nth lo l)
               (elim cz return (λ (cy : Nat). List Nat) { Z => l, S (cnt') rec => partScanRangeL (nth lo l) lo cnt' Z Z l })) {
      Z => λ (hb : Le (Add lo Z) (Len l)). allLeR_empty lo (nth lo l) l,
      S (cnt') rec => λ (hb : Le (Add lo (S cnt')) (Len l)).
        partScanRangeL_allLeR (nth lo l) lo cnt' Z Z l
          (le_rw_l (Len l) (Add lo (S cnt')) (Add lo (S (Add cnt' Z)))
            (id_congr Nat Nat (λ (a : Nat). Add lo (S a)) cnt' (Add cnt' Z)
              (id_sym Nat (Add cnt' Z) cnt' (add_zero cnt')))
            hb)
          Refl
          (allLeR_empty (S lo) (nth lo l) l) } }

def partition_allLeR_ty : Term := prog{
  Π (lo : Nat) → Π (cnt : Nat) → Π (l : List Nat) → Le (Add lo cnt) (Len l) →
    AllLeR (partIdxRangeL lo cnt l) lo (nth lo l) (partitionRangeL lo cnt l) }
-- partition_allGtR : wrapper of partScanRangeL_allGtR at i=g=0 (AllGtR Z precondition vacuous).
def partition_allGtR : Term := prog{
  λ (lo : Nat). λ (cnt : Nat). λ (l : List Nat).
    elim cnt return (λ (cz : Nat).
        Le (Add lo cz) (Len l) →
        AllGtR (elim cz return (λ (cy : Nat). Nat) { Z => Z, S (cnt') rec => partScanGapRangeL (nth lo l) lo cnt' Z Z l })
               (Add (S (elim cz return (λ (cy : Nat). Nat) { Z => Z, S (cnt') rec => partScanIdxRangeL (nth lo l) lo cnt' Z Z l })) lo) (nth lo l)
               (elim cz return (λ (cy : Nat). List Nat) { Z => l, S (cnt') rec => partScanRangeL (nth lo l) lo cnt' Z Z l })) {
      Z => λ (hb : Le (Add lo Z) (Len l)). allGtR_empty (Add (S Z) lo) (nth lo l) l,
      S (cnt') rec => λ (hb : Le (Add lo (S cnt')) (Len l)).
        partScanRangeL_allGtR (nth lo l) lo cnt' Z Z l
          (le_rw_l (Len l) (Add lo (S cnt')) (Add lo (S (Add cnt' Z)))
            (id_congr Nat Nat (λ (a : Nat). Add lo (S a)) cnt' (Add cnt' Z)
              (id_sym Nat (Add cnt' Z) cnt' (add_zero cnt')))
            hb)
          Refl
          (allGtR_empty (Add (S Z) lo) (nth lo l) l) } }

def partition_allGtR_ty : Term := prog{
  Π (lo : Nat) → Π (cnt : Nat) → Π (l : List Nat) → Le (Add lo cnt) (Len l) →
    AllGtR (partGapRangeL lo cnt l) (Add (S (partIdxRangeL lo cnt l)) lo) (nth lo l) (partitionRangeL lo cnt l) }
def partition_pivot_ty : Term := prog{
  Π (lo : Nat) → Π (cnt : Nat) → Π (l : List Nat) → Le (Add lo cnt) (Len l) →
    Id Nat (nth (Add (partIdxRangeL lo cnt l) lo) (partitionRangeL lo cnt l)) (nth lo l) }

-- Truncated subtraction + its reindex identity — the glue's both-right case maps a
-- whole-range index k>i into the right-segment index `sub k (S i)`, then transports
-- the position `add (sub k (S i)) (add (S i) lo)` back to `add k lo` via add_assoc +
-- `add (sub k (S i)) (S i) = k` (add_comm of add_sub_cancel). sub recurses on the
-- minuend so `sub (S a)(S b) = sub a b`; add_sub_cancel is a clean double induction.
def sub : Term := prog{
  λ (a : Nat).
    elim a return (λ (az : Nat). Nat → Nat) {
      Z => λ (b : Nat). Z,
      S (a') rec => λ (b : Nat). elim b return (λ (bz : Nat). Nat) { Z => S a', S (b') bih => rec b' } } }
def sub_ty : Term := prog{ Π (a : Nat) → Nat → Nat }
def add_sub_cancel : Term := prog{
  λ (a : Nat).
    elim a return (λ (az : Nat). Π (b : Nat) → Le b az → Id Nat (Add b (sub az b)) az) {
      Z => λ (b : Nat).
        elim b return (λ (bz : Nat). Le bz Z → Id Nat (Add bz (sub Z bz)) Z) {
          Z => λ (h : Le Z Z). Refl,
          S (b') bih => λ (h : Le (S b') Z). botElim (Id Nat (Add (S b') (sub Z (S b'))) Z) h },
      S (a') ih => λ (b : Nat).
        elim b return (λ (bz : Nat). Le bz (S a') → Id Nat (Add bz (sub (S a') bz)) (S a')) {
          Z => λ (h : Le Z (S a')). Refl,
          S (b') bih => λ (h : Le (S b') (S a')).
            id_congr Nat Nat (λ (n : Nat). S n) (Add b' (sub a' b')) a' (ih b' h) } } }
def add_sub_cancel_ty : Term := prog{ Π (a : Nat) → Π (b : Nat) → Le b a → Id Nat (Add b (sub a b)) a }

/-! ## The GLUE — assemble a sorted range from sorted halves (§22, M22-c step 4)

    `glue`: given the pivot at position `add i lo`, the left range [lo, lo+i) sorted
    and ≤ pivot, the right range [lo+i+1, …) sorted and > pivot, the WHOLE range
    [lo, lo+i+1+g) is sorted. A nested `leb`-elim on k vs i (the REMEMBER-SCRUTINEE
    idiom `elim (leb X) return (λ w. Id Bool (leb X) w → GOAL) {…} Refl` to recover the
    branch equation) splits the adjacent pair into four cases: both-left (SortedR
    left), left-pivot (k+1=i via le_antisym; AllLeR + hpiv transport), pivot-right
    (k=i; AllGtR at the first right, after g≥1 from `gap_pos`), both-right (k>i;
    reindex the whole-index k into the right segment's `sub k (S i)` via the
    reindex_* helpers, then SortedR right). Every arithmetic bridge is discharged by
    the add-order toolkit — the positional-predicate ↔ offset-model tax, paid once
    per bound. All kernel-green. -/
def le_pred_l : Term := prog{
  λ (a : Nat). λ (b : Nat). λ (h : Le (S a) b).
    le_trans a (S a) b (le_up_r a a (le_refl a)) h }
def le_pred_l_ty : Term := prog{ Π (a : Nat) → Π (b : Nat) → Le (S a) b → Le a b }
def gap_pos : Term := prog{
  λ (i : Nat). λ (g : Nat). λ (h : Le (S i) (Add i g)).
    le_add_cancel_l i (S Z) g
      (le_rw_l (Add i g) (S i) (Add i (S Z))
        (id_sym Nat (Add i (S Z)) (S i)
          (id_trans Nat (Add i (S Z)) (S (Add i Z)) (S i)
            (add_succ i Z)
            (id_congr Nat Nat (λ (n : Nat). S n) (Add i Z) i (add_zero i))))
        h) }
def gap_pos_ty : Term := prog{ Π (i : Nat) → Π (g : Nat) → Le (S i) (Add i g) → Le (S Z) g }
def reindex_pos : Term := prog{
  λ (i : Nat). λ (k : Nat). λ (lo : Nat). λ (hik : Le (S i) k).
    id_trans Nat
      (Add (sub k (S i)) (S (Add i lo)))
      (Add (Add (sub k (S i)) (S i)) lo)
      (Add k lo)
      (id_sym Nat (Add (Add (sub k (S i)) (S i)) lo) (Add (sub k (S i)) (S (Add i lo)))
        (add_assoc (sub k (S i)) (S i) lo))
      (id_congr Nat Nat (λ (x : Nat). Add x lo) (Add (sub k (S i)) (S i)) k
        (id_trans Nat (Add (sub k (S i)) (S i)) (Add (S i) (sub k (S i))) k
          (add_comm (sub k (S i)) (S i))
          (add_sub_cancel k (S i) hik))) }
def reindex_pos_ty : Term := prog{
  Π (i : Nat) → Π (k : Nat) → Π (lo : Nat) → Le (S i) k →
    Id Nat (Add (sub k (S i)) (S (Add i lo))) (Add k lo) }
def reindex_pos_s : Term := prog{
  λ (i : Nat). λ (k : Nat). λ (lo : Nat). λ (hik : Le (S i) k).
    id_trans Nat
      (Add (S (sub k (S i))) (S (Add i lo)))
      (Add (Add (S (sub k (S i))) (S i)) lo)
      (Add (S k) lo)
      (id_sym Nat (Add (Add (S (sub k (S i))) (S i)) lo) (Add (S (sub k (S i))) (S (Add i lo)))
        (add_assoc (S (sub k (S i))) (S i) lo))
      (id_congr Nat Nat (λ (x : Nat). Add x lo) (Add (S (sub k (S i))) (S i)) (S k)
        (id_congr Nat Nat (λ (n : Nat). S n) (Add (sub k (S i)) (S i)) k
          (id_trans Nat (Add (sub k (S i)) (S i)) (Add (S i) (sub k (S i))) k
            (add_comm (sub k (S i)) (S i))
            (add_sub_cancel k (S i) hik)))) }
def reindex_pos_s_ty : Term := prog{
  Π (i : Nat) → Π (k : Nat) → Π (lo : Nat) → Le (S i) k →
    Id Nat (Add (S (sub k (S i))) (S (Add i lo))) (Add (S k) lo) }
def reindex_bnd : Term := prog{
  λ (i : Nat). λ (g : Nat). λ (k : Nat). λ (hik : Le (S i) k). λ (hk : Le (S k) (Add i g)).
    le_add_cancel_l i (S (S (sub k (S i)))) g
      (le_rw_l (Add i g)
        (S (S (Add i (sub k (S i)))))
        (Add i (S (S (sub k (S i)))))
        (id_sym Nat (Add i (S (S (sub k (S i))))) (S (S (Add i (sub k (S i)))))
          (id_trans Nat (Add i (S (S (sub k (S i))))) (S (Add i (S (sub k (S i))))) (S (S (Add i (sub k (S i)))))
            (add_succ i (S (sub k (S i))))
            (id_congr Nat Nat (λ (n : Nat). S n) (Add i (S (sub k (S i)))) (S (Add i (sub k (S i))))
              (add_succ i (sub k (S i))))))
        (le_rw_l (Add i g) (S k) (S (S (Add i (sub k (S i)))))
          (id_congr Nat Nat (λ (n : Nat). S n) k (S (Add i (sub k (S i))))
            (id_sym Nat (S (Add i (sub k (S i)))) k (add_sub_cancel k (S i) hik)))
          hk)) }
def reindex_bnd_ty : Term := prog{
  Π (i : Nat) → Π (g : Nat) → Π (k : Nat) → Le (S i) k → Le (S k) (Add i g) →
    Le (S (S (sub k (S i)))) g }
def glue_left_pivot : Term := prog{
  λ (i : Nat). λ (k : Nat). λ (lo : Nat). λ (pivot : Nat). λ (R : List Nat).
    λ (e1 : Id Bool (Leb (S k) i) True).
    λ (e2 : Id Bool (Leb (S (S k)) i) False).
    λ (hpiv : Id Nat pivot (nth (Add i lo) R)).
    λ (al : AllLeR i lo pivot R).
      le_rw_r (nth (Add k lo) R) pivot (nth (Add (S k) lo) R)
        (id_trans Nat pivot (nth (Add i lo) R) (nth (Add (S k) lo) R)
          hpiv
          (id_congr Nat Nat (λ (x : Nat). nth (Add x lo) R) i (S k)
            (le_antisym i (S k) (leb_false_gt (S (S k)) i e2) (leb_true_le (S k) i e1))))
        (al k (leb_true_le (S k) i e1)) }
def glue_left_pivot_ty : Term := prog{
  Π (i : Nat) → Π (k : Nat) → Π (lo : Nat) → Π (pivot : Nat) → Π (R : List Nat) →
    Id Bool (Leb (S k) i) True → Id Bool (Leb (S (S k)) i) False →
    Id Nat pivot (nth (Add i lo) R) → AllLeR i lo pivot R →
    Le (nth (Add k lo) R) (nth (Add (S k) lo) R) }
def glue_pivot_right : Term := prog{
  λ (i : Nat). λ (g : Nat). λ (k : Nat). λ (lo : Nat). λ (pivot : Nat). λ (R : List Nat).
    λ (e1 : Id Bool (Leb (S k) i) False).
    λ (e2 : Id Bool (Leb (S i) k) False).
    λ (hk : Le (S (S k)) (S (Add i g))).
    λ (hpiv : Id Nat pivot (nth (Add i lo) R)).
    λ (ag : AllGtR g (S (Add i lo)) pivot R).
      le_rw_l (nth (Add (S k) lo) R) pivot (nth (Add k lo) R)
        (id_sym Nat (nth (Add k lo) R) pivot
          (id_trans Nat (nth (Add k lo) R) (nth (Add i lo) R) pivot
            (id_congr Nat Nat (λ (x : Nat). nth (Add x lo) R) k i
              (le_antisym k i (leb_false_gt (S i) k e2) (leb_false_gt (S k) i e1)))
            (id_sym Nat pivot (nth (Add i lo) R) hpiv)))
        (le_rw_r pivot (nth (S (Add i lo)) R) (nth (Add (S k) lo) R)
          (id_congr Nat Nat (λ (x : Nat). nth (S (Add x lo)) R) i k
            (id_sym Nat k i (le_antisym k i (leb_false_gt (S i) k e2) (leb_false_gt (S k) i e1))))
          (le_pred_l pivot (nth (S (Add i lo)) R)
            (ag Z (gap_pos i g
              (le_rw_l (Add i g) (S k) (S i)
                (id_congr Nat Nat (λ (n : Nat). S n) k i
                  (le_antisym k i (leb_false_gt (S i) k e2) (leb_false_gt (S k) i e1)))
                hk))))) }
def glue_pivot_right_ty : Term := prog{
  Π (i : Nat) → Π (g : Nat) → Π (k : Nat) → Π (lo : Nat) → Π (pivot : Nat) → Π (R : List Nat) →
    Id Bool (Leb (S k) i) False → Id Bool (Leb (S i) k) False →
    Le (S (S k)) (S (Add i g)) → Id Nat pivot (nth (Add i lo) R) →
    AllGtR g (S (Add i lo)) pivot R →
    Le (nth (Add k lo) R) (nth (Add (S k) lo) R) }
def glue_both_right : Term := prog{
  λ (i : Nat). λ (g : Nat). λ (k : Nat). λ (lo : Nat). λ (pivot : Nat). λ (R : List Nat).
    λ (e2 : Id Bool (Leb (S i) k) True).
    λ (hk : Le (S (S k)) (S (Add i g))).
    λ (sr : SortedR g (S (Add i lo)) R).
      le_rw_l (nth (Add (S k) lo) R)
        (nth (Add (sub k (S i)) (S (Add i lo))) R)
        (nth (Add k lo) R)
        (id_congr Nat Nat (λ (p : Nat). nth p R) (Add (sub k (S i)) (S (Add i lo))) (Add k lo)
          (reindex_pos i k lo (leb_true_le (S i) k e2)))
        (le_rw_r (nth (Add (sub k (S i)) (S (Add i lo))) R)
          (nth (Add (S (sub k (S i))) (S (Add i lo))) R)
          (nth (Add (S k) lo) R)
          (id_congr Nat Nat (λ (p : Nat). nth p R) (Add (S (sub k (S i))) (S (Add i lo))) (Add (S k) lo)
            (reindex_pos_s i k lo (leb_true_le (S i) k e2)))
          (sr (sub k (S i)) (reindex_bnd i g k (leb_true_le (S i) k e2) hk))) }
def glue_both_right_ty : Term := prog{
  Π (i : Nat) → Π (g : Nat) → Π (k : Nat) → Π (lo : Nat) → Π (pivot : Nat) → Π (R : List Nat) →
    Id Bool (Leb (S i) k) True → Le (S (S k)) (S (Add i g)) →
    SortedR g (S (Add i lo)) R →
    Le (nth (Add k lo) R) (nth (Add (S k) lo) R) }
def glue : Term := prog{
  λ (i : Nat). λ (g : Nat). λ (lo : Nat). λ (pivot : Nat). λ (R : List Nat).
    λ (hpiv : Id Nat pivot (nth (Add i lo) R)).
    λ (sl : SortedR i lo R).
    λ (al : AllLeR i lo pivot R).
    λ (ag : AllGtR g (S (Add i lo)) pivot R).
    λ (sr : SortedR g (S (Add i lo)) R).
    λ (k : Nat). λ (hk : Le (S (S k)) (S (Add i g))).
      (elim (Leb (S k) i) return (λ (w : Bool).
          Id Bool (Leb (S k) i) w → Le (nth (Add k lo) R) (nth (Add (S k) lo) R)) {
        True => λ (e1 : Id Bool (Leb (S k) i) True).
          (elim (Leb (S (S k)) i) return (λ (w2 : Bool).
              Id Bool (Leb (S (S k)) i) w2 → Le (nth (Add k lo) R) (nth (Add (S k) lo) R)) {
            True => λ (e2 : Id Bool (Leb (S (S k)) i) True). sl k (leb_true_le (S (S k)) i e2),
            False => λ (e2 : Id Bool (Leb (S (S k)) i) False). glue_left_pivot i k lo pivot R e1 e2 hpiv al
          }) Refl,
        False => λ (e1 : Id Bool (Leb (S k) i) False).
          (elim (Leb (S i) k) return (λ (w2 : Bool).
              Id Bool (Leb (S i) k) w2 → Le (nth (Add k lo) R) (nth (Add (S k) lo) R)) {
            True => λ (e2 : Id Bool (Leb (S i) k) True). glue_both_right i g k lo pivot R e2 hk sr,
            False => λ (e2 : Id Bool (Leb (S i) k) False). glue_pivot_right i g k lo pivot R e1 e2 hk hpiv ag
          }) Refl
      }) Refl }
def glue_ty : Term := prog{
  Π (i : Nat) → Π (g : Nat) → Π (lo : Nat) → Π (pivot : Nat) → Π (R : List Nat) →
    Id Nat pivot (nth (Add i lo) R) →
    SortedR i lo R →
    AllLeR i lo pivot R →
    AllGtR g (S (Add i lo)) pivot R →
    SortedR g (S (Add i lo)) R →
    SortedR (S (Add i g)) lo R }

/-! ## The KEYSTONE — range bounds survive sorting (§22, M22-c step 3; bridges dispatched)

    `allLeR_sortRange` / `allGtR_sortRange`: sorting the range [lo, lo+w) preserves the
    ≤-bound / >-bound over that range. This is what lets sorted_sortRangeL carry the
    partition invariant's bounds through the two recursive sorts. Positional AllLeR is
    NOT natively perm-invariant, so it routes through the multiset: `noAbove p =
    Π x. Le (S p) x → segCount x = Z` (no element > p in the segment) IS perm-invariant
    (segCount_sortRangeL, on main). Composition (MINE): allLeR_sortRange =
    noAbove_to_allLeR ∘ (id_trans with segCount_sortRangeL) ∘ allLeR_to_noAbove. The
    three bridges + the shared membership helper (nth_seg_count_pos) are MECHANICAL
    count/segment inductions — PROOFS DISPATCHED to dllbc-seg (reusing nth_drop /
    count_split / count_seg_preserved / count_cons on main). Statements elaboration-
    verified. AllGtR mirrors with noBelow = Π x. Le x p → segCount x = Z. -/
-- Keystone bridge helpers: eqb comparison, the count "miss" step, count-zero-by-extension,
-- and take-vs-nth/len facts. All mechanical count/segment inductions.
def eqb_gt_false : Term := prog{
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
def eqb_gt_false_ty : Term := prog{ Π (h : Nat) → Π (x : Nat) → Le (S h) x → Id Bool (Eqb x h) False }

def eqb_lt_false : Term := prog{
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
def eqb_lt_false_ty : Term := prog{ Π (a : Nat) → Π (b : Nat) → Le (S a) b → Id Bool (Eqb a b) False }

def count_cons_miss : Term := prog{
  λ (m : Nat). λ (h : Nat). λ (t : List Nat). λ (hq : Id Bool (Eqb m h) False).
    j Bool False
      (λ (z : Bool). λ (hh : Id Bool False z).
        Id Nat (boolRec (λ (w : Bool). Nat) (S (Count m t)) (Count m t) z) (Count m t))
      Refl (Eqb m h) (id_sym Bool (Eqb m h) False hq) }
def count_cons_miss_ty : Term := prog{
  Π (m : Nat) → Π (h : Nat) → Π (t : List Nat) → Id Bool (Eqb m h) False →
    Id Nat (Count m (Cons h t)) (Count m t) }

def count_zero_ext : Term := prog{
  λ (x : Nat). λ (s : List Nat).
    elim s return (λ (sz : List Nat). (Π (j : Nat) → Le (S j) (Len sz) → Id Bool (Eqb x (nth j sz)) False) → Id Nat (Count x sz) Z) {
      Nil => λ (heq : Π (j : Nat) → Le (S j) (Len Nil) → Id Bool (Eqb x (nth j Nil)) False). Refl,
      Cons (h) (t) ih => λ (heq : Π (j : Nat) → Le (S j) (Len (Cons h t)) → Id Bool (Eqb x (nth j (Cons h t))) False).
        id_trans Nat (Count x (Cons h t)) (Count x t) Z
          (count_cons_miss x h t (heq Z unit))
          (ih (λ (j : Nat). λ (hj : Le (S j) (Len t)). heq (S j) hj)) } }
def count_zero_ext_ty : Term := prog{
  Π (x : Nat) → Π (s : List Nat) →
    (Π (j : Nat) → Le (S j) (Len s) → Id Bool (Eqb x (nth j s)) False) → Id Nat (Count x s) Z }

def nth_take : Term := prog{
  λ (w : Nat).
    elim w return (λ (wz : Nat). Π (j : Nat) → Π (s : List Nat) → Le (S j) wz → Id Nat (nth j (Take wz s)) (nth j s)) {
      Z => λ (j : Nat). λ (s : List Nat). λ (hlt : Le (S j) Z). botElim (Id Nat (nth j (Take Z s)) (nth j s)) hlt,
      S (w') ih => λ (j : Nat). λ (s : List Nat).
        elim j return (λ (jz : Nat). Le (S jz) (S w') → Id Nat (nth jz (Take (S w') s)) (nth jz s)) {
          Z => λ (hlt : Le (S Z) (S w')).
            elim s return (λ (sz : List Nat). Id Nat (nth Z (Take (S w') sz)) (nth Z sz)) {
              Nil => Refl, Cons (h) (t) sih => Refl },
          S (j') jih => λ (hlt : Le (S (S j')) (S w')).
            elim s return (λ (sz : List Nat). Id Nat (nth (S j') (Take (S w') sz)) (nth (S j') sz)) {
              Nil => Refl,
              Cons (h) (t) sih => ih j' t hlt } } } }
def nth_take_ty : Term := prog{
  Π (w : Nat) → Π (j : Nat) → Π (s : List Nat) → Le (S j) w → Id Nat (nth j (Take w s)) (nth j s) }

def len_take_le : Term := prog{
  λ (w : Nat).
    elim w return (λ (wz : Nat). Π (s : List Nat) → Le (Len (Take wz s)) wz) {
      Z => λ (s : List Nat). unit,
      S (w') ih => λ (s : List Nat).
        elim s return (λ (sz : List Nat). Le (Len (Take (S w') sz)) (S w')) {
          Nil => unit,
          Cons (h) (t) sih => ih t } } }
def len_take_le_ty : Term := prog{ Π (w : Nat) → Π (s : List Nat) → Le (Len (Take w s)) w }

-- #2 allLeR_to_noAbove : every segment element ≤ p, so an x>p occurs 0× (count_zero_ext,
-- with each element bridged nth j (take w (drop lo l)) → nth (add j lo) l via nth_take/nth_drop).
def allLeR_to_noAbove : Term := prog{
  λ (w : Nat). λ (lo : Nat). λ (p : Nat). λ (l : List Nat).
    λ (hAll : AllLeR w lo p l). λ (x : Nat). λ (hpx : Le (S p) x).
      count_zero_ext x (Take w (Drop lo l))
        (λ (j : Nat). λ (hj : Le (S j) (Len (Take w (Drop lo l)))).
          eqb_gt_false (nth j (Take w (Drop lo l))) x
            (le_trans (S (nth j (Take w (Drop lo l)))) (S p) x
              (le_rw_l p (nth (Add j lo) l) (nth j (Take w (Drop lo l)))
                (id_sym Nat (nth j (Take w (Drop lo l))) (nth (Add j lo) l)
                  (id_trans Nat (nth j (Take w (Drop lo l))) (nth j (Drop lo l)) (nth (Add j lo) l)
                    (nth_take w j (Drop lo l) (le_trans (S j) (Len (Take w (Drop lo l))) w hj (len_take_le w (Drop lo l))))
                    (id_trans Nat (nth j (Drop lo l)) (nth (Add lo j) l) (nth (Add j lo) l)
                      (nth_drop lo j l)
                      (id_congr Nat Nat (λ (q : Nat). nth q l) (Add lo j) (Add j lo) (add_comm lo j)))))
                (hAll j (le_trans (S j) (Len (Take w (Drop lo l))) w hj (len_take_le w (Drop lo l)))))
              hpx)) }

-- #4 allGtR_to_noBelow : every segment element > p, so an x≤p occurs 0× (mirror of #2).
def allGtR_to_noBelow : Term := prog{
  λ (w : Nat). λ (lo : Nat). λ (p : Nat). λ (l : List Nat).
    λ (hAll : AllGtR w lo p l). λ (x : Nat). λ (hxp : Le x p).
      count_zero_ext x (Take w (Drop lo l))
        (λ (j : Nat). λ (hj : Le (S j) (Len (Take w (Drop lo l)))).
          eqb_lt_false x (nth j (Take w (Drop lo l)))
            (le_trans (S x) (S p) (nth j (Take w (Drop lo l)))
              hxp
              (le_rw_r (S p) (nth (Add j lo) l) (nth j (Take w (Drop lo l)))
                (id_sym Nat (nth j (Take w (Drop lo l))) (nth (Add j lo) l)
                  (id_trans Nat (nth j (Take w (Drop lo l))) (nth j (Drop lo l)) (nth (Add j lo) l)
                    (nth_take w j (Drop lo l) (le_trans (S j) (Len (Take w (Drop lo l))) w hj (len_take_le w (Drop lo l))))
                    (id_trans Nat (nth j (Drop lo l)) (nth (Add lo j) l) (nth (Add j lo) l)
                      (nth_drop lo j l)
                      (id_congr Nat Nat (λ (q : Nat). nth q l) (Add lo j) (Add j lo) (add_comm lo j)))))
                (hAll j (le_trans (S j) (Len (Take w (Drop lo l))) w hj (len_take_le w (Drop lo l))))))) }

-- Membership side (#1/#3/#5): the range-fits bound makes the element genuinely present.
def eqb_refl : Term := prog{
  λ (n : Nat). elim n return (λ (nz : Nat). Id Bool (Eqb nz nz) True) {
    Z => Refl,
    S (n') ih => ih } }
def eqb_refl_ty : Term := prog{ Π (n : Nat) → Id Bool (Eqb n n) True }

def len_drop_bound : Term := prog{
  λ (lo : Nat).
    elim lo return (λ (loz : Nat). Π (k : Nat) → Π (l : List Nat) → Le (Add loz k) (Len l) → Le k (Len (Drop loz l))) {
      Z => λ (k : Nat). λ (l : List Nat). λ (hb : Le (Add Z k) (Len l)). hb,
      S (lo') ih => λ (k : Nat). λ (l : List Nat).
        elim l return (λ (lz : List Nat). Le (Add (S lo') k) (Len lz) → Le k (Len (Drop (S lo') lz))) {
          Nil => λ (hb : Le (Add (S lo') k) (Len Nil)). botElim (Le k (Len (Drop (S lo') Nil))) hb,
          Cons (h) (t) lih => λ (hb : Le (Add (S lo') k) (Len (Cons h t))). ih k t hb } } }
def len_drop_bound_ty : Term := prog{
  Π (lo : Nat) → Π (k : Nat) → Π (l : List Nat) → Le (Add lo k) (Len l) → Le k (Len (Drop lo l)) }

def count_take_nth_pos : Term := prog{
  λ (w : Nat).
    elim w return (λ (wz : Nat). Π (m : Nat) → Π (s : List Nat) → Le (S m) wz → Le (S m) (Len s) → Le (S Z) (Count (nth m s) (Take wz s))) {
      Z => λ (m : Nat). λ (s : List Nat). λ (hw : Le (S m) Z). λ (hs : Le (S m) (Len s)). botElim (Le (S Z) (Count (nth m s) (Take Z s))) hw,
      S (w') ih => λ (m : Nat). λ (s : List Nat). λ (hw : Le (S m) (S w')). λ (hs : Le (S m) (Len s)).
        elim s return (λ (sz : List Nat). Le (S m) (Len sz) → Le (S Z) (Count (nth m sz) (Take (S w') sz))) {
          Nil => λ (hs0 : Le (S m) (Len Nil)). botElim (Le (S Z) (Count (nth m Nil) (Take (S w') Nil))) hs0,
          Cons (h) (t) sih => λ (hs0 : Le (S m) (Len (Cons h t))).
            elim m return (λ (mz : Nat). Le (S mz) (S w') → Le (S mz) (Len (Cons h t)) → Le (S Z) (Count (nth mz (Cons h t)) (Take (S w') (Cons h t)))) {
              Z => λ (hw1 : Le (S Z) (S w')). λ (hs1 : Le (S Z) (Len (Cons h t))).
                le_rw_r (S Z) (S (Count h (Take w' t))) (Count h (Cons h (Take w' t)))
                  (id_sym Nat (Count h (Cons h (Take w' t))) (S (Count h (Take w' t)))
                    (count_cons_hit h h (Take w' t) (eqb_refl h)))
                  unit,
              S (m') mih => λ (hw1 : Le (S (S m')) (S w')). λ (hs1 : Le (S (S m')) (Len (Cons h t))).
                elim (Eqb (nth m' t) h) return (λ (b : Bool). Le (S Z) (boolRec (λ (bw : Bool). Nat) (S (Count (nth m' t) (Take w' t))) (Count (nth m' t) (Take w' t)) b)) {
                  True => unit,
                  False => ih m' t hw1 hs1 }
            } hw hs0 } hs } }
def count_take_nth_pos_ty : Term := prog{
  Π (w : Nat) → Π (m : Nat) → Π (s : List Nat) → Le (S m) w → Le (S m) (Len s) →
    Le (S Z) (Count (nth m s) (Take w s)) }

-- #1 nth_seg_count_pos : element at range position lo+m occurs ≥1× in the segment (needs range-fits).
def nth_seg_count_pos : Term := prog{
  λ (m : Nat). λ (w : Nat). λ (lo : Nat). λ (l : List Nat).
    λ (hmw : Le (S m) w). λ (hrange : Le (Add lo w) (Len l)).
      le_rw_r (S Z) (Count (nth m (Drop lo l)) (Take w (Drop lo l))) (Count (nth (Add m lo) l) (Take w (Drop lo l)))
        (id_congr Nat Nat (λ (q : Nat). Count q (Take w (Drop lo l))) (nth m (Drop lo l)) (nth (Add m lo) l)
          (id_trans Nat (nth m (Drop lo l)) (nth (Add lo m) l) (nth (Add m lo) l)
            (nth_drop lo m l)
            (id_congr Nat Nat (λ (q : Nat). nth q l) (Add lo m) (Add m lo) (add_comm lo m))))
        (count_take_nth_pos w m (Drop lo l) hmw
          (len_drop_bound lo (S m) l
            (le_trans (Add lo (S m)) (Add lo w) (Len l) (le_add_mono_l lo (S m) w hmw) hrange))) }

-- #3 noAbove_to_allLeR : no element > p in the segment ⟹ range ≤ p (leb + contradiction via #1).
def noAbove_to_allLeR : Term := prog{
  λ (w : Nat). λ (lo : Nat). λ (p : Nat). λ (l : List Nat).
    λ (hrange : Le (Add lo w) (Len l)). λ (hnoAbove : Π (x : Nat) → Le (S p) x → Id Nat (segCount x lo w l) Z).
    λ (m : Nat). λ (hm : Le (S m) w).
      elim (Leb (nth (Add m lo) l) p) return (λ (b : Bool). Id Bool (Leb (nth (Add m lo) l) p) b → Le (nth (Add m lo) l) p) {
        True => λ (e : Id Bool (Leb (nth (Add m lo) l) p) True). leb_true_le (nth (Add m lo) l) p e,
        False => λ (e : Id Bool (Leb (nth (Add m lo) l) p) False).
          botElim (Le (nth (Add m lo) l) p)
            (le_rw_r (S Z) (segCount (nth (Add m lo) l) lo w l) Z
              (hnoAbove (nth (Add m lo) l) (leb_false_gt (nth (Add m lo) l) p e))
              (nth_seg_count_pos m w lo l hm hrange))
      } Refl }

-- #5 noBelow_to_allGtR : mirror of #3.
def noBelow_to_allGtR : Term := prog{
  λ (w : Nat). λ (lo : Nat). λ (p : Nat). λ (l : List Nat).
    λ (hrange : Le (Add lo w) (Len l)). λ (hnoBelow : Π (x : Nat) → Le x p → Id Nat (segCount x lo w l) Z).
    λ (m : Nat). λ (hm : Le (S m) w).
      elim (Leb (nth (Add m lo) l) p) return (λ (b : Bool). Id Bool (Leb (nth (Add m lo) l) p) b → Le (S p) (nth (Add m lo) l)) {
        True => λ (e : Id Bool (Leb (nth (Add m lo) l) p) True).
          botElim (Le (S p) (nth (Add m lo) l))
            (le_rw_r (S Z) (segCount (nth (Add m lo) l) lo w l) Z
              (hnoBelow (nth (Add m lo) l) (leb_true_le (nth (Add m lo) l) p e))
              (nth_seg_count_pos m w lo l hm hrange)),
        False => λ (e : Id Bool (Leb (nth (Add m lo) l) p) False). leb_false_gt (nth (Add m lo) l) p e
      } Refl }

def allLeR_to_noAbove_ty : Term := prog{
  Π (w : Nat) → Π (lo : Nat) → Π (p : Nat) → Π (l : List Nat) →
    AllLeR w lo p l → Π (x : Nat) → Le (S p) x → Id Nat (segCount x lo w l) Z }
def noAbove_to_allLeR_ty : Term := prog{
  Π (w : Nat) → Π (lo : Nat) → Π (p : Nat) → Π (l : List Nat) → Le (Add lo w) (Len l) →
    (Π (x : Nat) → Le (S p) x → Id Nat (segCount x lo w l) Z) → AllLeR w lo p l }
def allGtR_to_noBelow_ty : Term := prog{
  Π (w : Nat) → Π (lo : Nat) → Π (p : Nat) → Π (l : List Nat) →
    AllGtR w lo p l → Π (x : Nat) → Le x p → Id Nat (segCount x lo w l) Z }
def noBelow_to_allGtR_ty : Term := prog{
  Π (w : Nat) → Π (lo : Nat) → Π (p : Nat) → Π (l : List Nat) → Le (Add lo w) (Len l) →
    (Π (x : Nat) → Le x p → Id Nat (segCount x lo w l) Z) → AllGtR w lo p l }
-- #1/#3/#5 carry the range-fits bound `Le (add lo w) (len l)`: without it an off-the-end
-- position reads Z, which need not occur in the segment, so #1 (present ≥1×) and #5
-- (AllGtR needs nth>p at every m<w, but off-end nth=Z isn't) are FALSE (dllbc-seg's
-- gate finding, computationally checked). #2/#4 iterate the ACTUAL segment so need no
-- bound. The keystone already carries this bound and len is sort-invariant, so the
-- composition feeds #3/#5 the bound over the sorted list.
def nth_seg_count_pos_ty : Term := prog{
  Π (m : Nat) → Π (w : Nat) → Π (lo : Nat) → Π (l : List Nat) →
    Le (S m) w → Le (Add lo w) (Len l) → Le (S Z) (segCount (nth (Add m lo) l) lo w l) }
def allLeR_sortRange_ty : Term := prog{
  Π (fuel : Nat) → Π (lo : Nat) → Π (w : Nat) → Π (p : Nat) → Π (l : List Nat) →
    Le (Add lo w) (Len l) → AllLeR w lo p l → AllLeR w lo p (sortRangeL fuel lo w l) }
def allGtR_sortRange_ty : Term := prog{
  Π (fuel : Nat) → Π (lo : Nat) → Π (w : Nat) → Π (p : Nat) → Π (l : List Nat) →
    Le (Add lo w) (Len l) → AllGtR w lo p l → AllGtR w lo p (sortRangeL fuel lo w l) }

-- KEYSTONE composition (mine): route the positional bound through the perm-invariant
-- noAbove/noBelow (segCount preserved by segCount_sortRangeL), feeding the range bound
-- over the sorted list (len sort-invariant, le_rw_r over len_sortRangeL).
def allLeR_sortRange : Term := prog{
  λ (fuel : Nat). λ (lo : Nat). λ (w : Nat). λ (p : Nat). λ (l : List Nat).
    λ (bound : Le (Add lo w) (Len l)). λ (h : AllLeR w lo p l).
      noAbove_to_allLeR w lo p (sortRangeL fuel lo w l)
        (le_rw_r (Add lo w) (Len l) (Len (sortRangeL fuel lo w l))
          (id_sym Nat (Len (sortRangeL fuel lo w l)) (Len l) (len_sortRangeL fuel lo w l))
          bound)
        (λ (x : Nat). λ (hx : Le (S p) x).
          id_trans Nat (segCount x lo w (sortRangeL fuel lo w l)) (segCount x lo w l) Z
            (segCount_sortRangeL x fuel lo w l bound)
            (allLeR_to_noAbove w lo p l h x hx)) }
def allGtR_sortRange : Term := prog{
  λ (fuel : Nat). λ (lo : Nat). λ (w : Nat). λ (p : Nat). λ (l : List Nat).
    λ (bound : Le (Add lo w) (Len l)). λ (h : AllGtR w lo p l).
      noBelow_to_allGtR w lo p (sortRangeL fuel lo w l)
        (le_rw_r (Add lo w) (Len l) (Len (sortRangeL fuel lo w l))
          (id_sym Nat (Len (sortRangeL fuel lo w l)) (Len l) (len_sortRangeL fuel lo w l))
          bound)
        (λ (x : Nat). λ (hx : Le x p).
          id_trans Nat (segCount x lo w (sortRangeL fuel lo w l)) (segCount x lo w l) Z
            (segCount_sortRangeL x fuel lo w l bound)
            (allGtR_to_noBelow w lo p l h x hx)) }

/-! ## sorted_sortRangeL — the full sort is sorted (§22, M22-c step 5; proof dispatched)

    The model half of the North Star's sortedness. Fuel-structural induction mirroring
    count_sortRangeL. FUEL-SUFFICIENCY: sortedness (unlike count/len) is NOT preserved by
    the out-of-fuel identity, so it carries `Le cnt fuel` (the recursion depth ≤ cnt). The
    step (cnt ≥ 2) applies the GLUE to the two recursively-sorted sub-ranges, feeding it:
    the pivot placement (partition_pivot + locality — the sorts don't touch position
    lo+i), the two sub-range SortedRs (the two IHs + locality), and AllLeR-left/AllGtR-right
    SURVIVING both sorts (partition_allLeR/allGtR = invariant, then allLeR/allGtR_sortRange
    = keystone, then locality for the OTHER sort). The glue's width S(add i g) = cnt via
    partScanSizeL (i+g = cnt-1). Sub-range bounds/fuel from partScanSizeL + the len lemmas.
    Assembly over now-proven pieces (glue, keystone, invariant, locality all on main) —
    proof owned by dllbc-seg per skeleton+prove; statement mine. -/
def sorted_sortRangeL_ty : Term := prog{
  Π (fuel : Nat) → Π (lo : Nat) → Π (cnt : Nat) → Π (l : List Nat) →
    Le cnt fuel → Le (Add lo cnt) (Len l) →
    SortedR cnt lo (sortRangeL fuel lo cnt l) }

-- SortedR transport kit for sorted_sortRangeL (spine takeover): move a SortedR across
-- a fixed region (SortedR_cong, le_rw both endpoints), a width rewrite (sortedR_width_cong,
-- j on the width — for the glue's S(add i g) → cnt), or an offset rewrite (sortedR_off_cong,
-- j on the offset — for the add_comm S(add lo i) ↔ S(add i lo) bridge).
def SortedR_cong : Term := prog{
  λ (w : Nat). λ (lo : Nat). λ (l : List Nat). λ (l' : List Nat).
    λ (s : SortedR w lo l).
    λ (agree : Π (q : Nat) → Le (S q) w → Id Nat (nth (Add q lo) l') (nth (Add q lo) l)).
      λ (k : Nat). λ (hk : Le (S (S k)) w).
        le_rw_r (nth (Add k lo) l') (nth (Add (S k) lo) l) (nth (Add (S k) lo) l')
          (id_sym Nat (nth (Add (S k) lo) l') (nth (Add (S k) lo) l) (agree (S k) hk))
          (le_rw_l (nth (Add (S k) lo) l) (nth (Add k lo) l) (nth (Add k lo) l')
            (id_sym Nat (nth (Add k lo) l') (nth (Add k lo) l) (agree k (le_pred_l (S k) w hk)))
            (s k hk)) }
def SortedR_cong_ty : Term := prog{
  Π (w : Nat) → Π (lo : Nat) → Π (l : List Nat) → Π (l' : List Nat) →
    SortedR w lo l →
    (Π (q : Nat) → Le (S q) w → Id Nat (nth (Add q lo) l') (nth (Add q lo) l)) →
    SortedR w lo l' }
def sortedR_width_cong : Term := prog{
  λ (w : Nat). λ (w' : Nat). λ (lo : Nat). λ (l : List Nat).
    λ (e : Id Nat w w'). λ (s : SortedR w lo l).
      j Nat w (λ (w2 : Nat). λ (h : Id Nat w w2). SortedR w2 lo l) s w' e }
def sortedR_width_cong_ty : Term := prog{
  Π (w : Nat) → Π (w' : Nat) → Π (lo : Nat) → Π (l : List Nat) →
    Id Nat w w' → SortedR w lo l → SortedR w' lo l }
def sortedR_off_cong : Term := prog{
  λ (w : Nat). λ (lo : Nat). λ (lo' : Nat). λ (l : List Nat).
    λ (e : Id Nat lo lo'). λ (s : SortedR w lo l).
      j Nat lo (λ (lo2 : Nat). λ (h : Id Nat lo lo2). SortedR w lo2 l) s lo' e }
def sortedR_off_cong_ty : Term := prog{
  Π (w : Nat) → Π (lo : Nat) → Π (lo' : Nat) → Π (l : List Nat) →
    Id Nat lo lo' → SortedR w lo l → SortedR w lo' l }

/-! ## sorted_sortRangeL's 5 glue inputs (spine takeover) — each survives BOTH sub-sorts.
    Setup: L = sortRangeL f' lo i p (left sort), result = sortRangeL f' (S(add lo i)) g L
    (right sort). SL/AL: left region [lo,lo+i) is BELOW the right sort (nth_sortRangeL_lt);
    AG: gap is ABOVE the left sort (nth_sortRangeL_ge). Keystone (allLeR/allGtR_sortRange)
    carries bounds across the OWN sort; cong across the fixed region. add_comm bridges the
    positional-predicate offset (add i lo) ↔ model offset (add lo i). -/
def pos_lt_bound : Term := prog{
  λ (q : Nat). λ (i : Nat). λ (lo : Nat). λ (hq : Le (S q) i).
    le_rw_l (Add lo i) (Add lo q) (Add q lo) (add_comm lo q)
      (le_add_mono_l lo q i (le_pred_l q i hq)) }
def pos_lt_bound_ty : Term := prog{
  Π (q : Nat) → Π (i : Nat) → Π (lo : Nat) → Le (S q) i → Le (S (Add q lo)) (S (Add lo i)) }
def allGtR_off_cong : Term := prog{
  λ (w : Nat). λ (off : Nat). λ (off' : Nat). λ (p : Nat). λ (l : List Nat).
    λ (e : Id Nat off off'). λ (s : AllGtR w off p l).
      j Nat off (λ (o2 : Nat). λ (h : Id Nat off o2). AllGtR w o2 p l) s off' e }
def allGtR_off_cong_ty : Term := prog{
  Π (w : Nat) → Π (off : Nat) → Π (off' : Nat) → Π (p : Nat) → Π (l : List Nat) →
    Id Nat off off' → AllGtR w off p l → AllGtR w off' p l }
def gap_ge_bound : Term := prog{
  λ (m : Nat). λ (i : Nat). λ (lo : Nat).
    le_rw_l (Add m (S (Add i lo))) (Add i lo) (Add lo i) (add_comm i lo)
      (le_trans (Add i lo) (S (Add i lo)) (Add m (S (Add i lo)))
        (le_up_r (Add i lo) (Add i lo) (le_refl (Add i lo)))
        (le_add_l (S (Add i lo)) m)) }
def gap_ge_bound_ty : Term := prog{
  Π (m : Nat) → Π (i : Nat) → Π (lo : Nat) → Le (Add lo i) (Add m (S (Add i lo))) }
def sorted_in_SL : Term := prog{
  λ (i : Nat). λ (g : Nat). λ (lo : Nat). λ (p : List Nat). λ (f' : Nat).
    λ (ihL : SortedR i lo (sortRangeL f' lo i p)).
      SortedR_cong i lo (sortRangeL f' lo i p) (sortRangeL f' (S (Add lo i)) g (sortRangeL f' lo i p))
        ihL
        (λ (q : Nat). λ (hq : Le (S q) i).
          nth_sortRangeL_lt f' (Add q lo) (S (Add lo i)) g (sortRangeL f' lo i p) (pos_lt_bound q i lo hq)) }
def sorted_in_SL_ty : Term := prog{
  Π (i : Nat) → Π (g : Nat) → Π (lo : Nat) → Π (p : List Nat) → Π (f' : Nat) →
    SortedR i lo (sortRangeL f' lo i p) →
    SortedR i lo (sortRangeL f' (S (Add lo i)) g (sortRangeL f' lo i p)) }
def sorted_in_SR : Term := prog{
  λ (i : Nat). λ (g : Nat). λ (lo : Nat). λ (p : List Nat). λ (f' : Nat).
    λ (ihR : SortedR g (S (Add lo i)) (sortRangeL f' (S (Add lo i)) g (sortRangeL f' lo i p))).
      sortedR_off_cong g (S (Add lo i)) (S (Add i lo)) (sortRangeL f' (S (Add lo i)) g (sortRangeL f' lo i p))
        (id_congr Nat Nat (λ (n : Nat). S n) (Add lo i) (Add i lo) (add_comm lo i))
        ihR }
def sorted_in_SR_ty : Term := prog{
  Π (i : Nat) → Π (g : Nat) → Π (lo : Nat) → Π (p : List Nat) → Π (f' : Nat) →
    SortedR g (S (Add lo i)) (sortRangeL f' (S (Add lo i)) g (sortRangeL f' lo i p)) →
    SortedR g (S (Add i lo)) (sortRangeL f' (S (Add lo i)) g (sortRangeL f' lo i p)) }
def sorted_in_HPIV : Term := prog{
  λ (i : Nat). λ (g : Nat). λ (lo : Nat). λ (pivot : Nat). λ (p : List Nat). λ (f' : Nat).
    λ (ppiv : Id Nat (nth (Add i lo) p) pivot).
      id_sym Nat (nth (Add i lo) (sortRangeL f' (S (Add lo i)) g (sortRangeL f' lo i p))) pivot
        (id_trans Nat
          (nth (Add i lo) (sortRangeL f' (S (Add lo i)) g (sortRangeL f' lo i p)))
          (nth (Add i lo) (sortRangeL f' lo i p))
          pivot
          (nth_sortRangeL_lt f' (Add i lo) (S (Add lo i)) g (sortRangeL f' lo i p)
            (le_rw_r (Add i lo) (Add i lo) (Add lo i) (add_comm i lo) (le_refl (Add i lo))))
          (id_trans Nat (nth (Add i lo) (sortRangeL f' lo i p)) (nth (Add i lo) p) pivot
            (nth_sortRangeL_ge f' (Add i lo) lo i p
              (le_rw_l (Add i lo) (Add i lo) (Add lo i) (add_comm i lo) (le_refl (Add i lo))))
            ppiv)) }
def sorted_in_HPIV_ty : Term := prog{
  Π (i : Nat) → Π (g : Nat) → Π (lo : Nat) → Π (pivot : Nat) → Π (p : List Nat) → Π (f' : Nat) →
    Id Nat (nth (Add i lo) p) pivot →
    Id Nat pivot (nth (Add i lo) (sortRangeL f' (S (Add lo i)) g (sortRangeL f' lo i p))) }
def sorted_in_AL : Term := prog{
  λ (i : Nat). λ (g : Nat). λ (lo : Nat). λ (pivot : Nat). λ (p : List Nat). λ (f' : Nat).
    λ (pAL : AllLeR i lo pivot p). λ (bl : Le (Add lo i) (Len p)).
      allLeR_cong i lo pivot (sortRangeL f' lo i p) (sortRangeL f' (S (Add lo i)) g (sortRangeL f' lo i p))
        (λ (q : Nat). λ (hq : Le (S q) i).
          nth_sortRangeL_lt f' (Add q lo) (S (Add lo i)) g (sortRangeL f' lo i p) (pos_lt_bound q i lo hq))
        (allLeR_sortRange f' lo i pivot p bl pAL) }
def sorted_in_AL_ty : Term := prog{
  Π (i : Nat) → Π (g : Nat) → Π (lo : Nat) → Π (pivot : Nat) → Π (p : List Nat) → Π (f' : Nat) →
    AllLeR i lo pivot p → Le (Add lo i) (Len p) →
    AllLeR i lo pivot (sortRangeL f' (S (Add lo i)) g (sortRangeL f' lo i p)) }
def sorted_in_AG : Term := prog{
  λ (i : Nat). λ (g : Nat). λ (lo : Nat). λ (pivot : Nat). λ (p : List Nat). λ (f' : Nat).
    λ (pAG : AllGtR g (S (Add i lo)) pivot p).
    λ (br : Le (Add (S (Add lo i)) g) (Len (sortRangeL f' lo i p))).
      allGtR_off_cong g (S (Add lo i)) (S (Add i lo)) pivot (sortRangeL f' (S (Add lo i)) g (sortRangeL f' lo i p))
        (id_congr Nat Nat (λ (n : Nat). S n) (Add lo i) (Add i lo) (add_comm lo i))
        (allGtR_sortRange f' (S (Add lo i)) g pivot (sortRangeL f' lo i p) br
          (allGtR_off_cong g (S (Add i lo)) (S (Add lo i)) pivot (sortRangeL f' lo i p)
            (id_congr Nat Nat (λ (n : Nat). S n) (Add i lo) (Add lo i) (add_comm i lo))
            (allGtR_cong g (S (Add i lo)) pivot p (sortRangeL f' lo i p)
              (λ (m : Nat). λ (hm : Le (S m) g).
                nth_sortRangeL_ge f' (Add m (S (Add i lo))) lo i p (gap_ge_bound m i lo))
              pAG))) }
def sorted_in_AG_ty : Term := prog{
  Π (i : Nat) → Π (g : Nat) → Π (lo : Nat) → Π (pivot : Nat) → Π (p : List Nat) → Π (f' : Nat) →
    AllGtR g (S (Add i lo)) pivot p → Le (Add (S (Add lo i)) g) (Len (sortRangeL f' lo i p)) →
    AllGtR g (S (Add i lo)) pivot (sortRangeL f' (S (Add lo i)) g (sortRangeL f' lo i p)) }

-- i+g = cnt-1 for the top partition (partScanSizeL + add_zero); reused by the size
-- transport and both fuel-sufficiency derivations in sorted_sortRangeL.
def part_size : Term := prog{
  λ (lo : Nat). λ (cnt'' : Nat). λ (l : List Nat).
    id_trans Nat
      (Add (partIdxRangeL lo (S (S cnt'')) l) (partGapRangeL lo (S (S cnt'')) l))
      (S (Add cnt'' Z)) (S cnt'')
      (partScanSizeL (nth lo l) lo (S cnt'') Z Z l)
      (id_congr Nat Nat (λ (n : Nat). S n) (Add cnt'' Z) cnt'' (add_zero cnt'')) }
def part_size_ty : Term := prog{
  Π (lo : Nat) → Π (cnt'' : Nat) → Π (l : List Nat) →
    Id Nat (Add (partIdxRangeL lo (S (S cnt'')) l) (partGapRangeL lo (S (S cnt'')) l)) (S cnt'') }


def sorted_sortRangeL : Term := prog{
  λ (fuel : Nat).
    elim fuel return (λ (fz : Nat). Π (lo : Nat) → Π (cnt : Nat) → Π (l : List Nat) →
        Le cnt fz → Le (Add lo cnt) (Len l) → SortedR cnt lo (sortRangeL fz lo cnt l)) {
      Z => λ (lo : Nat). λ (cnt : Nat). λ (l : List Nat).
        elim cnt return (λ (cz : Nat). Le cz Z → Le (Add lo cz) (Len l) → SortedR cz lo l) {
          Z => λ (hf : Le Z Z). λ (hb : Le (Add lo Z) (Len l)). sortedR_zero lo l,
          S (c) cih => λ (hf : Le (S c) Z). λ (hb : Le (Add lo (S c)) (Len l)). botElim (SortedR (S c) lo l) hf },
      S (f') ih => λ (lo : Nat). λ (cnt : Nat). λ (l : List Nat).
        elim cnt return (λ (cz : Nat). Le cz (S f') → Le (Add lo cz) (Len l) → SortedR cz lo (sortRangeL (S f') lo cz l)) {
          Z => λ (hf : Le Z (S f')). λ (hb : Le (Add lo Z) (Len l)). sortedR_zero lo l,
          S (cnt') nih => elim cnt' return (λ (cz' : Nat). Le (S cz') (S f') → Le (Add lo (S cz')) (Len l) → SortedR (S cz') lo (sortRangeL (S f') lo (S cz') l)) {
            Z => λ (hf : Le (S Z) (S f')). λ (hb : Le (Add lo (S Z)) (Len l)). sortedR_one lo l,
            S (cnt'') n2ih => λ (hf : Le (S (S cnt'')) (S f')). λ (hb : Le (Add lo (S (S cnt''))) (Len l)).
              sortedR_width_cong
                (S (Add (partIdxRangeL lo (S (S cnt'')) l) (partGapRangeL lo (S (S cnt'')) l)))
                (S (S cnt'')) lo
                (sortRangeL f' (S (Add lo (partIdxRangeL lo (S (S cnt'')) l))) (partGapRangeL lo (S (S cnt'')) l)
                  (sortRangeL f' lo (partIdxRangeL lo (S (S cnt'')) l) (partitionRangeL lo (S (S cnt'')) l)))
                (id_congr Nat Nat (λ (n : Nat). S n)
                  (Add (partIdxRangeL lo (S (S cnt'')) l) (partGapRangeL lo (S (S cnt'')) l)) (S cnt'')
                  (part_size lo cnt'' l))
                (glue (partIdxRangeL lo (S (S cnt'')) l) (partGapRangeL lo (S (S cnt'')) l) lo (nth lo l)
                  (sortRangeL f' (S (Add lo (partIdxRangeL lo (S (S cnt'')) l))) (partGapRangeL lo (S (S cnt'')) l)
                    (sortRangeL f' lo (partIdxRangeL lo (S (S cnt'')) l) (partitionRangeL lo (S (S cnt'')) l)))
                  (sorted_in_HPIV (partIdxRangeL lo (S (S cnt'')) l) (partGapRangeL lo (S (S cnt'')) l) lo (nth lo l)
                    (partitionRangeL lo (S (S cnt'')) l) f' (partition_pivot lo (S (S cnt'')) l hb))
                  (sorted_in_SL (partIdxRangeL lo (S (S cnt'')) l) (partGapRangeL lo (S (S cnt'')) l) lo
                    (partitionRangeL lo (S (S cnt'')) l) f'
                    (ih lo (partIdxRangeL lo (S (S cnt'')) l) (partitionRangeL lo (S (S cnt'')) l)
                      (le_trans (partIdxRangeL lo (S (S cnt'')) l) (S cnt'') f'
                        (le_rw_r (partIdxRangeL lo (S (S cnt'')) l)
                          (Add (partIdxRangeL lo (S (S cnt'')) l) (partGapRangeL lo (S (S cnt'')) l)) (S cnt'')
                          (part_size lo cnt'' l)
                          (le_add (partIdxRangeL lo (S (S cnt'')) l) (partGapRangeL lo (S (S cnt'')) l)))
                        hf)
                      (sortRangeBL lo cnt'' l hb)))
                  (sorted_in_AL (partIdxRangeL lo (S (S cnt'')) l) (partGapRangeL lo (S (S cnt'')) l) lo (nth lo l)
                    (partitionRangeL lo (S (S cnt'')) l) f'
                    (partition_allLeR lo (S (S cnt'')) l hb) (sortRangeBL lo cnt'' l hb))
                  (sorted_in_AG (partIdxRangeL lo (S (S cnt'')) l) (partGapRangeL lo (S (S cnt'')) l) lo (nth lo l)
                    (partitionRangeL lo (S (S cnt'')) l) f'
                    (partition_allGtR lo (S (S cnt'')) l hb) (sortRangeBR f' lo cnt'' l hb))
                  (sorted_in_SR (partIdxRangeL lo (S (S cnt'')) l) (partGapRangeL lo (S (S cnt'')) l) lo
                    (partitionRangeL lo (S (S cnt'')) l) f'
                    (ih (S (Add lo (partIdxRangeL lo (S (S cnt'')) l))) (partGapRangeL lo (S (S cnt'')) l)
                      (sortRangeL f' lo (partIdxRangeL lo (S (S cnt'')) l) (partitionRangeL lo (S (S cnt'')) l))
                      (le_trans (partGapRangeL lo (S (S cnt'')) l) (S cnt'') f'
                        (le_rw_r (partGapRangeL lo (S (S cnt'')) l)
                          (Add (partIdxRangeL lo (S (S cnt'')) l) (partGapRangeL lo (S (S cnt'')) l)) (S cnt'')
                          (part_size lo cnt'' l)
                          (le_add_l (partGapRangeL lo (S (S cnt'')) l) (partIdxRangeL lo (S (S cnt'')) l)))
                        hf)
                      (sortRangeBR f' lo cnt'' l hb))))
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

    `insertL k x l`: `x` spliced in at index `k` (past the end it lands last). This
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

def insertL : Term := prog{
  λ (k : Nat).
    elim k return (λ (kz : Nat). Nat → List Nat → List Nat) {
      Z => λ (x : Nat). λ (l : List Nat). Cons x l,
      S (k2) ih => λ (x : Nat). λ (l : List Nat).
        elim l return (λ (lz : List Nat). List Nat) {
          Nil => Cons x Nil,
          Cons (h) (t) iht => Cons h (ih x t) } } }

/-- Generic J-transport at `List Nat`: `x = y ⟹ P x → P y`. `le_rw_r`/`le_rw_l` are
    this at `Le`-shaped `P` over `Nat`; a back-less body needs the unrestricted form,
    because every certificate it returns is stated over an exit snapshot it only
    knows PROPOSITIONALLY (the callee's evidence), never definitionally. -/
def list_rw : Term := prog{
  λ (P : List Nat → Type). λ (x : List Nat). λ (y : List Nat).
    λ (h : Id (List Nat) x y). λ (px : P x).
      j (List Nat) x (λ (y2 : List Nat). λ (hh : Id (List Nat) x y2). P y2) px y h }
def list_rw_ty : Term := prog{
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

def sorted_head : Term := prog{
  λ (h : Nat). λ (t : List Nat). λ (s : Σ (hb : Bound h t) → Sorted t).
    elim s return (λ (q : Σ (hb : Bound h t) → Sorted t). Bound h t) {
      Pair (x) (y) => x } }
def sorted_head_ty : Term := prog{
  Π (h : Nat) → Π (t : List Nat) → Sorted (Cons h t) → Bound h t }

def sorted_tail : Term := prog{
  λ (h : Nat). λ (t : List Nat). λ (s : Σ (hb : Bound h t) → Sorted t).
    elim s return (λ (q : Σ (hb : Bound h t) → Sorted t). Sorted t) {
      Pair (x) (y) => y } }
def sorted_tail_ty : Term := prog{
  Π (h : Nat) → Π (t : List Nat) → Sorted (Cons h t) → Sorted t }

def ub_head : Term := prog{
  λ (p : Nat). λ (h : Nat). λ (t : List Nat). λ (u : Σ (hu : Le h p) → Ub p t).
    elim u return (λ (q : Σ (hu : Le h p) → Ub p t). Le h p) {
      Pair (x) (y) => x } }
def ub_head_ty : Term := prog{
  Π (p : Nat) → Π (h : Nat) → Π (t : List Nat) → Ub p (Cons h t) → Le h p }

def ub_tail : Term := prog{
  λ (p : Nat). λ (h : Nat). λ (t : List Nat). λ (u : Σ (hu : Le h p) → Ub p t).
    elim u return (λ (q : Σ (hu : Le h p) → Ub p t). Ub p t) {
      Pair (x) (y) => y } }
def ub_tail_ty : Term := prog{
  Π (p : Nat) → Π (h : Nat) → Π (t : List Nat) → Ub p (Cons h t) → Ub p t }

/-- `Lb p l ⟹ Bound p l`: a lower bound on EVERY element is in particular a bound on
    the HEAD, which is all `Sorted (Cons p b)` asks of the pivot. The two predicates
    agree definitionally at `Nil` (both `⊤`) and differ at `Cons` only by how much
    they say, so this is a `listRec` whose `Cons` arm is a first projection. -/
def lb_bound : Term := prog{
  λ (p : Nat). λ (l : List Nat).
    elim l return (λ (lz : List Nat). Lb p lz → Bound p lz) {
      Nil => λ (hn : Unit). hn,
      Cons (h) (t) ih => λ (hl : Σ (hh : Le p h) → Lb p t).
        elim hl return (λ (q : Σ (hh : Le p h) → Lb p t). Le p h) {
          Pair (x) (y) => x } } }
def lb_bound_ty : Term := prog{
  Π (p : Nat) → Π (l : List Nat) → Lb p l → Bound p l }

/-- Head-bound transport across the splice: if `h` bounds the head of `t`, and `h ≤
    p`, then `h` bounds the head of `t ++ p :: b`. The `listRec` on `t` IS the case
    analysis the caller would otherwise have to do inline: at `Nil` the new head is
    the PIVOT (so the bound is `Le h p`, the second hypothesis), at `Cons` the head is
    unchanged by the append (so the bound is the first hypothesis, verbatim). No IH is
    consumed — `Bound` looks exactly one cell deep, so this recursion is a case
    analysis and nothing more. -/
def bound_append : Term := prog{
  λ (h : Nat). λ (p : Nat). λ (t : List Nat). λ (b : List Nat).
    elim t return (λ (tz : List Nat).
        Bound h tz → Le h p → Bound h (append tz (Cons p b))) {
      Nil => λ (hb : Unit). λ (hp : Le h p). hp,
      Cons (h2) (t2) ih => λ (hb : Le h h2). λ (hp : Le h p). hb } }
def bound_append_ty : Term := prog{
  Π (h : Nat) → Π (p : Nat) → Π (t : List Nat) → Π (b : List Nat) →
    Bound h t → Le h p → Bound h (append t (Cons p b)) }

/-- The pivot glue. `Sorted a → Ub p a → Sorted b → Lb p b → Sorted (a ++ p :: b)`.

    Induction on `a`, with `b`/`p` and the two right-hand hypotheses fixed outside
    the elim (they do not vary), and `Sorted a`/`Ub p a` INSIDE the motive because
    they do — the `le_trans` idiom of applying the elim to its own hypotheses at the
    end (`} sa ua`), which is what lets the stated argument order survive an
    induction that needs two of them abstracted.

    The motive is OPEN: it mentions `p` and `b`, which are λ-bound outside the elim
    rather than being parameters of the recursion. That is exactly the shape b86742d4
    settled — `hasType` σ-instantiates λ binders as it descends, so the motive is
    pvar-free by the time the recursor is typed. This lemma is a working positive
    control for it.

    At `Nil` the goal is `Sorted (Cons p b)` = `Bound p b × Sorted b`, built from
    `lb_bound` and the fixed `sb`. At `Cons h t` the goal is `Bound h (t ++ p :: b) ×
    Sorted (t ++ p :: b)`: the head bound is `bound_append` fed a's own head bound and
    `h ≤ p` from `Ub`, and the tail is the IH at the two tails. Both components are
    definitional — `append (Cons h t) (Cons p b)` whnf's to `Cons h (append t (Cons p
    b))`, so `Sorted` unfolds straight onto the pair — which is why no `list_rw`
    transport appears anywhere in this proof. -/
def sorted_append_pivot : Term := prog{
  λ (p : Nat). λ (a : List Nat). λ (b : List Nat).
    λ (sa : Sorted a). λ (ua : Ub p a). λ (sb : Sorted b). λ (lb : Lb p b).
      elim a return (λ (az : List Nat).
          Sorted az → Ub p az → Sorted (append az (Cons p b))) {
        Nil => λ (sn : Unit). λ (un : Unit). Pair(lb_bound p b lb, sb),
        Cons (h) (t) ih => λ (sc : Sorted (Cons h t)). λ (uc : Ub p (Cons h t)).
          Pair(bound_append h p t b (sorted_head h t sc) (ub_head p h t uc),
               ih (sorted_tail h t sc) (ub_tail p h t uc))
      } sa ua }
def sorted_append_pivot_ty : Term := prog{
  Π (p : Nat) → Π (a : List Nat) → Π (b : List Nat) →
    Sorted a → Ub p a → Sorted b → Lb p b → Sorted (append a (Cons p b)) }

/-! ## M23 stage (iv) — the two-part vocabulary a relational partition needs

    A partition returns TWO lists whose counts together reconstruct the input's, and
    it decides each element by a `leb` split. Two facts close the gap between what the
    split hands back and what the postcondition asks for; both are observation-level
    (`count`, `add`) and neither mentions partition. The third thing the body wants —
    `Le (S p) x ⟹ Le p x`, to bend `leb_false_gt` into what `Lb p (Cons x _)` asks —
    is already `le_pred_l` above, from the M22 stack.

    The two-part count step, in its two directions. A partition's invariant is
    `count n lo + count n hi = count n l`, and each recursion step puts the head on
    ONE of the two sides — so the same equation extends by a `Cons` on the left part
    or on the right part, with the whole list gaining that `Cons` either way. Both are
    a `boolRec` on the `eqb n x` that `count n (Cons x ·)` unfolds to (the motive
    abstracts the scrutinee out of all three occurrences at once); the arms differ only
    in where the successor has to travel through `add`. -/

/-- Head onto the LEFT part. `add (S u) w` is definitionally `S (add u w)` (`add`
    recurses on its first argument), so the `True` arm is one `id_congr`. -/
def count_cons_l : Term := prog{
  λ (n : Nat). λ (x : Nat). λ (a : List Nat). λ (b : List Nat). λ (c : List Nat).
    λ (h : Id Nat (Add (Count n a) (Count n b)) (Count n c)).
      elim (Eqb n x) return (λ (bv : Bool).
        Id Nat (Add (boolRec (λ (w : Bool). Nat) (S (Count n a)) (Count n a) bv) (Count n b))
               (boolRec (λ (w : Bool). Nat) (S (Count n c)) (Count n c) bv)) {
        True => id_congr Nat Nat (λ (r : Nat). S r)
                  (Add (Count n a) (Count n b)) (Count n c) h,
        False => h } }
def count_cons_l_ty : Term := prog{
  Π (n : Nat) → Π (x : Nat) → Π (a : List Nat) → Π (b : List Nat) → Π (c : List Nat) →
    Id Nat (Add (Count n a) (Count n b)) (Count n c) →
    Id Nat (Add (Count n (Cons x a)) (Count n b)) (Count n (Cons x c)) }

/-- Head onto the RIGHT part. Here the successor lands under `add`'s SECOND argument,
    which is where the asymmetry of a first-argument-recursive `add` shows up: the
    `True` arm needs `add_succ` before the `id_congr`. -/
def count_cons_r : Term := prog{
  λ (n : Nat). λ (x : Nat). λ (a : List Nat). λ (b : List Nat). λ (c : List Nat).
    λ (h : Id Nat (Add (Count n a) (Count n b)) (Count n c)).
      elim (Eqb n x) return (λ (bv : Bool).
        Id Nat (Add (Count n a) (boolRec (λ (w : Bool). Nat) (S (Count n b)) (Count n b) bv))
               (boolRec (λ (w : Bool). Nat) (S (Count n c)) (Count n c) bv)) {
        True => id_trans Nat (Add (Count n a) (S (Count n b)))
                  (S (Add (Count n a) (Count n b))) (S (Count n c))
                  (add_succ (Count n a) (Count n b))
                  (id_congr Nat Nat (λ (r : Nat). S r)
                    (Add (Count n a) (Count n b)) (Count n c) h),
        False => h } }
def count_cons_r_ty : Term := prog{
  Π (n : Nat) → Π (x : Nat) → Π (a : List Nat) → Π (b : List Nat) → Π (c : List Nat) →
    Id Nat (Add (Count n a) (Count n b)) (Count n c) →
    Id Nat (Add (Count n a) (Count n (Cons x b))) (Count n (Cons x c)) }

/-! ## M23 stage (vi) — BOUND SURVIVAL, the whole-list keystone

    A partition-based quicksort's sortedness proof needs `Ub p a` where `a` is the
    left part AFTER it has been sorted, while the partition only ever bounded it
    BEFORE. So a bound must survive a permutation, and `Ub`/`Lb` — being Σ-chains over
    the list's spine — are not natively permutation-invariant.

    M22 hit this at the positional encoding and named the route: go through the
    multiset. `noAbove p l := Π x. Le (S p) x → count x l = Z` ("nothing above p is
    present") is *manifestly* permutation-invariant, because it is a statement about
    counts and nothing else — so `ub_perm` is two conversions with a one-line
    `id_trans` between them, and all the work sits in the conversions, where it is
    ordinary induction. The `Lb` side mirrors it through `noBelow`.

    The two predicates are written inline as Π-types rather than named: they exist
    only to be crossed. -/

/-- The two `Lb` projections, mirroring `ub_head`/`ub_tail`. -/
def lb_head : Term := prog{
  λ (p : Nat). λ (h : Nat). λ (t : List Nat). λ (u : Σ (hu : Le p h) → Lb p t).
    elim u return (λ (q : Σ (hu : Le p h) → Lb p t). Le p h) {
      Pair (x) (y) => x } }
def lb_head_ty : Term := prog{
  Π (p : Nat) → Π (h : Nat) → Π (t : List Nat) → Lb p (Cons h t) → Le p h }

def lb_tail : Term := prog{
  λ (p : Nat). λ (h : Nat). λ (t : List Nat). λ (u : Σ (hu : Le p h) → Lb p t).
    elim u return (λ (q : Σ (hu : Le p h) → Lb p t). Lb p t) {
      Pair (x) (y) => y } }
def lb_tail_ty : Term := prog{
  Π (p : Nat) → Π (h : Nat) → Π (t : List Nat) → Lb p (Cons h t) → Lb p t }

/-- `Ub p l ⟹ nothing above p occurs in l`. At `Cons h t` the head misses every
    `x > p`, because `h ≤ p < x` makes `eqb x h` False (`eqb_gt_false`), so the count
    steps past the head onto the IH. -/
def noAbove_of_ub : Term := prog{
  λ (p : Nat). λ (l : List Nat).
    elim l return (λ (lz : List Nat).
        Ub p lz → Π (x : Nat) → Le (S p) x → Id Nat (Count x lz) Z) {
      Nil => λ (u : Unit). λ (x : Nat). λ (hx : Le (S p) x). Refl,
      Cons (h) (t) ih => λ (u : Σ (hh : Le h p) → Ub p t). λ (x : Nat). λ (hx : Le (S p) x).
        id_trans Nat (Count x (Cons h t)) (Count x t) Z
          (count_cons_miss x h t
            (eqb_gt_false h x (le_trans (S h) (S p) x (ub_head p h t u) hx)))
          (ih (ub_tail p h t u) x hx) } }
def noAbove_of_ub_ty : Term := prog{
  Π (p : Nat) → Π (l : List Nat) → Ub p l →
    Π (x : Nat) → Le (S p) x → Id Nat (Count x l) Z }

/-- …and back. The head bound comes from a `leb h p` split: if it were False then
    `h > p`, so `count h l = Z` by hypothesis — but `count h (Cons h t)` is `S (count
    h t)` (`eqb_refl`), and `Z = S _` is `znots`. The tail hypothesis is the same
    argument run the other way: `count x (Cons h t) = Z` forces `count x t = Z`,
    trivially when `eqb x h` misses and by the same contradiction when it hits. -/
def ub_of_noAbove : Term := prog{
  λ (p : Nat). λ (l : List Nat).
    elim l return (λ (lz : List Nat).
        (Π (x : Nat) → Le (S p) x → Id Nat (Count x lz) Z) → Ub p lz) {
      Nil => λ (hn : Π (x : Nat) → Le (S p) x → Id Nat (Count x Nil) Z). unit,
      Cons (h) (t) ih => λ (hn : Π (x : Nat) → Le (S p) x → Id Nat (Count x (Cons h t)) Z).
        Pair(
          elim (Leb h p) return (λ (bv : Bool). Id Bool (Leb h p) bv → Le h p) {
            True => λ (e : Id Bool (Leb h p) True). leb_true_le h p e,
            False => λ (e : Id Bool (Leb h p) False).
              botElim (Le h p)
                (znots (Count h t)
                  (id_trans Nat Z (Count h (Cons h t)) (S (Count h t))
                    (id_sym Nat (Count h (Cons h t)) Z (hn h (leb_false_gt h p e)))
                    (count_cons_hit h h t (eqb_refl h))))
          } Refl,
          ih (λ (x : Nat). λ (hx : Le (S p) x).
                elim (Eqb x h) return (λ (bv : Bool). Id Bool (Eqb x h) bv → Id Nat (Count x t) Z) {
                  True => λ (eq : Id Bool (Eqb x h) True).
                    botElim (Id Nat (Count x t) Z)
                      (znots (Count x t)
                        (id_trans Nat Z (Count x (Cons h t)) (S (Count x t))
                          (id_sym Nat (Count x (Cons h t)) Z (hn x hx))
                          (count_cons_hit x h t eq))),
                  False => λ (eq : Id Bool (Eqb x h) False).
                    id_trans Nat (Count x t) (Count x (Cons h t)) Z
                      (id_sym Nat (Count x (Cons h t)) (Count x t) (count_cons_miss x h t eq))
                      (hn x hx)
                } Refl)) } }
def ub_of_noAbove_ty : Term := prog{
  Π (p : Nat) → Π (l : List Nat) →
    (Π (x : Nat) → Le (S p) x → Id Nat (Count x l) Z) → Ub p l }

/-- THE KEYSTONE. An upper bound survives any count-preserving rearrangement — which
    is exactly what a recursive sort hands back about the part it sorted. -/
def ub_perm : Term := prog{
  λ (p : Nat). λ (a : List Nat). λ (b : List Nat).
    λ (hc : Π (n : Nat) → Id Nat (Count n a) (Count n b)). λ (hb : Ub p b).
      ub_of_noAbove p a (λ (x : Nat). λ (hx : Le (S p) x).
        id_trans Nat (Count x a) (Count x b) Z (hc x) (noAbove_of_ub p b hb x hx)) }
def ub_perm_ty : Term := prog{
  Π (p : Nat) → Π (a : List Nat) → Π (b : List Nat) →
    (Π (n : Nat) → Id Nat (Count n a) (Count n b)) → Ub p b → Ub p a }

/-- The `Lb` mirror: `Lb p l ⟹ nothing strictly below p occurs`. Here the head misses
    every `x < p ≤ h` by `eqb_lt_false`. -/
def noBelow_of_lb : Term := prog{
  λ (p : Nat). λ (l : List Nat).
    elim l return (λ (lz : List Nat).
        Lb p lz → Π (x : Nat) → Le (S x) p → Id Nat (Count x lz) Z) {
      Nil => λ (u : Unit). λ (x : Nat). λ (hx : Le (S x) p). Refl,
      Cons (h) (t) ih => λ (u : Σ (hh : Le p h) → Lb p t). λ (x : Nat). λ (hx : Le (S x) p).
        id_trans Nat (Count x (Cons h t)) (Count x t) Z
          (count_cons_miss x h t
            (eqb_lt_false x h (le_trans (S x) p h hx (lb_head p h t u))))
          (ih (lb_tail p h t u) x hx) } }
def noBelow_of_lb_ty : Term := prog{
  Π (p : Nat) → Π (l : List Nat) → Lb p l →
    Π (x : Nat) → Le (S x) p → Id Nat (Count x l) Z }

def lb_of_noBelow : Term := prog{
  λ (p : Nat). λ (l : List Nat).
    elim l return (λ (lz : List Nat).
        (Π (x : Nat) → Le (S x) p → Id Nat (Count x lz) Z) → Lb p lz) {
      Nil => λ (hn : Π (x : Nat) → Le (S x) p → Id Nat (Count x Nil) Z). unit,
      Cons (h) (t) ih => λ (hn : Π (x : Nat) → Le (S x) p → Id Nat (Count x (Cons h t)) Z).
        Pair(
          elim (Leb p h) return (λ (bv : Bool). Id Bool (Leb p h) bv → Le p h) {
            True => λ (e : Id Bool (Leb p h) True). leb_true_le p h e,
            False => λ (e : Id Bool (Leb p h) False).
              botElim (Le p h)
                (znots (Count h t)
                  (id_trans Nat Z (Count h (Cons h t)) (S (Count h t))
                    (id_sym Nat (Count h (Cons h t)) Z (hn h (leb_false_gt p h e)))
                    (count_cons_hit h h t (eqb_refl h))))
          } Refl,
          ih (λ (x : Nat). λ (hx : Le (S x) p).
                elim (Eqb x h) return (λ (bv : Bool). Id Bool (Eqb x h) bv → Id Nat (Count x t) Z) {
                  True => λ (eq : Id Bool (Eqb x h) True).
                    botElim (Id Nat (Count x t) Z)
                      (znots (Count x t)
                        (id_trans Nat Z (Count x (Cons h t)) (S (Count x t))
                          (id_sym Nat (Count x (Cons h t)) Z (hn x hx))
                          (count_cons_hit x h t eq))),
                  False => λ (eq : Id Bool (Eqb x h) False).
                    id_trans Nat (Count x t) (Count x (Cons h t)) Z
                      (id_sym Nat (Count x (Cons h t)) (Count x t) (count_cons_miss x h t eq))
                      (hn x hx)
                } Refl)) } }
def lb_of_noBelow_ty : Term := prog{
  Π (p : Nat) → Π (l : List Nat) →
    (Π (x : Nat) → Le (S x) p → Id Nat (Count x l) Z) → Lb p l }

def lb_perm : Term := prog{
  λ (p : Nat). λ (a : List Nat). λ (b : List Nat).
    λ (hc : Π (n : Nat) → Id Nat (Count n a) (Count n b)). λ (hb : Lb p b).
      lb_of_noBelow p a (λ (x : Nat). λ (hx : Le (S x) p).
        id_trans Nat (Count x a) (Count x b) Z (hc x) (noBelow_of_lb p b hb x hx)) }
def lb_perm_ty : Term := prog{
  Π (p : Nat) → Π (a : List Nat) → Π (b : List Nat) →
    (Π (n : Nat) → Id Nat (Count n a) (Count n b)) → Lb p b → Lb p a }

/-! ## M24 — the ARRAY layer (¶6's migration ledger, item 3)

    ¶1.3's promise: "Every lemma in the quicksort library — `count`, `Sorted`, `Bound`,
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
def anil : Term := prog{ Arr() }

/-- `countA x a` — the multiset counter, `count`'s transfer. -/
def countA : Term := prog{
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

/-- `asingle x` — the one-element array, `[x]`. ¶6's glue is stated over
    `arrCat (asingle p) r`, which is the array spelling of `Cons p b`. -/
def asingle : Term := prog{ λ (x : Nat). acons Z x Arr() }

/-! ### The glue, and the standing claim it tests

    ¶6: "Set `append ↦ arrCat` and `Cons p b ↦ arrCat (asingle p) r` and it IS the array
    lemma, hypothesis for hypothesis — not merely the same shape but the same statement
    modulo the container … So the migration INHERITS that proof rather than opening a
    stratum."

    Below is `sorted_append_pivot` and its four helpers with exactly that substitution
    applied and nothing else. The claim is checkable and it checks. Note in particular
    that `arrCat 1 q (asingle p) b` COMPUTES to `acons q p b` — the array `Cons p b` —
    so the doc's chosen spelling of the pivot splice needs no lemma to relate it to the
    cons view. -/

def sorted_headA : Term := prog{
  λ (k : Nat). λ (h : Nat). λ (t : Array k Nat).
    λ (s : Σ (hb : BoundA h k t) → SortedA k t).
      elim s return (λ (q : Σ (hb : BoundA h k t) → SortedA k t). BoundA h k t) {
        Pair (x) (y) => x } }
def sorted_headA_ty : Term := prog{
  Π (k : Nat) → Π (h : Nat) → Π (t : Array k Nat) →
    SortedA (S k) (acons k h t) → BoundA h k t }

def sorted_tailA : Term := prog{
  λ (k : Nat). λ (h : Nat). λ (t : Array k Nat).
    λ (s : Σ (hb : BoundA h k t) → SortedA k t).
      elim s return (λ (q : Σ (hb : BoundA h k t) → SortedA k t). SortedA k t) {
        Pair (x) (y) => y } }
def sorted_tailA_ty : Term := prog{
  Π (k : Nat) → Π (h : Nat) → Π (t : Array k Nat) →
    SortedA (S k) (acons k h t) → SortedA k t }

def ub_headA : Term := prog{
  λ (p : Nat). λ (k : Nat). λ (h : Nat). λ (t : Array k Nat).
    λ (u : Σ (hu : Le h p) → UbA p k t).
      elim u return (λ (q : Σ (hu : Le h p) → UbA p k t). Le h p) {
        Pair (x) (y) => x } }
def ub_headA_ty : Term := prog{
  Π (p : Nat) → Π (k : Nat) → Π (h : Nat) → Π (t : Array k Nat) →
    UbA p (S k) (acons k h t) → Le h p }

def ub_tailA : Term := prog{
  λ (p : Nat). λ (k : Nat). λ (h : Nat). λ (t : Array k Nat).
    λ (u : Σ (hu : Le h p) → UbA p k t).
      elim u return (λ (q : Σ (hu : Le h p) → UbA p k t). UbA p k t) {
        Pair (x) (y) => y } }
def ub_tailA_ty : Term := prog{
  Π (p : Nat) → Π (k : Nat) → Π (h : Nat) → Π (t : Array k Nat) →
    UbA p (S k) (acons k h t) → UbA p k t }

/-- `LbA p a ⟹ BoundA p a`, `lb_bound`'s transfer: a lower bound on every element is in
    particular a bound on the head, which is all `SortedA (acons p b)` asks of the pivot. -/
def lb_boundA : Term := prog{
  λ (p : Nat). λ (n : Nat). λ (a : Array n Nat).
    arrRec Nat (λ (m : Nat). λ (b : Array m Nat). LbA p m b → BoundA p m b)
      (λ (hn : Unit). hn)
      (λ (k : Nat). λ (h : Nat). λ (t : Array k Nat).
        λ (ih : LbA p k t → BoundA p k t).
          λ (hl : Σ (hh : Le p h) → LbA p k t).
            elim hl return (λ (q : Σ (hh : Le p h) → LbA p k t). Le p h) {
              Pair (x) (y) => x })
      n a }
def lb_boundA_ty : Term := prog{
  Π (p : Nat) → Π (n : Nat) → Π (a : Array n Nat) → LbA p n a → BoundA p n a }

/-- `bound_append`'s transfer: the head bound survives the splice. The recursion IS the
    case analysis — at the empty array the new head is the PIVOT, otherwise the head is
    unchanged by the concatenation. No IH is consumed, because `BoundA` looks exactly one
    cell deep. -/
def bound_arrCat : Term := prog{
  λ (h : Nat). λ (p : Nat). λ (k : Nat). λ (t : Array k Nat).
    λ (q : Nat). λ (b : Array q Nat).
      arrRec Nat (λ (m : Nat). λ (tz : Array m Nat).
          BoundA h m tz → Le h p →
            BoundA h (Add m (S q)) (arrCat m (S q) tz (arrCat 1 q (asingle p) b)))
        (λ (hb : Unit). λ (hp : Le h p). hp)
        (λ (k2 : Nat). λ (h2 : Nat). λ (t2 : Array k2 Nat).
          λ (ih : BoundA h k2 t2 → Le h p →
              BoundA h (Add k2 (S q)) (arrCat k2 (S q) t2 (arrCat 1 q (asingle p) b))).
            λ (hb : Le h h2). λ (hp : Le h p). hb)
        k t }
def bound_arrCat_ty : Term := prog{
  Π (h : Nat) → Π (p : Nat) → Π (k : Nat) → Π (t : Array k Nat) →
    Π (q : Nat) → Π (b : Array q Nat) →
      BoundA h k t → Le h p →
        BoundA h (Add k (S q)) (arrCat k (S q) t (arrCat 1 q (asingle p) b)) }

/-- **The quicksort glue** — `sorted_append_pivot` with the container swapped, and
    nothing else changed. This is ¶6's "textbook quicksort correctness statement, in the
    textbook shape", and the standing check on the whole migration: if this were not the
    near-verbatim restatement, something would be off. -/
def sorted_arrCat : Term := prog{
  λ (p : Nat). λ (m : Nat). λ (a : Array m Nat). λ (q : Nat). λ (b : Array q Nat).
    λ (sa : SortedA m a). λ (ua : UbA p m a). λ (sb : SortedA q b). λ (lb : LbA p q b).
      arrRec Nat (λ (mz : Nat). λ (az : Array mz Nat).
          SortedA mz az → UbA p mz az →
            SortedA (Add mz (S q)) (arrCat mz (S q) az (arrCat 1 q (asingle p) b)))
        (λ (sn : Unit). λ (un : Unit). Pair(lb_boundA p q b lb, sb))
        (λ (k : Nat). λ (h : Nat). λ (t : Array k Nat).
          λ (ih : SortedA k t → UbA p k t →
              SortedA (Add k (S q)) (arrCat k (S q) t (arrCat 1 q (asingle p) b))).
            λ (sc : Σ (hb : BoundA h k t) → SortedA k t).
              λ (uc : Σ (hu : Le h p) → UbA p k t).
                Pair(bound_arrCat h p k t q b (sorted_headA k h t sc) (ub_headA p k h t uc),
                     ih (sorted_tailA k h t sc) (ub_tailA p k h t uc)))
        m a sa ua }
def sorted_arrCat_ty : Term := prog{
  Π (p : Nat) → Π (m : Nat) → Π (a : Array m Nat) → Π (q : Nat) → Π (b : Array q Nat) →
    SortedA m a → UbA p m a → SortedA q b → LbA p q b →
      SortedA (Add m (S q)) (arrCat m (S q) a (arrCat 1 q (asingle p) b)) }

/-- `count_append`'s transfer, and ¶6's named survivor: "the one lemma that replaces
    `count_append`/`take`/`drop` is `count_arrCat : count x (arrCat a b) = add (count x a)
    (count x b)`, which is the same induction." It is the same induction — the `Cons`
    arm's dependent Bool-elim on `eqb x h` transfers unchanged, because `countA` unfolds
    on an `acons` exactly as `count` unfolds on a `Cons`. -/
def count_arrCat : Term := prog{
  λ (x : Nat). λ (m : Nat). λ (a : Array m Nat). λ (q : Nat). λ (b : Array q Nat).
    arrRec Nat (λ (mz : Nat). λ (az : Array mz Nat).
        Id Nat (countA x (Add mz q) (arrCat mz q az b))
               (Add (countA x mz az) (countA x q b)))
      Refl
      (λ (k : Nat). λ (h : Nat). λ (t : Array k Nat).
        λ (ih : Id Nat (countA x (Add k q) (arrCat k q t b))
                       (Add (countA x k t) (countA x q b))).
          elim (Eqb x h) return (λ (bv : Bool).
            Id Nat (boolRec (λ (w : Bool). Nat)
                     (S (countA x (Add k q) (arrCat k q t b)))
                     (countA x (Add k q) (arrCat k q t b)) bv)
                   (Add (boolRec (λ (w : Bool). Nat)
                     (S (countA x k t)) (countA x k t) bv) (countA x q b))) {
            True => id_congr Nat Nat (λ (n : Nat). S n)
                      (countA x (Add k q) (arrCat k q t b))
                      (Add (countA x k t) (countA x q b)) ih,
            False => ih })
      m a }
def count_arrCat_ty : Term := prog{
  Π (x : Nat) → Π (m : Nat) → Π (a : Array m Nat) → Π (q : Nat) → Π (b : Array q Nat) →
    Id Nat (countA x (Add m q) (arrCat m q a b)) (Add (countA x m a) (countA x q b)) }

/-! ### The permutation layer, transferred

    M23's keystone: "`Ub` and `Lb` (Σ-chains over the spine) are not natively
    permutation-invariant. Cross to the multiset, where the property is
    `Π x. x > p → count x l = Z` and permutation-invariance is a one-line `id_trans`."
    That crossing transfers with the container like everything else. -/

def count_acons_hit : Term := prog{
  λ (m : Nat). λ (a : Nat). λ (k : Nat). λ (l : Array k Nat). λ (hq : Id Bool (Eqb m a) True).
    j Bool True
      (λ (z : Bool). λ (h : Id Bool True z).
        Id Nat (boolRec (λ (w : Bool). Nat) (S (countA m k l)) (countA m k l) z)
               (S (countA m k l)))
      Refl (Eqb m a) (id_sym Bool (Eqb m a) True hq) }
def count_acons_hit_ty : Term := prog{
  Π (m : Nat) → Π (a : Nat) → Π (k : Nat) → Π (l : Array k Nat) → Id Bool (Eqb m a) True →
    Id Nat (countA m (S k) (acons k a l)) (S (countA m k l)) }

def count_acons_miss : Term := prog{
  λ (m : Nat). λ (h : Nat). λ (k : Nat). λ (t : Array k Nat). λ (hq : Id Bool (Eqb m h) False).
    j Bool False
      (λ (z : Bool). λ (hh : Id Bool False z).
        Id Nat (boolRec (λ (w : Bool). Nat) (S (countA m k t)) (countA m k t) z)
               (countA m k t))
      Refl (Eqb m h) (id_sym Bool (Eqb m h) False hq) }
def count_acons_miss_ty : Term := prog{
  Π (m : Nat) → Π (h : Nat) → Π (k : Nat) → Π (t : Array k Nat) → Id Bool (Eqb m h) False →
    Id Nat (countA m (S k) (acons k h t)) (countA m k t) }

def lb_headA : Term := prog{
  λ (p : Nat). λ (k : Nat). λ (h : Nat). λ (t : Array k Nat).
    λ (u : Σ (hh : Le p h) → LbA p k t).
      elim u return (λ (q : Σ (hh : Le p h) → LbA p k t). Le p h) { Pair (x) (y) => x } }
def lb_tailA : Term := prog{
  λ (p : Nat). λ (k : Nat). λ (h : Nat). λ (t : Array k Nat).
    λ (u : Σ (hh : Le p h) → LbA p k t).
      elim u return (λ (q : Σ (hh : Le p h) → LbA p k t). LbA p k t) { Pair (x) (y) => y } }

def noAbove_of_ubA : Term := prog{
  λ (p : Nat). λ (n : Nat). λ (a : Array n Nat).
    arrRec Nat (λ (m : Nat). λ (az : Array m Nat).
        UbA p m az → Π (x : Nat) → Le (S p) x → Id Nat (countA x m az) Z)
      (λ (u : Unit). λ (x : Nat). λ (hx : Le (S p) x). Refl)
      (λ (k : Nat). λ (h : Nat). λ (t : Array k Nat).
        λ (ih : UbA p k t → Π (x : Nat) → Le (S p) x → Id Nat (countA x k t) Z).
          λ (u : Σ (hh : Le h p) → UbA p k t). λ (x : Nat). λ (hx : Le (S p) x).
            id_trans Nat (countA x (S k) (acons k h t)) (countA x k t) Z
              (count_acons_miss x h k t
                (eqb_gt_false h x (le_trans (S h) (S p) x (ub_headA p k h t u) hx)))
              (ih (ub_tailA p k h t u) x hx))
      n a }
def noAbove_of_ubA_ty : Term := prog{
  Π (p : Nat) → Π (n : Nat) → Π (a : Array n Nat) → UbA p n a →
    Π (x : Nat) → Le (S p) x → Id Nat (countA x n a) Z }

def ub_of_noAboveA : Term := prog{
  λ (p : Nat). λ (n : Nat). λ (a : Array n Nat).
    arrRec Nat (λ (m : Nat). λ (az : Array m Nat).
        (Π (x : Nat) → Le (S p) x → Id Nat (countA x m az) Z) → UbA p m az)
      (λ (hn : Π (x : Nat) → Le (S p) x → Id Nat (countA x Z Arr()) Z). unit)
      (λ (k : Nat). λ (h : Nat). λ (t : Array k Nat).
        λ (ih : (Π (x : Nat) → Le (S p) x → Id Nat (countA x k t) Z) → UbA p k t).
          λ (hn : Π (x : Nat) → Le (S p) x → Id Nat (countA x (S k) (acons k h t)) Z).
            Pair(
              elim (Leb h p) return (λ (bv : Bool). Id Bool (Leb h p) bv → Le h p) {
                True => λ (e : Id Bool (Leb h p) True). leb_true_le h p e,
                False => λ (e : Id Bool (Leb h p) False).
                  botElim (Le h p)
                    (znots (countA h k t)
                      (id_trans Nat Z (countA h (S k) (acons k h t)) (S (countA h k t))
                        (id_sym Nat (countA h (S k) (acons k h t)) Z (hn h (leb_false_gt h p e)))
                        (count_acons_hit h h k t (eqb_refl h))))
              } Refl,
              ih (λ (x : Nat). λ (hx : Le (S p) x).
                    elim (Eqb x h) return (λ (bv : Bool).
                        Id Bool (Eqb x h) bv → Id Nat (countA x k t) Z) {
                      True => λ (eq : Id Bool (Eqb x h) True).
                        botElim (Id Nat (countA x k t) Z)
                          (znots (countA x k t)
                            (id_trans Nat Z (countA x (S k) (acons k h t)) (S (countA x k t))
                              (id_sym Nat (countA x (S k) (acons k h t)) Z (hn x hx))
                              (count_acons_hit x h k t eq))),
                      False => λ (eq : Id Bool (Eqb x h) False).
                        id_trans Nat (countA x k t) (countA x (S k) (acons k h t)) Z
                          (id_sym Nat (countA x (S k) (acons k h t)) (countA x k t)
                            (count_acons_miss x h k t eq))
                          (hn x hx)
                    } Refl)))
      n a }
def ub_of_noAboveA_ty : Term := prog{
  Π (p : Nat) → Π (n : Nat) → Π (a : Array n Nat) →
    (Π (x : Nat) → Le (S p) x → Id Nat (countA x n a) Z) → UbA p n a }

/-- THE KEYSTONE, transferred: an upper bound survives any count-preserving
    rearrangement — which is exactly what a recursive sort hands back about the part it
    sorted. -/
def ub_permA : Term := prog{
  λ (p : Nat). λ (m : Nat). λ (a : Array m Nat). λ (q : Nat). λ (b : Array q Nat).
    λ (hc : Π (x : Nat) → Id Nat (countA x m a) (countA x q b)). λ (hb : UbA p q b).
      ub_of_noAboveA p m a (λ (x : Nat). λ (hx : Le (S p) x).
        id_trans Nat (countA x m a) (countA x q b) Z (hc x)
          (noAbove_of_ubA p q b hb x hx)) }
def ub_permA_ty : Term := prog{
  Π (p : Nat) → Π (m : Nat) → Π (a : Array m Nat) → Π (q : Nat) → Π (b : Array q Nat) →
    (Π (x : Nat) → Id Nat (countA x m a) (countA x q b)) → UbA p q b → UbA p m a }

def noBelow_of_lbA : Term := prog{
  λ (p : Nat). λ (n : Nat). λ (a : Array n Nat).
    arrRec Nat (λ (m : Nat). λ (az : Array m Nat).
        LbA p m az → Π (x : Nat) → Le (S x) p → Id Nat (countA x m az) Z)
      (λ (u : Unit). λ (x : Nat). λ (hx : Le (S x) p). Refl)
      (λ (k : Nat). λ (h : Nat). λ (t : Array k Nat).
        λ (ih : LbA p k t → Π (x : Nat) → Le (S x) p → Id Nat (countA x k t) Z).
          λ (u : Σ (hh : Le p h) → LbA p k t). λ (x : Nat). λ (hx : Le (S x) p).
            id_trans Nat (countA x (S k) (acons k h t)) (countA x k t) Z
              (count_acons_miss x h k t
                (eqb_lt_false x h (le_trans (S x) p h hx (lb_headA p k h t u))))
              (ih (lb_tailA p k h t u) x hx))
      n a }
def noBelow_of_lbA_ty : Term := prog{
  Π (p : Nat) → Π (n : Nat) → Π (a : Array n Nat) → LbA p n a →
    Π (x : Nat) → Le (S x) p → Id Nat (countA x n a) Z }

def lb_of_noBelowA : Term := prog{
  λ (p : Nat). λ (n : Nat). λ (a : Array n Nat).
    arrRec Nat (λ (m : Nat). λ (az : Array m Nat).
        (Π (x : Nat) → Le (S x) p → Id Nat (countA x m az) Z) → LbA p m az)
      (λ (hn : Π (x : Nat) → Le (S x) p → Id Nat (countA x Z Arr()) Z). unit)
      (λ (k : Nat). λ (h : Nat). λ (t : Array k Nat).
        λ (ih : (Π (x : Nat) → Le (S x) p → Id Nat (countA x k t) Z) → LbA p k t).
          λ (hn : Π (x : Nat) → Le (S x) p → Id Nat (countA x (S k) (acons k h t)) Z).
            Pair(
              elim (Leb p h) return (λ (bv : Bool). Id Bool (Leb p h) bv → Le p h) {
                True => λ (e : Id Bool (Leb p h) True). leb_true_le p h e,
                False => λ (e : Id Bool (Leb p h) False).
                  botElim (Le p h)
                    (znots (countA h k t)
                      (id_trans Nat Z (countA h (S k) (acons k h t)) (S (countA h k t))
                        (id_sym Nat (countA h (S k) (acons k h t)) Z (hn h (leb_false_gt p h e)))
                        (count_acons_hit h h k t (eqb_refl h))))
              } Refl,
              ih (λ (x : Nat). λ (hx : Le (S x) p).
                    elim (Eqb x h) return (λ (bv : Bool).
                        Id Bool (Eqb x h) bv → Id Nat (countA x k t) Z) {
                      True => λ (eq : Id Bool (Eqb x h) True).
                        botElim (Id Nat (countA x k t) Z)
                          (znots (countA x k t)
                            (id_trans Nat Z (countA x (S k) (acons k h t)) (S (countA x k t))
                              (id_sym Nat (countA x (S k) (acons k h t)) Z (hn x hx))
                              (count_acons_hit x h k t eq))),
                      False => λ (eq : Id Bool (Eqb x h) False).
                        id_trans Nat (countA x k t) (countA x (S k) (acons k h t)) Z
                          (id_sym Nat (countA x (S k) (acons k h t)) (countA x k t)
                            (count_acons_miss x h k t eq))
                          (hn x hx)
                    } Refl)))
      n a }
def lb_of_noBelowA_ty : Term := prog{
  Π (p : Nat) → Π (n : Nat) → Π (a : Array n Nat) →
    (Π (x : Nat) → Le (S x) p → Id Nat (countA x n a) Z) → LbA p n a }

def lb_permA : Term := prog{
  λ (p : Nat). λ (m : Nat). λ (a : Array m Nat). λ (q : Nat). λ (b : Array q Nat).
    λ (hc : Π (x : Nat) → Id Nat (countA x m a) (countA x q b)). λ (hb : LbA p q b).
      lb_of_noBelowA p m a (λ (x : Nat). λ (hx : Le (S x) p).
        id_trans Nat (countA x m a) (countA x q b) Z (hc x)
          (noBelow_of_lbA p q b hb x hx)) }
def lb_permA_ty : Term := prog{
  Π (p : Nat) → Π (m : Nat) → Π (a : Array m Nat) → Π (q : Nat) → Π (b : Array q Nat) →
    (Π (x : Nat) → Id Nat (countA x m a) (countA x q b)) → LbA p q b → LbA p m a }

/-- Two-element count commutation over arrays — `cons2_comm`'s transfer at the fixed
    width the miniature sort needs. Double case split on `eqb`, all four arms `Refl`;
    the `eqb m a = False` arm needs no inner split because both sides already agree. -/
def count_swap2 : Term := prog{
  λ (m : Nat). λ (a : Nat). λ (b : Nat).
    elim (Eqb m a) generalizing (Id Nat (countA m 2 Arr(b, a)) (countA m 2 Arr(a, b))) {
      True => elim (Eqb m b) generalizing
        (Id Nat (boolRec (λ (w : Bool). Nat) (S (S Z)) (S Z) (Eqb m b))
                (S (boolRec (λ (w : Bool). Nat) (S Z) Z (Eqb m b)))) {
        True => Refl, False => Refl },
      False => Refl } }
def count_swap2_ty : Term := prog{
  Π (m : Nat) → Π (a : Nat) → Π (b : Nat) →
    Id Nat (countA m 2 Arr(b, a)) (countA m 2 Arr(a, b)) }

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
    `Array (add k r)` convert only after the caller's own carve has refined `n`, and a
    segment cannot be returned by value either, because reading one MOVES it and leaves
    the borrow holding a hole. So the partition's interface is positional and the sort's
    internals are not — one predicate, `PartA`, and the bridge back to ¶1.3's transferred
    library is a single lemma.

    Two predicates, both `arrRec` over the cons view with the skip count threaded as an
    ordinary `Nat` argument (M22's bounded-Π encoding, which the whole-array predicates
    got to drop and these do not):

      `SplitA p k a`  the first `k` elements are ≤ p, the rest are ≥ p
      `PartA pv k a`  the first `k` are ≤ pv, element `k` **is** pv, the rest are ≥ pv

    `PartA` is shaped so its `kz = 0` case yields `LbA` — the LIBRARY predicate, not a
    third one — which is what makes the bridge to `sorted_arrCat` one lemma instead of a
    monotonicity stratum. -/

/-- Transport along a `Nat` identity — `list_rw`'s counterpart, needed to move the
    glue from the pivot VALUE the partition returned to the element sitting in the
    carved pivot slot. -/
def nat_rw : Term := prog{
  λ (P : Nat → Type). λ (x : Nat). λ (y : Nat). λ (h : Id Nat x y). λ (px : P x).
    j Nat x (λ (y2 : Nat). λ (hh : Id Nat x y2). P y2) px y h }
def nat_rw_ty : Term := prog{
  Π (P : Nat → Type) → Π (x : Nat) → Π (y : Nat) → Id Nat x y → P x → P y }

/-- `Le n Z ⟹ n = Z`. The array quicksort tests emptiness with `leb 1 n` rather than
    by matching `n`, because matching refines the length to `S m` and T2's rigid-extent
    restriction then blocks the three-way carve at the returned index. So the False
    branch holds `Le n Z` and has to turn it into the equation the nil lemmas want. -/
def le_zero_eq : Term := prog{
  λ (n : Nat). elim n return (λ (z : Nat). Le z Z → Id Nat z Z) {
    Z => λ (h : Le Z Z). Refl,
    S (n2) ih => λ (h : Bot). botElim (Id Nat (S n2) Z) h } }
def le_zero_eq_ty : Term := prog{ Π (n : Nat) → Le n Z → Id Nat n Z }

/-- `SortedA` of an array whose LENGTH is zero.

    Not `unit`, and that is the point: there is no η at length zero. `SortedA Z σ` is a
    stuck `arrRec` — the recursor fires on `Arr`, never on the index — so an opaque
    length-zero payload does not compute to `Unit` and the sort's base case cannot be
    discharged by the trivial term. The induction is on the ARRAY with the equation
    carried, and the cons case is dead. -/
def sortedA_nil : Term := prog{
  λ (n : Nat). λ (a : Array n Nat).
    arrRec Nat (λ (m : Nat). λ (b : Array m Nat). Id Nat m Z → SortedA m b)
      (λ (h : Id Nat Z Z). unit)
      (λ (k : Nat). λ (hh : Nat). λ (t : Array k Nat).
        λ (ih : Id Nat k Z → SortedA k t).
          λ (h : Id Nat (S k) Z).
            botElim (SortedA (S k) (acons k hh t)) (znots k (id_sym Nat (S k) Z h)))
      n a }
def sortedA_nil_ty : Term := prog{
  Π (n : Nat) → Π (a : Array n Nat) → Id Nat n Z → SortedA n a }

/-- `SplitA p k a` — the first `k` elements are ≤ `p`, the rest are ≥ `p`. -/
def SplitA : Term := prog{
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
    `SplitA` does not give: without it the element in the carved pivot slot is merely
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

/-- `SplitA` of a length-zero array, at any skip count — `sortedA_nil`'s twin, and
    needed for the same reason. -/
def splitA_nil : Term := prog{
  λ (p : Nat). λ (kz : Nat). λ (n : Nat). λ (a : Array n Nat). λ (hz : Id Nat n Z).
    arrRec Nat (λ (m : Nat). λ (b : Array m Nat).
        Π (k2 : Nat) → Id Nat m Z → SplitA p k2 m b)
      (λ (k2 : Nat). λ (h : Id Nat Z Z). unit)
      (λ (m : Nat). λ (hh : Nat). λ (t : Array m Nat).
        λ (ih : Π (k2 : Nat) → Id Nat m Z → SplitA p k2 m t).
          λ (k2 : Nat). λ (h : Id Nat (S m) Z).
            botElim (SplitA p k2 (S m) (acons m hh t)) (znots m (id_sym Nat (S m) Z h)))
      n a kz hz }
def splitA_nil_ty : Term := prog{
  Π (p : Nat) → Π (kz : Nat) → Π (n : Nat) → Π (a : Array n Nat) →
    Id Nat n Z → SplitA p kz n a }

/-! ### Crossing a concatenation

    Every one of these is an induction on the LEFT array and nothing else — the same
    `arrRec` shape as `bound_arrCat` and `sorted_arrCat`, which is the evidence that
    this stratum, though new, is not a new KIND of work.

    The spellings are chosen to be the ones the programs actually produce, which is
    R7's lesson arriving in the pure layer: `add k mm` where the carve decomposes, `S k`
    where a skip count runs one PAST the left part. Stating `splitA_cat_e1` with the
    generic `add k t` instead of `S k` would have been more general and unusable, since
    `S k` and `add k 1` do not convert for symbolic `k` and the program has the former. -/

/-- A zero skip count is a lower bound on the whole array — the crossing from the
    partition layer back into ¶1.3's transferred library. -/
def splitA0_lb : Term := prog{
  λ (p : Nat). λ (n : Nat). λ (a : Array n Nat).
    arrRec Nat (λ (m : Nat). λ (b : Array m Nat). SplitA p Z m b → LbA p m b)
      (λ (h : Unit). unit)
      (λ (k : Nat). λ (hh : Nat). λ (t : Array k Nat).
        λ (ih : SplitA p Z k t → LbA p k t).
          λ (s : Σ (h2 : Le p hh) → SplitA p Z k t).
            elim s return (λ (qz : Σ (h2 : Le p hh) → SplitA p Z k t). LbA p (S k) (acons k hh t)) {
              Pair (u) (v) => Pair(u, ih v) })
      n a }
def splitA0_lb_ty : Term := prog{
  Π (p : Nat) → Π (n : Nat) → Π (a : Array n Nat) → SplitA p Z n a → LbA p n a }

/-- Split a `SplitA` whose skip count runs ONE PAST the left part: the left part is
    wholly bounded, and what is left is a `SplitA` at skip 1 over the right part. This
    is the shape the swap branch needs — it reads off both "the left part is all ≤ p"
    and "the element about to be swapped out is ≤ p" in one step. -/
def splitA_cat_e1 : Term := prog{
  λ (p : Nat). λ (k : Nat). λ (mm : Nat). λ (l : Array k Nat). λ (w : Array mm Nat).
    arrRec Nat (λ (kz : Nat). λ (lz : Array kz Nat).
        SplitA p (S kz) (Add kz mm) (arrCat kz mm lz w) →
          Σ (hu : UbA p kz lz) → SplitA p (S Z) mm w)
      (λ (h : SplitA p (S Z) mm w). Pair(unit, h))
      (λ (k2 : Nat). λ (hh : Nat). λ (t : Array k2 Nat).
        λ (ih : SplitA p (S k2) (Add k2 mm) (arrCat k2 mm t w) →
                  Σ (hu : UbA p k2 t) → SplitA p (S Z) mm w).
          λ (s : Σ (h2 : Le hh p) → SplitA p (S k2) (Add k2 mm) (arrCat k2 mm t w)).
            elim s return (λ (qz : Σ (h2 : Le hh p) →
                                SplitA p (S k2) (Add k2 mm) (arrCat k2 mm t w)).
                Σ (hu : UbA p (S k2) (acons k2 hh t)) → SplitA p (S Z) mm w) {
              Pair (u) (v) =>
                elim (ih v) return (λ (qz2 : Σ (hu : UbA p k2 t) → SplitA p (S Z) mm w).
                    Σ (hu : UbA p (S k2) (acons k2 hh t)) → SplitA p (S Z) mm w) {
                  Pair (a1) (b1) => Pair(Pair(u, a1), b1) } })
      k l }
def splitA_cat_e1_ty : Term := prog{
  Π (p : Nat) → Π (k : Nat) → Π (mm : Nat) → Π (l : Array k Nat) → Π (w : Array mm Nat) →
    SplitA p (S k) (Add k mm) (arrCat k mm l w) →
      Σ (hu : UbA p k l) → SplitA p (S Z) mm w }

/-- The converse at skip exactly `k`: a bounded left part in front of a `SplitA` at
    skip zero is a `SplitA` at skip `k`. -/
def splitA_cat_i0 : Term := prog{
  λ (p : Nat). λ (k : Nat). λ (mm : Nat). λ (l : Array k Nat). λ (w : Array mm Nat).
    arrRec Nat (λ (kz : Nat). λ (lz : Array kz Nat).
        UbA p kz lz → SplitA p Z mm w → SplitA p kz (Add kz mm) (arrCat kz mm lz w))
      (λ (u : Unit). λ (h : SplitA p Z mm w). h)
      (λ (k2 : Nat). λ (hh : Nat). λ (t : Array k2 Nat).
        λ (ih : UbA p k2 t → SplitA p Z mm w →
                  SplitA p k2 (Add k2 mm) (arrCat k2 mm t w)).
          λ (u : Σ (h2 : Le hh p) → UbA p k2 t). λ (h : SplitA p Z mm w).
            elim u return (λ (qz : Σ (h2 : Le hh p) → UbA p k2 t).
                SplitA p (S k2) (Add (S k2) mm) (arrCat (S k2) mm (acons k2 hh t) w)) {
              Pair (a1) (b1) => Pair(a1, ih b1 h) })
      k l }
def splitA_cat_i0_ty : Term := prog{
  Π (p : Nat) → Π (k : Nat) → Π (mm : Nat) → Π (l : Array k Nat) → Π (w : Array mm Nat) →
    UbA p k l → SplitA p Z mm w → SplitA p k (Add k mm) (arrCat k mm l w) }

/-- `PartA`'s introduction, the partition's last step: a bounded left part in front of
    a `PartA` at skip zero (which is "the head IS the pivot, the tail is ≥ it"). -/
def partA_cat_i0 : Term := prog{
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
def partA_cat_i0_ty : Term := prog{
  Π (pv : Nat) → Π (k : Nat) → Π (mm : Nat) → Π (l : Array k Nat) → Π (w : Array mm Nat) →
    UbA pv k l → PartA pv Z mm w → PartA pv k (Add k mm) (arrCat k mm l w) }

/-- **THE BRIDGE.** `PartA`'s elimination at the sort's own carve: the left segment is
    bounded above by the pivot, and what remains is `PartA` at skip zero over the pivot
    slot and the right segment — which unfolds, with no further lemma, to exactly
    `Id Nat (that element) pv` and `LbA pv (right segment)`. Those three facts are
    `sorted_arrCat`'s four hypotheses minus the two the recursive calls supply. -/
def partA_cat_e0 : Term := prog{
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
def partA_cat_e0_ty : Term := prog{
  Π (pv : Nat) → Π (k : Nat) → Π (mm : Nat) → Π (l : Array k Nat) → Π (w : Array mm Nat) →
    PartA pv k (Add k mm) (arrCat k mm l w) →
      Σ (hu : UbA pv k l) → PartA pv Z mm w }

/-! ### The same crossings, one conclusion each

    A body cannot conveniently destructure a Σ — a `let`-bound pure value is not
    type-checked (§23's filed checker gap), so the alternative is an inline `elim` whose
    `return` motive is the function's whole return type written out again. Splitting each
    crossing into its two conclusions moves that cost into the pure layer, where writing
    the types is free, and keeps the programs readable. -/

def splitA_cat_ub : Term := prog{
  λ (p : Nat). λ (k : Nat). λ (mm : Nat). λ (l : Array k Nat). λ (w : Array mm Nat).
    λ (s : SplitA p (S k) (Add k mm) (arrCat k mm l w)).
      elim (splitA_cat_e1 p k mm l w s)
        return (λ (qz : Σ (hu : UbA p k l) → SplitA p (S Z) mm w). UbA p k l) {
          Pair (u) (v) => u } }
def splitA_cat_ub_ty : Term := prog{
  Π (p : Nat) → Π (k : Nat) → Π (mm : Nat) → Π (l : Array k Nat) → Π (w : Array mm Nat) →
    SplitA p (S k) (Add k mm) (arrCat k mm l w) → UbA p k l }

def splitA_cat_rest : Term := prog{
  λ (p : Nat). λ (k : Nat). λ (mm : Nat). λ (l : Array k Nat). λ (w : Array mm Nat).
    λ (s : SplitA p (S k) (Add k mm) (arrCat k mm l w)).
      elim (splitA_cat_e1 p k mm l w s)
        return (λ (qz : Σ (hu : UbA p k l) → SplitA p (S Z) mm w). SplitA p (S Z) mm w) {
          Pair (u) (v) => v } }
def splitA_cat_rest_ty : Term := prog{
  Π (p : Nat) → Π (k : Nat) → Π (mm : Nat) → Π (l : Array k Nat) → Π (w : Array mm Nat) →
    SplitA p (S k) (Add k mm) (arrCat k mm l w) → SplitA p (S Z) mm w }

/-- A skip-1 `SplitA` over a cons: its head is bounded, and its tail is a skip-0 one.
    Both are definitional unfoldings; naming them keeps the swap branch flat. -/
def splitA1_head : Term := prog{
  λ (p : Nat). λ (r : Nat). λ (g : Array r Nat). λ (yv : Nat).
    λ (s : Σ (hh : Le yv p) → SplitA p Z r g).
      elim s return (λ (qz : Σ (hh : Le yv p) → SplitA p Z r g). Le yv p) {
        Pair (u) (v) => u } }
def splitA1_head_ty : Term := prog{
  Π (p : Nat) → Π (r : Nat) → Π (g : Array r Nat) → Π (yv : Nat) →
    SplitA p (S Z) (S r) (acons r yv g) → Le yv p }

def splitA1_tail : Term := prog{
  λ (p : Nat). λ (r : Nat). λ (g : Array r Nat). λ (yv : Nat).
    λ (s : Σ (hh : Le yv p) → SplitA p Z r g).
      elim s return (λ (qz : Σ (hh : Le yv p) → SplitA p Z r g). SplitA p Z r g) {
        Pair (u) (v) => v } }
def splitA1_tail_ty : Term := prog{
  Π (p : Nat) → Π (r : Nat) → Π (g : Array r Nat) → Π (yv : Nat) →
    SplitA p (S Z) (S r) (acons r yv g) → SplitA p Z r g }

def partA_cat_ub : Term := prog{
  λ (pv : Nat). λ (k : Nat). λ (mm : Nat). λ (l : Array k Nat). λ (w : Array mm Nat).
    λ (s : PartA pv k (Add k mm) (arrCat k mm l w)).
      elim (partA_cat_e0 pv k mm l w s)
        return (λ (qz : Σ (hu : UbA pv k l) → PartA pv Z mm w). UbA pv k l) {
          Pair (u) (v) => u } }
def partA_cat_ub_ty : Term := prog{
  Π (pv : Nat) → Π (k : Nat) → Π (mm : Nat) → Π (l : Array k Nat) → Π (w : Array mm Nat) →
    PartA pv k (Add k mm) (arrCat k mm l w) → UbA pv k l }

def partA_cat_rest : Term := prog{
  λ (pv : Nat). λ (k : Nat). λ (mm : Nat). λ (l : Array k Nat). λ (w : Array mm Nat).
    λ (s : PartA pv k (Add k mm) (arrCat k mm l w)).
      elim (partA_cat_e0 pv k mm l w s)
        return (λ (qz : Σ (hu : UbA pv k l) → PartA pv Z mm w). PartA pv Z mm w) {
          Pair (u) (v) => v } }
def partA_cat_rest_ty : Term := prog{
  Π (pv : Nat) → Π (k : Nat) → Π (mm : Nat) → Π (l : Array k Nat) → Π (w : Array mm Nat) →
    PartA pv k (Add k mm) (arrCat k mm l w) → PartA pv Z mm w }

/-- The pivot slot, read off a skip-0 `PartA`: the element there IS the pivot, and
    everything after it is bounded below by the pivot. These two are `sorted_arrCat`'s
    remaining hypotheses, and the reason `PartA` records the pivot's identity at all. -/
def partA0_eq : Term := prog{
  λ (pv : Nat). λ (jj : Nat). λ (g : Array jj Nat). λ (ev : Nat).
    λ (s : Σ (he : Id Nat ev pv) → LbA pv jj g).
      elim s return (λ (qz : Σ (he : Id Nat ev pv) → LbA pv jj g). Id Nat ev pv) {
        Pair (u) (v) => u } }
def partA0_eq_ty : Term := prog{
  Π (pv : Nat) → Π (jj : Nat) → Π (g : Array jj Nat) → Π (ev : Nat) →
    PartA pv Z (S jj) (acons jj ev g) → Id Nat ev pv }

def partA0_lb : Term := prog{
  λ (pv : Nat). λ (jj : Nat). λ (g : Array jj Nat). λ (ev : Nat).
    λ (s : Σ (he : Id Nat ev pv) → LbA pv jj g).
      elim s return (λ (qz : Σ (he : Id Nat ev pv) → LbA pv jj g). LbA pv jj g) {
        Pair (u) (v) => v } }
def partA0_lb_ty : Term := prog{
  Π (pv : Nat) → Π (jj : Nat) → Π (g : Array jj Nat) → Π (ev : Nat) →
    PartA pv Z (S jj) (acons jj ev g) → LbA pv jj g }

/-! ### The count layer for a swap across a carve

    The partition's one mutating step exchanges the array's head with the element at
    the split point, and those two sit in DIFFERENT segments — the whole reason the
    swap is writable at all is that each is at index 0 of its own carve (¶6's "a
    segment with its own zero"). What the permutation conjunct then owes is that the
    exchange does not move any count, over a spine four levels deep. -/

/-- `countA`'s own step function, named so a congruence can be stated over it: the
    count of a cons is a `bump` of the count of its tail. -/
def bumpN : Term := prog{
  λ (b : Bool). λ (c : Nat). elim b return (λ (w : Bool). Nat) { True => S c, False => c } }

/-- Congruence for `countA` under a cons — `count_cons_congr`'s array counterpart. -/
def count_acons_congr : Term := prog{
  λ (q : Nat). λ (h : Nat). λ (k : Nat). λ (t1 : Array k Nat). λ (t2 : Array k Nat).
    λ (hc : Id Nat (countA q k t1) (countA q k t2)).
      id_congr Nat Nat (λ (c : Nat). bumpN (Eqb q h) c)
        (countA q k t1) (countA q k t2) hc }
def count_acons_congr_ty : Term := prog{
  Π (q : Nat) → Π (h : Nat) → Π (k : Nat) → Π (t1 : Array k Nat) → Π (t2 : Array k Nat) →
    Id Nat (countA q k t1) (countA q k t2) →
      Id Nat (countA q (S k) (acons k h t1)) (countA q (S k) (acons k h t2)) }

/-- The arithmetic core of the swap, over the two `bump`s alone: which of the two
    exchanged elements is being counted does not matter. Four arms; the two mixed ones
    are `add_succ` and its symmetry, and the two matching ones are `Refl` — `count_swap2`
    at width two had all four `Refl` because both counts were concrete. -/
def bump_comm : Term := prog{
  λ (b1 : Bool). λ (b2 : Bool). λ (cl : Nat). λ (cg : Nat).
    elim b1 return (λ (w : Bool).
        Id Nat (bumpN b2 (Add cl (bumpN w cg))) (bumpN w (Add cl (bumpN b2 cg)))) {
      True =>
        elim b2 return (λ (w2 : Bool).
            Id Nat (bumpN w2 (Add cl (S cg))) (S (Add cl (bumpN w2 cg)))) {
          True => Refl,
          False => add_succ cl cg },
      False =>
        elim b2 return (λ (w2 : Bool).
            Id Nat (bumpN w2 (Add cl cg)) (Add cl (bumpN w2 cg))) {
          True => id_sym Nat (Add cl (S cg)) (S (Add cl cg)) (add_succ cl cg),
          False => Refl } } }
def bump_comm_ty : Term := prog{
  Π (b1 : Bool) → Π (b2 : Bool) → Π (cl : Nat) → Π (cg : Nat) →
    Id Nat (bumpN b2 (Add cl (bumpN b1 cg))) (bumpN b1 (Add cl (bumpN b2 cg))) }

/-- **The swap preserves every count**, stated over exactly the spine the partition
    produces: head, left segment, the swapped cell, right segment. Two `count_arrCat`
    rewrites bracket `bump_comm`. -/
def count_swapA : Term := prog{
  λ (q : Nat). λ (x : Nat). λ (y : Nat). λ (k : Nat). λ (l : Array k Nat).
  λ (r : Nat). λ (g : Array r Nat).
    id_trans Nat
      (countA q (S (Add k (S r))) (acons (Add k (S r)) y (arrCat k (S r) l (acons r x g))))
      (bumpN (Eqb q y) (Add (countA q k l) (bumpN (Eqb q x) (countA q r g))))
      (countA q (S (Add k (S r))) (acons (Add k (S r)) x (arrCat k (S r) l (acons r y g))))
      (id_congr Nat Nat (λ (c : Nat). bumpN (Eqb q y) c)
         (countA q (Add k (S r)) (arrCat k (S r) l (acons r x g)))
         (Add (countA q k l) (countA q (S r) (acons r x g)))
         (count_arrCat q k l (S r) (acons r x g)))
      (id_trans Nat
        (bumpN (Eqb q y) (Add (countA q k l) (bumpN (Eqb q x) (countA q r g))))
        (bumpN (Eqb q x) (Add (countA q k l) (bumpN (Eqb q y) (countA q r g))))
        (countA q (S (Add k (S r))) (acons (Add k (S r)) x (arrCat k (S r) l (acons r y g))))
        (bump_comm (Eqb q x) (Eqb q y) (countA q k l) (countA q r g))
        (id_sym Nat
          (countA q (S (Add k (S r))) (acons (Add k (S r)) x (arrCat k (S r) l (acons r y g))))
          (bumpN (Eqb q x) (Add (countA q k l) (bumpN (Eqb q y) (countA q r g))))
          (id_congr Nat Nat (λ (c : Nat). bumpN (Eqb q x) c)
             (countA q (Add k (S r)) (arrCat k (S r) l (acons r y g)))
             (Add (countA q k l) (countA q (S r) (acons r y g)))
             (count_arrCat q k l (S r) (acons r y g))))) }
def count_swapA_ty : Term := prog{
  Π (q : Nat) → Π (x : Nat) → Π (y : Nat) → Π (k : Nat) → Π (l : Array k Nat) →
  Π (r : Nat) → Π (g : Array r Nat) →
    Id Nat (countA q (S (Add k (S r))) (acons (Add k (S r)) y (arrCat k (S r) l (acons r x g))))
           (countA q (S (Add k (S r))) (acons (Add k (S r)) x (arrCat k (S r) l (acons r y g)))) }

end Dllbc.StdLemmas

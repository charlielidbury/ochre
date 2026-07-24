import Dllbc.Std
import Dllbc.PureMacro

/-!
# `Dllbc.StdLemmas` — the pure lemmas, authored in the §15 surface syntax

The M11 wall — `le_trans` as a raw de Bruijn term across ~15 binder contexts,
each mis-index failing silently — collapsed by names and explicit motives. Every
lemma here is written in `pure{ … }`: binders are named, motives are written once
and visible, and elaboration resolves names or errors (no silent fallback). The
kernel terms they elaborate to are the same de Bruijn `Term`s hasType already
checks; the surface is authoring sugar only.

`Le`/`count` are the surface names for the library functions (Term-valued, so a
`pure{ }` application `Le a b` is an ordinary app spine).
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

def le_refl : Term := pure{
  λ (n : Nat). elim n return (λ (m : Nat). Le m m) {
    Z => unit,
    S (k) ih => ih } }
def le_refl_ty : Term := pure{ Π (n : Nat) → Le n n }

-- The wall. Single outer elim on `a`; the `S` case elims on `b`, whose `S` case
-- elims on `c`, with the IH applied at the peeled proofs — every step
-- definitional through the `Le` equations. Nested, but every binder is NAMED and
-- every motive is written once and visible.
def le_trans : Term := pure{
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
def le_trans_ty : Term := pure{
  Π (a : Nat) → Π (b : Nat) → Π (c : Nat) → Le a b → Le b c → Le a c }

-- Right-successor monotonicity: `a ≤ b ⟹ a ≤ S b`. Double induction (on `a`,
-- casing `b`): the `Z` head is trivial (`Le Z _ = ⊤`); the `S a'` head cases `b`
-- (`Le (S a') Z = ⊥`, else `Le a' b'` and the IH lifts it to `Le a' (S b')`).
-- The glue `count_swapL'` needs to bend swapS's `Le (S i) j` into count_swapL's
-- `Le (S i) (len l)` via one `le_trans`.
def le_up_r : Term := pure{
  λ (a : Nat). elim a return (λ (az : Nat). Π (b : Nat) → Le az b → Le az (S b)) {
    Z => λ (b : Nat). λ (h : Le Z b). unit,
    S (a') ih => λ (b : Nat). λ (h : Le (S a') b).
      elim b return (λ (bz : Nat). Le (S a') bz → Le (S a') (S bz)) {
        Z => λ (h0 : Le (S a') Z). botElim (Le (S a') (S Z)) h0,
        S (b') ihb => λ (h0 : Le (S a') (S b')). ih b' h0
      } h } }
def le_up_r_ty : Term := pure{ Π (a : Nat) → Π (b : Nat) → Le a b → Le a (S b) }

-- `i ≤ i + g`: the boundary never passes the scan position it feeds. A clean
-- induction on `i` (`add (S i') g = S (add i' g)`, so `Le (S i') (add (S i') g)`
-- reduces to the IH). The partition swaps consume this as their `pij`.
def le_add : Term := pure{
  λ (i : Nat). elim i return (λ (iz : Nat). Π (g : Nat) → Le iz (add iz g)) {
    Z => λ (g : Nat). unit,
    S (i') ih => λ (g : Nat). ih g } }
def le_add_ty : Term := pure{ Π (i : Nat) → Π (g : Nat) → Le i (add i g) }

-- `b ≤ a + b` — the companion where the summand is on the LEFT (`le_add` has it on
-- the right). Induction on `a`: base is `le_refl` (`add Z b = b`), step lifts the
-- IH with `le_up_r` (`add (S a') b = S (add a' b)`). The scan-position bound uses
-- this because the length equation carries the remaining count `k` on the left.
def le_add_l : Term := pure{
  λ (b : Nat). λ (a : Nat).
    elim a return (λ (az : Nat). Le b (add az b)) {
      Z => le_refl b,
      S (a') ih => le_up_r b (add a' b) ih } }
def le_add_l_ty : Term := pure{ Π (b : Nat) → Π (a : Nat) → Le b (add a b) }

-- `S i ≤ i + (S g)` — the swap's `pij`: the boundary `S i` is below the scan
-- position `S (add i (S g))` whenever the gap is non-empty. Induction on `i`
-- avoids an add_succ transport (`add (S i') x = S (add i' x)` is definitional),
-- so no rewrite is needed here.
def le_add_succ : Term := pure{
  λ (i : Nat). elim i return (λ (iz : Nat). Π (g : Nat) → Le (S iz) (add iz (S g))) {
    Z => λ (g : Nat). unit,
    S (i') ih => λ (g : Nat). ih g } }
def le_add_succ_ty : Term := pure{ Π (i : Nat) → Π (g : Nat) → Le (S i) (add i (S g)) }

-- Transport a `Le` along an `Id` on its SECOND argument: `x = y ⟹ Le a x → Le a
-- y`. The bounds derived over the arithmetic normal form are moved onto `len *v`
-- (and back through `len_swapL`) with this J-transport — the "le_trans/le_step
-- glue where descent is not definitional".
def le_rw_r : Term := pure{
  λ (a : Nat). λ (x : Nat). λ (y : Nat). λ (h : Id Nat x y). λ (p : Le a x).
    j Nat x (λ (y' : Nat). λ (hh : Id Nat x y'). Le a y') p y h }
def le_rw_r_ty : Term := pure{ Π (a : Nat) → Π (x : Nat) → Π (y : Nat) → Id Nat x y → Le a x → Le a y }

-- Transport a `Le` along an `Id` on its FIRST (smaller) argument: `x = y ⟹ Le x
-- b → Le y b`. The range partition's bound `Le (add lo (S (add k (add i g))))
-- (len *v)` is invariant across the recursion (the sum k+i+g is preserved), but
-- its SYNTACTIC form shifts as k descends and i/g grow; this moves the bound
-- between forms via the hshift identities — the Le mirror of le_rw_r, and the one
-- lemma the M20 Id-toolkit lacked for the subrange generalization (§21).
def le_rw_l : Term := pure{
  λ (b : Nat). λ (x : Nat). λ (y : Nat). λ (h : Id Nat x y). λ (p : Le x b).
    j Nat x (λ (y' : Nat). λ (hh : Id Nat x y'). Le y' b) p y h }
def le_rw_l_ty : Term := pure{ Π (b : Nat) → Π (x : Nat) → Π (y : Nat) → Id Nat x y → Le x b → Le y b }

-- Left-add monotonicity: `a ≤ b ⟹ lo + a ≤ lo + b`. Induction on `lo`: base is
-- the hypothesis (`add Z x = x`), step is the IH verbatim (`add (S lo') x =
-- S (add lo' x)` and `Le (S _) (S _) = Le _ _` are both definitional). The range
-- partition's swap bounds shift the entry bound `Le (S i) (S (add i g))` through
-- `add lo` to reach `Le (add lo (S i)) (add lo (S (add i g)))` (§21).
def le_add_mono_l : Term := pure{
  λ (lo : Nat). λ (a : Nat). λ (b : Nat). λ (h : Le a b).
    elim lo return (λ (loz : Nat). Le (add loz a) (add loz b)) {
      Z => h,
      S (lo') ih => ih } }
def le_add_mono_l_ty : Term := pure{ Π (lo : Nat) → Π (a : Nat) → Π (b : Nat) → Le a b → Le (add lo a) (add lo b) }

/-! ## `id_trans`, `id_congr` — the J warm-ups partition's count-chaining consumes -/

def id_trans : Term := pure{
  λ (A : Type). λ (x : A). λ (y : A). λ (z : A). λ (p : Id A x y). λ (q : Id A y z).
    j A x (λ (y' : A). λ (h : Id A x y'). Id A y' z → Id A x z) (λ (h : Id A x z). h) y p q }
def id_trans_ty : Term := pure{
  Π (A : Type) → Π (x : A) → Π (y : A) → Π (z : A) → Id A x y → Id A y z → Id A x z }

def id_congr : Term := pure{
  λ (A : Type). λ (B : Type). λ (f : A → B). λ (x : A). λ (y : A). λ (p : Id A x y).
    j A x (λ (y' : A). λ (h : Id A x y'). Id B (f x) (f y')) Refl y p }
def id_congr_ty : Term := pure{
  Π (A : Type) → Π (B : Type) → Π (f : A → B) → Π (x : A) → Π (y : A) → Id A x y → Id B (f x) (f y) }

def id_sym : Term := pure{
  λ (A : Type). λ (x : A). λ (y : A). λ (p : Id A x y).
    j A x (λ (y' : A). λ (h : Id A x y'). Id A y' x) Refl y p }
def id_sym_ty : Term := pure{ Π (A : Type) → Π (x : A) → Π (y : A) → Id A x y → Id A y x }

/-! ## Arithmetic — the first double-inductions after the wall (§16 calibration) -/

def add_zero : Term := pure{
  λ (a : Nat). elim a return (λ (x : Nat). Id Nat (add x Z) x) {
    Z => Refl,
    S (a') ih => id_congr Nat Nat (λ (n : Nat). S n) (add a' Z) a' ih } }
def add_zero_ty : Term := pure{ Π (a : Nat) → Id Nat (add a Z) a }

def add_succ : Term := pure{
  λ (a : Nat). λ (b : Nat). elim a return (λ (x : Nat). Id Nat (add x (S b)) (S (add x b))) {
    Z => Refl,
    S (a') ih => id_congr Nat Nat (λ (n : Nat). S n) (add a' (S b)) (S (add a' b)) ih } }
def add_succ_ty : Term := pure{ Π (a : Nat) → Π (b : Nat) → Id Nat (add a (S b)) (S (add a b)) }

-- Commutativity: the classic proof, authored in the surface and checked first try.
def add_comm : Term := pure{
  λ (a : Nat). elim a return (λ (x : Nat). Π (b : Nat) → Id Nat (add x b) (add b x)) {
    Z => λ (b : Nat). id_sym Nat (add b Z) b (add_zero b),
    S (a') ih => λ (b : Nat).
      id_trans Nat (S (add a' b)) (S (add b a')) (add b (S a'))
        (id_congr Nat Nat (λ (n : Nat). S n) (add a' b) (add b a') (ih b))
        (id_sym Nat (add b (S a')) (S (add b a')) (add_succ b a')) } }
def add_comm_ty : Term := pure{ Π (a : Nat) → Π (b : Nat) → Id Nat (add a b) (add b a) }

def add_assoc : Term := pure{
  λ (a : Nat). elim a return (λ (x : Nat). Π (b : Nat) → Π (c : Nat) → Id Nat (add (add x b) c) (add x (add b c))) {
    Z => λ (b : Nat). λ (c : Nat). Refl,
    S (a') ih => λ (b : Nat). λ (c : Nat).
      id_congr Nat Nat (λ (n : Nat). S n) (add (add a' b) c) (add a' (add b c)) (ih b c) } }
def add_assoc_ty : Term := pure{ Π (a : Nat) → Π (b : Nat) → Π (c : Nat) → Id Nat (add (add a b) c) (add a (add b c)) }

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
def hshift_true : Term := pure{
  λ (k : Nat). λ (i : Nat). λ (g : Nat).
    id_sym Nat (add k (S (add i g))) (S (add k (add i g))) (add_succ k (add i g)) }
def hshift_true_ty : Term := pure{ Π (k : Nat) → Π (i : Nat) → Π (g : Nat) →
  Id Nat (add (S k) (add i g)) (add k (add (S i) g)) }

-- Gap growth: `add (S k) (add i g) = add k (add i (S g))` (move a successor from k
-- to g). `add i (S g)` is stuck (add recurses on i), so this needs add_succ TWICE
-- — once under `add k` to grow the gap, once to pull the successor out front.
def hshift_false : Term := pure{
  λ (k : Nat). λ (i : Nat). λ (g : Nat).
    id_sym Nat (add k (add i (S g))) (S (add k (add i g)))
      (id_trans Nat (add k (add i (S g))) (add k (S (add i g))) (S (add k (add i g)))
        (id_congr Nat Nat (λ (x : Nat). add k x) (add i (S g)) (S (add i g)) (add_succ i g))
        (add_succ k (add i g))) }
def hshift_false_ty : Term := pure{ Π (k : Nat) → Π (i : Nat) → Π (g : Nat) →
  Id Nat (add (S k) (add i g)) (add k (add i (S g))) }

-- `count`'s Cons-unfolding equation as an Id — definitional, a `Refl` after whnf.
def count_cons : Term := pure{ λ (m : Nat). λ (h : Nat). λ (t : List Nat). Refl }
def count_cons_ty : Term := pure{
  Π (m : Nat) → Π (h : Nat) → Π (t : List Nat) →
    Id Nat (count m (Cons h t)) (boolRec (λ (b : Bool). Nat) (S (count m t)) (count m t) (eqb m h)) }

/-! ## The `count`/`append`/`take`/`drop` lemmas (§16-2)

    `count_append` — count distributes over `append` — needs a dependent Bool-elim
    on `eqb m h` in the `Cons` case (the motive abstracts the `boolRec` that
    `count (Cons …)` unfolds to). `take_drop_id` reassembles a list from its
    prefix and suffix. Both are the building blocks the swap-count lemma consumes. -/

def count_append : Term := pure{
  λ (m : Nat). λ (a : List Nat). λ (b : List Nat).
    elim a return (λ (x : List Nat). Id Nat (count m (append x b)) (add (count m x) (count m b))) {
      Nil => Refl,
      Cons (h) (t) ih =>
        elim (eqb m h) return (λ (bv : Bool).
          Id Nat (boolRec (λ (w : Bool). Nat) (S (count m (append t b))) (count m (append t b)) bv)
                 (add (boolRec (λ (w : Bool). Nat) (S (count m t)) (count m t) bv) (count m b))) {
          True => id_congr Nat Nat (λ (n : Nat). S n) (count m (append t b)) (add (count m t) (count m b)) ih,
          False => ih
        }
    } }
def count_append_ty : Term := pure{
  Π (m : Nat) → Π (a : List Nat) → Π (b : List Nat) →
    Id Nat (count m (append a b)) (add (count m a) (count m b)) }

def take_drop_id : Term := pure{
  λ (i : Nat). elim i return (λ (k : Nat). Π (l : List Nat) → Id (List Nat) (append (take k l) (drop k l)) l) {
    Z => λ (l : List Nat). Refl,
    S (i') ih => λ (l : List Nat).
      elim l return (λ (x : List Nat). Id (List Nat) (append (take (S i') x) (drop (S i') x)) x) {
        Nil => Refl,
        Cons (h) (t) ihl =>
          id_congr (List Nat) (List Nat) (λ (r : List Nat). Cons h r)
            (append (take i' t) (drop i' t)) t (ih t)
      } } }
def take_drop_id_ty : Term := pure{
  Π (i : Nat) → Π (l : List Nat) → Id (List Nat) (append (take i l) (drop i l)) l }

/-! ## `nth`, `set`, `swapL` — the pure specification of swap (§16-2)

    Authored in the surface (dogfooding §15 — a first raw-de-Bruijn `set` had a
    `pvar 4`-vs-`pvar 3` slip; the surface version cannot slip). `swapL` mirrors
    the cursor walk: recurse past the prefix, then at `i = 0` exchange the head
    with position `j` of the tail (`Cons (nth j' xs) (set j' x xs)`). Reduces:
    `swapL 0 2 [1,2,3] = [3,2,1]`. `count_swapL` is the pending node — see the
    milestone report: it requires a BOUND (`swapL` off the end defaults `nth` to
    `Z`, breaking count preservation), so it decomposes into a bounded stack. -/

def nth : Term := pure{
  λ (k : Nat). elim k return (λ (z : Nat). List Nat → Nat) {
    Z => λ (l : List Nat). elim l return (λ (z : List Nat). Nat) { Nil => Z, Cons (h) (t) ihl => h },
    S (k') rec => λ (l : List Nat). elim l return (λ (z : List Nat). Nat) { Nil => Z, Cons (h) (t) ihl => rec t } } }

def set : Term := pure{
  λ (k : Nat). λ (v : Nat). elim k return (λ (z : Nat). List Nat → List Nat) {
    Z => λ (l : List Nat). elim l return (λ (z : List Nat). List Nat) { Nil => Nil, Cons (h) (t) ihl => Cons v t },
    S (k') rec => λ (l : List Nat). elim l return (λ (z : List Nat). List Nat) { Nil => Nil, Cons (h) (t) ihl => Cons h (rec t) } } }

def swapL : Term := pure{
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

def len_set : Term := pure{
  λ (k : Nat). λ (v : Nat).
    elim k return (λ (z : Nat). Π (l : List Nat) → Id Nat (len (set z v l)) (len l)) {
      Z => λ (l : List Nat). elim l return (λ (x : List Nat). Id Nat (len (set Z v x)) (len x)) {
        Nil => Refl, Cons (h) (t) ihl => Refl },
      S (k') ih => λ (l : List Nat). elim l return (λ (x : List Nat). Id Nat (len (set (S k') v x)) (len x)) {
        Nil => Refl,
        Cons (h) (t) ihl => id_congr Nat Nat (λ (n : Nat). S n) (len (set k' v t)) (len t) (ih t) } } }
def len_set_ty : Term := pure{ Π (k : Nat) → Π (v : Nat) → Π (l : List Nat) → Id Nat (len (set k v l)) (len l) }

def len_swapL : Term := pure{
  λ (i : Nat).
    elim i return (λ (z : Nat). Π (j : Nat) → Π (l : List Nat) → Id Nat (len (swapL z j l)) (len l)) {
      Z => λ (j : Nat). λ (l : List Nat).
        elim l return (λ (x : List Nat). Id Nat (len (swapL Z j x)) (len x)) {
          Nil => Refl,
          Cons (y) (ys) ihl => elim j return (λ (w : Nat). Id Nat (len (swapL Z w (Cons y ys))) (len (Cons y ys))) {
            Z => Refl,
            S (j') jih => id_congr Nat Nat (λ (n : Nat). S n) (len (set j' y ys)) (len ys) (len_set j' y ys) } },
      S (i') ih => λ (j : Nat). λ (l : List Nat).
        elim l return (λ (x : List Nat). Id Nat (len (swapL (S i') j x)) (len x)) {
          Nil => Refl,
          Cons (y) (ys) ihl => elim j return (λ (w : Nat). Id Nat (len (swapL (S i') w (Cons y ys))) (len (Cons y ys))) {
            Z => Refl,
            S (j') jih => id_congr Nat Nat (λ (n : Nat). S n) (len (swapL i' j' ys)) (len ys) (ih j' ys) } } } }
def len_swapL_ty : Term := pure{ Π (i : Nat) → Π (j : Nat) → Π (l : List Nat) → Id Nat (len (swapL i j l)) (len l) }

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

def cons2_comm : Term := pure{
  λ (m : Nat). λ (a : Nat). λ (b : Nat). λ (l : List Nat).
    elim (eqb m a) generalizing (Id Nat (count m (Cons a (Cons b l))) (count m (Cons b (Cons a l)))) {
      True => elim (eqb m b) generalizing
        (Id Nat (S (count m (Cons b l)))
                (boolRec (λ (w : Bool). Nat) (S (S (count m l))) (S (count m l)) (eqb m b))) {
        True => Refl, False => Refl },
      False => Refl } }
def cons2_comm_ty : Term := pure{
  Π (m : Nat) → Π (a : Nat) → Π (b : Nat) → Π (l : List Nat) →
    Id Nat (count m (Cons a (Cons b l))) (count m (Cons b (Cons a l))) }

-- Congruence of `count` under `Cons`: the `f` abstracts `count m ·` out of BOTH
-- occurrences in the `boolRec` that `count m (Cons h ·)` whnf's to, so a single
-- `id_congr` transports the tail equation through the head.
def count_cons_congr : Term := pure{
  λ (m : Nat). λ (h : Nat). λ (l1 : List Nat). λ (l2 : List Nat). λ (p : Id Nat (count m l1) (count m l2)).
    id_congr Nat Nat (λ (r : Nat). boolRec (λ (w : Bool). Nat) (S r) r (eqb m h)) (count m l1) (count m l2) p }
def count_cons_congr_ty : Term := pure{
  Π (m : Nat) → Π (h : Nat) → Π (l1 : List Nat) → Π (l2 : List Nat) →
    Id Nat (count m l1) (count m l2) → Id Nat (count m (Cons h l1)) (count m (Cons h l2)) }

-- The §18 rewrite-by-Id lemma, named: from a RECEIVED equation `eqb m a = True`,
-- resolve the STUCK `count m (Cons a l)` to `S (count m l)`. J transports `Refl`
-- along `id_sym hq`, the motive abstracting the scrutinee `z` out of the `boolRec`
-- that `count (Cons …)` unfolds to. Abstraction alone cannot do this (the subterm
-- hides behind the scrutinee's own reduction); this is the knowledge half. The
-- imperative tie-in returns THIS applied to its params.
def count_cons_hit : Term := pure{
  λ (m : Nat). λ (a : Nat). λ (l : List Nat). λ (hq : Id Bool (eqb m a) True).
    j Bool True
      (λ (z : Bool). λ (h : Id Bool True z).
        Id Nat (boolRec (λ (w : Bool). Nat) (S (count m l)) (count m l) z) (S (count m l)))
      Refl (eqb m a) (id_sym Bool (eqb m a) True hq) }
def count_cons_hit_ty : Term := pure{
  Π (m : Nat) → Π (a : Nat) → Π (l : List Nat) → Id Bool (eqb m a) True →
    Id Nat (count m (Cons a l)) (S (count m l)) }

-- Bounded head-swap: exchanging the head `x` with position `j` of the tail `xs`
-- preserves count, PROVIDED `j` is in range (`Le (S j) (len xs)`). Induction on
-- `j`, casing `xs`; the `Nil` leaves are ⊥-discharged by the bound (`Le (S _) Z`).
-- Base (`j = Z`): the swap is `Cons y (Cons x ys) ↔ Cons x (Cons y ys)`, exactly
-- `cons2_comm`. Step (`j = S j'`): a three-link `id_trans` chain — float the
-- swapped-in element past the head with `cons2_comm`, apply the IH under the head
-- via `count_cons_congr`, then `cons2_comm` back.
def count_headswap : Term := pure{
  λ (m : Nat). λ (x : Nat). λ (j : Nat).
    elim j return (λ (jz : Nat).
        Π (xs : List Nat) → Le (S jz) (len xs) →
          Id Nat (count m (Cons (nth jz xs) (set jz x xs))) (count m (Cons x xs))) {
      Z => λ (xs : List Nat).
        elim xs return (λ (xz : List Nat).
            Le (S Z) (len xz) →
              Id Nat (count m (Cons (nth Z xz) (set Z x xz))) (count m (Cons x xz))) {
          Nil => λ (bnd0 : Le (S Z) (len Nil)).
            botElim (Id Nat (count m (Cons (nth Z Nil) (set Z x Nil))) (count m (Cons x Nil))) bnd0,
          Cons (y) (ys) ihx => λ (bnd0 : Le (S Z) (len (Cons y ys))).
            cons2_comm m y x ys },
      S (j') ih => λ (xs : List Nat).
        elim xs return (λ (xz : List Nat).
            Le (S (S j')) (len xz) →
              Id Nat (count m (Cons (nth (S j') xz) (set (S j') x xz))) (count m (Cons x xz))) {
          Nil => λ (bnd0 : Le (S (S j')) (len Nil)).
            botElim (Id Nat (count m (Cons (nth (S j') Nil) (set (S j') x Nil))) (count m (Cons x Nil))) bnd0,
          Cons (y) (ys) ihx => λ (bnd0 : Le (S (S j')) (len (Cons y ys))).
            id_trans Nat
              (count m (Cons (nth j' ys) (Cons y (set j' x ys))))
              (count m (Cons y (Cons (nth j' ys) (set j' x ys))))
              (count m (Cons x (Cons y ys)))
              (cons2_comm m (nth j' ys) y (set j' x ys))
              (id_trans Nat
                (count m (Cons y (Cons (nth j' ys) (set j' x ys))))
                (count m (Cons y (Cons x ys)))
                (count m (Cons x (Cons y ys)))
                (count_cons_congr m y (Cons (nth j' ys) (set j' x ys)) (Cons x ys) (ih ys bnd0))
                (cons2_comm m y x ys)) } } }
def count_headswap_ty : Term := pure{
  Π (m : Nat) → Π (x : Nat) → Π (j : Nat) → Π (xs : List Nat) → Le (S j) (len xs) →
    Id Nat (count m (Cons (nth j xs) (set j x xs))) (count m (Cons x xs)) }

-- The top: `swapL i j` preserves count when both indices are in range. Induction
-- on `i`, casing `l` then `j`. The head case (`i = Z`, `j = S j'`) is exactly a
-- `count_headswap` (`swapL Z (S j') (Cons y ys) = Cons (nth j' ys) (set j' y ys)`);
-- the recursive case (`i = S i'`, `j = S j'`) rebuilds `Cons y (swapL i' j' ys)`,
-- discharged by `count_cons_congr` on the IH; the degenerate `j = Z` / `i > j`
-- cases are the identity swap (`Refl`); `Nil` is ⊥-discharged by `Le (S i) …`.
def count_swapL : Term := pure{
  λ (m : Nat). λ (i : Nat).
    elim i return (λ (iz : Nat).
        Π (j : Nat) → Π (l : List Nat) → Le (S iz) (len l) → Le (S j) (len l) →
          Id Nat (count m (swapL iz j l)) (count m l)) {
      Z => λ (j : Nat). λ (l : List Nat).
        elim l return (λ (lz : List Nat).
            Le (S Z) (len lz) → Le (S j) (len lz) → Id Nat (count m (swapL Z j lz)) (count m lz)) {
          Nil => λ (bi0 : Le (S Z) (len Nil)). λ (bj0 : Le (S j) (len Nil)).
            botElim (Id Nat (count m (swapL Z j Nil)) (count m Nil)) bi0,
          Cons (y) (ys) ihl => λ (bi0 : Le (S Z) (len (Cons y ys))). λ (bj0 : Le (S j) (len (Cons y ys))).
            elim j return (λ (jz : Nat).
                Le (S jz) (len (Cons y ys)) →
                  Id Nat (count m (swapL Z jz (Cons y ys))) (count m (Cons y ys))) {
              Z => λ (bj1 : Le (S Z) (len (Cons y ys))). Refl,
              S (j') jih => λ (bj1 : Le (S (S j')) (len (Cons y ys))).
                count_headswap m y j' ys bj1
            } bj0 },
      S (i') ih => λ (j : Nat). λ (l : List Nat).
        elim l return (λ (lz : List Nat).
            Le (S (S i')) (len lz) → Le (S j) (len lz) → Id Nat (count m (swapL (S i') j lz)) (count m lz)) {
          Nil => λ (bi0 : Le (S (S i')) (len Nil)). λ (bj0 : Le (S j) (len Nil)).
            botElim (Id Nat (count m (swapL (S i') j Nil)) (count m Nil)) bi0,
          Cons (y) (ys) ihl => λ (bi0 : Le (S (S i')) (len (Cons y ys))). λ (bj0 : Le (S j) (len (Cons y ys))).
            elim j return (λ (jz : Nat).
                Le (S jz) (len (Cons y ys)) →
                  Id Nat (count m (swapL (S i') jz (Cons y ys))) (count m (Cons y ys))) {
              Z => λ (bj1 : Le (S Z) (len (Cons y ys))). Refl,
              S (j') jih => λ (bj1 : Le (S (S j')) (len (Cons y ys))).
                count_cons_congr m y (swapL i' j' ys) ys (ih j' ys bi0 bj1)
            } bj0 } } }
def count_swapL_ty : Term := pure{
  Π (m : Nat) → Π (i : Nat) → Π (j : Nat) → Π (l : List Nat) →
    Le (S i) (len l) → Le (S j) (len l) → Id Nat (count m (swapL i j l)) (count m l) }

-- The friction-free corollary: count_swapL with swapS's telescope-mirrored
-- premises (`Le (S i) j`, `Le (S j) (len l)` — exactly the `pij`/`p2` a swapS
-- caller holds). The general count_swapL is the mathematically right statement
-- (independent bounds, no `i ≤ j` needed); this derives the caller's hand-off from
-- it. `Le (S i) (len l)` comes by `le_trans (S i) (S j) (len l)`: `le_up_r` lifts
-- `pij : Le (S i) j` to `Le (S i) (S j)`, then chain with `p2`.
def count_swapL' : Term := pure{
  λ (m : Nat). λ (i : Nat). λ (j : Nat). λ (l : List Nat).
    λ (pij : Le (S i) j). λ (p2 : Le (S j) (len l)).
      count_swapL m i j l (le_trans (S i) (S j) (len l) (le_up_r (S i) j pij) p2) p2 }
def count_swapL'_ty : Term := pure{
  Π (m : Nat) → Π (i : Nat) → Π (j : Nat) → Π (l : List Nat) →
    Le (S i) j → Le (S j) (len l) → Id Nat (count m (swapL i j l)) (count m l) }

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

def partScanL : Term := pure{
  λ (pivot : Nat). λ (k : Nat).
    elim k return (λ (kz : Nat). Π (i : Nat) → Π (g : Nat) → List Nat → List Nat) {
      Z => λ (i : Nat). λ (g : Nat). λ (l : List Nat).
        elim i return (λ (iz : Nat). List Nat) {
          Z => l,
          S (i') iih => swapL Z (S i') l },
      S (k') rec => λ (i : Nat). λ (g : Nat). λ (l : List Nat).
        elim (leb (nth (S (add i g)) l) pivot) return (λ (w : Bool). List Nat) {
          True => elim g return (λ (gz : Nat). List Nat) {
            Z => rec (S i) Z l,
            S (g') gih => rec (S i) (S g') (swapL (S i) (S (add i g)) l) },
          False => rec i (S g) l } } }

def partitionL : Term := pure{
  λ (n : Nat). λ (l : List Nat).
    elim n return (λ (nz : Nat). List Nat) {
      Z => l,
      S (n') rec => partScanL (nth Z l) n' Z Z l } }
def partitionL_ty : Term := pure{ Π (n : Nat) → List Nat → List Nat }

/-! ## `partScanIdxL` / `partIdxL` — the boundary INDEX the scan produces (§21)

    Mirror of partScanL's recursion but returning the boundary `i` (the pivot's
    final position) at `k = Z` instead of the placed list. This is the index the
    imperative partition returns transparently (a Σ pinning it to `partIdxL`), and
    the split point sortL's two recursive calls ride. Same casings/arithmetic as
    partScanL, so the two stay in lockstep. -/

def partScanIdxL : Term := pure{
  λ (pivot : Nat). λ (k : Nat).
    elim k return (λ (kz : Nat). Π (i : Nat) → Π (g : Nat) → List Nat → Nat) {
      Z => λ (i : Nat). λ (g : Nat). λ (l : List Nat). i,
      S (k') rec => λ (i : Nat). λ (g : Nat). λ (l : List Nat).
        elim (leb (nth (S (add i g)) l) pivot) return (λ (w : Bool). Nat) {
          True => elim g return (λ (gz : Nat). Nat) {
            Z => rec (S i) Z l,
            S (g') gih => rec (S i) (S g') (swapL (S i) (S (add i g)) l) },
          False => rec i (S g) l } } }

def partIdxL : Term := pure{
  λ (n : Nat). λ (l : List Nat).
    elim n return (λ (nz : Nat). Nat) {
      Z => Z,
      S (n') rec => partScanIdxL (nth Z l) n' Z Z l } }
def partIdxL_ty : Term := pure{ Π (n : Nat) → List Nat → Nat }

/-! ## `sortL` — the pure quicksort model (§21)

    Fuel-structural (natRec on `fuel`; the caller passes `fuel = n` at the top).
    Base: out of fuel, or a segment of length ≤ 1 (already sorted) → identity. Step
    (n ≥ 2): partition the segment (`p = partitionL n l`, pivot lands at `i =
    partIdxL n l`), then recursively sort the two sub-slices — the prefix `take i p`
    (length `i`) and the suffix `drop (S i) p` (length `len (drop (S i) p)`, which
    avoids Nat subtraction) — reassembling `sortedPrefix ++ [pivot] ++ sortedSuffix`.
    The imperative quicksort mirrors this exactly (partition returns the transparent
    `i`, both recursions ride it), so the conformance is conversion. -/

def sortL : Term := pure{
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
              append (rec i (take i p)) (Cons (nth i p) (rec (len (drop (S i) p)) (drop (S i) p)))
          } } } }
def sortL_ty : Term := pure{ Π (fuel : Nat) → Π (n : Nat) → List Nat → List Nat }

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

def partScanRangeL : Term := pure{
  λ (pivot : Nat). λ (lo : Nat). λ (k : Nat).
    elim k return (λ (kz : Nat). Π (i : Nat) → Π (g : Nat) → List Nat → List Nat) {
      Z => λ (i : Nat). λ (g : Nat). λ (l : List Nat).
        elim i return (λ (iz : Nat). List Nat) {
          Z => l,
          S (i') iih => swapL lo (add lo (S i')) l },
      S (k') rec => λ (i : Nat). λ (g : Nat). λ (l : List Nat).
        elim (leb (nth (add lo (S (add i g))) l) pivot) return (λ (w : Bool). List Nat) {
          True => elim g return (λ (gz : Nat). List Nat) {
            Z => rec (S i) Z l,
            S (g') gih => rec (S i) (S g') (swapL (add lo (S i)) (add lo (S (add i g))) l) },
          False => rec i (S g) l } } }

def partitionRangeL : Term := pure{
  λ (lo : Nat). λ (cnt : Nat). λ (l : List Nat).
    elim cnt return (λ (cz : Nat). List Nat) {
      Z => l,
      S (cnt') rec => partScanRangeL (nth lo l) lo cnt' Z Z l } }

def partScanIdxRangeL : Term := pure{
  λ (pivot : Nat). λ (lo : Nat). λ (k : Nat).
    elim k return (λ (kz : Nat). Π (i : Nat) → Π (g : Nat) → List Nat → Nat) {
      Z => λ (i : Nat). λ (g : Nat). λ (l : List Nat). i,
      S (k') rec => λ (i : Nat). λ (g : Nat). λ (l : List Nat).
        elim (leb (nth (add lo (S (add i g))) l) pivot) return (λ (w : Bool). Nat) {
          True => elim g return (λ (gz : Nat). Nat) {
            Z => rec (S i) Z l,
            S (g') gih => rec (S i) (S g') (swapL (add lo (S i)) (add lo (S (add i g))) l) },
          False => rec i (S g) l } } }

def partIdxRangeL : Term := pure{
  λ (lo : Nat). λ (cnt : Nat). λ (l : List Nat).
    elim cnt return (λ (cz : Nat). Nat) {
      Z => Z,
      S (cnt') rec => partScanIdxRangeL (nth lo l) lo cnt' Z Z l } }

def partScanGapRangeL : Term := pure{
  λ (pivot : Nat). λ (lo : Nat). λ (k : Nat).
    elim k return (λ (kz : Nat). Π (i : Nat) → Π (g : Nat) → List Nat → Nat) {
      Z => λ (i : Nat). λ (g : Nat). λ (l : List Nat). g,
      S (k') rec => λ (i : Nat). λ (g : Nat). λ (l : List Nat).
        elim (leb (nth (add lo (S (add i g))) l) pivot) return (λ (w : Bool). Nat) {
          True => elim g return (λ (gz : Nat). Nat) {
            Z => rec (S i) Z l,
            S (g') gih => rec (S i) (S g') (swapL (add lo (S i)) (add lo (S (add i g))) l) },
          False => rec i (S g) l } } }

def partGapRangeL : Term := pure{
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
def partScanSizeL : Term := pure{
  λ (pivot : Nat). λ (lo : Nat). λ (k : Nat).
    elim k return (λ (kz : Nat). Π (i : Nat) → Π (g : Nat) → Π (l : List Nat) →
        Id Nat (add (partScanIdxRangeL pivot lo kz i g l) (partScanGapRangeL pivot lo kz i g l)) (add kz (add i g))) {
      Z => λ (i : Nat). λ (g : Nat). λ (l : List Nat). Refl,
      S (k') ih => λ (i : Nat). λ (g : Nat). λ (l : List Nat).
        elim (leb (nth (add lo (S (add i g))) l) pivot)
          return (λ (w : Bool). Id Nat
            (add (elim w return (λ (ww : Bool). Nat) {
                    True => elim g return (λ (gz : Nat). Nat) {
                      Z => partScanIdxRangeL pivot lo k' (S i) Z l,
                      S (g') gih => partScanIdxRangeL pivot lo k' (S i) (S g') (swapL (add lo (S i)) (add lo (S (add i g))) l) },
                    False => partScanIdxRangeL pivot lo k' i (S g) l })
                 (elim w return (λ (ww : Bool). Nat) {
                    True => elim g return (λ (gz : Nat). Nat) {
                      Z => partScanGapRangeL pivot lo k' (S i) Z l,
                      S (g') gih => partScanGapRangeL pivot lo k' (S i) (S g') (swapL (add lo (S i)) (add lo (S (add i g))) l) },
                    False => partScanGapRangeL pivot lo k' i (S g) l }))
            (add (S k') (add i g))) {
          True => elim g return (λ (gz : Nat). Id Nat
                    (add (elim gz return (λ (gy : Nat). Nat) {
                            Z => partScanIdxRangeL pivot lo k' (S i) Z l,
                            S (g') gih => partScanIdxRangeL pivot lo k' (S i) (S g') (swapL (add lo (S i)) (add lo (S (add i g))) l) })
                         (elim gz return (λ (gy : Nat). Nat) {
                            Z => partScanGapRangeL pivot lo k' (S i) Z l,
                            S (g') gih => partScanGapRangeL pivot lo k' (S i) (S g') (swapL (add lo (S i)) (add lo (S (add i g))) l) }))
                    (add (S k') (add i gz))) {
            Z => id_trans Nat
                   (add (partScanIdxRangeL pivot lo k' (S i) Z l) (partScanGapRangeL pivot lo k' (S i) Z l))
                   (add k' (add (S i) Z))
                   (add (S k') (add i Z))
                   (ih (S i) Z l)
                   (id_sym Nat (add (S k') (add i Z)) (add k' (add (S i) Z)) (hshift_true k' i Z)),
            S (g') gih => id_trans Nat
                   (add (partScanIdxRangeL pivot lo k' (S i) (S g') (swapL (add lo (S i)) (add lo (S (add i g))) l)) (partScanGapRangeL pivot lo k' (S i) (S g') (swapL (add lo (S i)) (add lo (S (add i g))) l)))
                   (add k' (add (S i) (S g')))
                   (add (S k') (add i (S g')))
                   (ih (S i) (S g') (swapL (add lo (S i)) (add lo (S (add i g))) l))
                   (id_sym Nat (add (S k') (add i (S g'))) (add k' (add (S i) (S g'))) (hshift_true k' i (S g')))
          },
          False => id_trans Nat
                     (add (partScanIdxRangeL pivot lo k' i (S g) l) (partScanGapRangeL pivot lo k' i (S g) l))
                     (add k' (add i (S g)))
                     (add (S k') (add i g))
                     (ih i (S g) l)
                     (id_sym Nat (add (S k') (add i g)) (add k' (add i (S g))) (hshift_false k' i g))
        }
    } }
def partScanSizeL_ty : Term := pure{ Π (pivot : Nat) → Π (lo : Nat) → Π (k : Nat) → Π (i : Nat) → Π (g : Nat) → Π (l : List Nat) →
  Id Nat (add (partScanIdxRangeL pivot lo k i g l) (partScanGapRangeL pivot lo k i g l)) (add k (add i g)) }

-- The range scan preserves length — it only ever rebuilds the same spine (swapL,
-- which len_swapL knows preserves length) or leaves it. Same induction shape as
-- partScanSizeL (on k, elim the leb Bool, elim g in True), but the leaves are
-- simpler: each recursive step is the IH, and the two swapL cases (Z-base pivot
-- placement, True/S-g swap) bridge through len_swapL. The quicksort recursion
-- needs this because partitionRange MUTATES *v, and the two recursive-call range
-- bounds refer to len (*v-after-partition) — this moves them back onto len (entry).
def len_partScanRangeL : Term := pure{
  λ (pivot : Nat). λ (lo : Nat). λ (k : Nat).
    elim k return (λ (kz : Nat). Π (i : Nat) → Π (g : Nat) → Π (l : List Nat) →
        Id Nat (len (partScanRangeL pivot lo kz i g l)) (len l)) {
      Z => λ (i : Nat). λ (g : Nat). λ (l : List Nat).
        elim i return (λ (iz : Nat). Id Nat
            (len (elim iz return (λ (iy : Nat). List Nat) { Z => l, S (i') iih => swapL lo (add lo (S i')) l }))
            (len l)) {
          Z => Refl,
          S (i') iih => len_swapL lo (add lo (S i')) l },
      S (k') ih => λ (i : Nat). λ (g : Nat). λ (l : List Nat).
        elim (leb (nth (add lo (S (add i g))) l) pivot)
          return (λ (w : Bool). Id Nat
            (len (elim w return (λ (ww : Bool). List Nat) {
                    True => elim g return (λ (gz : Nat). List Nat) {
                      Z => partScanRangeL pivot lo k' (S i) Z l,
                      S (g') gih => partScanRangeL pivot lo k' (S i) (S g') (swapL (add lo (S i)) (add lo (S (add i g))) l) },
                    False => partScanRangeL pivot lo k' i (S g) l }))
            (len l)) {
          True => elim g return (λ (gz : Nat). Id Nat
                    (len (elim gz return (λ (gy : Nat). List Nat) {
                            Z => partScanRangeL pivot lo k' (S i) Z l,
                            S (g') gih => partScanRangeL pivot lo k' (S i) (S g') (swapL (add lo (S i)) (add lo (S (add i g))) l) }))
                    (len l)) {
            Z => ih (S i) Z l,
            S (g') gih => id_trans Nat
                   (len (partScanRangeL pivot lo k' (S i) (S g') (swapL (add lo (S i)) (add lo (S (add i g))) l)))
                   (len (swapL (add lo (S i)) (add lo (S (add i g))) l))
                   (len l)
                   (ih (S i) (S g') (swapL (add lo (S i)) (add lo (S (add i g))) l))
                   (len_swapL (add lo (S i)) (add lo (S (add i g))) l)
          },
          False => ih i (S g) l
        }
    } }
def len_partScanRangeL_ty : Term := pure{ Π (pivot : Nat) → Π (lo : Nat) → Π (k : Nat) → Π (i : Nat) → Π (g : Nat) → Π (l : List Nat) →
  Id Nat (len (partScanRangeL pivot lo k i g l)) (len l) }

-- The wrapper form the quicksort recursion consumes: partitionRangeL is
-- partScanRangeL after picking the pivot, so its length preservation is the scan's
-- (Z base is Refl, S cnt' is len_partScanRangeL at the entry offsets).
def len_partitionRangeL : Term := pure{
  λ (lo : Nat). λ (cnt : Nat). λ (l : List Nat).
    elim cnt return (λ (cz : Nat). Id Nat
        (len (elim cz return (λ (cy : Nat). List Nat) { Z => l, S (cnt') rec => partScanRangeL (nth lo l) lo cnt' Z Z l }))
        (len l)) {
      Z => Refl,
      S (cnt') rec => len_partScanRangeL (nth lo l) lo cnt' Z Z l } }
def len_partitionRangeL_ty : Term := pure{ Π (lo : Nat) → Π (cnt : Nat) → Π (l : List Nat) → Id Nat (len (partitionRangeL lo cnt l)) (len l) }

/-- `sortRangeL fuel lo cnt l` — sort the `cnt` elements of `l` at offset `lo` in
    place. Fuel-structural; base = out of fuel or `cnt ≤ 1`; step partitions the
    range, then sorts the left sub-range `[lo, lo+i)` (count `i`) and the right
    `[lo+i+1, …)` (count `g`), the right on the result of the left — the raw
    composition the imperative body implements. `partitionQ` is the `lo = 0` slice. -/
def sortRangeL : Term := pure{
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
              rec (S (add lo i)) g (rec lo i p)
          } } } }
def sortRangeL_ty : Term := pure{ Π (fuel : Nat) → Π (lo : Nat) → Π (cnt : Nat) → List Nat → List Nat }

end Dllbc.StdLemmas

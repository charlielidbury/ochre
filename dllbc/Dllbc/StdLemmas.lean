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

end Dllbc.StdLemmas

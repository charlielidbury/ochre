import Pss.Syntax.Term
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.SDiff
import Mathlib.Data.Fintype.Card

/-! # `Pss.Syntax.LocallyNameless` — opening, closing, substitution and `LC`

Standard locally-nameless infrastructure following

  Aydemir, Charguéraud, Pierce, Pollack, Weirich,
  *Engineering Formal Metatheory*, POPL 2008.

All operations and the local-closure predicate `LC` use cofinite quantification
in the binder case, which gives the right induction principle for free.

The lemma names below are *load-bearing* — downstream waves cite them by these
exact names. See `PLAN.md` §3 / Risk 1.
-/

namespace Pss

/-! ## Free variables -/

/-- Free (string-named) variables of a term. -/
def Term.fv : Term → Finset String
  | .bvar _    => ∅
  | .fvar x    => {x}
  | .top       => ∅
  | .abs t u   => Term.fv t ∪ Term.fv u
  | .app t u   => Term.fv t ∪ Term.fv u

/-! ## Syntactic size

The conventional locally-nameless syntactic size: counts AST nodes,
counting `bvar`/`fvar`/`top` as leaves of size 1, and `abs`/`app` as
internal nodes whose size is `1 +` the recursive sums.

**Why this matters (iter-4 / iter-5 plan).** The Lemma 2 / Lemma 1
diamond proofs need a derivation-WF measure that lets the body
sub-derivations of cofinite-quantified `MEqRed` constructors count as
"strictly smaller" than the parent. The naïve `derSize` measure
(see `Pss.Mpss.MEqRedSize`) samples the body at `pickFresh L`, which
is NOT y-invariant — so an arbitrary-y body-decrease lemma is not
provable without the renaming functor (see Diamond.lean §3.2 iter-4
docstring on `Lemma_2_DiamondMEqRed_core`).

`Term.size` is **y-invariant under opening**: opening a body with
`.fvar y` does not change syntactic size (Term.size_open_fvar below).
This makes `Term.size t₀` a viable WF measure for the cofinite-arm
body recursion in Lemma 2 / Lemma 1, modulo handling the `pro` arm
(whose lookup-α may be arbitrarily large) via a lex with the
context's syntactic size. -/
def Term.size : Term → Nat
  | .bvar _    => 1
  | .fvar _    => 1
  | .top       => 1
  | .abs t u   => 1 + Term.size t + Term.size u
  | .app t u   => 1 + Term.size t + Term.size u

/-! ## Opening: replace `bvar k` with `u` -/

/-- `Term.open_ k u e` substitutes the bound variable `bvar k` in `e` with `u`,
incrementing `k` under each binder. -/
def Term.open_ (k : Nat) (u : Term) : Term → Term
  | .bvar i    => if i = k then u else .bvar i
  | .fvar x    => .fvar x
  | .top       => .top
  | .abs t b   => .abs (Term.open_ k u t) (Term.open_ (k + 1) u b)
  | .app t s   => .app (Term.open_ k u t) (Term.open_ k u s)

/-- "Open the body" — replace the outermost bound variable. The standard entry
point: `e^[x]` opens `e` with `fvar x`. -/
def Term.opening (u : Term) : Term → Term := Term.open_ 0 u

/-! ## Closing: turn a free variable into `bvar k` -/

/-- `Term.close_ k x e` is the inverse of opening: it abstracts free variable
`x` in `e` to `bvar k`. -/
def Term.close_ (k : Nat) (x : String) : Term → Term
  | .bvar i    => .bvar i
  | .fvar y    => if y = x then .bvar k else .fvar y
  | .top       => .top
  | .abs t b   => .abs (Term.close_ k x t) (Term.close_ (k + 1) x b)
  | .app t s   => .app (Term.close_ k x t) (Term.close_ k x s)

/-! ## Substitution of free variables -/

/-- `Term.subst x u e` substitutes `u` for every free occurrence of `fvar x`
in `e`. Bound-variable indices are not touched (no shifting needed: `u` lives
"outside" any binder we descend through, but we *do* need `LC u` for the
substitution-and-opening lemma). -/
def Term.subst (x : String) (u : Term) : Term → Term
  | .bvar i    => .bvar i
  | .fvar y    => if y = x then u else .fvar y
  | .top       => .top
  | .abs t b   => .abs (Term.subst x u t) (Term.subst x u b)
  | .app t s   => .app (Term.subst x u t) (Term.subst x u s)

/-! ## Local closure -/

/-- A term is *locally closed* if every bound variable is bound by some
enclosing `abs`. The binder case uses cofinite quantification (Aydemir et al.).

**Lifted to `Type`** (post-Type-LC refactor): this enables `MEqRed.refl`
to be defined by direct structural recursion on `LC`, eliminating the
`Classical.choice` opacity that blocked discharge of the β-residual
axioms. See `PLAN.md` discharge-campaign Option B. -/
inductive Term.LC : Term → Type
  | top  : Term.LC .top
  | fvar (x : String) : Term.LC (.fvar x)
  | app {u v : Term} : Term.LC u → Term.LC v → Term.LC (.app u v)
  | abs (L : Finset String) {bound body : Term} :
      Term.LC bound →
      (∀ x, x ∉ L → Term.LC (Term.opening (.fvar x) body)) →
      Term.LC (.abs bound body)

/-- `e^[x]` opens `e` with the free variable named `x`. -/
notation:max e "^[" x "]" => Term.opening (Term.fvar x) e

/-! ## Picking a fresh name -/

/-- Existence of a fresh name (using Mathlib's infinite-string fact). -/
lemma Term.exists_fresh (s : Finset String) : ∃ x : String, x ∉ s := by
  classical
  exact Infinite.exists_not_mem_finset s

/-! ## Free-variable simp lemmas -/

@[simp] lemma Term.fv_bvar (i : Nat) : Term.fv (.bvar i) = ∅ := rfl
@[simp] lemma Term.fv_fvar (x : String) : Term.fv (.fvar x) = {x} := rfl
@[simp] lemma Term.fv_top : Term.fv .top = ∅ := rfl
@[simp] lemma Term.fv_abs (t b : Term) :
    Term.fv (.abs t b) = Term.fv t ∪ Term.fv b := rfl
@[simp] lemma Term.fv_app (t u : Term) :
    Term.fv (.app t u) = Term.fv t ∪ Term.fv u := rfl

/-! ## Size simp lemmas -/

@[simp] lemma Term.size_bvar (i : Nat) : Term.size (.bvar i) = 1 := rfl
@[simp] lemma Term.size_fvar (x : String) : Term.size (.fvar x) = 1 := rfl
@[simp] lemma Term.size_top : Term.size .top = 1 := rfl
@[simp] lemma Term.size_abs (t b : Term) :
    Term.size (.abs t b) = 1 + Term.size t + Term.size b := rfl
@[simp] lemma Term.size_app (t u : Term) :
    Term.size (.app t u) = 1 + Term.size t + Term.size u := rfl

/-! ## Size under opening — the y-invariance load-bearing for path (A) -/

/-- Opening with a free variable preserves syntactic size: `Term.size
(open_ k (.fvar x) e) = Term.size e`. The free-variable substituent has
size 1 (a leaf), so the bvar→fvar swap is size-neutral. -/
theorem Term.size_open_fvar (k : Nat) (x : String) (e : Term) :
    Term.size (Term.open_ k (Term.fvar x) e) = Term.size e := by
  induction e generalizing k with
  | bvar i =>
    by_cases h : i = k
    · simp [Term.open_, h, Term.size]
    · simp [Term.open_, h, Term.size]
  | fvar y => simp [Term.open_, Term.size]
  | top => simp [Term.open_, Term.size]
  | abs t b iht ihb =>
    simp [Term.open_, Term.size, iht, ihb]
  | app t u iht ihu =>
    simp [Term.open_, Term.size, iht, ihu]

/-- Specialization to `Term.opening` (= `open_ 0`): `^[x]` preserves
size. -/
theorem Term.size_opening_fvar (x : String) (e : Term) :
    Term.size (e^[x]) = Term.size e :=
  Term.size_open_fvar 0 x e

/-! ## fv under operations -/

/-- **fv_open_subset**: `fv (open_ k u e) ⊆ fv e ∪ fv u`. -/
theorem Term.fv_open_subset (k : Nat) (u e : Term) :
    Term.fv (Term.open_ k u e) ⊆ Term.fv e ∪ Term.fv u := by
  induction e generalizing k with
  | bvar i =>
    by_cases h : i = k
    · simp [Term.open_, h]
    · simp [Term.open_, h]
  | fvar x => simp [Term.open_]
  | top => simp [Term.open_]
  | abs t b iht ihb =>
    intro y hy
    simp [Term.open_, Term.fv] at hy
    rcases hy with hy | hy
    · have := iht k hy
      rcases Finset.mem_union.mp this with h | h
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl h)))
      · exact Finset.mem_union.mpr (Or.inr h)
    · have := ihb (k+1) hy
      rcases Finset.mem_union.mp this with h | h
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr h)))
      · exact Finset.mem_union.mpr (Or.inr h)
  | app t s iht ihs =>
    intro y hy
    simp [Term.open_, Term.fv] at hy
    rcases hy with hy | hy
    · have := iht k hy
      rcases Finset.mem_union.mp this with h | h
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl h)))
      · exact Finset.mem_union.mpr (Or.inr h)
    · have := ihs k hy
      rcases Finset.mem_union.mp this with h | h
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr h)))
      · exact Finset.mem_union.mpr (Or.inr h)

/-- **fv_subst_subset**: `fv (subst x u e) ⊆ (fv e \ {x}) ∪ fv u`. -/
theorem Term.fv_subst_subset (x : String) (u e : Term) :
    Term.fv (Term.subst x u e) ⊆ (Term.fv e \ {x}) ∪ Term.fv u := by
  induction e with
  | bvar i => simp [Term.subst, Term.fv]
  | fvar y =>
    by_cases h : y = x
    · simp [Term.subst, h]
    · intro z hz
      simp [Term.subst, h, Term.fv] at hz
      subst hz
      apply Finset.mem_union.mpr; left
      apply Finset.mem_sdiff.mpr
      refine ⟨by simp, ?_⟩
      simp
      exact h
  | top => simp [Term.subst, Term.fv]
  | abs t b iht ihb =>
    intro z hz
    simp [Term.subst, Term.fv] at hz
    rcases hz with hz | hz
    · have := iht hz
      rcases Finset.mem_union.mp this with h | h
      · rcases Finset.mem_sdiff.mp h with ⟨h1, h2⟩
        exact Finset.mem_union.mpr (Or.inl (Finset.mem_sdiff.mpr ⟨Finset.mem_union.mpr (Or.inl h1), h2⟩))
      · exact Finset.mem_union.mpr (Or.inr h)
    · have := ihb hz
      rcases Finset.mem_union.mp this with h | h
      · rcases Finset.mem_sdiff.mp h with ⟨h1, h2⟩
        exact Finset.mem_union.mpr (Or.inl (Finset.mem_sdiff.mpr ⟨Finset.mem_union.mpr (Or.inr h1), h2⟩))
      · exact Finset.mem_union.mpr (Or.inr h)
  | app t s iht ihs =>
    intro z hz
    simp [Term.subst, Term.fv] at hz
    rcases hz with hz | hz
    · have := iht hz
      rcases Finset.mem_union.mp this with h | h
      · rcases Finset.mem_sdiff.mp h with ⟨h1, h2⟩
        exact Finset.mem_union.mpr (Or.inl (Finset.mem_sdiff.mpr ⟨Finset.mem_union.mpr (Or.inl h1), h2⟩))
      · exact Finset.mem_union.mpr (Or.inr h)
    · have := ihs hz
      rcases Finset.mem_union.mp this with h | h
      · rcases Finset.mem_sdiff.mp h with ⟨h1, h2⟩
        exact Finset.mem_union.mpr (Or.inl (Finset.mem_sdiff.mpr ⟨Finset.mem_union.mpr (Or.inr h1), h2⟩))
      · exact Finset.mem_union.mpr (Or.inr h)

/-! ## Opening at distinct levels: the swap lemma. -/

/-- **open_open_core** (Aydemir's `open_rec_term_core`): the workhorse lemma
for proving `open_lc`. If opening `e` at level `j` with `v` is invariant under
opening at level `i ≠ j` with `u`, then `e` itself is invariant under
opening at level `i` with `u`. -/
lemma Term.open_open_core (e : Term) :
    ∀ (i j : Nat) (u v : Term), i ≠ j →
      Term.open_ j v e = Term.open_ i u (Term.open_ j v e) →
      e = Term.open_ i u e := by
  induction e with
  | bvar k =>
    intro i j u v hij h
    by_cases hki : k = i
    · subst hki
      have hkj : k ≠ j := hij
      simp [Term.open_, hkj] at h
      simp [Term.open_]
      exact h
    · simp [Term.open_, hki]
  | fvar x => intro _ _ _ _ _ _; simp [Term.open_]
  | top    => intro _ _ _ _ _ _; simp [Term.open_]
  | abs t b iht ihb =>
    intro i j u v hij h
    simp [Term.open_, Term.abs.injEq] at h
    obtain ⟨h1, h2⟩ := h
    have ht := iht i j u v hij h1
    have hb := ihb (i+1) (j+1) u v (by intro hh; apply hij; omega) h2
    simp [Term.open_]
    exact ⟨ht, hb⟩
  | app t s iht ihs =>
    intro i j u v hij h
    simp [Term.open_, Term.app.injEq] at h
    obtain ⟨h1, h2⟩ := h
    have ht := iht i j u v hij h1
    have hs := ihs i j u v hij h2
    simp [Term.open_]
    exact ⟨ht, hs⟩

/-! ## `open_lc` -/

/-- **open_lc**: opening a locally-closed term is a no-op. -/
theorem Term.open_lc {e : Term} (he : Term.LC e) :
    ∀ (k : Nat) (u : Term), Term.open_ k u e = e := by
  induction he with
  | top => intro _ _; rfl
  | fvar _ => intro _ _; rfl
  | app _ _ ihu ihv =>
    intro k u
    simp [Term.open_, ihu, ihv]
  | @abs L bound body _ _ iht ihb =>
    intro k u
    classical
    obtain ⟨x, hx⟩ := Term.exists_fresh L
    -- ihb x hx : ∀ k' u', open_ k' u' (body^[x]) = body^[x]
    have hbx : Term.open_ (k+1) u (Term.open_ 0 (.fvar x) body) = Term.open_ 0 (.fvar x) body :=
      ihb x hx (k+1) u
    -- Apply open_open_core with i = k+1, j = 0, v = fvar x.
    have hswap : body = Term.open_ (k+1) u body :=
      Term.open_open_core body (k+1) 0 u (.fvar x)
        (by intro h; cases h)
        hbx.symm
    simp [Term.open_, iht]
    exact hswap.symm

/-- **opening_lc** corollary. -/
theorem Term.opening_lc {e : Term} (he : Term.LC e) (u : Term) :
    Term.opening u e = e := Term.open_lc he 0 u

/-! ## `subst_fresh` -/

/-- **subst_fresh**: substituting a variable not in `fv e` is a no-op. -/
theorem Term.subst_fresh {x : String} {u e : Term} (hx : x ∉ Term.fv e) :
    Term.subst x u e = e := by
  induction e with
  | bvar i => rfl
  | fvar y =>
    simp [Term.fv] at hx
    simp [Term.subst, Ne.symm hx]
  | top => rfl
  | abs t b iht ihb =>
    simp [Term.fv] at hx
    simp [Term.subst, iht hx.1, ihb hx.2]
  | app t s iht ihs =>
    simp [Term.fv] at hx
    simp [Term.subst, iht hx.1, ihs hx.2]

/-! ## `subst_open` and friends -/

/-- **subst_open**: substitution distributes over opening, given `LC u`. -/
theorem Term.subst_open {x : String} {u : Term} (hu : Term.LC u)
    (k : Nat) (v e : Term) :
    Term.subst x u (Term.open_ k v e)
      = Term.open_ k (Term.subst x u v) (Term.subst x u e) := by
  induction e generalizing k with
  | bvar i =>
    by_cases h : i = k
    · simp [Term.open_, h, Term.subst]
    · simp [Term.open_, h, Term.subst]
  | fvar y =>
    by_cases h : y = x
    · subst h
      simp [Term.subst, Term.open_]
      exact (Term.open_lc hu k _).symm
    · simp [Term.subst, h, Term.open_]
  | top => simp [Term.subst, Term.open_]
  | abs t b iht ihb =>
    simp [Term.subst, Term.open_, iht, ihb]
  | app t s iht ihs =>
    simp [Term.subst, Term.open_, iht, ihs]

/-- **subst_open_var**: special case of `subst_open` for opening with a fresh
variable. -/
theorem Term.subst_open_var {x y : String} {u : Term}
    (hxy : x ≠ y) (hu : Term.LC u) (e : Term) :
    Term.subst x u (e^[y]) = (Term.subst x u e)^[y] := by
  unfold Term.opening
  rw [Term.subst_open hu]
  congr 1
  simp [Term.subst, Ne.symm hxy]

/-- **subst_intro**: opening with `u` factors through opening with a fresh `x`
followed by substitution. -/
theorem Term.subst_intro {x : String} {u e : Term} (hx : x ∉ Term.fv e)
    (hu : Term.LC u) :
    Term.opening u e = Term.subst x u (e^[x]) := by
  unfold Term.opening
  rw [Term.subst_open hu]
  rw [Term.subst_fresh hx]
  simp [Term.subst]

/-! ## `subst_lc` — needs the cofinite trick. -/

/-- **subst_lc**: substituting a locally-closed term preserves local closure.

`Type`-valued (since `Term.LC : Type`); use `noncomputable def` because
the recursion uses `LC` constructors that the code generator does not
synthesize for `Type`-valued inductives by default. -/
noncomputable def Term.subst_lc {x : String} {u e : Term}
    (hu : Term.LC u) (he : Term.LC e) :
    Term.LC (Term.subst x u e) := by
  induction he with
  | top => exact Term.LC.top
  | fvar y =>
    by_cases h : y = x
    · simp [Term.subst, h]; exact hu
    · simp [Term.subst, h]; exact Term.LC.fvar y
  | app _ _ iht ihs =>
    exact Term.LC.app iht ihs
  | @abs L bound body _ _ iht ihb =>
    refine Term.LC.abs (L ∪ {x} ∪ Term.fv u) iht ?_
    intro y hy
    have hyL : y ∉ L := fun h => hy (by
      apply Finset.mem_union.mpr; left
      apply Finset.mem_union.mpr; left
      exact h)
    have hyx : y ≠ x := fun h => hy (by
      apply Finset.mem_union.mpr; left
      apply Finset.mem_union.mpr; right
      simp [h])
    have hxy : x ≠ y := Ne.symm hyx
    have key : (Term.subst x u body)^[y] = Term.subst x u (body^[y]) :=
      (Term.subst_open_var hxy hu body).symm
    rw [key]
    exact ihb y hyL

/-! ## `lc_opening_intro` -/

/-- Restated `LC.abs`: a `λ-abs` is locally closed when its bound annotation is
LC and its body opens to LC for cofinitely many names.

`Type`-valued (since `Term.LC : Type`); use `def` rather than `theorem`. -/
def Term.lc_opening_intro (L : Finset String) {bound body : Term}
    (hb : Term.LC bound)
    (hbody : ∀ x, x ∉ L → Term.LC (body^[x])) :
    Term.LC (.abs bound body) :=
  Term.LC.abs L hb hbody

/-! ## Round-trip: `close_open` -/

/-- **close_open**: closing then re-opening (with the same name) is the
identity, provided the variable is fresh. -/
theorem Term.close_open (k : Nat) (x : String) (e : Term)
    (hx : x ∉ Term.fv e) :
    Term.close_ k x (Term.open_ k (.fvar x) e) = e := by
  induction e generalizing k with
  | bvar i =>
    by_cases h : i = k
    · simp [Term.open_, h, Term.close_]
    · simp [Term.open_, h, Term.close_]
  | fvar y =>
    simp [Term.fv] at hx
    simp [Term.open_, Term.close_, Ne.symm hx]
  | top => simp [Term.open_, Term.close_]
  | abs t b iht ihb =>
    simp [Term.fv] at hx
    simp [Term.open_, Term.close_, iht k hx.1, ihb (k+1) hx.2]
  | app t s iht ihs =>
    simp [Term.fv] at hx
    simp [Term.open_, Term.close_, iht k hx.1, ihs k hx.2]

/-! ## Round-trip: `open_close`

We use the structural variant `open_close_struct`: for ANY term `e` (not just
LC), the equation `open_ k (.fvar x) (close_ k x e) = e` holds whenever `e`
"already has no `bvar k`". For LC terms this side condition is satisfied
inductively for the body using cofinite quantification.

Rather than develop full no-`bvar k` machinery, we state the direct result
under `LC e`. -/

/-- Helper: a structural lemma about `close_` followed by `open_` at level `k`,
where the side condition is that `e` has no free `bvar k`. -/
private lemma Term.open_close_aux (e : Term) :
    ∀ (k : Nat) (x : String),
      Term.open_ k (.fvar x) e = e →
      Term.open_ k (.fvar x) (Term.close_ k x e) = e := by
  induction e with
  | bvar i =>
    intro k x h
    by_cases hik : i = k
    · subst hik
      -- h : open_ i (fvar x) (bvar i) = bvar i, i.e. fvar x = bvar i — contradiction.
      simp [Term.open_] at h
    · simp [Term.close_, Term.open_, hik]
  | fvar y =>
    intro k x _
    by_cases h : y = x
    · simp [Term.close_, h, Term.open_]
    · simp [Term.close_, h, Term.open_]
  | top => intro k x _; simp [Term.close_, Term.open_]
  | abs t b iht ihb =>
    intro k x h
    simp [Term.open_, Term.abs.injEq] at h
    obtain ⟨h1, h2⟩ := h
    simp [Term.close_, Term.open_, iht k x h1, ihb (k+1) x h2]
  | app t s iht ihs =>
    intro k x h
    simp [Term.open_, Term.app.injEq] at h
    obtain ⟨h1, h2⟩ := h
    simp [Term.close_, Term.open_, iht k x h1, ihs k x h2]

/-- **open_close**: opening (with `fvar x`) a closed-on-`x` LC term recovers
the original. Aydemir-style; uses `open_lc` to discharge the side condition. -/
theorem Term.open_close {e : Term} (he : Term.LC e) (k : Nat) (x : String) :
    Term.open_ k (.fvar x) (Term.close_ k x e) = e :=
  Term.open_close_aux e k x (Term.open_lc he k _)

/-! ## §`openInverse` — Phase 1 of Lever A (iter-31)

`Term.openInverse y target_open` recovers a "closed" form: it replaces every
free occurrence of `y` in `target_open` with `bvar k` at the matching
binding depth `k` (initial `k = 0`). This is the inverse of opening: when
`target_open = target^[y]` for some `y`-fresh `target`, `openInverse y` gives
back `target`.

Operationally, `openInverse y t = Term.close_ 0 y t` — i.e. it is exactly the
existing close operation specialised at level 0. The dedicated alias and
lemma names are introduced for the consumer-facing API in
`Pss/Mpss/Renaming.lean §13` (Lever A, open-target descent), where the call
site reads more naturally as `Term.openInverse y target` than as
`Term.close_ 0 y target`.

This is the **prerequisite** for the iter-32+ `MEqRed.openInverse_descend`
construction that lifts a body-diamond's join target back into a y-fresh
form, unblocking the consumer-side reconstruction of cofinite hypotheses
for `MEqRed.bet`'s body slot. See `Pss/Mpss/Renaming.lean §13` for the
sharpened plan.
-/

/-- **openInverseAt**: the level-indexed inverse of opening. Replaces each
`fvar y` with `bvar k` at the matching binding depth, leaves `bvar` and
other `fvar`s alone. Identical to `Term.close_ k y`; provided as a named
alias for the Lever A / open-target descent API. -/
def Term.openInverseAt (y : String) (k : Nat) : Term → Term := Term.close_ k y

/-- **openInverse**: top-level entry point — `openInverseAt y 0`. The function
the consumer in `Renaming.lean §13` will call. -/
def Term.openInverse (y : String) : Term → Term := Term.openInverseAt y 0

@[simp] lemma Term.openInverseAt_def (y : String) (k : Nat) (e : Term) :
    Term.openInverseAt y k e = Term.close_ k y e := rfl

@[simp] lemma Term.openInverse_def (y : String) (e : Term) :
    Term.openInverse y e = Term.close_ 0 y e := rfl

/-! ### Required properties (iter-31 Phase 1 deliverable) -/

/-- **openInverse_open** (the headline): inverse-then-open recovers the
original LC term. Direct corollary of `Term.open_close` at `k = 0`.

The hypothesis `hy : y ∉ Term.fv target` is **not** required for this
direction — `Term.open_close` discharges the side condition from `LC target`
alone (LC means `target` has no free `bvar 0`, so closing then opening is
honest). We accept `hy` in the signature for API uniformity with the
consumer call site, but the proof does not consume it. -/
theorem Term.openInverse_open (y : String) (target : Term)
    (_hy : y ∉ Term.fv target) (hLC : Term.LC target) :
    (Term.openInverse y target)^[y] = target := by
  unfold Term.opening
  show Term.open_ 0 (.fvar y) (Term.close_ 0 y target) = target
  exact Term.open_close hLC 0 y

/-- **openInverse_fresh** (sanity): when `y` doesn't occur free, `openInverse`
is the identity. Proved by induction on the term; mirrors
`Term.subst_fresh`. -/
theorem Term.openInverse_fresh (y : String) (t : Term) (hy : y ∉ Term.fv t) :
    Term.openInverse y t = t := by
  show Term.close_ 0 y t = t
  -- Generalise over the level since the recursion increments under abs.
  suffices h : ∀ k, Term.close_ k y t = t from h 0
  intro k
  induction t generalizing k with
  | bvar i => rfl
  | fvar z =>
    simp [Term.fv] at hy
    simp [Term.close_, Ne.symm hy]
  | top => rfl
  | abs t b iht ihb =>
    simp [Term.fv] at hy
    simp [Term.close_, iht hy.1 k, ihb hy.2 (k+1)]
  | app t s iht ihs =>
    simp [Term.fv] at hy
    simp [Term.close_, iht hy.1 k, ihs hy.2 k]

/-- **openInverse_open_self** (the round-trip): opening with `y` then
inverse-opening recovers `t`, when `y` was fresh in `t`. Direct corollary
of `Term.close_open`. -/
theorem Term.openInverse_open_self (y : String) (t : Term)
    (hy : y ∉ Term.fv t) :
    Term.openInverse y (t^[y]) = t := by
  show Term.close_ 0 y (Term.open_ 0 (.fvar y) t) = t
  exact Term.close_open 0 y t hy

/-- **openInverse_fv** (free-variable bound): `openInverse y t` removes `y`
from `fv` (replaced by `bvar 0`) and introduces no new free names.

Proof: structural induction over `t` with the level generalised. -/
theorem Term.openInverse_fv (y : String) (t : Term) :
    Term.fv (Term.openInverse y t) ⊆ Term.fv t \ {y} := by
  show Term.fv (Term.close_ 0 y t) ⊆ Term.fv t \ {y}
  -- Generalise the level: `close_ k y` has the same fv behaviour for all k.
  suffices h : ∀ k, Term.fv (Term.close_ k y t) ⊆ Term.fv t \ {y} from h 0
  intro k
  induction t generalizing k with
  | bvar i =>
    simp [Term.close_, Term.fv]
  | fvar z =>
    by_cases h : z = y
    · subst h
      simp [Term.close_, Term.fv]
    · simp only [Term.close_, h, if_false, Term.fv]
      intro w hw
      simp at hw
      subst hw
      refine Finset.mem_sdiff.mpr ⟨by simp, ?_⟩
      simp; exact h
  | top => simp [Term.close_, Term.fv]
  | abs t b iht ihb =>
    intro w hw
    simp [Term.close_, Term.fv] at hw
    rcases hw with hw | hw
    · have := iht k hw
      rcases Finset.mem_sdiff.mp this with ⟨h1, h2⟩
      refine Finset.mem_sdiff.mpr ⟨?_, h2⟩
      exact Finset.mem_union.mpr (Or.inl h1)
    · have := ihb (k+1) hw
      rcases Finset.mem_sdiff.mp this with ⟨h1, h2⟩
      refine Finset.mem_sdiff.mpr ⟨?_, h2⟩
      exact Finset.mem_union.mpr (Or.inr h1)
  | app t s iht ihs =>
    intro w hw
    simp [Term.close_, Term.fv] at hw
    rcases hw with hw | hw
    · have := iht k hw
      rcases Finset.mem_sdiff.mp this with ⟨h1, h2⟩
      refine Finset.mem_sdiff.mpr ⟨?_, h2⟩
      exact Finset.mem_union.mpr (Or.inl h1)
    · have := ihs k hw
      rcases Finset.mem_sdiff.mp this with ⟨h1, h2⟩
      refine Finset.mem_sdiff.mpr ⟨?_, h2⟩
      exact Finset.mem_union.mpr (Or.inr h1)

end Pss

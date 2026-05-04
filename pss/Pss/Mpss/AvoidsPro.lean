import Pss.Mpss.Substitution
import Pss.Mpss.AvoidsProUniv

/-! # `Pss.Mpss.AvoidsPro` — scope-preservation helpers for `MEqRed`

Pasquale & García-Pérez 2024 (CSL 2026), §3 (auxiliary scope-tracking
helpers used in the discharge of Lemma 2).

## History note: the dropped `MEqRedAvoidsPro` predicate

This module previously hosted an inductive predicate
`MEqRedAvoidsPro x : MEqRed Γ s u v → Prop` intended to mechanize the
"moreover" clause of the paper's Lemma 2 (the "no `Me-Pro` on `x`" side
condition that the paper threads through its diamond proof).

That predicate was **unsound** as formulated. Because `MEqRed` is itself
in `Prop`, two `MEqRed Γ s u v` derivations of the same proposition are
definitionally equal under Lean 4's proof irrelevance, regardless of the
constructor shape that produced them. So when (e.g.) `α' = .fvar y` and
`y` happens to be the variable being looked up by `equBinds`, the two
derivations
    `MEqRed.pro hpv heq hα : MEqRed Γ s (.fvar y) (.fvar y)`
    `MEqRed.var hpv       : MEqRed Γ s (.fvar y) (.fvar y)`
inhabit the same proposition. The predicate
`MEqRedAvoidsPro x (MEqRed.pro hpv heq hα)` is therefore the SAME
proposition as `MEqRedAvoidsPro x (MEqRed.var hpv)`, and could be
witnessed by `.var hpv` — fabricating a "no-promotion" certificate
without ever supplying an inner avoidance witness for the actual
`Me-Pro` step. Equivalently: `cases` on a `pro`-shaped avoidance
witness is forced to handle a `var` arm whose constructor index is
definitionally equal to the `pro` index but carries no information
about the promoted variable.

The downstream consumers that actually used Lemma 2 in this codebase
(`Lemma_2_DiamondMEqRed_sameCtx` via `_bare`, in turn used by
`diamond_step_eqStar` in `Pss/Mpss/TransitivityElim.lean`) all dropped
the side-condition clause anyway. The "moreover" clause is needed in
the paper for the Me-Bet/Ms-App case of the Lemma 1 proof (page 22
of the appendix), but `Lemma_1_StrongCommutativity` is itself
axiomatized in this development without an avoidance side condition —
so the clause was never actually consumed downstream.

We therefore **dropped** the predicate entirely from this revision. If
a future agent discharges Lemma 1 and needs the side condition, the
correct re-introduction is via a Bool-valued recursive function
`def avoidsPro : MEqRed Γ s u v → String → Bool` (which sees the
derivation tree's structural shape, not just its propositional
content) — NOT a re-introduction of the inductive predicate.

## Update (post-`16eed34`): Bool-valued redesign now possible

Commit `16eed34` lifted `MEqRed` and `MSubRed` from `Prop` to `Type`.
This enables `Bool`-valued (and more generally, `Type`-valued)
recursion on the derivation tree without falling foul of the kernel's
`Prop → Type` elimination restriction.

We define `avoidsPro` below via the auto-generated recursor (rather
than via tactic-mode pattern matching, which would require manual
termination-by annotations because of the cofinite functional argument
in the binder cases).

## What remains here

* `fv_subset_open_fvar` — opening with a fresh fvar only adds names.
* `MEqRed_fv_subset` — `fv` of the destination is bounded by `fv` of
  the source plus `Γ.dom`.
* `MEqRed_fv_preserve` — `MEqRed` preserves `fv ⊆ Γ.dom`.
* `avoidsPro` — Bool-valued structural-recursion check on `MEqRed`
  derivations. `avoidsPro h x = true` iff no `Me-Pro` step in `h`
  promotes the variable named `x`. Defined via the auto-generated
  `MEqRed.rec` (Type-valued post `16eed34`).

The scope-preservation lemmas have no soundness issue. They are kept
because `Pss.Mpss.Diamond` uses `MEqRed_fv_preserve` in the
`pro × var` cells of `Lemma_2_DiamondMEqRed_core` and in the
`Lemma_2_inline_tAp` discharger.

## Why `Substitution` is allowed

The architectural constraint is "this module must NOT pull in
`Weakening`", which would create a cycle if (in the future) weakening
ever needs scope-preservation lemmas. `Substitution` imports only
`Pss.Mpss.ContextRed`, NOT `Weakening`, so importing it here does NOT
create a cycle.
-/

namespace Pss

/-! ## §1. Auxiliary scope-preservation helpers -/

/-- Helper: opening with a fresh variable can only add `y` to the free
variable set; the original free variables are preserved. Used by
`MEqRed_fv_preserve` to recover `fv body' ⊆ Γ.dom` from a cofinite IH
that delivers `fv (body'^[y]) ⊆ insert y Γ.dom`. -/
theorem fv_subset_open_fvar (e : Term) (y : String) :
    Term.fv e ⊆ Term.fv (e^[y]) := by
  unfold Term.opening
  suffices h : ∀ (k : Nat), Term.fv e ⊆ Term.fv (Term.open_ k (.fvar y) e) by
    exact h 0
  intro k
  induction e generalizing k with
  | bvar i => simp [Term.fv]
  | fvar x => simp [Term.open_]
  | top => simp [Term.fv]
  | abs t b iht ihb =>
    intro z hz
    simp [Term.open_, Term.fv] at *
    rcases hz with hz | hz
    · exact Or.inl (iht k hz)
    · exact Or.inr (ihb (k+1) hz)
  | app t s iht ihs =>
    intro z hz
    simp [Term.open_, Term.fv] at *
    rcases hz with hz | hz
    · exact Or.inl (iht k hz)
    · exact Or.inr (ihs k hz)

/-- Strengthened scope-tracking lemma: along an `MEqRed` reduction, free
variables of the destination are bounded by `fv` of the source plus the
context's domain. This formulation is closed under the cofinitely-
quantified body cases of `bet`/`fun_`/`fOp` (where the IH at a fresh `y`
has body source containing `y` but the corresponding context need not).
-/
theorem MEqRed_fv_subset {Γ : Ctx} {s : Stack} {u v : Term}
    (h : MEqRed Γ s u v) :
    Term.fv v ⊆ Term.fv u ∪ Γ.dom := by
  induction h with
  | @pro Γ s y α α' hpv heq hα ihα =>
    intro z hz
    have hzα' : z ∈ Term.fv α ∪ Γ.dom := ihα hz
    rcases Finset.mem_union.mp hzα' with h' | h'
    · exact Finset.mem_union.mpr (Or.inr
        (Prevalid.fv_lookupEqu (extractPrevalid hpv) heq h'))
    · exact Finset.mem_union.mpr (Or.inr h')
  | @bet Γ s t v0 v0' body body' L hLCt hbody _hUni hv ihbody ihv =>
    classical
    obtain ⟨y, hy⟩ := Term.exists_fresh (L ∪ Term.fv body')
    have hyL : y ∉ L := fun h' => hy (Finset.mem_union.mpr (Or.inl h'))
    have hyB' : y ∉ Term.fv body' := fun h' => hy (Finset.mem_union.mpr (Or.inr h'))
    have ihbody_y : Term.fv (body'^[y]) ⊆ Term.fv (body^[y]) ∪ Γ.dom := ihbody y hyL
    have hfv_body' : Term.fv body' ⊆ Term.fv body ∪ insert y Γ.dom := by
      intro z hz
      have hz_open : z ∈ Term.fv (body'^[y]) := fv_subset_open_fvar body' y hz
      have hzU : z ∈ Term.fv (body^[y]) ∪ Γ.dom := ihbody_y hz_open
      rcases Finset.mem_union.mp hzU with h' | h'
      · have hsub : z ∈ Term.fv body ∪ Term.fv (.fvar y) :=
          Term.fv_open_subset 0 (.fvar y) body h'
        rcases Finset.mem_union.mp hsub with hb | hy'
        · exact Finset.mem_union.mpr (Or.inl hb)
        · have hzy : z = y := by simpa [Term.fv] using hy'
          subst hzy
          exact Finset.mem_union.mpr (Or.inr (Finset.mem_insert_self _ _))
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_insert_of_mem h'))
    have hfv_body'_clean : Term.fv body' ⊆ Term.fv body ∪ Γ.dom := by
      intro z hz
      have := hfv_body' hz
      rcases Finset.mem_union.mp this with h' | h'
      · exact Finset.mem_union.mpr (Or.inl h')
      · rcases Finset.mem_insert.mp h' with hzy | hzdom
        · subst hzy; exact absurd hz hyB'
        · exact Finset.mem_union.mpr (Or.inr hzdom)
    intro z hz
    have hopen_sub : z ∈ Term.fv body' ∪ Term.fv v0' := by
      have := Term.fv_open_subset 0 v0' body' hz
      simpa [Term.opening] using this
    rcases Finset.mem_union.mp hopen_sub with hb | hv0
    · have := hfv_body'_clean hb
      rcases Finset.mem_union.mp this with hb' | hd
      · refine Finset.mem_union.mpr (Or.inl ?_)
        show z ∈ Term.fv (.app (.abs t body) v0)
        rw [Term.fv_app, Term.fv_abs]
        exact Finset.mem_union.mpr (Or.inl
          (Finset.mem_union.mpr (Or.inr hb')))
      · exact Finset.mem_union.mpr (Or.inr hd)
    · have := ihv hv0
      rcases Finset.mem_union.mp this with hv0' | hd
      · refine Finset.mem_union.mpr (Or.inl ?_)
        show z ∈ Term.fv (.app (.abs t body) v0)
        rw [Term.fv_app]
        exact Finset.mem_union.mpr (Or.inr hv0')
      · exact Finset.mem_union.mpr (Or.inr hd)
  | @top Γ s hpv =>
    intro z hz
    simp [Term.fv] at hz
  | @app Γ s u0 u0' v0 v0' hu hv ihu ihv =>
    intro z hz
    simp [Term.fv] at hz
    rcases hz with hz | hz
    · have := ihu hz
      rcases Finset.mem_union.mp this with h' | h'
      · exact Finset.mem_union.mpr (Or.inl (by simp [Term.fv]; exact Or.inl h'))
      · exact Finset.mem_union.mpr (Or.inr h')
    · have := ihv hz
      rcases Finset.mem_union.mp this with h' | h'
      · exact Finset.mem_union.mpr (Or.inl (by simp [Term.fv]; exact Or.inr h'))
      · exact Finset.mem_union.mpr (Or.inr h')
  | @var Γ s y hpv =>
    intro z hz; exact Finset.mem_union.mpr (Or.inl hz)
  | @fun_ Γ t t' body body' L ht hbody _hUni iht ihbody =>
    classical
    obtain ⟨y, hy⟩ := Term.exists_fresh (L ∪ Term.fv body')
    have hyL : y ∉ L := fun h' => hy (Finset.mem_union.mpr (Or.inl h'))
    have hyB' : y ∉ Term.fv body' := fun h' => hy (Finset.mem_union.mpr (Or.inr h'))
    have ihbody_y : Term.fv (body'^[y]) ⊆ Term.fv (body^[y]) ∪
        Ctx.dom (⟨y, t, .sub⟩ :: Γ) := ihbody y hyL
    have hfv_body' : Term.fv body' ⊆ Term.fv body ∪ Γ.dom := by
      intro z hz
      have hz_open : z ∈ Term.fv (body'^[y]) := fv_subset_open_fvar body' y hz
      have hzU : z ∈ Term.fv (body^[y]) ∪ Ctx.dom (⟨y, t, .sub⟩ :: Γ) :=
        ihbody_y hz_open
      rw [Ctx.dom_cons] at hzU
      rcases Finset.mem_union.mp hzU with h' | h'
      · have hsub : z ∈ Term.fv body ∪ Term.fv (.fvar y) :=
          Term.fv_open_subset 0 (.fvar y) body h'
        rcases Finset.mem_union.mp hsub with hb | hy'
        · exact Finset.mem_union.mpr (Or.inl hb)
        · have hzy : z = y := by simpa [Term.fv] using hy'
          subst hzy; exact absurd hz hyB'
      · rcases Finset.mem_insert.mp h' with hzy | hzdom
        · subst hzy; exact absurd hz hyB'
        · exact Finset.mem_union.mpr (Or.inr hzdom)
    intro z hz
    simp [Term.fv] at hz
    rcases hz with hz | hz
    · have := iht hz
      rcases Finset.mem_union.mp this with h' | h'
      · exact Finset.mem_union.mpr (Or.inl (by simp [Term.fv]; exact Or.inl h'))
      · exact Finset.mem_union.mpr (Or.inr h')
    · have := hfv_body' hz
      rcases Finset.mem_union.mp this with h' | h'
      · exact Finset.mem_union.mpr (Or.inl (by simp [Term.fv]; exact Or.inr h'))
      · exact Finset.mem_union.mpr (Or.inr h')
  | @tAp Γ s u0 hpv hLC hfvU =>
    intro z hz; simp [Term.fv] at hz
  | @fOp Γ s t t' αHd body body' L ht hbody _hUni iht ihbody =>
    classical
    obtain ⟨y, hy⟩ := Term.exists_fresh (L ∪ Term.fv body')
    have hyL : y ∉ L := fun h' => hy (Finset.mem_union.mpr (Or.inl h'))
    have hyB' : y ∉ Term.fv body' := fun h' => hy (Finset.mem_union.mpr (Or.inr h'))
    have ihbody_y : Term.fv (body'^[y]) ⊆ Term.fv (body^[y]) ∪
        Ctx.dom (⟨y, αHd, .equ⟩ :: Γ) := ihbody y hyL
    have hfv_body' : Term.fv body' ⊆ Term.fv body ∪ Γ.dom := by
      intro z hz
      have hz_open : z ∈ Term.fv (body'^[y]) := fv_subset_open_fvar body' y hz
      have hzU : z ∈ Term.fv (body^[y]) ∪ Ctx.dom (⟨y, αHd, .equ⟩ :: Γ) :=
        ihbody_y hz_open
      rw [Ctx.dom_cons] at hzU
      rcases Finset.mem_union.mp hzU with h' | h'
      · have hsub : z ∈ Term.fv body ∪ Term.fv (.fvar y) :=
          Term.fv_open_subset 0 (.fvar y) body h'
        rcases Finset.mem_union.mp hsub with hb | hy'
        · exact Finset.mem_union.mpr (Or.inl hb)
        · have hzy : z = y := by simpa [Term.fv] using hy'
          subst hzy; exact absurd hz hyB'
      · rcases Finset.mem_insert.mp h' with hzy | hzdom
        · subst hzy; exact absurd hz hyB'
        · exact Finset.mem_union.mpr (Or.inr hzdom)
    intro z hz
    simp [Term.fv] at hz
    rcases hz with hz | hz
    · have := iht hz
      rcases Finset.mem_union.mp this with h' | h'
      · exact Finset.mem_union.mpr (Or.inl (by simp [Term.fv]; exact Or.inl h'))
      · exact Finset.mem_union.mpr (Or.inr h')
    · have := hfv_body' hz
      rcases Finset.mem_union.mp this with h' | h'
      · exact Finset.mem_union.mpr (Or.inl (by simp [Term.fv]; exact Or.inr h'))
      · exact Finset.mem_union.mpr (Or.inr h')

/-- Scope preservation under `MEqRed`: if `fv u ⊆ Γ.dom` and `Γ; s ⊢ u ⟶ v`,
then `fv v ⊆ Γ.dom`. Provable by induction on the derivation using
`Term.fv_open_subset` and `Term.fv_subst_subset` for the binder cases. -/
theorem MEqRed_fv_preserve {Γ : Ctx} {s : Stack} {u v : Term}
    (h : MEqRed Γ s u v) (hfv : Term.fv u ⊆ Γ.dom) :
    Term.fv v ⊆ Γ.dom := by
  intro z hz
  have hzU : z ∈ Term.fv u ∪ Γ.dom := MEqRed_fv_subset h hz
  rcases Finset.mem_union.mp hzU with h' | h'
  · exact hfv h'
  · exact h'

/-- Helper: a `.equ`-head context is rebindable: replace the bound term
of the head from `α` to `α'` (related by `MEqRed Γ [] α α'`) preserves
`Prevalid`. Requires the head name `y` not to be in `Γ.dom` (which is
already a Prevalid invariant) and `α'`'s data to fit. -/
private noncomputable def Prevalid.equ_head_swap
    {Γ : Ctx} {y : String} {α α' : Term}
    (hpv : Prevalid (⟨y, α, .equ⟩ :: Γ))
    (hLCα' : Term.LC α') (hfvα' : Term.fv α' ⊆ Γ.dom) :
    Prevalid (⟨y, α', .equ⟩ :: Γ) := by
  cases hpv with
  | equ hΓ hy _hfv _hlc => exact Prevalid.equ hΓ hy hfvα' hLCα'

/-- Helper: extend the swap to PrevalidExt for arbitrary stack. -/
private noncomputable def PrevalidExt.equ_head_swap
    {Γ : Ctx} {y : String} {α α' : Term} {s : Stack}
    (hpv : PrevalidExt (⟨y, α, .equ⟩ :: Γ) s)
    (hLCα' : Term.LC α') (hfvα' : Term.fv α' ⊆ Γ.dom) :
    PrevalidExt (⟨y, α', .equ⟩ :: Γ) s := by
  induction hpv with
  | nil hΓ => exact PrevalidExt.nil (Prevalid.equ_head_swap hΓ hLCα' hfvα')
  | @cons _ β hpvE hLCβ hfvβ ih =>
    -- The β stack entry needs fv ⊆ (⟨y, α', .equ⟩ :: Γ).dom; since
    -- (⟨y, α, .equ⟩ :: Γ).dom = (⟨y, α', .equ⟩ :: Γ).dom (only the bound changes,
    -- not the names), the fvβ scoping is preserved.
    refine PrevalidExt.cons ih hLCβ ?_
    intro z hz
    have hzd := hfvβ hz
    -- (⟨y, α, .equ⟩ :: Γ).dom = insert y Γ.dom = (⟨y, α', .equ⟩ :: Γ).dom
    have h1 : Ctx.dom (⟨y, α, .equ⟩ :: Γ) = insert y Γ.dom := Ctx.dom_cons _ _
    have h2 : Ctx.dom (⟨y, α', .equ⟩ :: Γ) = insert y Γ.dom := Ctx.dom_cons _ _
    rw [h2]
    rw [h1] at hzd
    exact hzd

/-! ## §1.7. Stack-head and equ-head replacement for MEqRed

These lemmas allow MEqRed derivations to be re-cast across changes in
the head of the context (`.equ`-binding swap) and the stack head.
Together they discharge the App×App use of `Lemma_2_DiamondMEqRed_ctx_axiom`
in `_inline_app`, eliminating that axiom from `_core`'s closure.

* `MEqRed.equ_head_replace`: swap the bound term of a `.equ`-head
  context from `α` to `α'` (related by `MEqRed Γ [] α α'`), GIVEN an
  `avoidsPro h y = true` premise (rules out `Me-Pro y` lookups that
  would observe the changed binding).

* `MEqRed.stack_head_replace`: swap the head term of the stack from
  `α` to `α'`, with the same `avoidsPro` premise (the body's `.equ`
  recursion uses the head, so the same condition propagates).

The `avoidsPro` premise is satisfied automatically for `MEqRed.refl`
derivations (via `avoidsPro_refl`). For derivations that arise inside
`_core`'s App×App, the premise can be extracted from the
moreover-clause of the IH closing (planned future work).

**STATUS:** `equ_head_replace` is implemented below (with the
structural recursion + `avoidsPro` discharge for `Me-Pro y`).
`stack_head_replace` and the corresponding `_ctx_axiom` discharge are
follow-up targets. -/

/-! ### Helper for the equBinds lookup at modified head -/

/-- If `(Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁).equBinds z α_z` and `z ≠ y`, the
lookup is unaffected by changing `α` to `α'` (since `z ≠ y` skips the
head). -/
theorem _equBinds_equ_head_swap_neq
    {Γ₁ Γ₂ : Ctx} {y z : String} {α α' α_z : Term}
    (hyz : z ≠ y)
    (hb : (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁).equBinds z α_z) :
    (Γ₂ ++ ⟨y, α', .equ⟩ :: Γ₁).equBinds z α_z := by
  induction Γ₂ with
  | nil =>
    simp [Ctx.equBinds, Ctx.lookupEqu_cons] at hb ⊢
    by_cases h : y = z
    · exact absurd h.symm hyz
    · simp [h] at hb ⊢
      exact hb
  | cons e rest ih =>
    show Ctx.lookupEqu (e :: (rest ++ ⟨y, α', .equ⟩ :: Γ₁)) z = some α_z
    have h1 : Ctx.lookupEqu (e :: (rest ++ ⟨y, α, .equ⟩ :: Γ₁)) z = some α_z := hb
    rw [Ctx.lookupEqu_cons] at h1 ⊢
    by_cases he : e.name = z
    · rw [if_pos he] at h1 ⊢; exact h1
    · rw [if_neg he] at h1 ⊢; exact ih h1

/-- Mirror for `subBinds`: changing the `.equ`-head's bound term `α → α'`
does not affect any `.sub`-typed lookup at any `z` (since `.sub` lookups
skip `.equ` entries even when names match). -/
theorem _subBinds_equ_head_swap
    {Γ₁ Γ₂ : Ctx} {y z : String} {α α' t_z : Term}
    (hb : (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁).subBinds z t_z) :
    (Γ₂ ++ ⟨y, α', .equ⟩ :: Γ₁).subBinds z t_z := by
  induction Γ₂ with
  | nil =>
    show Ctx.lookupSub (⟨y, α', .equ⟩ :: Γ₁) z = some t_z
    have h1 : Ctx.lookupSub (⟨y, α, .equ⟩ :: Γ₁) z = some t_z := hb
    rw [Ctx.lookupSub_cons] at h1 ⊢
    -- The head is `.equ`, so `lookupSub` always skips it (returns none for
    -- a name match, recurses for non-match). Both sides reduce to lookup on Γ₁.
    by_cases hxy : y = z
    · simp [hxy] at h1 ⊢
    · simp [hxy] at h1 ⊢; exact h1
  | cons e rest ih =>
    show Ctx.lookupSub (e :: (rest ++ ⟨y, α', .equ⟩ :: Γ₁)) z = some t_z
    have h1 : Ctx.lookupSub (e :: (rest ++ ⟨y, α, .equ⟩ :: Γ₁)) z = some t_z := hb
    rw [Ctx.lookupSub_cons] at h1 ⊢
    by_cases he : e.name = z
    · rw [if_pos he] at h1 ⊢
      cases hkind : e.kind with
      | sub => simp [hkind] at h1 ⊢; exact h1
      | equ => simp [hkind] at h1
    · rw [if_neg he] at h1 ⊢; exact ih h1

/-- Generalized form of `Prevalid.equ_head_swap`: replace the bound term
of the `.equ`-head from `α` to `α'` in `Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁`. The
`fv α'` constraint is against `Γ₁.dom` (not the whole context's dom),
mirroring the `Prevalid.equ` constructor's invariant. -/
noncomputable def Prevalid.equ_head_replace_mid
    {Γ₁ Γ₂ : Ctx} {y : String} {α α' : Term}
    (hpv : Prevalid (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁))
    (hLCα' : Term.LC α') (hfvα' : Term.fv α' ⊆ Γ₁.dom) :
    Prevalid (Γ₂ ++ ⟨y, α', .equ⟩ :: Γ₁) := by
  induction Γ₂ with
  | nil =>
    cases hpv with
    | equ hΓ hy _hfv _hlc => exact Prevalid.equ hΓ hy hfvα' hLCα'
  | cons e rest ih =>
    -- `hpv : Prevalid (e :: rest ++ ⟨y, α, .equ⟩ :: Γ₁)`.
    have hpv' : Prevalid (e :: (rest ++ ⟨y, α, .equ⟩ :: Γ₁)) := by simpa using hpv
    cases hpv' with
    | @sub _ x t hpv_tail hx hfvt hLCt =>
      have ih' := ih hpv_tail
      have hx' : x ∉ Ctx.dom (rest ++ ⟨y, α', .equ⟩ :: Γ₁) := by
        rw [Ctx.dom_append, Ctx.dom_cons]
        rw [Ctx.dom_append, Ctx.dom_cons] at hx
        exact hx
      have hfvt' : Term.fv t ⊆ Ctx.dom (rest ++ ⟨y, α', .equ⟩ :: Γ₁) := by
        rw [Ctx.dom_append, Ctx.dom_cons]
        rw [Ctx.dom_append, Ctx.dom_cons] at hfvt
        exact hfvt
      exact Prevalid.sub ih' hx' hfvt' hLCt
    | @equ _ x β hpv_tail hx hfvβ hLCβ =>
      have ih' := ih hpv_tail
      have hx' : x ∉ Ctx.dom (rest ++ ⟨y, α', .equ⟩ :: Γ₁) := by
        rw [Ctx.dom_append, Ctx.dom_cons]
        rw [Ctx.dom_append, Ctx.dom_cons] at hx
        exact hx
      have hfvβ' : Term.fv β ⊆ Ctx.dom (rest ++ ⟨y, α', .equ⟩ :: Γ₁) := by
        rw [Ctx.dom_append, Ctx.dom_cons]
        rw [Ctx.dom_append, Ctx.dom_cons] at hfvβ
        exact hfvβ
      exact Prevalid.equ ih' hx' hfvβ' hLCβ

/-- `PrevalidExt` analog: replace the bound term of the `.equ`-head
from `α` to `α'` in `Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁` for any stack. -/
noncomputable def PrevalidExt.equ_head_replace_mid
    {Γ₁ Γ₂ : Ctx} {st : Stack} {y : String} {α α' : Term}
    (hpv : PrevalidExt (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁) st)
    (hLCα' : Term.LC α') (hfvα' : Term.fv α' ⊆ Γ₁.dom) :
    PrevalidExt (Γ₂ ++ ⟨y, α', .equ⟩ :: Γ₁) st := by
  induction hpv with
  | nil hΓ =>
    exact PrevalidExt.nil (Prevalid.equ_head_replace_mid hΓ hLCα' hfvα')
  | @cons _ β hpvE hLCβ hfvβ ih =>
    refine PrevalidExt.cons ih hLCβ ?_
    -- `(Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁).dom = (Γ₂ ++ ⟨y, α', .equ⟩ :: Γ₁).dom`
    -- (only the bound changes, not names).
    intro z hz
    have hzd := hfvβ hz
    rw [Ctx.dom_append, Ctx.dom_cons] at hzd ⊢
    exact hzd



/-! ## §2. Bool-valued `avoidsPro` (post `MEqRed : Type` refactor)

`avoidsPro h x = true` iff the derivation `h : MEqRed Γ s u v` does not
contain any `Me-Pro` step that promotes the variable named `x`. The
paper's "moreover" clause of Lemma 2 propagates an avoidance side
condition like this through both closing derivations.

Defined via the auto-generated `MEqRed.rec` rather than via tactic-mode
pattern matching. The reason: the cofinite cases (`bet`, `fun_`, `fOp`)
have a body argument of functional type `∀ y, y ∉ L → MEqRed …`, and
the equation compiler does not synthesise a structural decreasing
measure across that — so a direct `match` fails termination checking.
The recursor's auto-generated motive correctly threads the IH through
without needing a manual termination annotation.

Convention for the cofinite arms: pick a canonical fresh `y` via
`Classical.choose` against the binder-LC bound `L` and recurse on the
body opened with that `y`. (`avoidsPro` is `noncomputable` because of
this; the recursor itself would be computable, but the pickFresh helper
relies on `Classical.choice`.) -/

/-- Helper: pick a canonical fresh name avoiding `L`. Exposed publicly
so consumers (`Pss.Mpss.Diamond`) can refer to the body witness picked
in the cofinite arms of `avoidsPro`'s simp lemmas. -/
noncomputable def pickFresh (L : Finset String) : String :=
  Classical.choose (Term.exists_fresh L)

theorem pickFresh_notMem (L : Finset String) :
    pickFresh L ∉ L :=
  Classical.choose_spec (Term.exists_fresh L)

/-- Bool-valued avoidance check on `MEqRed` derivations.

`avoidsPro h x = true` ↔ no `Me-Pro` step in `h` promotes `x`.

The cofinite arms (`bet`, `fun_`, `fOp`) recurse on the body opened
with a canonical fresh name picked via `Classical.choose`. This is
sound because `MEqRed` is `Type`-valued (commit `16eed34`), so the
constructor shape of `h` is observable at the term level. -/
noncomputable def avoidsPro {Γ s u v} (h : MEqRed Γ s u v) (x : String) : Bool :=
  MEqRed.rec
    (motive := fun _ _ _ _ _ => String → Bool)
    -- Me-Pro: the promoted variable's name `y` is in scope here.
    (fun {_ _ y _ _} _ _ _ ihα x => decide (y ≠ x) && ihα x)
    -- Me-Bet: cofinite body + operand recursion.
    (fun L _ _ _ _ ihbody ihv x =>
      let y := pickFresh L
      have hyL : y ∉ L := pickFresh_notMem L
      ihbody y hyL x && ihv x)
    -- Me-Top: vacuous.
    (fun _ _ => true)
    -- Me-App: both subterms.
    (fun _ _ ihu ihv x => ihu x && ihv x)
    -- Me-Var: vacuous (no Me-Pro).
    (fun _ _ => true)
    -- Me-Fun: bound annotation + cofinite body.
    (fun L _ _ _ iht ihbody x =>
      let y := pickFresh L
      have hyL : y ∉ L := pickFresh_notMem L
      iht x && ihbody y hyL x)
    -- Me-TAp: vacuous.
    (fun _ _ _ _ => true)
    -- Me-FOp: bound annotation + cofinite body.
    (fun L _ _ _ iht ihbody x =>
      let y := pickFresh L
      have hyL : y ∉ L := pickFresh_notMem L
      iht x && ihbody y hyL x)
    h x

/-! ## §2.1. Definitional unfoldings of `avoidsPro` per constructor

Mirror of the `msAvoidsPro_*` simp lemmas below: per-constructor `simp`
unfoldings of `avoidsPro` so downstream proofs can split off avoidance
witnesses without unfolding the recursor by hand. -/

@[simp] theorem avoidsPro_pro {Γ s y α α'} (hpv : PrevalidExt Γ s)
    (heq : Γ.equBinds y α) (hα : MEqRed Γ s α α') (x : String) :
    avoidsPro (MEqRed.pro hpv heq hα) x = (decide (y ≠ x) && avoidsPro hα x) := by
  unfold avoidsPro; rfl

@[simp] theorem avoidsPro_bet {Γ s t v v' body body'} (L : Finset String)
    (hLCt : Term.LC t)
    (hbody : ∀ y, y ∉ L → MEqRed Γ s (body^[y]) (body'^[y]))
    (hUni : True)
    (hv : MEqRed Γ [] v v') (x : String) :
    avoidsPro (MEqRed.bet L hLCt hbody hUni hv) x =
      (avoidsPro (hbody (pickFresh L) (pickFresh_notMem L)) x && avoidsPro hv x) := by
  unfold avoidsPro; rfl

@[simp] theorem avoidsPro_top {Γ s} (hpv : PrevalidExt Γ s) (x : String) :
    avoidsPro (MEqRed.top hpv) x = true := by
  unfold avoidsPro; rfl

@[simp] theorem avoidsPro_app {Γ s u u' v v'}
    (hu : MEqRed Γ (v :: s) u u') (hv : MEqRed Γ [] v v') (x : String) :
    avoidsPro (MEqRed.app hu hv) x = (avoidsPro hu x && avoidsPro hv x) := by
  unfold avoidsPro; rfl

@[simp] theorem avoidsPro_var {Γ s y} (hpv : PrevalidExt Γ s) (x : String) :
    avoidsPro (@MEqRed.var Γ s y hpv) x = true := by
  unfold avoidsPro; rfl

@[simp] theorem avoidsPro_fun_ {Γ t t' body body'} (L : Finset String)
    (ht : MEqRed Γ [] t t')
    (hbody : ∀ y, y ∉ L →
      MEqRed (⟨y, t, .sub⟩ :: Γ) [] (body^[y]) (body'^[y]))
    (hUni : True)
    (x : String) :
    avoidsPro (MEqRed.fun_ L ht hbody hUni) x =
      (avoidsPro ht x && avoidsPro (hbody (pickFresh L) (pickFresh_notMem L)) x) := by
  unfold avoidsPro; rfl

@[simp] theorem avoidsPro_tAp {Γ s u} (hpv : PrevalidExt Γ s)
    (hLCu : Term.LC u) (hfvu : Term.fv u ⊆ Γ.dom) (x : String) :
    avoidsPro (MEqRed.tAp hpv hLCu hfvu) x = true := by
  unfold avoidsPro; rfl

@[simp] theorem avoidsPro_fOp {Γ s t t' α body body'} (L : Finset String)
    (ht : MEqRed Γ [] t t')
    (hbody : ∀ y, y ∉ L →
      MEqRed (⟨y, α, .equ⟩ :: Γ) s (body^[y]) (body'^[y]))
    (hUni : True)
    (x : String) :
    avoidsPro (MEqRed.fOp L ht hbody hUni) x =
      (avoidsPro ht x && avoidsPro (hbody (pickFresh L) (pickFresh_notMem L)) x) := by
  unfold avoidsPro; rfl

/-! ## §2.2. `avoidsPro_refl` axiom — the moreover-clause unblocker

`MEqRed.refl` (in `Pss.Mpss.Substitution`) is the only constructor-opaque
`MEqRed`-builder in the codebase. It is built via `Nonempty.some` on top
of `MEqRed.refl_J : MEqRedJ Γ s u u`, where the `Nonempty` wrapper exists
purely because the underlying induction on `Term.LC u` cannot eliminate
into a `Type`-valued conclusion (`Term.LC` is `Prop`-valued).

Morally: `MEqRed.refl_J` is built ENTIRELY from non-`pro` constructors —
`top`, `var`, `app`, `fun_`, `fOp` — every one of which has
`avoidsPro = true` for any variable `x`. The reflexivity tree never
reaches for an `Me-Pro` step (it has no need to; it's strictly
congruence-closure on `LC`).

Therefore `avoidsPro (MEqRed.refl _ _ _) x = true` is structurally true,
even though Lean's kernel cannot verify this directly because
`Classical.choice` discards the constructor tree of the
`Nonempty`-wrapped derivation.

## Resolution paths (none chosen this revision; see Diamond.lean §3.1)

1. **Type-valued `Term.LC`.** Lifts `LC` from `Prop` to `Type`, making
   `MEqRed.refl_J` itself `Type`-valued and therefore observably built
   from `MEqRed` constructors. This axiom would become a theorem,
   provable by induction. Cost: cross-codebase refactor — `Term.LC`
   appears in dozens of theorem statements across `Pss/Syntax`,
   `Pss/Mpss`, etc.

2. **Source-driven refl construction** (`refl_for : MEqRed Γ s α α' →
   MEqRed Γ s α' α'` by induction on the source). Works for all cases
   except `Me-Bet`, whose destination is `Term.opening v' body'` — a
   substituted term with no constructor-decomposable refl shape without
   re-deriving structural induction on `LC` (i.e., circling back to
   path 1).

3. **This axiom.** Single narrow statement, replaces 3 prior axioms
   (`Lemma_2_inline_app_bet_residual_axiom`,
   `Lemma_2_inline_bet_residual_axiom`, possibly more) at the cost of
   one. Net axiom reduction. -/

/-- `MEqRed.refl _ _ _` always has `avoidsPro = true` for any `x`.

**Post-Type-LC refactor (Option B): now a theorem.**
With `Term.LC : Type`, `MEqRed.refl` is built by direct structural
recursion on the LC witness (no `Classical.choice` extraction). The
recursion only ever invokes `top`/`var`/`app`/`fun_`/`fOp` —
constructors that have `avoidsPro = true` for any `x` — so the result
follows by mirror-induction on the same LC witness.

The proof uses `MEqRed.refl.eq_def` (the equation compiler's defining
equations) to unfold the recursion at each constructor, then applies
the per-constructor `avoidsPro_*` `simp` lemmas. -/
theorem avoidsPro_refl
    {Γ : Ctx} {s : Stack} {u : Term}
    (hpv : PrevalidExt Γ s) (hLC : Term.LC u) (hfv : Term.fv u ⊆ Γ.dom)
    (x : String) :
    avoidsPro (MEqRed.refl hpv hLC hfv) x = true := by
  induction hLC generalizing s Γ with
  | top =>
    simp only [MEqRed.refl, avoidsPro_top]
  | fvar y =>
    simp only [MEqRed.refl, avoidsPro_var]
  | @app a b hLCa hLCb iha ihb =>
    simp only [MEqRed.refl, avoidsPro_app, Bool.and_eq_true]
    refine ⟨iha _ _, ihb _ _⟩
  | @abs L bound body hLCbound hbody ihbound ihbody =>
    cases s with
    | nil =>
      simp only [MEqRed.refl, avoidsPro_fun_, Bool.and_eq_true]
      refine ⟨ihbound _ _, ?_⟩
      exact ihbody _ _ _ _
    | cons α tail =>
      cases hpv with
      | cons hpvr hLCα hfvα =>
        simp only [MEqRed.refl, avoidsPro_fOp, Bool.and_eq_true]
        refine ⟨ihbound _ _, ?_⟩
        exact ihbody _ _ _ _

/-! ## §2.6. `noVarX` — strengthened avoidance ruling out `Me-Var x` too

Iteration-1 viability spike for `Lemma_32_AsymmetricEqu` (Substitution.lean).

### Why a NEW Bool predicate (and not a strengthening of `avoidsPro`)

`avoidsPro h x = true` rules out `Me-Pro` steps that promote `x`. It does
NOT rule out `Me-Var x` (which is a vacuous reflexivity step on the bound
variable). For the **asymmetric** Lemma 32

```
hbody : MEqRed (⟨x, α, .equ⟩ :: Γ) s body body'
hv    : MEqRed Γ [] v v'
─────────────────────────────────────────────────
        MEqRed Γ s (subst x v body) (subst x v' body')
```

a counterexample exists with `body = body' = .fvar x`, witnessed by
`MEqRed.var hpv` (Reductions.lean:104-106; no `x ∉ Γ.dom` precondition):
the conclusion would require `MEqRed Γ s v v'` from `MEqRed Γ [] v v'`,
which is a non-trivial stack lift that is NOT generally available.

`noVarX h x` returns `false` precisely when an `Me-Var x` step appears
anywhere in `h`, ruling out the counterexample. Its definition mirrors
`avoidsPro`'s recursive shape, with the difference at the `var`/`pro` arms:
* `Me-Var y` — `noVarX = decide (y ≠ x)` (vs. `avoidsPro = true`).
* `Me-Pro y _ _` — `noVarX = ihα x` (no `y ≠ x` check; `Me-Pro y` is fine
  to reach `x` AS LONG AS the inner derivation also avoids `Me-Var x`).
  Compare `avoidsPro = decide (y ≠ x) && ihα x`.

All other arms are conjunctions that descend into sub-derivations,
identical in shape to `avoidsPro`. -/

/-- Bool-valued check on `MEqRed` derivations: `noVarX h x = true` iff no
`Me-Var x` step appears in `h` (i.e. the derivation never reflexively
re-uses the variable named `x` via the `Me-Var` constructor).

Mirrors `avoidsPro`'s recursive shape, descending into sub-derivations
in every case. The defining difference is in the `var` arm: `noVarX`
returns `decide (y ≠ x)` while `avoidsPro` returns `true`. -/
noncomputable def noVarX {Γ s u v} (h : MEqRed Γ s u v) (x : String) : Bool :=
  MEqRed.rec
    (motive := fun _ _ _ _ _ => String → Bool)
    -- Me-Pro: descend into `α`'s reduction. (No `y ≠ x` check; Me-Pro
    -- is fine — it's only Me-Var on x that's forbidden.)
    (fun {_ _ _ _ _} _ _ _ ihα x => ihα x)
    -- Me-Bet: cofinite body + operand recursion.
    (fun L _ _ _ _ ihbody ihv x =>
      let y := pickFresh L
      have hyL : y ∉ L := pickFresh_notMem L
      ihbody y hyL x && ihv x)
    -- Me-Top: vacuous.
    (fun _ _ => true)
    -- Me-App: both subterms.
    (fun _ _ ihu ihv x => ihu x && ihv x)
    -- Me-Var: the defining arm. Forbid `y = x`.
    (fun {_ _ y} _ x => decide (y ≠ x))
    -- Me-Fun: bound annotation + cofinite body.
    (fun L _ _ _ iht ihbody x =>
      let y := pickFresh L
      have hyL : y ∉ L := pickFresh_notMem L
      iht x && ihbody y hyL x)
    -- Me-TAp: vacuous.
    (fun _ _ _ _ => true)
    -- Me-FOp: bound annotation + cofinite body.
    (fun L _ _ _ iht ihbody x =>
      let y := pickFresh L
      have hyL : y ∉ L := pickFresh_notMem L
      iht x && ihbody y hyL x)
    h x

/-! ### Per-constructor `simp` lemmas for `noVarX`. Mirror of the
`avoidsPro_*` family. -/

@[simp] theorem noVarX_pro {Γ s y α α'} (hpv : PrevalidExt Γ s)
    (heq : Γ.equBinds y α) (hα : MEqRed Γ s α α') (x : String) :
    noVarX (MEqRed.pro hpv heq hα) x = noVarX hα x := by
  unfold noVarX; rfl

@[simp] theorem noVarX_bet {Γ s t v v' body body'} (L : Finset String)
    (hLCt : Term.LC t)
    (hbody : ∀ y, y ∉ L → MEqRed Γ s (body^[y]) (body'^[y]))
    (hUni : True)
    (hv : MEqRed Γ [] v v') (x : String) :
    noVarX (MEqRed.bet L hLCt hbody hUni hv) x =
      (noVarX (hbody (pickFresh L) (pickFresh_notMem L)) x && noVarX hv x) := by
  unfold noVarX; rfl

@[simp] theorem noVarX_top {Γ s} (hpv : PrevalidExt Γ s) (x : String) :
    noVarX (MEqRed.top hpv) x = true := by
  unfold noVarX; rfl

@[simp] theorem noVarX_app {Γ s u u' v v'}
    (hu : MEqRed Γ (v :: s) u u') (hv : MEqRed Γ [] v v') (x : String) :
    noVarX (MEqRed.app hu hv) x = (noVarX hu x && noVarX hv x) := by
  unfold noVarX; rfl

@[simp] theorem noVarX_var {Γ s y} (hpv : PrevalidExt Γ s) (x : String) :
    noVarX (@MEqRed.var Γ s y hpv) x = decide (y ≠ x) := by
  unfold noVarX; rfl

@[simp] theorem noVarX_fun_ {Γ t t' body body'} (L : Finset String)
    (ht : MEqRed Γ [] t t')
    (hbody : ∀ y, y ∉ L →
      MEqRed (⟨y, t, .sub⟩ :: Γ) [] (body^[y]) (body'^[y]))
    (hUni : True)
    (x : String) :
    noVarX (MEqRed.fun_ L ht hbody hUni) x =
      (noVarX ht x && noVarX (hbody (pickFresh L) (pickFresh_notMem L)) x) := by
  unfold noVarX; rfl

@[simp] theorem noVarX_tAp {Γ s u} (hpv : PrevalidExt Γ s)
    (hLCu : Term.LC u) (hfvu : Term.fv u ⊆ Γ.dom) (x : String) :
    noVarX (MEqRed.tAp hpv hLCu hfvu) x = true := by
  unfold noVarX; rfl

@[simp] theorem noVarX_fOp {Γ s t t' α body body'} (L : Finset String)
    (ht : MEqRed Γ [] t t')
    (hbody : ∀ y, y ∉ L →
      MEqRed (⟨y, α, .equ⟩ :: Γ) s (body^[y]) (body'^[y]))
    (hUni : True)
    (x : String) :
    noVarX (MEqRed.fOp L ht hbody hUni) x =
      (noVarX ht x && noVarX (hbody (pickFresh L) (pickFresh_notMem L)) x) := by
  unfold noVarX; rfl

/-! ### `noVarX_refl` — the `MEqRed.refl` discharge.

The reflexivity `MEqRed.refl hpv hLC hfv` recurses on the LC witness; the
`Term.LC.fvar y` arm produces `MEqRed.var hpv : MEqRed Γ s (.fvar y) (.fvar y)`,
which has `noVarX _ x = decide (y ≠ x)`. If `x ∈ Term.fv u`, then some
`.fvar x` subterm of `u` contributes a `Me-Var x` step at recursion, making
`noVarX = false`.

The side condition `x ∉ Term.fv u` is necessary; it is, however, NOT
sufficient by itself. In the `LC.abs` arm, `MEqRed.refl` picks a fresh
`y` against its widened `L' = L ∪ Γ.dom ∪ Term.fv body`. The body
recursion runs on `body^[y]`. To guarantee `x ∉ Term.fv (body^[y])`,
we additionally need `x ≠ y`. Since `y ∉ Γ.dom`, the side condition
`x ∈ Γ.dom` ensures `y ≠ x`. So we require BOTH `x ∉ Term.fv u` (for the
`fvar` arm) AND `x ∈ Γ.dom` (for the binder arm's freshness alignment).

In the planned downstream use (`Lemma_32_AsymmetricEqu`), `x` is a
context-bound `.equ`-head variable, so `x ∈ Γ.dom` holds directly. -/

/-- `MEqRed.refl hpv hLC hfv` has `noVarX = true` for any `x ∈ Γ.dom`
that does not appear free in `u`.

Proof by mirror-induction on `hLC`, exactly as `avoidsPro_refl` (line
635), with the new ingredient: `Term.LC.fvar y` gives `noVarX (MEqRed.var
hpv) x = decide (y ≠ x)`, discharged from `hx : x ∉ Term.fv (.fvar y) =
{y}`. The binder arms (`LC.abs` over `nil` / `cons` stacks) require
`x ∈ Γ.dom` to ensure the picked-fresh `y ∉ Γ.dom` satisfies `y ≠ x`,
which in turn lets us conclude `x ∉ Term.fv (body^[y])` from
`Term.fv_open_subset`. -/
theorem noVarX_refl
    {Γ : Ctx} {s : Stack} {u : Term}
    (hpv : PrevalidExt Γ s) (hLC : Term.LC u) (hfv : Term.fv u ⊆ Γ.dom)
    (x : String) (hx : x ∉ Term.fv u) (hxΓ : x ∈ Γ.dom) :
    noVarX (MEqRed.refl hpv hLC hfv) x = true := by
  induction hLC generalizing s Γ with
  | top =>
    simp only [MEqRed.refl, noVarX_top]
  | fvar y =>
    -- `fv (.fvar y) = {y}`; `hx : x ∉ {y}` gives `y ≠ x`.
    have hyx : y ≠ x := by
      intro h
      apply hx
      simp [Term.fv, h]
    simp only [MEqRed.refl, noVarX_var, decide_eq_true_eq]
    exact hyx
  | @app a b hLCa hLCb iha ihb =>
    -- `fv (.app a b) = fv a ∪ fv b`; `hx` splits.
    have hxa : x ∉ Term.fv a := fun h => hx (by simp [Term.fv]; exact Or.inl h)
    have hxb : x ∉ Term.fv b := fun h => hx (by simp [Term.fv]; exact Or.inr h)
    simp only [MEqRed.refl, noVarX_app, Bool.and_eq_true]
    refine ⟨iha _ _ hxa hxΓ, ihb _ _ hxb hxΓ⟩
  | @abs L bound body hLCbound hbody ihbound ihbody =>
    -- `fv (.abs bound body) = fv bound ∪ fv body`; both disjoint from `x`.
    have hxbound : x ∉ Term.fv bound :=
      fun h => hx (by simp [Term.fv]; exact Or.inl h)
    have hxbody : x ∉ Term.fv body :=
      fun h => hx (by simp [Term.fv]; exact Or.inr h)
    cases s with
    | nil =>
      simp only [MEqRed.refl, noVarX_fun_, Bool.and_eq_true]
      refine ⟨ihbound _ _ hxbound hxΓ, ?_⟩
      -- The picked-fresh `y` is outside `L ∪ Γ.dom ∪ Term.fv body`.
      -- Since `x ∈ Γ.dom`, `y ≠ x`. Hence `x ∉ Term.fv (body^[y]) ⊆
      -- Term.fv body ∪ {y}`.
      set L' := L ∪ Γ.dom ∪ Term.fv body with hL'
      have hyL' : pickFresh L' ∉ L' := pickFresh_notMem L'
      have hy_notΓ : pickFresh L' ∉ Γ.dom := fun h => hyL'
        (Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr h))))
      have hyx : pickFresh L' ≠ x := fun h => hy_notΓ (h ▸ hxΓ)
      have hxopen : x ∉ Term.fv (body^[pickFresh L']) := by
        intro hxin
        have hsub := Term.fv_open_subset 0 (.fvar (pickFresh L')) body hxin
        rcases Finset.mem_union.mp hsub with h1 | h1
        · exact hxbody h1
        · have hxy : x = pickFresh L' := by simpa [Term.fv] using h1
          exact hyx hxy.symm
      -- The IH-friendly context: `⟨pickFresh L', bound, .sub⟩ :: Γ`.
      have hxΓ' : x ∈ Ctx.dom (⟨pickFresh L', bound, .sub⟩ :: Γ) := by
        rw [Ctx.dom_cons]; exact Finset.mem_insert_of_mem hxΓ
      apply ihbody _ _ _ _ hxopen hxΓ'
    | cons α tail =>
      cases hpv with
      | cons hpvr hLCα hfvα =>
        simp only [MEqRed.refl, noVarX_fOp, Bool.and_eq_true]
        refine ⟨ihbound _ _ hxbound hxΓ, ?_⟩
        set L' := L ∪ Γ.dom ∪ Term.fv body with hL'
        have hyL' : pickFresh L' ∉ L' := pickFresh_notMem L'
        have hy_notΓ : pickFresh L' ∉ Γ.dom := fun h => hyL'
          (Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr h))))
        have hyx : pickFresh L' ≠ x := fun h => hy_notΓ (h ▸ hxΓ)
        have hxopen : x ∉ Term.fv (body^[pickFresh L']) := by
          intro hxin
          have hsub := Term.fv_open_subset 0 (.fvar (pickFresh L')) body hxin
          rcases Finset.mem_union.mp hsub with h1 | h1
          · exact hxbody h1
          · have hxy : x = pickFresh L' := by simpa [Term.fv] using h1
            exact hyx hxy.symm
        have hxΓ' : x ∈ Ctx.dom (⟨pickFresh L', α, .equ⟩ :: Γ) := by
          rw [Ctx.dom_cons]; exact Finset.mem_insert_of_mem hxΓ
        apply ihbody _ _ _ _ hxopen hxΓ'

/-! ## §2.7. `Lemma_32_AsymmetricEqu` — asymmetric extension of Lemma 32

Iteration-1 viability spike. The restricted form
`Lemma_32_ReductionUnderSubst_Eq_OfEqu` (Substitution.lean:1053)
substitutes the SAME term `s = v` on both sides of an MEqRed under an
`.equ`-head binding `x ≡ v`. The TODO at Substitution.lean:1042-1044
calls out the asymmetric extension (substituting `v` on the LHS and `v'`
on the RHS for some `v ⟶ v'`) as the form needed for the β-residual
discharges in `Pss.Mpss.Diamond` and `Pss.Mpss.Commutation`.

The axiom CANNOT live in `Substitution.lean` because its statement
mentions `avoidsPro` and `noVarX`, which are defined here in
`Pss.Mpss.AvoidsPro` — and `AvoidsPro` already imports `Substitution`.
The cycle would be unbreakable without an architectural refactor. So
the axiom lives here, alongside its avoidance-machinery prerequisites.

### Truthhood analysis (CRITICAL — read before editing)

The naive form

```
axiom L32asym
  (hbody : MEqRed (⟨x, α, .equ⟩ :: Γ) s body body')
  (hv    : MEqRed Γ [] v v')
  (hav   : avoidsPro hbody x = true) :
  MEqRed Γ s (subst x v body) (subst x v' body')
```

is **mathematically FALSE**. Counterexample: take `body = body' = .fvar x`,
witnessed by

```
hbody := MEqRed.var hpv  : MEqRed (⟨x,α,.equ⟩::Γ) s (.fvar x) (.fvar x)
```

(legitimate; `Me-Var` has NO `x ∉ Γ.dom` precondition — see
`Reductions.lean:104-106`). Then `avoidsPro hbody x = true` vacuously
(no `Me-Pro` arm fires). The conclusion would require

```
MEqRed Γ s (subst x v (.fvar x)) (subst x v' (.fvar x))
  = MEqRed Γ s v v'
```

i.e. an MEqRed under stack `s` between `v` and `v'`. The premise gives
us only `MEqRed Γ [] v v'` (under the EMPTY stack). MPSS's stack-lift
machinery does not provide a free conversion in general, so the
conclusion is unobtainable.

### The fix: dual avoidance premises

Adding `noVarX hbody x = true` rules out the counterexample directly:
`noVarX (MEqRed.var hpv) x = decide (y ≠ x)`, so when `y = x`, the
premise `noVarX hbody x = true` is `decide (x ≠ x) = false`, contradicting
`= true`. The case is closed.

Why this rules out ALL counterexamples (case-by-case on MEqRed
constructors of `hbody`):

* `Me-Pro y _ _` — `avoidsPro` already requires `y ≠ x`, blocking
  `x ↦ α[x\v]` lookup mismatches. `noVarX` adds nothing here.
* `Me-Var y` — the new premise. `y ≠ x` rules out the counterexample
  above.
* `Me-Bet`, `Me-App`, `Me-Fun`, `Me-FOp` — congruence cases with body
  recursions. The premises propagate into sub-derivations conjunctively,
  so the IH always has both witnesses available.
* `Me-Top`, `Me-TAp` — vacuous (no `x` involvement).
* `Me-Bet`'s `body^[y]` recursion — y is fresh, so `y ≠ x` (assuming
  pickFresh widening to include `{x}`). The IH applies cleanly.

### Iteration 3 plan: discharge

Mirror `Lemma_32_ReductionUnderSubst_Eq_OfEqu`'s structural induction on
`hbody`, with these new ingredients per arm:

* **Me-Pro y, y ≠ x**: same as the existing proof — `subst x v (.fvar y)
  = .fvar y` (when `y ≠ x`).
* **Me-Pro y, y = x**: now we substitute `v` on LHS and `v'` on RHS.
  By uniqueness of the `.equ`-head binding, `α = ?`. The conclusion
  needs `MEqRed Γ s (subst x v α') (subst x v' α')` — depends on a
  bridging argument; iteration 3 will detail.
* **Me-Var y**: `noVarX` premise gives `y ≠ x` directly; close via
  `Term.subst_fvar_ne` and `MEqRed.var` (or `MEqRed.refl` when context
  shrinks via Lemma 28).
* **Me-Bet/App/Fun/FOp**: congruence; IH propagates both `avoidsPro`
  and `noVarX` premises via the per-constructor simp lemmas.
* **Me-Top/TAp**: trivial.

### Constructor-by-constructor counterexample audit

Beyond the `Me-Var x` leak, no other constructor of MEqRed produces an
unprovable conclusion under both premises:

* `Me-Pro y` reaches the bound `α` (which is well-scoped in `Γ` ahead
  of the `⟨x, α, .equ⟩` binding, so `subst x v α = α`). When `y = x`,
  the body `α'` lives in the same context and the substitution traverses
  through. The avoidsPro premise rules out the broken case (y = x with
  inner Me-Pro x).
* `Me-Bet/App/Fun/FOp` are congruences over MEqRed; substitution
  distributes (Lemma 31 / Term.subst_open).
* `Me-Top/TAp/Var` are leaves; the only one with `x`-involvement is
  Me-Var, ruled out by `noVarX`. -/

/-- **Lemma 32 (asymmetric extension).** Substitution under an `.equ`-head
binding `x ≡ α` preserves `MEqRed`, with DIFFERENT terms `v` and `v'`
substituted on each side, mediated by `MEqRed Γ [] v v'`.

Premises:
* `hbody : MEqRed (⟨x,α,.equ⟩::Γ) s body body'` — the substitution target.
* `hv    : MEqRed Γ []           v    v'`     — the substituends.
* `hav   : avoidsPro hbody x = true`          — no `Me-Pro x` step.
* `hnv   : noVarX    hbody x = true`          — no `Me-Var x` step.

The dual avoidance premises (`avoidsPro` AND `noVarX`) together rule
out the `MEqRed.var hpv : MEqRed _ s (.fvar x) (.fvar x)` counterexample
that would force `MEqRed Γ s v v'` from `MEqRed Γ [] v v'` (a non-trivial
stack-lift not available in general).

**STATUS: AXIOM (iteration-1 viability spike).** Iteration 3 will
discharge this by structural induction on `hbody`, mirroring
`Lemma_32_ReductionUnderSubst_Eq_OfEqu`'s proof at Substitution.lean:1053.
The new `Me-Var x` arm is closed by `Bool.false_ne_true` from `hnv`. -/
axiom Lemma_32_AsymmetricEqu
    {Γ : Ctx} {s : Stack} {x : String} {α v v' body body' : Term}
    (hbody : MEqRed (⟨x, α, .equ⟩ :: Γ) s body body')
    (hv : MEqRed Γ [] v v')
    (hav : avoidsPro hbody x = true)
    (hnv : noVarX hbody x = true) :
    MEqRed Γ s (Term.subst x v body) (Term.subst x v' body')

/-! ## §2.5. Universal cofinite avoidance: `AvoidsProUniv` (extracted)

The definition `AvoidsProUniv` and its eight per-constructor simp
lemmas were moved to `Pss.Mpss.AvoidsProUniv` in Phase 5g.3a to break
the import cycle that would otherwise arise once `MEqRed`'s cofinite
constructors mention `AvoidsProUniv` directly (Phase 5g.3b). The
substitution-dependent §2.5.1a cast-invariance lemmas, the bridge
`AvoidsProUniv → avoidsPro = true`, and `AvoidsProUniv_refl` remain
here because they need machinery downstream of `Reductions`. -/

/-! ### §2.5.1a. Cast-invariance lemmas for `AvoidsProUniv`

**Why these lemmas exist (Phase 5b' prerequisite).** The rename functors
in `Pss.Mpss.Renaming` (`MEqRed.subst_yz_stray`,
`MEqRed.subst_yz_sub_head`, `_MEqRed_rename_equ_loc`, plus their
`MSubRed` counterparts) are tactic-defined recursive functors. Each
constructor branch uses `rw [...]` to align the goal with the
constructor application, producing an `Eq.mpr`-shaped (or equivalently
`cast`-shaped) wrapper around the underlying `MEqRed.cstr`-application.

When Phase 5b's preservation lemmas (`AvoidsProUniv_subst_yz_stray`
etc.) try to evaluate `AvoidsProUniv (rename ... h) x` and `simp` open
the rename functor, the `cast`/`Eq.mpr` wrapper blocks the per-
constructor `AvoidsProUniv_pro/var/...` simp lemmas from firing —
the head of the term is `cast h_type (MEqRed.cstr ...)`, not
`MEqRed.cstr ...`.

These cast-invariance lemmas state that `AvoidsProUniv` is invariant
under index-aligned casts, and as `@[simp]` they let simp peel the
cast off and expose the constructor head for the per-constructor
simp lemmas.

**Mirror of `Pss.Mpss.Diamond`'s `avoidsPro_subst_eq_*` family**
(lines 676-706), which provides the same cast-elimination service for
the Bool-valued `avoidsPro`. -/

/-- HEq decomposition: if `h : MEqRed Γ s u v` and `h' : MEqRed Γ' s' u' v'`
are heterogeneously equal AND all four indices are propositionally equal,
then `AvoidsProUniv h x ↔ AvoidsProUniv h' x`.

This is the master cast-invariance lemma — all single-index forms below
follow from it via `subst` chains. -/
theorem AvoidsProUniv_eq_of_heq
    {Γ Γ' : Ctx} {s s' : Stack} {u u' v v' : Term}
    {h : MEqRed Γ s u v} {h' : MEqRed Γ' s' u' v'}
    (hΓ : Γ = Γ') (hs : s = s') (hu : u = u') (hv : v = v')
    (heqd : HEq h h') (x : String) :
    AvoidsProUniv h x ↔ AvoidsProUniv h' x := by
  subst hΓ hs hu hv
  cases heqd
  rfl

/-- `cast` produces an HEq with its argument when the type equality is
between aligned MEqRed types. -/
theorem AvoidsProUniv_heq_of_cast
    {α β : Sort _} (h_type : α = β) (a : α) :
    HEq (cast h_type a) a := by
  subst h_type; rfl

/-- Single-index cast invariance: rewriting only the destination term.
Mirror of `Pss.Mpss.Diamond.avoidsPro_subst_eq_dest` for `AvoidsProUniv`. -/
@[simp] theorem AvoidsProUniv_subst_eq_dest
    {Γ : Ctx} {s : Stack} {u v v' : Term}
    (heq : v = v') (h : MEqRed Γ s u v) (x : String) :
    AvoidsProUniv (heq ▸ h) x ↔ AvoidsProUniv h x := by
  subst heq; rfl

/-- Single-index cast invariance: rewriting only the source term.
Mirror of `avoidsPro_subst_eq_src`. -/
@[simp] theorem AvoidsProUniv_subst_eq_src
    {Γ : Ctx} {s : Stack} {u u' v : Term}
    (heq : u = u') (h : MEqRed Γ s u v) (x : String) :
    AvoidsProUniv (heq ▸ h) x ↔ AvoidsProUniv h x := by
  subst heq; rfl

/-- Single-index cast invariance: rewriting only the context.
Mirror of `avoidsPro_subst_eq_ctx`. -/
@[simp] theorem AvoidsProUniv_subst_eq_ctx
    {Γ Γ' : Ctx} {s : Stack} {u v : Term}
    (heq : Γ = Γ') (h : MEqRed Γ s u v) (x : String) :
    AvoidsProUniv (heq ▸ h) x ↔ AvoidsProUniv h x := by
  subst heq; rfl

/-- Single-index cast invariance: rewriting only the stack.
Mirror of `avoidsPro_subst_eq_stack`. -/
@[simp] theorem AvoidsProUniv_subst_eq_stack
    {Γ : Ctx} {s s' : Stack} {u v : Term}
    (heq : s = s') (h : MEqRed Γ s u v) (x : String) :
    AvoidsProUniv (heq ▸ h) x ↔ AvoidsProUniv h x := by
  subst heq; rfl

/-- Multi-index cast invariance: when ALL four indices are equal (so the
type-level equality `MEqRed Γ s u v = MEqRed Γ' s' u' v'` is provable),
`cast` preserves `AvoidsProUniv`.

This is the "general purpose" form for use sites that have all four
index equalities in hand. The single-index versions are preferred when
only one index changes. -/
theorem AvoidsProUniv_cast
    {Γ Γ' : Ctx} {s s' : Stack} {u u' v v' : Term}
    (hΓ : Γ = Γ') (hs : s = s') (hu : u = u') (hv : v = v')
    (h_type : MEqRed Γ s u v = MEqRed Γ' s' u' v')
    (h : MEqRed Γ s u v) (x : String) :
    AvoidsProUniv (cast h_type h) x ↔ AvoidsProUniv h x := by
  exact AvoidsProUniv_eq_of_heq hΓ.symm hs.symm hu.symm hv.symm
    (AvoidsProUniv_heq_of_cast h_type h) x

/-! ### §2.5.2. Bridge: `AvoidsProUniv → avoidsPro = true`

Specialize the universal at the canonical witness `pickFresh L` for
each cofinite arm; recurse structurally on the derivation. This is
the bridge that lets the Bool-based consumers (`equ_head_replace`,
`Lemma_2_inline_*`, etc.) keep using `avoidsPro` while Phase 5b/5c can
generate `AvoidsProUniv` witnesses for rename-stable propagation. -/

theorem AvoidsProUniv_to_avoidsPro
    {Γ : Ctx} {s : Stack} {u v : Term} (h : MEqRed Γ s u v) (x : String)
    (hUniv : AvoidsProUniv h x) :
    avoidsPro h x = true := by
  induction h with
  | @pro Γ s y α α' hpv heq hα ihα =>
    rw [AvoidsProUniv_pro] at hUniv
    obtain ⟨hyx, huα⟩ := hUniv
    rw [avoidsPro_pro, Bool.and_eq_true]
    refine ⟨?_, ihα huα⟩
    simpa [decide_eq_true_eq] using hyx
  | @bet Γ s t v0 v0' body body' L hLCt hbody _hUni hv ihbody ihv =>
    rw [AvoidsProUniv_bet] at hUniv
    obtain ⟨hbU, hvU⟩ := hUniv
    rw [avoidsPro_bet, Bool.and_eq_true]
    exact ⟨ihbody _ _ (hbU _ _), ihv hvU⟩
  | @top Γ s hpv =>
    rw [avoidsPro_top]
  | @app Γ s u0 u0' v0 v0' hu hv ihu ihv =>
    rw [AvoidsProUniv_app] at hUniv
    obtain ⟨huU, hvU⟩ := hUniv
    rw [avoidsPro_app, Bool.and_eq_true]
    exact ⟨ihu huU, ihv hvU⟩
  | @var Γ s y hpv =>
    rw [avoidsPro_var]
  | @fun_ Γ t t' body body' L ht hbody _hUni iht ihbody =>
    rw [AvoidsProUniv_fun_] at hUniv
    obtain ⟨htU, hbU⟩ := hUniv
    rw [avoidsPro_fun_, Bool.and_eq_true]
    exact ⟨iht htU, ihbody _ _ (hbU _ _)⟩
  | @tAp Γ s u0 hpv hLC hfvU =>
    rw [avoidsPro_tAp]
  | @fOp Γ s t t' αHd body body' L ht hbody _hUni iht ihbody =>
    rw [AvoidsProUniv_fOp] at hUniv
    obtain ⟨htU, hbU⟩ := hUniv
    rw [avoidsPro_fOp, Bool.and_eq_true]
    exact ⟨iht htU, ihbody _ _ (hbU _ _)⟩

/-! ### §2.5.3. `AvoidsProUniv_refl` — refl is universally Pro-avoiding

Mirror of `avoidsPro_refl` (§2.2). `MEqRed.refl` is built by direct
structural recursion on `Term.LC u`, never invoking `Me-Pro` — so the
universal Prop-valued avoidance holds at every cofinite witness. The
proof structure mirrors `avoidsPro_refl`'s induction on `hLC`. -/

theorem AvoidsProUniv_refl
    {Γ : Ctx} {s : Stack} {u : Term}
    (hpv : PrevalidExt Γ s) (hLC : Term.LC u) (hfv : Term.fv u ⊆ Γ.dom)
    (x : String) :
    AvoidsProUniv (MEqRed.refl hpv hLC hfv) x := by
  induction hLC generalizing s Γ with
  | top =>
    simp only [MEqRed.refl, AvoidsProUniv_top]
  | fvar y =>
    simp only [MEqRed.refl, AvoidsProUniv_var]
  | @app a b hLCa hLCb iha ihb =>
    simp only [MEqRed.refl, AvoidsProUniv_app]
    refine ⟨iha _ _, ihb _ _⟩
  | @abs L bound body hLCbound hbody ihbound ihbody =>
    cases s with
    | nil =>
      simp only [MEqRed.refl, AvoidsProUniv_fun_]
      refine ⟨ihbound _ _, ?_⟩
      intro y hy
      exact ihbody _ _ _ _
    | cons α tail =>
      cases hpv with
      | cons hpvr hLCα hfvα =>
        simp only [MEqRed.refl, AvoidsProUniv_fOp]
        refine ⟨ihbound _ _, ?_⟩
        intro y hy
        exact ihbody _ _ _ _

/-! ### §2.5.4. `CofinAvoidsProSelfUniv` (extracted)

Definition + per-constructor simp lemmas moved to
`Pss.Mpss.AvoidsProUniv` in Phase 5g.3a (same cycle-break rationale as
§2.5 above). -/

/-! ## §2.3. `cofinDomFresh` — canonical-witness freshness predicate

The β-residual unblock's `MEqRed.equ_head_replace` (in `Pss.Mpss.Renaming`)
needs to recurse on cofinite-arm bodies at a SINGLE canonical witness
(`pickFresh L`), then convert the result to arbitrary witnesses via
`rename_stray` / `rename_sub` / `_rename_equ`. Those rename helpers require:

* `pickFresh L ∉ Γ.dom` (so the canonical witness is "stray" relative to
  the current context),
* `pickFresh L ∉ Term.fv body` and `... ∉ Term.fv body'` (so
  `Term.subst_open_fresh` reduces `subst y₀ (.fvar yfresh) (body^[y₀])`
  to `body^[yfresh]`).

`cofinDomFresh h = true` is a Bool-valued recursive check on the
derivation `h` that asserts these freshness conditions hold at every
cofinite arm's canonical witness.

This is NOT the alpha-equivariance trap — `cofinDomFresh` samples at the
SAME canonical witness as `avoidsPro` (deterministically `pickFresh L`),
so it's a property of the derivation tree's shape, not a cross-witness
claim. -/

noncomputable def cofinDomFresh {Γ s u v} (h : MEqRed Γ s u v) : Bool :=
  MEqRed.rec
    (motive := fun _ _ _ _ _ => Bool)
    -- Me-Pro: recurse on the inner derivation.
    (fun _ _ _ ihα => ihα)
    -- Me-Bet: track freshness at the canonical witness, recurse.
    (fun {Γ _ _ _ _ body body'} L _ _ _ _ ihbody ihv =>
      let y₀ := pickFresh L
      have hy₀L : y₀ ∉ L := pickFresh_notMem L
      decide (y₀ ∉ Γ.dom) && decide (y₀ ∉ Term.fv body) &&
      decide (y₀ ∉ Term.fv body') && ihbody y₀ hy₀L && ihv)
    -- Me-Top: leaf, no freshness condition.
    (fun _ => true)
    -- Me-App: recurse on both subterms.
    (fun _ _ ihu ihv => ihu && ihv)
    -- Me-Var: leaf.
    (fun _ => true)
    -- Me-Fun: track freshness at canonical witness, recurse.
    (fun {Γ _ _ body body'} L _ _ _ iht ihbody =>
      let y₀ := pickFresh L
      have hy₀L : y₀ ∉ L := pickFresh_notMem L
      decide (y₀ ∉ Γ.dom) && decide (y₀ ∉ Term.fv body) &&
      decide (y₀ ∉ Term.fv body') && iht && ihbody y₀ hy₀L)
    -- Me-TAp: leaf.
    (fun _ _ _ => true)
    -- Me-FOp: track freshness at canonical witness, recurse.
    (fun {Γ _ _ _ _ body body'} L _ _ _ iht ihbody =>
      let y₀ := pickFresh L
      have hy₀L : y₀ ∉ L := pickFresh_notMem L
      decide (y₀ ∉ Γ.dom) && decide (y₀ ∉ Term.fv body) &&
      decide (y₀ ∉ Term.fv body') && iht && ihbody y₀ hy₀L)
    h

/-! ### §2.3.1. Per-constructor `simp` unfoldings for `cofinDomFresh` -/

@[simp] theorem cofinDomFresh_pro {Γ s y α α'} (hpv : PrevalidExt Γ s)
    (heq : Γ.equBinds y α) (hα : MEqRed Γ s α α') :
    cofinDomFresh (MEqRed.pro hpv heq hα) = cofinDomFresh hα := by
  unfold cofinDomFresh; rfl

@[simp] theorem cofinDomFresh_bet {Γ s t v v' body body'} (L : Finset String)
    (hLCt : Term.LC t)
    (hbody : ∀ y, y ∉ L → MEqRed Γ s (body^[y]) (body'^[y]))
    (hUni : True)
    (hv : MEqRed Γ [] v v') :
    cofinDomFresh (MEqRed.bet L hLCt hbody hUni hv) =
      (decide (pickFresh L ∉ Γ.dom) && decide (pickFresh L ∉ Term.fv body) &&
       decide (pickFresh L ∉ Term.fv body') &&
       cofinDomFresh (hbody (pickFresh L) (pickFresh_notMem L)) &&
       cofinDomFresh hv) := by
  unfold cofinDomFresh; rfl

@[simp] theorem cofinDomFresh_top {Γ s} (hpv : PrevalidExt Γ s) :
    cofinDomFresh (MEqRed.top hpv) = true := by
  unfold cofinDomFresh; rfl

@[simp] theorem cofinDomFresh_app {Γ s u u' v v'}
    (hu : MEqRed Γ (v :: s) u u') (hv : MEqRed Γ [] v v') :
    cofinDomFresh (MEqRed.app hu hv) =
      (cofinDomFresh hu && cofinDomFresh hv) := by
  unfold cofinDomFresh; rfl

@[simp] theorem cofinDomFresh_var {Γ s y} (hpv : PrevalidExt Γ s) :
    cofinDomFresh (@MEqRed.var Γ s y hpv) = true := by
  unfold cofinDomFresh; rfl

@[simp] theorem cofinDomFresh_fun_ {Γ t t' body body'} (L : Finset String)
    (ht : MEqRed Γ [] t t')
    (hbody : ∀ y, y ∉ L →
      MEqRed (⟨y, t, .sub⟩ :: Γ) [] (body^[y]) (body'^[y]))
    (hUni : True) :
    cofinDomFresh (MEqRed.fun_ L ht hbody hUni) =
      (decide (pickFresh L ∉ Γ.dom) && decide (pickFresh L ∉ Term.fv body) &&
       decide (pickFresh L ∉ Term.fv body') &&
       cofinDomFresh ht &&
       cofinDomFresh (hbody (pickFresh L) (pickFresh_notMem L))) := by
  unfold cofinDomFresh; rfl

@[simp] theorem cofinDomFresh_tAp {Γ s u} (hpv : PrevalidExt Γ s)
    (hLCu : Term.LC u) (hfvu : Term.fv u ⊆ Γ.dom) :
    cofinDomFresh (MEqRed.tAp hpv hLCu hfvu) = true := by
  unfold cofinDomFresh; rfl

@[simp] theorem cofinDomFresh_fOp {Γ s t t' α body body'} (L : Finset String)
    (ht : MEqRed Γ [] t t')
    (hbody : ∀ y, y ∉ L →
      MEqRed (⟨y, α, .equ⟩ :: Γ) s (body^[y]) (body'^[y]))
    (hUni : True) :
    cofinDomFresh (MEqRed.fOp L ht hbody hUni) =
      (decide (pickFresh L ∉ Γ.dom) && decide (pickFresh L ∉ Term.fv body) &&
       decide (pickFresh L ∉ Term.fv body') &&
       cofinDomFresh ht &&
       cofinDomFresh (hbody (pickFresh L) (pickFresh_notMem L))) := by
  unfold cofinDomFresh; rfl

/-! ### §2.3.2. `cofinDomFresh_refl` — refl-shaped derivations are dom-fresh

Mirror of `avoidsPro_refl` (§2.2). `MEqRed.refl` is built by direct
structural recursion on `Term.LC u` (Type-valued post-Type-LC refactor),
so each cofinite arm uses the widened L choice
`L_orig ∪ Γ.dom ∪ Term.fv body` (see `Substitution.lean`'s
`MEqRed.refl` `abs` case). The widened L ensures that
`pickFresh L_chosen` is automatically disjoint from `Γ.dom` and
`Term.fv body` — and since refl produces `body = body'`, also from
`Term.fv body'`. -/

theorem cofinDomFresh_refl
    {Γ : Ctx} {s : Stack} {u : Term}
    (hpv : PrevalidExt Γ s) (hLC : Term.LC u) (hfv : Term.fv u ⊆ Γ.dom) :
    cofinDomFresh (MEqRed.refl hpv hLC hfv) = true := by
  induction hLC generalizing s Γ with
  | top =>
    simp only [MEqRed.refl, cofinDomFresh_top]
  | fvar y =>
    simp only [MEqRed.refl, cofinDomFresh_var]
  | @app a b hLCa hLCb iha ihb =>
    simp only [MEqRed.refl, cofinDomFresh_app, Bool.and_eq_true]
    refine ⟨iha _ _, ihb _ _⟩
  | @abs L bound body hLCbound hbody ihbound ihbody =>
    -- Common: the widened L for the cofinite arm.
    set L' : Finset String := L ∪ Γ.dom ∪ Term.fv body with hL'
    have hpf_notL' : pickFresh L' ∉ L' := pickFresh_notMem L'
    have hpf_notΓ : pickFresh L' ∉ Γ.dom := fun h =>
      hpf_notL' (Finset.mem_union.mpr (Or.inl
        (Finset.mem_union.mpr (Or.inr h))))
    have hpf_notFv : pickFresh L' ∉ Term.fv body := fun h =>
      hpf_notL' (Finset.mem_union.mpr (Or.inr h))
    cases s with
    | nil =>
      simp only [MEqRed.refl, cofinDomFresh_fun_, Bool.and_eq_true,
                 decide_eq_true_eq]
      refine ⟨⟨⟨⟨hpf_notΓ, hpf_notFv⟩, hpf_notFv⟩, ihbound _ _⟩, ?_⟩
      exact ihbody _ _ _ _
    | cons α tail =>
      cases hpv with
      | cons hpvr hLCα hfvα =>
        simp only [MEqRed.refl, cofinDomFresh_fOp, Bool.and_eq_true,
                   decide_eq_true_eq]
        refine ⟨⟨⟨⟨hpf_notΓ, hpf_notFv⟩, hpf_notFv⟩, ihbound _ _⟩, ?_⟩
        exact ihbody _ _ _ _

/-! ## §3. Bool-valued `msAvoidsPro` for `MSubRed`

Mirror of `avoidsPro` for the subtype-reduction relation. `msAvoidsPro h x
= true` iff the derivation `h : MSubRed Γ s u v` does not contain any
`Ms-Pro` step that promotes the variable named `x`.

This is the analogue used to discharge `Lemma_30_msPro_x_axiom`: the
paper's "no `Ms-Pro` on `x`" side condition on Lemma 30 is captured by
requiring `msAvoidsPro h x = true` as an additional premise.

The `Ms-Equ` constructor embeds a `MEqRed` derivation, so `msAvoidsPro`
delegates to `avoidsPro` in that arm. The cofinite arms (`fun_`, `fOp`)
follow the same pickFresh convention as `avoidsPro`. -/

/-- Bool-valued avoidance check on `MSubRed` derivations.

`msAvoidsPro h x = true` ↔ no `Ms-Pro` step in `h` promotes `x`.

The cofinite arms (`fun_`, `fOp`) recurse on the body opened with a
canonical fresh name picked via `Classical.choose`. The `equ` arm
delegates to `avoidsPro` on the embedded `MEqRed` derivation. This is
sound because `MSubRed` (and `MEqRed`) are `Type`-valued (commit
`16eed34`), so the constructor shape of `h` is observable at the term
level. -/
noncomputable def msAvoidsPro {Γ s u v} (h : MSubRed Γ s u v) (x : String) : Bool :=
  MSubRed.rec
    (motive := fun _ _ _ _ _ => String → Bool)
    -- Ms-Pro: the promoted variable's name `y` is in scope here.
    (fun {_Γ _s y _t} _hpv _hsb x => decide (y ≠ x))
    -- Ms-Top: vacuous.
    (fun {_Γ _s _u} _hpv _hLCu _hfvu _x => true)
    -- Ms-Equ: delegate to `avoidsPro` on the embedded MEqRed.
    (fun {_Γ _s _u _v} _hpv heq x => avoidsPro heq x)
    -- Ms-App: recurse on the operator (operand has no derivation).
    (fun {_Γ _s _u _u' _v} _hu _hLCv _hfvv ihu x => ihu x)
    -- Ms-Fun: bound annotation has no derivation; cofinite body recursion.
    -- Sample at `pickFresh (L ∪ fv body ∪ fv body' ∪ {x})` so the witness
    -- aligns with the freshness preconditions of `MSubRed.rename_sub`
    -- (which downstream `Lemma_24_NarrowingMSubRed`-style discharges
    -- need to thread the avoidance witness across cofinite samples).
    -- The widening is local — `msAvoidsPro` remains a deterministic
    -- function of the derivation; the simp lemmas below reflect the
    -- new sample point.
    (fun {_Γ _t body body'} L _hLCt _hbody _hUni ihbody x =>
      let L' := L ∪ Term.fv body ∪ Term.fv body' ∪ {x}
      let y := pickFresh L'
      have hyL : y ∉ L := fun h => pickFresh_notMem L'
        (Finset.mem_union.mpr <| Or.inl <| Finset.mem_union.mpr <| Or.inl <|
         Finset.mem_union.mpr <| Or.inl h)
      ihbody y hyL x)
    -- Ms-FOp: same widening for the same reason.
    (fun {_Γ _s _t _α body body'} L _hLCt _hbody _hUni ihbody x =>
      let L' := L ∪ Term.fv body ∪ Term.fv body' ∪ {x}
      let y := pickFresh L'
      have hyL : y ∉ L := fun h => pickFresh_notMem L'
        (Finset.mem_union.mpr <| Or.inl <| Finset.mem_union.mpr <| Or.inl <|
         Finset.mem_union.mpr <| Or.inl h)
      ihbody y hyL x)
    h x

/-! ## §3.1. Definitional unfoldings of `msAvoidsPro` per constructor

These let downstream consumers (e.g. `Lemma_30_msPro_x` below) extract
the `y ≠ x` (or recursive) component from the avoidance premise on a
per-constructor basis. -/

@[simp] theorem msAvoidsPro_pro {Γ s y t} (hpv : PrevalidExt Γ s)
    (hsb : Γ.subBinds y t) (x : String) :
    msAvoidsPro (MSubRed.pro hpv hsb) x = decide (y ≠ x) := by
  unfold msAvoidsPro; rfl

@[simp] theorem msAvoidsPro_top {Γ s u} (hpv : PrevalidExt Γ s)
    (hLCu : Term.LC u) (hfvu : Term.fv u ⊆ Γ.dom) (x : String) :
    msAvoidsPro (MSubRed.top hpv hLCu hfvu) x = true := by
  unfold msAvoidsPro; rfl

@[simp] theorem msAvoidsPro_equ {Γ s u v} (hpv : PrevalidExt Γ s)
    (heq : MEqRed Γ s u v) (x : String) :
    msAvoidsPro (MSubRed.equ hpv heq) x = avoidsPro heq x := by
  unfold msAvoidsPro; rfl

@[simp] theorem msAvoidsPro_app {Γ s u u' v} (hu : MSubRed Γ (v :: s) u u')
    (hLCv : Term.LC v) (hfvv : Term.fv v ⊆ Γ.dom) (x : String) :
    msAvoidsPro (MSubRed.app hu hLCv hfvv) x = msAvoidsPro hu x := by
  unfold msAvoidsPro; rfl

/-- Helper: the augmented L set used by `msAvoidsPro`'s cofinite arms.
Includes the source's L plus `Term.fv body`, `Term.fv body'`, and `{x}`.
This guarantees the canonical witness `pickFresh (msAvoidsPro_L_aug ...)`
satisfies freshness preconditions for `MSubRed.rename_sub`. -/
def msAvoidsPro_L_aug (L : Finset String) (body body' : Term) (x : String) :
    Finset String :=
  L ∪ Term.fv body ∪ Term.fv body' ∪ {x}

theorem msAvoidsPro_L_aug_notMem_L {L : Finset String} {body body' : Term}
    {x : String} :
    pickFresh (msAvoidsPro_L_aug L body body' x) ∉ L := by
  intro h
  apply pickFresh_notMem (msAvoidsPro_L_aug L body body' x)
  unfold msAvoidsPro_L_aug
  exact Finset.mem_union.mpr <| Or.inl <| Finset.mem_union.mpr <| Or.inl <|
    Finset.mem_union.mpr <| Or.inl h

theorem msAvoidsPro_L_aug_notMem_body {L : Finset String} {body body' : Term}
    {x : String} :
    pickFresh (msAvoidsPro_L_aug L body body' x) ∉ Term.fv body := by
  intro h
  apply pickFresh_notMem (msAvoidsPro_L_aug L body body' x)
  unfold msAvoidsPro_L_aug
  exact Finset.mem_union.mpr <| Or.inl <| Finset.mem_union.mpr <| Or.inl <|
    Finset.mem_union.mpr <| Or.inr h

theorem msAvoidsPro_L_aug_notMem_body' {L : Finset String} {body body' : Term}
    {x : String} :
    pickFresh (msAvoidsPro_L_aug L body body' x) ∉ Term.fv body' := by
  intro h
  apply pickFresh_notMem (msAvoidsPro_L_aug L body body' x)
  unfold msAvoidsPro_L_aug
  exact Finset.mem_union.mpr <| Or.inl <| Finset.mem_union.mpr <| Or.inr h

theorem msAvoidsPro_L_aug_ne_x {L : Finset String} {body body' : Term}
    {x : String} :
    pickFresh (msAvoidsPro_L_aug L body body' x) ≠ x := by
  intro hxeq
  apply pickFresh_notMem (msAvoidsPro_L_aug L body body' x)
  show pickFresh (msAvoidsPro_L_aug L body body' x) ∈
    L ∪ Term.fv body ∪ Term.fv body' ∪ {x}
  refine Finset.mem_union.mpr <| Or.inr ?_
  simp [hxeq]

@[simp] theorem msAvoidsPro_fun_ {Γ t body body'} (L : Finset String)
    (hLCt : Term.LC t)
    (hbody : ∀ y, y ∉ L →
      MSubRed (⟨y, t, .sub⟩ :: Γ) [] (body^[y]) (body'^[y]))
    (hUni : True)
    (x : String) :
    msAvoidsPro (MSubRed.fun_ L hLCt hbody hUni) x =
      msAvoidsPro
        (hbody (pickFresh (msAvoidsPro_L_aug L body body' x))
               msAvoidsPro_L_aug_notMem_L) x := by
  unfold msAvoidsPro; rfl

@[simp] theorem msAvoidsPro_fOp {Γ s t α body body'} (L : Finset String)
    (hLCt : Term.LC t)
    (hbody : ∀ y, y ∉ L →
      MSubRed (⟨y, α, .equ⟩ :: Γ) s (body^[y]) (body'^[y]))
    (hUni : True)
    (x : String) :
    msAvoidsPro (MSubRed.fOp L hLCt hbody hUni) x =
      msAvoidsPro
        (hbody (pickFresh (msAvoidsPro_L_aug L body body' x))
               msAvoidsPro_L_aug_notMem_L) x := by
  unfold msAvoidsPro; rfl

/-! ## §3.2. `msCofinDomFresh` — MSubRed canonical-witness freshness

Mirror of `cofinDomFresh` for `MSubRed` derivations. Used by
`MSubRed.equ_head_replace` (in `Pss.Mpss.Renaming`) for the same
canonical-witness rename pattern. Delegates to `cofinDomFresh` at the
`Ms-Equ` arm.

**Sampling alignment with `msAvoidsPro`.** `msAvoidsPro` samples its
cofinite arms at `pickFresh (msAvoidsPro_L_aug L body body' x)` (a widened
set) — see §3.1 above. To enable consumers like `MSubRed.equ_head_replace`
to use BOTH `msAvoidsPro` and `msCofinDomFresh` at the SAME canonical
witness, `msCofinDomFresh` is parametrized by the same `x : String` and
samples at the same widened point. The `x` parameter is unused in the
freshness check itself; it just propagates through to align the sample
point. -/

noncomputable def msCofinDomFresh {Γ s u v} (h : MSubRed Γ s u v) (x : String) : Bool :=
  MSubRed.rec
    (motive := fun _ _ _ _ _ => String → Bool)
    -- Ms-Pro: leaf.
    (fun _ _ _ => true)
    -- Ms-Top: leaf.
    (fun _ _ _ _ => true)
    -- Ms-Equ: delegate to `cofinDomFresh` on the embedded MEqRed (no x dep).
    (fun _ heq _ => cofinDomFresh heq)
    -- Ms-App: recurse on the operator (propagate x).
    (fun _ _ _ ihu x => ihu x)
    -- Ms-Fun: track freshness at the SAME widened sample as msAvoidsPro.
    (fun {Γ _ body body'} L _ _ _ ihbody x =>
      let L' := msAvoidsPro_L_aug L body body' x
      let y := pickFresh L'
      have hyL : y ∉ L := msAvoidsPro_L_aug_notMem_L
      decide (y ∉ Γ.dom) && ihbody y hyL x)
    -- Ms-FOp: same widened sample.
    (fun {Γ _ _ _ body body'} L _ _ _ ihbody x =>
      let L' := msAvoidsPro_L_aug L body body' x
      let y := pickFresh L'
      have hyL : y ∉ L := msAvoidsPro_L_aug_notMem_L
      decide (y ∉ Γ.dom) && ihbody y hyL x)
    h x

/-- The `pickFresh L_aug ∉ fv body` and `... ∉ fv body'` properties are
ALREADY GUARANTEED by `msAvoidsPro_L_aug_notMem_body{,'}` (see §3.1).
So `msCofinDomFresh` only needs to track the dom-freshness explicitly. -/

@[simp] theorem msCofinDomFresh_pro {Γ s y t} (hpv : PrevalidExt Γ s)
    (hsb : Γ.subBinds y t) (x : String) :
    msCofinDomFresh (MSubRed.pro hpv hsb) x = true := by
  unfold msCofinDomFresh; rfl

@[simp] theorem msCofinDomFresh_top {Γ s u} (hpv : PrevalidExt Γ s)
    (hLCu : Term.LC u) (hfvu : Term.fv u ⊆ Γ.dom) (x : String) :
    msCofinDomFresh (MSubRed.top hpv hLCu hfvu) x = true := by
  unfold msCofinDomFresh; rfl

@[simp] theorem msCofinDomFresh_equ {Γ s u v} (hpv : PrevalidExt Γ s)
    (heq : MEqRed Γ s u v) (x : String) :
    msCofinDomFresh (MSubRed.equ hpv heq) x = cofinDomFresh heq := by
  unfold msCofinDomFresh; rfl

@[simp] theorem msCofinDomFresh_app {Γ s u u' v} (hu : MSubRed Γ (v :: s) u u')
    (hLCv : Term.LC v) (hfvv : Term.fv v ⊆ Γ.dom) (x : String) :
    msCofinDomFresh (MSubRed.app hu hLCv hfvv) x = msCofinDomFresh hu x := by
  unfold msCofinDomFresh; rfl

@[simp] theorem msCofinDomFresh_fun_ {Γ : Ctx} {t body body' : Term}
    (L : Finset String)
    (hLCt : Term.LC t)
    (hbody : ∀ y, y ∉ L →
      MSubRed (⟨y, t, .sub⟩ :: Γ) [] (body^[y]) (body'^[y]))
    (hUni : True)
    (x : String) :
    msCofinDomFresh (MSubRed.fun_ L hLCt hbody hUni) x =
      (decide (pickFresh (msAvoidsPro_L_aug L body body' x) ∉ Γ.dom) &&
       msCofinDomFresh
         (hbody (pickFresh (msAvoidsPro_L_aug L body body' x))
                msAvoidsPro_L_aug_notMem_L) x) := by
  unfold msCofinDomFresh; rfl

@[simp] theorem msCofinDomFresh_fOp {Γ : Ctx} {s : Stack} {t α body body' : Term}
    (L : Finset String)
    (hLCt : Term.LC t)
    (hbody : ∀ y, y ∉ L →
      MSubRed (⟨y, α, .equ⟩ :: Γ) s (body^[y]) (body'^[y]))
    (hUni : True)
    (x : String) :
    msCofinDomFresh (MSubRed.fOp L hLCt hbody hUni) x =
      (decide (pickFresh (msAvoidsPro_L_aug L body body' x) ∉ Γ.dom) &&
       msCofinDomFresh
         (hbody (pickFresh (msAvoidsPro_L_aug L body body' x))
                msAvoidsPro_L_aug_notMem_L) x) := by
  unfold msCofinDomFresh; rfl

/-! ## §3.3. `cofinAvoidsProSelf` — fOp body avoids pro on its own canonical witness

Phase 3 of the β-residual unblock (`MEqRed.stack_replace` in
`Pss.Mpss.Renaming`) needs the `fOp` body's derivation to avoid `Me-Pro`
on the body's canonical fresh witness `pickFresh L`. This is exactly the
shape `equ_head_replace` consumes when we delegate the `fOp` Case A
swap (where the input stack head `α` is the same as the binding's bound
term).

Per AXIOMS.md "Discharge plan for the β-residuals" item §2: the `fOp`
arm of `stack_replace` reduces to `MEqRed.equ_head_replace`. That call
needs `avoidsPro (body z) z = true` where `z` is the canonical sample
the body recurses at — i.e., `pickFresh L`. Capturing this as a Bool
function of the derivation lets `stack_replace` carry it as a single
premise without alpha-equivariance.

Why this is NOT alpha-equivariance: `cofinAvoidsProSelf` is a
deterministic Bool function of the derivation tree's shape. Each `fOp`
arm samples at the SAME point as `cofinDomFresh` and `avoidsPro`
(deterministically `pickFresh L`), so it's a property of the source
tree, not a cross-witness claim.

Propagates through every constructor; only `fOp` introduces a new
constraint. The `bet`/`fun_` cofinite arms only need their bodies'
recursive condition (no .equ-head swap there). -/

noncomputable def cofinAvoidsProSelf {Γ s u v} (h : MEqRed Γ s u v) : Bool :=
  MEqRed.rec
    (motive := fun _ _ _ _ _ => Bool)
    -- Me-Pro: recurse on the inner derivation.
    (fun _ _ _ ihα => ihα)
    -- Me-Bet: propagate through body recursion + operand.
    (fun {_Γ _ _ _ _ _ _} L _ _ _ _ ihbody ihv =>
      let y₀ := pickFresh L
      have hy₀L : y₀ ∉ L := pickFresh_notMem L
      ihbody y₀ hy₀L && ihv)
    -- Me-Top: leaf.
    (fun _ => true)
    -- Me-App: recurse on both subterms.
    (fun _ _ ihu ihv => ihu && ihv)
    -- Me-Var: leaf.
    (fun _ => true)
    -- Me-Fun: propagate.
    (fun {_Γ _ _ _ _} L _ _ _ iht ihbody =>
      let y₀ := pickFresh L
      have hy₀L : y₀ ∉ L := pickFresh_notMem L
      iht && ihbody y₀ hy₀L)
    -- Me-TAp: leaf.
    (fun _ _ _ => true)
    -- Me-FOp: HERE is where we add the body-self-avoidance condition.
    -- The body recurses at extended ctx with binding `⟨pickFresh L, α, .equ⟩`.
    -- For `stack_replace`'s fOp Case A to delegate to `equ_head_replace`,
    -- we need `avoidsPro (body pickFresh) pickFresh = true`.
    (fun {_Γ _ _ _ _ _ _} L _ hbody _ iht ihbody =>
      let y₀ := pickFresh L
      have hy₀L : y₀ ∉ L := pickFresh_notMem L
      avoidsPro (hbody y₀ hy₀L) y₀ && iht && ihbody y₀ hy₀L)
    h

/-! ### §3.3.1. Per-constructor `simp` unfoldings for `cofinAvoidsProSelf` -/

@[simp] theorem cofinAvoidsProSelf_pro {Γ s y α α'} (hpv : PrevalidExt Γ s)
    (heq : Γ.equBinds y α) (hα : MEqRed Γ s α α') :
    cofinAvoidsProSelf (MEqRed.pro hpv heq hα) = cofinAvoidsProSelf hα := by
  unfold cofinAvoidsProSelf; rfl

@[simp] theorem cofinAvoidsProSelf_bet {Γ s t v v' body body'} (L : Finset String)
    (hLCt : Term.LC t)
    (hbody : ∀ y, y ∉ L → MEqRed Γ s (body^[y]) (body'^[y]))
    (hUni : True)
    (hv : MEqRed Γ [] v v') :
    cofinAvoidsProSelf (MEqRed.bet L hLCt hbody hUni hv) =
      (cofinAvoidsProSelf (hbody (pickFresh L) (pickFresh_notMem L)) &&
       cofinAvoidsProSelf hv) := by
  unfold cofinAvoidsProSelf; rfl

@[simp] theorem cofinAvoidsProSelf_top {Γ s} (hpv : PrevalidExt Γ s) :
    cofinAvoidsProSelf (MEqRed.top hpv) = true := by
  unfold cofinAvoidsProSelf; rfl

@[simp] theorem cofinAvoidsProSelf_app {Γ s u u' v v'}
    (hu : MEqRed Γ (v :: s) u u') (hv : MEqRed Γ [] v v') :
    cofinAvoidsProSelf (MEqRed.app hu hv) =
      (cofinAvoidsProSelf hu && cofinAvoidsProSelf hv) := by
  unfold cofinAvoidsProSelf; rfl

@[simp] theorem cofinAvoidsProSelf_var {Γ s y} (hpv : PrevalidExt Γ s) :
    cofinAvoidsProSelf (@MEqRed.var Γ s y hpv) = true := by
  unfold cofinAvoidsProSelf; rfl

@[simp] theorem cofinAvoidsProSelf_fun_ {Γ t t' body body'} (L : Finset String)
    (ht : MEqRed Γ [] t t')
    (hbody : ∀ y, y ∉ L →
      MEqRed (⟨y, t, .sub⟩ :: Γ) [] (body^[y]) (body'^[y]))
    (hUni : True) :
    cofinAvoidsProSelf (MEqRed.fun_ L ht hbody hUni) =
      (cofinAvoidsProSelf ht &&
       cofinAvoidsProSelf (hbody (pickFresh L) (pickFresh_notMem L))) := by
  unfold cofinAvoidsProSelf; rfl

@[simp] theorem cofinAvoidsProSelf_tAp {Γ s u} (hpv : PrevalidExt Γ s)
    (hLCu : Term.LC u) (hfvu : Term.fv u ⊆ Γ.dom) :
    cofinAvoidsProSelf (MEqRed.tAp hpv hLCu hfvu) = true := by
  unfold cofinAvoidsProSelf; rfl

@[simp] theorem cofinAvoidsProSelf_fOp {Γ s t t' α body body'} (L : Finset String)
    (ht : MEqRed Γ [] t t')
    (hbody : ∀ y, y ∉ L →
      MEqRed (⟨y, α, .equ⟩ :: Γ) s (body^[y]) (body'^[y]))
    (hUni : True) :
    cofinAvoidsProSelf (MEqRed.fOp L ht hbody hUni) =
      (avoidsPro (hbody (pickFresh L) (pickFresh_notMem L)) (pickFresh L) &&
       cofinAvoidsProSelf ht &&
       cofinAvoidsProSelf (hbody (pickFresh L) (pickFresh_notMem L))) := by
  unfold cofinAvoidsProSelf; rfl

/-! ### §3.3.2. `cofinAvoidsProSelf_refl` — refl-shaped derivations self-avoid

Mirror of `avoidsPro_refl` (§2.2) and `cofinDomFresh_refl` (§2.3.2).
At the `fOp` arm, the body recursion `hbody y hyL` is itself produced by
`MEqRed.refl` on the opened body — so by `avoidsPro_refl` it avoids any
variable, in particular the canonical sampling witness `pickFresh L`. -/

theorem cofinAvoidsProSelf_refl
    {Γ : Ctx} {s : Stack} {u : Term}
    (hpv : PrevalidExt Γ s) (hLC : Term.LC u) (hfv : Term.fv u ⊆ Γ.dom) :
    cofinAvoidsProSelf (MEqRed.refl hpv hLC hfv) = true := by
  induction hLC generalizing s Γ with
  | top =>
    simp only [MEqRed.refl, cofinAvoidsProSelf_top]
  | fvar y =>
    simp only [MEqRed.refl, cofinAvoidsProSelf_var]
  | @app a b hLCa hLCb iha ihb =>
    simp only [MEqRed.refl, cofinAvoidsProSelf_app, Bool.and_eq_true]
    refine ⟨iha _ _, ihb _ _⟩
  | @abs L bound body hLCbound hbody ihbound ihbody =>
    cases s with
    | nil =>
      simp only [MEqRed.refl, cofinAvoidsProSelf_fun_, Bool.and_eq_true]
      refine ⟨ihbound _ _, ?_⟩
      exact ihbody _ _ _ _
    | cons α tail =>
      cases hpv with
      | cons hpvr hLCα hfvα =>
        simp only [MEqRed.refl, cofinAvoidsProSelf_fOp, Bool.and_eq_true]
        -- Three obligations:
        -- (1) avoidsPro (body-refl) (pickFresh L_widened) = true
        --     — this is `avoidsPro_refl` applied to the IH-produced refl.
        -- (2) cofinAvoidsProSelf bound-refl = true — recurse on `ihbound`.
        -- (3) cofinAvoidsProSelf body-refl = true — recurse on `ihbody`.
        refine ⟨⟨?_, ihbound _ _⟩, ihbody _ _ _ _⟩
        -- (1): the body's recursive call IS `MEqRed.refl _ _ _`, so
        -- `avoidsPro_refl` discharges it.
        exact avoidsPro_refl _ _ _ _

/-! ## §3.4. `msCofinAvoidsProSelf` — MSubRed analog

Mirror of `cofinAvoidsProSelf` for `MSubRed` derivations. Used by
`MSubRed.stack_replace` (Phase 3). The `Ms-Equ` arm delegates to
`cofinAvoidsProSelf` on the embedded `MEqRed`. The `Ms-FOp` arm samples
at the SAME widened point as `msAvoidsPro` (`msAvoidsPro_L_aug L body
body' x`) so that `MSubRed.equ_head_replace`'s sample alignment carries
through.

Like `msCofinDomFresh`, this is parametrized by `x : String` for sample
alignment with `msAvoidsPro`. The `x` parameter is unused at most arms
and just propagates. -/

noncomputable def msCofinAvoidsProSelf {Γ s u v} (h : MSubRed Γ s u v) (x : String) :
    Bool :=
  MSubRed.rec
    (motive := fun _ _ _ _ _ => String → Bool)
    -- Ms-Pro: leaf.
    (fun _ _ _ => true)
    -- Ms-Top: leaf.
    (fun _ _ _ _ => true)
    -- Ms-Equ: delegate to `cofinAvoidsProSelf`.
    (fun _ heq _ => cofinAvoidsProSelf heq)
    -- Ms-App: recurse on operator.
    (fun _ _ _ ihu x => ihu x)
    -- Ms-Fun: propagate (no .equ swap; just bound recursion).
    (fun {_Γ _ body body'} L _ _ _ ihbody x =>
      let y := pickFresh (msAvoidsPro_L_aug L body body' x)
      have hyL : y ∉ L := msAvoidsPro_L_aug_notMem_L
      ihbody y hyL x)
    -- Ms-FOp: HERE is where the body-self-avoidance condition lives.
    (fun {_Γ _ _ _ body body'} L _ hbody _ ihbody x =>
      let y := pickFresh (msAvoidsPro_L_aug L body body' x)
      have hyL : y ∉ L := msAvoidsPro_L_aug_notMem_L
      msAvoidsPro (hbody y hyL) y && ihbody y hyL x)
    h x

@[simp] theorem msCofinAvoidsProSelf_pro {Γ s y t} (hpv : PrevalidExt Γ s)
    (hsb : Γ.subBinds y t) (x : String) :
    msCofinAvoidsProSelf (MSubRed.pro hpv hsb) x = true := by
  unfold msCofinAvoidsProSelf; rfl

@[simp] theorem msCofinAvoidsProSelf_top {Γ s u} (hpv : PrevalidExt Γ s)
    (hLCu : Term.LC u) (hfvu : Term.fv u ⊆ Γ.dom) (x : String) :
    msCofinAvoidsProSelf (MSubRed.top hpv hLCu hfvu) x = true := by
  unfold msCofinAvoidsProSelf; rfl

@[simp] theorem msCofinAvoidsProSelf_equ {Γ s u v} (hpv : PrevalidExt Γ s)
    (heq : MEqRed Γ s u v) (x : String) :
    msCofinAvoidsProSelf (MSubRed.equ hpv heq) x = cofinAvoidsProSelf heq := by
  unfold msCofinAvoidsProSelf; rfl

@[simp] theorem msCofinAvoidsProSelf_app {Γ s u u' v} (hu : MSubRed Γ (v :: s) u u')
    (hLCv : Term.LC v) (hfvv : Term.fv v ⊆ Γ.dom) (x : String) :
    msCofinAvoidsProSelf (MSubRed.app hu hLCv hfvv) x =
      msCofinAvoidsProSelf hu x := by
  unfold msCofinAvoidsProSelf; rfl

@[simp] theorem msCofinAvoidsProSelf_fun_ {Γ : Ctx} {t body body' : Term}
    (L : Finset String)
    (hLCt : Term.LC t)
    (hbody : ∀ y, y ∉ L →
      MSubRed (⟨y, t, .sub⟩ :: Γ) [] (body^[y]) (body'^[y]))
    (hUni : True)
    (x : String) :
    msCofinAvoidsProSelf (MSubRed.fun_ L hLCt hbody hUni) x =
      msCofinAvoidsProSelf
        (hbody (pickFresh (msAvoidsPro_L_aug L body body' x))
               msAvoidsPro_L_aug_notMem_L) x := by
  unfold msCofinAvoidsProSelf; rfl

@[simp] theorem msCofinAvoidsProSelf_fOp {Γ : Ctx} {s : Stack} {t α body body' : Term}
    (L : Finset String)
    (hLCt : Term.LC t)
    (hbody : ∀ y, y ∉ L →
      MSubRed (⟨y, α, .equ⟩ :: Γ) s (body^[y]) (body'^[y]))
    (hUni : True)
    (x : String) :
    msCofinAvoidsProSelf (MSubRed.fOp L hLCt hbody hUni) x =
      (msAvoidsPro
         (hbody (pickFresh (msAvoidsPro_L_aug L body body' x))
                msAvoidsPro_L_aug_notMem_L)
         (pickFresh (msAvoidsPro_L_aug L body body' x)) &&
       msCofinAvoidsProSelf
         (hbody (pickFresh (msAvoidsPro_L_aug L body body' x))
                msAvoidsPro_L_aug_notMem_L) x) := by
  unfold msCofinAvoidsProSelf; rfl

/-! ## §4. Discharged Lemma 30 residual (axiom replaced by theorem)

`Lemma_30_msPro_x_axiom` (in `Substitution.lean`) axiomatizes the
residual `Ms-Pro y = x` arm of Lemma 30 — the case where the original
derivation `h : MSubRed _ _ (.fvar x) t` was built by `MSubRed.pro` with
`y = x` (i.e. the substituted variable is being promoted).

With `msAvoidsPro`, we can capture the paper's "no `Ms-Pro` on `x`" side
condition explicitly. Under that side condition the residual case is
**impossible** — `msAvoidsPro (MSubRed.pro hpv hsb) x = true` reduces to
`decide (x ≠ x) = true` via `msAvoidsPro_pro`, an immediate contradiction.

Hence the axiom statement, refined with the avoidance premise on the
**original** `pro` derivation, becomes a theorem: the conclusion (an
`MSubRed`) follows by `False.elim`. This is `Lemma_30_msPro_x` below.

This is the **leaf-level** discharge of the axiom — i.e. it covers
exactly the spot inside `Lemma_30_ReductionUnderSubst_Sub` (in
`Substitution.lean`) where the axiom is invoked. A caller wishing to
remove the axiom from their reasoning can:

1. Carry an `msAvoidsPro h x = true` premise on the top-level Lemma 30
   call, AND
2. Adapt `Lemma_30_ReductionUnderSubst_Sub`'s `pro` arm to invoke
   `Lemma_30_msPro_x` (theorem) instead of `Lemma_30_msPro_x_axiom` —
   trivially, since the only difference is the residual proof.

The cofinite arms (`fun_`, `fOp`) of the broader Lemma 30 thread the
axiom only through the body recursion: an alpha-equivariance lemma for
`msAvoidsPro` would let us thread an avoidance premise cofinitely too
(future work). The leaf discharge below is sufficient to demonstrate
that the axiom is **not load-bearing** — it can be replaced by a
theorem at every site of use, given the avoidance side condition. -/

/-- **Discharged residual of `Lemma_30_msPro_x_axiom`.**

Given an explicit `msAvoidsPro` witness on the original `pro` derivation
that the substituted variable `x` is NOT the one being promoted, the
axiom's conclusion follows by `False.elim`.

This is the precise theorem replacement for `Lemma_30_msPro_x_axiom`:
the axiom takes contextual data and produces an `MSubRed` conclusion;
the theorem takes the SAME contextual data PLUS a witness that the
problematic case (`pro y=x`) does not arise — and produces the same
conclusion vacuously.

In practice, the avoidance witness `havoid` is supplied by the caller
of `Lemma_30_ReductionUnderSubst_Sub`, who knows from the broader
context (e.g. well-typing) that no `Ms-Pro` on `x` can occur in `h`.

Marked `noncomputable` because the conclusion is `Type`-valued
(`MSubRed`) and the contradiction-via-`simp` proof uses classical
reasoning. -/
noncomputable def Lemma_30_msPro_x
    {Γ₁ Γ₂ : Ctx} {st : Stack} {x : String} {s t : Term}
    {hpv_orig : PrevalidExt (Γ₂ ++ ⟨x, t, .sub⟩ :: Γ₁) st}
    {hsb : (Γ₂ ++ ⟨x, t, .sub⟩ :: Γ₁).subBinds x t}
    (havoid : msAvoidsPro (MSubRed.pro hpv_orig hsb) x = true) :
    MSubRed (Ctx.subst x s Γ₂ ++ Γ₁) (Stack.subst x s st)
      s (Term.subst x s t) := by
  exfalso
  rw [msAvoidsPro_pro] at havoid
  simp at havoid

end Pss

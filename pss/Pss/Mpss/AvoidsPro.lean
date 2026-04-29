import Pss.Mpss.Substitution

/-! # `Pss.Mpss.AvoidsPro` — the `MEqRedAvoidsPro` predicate

Pasquale & García-Pérez 2024 (CSL 2026), §3 (the "moreover" clause of
Lemma 2's statement and its propagation in proofs that consume
Lemma 2 across `↣*` evolutions).

This module hoists the `MEqRedAvoidsPro` predicate (and its supporting
scope-preservation / proof-irrelevance lemmas) **below** `Pss.Mpss.Weakening`
so that the weakening machinery can take `MEqRedAvoidsPro` premises in
its lift theorems for `ExtCtxRed`. This is the architectural fix that
unblocks the discharge of the previous `Lemma_2_DiamondMEqRed_ctx_axiom`
(see `Pss/Mpss/Diamond.lean` for the consumer).

## What lives here

* `MEqRedAvoidsPro` — the inductive "no `Me-Pro` on `x`" predicate on
  `MEqRed` derivations. One constructor per `MEqRed` constructor; the
  `pro` constructor carries the side condition `y ≠ x`.
* `fv_subset_open_fvar` — opening with a fresh fvar only adds names.
* `MEqRed_fv_subset` — `fv` of the destination is bounded by `fv` of
  the source plus `Γ.dom`.
* `MEqRed_fv_preserve` — `MEqRed` preserves `fv ⊆ Γ.dom`.
* `MEqRedAvoidsPro_refl` — every `MEqRed.refl` derivation avoids `Me-Pro`
  on every variable.
* `MEqRedAvoidsPro_proInv_propagate` — propagating avoidance across a
  re-witnessing of the `PrevalidExt` premise of a `Me-Pro` step.

## Why `Substitution` is allowed

The helper `MEqRedAvoidsPro_refl` constructs a witness mirroring
`MEqRed.refl` (which lives in `Pss.Mpss.Substitution`). `Substitution`
imports only `Pss.Mpss.ContextRed`, NOT `Weakening`, so importing it
here does NOT create a cycle with the downstream `Weakening` consumer.
The architectural constraint is "AvoidsPro must NOT pull in Weakening",
which is preserved.

## Naming / visibility

The 5 helper theorems were originally `private` in `Diamond.lean`. They
are promoted to **public** here so `Weakening.lean` (the downstream
consumer) can call them when discharging the lift theorems for
`ExtCtxRed`. The originals were never used outside the namespace, so
this widening is benign.
-/

namespace Pss

/-! ## §1. The "no Me-Pro on `x`" predicate

Defined as an inductive predicate (Approach A from the original Diamond
plan, with the inductive flavour of formulation, since the cofinitely-
quantified body cases of `bet`/`fun_`/`fOp` make a `def`-by-recursion
form awkward to state cleanly). -/

/-- Predicate on `MEqRed` derivations: the derivation does NOT contain
an application of `Me-Pro` that promotes the named variable `x`.

The predicate has one constructor per `MEqRed` constructor; the `pro`
constructor is the only one with non-trivial side condition (`y ≠ x`),
and it propagates the predicate to its operand sub-derivation. All other
constructors propagate the predicate structurally to all sub-derivations
(including the cofinitely-quantified body sub-derivations, which must
satisfy the predicate uniformly over the `y ∉ L` witnesses). -/
inductive MEqRedAvoidsPro (x : String) :
    ∀ {Γ : Ctx} {s : Stack} {u v : Term}, MEqRed Γ s u v → Prop where
  /-- `Me-Pro` on `y ≠ x`, with the operand sub-derivation also avoiding
  promotion of `x`. -/
  | pro {Γ s y α α'}
        (hpv : PrevalidExt Γ s)
        (heq : Γ.equBinds y α)
        (hα : MEqRed Γ s α α')
        (hyx : y ≠ x)
        (hAv : MEqRedAvoidsPro x hα) :
      MEqRedAvoidsPro x (MEqRed.pro hpv heq hα)
  /-- `Me-Bet` with both body and operand sub-derivations avoiding `x`. -/
  | bet {Γ s t v v' body body'} {L : Finset String}
        (hLCt : Term.LC t)
        (hbody : ∀ y, y ∉ L → MEqRed Γ s (body^[y]) (body'^[y]))
        (hv : MEqRed Γ [] v v')
        (hAvBody : ∀ y (hy : y ∉ L), MEqRedAvoidsPro x (hbody y hy))
        (hAvV : MEqRedAvoidsPro x hv) :
      MEqRedAvoidsPro x (MEqRed.bet (L := L) hLCt hbody hv)
  /-- `Me-Top` is always fine. -/
  | top {Γ s} (hpv : PrevalidExt Γ s) :
      MEqRedAvoidsPro x (MEqRed.top hpv)
  /-- `Me-App` with both operator and operand sub-derivations avoiding `x`. -/
  | app {Γ s u u' v v'}
        (hu : MEqRed Γ (v :: s) u u')
        (hv : MEqRed Γ [] v v')
        (hAvU : MEqRedAvoidsPro x hu)
        (hAvV : MEqRedAvoidsPro x hv) :
      MEqRedAvoidsPro x (MEqRed.app hu hv)
  /-- `Me-Var` is always fine. -/
  | var {Γ s y} (hpv : PrevalidExt Γ s) :
      MEqRedAvoidsPro x (MEqRed.var (x := y) hpv)
  /-- `Me-Fun` with both bound-annotation and body sub-derivations avoiding `x`. -/
  | fun_ {Γ t t' body body'} {L : Finset String}
        (ht : MEqRed Γ [] t t')
        (hbody : ∀ y, y ∉ L →
          MEqRed (⟨y, t, .sub⟩ :: Γ) [] (body^[y]) (body'^[y]))
        (hAvT : MEqRedAvoidsPro x ht)
        (hAvBody : ∀ y (hy : y ∉ L), MEqRedAvoidsPro x (hbody y hy)) :
      MEqRedAvoidsPro x (MEqRed.fun_ (L := L) ht hbody)
  /-- `Me-TAp` is always fine. -/
  | tAp {Γ s u}
        (hpv : PrevalidExt Γ s) (hLC : Term.LC u) (hfv : Term.fv u ⊆ Γ.dom) :
      MEqRedAvoidsPro x (MEqRed.tAp hpv hLC hfv)
  /-- `Me-FOp` with both bound-annotation and body sub-derivations avoiding `x`. -/
  | fOp {Γ s t t' α body body'} {L : Finset String}
        (ht : MEqRed Γ [] t t')
        (hbody : ∀ y, y ∉ L →
          MEqRed (⟨y, α, .equ⟩ :: Γ) s (body^[y]) (body'^[y]))
        (hAvT : MEqRedAvoidsPro x ht)
        (hAvBody : ∀ y (hy : y ∉ L), MEqRedAvoidsPro x (hbody y hy)) :
      MEqRedAvoidsPro x (MEqRed.fOp (L := L) ht hbody)

/-! ## §2. Auxiliary scope-preservation helpers -/

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
  | @bet Γ s t v0 v0' body body' L hLCt hbody hv ihbody ihv =>
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
  | @fun_ Γ t t' body body' L ht hbody iht ihbody =>
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
  | @fOp Γ s t t' αHd body body' L ht hbody iht ihbody =>
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

/-- Every closing derivation produced by `MEqRed.refl` avoids `Me-Pro`
on every variable, since the only constructors `MEqRed.refl` invokes
are `var`/`top`/`app`/`fun_`/`fOp`/`tAp` — never `Me-Pro`.

The proof relies on Lean 4's proof irrelevance: since `MEqRed Γ s u u`
is in `Prop`, any two proofs of it are definitionally equal, so the
type `MEqRedAvoidsPro x (MEqRed.refl hpv hLC hfv)` is definitionally
equal to `MEqRedAvoidsPro x h` for any `h : MEqRed Γ s u u`. We
construct an explicit derivation `h_av` mirroring `MEqRed.refl`'s
structure and prove `MEqRedAvoidsPro x h_av` directly; the proof
re-types to the desired statement by proof irrelevance. -/
theorem MEqRedAvoidsPro_refl (x : String) {Γ : Ctx} {s : Stack} {u : Term}
    (hpv : PrevalidExt Γ s) (hLC : Term.LC u) (hfv : Term.fv u ⊆ Γ.dom) :
    MEqRedAvoidsPro x (MEqRed.refl hpv hLC hfv) := by
  suffices h : ∃ (h_av : MEqRed Γ s u u), MEqRedAvoidsPro x h_av by
    obtain ⟨h_av, hAv⟩ := h
    have heq : h_av = MEqRed.refl hpv hLC hfv := rfl
    rw [← heq]; exact hAv
  suffices hGen : ∀ (Γ : Ctx) (s : Stack),
      PrevalidExt Γ s → Term.fv u ⊆ Γ.dom →
        ∃ (h_av : MEqRed Γ s u u), MEqRedAvoidsPro x h_av by
    exact hGen Γ s hpv hfv
  clear hpv hfv Γ s
  intro Γ s
  induction hLC generalizing Γ s with
  | top =>
    intro hpv hfv
    exact ⟨MEqRed.top hpv, .top hpv⟩
  | fvar y =>
    intro hpv hfv
    exact ⟨MEqRed.var hpv, .var hpv⟩
  | @app a b hLCa hLCb iha ihb =>
    intro hpv hfv
    have hfa : Term.fv a ⊆ Γ.dom := by
      intro z hz; exact hfv (by simp [Term.fv]; exact Or.inl hz)
    have hfb : Term.fv b ⊆ Γ.dom := by
      intro z hz; exact hfv (by simp [Term.fv]; exact Or.inr hz)
    have hpvb : PrevalidExt Γ (b :: s) := PrevalidExt.cons hpv hLCb hfb
    have hpvnil : PrevalidExt Γ [] := PrevalidExt.nil (extractPrevalid hpv)
    obtain ⟨ha_av, hAvA⟩ := iha Γ (b :: s) hpvb hfa
    obtain ⟨hb_av, hAvB⟩ := ihb Γ [] hpvnil hfb
    exact ⟨MEqRed.app ha_av hb_av, .app ha_av hb_av hAvA hAvB⟩
  | @abs L bound body hLCbound hbody ihbound ihbody =>
    intro hpv hfv
    have hpvnil : PrevalidExt Γ [] := PrevalidExt.nil (extractPrevalid hpv)
    have hfb : Term.fv bound ⊆ Γ.dom := by
      intro z hz; exact hfv (by simp [Term.fv]; exact Or.inl hz)
    have hfbody : Term.fv body ⊆ Γ.dom := by
      intro z hz; exact hfv (by simp [Term.fv]; exact Or.inr hz)
    obtain ⟨hb_av, hAvB⟩ := ihbound Γ [] hpvnil hfb
    cases s with
    | nil =>
      let L' := L ∪ Γ.dom
      have hbody_av_pkg : ∀ y, y ∉ L' →
          ∃ (h_av : MEqRed (⟨y, bound, .sub⟩ :: Γ) [] (body^[y]) (body^[y])),
              MEqRedAvoidsPro x h_av := by
        intro y hy
        have hyL : y ∉ L := fun h => hy (Finset.mem_union.mpr (Or.inl h))
        have hyΓ : y ∉ Γ.dom := fun h => hy (Finset.mem_union.mpr (Or.inr h))
        have hpvy : Prevalid (⟨y, bound, .sub⟩ :: Γ) :=
          Prevalid.sub (extractPrevalid hpv) hyΓ hfb hLCbound
        have hpvey : PrevalidExt (⟨y, bound, .sub⟩ :: Γ) [] := PrevalidExt.nil hpvy
        have hfvy : Term.fv (body^[y]) ⊆ Ctx.dom (⟨y, bound, .sub⟩ :: Γ) := by
          intro z hz
          have hsub := Term.fv_open_subset 0 (.fvar y) body
          have hmem : z ∈ Term.fv body ∪ Term.fv (.fvar y) := hsub hz
          rw [Ctx.dom_cons]
          rcases Finset.mem_union.mp hmem with h | h
          · exact Finset.mem_insert_of_mem (hfbody h)
          · have hzy : z = y := by simpa [Term.fv] using h
            subst hzy; exact Finset.mem_insert_self _ _
        exact ihbody y hyL (⟨y, bound, .sub⟩ :: Γ) [] hpvey hfvy
      classical
      refine ⟨MEqRed.fun_ (L := L') hb_av (fun y hy => (hbody_av_pkg y hy).choose), ?_⟩
      exact .fun_ hb_av _ hAvB (fun y hy => (hbody_av_pkg y hy).choose_spec)
    | cons α tail =>
      cases hpv with
      | cons hpvr hLCα hfvα =>
        let L' := L ∪ Γ.dom
        have hbody_av_pkg : ∀ y, y ∉ L' →
            ∃ (h_av : MEqRed (⟨y, α, .equ⟩ :: Γ) tail (body^[y]) (body^[y])),
                MEqRedAvoidsPro x h_av := by
          intro y hy
          have hyL : y ∉ L := fun h => hy (Finset.mem_union.mpr (Or.inl h))
          have hyΓ : y ∉ Γ.dom := fun h => hy (Finset.mem_union.mpr (Or.inr h))
          have hpvy : Prevalid (⟨y, α, .equ⟩ :: Γ) :=
            Prevalid.equ (extractPrevalid hpvr) hyΓ hfvα hLCα
          have hpvey : PrevalidExt (⟨y, α, .equ⟩ :: Γ) tail := by
            have aux : ∀ {st : Stack}, PrevalidExt Γ st →
                PrevalidExt (⟨y, α, .equ⟩ :: Γ) st := by
              intro st hst
              induction hst with
              | nil _ => exact PrevalidExt.nil hpvy
              | @cons _ β hpvE hLCβ hfvβ ih =>
                refine PrevalidExt.cons ih hLCβ ?_
                intro z hz
                have hzΓ : z ∈ Γ.dom := hfvβ hz
                show z ∈ Ctx.dom (⟨y, α, .equ⟩ :: Γ)
                rw [Ctx.dom_cons]
                exact Finset.mem_insert_of_mem hzΓ
            exact aux hpvr
          have hfvy : Term.fv (body^[y]) ⊆ Ctx.dom (⟨y, α, .equ⟩ :: Γ) := by
            intro z hz
            have hsub := Term.fv_open_subset 0 (.fvar y) body
            have hmem : z ∈ Term.fv body ∪ Term.fv (.fvar y) := hsub hz
            rw [Ctx.dom_cons]
            rcases Finset.mem_union.mp hmem with h | h
            · exact Finset.mem_insert_of_mem (hfbody h)
            · have hzy : z = y := by simpa [Term.fv] using h
              subst hzy; exact Finset.mem_insert_self _ _
          exact ihbody y hyL (⟨y, α, .equ⟩ :: Γ) tail hpvey hfvy
        classical
        refine ⟨MEqRed.fOp (L := L') hb_av (fun y hy => (hbody_av_pkg y hy).choose), ?_⟩
        exact .fOp hb_av _ hAvB (fun y hy => (hbody_av_pkg y hy).choose_spec)

/-- Helper: avoidance under `Me-Pro` propagates across changing the
`PrevalidExt` witness. If `pro hpv₁ heq hα` avoids `x`, then any other
`pro hpv₂ heq hα` (with the same `heq` and `hα`) also avoids `x`.

Provable by Lean 4's proof irrelevance: the two derivations are
definitionally equal as terms, so `MEqRedAvoidsPro x` of one is the
same proposition as `MEqRedAvoidsPro x` of the other. -/
theorem MEqRedAvoidsPro_proInv_propagate
    (x : String) {Γ : Ctx} {s : Stack} {y : String} {α α' : Term}
    (hpv₁ : PrevalidExt Γ s) (heq : Γ.equBinds y α) (hα : MEqRed Γ s α α')
    (hpv₂ : PrevalidExt Γ s)
    (hAv : MEqRedAvoidsPro x (MEqRed.pro hpv₁ heq hα)) :
    MEqRedAvoidsPro x (MEqRed.pro hpv₂ heq hα) := by
  exact hAv

end Pss

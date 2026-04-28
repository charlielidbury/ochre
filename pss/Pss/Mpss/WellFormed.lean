import Pss.Mpss.Weakening

set_option linter.unusedVariables false

/-! # `Pss.Mpss.WellFormed` — MPSS well-formedness, well-subtyping, transitive
well-subtyping

Pasquale & García-Pérez 2024 (CSL 2026), Figure 4. Three judgments:

* `WfM Γ t`         — `Γ ⊢ t wf`         (term well-formedness; 5 rules)
* `WSubM Γ t u`     — `Γ ⊢ t ≤_wf u`     (well-subtyping; 4 rules)
* `WSubMStar Γ t u` — `Γ ⊢ t ≤*_wf u`    (transitive well-subtyping; 2 rules)

The three are mutually inductive:

* `WfM` references `WSubMStar` (in `Wf-App`).
* `WSubM` references `WfM` (in `Ws-Rfl`, `Ws-Lf2`).
* `WSubMStar` references `WfM` and `WSubM` (in `Ws-Sub`, `Ws-Trs`).

We mechanize ONLY the `≤_wf` instance of the paper's `◁_wf` meta-judgment.
The `≡_wf` variant is not used by `WfM` and is out of scope here; this
also means Lemmas 15/16 (which are about `≡_wf`) are not mechanized.

## Wave 4A bridge axioms

The `MEqRed.toScoped` / `MSubRed.toScoped` axioms in `Pss.Mpss.Weakening`
were investigated. The discharge requires a refactor of `MEqRedScoped.bet`
(the freshly-opened body `body^[x]` may legitimately contain `x ∉ Γ.dom`,
which the current scoped predicate forbids). We leave them in place; they
require structural changes to the scoped wrapper, outside the scope of
Wave 5 Agent 5A.
-/

namespace Pss

/-! ## §1. Mutual inductive definitions -/

mutual

/-- MPSS term well-formedness `Γ ⊢ t wf`. Pasquale & García-Pérez 2024,
Figure 4. -/
inductive WfM : Ctx → Term → Prop where
  /-- **Wf-PrS**: a variable bound by `≤` is well-formed. -/
  | varSub {Γ : Ctx} {x : String} {t : Term} :
      Prevalid Γ → Γ.subBinds x t → WfM Γ (.fvar x)
  /-- **Wf-PrE**: a variable bound by `≡` is well-formed. -/
  | varEqu {Γ : Ctx} {x : String} {α : Term} :
      Prevalid Γ → Γ.equBinds x α → WfM Γ (.fvar x)
  /-- **Wf-Top**: `Top` is well-formed in any prevalid context. -/
  | top {Γ : Ctx} : Prevalid Γ → WfM Γ .top
  /-- **Wf-Fun**: cofinite quantification on the body name. -/
  | fun_ {Γ : Ctx} {t u : Term} (L : Finset String) :
      WfM Γ t →
      (∀ x, x ∉ L → WfM (⟨x, t, .sub⟩ :: Γ) (Term.opening (.fvar x) u)) →
      WfM Γ (.abs t u)
  /-- **Wf-App**: an application is well-formed iff its operator is a
  transitive well-subtype of `λ x ≤ t. Top` and its operand is a transitive
  well-subtype of `t`. -/
  | app {Γ : Ctx} {u v t : Term} :
      WSubMStar Γ u (.abs t .top) →
      WSubMStar Γ v t →
      WfM Γ (.app u v)

/-- MPSS well-subtyping `Γ ⊢ u ≤_wf t`. Pasquale & García-Pérez 2024,
Figure 4 (Ws-Rfl, Ws-Lf1, Ws-Lf2, Ws-Rgh). -/
inductive WSubM : Ctx → Term → Term → Prop where
  /-- **Ws-Rfl**: reflexivity. We attach `WfM Γ t` to recover the
  paper's "Γ prevalid" antecedent. -/
  | rfl {Γ : Ctx} {t : Term} :
      WfM Γ t → WSubM Γ t t
  /-- **Ws-Lf1**: prepend an equivalence reduction step on the left. -/
  | lf1 {Γ : Ctx} {v v' t : Term} :
      MEqRed Γ [] v v' →
      WSubM Γ v' t →
      WSubM Γ v t
  /-- **Ws-Lf2**: prepend a subtype reduction step on the left, with
  conjecture-8 well-formedness premises on both endpoints. -/
  | lf2 {Γ : Ctx} {v v' t : Term} :
      WfM Γ v →
      MSubRed Γ [] v v' →
      WfM Γ v' →
      WSubM Γ v' t →
      WSubM Γ v t
  /-- **Ws-Rgh**: append an equivalence reduction step on the right. -/
  | rgh {Γ : Ctx} {v t t' : Term} :
      WSubM Γ v t' →
      MEqRed Γ [] t t' →
      WSubM Γ v t

/-- MPSS transitive well-subtyping `Γ ⊢ v ≤*_wf t`. Pasquale &
García-Pérez 2024, Figure 4 (Ws-Sub, Ws-Trs). -/
inductive WSubMStar : Ctx → Term → Term → Prop where
  /-- **Ws-Sub**: a single well-subtyping step is transitive. -/
  | sub {Γ : Ctx} {v t : Term} :
      WfM Γ v → WSubM Γ v t → WfM Γ t →
      WSubMStar Γ v t
  /-- **Ws-Trs**: transitivity. -/
  | trs {Γ : Ctx} {v u t : Term} :
      WSubMStar Γ v u → WfM Γ u → WSubMStar Γ u t →
      WSubMStar Γ v t

end

/-! ## §2. Notation -/

@[inherit_doc] notation:50 Γ " ⊢ₘ " t " wf "    => WfM Γ t
@[inherit_doc] notation:50 Γ " ⊢ₘ " t " ≤_wf "  u => WSubM Γ t u
@[inherit_doc] notation:50 Γ " ⊢ₘ " t " ≤*_wf " u => WSubMStar Γ t u

/-! ## §3. Reflexivity helper -/

/-- Reflexivity at any well-formed term. -/
theorem WSubMStar.refl_of_wfM {Γ : Ctx} {t : Term} (h : WfM Γ t) :
    WSubMStar Γ t t :=
  WSubMStar.sub h (WSubM.rfl h) h

/-! ## §4. Local closure for all three predicates

We package the four LC payloads (LC of left endpoint of WfM/WSubM/WSubMStar,
plus LC of right endpoint of WSubM/WSubMStar) into a single mutual proof
using `WfM.rec`. Lean's mutual recursor takes one motive per inductive in
the block. -/

/-- Combined LC payload for the three mutual predicates. We use a unified
motive on each of the three so the recursor can be applied uniformly. -/
private def _LC_motive_wf : (Γ : Ctx) → (t : Term) → WfM Γ t → Prop :=
  fun _ t _ => Term.LC t

private def _LC_motive_sub : (Γ : Ctx) → (v t : Term) → WSubM Γ v t → Prop :=
  fun _ v t _ => Term.LC v ∧ Term.LC t

private def _LC_motive_star : (Γ : Ctx) → (v t : Term) → WSubMStar Γ v t → Prop :=
  fun _ v t _ => Term.LC v ∧ Term.LC t

/-- The 12 case payloads for the LC mutual recursor. We reuse them across
the three induction principles. -/

private theorem _LC_varSub : ∀ {Γ : Ctx} {x : String} {t : Term}
    (hpv : Prevalid Γ) (hb : Γ.subBinds x t),
    _LC_motive_wf Γ (.fvar x) (WfM.varSub hpv hb) :=
  fun _ _ => Term.LC.fvar _

private theorem _LC_varEqu : ∀ {Γ : Ctx} {x : String} {α : Term}
    (hpv : Prevalid Γ) (hb : Γ.equBinds x α),
    _LC_motive_wf Γ (.fvar x) (WfM.varEqu hpv hb) :=
  fun _ _ => Term.LC.fvar _

private theorem _LC_top : ∀ {Γ : Ctx} (hpv : Prevalid Γ),
    _LC_motive_wf Γ .top (WfM.top hpv) :=
  fun _ => Term.LC.top

private theorem _LC_fun : ∀ {Γ : Ctx} {t u : Term} (L : Finset String)
    (hT : WfM Γ t)
    (hB : ∀ x, x ∉ L → WfM (⟨x, t, .sub⟩ :: Γ) (Term.opening (.fvar x) u))
    (ihT : Term.LC t)
    (ihB : ∀ x (hx : x ∉ L), Term.LC (Term.opening (.fvar x) u)),
    _LC_motive_wf Γ (.abs t u) (WfM.fun_ L hT hB) :=
  fun L _ _ ihT ihB => Term.LC.abs L ihT ihB

private theorem _LC_app : ∀ {Γ : Ctx} {u v t : Term}
    (hStarU : WSubMStar Γ u (.abs t .top))
    (hStarV : WSubMStar Γ v t)
    (ihU : Term.LC u ∧ Term.LC (.abs t .top))
    (ihV : Term.LC v ∧ Term.LC t),
    _LC_motive_wf Γ (.app u v) (WfM.app hStarU hStarV) :=
  fun _ _ ihU ihV => Term.LC.app ihU.1 ihV.1

private theorem _LC_rfl : ∀ {Γ : Ctx} {t : Term} (hwf : WfM Γ t)
    (ihwf : Term.LC t),
    _LC_motive_sub Γ t t (WSubM.rfl hwf) :=
  fun _ ihwf => ⟨ihwf, ihwf⟩

private theorem _LC_lf1 : ∀ {Γ : Ctx} {v v' t : Term}
    (hred : MEqRed Γ [] v v')
    (hsub : WSubM Γ v' t)
    (ih : Term.LC v' ∧ Term.LC t),
    _LC_motive_sub Γ v t (WSubM.lf1 hred hsub) :=
  fun hred _ ih => ⟨MEqRed.lc_left hred, ih.2⟩

private theorem _LC_lf2 : ∀ {Γ : Ctx} {v v' t : Term}
    (hwfV : WfM Γ v) (hred : MSubRed Γ [] v v')
    (hwfV' : WfM Γ v') (hsub : WSubM Γ v' t)
    (ihwfV : Term.LC v) (ihwfV' : Term.LC v') (ih : Term.LC v' ∧ Term.LC t),
    _LC_motive_sub Γ v t (WSubM.lf2 hwfV hred hwfV' hsub) :=
  fun _ _ _ _ ihwfV _ ih => ⟨ihwfV, ih.2⟩

private theorem _LC_rgh : ∀ {Γ : Ctx} {v t t' : Term}
    (hsub : WSubM Γ v t') (hred : MEqRed Γ [] t t')
    (ih : Term.LC v ∧ Term.LC t'),
    _LC_motive_sub Γ v t (WSubM.rgh hsub hred) :=
  fun _ hred ih => ⟨ih.1, MEqRed.lc_left hred⟩

private theorem _LC_sub_star : ∀ {Γ : Ctx} {v t : Term}
    (hwfV : WfM Γ v) (hsub : WSubM Γ v t) (hwfT : WfM Γ t)
    (ihwfV : Term.LC v) (ihsub : Term.LC v ∧ Term.LC t)
    (ihwfT : Term.LC t),
    _LC_motive_star Γ v t (WSubMStar.sub hwfV hsub hwfT) :=
  fun _ _ _ ihwfV _ ihwfT => ⟨ihwfV, ihwfT⟩

private theorem _LC_trs_star : ∀ {Γ : Ctx} {v u t : Term}
    (hStar1 : WSubMStar Γ v u) (hwfU : WfM Γ u) (hStar2 : WSubMStar Γ u t)
    (ih1 : Term.LC v ∧ Term.LC u) (ihwfU : Term.LC u)
    (ih2 : Term.LC u ∧ Term.LC t),
    _LC_motive_star Γ v t (WSubMStar.trs hStar1 hwfU hStar2) :=
  fun _ _ _ ih1 _ ih2 => ⟨ih1.1, ih2.2⟩

theorem WfM.lc {Γ : Ctx} {t : Term} (h : WfM Γ t) : Term.LC t :=
  WfM.rec
    (motive_1 := _LC_motive_wf)
    (motive_2 := _LC_motive_sub)
    (motive_3 := _LC_motive_star)
    @_LC_varSub @_LC_varEqu @_LC_top @_LC_fun @_LC_app
    @_LC_rfl @_LC_lf1 @_LC_lf2 @_LC_rgh
    @_LC_sub_star @_LC_trs_star
    h

theorem WSubM.lc_pair {Γ : Ctx} {v t : Term} (h : WSubM Γ v t) :
    Term.LC v ∧ Term.LC t :=
  WSubM.rec
    (motive_1 := _LC_motive_wf)
    (motive_2 := _LC_motive_sub)
    (motive_3 := _LC_motive_star)
    @_LC_varSub @_LC_varEqu @_LC_top @_LC_fun @_LC_app
    @_LC_rfl @_LC_lf1 @_LC_lf2 @_LC_rgh
    @_LC_sub_star @_LC_trs_star
    h

theorem WSubMStar.lc_pair {Γ : Ctx} {v t : Term} (h : WSubMStar Γ v t) :
    Term.LC v ∧ Term.LC t :=
  WSubMStar.rec
    (motive_1 := _LC_motive_wf)
    (motive_2 := _LC_motive_sub)
    (motive_3 := _LC_motive_star)
    @_LC_varSub @_LC_varEqu @_LC_top @_LC_fun @_LC_app
    @_LC_rfl @_LC_lf1 @_LC_lf2 @_LC_rgh
    @_LC_sub_star @_LC_trs_star
    h

/-- LC for `WSubM` (left endpoint). -/
theorem WSubM.lc_left {Γ : Ctx} {v t : Term} (h : WSubM Γ v t) :
    Term.LC v := (WSubM.lc_pair h).1

/-- LC for `WSubM` (right endpoint). -/
theorem WSubM.lc_right {Γ : Ctx} {v t : Term} (h : WSubM Γ v t) :
    Term.LC t := (WSubM.lc_pair h).2

/-- LC for `WSubMStar` (left endpoint). -/
theorem WSubMStar.lc_left {Γ : Ctx} {v t : Term} (h : WSubMStar Γ v t) :
    Term.LC v := (WSubMStar.lc_pair h).1

/-- LC for `WSubMStar` (right endpoint). -/
theorem WSubMStar.lc_right {Γ : Ctx} {v t : Term} (h : WSubMStar Γ v t) :
    Term.LC t := (WSubMStar.lc_pair h).2

/-! ## §5. Free-variable scoping

For `WfM Γ t`, every free variable of `t` is in `Γ.dom`. Standard
cofinite-quantification proof. -/

/-- Auxiliary: `fv e ⊆ fv (open_ k (.fvar x) e) ∪ {x}`. Used to argue that
opening only ADDS variables. -/
private theorem _fv_subset_open (x : String) :
    ∀ (k : Nat) (e : Term),
      Term.fv e ⊆ Term.fv (Term.open_ k (.fvar x) e) ∪ {x} := by
  intro k e
  induction e generalizing k with
  | bvar _ => intro w hw; simp [Term.fv] at hw
  | fvar z =>
    intro w hw
    simp [Term.fv] at hw; subst hw
    apply Finset.mem_union.mpr; left
    simp [Term.open_, Term.fv]
  | top => intro w hw; simp [Term.fv] at hw
  | abs tt bb iht ihb =>
    intro w hw
    simp [Term.fv] at hw
    rcases hw with hwT | hwB
    · have hh := iht k hwT
      rcases Finset.mem_union.mp hh with hh' | hh'
      · apply Finset.mem_union.mpr; left
        simp [Term.open_, Term.fv]; exact Or.inl hh'
      · exact Finset.mem_union.mpr (Or.inr hh')
    · have hh := ihb (k+1) hwB
      rcases Finset.mem_union.mp hh with hh' | hh'
      · apply Finset.mem_union.mpr; left
        simp [Term.open_, Term.fv]; exact Or.inr hh'
      · exact Finset.mem_union.mpr (Or.inr hh')
  | app tt ss iht ihs =>
    intro w hw
    simp [Term.fv] at hw
    rcases hw with hwT | hwS
    · have hh := iht k hwT
      rcases Finset.mem_union.mp hh with hh' | hh'
      · apply Finset.mem_union.mpr; left
        simp [Term.open_, Term.fv]; exact Or.inl hh'
      · exact Finset.mem_union.mpr (Or.inr hh')
    · have hh := ihs k hwS
      rcases Finset.mem_union.mp hh with hh' | hh'
      · apply Finset.mem_union.mpr; left
        simp [Term.open_, Term.fv]; exact Or.inr hh'
      · exact Finset.mem_union.mpr (Or.inr hh')

/-- Auxiliary: a `.sub`-bound variable is in the domain. -/
private lemma _subBinds_in_dom {Γ : Ctx} {x : String} {t : Term}
    (hb : Γ.subBinds x t) : x ∈ Γ.dom := by
  induction Γ with
  | nil => simp [Ctx.subBinds, Ctx.lookupSub] at hb
  | cons e rest ih =>
    simp [Ctx.subBinds, Ctx.lookupSub_cons] at hb
    by_cases hex : e.name = x
    · simp [Ctx.dom_cons, hex]
    · simp [hex] at hb
      simp [Ctx.dom_cons]
      exact Or.inr (ih hb)

/-- Auxiliary: an `.equ`-bound variable is in the domain. -/
private lemma _equBinds_in_dom {Γ : Ctx} {x : String} {α : Term}
    (hb : Γ.equBinds x α) : x ∈ Γ.dom := by
  induction Γ with
  | nil => simp [Ctx.equBinds, Ctx.lookupEqu] at hb
  | cons e rest ih =>
    simp [Ctx.equBinds, Ctx.lookupEqu_cons] at hb
    by_cases hex : e.name = x
    · simp [Ctx.dom_cons, hex]
    · simp [hex] at hb
      simp [Ctx.dom_cons]
      exact Or.inr (ih hb)

/-- Combined fv-subset for the three mutual predicates. The motive on
`WSubM` is trivial (we don't try to scope LHS in general — see Lemma 5.2
discussion in §5.5 below). -/
private theorem _wf_fv_combined :
    (∀ {Γ : Ctx} {t : Term}, WfM Γ t → Term.fv t ⊆ Γ.dom) ∧
    (∀ {Γ : Ctx} {v t : Term}, WSubMStar Γ v t →
        Term.fv v ⊆ Γ.dom ∧ Term.fv t ⊆ Γ.dom) := by
  refine ⟨?_, ?_⟩
  all_goals intro Γ
  · intro t h
    classical
    exact (WfM.rec
      (motive_1 := fun Γ t _ => Term.fv t ⊆ Γ.dom)
      (motive_2 := fun _ _ _ _ => True)
      (motive_3 := fun Γ v t _ => Term.fv v ⊆ Γ.dom ∧ Term.fv t ⊆ Γ.dom)
      -- Wf-PrS
      (fun {Γ x t} _ hb => by
        intro y hy; simp [Term.fv] at hy; subst hy
        exact _subBinds_in_dom hb)
      -- Wf-PrE
      (fun {Γ x α} _ hb => by
        intro y hy; simp [Term.fv] at hy; subst hy
        exact _equBinds_in_dom hb)
      -- Wf-Top
      (fun _ => by intro y hy; simp [Term.fv] at hy)
      -- Wf-Fun
      (fun {Γ t u} L _ _ ihT ihBody => by
        intro y hy
        simp [Term.fv] at hy
        rcases hy with hyT | hyU
        · exact ihT hyT
        · obtain ⟨x, hxF⟩ :=
            Term.exists_fresh (L ∪ Γ.dom ∪ Term.fv u ∪ {y})
          have hxL : x ∉ L := fun h => hxF (by
            apply Finset.mem_union.mpr; left
            apply Finset.mem_union.mpr; left
            apply Finset.mem_union.mpr; left; exact h)
          have hxy : x ≠ y := fun heq => hxF (by
            apply Finset.mem_union.mpr; right; simp [heq])
          have hIH : Term.fv (u^[x]) ⊆ Ctx.dom (⟨x, t, .sub⟩ :: Γ) :=
            ihBody x hxL
          simp [Ctx.dom] at hIH
          have hyOpen : y ∈ Term.fv (u^[x]) := by
            have h1 : y ∈ Term.fv (u^[x]) ∪ {x} := _fv_subset_open x 0 u hyU
            rcases Finset.mem_union.mp h1 with h' | h'
            · exact h'
            · simp at h'; exact absurd h'.symm hxy
          have hyIn : y ∈ insert x Γ.dom := hIH hyOpen
          rcases Finset.mem_insert.mp hyIn with hyx | hyDom
          · exact absurd hyx.symm hxy
          · exact hyDom)
      -- Wf-App
      (fun {Γ u v t} _ _ ihStarU ihStarV => by
        intro y hy
        simp [Term.fv] at hy
        rcases hy with hyU | hyV
        · exact ihStarU.1 hyU
        · exact ihStarV.1 hyV)
      -- WSubM cases (motive_2 = True). Constructor arities + IH count:
      -- rfl: 1 + 1 = 2; lf1: 2 + 1 = 3; lf2: 4 + 3 = 7; rgh: 2 + 1 = 3.
      (fun _ _ => trivial)
      (fun _ _ _ => trivial)
      (fun _ _ _ _ _ _ _ => trivial)
      (fun _ _ _ => trivial)
      -- WSubMStar.sub
      (fun {Γ v t} _ _ _ ihwfV _ ihwfT => ⟨ihwfV, ihwfT⟩)
      -- WSubMStar.trs
      (fun _ _ _ ih1 _ ih2 => ⟨ih1.1, ih2.2⟩)
      h)
  · intro v t h
    classical
    exact (WSubMStar.rec
      (motive_1 := fun Γ t _ => Term.fv t ⊆ Γ.dom)
      (motive_2 := fun _ _ _ _ => True)
      (motive_3 := fun Γ v t _ => Term.fv v ⊆ Γ.dom ∧ Term.fv t ⊆ Γ.dom)
      (fun {Γ x t} _ hb => by
        intro y hy; simp [Term.fv] at hy; subst hy
        exact _subBinds_in_dom hb)
      (fun {Γ x α} _ hb => by
        intro y hy; simp [Term.fv] at hy; subst hy
        exact _equBinds_in_dom hb)
      (fun _ => by intro y hy; simp [Term.fv] at hy)
      (fun {Γ t u} L _ _ ihT ihBody => by
        intro y hy
        simp [Term.fv] at hy
        rcases hy with hyT | hyU
        · exact ihT hyT
        · obtain ⟨x, hxF⟩ :=
            Term.exists_fresh (L ∪ Γ.dom ∪ Term.fv u ∪ {y})
          have hxL : x ∉ L := fun h => hxF (by
            apply Finset.mem_union.mpr; left
            apply Finset.mem_union.mpr; left
            apply Finset.mem_union.mpr; left; exact h)
          have hxy : x ≠ y := fun heq => hxF (by
            apply Finset.mem_union.mpr; right; simp [heq])
          have hIH : Term.fv (u^[x]) ⊆ Ctx.dom (⟨x, t, .sub⟩ :: Γ) :=
            ihBody x hxL
          simp [Ctx.dom] at hIH
          have hyOpen : y ∈ Term.fv (u^[x]) := by
            have h1 : y ∈ Term.fv (u^[x]) ∪ {x} := _fv_subset_open x 0 u hyU
            rcases Finset.mem_union.mp h1 with h' | h'
            · exact h'
            · simp at h'; exact absurd h'.symm hxy
          have hyIn : y ∈ insert x Γ.dom := hIH hyOpen
          rcases Finset.mem_insert.mp hyIn with hyx | hyDom
          · exact absurd hyx.symm hxy
          · exact hyDom)
      (fun {Γ u v t} _ _ ihStarU ihStarV => by
        intro y hy
        simp [Term.fv] at hy
        rcases hy with hyU | hyV
        · exact ihStarU.1 hyU
        · exact ihStarV.1 hyV)
      (fun _ _ => trivial)
      (fun _ _ _ => trivial)
      (fun _ _ _ _ _ _ _ => trivial)
      (fun _ _ _ => trivial)
      (fun {Γ v t} _ _ _ ihwfV _ ihwfT => ⟨ihwfV, ihwfT⟩)
      (fun _ _ _ ih1 _ ih2 => ⟨ih1.1, ih2.2⟩)
      h)

/-- `Γ ⊢ t wf  ⟹  fv t ⊆ Γ.dom`. -/
theorem WfM.fv_subset {Γ : Ctx} {t : Term} (h : WfM Γ t) :
    Term.fv t ⊆ Γ.dom := _wf_fv_combined.1 h

/-- LHS scope of `WSubMStar`. -/
theorem WSubMStar.fv_left_subset {Γ : Ctx} {v t : Term}
    (h : WSubMStar Γ v t) : Term.fv v ⊆ Γ.dom :=
  (_wf_fv_combined.2 h).1

/-- RHS scope of `WSubMStar`. -/
theorem WSubMStar.fv_right_subset {Γ : Ctx} {v t : Term}
    (h : WSubMStar Γ v t) : Term.fv t ⊆ Γ.dom :=
  (_wf_fv_combined.2 h).2

/-! ### §5.5. Why no `WSubM.fv_left_subset`?

`WSubM.lf1` accepts `MEqRed Γ [] v v'` for ANY `v` reducing to `v'`,
including pathological `v = .fvar x` for `x ∉ Γ.dom` (cf. `MEqRed.var`,
which only requires `PrevalidExt Γ s`, not scope on `x`). So
`Γ ⊢ v ≤_wf t` does NOT imply `fv v ⊆ Γ.dom` in general. Downstream
lemmas should phrase scoping requirements via the surrounding `WfM`
premises, not via a bare `WSubM` derivation. -/

/-! ## §6. Inversion-style lemmas (Lemmas 10, 15, 16)

* **Lemma 10** (Inversion): If `Γ ⊢ (λx≤t.u) ≤*_wf (λx≤t'.u')` then
  `Γ ⊢ t ≡_wf t'`. AXIOMATIZED — proof requires Theorem 3 (transitivity
  elimination) and Lemma 3 (which together flatten `≤*_wf` to `≤_wf`),
  plus `MEqRedStar` reasoning. Single-axiom Wave-5 quota.

* **Lemma 15** (`Γ ⊢ u ≡_wf v ⟹ Γ ⊢ v ≡_wf u`): OUT OF SCOPE.
  Requires defining `WEquM` (the `≡_wf` analogue of `WSubM`), which we
  do not introduce here.

* **Lemma 16** (`Γ ⊢ u ≡_wf v ⟹ Γ ⊢ u ≤_wf v`): OUT OF SCOPE. Same
  reason as Lemma 15.

We restate Lemma 10 in a slightly weaker, mechanizable form: instead of
returning `Γ ⊢ t ≡_wf t'`, we return the existence of a common
equivalence-reduct via `MEqRedStar`. Downstream uses of Lemma 10 in the
preservation proof actually consume this reduction-flavored statement.
-/

/-- **Lemma 10 (Inversion lemma, restricted form).** From a transitive
well-subtyping between two abstractions of the form `λ x ≤ t. u` and
`λ x ≤ t'. u'`, the bound annotations have a common equivalence-reduct.

Restricted form: returns a common reduct `z` with
`MEqRedStar Γ [] t z ∧ MEqRedStar Γ [] t' z`, instead of the paper's
`Γ ⊢ t ≡_wf t'`.

AXIOMATIZED (Wave 5 single-axiom quota for this file). Discharge requires
Theorem 3 (transitivity elimination) — see paper §3 and `PLAN.md`. -/
axiom Lemma_10_InversionRestricted
    {Γ : Ctx} {t t' u u' : Term}
    (h : WSubMStar Γ (.abs t u) (.abs t' u')) :
    ∃ z, MEqRedStar Γ [] t z ∧ MEqRedStar Γ [] t' z

end Pss

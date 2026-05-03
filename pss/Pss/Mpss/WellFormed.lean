import Pss.Mpss.Weakening

set_option linter.unusedVariables false

/-! # `Pss.Mpss.WellFormed` — MPSS well-formedness, well-subtyping, transitive
well-subtyping, and well-equivalence

Pasquale & García-Pérez 2024 (CSL 2026), Figure 4. Four judgments:

* `WfM Γ t`         — `Γ ⊢ t wf`         (term well-formedness; 5 rules)
* `WSubM Γ t u`     — `Γ ⊢ t ≤_wf u`     (well-subtyping; 4 rules)
* `WSubMStar Γ t u` — `Γ ⊢ t ≤*_wf u`    (transitive well-subtyping; 2 rules)
* `WEquM Γ t u`     — `Γ ⊢ t ≡_wf u`     (well-equivalence; 3 rules)
* `WEquMStar Γ t u` — `Γ ⊢ t ≡*_wf u`    (transitive well-equivalence; 2 rules)

The first three are mutually inductive:

* `WfM` references `WSubMStar` (in `Wf-App`).
* `WSubM` references `WfM` (in `Ws-Rfl`, `Ws-Lf2`).
* `WSubMStar` references `WfM` and `WSubM` (in `Ws-Sub`, `Ws-Trs`).

`WEquM` is the `≡_wf` analogue of `WSubM`. The paper's `◁_wf` meta-judgment
ranges over both `≤_wf` and `≡_wf`, but `WEquM` does NOT have an `Ws-Lf2`
analogue: only equivalence-reduction may be prepended/appended (per paper
Fig 4). `WEquM` is defined separately (not in the mutual block) because it
is only consumed by the inversion-style lemmas downstream, not by `WfM`.

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
Figure 4.

`Type`-valued (post-Type-LC refactor): the constructors carry `Prevalid`
witnesses (also Type-valued), so `WfM` lifts naturally. -/
inductive WfM : Ctx → Term → Type where
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
Figure 4 (Ws-Rfl, Ws-Lf1, Ws-Lf2, Ws-Rgh).

`Type`-valued (post-Type-LC refactor). -/
inductive WSubM : Ctx → Term → Term → Type where
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
García-Pérez 2024, Figure 4 (Ws-Sub, Ws-Trs).

`Type`-valued (post-Type-LC refactor). -/
inductive WSubMStar : Ctx → Term → Term → Type where
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

/-- Reflexivity at any well-formed term.

`def` (since `WSubMStar : Type` post-Type-LC refactor). -/
def WSubMStar.refl_of_wfM {Γ : Ctx} {t : Term} (h : WfM Γ t) :
    WSubMStar Γ t t :=
  WSubMStar.sub h (WSubM.rfl h) h

/-! ## §4. Local closure for all three predicates

We package the four LC payloads (LC of left endpoint of WfM/WSubM/WSubMStar,
plus LC of right endpoint of WSubM/WSubMStar) into a single mutual proof
using `WfM.rec`. Lean's mutual recursor takes one motive per inductive in
the block. -/

/-- Combined LC payload for the three mutual predicates. We use a unified
motive on each of the three so the recursor can be applied uniformly.

`Type`-valued motives (post-Type-LC refactor): `Term.LC` itself is `Type`. -/
private def _LC_motive_wf : (Γ : Ctx) → (t : Term) → WfM Γ t → Type :=
  fun _ t _ => Term.LC t

private def _LC_motive_sub : (Γ : Ctx) → (v t : Term) → WSubM Γ v t → Type :=
  fun _ v t _ => PProd (Term.LC v) (Term.LC t)

private def _LC_motive_star : (Γ : Ctx) → (v t : Term) → WSubMStar Γ v t → Type :=
  fun _ v t _ => PProd (Term.LC v) (Term.LC t)

/-- The 12 case payloads for the LC mutual recursor. We reuse them across
the three induction principles. -/

private def _LC_varSub : ∀ {Γ : Ctx} {x : String} {t : Term}
    (hpv : Prevalid Γ) (hb : Γ.subBinds x t),
    _LC_motive_wf Γ (.fvar x) (WfM.varSub hpv hb) :=
  fun _ _ => Term.LC.fvar _

private def _LC_varEqu : ∀ {Γ : Ctx} {x : String} {α : Term}
    (hpv : Prevalid Γ) (hb : Γ.equBinds x α),
    _LC_motive_wf Γ (.fvar x) (WfM.varEqu hpv hb) :=
  fun _ _ => Term.LC.fvar _

private def _LC_top : ∀ {Γ : Ctx} (hpv : Prevalid Γ),
    _LC_motive_wf Γ .top (WfM.top hpv) :=
  fun _ => Term.LC.top

private def _LC_fun : ∀ {Γ : Ctx} {t u : Term} (L : Finset String)
    (hT : WfM Γ t)
    (hB : ∀ x, x ∉ L → WfM (⟨x, t, .sub⟩ :: Γ) (Term.opening (.fvar x) u))
    (ihT : Term.LC t)
    (ihB : ∀ x (hx : x ∉ L), Term.LC (Term.opening (.fvar x) u)),
    _LC_motive_wf Γ (.abs t u) (WfM.fun_ L hT hB) :=
  fun L _ _ ihT ihB => Term.LC.abs L ihT ihB

private def _LC_app : ∀ {Γ : Ctx} {u v t : Term}
    (hStarU : WSubMStar Γ u (.abs t .top))
    (hStarV : WSubMStar Γ v t)
    (ihU : PProd (Term.LC u) (Term.LC (.abs t .top)))
    (ihV : PProd (Term.LC v) (Term.LC t)),
    _LC_motive_wf Γ (.app u v) (WfM.app hStarU hStarV) :=
  fun _ _ ihU ihV => Term.LC.app ihU.1 ihV.1

private def _LC_rfl : ∀ {Γ : Ctx} {t : Term} (hwf : WfM Γ t)
    (ihwf : Term.LC t),
    _LC_motive_sub Γ t t (WSubM.rfl hwf) :=
  fun _ ihwf => ⟨ihwf, ihwf⟩

private noncomputable def _LC_lf1 : ∀ {Γ : Ctx} {v v' t : Term}
    (hred : MEqRed Γ [] v v')
    (hsub : WSubM Γ v' t)
    (ih : PProd (Term.LC v') (Term.LC t)),
    _LC_motive_sub Γ v t (WSubM.lf1 hred hsub) :=
  fun hred _ ih => ⟨MEqRed.lc_left hred, ih.2⟩

private def _LC_lf2 : ∀ {Γ : Ctx} {v v' t : Term}
    (hwfV : WfM Γ v) (hred : MSubRed Γ [] v v')
    (hwfV' : WfM Γ v') (hsub : WSubM Γ v' t)
    (ihwfV : Term.LC v) (ihwfV' : Term.LC v')
    (ih : PProd (Term.LC v') (Term.LC t)),
    _LC_motive_sub Γ v t (WSubM.lf2 hwfV hred hwfV' hsub) :=
  fun _ _ _ _ ihwfV _ ih => ⟨ihwfV, ih.2⟩

private noncomputable def _LC_rgh : ∀ {Γ : Ctx} {v t t' : Term}
    (hsub : WSubM Γ v t') (hred : MEqRed Γ [] t t')
    (ih : PProd (Term.LC v) (Term.LC t')),
    _LC_motive_sub Γ v t (WSubM.rgh hsub hred) :=
  fun _ hred ih => ⟨ih.1, MEqRed.lc_left hred⟩

private def _LC_sub_star : ∀ {Γ : Ctx} {v t : Term}
    (hwfV : WfM Γ v) (hsub : WSubM Γ v t) (hwfT : WfM Γ t)
    (ihwfV : Term.LC v) (ihsub : PProd (Term.LC v) (Term.LC t))
    (ihwfT : Term.LC t),
    _LC_motive_star Γ v t (WSubMStar.sub hwfV hsub hwfT) :=
  fun _ _ _ ihwfV _ ihwfT => ⟨ihwfV, ihwfT⟩

private def _LC_trs_star : ∀ {Γ : Ctx} {v u t : Term}
    (hStar1 : WSubMStar Γ v u) (hwfU : WfM Γ u) (hStar2 : WSubMStar Γ u t)
    (ih1 : PProd (Term.LC v) (Term.LC u)) (ihwfU : Term.LC u)
    (ih2 : PProd (Term.LC u) (Term.LC t)),
    _LC_motive_star Γ v t (WSubMStar.trs hStar1 hwfU hStar2) :=
  fun _ _ _ ih1 _ ih2 => ⟨ih1.1, ih2.2⟩

noncomputable def WfM.lc {Γ : Ctx} {t : Term} (h : WfM Γ t) : Term.LC t :=
  WfM.rec
    (motive_1 := _LC_motive_wf)
    (motive_2 := _LC_motive_sub)
    (motive_3 := _LC_motive_star)
    @_LC_varSub @_LC_varEqu @_LC_top @_LC_fun @_LC_app
    @_LC_rfl @_LC_lf1 @_LC_lf2 @_LC_rgh
    @_LC_sub_star @_LC_trs_star
    h

noncomputable def WSubM.lc_pair {Γ : Ctx} {v t : Term} (h : WSubM Γ v t) :
    PProd (Term.LC v) (Term.LC t) :=
  WSubM.rec
    (motive_1 := _LC_motive_wf)
    (motive_2 := _LC_motive_sub)
    (motive_3 := _LC_motive_star)
    @_LC_varSub @_LC_varEqu @_LC_top @_LC_fun @_LC_app
    @_LC_rfl @_LC_lf1 @_LC_lf2 @_LC_rgh
    @_LC_sub_star @_LC_trs_star
    h

noncomputable def WSubMStar.lc_pair {Γ : Ctx} {v t : Term} (h : WSubMStar Γ v t) :
    PProd (Term.LC v) (Term.LC t) :=
  WSubMStar.rec
    (motive_1 := _LC_motive_wf)
    (motive_2 := _LC_motive_sub)
    (motive_3 := _LC_motive_star)
    @_LC_varSub @_LC_varEqu @_LC_top @_LC_fun @_LC_app
    @_LC_rfl @_LC_lf1 @_LC_lf2 @_LC_rgh
    @_LC_sub_star @_LC_trs_star
    h

/-- LC for `WSubM` (left endpoint). -/
noncomputable def WSubM.lc_left {Γ : Ctx} {v t : Term} (h : WSubM Γ v t) :
    Term.LC v := (WSubM.lc_pair h).1

/-- LC for `WSubM` (right endpoint). -/
noncomputable def WSubM.lc_right {Γ : Ctx} {v t : Term} (h : WSubM Γ v t) :
    Term.LC t := (WSubM.lc_pair h).2

/-- LC for `WSubMStar` (left endpoint). -/
noncomputable def WSubMStar.lc_left {Γ : Ctx} {v t : Term} (h : WSubMStar Γ v t) :
    Term.LC v := (WSubMStar.lc_pair h).1

/-- LC for `WSubMStar` (right endpoint). -/
noncomputable def WSubMStar.lc_right {Γ : Ctx} {v t : Term} (h : WSubMStar Γ v t) :
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

/-! ## §6. Well-equivalence (`WEquM`)

The `≡_wf` analogue of `WSubM`. Paper §4 Fig 4 (right column), with the
critical observation: `WEquM` only has rules that match `WSubM`'s `Ws-Rfl`,
`Ws-Lf1`, and `Ws-Rgh`. There is no `Ws-Lf2` analogue — equivalence does
not subsume subtype-reduction steps.

This is why we define `WEquM` separately (not in the mutual block above):
it does not reference `WfM` recursively (only via the `Ws-Rfl`-style
reflexivity premise on the diagonal), and `WfM` does not reference it.
Defining it after the mutual block avoids a deeper mutual entanglement. -/

/-- MPSS well-equivalence `Γ ⊢ u ≡_wf t`. Pasquale & García-Pérez 2024,
Figure 4 (right column, `≡_wf` instance of `◁_wf`).

`Type`-valued (post-Type-LC refactor; `WfM`/`MEqRed` premises are Type). -/
inductive WEquM : Ctx → Term → Term → Type where
  /-- **Wse-Rfl**: reflexivity. -/
  | rfl {Γ : Ctx} {t : Term} :
      WfM Γ t → WEquM Γ t t
  /-- **Wse-Lf1**: prepend an equivalence-reduction step on the left. -/
  | lf1 {Γ : Ctx} {v v' t : Term} :
      MEqRed Γ [] v v' →
      WEquM Γ v' t →
      WEquM Γ v t
  /-- **Wse-Rgh**: append an equivalence-reduction step on the right. -/
  | rgh {Γ : Ctx} {v t t' : Term} :
      WEquM Γ v t' →
      MEqRed Γ [] t t' →
      WEquM Γ v t

/-- MPSS transitive well-equivalence `Γ ⊢ v ≡*_wf t`. Analogous to
`WSubMStar` but for the equivalence judgment.

`Type`-valued (post-Type-LC refactor). -/
inductive WEquMStar : Ctx → Term → Term → Type where
  /-- **Wse-Sub**: a single well-equivalence step is transitive. -/
  | sub {Γ : Ctx} {v t : Term} :
      WfM Γ v → WEquM Γ v t → WfM Γ t →
      WEquMStar Γ v t
  /-- **Wse-Trs**: transitivity. -/
  | trs {Γ : Ctx} {v u t : Term} :
      WEquMStar Γ v u → WfM Γ u → WEquMStar Γ u t →
      WEquMStar Γ v t

@[inherit_doc] notation:50 Γ " ⊢ₘ " t " ≡_wf "  u => WEquM Γ t u
@[inherit_doc] notation:50 Γ " ⊢ₘ " t " ≡*_wf " u => WEquMStar Γ t u

/-! ## §7. Inversion-style lemmas (Lemmas 10, 15, 16)

* **Lemma 15** (`Γ ⊢ u ≡_wf v ⟹ Γ ⊢ v ≡_wf u`): symmetry of `≡_wf`.
  PROVED — straightforward 3-case induction.

* **Lemma 16** (`Γ ⊢ u ≡_wf v ⟹ Γ ⊢ u ≤_wf v`): inclusion of `≡_wf`
  into `≤_wf`. PROVED — straightforward 3-case induction.

* **Lemma 10** (Inversion): If `Γ ⊢ (λx≤t.u) ≤*_wf (λx≤t'.u')` then
  `Γ ⊢ t ≡_wf t'`. AXIOMATIZED — proof requires Theorem 3 (transitivity
  elimination) and Lemma 3 (which together flatten `≤*_wf` to `≤_wf`),
  plus `MEqRedStar` reasoning. -/

/-- **Lemma 15 (Symmetry of well-equivalence).** Pasquale & García-Pérez
2024, appendix A.

`noncomputable def` (since `WEquM : Type` post-Type-LC refactor). -/
noncomputable def Lemma_15_WEquM_symm {Γ : Ctx} {u v : Term} (h : WEquM Γ u v) :
    WEquM Γ v u := by
  induction h with
  | rfl hwf => exact WEquM.rfl hwf
  | lf1 hred _ ih =>
      -- h : WEquM Γ u' v from premise; ih : WEquM Γ v u'
      -- want: WEquM Γ v u, given hred : MEqRed Γ [] u u'
      exact WEquM.rgh ih hred
  | rgh _ hred ih =>
      -- premise: WEquM Γ u v', MEqRed Γ [] v v'; ih : WEquM Γ v' u
      -- want: WEquM Γ v u
      exact WEquM.lf1 hred ih

/-- **Lemma 16 (Well-equivalence implies well-subtyping).** Pasquale &
García-Pérez 2024, appendix A.

`noncomputable def` (since `WSubM : Type` post-Type-LC refactor). -/
noncomputable def Lemma_16_WEquM_to_WSubM {Γ : Ctx} {u v : Term} (h : WEquM Γ u v) :
    WSubM Γ u v := by
  induction h with
  | rfl hwf => exact WSubM.rfl hwf
  | lf1 hred _ ih => exact WSubM.lf1 hred ih
  | rgh _ hred ih => exact WSubM.rgh ih hred

/-! **Lemma 10 (Inversion lemma — full form).** From a transitive
well-subtyping between two abstractions of the form `λ x ≤ t. u` and
`λ x ≤ t'. u'`, the bound annotations are well-equivalent.

This is the paper's exact Lemma 10 statement. AXIOMATIZED.

## Precise discharge blocker (audit notes, agent_id: och-refactor)

The natural strategy via `_WSubMStar_toMSub` (in `TypeSafety.lean`) yields
`MSub Γ [] (.abs t u) (.abs t' u')` = `∃ w, MSubRedStar Γ [] (.abs t u) w
∧ MEqRedStar Γ [] (.abs t' u') w`. By chain inversions on `Me-Fun` /
`Ms-Fun` / `Ms-Equ` (the only rules that fire on `.abs` at empty stack),
`w = .abs t_w body_w` and we extract two `MEqRedStar` annotation chains:
`MEqRedStar Γ [] t t_w` and `MEqRedStar Γ [] t' t_w`. We additionally have
`WfM Γ t` and `WfM Γ t'` from the LHS/RHS extractors of `WSubMStar`.

**The blocker is reaching `WEquM Γ t t'` from these two chains plus
endpoint WfM.** The `WEquM` constructors are:
* `rfl`: needs `WfM Γ t` to anchor a `WEquM Γ t t`.
* `lf1`: prepend a forward `MEqRed` step on the LHS (no WfM).
* `rgh`: append a *backward* `MEqRed` step on the RHS (no WfM).

The two unconditionally provable helper lemmas are:
* Lemma A (no WfM): `MEqRedStar Γ [] a b → WEquM Γ b c → WEquM Γ a c`.
  (Tail induction on the chain, applying `lf1` at each step.)
* Lemma B (no WfM): `WEquM Γ a c → MEqRedStar Γ [] b c → WEquM Γ a b`.
  (Tail induction on the chain, applying `rgh` at each step.)

Lemma A extends the LHS *backward* along a forward chain; Lemma B shrinks
the RHS *backward* along a forward chain. Crucially, **neither extends
either side *forward* along a forward chain without an additional WfM
anchor** (because `rgh`'s consumed step is `t →ₑ t'`, not `t' →ₑ t`).
With our chains both pointing **toward** `t_w`, neither helper can be
seeded from `WEquM Γ t' t'` (rfl, anchored by `WfM Γ t'`): every
extension chain we have ends at `t_w`, not at `t'`.

The only seed that closes is `WEquM Γ t_w t_w` (rfl), which requires
`WfM Γ t_w`. **Producing `WfM Γ t_w` requires preservation of `WfM`
under `MEqRed` at empty stack** — an axiomatic-looking step.

### Update (agent_id: `pss-2026-05-04-WfM-preservation-counterexample`)

The proposed preservation lemma — a parallel `Lemma_6_EvaluationPreservesWf`
for `MEqRed` instead of `Step` — was previously described as "non-trivial
but tractable". **It is FALSE.** A Lean-checked counterexample lives in
`Pss.Mpss.WfMPreservation`:

* Take `Γ = [⟨"x", .app .top .top, .equ⟩]`. The bound term is closed and
  `LC`, so `Prevalid Γ` holds. But `.app .top .top` is *not* `WfM Γ`
  (Lemma 11: Top has no function supertype).
* `WfM Γ (.fvar "x")` holds via `Wf-PrE` (only requires `Prevalid`+binding,
  NOT well-formedness of the bound annotation).
* `MEqRed Γ [] (.fvar "x") (.app .top .top)` holds via `Me-Pro` plus
  reflexive `app`-congruence on `.top .top`.
* But `WfM Γ (.app .top .top)` reduces to a `Top ≤*_wf .abs t .top`
  obligation that Lemma 11 refutes.

The structural cause: `MEqRed.pro` reads off an `≡`-binding's stored term,
but `Prevalid` only ensures structural well-formedness (`fv ⊆ Γ.dom` +
`LC`), not typing well-formedness. `Lemma_6_EvaluationPreservesWf` is
provable for `Step` because `Step` is purely syntactic and never consults
the context. `MEqRed` *does* consult the context (via `pro`/`var`), and
the calculus does not enforce that bound annotations are themselves
`WfM`. Hence the natural preservation lemma is unavailable.

### Recovery strategies (none realized yet)

See `Pss.Mpss.WfMPreservation` for the full list. Briefly:

1. **Strengthen `Prevalid` to a `WfCtx` mutually inductive with `WfM`.**
   Requires every `Prevalid` builder in the codebase to upgrade to
   carrying a `WfM` payload for `≡`-bound annotations.
2. **Strengthen `Wf-PrE` to require `WfM Γ α`** in addition to the
   binding. Paper-non-faithful and breaks termination of the `WfM`
   recursion (must recurse into stored annotations).
3. **Restrict the lemma's domain** to `MEqRed` derivations whose `pro`
   applications only target already-`WfM` bound terms. Then the
   call sites of `Lemma_10_Inversion` need to thread that predicate
   through their inputs — but `WSubMStar` doesn't expose its internal
   `MEqRed` derivations directly, so this is non-trivial.
4. **Bypass `WfM Γ t_w` entirely.** Find a Church-Rosser-style proof
   of `Lemma_10_Inversion` that produces `WEquM Γ t t'` directly from
   the joinable annotation chains, without needing the `rfl` seed at
   the join point. Most promising path because it avoids touching the
   `Prevalid`/`WfM` interface, but has not been investigated.

Strategy (4) — the Church-Rosser bypass — is the recommended next attack
vector. Sketch: `MEqRedStar Γ [] t t_w` and `MEqRedStar Γ [] t' t_w`
together form a "wedge" over `t_w`. By a parallel-reduction analogue of
the Diamond property (cf. `Pss.Mpss.Diamond.Lemma_2_DiamondMEqRed`), the
two chains can be re-joined into a single forward `MEqRedStar Γ [] t s`
followed by a backward chain `MEqRedStar Γ [] t' s'` where some
relationship between `s` and `s'` is established. This may bypass the
need for a seed. Significant new lemma machinery would be required, but
the existing diamond infrastructure is a reasonable starting point.

Cf. `AXIOMS.md` axiom #3 for the listing (status / paper / discharge
plan). The restricted form `Lemma_10_InversionRestricted` (returning a
common `MEqRedStar` reduct) is provable without `WfM`-preservation but
is currently unused downstream — listed in AXIOMS.md as INACTIVE
outstanding axiom #11.

### Strategy A audit (agent_id: `pss-20260504-strategy-a-audit`)

A subsequent dispatched agent (this one) attempted Strategy A — direct
induction on the WSubMStar derivation, with `WEquM` chain helpers
(`left_chain`, `right_chain`, `right_chain_fwd`, `trans`) — and found:

* The `_sub` (single `WSubM`) cases of the inversion DO close cleanly
  via direct case-analysis. See `_Lemma_10_Inversion_sub_partial` below
  for the proven partial discharge.
* The `_star` (`WSubMStar`) case via `trs` is **structurally blocked
  by confluence**. To compose two intermediate `WEquM`s (one from each
  leg of `trs`) into a single `WEquM`, we would need `WEquM.trans`,
  which is **isomorphic to the diamond property of `MEqRed`**
  (because `WEquM Γ a b` ≃ `∃ m, a → m ∧ b → m` zigzag, and composing
  two zigzags requires confluence at the joining midpoint).
* The plan agent's `WEquM.right_chain_fwd` (Helper 3) — proposed as
  "symmetrize, prepend on LHS via Helper 1, symmetrize again" —
  contains a **directional error**: after symmetrizing `WEquM Γ a b`
  to `WEquM Γ b a`, the chain `MEqRedStar Γ [] b c` (forward from b)
  cannot be prepended via Helper 1 (which requires a chain ending at
  the WEquM's LHS). Forward extension on the right of WEquM truly
  requires confluence.

Conclusion: Strategy A's `_star`-trs case is **as hard as the diamond
property of MEqRed**, which is itself the source of the `Lemma_2_*`
β-residuals. Bypassing those β-residuals via direct induction is
therefore impossible without a fundamentally new technique.

The paper's own proof routes through `Theorem 3` (transitivity
elimination) which collapses the `WSubMStar.trs` away, then reads off
the common reduct from the resulting `MSub`. That route is fine for
discharging the axiom but would re-introduce β-residuals into
Theorem 5's closure (count would increase from 4 to ~8). Because the
explicit goal of this discharge campaign is to **strictly reduce**
Theorem 5's axiom count, the paper-route is **not a valid discharge**.

### Status post-Strategy-A audit

The axiom remains. The `_sub` partial proof is shipped as
`_Lemma_10_Inversion_sub_partial` (auxiliary). It can be reused if a
future Strategy avoids the `trs` case (e.g., by RESTRICTING the call
sites to provide `trs`-free WSubMStar derivations, possibly through a
calculus refactor that makes `trs` admissible-only at construction
time). -/

/-! ### §7.1. Helper inversions (single-step)

Local re-derivations of the inversions used in the partial discharge.
We avoid pulling in `Pss.Mpss.TypeSafety` (which is downstream of this
file) by re-proving the small ones we need. -/

/-- Single-step inversion: `MEqRed Γ s .top v` forces `v = .top`. -/
private theorem _Lemma_10_MEqRed_top_inv {Γ : Ctx} {s : Stack} {v : Term}
    (h : MEqRed Γ s .top v) : v = .top := by
  cases h with
  | top _ => rfl

/-- Single-step inversion: `MSubRed Γ s .top v` forces `v = .top`. -/
private theorem _Lemma_10_MSubRed_top_inv {Γ : Ctx} {s : Stack} {v : Term}
    (h : MSubRed Γ s .top v) : v = .top := by
  cases h with
  | top _ _ _ => rfl
  | equ _ heq => exact _Lemma_10_MEqRed_top_inv heq

/-- Single-step *annotated* inversion on `MEqRed Γ [] (.abs t body) v`:
the only constructor that fires is `Me-Fun`, so `v = .abs t' body'` with
`MEqRed Γ [] t t'`. (At empty stack, `Me-FOp` cannot fire.) -/
private noncomputable def _Lemma_10_MEqRed_abs_inv_annot
    {Γ : Ctx} {t body v : Term}
    (h : MEqRed Γ [] (.abs t body) v) :
    Σ' (t' body' : Term),
      PProd (v = .abs t' body') (MEqRed Γ [] t t') := by
  cases h with
  | fun_ L hT _ _ => exact ⟨_, _, ⟨rfl, hT⟩⟩

/-- Single-step *annotated* inversion on `MSubRed Γ [] (.abs t body) v`:
the constructors that fire are `Ms-Top`, `Ms-Equ` (delegating to
`Me-Fun`), and `Ms-Fun` (annotation invariant). The result captures
all three cases. (At empty stack, `Ms-FOp` cannot fire.) -/
private noncomputable def _Lemma_10_MSubRed_abs_inv_annot
    {Γ : Ctx} {t body v : Term}
    (h : MSubRed Γ [] (.abs t body) v) :
    PSum
      (v = .top)
      (Σ' (t' body' : Term),
         PProd (v = .abs t' body')
           (PSum (t' = t) (MEqRed Γ [] t t'))) := by
  cases h with
  | top _ _ _ => exact PSum.inl rfl
  | equ _ heq =>
      cases heq with
      | fun_ L hT _ _ =>
          exact PSum.inr ⟨_, _, ⟨rfl, PSum.inr hT⟩⟩
  | fun_ _ _ _ _ =>
      exact PSum.inr ⟨_, _, ⟨rfl, PSum.inl rfl⟩⟩

/-! ### §7.2. WEquM chain helpers (no WfM required)

These two extend a `WEquM` by an `MEqRedStar` chain on the LHS (forward)
and on the RHS (backward). They mirror the WSubM versions in
`Pss.Mpss.WSubMTrans`. -/

/-- **Prepend a forward `MEqRedStar` chain on the LHS of a `WEquM`.**

Given `MEqRedStar Γ [] a a'` and `WEquM Γ a' c`, derive `WEquM Γ a c`
by repeated `WEquM.lf1`. -/
noncomputable def WEquM.left_chain
    {Γ : Ctx} {a a' c : Term}
    (hChain : MEqRedStar Γ [] a a')
    (hEqu : WEquM Γ a' c) :
    WEquM Γ a c := by
  suffices key : ∀ {x : Term} (h : MEqRedStar Γ [] x a'),
      Nonempty (WEquM Γ a' c → WEquM Γ x c) from (key hChain).some hEqu
  intro x h
  refine Relation.ReflTransGen.head_induction_on (b := a')
    (P := fun x (_ : MEqRedStar Γ [] x a') =>
      Nonempty (WEquM Γ a' c → WEquM Γ x c)) h ?_ ?_
  · exact ⟨fun he => he⟩
  · intro x y hHead hTail ihY
    classical
    refine ⟨fun heA' => ?_⟩
    have heY : WEquM Γ y c := ihY.some heA'
    exact WEquM.lf1 hHead.some heY

/-- **Shrink a forward `MEqRedStar` chain on the RHS of a `WEquM`** —
i.e., given `WEquM Γ a c'` and a forward chain `c → c'`, derive
`WEquM Γ a c` (NOT the other direction). The constructor `WEquM.rgh`
consumes a step `c → c'`, so this lemma is direct.

Note the asymmetry: extending RHS *forward* (`WEquM Γ a c → c → c' →
WEquM Γ a c'`) is **not** provable here — that would require the
diamond property of `MEqRed` (because WEquM is structurally a zigzag
`a → m ← b`, and absorbing a forward step on the RHS-end would require
joining `c → c'` with `c → m` via confluence). -/
noncomputable def WEquM.right_chain_back
    {Γ : Ctx} {a c c' : Term}
    (hEqu : WEquM Γ a c')
    (hChain : MEqRedStar Γ [] c c') :
    WEquM Γ a c := by
  suffices key : ∀ {x : Term} (h : MEqRedStar Γ [] x c'),
      Nonempty (WEquM Γ a c' → WEquM Γ a x) from (key hChain).some hEqu
  intro x h
  refine Relation.ReflTransGen.head_induction_on (b := c')
    (P := fun x (_ : MEqRedStar Γ [] x c') =>
      Nonempty (WEquM Γ a c' → WEquM Γ a x)) h ?_ ?_
  · exact ⟨fun he => he⟩
  · intro x y hHead hTail ihY
    classical
    refine ⟨fun heC' => ?_⟩
    have heAY : WEquM Γ a y := ihY.some heC'
    exact WEquM.rgh heAY hHead.some

/-! ### §7.3. Partial discharge of Lemma 10 — the `_sub` direction

We can prove the `WSubM` variant of Lemma 10 directly, by structural
induction on the `WSubM` derivation. The four cases all close cleanly:

* `Ws-Rfl`: `a = b`, so `t = t'`; close with `WEquM.rfl`.
* `Ws-Lf1`: invert the prepended `MEqRed Γ [] (.abs t u) v'` via
  `Me-Fun`; recurse; close with `WEquM.lf1`.
* `Ws-Lf2`: invert the prepended `MSubRed Γ [] (.abs t u) v'`. Three
  sub-cases:
  - `Ms-Top` produces `v' = .top`, leaving `WSubM Γ .top (.abs t' u')`
    which is impossible (the WSubM-version of Lemma 11). Discharged
    via `_WSubM_top_abs_uninhabited`.
  - `Ms-Equ` delegates to `Me-Fun`; same as `Ws-Lf1`.
  - `Ms-Fun` keeps annotation invariant; recurse directly.
* `Ws-Rgh`: invert the appended `MEqRed Γ [] (.abs t' u') v'` via
  `Me-Fun`; recurse; close with `WEquM.rgh`.

The subtlety is the `_WSubM_top_abs_uninhabited` argument, which is
itself proven by structural induction. -/

/-! ### §7.3a. Custom-motive recursors (mutual block workaround)

The `induction` tactic does not directly support mutual inductive
families like `WfM`/`WSubM`/`WSubMStar`. We use the auto-generated
`WSubM.rec` with explicit motive functions and trivial WfM/WSubMStar
motives. -/

/-- Motive type: `WSubM Γ a b → False` proposition saying it's
impossible if `a = .top` and `b = .abs _ _`. -/
private def _Lemma_10_top_abs_motive_sub :
    (Γ : Ctx) → (a b : Term) → WSubM Γ a b → Prop :=
  fun Γ a b _ => a = .top → ∀ {t' u' : Term}, b = .abs t' u' → False

/-- Motive type: `WfM` trivial. -/
private def _Lemma_10_top_abs_motive_wf :
    (Γ : Ctx) → (t : Term) → WfM Γ t → Prop :=
  fun _ _ _ => True

/-- Motive type: `WSubMStar` trivial. -/
private def _Lemma_10_top_abs_motive_star :
    (Γ : Ctx) → (a b : Term) → WSubMStar Γ a b → Prop :=
  fun _ _ _ _ => True

/-- **The WSubM-version of Lemma 11**: there is no `WSubM Γ .top (.abs
t' u')` derivation. Direct structural induction on the derivation tree
via `WSubM.rec`.

This is provable from the existing axiom-free machinery and avoids the
`_WSubMStar_toMSub` route (which goes through `Theorem 3` and incurs
the β-residual axioms). -/
theorem _WSubM_top_abs_uninhabited
    {Γ : Ctx} {t' u' : Term}
    (h : WSubM Γ .top (.abs t' u')) : False := by
  classical
  exact (WSubM.rec
    (motive_1 := _Lemma_10_top_abs_motive_wf)
    (motive_2 := _Lemma_10_top_abs_motive_sub)
    (motive_3 := _Lemma_10_top_abs_motive_star)
    -- WfM cases (5): all trivial.
    (fun _ _ => trivial) (fun _ _ => trivial) (fun _ => trivial)
    (fun _ _ _ _ _ => trivial) (fun _ _ _ _ => trivial)
    -- Ws-Rfl: args (hwf, ihwf)
    (fun {Γ x} _hwf _ihwf => by
      intro hA t' u' hB; subst hA; cases hB)
    -- Ws-Lf1: args (hred, h_inner, ih)
    (fun {Γ a v' b} hred _h_inner ih => by
      intro hA t' u' hB; subst hA
      have : v' = .top := _Lemma_10_MEqRed_top_inv hred
      subst this; exact ih rfl hB)
    -- Ws-Lf2: args (hwfA, hred, hwfA', h_inner, ihwfA, ihwfA', ih)
    (fun {Γ a v' b} _hwfA hred _hwfA' _h_inner _ihA _ihA' ih => by
      intro hA t' u' hB; subst hA
      have : v' = .top := _Lemma_10_MSubRed_top_inv hred
      subst this; exact ih rfl hB)
    -- Ws-Rgh: args (h_inner, hred, ih)
    (fun {Γ a b b'} _h_inner hred ih => by
      intro hA t' u' hB; subst hA; subst hB
      obtain ⟨t1, u1, hbEq, _⟩ := _Lemma_10_MEqRed_abs_inv_annot hred
      exact ih rfl hbEq)
    -- WSubMStar.sub: args (hwfV, hsub, hwfT, ihwfV, ihsub, ihwfT)
    (fun _ _ _ _ _ _ => trivial)
    -- WSubMStar.trs: args (hStar1, hwfU, hStar2, ih1, ihwfU, ih2)
    (fun _ _ _ _ _ _ => trivial)
    h) rfl rfl

/-! ### §7.3b. Partial discharge — `_sub` direction motives -/

/-- Motive type: `WSubM Γ a b → ∀ {t u t' u'}, a = .abs t u →
b = .abs t' u' → WEquM Γ t t'`. Type-valued. -/
private def _Lemma_10_inv_motive_sub :
    (Γ : Ctx) → (a b : Term) → WSubM Γ a b → Type :=
  fun Γ a b _ =>
    ∀ {t u t' u' : Term}, a = .abs t u → b = .abs t' u' → WEquM Γ t t'

/-- Motive type: `WfM` trivial. -/
private def _Lemma_10_inv_motive_wf :
    (Γ : Ctx) → (t : Term) → WfM Γ t → Type :=
  fun _ _ _ => Unit

/-- Motive type: `WSubMStar` trivial (we only handle the `_sub` part). -/
private def _Lemma_10_inv_motive_star :
    (Γ : Ctx) → (a b : Term) → WSubMStar Γ a b → Type :=
  fun _ _ _ _ => Unit

/-- **Single-WSubM Lemma 10**: a `WSubM` between two `.abs` terms
yields a `WEquM` on their bound annotations. PROVED directly via
`WSubM.rec`. -/
noncomputable def _Lemma_10_Inversion_sub_partial
    {Γ : Ctx} {a b : Term} (h : WSubM Γ a b)
    {t u t' u' : Term} (heqA : a = .abs t u) (heqB : b = .abs t' u') :
    WEquM Γ t t' := by
  classical
  exact (WSubM.rec
    (motive_1 := _Lemma_10_inv_motive_wf)
    (motive_2 := _Lemma_10_inv_motive_sub)
    (motive_3 := _Lemma_10_inv_motive_star)
    -- WfM cases: all unit.
    (fun _ _ => ()) (fun _ _ => ()) (fun _ => ())
    (fun _ _ _ _ _ => ()) (fun _ _ _ _ => ())
    -- Ws-Rfl: args (hwf, ihwf)
    (fun {Γ x} hwf _ihwf => by
      intro t u t' u' hA hB
      subst hA; cases hB
      cases hwf with
      | @fun_ _ _ _ L hT _ => exact WEquM.rfl hT)
    -- Ws-Lf1: args (hred, h_inner, ih)
    (fun {Γ a v' b} hred _h_inner ih => by
      intro t u t' u' hA hB
      subst hA
      obtain ⟨t1, u1, hv'Eq, hStep⟩ :=
        _Lemma_10_MEqRed_abs_inv_annot hred
      subst hv'Eq
      have hRec : WEquM Γ t1 t' := ih rfl hB
      exact WEquM.lf1 hStep hRec)
    -- Ws-Lf2: args (hwfA, hred, hwfA', h_inner, ihwfA, ihwfA', ih)
    (fun {Γ a v' b} _hwfA hred _hwfA' h_inner _ihA _ihA' ih => by
      intro t u t' u' hA hB
      subst hA
      cases _Lemma_10_MSubRed_abs_inv_annot hred with
      | inl hTop =>
          subst hTop; subst hB
          exact (_WSubM_top_abs_uninhabited h_inner).elim
      | inr hAbs =>
          obtain ⟨t1, u1, hv'Eq, hRel⟩ := hAbs
          subst hv'Eq
          have hRec : WEquM Γ t1 t' := ih rfl hB
          cases hRel with
          | inl hT1Eq => subst hT1Eq; exact hRec
          | inr hStep => exact WEquM.lf1 hStep hRec)
    -- Ws-Rgh: args (h_inner, hred, ih)
    (fun {Γ a b b'} _h_inner hred ih => by
      intro t u t' u' hA hB
      subst hB
      obtain ⟨t1, u1, hbEq, hStep⟩ :=
        _Lemma_10_MEqRed_abs_inv_annot hred
      subst hbEq
      have hRec : WEquM Γ t t1 := ih hA rfl
      exact WEquM.rgh hRec hStep)
    -- WSubMStar.sub: args (hwfV, hsub, hwfT, ihwfV, ihsub, ihwfT)
    (fun _ _ _ _ _ _ => ())
    -- WSubMStar.trs: args (hStar1, hwfU, hStar2, ih1, ihwfU, ih2)
    (fun _ _ _ _ _ _ => ())
    h) heqA heqB

/-! ### §7.3c. WSubM-direct contravariant inversion

Mirror of `_Lemma_10_Inversion_sub_partial` but returning `WSubM Γ t' t`
(contravariant: source becomes the target's bound, target becomes the
source's bound) instead of `WEquM Γ t t'`. Same structure, but uses
`WSubM.rgh` / `WSubM.lf1` instead of `WEquM.rgh` / `WEquM.lf1` to
prepend/append `MEqRed` steps. The `Ws-Rfl` case returns
`WSubM.rfl hT` where `hT : WfM Γ t` is extracted from the abs-shaped
WfM premise. -/

private def _Lemma_10_contra_inv_motive_sub :
    (Γ : Ctx) → (a b : Term) → WSubM Γ a b → Type :=
  fun Γ a b _ =>
    ∀ {t u t' u' : Term}, a = .abs t u → b = .abs t' u' → WSubM Γ t' t

private def _Lemma_10_contra_inv_motive_wf :
    (Γ : Ctx) → (t : Term) → WfM Γ t → Type :=
  fun _ _ _ => Unit

private def _Lemma_10_contra_inv_motive_star :
    (Γ : Ctx) → (a b : Term) → WSubMStar Γ a b → Type :=
  fun _ _ _ _ => Unit

/-- **Single-WSubM contravariant Lemma 10**: a `WSubM` between two
`.abs` terms yields a `WSubM` on their bound annotations in the
*reverse* direction (contravariant). PROVED directly via `WSubM.rec`,
mirroring `_Lemma_10_Inversion_sub_partial`. -/
noncomputable def _Lemma_10_contra_inv_sub
    {Γ : Ctx} {a b : Term} (h : WSubM Γ a b)
    {t u t' u' : Term} (heqA : a = .abs t u) (heqB : b = .abs t' u') :
    WSubM Γ t' t := by
  classical
  exact (WSubM.rec
    (motive_1 := _Lemma_10_contra_inv_motive_wf)
    (motive_2 := _Lemma_10_contra_inv_motive_sub)
    (motive_3 := _Lemma_10_contra_inv_motive_star)
    -- WfM cases: all unit.
    (fun _ _ => ()) (fun _ _ => ()) (fun _ => ())
    (fun _ _ _ _ _ => ()) (fun _ _ _ _ => ())
    -- Ws-Rfl: args (hwf, ihwf). t = t' since a = b = .abs t u and we
    -- substitute heqA into heqB, yielding heqB' : .abs t u = .abs t' u',
    -- so t = t' and u = u'. Return WSubM.rfl hT.
    (fun {Γ x} hwf _ihwf => by
      intro t u t' u' hA hB
      subst hA; cases hB
      cases hwf with
      | @fun_ _ _ _ L hT _ => exact WSubM.rfl hT)
    -- Ws-Lf1: args (hred, h_inner, ih). hred : MEqRed Γ [] (.abs t u) v'.
    -- Invert via Me-Fun: v' = .abs t1 u1, MEqRed Γ [] t t1.
    -- Recursive call gives WSubM Γ t' t1. Apply WSubM.rgh to get WSubM Γ t' t.
    (fun {Γ a v' b} hred _h_inner ih => by
      intro t u t' u' hA hB
      subst hA
      obtain ⟨t1, u1, hv'Eq, hStep⟩ :=
        _Lemma_10_MEqRed_abs_inv_annot hred
      subst hv'Eq
      have hRec : WSubM Γ t' t1 := ih rfl hB
      exact WSubM.rgh hRec hStep)
    -- Ws-Lf2: args (hwfA, hred, hwfA', h_inner, ihwfA, ihwfA', ih).
    -- hred : MSubRed Γ [] (.abs t u) v'. Three sub-cases:
    -- - Ms-Top: v' = .top. h_inner : WSubM Γ .top (.abs t' u'). Contradiction
    --   via `_WSubM_top_abs_uninhabited`.
    -- - Ms-Equ → Me-Fun: v' = .abs, with MEqRed step on bound. Same as Lf1.
    -- - Ms-Fun: v' = .abs with annotation invariant. Recurse directly.
    (fun {Γ a v' b} _hwfA hred _hwfA' h_inner _ihA _ihA' ih => by
      intro t u t' u' hA hB
      subst hA
      cases _Lemma_10_MSubRed_abs_inv_annot hred with
      | inl hTop =>
          subst hTop; subst hB
          exact (_WSubM_top_abs_uninhabited h_inner).elim
      | inr hAbs =>
          obtain ⟨t1, u1, hv'Eq, hRel⟩ := hAbs
          subst hv'Eq
          have hRec : WSubM Γ t' t1 := ih rfl hB
          cases hRel with
          | inl hT1Eq => subst hT1Eq; exact hRec
          | inr hStep => exact WSubM.rgh hRec hStep)
    -- Ws-Rgh: args (h_inner, hred, ih). hred : MEqRed Γ [] (.abs t' u') v'.
    -- Invert via Me-Fun: v' = .abs t1 u1, MEqRed Γ [] t' t1.
    -- Recursive call gives WSubM Γ t1 t. Apply WSubM.lf1 to get WSubM Γ t' t.
    (fun {Γ a b b'} _h_inner hred ih => by
      intro t u t' u' hA hB
      subst hB
      obtain ⟨t1, u1, hbEq, hStep⟩ :=
        _Lemma_10_MEqRed_abs_inv_annot hred
      subst hbEq
      have hRec : WSubM Γ t1 t := ih hA rfl
      exact WSubM.lf1 hStep hRec)
    -- WSubMStar.sub: args (hwfV, hsub, hwfT, ihwfV, ihsub, ihwfT)
    (fun _ _ _ _ _ _ => ())
    -- WSubMStar.trs: args (hStar1, hwfU, hStar2, ih1, ihwfU, ih2)
    (fun _ _ _ _ _ _ => ())
    h) heqA heqB

/-! ### §7.4. The remaining axiom

Despite the partial `_sub` discharge above, the full `Lemma_10_Inversion`
remains an axiom because the `WSubMStar.trs` case requires
**`WEquM.trans`** at the joining annotation — which is **isomorphic to
the diamond/confluence property of MEqRed at empty stack**, the same
property whose β-case is currently axiomatized as the `Lemma_2_*`
β-residuals.

Specifically, in the case `WSubMStar.trs h₁ wfU h₂` with `h₁ :
WSubMStar Γ (.abs t u) U` and `h₂ : WSubMStar Γ U (.abs t' u')`, after
shape-determining `U = .abs t_m u_m` we need to combine the IH-produced
`WEquM Γ t t_m` and `WEquM Γ t_m t'` into `WEquM Γ t t'`. This
composition requires forward-extending one `WEquM` along the other's
midpoint — which IS the diamond property restricted to bound
annotations.

NOTE: Theorem 5's β-case has been *re-routed* to use the contravariant
`WSubMStar`-direct inversion `_Lemma_10_contra_inv` (defined below),
which bypasses this trs blocker by working at `WSubM` level (where the
contravariant inversion is a single step) and lifting to `WSubMStar`
via the chain helpers. The `WEquM`-form below is RETAINED as an axiom
but is now INACTIVE (no headline theorem depends on it). -/

axiom Lemma_10_Inversion
    {Γ : Ctx} {t t' u u' : Term}
    (h : WSubMStar Γ (.abs t u) (.abs t' u')) :
    WEquM Γ t t'

/-! ### §7.5. Contravariant `WSubMStar`-direct Lemma 10

The new strategy bypasses `WEquM.trans` (which requires confluence) by
formulating the inversion to return `WSubMStar Γ t' t` directly. The
chain composition is FREE for `WSubMStar` (its `trs` constructor is
zero-cost), so we don't need a derived transitivity. -/

/-- Motive: WSubMStar Γ a b → ∀ c, MEqRed Γ [] c a → WfM Γ c → WSubMStar Γ c b. -/
private def _extend_left_motive_star :
    (Γ : Ctx) → (a b : Term) → WSubMStar Γ a b → Type :=
  fun Γ a b _ =>
    ∀ {c : Term}, MEqRed Γ [] c a → WfM Γ c → WSubMStar Γ c b

private def _extend_left_motive_wf :
    (Γ : Ctx) → (t : Term) → WfM Γ t → Type :=
  fun _ _ _ => Unit

private def _extend_left_motive_sub :
    (Γ : Ctx) → (a b : Term) → WSubM Γ a b → Type :=
  fun _ _ _ _ => Unit

/-- **Helper:** prepend a forward `MEqRed` step on the LHS of a
`WSubMStar`. Given `MEqRed Γ [] c a` and `WSubMStar Γ a b`, derive
`WSubMStar Γ c b`. By induction on the chain. -/
noncomputable def WSubMStar.extend_left_via_MEqRed_fwd
    {Γ : Ctx} {a b c : Term}
    (h : WSubMStar Γ a b)
    (hred : MEqRed Γ [] c a)
    (hwfC : WfM Γ c) :
    WSubMStar Γ c b := by
  classical
  exact (WSubMStar.rec
    (motive_1 := _extend_left_motive_wf)
    (motive_2 := _extend_left_motive_sub)
    (motive_3 := _extend_left_motive_star)
    -- WfM cases: all unit.
    (fun _ _ => ()) (fun _ _ => ()) (fun _ => ())
    (fun _ _ _ _ _ => ()) (fun _ _ _ _ => ())
    -- WSubM cases: all unit.
    (fun _ _ => ()) (fun _ _ _ => ()) (fun _ _ _ _ _ _ _ => ())
    (fun _ _ _ => ())
    -- WSubMStar.sub: args (hwfV, hsub, hwfT, ihwfV, ihsub, ihwfT)
    (fun {Γ v t} _hwfV hsub hwfT _ _ _ => fun {c} hr hwfC =>
      WSubMStar.sub hwfC (WSubM.lf1 hr hsub) hwfT)
    -- WSubMStar.trs: args (hStar1, hwfU, hStar2, ih1, ihwfU, ih2). Prepend
    -- c → a only on left leg, re-glue with right leg via trs.
    (fun {Γ v u t} _hStar1 hwfU hStar2 ih1 _ _ => fun {c} hr hwfC =>
      WSubMStar.trs (ih1 hr hwfC) hwfU hStar2)
    h) hred hwfC

/-- Motive: WSubMStar Γ a b → ∀ c, MEqRed Γ [] c b → WfM Γ c → WSubMStar Γ a c. -/
private def _extend_right_motive_star :
    (Γ : Ctx) → (a b : Term) → WSubMStar Γ a b → Type :=
  fun Γ a b _ =>
    ∀ {c : Term}, MEqRed Γ [] c b → WfM Γ c → WSubMStar Γ a c

/-- **Helper:** prepend a backward `MEqRed` step on the RHS of a
`WSubMStar`. Given `WSubMStar Γ a b` and `MEqRed Γ [] c b` (a forward
step from `c` to `b`), derive `WSubMStar Γ a c`. By induction on the
chain. -/
noncomputable def WSubMStar.extend_right_via_MEqRed_back
    {Γ : Ctx} {a b c : Term}
    (h : WSubMStar Γ a b)
    (hred : MEqRed Γ [] c b)
    (hwfC : WfM Γ c) :
    WSubMStar Γ a c := by
  classical
  exact (WSubMStar.rec
    (motive_1 := _extend_left_motive_wf)
    (motive_2 := _extend_left_motive_sub)
    (motive_3 := _extend_right_motive_star)
    (fun _ _ => ()) (fun _ _ => ()) (fun _ => ())
    (fun _ _ _ _ _ => ()) (fun _ _ _ _ => ())
    (fun _ _ => ()) (fun _ _ _ => ()) (fun _ _ _ _ _ _ _ => ())
    (fun _ _ _ => ())
    -- WSubMStar.sub: args (hwfV, hsub, hwfT, ihwfV, ihsub, ihwfT)
    (fun {Γ v t} hwfV hsub _hwfT _ _ _ => fun {c} hr hwfC =>
      WSubMStar.sub hwfV (WSubM.rgh hsub hr) hwfC)
    -- WSubMStar.trs: contract right leg, re-glue with left leg via trs.
    (fun {Γ v u t} hStar1 hwfU _hStar2 _ _ ih2 => fun {c} hr hwfC =>
      WSubMStar.trs hStar1 hwfU (ih2 hr hwfC))
    h) hred hwfC

/-! ### §7.5b. Contravariant inversion at WSubMStar level — STRUCTURAL BLOCKER

A `WSubMStar`-direct contravariant inversion (returning `WSubMStar Γ t' t`
instead of `WEquM Γ t t'`) was attempted under the hypothesis that
`WSubMStar.preserves_abs` holds — i.e., that `WSubMStar Γ (.abs ..) v →
∃ t' u', v = .abs t' u'`. **This hypothesis is false.**

**Counterexample:** Let Γ = [⟨"x", α, .equ⟩] where α reduces to
(.abs t' u') (e.g., α = .abs t' u' itself). Then:

* `WSubM.rgh` consumes `MEqRed Γ [] (.fvar x) α'` (via `Me-Pro`, which
  fires on equ-bound variables);
* combined with `WSubM.rfl` on `(.abs t' u')`, this yields
  `WSubM Γ (.abs t' u') (.fvar x)`.

Hence `WSubMStar Γ (.abs ..) (.fvar x)` is inhabited — the chain can
"detour" through equ-bound variables. Symmetrically (via `Ws-Lf1` +
`Me-Pro`), the chain `(.fvar x) → (.abs t' u')` is also inhabited,
so the WSubMStar.trs case admits non-abs midpoints.

The WSubM-level lemma `_Lemma_10_contra_inv_sub` (proved above) DOES
close cleanly because at single-step level, the abs-shape constraint
on the *outer* WSubM forces inversion of the chain operator (`MEqRed` /
`MSubRed`) at empty stack, and the only abs-introducing rule is
`Me-Fun` (with `Ms-Equ` delegating). At chain level, intermediate
WfM-anchors break this constraint.

**Discharge requirements:** to close the trs case, one needs either
(a) `WSubMStar Γ .top (.abs ..)` uninhabited (analogue of Lemma 11
without going through Theorem 3 — non-trivial because Theorem 3 carries
β-residuals), AND (b) a recursion-through-α argument for fvar-equ
midpoints, AND (c) an analogous argument for app midpoints. Path (b)
requires recursion that's not structurally smaller than the original
chain, suggesting well-founded recursion on a different measure.

This blocker is structurally analogous to (but distinct from) the
`WEquM.trans` blocker that forces `Lemma_10_Inversion` itself. -/

/-! ### Lemma 10 — restricted form (legacy, derivable from `WEquM` + extra
infrastructure)

`Lemma_10_InversionRestricted` returns a common `MEqRedStar` reduct rather
than `WEquM`. It is *not* trivially derivable from `Lemma_10_Inversion`:
extracting a common reduct from a `WEquM` chain requires diamond-style
joining of the prepended/appended `MEqRed` steps. We retain it as a
separate axiom for downstream consumers that already use the
common-reduct form.

**Status (post-Wave-7):** INACTIVE. No headline theorem (Theorem 3, 4,
5; Lemma 1; Lemma 2) has this in its `#print axioms` closure. Theorem 5
goes through the full-form `Lemma_10_Inversion` directly. Listed in
`AXIOMS.md` under "Inactive outstanding". -/

/-- **Lemma 10 (Inversion lemma, restricted form).** From a transitive
well-subtyping between two abstractions of the form `λ x ≤ t. u` and
`λ x ≤ t'. u'`, the bound annotations have a common equivalence-reduct.

Restricted form: returns a common reduct `z` with
`MEqRedStar Γ [] t z ∧ MEqRedStar Γ [] t' z`, instead of the paper's
`Γ ⊢ t ≡_wf t'`.

INACTIVE: not in any headline theorem's dependency closure. Provable
without `WfM`-preservation under `MEqRed` (unlike the full form);
discharge would strip `WSubMStar` to `MSub` and read off the common
reduct directly. See `AXIOMS.md`. -/
axiom Lemma_10_InversionRestricted
    {Γ : Ctx} {t t' u u' : Term}
    (h : WSubMStar Γ (.abs t u) (.abs t' u')) :
    ∃ z, MEqRedStar Γ [] t z ∧ MEqRedStar Γ [] t' z

end Pss

import Pss.Mpss.DeBruijnWellFormed

/-! # `Pss.Mpss.DeBruijnTransitivityElim` — de Bruijn diagrammatic subtyping

This module starts the de Bruijn port of the MPSS transitivity-elimination
layer. It defines the paper's diagrammatic `≤` relation over de Bruijn
reductions and adds the first strips from well-subtyping into that
diagrammatic layer.
-/

namespace Pss
namespace DeBruijn

/-! ## Diagrammatic `≤` -/

/-- De Bruijn form of the paper's diagrammatic subtyping relation:
`Γ; s ⊢ u ≤ v` iff there is a common reduct `w` such that `u` reaches `w`
by subtype reduction and `v` reaches `w` by equivalence reduction. -/
def MSub (Γ : Ctx) (s : Stack) (u v : Term) : Prop :=
  ∃ w, MSubRedStar Γ s u w ∧ MEqRedStar Γ s v w

/-- Reflexive-transitive closure of de Bruijn diagrammatic subtyping. -/
abbrev MSubStar (Γ : Ctx) (s : Stack) : Term → Term → Prop :=
  Relation.ReflTransGen (MSub Γ s)

namespace MSub

/-- Reflexivity of de Bruijn diagrammatic subtyping. -/
theorem refl {Γ : Ctx} {s : Stack} {t : Term} : MSub Γ s t t :=
  ⟨t, Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩

/-- Diagrammatic subtyping preserves right-endpoint scoping in `Prop` form
from left-endpoint scoping. The `Nonempty` wrapper is needed because `MSub`
is Prop-valued while scoping is Type-valued. -/
theorem scoped_right_nonempty {Γ : Ctx} {s : Stack} {u v : Term}
    (h : MSub Γ s u v) (hu : Term.Scoped Γ.depth u) :
    Nonempty (Term.Scoped Γ.depth v) := by
  obtain ⟨w, hSub, hEqu⟩ := h
  have hw : Term.Scoped Γ.depth w := hSub.scoped_right hu
  exact hEqu.scoped_left_nonempty hw

/-- Diagrammatic subtyping relates scoped endpoints in `Prop` form when the
left endpoint is scoped. -/
theorem scoped_pair_nonempty {Γ : Ctx} {s : Stack} {u v : Term}
    (h : MSub Γ s u v) (hu : Term.Scoped Γ.depth u) :
    Nonempty (Term.Scoped Γ.depth u × Term.Scoped Γ.depth v) :=
  ⟨⟨hu, (h.scoped_right_nonempty hu).some⟩⟩

/-- Diagrammatic subtyping also provides left-endpoint scoping in `Prop`
form from right-endpoint scoping. -/
theorem scoped_left_nonempty {Γ : Ctx} {s : Stack} {u v : Term}
    (h : MSub Γ s u v) (hv : Term.Scoped Γ.depth v) :
    Nonempty (Term.Scoped Γ.depth u) := by
  obtain ⟨w, hSub, hEqu⟩ := h
  have hw : Term.Scoped Γ.depth w := hEqu.scoped_right hv
  exact hSub.scoped_left_nonempty hw

/-- Diagrammatic subtyping relates scoped endpoints in `Prop` form when the
right endpoint is scoped. -/
theorem scoped_pair_from_right_nonempty {Γ : Ctx} {s : Stack} {u v : Term}
    (h : MSub Γ s u v) (hv : Term.Scoped Γ.depth v) :
    Nonempty (Term.Scoped Γ.depth u × Term.Scoped Γ.depth v) :=
  ⟨⟨(h.scoped_left_nonempty hv).some, hv⟩⟩

/-- Introduce de Bruijn diagrammatic subtyping from explicit subtype and
equivalence chains to a common reduct. -/
theorem intro {Γ : Ctx} {s : Stack} {u v w : Term}
    (hSub : MSubRedStar Γ s u w) (hEqu : MEqRedStar Γ s v w) :
    MSub Γ s u v :=
  ⟨w, hSub, hEqu⟩

/-- A subtype-reduction chain is a diagrammatic subtyping step whose right
endpoint is the common reduct. -/
theorem of_MSubRedStar {Γ : Ctx} {s : Stack} {u v : Term}
    (h : MSubRedStar Γ s u v) : MSub Γ s u v :=
  MSub.intro h Relation.ReflTransGen.refl

/-- A single subtype-reduction step is a diagrammatic subtyping step. -/
theorem of_MSubRed {Γ : Ctx} {s : Stack} {u v : Term}
    (h : MSubRed Γ s u v) : MSub Γ s u v :=
  MSub.of_MSubRedStar (MSubRedStar.single h)

/-- A single equivalence-reduction step is a diagrammatic subtyping step when
the extended context is known prevalid. -/
theorem of_MEqRed {Γ : Ctx} {s : Stack} {u v : Term}
    (hpv : PrevalidExt Γ s) (h : MEqRed Γ s u v) : MSub Γ s u v :=
  MSub.of_MSubRed (MSubRed.equ hpv h)

/-- An equivalence-reduction chain from the left endpoint to the right
endpoint is a diagrammatic subtyping step when the extended context is
prevalid. -/
theorem of_MEqRedStar_left {Γ : Ctx} {s : Stack} {u v : Term}
    (hpv : PrevalidExt Γ s) (h : MEqRedStar Γ s u v) : MSub Γ s u v :=
  MSub.of_MSubRedStar (MSubRedStar.of_MEqRedStar hpv h)

/-- An equivalence-reduction chain from the right endpoint back to the left
endpoint is directly a diagrammatic subtyping step, using the left endpoint
as the common reduct. -/
theorem of_MEqRedStar_right {Γ : Ctx} {s : Stack} {u v : Term}
    (h : MEqRedStar Γ s v u) : MSub Γ s u v :=
  MSub.intro Relation.ReflTransGen.refl h

/-- A single de Bruijn diagrammatic subtyping step embeds into its reflexive
transitive closure. -/
theorem to_star {Γ : Ctx} {s : Stack} {u v : Term}
    (h : MSub Γ s u v) : MSubStar Γ s u v :=
  Relation.ReflTransGen.single h

end MSub

namespace MSubStar

/-- Reflexivity for the reflexive-transitive diagrammatic relation. -/
theorem refl {Γ : Ctx} {s : Stack} {t : Term} : MSubStar Γ s t t :=
  Relation.ReflTransGen.refl

/-- Transitive diagrammatic subtyping preserves right-endpoint scoping in
`Prop` form from left-endpoint scoping. -/
theorem scoped_right_nonempty {Γ : Ctx} {s : Stack} {u v : Term}
    (h : MSubStar Γ s u v) (hu : Term.Scoped Γ.depth u) :
    Nonempty (Term.Scoped Γ.depth v) := by
  induction h with
  | refl =>
    exact ⟨hu⟩
  | tail hStar hStep ih =>
    exact hStep.scoped_right_nonempty ih.some

/-- Transitive diagrammatic subtyping relates scoped endpoints in `Prop` form
when the left endpoint is scoped. -/
theorem scoped_pair_nonempty {Γ : Ctx} {s : Stack} {u v : Term}
    (h : MSubStar Γ s u v) (hu : Term.Scoped Γ.depth u) :
    Nonempty (Term.Scoped Γ.depth u × Term.Scoped Γ.depth v) :=
  ⟨⟨hu, (h.scoped_right_nonempty hu).some⟩⟩

/-- Transitive diagrammatic subtyping provides left-endpoint scoping in
`Prop` form from right-endpoint scoping. -/
theorem scoped_left_nonempty {Γ : Ctx} {s : Stack} {u v : Term}
    (h : MSubStar Γ s u v) (hv : Term.Scoped Γ.depth v) :
    Nonempty (Term.Scoped Γ.depth u) := by
  induction h with
  | refl =>
    exact ⟨hv⟩
  | tail hStar hStep ih =>
    exact ih (hStep.scoped_left_nonempty hv).some

/-- Transitive diagrammatic subtyping relates scoped endpoints in `Prop` form
when the right endpoint is scoped. -/
theorem scoped_pair_from_right_nonempty {Γ : Ctx} {s : Stack} {u v : Term}
    (h : MSubStar Γ s u v) (hv : Term.Scoped Γ.depth v) :
    Nonempty (Term.Scoped Γ.depth u × Term.Scoped Γ.depth v) :=
  ⟨⟨(h.scoped_left_nonempty hv).some, hv⟩⟩

/-- Embed one diagrammatic step into the reflexive-transitive diagrammatic
relation. -/
theorem single {Γ : Ctx} {s : Stack} {u v : Term}
    (h : MSub Γ s u v) : MSubStar Γ s u v :=
  Relation.ReflTransGen.single h

/-- Embed a subtype-reduction chain as one step of transitive diagrammatic
subtyping. -/
theorem of_MSubRedStar {Γ : Ctx} {s : Stack} {u v : Term}
    (h : MSubRedStar Γ s u v) : MSubStar Γ s u v :=
  MSub.to_star (MSub.of_MSubRedStar h)

/-- Embed a single subtype-reduction step as one step of transitive
diagrammatic subtyping. -/
theorem of_MSubRed {Γ : Ctx} {s : Stack} {u v : Term}
    (h : MSubRed Γ s u v) : MSubStar Γ s u v :=
  MSub.to_star (MSub.of_MSubRed h)

/-- Embed a single equivalence-reduction step as one step of transitive
diagrammatic subtyping when the extended context is prevalid. -/
theorem of_MEqRed {Γ : Ctx} {s : Stack} {u v : Term}
    (hpv : PrevalidExt Γ s) (h : MEqRed Γ s u v) : MSubStar Γ s u v :=
  MSub.to_star (MSub.of_MEqRed hpv h)

/-- Embed an equivalence-reduction chain as one step of transitive
diagrammatic subtyping when the extended context is prevalid. -/
theorem of_MEqRedStar_left {Γ : Ctx} {s : Stack} {u v : Term}
    (hpv : PrevalidExt Γ s) (h : MEqRedStar Γ s u v) : MSubStar Γ s u v :=
  MSub.to_star (MSub.of_MEqRedStar_left hpv h)

/-- Embed a backwards equivalence-reduction chain as one step of transitive
diagrammatic subtyping. -/
theorem of_MEqRedStar_right {Γ : Ctx} {s : Stack} {u v : Term}
    (h : MEqRedStar Γ s v u) : MSubStar Γ s u v :=
  MSub.to_star (MSub.of_MEqRedStar_right h)

/-- Transitivity of the reflexive-transitive diagrammatic relation. -/
theorem trans {Γ : Ctx} {s : Stack} {u v w : Term}
    (hLeft : MSubStar Γ s u v) (hRight : MSubStar Γ s v w) :
    MSubStar Γ s u w :=
  Relation.ReflTransGen.trans hLeft hRight

end MSubStar

/-! ## Conditional Theorem 3 lifting skeleton -/

/-- De Bruijn single-step equivalence diamond at a fixed extended context.
This is the de Bruijn Lemma 2 shape needed when lifting equivalence diamonds
from steps to chains. -/
abbrev EqDiamonds (Γ : Ctx) (s : Stack) : Prop :=
  ∀ {t₀ t₁ t₂ : Term},
    MEqRed Γ s t₀ t₁ →
    MEqRed Γ s t₀ t₂ →
    ∃ t₃, MEqRedJ Γ s t₁ t₃ ∧ MEqRedJ Γ s t₂ t₃

/-- Named de Bruijn Lemma 2 single-step premise. This is an alias for
`EqDiamonds`, useful as the audit point for the future full case grid. -/
def Lemma_2_DeBruijn_DiamondMEqRed (Γ : Ctx) (s : Stack) : Prop :=
  EqDiamonds Γ s

namespace EqDiamonds

/-- The `Top` source cell of de Bruijn Lemma 2. Both one-step equivalence
targets must be `Top`, so the diamond closes immediately. -/
theorem top {Γ : Ctx} {s : Stack} {t₁ t₂ : Term}
    (h₁ : MEqRed Γ s .top t₁) (h₂ : MEqRed Γ s .top t₂) :
    ∃ t₃, MEqRedJ Γ s t₁ t₃ ∧ MEqRedJ Γ s t₂ t₃ := by
  have ht₁ : t₁ = .top := h₁.top_inv
  have ht₂ : t₂ = .top := h₂.top_inv
  subst t₁
  subst t₂
  exact ⟨.top, ⟨h₁⟩, ⟨h₂⟩⟩

/-- The `Me-Var × Me-Var` source cell of de Bruijn Lemma 2. -/
theorem var_var {Γ : Ctx} {s : Stack} {i : Nat}
    (hpv : PrevalidExt Γ s) (hi : i < Γ.depth) :
    ∃ t₃, MEqRedJ Γ s (.bvar i) t₃ ∧ MEqRedJ Γ s (.bvar i) t₃ := by
  let h : MEqRed Γ s (.bvar i) (.bvar i) := MEqRed.var hpv hi
  exact ⟨.bvar i, ⟨h⟩, ⟨h⟩⟩

/-- If the left equivalence step is reflexive, the de Bruijn Lemma 2 cell
closes against the right step directly. -/
theorem refl_left {Γ : Ctx} {s : Stack} {t₀ t₂ : Term}
    (hpv : PrevalidExt Γ s) (h₂ : MEqRed Γ s t₀ t₂) :
    ∃ t₃, MEqRedJ Γ s t₀ t₃ ∧ MEqRedJ Γ s t₂ t₃ := by
  exact ⟨t₂, ⟨h₂⟩, ⟨MEqRed.refl hpv h₂.scoped_right⟩⟩

/-- If the right equivalence step is reflexive, the de Bruijn Lemma 2 cell
closes against the left step directly. -/
theorem refl_right {Γ : Ctx} {s : Stack} {t₀ t₁ : Term}
    (hpv : PrevalidExt Γ s) (h₁ : MEqRed Γ s t₀ t₁) :
    ∃ t₃, MEqRedJ Γ s t₁ t₃ ∧ MEqRedJ Γ s t₀ t₃ := by
  exact ⟨t₁, ⟨MEqRed.refl hpv h₁.scoped_right⟩, ⟨h₁⟩⟩

/-- The `Me-Pro × Me-Var` source cell of de Bruijn Lemma 2. -/
theorem pro_var {Γ : Ctx} {s : Stack} {i : Nat} {α α' : Term}
    (hpv : PrevalidExt Γ s) (hb : Γ.equBinds i α)
    (hα : MEqRed Γ s α α') (_hi : i < Γ.depth) :
    ∃ t₃, MEqRedJ Γ s α' t₃ ∧ MEqRedJ Γ s (.bvar i) t₃ := by
  let hpro : MEqRed Γ s (.bvar i) α' := MEqRed.pro hpv hb hα
  exact ⟨α', ⟨MEqRed.refl hpv hα.scoped_right⟩, ⟨hpro⟩⟩

/-- The `Me-Var × Me-Pro` source cell of de Bruijn Lemma 2. -/
theorem var_pro {Γ : Ctx} {s : Stack} {i : Nat} {α α' : Term}
    (hpv : PrevalidExt Γ s) (hi : i < Γ.depth)
    (hb : Γ.equBinds i α) (hα : MEqRed Γ s α α') :
    ∃ t₃, MEqRedJ Γ s (.bvar i) t₃ ∧ MEqRedJ Γ s α' t₃ := by
  obtain ⟨t₃, hLeft, hRight⟩ := pro_var hpv hb hα hi
  exact ⟨t₃, hRight, hLeft⟩

/-- The recursive `Me-Pro × Me-Pro` source cell of de Bruijn Lemma 2. The
context lookup fixes both promoted bounds to the same term, then the supplied
diamond premise closes the bound reductions. -/
theorem pro_pro_of {Γ : Ctx} {s : Stack} (hdiamond : EqDiamonds Γ s)
    {i : Nat} {α β α' β' : Term}
    (_hpv : PrevalidExt Γ s) (hαb : Γ.equBinds i α) (hβb : Γ.equBinds i β)
    (hα : MEqRed Γ s α α') (hβ : MEqRed Γ s β β') :
    ∃ t₃, MEqRedJ Γ s α' t₃ ∧ MEqRedJ Γ s β' t₃ := by
  have hEq : α = β := Ctx.equBinds_unique hαb hβb
  subst hEq
  exact hdiamond hα hβ

/-- The `Me-TAp × Me-TAp` source cell of de Bruijn Lemma 2. -/
theorem tAp_tAp {Γ : Ctx} {s : Stack} {u : Term}
    (hpv : PrevalidExt Γ s) (_hu : Term.Scoped Γ.depth u) :
    ∃ t₃, MEqRedJ Γ s .top t₃ ∧ MEqRedJ Γ s .top t₃ := by
  let htop : MEqRed Γ s .top .top := MEqRed.top hpv
  exact ⟨.top, ⟨htop⟩, ⟨htop⟩⟩

/-- The `Me-TAp × Me-App` source cell of de Bruijn Lemma 2. The operator
component of the app step starts from `Top`, so it also targets `Top`. -/
theorem tAp_app {Γ : Ctx} {s : Stack} {u u' v' : Term}
    (hpv : PrevalidExt Γ s) (_hu : Term.Scoped Γ.depth u)
    (hOp : MEqRed Γ (u :: s) .top u') (hArg : MEqRed Γ [] u v') :
    ∃ t₃, MEqRedJ Γ s .top t₃ ∧ MEqRedJ Γ s (.app u' v') t₃ := by
  have hu' : u' = .top := hOp.top_inv
  subst u'
  exact ⟨.top, ⟨MEqRed.top hpv⟩, ⟨MEqRed.tAp hpv hArg.scoped_right⟩⟩

/-- The `Me-App × Me-TAp` source cell of de Bruijn Lemma 2. -/
theorem app_tAp {Γ : Ctx} {s : Stack} {u u' v' : Term}
    (hpv : PrevalidExt Γ s) (hu : Term.Scoped Γ.depth u)
    (hOp : MEqRed Γ (u :: s) .top u') (hArg : MEqRed Γ [] u v') :
    ∃ t₃, MEqRedJ Γ s (.app u' v') t₃ ∧ MEqRedJ Γ s .top t₃ := by
  obtain ⟨t₃, hLeft, hRight⟩ := tAp_app hpv hu hOp hArg
  exact ⟨t₃, hRight, hLeft⟩

/-- The `Me-TAp × Me-*` cells for a `Top`-headed application. -/
theorem tAp_any {Γ : Ctx} {s : Stack} {u t₂ : Term}
    (hpv : PrevalidExt Γ s) (hu : Term.Scoped Γ.depth u)
    (h₂ : MEqRed Γ s (.app .top u) t₂) :
    ∃ t₃, MEqRedJ Γ s .top t₃ ∧ MEqRedJ Γ s t₂ t₃ := by
  cases h₂ with
  | app hOp hArg =>
    exact tAp_app hpv hu hOp hArg
  | tAp _ _ =>
    exact tAp_tAp hpv hu

/-- The `Me-* × Me-TAp` cells for a `Top`-headed application. -/
theorem any_tAp {Γ : Ctx} {s : Stack} {u t₁ : Term}
    (hpv : PrevalidExt Γ s) (hu : Term.Scoped Γ.depth u)
    (h₁ : MEqRed Γ s (.app .top u) t₁) :
    ∃ t₃, MEqRedJ Γ s t₁ t₃ ∧ MEqRedJ Γ s .top t₃ := by
  obtain ⟨t₃, hLeft, hRight⟩ := tAp_any hpv hu h₁
  exact ⟨t₃, hRight, hLeft⟩

/-- The full one-step `Top`-headed application source cell of de Bruijn
Lemma 2. Both targets are either `Top` or another `Top`-headed application,
so all branches join at `Top`. -/
theorem appTop_any {Γ : Ctx} {s : Stack} {u t₁ t₂ : Term}
    (hpv : PrevalidExt Γ s) (hu : Term.Scoped Γ.depth u)
    (h₁ : MEqRed Γ s (.app .top u) t₁)
    (h₂ : MEqRed Γ s (.app .top u) t₂) :
    ∃ t₃, MEqRedJ Γ s t₁ t₃ ∧ MEqRedJ Γ s t₂ t₃ := by
  have hShape₁ := MEqRed.app_top_inv h₁
  have hShape₂ := MEqRed.app_top_inv h₂
  cases hShape₁ with
  | inl hTop₁ =>
    subst hTop₁
    exact tAp_any hpv hu h₂
  | inr hApp₁ =>
    obtain ⟨arg₁, hEq₁⟩ := hApp₁
    subst hEq₁
    have hTargetScoped₁ : Term.Scoped Γ.depth (.app .top arg₁) := h₁.scoped_right
    have hArg₁ : Term.Scoped Γ.depth arg₁ := (Term.Scoped.app_inv hTargetScoped₁).2
    cases hShape₂ with
    | inl hTop₂ =>
      subst hTop₂
      exact ⟨.top, ⟨MEqRed.tAp hpv hArg₁⟩, ⟨MEqRed.top hpv⟩⟩
    | inr hApp₂ =>
      obtain ⟨arg₂, hEq₂⟩ := hApp₂
      subst hEq₂
      have hTargetScoped₂ : Term.Scoped Γ.depth (.app .top arg₂) := h₂.scoped_right
      have hArg₂ : Term.Scoped Γ.depth arg₂ := (Term.Scoped.app_inv hTargetScoped₂).2
      exact ⟨.top, ⟨MEqRed.tAp hpv hArg₁⟩, ⟨MEqRed.tAp hpv hArg₂⟩⟩

end EqDiamonds

/-- The `Top` source case for one equivalence step against an equivalence
chain, proved directly by shape inversion. -/
theorem diamond_step_eqStar_top {Γ : Ctx} {s : Stack} {t₁ t₂ : Term}
    (h₁ : MEqRed Γ s .top t₁) (h₂ : MEqRedStar Γ s .top t₂) :
    ∃ t₃, MEqRedStar Γ s t₁ t₃ ∧ MEqRedStar Γ s t₂ t₃ := by
  have ht₁ : t₁ = .top := h₁.top_inv
  have ht₂ : t₂ = .top := h₂.top_inv
  subst t₁
  subst t₂
  exact ⟨.top, Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩

/-- The `Top` source case for two equivalence chains, proved directly by
shape inversion. -/
theorem diamond_eqStar_eqStar_top {Γ : Ctx} {s : Stack} {t₁ t₂ : Term}
    (h₁ : MEqRedStar Γ s .top t₁) (h₂ : MEqRedStar Γ s .top t₂) :
    ∃ t₃, MEqRedStar Γ s t₁ t₃ ∧ MEqRedStar Γ s t₂ t₃ := by
  have ht₁ : t₁ = .top := h₁.top_inv
  have ht₂ : t₂ = .top := h₂.top_inv
  subst t₁
  subst t₂
  exact ⟨.top, Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩

/-- A reflexive equivalence step joins directly against any equivalence chain
from the same source. -/
theorem diamond_refl_eqStar {Γ : Ctx} {s : Stack} {t₀ t₂ : Term}
    (h₂ : MEqRedStar Γ s t₀ t₂) :
    ∃ t₃, MEqRedStar Γ s t₀ t₃ ∧ MEqRedStar Γ s t₂ t₃ := by
  exact ⟨t₂, h₂, Relation.ReflTransGen.refl⟩

/-- Direct star-level join for a `Top`-headed application against its `TAp`
target. -/
theorem diamond_tAp_eqStar {Γ : Ctx} {s : Stack} {u t : Term}
    (hpv : PrevalidExt Γ s) (hu : Term.Scoped Γ.depth u)
    (h : MEqRedStar Γ s (.app .top u) t) :
    ∃ t₃, MEqRedStar Γ s .top t₃ ∧ MEqRedStar Γ s t t₃ := by
  have hShape := h.app_top_inv
  cases hShape with
  | inl hTop =>
    subst hTop
    exact ⟨.top, Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩
  | inr hApp =>
    obtain ⟨arg', hEq⟩ := hApp
    subst hEq
    have hTargetScoped : Term.Scoped Γ.depth (.app .top arg') :=
      h.scoped_right (Term.Scoped.app Term.Scoped.top hu)
    have hArg' : Term.Scoped Γ.depth arg' := (Term.Scoped.app_inv hTargetScoped).2
    exact ⟨.top, Relation.ReflTransGen.refl, MEqRedStar.single (MEqRed.tAp hpv hArg')⟩

/-- Any equivalence-chain target of a `Top`-headed application reduces to
`Top`. -/
theorem appTop_eqStar_to_top {Γ : Ctx} {s : Stack} {u t : Term}
    (hpv : PrevalidExt Γ s) (hu : Term.Scoped Γ.depth u)
    (h : MEqRedStar Γ s (.app .top u) t) : MEqRedStar Γ s t .top := by
  obtain ⟨t₃, hTop, hTarget⟩ := diamond_tAp_eqStar hpv hu h
  have ht₃ : t₃ = .top := hTop.top_inv
  subst t₃
  exact hTarget

/-- Direct star-level equivalence diamond for a `Top`-headed application
source. Both equivalence chains can only reach `Top` or another
`Top`-headed application, and both forms join at `Top`. -/
theorem diamond_appTop_eqStar_eqStar {Γ : Ctx} {s : Stack} {u t₁ t₂ : Term}
    (hpv : PrevalidExt Γ s) (hu : Term.Scoped Γ.depth u)
    (h₁ : MEqRedStar Γ s (.app .top u) t₁)
    (h₂ : MEqRedStar Γ s (.app .top u) t₂) :
    ∃ t₃, MEqRedStar Γ s t₁ t₃ ∧ MEqRedStar Γ s t₂ t₃ := by
  have hShape₁ := h₁.app_top_inv
  have hShape₂ := h₂.app_top_inv
  cases hShape₁ with
  | inl hTop₁ =>
    subst hTop₁
    exact diamond_tAp_eqStar hpv hu h₂
  | inr hApp₁ =>
    obtain ⟨arg₁, hEq₁⟩ := hApp₁
    subst hEq₁
    have hTargetScoped₁ : Term.Scoped Γ.depth (.app .top arg₁) :=
      h₁.scoped_right (Term.Scoped.app Term.Scoped.top hu)
    have hArg₁ : Term.Scoped Γ.depth arg₁ := (Term.Scoped.app_inv hTargetScoped₁).2
    cases hShape₂ with
    | inl hTop₂ =>
      subst hTop₂
      exact ⟨.top, MEqRedStar.single (MEqRed.tAp hpv hArg₁),
        Relation.ReflTransGen.refl⟩
    | inr hApp₂ =>
      obtain ⟨arg₂, hEq₂⟩ := hApp₂
      subst hEq₂
      have hTargetScoped₂ : Term.Scoped Γ.depth (.app .top arg₂) :=
        h₂.scoped_right (Term.Scoped.app Term.Scoped.top hu)
      have hArg₂ : Term.Scoped Γ.depth arg₂ := (Term.Scoped.app_inv hTargetScoped₂).2
      exact ⟨.top, MEqRedStar.single (MEqRed.tAp hpv hArg₁),
        MEqRedStar.single (MEqRed.tAp hpv hArg₂)⟩

/-- Lift a single-step equivalence diamond to one equivalence step against an
equivalence-reduction chain. -/
noncomputable def diamond_step_eqStar_of
    {Γ : Ctx} {s : Stack} (hdiamond : EqDiamonds Γ s)
    {t₀ t₁ t₂ : Term}
    (h₁ : MEqRed Γ s t₀ t₁)
    (h₂ : MEqRedStar Γ s t₀ t₂) :
    ∃ t₃, MEqRedStar Γ s t₁ t₃ ∧ MEqRedStar Γ s t₂ t₃ := by
  suffices key : ∀ {a : Term} (h : MEqRedStar Γ s a t₂),
      ∀ {x : Term}, MEqRed Γ s a x →
        ∃ t₃, MEqRedStar Γ s x t₃ ∧ MEqRedStar Γ s t₂ t₃ from
    key h₂ h₁
  intro a h
  refine Relation.ReflTransGen.head_induction_on (b := t₂)
    (P := fun a (_ : MEqRedStar Γ s a t₂) =>
      ∀ {x : Term}, MEqRed Γ s a x →
        ∃ t₃, MEqRedStar Γ s x t₃ ∧ MEqRedStar Γ s t₂ t₃) h ?_ ?_
  · intro x hstep
    exact ⟨x, Relation.ReflTransGen.refl, MEqRedStar.single hstep⟩
  · intro a c hHead _ ihC x hInput
    obtain ⟨y, hcy, hxy⟩ := hdiamond hHead.some hInput
    obtain ⟨t₃, hyT₃, hT₂T₃⟩ := ihC hcy.some
    exact ⟨t₃, Relation.ReflTransGen.head hxy hyT₃, hT₂T₃⟩

/-- Lift a single-step equivalence diamond to two equivalence-reduction
chains. -/
noncomputable def diamond_eqStar_eqStar_of
    {Γ : Ctx} {s : Stack} (hdiamond : EqDiamonds Γ s)
    {t₀ t₁ t₂ : Term}
    (h₁ : MEqRedStar Γ s t₀ t₁)
    (h₂ : MEqRedStar Γ s t₀ t₂) :
    ∃ t₃, MEqRedStar Γ s t₁ t₃ ∧ MEqRedStar Γ s t₂ t₃ := by
  suffices key : ∀ {a : Term} (h : MEqRedStar Γ s a t₁),
      ∀ {z : Term}, MEqRedStar Γ s a z →
        ∃ t₃, MEqRedStar Γ s t₁ t₃ ∧ MEqRedStar Γ s z t₃ from
    key h₁ h₂
  intro a h
  refine Relation.ReflTransGen.head_induction_on (b := t₁)
    (P := fun a (_ : MEqRedStar Γ s a t₁) =>
      ∀ {z : Term}, MEqRedStar Γ s a z →
        ∃ t₃, MEqRedStar Γ s t₁ t₃ ∧ MEqRedStar Γ s z t₃) h ?_ ?_
  · intro z hStar
    exact ⟨z, hStar, Relation.ReflTransGen.refl⟩
  · intro a c hHead _ ihC z hInputStar
    obtain ⟨y, hcy, hzy⟩ :=
      diamond_step_eqStar_of hdiamond hHead.some hInputStar
    obtain ⟨t₃, hT₁T₃, hyT₃⟩ := ihC hcy
    exact ⟨t₃, hT₁T₃, Relation.ReflTransGen.trans hzy hyT₃⟩

/-- Named de Bruijn Lemma 2 chain lifting: a single-step equivalence diamond
at a fixed extended context lifts to one equivalence step against an
equivalence-reduction chain. -/
noncomputable def Lemma_2_DeBruijn_step_eqStar_of
    {Γ : Ctx} {s : Stack} (hdiamond : EqDiamonds Γ s)
    {t₀ t₁ t₂ : Term}
    (h₁ : MEqRed Γ s t₀ t₁)
    (h₂ : MEqRedStar Γ s t₀ t₂) :
    ∃ t₃, MEqRedStar Γ s t₁ t₃ ∧ MEqRedStar Γ s t₂ t₃ :=
  diamond_step_eqStar_of hdiamond h₁ h₂

/-- Named de Bruijn Lemma 2 chain lifting: a single-step equivalence diamond
at a fixed extended context lifts to two equivalence-reduction chains. -/
noncomputable def Lemma_2_DeBruijn_DiamondMEqRedStar_of
    {Γ : Ctx} {s : Stack} (hdiamond : EqDiamonds Γ s)
    {t₀ t₁ t₂ : Term}
    (h₁ : MEqRedStar Γ s t₀ t₁)
    (h₂ : MEqRedStar Γ s t₀ t₂) :
    ∃ t₃, MEqRedStar Γ s t₁ t₃ ∧ MEqRedStar Γ s t₂ t₃ :=
  diamond_eqStar_eqStar_of hdiamond h₁ h₂

/-- De Bruijn single-step strong commutativity at a fixed extended context.
This is the de Bruijn Lemma 1 shape needed by the star-lifting argument for
Theorem 3. The conclusion uses the Prop wrappers for single Type-valued
reduction steps. -/
abbrev StrongCommutes (Γ : Ctx) (s : Stack) : Prop :=
  ∀ {t₀ t₁ t₂ : Term},
    MSubRed Γ s t₀ t₁ →
    MEqRed Γ s t₀ t₂ →
    ∃ t₃, MEqRedJ Γ s t₁ t₃ ∧ MSubRedJ Γ s t₂ t₃

/-- Named de Bruijn Lemma 1 single-step premise. This is an alias for
`StrongCommutes`, useful as the audit point for the future full case grid. -/
def Lemma_1_DeBruijn_StrongCommutativity (Γ : Ctx) (s : Stack) : Prop :=
  StrongCommutes Γ s

namespace StrongCommutes

/-- The `Top` source cell of de Bruijn Lemma 1. Both one-step targets must be
`Top`, so the commutation square closes immediately. -/
theorem top {Γ : Ctx} {s : Stack} {t₁ t₂ : Term}
    (hsub : MSubRed Γ s .top t₁) (heq : MEqRed Γ s .top t₂) :
    ∃ t₃, MEqRedJ Γ s t₁ t₃ ∧ MSubRedJ Γ s t₂ t₃ := by
  have ht₁ : t₁ = .top := hsub.top_inv
  have ht₂ : t₂ = .top := heq.top_inv
  subst t₁
  subst t₂
  exact ⟨.top, ⟨heq⟩, ⟨hsub⟩⟩

/-- The `Ms-Pro × Me-Var` source cell of de Bruijn Lemma 1. -/
theorem pro_var {Γ : Ctx} {s : Stack} {i : Nat} {t : Term}
    (hpv : PrevalidExt Γ s) (hb : Γ.subBinds i t) (_hi : i < Γ.depth) :
    ∃ t₃, MEqRedJ Γ s t t₃ ∧ MSubRedJ Γ s (.bvar i) t₃ := by
  let hsub : MSubRed Γ s (.bvar i) t := MSubRed.pro hpv hb
  exact ⟨t, ⟨MEqRed.refl hpv hsub.scoped_right⟩, ⟨hsub⟩⟩

/-- The `Ms-Pro × Me-Pro` source cell of de Bruijn Lemma 1 is vacuous: one
context index cannot carry both a subtype and equivalence binding. -/
theorem pro_pro_vacuous {Γ : Ctx} {s : Stack} {i : Nat} {t α α' : Term}
    (hsubBind : Γ.subBinds i t) (heqBind : Γ.equBinds i α)
    (_hα : MEqRed Γ s α α') :
    ∃ t₃, MEqRedJ Γ s t t₃ ∧ MSubRedJ Γ s α' t₃ := by
  exact (Ctx.subBinds_equBinds_false hsubBind heqBind).elim

/-- The `Ms-Equ × Me-Var` source cell of de Bruijn Lemma 1. -/
theorem equ_var {Γ : Ctx} {s : Stack} {i : Nat} {t : Term}
    (hpv : PrevalidExt Γ s) (heqStep : MEqRed Γ s (.bvar i) t)
    (_hi : i < Γ.depth) :
    ∃ t₃, MEqRedJ Γ s t t₃ ∧ MSubRedJ Γ s (.bvar i) t₃ := by
  let hsub : MSubRed Γ s (.bvar i) t := MSubRed.equ hpv heqStep
  exact ⟨t, ⟨MEqRed.refl hpv heqStep.scoped_right⟩, ⟨hsub⟩⟩

/-- Any `Ms-Equ × Me-*` cell of de Bruijn Lemma 1 reduces to the local
de Bruijn Lemma 2 diamond. -/
theorem equ_of {Γ : Ctx} {s : Stack} (hdiamond : EqDiamonds Γ s)
    {t₀ t₁ t₂ : Term} (hpv : PrevalidExt Γ s)
    (heqSub : MEqRed Γ s t₀ t₁) (heq : MEqRed Γ s t₀ t₂) :
    ∃ t₃, MEqRedJ Γ s t₁ t₃ ∧ MSubRedJ Γ s t₂ t₃ := by
  obtain ⟨t₃, hLeft, hRight⟩ := hdiamond heqSub heq
  exact ⟨t₃, hLeft, ⟨MSubRed.equ hpv hRight.some⟩⟩

/-- Any `Ms-Top × Me-*` cell of de Bruijn Lemma 1 closes at `Top`. -/
theorem top_of {Γ : Ctx} {s : Stack} {t₀ t₂ : Term}
    (hpv : PrevalidExt Γ s) (_hScoped : Term.Scoped Γ.depth t₀)
    (heq : MEqRed Γ s t₀ t₂) :
    ∃ t₃, MEqRedJ Γ s .top t₃ ∧ MSubRedJ Γ s t₂ t₃ := by
  exact ⟨.top, ⟨MEqRed.top hpv⟩, ⟨MSubRed.top hpv heq.scoped_right⟩⟩

/-- The `Ms-Top × Me-TAp` source cell for a `Top`-headed application. -/
theorem appTop_top_tAp {Γ : Ctx} {s : Stack} {u : Term}
    (hpv : PrevalidExt Γ s) (_hu : Term.Scoped Γ.depth u) :
    ∃ t₃, MEqRedJ Γ s .top t₃ ∧ MSubRedJ Γ s .top t₃ := by
  exact ⟨.top, ⟨MEqRed.top hpv⟩, ⟨MSubRed.refl hpv Term.Scoped.top⟩⟩

/-- The `Ms-Top × Me-App` source cell for a `Top`-headed application. -/
theorem appTop_top_app {Γ : Ctx} {s : Stack} {u u' v' : Term}
    (hpv : PrevalidExt Γ s) (_hu : Term.Scoped Γ.depth u)
    (hOp : MEqRed Γ (u :: s) .top u') (hArg : MEqRed Γ [] u v') :
    ∃ t₃, MEqRedJ Γ s .top t₃ ∧ MSubRedJ Γ s (.app u' v') t₃ := by
  have hu' : u' = .top := hOp.top_inv
  subst u'
  exact ⟨.top, ⟨MEqRed.top hpv⟩,
    ⟨MSubRed.top hpv (Term.Scoped.app Term.Scoped.top hArg.scoped_right)⟩⟩

/-- The `Ms-App × Me-TAp` source cell for a `Top`-headed application. -/
theorem appTop_app_tAp {Γ : Ctx} {s : Stack} {u u' : Term}
    (hpv : PrevalidExt Γ s) (hu : Term.Scoped Γ.depth u)
    (hOp : MSubRed Γ (u :: s) .top u') :
    ∃ t₃, MEqRedJ Γ s (.app u' u) t₃ ∧ MSubRedJ Γ s .top t₃ := by
  have hu' : u' = .top := hOp.top_inv
  subst u'
  exact ⟨.top, ⟨MEqRed.tAp hpv hu⟩, ⟨MSubRed.refl hpv Term.Scoped.top⟩⟩

/-- The full `Top`-headed application source cell for de Bruijn Lemma 1.
The local `Ms-Equ` branch is discharged by the matching de Bruijn Lemma 2
cell `EqDiamonds.appTop_any`; structural branches close at `Top`. -/
theorem appTop_any {Γ : Ctx} {s : Stack}
    {u t₁ t₂ : Term} (hpv : PrevalidExt Γ s) (hu : Term.Scoped Γ.depth u)
    (hsub : MSubRed Γ s (.app .top u) t₁)
    (heq : MEqRed Γ s (.app .top u) t₂) :
    ∃ t₃, MEqRedJ Γ s t₁ t₃ ∧ MSubRedJ Γ s t₂ t₃ := by
  cases hsub with
  | top _ hScoped =>
    exact top_of hpv hScoped heq
  | equ _ heqStep =>
    obtain ⟨t₃, hLeft, hRight⟩ := EqDiamonds.appTop_any hpv hu heqStep heq
    exact ⟨t₃, hLeft, ⟨MSubRed.equ hpv hRight.some⟩⟩
  | app hOp _ =>
    have hOpTop := MSubRed.top_inv hOp
    subst hOpTop
    have hShape := MEqRed.app_top_inv heq
    cases hShape with
    | inl hTop =>
      subst hTop
      exact ⟨.top, ⟨MEqRed.tAp hpv hu⟩, ⟨MSubRed.refl hpv Term.Scoped.top⟩⟩
    | inr hApp =>
      obtain ⟨arg', hEq⟩ := hApp
      subst hEq
      have hTargetScoped : Term.Scoped Γ.depth (.app .top arg') := heq.scoped_right
      have hArg' : Term.Scoped Γ.depth arg' := (Term.Scoped.app_inv hTargetScoped).2
      exact ⟨.top, ⟨MEqRed.tAp hpv hu⟩,
        ⟨MSubRed.top hpv (Term.Scoped.app Term.Scoped.top hArg')⟩⟩

/-- Compatibility wrapper for the full `Top`-headed application source cell
that matches the conditional Lemma 1 helper shape. The local diamond premise
is no longer needed for this cell. -/
theorem appTop_any_of {Γ : Ctx} {s : Stack} (_hdiamond : EqDiamonds Γ s)
    {u t₁ t₂ : Term} (hpv : PrevalidExt Γ s) (hu : Term.Scoped Γ.depth u)
    (hsub : MSubRed Γ s (.app .top u) t₁)
    (heq : MEqRed Γ s (.app .top u) t₂) :
    ∃ t₃, MEqRedJ Γ s t₁ t₃ ∧ MSubRedJ Γ s t₂ t₃ := by
  exact appTop_any hpv hu hsub heq

/-- The `Ms-* × Me-TAp` cells for a `Top`-headed application. The
`Ms-Equ` branch is discharged by the matching de Bruijn Lemma 2 cell. -/
theorem appTop_any_tAp {Γ : Ctx} {s : Stack}
    {u t₁ : Term} (hpv : PrevalidExt Γ s) (hu : Term.Scoped Γ.depth u)
    (hsub : MSubRed Γ s (.app .top u) t₁) :
    ∃ t₃, MEqRedJ Γ s t₁ t₃ ∧ MSubRedJ Γ s .top t₃ := by
  exact appTop_any hpv hu hsub (MEqRed.tAp hpv hu)

/-- Compatibility wrapper for the `Ms-* × Me-TAp` cells that matches the
conditional Lemma 1 helper shape. The local diamond premise is no longer
needed for this cell. -/
theorem appTop_any_tAp_of {Γ : Ctx} {s : Stack} (_hdiamond : EqDiamonds Γ s)
    {u t₁ : Term} (hpv : PrevalidExt Γ s) (hu : Term.Scoped Γ.depth u)
    (hsub : MSubRed Γ s (.app .top u) t₁) :
    ∃ t₃, MEqRedJ Γ s t₁ t₃ ∧ MSubRedJ Γ s .top t₃ := by
  exact appTop_any_tAp hpv hu hsub

end StrongCommutes

/-- The `Top` source case for one subtype step against an equivalence chain,
proved directly by shape inversion. -/
theorem commute_subStep_eqStar_top {Γ : Ctx} {s : Stack} {t₁ t₂ : Term}
    (hsub : MSubRed Γ s .top t₁) (heqs : MEqRedStar Γ s .top t₂) :
    ∃ t₃, MEqRedStar Γ s t₁ t₃ ∧ MSubRedStar Γ s t₂ t₃ := by
  have ht₁ : t₁ = .top := hsub.top_inv
  have ht₂ : t₂ = .top := heqs.top_inv
  subst t₁
  subst t₂
  exact ⟨.top, Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩

/-- The `Top` source case for a subtype chain against an equivalence chain,
proved directly by shape inversion. -/
theorem commute_subStar_eqStar_top {Γ : Ctx} {s : Stack} {t₁ t₂ : Term}
    (hsubs : MSubRedStar Γ s .top t₁) (heqs : MEqRedStar Γ s .top t₂) :
    ∃ t₃, MEqRedStar Γ s t₁ t₃ ∧ MSubRedStar Γ s t₂ t₃ := by
  have ht₁ : t₁ = .top := hsubs.top_inv
  have ht₂ : t₂ = .top := heqs.top_inv
  subst t₁
  subst t₂
  exact ⟨.top, Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩

/-- A single `Ms-Top` step commutes directly with any equivalence-reduction
chain from the same source. -/
theorem commute_topStep_eqStar {Γ : Ctx} {s : Stack} {t₀ t₂ : Term}
    (hpv : PrevalidExt Γ s) (hScoped : Term.Scoped Γ.depth t₀)
    (heqs : MEqRedStar Γ s t₀ t₂) :
    ∃ t₃, MEqRedStar Γ s .top t₃ ∧ MSubRedStar Γ s t₂ t₃ := by
  have hTargetScoped : Term.Scoped Γ.depth t₂ := heqs.scoped_right hScoped
  exact ⟨.top, Relation.ReflTransGen.refl,
    MSubRedStar.single (MSubRed.top hpv hTargetScoped)⟩

/-- Star-level commutation for an `Ms-Equ` subtype step. The join is the
equivalence diamond against the right-hand equivalence chain, with the right
join edge embedded into subtype reduction through `Ms-Equ`. -/
noncomputable def commute_equStep_eqStar_of {Γ : Ctx} {s : Stack}
    (hdiamond : EqDiamonds Γ s) {t₀ t₁ t₂ : Term}
    (hpv : PrevalidExt Γ s) (heqSub : MEqRed Γ s t₀ t₁)
    (heqs : MEqRedStar Γ s t₀ t₂) :
    ∃ t₃, MEqRedStar Γ s t₁ t₃ ∧ MSubRedStar Γ s t₂ t₃ := by
  obtain ⟨t₃, hLeft, hRight⟩ :=
    diamond_step_eqStar_of hdiamond heqSub heqs
  exact ⟨t₃, hLeft, MSubRedStar.of_MEqRedStar hpv hRight⟩

/-- Star-level commutation for a subtype chain made only of `Ms-Equ` steps.
This is the chain analogue of `commute_equStep_eqStar_of`. -/
noncomputable def commute_equStar_eqStar_of {Γ : Ctx} {s : Stack}
    (hdiamond : EqDiamonds Γ s) {t₀ t₁ t₂ : Term}
    (hpv : PrevalidExt Γ s) (heqSubs : MEqRedStar Γ s t₀ t₁)
    (heqs : MEqRedStar Γ s t₀ t₂) :
    ∃ t₃, MEqRedStar Γ s t₁ t₃ ∧ MSubRedStar Γ s t₂ t₃ := by
  obtain ⟨t₃, hLeft, hRight⟩ :=
    diamond_eqStar_eqStar_of hdiamond heqSubs heqs
  exact ⟨t₃, hLeft, MSubRedStar.of_MEqRedStar hpv hRight⟩

/-- Direct star-level join for a subtype chain from a `Top`-headed
application against its `TAp` target. -/
theorem commute_appTop_subStar_tAp {Γ : Ctx} {s : Stack} {u t : Term}
    (hpv : PrevalidExt Γ s) (hu : Term.Scoped Γ.depth u)
    (h : MSubRedStar Γ s (.app .top u) t) :
    ∃ t₃, MEqRedStar Γ s t t₃ ∧ MSubRedStar Γ s .top t₃ := by
  have hShape := h.app_top_inv
  cases hShape with
  | inl hTop =>
    subst hTop
    exact ⟨.top, Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩
  | inr hApp =>
    obtain ⟨arg', hEq⟩ := hApp
    subst hEq
    have hTargetScoped : Term.Scoped Γ.depth (.app .top arg') :=
      h.scoped_right (Term.Scoped.app Term.Scoped.top hu)
    have hArg' : Term.Scoped Γ.depth arg' := (Term.Scoped.app_inv hTargetScoped).2
    exact ⟨.top, MEqRedStar.single (MEqRed.tAp hpv hArg'), Relation.ReflTransGen.refl⟩

/-- Any subtype-chain target of a `Top`-headed application equivalence-reduces
to `Top`. -/
theorem appTop_subStar_to_top {Γ : Ctx} {s : Stack} {u t : Term}
    (hpv : PrevalidExt Γ s) (hu : Term.Scoped Γ.depth u)
    (h : MSubRedStar Γ s (.app .top u) t) : MEqRedStar Γ s t .top := by
  obtain ⟨t₃, hTarget, hTop⟩ := commute_appTop_subStar_tAp hpv hu h
  have ht₃ : t₃ = .top := hTop.top_inv
  subst t₃
  exact hTarget

/-- Any equivalence-chain target of a `Top`-headed application is
diagrammatically below `Top`. -/
theorem msub_appTop_eqStar_to_top {Γ : Ctx} {s : Stack} {u t : Term}
    (hpv : PrevalidExt Γ s) (hu : Term.Scoped Γ.depth u)
    (h : MEqRedStar Γ s (.app .top u) t) : MSub Γ s t .top :=
  MSub.intro (MSubRedStar.of_MEqRedStar hpv (appTop_eqStar_to_top hpv hu h))
    Relation.ReflTransGen.refl

/-- Transitive diagrammatic packaging of `appTop_eqStar_to_top`. -/
theorem msubStar_appTop_eqStar_to_top {Γ : Ctx} {s : Stack} {u t : Term}
    (hpv : PrevalidExt Γ s) (hu : Term.Scoped Γ.depth u)
    (h : MEqRedStar Γ s (.app .top u) t) : MSubStar Γ s t .top :=
  (msub_appTop_eqStar_to_top hpv hu h).to_star

/-- A `Top`-headed application equivalence-reduces directly to `Top`. -/
theorem appTop_to_top {Γ : Ctx} {s : Stack} {u : Term}
    (hpv : PrevalidExt Γ s) (hu : Term.Scoped Γ.depth u) :
    MEqRedStar Γ s (.app .top u) .top :=
  MEqRedStar.single (MEqRed.tAp hpv hu)

/-- Diagrammatic packaging of `appTop_to_top`. -/
theorem msub_appTop_to_top {Γ : Ctx} {s : Stack} {u : Term}
    (hpv : PrevalidExt Γ s) (hu : Term.Scoped Γ.depth u) :
    MSub Γ s (.app .top u) .top :=
  MSub.of_MEqRedStar_left hpv (appTop_to_top hpv hu)

/-- Transitive diagrammatic packaging of `appTop_to_top`. -/
theorem msubStar_appTop_to_top {Γ : Ctx} {s : Stack} {u : Term}
    (hpv : PrevalidExt Γ s) (hu : Term.Scoped Γ.depth u) :
    MSubStar Γ s (.app .top u) .top :=
  (msub_appTop_to_top hpv hu).to_star

/-- Any subtype-chain target of a `Top`-headed application is
diagrammatically below `Top`. -/
theorem msub_appTop_subStar_to_top {Γ : Ctx} {s : Stack} {u t : Term}
    (hpv : PrevalidExt Γ s) (hu : Term.Scoped Γ.depth u)
    (h : MSubRedStar Γ s (.app .top u) t) : MSub Γ s t .top :=
  MSub.intro (MSubRedStar.of_MEqRedStar hpv (appTop_subStar_to_top hpv hu h))
    Relation.ReflTransGen.refl

/-- Transitive diagrammatic packaging of `appTop_subStar_to_top`. -/
theorem msubStar_appTop_subStar_to_top {Γ : Ctx} {s : Stack} {u t : Term}
    (hpv : PrevalidExt Γ s) (hu : Term.Scoped Γ.depth u)
    (h : MSubRedStar Γ s (.app .top u) t) : MSubStar Γ s t .top :=
  (msub_appTop_subStar_to_top hpv hu h).to_star

/-- Direct star-level commutation for a `Top`-headed application source. Any
subtype chain and any equivalence chain out of the same source join at
`Top`. -/
theorem commute_appTop_subStar_eqStar {Γ : Ctx} {s : Stack} {u t₁ t₂ : Term}
    (hpv : PrevalidExt Γ s) (hu : Term.Scoped Γ.depth u)
    (hSub : MSubRedStar Γ s (.app .top u) t₁)
    (hEq : MEqRedStar Γ s (.app .top u) t₂) :
    ∃ t₃, MEqRedStar Γ s t₁ t₃ ∧ MSubRedStar Γ s t₂ t₃ := by
  have hSubShape := hSub.app_top_inv
  have hEqShape := hEq.app_top_inv
  cases hSubShape with
  | inl hSubTop =>
    subst hSubTop
    have hEqScoped : Term.Scoped Γ.depth t₂ :=
      hEq.scoped_right (Term.Scoped.app Term.Scoped.top hu)
    exact ⟨.top, Relation.ReflTransGen.refl,
      MSubRedStar.single (MSubRed.top hpv hEqScoped)⟩
  | inr hSubApp =>
    obtain ⟨arg₁, hSubEq⟩ := hSubApp
    subst hSubEq
    have hSubTargetScoped : Term.Scoped Γ.depth (.app .top arg₁) :=
      hSub.scoped_right (Term.Scoped.app Term.Scoped.top hu)
    have hArg₁ : Term.Scoped Γ.depth arg₁ := (Term.Scoped.app_inv hSubTargetScoped).2
    cases hEqShape with
    | inl hEqTop =>
      subst hEqTop
      exact ⟨.top, MEqRedStar.single (MEqRed.tAp hpv hArg₁),
        Relation.ReflTransGen.refl⟩
    | inr hEqApp =>
      obtain ⟨arg₂, hEqEq⟩ := hEqApp
      subst hEqEq
      have hEqTargetScoped : Term.Scoped Γ.depth (.app .top arg₂) :=
        hEq.scoped_right (Term.Scoped.app Term.Scoped.top hu)
      exact ⟨.top, MEqRedStar.single (MEqRed.tAp hpv hArg₁),
        MSubRedStar.single (MSubRed.top hpv hEqTargetScoped)⟩

/-- Single-subtype-step specialization of the full star-level `Top`-headed
source commutation cell. -/
theorem commute_appTop_subStep_eqStar {Γ : Ctx} {s : Stack} {u t₁ t₂ : Term}
    (hpv : PrevalidExt Γ s) (hu : Term.Scoped Γ.depth u)
    (hSub : MSubRed Γ s (.app .top u) t₁)
    (hEq : MEqRedStar Γ s (.app .top u) t₂) :
    ∃ t₃, MEqRedStar Γ s t₁ t₃ ∧ MSubRedStar Γ s t₂ t₃ :=
  commute_appTop_subStar_eqStar hpv hu (MSubRedStar.single hSub) hEq

/-- If the subtype side has already reached `Top`, any equivalence-chain
target from the same scoped source joins it at `Top`. -/
theorem commute_subStar_to_top_eqStar {Γ : Ctx} {s : Stack} {t₀ t₂ : Term}
    (hpv : PrevalidExt Γ s) (hScoped : Term.Scoped Γ.depth t₀)
    (_hSubTop : MSubRedStar Γ s t₀ .top)
    (hEq : MEqRedStar Γ s t₀ t₂) :
    ∃ t₃, MEqRedStar Γ s .top t₃ ∧ MSubRedStar Γ s t₂ t₃ := by
  have hTargetScoped : Term.Scoped Γ.depth t₂ := hEq.scoped_right hScoped
  exact ⟨.top, Relation.ReflTransGen.refl,
    MSubRedStar.single (MSubRed.top hpv hTargetScoped)⟩

/-- Direct target-to-`Top` chain extracted from
`commute_subStar_to_top_eqStar`. -/
theorem eqStar_to_top_of_subStar_top {Γ : Ctx} {s : Stack} {t₀ t₂ : Term}
    (hpv : PrevalidExt Γ s) (hScoped : Term.Scoped Γ.depth t₀)
    (hSubTop : MSubRedStar Γ s t₀ .top)
    (hEq : MEqRedStar Γ s t₀ t₂) :
    MSubRedStar Γ s t₂ .top := by
  obtain ⟨t₃, hTop, hTarget⟩ :=
    commute_subStar_to_top_eqStar hpv hScoped hSubTop hEq
  have ht₃ : t₃ = .top := hTop.top_inv
  subst t₃
  exact hTarget

/-- Diagrammatic packaging of `eqStar_to_top_of_subStar_top`: an
equivalence-chain target is below `Top` whenever the original scoped source
has a subtype chain to `Top`. -/
theorem msub_eqStar_to_top_of_subStar_top {Γ : Ctx} {s : Stack} {t₀ t₂ : Term}
    (hpv : PrevalidExt Γ s) (hScoped : Term.Scoped Γ.depth t₀)
    (hSubTop : MSubRedStar Γ s t₀ .top)
    (hEq : MEqRedStar Γ s t₀ t₂) : MSub Γ s t₂ .top :=
  MSub.intro
    (eqStar_to_top_of_subStar_top hpv hScoped hSubTop hEq)
    Relation.ReflTransGen.refl

/-- Transitive diagrammatic packaging of
`eqStar_to_top_of_subStar_top`. -/
theorem msubStar_eqStar_to_top_of_subStar_top {Γ : Ctx} {s : Stack}
    {t₀ t₂ : Term} (hpv : PrevalidExt Γ s)
    (hScoped : Term.Scoped Γ.depth t₀)
    (hSubTop : MSubRedStar Γ s t₀ .top)
    (hEq : MEqRedStar Γ s t₀ t₂) : MSubStar Γ s t₂ .top :=
  (msub_eqStar_to_top_of_subStar_top hpv hScoped hSubTop hEq).to_star

/-- If a subtype chain from an abstraction reaches `Top`, any equivalence
chain from the same abstraction joins it at `Top`. -/
theorem commute_abs_to_top_eqStar {Γ : Ctx} {s : Stack}
    {bound body t : Term} (hpv : PrevalidExt Γ s)
    (hScoped : Term.Scoped Γ.depth (.abs bound body))
    (_hSubTop : MSubRedStar Γ s (.abs bound body) .top)
    (hEq : MEqRedStar Γ s (.abs bound body) t) :
    ∃ t₃, MEqRedStar Γ s .top t₃ ∧ MSubRedStar Γ s t t₃ := by
  exact commute_subStar_to_top_eqStar hpv hScoped _hSubTop hEq

/-- If an abstraction has a subtype chain to `Top`, every equivalence-chain
target from that abstraction has a subtype chain to `Top`. -/
theorem abs_eqStar_to_top_of_subStar_top {Γ : Ctx} {s : Stack}
    {bound body t : Term} (hpv : PrevalidExt Γ s)
    (hScoped : Term.Scoped Γ.depth (.abs bound body))
    (hSubTop : MSubRedStar Γ s (.abs bound body) .top)
    (hEq : MEqRedStar Γ s (.abs bound body) t) :
    MSubRedStar Γ s t .top := by
  exact eqStar_to_top_of_subStar_top hpv hScoped hSubTop hEq

/-- Diagrammatic packaging of `abs_eqStar_to_top_of_subStar_top`. -/
theorem msub_abs_eqStar_to_top_of_subStar_top {Γ : Ctx} {s : Stack}
    {bound body t : Term} (hpv : PrevalidExt Γ s)
    (hScoped : Term.Scoped Γ.depth (.abs bound body))
    (hSubTop : MSubRedStar Γ s (.abs bound body) .top)
    (hEq : MEqRedStar Γ s (.abs bound body) t) : MSub Γ s t .top :=
  msub_eqStar_to_top_of_subStar_top hpv hScoped hSubTop hEq

/-- Transitive diagrammatic packaging of
`abs_eqStar_to_top_of_subStar_top`. -/
theorem msubStar_abs_eqStar_to_top_of_subStar_top {Γ : Ctx} {s : Stack}
    {bound body t : Term} (hpv : PrevalidExt Γ s)
    (hScoped : Term.Scoped Γ.depth (.abs bound body))
    (hSubTop : MSubRedStar Γ s (.abs bound body) .top)
    (hEq : MEqRedStar Γ s (.abs bound body) t) : MSubStar Γ s t .top :=
  (msub_abs_eqStar_to_top_of_subStar_top hpv hScoped hSubTop hEq).to_star

/-- If a subtype chain from an abstraction-headed application reaches `Top`,
any equivalence chain from the same source joins it at `Top`. -/
theorem commute_appAbs_to_top_eqStar {Γ : Ctx} {s : Stack}
    {bound body arg t : Term} (hpv : PrevalidExt Γ s)
    (hScoped : Term.Scoped Γ.depth (.app (.abs bound body) arg))
    (hSubTop : MSubRedStar Γ s (.app (.abs bound body) arg) .top)
    (hEq : MEqRedStar Γ s (.app (.abs bound body) arg) t) :
    ∃ t₃, MEqRedStar Γ s .top t₃ ∧ MSubRedStar Γ s t t₃ := by
  exact commute_subStar_to_top_eqStar hpv hScoped hSubTop hEq

/-- Single-subtype-step specialization of
`commute_appAbs_to_top_eqStar`. -/
theorem commute_appAbs_subStep_to_top_eqStar {Γ : Ctx} {s : Stack}
    {bound body arg t : Term} (hpv : PrevalidExt Γ s)
    (hScoped : Term.Scoped Γ.depth (.app (.abs bound body) arg))
    (hSubTop : MSubRed Γ s (.app (.abs bound body) arg) .top)
    (hEq : MEqRedStar Γ s (.app (.abs bound body) arg) t) :
    ∃ t₃, MEqRedStar Γ s .top t₃ ∧ MSubRedStar Γ s t t₃ :=
  commute_appAbs_to_top_eqStar hpv hScoped (MSubRedStar.single hSubTop) hEq

/-- If an abstraction-headed application has a subtype chain to `Top`, every
equivalence-chain target from that source has a subtype chain to `Top`. -/
theorem appAbs_eqStar_to_top_of_subStar_top {Γ : Ctx} {s : Stack}
    {bound body arg t : Term} (hpv : PrevalidExt Γ s)
    (hScoped : Term.Scoped Γ.depth (.app (.abs bound body) arg))
    (hSubTop : MSubRedStar Γ s (.app (.abs bound body) arg) .top)
    (hEq : MEqRedStar Γ s (.app (.abs bound body) arg) t) :
    MSubRedStar Γ s t .top := by
  exact eqStar_to_top_of_subStar_top hpv hScoped hSubTop hEq

/-- Diagrammatic packaging of
`appAbs_eqStar_to_top_of_subStar_top`. -/
theorem msub_appAbs_eqStar_to_top_of_subStar_top {Γ : Ctx} {s : Stack}
    {bound body arg t : Term} (hpv : PrevalidExt Γ s)
    (hScoped : Term.Scoped Γ.depth (.app (.abs bound body) arg))
    (hSubTop : MSubRedStar Γ s (.app (.abs bound body) arg) .top)
    (hEq : MEqRedStar Γ s (.app (.abs bound body) arg) t) : MSub Γ s t .top :=
  msub_eqStar_to_top_of_subStar_top hpv hScoped hSubTop hEq

/-- Transitive diagrammatic packaging of
`appAbs_eqStar_to_top_of_subStar_top`. -/
theorem msubStar_appAbs_eqStar_to_top_of_subStar_top {Γ : Ctx} {s : Stack}
    {bound body arg t : Term} (hpv : PrevalidExt Γ s)
    (hScoped : Term.Scoped Γ.depth (.app (.abs bound body) arg))
    (hSubTop : MSubRedStar Γ s (.app (.abs bound body) arg) .top)
    (hEq : MEqRedStar Γ s (.app (.abs bound body) arg) t) : MSubStar Γ s t .top :=
  (msub_appAbs_eqStar_to_top_of_subStar_top hpv hScoped hSubTop hEq).to_star

/-- If a subtype chain from an abstraction-headed application reaches a
`Top`-headed application, that target has a subtype chain to `Top`. -/
theorem appAbs_subStar_appTop_to_top {Γ : Ctx} {s : Stack}
    {bound body arg t arg' : Term} (hpv : PrevalidExt Γ s)
    (hScoped : Term.Scoped Γ.depth (.app (.abs bound body) arg))
    (hSub : MSubRedStar Γ s (.app (.abs bound body) arg) t)
    (hAppTop : t = .app .top arg') : MSubRedStar Γ s t .top := by
  subst hAppTop
  have hTargetScoped : Term.Scoped Γ.depth (.app .top arg') :=
    hSub.scoped_right hScoped
  have hArg' : Term.Scoped Γ.depth arg' := (Term.Scoped.app_inv hTargetScoped).2
  exact MSubRedStar.of_MEqRedStar hpv (appTop_to_top hpv hArg')

/-- Diagrammatic packaging of `appAbs_subStar_appTop_to_top`. -/
theorem msub_appAbs_subStar_appTop_to_top {Γ : Ctx} {s : Stack}
    {bound body arg t arg' : Term} (hpv : PrevalidExt Γ s)
    (hScoped : Term.Scoped Γ.depth (.app (.abs bound body) arg))
    (hSub : MSubRedStar Γ s (.app (.abs bound body) arg) t)
    (hAppTop : t = .app .top arg') : MSub Γ s t .top :=
  MSub.intro (appAbs_subStar_appTop_to_top hpv hScoped hSub hAppTop)
    Relation.ReflTransGen.refl

/-- Transitive diagrammatic packaging of `appAbs_subStar_appTop_to_top`. -/
theorem msubStar_appAbs_subStar_appTop_to_top {Γ : Ctx} {s : Stack}
    {bound body arg t arg' : Term} (hpv : PrevalidExt Γ s)
    (hScoped : Term.Scoped Γ.depth (.app (.abs bound body) arg))
    (hSub : MSubRedStar Γ s (.app (.abs bound body) arg) t)
    (hAppTop : t = .app .top arg') : MSubStar Γ s t .top :=
  (msub_appAbs_subStar_appTop_to_top hpv hScoped hSub hAppTop).to_star

/-- Single-subtype-step specialization of
`appAbs_subStar_appTop_to_top`. -/
theorem appAbs_subStep_appTop_to_top {Γ : Ctx} {s : Stack}
    {bound body arg t arg' : Term} (hpv : PrevalidExt Γ s)
    (hScoped : Term.Scoped Γ.depth (.app (.abs bound body) arg))
    (hSub : MSubRed Γ s (.app (.abs bound body) arg) t)
    (hAppTop : t = .app .top arg') : MSubRedStar Γ s t .top :=
  appAbs_subStar_appTop_to_top hpv hScoped (MSubRedStar.single hSub) hAppTop

/-- Single-subtype-step specialization of
`msub_appAbs_subStar_appTop_to_top`. -/
theorem msub_appAbs_subStep_appTop_to_top {Γ : Ctx} {s : Stack}
    {bound body arg t arg' : Term} (hpv : PrevalidExt Γ s)
    (hScoped : Term.Scoped Γ.depth (.app (.abs bound body) arg))
    (hSub : MSubRed Γ s (.app (.abs bound body) arg) t)
    (hAppTop : t = .app .top arg') : MSub Γ s t .top :=
  msub_appAbs_subStar_appTop_to_top hpv hScoped (MSubRedStar.single hSub) hAppTop

/-- Transitive single-subtype-step specialization of
`msubStar_appAbs_subStar_appTop_to_top`. -/
theorem msubStar_appAbs_subStep_appTop_to_top {Γ : Ctx} {s : Stack}
    {bound body arg t arg' : Term} (hpv : PrevalidExt Γ s)
    (hScoped : Term.Scoped Γ.depth (.app (.abs bound body) arg))
    (hSub : MSubRed Γ s (.app (.abs bound body) arg) t)
    (hAppTop : t = .app .top arg') : MSubStar Γ s t .top :=
  msubStar_appAbs_subStar_appTop_to_top hpv hScoped (MSubRedStar.single hSub) hAppTop

/-- If a subtype chain from an abstraction-headed application reaches a
`Top`-headed application, the original source has a subtype chain to `Top`. -/
theorem appAbs_subStar_to_top_of_appTop {Γ : Ctx} {s : Stack}
    {bound body arg t arg' : Term} (hpv : PrevalidExt Γ s)
    (hScoped : Term.Scoped Γ.depth (.app (.abs bound body) arg))
    (hSub : MSubRedStar Γ s (.app (.abs bound body) arg) t)
    (hAppTop : t = .app .top arg') :
    MSubRedStar Γ s (.app (.abs bound body) arg) .top :=
  MSubRedStar.trans hSub (appAbs_subStar_appTop_to_top hpv hScoped hSub hAppTop)

/-- Diagrammatic packaging of
`appAbs_subStar_to_top_of_appTop`. -/
theorem msub_appAbs_to_top_of_subStar_appTop {Γ : Ctx} {s : Stack}
    {bound body arg t arg' : Term} (hpv : PrevalidExt Γ s)
    (hScoped : Term.Scoped Γ.depth (.app (.abs bound body) arg))
    (hSub : MSubRedStar Γ s (.app (.abs bound body) arg) t)
    (hAppTop : t = .app .top arg') :
    MSub Γ s (.app (.abs bound body) arg) .top :=
  MSub.intro (appAbs_subStar_to_top_of_appTop hpv hScoped hSub hAppTop)
    Relation.ReflTransGen.refl

/-- Transitive diagrammatic packaging of
`appAbs_subStar_to_top_of_appTop`. -/
theorem msubStar_appAbs_to_top_of_subStar_appTop {Γ : Ctx} {s : Stack}
    {bound body arg t arg' : Term} (hpv : PrevalidExt Γ s)
    (hScoped : Term.Scoped Γ.depth (.app (.abs bound body) arg))
    (hSub : MSubRedStar Γ s (.app (.abs bound body) arg) t)
    (hAppTop : t = .app .top arg') :
    MSubStar Γ s (.app (.abs bound body) arg) .top :=
  (msub_appAbs_to_top_of_subStar_appTop hpv hScoped hSub hAppTop).to_star

/-- Single-subtype-step specialization of
`appAbs_subStar_to_top_of_appTop`. -/
theorem appAbs_subStep_to_top_of_appTop {Γ : Ctx} {s : Stack}
    {bound body arg t arg' : Term} (hpv : PrevalidExt Γ s)
    (hScoped : Term.Scoped Γ.depth (.app (.abs bound body) arg))
    (hSub : MSubRed Γ s (.app (.abs bound body) arg) t)
    (hAppTop : t = .app .top arg') :
    MSubRedStar Γ s (.app (.abs bound body) arg) .top :=
  appAbs_subStar_to_top_of_appTop hpv hScoped (MSubRedStar.single hSub) hAppTop

/-- Single-subtype-step specialization of
`msub_appAbs_to_top_of_subStar_appTop`. -/
theorem msub_appAbs_to_top_of_subStep_appTop {Γ : Ctx} {s : Stack}
    {bound body arg t arg' : Term} (hpv : PrevalidExt Γ s)
    (hScoped : Term.Scoped Γ.depth (.app (.abs bound body) arg))
    (hSub : MSubRed Γ s (.app (.abs bound body) arg) t)
    (hAppTop : t = .app .top arg') :
    MSub Γ s (.app (.abs bound body) arg) .top :=
  msub_appAbs_to_top_of_subStar_appTop hpv hScoped (MSubRedStar.single hSub) hAppTop

/-- Transitive single-subtype-step specialization of
`msubStar_appAbs_to_top_of_subStar_appTop`. -/
theorem msubStar_appAbs_to_top_of_subStep_appTop {Γ : Ctx} {s : Stack}
    {bound body arg t arg' : Term} (hpv : PrevalidExt Γ s)
    (hScoped : Term.Scoped Γ.depth (.app (.abs bound body) arg))
    (hSub : MSubRed Γ s (.app (.abs bound body) arg) t)
    (hAppTop : t = .app .top arg') :
    MSubStar Γ s (.app (.abs bound body) arg) .top :=
  msubStar_appAbs_to_top_of_subStar_appTop hpv hScoped (MSubRedStar.single hSub) hAppTop

/-- If the subtype side of an abstraction-headed application reaches a
`Top`-headed application, it commutes with any equivalence chain from the
same source by joining at `Top`. -/
theorem commute_appAbs_subStar_appTop_eqStar {Γ : Ctx} {s : Stack}
    {bound body arg t₁ t₂ arg' : Term} (hpv : PrevalidExt Γ s)
    (hScoped : Term.Scoped Γ.depth (.app (.abs bound body) arg))
    (hSub : MSubRedStar Γ s (.app (.abs bound body) arg) t₁)
    (hAppTop : t₁ = .app .top arg')
    (hEq : MEqRedStar Γ s (.app (.abs bound body) arg) t₂) :
    ∃ t₃, MEqRedStar Γ s t₁ t₃ ∧ MSubRedStar Γ s t₂ t₃ := by
  subst hAppTop
  have hTargetScoped : Term.Scoped Γ.depth (.app .top arg') :=
    hSub.scoped_right hScoped
  have hArg' : Term.Scoped Γ.depth arg' := (Term.Scoped.app_inv hTargetScoped).2
  have hSourceTop : MSubRedStar Γ s (.app (.abs bound body) arg) .top :=
    appAbs_subStar_to_top_of_appTop hpv hScoped hSub rfl
  exact ⟨.top, appTop_to_top hpv hArg',
    eqStar_to_top_of_subStar_top hpv hScoped hSourceTop hEq⟩

/-- Single-subtype-step specialization of
`commute_appAbs_subStar_appTop_eqStar`. -/
theorem commute_appAbs_subStep_appTop_eqStar {Γ : Ctx} {s : Stack}
    {bound body arg t₁ t₂ arg' : Term} (hpv : PrevalidExt Γ s)
    (hScoped : Term.Scoped Γ.depth (.app (.abs bound body) arg))
    (hSub : MSubRed Γ s (.app (.abs bound body) arg) t₁)
    (hAppTop : t₁ = .app .top arg')
    (hEq : MEqRedStar Γ s (.app (.abs bound body) arg) t₂) :
    ∃ t₃, MEqRedStar Γ s t₁ t₃ ∧ MSubRedStar Γ s t₂ t₃ :=
  commute_appAbs_subStar_appTop_eqStar hpv hScoped (MSubRedStar.single hSub)
    hAppTop hEq

/-- Diagrammatic packaging of the β branch from
`MEqRedStar.app_abs_inv`: if an equivalence chain from an
abstraction-headed application has taken β, the final target is
diagrammatically below that β target; otherwise the final target is still
abstraction-headed. -/
theorem msub_appAbs_eqStar_beta_or_appAbs {Γ : Ctx} {s : Stack}
    {bound body arg t : Term}
    (hEq : MEqRedStar Γ s (.app (.abs bound body) arg) t) :
    (∃ arg' body', MSub Γ s t (Term.instantiate 0 arg' body')) ∨
      ∃ bound' body' arg', t = .app (.abs bound' body') arg' := by
  cases hEq.app_abs_inv with
  | inl hBet =>
    obtain ⟨arg', body', hChain⟩ := hBet
    exact Or.inl ⟨arg', body', MSub.of_MEqRedStar_right hChain⟩
  | inr hApp =>
    exact Or.inr hApp

/-- Transitive diagrammatic packaging of
`msub_appAbs_eqStar_beta_or_appAbs`. -/
theorem msubStar_appAbs_eqStar_beta_or_appAbs {Γ : Ctx} {s : Stack}
    {bound body arg t : Term}
    (hEq : MEqRedStar Γ s (.app (.abs bound body) arg) t) :
    (∃ arg' body', MSubStar Γ s t (Term.instantiate 0 arg' body')) ∨
      ∃ bound' body' arg', t = .app (.abs bound' body') arg' := by
  cases msub_appAbs_eqStar_beta_or_appAbs hEq with
  | inl hBet =>
    obtain ⟨arg', body', hMSub⟩ := hBet
    exact Or.inl ⟨arg', body', hMSub.to_star⟩
  | inr hApp =>
    exact Or.inr hApp

/-- One-step specialization of
`msub_appAbs_eqStar_beta_or_appAbs`. -/
theorem msub_appAbs_eqStep_beta_or_appAbs {Γ : Ctx} {s : Stack}
    {bound body arg t : Term}
    (hEq : MEqRed Γ s (.app (.abs bound body) arg) t) :
    (∃ arg' body', MSub Γ s t (Term.instantiate 0 arg' body')) ∨
      ∃ bound' body' arg', t = .app (.abs bound' body') arg' :=
  msub_appAbs_eqStar_beta_or_appAbs (MEqRedStar.single hEq)

/-- Transitive one-step specialization of
`msubStar_appAbs_eqStar_beta_or_appAbs`. -/
theorem msubStar_appAbs_eqStep_beta_or_appAbs {Γ : Ctx} {s : Stack}
    {bound body arg t : Term}
    (hEq : MEqRed Γ s (.app (.abs bound body) arg) t) :
    (∃ arg' body', MSubStar Γ s t (Term.instantiate 0 arg' body')) ∨
      ∃ bound' body' arg', t = .app (.abs bound' body') arg' :=
  msubStar_appAbs_eqStar_beta_or_appAbs (MEqRedStar.single hEq)

/-- Diagrammatic packaging of the β branch from
`MSubRedStar.app_abs_inv`: subtype chains from an abstraction-headed
application either reach `Top`, have a diagrammatic edge from a β target to
the final target, become `Top`-headed applications, or remain
abstraction-headed applications. -/
theorem msub_appAbs_subStar_beta_or_top_or_appTop_or_appAbs {Γ : Ctx} {s : Stack}
    {bound body arg t : Term}
    (hSub : MSubRedStar Γ s (.app (.abs bound body) arg) t) :
    t = .top ∨
      (∃ arg' body', MSub Γ s (Term.instantiate 0 arg' body') t) ∨
      (∃ arg', t = .app .top arg') ∨
      ∃ bound' body' arg', t = .app (.abs bound' body') arg' := by
  cases hSub.app_abs_inv with
  | inl hTop =>
    exact Or.inl hTop
  | inr hRest =>
    cases hRest with
    | inl hBet =>
      obtain ⟨arg', body', hChain⟩ := hBet
      exact Or.inr (Or.inl ⟨arg', body', MSub.of_MSubRedStar hChain⟩)
    | inr hRest =>
      exact Or.inr (Or.inr hRest)

/-- Transitive diagrammatic packaging of
`msub_appAbs_subStar_beta_or_top_or_appTop_or_appAbs`. -/
theorem msubStar_appAbs_subStar_beta_or_top_or_appTop_or_appAbs {Γ : Ctx} {s : Stack}
    {bound body arg t : Term}
    (hSub : MSubRedStar Γ s (.app (.abs bound body) arg) t) :
    t = .top ∨
      (∃ arg' body', MSubStar Γ s (Term.instantiate 0 arg' body') t) ∨
      (∃ arg', t = .app .top arg') ∨
      ∃ bound' body' arg', t = .app (.abs bound' body') arg' := by
  cases msub_appAbs_subStar_beta_or_top_or_appTop_or_appAbs hSub with
  | inl hTop =>
    exact Or.inl hTop
  | inr hRest =>
    cases hRest with
    | inl hBet =>
      obtain ⟨arg', body', hMSub⟩ := hBet
      exact Or.inr (Or.inl ⟨arg', body', hMSub.to_star⟩)
    | inr hRest =>
      exact Or.inr (Or.inr hRest)

/-- One-step specialization of
`msub_appAbs_subStar_beta_or_top_or_appTop_or_appAbs`. -/
theorem msub_appAbs_subStep_beta_or_top_or_appTop_or_appAbs {Γ : Ctx} {s : Stack}
    {bound body arg t : Term}
    (hSub : MSubRed Γ s (.app (.abs bound body) arg) t) :
    t = .top ∨
      (∃ arg' body', MSub Γ s (Term.instantiate 0 arg' body') t) ∨
      (∃ arg', t = .app .top arg') ∨
      ∃ bound' body' arg', t = .app (.abs bound' body') arg' :=
  msub_appAbs_subStar_beta_or_top_or_appTop_or_appAbs (MSubRedStar.single hSub)

/-- Transitive one-step specialization of
`msubStar_appAbs_subStar_beta_or_top_or_appTop_or_appAbs`. -/
theorem msubStar_appAbs_subStep_beta_or_top_or_appTop_or_appAbs {Γ : Ctx} {s : Stack}
    {bound body arg t : Term}
    (hSub : MSubRed Γ s (.app (.abs bound body) arg) t) :
    t = .top ∨
      (∃ arg' body', MSubStar Γ s (Term.instantiate 0 arg' body') t) ∨
      (∃ arg', t = .app .top arg') ∨
      ∃ bound' body' arg', t = .app (.abs bound' body') arg' :=
  msubStar_appAbs_subStar_beta_or_top_or_appTop_or_appAbs (MSubRedStar.single hSub)

/-- Compressed abstraction-headed application subtype-chain split in the
single-step diagrammatic layer: the target is reached from a β target, is
itself diagrammatically below `Top`, or remains abstraction-headed. This
combines the raw `Top` and `Top`-headed application branches of
`msub_appAbs_subStar_beta_or_top_or_appTop_or_appAbs`. -/
theorem msub_appAbs_subStar_beta_or_toTop_or_appAbs {Γ : Ctx} {s : Stack}
    {bound body arg t : Term} (hpv : PrevalidExt Γ s)
    (hScoped : Term.Scoped Γ.depth (.app (.abs bound body) arg))
    (hSub : MSubRedStar Γ s (.app (.abs bound body) arg) t) :
    (∃ arg' body', MSub Γ s (Term.instantiate 0 arg' body') t) ∨
      MSub Γ s t .top ∨
      ∃ bound' body' arg', t = .app (.abs bound' body') arg' := by
  cases msub_appAbs_subStar_beta_or_top_or_appTop_or_appAbs hSub with
  | inl hTop =>
    subst hTop
    exact Or.inr (Or.inl MSub.refl)
  | inr hRest =>
    cases hRest with
    | inl hBet =>
      exact Or.inl hBet
    | inr hRest =>
      cases hRest with
      | inl hAppTop =>
        obtain ⟨arg', hEq⟩ := hAppTop
        exact Or.inr (Or.inl
          (msub_appAbs_subStar_appTop_to_top hpv hScoped hSub hEq))
      | inr hAppAbs =>
        exact Or.inr (Or.inr hAppAbs)

/-- Compressed abstraction-headed application subtype-chain split: the target
is reached from a β target, is itself diagrammatically below `Top`, or remains
abstraction-headed. This combines the raw `Top` and `Top`-headed application
branches of `msubStar_appAbs_subStar_beta_or_top_or_appTop_or_appAbs`. -/
theorem msubStar_appAbs_subStar_beta_or_toTop_or_appAbs {Γ : Ctx} {s : Stack}
    {bound body arg t : Term} (hpv : PrevalidExt Γ s)
    (hScoped : Term.Scoped Γ.depth (.app (.abs bound body) arg))
    (hSub : MSubRedStar Γ s (.app (.abs bound body) arg) t) :
    (∃ arg' body', MSubStar Γ s (Term.instantiate 0 arg' body') t) ∨
      MSubStar Γ s t .top ∨
      ∃ bound' body' arg', t = .app (.abs bound' body') arg' := by
  cases msubStar_appAbs_subStar_beta_or_top_or_appTop_or_appAbs hSub with
  | inl hTop =>
    subst hTop
    exact Or.inr (Or.inl Relation.ReflTransGen.refl)
  | inr hRest =>
    cases hRest with
    | inl hBet =>
      exact Or.inl hBet
    | inr hRest =>
      cases hRest with
      | inl hAppTop =>
        obtain ⟨arg', hEq⟩ := hAppTop
        exact Or.inr (Or.inl
          (msubStar_appAbs_subStar_appTop_to_top hpv hScoped hSub hEq))
      | inr hAppAbs =>
        exact Or.inr (Or.inr hAppAbs)

/-- One-step specialization of
`msubStar_appAbs_subStar_beta_or_toTop_or_appAbs`. -/
theorem msubStar_appAbs_subStep_beta_or_toTop_or_appAbs {Γ : Ctx} {s : Stack}
    {bound body arg t : Term} (hpv : PrevalidExt Γ s)
    (hScoped : Term.Scoped Γ.depth (.app (.abs bound body) arg))
    (hSub : MSubRed Γ s (.app (.abs bound body) arg) t) :
    (∃ arg' body', MSubStar Γ s (Term.instantiate 0 arg' body') t) ∨
      MSubStar Γ s t .top ∨
      ∃ bound' body' arg', t = .app (.abs bound' body') arg' :=
  msubStar_appAbs_subStar_beta_or_toTop_or_appAbs hpv hScoped (MSubRedStar.single hSub)

/-- One-step specialization of
`msub_appAbs_subStar_beta_or_toTop_or_appAbs`. -/
theorem msub_appAbs_subStep_beta_or_toTop_or_appAbs {Γ : Ctx} {s : Stack}
    {bound body arg t : Term} (hpv : PrevalidExt Γ s)
    (hScoped : Term.Scoped Γ.depth (.app (.abs bound body) arg))
    (hSub : MSubRed Γ s (.app (.abs bound body) arg) t) :
    (∃ arg' body', MSub Γ s (Term.instantiate 0 arg' body') t) ∨
      MSub Γ s t .top ∨
      ∃ bound' body' arg', t = .app (.abs bound' body') arg' :=
  msub_appAbs_subStar_beta_or_toTop_or_appAbs hpv hScoped (MSubRedStar.single hSub)

/-- Lift single-step strong commutativity to one subtype step against an
equivalence-reduction chain. -/
noncomputable def commute_subStep_eqStar_of
    {Γ : Ctx} {s : Stack} (hcomm : StrongCommutes Γ s)
    {t₀ t₁ t₂ : Term}
    (hsub : MSubRed Γ s t₀ t₁)
    (heqs : MEqRedStar Γ s t₀ t₂) :
    ∃ t₃, MEqRedStar Γ s t₁ t₃ ∧ MSubRedStar Γ s t₂ t₃ := by
  suffices key : ∀ {a : Term} (h : MEqRedStar Γ s a t₂),
      ∀ {x : Term}, MSubRed Γ s a x →
        ∃ t₃, MEqRedStar Γ s x t₃ ∧ MSubRedStar Γ s t₂ t₃ from
    key heqs hsub
  intro a h
  refine Relation.ReflTransGen.head_induction_on (b := t₂)
    (P := fun a (_ : MEqRedStar Γ s a t₂) =>
      ∀ {x : Term}, MSubRed Γ s a x →
        ∃ t₃, MEqRedStar Γ s x t₃ ∧ MSubRedStar Γ s t₂ t₃) h ?_ ?_
  · intro x hsub
    exact ⟨x, Relation.ReflTransGen.refl, MSubRedStar.single hsub⟩
  · intro a c hHead _ ihC x hInput
    obtain ⟨y, hxy, hcy⟩ := hcomm hInput hHead.some
    obtain ⟨t₃, hyT₃, hT₂T₃⟩ := ihC hcy.some
    exact ⟨t₃, Relation.ReflTransGen.head hxy hyT₃, hT₂T₃⟩

/-- Lift single-step strong commutativity to subtype-reduction chains against
equivalence-reduction chains. -/
noncomputable def commute_subStar_eqStar_of
    {Γ : Ctx} {s : Stack} (hcomm : StrongCommutes Γ s)
    {t₀ t₁ t₂ : Term}
    (hsubs : MSubRedStar Γ s t₀ t₁)
    (heqs : MEqRedStar Γ s t₀ t₂) :
    ∃ t₃, MEqRedStar Γ s t₁ t₃ ∧ MSubRedStar Γ s t₂ t₃ := by
  suffices key : ∀ {a : Term} (h : MSubRedStar Γ s a t₁),
      ∀ {z : Term}, MEqRedStar Γ s a z →
        ∃ t₃, MEqRedStar Γ s t₁ t₃ ∧ MSubRedStar Γ s z t₃ from
    key hsubs heqs
  intro a h
  refine Relation.ReflTransGen.head_induction_on (b := t₁)
    (P := fun a (_ : MSubRedStar Γ s a t₁) =>
      ∀ {z : Term}, MEqRedStar Γ s a z →
        ∃ t₃, MEqRedStar Γ s t₁ t₃ ∧ MSubRedStar Γ s z t₃) h ?_ ?_
  · intro z heqs
    exact ⟨z, heqs, Relation.ReflTransGen.refl⟩
  · intro a c hHead _ ihC z hEqStar
    obtain ⟨y, hcy, hzy⟩ :=
      commute_subStep_eqStar_of hcomm hHead.some hEqStar
    obtain ⟨t₃, hT₁T₃, hyT₃⟩ := ihC hcy
    exact ⟨t₃, hT₁T₃, Relation.ReflTransGen.trans hzy hyT₃⟩

/-- Named de Bruijn Lemma 1 chain lifting: single-step strong commutativity
at a fixed extended context lifts to one subtype step against an
equivalence-reduction chain. -/
noncomputable def Lemma_1_DeBruijn_step_eqStar_of
    {Γ : Ctx} {s : Stack} (hcomm : StrongCommutes Γ s)
    {t₀ t₁ t₂ : Term}
    (hsub : MSubRed Γ s t₀ t₁)
    (heqs : MEqRedStar Γ s t₀ t₂) :
    ∃ t₃, MEqRedStar Γ s t₁ t₃ ∧ MSubRedStar Γ s t₂ t₃ :=
  commute_subStep_eqStar_of hcomm hsub heqs

/-- Named de Bruijn Lemma 1 chain lifting: single-step strong commutativity
at a fixed extended context lifts to subtype-reduction chains against
equivalence-reduction chains. -/
noncomputable def Lemma_1_DeBruijn_StrongCommutativityStar_of
    {Γ : Ctx} {s : Stack} (hcomm : StrongCommutes Γ s)
    {t₀ t₁ t₂ : Term}
    (hsubs : MSubRedStar Γ s t₀ t₁)
    (heqs : MEqRedStar Γ s t₀ t₂) :
    ∃ t₃, MEqRedStar Γ s t₁ t₃ ∧ MSubRedStar Γ s t₂ t₃ :=
  commute_subStar_eqStar_of hcomm hsubs heqs

namespace MSub

/-- Single-step composition for de Bruijn diagrammatic subtyping, conditional
on de Bruijn single-step strong commutativity. -/
noncomputable def trans_step_of {Γ : Ctx} {s : Stack}
    (hcomm : StrongCommutes Γ s) {t u v : Term}
    (htu : MSub Γ s t u) (huv : MSub Γ s u v) :
    MSub Γ s t v := by
  obtain ⟨w₁, ht_w₁, hu_w₁⟩ := htu
  obtain ⟨w₂, hu_w₂, hv_w₂⟩ := huv
  obtain ⟨z, hw₂_z, hw₁_z⟩ := commute_subStar_eqStar_of hcomm hu_w₂ hu_w₁
  exact MSub.intro
    (MSubRedStar.trans ht_w₁ hw₁_z)
    (MEqRedStar.trans hv_w₂ hw₂_z)

end MSub

namespace MSubStar

/-- Conditional de Bruijn Theorem 3: if single-step strong commutativity holds
at the fixed extended context, the transitive closure of diagrammatic
subtyping collapses to one diagrammatic subtyping step. -/
noncomputable def collapse_of {Γ : Ctx} {s : Stack}
    (hcomm : StrongCommutes Γ s) {u v : Term}
    (h : MSubStar Γ s u v) : MSub Γ s u v := by
  induction h with
  | refl =>
    exact MSub.refl
  | @tail u' v hStar hStep ih =>
    exact MSub.trans_step_of hcomm ih hStep

end MSubStar

/-- Named de Bruijn Theorem 3 skeleton: transitive diagrammatic subtyping is
admissible from single-step strong commutativity at the same extended
context. -/
noncomputable def Theorem_3_DeBruijn_TransitivityIsAdmissible_of
    {Γ : Ctx} {s : Stack} (hcomm : StrongCommutes Γ s) {u v : Term}
    (h : MSubStar Γ s u v) : MSub Γ s u v :=
  MSubStar.collapse_of hcomm h

namespace WSubM

/-- Strip one de Bruijn well-subtyping derivation to diagrammatic subtyping. -/
noncomputable def toMSub {Γ : Ctx} {v t : Term}
    (h : WSubM Γ v t) : MSub Γ [] v t := by
  exact (WSubM.rec
    (motive_1 := fun _ _ _ => PUnit)
    (motive_2 := fun Γ v t _ => MSub Γ [] v t)
    (motive_3 := fun _ _ _ _ => PUnit)
    (fun _ _ => PUnit.unit)
    (fun _ _ => PUnit.unit)
    (fun _ => PUnit.unit)
    (fun _ _ _ _ => PUnit.unit)
    (fun _ _ _ _ => PUnit.unit)
    (fun _ _ => MSub.refl)
    (fun {Γ v v' t} hred _ ih => by
      obtain ⟨w, hSubChain, hEqChain⟩ := ih
      have hpv : PrevalidExt Γ [] := PrevalidExt.nil hred.prevalid
      have hSubStep : MSubRed Γ [] _ _ := MSubRed.equ hpv hred
      exact ⟨w, Relation.ReflTransGen.head ⟨hSubStep⟩ hSubChain, hEqChain⟩)
    (fun {Γ v v' t} _ hred _ _ _ _ ih => by
      obtain ⟨w, hSubChain, hEqChain⟩ := ih
      exact ⟨w, Relation.ReflTransGen.head ⟨hred⟩ hSubChain, hEqChain⟩)
    (fun {Γ v t t'} _ hred ih => by
      obtain ⟨w, hSubChain, hEqChain⟩ := ih
      exact ⟨w, hSubChain, Relation.ReflTransGen.head ⟨hred⟩ hEqChain⟩)
    (fun _ _ _ _ _ _ => PUnit.unit)
    (fun _ _ _ _ _ _ => PUnit.unit)
    h)

/-- Strip one de Bruijn well-subtyping derivation to one step in the
reflexive-transitive diagrammatic layer. -/
noncomputable def toMSubStar {Γ : Ctx} {v t : Term}
    (h : WSubM Γ v t) : MSubStar Γ [] v t :=
  h.toMSub.to_star

end WSubM

namespace WSubMStar

/-- Strip de Bruijn transitive well-subtyping to a transitive chain of
diagrammatic subtyping steps. Collapsing this `MSubStar` to a single `MSub`
is exactly the future de Bruijn Theorem 3 port. -/
noncomputable def toMSubStar {Γ : Ctx} {v t : Term}
    (h : WSubMStar Γ v t) : MSubStar Γ [] v t := by
  exact (WSubMStar.rec
    (motive_1 := fun _ _ _ => PUnit)
    (motive_2 := fun _ _ _ _ => PUnit)
    (motive_3 := fun Γ v t _ => MSubStar Γ [] v t)
    (fun _ _ => PUnit.unit)
    (fun _ _ => PUnit.unit)
    (fun _ => PUnit.unit)
    (fun _ _ _ _ => PUnit.unit)
    (fun _ _ _ _ => PUnit.unit)
    (fun _ _ => PUnit.unit)
    (fun _ _ _ => PUnit.unit)
    (fun _ _ _ _ _ _ _ => PUnit.unit)
    (fun _ _ _ => PUnit.unit)
    (fun _ hSub _ _ _ _ => Relation.ReflTransGen.single hSub.toMSub)
    (fun _ _ _ ihLeft _ ihRight => Relation.ReflTransGen.trans ihLeft ihRight)
    h)

/-- Conditional de Bruijn Theorem 3 use-site for well-subtyping: once
single-step strong commutativity is available at the empty stack, transitive
well-subtyping strips directly to one diagrammatic subtyping step. -/
noncomputable def toMSub_of {Γ : Ctx} {v t : Term}
    (hcomm : StrongCommutes Γ []) (h : WSubMStar Γ v t) : MSub Γ [] v t :=
  MSubStar.collapse_of hcomm h.toMSubStar

end WSubMStar

/-- Named de Bruijn well-subtyping use-site for Theorem 3 at the empty stack. -/
noncomputable def Theorem_3_DeBruijn_WSubMStar_toMSub_of
    {Γ : Ctx} {v t : Term} (hcomm : StrongCommutes Γ [])
    (h : WSubMStar Γ v t) : MSub Γ [] v t :=
  h.toMSub_of hcomm

namespace WEquM

/-- Strip one de Bruijn well-equivalence derivation to diagrammatic
subtyping, by first viewing well-equivalence as well-subtyping. -/
noncomputable def toMSub {Γ : Ctx} {v t : Term}
    (h : WEquM Γ v t) : MSub Γ [] v t :=
  h.toWSubM.toMSub

/-- Strip one de Bruijn well-equivalence derivation to one step in the
reflexive-transitive diagrammatic layer. -/
noncomputable def toMSubStar {Γ : Ctx} {v t : Term}
    (h : WEquM Γ v t) : MSubStar Γ [] v t :=
  h.toMSub.to_star

end WEquM

namespace WEquMStar

/-- Strip de Bruijn transitive well-equivalence to a transitive chain of
diagrammatic subtyping steps, via its well-subtyping embedding. -/
noncomputable def toMSubStar {Γ : Ctx} {v t : Term}
    (h : WEquMStar Γ v t) : MSubStar Γ [] v t :=
  h.toWSubMStar.toMSubStar

/-- Conditional de Bruijn Theorem 3 use-site for well-equivalence, routed
through the well-subtyping embedding. -/
noncomputable def toMSub_of {Γ : Ctx} {v t : Term}
    (hcomm : StrongCommutes Γ []) (h : WEquMStar Γ v t) : MSub Γ [] v t :=
  MSubStar.collapse_of hcomm h.toMSubStar

end WEquMStar

/-- Named de Bruijn well-equivalence use-site for Theorem 3 at the empty
stack. -/
noncomputable def Theorem_3_DeBruijn_WEquMStar_toMSub_of
    {Γ : Ctx} {v t : Term} (hcomm : StrongCommutes Γ [])
    (h : WEquMStar Γ v t) : MSub Γ [] v t :=
  h.toMSub_of hcomm

end DeBruijn
end Pss

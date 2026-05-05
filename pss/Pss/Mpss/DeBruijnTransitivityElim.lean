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

/-- The full variable-source cell of de Bruijn Lemma 2. Each side is either
`Me-Var` or `Me-Pro`; the recursive `Me-Pro × Me-Pro` branch is delegated to
the supplied local diamond on the looked-up bound. -/
theorem bvar_any_of {Γ : Ctx} {s : Stack} (hdiamond : EqDiamonds Γ s)
    {i : Nat} {t₁ t₂ : Term} (hpv : PrevalidExt Γ s)
    (h₁ : MEqRed Γ s (.bvar i) t₁) (h₂ : MEqRed Γ s (.bvar i) t₂) :
    ∃ t₃, MEqRedJ Γ s t₁ t₃ ∧ MEqRedJ Γ s t₂ t₃ := by
  cases h₁ with
  | pro _ hαb hα =>
    cases h₂ with
    | pro _ hβb hβ =>
      exact pro_pro_of hdiamond hpv hαb hβb hα hβ
    | var _ hi =>
      exact pro_var hpv hαb hα hi
  | var _ hi =>
    cases h₂ with
    | pro _ hβb hβ =>
      exact var_pro hpv hi hβb hβ
    | var _ _ =>
      exact var_var hpv hi

/-- The full variable-source cell with `PrevalidExt` recovered from the
left equivalence step. -/
theorem bvar_any {Γ : Ctx} {s : Stack} (hdiamond : EqDiamonds Γ s)
    {i : Nat} {t₁ t₂ : Term}
    (h₁ : MEqRed Γ s (.bvar i) t₁) (h₂ : MEqRed Γ s (.bvar i) t₂) :
    ∃ t₃, MEqRedJ Γ s t₁ t₃ ∧ MEqRedJ Γ s t₂ t₃ := by
  cases h₁ with
  | pro hpv hBind hRed =>
      exact bvar_any_of hdiamond hpv (MEqRed.pro hpv hBind hRed) h₂
  | var hpv hi =>
      exact bvar_any_of hdiamond hpv (MEqRed.var hpv hi) h₂

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

/-- The full `Top`-headed application source cell with prevalidity and
argument scoping recovered from the left equivalence step. -/
theorem appTop_any_from_left {Γ : Ctx} {s : Stack} {u t₁ t₂ : Term}
    (h₁ : MEqRed Γ s (.app .top u) t₁)
    (h₂ : MEqRed Γ s (.app .top u) t₂) :
    ∃ t₃, MEqRedJ Γ s t₁ t₃ ∧ MEqRedJ Γ s t₂ t₃ := by
  cases h₁ with
  | app hOp hArg =>
    cases hOp with
    | top hpvCons =>
      exact appTop_any (PrevalidExt.tail hpvCons) hArg.scoped_left
        (MEqRed.app (MEqRed.top hpvCons) hArg) h₂
  | tAp hpv hu =>
    exact appTop_any hpv hu (MEqRed.tAp hpv hu) h₂

/-- The full `Top`-headed application source cell with prevalidity and
argument scoping recovered from the right equivalence step. -/
theorem appTop_any_from_right {Γ : Ctx} {s : Stack} {u t₁ t₂ : Term}
    (h₁ : MEqRed Γ s (.app .top u) t₁)
    (h₂ : MEqRed Γ s (.app .top u) t₂) :
    ∃ t₃, MEqRedJ Γ s t₁ t₃ ∧ MEqRedJ Γ s t₂ t₃ := by
  obtain ⟨t₃, hRight, hLeft⟩ := appTop_any_from_left h₂ h₁
  exact ⟨t₃, hLeft, hRight⟩

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

/-- Type-valued chain form of de Bruijn Lemma 2 lifting. This reuses the
Prop-valued star diamond theorem and chooses Type-valued chain witnesses for
its two resulting closures. -/
noncomputable def diamond_eqChain_eqChain_of
    {Γ : Ctx} {s : Stack} (hdiamond : EqDiamonds Γ s)
    {t₀ t₁ t₂ : Term}
    (h₁ : MEqRedChain Γ s t₀ t₁)
    (h₂ : MEqRedChain Γ s t₀ t₂) :
    Sigma fun t₃ =>
      MEqRedChain Γ s t₁ t₃ × MEqRedChain Γ s t₂ t₃ := by
  let h := diamond_eqStar_eqStar_of hdiamond h₁.to_star h₂.to_star
  let t₃ := Classical.choose h
  have hSpec :
      MEqRedStar Γ s t₁ t₃ ∧ MEqRedStar Γ s t₂ t₃ :=
    Classical.choose_spec h
  exact ⟨t₃, MEqRedChain.of_star hSpec.1, MEqRedChain.of_star hSpec.2⟩

/-- Named de Bruijn Lemma 2 chain lifting in Type-valued chain form. -/
noncomputable def Lemma_2_DeBruijn_DiamondMEqRedChain_of
    {Γ : Ctx} {s : Stack} (hdiamond : EqDiamonds Γ s)
    {t₀ t₁ t₂ : Term}
    (h₁ : MEqRedChain Γ s t₀ t₁)
    (h₂ : MEqRedChain Γ s t₀ t₂) :
    Sigma fun t₃ =>
      MEqRedChain Γ s t₁ t₃ × MEqRedChain Γ s t₂ t₃ :=
  diamond_eqChain_eqChain_of hdiamond h₁ h₂

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

/-- The full `Ms-Pro × Me-*` source cell for de Bruijn Lemma 1. An
equivalence step from the same variable source is either `Me-Var`, which
closes by the subtype binding, or `Me-Pro`, which is impossible because one
context index cannot carry both binding kinds. -/
theorem pro_any {Γ : Ctx} {s : Stack} {i : Nat} {t t₂ : Term}
    (hpv : PrevalidExt Γ s) (hsubBind : Γ.subBinds i t)
    (heq : MEqRed Γ s (.bvar i) t₂) :
    ∃ t₃, MEqRedJ Γ s t t₃ ∧ MSubRedJ Γ s t₂ t₃ := by
  cases heq with
  | pro _ heqBind hα =>
    exact pro_pro_vacuous hsubBind heqBind hα
  | var _ hi =>
    exact pro_var hpv hsubBind hi

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

/-- The full variable-source cell of de Bruijn Lemma 1. Subtype steps from
the source variable are `Ms-Pro`, `Ms-Equ`, or `Ms-Top`; the `Ms-Equ` branch
uses the local variable diamond. -/
theorem bvar_any_of {Γ : Ctx} {s : Stack} (hdiamond : EqDiamonds Γ s)
    {i : Nat} {t₁ t₂ : Term} (hpv : PrevalidExt Γ s)
    (hsub : MSubRed Γ s (.bvar i) t₁) (heq : MEqRed Γ s (.bvar i) t₂) :
    ∃ t₃, MEqRedJ Γ s t₁ t₃ ∧ MSubRedJ Γ s t₂ t₃ := by
  cases hsub with
  | pro _ hsubBind =>
    exact pro_any hpv hsubBind heq
  | top _ hScoped =>
    exact top_of hpv hScoped heq
  | equ _ heqSub =>
    exact equ_of hdiamond hpv heqSub heq

/-- The full variable-source commutation cell with `PrevalidExt` recovered
from the subtype step. -/
theorem bvar_any {Γ : Ctx} {s : Stack} (hdiamond : EqDiamonds Γ s)
    {i : Nat} {t₁ t₂ : Term}
    (hsub : MSubRed Γ s (.bvar i) t₁) (heq : MEqRed Γ s (.bvar i) t₂) :
    ∃ t₃, MEqRedJ Γ s t₁ t₃ ∧ MSubRedJ Γ s t₂ t₃ := by
  cases hsub with
  | pro hpv hBind =>
      exact bvar_any_of hdiamond hpv (MSubRed.pro hpv hBind) heq
  | top hpv hScoped =>
      exact bvar_any_of hdiamond hpv (MSubRed.top hpv hScoped) heq
  | equ hpv heqSub =>
      exact bvar_any_of hdiamond hpv (MSubRed.equ hpv heqSub) heq

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

/-- The full `Top`-headed application source cell with prevalidity and
argument scoping recovered from the subtype step. -/
theorem appTop_any_from_left {Γ : Ctx} {s : Stack}
    {u t₁ t₂ : Term}
    (hsub : MSubRed Γ s (.app .top u) t₁)
    (heq : MEqRed Γ s (.app .top u) t₂) :
    ∃ t₃, MEqRedJ Γ s t₁ t₃ ∧ MSubRedJ Γ s t₂ t₃ := by
  cases hsub with
  | top hpv hScoped =>
    exact appTop_any hpv (Term.Scoped.app_inv hScoped).2
      (MSubRed.top hpv hScoped) heq
  | equ hpv heqSub =>
    exact appTop_any hpv (Term.Scoped.app_inv heqSub.scoped_left).2
      (MSubRed.equ hpv heqSub) heq
  | app hOp hArg =>
    cases hOp with
    | top hpvCons hScoped =>
      exact appTop_any (PrevalidExt.tail hpvCons) hArg
        (MSubRed.app (MSubRed.top hpvCons hScoped) hArg) heq
    | equ hpvCons heqOp =>
      exact appTop_any (PrevalidExt.tail hpvCons) hArg
        (MSubRed.app (MSubRed.equ hpvCons heqOp) hArg) heq

/-- The full `Top`-headed application source cell with prevalidity and
argument scoping recovered from the equivalence step. -/
theorem appTop_any_from_right {Γ : Ctx} {s : Stack}
    {u t₁ t₂ : Term}
    (hsub : MSubRed Γ s (.app .top u) t₁)
    (heq : MEqRed Γ s (.app .top u) t₂) :
    ∃ t₃, MEqRedJ Γ s t₁ t₃ ∧ MSubRedJ Γ s t₂ t₃ := by
  cases heq with
  | app hOp hArg =>
    cases hOp with
    | top hpvCons =>
      exact appTop_any (PrevalidExt.tail hpvCons) hArg.scoped_left
        hsub (MEqRed.app (MEqRed.top hpvCons) hArg)
  | tAp hpv hu =>
    exact appTop_any hpv hu hsub (MEqRed.tAp hpv hu)

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

/-- Single-subtype-step `Top`-headed application commutation with
prevalidity and argument scoping recovered from the subtype step. -/
theorem commute_appTop_subStep_eqStar_from_left {Γ : Ctx} {s : Stack}
    {u t₁ t₂ : Term}
    (hSub : MSubRed Γ s (.app .top u) t₁)
    (hEq : MEqRedStar Γ s (.app .top u) t₂) :
    ∃ t₃, MEqRedStar Γ s t₁ t₃ ∧ MSubRedStar Γ s t₂ t₃ := by
  cases hSub with
  | top hpv hScoped =>
    exact commute_appTop_subStep_eqStar hpv (Term.Scoped.app_inv hScoped).2
      (MSubRed.top hpv hScoped) hEq
  | equ hpv heqSub =>
    exact commute_appTop_subStep_eqStar hpv (Term.Scoped.app_inv heqSub.scoped_left).2
      (MSubRed.equ hpv heqSub) hEq
  | app hOp hArg =>
    cases hOp with
    | top hpvCons hScoped =>
      exact commute_appTop_subStep_eqStar (PrevalidExt.tail hpvCons) hArg
        (MSubRed.app (MSubRed.top hpvCons hScoped) hArg) hEq
    | equ hpvCons heqOp =>
      exact commute_appTop_subStep_eqStar (PrevalidExt.tail hpvCons) hArg
        (MSubRed.app (MSubRed.equ hpvCons heqOp) hArg) hEq

/-- Single-equivalence-step `Top`-headed application commutation with
prevalidity and argument scoping recovered from the equivalence step. -/
theorem commute_appTop_subStar_eqStep_from_right {Γ : Ctx} {s : Stack}
    {u t₁ t₂ : Term}
    (hSub : MSubRedStar Γ s (.app .top u) t₁)
    (hEq : MEqRed Γ s (.app .top u) t₂) :
    ∃ t₃, MEqRedStar Γ s t₁ t₃ ∧ MSubRedStar Γ s t₂ t₃ := by
  cases hEq with
  | app hOp hArg =>
    cases hOp with
    | top hpvCons =>
      exact commute_appTop_subStar_eqStar (PrevalidExt.tail hpvCons)
        hArg.scoped_left hSub (MEqRedStar.single (MEqRed.app (MEqRed.top hpvCons) hArg))
  | tAp hpv hu =>
    exact commute_appTop_subStar_eqStar hpv hu hSub (MEqRedStar.single (MEqRed.tAp hpv hu))

/-- Direct one-step `Top`-headed application commutation with prevalidity
and argument scoping recovered from the subtype step. -/
theorem commute_appTop_subStep_eqStep_from_left {Γ : Ctx} {s : Stack}
    {u t₁ t₂ : Term}
    (hSub : MSubRed Γ s (.app .top u) t₁)
    (hEq : MEqRed Γ s (.app .top u) t₂) :
    ∃ t₃, MEqRedStar Γ s t₁ t₃ ∧ MSubRedStar Γ s t₂ t₃ :=
  commute_appTop_subStep_eqStar_from_left hSub (MEqRedStar.single hEq)

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

/-- Diagrammatic split for subtype chains from an abstraction. The target is
either `Top` or another abstraction. -/
theorem msub_abs_subStar_top_or_abs {Γ : Ctx} {s : Stack}
    {bound body t : Term} (hSub : MSubRedStar Γ s (.abs bound body) t) :
    MSub Γ s (.abs bound body) .top ∨
      ∃ bound' body',
        t = .abs bound' body' ∧
          MSub Γ s (.abs bound body) (.abs bound' body') := by
  cases hSub.abs_inv with
  | inl hTop =>
      subst hTop
      exact Or.inl (MSub.of_MSubRedStar hSub)
  | inr hAbs =>
      obtain ⟨bound', body', hEq⟩ := hAbs
      subst hEq
      exact Or.inr ⟨bound', body', rfl, MSub.of_MSubRedStar hSub⟩

/-- Transitive diagrammatic split for subtype chains from an abstraction. -/
theorem msubStar_abs_subStar_top_or_abs {Γ : Ctx} {s : Stack}
    {bound body t : Term} (hSub : MSubRedStar Γ s (.abs bound body) t) :
    MSubStar Γ s (.abs bound body) .top ∨
      ∃ bound' body',
        t = .abs bound' body' ∧
          MSubStar Γ s (.abs bound body) (.abs bound' body') := by
  cases msub_abs_subStar_top_or_abs hSub with
  | inl hTop =>
      exact Or.inl hTop.to_star
  | inr hAbs =>
      obtain ⟨bound', body', hEq, hBranch⟩ := hAbs
      exact Or.inr ⟨bound', body', hEq, hBranch.to_star⟩

/-- One-step specialization of `msub_abs_subStar_top_or_abs`. -/
theorem msub_abs_subStep_top_or_abs {Γ : Ctx} {s : Stack}
    {bound body t : Term} (hSub : MSubRed Γ s (.abs bound body) t) :
    MSub Γ s (.abs bound body) .top ∨
      ∃ bound' body',
        t = .abs bound' body' ∧
          MSub Γ s (.abs bound body) (.abs bound' body') :=
  msub_abs_subStar_top_or_abs (MSubRedStar.single hSub)

/-- Transitive diagrammatic one-step specialization of
`msub_abs_subStar_top_or_abs`. -/
theorem msubStar_abs_subStep_top_or_abs {Γ : Ctx} {s : Stack}
    {bound body t : Term} (hSub : MSubRed Γ s (.abs bound body) t) :
    MSubStar Γ s (.abs bound body) .top ∨
      ∃ bound' body',
        t = .abs bound' body' ∧
          MSubStar Γ s (.abs bound body) (.abs bound' body') :=
  msubStar_abs_subStar_top_or_abs (MSubRedStar.single hSub)

/-- Diagrammatic packaging for equivalence chains from an abstraction. The
target is always another abstraction. -/
theorem msub_abs_eqStar_abs {Γ : Ctx} {s : Stack}
    {bound body t : Term} (hpv : PrevalidExt Γ s)
    (hEq : MEqRedStar Γ s (.abs bound body) t) :
    ∃ bound' body',
      t = .abs bound' body' ∧
        MSub Γ s (.abs bound body) (.abs bound' body') := by
  obtain ⟨bound', body', hTarget⟩ := hEq.abs_inv
  subst hTarget
  exact ⟨bound', body', rfl, MSub.of_MEqRedStar_left hpv hEq⟩

/-- Transitive diagrammatic packaging for equivalence chains from an
abstraction. -/
theorem msubStar_abs_eqStar_abs {Γ : Ctx} {s : Stack}
    {bound body t : Term} (hpv : PrevalidExt Γ s)
    (hEq : MEqRedStar Γ s (.abs bound body) t) :
    ∃ bound' body',
      t = .abs bound' body' ∧
        MSubStar Γ s (.abs bound body) (.abs bound' body') := by
  obtain ⟨bound', body', hTarget, hBranch⟩ := msub_abs_eqStar_abs hpv hEq
  exact ⟨bound', body', hTarget, hBranch.to_star⟩

/-- One-step specialization of `msub_abs_eqStar_abs`. -/
theorem msub_abs_eqStep_abs {Γ : Ctx} {s : Stack}
    {bound body t : Term} (hpv : PrevalidExt Γ s)
    (hEq : MEqRed Γ s (.abs bound body) t) :
    ∃ bound' body',
      t = .abs bound' body' ∧
        MSub Γ s (.abs bound body) (.abs bound' body') :=
  msub_abs_eqStar_abs hpv (MEqRedStar.single hEq)

/-- Transitive diagrammatic one-step specialization of
`msub_abs_eqStar_abs`. -/
theorem msubStar_abs_eqStep_abs {Γ : Ctx} {s : Stack}
    {bound body t : Term} (hpv : PrevalidExt Γ s)
    (hEq : MEqRed Γ s (.abs bound body) t) :
    ∃ bound' body',
      t = .abs bound' body' ∧
        MSubStar Γ s (.abs bound body) (.abs bound' body') :=
  msubStar_abs_eqStar_abs hpv (MEqRedStar.single hEq)

/-- Combined abstraction-source dispatcher for subtype and equivalence chains.
The subtype branch to `Top` closes immediately; the remaining branch exposes
both abstraction-shaped targets diagrammatically. -/
theorem commute_abs_subStar_eqStar_top_or_absAbs {Γ : Ctx} {s : Stack}
    {bound body t₁ t₂ : Term} (hpv : PrevalidExt Γ s)
    (hScoped : Term.Scoped Γ.depth (.abs bound body))
    (hSub : MSubRedStar Γ s (.abs bound body) t₁)
    (hEq : MEqRedStar Γ s (.abs bound body) t₂) :
    (∃ t₃, MEqRedStar Γ s t₁ t₃ ∧ MSubRedStar Γ s t₂ t₃) ∨
      ∃ bound₁ body₁ bound₂ body₂,
        t₁ = .abs bound₁ body₁ ∧
          t₂ = .abs bound₂ body₂ ∧
          MSubStar Γ s (.abs bound body) (.abs bound₁ body₁) ∧
          MSubStar Γ s (.abs bound body) (.abs bound₂ body₂) := by
  cases hSub.abs_inv with
  | inl hTop =>
      subst hTop
      exact Or.inl (commute_abs_to_top_eqStar hpv hScoped hSub hEq)
  | inr hAbs₁ =>
      obtain ⟨bound₁, body₁, hTarget₁⟩ := hAbs₁
      subst hTarget₁
      obtain ⟨bound₂, body₂, hTarget₂, hEqBranch⟩ :=
        msubStar_abs_eqStar_abs hpv hEq
      subst hTarget₂
      exact Or.inr ⟨bound₁, body₁, bound₂, body₂, rfl, rfl,
        MSubStar.of_MSubRedStar hSub, hEqBranch⟩

/-- One-subtype-step specialization of
`commute_abs_subStar_eqStar_top_or_absAbs`. -/
theorem commute_abs_subStep_eqStar_top_or_absAbs {Γ : Ctx} {s : Stack}
    {bound body t₁ t₂ : Term} (hpv : PrevalidExt Γ s)
    (hScoped : Term.Scoped Γ.depth (.abs bound body))
    (hSub : MSubRed Γ s (.abs bound body) t₁)
    (hEq : MEqRedStar Γ s (.abs bound body) t₂) :
    (∃ t₃, MEqRedStar Γ s t₁ t₃ ∧ MSubRedStar Γ s t₂ t₃) ∨
      ∃ bound₁ body₁ bound₂ body₂,
        t₁ = .abs bound₁ body₁ ∧
          t₂ = .abs bound₂ body₂ ∧
          MSubStar Γ s (.abs bound body) (.abs bound₁ body₁) ∧
          MSubStar Γ s (.abs bound body) (.abs bound₂ body₂) :=
  commute_abs_subStar_eqStar_top_or_absAbs hpv hScoped
    (MSubRedStar.single hSub) hEq

/-- One-subtype-step abstraction dispatcher with source side conditions
recovered from the inspected subtype step. -/
theorem commute_abs_subStep_eqStar_top_or_absAbs_from_left {Γ : Ctx} {s : Stack}
    {bound body t₁ t₂ : Term}
    (hSub : MSubRed Γ s (.abs bound body) t₁)
    (hEq : MEqRedStar Γ s (.abs bound body) t₂) :
    (∃ t₃, MEqRedStar Γ s t₁ t₃ ∧ MSubRedStar Γ s t₂ t₃) ∨
      ∃ bound₁ body₁ bound₂ body₂,
        t₁ = .abs bound₁ body₁ ∧
          t₂ = .abs bound₂ body₂ ∧
          MSubStar Γ s (.abs bound body) (.abs bound₁ body₁) ∧
          MSubStar Γ s (.abs bound body) (.abs bound₂ body₂) :=
  commute_abs_subStep_eqStar_top_or_absAbs hSub.prevalidExt hSub.scoped_left
    hSub hEq

/-- One-equivalence-step specialization of
`commute_abs_subStar_eqStar_top_or_absAbs`. -/
theorem commute_abs_subStar_eqStep_top_or_absAbs {Γ : Ctx} {s : Stack}
    {bound body t₁ t₂ : Term} (hpv : PrevalidExt Γ s)
    (hScoped : Term.Scoped Γ.depth (.abs bound body))
    (hSub : MSubRedStar Γ s (.abs bound body) t₁)
    (hEq : MEqRed Γ s (.abs bound body) t₂) :
    (∃ t₃, MEqRedStar Γ s t₁ t₃ ∧ MSubRedStar Γ s t₂ t₃) ∨
      ∃ bound₁ body₁ bound₂ body₂,
        t₁ = .abs bound₁ body₁ ∧
          t₂ = .abs bound₂ body₂ ∧
          MSubStar Γ s (.abs bound body) (.abs bound₁ body₁) ∧
          MSubStar Γ s (.abs bound body) (.abs bound₂ body₂) :=
  commute_abs_subStar_eqStar_top_or_absAbs hpv hScoped hSub
    (MEqRedStar.single hEq)

/-- One-equivalence-step abstraction dispatcher with source side conditions
recovered from the inspected equivalence step. -/
theorem commute_abs_subStar_eqStep_top_or_absAbs_from_right {Γ : Ctx} {s : Stack}
    {bound body t₁ t₂ : Term}
    (hSub : MSubRedStar Γ s (.abs bound body) t₁)
    (hEq : MEqRed Γ s (.abs bound body) t₂) :
    (∃ t₃, MEqRedStar Γ s t₁ t₃ ∧ MSubRedStar Γ s t₂ t₃) ∨
      ∃ bound₁ body₁ bound₂ body₂,
        t₁ = .abs bound₁ body₁ ∧
          t₂ = .abs bound₂ body₂ ∧
          MSubStar Γ s (.abs bound body) (.abs bound₁ body₁) ∧
          MSubStar Γ s (.abs bound body) (.abs bound₂ body₂) :=
  commute_abs_subStar_eqStep_top_or_absAbs hEq.prevalidExt hEq.scoped_left
    hSub hEq

/-- One-step × one-step specialization of
`commute_abs_subStar_eqStar_top_or_absAbs`. -/
theorem commute_abs_subStep_eqStep_top_or_absAbs {Γ : Ctx} {s : Stack}
    {bound body t₁ t₂ : Term} (hpv : PrevalidExt Γ s)
    (hScoped : Term.Scoped Γ.depth (.abs bound body))
    (hSub : MSubRed Γ s (.abs bound body) t₁)
    (hEq : MEqRed Γ s (.abs bound body) t₂) :
    (∃ t₃, MEqRedStar Γ s t₁ t₃ ∧ MSubRedStar Γ s t₂ t₃) ∨
      ∃ bound₁ body₁ bound₂ body₂,
        t₁ = .abs bound₁ body₁ ∧
          t₂ = .abs bound₂ body₂ ∧
          MSubStar Γ s (.abs bound body) (.abs bound₁ body₁) ∧
          MSubStar Γ s (.abs bound body) (.abs bound₂ body₂) :=
  commute_abs_subStar_eqStar_top_or_absAbs hpv hScoped
    (MSubRedStar.single hSub) (MEqRedStar.single hEq)

/-- One-step abstraction dispatcher with source side conditions recovered from
the inspected subtype step. -/
theorem commute_abs_subStep_eqStep_top_or_absAbs_from_left {Γ : Ctx} {s : Stack}
    {bound body t₁ t₂ : Term}
    (hSub : MSubRed Γ s (.abs bound body) t₁)
    (hEq : MEqRed Γ s (.abs bound body) t₂) :
    (∃ t₃, MEqRedStar Γ s t₁ t₃ ∧ MSubRedStar Γ s t₂ t₃) ∨
      ∃ bound₁ body₁ bound₂ body₂,
        t₁ = .abs bound₁ body₁ ∧
          t₂ = .abs bound₂ body₂ ∧
          MSubStar Γ s (.abs bound body) (.abs bound₁ body₁) ∧
          MSubStar Γ s (.abs bound body) (.abs bound₂ body₂) :=
  commute_abs_subStep_eqStep_top_or_absAbs hSub.prevalidExt hSub.scoped_left
    hSub hEq

/-- One-step abstraction dispatcher with source side conditions recovered from
the inspected equivalence step. -/
theorem commute_abs_subStep_eqStep_top_or_absAbs_from_right {Γ : Ctx} {s : Stack}
    {bound body t₁ t₂ : Term}
    (hSub : MSubRed Γ s (.abs bound body) t₁)
    (hEq : MEqRed Γ s (.abs bound body) t₂) :
    (∃ t₃, MEqRedStar Γ s t₁ t₃ ∧ MSubRedStar Γ s t₂ t₃) ∨
      ∃ bound₁ body₁ bound₂ body₂,
        t₁ = .abs bound₁ body₁ ∧
          t₂ = .abs bound₂ body₂ ∧
          MSubStar Γ s (.abs bound body) (.abs bound₁ body₁) ∧
          MSubStar Γ s (.abs bound body) (.abs bound₂ body₂) :=
  commute_abs_subStep_eqStep_top_or_absAbs hEq.prevalidExt hEq.scoped_left
    hSub hEq

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

/-- Combined `Top` / `Top`-headed target branch for abstraction-headed
application commutation. Both branches join any equivalence chain from the
same source at `Top`. -/
theorem commute_appAbs_subStar_topOrAppTop_eqStar {Γ : Ctx} {s : Stack}
    {bound body arg t₁ t₂ : Term} (hpv : PrevalidExt Γ s)
    (hScoped : Term.Scoped Γ.depth (.app (.abs bound body) arg))
    (hSub : MSubRedStar Γ s (.app (.abs bound body) arg) t₁)
    (hShape : t₁ = .top ∨ ∃ arg', t₁ = .app .top arg')
    (hEq : MEqRedStar Γ s (.app (.abs bound body) arg) t₂) :
    ∃ t₃, MEqRedStar Γ s t₁ t₃ ∧ MSubRedStar Γ s t₂ t₃ := by
  cases hShape with
  | inl hTop =>
    subst hTop
    exact commute_appAbs_to_top_eqStar hpv hScoped hSub hEq
  | inr hAppTop =>
    obtain ⟨arg', hEqTop⟩ := hAppTop
    exact commute_appAbs_subStar_appTop_eqStar hpv hScoped hSub hEqTop hEq

/-- Single-subtype-step specialization of
`commute_appAbs_subStar_topOrAppTop_eqStar`. -/
theorem commute_appAbs_subStep_topOrAppTop_eqStar {Γ : Ctx} {s : Stack}
    {bound body arg t₁ t₂ : Term} (hpv : PrevalidExt Γ s)
    (hScoped : Term.Scoped Γ.depth (.app (.abs bound body) arg))
    (hSub : MSubRed Γ s (.app (.abs bound body) arg) t₁)
    (hShape : t₁ = .top ∨ ∃ arg', t₁ = .app .top arg')
    (hEq : MEqRedStar Γ s (.app (.abs bound body) arg) t₂) :
    ∃ t₃, MEqRedStar Γ s t₁ t₃ ∧ MSubRedStar Γ s t₂ t₃ :=
  commute_appAbs_subStar_topOrAppTop_eqStar hpv hScoped
    (MSubRedStar.single hSub) hShape hEq

/-- Single-subtype-step `Top` / `Top`-headed branch for
abstraction-headed application commutation with side conditions recovered
from the subtype step. -/
theorem commute_appAbs_subStep_topOrAppTop_eqStar_from_left {Γ : Ctx} {s : Stack}
    {bound body arg t₁ t₂ : Term}
    (hSub : MSubRed Γ s (.app (.abs bound body) arg) t₁)
    (hShape : t₁ = .top ∨ ∃ arg', t₁ = .app .top arg')
    (hEq : MEqRedStar Γ s (.app (.abs bound body) arg) t₂) :
    ∃ t₃, MEqRedStar Γ s t₁ t₃ ∧ MSubRedStar Γ s t₂ t₃ := by
  have hScoped : Term.Scoped Γ.depth (.app (.abs bound body) arg) := hSub.scoped_left
  cases hSub with
  | top hpv hScopedTop =>
    exact commute_appAbs_subStep_topOrAppTop_eqStar hpv hScopedTop
      (MSubRed.top hpv hScopedTop) hShape hEq
  | equ hpv heqSub =>
    exact commute_appAbs_subStep_topOrAppTop_eqStar hpv heqSub.scoped_left
      (MSubRed.equ hpv heqSub) hShape hEq
  | app hOp hArg =>
    cases hOp with
    | top hpvCons hOpScoped =>
      exact commute_appAbs_subStep_topOrAppTop_eqStar (PrevalidExt.tail hpvCons)
        hScoped (MSubRed.app (MSubRed.top hpvCons hOpScoped) hArg) hShape hEq
    | equ hpvCons heqOp =>
      exact commute_appAbs_subStep_topOrAppTop_eqStar (PrevalidExt.tail hpvCons)
        hScoped (MSubRed.app (MSubRed.equ hpvCons heqOp) hArg) hShape hEq
    | fOp _ _ _ =>
      cases hShape with
      | inl hTop =>
        cases hTop
      | inr hAppTop =>
        obtain ⟨arg', hTarget⟩ := hAppTop
        cases hTarget

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
  cases msub_appAbs_subStar_beta_or_toTop_or_appAbs hpv hScoped hSub with
  | inl hBet =>
    obtain ⟨arg', body', hMSub⟩ := hBet
    exact Or.inl ⟨arg', body', hMSub.to_star⟩
  | inr hRest =>
    cases hRest with
    | inl hTop =>
      exact Or.inr (Or.inl hTop.to_star)
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

/-- Abstraction-headed application subtype-chain branch classifier for
strong commutativity. The raw `Top` and `Top`-headed target branches already
produce the required join against any equivalence chain from the same source;
the remaining branches are the β target package and the residual
abstraction-headed shape. -/
theorem commute_appAbs_subStar_beta_or_join_or_appAbs {Γ : Ctx} {s : Stack}
    {bound body arg t₁ t₂ : Term} (hpv : PrevalidExt Γ s)
    (hScoped : Term.Scoped Γ.depth (.app (.abs bound body) arg))
    (hSub : MSubRedStar Γ s (.app (.abs bound body) arg) t₁)
    (hEq : MEqRedStar Γ s (.app (.abs bound body) arg) t₂) :
    (∃ arg' body', MSub Γ s (Term.instantiate 0 arg' body') t₁) ∨
      (∃ t₃, MEqRedStar Γ s t₁ t₃ ∧ MSubRedStar Γ s t₂ t₃) ∨
      ∃ bound' body' arg', t₁ = .app (.abs bound' body') arg' := by
  cases msub_appAbs_subStar_beta_or_top_or_appTop_or_appAbs hSub with
  | inl hTop =>
    exact Or.inr (Or.inl
      (commute_appAbs_subStar_topOrAppTop_eqStar hpv hScoped hSub
        (Or.inl hTop) hEq))
  | inr hRest =>
    cases hRest with
    | inl hBet =>
      exact Or.inl hBet
    | inr hRest =>
      cases hRest with
      | inl hAppTop =>
        exact Or.inr (Or.inl
          (commute_appAbs_subStar_topOrAppTop_eqStar hpv hScoped hSub
            (Or.inr hAppTop) hEq))
      | inr hAppAbs =>
        exact Or.inr (Or.inr hAppAbs)

/-- One-step specialization of
`commute_appAbs_subStar_beta_or_join_or_appAbs`. -/
theorem commute_appAbs_subStep_beta_or_join_or_appAbs {Γ : Ctx} {s : Stack}
    {bound body arg t₁ t₂ : Term} (hpv : PrevalidExt Γ s)
    (hScoped : Term.Scoped Γ.depth (.app (.abs bound body) arg))
    (hSub : MSubRed Γ s (.app (.abs bound body) arg) t₁)
    (hEq : MEqRedStar Γ s (.app (.abs bound body) arg) t₂) :
    (∃ arg' body', MSub Γ s (Term.instantiate 0 arg' body') t₁) ∨
      (∃ t₃, MEqRedStar Γ s t₁ t₃ ∧ MSubRedStar Γ s t₂ t₃) ∨
      ∃ bound' body' arg', t₁ = .app (.abs bound' body') arg' :=
  commute_appAbs_subStar_beta_or_join_or_appAbs hpv hScoped
    (MSubRedStar.single hSub) hEq

/-- One-step abstraction-headed application classifier with source side
conditions recovered from the subtype step. The structural `Ms-App` branch
whose operator remains abstraction-headed is returned directly. -/
theorem commute_appAbs_subStep_beta_or_join_or_appAbs_from_left {Γ : Ctx}
    {s : Stack} {bound body arg t₁ t₂ : Term}
    (hSub : MSubRed Γ s (.app (.abs bound body) arg) t₁)
    (hEq : MEqRedStar Γ s (.app (.abs bound body) arg) t₂) :
    (∃ arg' body', MSub Γ s (Term.instantiate 0 arg' body') t₁) ∨
      (∃ t₃, MEqRedStar Γ s t₁ t₃ ∧ MSubRedStar Γ s t₂ t₃) ∨
      ∃ bound' body' arg', t₁ = .app (.abs bound' body') arg' := by
  have hScoped : Term.Scoped Γ.depth (.app (.abs bound body) arg) := hSub.scoped_left
  cases hSub with
  | top hpv hScopedTop =>
    exact commute_appAbs_subStep_beta_or_join_or_appAbs hpv hScopedTop
      (MSubRed.top hpv hScopedTop) hEq
  | equ hpv heqSub =>
    exact commute_appAbs_subStep_beta_or_join_or_appAbs hpv heqSub.scoped_left
      (MSubRed.equ hpv heqSub) hEq
  | app hOp hArg =>
    cases hOp with
    | top hpvCons hOpScoped =>
      exact commute_appAbs_subStep_beta_or_join_or_appAbs
        (PrevalidExt.tail hpvCons) hScoped
        (MSubRed.app (MSubRed.top hpvCons hOpScoped) hArg) hEq
    | equ hpvCons heqOp =>
      exact commute_appAbs_subStep_beta_or_join_or_appAbs
        (PrevalidExt.tail hpvCons) hScoped
        (MSubRed.app (MSubRed.equ hpvCons heqOp) hArg) hEq
    | fOp _ _ hBody =>
      exact Or.inr (Or.inr ⟨bound, _, arg, rfl⟩)

/-- Paired abstraction-headed application branch classifier for strong
commutativity. It combines the subtype-side classifier with the
equivalence-side β/residual split: either the subtype target is reached from a
β target, the commutation join is already available, the equivalence target is
diagrammatically below a β target, or both targets remain
abstraction-headed. -/
theorem commute_appAbs_subStar_eqStar_beta_or_join_or_appAbs {Γ : Ctx}
    {s : Stack} {bound body arg t₁ t₂ : Term}
    (hpv : PrevalidExt Γ s)
    (hScoped : Term.Scoped Γ.depth (.app (.abs bound body) arg))
    (hSub : MSubRedStar Γ s (.app (.abs bound body) arg) t₁)
    (hEq : MEqRedStar Γ s (.app (.abs bound body) arg) t₂) :
    (∃ arg' body', MSub Γ s (Term.instantiate 0 arg' body') t₁) ∨
      (∃ t₃, MEqRedStar Γ s t₁ t₃ ∧ MSubRedStar Γ s t₂ t₃) ∨
      (∃ arg' body', MSub Γ s t₂ (Term.instantiate 0 arg' body')) ∨
      (∃ bound₁ body₁ arg₁ bound₂ body₂ arg₂,
        t₁ = .app (.abs bound₁ body₁) arg₁ ∧
        t₂ = .app (.abs bound₂ body₂) arg₂) := by
  cases commute_appAbs_subStar_beta_or_join_or_appAbs hpv hScoped hSub hEq with
  | inl hSubBet =>
    exact Or.inl hSubBet
  | inr hRest =>
    cases hRest with
    | inl hJoin =>
      exact Or.inr (Or.inl hJoin)
    | inr hSubAppAbs =>
      cases msub_appAbs_eqStar_beta_or_appAbs hEq with
      | inl hEqBet =>
        exact Or.inr (Or.inr (Or.inl hEqBet))
      | inr hEqAppAbs =>
        obtain ⟨bound₁, body₁, arg₁, hEq₁⟩ := hSubAppAbs
        obtain ⟨bound₂, body₂, arg₂, hEq₂⟩ := hEqAppAbs
        exact Or.inr (Or.inr (Or.inr
          ⟨bound₁, body₁, arg₁, bound₂, body₂, arg₂, hEq₁, hEq₂⟩))

/-- One-step specialization of
`commute_appAbs_subStar_eqStar_beta_or_join_or_appAbs`. -/
theorem commute_appAbs_subStep_eqStar_beta_or_join_or_appAbs {Γ : Ctx}
    {s : Stack} {bound body arg t₁ t₂ : Term}
    (hpv : PrevalidExt Γ s)
    (hScoped : Term.Scoped Γ.depth (.app (.abs bound body) arg))
    (hSub : MSubRed Γ s (.app (.abs bound body) arg) t₁)
    (hEq : MEqRedStar Γ s (.app (.abs bound body) arg) t₂) :
    (∃ arg' body', MSub Γ s (Term.instantiate 0 arg' body') t₁) ∨
      (∃ t₃, MEqRedStar Γ s t₁ t₃ ∧ MSubRedStar Γ s t₂ t₃) ∨
      (∃ arg' body', MSub Γ s t₂ (Term.instantiate 0 arg' body')) ∨
      (∃ bound₁ body₁ arg₁ bound₂ body₂ arg₂,
        t₁ = .app (.abs bound₁ body₁) arg₁ ∧
        t₂ = .app (.abs bound₂ body₂) arg₂) :=
  commute_appAbs_subStar_eqStar_beta_or_join_or_appAbs hpv hScoped
    (MSubRedStar.single hSub) hEq

/-- One-step paired abstraction-headed application classifier with source
side conditions recovered from the subtype step. -/
theorem commute_appAbs_subStep_eqStar_beta_or_join_or_appAbs_from_left
    {Γ : Ctx} {s : Stack} {bound body arg t₁ t₂ : Term}
    (hSub : MSubRed Γ s (.app (.abs bound body) arg) t₁)
    (hEq : MEqRedStar Γ s (.app (.abs bound body) arg) t₂) :
    (∃ arg' body', MSub Γ s (Term.instantiate 0 arg' body') t₁) ∨
      (∃ t₃, MEqRedStar Γ s t₁ t₃ ∧ MSubRedStar Γ s t₂ t₃) ∨
      (∃ arg' body', MSub Γ s t₂ (Term.instantiate 0 arg' body')) ∨
      (∃ bound₁ body₁ arg₁ bound₂ body₂ arg₂,
        t₁ = .app (.abs bound₁ body₁) arg₁ ∧
        t₂ = .app (.abs bound₂ body₂) arg₂) := by
  cases commute_appAbs_subStep_beta_or_join_or_appAbs_from_left hSub hEq with
  | inl hSubBet =>
    exact Or.inl hSubBet
  | inr hRest =>
    cases hRest with
    | inl hJoin =>
      exact Or.inr (Or.inl hJoin)
    | inr hSubAppAbs =>
      cases msub_appAbs_eqStar_beta_or_appAbs hEq with
      | inl hEqBet =>
        exact Or.inr (Or.inr (Or.inl hEqBet))
      | inr hEqAppAbs =>
        obtain ⟨bound₁, body₁, arg₁, hEq₁⟩ := hSubAppAbs
        obtain ⟨bound₂, body₂, arg₂, hEq₂⟩ := hEqAppAbs
        exact Or.inr (Or.inr (Or.inr
          ⟨bound₁, body₁, arg₁, bound₂, body₂, arg₂, hEq₁, hEq₂⟩))

/-- Direct one-equivalence-step paired abstraction-headed application
classifier with source side conditions recovered from the subtype step. -/
theorem commute_appAbs_subStep_eqStep_beta_or_join_or_appAbs_from_left
    {Γ : Ctx} {s : Stack} {bound body arg t₁ t₂ : Term}
    (hSub : MSubRed Γ s (.app (.abs bound body) arg) t₁)
    (hEq : MEqRed Γ s (.app (.abs bound body) arg) t₂) :
    (∃ arg' body', MSub Γ s (Term.instantiate 0 arg' body') t₁) ∨
      (∃ t₃, MEqRedStar Γ s t₁ t₃ ∧ MSubRedStar Γ s t₂ t₃) ∨
      (∃ arg' body', MSub Γ s t₂ (Term.instantiate 0 arg' body')) ∨
      (∃ bound₁ body₁ arg₁ bound₂ body₂ arg₂,
        t₁ = .app (.abs bound₁ body₁) arg₁ ∧
        t₂ = .app (.abs bound₂ body₂) arg₂) :=
  commute_appAbs_subStep_eqStar_beta_or_join_or_appAbs_from_left hSub
    (MEqRedStar.single hEq)

/-- Conditional abstraction-headed application commutation from the paired
branch classifier. The already-closed `Top` / `Top`-headed target branch is
handled internally; callers only need to discharge subtype β, equivalence β,
and residual app-abs/app-abs branches. -/
theorem commute_appAbs_subStar_eqStar_of_branches {Γ : Ctx} {s : Stack}
    {bound body arg t₁ t₂ : Term} (hpv : PrevalidExt Γ s)
    (hScoped : Term.Scoped Γ.depth (.app (.abs bound body) arg))
    (hSub : MSubRedStar Γ s (.app (.abs bound body) arg) t₁)
    (hEq : MEqRedStar Γ s (.app (.abs bound body) arg) t₂)
    (hSubBet :
      ∀ {arg' body' : Term},
        MSub Γ s (Term.instantiate 0 arg' body') t₁ →
        ∃ t₃, MEqRedStar Γ s t₁ t₃ ∧ MSubRedStar Γ s t₂ t₃)
    (hEqBet :
      ∀ {arg' body' : Term},
        MSub Γ s t₂ (Term.instantiate 0 arg' body') →
        ∃ t₃, MEqRedStar Γ s t₁ t₃ ∧ MSubRedStar Γ s t₂ t₃)
    (hAppAbs :
      ∀ {bound₁ body₁ arg₁ bound₂ body₂ arg₂ : Term},
        t₁ = .app (.abs bound₁ body₁) arg₁ →
        t₂ = .app (.abs bound₂ body₂) arg₂ →
        ∃ t₃, MEqRedStar Γ s t₁ t₃ ∧ MSubRedStar Γ s t₂ t₃) :
    ∃ t₃, MEqRedStar Γ s t₁ t₃ ∧ MSubRedStar Γ s t₂ t₃ := by
  cases commute_appAbs_subStar_eqStar_beta_or_join_or_appAbs
      hpv hScoped hSub hEq with
  | inl hSubBeta =>
    obtain ⟨arg', body', hMSub⟩ := hSubBeta
    exact hSubBet hMSub
  | inr hRest =>
    cases hRest with
    | inl hJoin =>
      exact hJoin
    | inr hRest =>
      cases hRest with
      | inl hEqBeta =>
        obtain ⟨arg', body', hMSub⟩ := hEqBeta
        exact hEqBet hMSub
      | inr hBothAppAbs =>
        obtain ⟨bound₁, body₁, arg₁, bound₂, body₂, arg₂, hEq₁, hEq₂⟩ :=
          hBothAppAbs
        exact hAppAbs hEq₁ hEq₂

/-- One-step specialization of
`commute_appAbs_subStar_eqStar_of_branches`. -/
theorem commute_appAbs_subStep_eqStar_of_branches {Γ : Ctx} {s : Stack}
    {bound body arg t₁ t₂ : Term} (hpv : PrevalidExt Γ s)
    (hScoped : Term.Scoped Γ.depth (.app (.abs bound body) arg))
    (hSub : MSubRed Γ s (.app (.abs bound body) arg) t₁)
    (hEq : MEqRedStar Γ s (.app (.abs bound body) arg) t₂)
    (hSubBet :
      ∀ {arg' body' : Term},
        MSub Γ s (Term.instantiate 0 arg' body') t₁ →
        ∃ t₃, MEqRedStar Γ s t₁ t₃ ∧ MSubRedStar Γ s t₂ t₃)
    (hEqBet :
      ∀ {arg' body' : Term},
        MSub Γ s t₂ (Term.instantiate 0 arg' body') →
        ∃ t₃, MEqRedStar Γ s t₁ t₃ ∧ MSubRedStar Γ s t₂ t₃)
    (hAppAbs :
      ∀ {bound₁ body₁ arg₁ bound₂ body₂ arg₂ : Term},
        t₁ = .app (.abs bound₁ body₁) arg₁ →
        t₂ = .app (.abs bound₂ body₂) arg₂ →
        ∃ t₃, MEqRedStar Γ s t₁ t₃ ∧ MSubRedStar Γ s t₂ t₃) :
    ∃ t₃, MEqRedStar Γ s t₁ t₃ ∧ MSubRedStar Γ s t₂ t₃ :=
  commute_appAbs_subStar_eqStar_of_branches hpv hScoped
    (MSubRedStar.single hSub) hEq hSubBet hEqBet hAppAbs

/-- One-step conditional abstraction-headed application commutation with the
source side conditions recovered from the subtype step. -/
theorem commute_appAbs_subStep_eqStar_of_branches_from_left {Γ : Ctx} {s : Stack}
    {bound body arg t₁ t₂ : Term}
    (hSub : MSubRed Γ s (.app (.abs bound body) arg) t₁)
    (hEq : MEqRedStar Γ s (.app (.abs bound body) arg) t₂)
    (hSubBet :
      ∀ {arg' body' : Term},
        MSub Γ s (Term.instantiate 0 arg' body') t₁ →
        ∃ t₃, MEqRedStar Γ s t₁ t₃ ∧ MSubRedStar Γ s t₂ t₃)
    (hEqBet :
      ∀ {arg' body' : Term},
        MSub Γ s t₂ (Term.instantiate 0 arg' body') →
        ∃ t₃, MEqRedStar Γ s t₁ t₃ ∧ MSubRedStar Γ s t₂ t₃)
    (hAppAbs :
      ∀ {bound₁ body₁ arg₁ bound₂ body₂ arg₂ : Term},
        t₁ = .app (.abs bound₁ body₁) arg₁ →
        t₂ = .app (.abs bound₂ body₂) arg₂ →
        ∃ t₃, MEqRedStar Γ s t₁ t₃ ∧ MSubRedStar Γ s t₂ t₃) :
    ∃ t₃, MEqRedStar Γ s t₁ t₃ ∧ MSubRedStar Γ s t₂ t₃ := by
  cases commute_appAbs_subStep_eqStar_beta_or_join_or_appAbs_from_left
      hSub hEq with
  | inl hSubBeta =>
    obtain ⟨arg', body', hMSub⟩ := hSubBeta
    exact hSubBet hMSub
  | inr hRest =>
    cases hRest with
    | inl hJoin =>
      exact hJoin
    | inr hRest =>
      cases hRest with
      | inl hEqBeta =>
        obtain ⟨arg', body', hMSub⟩ := hEqBeta
        exact hEqBet hMSub
      | inr hBothAppAbs =>
        obtain ⟨bound₁, body₁, arg₁, bound₂, body₂, arg₂, hEq₁, hEq₂⟩ :=
          hBothAppAbs
        exact hAppAbs hEq₁ hEq₂

/-- Direct one-equivalence-step conditional abstraction-headed application
commutation with the source side conditions recovered from the subtype step. -/
theorem commute_appAbs_subStep_eqStep_of_branches_from_left {Γ : Ctx}
    {s : Stack} {bound body arg t₁ t₂ : Term}
    (hSub : MSubRed Γ s (.app (.abs bound body) arg) t₁)
    (hEq : MEqRed Γ s (.app (.abs bound body) arg) t₂)
    (hSubBet :
      ∀ {arg' body' : Term},
        MSub Γ s (Term.instantiate 0 arg' body') t₁ →
        ∃ t₃, MEqRedStar Γ s t₁ t₃ ∧ MSubRedStar Γ s t₂ t₃)
    (hEqBet :
      ∀ {arg' body' : Term},
        MSub Γ s t₂ (Term.instantiate 0 arg' body') →
        ∃ t₃, MEqRedStar Γ s t₁ t₃ ∧ MSubRedStar Γ s t₂ t₃)
    (hAppAbs :
      ∀ {bound₁ body₁ arg₁ bound₂ body₂ arg₂ : Term},
        t₁ = .app (.abs bound₁ body₁) arg₁ →
        t₂ = .app (.abs bound₂ body₂) arg₂ →
        ∃ t₃, MEqRedStar Γ s t₁ t₃ ∧ MSubRedStar Γ s t₂ t₃) :
    ∃ t₃, MEqRedStar Γ s t₁ t₃ ∧ MSubRedStar Γ s t₂ t₃ :=
  commute_appAbs_subStep_eqStar_of_branches_from_left hSub
    (MEqRedStar.single hEq) hSubBet hEqBet hAppAbs

/-- One-step abstraction-headed application commutation split with the local
equivalence diamond available, preserving the residual structural `Ms-App`
operator step. `Ms-Top`, `Ms-Equ`, and the `Ms-App` branch whose operator
reaches `Top` already commute; the only residual is the structural `Ms-App`
branch whose operator remains abstraction-headed. -/
theorem commute_appAbs_subStep_eqStar_of_diamond_or_structApp {Γ : Ctx}
    {s : Stack} {bound body arg t₁ t₂ : Term}
    (hdiamond : EqDiamonds Γ s) (hpv : PrevalidExt Γ s)
    (hScoped : Term.Scoped Γ.depth (.app (.abs bound body) arg))
    (hSub : MSubRed Γ s (.app (.abs bound body) arg) t₁)
    (hEq : MEqRedStar Γ s (.app (.abs bound body) arg) t₂) :
    (∃ t₃, MEqRedStar Γ s t₁ t₃ ∧ MSubRedStar Γ s t₂ t₃) ∨
      ∃ bound' body',
        MSubRedJ Γ (arg :: s) (.abs bound body) (.abs bound' body') ∧
          t₁ = .app (.abs bound' body') arg := by
  cases hSub with
  | top _ _ =>
    exact Or.inl (commute_appAbs_subStep_to_top_eqStar hpv hScoped
      (MSubRed.top hpv hScoped) hEq)
  | equ _ hEqSub =>
    exact Or.inl (commute_equStep_eqStar_of hdiamond hpv hEqSub hEq)
  | app hOp hArg =>
    cases hOp.abs_inv with
    | inl hTop =>
      subst hTop
      exact Or.inl (commute_appAbs_subStep_appTop_eqStar hpv hScoped
        (MSubRed.app hOp hArg) rfl hEq)
    | inr hAbs =>
      obtain ⟨bound', body', hEqAbs⟩ := hAbs
      subst hEqAbs
      exact Or.inr ⟨bound', body', ⟨hOp⟩, rfl⟩

/-- Side-condition-free wrapper for
`commute_appAbs_subStep_eqStar_of_diamond_or_structApp`: source validity and
scoping are recovered from the one-step subtype proof. -/
theorem commute_appAbs_subStep_eqStar_of_diamond_or_structApp_from_left
    {Γ : Ctx} {s : Stack} {bound body arg t₁ t₂ : Term}
    (hdiamond : EqDiamonds Γ s)
    (hSub : MSubRed Γ s (.app (.abs bound body) arg) t₁)
    (hEq : MEqRedStar Γ s (.app (.abs bound body) arg) t₂) :
    (∃ t₃, MEqRedStar Γ s t₁ t₃ ∧ MSubRedStar Γ s t₂ t₃) ∨
      ∃ bound' body',
        MSubRedJ Γ (arg :: s) (.abs bound body) (.abs bound' body') ∧
          t₁ = .app (.abs bound' body') arg := by
  have hScoped : Term.Scoped Γ.depth (.app (.abs bound body) arg) := hSub.scoped_left
  cases hSub with
  | top hpv hScopedTop =>
    exact commute_appAbs_subStep_eqStar_of_diamond_or_structApp hdiamond hpv
      hScopedTop (MSubRed.top hpv hScopedTop) hEq
  | equ hpv heqSub =>
    exact commute_appAbs_subStep_eqStar_of_diamond_or_structApp hdiamond hpv
      heqSub.scoped_left (MSubRed.equ hpv heqSub) hEq
  | app hOp hArg =>
    cases hOp with
    | top hpvCons hOpScoped =>
      exact Or.inl (commute_appAbs_subStep_appTop_eqStar
        (PrevalidExt.tail hpvCons) hScoped
        (MSubRed.app (MSubRed.top hpvCons hOpScoped) hArg) rfl hEq)
    | equ hpvCons heqOp =>
      obtain ⟨bound', body', hEqAbs⟩ := heqOp.abs_inv
      subst hEqAbs
      exact Or.inr ⟨bound', body', ⟨MSubRed.equ hpvCons heqOp⟩, rfl⟩
    | fOp hBound hOpnd hBody =>
      exact Or.inr ⟨bound, _, ⟨MSubRed.fOp hBound hOpnd hBody⟩, rfl⟩

/-- Single-equivalence-step wrapper for the structural app-abs
diamond-or-residual split. -/
theorem commute_appAbs_subStep_eqStep_of_diamond_or_structApp_from_left
    {Γ : Ctx} {s : Stack} {bound body arg t₁ t₂ : Term}
    (hdiamond : EqDiamonds Γ s)
    (hSub : MSubRed Γ s (.app (.abs bound body) arg) t₁)
    (hEq : MEqRed Γ s (.app (.abs bound body) arg) t₂) :
    (∃ t₃, MEqRedStar Γ s t₁ t₃ ∧ MSubRedStar Γ s t₂ t₃) ∨
      ∃ bound' body',
        MSubRedJ Γ (arg :: s) (.abs bound body) (.abs bound' body') ∧
          t₁ = .app (.abs bound' body') arg :=
  commute_appAbs_subStep_eqStar_of_diamond_or_structApp_from_left
    hdiamond hSub (MEqRedStar.single hEq)

/-- Shape-only corollary of
`commute_appAbs_subStep_eqStar_of_diamond_or_structApp`. -/
theorem commute_appAbs_subStep_eqStar_of_diamond_or_appAbs {Γ : Ctx}
    {s : Stack} {bound body arg t₁ t₂ : Term}
    (hdiamond : EqDiamonds Γ s) (hpv : PrevalidExt Γ s)
    (hScoped : Term.Scoped Γ.depth (.app (.abs bound body) arg))
    (hSub : MSubRed Γ s (.app (.abs bound body) arg) t₁)
    (hEq : MEqRedStar Γ s (.app (.abs bound body) arg) t₂) :
    (∃ t₃, MEqRedStar Γ s t₁ t₃ ∧ MSubRedStar Γ s t₂ t₃) ∨
      ∃ bound' body' arg', t₁ = .app (.abs bound' body') arg' := by
  cases commute_appAbs_subStep_eqStar_of_diamond_or_structApp
      hdiamond hpv hScoped hSub hEq with
  | inl hJoin =>
    exact Or.inl hJoin
  | inr hStruct =>
    obtain ⟨bound', body', _hOp, hEqTarget⟩ := hStruct
    exact Or.inr ⟨bound', body', arg, hEqTarget⟩

/-- Shape-only side-condition-free wrapper for
`commute_appAbs_subStep_eqStar_of_diamond_or_appAbs`. -/
theorem commute_appAbs_subStep_eqStar_of_diamond_or_appAbs_from_left
    {Γ : Ctx} {s : Stack} {bound body arg t₁ t₂ : Term}
    (hdiamond : EqDiamonds Γ s)
    (hSub : MSubRed Γ s (.app (.abs bound body) arg) t₁)
    (hEq : MEqRedStar Γ s (.app (.abs bound body) arg) t₂) :
    (∃ t₃, MEqRedStar Γ s t₁ t₃ ∧ MSubRedStar Γ s t₂ t₃) ∨
      ∃ bound' body' arg', t₁ = .app (.abs bound' body') arg' := by
  cases commute_appAbs_subStep_eqStar_of_diamond_or_structApp_from_left
      hdiamond hSub hEq with
  | inl hJoin =>
    exact Or.inl hJoin
  | inr hStruct =>
    obtain ⟨bound', body', _hOp, hEqTarget⟩ := hStruct
    exact Or.inr ⟨bound', body', arg, hEqTarget⟩

/-- Single-equivalence-step shape-only wrapper for the app-abs
diamond-or-residual split. -/
theorem commute_appAbs_subStep_eqStep_of_diamond_or_appAbs_from_left
    {Γ : Ctx} {s : Stack} {bound body arg t₁ t₂ : Term}
    (hdiamond : EqDiamonds Γ s)
    (hSub : MSubRed Γ s (.app (.abs bound body) arg) t₁)
    (hEq : MEqRed Γ s (.app (.abs bound body) arg) t₂) :
    (∃ t₃, MEqRedStar Γ s t₁ t₃ ∧ MSubRedStar Γ s t₂ t₃) ∨
      ∃ bound' body' arg', t₁ = .app (.abs bound' body') arg' :=
  commute_appAbs_subStep_eqStar_of_diamond_or_appAbs_from_left hdiamond hSub
    (MEqRedStar.single hEq)

/-- Same-argument structural application commutation for abstraction-headed
applications. If the subtype and equivalence sides both step only the
operator under the same argument stack, strong commutativity at that operator
stack lifts to a join of the two applications. The general changed-argument
case still needs stack-transport infrastructure. -/
theorem commute_appAbs_structApp_eqStep_sameArg_of {Γ : Ctx} {s : Stack}
    {bound body arg bound₁ body₁ bound₂ body₂ : Term}
    (hcommArg : StrongCommutes Γ (arg :: s))
    (hArgScoped : Term.Scoped Γ.depth arg)
    (hSubOp : MSubRed Γ (arg :: s) (.abs bound body) (.abs bound₁ body₁))
    (hEqOp : MEqRed Γ (arg :: s) (.abs bound body) (.abs bound₂ body₂)) :
    ∃ t₃,
      MEqRedStar Γ s (.app (.abs bound₁ body₁) arg) t₃ ∧
        MSubRedStar Γ s (.app (.abs bound₂ body₂) arg) t₃ := by
  obtain ⟨op₃, hEqJoin, hSubJoin⟩ := hcommArg hSubOp hEqOp
  have hpvNil : PrevalidExt Γ [] := PrevalidExt.nil hEqJoin.some.prevalid
  have hArgRefl : MEqRed Γ [] arg arg := MEqRed.refl hpvNil hArgScoped
  exact ⟨.app op₃ arg,
    MEqRedStar.single (MEqRed.app hEqJoin.some hArgRefl),
    MSubRedStar.single (MSubRed.app hSubJoin.some hArgScoped)⟩

/-- Side-condition-free same-argument structural application commutation:
the fixed argument scopedness is recovered from the operator subtype step. -/
theorem commute_appAbs_structApp_eqStep_sameArg_of_from_left {Γ : Ctx} {s : Stack}
    {bound body arg bound₁ body₁ bound₂ body₂ : Term}
    (hcommArg : StrongCommutes Γ (arg :: s))
    (hSubOp : MSubRed Γ (arg :: s) (.abs bound body) (.abs bound₁ body₁))
    (hEqOp : MEqRed Γ (arg :: s) (.abs bound body) (.abs bound₂ body₂)) :
    ∃ t₃,
      MEqRedStar Γ s (.app (.abs bound₁ body₁) arg) t₃ ∧
        MSubRedStar Γ s (.app (.abs bound₂ body₂) arg) t₃ :=
  commute_appAbs_structApp_eqStep_sameArg_of hcommArg
    (PrevalidExt.head_scoped hSubOp.prevalidExt) hSubOp hEqOp

/-- Lift an operator subtype-reduction chain under a fixed argument into an
application subtype-reduction chain. -/
theorem msubRedStar_app_fixed_arg {Γ : Ctx} {s : Stack}
    {arg u u' : Term} (hArgScoped : Term.Scoped Γ.depth arg)
    (h : MSubRedStar Γ (arg :: s) u u') :
    MSubRedStar Γ s (.app u arg) (.app u' arg) := by
  induction h with
  | refl =>
    exact Relation.ReflTransGen.refl
  | @tail y z hStar hStep ih =>
    exact Relation.ReflTransGen.trans ih
      (MSubRedStar.single (MSubRed.app hStep.some hArgScoped))

/-- Lift an operator equivalence-reduction chain under a fixed argument into
an application equivalence-reduction chain. -/
theorem meqRedStar_app_fixed_arg {Γ : Ctx} {s : Stack}
    {arg u u' : Term} (hArg : MEqRed Γ [] arg arg)
    (h : MEqRedStar Γ (arg :: s) u u') :
    MEqRedStar Γ s (.app u arg) (.app u' arg) := by
  induction h with
  | refl =>
    exact Relation.ReflTransGen.refl
  | @tail y z hStar hStep ih =>
    exact Relation.ReflTransGen.trans ih
      (MEqRedStar.single (MEqRed.app hStep.some hArg))

/-- Lift a diagrammatic subtype step under a fixed application argument. -/
theorem msub_app_fixed_arg {Γ : Ctx} {s : Stack}
    {arg u v : Term}
    (hpvTail : PrevalidExt Γ s)
    (hArgScoped : Term.Scoped Γ.depth arg)
    (h : MSub Γ (arg :: s) u v) :
    MSub Γ s (.app u arg) (.app v arg) := by
  obtain ⟨w, hSub, hEq⟩ := h
  have hpvNil : PrevalidExt Γ [] := PrevalidExt.nil (PrevalidExt.ctx hpvTail)
  have hArgRefl : MEqRed Γ [] arg arg := MEqRed.refl hpvNil hArgScoped
  exact MSub.intro
    (msubRedStar_app_fixed_arg hArgScoped hSub)
    (meqRedStar_app_fixed_arg hArgRefl hEq)

/-- Lift a diagrammatic subtype chain under a fixed application argument. -/
theorem msubStar_app_fixed_arg {Γ : Ctx} {s : Stack}
    {arg u v : Term}
    (hpvTail : PrevalidExt Γ s)
    (hArgScoped : Term.Scoped Γ.depth arg)
    (h : MSubStar Γ (arg :: s) u v) :
    MSubStar Γ s (.app u arg) (.app v arg) := by
  induction h with
  | refl =>
    exact Relation.ReflTransGen.refl
  | @tail mid v hStar hStep ih =>
    exact Relation.ReflTransGen.trans ih
      (MSub.to_star (msub_app_fixed_arg hpvTail hArgScoped hStep))

/-- Changed-argument structural application commutation for
abstraction-headed applications, isolated behind the precise missing
stack-head transport. The transport premise moves the operator-side subtype
join from the old stack head `arg :: s` to the new one `arg' :: s`. -/
theorem commute_appAbs_structApp_eqStep_of_stackHead_transport {Γ : Ctx}
    {s : Stack} {bound body arg bound₁ body₁ bound₂ body₂ arg' : Term}
    (hcommArg : StrongCommutes Γ (arg :: s))
    (hSubOp : MSubRed Γ (arg :: s) (.abs bound body) (.abs bound₁ body₁))
    (hEqOp : MEqRed Γ (arg :: s) (.abs bound body) (.abs bound₂ body₂))
    (hEqArg : MEqRed Γ [] arg arg')
    (hTransport :
      ∀ {u v : Term},
        MSubRedStar Γ (arg :: s) u v →
        MSubRedStar Γ (arg' :: s) u v) :
    ∃ t₃,
      MEqRedStar Γ s (.app (.abs bound₁ body₁) arg) t₃ ∧
        MSubRedStar Γ s (.app (.abs bound₂ body₂) arg') t₃ := by
  obtain ⟨op₃, hEqJoin, hSubJoin⟩ := hcommArg hSubOp hEqOp
  have hArg'Scoped : Term.Scoped Γ.depth arg' := hEqArg.scoped_right
  exact ⟨.app op₃ arg',
    MEqRedStar.single (MEqRed.app hEqJoin.some hEqArg),
    msubRedStar_app_fixed_arg hArg'Scoped
      (hTransport (Relation.ReflTransGen.single hSubJoin))⟩

/-- One-step stack-head transport splitter for abstraction-to-abstraction
subtype steps. At a non-empty operator stack, the abstraction-to-abstraction
branches are `FOp`-shaped, so they remain as explicit residuals whose body
derivation is tied to the old stack head. -/
theorem msub_abs_step_stackHead_transport_or_fOp {Γ : Ctx} {s : Stack}
    {arg arg' bound body bound' body' : Term}
    (_hpvTail : PrevalidExt Γ s)
    (_hEqArg : MEqRed Γ [] arg arg')
    (h : MSubRed Γ (arg :: s) (.abs bound body) (.abs bound' body')) :
    MSubRedJ Γ (arg' :: s) (.abs bound body) (.abs bound' body') ∨
      (∃ oldArg rest,
        arg :: s = oldArg :: rest ∧
          MEqRedJ Γ [] bound bound' ∧
          MEqRedJ ({ bound := oldArg, kind := .equ } :: Γ)
            (Stack.shift 0 rest) body body') ∨
      (∃ oldArg rest,
        arg :: s = oldArg :: rest ∧
          bound' = bound ∧
          MSubRedJ ({ bound := oldArg, kind := .equ } :: Γ)
            (Stack.shift 0 rest) body body') := by
  cases h with
  | equ _ heq =>
    cases heq with
    | fOp hBound _ hBody =>
      exact Or.inr (Or.inl ⟨arg, s, rfl, ⟨hBound⟩, ⟨hBody⟩⟩)
  | fOp _ _ hBody =>
    exact Or.inr (Or.inr ⟨arg, s, rfl, rfl, ⟨hBody⟩⟩)

/-- Side-condition-free stack-head transport splitter for one-step
abstraction-to-abstraction subtype reductions. The tail prevalidity premise
of `msub_abs_step_stackHead_transport_or_fOp` is recovered from the subtype
step. -/
theorem msub_abs_step_stackHead_transport_or_fOp_from_left {Γ : Ctx} {s : Stack}
    {arg arg' bound body bound' body' : Term}
    (hEqArg : MEqRed Γ [] arg arg')
    (h : MSubRed Γ (arg :: s) (.abs bound body) (.abs bound' body')) :
    MSubRedJ Γ (arg' :: s) (.abs bound body) (.abs bound' body') ∨
      (∃ oldArg rest,
        arg :: s = oldArg :: rest ∧
          MEqRedJ Γ [] bound bound' ∧
          MEqRedJ ({ bound := oldArg, kind := .equ } :: Γ)
            (Stack.shift 0 rest) body body') ∨
      (∃ oldArg rest,
        arg :: s = oldArg :: rest ∧
          bound' = bound ∧
          MSubRedJ ({ bound := oldArg, kind := .equ } :: Γ)
            (Stack.shift 0 rest) body body') :=
  msub_abs_step_stackHead_transport_or_fOp
    (PrevalidExt.tail h.prevalidExt) hEqArg h

/-- Changed-argument structural application commutation reduced to the
operator-side `FOp` residual. After applying strong commutativity to the
operator steps, the only obstruction to building the changed-argument
application join is transporting the operator subtype join across the stack
head; for abstraction targets that obstruction is exactly an `FOp` body
derivation tied to the old head. -/
theorem commute_appAbs_structApp_eqStep_or_fOp_residual {Γ : Ctx} {s : Stack}
    {bound body arg bound₁ body₁ bound₂ body₂ arg' : Term}
    (hpvTail : PrevalidExt Γ s)
    (hcommArg : StrongCommutes Γ (arg :: s))
    (hSubOp : MSubRed Γ (arg :: s) (.abs bound body) (.abs bound₁ body₁))
    (hEqOp : MEqRed Γ (arg :: s) (.abs bound body) (.abs bound₂ body₂))
    (hEqArg : MEqRed Γ [] arg arg') :
    (∃ t₃,
      MEqRedStar Γ s (.app (.abs bound₁ body₁) arg) t₃ ∧
        MSubRedStar Γ s (.app (.abs bound₂ body₂) arg') t₃) ∨
      ∃ joinBound joinBody,
        MEqRedJ Γ (arg :: s) (.abs bound₁ body₁) (.abs joinBound joinBody) ∧
          ((∃ oldArg rest,
            arg :: s = oldArg :: rest ∧
              MEqRedJ Γ [] bound₂ joinBound ∧
              MEqRedJ ({ bound := oldArg, kind := .equ } :: Γ)
                (Stack.shift 0 rest) body₂ joinBody) ∨
            ∃ oldArg rest,
              arg :: s = oldArg :: rest ∧
                joinBound = bound₂ ∧
                MSubRedJ ({ bound := oldArg, kind := .equ } :: Γ)
                  (Stack.shift 0 rest) body₂ joinBody) := by
  obtain ⟨op₃, hEqJoin, hSubJoin⟩ := hcommArg hSubOp hEqOp
  obtain ⟨joinBound, joinBody, hOp₃⟩ := hEqJoin.some.abs_inv
  subst hOp₃
  cases msub_abs_step_stackHead_transport_or_fOp hpvTail hEqArg hSubJoin.some with
  | inl hTransportStep =>
    have hArg'Scoped : Term.Scoped Γ.depth arg' := hEqArg.scoped_right
    exact Or.inl ⟨.app (.abs joinBound joinBody) arg',
      MEqRedStar.single (MEqRed.app hEqJoin.some hEqArg),
      MSubRedStar.single (MSubRed.app hTransportStep.some hArg'Scoped)⟩
  | inr hResidual =>
    exact Or.inr ⟨joinBound, joinBody, hEqJoin, hResidual⟩

/-- Side-condition-free wrapper for
`commute_appAbs_structApp_eqStep_or_fOp_residual`: the tail stack
prevalidity is recovered from the operator subtype step. -/
theorem commute_appAbs_structApp_eqStep_or_fOp_residual_from_left {Γ : Ctx}
    {s : Stack} {bound body arg bound₁ body₁ bound₂ body₂ arg' : Term}
    (hcommArg : StrongCommutes Γ (arg :: s))
    (hSubOp : MSubRed Γ (arg :: s) (.abs bound body) (.abs bound₁ body₁))
    (hEqOp : MEqRed Γ (arg :: s) (.abs bound body) (.abs bound₂ body₂))
    (hEqArg : MEqRed Γ [] arg arg') :
    (∃ t₃,
      MEqRedStar Γ s (.app (.abs bound₁ body₁) arg) t₃ ∧
        MSubRedStar Γ s (.app (.abs bound₂ body₂) arg') t₃) ∨
      ∃ joinBound joinBody,
        MEqRedJ Γ (arg :: s) (.abs bound₁ body₁) (.abs joinBound joinBody) ∧
          ((∃ oldArg rest,
            arg :: s = oldArg :: rest ∧
              MEqRedJ Γ [] bound₂ joinBound ∧
              MEqRedJ ({ bound := oldArg, kind := .equ } :: Γ)
                (Stack.shift 0 rest) body₂ joinBody) ∨
            ∃ oldArg rest,
              arg :: s = oldArg :: rest ∧
                joinBound = bound₂ ∧
                MSubRedJ ({ bound := oldArg, kind := .equ } :: Γ)
                  (Stack.shift 0 rest) body₂ joinBody) :=
  commute_appAbs_structApp_eqStep_or_fOp_residual
    (PrevalidExt.tail hSubOp.prevalidExt) hcommArg hSubOp hEqOp hEqArg

/-- Changed-argument structural application commutation isolated behind the
two precise `FOp` replacement obligations. These handlers are weaker than a
blanket stack-head transport theorem: they only need to replace the old
`.equ` head in the two residual shapes exposed by
`commute_appAbs_structApp_eqStep_or_fOp_residual`. -/
theorem commute_appAbs_structApp_eqStep_of_fOp_handlers {Γ : Ctx} {s : Stack}
    {bound body arg bound₁ body₁ bound₂ body₂ arg' : Term}
    (_hpvTail : PrevalidExt Γ s)
    (hcommArg : StrongCommutes Γ (arg :: s))
    (hSubOp : MSubRed Γ (arg :: s) (.abs bound body) (.abs bound₁ body₁))
    (hEqOp : MEqRed Γ (arg :: s) (.abs bound body) (.abs bound₂ body₂))
    (hEqArg : MEqRed Γ [] arg arg')
    (hEquResidual :
      ∀ {joinBound joinBody oldArg : Term} {rest : Stack},
        arg :: s = oldArg :: rest →
        MEqRed Γ [] bound₂ joinBound →
        MEqRed ({ bound := oldArg, kind := .equ } :: Γ)
          (Stack.shift 0 rest) body₂ joinBody →
        MSubRedStar Γ (arg' :: s) (.abs bound₂ body₂)
          (.abs joinBound joinBody))
    (hSubResidual :
      ∀ {joinBody oldArg : Term} {rest : Stack},
        arg :: s = oldArg :: rest →
        MSubRed ({ bound := oldArg, kind := .equ } :: Γ)
          (Stack.shift 0 rest) body₂ joinBody →
        MSubRedStar Γ (arg' :: s) (.abs bound₂ body₂)
          (.abs bound₂ joinBody)) :
    ∃ t₃,
      MEqRedStar Γ s (.app (.abs bound₁ body₁) arg) t₃ ∧
        MSubRedStar Γ s (.app (.abs bound₂ body₂) arg') t₃ := by
  cases commute_appAbs_structApp_eqStep_or_fOp_residual_from_left hcommArg hSubOp
      hEqOp hEqArg with
  | inl hJoin =>
    exact hJoin
  | inr hResidual =>
    obtain ⟨joinBound, joinBody, hEqJoin, hResidual⟩ := hResidual
    have hArg'Scoped : Term.Scoped Γ.depth arg' := hEqArg.scoped_right
    refine ⟨.app (.abs joinBound joinBody) arg',
      MEqRedStar.single (MEqRed.app hEqJoin.some hEqArg), ?_⟩
    cases hResidual with
    | inl hEqu =>
      obtain ⟨oldArg, rest, hStack, hBound, hBody⟩ := hEqu
      exact msubRedStar_app_fixed_arg hArg'Scoped
        (hEquResidual hStack hBound.some hBody.some)
    | inr hSub =>
      obtain ⟨oldArg, rest, hStack, hBoundEq, hBody⟩ := hSub
      cases hBoundEq
      exact msubRedStar_app_fixed_arg hArg'Scoped
        (hSubResidual hStack hBody.some)

/-- Side-condition-free wrapper for
`commute_appAbs_structApp_eqStep_of_fOp_handlers`: the tail stack
prevalidity is recovered from the operator subtype step. -/
theorem commute_appAbs_structApp_eqStep_of_fOp_handlers_from_left {Γ : Ctx}
    {s : Stack} {bound body arg bound₁ body₁ bound₂ body₂ arg' : Term}
    (hcommArg : StrongCommutes Γ (arg :: s))
    (hSubOp : MSubRed Γ (arg :: s) (.abs bound body) (.abs bound₁ body₁))
    (hEqOp : MEqRed Γ (arg :: s) (.abs bound body) (.abs bound₂ body₂))
    (hEqArg : MEqRed Γ [] arg arg')
    (hEquResidual :
      ∀ {joinBound joinBody oldArg : Term} {rest : Stack},
        arg :: s = oldArg :: rest →
        MEqRed Γ [] bound₂ joinBound →
        MEqRed ({ bound := oldArg, kind := .equ } :: Γ)
          (Stack.shift 0 rest) body₂ joinBody →
        MSubRedStar Γ (arg' :: s) (.abs bound₂ body₂)
          (.abs joinBound joinBody))
    (hSubResidual :
      ∀ {joinBody oldArg : Term} {rest : Stack},
        arg :: s = oldArg :: rest →
        MSubRed ({ bound := oldArg, kind := .equ } :: Γ)
          (Stack.shift 0 rest) body₂ joinBody →
        MSubRedStar Γ (arg' :: s) (.abs bound₂ body₂)
          (.abs bound₂ joinBody)) :
    ∃ t₃,
      MEqRedStar Γ s (.app (.abs bound₁ body₁) arg) t₃ ∧
        MSubRedStar Γ s (.app (.abs bound₂ body₂) arg') t₃ :=
  commute_appAbs_structApp_eqStep_of_fOp_handlers
    (PrevalidExt.tail hSubOp.prevalidExt) hcommArg hSubOp hEqOp hEqArg
    hEquResidual hSubResidual

/-- Changed-argument structural application commutation reduced to body-level
replacement under the `FOp` `.equ` head. The two replacement premises are the
remaining de Bruijn analogue of stack-head replacement: they move residual
body reductions from the old head `arg` to the changed head `arg'`. -/
theorem commute_appAbs_structApp_eqStep_of_body_fOp_replacements {Γ : Ctx}
    {s : Stack} {bound body arg bound₁ body₁ bound₂ body₂ arg' : Term}
    (hpvTail : PrevalidExt Γ s)
    (hcommArg : StrongCommutes Γ (arg :: s))
    (hSubOp : MSubRed Γ (arg :: s) (.abs bound body) (.abs bound₁ body₁))
    (hEqOp : MEqRed Γ (arg :: s) (.abs bound body) (.abs bound₂ body₂))
    (hEqArg : MEqRed Γ [] arg arg')
    (hEquBodyReplace :
      ∀ {joinBound joinBody : Term},
        MEqRed Γ [] bound₂ joinBound →
        MEqRed ({ bound := arg, kind := .equ } :: Γ)
          (Stack.shift 0 s) body₂ joinBody →
        MEqRed ({ bound := arg', kind := .equ } :: Γ)
          (Stack.shift 0 s) body₂ joinBody)
    (hSubBodyReplace :
      ∀ {joinBody : Term},
        MSubRed ({ bound := arg, kind := .equ } :: Γ)
          (Stack.shift 0 s) body₂ joinBody →
        MSubRed ({ bound := arg', kind := .equ } :: Γ)
          (Stack.shift 0 s) body₂ joinBody) :
    ∃ t₃,
      MEqRedStar Γ s (.app (.abs bound₁ body₁) arg) t₃ ∧
        MSubRedStar Γ s (.app (.abs bound₂ body₂) arg') t₃ := by
  have hArg'Scoped : Term.Scoped Γ.depth arg' := hEqArg.scoped_right
  have hBound₂Scoped : Term.Scoped Γ.depth bound₂ :=
    (Term.Scoped.abs_inv hEqOp.scoped_right).1
  have hpvNew : PrevalidExt Γ (arg' :: s) :=
    PrevalidExt.cons hpvTail hArg'Scoped
  refine commute_appAbs_structApp_eqStep_of_fOp_handlers hpvTail hcommArg
    hSubOp hEqOp hEqArg ?_ ?_
  · intro joinBound joinBody oldArg rest hStack hBound hBody
    cases hStack
    exact MSubRedStar.single (MSubRed.equ hpvNew
      (MEqRed.fOp hBound hArg'Scoped (hEquBodyReplace hBound hBody)))
  · intro joinBody oldArg rest hStack hBody
    cases hStack
    exact MSubRedStar.single (MSubRed.fOp hBound₂Scoped hArg'Scoped
      (hSubBodyReplace hBody))

/-- Side-condition-free wrapper for
`commute_appAbs_structApp_eqStep_of_body_fOp_replacements`: the tail stack
prevalidity is recovered from the operator subtype step. -/
theorem commute_appAbs_structApp_eqStep_of_body_fOp_replacements_from_left
    {Γ : Ctx} {s : Stack}
    {bound body arg bound₁ body₁ bound₂ body₂ arg' : Term}
    (hcommArg : StrongCommutes Γ (arg :: s))
    (hSubOp : MSubRed Γ (arg :: s) (.abs bound body) (.abs bound₁ body₁))
    (hEqOp : MEqRed Γ (arg :: s) (.abs bound body) (.abs bound₂ body₂))
    (hEqArg : MEqRed Γ [] arg arg')
    (hEquBodyReplace :
      ∀ {joinBound joinBody : Term},
        MEqRed Γ [] bound₂ joinBound →
        MEqRed ({ bound := arg, kind := .equ } :: Γ)
          (Stack.shift 0 s) body₂ joinBody →
        MEqRed ({ bound := arg', kind := .equ } :: Γ)
          (Stack.shift 0 s) body₂ joinBody)
    (hSubBodyReplace :
      ∀ {joinBody : Term},
        MSubRed ({ bound := arg, kind := .equ } :: Γ)
          (Stack.shift 0 s) body₂ joinBody →
        MSubRed ({ bound := arg', kind := .equ } :: Γ)
          (Stack.shift 0 s) body₂ joinBody) :
    ∃ t₃,
      MEqRedStar Γ s (.app (.abs bound₁ body₁) arg) t₃ ∧
        MSubRedStar Γ s (.app (.abs bound₂ body₂) arg') t₃ :=
  commute_appAbs_structApp_eqStep_of_body_fOp_replacements
    (PrevalidExt.tail hSubOp.prevalidExt) hcommArg hSubOp hEqOp hEqArg
    hEquBodyReplace hSubBodyReplace

/-- Lift a body subtype-reduction chain under an `.equ` head into an
abstraction subtype-reduction chain through the matching `FOp` stack head,
keeping the abstraction bound fixed. -/
theorem msubRedStar_abs_fOp_body_fixed_bound {Γ : Ctx} {s : Stack}
    {α bound body body' : Term}
    (hBoundScoped : Term.Scoped Γ.depth bound)
    (hα : Term.Scoped Γ.depth α)
    (hBody : MSubRedStar ({ bound := α, kind := .equ } :: Γ)
      (Stack.shift 0 s) body body') :
    MSubRedStar Γ (α :: s) (.abs bound body) (.abs bound body') := by
  induction hBody with
  | refl =>
    exact Relation.ReflTransGen.refl
  | @tail mid body' hStar hStep ih =>
    exact Relation.ReflTransGen.trans ih
      (MSubRedStar.single (MSubRed.fOp hBoundScoped hα hStep.some))

/-- Lift a body equivalence-reduction chain under an `.equ` head into an
abstraction equivalence-reduction chain through the matching `FOp` stack
head, keeping the abstraction bound fixed. -/
theorem meqRedStar_abs_fOp_body_fixed_bound {Γ : Ctx} {s : Stack}
    {α bound body body' : Term}
    (hpvTail : PrevalidExt Γ s)
    (hBoundScoped : Term.Scoped Γ.depth bound)
    (hα : Term.Scoped Γ.depth α)
    (hBody : MEqRedStar ({ bound := α, kind := .equ } :: Γ)
      (Stack.shift 0 s) body body') :
    MEqRedStar Γ (α :: s) (.abs bound body) (.abs bound body') := by
  have hpvNil : PrevalidExt Γ [] := PrevalidExt.nil (PrevalidExt.ctx hpvTail)
  have hBoundRefl : MEqRed Γ [] bound bound :=
    MEqRed.refl hpvNil hBoundScoped
  induction hBody with
  | refl =>
    exact Relation.ReflTransGen.refl
  | @tail mid body' hStar hStep ih =>
    exact Relation.ReflTransGen.trans ih
      (MEqRedStar.single (MEqRed.fOp hBoundRefl hα hStep.some))

/-- Lift a diagrammatic body subtyping step under an `.equ` head into an
abstraction subtyping step through `FOp`, keeping the abstraction bound fixed.
-/
theorem msub_abs_fOp_body_fixed_bound {Γ : Ctx} {s : Stack}
    {α bound body body' : Term}
    (hpvTail : PrevalidExt Γ s)
    (hBoundScoped : Term.Scoped Γ.depth bound)
    (hα : Term.Scoped Γ.depth α)
    (hBody : MSub ({ bound := α, kind := .equ } :: Γ)
      (Stack.shift 0 s) body body') :
    MSub Γ (α :: s) (.abs bound body) (.abs bound body') := by
  obtain ⟨joinBody, hSubBody, hEqBody⟩ := hBody
  exact MSub.intro
    (msubRedStar_abs_fOp_body_fixed_bound hBoundScoped hα hSubBody)
    (meqRedStar_abs_fOp_body_fixed_bound hpvTail hBoundScoped hα hEqBody)

/-- Lift a diagrammatic body subtyping chain under an `.equ` head into an
abstraction subtyping chain through `FOp`, keeping the abstraction bound
fixed. -/
theorem msubStar_abs_fOp_body_fixed_bound {Γ : Ctx} {s : Stack}
    {α bound body body' : Term}
    (hpvTail : PrevalidExt Γ s)
    (hBoundScoped : Term.Scoped Γ.depth bound)
    (hα : Term.Scoped Γ.depth α)
    (hBody : MSubStar ({ bound := α, kind := .equ } :: Γ)
      (Stack.shift 0 s) body body') :
    MSubStar Γ (α :: s) (.abs bound body) (.abs bound body') := by
  induction hBody with
  | refl =>
    exact Relation.ReflTransGen.refl
  | @tail mid body' hStar hStep ih =>
    exact Relation.ReflTransGen.trans ih
      (MSub.to_star
        (msub_abs_fOp_body_fixed_bound hpvTail hBoundScoped hα hStep))

/-- Fixed-bound `FOp` abstraction cell for de Bruijn Lemma 2. A body-level
equivalence diamond under the operand `.equ` head lifts to the abstraction
level. -/
theorem diamond_abs_fOp_body_fixed_bound {Γ : Ctx} {s : Stack}
    {α bound body body₁ body₂ : Term}
    (hpvTail : PrevalidExt Γ s)
    (hBoundScoped : Term.Scoped Γ.depth bound)
    (hα : Term.Scoped Γ.depth α)
    (hdiamondBody : EqDiamonds ({ bound := α, kind := .equ } :: Γ)
      (Stack.shift 0 s))
    (hBody₁ : MEqRed ({ bound := α, kind := .equ } :: Γ)
      (Stack.shift 0 s) body body₁)
    (hBody₂ : MEqRed ({ bound := α, kind := .equ } :: Γ)
      (Stack.shift 0 s) body body₂) :
    ∃ t₃,
      MEqRedStar Γ (α :: s) (.abs bound body₁) t₃ ∧
        MEqRedStar Γ (α :: s) (.abs bound body₂) t₃ := by
  obtain ⟨body₃, hLeft, hRight⟩ := hdiamondBody hBody₁ hBody₂
  exact ⟨.abs bound body₃,
    meqRedStar_abs_fOp_body_fixed_bound hpvTail hBoundScoped hα
      (MEqRedStar.single hLeft.some),
    meqRedStar_abs_fOp_body_fixed_bound hpvTail hBoundScoped hα
      (MEqRedStar.single hRight.some)⟩

/-- Fixed-bound `FOp` abstraction cell with stack prevalidity and operand
scopedness recovered from the left abstraction equivalence step. -/
theorem diamond_abs_fOp_body_fixed_bound_from_left {Γ : Ctx} {s : Stack}
    {α bound body body₁ body₂ : Term}
    (hdiamondBody : EqDiamonds ({ bound := α, kind := .equ } :: Γ)
      (Stack.shift 0 s))
    (hLeft : MEqRed Γ (α :: s) (.abs bound body) (.abs bound body₁))
    (hBody₁ : MEqRed ({ bound := α, kind := .equ } :: Γ)
      (Stack.shift 0 s) body body₁)
    (hBody₂ : MEqRed ({ bound := α, kind := .equ } :: Γ)
      (Stack.shift 0 s) body body₂) :
    ∃ t₃,
      MEqRedStar Γ (α :: s) (.abs bound body₁) t₃ ∧
        MEqRedStar Γ (α :: s) (.abs bound body₂) t₃ := by
  exact diamond_abs_fOp_body_fixed_bound
    (PrevalidExt.tail hLeft.prevalidExt)
    (Term.Scoped.abs_inv hLeft.scoped_left).1
    (PrevalidExt.head_scoped hLeft.prevalidExt)
    hdiamondBody hBody₁ hBody₂

/-- Star-level fixed-bound `FOp` abstraction diamond. A body-level de Bruijn
Lemma-2 premise lifts to equivalence chains under the operand `.equ` head,
then through the abstraction. -/
noncomputable def diamond_abs_fOp_body_fixed_bound_star {Γ : Ctx} {s : Stack}
    {α bound body body₁ body₂ : Term}
    (hpvTail : PrevalidExt Γ s)
    (hBoundScoped : Term.Scoped Γ.depth bound)
    (hα : Term.Scoped Γ.depth α)
    (hdiamondBody : EqDiamonds ({ bound := α, kind := .equ } :: Γ)
      (Stack.shift 0 s))
    (hBody₁ : MEqRedStar ({ bound := α, kind := .equ } :: Γ)
      (Stack.shift 0 s) body body₁)
    (hBody₂ : MEqRedStar ({ bound := α, kind := .equ } :: Γ)
      (Stack.shift 0 s) body body₂) :
    ∃ t₃,
      MEqRedStar Γ (α :: s) (.abs bound body₁) t₃ ∧
        MEqRedStar Γ (α :: s) (.abs bound body₂) t₃ := by
  obtain ⟨body₃, hLeft, hRight⟩ :=
    diamond_eqStar_eqStar_of hdiamondBody hBody₁ hBody₂
  exact ⟨.abs bound body₃,
    meqRedStar_abs_fOp_body_fixed_bound hpvTail hBoundScoped hα hLeft,
    meqRedStar_abs_fOp_body_fixed_bound hpvTail hBoundScoped hα hRight⟩

/-- Fixed-bound `FOp` abstraction cell for de Bruijn Lemma 1. A body-level
strong-commutativity square under the operand `.equ` head lifts to the
abstraction level. -/
theorem commute_abs_fOp_body_fixed_bound {Γ : Ctx} {s : Stack}
    {α bound body body₁ body₂ : Term}
    (hpvTail : PrevalidExt Γ s)
    (hBoundScoped : Term.Scoped Γ.depth bound)
    (hα : Term.Scoped Γ.depth α)
    (hcommBody : StrongCommutes ({ bound := α, kind := .equ } :: Γ)
      (Stack.shift 0 s))
    (hSubBody : MSubRed ({ bound := α, kind := .equ } :: Γ)
      (Stack.shift 0 s) body body₁)
    (hEqBody : MEqRed ({ bound := α, kind := .equ } :: Γ)
      (Stack.shift 0 s) body body₂) :
    ∃ t₃,
      MEqRedStar Γ (α :: s) (.abs bound body₁) t₃ ∧
        MSubRedStar Γ (α :: s) (.abs bound body₂) t₃ := by
  obtain ⟨body₃, hLeft, hRight⟩ := hcommBody hSubBody hEqBody
  exact ⟨.abs bound body₃,
    meqRedStar_abs_fOp_body_fixed_bound hpvTail hBoundScoped hα
      (MEqRedStar.single hLeft.some),
    msubRedStar_abs_fOp_body_fixed_bound hBoundScoped hα
      (MSubRedStar.single hRight.some)⟩

/-- Fixed-bound `FOp` abstraction commutation with stack prevalidity and
operand scopedness recovered from the left abstraction subtype step. -/
theorem commute_abs_fOp_body_fixed_bound_from_left {Γ : Ctx} {s : Stack}
    {α bound body body₁ body₂ : Term}
    (hcommBody : StrongCommutes ({ bound := α, kind := .equ } :: Γ)
      (Stack.shift 0 s))
    (hLeft : MSubRed Γ (α :: s) (.abs bound body) (.abs bound body₁))
    (hSubBody : MSubRed ({ bound := α, kind := .equ } :: Γ)
      (Stack.shift 0 s) body body₁)
    (hEqBody : MEqRed ({ bound := α, kind := .equ } :: Γ)
      (Stack.shift 0 s) body body₂) :
    ∃ t₃,
      MEqRedStar Γ (α :: s) (.abs bound body₁) t₃ ∧
        MSubRedStar Γ (α :: s) (.abs bound body₂) t₃ := by
  exact commute_abs_fOp_body_fixed_bound
    (PrevalidExt.tail hLeft.prevalidExt)
    (Term.Scoped.abs_inv hLeft.scoped_left).1
    (PrevalidExt.head_scoped hLeft.prevalidExt)
    hcommBody hSubBody hEqBody

/-- Fixed-body `FOp` abstraction cell for de Bruijn Lemma 2. A bound-level
equivalence diamond lifts through `FOp` when the operand and body are
unchanged. -/
theorem diamond_abs_fOp_bound_fixed_body {Γ : Ctx} {s : Stack}
    {α bound bound₁ bound₂ body : Term}
    (hpvTail : PrevalidExt Γ s)
    (hα : Term.Scoped Γ.depth α)
    (hBodyScoped : Term.Scoped
      (Ctx.depth ({ bound := α, kind := .equ } :: Γ)) body)
    (hdiamondBound : EqDiamonds Γ [])
    (hBound₁ : MEqRed Γ [] bound bound₁)
    (hBound₂ : MEqRed Γ [] bound bound₂) :
    ∃ t₃,
      MEqRedStar Γ (α :: s) (.abs bound₁ body) t₃ ∧
        MEqRedStar Γ (α :: s) (.abs bound₂ body) t₃ := by
  obtain ⟨bound₃, hLeft, hRight⟩ := hdiamondBound hBound₁ hBound₂
  have hpvBody : PrevalidExt ({ bound := α, kind := .equ } :: Γ)
      (Stack.shift 0 s) :=
    PrevalidExt.weaken_head hpvTail (Prevalid.equ (PrevalidExt.ctx hpvTail) hα)
  have hBodyRefl : MEqRed ({ bound := α, kind := .equ } :: Γ)
      (Stack.shift 0 s) body body :=
    MEqRed.refl hpvBody hBodyScoped
  exact ⟨.abs bound₃ body,
    MEqRedStar.single (MEqRed.fOp hLeft.some hα hBodyRefl),
    MEqRedStar.single (MEqRed.fOp hRight.some hα hBodyRefl)⟩

/-- Fixed-body `FOp` abstraction cell with stack prevalidity, operand
scopedness, and body scopedness recovered from the left abstraction
equivalence step. -/
theorem diamond_abs_fOp_bound_fixed_body_from_left {Γ : Ctx} {s : Stack}
    {α bound bound₁ bound₂ body : Term}
    (hdiamondBound : EqDiamonds Γ [])
    (hLeft : MEqRed Γ (α :: s) (.abs bound body) (.abs bound₁ body))
    (hBound₁ : MEqRed Γ [] bound bound₁)
    (hBound₂ : MEqRed Γ [] bound bound₂) :
    ∃ t₃,
      MEqRedStar Γ (α :: s) (.abs bound₁ body) t₃ ∧
        MEqRedStar Γ (α :: s) (.abs bound₂ body) t₃ := by
  exact diamond_abs_fOp_bound_fixed_body
    (PrevalidExt.tail hLeft.prevalidExt)
    (PrevalidExt.head_scoped hLeft.prevalidExt)
    (by simpa [Ctx.depth] using (Term.Scoped.abs_inv hLeft.scoped_left).2)
    hdiamondBound hBound₁ hBound₂

/-- Lift a bound equivalence-reduction chain through `FOp` while keeping the
operand and body fixed. -/
theorem meqRedStar_abs_fOp_bound_fixed_body {Γ : Ctx} {s : Stack}
    {α bound bound' body : Term}
    (hpvTail : PrevalidExt Γ s)
    (hα : Term.Scoped Γ.depth α)
    (hBodyScoped : Term.Scoped
      (Ctx.depth ({ bound := α, kind := .equ } :: Γ)) body)
    (hBound : MEqRedStar Γ [] bound bound') :
    MEqRedStar Γ (α :: s) (.abs bound body) (.abs bound' body) := by
  have hpvBody : PrevalidExt ({ bound := α, kind := .equ } :: Γ)
      (Stack.shift 0 s) :=
    PrevalidExt.weaken_head hpvTail (Prevalid.equ (PrevalidExt.ctx hpvTail) hα)
  have hBodyRefl : MEqRed ({ bound := α, kind := .equ } :: Γ)
      (Stack.shift 0 s) body body :=
    MEqRed.refl hpvBody hBodyScoped
  induction hBound with
  | refl =>
      exact Relation.ReflTransGen.refl
  | @tail mid bound' hStar hStep ih =>
      exact Relation.ReflTransGen.trans ih
        (MEqRedStar.single (MEqRed.fOp hStep.some hα hBodyRefl))

/-- Star-level fixed-body `FOp` abstraction diamond. A bound-level
equivalence-chain diamond lifts through `FOp` when the operand and body are
unchanged. -/
noncomputable def diamond_abs_fOp_bound_fixed_body_star {Γ : Ctx} {s : Stack}
    {α bound bound₁ bound₂ body : Term}
    (hpvTail : PrevalidExt Γ s)
    (hα : Term.Scoped Γ.depth α)
    (hBodyScoped : Term.Scoped
      (Ctx.depth ({ bound := α, kind := .equ } :: Γ)) body)
    (hdiamondBound : EqDiamonds Γ [])
    (hBound₁ : MEqRedStar Γ [] bound bound₁)
    (hBound₂ : MEqRedStar Γ [] bound bound₂) :
    ∃ t₃,
      MEqRedStar Γ (α :: s) (.abs bound₁ body) t₃ ∧
        MEqRedStar Γ (α :: s) (.abs bound₂ body) t₃ := by
  obtain ⟨bound₃, hLeft, hRight⟩ :=
    diamond_eqStar_eqStar_of hdiamondBound hBound₁ hBound₂
  exact ⟨.abs bound₃ body,
    meqRedStar_abs_fOp_bound_fixed_body hpvTail hα hBodyScoped hLeft,
    meqRedStar_abs_fOp_bound_fixed_body hpvTail hα hBodyScoped hRight⟩

/-- Fixed-body `FOp` abstraction cell for de Bruijn Lemma 1's `Ms-FOp ×
Me-FOp` branch when the subtype-side body is unchanged. The equivalence side's
bound step supplies the shared target directly. -/
theorem commute_abs_fOp_bound_fixed_body {Γ : Ctx} {s : Stack}
    {α bound bound₂ body : Term}
    (hpvTail : PrevalidExt Γ s)
    (hα : Term.Scoped Γ.depth α)
    (hBodyScoped : Term.Scoped
      (Ctx.depth ({ bound := α, kind := .equ } :: Γ)) body)
    (hEqBound : MEqRed Γ [] bound bound₂) :
    ∃ t₃,
      MEqRedStar Γ (α :: s) (.abs bound body) t₃ ∧
        MSubRedStar Γ (α :: s) (.abs bound₂ body) t₃ := by
  have hpvBody : PrevalidExt ({ bound := α, kind := .equ } :: Γ)
      (Stack.shift 0 s) :=
    PrevalidExt.weaken_head hpvTail (Prevalid.equ (PrevalidExt.ctx hpvTail) hα)
  have hBodyEqRefl : MEqRed ({ bound := α, kind := .equ } :: Γ)
      (Stack.shift 0 s) body body :=
    MEqRed.refl hpvBody hBodyScoped
  have hBodySubRefl : MSubRed ({ bound := α, kind := .equ } :: Γ)
      (Stack.shift 0 s) body body :=
    MSubRed.refl hpvBody hBodyScoped
  exact ⟨.abs bound₂ body,
    MEqRedStar.single (MEqRed.fOp hEqBound hα hBodyEqRefl),
    MSubRedStar.single (MSubRed.fOp hEqBound.scoped_right hα hBodySubRefl)⟩

/-- Fixed-body `FOp` abstraction commutation with stack prevalidity, operand
scopedness, and body scopedness recovered from the left abstraction subtype
step. -/
theorem commute_abs_fOp_bound_fixed_body_from_left {Γ : Ctx} {s : Stack}
    {α bound bound₂ body : Term}
    (hLeft : MSubRed Γ (α :: s) (.abs bound body) (.abs bound body))
    (hEqBound : MEqRed Γ [] bound bound₂) :
    ∃ t₃,
      MEqRedStar Γ (α :: s) (.abs bound body) t₃ ∧
        MSubRedStar Γ (α :: s) (.abs bound₂ body) t₃ := by
  exact commute_abs_fOp_bound_fixed_body
    (PrevalidExt.tail hLeft.prevalidExt)
    (PrevalidExt.head_scoped hLeft.prevalidExt)
    (by simpa [Ctx.depth] using (Term.Scoped.abs_inv hLeft.scoped_left).2)
    hEqBound

/-- Lift a diagrammatic body replacement chain through `FOp` after first
changing the abstraction bound by an empty-stack equivalence step. -/
theorem msubStar_abs_fOp_equ_bound_body {Γ : Ctx} {s : Stack}
    {α bound bound' body body' : Term}
    (hpvTail : PrevalidExt Γ s)
    (hBound : MEqRed Γ [] bound bound')
    (hα : Term.Scoped Γ.depth α)
    (hBodyScoped : Term.Scoped (Ctx.depth ({ bound := α, kind := .equ } :: Γ)) body)
    (hBody : MSubStar ({ bound := α, kind := .equ } :: Γ)
      (Stack.shift 0 s) body body') :
    MSubStar Γ (α :: s) (.abs bound body) (.abs bound' body') := by
  have hpvBodyCtx : Prevalid ({ bound := α, kind := .equ } :: Γ) :=
    Prevalid.equ (PrevalidExt.ctx hpvTail) hα
  have hpvBody : PrevalidExt ({ bound := α, kind := .equ } :: Γ)
      (Stack.shift 0 s) :=
    PrevalidExt.weaken_head hpvTail hpvBodyCtx
  have hBodyRefl : MEqRed ({ bound := α, kind := .equ } :: Γ)
      (Stack.shift 0 s) body body :=
    MEqRed.refl hpvBody hBodyScoped
  exact MSubStar.trans
    (MSub.to_star (MSub.of_MEqRed (PrevalidExt.cons hpvTail hα)
      (MEqRed.fOp hBound hα hBodyRefl)))
    (msubStar_abs_fOp_body_fixed_bound hpvTail hBound.scoped_right hα hBody)

/-- Lift an empty-stack body subtype-reduction chain under a `.sub` head into
an abstraction subtype-reduction chain through `Fun`, keeping the abstraction
bound fixed. -/
theorem msubRedStar_abs_fun_body_fixed_bound {Γ : Ctx}
    {bound body body' : Term}
    (hpvNil : PrevalidExt Γ [])
    (hBoundScoped : Term.Scoped Γ.depth bound)
    (hBody : MSubRedStar ({ bound := bound, kind := .sub } :: Γ) []
      body body') :
    MSubRedStar Γ [] (.abs bound body) (.abs bound body') := by
  have hBoundRefl : MEqRed Γ [] bound bound :=
    MEqRed.refl hpvNil hBoundScoped
  induction hBody with
  | refl =>
    exact Relation.ReflTransGen.refl
  | @tail mid body' hStar hStep ih =>
    exact Relation.ReflTransGen.trans ih
      (MSubRedStar.single (MSubRed.fun_ hBoundScoped hBoundRefl hStep.some))

/-- Lift an empty-stack body equivalence-reduction chain under a `.sub` head
into an abstraction equivalence-reduction chain through `Fun`, keeping the
abstraction bound fixed. -/
theorem meqRedStar_abs_fun_body_fixed_bound {Γ : Ctx}
    {bound body body' : Term}
    (hpvNil : PrevalidExt Γ [])
    (hBoundScoped : Term.Scoped Γ.depth bound)
    (hBody : MEqRedStar ({ bound := bound, kind := .sub } :: Γ) []
      body body') :
    MEqRedStar Γ [] (.abs bound body) (.abs bound body') := by
  have hBoundRefl : MEqRed Γ [] bound bound :=
    MEqRed.refl hpvNil hBoundScoped
  induction hBody with
  | refl =>
    exact Relation.ReflTransGen.refl
  | @tail mid body' hStar hStep ih =>
    exact Relation.ReflTransGen.trans ih
      (MEqRedStar.single (MEqRed.fun_ hBoundRefl hStep.some))

/-- Lift a diagrammatic body subtyping step under a `.sub` head into an
abstraction subtyping step through `Fun`, keeping the abstraction bound
fixed. -/
theorem msub_abs_fun_body_fixed_bound {Γ : Ctx}
    {bound body body' : Term}
    (hpvNil : PrevalidExt Γ [])
    (hBoundScoped : Term.Scoped Γ.depth bound)
    (hBody : MSub ({ bound := bound, kind := .sub } :: Γ) [] body body') :
    MSub Γ [] (.abs bound body) (.abs bound body') := by
  obtain ⟨joinBody, hSubBody, hEqBody⟩ := hBody
  exact MSub.intro
    (msubRedStar_abs_fun_body_fixed_bound hpvNil hBoundScoped hSubBody)
    (meqRedStar_abs_fun_body_fixed_bound hpvNil hBoundScoped hEqBody)

/-- Lift a diagrammatic body subtyping chain under a `.sub` head into an
abstraction subtyping chain through `Fun`, keeping the abstraction bound
fixed. -/
theorem msubStar_abs_fun_body_fixed_bound {Γ : Ctx}
    {bound body body' : Term}
    (hpvNil : PrevalidExt Γ [])
    (hBoundScoped : Term.Scoped Γ.depth bound)
    (hBody : MSubStar ({ bound := bound, kind := .sub } :: Γ) [] body body') :
    MSubStar Γ [] (.abs bound body) (.abs bound body') := by
  induction hBody with
  | refl =>
    exact Relation.ReflTransGen.refl
  | @tail mid body' hStar hStep ih =>
    exact Relation.ReflTransGen.trans ih
      (MSub.to_star (msub_abs_fun_body_fixed_bound hpvNil hBoundScoped hStep))

/-- Fixed-bound `Fun` abstraction cell for de Bruijn Lemma 2. A body-level
equivalence diamond under the `.sub` head lifts to the abstraction level. -/
theorem diamond_abs_fun_body_fixed_bound {Γ : Ctx}
    {bound body body₁ body₂ : Term}
    (hpvNil : PrevalidExt Γ [])
    (hBoundScoped : Term.Scoped Γ.depth bound)
    (hdiamondBody : EqDiamonds ({ bound := bound, kind := .sub } :: Γ) [])
    (hBody₁ : MEqRed ({ bound := bound, kind := .sub } :: Γ) [] body body₁)
    (hBody₂ : MEqRed ({ bound := bound, kind := .sub } :: Γ) [] body body₂) :
    ∃ t₃,
      MEqRedStar Γ [] (.abs bound body₁) t₃ ∧
        MEqRedStar Γ [] (.abs bound body₂) t₃ := by
  obtain ⟨body₃, hLeft, hRight⟩ := hdiamondBody hBody₁ hBody₂
  exact ⟨.abs bound body₃,
    meqRedStar_abs_fun_body_fixed_bound hpvNil hBoundScoped
      (MEqRedStar.single hLeft.some),
    meqRedStar_abs_fun_body_fixed_bound hpvNil hBoundScoped
      (MEqRedStar.single hRight.some)⟩

/-- Fixed-bound `Fun` abstraction cell with empty-stack prevalidity and bound
scopedness recovered from the left abstraction equivalence step. -/
theorem diamond_abs_fun_body_fixed_bound_from_left {Γ : Ctx}
    {bound body body₁ body₂ : Term}
    (hdiamondBody : EqDiamonds ({ bound := bound, kind := .sub } :: Γ) [])
    (hLeft : MEqRed Γ [] (.abs bound body) (.abs bound body₁))
    (hBody₁ : MEqRed ({ bound := bound, kind := .sub } :: Γ) [] body body₁)
    (hBody₂ : MEqRed ({ bound := bound, kind := .sub } :: Γ) [] body body₂) :
    ∃ t₃,
      MEqRedStar Γ [] (.abs bound body₁) t₃ ∧
        MEqRedStar Γ [] (.abs bound body₂) t₃ := by
  exact diamond_abs_fun_body_fixed_bound hLeft.prevalidExt
    (Term.Scoped.abs_inv hLeft.scoped_left).1 hdiamondBody hBody₁ hBody₂

/-- Star-level fixed-bound `Fun` abstraction diamond. A body-level de Bruijn
Lemma-2 premise lifts to equivalence chains under the `.sub` head, then
through the abstraction. -/
noncomputable def diamond_abs_fun_body_fixed_bound_star {Γ : Ctx}
    {bound body body₁ body₂ : Term}
    (hpvNil : PrevalidExt Γ [])
    (hBoundScoped : Term.Scoped Γ.depth bound)
    (hdiamondBody : EqDiamonds ({ bound := bound, kind := .sub } :: Γ) [])
    (hBody₁ : MEqRedStar ({ bound := bound, kind := .sub } :: Γ) [] body body₁)
    (hBody₂ : MEqRedStar ({ bound := bound, kind := .sub } :: Γ) [] body body₂) :
    ∃ t₃,
      MEqRedStar Γ [] (.abs bound body₁) t₃ ∧
        MEqRedStar Γ [] (.abs bound body₂) t₃ := by
  obtain ⟨body₃, hLeft, hRight⟩ :=
    diamond_eqStar_eqStar_of hdiamondBody hBody₁ hBody₂
  exact ⟨.abs bound body₃,
    meqRedStar_abs_fun_body_fixed_bound hpvNil hBoundScoped hLeft,
    meqRedStar_abs_fun_body_fixed_bound hpvNil hBoundScoped hRight⟩

/-- Fixed-bound `Fun` abstraction cell for de Bruijn Lemma 1. A body-level
strong-commutativity square under the `.sub` head lifts to the abstraction
level. -/
theorem commute_abs_fun_body_fixed_bound {Γ : Ctx}
    {bound body body₁ body₂ : Term}
    (hpvNil : PrevalidExt Γ [])
    (hBoundScoped : Term.Scoped Γ.depth bound)
    (hcommBody : StrongCommutes ({ bound := bound, kind := .sub } :: Γ) [])
    (hSubBody : MSubRed ({ bound := bound, kind := .sub } :: Γ) [] body body₁)
    (hEqBody : MEqRed ({ bound := bound, kind := .sub } :: Γ) [] body body₂) :
    ∃ t₃,
      MEqRedStar Γ [] (.abs bound body₁) t₃ ∧
        MSubRedStar Γ [] (.abs bound body₂) t₃ := by
  obtain ⟨body₃, hLeft, hRight⟩ := hcommBody hSubBody hEqBody
  exact ⟨.abs bound body₃,
    meqRedStar_abs_fun_body_fixed_bound hpvNil hBoundScoped
      (MEqRedStar.single hLeft.some),
    msubRedStar_abs_fun_body_fixed_bound hpvNil hBoundScoped
      (MSubRedStar.single hRight.some)⟩

/-- Fixed-bound `Fun` abstraction commutation with empty-stack prevalidity and
bound scopedness recovered from the left abstraction subtype step. -/
theorem commute_abs_fun_body_fixed_bound_from_left {Γ : Ctx}
    {bound body body₁ body₂ : Term}
    (hcommBody : StrongCommutes ({ bound := bound, kind := .sub } :: Γ) [])
    (hLeft : MSubRed Γ [] (.abs bound body) (.abs bound body₁))
    (hSubBody : MSubRed ({ bound := bound, kind := .sub } :: Γ) [] body body₁)
    (hEqBody : MEqRed ({ bound := bound, kind := .sub } :: Γ) [] body body₂) :
    ∃ t₃,
      MEqRedStar Γ [] (.abs bound body₁) t₃ ∧
        MSubRedStar Γ [] (.abs bound body₂) t₃ := by
  exact commute_abs_fun_body_fixed_bound hLeft.prevalidExt
    (Term.Scoped.abs_inv hLeft.scoped_left).1 hcommBody hSubBody hEqBody

/-- Fixed-body `Fun` abstraction cell for de Bruijn Lemma 2. A bound-level
equivalence diamond lifts to abstractions when the body is unchanged. -/
theorem diamond_abs_fun_bound_fixed_body {Γ : Ctx}
    {bound bound₁ bound₂ body : Term}
    (hpvNil : PrevalidExt Γ [])
    (hBodyScoped : Term.Scoped (Ctx.depth ({ bound := bound, kind := .sub } :: Γ)) body)
    (hdiamondBound : EqDiamonds Γ [])
    (hBound₁ : MEqRed Γ [] bound bound₁)
    (hBound₂ : MEqRed Γ [] bound bound₂) :
    ∃ t₃,
      MEqRedStar Γ [] (.abs bound₁ body) t₃ ∧
        MEqRedStar Γ [] (.abs bound₂ body) t₃ := by
  obtain ⟨bound₃, hLeft, hRight⟩ := hdiamondBound hBound₁ hBound₂
  have hpvBody₁ : PrevalidExt ({ bound := bound₁, kind := .sub } :: Γ) [] :=
    PrevalidExt.nil (Prevalid.sub (PrevalidExt.ctx hpvNil) hBound₁.scoped_right)
  have hpvBody₂ : PrevalidExt ({ bound := bound₂, kind := .sub } :: Γ) [] :=
    PrevalidExt.nil (Prevalid.sub (PrevalidExt.ctx hpvNil) hBound₂.scoped_right)
  have hBody₁ : MEqRed ({ bound := bound₁, kind := .sub } :: Γ) [] body body :=
    MEqRed.refl hpvBody₁ hBodyScoped
  have hBody₂ : MEqRed ({ bound := bound₂, kind := .sub } :: Γ) [] body body :=
    MEqRed.refl hpvBody₂ hBodyScoped
  exact ⟨.abs bound₃ body,
    MEqRedStar.single (MEqRed.fun_ hLeft.some hBody₁),
    MEqRedStar.single (MEqRed.fun_ hRight.some hBody₂)⟩

/-- Fixed-body `Fun` abstraction cell with empty-stack prevalidity and body
scopedness recovered from the left abstraction equivalence step. -/
theorem diamond_abs_fun_bound_fixed_body_from_left {Γ : Ctx}
    {bound bound₁ bound₂ body : Term}
    (hdiamondBound : EqDiamonds Γ [])
    (hLeft : MEqRed Γ [] (.abs bound body) (.abs bound₁ body))
    (hBound₁ : MEqRed Γ [] bound bound₁)
    (hBound₂ : MEqRed Γ [] bound bound₂) :
    ∃ t₃,
      MEqRedStar Γ [] (.abs bound₁ body) t₃ ∧
        MEqRedStar Γ [] (.abs bound₂ body) t₃ := by
  exact diamond_abs_fun_bound_fixed_body hLeft.prevalidExt
    (by simpa [Ctx.depth] using (Term.Scoped.abs_inv hLeft.scoped_left).2)
    hdiamondBound hBound₁ hBound₂

/-- Lift a bound equivalence-reduction chain through `Fun` while keeping the
body fixed. -/
theorem meqRedStar_abs_fun_bound_fixed_body {Γ : Ctx}
    {bound bound' body : Term}
    (hpvNil : PrevalidExt Γ [])
    (hBodyScoped : Term.Scoped (Ctx.depth ({ bound := bound, kind := .sub } :: Γ)) body)
    (hBound : MEqRedStar Γ [] bound bound') :
    MEqRedStar Γ [] (.abs bound body) (.abs bound' body) := by
  induction hBound with
  | refl =>
      exact Relation.ReflTransGen.refl
  | @tail mid bound' hStar hStep ih =>
      have hpvBody : PrevalidExt ({ bound := mid, kind := .sub } :: Γ) [] :=
        PrevalidExt.nil (Prevalid.sub (PrevalidExt.ctx hpvNil) hStep.some.scoped_left)
      have hBodyRefl : MEqRed ({ bound := mid, kind := .sub } :: Γ) [] body body :=
        MEqRed.refl hpvBody hBodyScoped
      exact Relation.ReflTransGen.trans ih
        (MEqRedStar.single (MEqRed.fun_ hStep.some hBodyRefl))

/-- Lift a bound equivalence-reduction chain through `Fun` as a subtype chain
while keeping the body fixed. -/
theorem msubRedStar_abs_fun_bound_fixed_body {Γ : Ctx}
    {bound bound' body : Term}
    (hpvNil : PrevalidExt Γ [])
    (hBodyScoped : Term.Scoped (Ctx.depth ({ bound := bound, kind := .sub } :: Γ)) body)
    (hBound : MEqRedStar Γ [] bound bound') :
    MSubRedStar Γ [] (.abs bound body) (.abs bound' body) := by
  induction hBound with
  | refl =>
      exact Relation.ReflTransGen.refl
  | @tail mid bound' hStar hStep ih =>
      have hpvBody : PrevalidExt ({ bound := mid, kind := .sub } :: Γ) [] :=
        PrevalidExt.nil (Prevalid.sub (PrevalidExt.ctx hpvNil) hStep.some.scoped_left)
      have hBodyRefl : MSubRed ({ bound := mid, kind := .sub } :: Γ) [] body body :=
        MSubRed.refl hpvBody hBodyScoped
      exact Relation.ReflTransGen.trans ih
        (MSubRedStar.single
          (MSubRed.fun_ hStep.some.scoped_left hStep.some hBodyRefl))

/-- Star-level fixed-body `Fun` abstraction diamond. A bound-level
equivalence-chain diamond lifts through `Fun` when the body is unchanged. -/
noncomputable def diamond_abs_fun_bound_fixed_body_star {Γ : Ctx}
    {bound bound₁ bound₂ body : Term}
    (hpvNil : PrevalidExt Γ [])
    (hBodyScoped : Term.Scoped (Ctx.depth ({ bound := bound, kind := .sub } :: Γ)) body)
    (hdiamondBound : EqDiamonds Γ [])
    (hBound₁ : MEqRedStar Γ [] bound bound₁)
    (hBound₂ : MEqRedStar Γ [] bound bound₂) :
    ∃ t₃,
      MEqRedStar Γ [] (.abs bound₁ body) t₃ ∧
        MEqRedStar Γ [] (.abs bound₂ body) t₃ := by
  obtain ⟨bound₃, hLeft, hRight⟩ :=
    diamond_eqStar_eqStar_of hdiamondBound hBound₁ hBound₂
  exact ⟨.abs bound₃ body,
    meqRedStar_abs_fun_bound_fixed_body hpvNil hBodyScoped hLeft,
    meqRedStar_abs_fun_bound_fixed_body hpvNil hBodyScoped hRight⟩

/-- Fixed-body `Fun` abstraction cell for de Bruijn Lemma 1's `Ms-Fun ×
Me-Fun` branch. The subtype constructor's bound premise is itself an
equivalence step, so a bound-level equivalence diamond supplies the shared
bound target. -/
theorem commute_abs_fun_bound_fixed_body {Γ : Ctx}
    {bound bound₁ bound₂ body : Term}
    (hpvNil : PrevalidExt Γ [])
    (hBodyScoped : Term.Scoped (Ctx.depth ({ bound := bound, kind := .sub } :: Γ)) body)
    (hdiamondBound : EqDiamonds Γ [])
    (hSubBound : MEqRed Γ [] bound bound₁)
    (hEqBound : MEqRed Γ [] bound bound₂) :
    ∃ t₃,
      MEqRedStar Γ [] (.abs bound₁ body) t₃ ∧
        MSubRedStar Γ [] (.abs bound₂ body) t₃ := by
  obtain ⟨bound₃, hLeft, hRight⟩ := hdiamondBound hSubBound hEqBound
  have hpvBody₁ : PrevalidExt ({ bound := bound₁, kind := .sub } :: Γ) [] :=
    PrevalidExt.nil (Prevalid.sub (PrevalidExt.ctx hpvNil) hSubBound.scoped_right)
  have hpvBody₂ : PrevalidExt ({ bound := bound₂, kind := .sub } :: Γ) [] :=
    PrevalidExt.nil (Prevalid.sub (PrevalidExt.ctx hpvNil) hEqBound.scoped_right)
  have hBody₁ : MEqRed ({ bound := bound₁, kind := .sub } :: Γ) [] body body :=
    MEqRed.refl hpvBody₁ hBodyScoped
  have hBody₂ : MSubRed ({ bound := bound₂, kind := .sub } :: Γ) [] body body :=
    MSubRed.refl hpvBody₂ hBodyScoped
  exact ⟨.abs bound₃ body,
    MEqRedStar.single (MEqRed.fun_ hLeft.some hBody₁),
    MSubRedStar.single (MSubRed.fun_ hEqBound.scoped_right hRight.some hBody₂)⟩

/-- Fixed-body `Fun` abstraction commutation with empty-stack prevalidity and
body scopedness recovered from the left abstraction subtype step. -/
theorem commute_abs_fun_bound_fixed_body_from_left {Γ : Ctx}
    {bound bound₁ bound₂ body : Term}
    (hdiamondBound : EqDiamonds Γ [])
    (hLeft : MSubRed Γ [] (.abs bound body) (.abs bound₁ body))
    (hSubBound : MEqRed Γ [] bound bound₁)
    (hEqBound : MEqRed Γ [] bound bound₂) :
    ∃ t₃,
      MEqRedStar Γ [] (.abs bound₁ body) t₃ ∧
        MSubRedStar Γ [] (.abs bound₂ body) t₃ := by
  exact commute_abs_fun_bound_fixed_body hLeft.prevalidExt
    (by simpa [Ctx.depth] using (Term.Scoped.abs_inv hLeft.scoped_left).2)
    hdiamondBound hSubBound hEqBound

/-- Lift a diagrammatic body replacement chain through `Fun` after first
changing the abstraction bound by an empty-stack equivalence step. -/
theorem msubStar_abs_fun_equ_bound_body {Γ : Ctx}
    {bound bound' body body' : Term}
    (hpvNil : PrevalidExt Γ [])
    (hBound : MEqRed Γ [] bound bound')
    (hBodyScoped : Term.Scoped (Ctx.depth ({ bound := bound, kind := .sub } :: Γ)) body)
    (hBody : MSubStar ({ bound := bound', kind := .sub } :: Γ) [] body body') :
    MSubStar Γ [] (.abs bound body) (.abs bound' body') := by
  have hpvBodyCtx : Prevalid ({ bound := bound, kind := .sub } :: Γ) :=
    Prevalid.sub (PrevalidExt.ctx hpvNil) hBound.scoped_left
  have hpvBody : PrevalidExt ({ bound := bound, kind := .sub } :: Γ) [] :=
    PrevalidExt.nil hpvBodyCtx
  have hBodyRefl : MEqRed ({ bound := bound, kind := .sub } :: Γ) [] body body :=
    MEqRed.refl hpvBody hBodyScoped
  exact MSubStar.trans
    (MSub.to_star (MSub.of_MEqRed hpvNil (MEqRed.fun_ hBound hBodyRefl)))
    (msubStar_abs_fun_body_fixed_bound hpvNil hBound.scoped_right hBody)

/-- One-step subtype replacement splitter for an innermost changed `.equ`
head. Stable leaves are discharged immediately; constructor cases whose
subderivations must be recursively replaced are exposed as explicit handlers.
-/
theorem msubRed_equ_head_replace_from_handlers {Γ : Ctx} {s : Stack}
    {old new u v : Term}
    (hpv : PrevalidExt ({ bound := old, kind := .equ } :: Γ) s)
    (hnew : Term.Scoped Γ.depth new)
    (hEq :
      ∀ {u v : Term},
        MEqRed ({ bound := old, kind := .equ } :: Γ) s u v →
        MSubStar ({ bound := new, kind := .equ } :: Γ) s u v)
    (hApp :
      ∀ {op op' arg : Term},
        MSubRed ({ bound := old, kind := .equ } :: Γ) (arg :: s) op op' →
        Term.Scoped (Ctx.depth ({ bound := old, kind := .equ } :: Γ)) arg →
        MSubStar ({ bound := new, kind := .equ } :: Γ) s
          (.app op arg) (.app op' arg))
    (hFun :
      ∀ {bound bound' body body' : Term},
        Term.Scoped (Ctx.depth ({ bound := old, kind := .equ } :: Γ)) bound →
        MEqRed ({ bound := old, kind := .equ } :: Γ) [] bound bound' →
        MSubRed ({ bound := bound, kind := .sub } ::
          { bound := old, kind := .equ } :: Γ) [] body body' →
        MSubStar ({ bound := new, kind := .equ } :: Γ) []
          (.abs bound body) (.abs bound' body'))
    (hFOp :
      ∀ {bound arg body body' : Term} {rest : Stack},
        Term.Scoped (Ctx.depth ({ bound := old, kind := .equ } :: Γ)) bound →
        Term.Scoped (Ctx.depth ({ bound := old, kind := .equ } :: Γ)) arg →
        s = arg :: rest →
        MSubRed ({ bound := arg, kind := .equ } ::
          { bound := old, kind := .equ } :: Γ) (Stack.shift 0 rest) body body' →
        MSubStar ({ bound := new, kind := .equ } :: Γ) s
          (.abs bound body) (.abs bound body'))
    (h : MSubRed ({ bound := old, kind := .equ } :: Γ) s u v) :
    MSubStar ({ bound := new, kind := .equ } :: Γ) s u v := by
  cases h with
  | pro _ hb =>
    exact MSubStar.of_MSubRed (MSubRed.pro_equ_head_replace hpv hnew hb)
  | top _ hu =>
    exact MSubStar.of_MSubRed (MSubRed.top_equ_head_replace hpv hnew hu)
  | equ _ heq =>
    exact hEq heq
  | app hOp hArg =>
    exact hApp hOp hArg
  | fun_ ht hBound hBody =>
    exact hFun ht hBound hBody
  | fOp ht hArg hBody =>
    exact hFOp ht hArg rfl hBody

/-- One-step subtype replacement splitter when the changed `.equ` entry sits
immediately under a preserved head. This is the shape reached by recursive
replacement inside binder bodies. -/
theorem msubRed_equ_under_head_replace_from_handlers {Γ : Ctx} {s : Stack}
    {head : CtxEntry} {old new u v : Term}
    (hpv : PrevalidExt (head :: { bound := old, kind := .equ } :: Γ) s)
    (hnew : Term.Scoped Γ.depth new)
    (hEq :
      ∀ {u v : Term},
        MEqRed (head :: { bound := old, kind := .equ } :: Γ) s u v →
        MSubStar (head :: { bound := new, kind := .equ } :: Γ) s u v)
    (hApp :
      ∀ {op op' arg : Term},
        MSubRed (head :: { bound := old, kind := .equ } :: Γ) (arg :: s) op op' →
        Term.Scoped (Ctx.depth (head :: { bound := old, kind := .equ } :: Γ)) arg →
        MSubStar (head :: { bound := new, kind := .equ } :: Γ) s
          (.app op arg) (.app op' arg))
    (hFun :
      ∀ {bound bound' body body' : Term},
        Term.Scoped (Ctx.depth (head :: { bound := old, kind := .equ } :: Γ)) bound →
        MEqRed (head :: { bound := old, kind := .equ } :: Γ) [] bound bound' →
        MSubRed ({ bound := bound, kind := .sub } :: head ::
          { bound := old, kind := .equ } :: Γ) [] body body' →
        MSubStar (head :: { bound := new, kind := .equ } :: Γ) []
          (.abs bound body) (.abs bound' body'))
    (hFOp :
      ∀ {bound arg body body' : Term} {rest : Stack},
        Term.Scoped (Ctx.depth (head :: { bound := old, kind := .equ } :: Γ)) bound →
        Term.Scoped (Ctx.depth (head :: { bound := old, kind := .equ } :: Γ)) arg →
        s = arg :: rest →
        MSubRed ({ bound := arg, kind := .equ } :: head ::
          { bound := old, kind := .equ } :: Γ) (Stack.shift 0 rest) body body' →
        MSubStar (head :: { bound := new, kind := .equ } :: Γ) s
          (.abs bound body) (.abs bound body'))
    (h : MSubRed (head :: { bound := old, kind := .equ } :: Γ) s u v) :
    MSubStar (head :: { bound := new, kind := .equ } :: Γ) s u v := by
  cases h with
  | pro _ hb =>
    exact MSubStar.of_MSubRed (MSubRed.pro_equ_under_head_replace hpv hnew hb)
  | top _ hu =>
    exact MSubStar.of_MSubRed (MSubRed.top_equ_under_head_replace hpv hnew hu)
  | equ _ heq =>
    exact hEq heq
  | app hOp hArg =>
    exact hApp hOp hArg
  | fun_ ht hBound hBody =>
    exact hFun ht hBound hBody
  | fOp ht hArg hBody =>
    exact hFOp ht hArg rfl hBody

/-- Canonical `Ms-App` handler for innermost `.equ` replacement: recursively
replace the operator at the extended argument stack, then lift the resulting
diagrammatic chain through application with the fixed argument. -/
theorem msub_equ_head_app_handler_of_operator_replacement {Γ : Ctx} {s : Stack}
    {old new : Term}
    (hpv : PrevalidExt ({ bound := old, kind := .equ } :: Γ) s)
    (hnew : Term.Scoped Γ.depth new)
    (hOpReplace :
      ∀ {op op' arg : Term},
        MSubRed ({ bound := old, kind := .equ } :: Γ) (arg :: s) op op' →
        Term.Scoped (Ctx.depth ({ bound := old, kind := .equ } :: Γ)) arg →
        MSubStar ({ bound := new, kind := .equ } :: Γ) (arg :: s) op op')
    {op op' arg : Term}
    (hOp : MSubRed ({ bound := old, kind := .equ } :: Γ) (arg :: s) op op')
    (hArgScoped : Term.Scoped (Ctx.depth ({ bound := old, kind := .equ } :: Γ)) arg) :
    MSubStar ({ bound := new, kind := .equ } :: Γ) s
      (.app op arg) (.app op' arg) :=
  msubStar_app_fixed_arg (PrevalidExt.equ_head_replace hpv hnew) hArgScoped
    (hOpReplace hOp hArgScoped)

/-- Canonical `Ms-App` handler for under-head `.equ` replacement. -/
theorem msub_equ_under_head_app_handler_of_operator_replacement {Γ : Ctx}
    {s : Stack} {head : CtxEntry} {old new : Term}
    (hpv : PrevalidExt (head :: { bound := old, kind := .equ } :: Γ) s)
    (hnew : Term.Scoped Γ.depth new)
    (hOpReplace :
      ∀ {op op' arg : Term},
        MSubRed (head :: { bound := old, kind := .equ } :: Γ) (arg :: s) op op' →
        Term.Scoped (Ctx.depth (head :: { bound := old, kind := .equ } :: Γ)) arg →
        MSubStar (head :: { bound := new, kind := .equ } :: Γ) (arg :: s) op op')
    {op op' arg : Term}
    (hOp : MSubRed (head :: { bound := old, kind := .equ } :: Γ) (arg :: s) op op')
    (hArgScoped : Term.Scoped (Ctx.depth (head :: { bound := old, kind := .equ } :: Γ)) arg) :
    MSubStar (head :: { bound := new, kind := .equ } :: Γ) s
      (.app op arg) (.app op' arg) :=
  msubStar_app_fixed_arg (PrevalidExt.equ_under_head_replace hpv hnew) hArgScoped
    (hOpReplace hOp hArgScoped)

/-- Canonical `Ms-Fun` handler for innermost `.equ` replacement when the
bound equivalence and body subtype premises have already been replaced as raw
one-step reductions. -/
theorem msub_equ_head_fun_handler_of_raw_replacements {Γ : Ctx}
    {old new : Term}
    (hBoundReplace :
      ∀ {bound bound' : Term},
        MEqRed ({ bound := old, kind := .equ } :: Γ) [] bound bound' →
        MEqRed ({ bound := new, kind := .equ } :: Γ) [] bound bound')
    (hBodyReplace :
      ∀ {bound body body' : Term},
        MSubRed ({ bound := bound, kind := .sub } ::
          { bound := old, kind := .equ } :: Γ) [] body body' →
        MSubRed ({ bound := bound, kind := .sub } ::
          { bound := new, kind := .equ } :: Γ) [] body body')
    {bound bound' body body' : Term}
    (hBoundScoped : Term.Scoped (Ctx.depth ({ bound := old, kind := .equ } :: Γ)) bound)
    (hBound : MEqRed ({ bound := old, kind := .equ } :: Γ) [] bound bound')
    (hBody : MSubRed ({ bound := bound, kind := .sub } ::
      { bound := old, kind := .equ } :: Γ) [] body body') :
    MSubStar ({ bound := new, kind := .equ } :: Γ) []
      (.abs bound body) (.abs bound' body') :=
  MSubStar.of_MSubRed
    (MSubRed.fun_equ_head_replace hBoundScoped (hBoundReplace hBound)
      (hBodyReplace hBody))

/-- Canonical `Ms-Fun` handler for under-head `.equ` replacement when the
bound equivalence and body subtype premises have already been replaced as raw
one-step reductions. -/
theorem msub_equ_under_head_fun_handler_of_raw_replacements {Γ : Ctx}
    {head : CtxEntry} {old new : Term}
    (hBoundReplace :
      ∀ {bound bound' : Term},
        MEqRed (head :: { bound := old, kind := .equ } :: Γ) [] bound bound' →
        MEqRed (head :: { bound := new, kind := .equ } :: Γ) [] bound bound')
    (hBodyReplace :
      ∀ {bound body body' : Term},
        MSubRed ({ bound := bound, kind := .sub } :: head ::
          { bound := old, kind := .equ } :: Γ) [] body body' →
        MSubRed ({ bound := bound, kind := .sub } :: head ::
          { bound := new, kind := .equ } :: Γ) [] body body')
    {bound bound' body body' : Term}
    (hBoundScoped : Term.Scoped (Ctx.depth (head :: { bound := old, kind := .equ } :: Γ)) bound)
    (hBound : MEqRed (head :: { bound := old, kind := .equ } :: Γ) [] bound bound')
    (hBody : MSubRed ({ bound := bound, kind := .sub } :: head ::
      { bound := old, kind := .equ } :: Γ) [] body body') :
    MSubStar (head :: { bound := new, kind := .equ } :: Γ) []
      (.abs bound body) (.abs bound' body') :=
  MSubStar.of_MSubRed
    (MSubRed.fun_equ_under_head_replace hBoundScoped (hBoundReplace hBound)
      (hBodyReplace hBody))

/-- Canonical `Ms-FOp` handler for innermost `.equ` replacement: recursively
replace the body under the preserved operand head, then lift the resulting
diagrammatic chain through `FOp` with the fixed abstraction bound. -/
theorem msub_equ_head_fop_handler_of_body_replacement {Γ : Ctx} {s : Stack}
    {old new : Term}
    (hpvTail : PrevalidExt ({ bound := old, kind := .equ } :: Γ) s)
    (hnew : Term.Scoped Γ.depth new)
    (hBodyReplace :
      ∀ {arg body body' : Term} {rest : Stack},
        Term.Scoped (Ctx.depth ({ bound := old, kind := .equ } :: Γ)) arg →
        s = arg :: rest →
        MSubRed ({ bound := arg, kind := .equ } ::
          { bound := old, kind := .equ } :: Γ) (Stack.shift 0 rest) body body' →
        MSubStar ({ bound := arg, kind := .equ } ::
          { bound := new, kind := .equ } :: Γ) (Stack.shift 0 rest) body body')
    {bound arg body body' : Term} {rest : Stack}
    (hBoundScoped : Term.Scoped (Ctx.depth ({ bound := old, kind := .equ } :: Γ)) bound)
    (hArgScoped : Term.Scoped (Ctx.depth ({ bound := old, kind := .equ } :: Γ)) arg)
    (hStack : s = arg :: rest)
    (hBody : MSubRed ({ bound := arg, kind := .equ } ::
      { bound := old, kind := .equ } :: Γ) (Stack.shift 0 rest) body body') :
    MSubStar ({ bound := new, kind := .equ } :: Γ) s
      (.abs bound body) (.abs bound body') := by
  subst hStack
  have hpvNewTail : PrevalidExt ({ bound := new, kind := .equ } :: Γ) rest :=
    PrevalidExt.equ_head_replace (PrevalidExt.tail hpvTail) hnew
  exact msubStar_abs_fOp_body_fixed_bound hpvNewTail hBoundScoped hArgScoped
    (hBodyReplace hArgScoped rfl hBody)

/-- Canonical `Ms-FOp` handler for under-head `.equ` replacement. -/
theorem msub_equ_under_head_fop_handler_of_body_replacement {Γ : Ctx} {s : Stack}
    {head : CtxEntry} {old new : Term}
    (hpvTail : PrevalidExt (head :: { bound := old, kind := .equ } :: Γ) s)
    (hnew : Term.Scoped Γ.depth new)
    (hBodyReplace :
      ∀ {arg body body' : Term} {rest : Stack},
        Term.Scoped (Ctx.depth (head :: { bound := old, kind := .equ } :: Γ)) arg →
        s = arg :: rest →
        MSubRed ({ bound := arg, kind := .equ } :: head ::
          { bound := old, kind := .equ } :: Γ) (Stack.shift 0 rest) body body' →
        MSubStar ({ bound := arg, kind := .equ } :: head ::
          { bound := new, kind := .equ } :: Γ) (Stack.shift 0 rest) body body')
    {bound arg body body' : Term} {rest : Stack}
    (hBoundScoped : Term.Scoped (Ctx.depth (head :: { bound := old, kind := .equ } :: Γ)) bound)
    (hArgScoped : Term.Scoped (Ctx.depth (head :: { bound := old, kind := .equ } :: Γ)) arg)
    (hStack : s = arg :: rest)
    (hBody : MSubRed ({ bound := arg, kind := .equ } :: head ::
      { bound := old, kind := .equ } :: Γ) (Stack.shift 0 rest) body body') :
    MSubStar (head :: { bound := new, kind := .equ } :: Γ) s
      (.abs bound body) (.abs bound body') := by
  subst hStack
  have hpvNewTail : PrevalidExt (head :: { bound := new, kind := .equ } :: Γ) rest :=
    PrevalidExt.equ_under_head_replace (PrevalidExt.tail hpvTail) hnew
  exact msubStar_abs_fOp_body_fixed_bound hpvNewTail hBoundScoped hArgScoped
    (hBodyReplace hArgScoped rfl hBody)

/-- Canonical `Me-App` handler for innermost `.equ` replacement when both
recursive premises have already been replaced as raw equivalence steps. -/
theorem meq_equ_head_app_handler_of_raw_replacements {Γ : Ctx} {s : Stack}
    {old new : Term}
    (hpv : PrevalidExt ({ bound := old, kind := .equ } :: Γ) s)
    (hnew : Term.Scoped Γ.depth new)
    (hOpReplace :
      ∀ {op op' arg : Term},
        MEqRed ({ bound := old, kind := .equ } :: Γ) (arg :: s) op op' →
        MEqRed ({ bound := new, kind := .equ } :: Γ) (arg :: s) op op')
    (hArgReplace :
      ∀ {arg arg' : Term},
        MEqRed ({ bound := old, kind := .equ } :: Γ) [] arg arg' →
        MEqRed ({ bound := new, kind := .equ } :: Γ) [] arg arg')
    {op op' arg arg' : Term}
    (hOp : MEqRed ({ bound := old, kind := .equ } :: Γ) (arg :: s) op op')
    (hArg : MEqRed ({ bound := old, kind := .equ } :: Γ) [] arg arg') :
    MSubStar ({ bound := new, kind := .equ } :: Γ) s
      (.app op arg) (.app op' arg') :=
  MSubStar.of_MEqRed (PrevalidExt.equ_head_replace hpv hnew)
    (MEqRed.app_equ_head_replace (_old := old) (hOpReplace hOp) (hArgReplace hArg))

/-- Canonical `Me-App` handler for under-head `.equ` replacement when both
recursive premises have already been replaced as raw equivalence steps. -/
theorem meq_equ_under_head_app_handler_of_raw_replacements {Γ : Ctx}
    {s : Stack} {head : CtxEntry} {old new : Term}
    (hpv : PrevalidExt (head :: { bound := old, kind := .equ } :: Γ) s)
    (hnew : Term.Scoped Γ.depth new)
    (hOpReplace :
      ∀ {op op' arg : Term},
        MEqRed (head :: { bound := old, kind := .equ } :: Γ) (arg :: s) op op' →
        MEqRed (head :: { bound := new, kind := .equ } :: Γ) (arg :: s) op op')
    (hArgReplace :
      ∀ {arg arg' : Term},
        MEqRed (head :: { bound := old, kind := .equ } :: Γ) [] arg arg' →
        MEqRed (head :: { bound := new, kind := .equ } :: Γ) [] arg arg')
    {op op' arg arg' : Term}
    (hOp : MEqRed (head :: { bound := old, kind := .equ } :: Γ) (arg :: s) op op')
    (hArg : MEqRed (head :: { bound := old, kind := .equ } :: Γ) [] arg arg') :
    MSubStar (head :: { bound := new, kind := .equ } :: Γ) s
      (.app op arg) (.app op' arg') :=
  MSubStar.of_MEqRed (PrevalidExt.equ_under_head_replace hpv hnew)
    (MEqRed.app_equ_under_head_replace (_old := old) (hOpReplace hOp)
      (hArgReplace hArg))

/-- Canonical `Me-Fun` handler for innermost `.equ` replacement when the
bound and body premises have already been replaced as raw equivalence steps.
-/
theorem meq_equ_head_fun_handler_of_raw_replacements {Γ : Ctx}
    {old new : Term}
    (hpvNil : PrevalidExt ({ bound := old, kind := .equ } :: Γ) [])
    (hnew : Term.Scoped Γ.depth new)
    (hBoundReplace :
      ∀ {bound bound' : Term},
        MEqRed ({ bound := old, kind := .equ } :: Γ) [] bound bound' →
        MEqRed ({ bound := new, kind := .equ } :: Γ) [] bound bound')
    (hBodyReplace :
      ∀ {bound body body' : Term},
        MEqRed ({ bound := bound, kind := .sub } ::
          { bound := old, kind := .equ } :: Γ) [] body body' →
        MEqRed ({ bound := bound, kind := .sub } ::
          { bound := new, kind := .equ } :: Γ) [] body body')
    {bound bound' body body' : Term}
    (hBound : MEqRed ({ bound := old, kind := .equ } :: Γ) [] bound bound')
    (hBody : MEqRed ({ bound := bound, kind := .sub } ::
      { bound := old, kind := .equ } :: Γ) [] body body') :
    MSubStar ({ bound := new, kind := .equ } :: Γ) []
      (.abs bound body) (.abs bound' body') :=
  MSubStar.of_MEqRed (PrevalidExt.equ_head_replace hpvNil hnew)
    (MEqRed.fun_equ_head_replace (_old := old) (hBoundReplace hBound)
      (hBodyReplace hBody))

/-- Canonical `Me-Fun` handler for under-head `.equ` replacement when the
bound and body premises have already been replaced as raw equivalence steps.
-/
theorem meq_equ_under_head_fun_handler_of_raw_replacements {Γ : Ctx}
    {head : CtxEntry} {old new : Term}
    (hpvNil : PrevalidExt (head :: { bound := old, kind := .equ } :: Γ) [])
    (hnew : Term.Scoped Γ.depth new)
    (hBoundReplace :
      ∀ {bound bound' : Term},
        MEqRed (head :: { bound := old, kind := .equ } :: Γ) [] bound bound' →
        MEqRed (head :: { bound := new, kind := .equ } :: Γ) [] bound bound')
    (hBodyReplace :
      ∀ {bound body body' : Term},
        MEqRed ({ bound := bound, kind := .sub } :: head ::
          { bound := old, kind := .equ } :: Γ) [] body body' →
        MEqRed ({ bound := bound, kind := .sub } :: head ::
          { bound := new, kind := .equ } :: Γ) [] body body')
    {bound bound' body body' : Term}
    (hBound : MEqRed (head :: { bound := old, kind := .equ } :: Γ) [] bound bound')
    (hBody : MEqRed ({ bound := bound, kind := .sub } :: head ::
      { bound := old, kind := .equ } :: Γ) [] body body') :
    MSubStar (head :: { bound := new, kind := .equ } :: Γ) []
      (.abs bound body) (.abs bound' body') :=
  MSubStar.of_MEqRed (PrevalidExt.equ_under_head_replace hpvNil hnew)
    (MEqRed.fun_equ_under_head_replace (_old := old) (hBoundReplace hBound)
      (hBodyReplace hBody))

/-- Canonical `Me-Bet` handler for innermost `.equ` replacement when the body
and argument premises have already been replaced as raw equivalence steps. -/
theorem meq_equ_head_bet_handler_of_raw_replacements {Γ : Ctx} {s : Stack}
    {old new : Term}
    (hpv : PrevalidExt ({ bound := old, kind := .equ } :: Γ) s)
    (hnew : Term.Scoped Γ.depth new)
    (hBodyReplace :
      ∀ {bound body body' : Term},
        MEqRed ({ bound := bound, kind := .sub } ::
          { bound := old, kind := .equ } :: Γ) (Stack.shift 0 s) body body' →
        MEqRed ({ bound := bound, kind := .sub } ::
          { bound := new, kind := .equ } :: Γ) (Stack.shift 0 s) body body')
    (hArgReplace :
      ∀ {arg arg' : Term},
        MEqRed ({ bound := old, kind := .equ } :: Γ) [] arg arg' →
        MEqRed ({ bound := new, kind := .equ } :: Γ) [] arg arg')
    {bound arg arg' body body' : Term}
    (hBoundScoped : Term.Scoped (Ctx.depth ({ bound := old, kind := .equ } :: Γ)) bound)
    (hBody : MEqRed ({ bound := bound, kind := .sub } ::
      { bound := old, kind := .equ } :: Γ) (Stack.shift 0 s) body body')
    (hArg : MEqRed ({ bound := old, kind := .equ } :: Γ) [] arg arg') :
    MSubStar ({ bound := new, kind := .equ } :: Γ) s
      (.app (.abs bound body) arg) (Term.instantiate 0 arg' body') :=
  MSubStar.of_MEqRed (PrevalidExt.equ_head_replace hpv hnew)
    (MEqRed.bet_equ_head_replace hBoundScoped (hBodyReplace hBody)
      (hArgReplace hArg))

/-- Canonical `Me-Bet` handler for under-head `.equ` replacement when the body
and argument premises have already been replaced as raw equivalence steps. -/
theorem meq_equ_under_head_bet_handler_of_raw_replacements {Γ : Ctx} {s : Stack}
    {head : CtxEntry} {old new : Term}
    (hpv : PrevalidExt (head :: { bound := old, kind := .equ } :: Γ) s)
    (hnew : Term.Scoped Γ.depth new)
    (hBodyReplace :
      ∀ {bound body body' : Term},
        MEqRed ({ bound := bound, kind := .sub } :: head ::
          { bound := old, kind := .equ } :: Γ) (Stack.shift 0 s) body body' →
        MEqRed ({ bound := bound, kind := .sub } :: head ::
          { bound := new, kind := .equ } :: Γ) (Stack.shift 0 s) body body')
    (hArgReplace :
      ∀ {arg arg' : Term},
        MEqRed (head :: { bound := old, kind := .equ } :: Γ) [] arg arg' →
        MEqRed (head :: { bound := new, kind := .equ } :: Γ) [] arg arg')
    {bound arg arg' body body' : Term}
    (hBoundScoped : Term.Scoped (Ctx.depth (head :: { bound := old, kind := .equ } :: Γ)) bound)
    (hBody : MEqRed ({ bound := bound, kind := .sub } :: head ::
      { bound := old, kind := .equ } :: Γ) (Stack.shift 0 s) body body')
    (hArg : MEqRed (head :: { bound := old, kind := .equ } :: Γ) [] arg arg') :
    MSubStar (head :: { bound := new, kind := .equ } :: Γ) s
      (.app (.abs bound body) arg) (Term.instantiate 0 arg' body') :=
  MSubStar.of_MEqRed (PrevalidExt.equ_under_head_replace hpv hnew)
    (MEqRed.bet_equ_under_head_replace hBoundScoped (hBodyReplace hBody)
      (hArgReplace hArg))

/-- Canonical `Me-FOp` handler for innermost `.equ` replacement: replace the
abstraction-bound equivalence as a raw step, replace the body recursively as a
diagrammatic chain under the preserved operand head, then lift both through
`FOp`. -/
theorem meq_equ_head_fop_handler_of_body_replacement {Γ : Ctx} {s : Stack}
    {old new : Term}
    (hpvTail : PrevalidExt ({ bound := old, kind := .equ } :: Γ) s)
    (hnew : Term.Scoped Γ.depth new)
    (hBoundReplace :
      ∀ {bound bound' : Term},
        MEqRed ({ bound := old, kind := .equ } :: Γ) [] bound bound' →
        MEqRed ({ bound := new, kind := .equ } :: Γ) [] bound bound')
    (hBodyReplace :
      ∀ {arg body body' : Term} {rest : Stack},
        Term.Scoped (Ctx.depth ({ bound := old, kind := .equ } :: Γ)) arg →
        s = arg :: rest →
        MEqRed ({ bound := arg, kind := .equ } ::
          { bound := old, kind := .equ } :: Γ) (Stack.shift 0 rest) body body' →
        MSubStar ({ bound := arg, kind := .equ } ::
          { bound := new, kind := .equ } :: Γ) (Stack.shift 0 rest) body body')
    {bound bound' arg body body' : Term} {rest : Stack}
    (hBound : MEqRed ({ bound := old, kind := .equ } :: Γ) [] bound bound')
    (hArgScoped : Term.Scoped (Ctx.depth ({ bound := old, kind := .equ } :: Γ)) arg)
    (hStack : s = arg :: rest)
    (hBody : MEqRed ({ bound := arg, kind := .equ } ::
      { bound := old, kind := .equ } :: Γ) (Stack.shift 0 rest) body body') :
    MSubStar ({ bound := new, kind := .equ } :: Γ) s
      (.abs bound body) (.abs bound' body') := by
  subst hStack
  have hpvNewTail : PrevalidExt ({ bound := new, kind := .equ } :: Γ) rest :=
    PrevalidExt.equ_head_replace (PrevalidExt.tail hpvTail) hnew
  exact msubStar_abs_fOp_equ_bound_body hpvNewTail (hBoundReplace hBound)
    hArgScoped hBody.scoped_left (hBodyReplace hArgScoped rfl hBody)

/-- Canonical `Me-FOp` handler for under-head `.equ` replacement. -/
theorem meq_equ_under_head_fop_handler_of_body_replacement {Γ : Ctx} {s : Stack}
    {head : CtxEntry} {old new : Term}
    (hpvTail : PrevalidExt (head :: { bound := old, kind := .equ } :: Γ) s)
    (hnew : Term.Scoped Γ.depth new)
    (hBoundReplace :
      ∀ {bound bound' : Term},
        MEqRed (head :: { bound := old, kind := .equ } :: Γ) [] bound bound' →
        MEqRed (head :: { bound := new, kind := .equ } :: Γ) [] bound bound')
    (hBodyReplace :
      ∀ {arg body body' : Term} {rest : Stack},
        Term.Scoped (Ctx.depth (head :: { bound := old, kind := .equ } :: Γ)) arg →
        s = arg :: rest →
        MEqRed ({ bound := arg, kind := .equ } :: head ::
          { bound := old, kind := .equ } :: Γ) (Stack.shift 0 rest) body body' →
        MSubStar ({ bound := arg, kind := .equ } :: head ::
          { bound := new, kind := .equ } :: Γ) (Stack.shift 0 rest) body body')
    {bound bound' arg body body' : Term} {rest : Stack}
    (hBound : MEqRed (head :: { bound := old, kind := .equ } :: Γ) [] bound bound')
    (hArgScoped : Term.Scoped (Ctx.depth (head :: { bound := old, kind := .equ } :: Γ)) arg)
    (hStack : s = arg :: rest)
    (hBody : MEqRed ({ bound := arg, kind := .equ } :: head ::
      { bound := old, kind := .equ } :: Γ) (Stack.shift 0 rest) body body') :
    MSubStar (head :: { bound := new, kind := .equ } :: Γ) s
      (.abs bound body) (.abs bound' body') := by
  subst hStack
  have hpvNewTail : PrevalidExt (head :: { bound := new, kind := .equ } :: Γ) rest :=
    PrevalidExt.equ_under_head_replace (PrevalidExt.tail hpvTail) hnew
  exact msubStar_abs_fOp_equ_bound_body hpvNewTail (hBoundReplace hBound)
    hArgScoped hBody.scoped_left (hBodyReplace hArgScoped rfl hBody)

/-- Subtype replacement across an innermost changed `.equ` head, with the
stable cases and canonical constructor handlers wired in. The remaining
premises are precisely the recursive replacements for equivalence premises,
application operators, function components, and `FOp` bodies. -/
theorem msubRed_equ_head_replace_from_replacements {Γ : Ctx} {s : Stack}
    {old new u v : Term}
    (hpv : PrevalidExt ({ bound := old, kind := .equ } :: Γ) s)
    (hnew : Term.Scoped Γ.depth new)
    (hEq :
      ∀ {u v : Term},
        MEqRed ({ bound := old, kind := .equ } :: Γ) s u v →
        MSubStar ({ bound := new, kind := .equ } :: Γ) s u v)
    (hAppOpReplace :
      ∀ {op op' arg : Term},
        MSubRed ({ bound := old, kind := .equ } :: Γ) (arg :: s) op op' →
        Term.Scoped (Ctx.depth ({ bound := old, kind := .equ } :: Γ)) arg →
        MSubStar ({ bound := new, kind := .equ } :: Γ) (arg :: s) op op')
    (hFunBoundReplace :
      ∀ {bound bound' : Term},
        MEqRed ({ bound := old, kind := .equ } :: Γ) [] bound bound' →
        MEqRed ({ bound := new, kind := .equ } :: Γ) [] bound bound')
    (hFunBodyReplace :
      ∀ {bound body body' : Term},
        MSubRed ({ bound := bound, kind := .sub } ::
          { bound := old, kind := .equ } :: Γ) [] body body' →
        MSubRed ({ bound := bound, kind := .sub } ::
          { bound := new, kind := .equ } :: Γ) [] body body')
    (hFOpBodyReplace :
      ∀ {arg body body' : Term} {rest : Stack},
        Term.Scoped (Ctx.depth ({ bound := old, kind := .equ } :: Γ)) arg →
        s = arg :: rest →
        MSubRed ({ bound := arg, kind := .equ } ::
          { bound := old, kind := .equ } :: Γ) (Stack.shift 0 rest) body body' →
        MSubStar ({ bound := arg, kind := .equ } ::
          { bound := new, kind := .equ } :: Γ) (Stack.shift 0 rest) body body')
    (h : MSubRed ({ bound := old, kind := .equ } :: Γ) s u v) :
    MSubStar ({ bound := new, kind := .equ } :: Γ) s u v :=
  msubRed_equ_head_replace_from_handlers hpv hnew hEq
    (msub_equ_head_app_handler_of_operator_replacement hpv hnew hAppOpReplace)
    (msub_equ_head_fun_handler_of_raw_replacements hFunBoundReplace hFunBodyReplace)
    (msub_equ_head_fop_handler_of_body_replacement hpv hnew hFOpBodyReplace)
    h

/-- Subtype replacement when the changed `.equ` entry sits immediately under
a preserved head, with the canonical constructor handlers wired in. -/
theorem msubRed_equ_under_head_replace_from_replacements {Γ : Ctx} {s : Stack}
    {head : CtxEntry} {old new u v : Term}
    (hpv : PrevalidExt (head :: { bound := old, kind := .equ } :: Γ) s)
    (hnew : Term.Scoped Γ.depth new)
    (hEq :
      ∀ {u v : Term},
        MEqRed (head :: { bound := old, kind := .equ } :: Γ) s u v →
        MSubStar (head :: { bound := new, kind := .equ } :: Γ) s u v)
    (hAppOpReplace :
      ∀ {op op' arg : Term},
        MSubRed (head :: { bound := old, kind := .equ } :: Γ) (arg :: s) op op' →
        Term.Scoped (Ctx.depth (head :: { bound := old, kind := .equ } :: Γ)) arg →
        MSubStar (head :: { bound := new, kind := .equ } :: Γ) (arg :: s) op op')
    (hFunBoundReplace :
      ∀ {bound bound' : Term},
        MEqRed (head :: { bound := old, kind := .equ } :: Γ) [] bound bound' →
        MEqRed (head :: { bound := new, kind := .equ } :: Γ) [] bound bound')
    (hFunBodyReplace :
      ∀ {bound body body' : Term},
        MSubRed ({ bound := bound, kind := .sub } :: head ::
          { bound := old, kind := .equ } :: Γ) [] body body' →
        MSubRed ({ bound := bound, kind := .sub } :: head ::
          { bound := new, kind := .equ } :: Γ) [] body body')
    (hFOpBodyReplace :
      ∀ {arg body body' : Term} {rest : Stack},
        Term.Scoped (Ctx.depth (head :: { bound := old, kind := .equ } :: Γ)) arg →
        s = arg :: rest →
        MSubRed ({ bound := arg, kind := .equ } :: head ::
          { bound := old, kind := .equ } :: Γ) (Stack.shift 0 rest) body body' →
        MSubStar ({ bound := arg, kind := .equ } :: head ::
          { bound := new, kind := .equ } :: Γ) (Stack.shift 0 rest) body body')
    (h : MSubRed (head :: { bound := old, kind := .equ } :: Γ) s u v) :
    MSubStar (head :: { bound := new, kind := .equ } :: Γ) s u v :=
  msubRed_equ_under_head_replace_from_handlers hpv hnew hEq
    (msub_equ_under_head_app_handler_of_operator_replacement hpv hnew hAppOpReplace)
    (msub_equ_under_head_fun_handler_of_raw_replacements
      hFunBoundReplace hFunBodyReplace)
    (msub_equ_under_head_fop_handler_of_body_replacement hpv hnew hFOpBodyReplace)
    h

/-- One-step equivalence replacement splitter for an innermost changed `.equ`
head. Stable leaves are discharged immediately; the head `Me-Pro` case is
exposed as its precise residual, and recursive constructor cases are exposed
as explicit handlers. -/
theorem meqRed_equ_head_replace_from_handlers {Γ : Ctx} {s : Stack}
    {old new u v : Term}
    (hpv : PrevalidExt ({ bound := old, kind := .equ } :: Γ) s)
    (hnew : Term.Scoped Γ.depth new)
    (hProHead :
      ∀ {target : Term},
        MEqRed ({ bound := old, kind := .equ } :: Γ) s
          (Term.shift 0 old) target →
        MSubStar ({ bound := new, kind := .equ } :: Γ) s (.bvar 0) target)
    (hProTail :
      ∀ {i : Nat} {α α' : Term},
        Ctx.equBinds ({ bound := old, kind := .equ } :: Γ) (i + 1) α →
        MEqRed ({ bound := old, kind := .equ } :: Γ) s α α' →
        MSubStar ({ bound := new, kind := .equ } :: Γ) s (.bvar (i + 1)) α')
    (hApp :
      ∀ {op op' arg arg' : Term},
        MEqRed ({ bound := old, kind := .equ } :: Γ) (arg :: s) op op' →
        MEqRed ({ bound := old, kind := .equ } :: Γ) [] arg arg' →
        MSubStar ({ bound := new, kind := .equ } :: Γ) s
          (.app op arg) (.app op' arg'))
    (hFun :
      ∀ {bound bound' body body' : Term},
        MEqRed ({ bound := old, kind := .equ } :: Γ) [] bound bound' →
        MEqRed ({ bound := bound, kind := .sub } ::
          { bound := old, kind := .equ } :: Γ) [] body body' →
        MSubStar ({ bound := new, kind := .equ } :: Γ) []
          (.abs bound body) (.abs bound' body'))
    (hBet :
      ∀ {bound arg arg' body body' : Term},
        Term.Scoped (Ctx.depth ({ bound := old, kind := .equ } :: Γ)) bound →
        MEqRed ({ bound := bound, kind := .sub } ::
          { bound := old, kind := .equ } :: Γ) (Stack.shift 0 s) body body' →
        MEqRed ({ bound := old, kind := .equ } :: Γ) [] arg arg' →
        MSubStar ({ bound := new, kind := .equ } :: Γ) s
          (.app (.abs bound body) arg) (Term.instantiate 0 arg' body'))
    (hFOp :
      ∀ {bound bound' arg body body' : Term} {rest : Stack},
        MEqRed ({ bound := old, kind := .equ } :: Γ) [] bound bound' →
        Term.Scoped (Ctx.depth ({ bound := old, kind := .equ } :: Γ)) arg →
        s = arg :: rest →
        MEqRed ({ bound := arg, kind := .equ } ::
          { bound := old, kind := .equ } :: Γ) (Stack.shift 0 rest) body body' →
        MSubStar ({ bound := new, kind := .equ } :: Γ) s
          (.abs bound body) (.abs bound' body'))
    (h : MEqRed ({ bound := old, kind := .equ } :: Γ) s u v) :
    MSubStar ({ bound := new, kind := .equ } :: Γ) s u v := by
  have hpvNew : PrevalidExt ({ bound := new, kind := .equ } :: Γ) s :=
    PrevalidExt.equ_head_replace hpv hnew
  cases h with
  | @pro Γp sp i α α' _ hb hα =>
    cases i with
    | zero =>
      obtain ⟨hαEq, hResidual⟩ := MEqRed.pro_equ_head_zero_residual hb hα
      subst hαEq
      exact hProHead hResidual.some
    | succ i =>
      exact hProTail hb hα
  | top _ =>
    exact MSubStar.of_MEqRed hpvNew (MEqRed.top_equ_head_replace hpv hnew)
  | app hOp hArg =>
    exact hApp hOp hArg
  | var _ hi =>
    exact MSubStar.of_MEqRed hpvNew (MEqRed.var_equ_head_replace hpv hnew hi)
  | fun_ hBound hBody =>
    exact hFun hBound hBody
  | tAp _ hu =>
    exact MSubStar.of_MEqRed hpvNew (MEqRed.tAp_equ_head_replace hpv hnew hu)
  | fOp hBound hArg hBody =>
    exact hFOp hBound hArg rfl hBody
  | bet ht hBody hArg =>
    exact hBet ht hBody hArg

/-- One-step equivalence replacement splitter when the changed `.equ` entry
sits immediately under a preserved head. The residual `Me-Pro` case is the
under-head index `1`; preserved-head index `0` and indices `2+` are delegated
to stable/recursive handlers. -/
theorem meqRed_equ_under_head_replace_from_handlers {Γ : Ctx} {s : Stack}
    {head : CtxEntry} {old new u v : Term}
    (hpv : PrevalidExt (head :: { bound := old, kind := .equ } :: Γ) s)
    (hnew : Term.Scoped Γ.depth new)
    (hProZero :
      ∀ {α α' : Term},
        Ctx.equBinds (head :: { bound := old, kind := .equ } :: Γ) 0 α →
        MEqRed (head :: { bound := old, kind := .equ } :: Γ) s α α' →
        MSubStar (head :: { bound := new, kind := .equ } :: Γ) s (.bvar 0) α')
    (hProOne :
      ∀ {target : Term},
        MEqRed (head :: { bound := old, kind := .equ } :: Γ) s
          (Term.shift 0 (Term.shift 0 old)) target →
        MSubStar (head :: { bound := new, kind := .equ } :: Γ) s (.bvar 1) target)
    (hProTail :
      ∀ {i : Nat} {α α' : Term},
        Ctx.equBinds (head :: { bound := old, kind := .equ } :: Γ) ((i + 1) + 1) α →
        MEqRed (head :: { bound := old, kind := .equ } :: Γ) s α α' →
        MSubStar (head :: { bound := new, kind := .equ } :: Γ) s
          (.bvar ((i + 1) + 1)) α')
    (hApp :
      ∀ {op op' arg arg' : Term},
        MEqRed (head :: { bound := old, kind := .equ } :: Γ) (arg :: s) op op' →
        MEqRed (head :: { bound := old, kind := .equ } :: Γ) [] arg arg' →
        MSubStar (head :: { bound := new, kind := .equ } :: Γ) s
          (.app op arg) (.app op' arg'))
    (hFun :
      ∀ {bound bound' body body' : Term},
        MEqRed (head :: { bound := old, kind := .equ } :: Γ) [] bound bound' →
        MEqRed ({ bound := bound, kind := .sub } :: head ::
          { bound := old, kind := .equ } :: Γ) [] body body' →
        MSubStar (head :: { bound := new, kind := .equ } :: Γ) []
          (.abs bound body) (.abs bound' body'))
    (hBet :
      ∀ {bound arg arg' body body' : Term},
        Term.Scoped (Ctx.depth (head :: { bound := old, kind := .equ } :: Γ)) bound →
        MEqRed ({ bound := bound, kind := .sub } :: head ::
          { bound := old, kind := .equ } :: Γ) (Stack.shift 0 s) body body' →
        MEqRed (head :: { bound := old, kind := .equ } :: Γ) [] arg arg' →
        MSubStar (head :: { bound := new, kind := .equ } :: Γ) s
          (.app (.abs bound body) arg) (Term.instantiate 0 arg' body'))
    (hFOp :
      ∀ {bound bound' arg body body' : Term} {rest : Stack},
        MEqRed (head :: { bound := old, kind := .equ } :: Γ) [] bound bound' →
        Term.Scoped (Ctx.depth (head :: { bound := old, kind := .equ } :: Γ)) arg →
        s = arg :: rest →
        MEqRed ({ bound := arg, kind := .equ } :: head ::
          { bound := old, kind := .equ } :: Γ) (Stack.shift 0 rest) body body' →
        MSubStar (head :: { bound := new, kind := .equ } :: Γ) s
          (.abs bound body) (.abs bound' body'))
    (h : MEqRed (head :: { bound := old, kind := .equ } :: Γ) s u v) :
    MSubStar (head :: { bound := new, kind := .equ } :: Γ) s u v := by
  have hpvNew : PrevalidExt (head :: { bound := new, kind := .equ } :: Γ) s :=
    PrevalidExt.equ_under_head_replace hpv hnew
  cases h with
  | @pro Γp sp i α α' _ hb hα =>
    cases i with
    | zero =>
      exact hProZero hb hα
    | succ i =>
      cases i with
      | zero =>
        obtain ⟨hαEq, hResidual⟩ := MEqRed.pro_equ_under_head_one_residual hb hα
        subst hαEq
        exact hProOne hResidual.some
      | succ i =>
        exact hProTail hb hα
  | top _ =>
    exact MSubStar.of_MEqRed hpvNew (MEqRed.top_equ_under_head_replace hpv hnew)
  | app hOp hArg =>
    exact hApp hOp hArg
  | var _ hi =>
    exact MSubStar.of_MEqRed hpvNew (MEqRed.var_equ_under_head_replace hpv hnew hi)
  | fun_ hBound hBody =>
    exact hFun hBound hBody
  | tAp _ hu =>
    exact MSubStar.of_MEqRed hpvNew (MEqRed.tAp_equ_under_head_replace hpv hnew hu)
  | fOp hBound hArg hBody =>
    exact hFOp hBound hArg rfl hBody
  | bet ht hBody hArg =>
    exact hBet ht hBody hArg

/-- Equivalence replacement across an innermost changed `.equ` head, with
canonical constructor handlers wired in. The `Me-Pro` residual handlers stay
explicit because they are the only lookup-sensitive cases. -/
theorem meqRed_equ_head_replace_from_replacements {Γ : Ctx} {s : Stack}
    {old new u v : Term}
    (hpv : PrevalidExt ({ bound := old, kind := .equ } :: Γ) s)
    (hnew : Term.Scoped Γ.depth new)
    (hProHead :
      ∀ {target : Term},
        MEqRed ({ bound := old, kind := .equ } :: Γ) s
          (Term.shift 0 old) target →
        MSubStar ({ bound := new, kind := .equ } :: Γ) s (.bvar 0) target)
    (hProTail :
      ∀ {i : Nat} {α α' : Term},
        Ctx.equBinds ({ bound := old, kind := .equ } :: Γ) (i + 1) α →
        MEqRed ({ bound := old, kind := .equ } :: Γ) s α α' →
        MSubStar ({ bound := new, kind := .equ } :: Γ) s (.bvar (i + 1)) α')
    (hAppOpReplace :
      ∀ {op op' arg : Term},
        MEqRed ({ bound := old, kind := .equ } :: Γ) (arg :: s) op op' →
        MEqRed ({ bound := new, kind := .equ } :: Γ) (arg :: s) op op')
    (hNilReplace :
      ∀ {arg arg' : Term},
        MEqRed ({ bound := old, kind := .equ } :: Γ) [] arg arg' →
        MEqRed ({ bound := new, kind := .equ } :: Γ) [] arg arg')
    (hFunBodyReplace :
      ∀ {bound body body' : Term},
        MEqRed ({ bound := bound, kind := .sub } ::
          { bound := old, kind := .equ } :: Γ) [] body body' →
        MEqRed ({ bound := bound, kind := .sub } ::
          { bound := new, kind := .equ } :: Γ) [] body body')
    (hBetBodyReplace :
      ∀ {bound body body' : Term},
        MEqRed ({ bound := bound, kind := .sub } ::
          { bound := old, kind := .equ } :: Γ) (Stack.shift 0 s) body body' →
        MEqRed ({ bound := bound, kind := .sub } ::
          { bound := new, kind := .equ } :: Γ) (Stack.shift 0 s) body body')
    (hFOpBodyReplace :
      ∀ {arg body body' : Term} {rest : Stack},
        Term.Scoped (Ctx.depth ({ bound := old, kind := .equ } :: Γ)) arg →
        s = arg :: rest →
        MEqRed ({ bound := arg, kind := .equ } ::
          { bound := old, kind := .equ } :: Γ) (Stack.shift 0 rest) body body' →
        MSubStar ({ bound := arg, kind := .equ } ::
          { bound := new, kind := .equ } :: Γ) (Stack.shift 0 rest) body body')
    (h : MEqRed ({ bound := old, kind := .equ } :: Γ) s u v) :
    MSubStar ({ bound := new, kind := .equ } :: Γ) s u v :=
  meqRed_equ_head_replace_from_handlers hpv hnew hProHead hProTail
    (meq_equ_head_app_handler_of_raw_replacements hpv hnew hAppOpReplace hNilReplace)
    (meq_equ_head_fun_handler_of_raw_replacements
      (PrevalidExt.nil (PrevalidExt.ctx hpv)) hnew hNilReplace hFunBodyReplace)
    (meq_equ_head_bet_handler_of_raw_replacements hpv hnew
      hBetBodyReplace hNilReplace)
    (meq_equ_head_fop_handler_of_body_replacement hpv hnew
      hNilReplace hFOpBodyReplace)
    h

/-- Equivalence replacement when the changed `.equ` entry sits immediately
under a preserved head, with canonical constructor handlers wired in. -/
theorem meqRed_equ_under_head_replace_from_replacements {Γ : Ctx} {s : Stack}
    {head : CtxEntry} {old new u v : Term}
    (hpv : PrevalidExt (head :: { bound := old, kind := .equ } :: Γ) s)
    (hnew : Term.Scoped Γ.depth new)
    (hProZero :
      ∀ {α α' : Term},
        Ctx.equBinds (head :: { bound := old, kind := .equ } :: Γ) 0 α →
        MEqRed (head :: { bound := old, kind := .equ } :: Γ) s α α' →
        MSubStar (head :: { bound := new, kind := .equ } :: Γ) s (.bvar 0) α')
    (hProOne :
      ∀ {target : Term},
        MEqRed (head :: { bound := old, kind := .equ } :: Γ) s
          (Term.shift 0 (Term.shift 0 old)) target →
        MSubStar (head :: { bound := new, kind := .equ } :: Γ) s (.bvar 1) target)
    (hProTail :
      ∀ {i : Nat} {α α' : Term},
        Ctx.equBinds (head :: { bound := old, kind := .equ } :: Γ) ((i + 1) + 1) α →
        MEqRed (head :: { bound := old, kind := .equ } :: Γ) s α α' →
        MSubStar (head :: { bound := new, kind := .equ } :: Γ) s
          (.bvar ((i + 1) + 1)) α')
    (hAppOpReplace :
      ∀ {op op' arg : Term},
        MEqRed (head :: { bound := old, kind := .equ } :: Γ) (arg :: s) op op' →
        MEqRed (head :: { bound := new, kind := .equ } :: Γ) (arg :: s) op op')
    (hNilReplace :
      ∀ {arg arg' : Term},
        MEqRed (head :: { bound := old, kind := .equ } :: Γ) [] arg arg' →
        MEqRed (head :: { bound := new, kind := .equ } :: Γ) [] arg arg')
    (hFunBodyReplace :
      ∀ {bound body body' : Term},
        MEqRed ({ bound := bound, kind := .sub } :: head ::
          { bound := old, kind := .equ } :: Γ) [] body body' →
        MEqRed ({ bound := bound, kind := .sub } :: head ::
          { bound := new, kind := .equ } :: Γ) [] body body')
    (hBetBodyReplace :
      ∀ {bound body body' : Term},
        MEqRed ({ bound := bound, kind := .sub } :: head ::
          { bound := old, kind := .equ } :: Γ) (Stack.shift 0 s) body body' →
        MEqRed ({ bound := bound, kind := .sub } :: head ::
          { bound := new, kind := .equ } :: Γ) (Stack.shift 0 s) body body')
    (hFOpBodyReplace :
      ∀ {arg body body' : Term} {rest : Stack},
        Term.Scoped (Ctx.depth (head :: { bound := old, kind := .equ } :: Γ)) arg →
        s = arg :: rest →
        MEqRed ({ bound := arg, kind := .equ } :: head ::
          { bound := old, kind := .equ } :: Γ) (Stack.shift 0 rest) body body' →
        MSubStar ({ bound := arg, kind := .equ } :: head ::
          { bound := new, kind := .equ } :: Γ) (Stack.shift 0 rest) body body')
    (h : MEqRed (head :: { bound := old, kind := .equ } :: Γ) s u v) :
    MSubStar (head :: { bound := new, kind := .equ } :: Γ) s u v :=
  meqRed_equ_under_head_replace_from_handlers hpv hnew hProZero hProOne hProTail
    (meq_equ_under_head_app_handler_of_raw_replacements hpv hnew
      hAppOpReplace hNilReplace)
    (meq_equ_under_head_fun_handler_of_raw_replacements
      (PrevalidExt.nil (PrevalidExt.ctx hpv)) hnew hNilReplace hFunBodyReplace)
    (meq_equ_under_head_bet_handler_of_raw_replacements hpv hnew
      hBetBodyReplace hNilReplace)
    (meq_equ_under_head_fop_handler_of_body_replacement hpv hnew
      hNilReplace hFOpBodyReplace)
    h

/-- Consume a subtype-reduction chain when each old-context step has already
been replaced by a diagrammatic chain in the new context. -/
theorem msubRedStar_replace_from_step_replacement {Γ Γ' : Ctx} {s : Stack}
    {u v : Term}
    (hStep :
      ∀ {a b : Term}, MSubRed Γ s a b → MSubStar Γ' s a b)
    (h : MSubRedStar Γ s u v) : MSubStar Γ' s u v := by
  induction h with
  | refl =>
    exact MSubStar.refl
  | @tail mid v hStar hLast ih =>
    exact MSubStar.trans ih (hStep hLast.some)

/-- Consume an equivalence-reduction chain when each old-context step has
already been replaced by a diagrammatic chain in the new context. -/
theorem meqRedStar_replace_from_step_replacement {Γ Γ' : Ctx} {s : Stack}
    {u v : Term}
    (hStep :
      ∀ {a b : Term}, MEqRed Γ s a b → MSubStar Γ' s a b)
    (h : MEqRedStar Γ s u v) : MSubStar Γ' s u v := by
  induction h with
  | refl =>
    exact MSubStar.refl
  | @tail mid v hStar hLast ih =>
    exact MSubStar.trans ih (hStep hLast.some)

/-- Function-valued variant of
`msubRedStar_replace_from_step_replacement`: consume subtype-reduction
chains at every residual stack from a tail-polymorphic step replacement. -/
theorem msubRedStar_replace_from_step_replacement_function {Γ Γ' : Ctx}
    {u v : Term}
    (hStep :
      ∀ {s : Stack},
        PrevalidExt Γ s →
        ∀ {a b : Term},
          MSubRed Γ s a b → MSubStar Γ' s a b)
    (h : ∀ {s : Stack}, PrevalidExt Γ s → MSubRedStar Γ s u v) :
    ∀ {s : Stack}, PrevalidExt Γ s → MSubStar Γ' s u v :=
  fun hpv =>
    msubRedStar_replace_from_step_replacement (hStep hpv) (h hpv)

/-- Function-valued variant of
`meqRedStar_replace_from_step_replacement`: consume equivalence-reduction
chains at every residual stack from a tail-polymorphic step replacement. -/
theorem meqRedStar_replace_from_step_replacement_function {Γ Γ' : Ctx}
    {u v : Term}
    (hStep :
      ∀ {s : Stack},
        PrevalidExt Γ s →
        ∀ {a b : Term},
          MEqRed Γ s a b → MSubStar Γ' s a b)
    (h : ∀ {s : Stack}, PrevalidExt Γ s → MEqRedStar Γ s u v) :
    ∀ {s : Stack}, PrevalidExt Γ s → MSubStar Γ' s u v :=
  fun hpv =>
    meqRedStar_replace_from_step_replacement (hStep hpv) (h hpv)

/-- Star-level subtype replacement across an innermost changed `.equ` head,
obtained by composing the one-step replacement wrapper over a subtype
reduction chain. -/
theorem msubRedStar_equ_head_replace_from_replacements {Γ : Ctx} {s : Stack}
    {old new u v : Term}
    (hpv : PrevalidExt ({ bound := old, kind := .equ } :: Γ) s)
    (hnew : Term.Scoped Γ.depth new)
    (hEq :
      ∀ {u v : Term},
        MEqRed ({ bound := old, kind := .equ } :: Γ) s u v →
        MSubStar ({ bound := new, kind := .equ } :: Γ) s u v)
    (hAppOpReplace :
      ∀ {op op' arg : Term},
        MSubRed ({ bound := old, kind := .equ } :: Γ) (arg :: s) op op' →
        Term.Scoped (Ctx.depth ({ bound := old, kind := .equ } :: Γ)) arg →
        MSubStar ({ bound := new, kind := .equ } :: Γ) (arg :: s) op op')
    (hFunBoundReplace :
      ∀ {bound bound' : Term},
        MEqRed ({ bound := old, kind := .equ } :: Γ) [] bound bound' →
        MEqRed ({ bound := new, kind := .equ } :: Γ) [] bound bound')
    (hFunBodyReplace :
      ∀ {bound body body' : Term},
        MSubRed ({ bound := bound, kind := .sub } ::
          { bound := old, kind := .equ } :: Γ) [] body body' →
        MSubRed ({ bound := bound, kind := .sub } ::
          { bound := new, kind := .equ } :: Γ) [] body body')
    (hFOpBodyReplace :
      ∀ {arg body body' : Term} {rest : Stack},
        Term.Scoped (Ctx.depth ({ bound := old, kind := .equ } :: Γ)) arg →
        s = arg :: rest →
        MSubRed ({ bound := arg, kind := .equ } ::
          { bound := old, kind := .equ } :: Γ) (Stack.shift 0 rest) body body' →
        MSubStar ({ bound := arg, kind := .equ } ::
          { bound := new, kind := .equ } :: Γ) (Stack.shift 0 rest) body body')
    (h : MSubRedStar ({ bound := old, kind := .equ } :: Γ) s u v) :
    MSubStar ({ bound := new, kind := .equ } :: Γ) s u v :=
  msubRedStar_replace_from_step_replacement
    (msubRed_equ_head_replace_from_replacements hpv hnew hEq hAppOpReplace
      hFunBoundReplace hFunBodyReplace hFOpBodyReplace)
    h

/-- Star-level subtype replacement when the changed `.equ` entry sits under
a preserved head. -/
theorem msubRedStar_equ_under_head_replace_from_replacements {Γ : Ctx} {s : Stack}
    {head : CtxEntry} {old new u v : Term}
    (hpv : PrevalidExt (head :: { bound := old, kind := .equ } :: Γ) s)
    (hnew : Term.Scoped Γ.depth new)
    (hEq :
      ∀ {u v : Term},
        MEqRed (head :: { bound := old, kind := .equ } :: Γ) s u v →
        MSubStar (head :: { bound := new, kind := .equ } :: Γ) s u v)
    (hAppOpReplace :
      ∀ {op op' arg : Term},
        MSubRed (head :: { bound := old, kind := .equ } :: Γ) (arg :: s) op op' →
        Term.Scoped (Ctx.depth (head :: { bound := old, kind := .equ } :: Γ)) arg →
        MSubStar (head :: { bound := new, kind := .equ } :: Γ) (arg :: s) op op')
    (hFunBoundReplace :
      ∀ {bound bound' : Term},
        MEqRed (head :: { bound := old, kind := .equ } :: Γ) [] bound bound' →
        MEqRed (head :: { bound := new, kind := .equ } :: Γ) [] bound bound')
    (hFunBodyReplace :
      ∀ {bound body body' : Term},
        MSubRed ({ bound := bound, kind := .sub } :: head ::
          { bound := old, kind := .equ } :: Γ) [] body body' →
        MSubRed ({ bound := bound, kind := .sub } :: head ::
          { bound := new, kind := .equ } :: Γ) [] body body')
    (hFOpBodyReplace :
      ∀ {arg body body' : Term} {rest : Stack},
        Term.Scoped (Ctx.depth (head :: { bound := old, kind := .equ } :: Γ)) arg →
        s = arg :: rest →
        MSubRed ({ bound := arg, kind := .equ } :: head ::
          { bound := old, kind := .equ } :: Γ) (Stack.shift 0 rest) body body' →
        MSubStar ({ bound := arg, kind := .equ } :: head ::
          { bound := new, kind := .equ } :: Γ) (Stack.shift 0 rest) body body')
    (h : MSubRedStar (head :: { bound := old, kind := .equ } :: Γ) s u v) :
    MSubStar (head :: { bound := new, kind := .equ } :: Γ) s u v :=
  msubRedStar_replace_from_step_replacement
    (msubRed_equ_under_head_replace_from_replacements hpv hnew hEq hAppOpReplace
      hFunBoundReplace hFunBodyReplace hFOpBodyReplace)
    h

/-- Function-valued star-level subtype replacement across an innermost
changed `.equ` head. This packages the unshifted subtype replacement wrapper
for every residual stack. -/
theorem msubRedStar_equ_head_replace_function_from_replacements {Γ : Ctx}
    {old new u v : Term}
    (hnew : Term.Scoped Γ.depth new)
    (hEq :
      ∀ {s : Stack},
        PrevalidExt ({ bound := old, kind := .equ } :: Γ) s →
        ∀ {u v : Term},
          MEqRed ({ bound := old, kind := .equ } :: Γ) s u v →
          MSubStar ({ bound := new, kind := .equ } :: Γ) s u v)
    (hAppOpReplace :
      ∀ {s : Stack},
        PrevalidExt ({ bound := old, kind := .equ } :: Γ) s →
        ∀ {op op' arg : Term},
          MSubRed ({ bound := old, kind := .equ } :: Γ) (arg :: s) op op' →
          Term.Scoped (Ctx.depth ({ bound := old, kind := .equ } :: Γ)) arg →
          MSubStar ({ bound := new, kind := .equ } :: Γ) (arg :: s) op op')
    (hFunBoundReplace :
      ∀ {bound bound' : Term},
        MEqRed ({ bound := old, kind := .equ } :: Γ) [] bound bound' →
        MEqRed ({ bound := new, kind := .equ } :: Γ) [] bound bound')
    (hFunBodyReplace :
      ∀ {bound body body' : Term},
        MSubRed ({ bound := bound, kind := .sub } ::
          { bound := old, kind := .equ } :: Γ) [] body body' →
        MSubRed ({ bound := bound, kind := .sub } ::
          { bound := new, kind := .equ } :: Γ) [] body body')
    (hFOpBodyReplace :
      ∀ {s : Stack},
        PrevalidExt ({ bound := old, kind := .equ } :: Γ) s →
        ∀ {arg body body' : Term} {rest : Stack},
          Term.Scoped (Ctx.depth ({ bound := old, kind := .equ } :: Γ)) arg →
          s = arg :: rest →
          MSubRed ({ bound := arg, kind := .equ } ::
            { bound := old, kind := .equ } :: Γ) (Stack.shift 0 rest) body body' →
          MSubStar ({ bound := arg, kind := .equ } ::
            { bound := new, kind := .equ } :: Γ) (Stack.shift 0 rest) body body')
    (h :
      ∀ {s : Stack},
        PrevalidExt ({ bound := old, kind := .equ } :: Γ) s →
        MSubRedStar ({ bound := old, kind := .equ } :: Γ) s u v) :
    ∀ {s : Stack},
      PrevalidExt ({ bound := old, kind := .equ } :: Γ) s →
      MSubStar ({ bound := new, kind := .equ } :: Γ) s u v :=
  fun hpv =>
    msubRedStar_equ_head_replace_from_replacements hpv hnew (hEq hpv)
      (hAppOpReplace hpv) hFunBoundReplace hFunBodyReplace
      (hFOpBodyReplace hpv) (h hpv)

/-- Function-valued star-level subtype replacement when the changed `.equ`
entry sits under a preserved head. This packages the unshifted under-head
subtype replacement wrapper for every residual stack. -/
theorem msubRedStar_equ_under_head_replace_function_from_replacements {Γ : Ctx}
    {head : CtxEntry} {old new u v : Term}
    (hnew : Term.Scoped Γ.depth new)
    (hEq :
      ∀ {s : Stack},
        PrevalidExt (head :: { bound := old, kind := .equ } :: Γ) s →
        ∀ {u v : Term},
          MEqRed (head :: { bound := old, kind := .equ } :: Γ) s u v →
          MSubStar (head :: { bound := new, kind := .equ } :: Γ) s u v)
    (hAppOpReplace :
      ∀ {s : Stack},
        PrevalidExt (head :: { bound := old, kind := .equ } :: Γ) s →
        ∀ {op op' arg : Term},
          MSubRed (head :: { bound := old, kind := .equ } :: Γ) (arg :: s) op op' →
          Term.Scoped (Ctx.depth (head :: { bound := old, kind := .equ } :: Γ)) arg →
          MSubStar (head :: { bound := new, kind := .equ } :: Γ) (arg :: s) op op')
    (hFunBoundReplace :
      ∀ {bound bound' : Term},
        MEqRed (head :: { bound := old, kind := .equ } :: Γ) [] bound bound' →
        MEqRed (head :: { bound := new, kind := .equ } :: Γ) [] bound bound')
    (hFunBodyReplace :
      ∀ {bound body body' : Term},
        MSubRed ({ bound := bound, kind := .sub } :: head ::
          { bound := old, kind := .equ } :: Γ) [] body body' →
        MSubRed ({ bound := bound, kind := .sub } :: head ::
          { bound := new, kind := .equ } :: Γ) [] body body')
    (hFOpBodyReplace :
      ∀ {s : Stack},
        PrevalidExt (head :: { bound := old, kind := .equ } :: Γ) s →
        ∀ {arg body body' : Term} {rest : Stack},
          Term.Scoped (Ctx.depth (head :: { bound := old, kind := .equ } :: Γ)) arg →
          s = arg :: rest →
          MSubRed ({ bound := arg, kind := .equ } :: head ::
            { bound := old, kind := .equ } :: Γ) (Stack.shift 0 rest) body body' →
          MSubStar ({ bound := arg, kind := .equ } :: head ::
            { bound := new, kind := .equ } :: Γ) (Stack.shift 0 rest) body body')
    (h :
      ∀ {s : Stack},
        PrevalidExt (head :: { bound := old, kind := .equ } :: Γ) s →
        MSubRedStar (head :: { bound := old, kind := .equ } :: Γ) s u v) :
    ∀ {s : Stack},
      PrevalidExt (head :: { bound := old, kind := .equ } :: Γ) s →
      MSubStar (head :: { bound := new, kind := .equ } :: Γ) s u v :=
  fun hpv =>
    msubRedStar_equ_under_head_replace_from_replacements hpv hnew (hEq hpv)
      (hAppOpReplace hpv) hFunBoundReplace hFunBodyReplace
      (hFOpBodyReplace hpv) (h hpv)

/-- Star-level equivalence replacement across an innermost changed `.equ`
head, obtained by composing the one-step equivalence replacement wrapper over
an equivalence-reduction chain. -/
theorem meqRedStar_equ_head_replace_from_replacements {Γ : Ctx} {s : Stack}
    {old new u v : Term}
    (hpv : PrevalidExt ({ bound := old, kind := .equ } :: Γ) s)
    (hnew : Term.Scoped Γ.depth new)
    (hProHead :
      ∀ {target : Term},
        MEqRed ({ bound := old, kind := .equ } :: Γ) s
          (Term.shift 0 old) target →
        MSubStar ({ bound := new, kind := .equ } :: Γ) s (.bvar 0) target)
    (hProTail :
      ∀ {i : Nat} {α α' : Term},
        Ctx.equBinds ({ bound := old, kind := .equ } :: Γ) (i + 1) α →
        MEqRed ({ bound := old, kind := .equ } :: Γ) s α α' →
        MSubStar ({ bound := new, kind := .equ } :: Γ) s (.bvar (i + 1)) α')
    (hAppOpReplace :
      ∀ {op op' arg : Term},
        MEqRed ({ bound := old, kind := .equ } :: Γ) (arg :: s) op op' →
        MEqRed ({ bound := new, kind := .equ } :: Γ) (arg :: s) op op')
    (hNilReplace :
      ∀ {arg arg' : Term},
        MEqRed ({ bound := old, kind := .equ } :: Γ) [] arg arg' →
        MEqRed ({ bound := new, kind := .equ } :: Γ) [] arg arg')
    (hFunBodyReplace :
      ∀ {bound body body' : Term},
        MEqRed ({ bound := bound, kind := .sub } ::
          { bound := old, kind := .equ } :: Γ) [] body body' →
        MEqRed ({ bound := bound, kind := .sub } ::
          { bound := new, kind := .equ } :: Γ) [] body body')
    (hBetBodyReplace :
      ∀ {bound body body' : Term},
        MEqRed ({ bound := bound, kind := .sub } ::
          { bound := old, kind := .equ } :: Γ) (Stack.shift 0 s) body body' →
        MEqRed ({ bound := bound, kind := .sub } ::
          { bound := new, kind := .equ } :: Γ) (Stack.shift 0 s) body body')
    (hFOpBodyReplace :
      ∀ {arg body body' : Term} {rest : Stack},
        Term.Scoped (Ctx.depth ({ bound := old, kind := .equ } :: Γ)) arg →
        s = arg :: rest →
        MEqRed ({ bound := arg, kind := .equ } ::
          { bound := old, kind := .equ } :: Γ) (Stack.shift 0 rest) body body' →
        MSubStar ({ bound := arg, kind := .equ } ::
          { bound := new, kind := .equ } :: Γ) (Stack.shift 0 rest) body body')
    (h : MEqRedStar ({ bound := old, kind := .equ } :: Γ) s u v) :
    MSubStar ({ bound := new, kind := .equ } :: Γ) s u v :=
  meqRedStar_replace_from_step_replacement
    (meqRed_equ_head_replace_from_replacements hpv hnew hProHead hProTail
      hAppOpReplace hNilReplace hFunBodyReplace hBetBodyReplace hFOpBodyReplace)
    h

/-- Star-level equivalence replacement when the changed `.equ` entry sits
immediately under a preserved head. -/
theorem meqRedStar_equ_under_head_replace_from_replacements {Γ : Ctx} {s : Stack}
    {head : CtxEntry} {old new u v : Term}
    (hpv : PrevalidExt (head :: { bound := old, kind := .equ } :: Γ) s)
    (hnew : Term.Scoped Γ.depth new)
    (hProZero :
      ∀ {α α' : Term},
        Ctx.equBinds (head :: { bound := old, kind := .equ } :: Γ) 0 α →
        MEqRed (head :: { bound := old, kind := .equ } :: Γ) s α α' →
        MSubStar (head :: { bound := new, kind := .equ } :: Γ) s (.bvar 0) α')
    (hProOne :
      ∀ {target : Term},
        MEqRed (head :: { bound := old, kind := .equ } :: Γ) s
          (Term.shift 0 (Term.shift 0 old)) target →
        MSubStar (head :: { bound := new, kind := .equ } :: Γ) s (.bvar 1) target)
    (hProTail :
      ∀ {i : Nat} {α α' : Term},
        Ctx.equBinds (head :: { bound := old, kind := .equ } :: Γ) ((i + 1) + 1) α →
        MEqRed (head :: { bound := old, kind := .equ } :: Γ) s α α' →
        MSubStar (head :: { bound := new, kind := .equ } :: Γ) s
          (.bvar ((i + 1) + 1)) α')
    (hAppOpReplace :
      ∀ {op op' arg : Term},
        MEqRed (head :: { bound := old, kind := .equ } :: Γ) (arg :: s) op op' →
        MEqRed (head :: { bound := new, kind := .equ } :: Γ) (arg :: s) op op')
    (hNilReplace :
      ∀ {arg arg' : Term},
        MEqRed (head :: { bound := old, kind := .equ } :: Γ) [] arg arg' →
        MEqRed (head :: { bound := new, kind := .equ } :: Γ) [] arg arg')
    (hFunBodyReplace :
      ∀ {bound body body' : Term},
        MEqRed ({ bound := bound, kind := .sub } :: head ::
          { bound := old, kind := .equ } :: Γ) [] body body' →
        MEqRed ({ bound := bound, kind := .sub } :: head ::
          { bound := new, kind := .equ } :: Γ) [] body body')
    (hBetBodyReplace :
      ∀ {bound body body' : Term},
        MEqRed ({ bound := bound, kind := .sub } :: head ::
          { bound := old, kind := .equ } :: Γ) (Stack.shift 0 s) body body' →
        MEqRed ({ bound := bound, kind := .sub } :: head ::
          { bound := new, kind := .equ } :: Γ) (Stack.shift 0 s) body body')
    (hFOpBodyReplace :
      ∀ {arg body body' : Term} {rest : Stack},
        Term.Scoped (Ctx.depth (head :: { bound := old, kind := .equ } :: Γ)) arg →
        s = arg :: rest →
        MEqRed ({ bound := arg, kind := .equ } :: head ::
          { bound := old, kind := .equ } :: Γ) (Stack.shift 0 rest) body body' →
        MSubStar ({ bound := arg, kind := .equ } :: head ::
          { bound := new, kind := .equ } :: Γ) (Stack.shift 0 rest) body body')
    (h : MEqRedStar (head :: { bound := old, kind := .equ } :: Γ) s u v) :
    MSubStar (head :: { bound := new, kind := .equ } :: Γ) s u v :=
  meqRedStar_replace_from_step_replacement
    (meqRed_equ_under_head_replace_from_replacements hpv hnew hProZero hProOne
      hProTail hAppOpReplace hNilReplace hFunBodyReplace hBetBodyReplace
      hFOpBodyReplace)
    h

/-- Function-valued star-level equivalence replacement across an innermost
changed `.equ` head. This packages the unshifted equivalence replacement
wrapper for every residual stack. -/
theorem meqRedStar_equ_head_replace_function_from_replacements {Γ : Ctx}
    {old new u v : Term}
    (hnew : Term.Scoped Γ.depth new)
    (hProHead :
      ∀ {s : Stack},
        PrevalidExt ({ bound := old, kind := .equ } :: Γ) s →
        ∀ {target : Term},
          MEqRed ({ bound := old, kind := .equ } :: Γ) s
            (Term.shift 0 old) target →
          MSubStar ({ bound := new, kind := .equ } :: Γ) s (.bvar 0) target)
    (hProTail :
      ∀ {s : Stack},
        PrevalidExt ({ bound := old, kind := .equ } :: Γ) s →
        ∀ {i : Nat} {α α' : Term},
          Ctx.equBinds ({ bound := old, kind := .equ } :: Γ) (i + 1) α →
          MEqRed ({ bound := old, kind := .equ } :: Γ) s α α' →
          MSubStar ({ bound := new, kind := .equ } :: Γ) s (.bvar (i + 1)) α')
    (hAppOpReplace :
      ∀ {s : Stack},
        PrevalidExt ({ bound := old, kind := .equ } :: Γ) s →
        ∀ {op op' arg : Term},
          MEqRed ({ bound := old, kind := .equ } :: Γ) (arg :: s) op op' →
          MEqRed ({ bound := new, kind := .equ } :: Γ) (arg :: s) op op')
    (hNilReplace :
      ∀ {arg arg' : Term},
        MEqRed ({ bound := old, kind := .equ } :: Γ) [] arg arg' →
        MEqRed ({ bound := new, kind := .equ } :: Γ) [] arg arg')
    (hFunBodyReplace :
      ∀ {bound body body' : Term},
        MEqRed ({ bound := bound, kind := .sub } ::
          { bound := old, kind := .equ } :: Γ) [] body body' →
        MEqRed ({ bound := bound, kind := .sub } ::
          { bound := new, kind := .equ } :: Γ) [] body body')
    (hBetBodyReplace :
      ∀ {s : Stack},
        PrevalidExt ({ bound := old, kind := .equ } :: Γ) s →
        ∀ {bound body body' : Term},
          MEqRed ({ bound := bound, kind := .sub } ::
            { bound := old, kind := .equ } :: Γ) (Stack.shift 0 s) body body' →
          MEqRed ({ bound := bound, kind := .sub } ::
            { bound := new, kind := .equ } :: Γ) (Stack.shift 0 s) body body')
    (hFOpBodyReplace :
      ∀ {s : Stack},
        PrevalidExt ({ bound := old, kind := .equ } :: Γ) s →
        ∀ {arg body body' : Term} {rest : Stack},
          Term.Scoped (Ctx.depth ({ bound := old, kind := .equ } :: Γ)) arg →
          s = arg :: rest →
          MEqRed ({ bound := arg, kind := .equ } ::
            { bound := old, kind := .equ } :: Γ) (Stack.shift 0 rest) body body' →
          MSubStar ({ bound := arg, kind := .equ } ::
            { bound := new, kind := .equ } :: Γ) (Stack.shift 0 rest) body body')
    (h :
      ∀ {s : Stack},
        PrevalidExt ({ bound := old, kind := .equ } :: Γ) s →
        MEqRedStar ({ bound := old, kind := .equ } :: Γ) s u v) :
    ∀ {s : Stack},
      PrevalidExt ({ bound := old, kind := .equ } :: Γ) s →
      MSubStar ({ bound := new, kind := .equ } :: Γ) s u v :=
  fun hpv =>
    meqRedStar_equ_head_replace_from_replacements hpv hnew (hProHead hpv)
      (hProTail hpv) (hAppOpReplace hpv) hNilReplace hFunBodyReplace
      (hBetBodyReplace hpv) (hFOpBodyReplace hpv) (h hpv)

/-- Function-valued star-level equivalence replacement when the changed
`.equ` entry sits immediately under a preserved head. This packages the
unshifted under-head equivalence wrapper for every residual stack. -/
theorem meqRedStar_equ_under_head_replace_function_from_replacements {Γ : Ctx}
    {head : CtxEntry} {old new u v : Term}
    (hnew : Term.Scoped Γ.depth new)
    (hProZero :
      ∀ {s : Stack},
        PrevalidExt (head :: { bound := old, kind := .equ } :: Γ) s →
        ∀ {α α' : Term},
          Ctx.equBinds (head :: { bound := old, kind := .equ } :: Γ) 0 α →
          MEqRed (head :: { bound := old, kind := .equ } :: Γ) s α α' →
          MSubStar (head :: { bound := new, kind := .equ } :: Γ) s (.bvar 0) α')
    (hProOne :
      ∀ {s : Stack},
        PrevalidExt (head :: { bound := old, kind := .equ } :: Γ) s →
        ∀ {target : Term},
          MEqRed (head :: { bound := old, kind := .equ } :: Γ) s
            (Term.shift 0 (Term.shift 0 old)) target →
          MSubStar (head :: { bound := new, kind := .equ } :: Γ) s
            (.bvar 1) target)
    (hProTail :
      ∀ {s : Stack},
        PrevalidExt (head :: { bound := old, kind := .equ } :: Γ) s →
        ∀ {i : Nat} {α α' : Term},
          Ctx.equBinds (head :: { bound := old, kind := .equ } :: Γ)
            ((i + 1) + 1) α →
          MEqRed (head :: { bound := old, kind := .equ } :: Γ) s α α' →
          MSubStar (head :: { bound := new, kind := .equ } :: Γ) s
            (.bvar ((i + 1) + 1)) α')
    (hAppOpReplace :
      ∀ {s : Stack},
        PrevalidExt (head :: { bound := old, kind := .equ } :: Γ) s →
        ∀ {op op' arg : Term},
          MEqRed (head :: { bound := old, kind := .equ } :: Γ) (arg :: s) op op' →
          MEqRed (head :: { bound := new, kind := .equ } :: Γ) (arg :: s) op op')
    (hNilReplace :
      ∀ {arg arg' : Term},
        MEqRed (head :: { bound := old, kind := .equ } :: Γ) [] arg arg' →
        MEqRed (head :: { bound := new, kind := .equ } :: Γ) [] arg arg')
    (hFunBodyReplace :
      ∀ {bound body body' : Term},
        MEqRed ({ bound := bound, kind := .sub } :: head ::
          { bound := old, kind := .equ } :: Γ) [] body body' →
        MEqRed ({ bound := bound, kind := .sub } :: head ::
          { bound := new, kind := .equ } :: Γ) [] body body')
    (hBetBodyReplace :
      ∀ {s : Stack},
        PrevalidExt (head :: { bound := old, kind := .equ } :: Γ) s →
        ∀ {bound body body' : Term},
          MEqRed ({ bound := bound, kind := .sub } :: head ::
            { bound := old, kind := .equ } :: Γ) (Stack.shift 0 s) body body' →
          MEqRed ({ bound := bound, kind := .sub } :: head ::
            { bound := new, kind := .equ } :: Γ) (Stack.shift 0 s) body body')
    (hFOpBodyReplace :
      ∀ {s : Stack},
        PrevalidExt (head :: { bound := old, kind := .equ } :: Γ) s →
        ∀ {arg body body' : Term} {rest : Stack},
          Term.Scoped (Ctx.depth (head :: { bound := old, kind := .equ } :: Γ)) arg →
          s = arg :: rest →
          MEqRed ({ bound := arg, kind := .equ } :: head ::
            { bound := old, kind := .equ } :: Γ) (Stack.shift 0 rest) body body' →
          MSubStar ({ bound := arg, kind := .equ } :: head ::
            { bound := new, kind := .equ } :: Γ) (Stack.shift 0 rest) body body')
    (h :
      ∀ {s : Stack},
        PrevalidExt (head :: { bound := old, kind := .equ } :: Γ) s →
        MEqRedStar (head :: { bound := old, kind := .equ } :: Γ) s u v) :
    ∀ {s : Stack},
      PrevalidExt (head :: { bound := old, kind := .equ } :: Γ) s →
      MSubStar (head :: { bound := new, kind := .equ } :: Γ) s u v :=
  fun hpv =>
    meqRedStar_equ_under_head_replace_from_replacements hpv hnew
      (hProZero hpv) (hProOne hpv) (hProTail hpv) (hAppOpReplace hpv)
      hNilReplace hFunBodyReplace (hBetBodyReplace hpv) (hFOpBodyReplace hpv)
      (h hpv)

/-- Under a changed `.equ` head, the old shifted head bound diagrammatically
subtypes the new head variable. The subtype side uses an old-to-new head
equivalence at the same residual stack; the equivalence side promotes
`bvar 0` through the new `.equ` head. This isolates the remaining
stack-sensitive lift needed to use a top-level argument equivalence inside
arbitrary `FOp` body stacks. -/
theorem msub_equ_head_old_bound_to_new_bvar0 {Γ : Ctx} {s : Stack}
    {old new : Term}
    (hpvTail : PrevalidExt Γ s)
    (hNewScoped : Term.Scoped Γ.depth new)
    (hOldNewStack : MEqRed ({ bound := new, kind := .equ } :: Γ)
      (Stack.shift 0 s) (Term.shift 0 old) (Term.shift 0 new)) :
    MSub ({ bound := new, kind := .equ } :: Γ) (Stack.shift 0 s)
      (Term.shift 0 old) (.bvar 0) := by
  have hpvNewCtx : Prevalid ({ bound := new, kind := .equ } :: Γ) :=
    Prevalid.equ (PrevalidExt.ctx hpvTail) hNewScoped
  have hpvNew : PrevalidExt ({ bound := new, kind := .equ } :: Γ)
      (Stack.shift 0 s) :=
    PrevalidExt.weaken_head hpvTail hpvNewCtx
  have hNewRefl : MEqRed ({ bound := new, kind := .equ } :: Γ)
      (Stack.shift 0 s) (Term.shift 0 new) (Term.shift 0 new) :=
    MEqRed.refl hpvNew
      (Term.shift_scoped 0 Γ.depth new (Nat.zero_le _) hNewScoped)
  have hVarNew : MEqRed ({ bound := new, kind := .equ } :: Γ)
      (Stack.shift 0 s) (.bvar 0) (Term.shift 0 new) :=
    MEqRed.pro hpvNew (Ctx.equBinds_zero_self Γ new) hNewRefl
  exact MSub.intro
    (MSubRedStar.single (MSubRed.equ hpvNew hOldNewStack))
    (MEqRedStar.single hVarNew)

/-- Converse diagrammatic bridge for a changed `.equ` head: the new head
variable subtypes the old shifted head bound, using the new shifted bound as
the common reduct. -/
theorem msub_equ_head_new_bvar0_to_old_bound {Γ : Ctx} {s : Stack}
    {old new : Term}
    (hpvTail : PrevalidExt Γ s)
    (hNewScoped : Term.Scoped Γ.depth new)
    (hOldNewStack : MEqRed ({ bound := new, kind := .equ } :: Γ)
      (Stack.shift 0 s) (Term.shift 0 old) (Term.shift 0 new)) :
    MSub ({ bound := new, kind := .equ } :: Γ) (Stack.shift 0 s)
      (.bvar 0) (Term.shift 0 old) := by
  have hpvNewCtx : Prevalid ({ bound := new, kind := .equ } :: Γ) :=
    Prevalid.equ (PrevalidExt.ctx hpvTail) hNewScoped
  have hpvNew : PrevalidExt ({ bound := new, kind := .equ } :: Γ)
      (Stack.shift 0 s) :=
    PrevalidExt.weaken_head hpvTail hpvNewCtx
  have hNewRefl : MEqRed ({ bound := new, kind := .equ } :: Γ)
      (Stack.shift 0 s) (Term.shift 0 new) (Term.shift 0 new) :=
    MEqRed.refl hpvNew
      (Term.shift_scoped 0 Γ.depth new (Nat.zero_le _) hNewScoped)
  have hVarNew : MEqRed ({ bound := new, kind := .equ } :: Γ)
      (Stack.shift 0 s) (.bvar 0) (Term.shift 0 new) :=
    MEqRed.pro hpvNew (Ctx.equBinds_zero_self Γ new) hNewRefl
  exact MSub.intro
    (MSubRedStar.single (MSubRed.equ hpvNew hVarNew))
    (MEqRedStar.single hOldNewStack)

/-- Consume a head `Me-Pro` replacement residual by first joining the new
head variable back to the old shifted bound, then following a recursively
replaced residual chain from that old bound. -/
theorem msubStar_equ_head_new_bvar0_to_replaced_residual {Γ : Ctx} {s : Stack}
    {old new target : Term}
    (hpvTail : PrevalidExt Γ s)
    (hNewScoped : Term.Scoped Γ.depth new)
    (hOldNewStack : MEqRed ({ bound := new, kind := .equ } :: Γ)
      (Stack.shift 0 s) (Term.shift 0 old) (Term.shift 0 new))
    (hResidual : MSubStar ({ bound := new, kind := .equ } :: Γ)
      (Stack.shift 0 s) (Term.shift 0 old) target) :
    MSubStar ({ bound := new, kind := .equ } :: Γ) (Stack.shift 0 s)
      (.bvar 0) target :=
  MSubStar.trans
    (MSub.to_star
      (msub_equ_head_new_bvar0_to_old_bound hpvTail hNewScoped hOldNewStack))
    hResidual

/-- Canonical handler for the head `Me-Pro` replacement residual: replace the
old-bound residual recursively, then compose it with the converse head bridge.
-/
theorem meq_equ_head_pro_residual_handler_of_replacement {Γ : Ctx} {s : Stack}
    {old new : Term}
    (hpvTail : PrevalidExt Γ s)
    (hNewScoped : Term.Scoped Γ.depth new)
    (hOldNewStack : MEqRed ({ bound := new, kind := .equ } :: Γ)
      (Stack.shift 0 s) (Term.shift 0 old) (Term.shift 0 new))
    (hReplace :
      ∀ {target : Term},
        MEqRed ({ bound := old, kind := .equ } :: Γ) (Stack.shift 0 s)
          (Term.shift 0 old) target →
        MSubStar ({ bound := new, kind := .equ } :: Γ) (Stack.shift 0 s)
          (Term.shift 0 old) target)
    {target : Term}
    (hResidual : MEqRed ({ bound := old, kind := .equ } :: Γ) (Stack.shift 0 s)
      (Term.shift 0 old) target) :
    MSubStar ({ bound := new, kind := .equ } :: Γ) (Stack.shift 0 s)
      (.bvar 0) target :=
  msubStar_equ_head_new_bvar0_to_replaced_residual hpvTail hNewScoped
    hOldNewStack (hReplace hResidual)

/-- Canonical handler for non-head `Me-Pro` during innermost `.equ`
replacement: rebuild the shifted variable through the new head, then follow
the recursively replaced looked-up bound chain. -/
theorem meq_equ_head_pro_tail_handler_of_replacement {Γ : Ctx} {s : Stack}
    {old new : Term}
    (hpv : PrevalidExt ({ bound := old, kind := .equ } :: Γ) s)
    (hNewScoped : Term.Scoped Γ.depth new)
    (hReplace :
      ∀ {α α' : Term},
        MEqRed ({ bound := old, kind := .equ } :: Γ) s α α' →
        MSubStar ({ bound := new, kind := .equ } :: Γ) s α α')
    {i : Nat} {α α' : Term}
    (hb : Ctx.equBinds ({ bound := old, kind := .equ } :: Γ) (i + 1) α)
    (hα : MEqRed ({ bound := old, kind := .equ } :: Γ) s α α') :
    MSubStar ({ bound := new, kind := .equ } :: Γ) s (.bvar (i + 1)) α' :=
  MSubStar.trans
    (MSubStar.of_MEqRed (PrevalidExt.equ_head_replace hpv hNewScoped)
      (MEqRed.pro_equ_head_replace_succ hpv hNewScoped hb
        (MEqRed.refl (PrevalidExt.equ_head_replace hpv hNewScoped)
          hα.scoped_left)))
    (hReplace hα)

/-- One-step equivalence replacement across a changed `.equ` head at a
shifted residual stack. This wires the canonical head `Me-Pro` residual and
non-head `Me-Pro` handlers; the remaining premises are the constructor
recursive replacements. -/
theorem meqRed_equ_head_shifted_replace_from_replacements {Γ : Ctx} {s : Stack}
    {old new u v : Term}
    (hpvTail : PrevalidExt Γ s)
    (hOldScoped : Term.Scoped Γ.depth old)
    (hnew : Term.Scoped Γ.depth new)
    (hOldNewStack : MEqRed ({ bound := new, kind := .equ } :: Γ)
      (Stack.shift 0 s) (Term.shift 0 old) (Term.shift 0 new))
    (hSelfReplace :
      ∀ {u v : Term},
        MEqRed ({ bound := old, kind := .equ } :: Γ) (Stack.shift 0 s) u v →
        MSubStar ({ bound := new, kind := .equ } :: Γ) (Stack.shift 0 s) u v)
    (hAppOpReplace :
      ∀ {op op' arg : Term},
        MEqRed ({ bound := old, kind := .equ } :: Γ)
          (arg :: Stack.shift 0 s) op op' →
        MEqRed ({ bound := new, kind := .equ } :: Γ)
          (arg :: Stack.shift 0 s) op op')
    (hNilReplace :
      ∀ {arg arg' : Term},
        MEqRed ({ bound := old, kind := .equ } :: Γ) [] arg arg' →
        MEqRed ({ bound := new, kind := .equ } :: Γ) [] arg arg')
    (hFunBodyReplace :
      ∀ {bound body body' : Term},
        MEqRed ({ bound := bound, kind := .sub } ::
          { bound := old, kind := .equ } :: Γ) [] body body' →
        MEqRed ({ bound := bound, kind := .sub } ::
          { bound := new, kind := .equ } :: Γ) [] body body')
    (hBetBodyReplace :
      ∀ {bound body body' : Term},
        MEqRed ({ bound := bound, kind := .sub } ::
          { bound := old, kind := .equ } :: Γ) (Stack.shift 0 (Stack.shift 0 s))
          body body' →
        MEqRed ({ bound := bound, kind := .sub } ::
          { bound := new, kind := .equ } :: Γ) (Stack.shift 0 (Stack.shift 0 s))
          body body')
    (hFOpBodyReplace :
      ∀ {arg body body' : Term} {rest : Stack},
        Term.Scoped (Ctx.depth ({ bound := old, kind := .equ } :: Γ)) arg →
        Stack.shift 0 s = arg :: rest →
        MEqRed ({ bound := arg, kind := .equ } ::
          { bound := old, kind := .equ } :: Γ) (Stack.shift 0 rest) body body' →
        MSubStar ({ bound := arg, kind := .equ } ::
          { bound := new, kind := .equ } :: Γ) (Stack.shift 0 rest) body body')
    (h : MEqRed ({ bound := old, kind := .equ } :: Γ) (Stack.shift 0 s) u v) :
    MSubStar ({ bound := new, kind := .equ } :: Γ) (Stack.shift 0 s) u v := by
  have hpv : PrevalidExt ({ bound := old, kind := .equ } :: Γ) (Stack.shift 0 s) := by
    have hpvOldCtx : Prevalid ({ bound := old, kind := .equ } :: Γ) :=
      Prevalid.equ (PrevalidExt.ctx hpvTail) hOldScoped
    exact PrevalidExt.weaken_head hpvTail hpvOldCtx
  exact meqRed_equ_head_replace_from_replacements hpv hnew
    (meq_equ_head_pro_residual_handler_of_replacement hpvTail hnew hOldNewStack
      (fun hResidual => hSelfReplace hResidual))
    (meq_equ_head_pro_tail_handler_of_replacement hpv hnew
      (fun hα => hSelfReplace hα))
    hAppOpReplace hNilReplace hFunBodyReplace hBetBodyReplace hFOpBodyReplace h

/-- Star-level shifted-stack equivalence replacement across a changed `.equ`
head, with the canonical `Me-Pro` handlers wired at each step. -/
theorem meqRedStar_equ_head_shifted_replace_from_replacements {Γ : Ctx} {s : Stack}
    {old new u v : Term}
    (hpvTail : PrevalidExt Γ s)
    (hOldScoped : Term.Scoped Γ.depth old)
    (hnew : Term.Scoped Γ.depth new)
    (hOldNewStack : MEqRed ({ bound := new, kind := .equ } :: Γ)
      (Stack.shift 0 s) (Term.shift 0 old) (Term.shift 0 new))
    (hSelfReplace :
      ∀ {u v : Term},
        MEqRed ({ bound := old, kind := .equ } :: Γ) (Stack.shift 0 s) u v →
        MSubStar ({ bound := new, kind := .equ } :: Γ) (Stack.shift 0 s) u v)
    (hAppOpReplace :
      ∀ {op op' arg : Term},
        MEqRed ({ bound := old, kind := .equ } :: Γ)
          (arg :: Stack.shift 0 s) op op' →
        MEqRed ({ bound := new, kind := .equ } :: Γ)
          (arg :: Stack.shift 0 s) op op')
    (hNilReplace :
      ∀ {arg arg' : Term},
        MEqRed ({ bound := old, kind := .equ } :: Γ) [] arg arg' →
        MEqRed ({ bound := new, kind := .equ } :: Γ) [] arg arg')
    (hFunBodyReplace :
      ∀ {bound body body' : Term},
        MEqRed ({ bound := bound, kind := .sub } ::
          { bound := old, kind := .equ } :: Γ) [] body body' →
        MEqRed ({ bound := bound, kind := .sub } ::
          { bound := new, kind := .equ } :: Γ) [] body body')
    (hBetBodyReplace :
      ∀ {bound body body' : Term},
        MEqRed ({ bound := bound, kind := .sub } ::
          { bound := old, kind := .equ } :: Γ) (Stack.shift 0 (Stack.shift 0 s))
          body body' →
        MEqRed ({ bound := bound, kind := .sub } ::
          { bound := new, kind := .equ } :: Γ) (Stack.shift 0 (Stack.shift 0 s))
          body body')
    (hFOpBodyReplace :
      ∀ {arg body body' : Term} {rest : Stack},
        Term.Scoped (Ctx.depth ({ bound := old, kind := .equ } :: Γ)) arg →
        Stack.shift 0 s = arg :: rest →
        MEqRed ({ bound := arg, kind := .equ } ::
          { bound := old, kind := .equ } :: Γ) (Stack.shift 0 rest) body body' →
        MSubStar ({ bound := arg, kind := .equ } ::
          { bound := new, kind := .equ } :: Γ) (Stack.shift 0 rest) body body')
    (h : MEqRedStar ({ bound := old, kind := .equ } :: Γ) (Stack.shift 0 s) u v) :
    MSubStar ({ bound := new, kind := .equ } :: Γ) (Stack.shift 0 s) u v :=
  meqRedStar_replace_from_step_replacement
    (meqRed_equ_head_shifted_replace_from_replacements hpvTail hOldScoped hnew
      hOldNewStack hSelfReplace hAppOpReplace hNilReplace hFunBodyReplace
      hBetBodyReplace hFOpBodyReplace)
    h

/-- Function-valued shifted-stack equivalence replacement across a changed
`.equ` head. This packages the star-level shifted replacement for every
tail stack. -/
theorem meqRedStar_equ_head_shifted_replace_function_from_replacements {Γ : Ctx}
    {old new u v : Term}
    (hOldScoped : Term.Scoped Γ.depth old)
    (hnew : Term.Scoped Γ.depth new)
    (hOldNewStack :
      ∀ {s : Stack},
        PrevalidExt Γ s →
        MEqRed ({ bound := new, kind := .equ } :: Γ)
          (Stack.shift 0 s) (Term.shift 0 old) (Term.shift 0 new))
    (hSelfReplace :
      ∀ {s : Stack},
        PrevalidExt Γ s →
        ∀ {u v : Term},
          MEqRed ({ bound := old, kind := .equ } :: Γ) (Stack.shift 0 s) u v →
          MSubStar ({ bound := new, kind := .equ } :: Γ) (Stack.shift 0 s) u v)
    (hAppOpReplace :
      ∀ {s : Stack},
        PrevalidExt Γ s →
        ∀ {op op' arg : Term},
          MEqRed ({ bound := old, kind := .equ } :: Γ)
            (arg :: Stack.shift 0 s) op op' →
          MEqRed ({ bound := new, kind := .equ } :: Γ)
            (arg :: Stack.shift 0 s) op op')
    (hNilReplace :
      ∀ {arg arg' : Term},
        MEqRed ({ bound := old, kind := .equ } :: Γ) [] arg arg' →
        MEqRed ({ bound := new, kind := .equ } :: Γ) [] arg arg')
    (hFunBodyReplace :
      ∀ {bound body body' : Term},
        MEqRed ({ bound := bound, kind := .sub } ::
          { bound := old, kind := .equ } :: Γ) [] body body' →
        MEqRed ({ bound := bound, kind := .sub } ::
          { bound := new, kind := .equ } :: Γ) [] body body')
    (hBetBodyReplace :
      ∀ {s : Stack},
        PrevalidExt Γ s →
        ∀ {bound body body' : Term},
          MEqRed ({ bound := bound, kind := .sub } ::
            { bound := old, kind := .equ } :: Γ) (Stack.shift 0 (Stack.shift 0 s))
            body body' →
          MEqRed ({ bound := bound, kind := .sub } ::
            { bound := new, kind := .equ } :: Γ) (Stack.shift 0 (Stack.shift 0 s))
            body body')
    (hFOpBodyReplace :
      ∀ {s : Stack},
        PrevalidExt Γ s →
        ∀ {arg body body' : Term} {rest : Stack},
          Term.Scoped (Ctx.depth ({ bound := old, kind := .equ } :: Γ)) arg →
          Stack.shift 0 s = arg :: rest →
          MEqRed ({ bound := arg, kind := .equ } ::
            { bound := old, kind := .equ } :: Γ) (Stack.shift 0 rest) body body' →
          MSubStar ({ bound := arg, kind := .equ } ::
            { bound := new, kind := .equ } :: Γ) (Stack.shift 0 rest) body body')
    (h :
      ∀ {s : Stack},
        PrevalidExt Γ s →
        MEqRedStar ({ bound := old, kind := .equ } :: Γ)
          (Stack.shift 0 s) u v) :
    ∀ {s : Stack},
      PrevalidExt Γ s →
      MSubStar ({ bound := new, kind := .equ } :: Γ) (Stack.shift 0 s) u v :=
  fun hpvTail =>
    meqRedStar_equ_head_shifted_replace_from_replacements hpvTail hOldScoped
      hnew (hOldNewStack hpvTail) (hSelfReplace hpvTail)
      (hAppOpReplace hpvTail) hNilReplace hFunBodyReplace
      (hBetBodyReplace hpvTail) (hFOpBodyReplace hpvTail) (h hpvTail)

/-- One-step subtype replacement across a changed `.equ` head at a shifted
residual stack. The `Ms-Equ` branch is handled by the shifted equivalence
replacement package, so callers only supply recursive constructor
replacements. -/
theorem msubRed_equ_head_shifted_replace_from_replacements {Γ : Ctx} {s : Stack}
    {old new u v : Term}
    (hpvTail : PrevalidExt Γ s)
    (hOldScoped : Term.Scoped Γ.depth old)
    (hnew : Term.Scoped Γ.depth new)
    (hOldNewStack : MEqRed ({ bound := new, kind := .equ } :: Γ)
      (Stack.shift 0 s) (Term.shift 0 old) (Term.shift 0 new))
    (hEqSelfReplace :
      ∀ {u v : Term},
        MEqRed ({ bound := old, kind := .equ } :: Γ) (Stack.shift 0 s) u v →
        MSubStar ({ bound := new, kind := .equ } :: Γ) (Stack.shift 0 s) u v)
    (hEqAppOpReplace :
      ∀ {op op' arg : Term},
        MEqRed ({ bound := old, kind := .equ } :: Γ)
          (arg :: Stack.shift 0 s) op op' →
        MEqRed ({ bound := new, kind := .equ } :: Γ)
          (arg :: Stack.shift 0 s) op op')
    (hNilReplace :
      ∀ {arg arg' : Term},
        MEqRed ({ bound := old, kind := .equ } :: Γ) [] arg arg' →
        MEqRed ({ bound := new, kind := .equ } :: Γ) [] arg arg')
    (hEqFunBodyReplace :
      ∀ {bound body body' : Term},
        MEqRed ({ bound := bound, kind := .sub } ::
          { bound := old, kind := .equ } :: Γ) [] body body' →
        MEqRed ({ bound := bound, kind := .sub } ::
          { bound := new, kind := .equ } :: Γ) [] body body')
    (hEqBetBodyReplace :
      ∀ {bound body body' : Term},
        MEqRed ({ bound := bound, kind := .sub } ::
          { bound := old, kind := .equ } :: Γ) (Stack.shift 0 (Stack.shift 0 s))
          body body' →
        MEqRed ({ bound := bound, kind := .sub } ::
          { bound := new, kind := .equ } :: Γ) (Stack.shift 0 (Stack.shift 0 s))
          body body')
    (hEqFOpBodyReplace :
      ∀ {arg body body' : Term} {rest : Stack},
        Term.Scoped (Ctx.depth ({ bound := old, kind := .equ } :: Γ)) arg →
        Stack.shift 0 s = arg :: rest →
        MEqRed ({ bound := arg, kind := .equ } ::
          { bound := old, kind := .equ } :: Γ) (Stack.shift 0 rest) body body' →
        MSubStar ({ bound := arg, kind := .equ } ::
          { bound := new, kind := .equ } :: Γ) (Stack.shift 0 rest) body body')
    (hAppOpReplace :
      ∀ {op op' arg : Term},
        MSubRed ({ bound := old, kind := .equ } :: Γ)
          (arg :: Stack.shift 0 s) op op' →
        Term.Scoped (Ctx.depth ({ bound := old, kind := .equ } :: Γ)) arg →
        MSubStar ({ bound := new, kind := .equ } :: Γ)
          (arg :: Stack.shift 0 s) op op')
    (hFunBodyReplace :
      ∀ {bound body body' : Term},
        MSubRed ({ bound := bound, kind := .sub } ::
          { bound := old, kind := .equ } :: Γ) [] body body' →
        MSubRed ({ bound := bound, kind := .sub } ::
          { bound := new, kind := .equ } :: Γ) [] body body')
    (hFOpBodyReplace :
      ∀ {arg body body' : Term} {rest : Stack},
        Term.Scoped (Ctx.depth ({ bound := old, kind := .equ } :: Γ)) arg →
        Stack.shift 0 s = arg :: rest →
        MSubRed ({ bound := arg, kind := .equ } ::
          { bound := old, kind := .equ } :: Γ) (Stack.shift 0 rest) body body' →
        MSubStar ({ bound := arg, kind := .equ } ::
          { bound := new, kind := .equ } :: Γ) (Stack.shift 0 rest) body body')
    (h : MSubRed ({ bound := old, kind := .equ } :: Γ) (Stack.shift 0 s) u v) :
    MSubStar ({ bound := new, kind := .equ } :: Γ) (Stack.shift 0 s) u v := by
  have hpv : PrevalidExt ({ bound := old, kind := .equ } :: Γ) (Stack.shift 0 s) := by
    have hpvOldCtx : Prevalid ({ bound := old, kind := .equ } :: Γ) :=
      Prevalid.equ (PrevalidExt.ctx hpvTail) hOldScoped
    exact PrevalidExt.weaken_head hpvTail hpvOldCtx
  exact msubRed_equ_head_replace_from_replacements hpv hnew
    (meqRed_equ_head_shifted_replace_from_replacements hpvTail hOldScoped hnew
      hOldNewStack hEqSelfReplace hEqAppOpReplace hNilReplace hEqFunBodyReplace
      hEqBetBodyReplace hEqFOpBodyReplace)
    hAppOpReplace hNilReplace hFunBodyReplace hFOpBodyReplace h

/-- Chain-level shifted-stack subtype replacement across a changed `.equ`
head, using the shifted equivalence package for every `Ms-Equ` step. -/
theorem msubRedStar_equ_head_shifted_replace_from_replacements {Γ : Ctx}
    {s : Stack} {old new u v : Term}
    (hpvTail : PrevalidExt Γ s)
    (hOldScoped : Term.Scoped Γ.depth old)
    (hnew : Term.Scoped Γ.depth new)
    (hOldNewStack : MEqRed ({ bound := new, kind := .equ } :: Γ)
      (Stack.shift 0 s) (Term.shift 0 old) (Term.shift 0 new))
    (hEqSelfReplace :
      ∀ {u v : Term},
        MEqRed ({ bound := old, kind := .equ } :: Γ) (Stack.shift 0 s) u v →
        MSubStar ({ bound := new, kind := .equ } :: Γ) (Stack.shift 0 s) u v)
    (hEqAppOpReplace :
      ∀ {op op' arg : Term},
        MEqRed ({ bound := old, kind := .equ } :: Γ)
          (arg :: Stack.shift 0 s) op op' →
        MEqRed ({ bound := new, kind := .equ } :: Γ)
          (arg :: Stack.shift 0 s) op op')
    (hNilReplace :
      ∀ {arg arg' : Term},
        MEqRed ({ bound := old, kind := .equ } :: Γ) [] arg arg' →
        MEqRed ({ bound := new, kind := .equ } :: Γ) [] arg arg')
    (hEqFunBodyReplace :
      ∀ {bound body body' : Term},
        MEqRed ({ bound := bound, kind := .sub } ::
          { bound := old, kind := .equ } :: Γ) [] body body' →
        MEqRed ({ bound := bound, kind := .sub } ::
          { bound := new, kind := .equ } :: Γ) [] body body')
    (hEqBetBodyReplace :
      ∀ {bound body body' : Term},
        MEqRed ({ bound := bound, kind := .sub } ::
          { bound := old, kind := .equ } :: Γ) (Stack.shift 0 (Stack.shift 0 s))
          body body' →
        MEqRed ({ bound := bound, kind := .sub } ::
          { bound := new, kind := .equ } :: Γ) (Stack.shift 0 (Stack.shift 0 s))
          body body')
    (hEqFOpBodyReplace :
      ∀ {arg body body' : Term} {rest : Stack},
        Term.Scoped (Ctx.depth ({ bound := old, kind := .equ } :: Γ)) arg →
        Stack.shift 0 s = arg :: rest →
        MEqRed ({ bound := arg, kind := .equ } ::
          { bound := old, kind := .equ } :: Γ) (Stack.shift 0 rest) body body' →
        MSubStar ({ bound := arg, kind := .equ } ::
          { bound := new, kind := .equ } :: Γ) (Stack.shift 0 rest) body body')
    (hAppOpReplace :
      ∀ {op op' arg : Term},
        MSubRed ({ bound := old, kind := .equ } :: Γ)
          (arg :: Stack.shift 0 s) op op' →
        Term.Scoped (Ctx.depth ({ bound := old, kind := .equ } :: Γ)) arg →
        MSubStar ({ bound := new, kind := .equ } :: Γ)
          (arg :: Stack.shift 0 s) op op')
    (hFunBodyReplace :
      ∀ {bound body body' : Term},
        MSubRed ({ bound := bound, kind := .sub } ::
          { bound := old, kind := .equ } :: Γ) [] body body' →
        MSubRed ({ bound := bound, kind := .sub } ::
          { bound := new, kind := .equ } :: Γ) [] body body')
    (hFOpBodyReplace :
      ∀ {arg body body' : Term} {rest : Stack},
        Term.Scoped (Ctx.depth ({ bound := old, kind := .equ } :: Γ)) arg →
        Stack.shift 0 s = arg :: rest →
        MSubRed ({ bound := arg, kind := .equ } ::
          { bound := old, kind := .equ } :: Γ) (Stack.shift 0 rest) body body' →
        MSubStar ({ bound := arg, kind := .equ } ::
          { bound := new, kind := .equ } :: Γ) (Stack.shift 0 rest) body body')
    (h : MSubRedStar ({ bound := old, kind := .equ } :: Γ) (Stack.shift 0 s) u v) :
    MSubStar ({ bound := new, kind := .equ } :: Γ) (Stack.shift 0 s) u v :=
  msubRedStar_replace_from_step_replacement
    (msubRed_equ_head_shifted_replace_from_replacements hpvTail hOldScoped hnew
      hOldNewStack hEqSelfReplace hEqAppOpReplace hNilReplace hEqFunBodyReplace
      hEqBetBodyReplace hEqFOpBodyReplace hAppOpReplace hFunBodyReplace
      hFOpBodyReplace)
    h

/-- Function-valued shifted-stack subtype replacement across a changed
`.equ` head. This packages the chain-level subtype replacement for every
tail stack, using the shifted equivalence package for each `Ms-Equ` step. -/
theorem msubRedStar_equ_head_shifted_replace_function_from_replacements {Γ : Ctx}
    {old new u v : Term}
    (hOldScoped : Term.Scoped Γ.depth old)
    (hnew : Term.Scoped Γ.depth new)
    (hOldNewStack :
      ∀ {s : Stack},
        PrevalidExt Γ s →
        MEqRed ({ bound := new, kind := .equ } :: Γ)
          (Stack.shift 0 s) (Term.shift 0 old) (Term.shift 0 new))
    (hEqSelfReplace :
      ∀ {s : Stack},
        PrevalidExt Γ s →
        ∀ {u v : Term},
          MEqRed ({ bound := old, kind := .equ } :: Γ) (Stack.shift 0 s) u v →
          MSubStar ({ bound := new, kind := .equ } :: Γ) (Stack.shift 0 s) u v)
    (hEqAppOpReplace :
      ∀ {s : Stack},
        PrevalidExt Γ s →
        ∀ {op op' arg : Term},
          MEqRed ({ bound := old, kind := .equ } :: Γ)
            (arg :: Stack.shift 0 s) op op' →
          MEqRed ({ bound := new, kind := .equ } :: Γ)
            (arg :: Stack.shift 0 s) op op')
    (hNilReplace :
      ∀ {arg arg' : Term},
        MEqRed ({ bound := old, kind := .equ } :: Γ) [] arg arg' →
        MEqRed ({ bound := new, kind := .equ } :: Γ) [] arg arg')
    (hEqFunBodyReplace :
      ∀ {bound body body' : Term},
        MEqRed ({ bound := bound, kind := .sub } ::
          { bound := old, kind := .equ } :: Γ) [] body body' →
        MEqRed ({ bound := bound, kind := .sub } ::
          { bound := new, kind := .equ } :: Γ) [] body body')
    (hEqBetBodyReplace :
      ∀ {s : Stack},
        PrevalidExt Γ s →
        ∀ {bound body body' : Term},
          MEqRed ({ bound := bound, kind := .sub } ::
            { bound := old, kind := .equ } :: Γ) (Stack.shift 0 (Stack.shift 0 s))
            body body' →
          MEqRed ({ bound := bound, kind := .sub } ::
            { bound := new, kind := .equ } :: Γ) (Stack.shift 0 (Stack.shift 0 s))
            body body')
    (hEqFOpBodyReplace :
      ∀ {s : Stack},
        PrevalidExt Γ s →
        ∀ {arg body body' : Term} {rest : Stack},
          Term.Scoped (Ctx.depth ({ bound := old, kind := .equ } :: Γ)) arg →
          Stack.shift 0 s = arg :: rest →
          MEqRed ({ bound := arg, kind := .equ } ::
            { bound := old, kind := .equ } :: Γ) (Stack.shift 0 rest) body body' →
          MSubStar ({ bound := arg, kind := .equ } ::
            { bound := new, kind := .equ } :: Γ) (Stack.shift 0 rest) body body')
    (hAppOpReplace :
      ∀ {s : Stack},
        PrevalidExt Γ s →
        ∀ {op op' arg : Term},
          MSubRed ({ bound := old, kind := .equ } :: Γ)
            (arg :: Stack.shift 0 s) op op' →
          Term.Scoped (Ctx.depth ({ bound := old, kind := .equ } :: Γ)) arg →
          MSubStar ({ bound := new, kind := .equ } :: Γ)
            (arg :: Stack.shift 0 s) op op')
    (hFunBodyReplace :
      ∀ {bound body body' : Term},
        MSubRed ({ bound := bound, kind := .sub } ::
          { bound := old, kind := .equ } :: Γ) [] body body' →
        MSubRed ({ bound := bound, kind := .sub } ::
          { bound := new, kind := .equ } :: Γ) [] body body')
    (hFOpBodyReplace :
      ∀ {s : Stack},
        PrevalidExt Γ s →
        ∀ {arg body body' : Term} {rest : Stack},
          Term.Scoped (Ctx.depth ({ bound := old, kind := .equ } :: Γ)) arg →
          Stack.shift 0 s = arg :: rest →
          MSubRed ({ bound := arg, kind := .equ } ::
            { bound := old, kind := .equ } :: Γ) (Stack.shift 0 rest) body body' →
          MSubStar ({ bound := arg, kind := .equ } ::
            { bound := new, kind := .equ } :: Γ) (Stack.shift 0 rest) body body')
    (h :
      ∀ {s : Stack},
        PrevalidExt Γ s →
        MSubRedStar ({ bound := old, kind := .equ } :: Γ)
          (Stack.shift 0 s) u v) :
    ∀ {s : Stack},
      PrevalidExt Γ s →
      MSubStar ({ bound := new, kind := .equ } :: Γ) (Stack.shift 0 s) u v :=
  fun hpvTail =>
    msubRedStar_equ_head_shifted_replace_from_replacements hpvTail hOldScoped
      hnew (hOldNewStack hpvTail) (hEqSelfReplace hpvTail)
      (hEqAppOpReplace hpvTail) hNilReplace hEqFunBodyReplace
      (hEqBetBodyReplace hpvTail) (hEqFOpBodyReplace hpvTail)
      (hAppOpReplace hpvTail) hFunBodyReplace (hFOpBodyReplace hpvTail)
      (h hpvTail)

/-- Under a preserved head and changed `.equ` entry, the old shifted
under-head bound diagrammatically subtypes the new variable at index `1`.
This is the one-level-deeper analogue of
`msub_equ_head_old_bound_to_new_bvar0` for the residual exposed by
`MEqRed.pro_equ_under_head_one_residual`. -/
theorem msub_equ_under_head_old_bound_to_new_bvar1 {Γ : Ctx} {s : Stack}
    {head : CtxEntry} {old new : Term}
    (hpvNew : PrevalidExt (head :: { bound := new, kind := .equ } :: Γ) s)
    (hNewScoped : Term.Scoped Γ.depth new)
    (hOldNewStack : MEqRed (head :: { bound := new, kind := .equ } :: Γ) s
      (Term.shift 0 (Term.shift 0 old)) (Term.shift 0 (Term.shift 0 new))) :
    MSub (head :: { bound := new, kind := .equ } :: Γ) s
      (Term.shift 0 (Term.shift 0 old)) (.bvar 1) := by
  have hNewShiftScoped :
      Term.Scoped (Ctx.depth (head :: { bound := new, kind := .equ } :: Γ))
        (Term.shift 0 (Term.shift 0 new)) := by
    have hOnce : Term.Scoped (Γ.depth + 1) (Term.shift 0 new) :=
      Term.shift_scoped 0 Γ.depth new (Nat.zero_le _) hNewScoped
    have hTwice : Term.Scoped ((Γ.depth + 1) + 1)
        (Term.shift 0 (Term.shift 0 new)) :=
      Term.shift_scoped 0 (Γ.depth + 1) (Term.shift 0 new) (Nat.zero_le _) hOnce
    simpa [Ctx.depth, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hTwice
  have hNewRefl : MEqRed (head :: { bound := new, kind := .equ } :: Γ) s
      (Term.shift 0 (Term.shift 0 new)) (Term.shift 0 (Term.shift 0 new)) :=
    MEqRed.refl hpvNew hNewShiftScoped
  have hVarNew : MEqRed (head :: { bound := new, kind := .equ } :: Γ) s
      (.bvar 1) (Term.shift 0 (Term.shift 0 new)) :=
    MEqRed.pro hpvNew (by simp [Ctx.equBinds]) hNewRefl
  exact MSub.intro
    (MSubRedStar.single (MSubRed.equ hpvNew hOldNewStack))
    (MEqRedStar.single hVarNew)

/-- Converse under-head bridge: the new variable at index `1`
diagrammatically subtypes the old shifted under-head bound, again using the
new shifted under-head bound as the common reduct. -/
theorem msub_equ_under_head_new_bvar1_to_old_bound {Γ : Ctx} {s : Stack}
    {head : CtxEntry} {old new : Term}
    (hpvNew : PrevalidExt (head :: { bound := new, kind := .equ } :: Γ) s)
    (hNewScoped : Term.Scoped Γ.depth new)
    (hOldNewStack : MEqRed (head :: { bound := new, kind := .equ } :: Γ) s
      (Term.shift 0 (Term.shift 0 old)) (Term.shift 0 (Term.shift 0 new))) :
    MSub (head :: { bound := new, kind := .equ } :: Γ) s
      (.bvar 1) (Term.shift 0 (Term.shift 0 old)) := by
  have hNewShiftScoped :
      Term.Scoped (Ctx.depth (head :: { bound := new, kind := .equ } :: Γ))
        (Term.shift 0 (Term.shift 0 new)) := by
    have hOnce : Term.Scoped (Γ.depth + 1) (Term.shift 0 new) :=
      Term.shift_scoped 0 Γ.depth new (Nat.zero_le _) hNewScoped
    have hTwice : Term.Scoped ((Γ.depth + 1) + 1)
        (Term.shift 0 (Term.shift 0 new)) :=
      Term.shift_scoped 0 (Γ.depth + 1) (Term.shift 0 new) (Nat.zero_le _) hOnce
    simpa [Ctx.depth, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hTwice
  have hNewRefl : MEqRed (head :: { bound := new, kind := .equ } :: Γ) s
      (Term.shift 0 (Term.shift 0 new)) (Term.shift 0 (Term.shift 0 new)) :=
    MEqRed.refl hpvNew hNewShiftScoped
  have hVarNew : MEqRed (head :: { bound := new, kind := .equ } :: Γ) s
      (.bvar 1) (Term.shift 0 (Term.shift 0 new)) :=
    MEqRed.pro hpvNew (by simp [Ctx.equBinds]) hNewRefl
  exact MSub.intro
    (MSubRedStar.single (MSubRed.equ hpvNew hVarNew))
    (MEqRedStar.single hOldNewStack)

/-- Consume an under-head `Me-Pro` replacement residual by first joining the
new variable at index `1` back to the old doubly shifted bound, then following
a recursively replaced residual chain from that old bound. -/
theorem msubStar_equ_under_head_new_bvar1_to_replaced_residual {Γ : Ctx}
    {s : Stack} {head : CtxEntry} {old new target : Term}
    (hpvNew : PrevalidExt (head :: { bound := new, kind := .equ } :: Γ) s)
    (hNewScoped : Term.Scoped Γ.depth new)
    (hOldNewStack : MEqRed (head :: { bound := new, kind := .equ } :: Γ) s
      (Term.shift 0 (Term.shift 0 old)) (Term.shift 0 (Term.shift 0 new)))
    (hResidual : MSubStar (head :: { bound := new, kind := .equ } :: Γ) s
      (Term.shift 0 (Term.shift 0 old)) target) :
    MSubStar (head :: { bound := new, kind := .equ } :: Γ) s
      (.bvar 1) target :=
  MSubStar.trans
    (MSub.to_star
      (msub_equ_under_head_new_bvar1_to_old_bound hpvNew hNewScoped hOldNewStack))
    hResidual

/-- Canonical handler for the under-head `Me-Pro` replacement residual:
replace the old doubly shifted bound recursively, then compose it with the
converse under-head bridge. -/
theorem meq_equ_under_head_pro_residual_handler_of_replacement {Γ : Ctx}
    {s : Stack} {head : CtxEntry} {old new : Term}
    (hpvNew : PrevalidExt (head :: { bound := new, kind := .equ } :: Γ) s)
    (hNewScoped : Term.Scoped Γ.depth new)
    (hOldNewStack : MEqRed (head :: { bound := new, kind := .equ } :: Γ) s
      (Term.shift 0 (Term.shift 0 old)) (Term.shift 0 (Term.shift 0 new)))
    (hReplace :
      ∀ {target : Term},
        MEqRed (head :: { bound := old, kind := .equ } :: Γ) s
          (Term.shift 0 (Term.shift 0 old)) target →
        MSubStar (head :: { bound := new, kind := .equ } :: Γ) s
          (Term.shift 0 (Term.shift 0 old)) target)
    {target : Term}
    (hResidual : MEqRed (head :: { bound := old, kind := .equ } :: Γ) s
      (Term.shift 0 (Term.shift 0 old)) target) :
    MSubStar (head :: { bound := new, kind := .equ } :: Γ) s
      (.bvar 1) target :=
  msubStar_equ_under_head_new_bvar1_to_replaced_residual hpvNew hNewScoped
    hOldNewStack (hReplace hResidual)

/-- Canonical handler for preserved-head index `0` `Me-Pro` during under-head
`.equ` replacement. -/
theorem meq_equ_under_head_pro_zero_handler_of_replacement {Γ : Ctx} {s : Stack}
    {head : CtxEntry} {old new : Term}
    (hpv : PrevalidExt (head :: { bound := old, kind := .equ } :: Γ) s)
    (hNewScoped : Term.Scoped Γ.depth new)
    (hReplace :
      ∀ {α α' : Term},
        MEqRed (head :: { bound := old, kind := .equ } :: Γ) s α α' →
        MSubStar (head :: { bound := new, kind := .equ } :: Γ) s α α')
    {α α' : Term}
    (hb : Ctx.equBinds (head :: { bound := old, kind := .equ } :: Γ) 0 α)
    (hα : MEqRed (head :: { bound := old, kind := .equ } :: Γ) s α α') :
    MSubStar (head :: { bound := new, kind := .equ } :: Γ) s (.bvar 0) α' :=
  MSubStar.trans
    (MSubStar.of_MEqRed (PrevalidExt.equ_under_head_replace hpv hNewScoped)
      (MEqRed.pro_equ_under_head_replace_zero hpv hNewScoped hb
        (MEqRed.refl (PrevalidExt.equ_under_head_replace hpv hNewScoped)
          hα.scoped_left)))
    (hReplace hα)

/-- Canonical handler for non-residual indices `2+` of `Me-Pro` during
under-head `.equ` replacement. -/
theorem meq_equ_under_head_pro_tail_handler_of_replacement {Γ : Ctx} {s : Stack}
    {head : CtxEntry} {old new : Term}
    (hpv : PrevalidExt (head :: { bound := old, kind := .equ } :: Γ) s)
    (hNewScoped : Term.Scoped Γ.depth new)
    (hReplace :
      ∀ {α α' : Term},
        MEqRed (head :: { bound := old, kind := .equ } :: Γ) s α α' →
        MSubStar (head :: { bound := new, kind := .equ } :: Γ) s α α')
    {i : Nat} {α α' : Term}
    (hb : Ctx.equBinds (head :: { bound := old, kind := .equ } :: Γ)
      ((i + 1) + 1) α)
    (hα : MEqRed (head :: { bound := old, kind := .equ } :: Γ) s α α') :
    MSubStar (head :: { bound := new, kind := .equ } :: Γ) s
      (.bvar ((i + 1) + 1)) α' :=
  MSubStar.trans
    (MSubStar.of_MEqRed (PrevalidExt.equ_under_head_replace hpv hNewScoped)
      (MEqRed.pro_equ_under_head_replace_succ_succ hpv hNewScoped hb
      (MEqRed.refl (PrevalidExt.equ_under_head_replace hpv hNewScoped)
          hα.scoped_left)))
    (hReplace hα)

/-- One-step equivalence replacement under a preserved head with all
`Me-Pro` cases wired. The preserved-head index `0`, changed-entry residual
index `1`, and non-residual tail indices `2+` are discharged by the canonical
handlers; constructor recursive replacements remain explicit. -/
theorem meqRed_equ_under_head_replace_with_pro_from_replacements {Γ : Ctx}
    {s : Stack} {head : CtxEntry} {old new u v : Term}
    (hpvOld : PrevalidExt (head :: { bound := old, kind := .equ } :: Γ) s)
    (hpvNew : PrevalidExt (head :: { bound := new, kind := .equ } :: Γ) s)
    (hnew : Term.Scoped Γ.depth new)
    (hOldNewStack : MEqRed (head :: { bound := new, kind := .equ } :: Γ) s
      (Term.shift 0 (Term.shift 0 old)) (Term.shift 0 (Term.shift 0 new)))
    (hSelfReplace :
      ∀ {u v : Term},
        MEqRed (head :: { bound := old, kind := .equ } :: Γ) s u v →
        MSubStar (head :: { bound := new, kind := .equ } :: Γ) s u v)
    (hAppOpReplace :
      ∀ {op op' arg : Term},
        MEqRed (head :: { bound := old, kind := .equ } :: Γ) (arg :: s) op op' →
        MEqRed (head :: { bound := new, kind := .equ } :: Γ) (arg :: s) op op')
    (hNilReplace :
      ∀ {arg arg' : Term},
        MEqRed (head :: { bound := old, kind := .equ } :: Γ) [] arg arg' →
        MEqRed (head :: { bound := new, kind := .equ } :: Γ) [] arg arg')
    (hFunBodyReplace :
      ∀ {bound body body' : Term},
        MEqRed ({ bound := bound, kind := .sub } :: head ::
          { bound := old, kind := .equ } :: Γ) [] body body' →
        MEqRed ({ bound := bound, kind := .sub } :: head ::
          { bound := new, kind := .equ } :: Γ) [] body body')
    (hBetBodyReplace :
      ∀ {bound body body' : Term},
        MEqRed ({ bound := bound, kind := .sub } :: head ::
          { bound := old, kind := .equ } :: Γ) (Stack.shift 0 s) body body' →
        MEqRed ({ bound := bound, kind := .sub } :: head ::
          { bound := new, kind := .equ } :: Γ) (Stack.shift 0 s) body body')
    (hFOpBodyReplace :
      ∀ {arg body body' : Term} {rest : Stack},
        Term.Scoped (Ctx.depth (head :: { bound := old, kind := .equ } :: Γ)) arg →
        s = arg :: rest →
        MEqRed ({ bound := arg, kind := .equ } :: head ::
          { bound := old, kind := .equ } :: Γ) (Stack.shift 0 rest) body body' →
        MSubStar ({ bound := arg, kind := .equ } :: head ::
          { bound := new, kind := .equ } :: Γ) (Stack.shift 0 rest) body body')
    (h : MEqRed (head :: { bound := old, kind := .equ } :: Γ) s u v) :
    MSubStar (head :: { bound := new, kind := .equ } :: Γ) s u v :=
  meqRed_equ_under_head_replace_from_replacements hpvOld hnew
    (meq_equ_under_head_pro_zero_handler_of_replacement hpvOld hnew
      (fun hα => hSelfReplace hα))
    (meq_equ_under_head_pro_residual_handler_of_replacement hpvNew hnew
      hOldNewStack (fun hResidual => hSelfReplace hResidual))
    (meq_equ_under_head_pro_tail_handler_of_replacement hpvOld hnew
      (fun hα => hSelfReplace hα))
    hAppOpReplace hNilReplace hFunBodyReplace hBetBodyReplace hFOpBodyReplace h

/-- Chain-level under-head equivalence replacement with all `Me-Pro` cases
wired through the canonical handlers. -/
theorem meqRedStar_equ_under_head_replace_with_pro_from_replacements {Γ : Ctx}
    {s : Stack} {head : CtxEntry} {old new u v : Term}
    (hpvOld : PrevalidExt (head :: { bound := old, kind := .equ } :: Γ) s)
    (hpvNew : PrevalidExt (head :: { bound := new, kind := .equ } :: Γ) s)
    (hnew : Term.Scoped Γ.depth new)
    (hOldNewStack : MEqRed (head :: { bound := new, kind := .equ } :: Γ) s
      (Term.shift 0 (Term.shift 0 old)) (Term.shift 0 (Term.shift 0 new)))
    (hSelfReplace :
      ∀ {u v : Term},
        MEqRed (head :: { bound := old, kind := .equ } :: Γ) s u v →
        MSubStar (head :: { bound := new, kind := .equ } :: Γ) s u v)
    (hAppOpReplace :
      ∀ {op op' arg : Term},
        MEqRed (head :: { bound := old, kind := .equ } :: Γ) (arg :: s) op op' →
        MEqRed (head :: { bound := new, kind := .equ } :: Γ) (arg :: s) op op')
    (hNilReplace :
      ∀ {arg arg' : Term},
        MEqRed (head :: { bound := old, kind := .equ } :: Γ) [] arg arg' →
        MEqRed (head :: { bound := new, kind := .equ } :: Γ) [] arg arg')
    (hFunBodyReplace :
      ∀ {bound body body' : Term},
        MEqRed ({ bound := bound, kind := .sub } :: head ::
          { bound := old, kind := .equ } :: Γ) [] body body' →
        MEqRed ({ bound := bound, kind := .sub } :: head ::
          { bound := new, kind := .equ } :: Γ) [] body body')
    (hBetBodyReplace :
      ∀ {bound body body' : Term},
        MEqRed ({ bound := bound, kind := .sub } :: head ::
          { bound := old, kind := .equ } :: Γ) (Stack.shift 0 s) body body' →
        MEqRed ({ bound := bound, kind := .sub } :: head ::
          { bound := new, kind := .equ } :: Γ) (Stack.shift 0 s) body body')
    (hFOpBodyReplace :
      ∀ {arg body body' : Term} {rest : Stack},
        Term.Scoped (Ctx.depth (head :: { bound := old, kind := .equ } :: Γ)) arg →
        s = arg :: rest →
        MEqRed ({ bound := arg, kind := .equ } :: head ::
          { bound := old, kind := .equ } :: Γ) (Stack.shift 0 rest) body body' →
        MSubStar ({ bound := arg, kind := .equ } :: head ::
          { bound := new, kind := .equ } :: Γ) (Stack.shift 0 rest) body body')
    (h : MEqRedStar (head :: { bound := old, kind := .equ } :: Γ) s u v) :
    MSubStar (head :: { bound := new, kind := .equ } :: Γ) s u v :=
  meqRedStar_replace_from_step_replacement
    (meqRed_equ_under_head_replace_with_pro_from_replacements hpvOld hpvNew hnew
      hOldNewStack hSelfReplace hAppOpReplace hNilReplace hFunBodyReplace
      hBetBodyReplace hFOpBodyReplace)
    h

/-- Function-valued chain-level under-head equivalence replacement with all
canonical `Me-Pro` cases wired. This packages
`meqRedStar_equ_under_head_replace_with_pro_from_replacements` across every
residual stack, deriving the new-context prevalidity from the old one. -/
theorem meqRedStar_equ_under_head_replace_with_pro_function_from_replacements
    {Γ : Ctx} {head : CtxEntry} {old new u v : Term}
    (hnew : Term.Scoped Γ.depth new)
    (hOldNewStack :
      ∀ {s : Stack},
        PrevalidExt (head :: { bound := old, kind := .equ } :: Γ) s →
        MEqRed (head :: { bound := new, kind := .equ } :: Γ) s
          (Term.shift 0 (Term.shift 0 old)) (Term.shift 0 (Term.shift 0 new)))
    (hSelfReplace :
      ∀ {s : Stack},
        PrevalidExt (head :: { bound := old, kind := .equ } :: Γ) s →
        ∀ {u v : Term},
          MEqRed (head :: { bound := old, kind := .equ } :: Γ) s u v →
          MSubStar (head :: { bound := new, kind := .equ } :: Γ) s u v)
    (hAppOpReplace :
      ∀ {s : Stack},
        PrevalidExt (head :: { bound := old, kind := .equ } :: Γ) s →
        ∀ {op op' arg : Term},
          MEqRed (head :: { bound := old, kind := .equ } :: Γ) (arg :: s) op op' →
          MEqRed (head :: { bound := new, kind := .equ } :: Γ) (arg :: s) op op')
    (hNilReplace :
      ∀ {arg arg' : Term},
        MEqRed (head :: { bound := old, kind := .equ } :: Γ) [] arg arg' →
        MEqRed (head :: { bound := new, kind := .equ } :: Γ) [] arg arg')
    (hFunBodyReplace :
      ∀ {bound body body' : Term},
        MEqRed ({ bound := bound, kind := .sub } :: head ::
          { bound := old, kind := .equ } :: Γ) [] body body' →
        MEqRed ({ bound := bound, kind := .sub } :: head ::
          { bound := new, kind := .equ } :: Γ) [] body body')
    (hBetBodyReplace :
      ∀ {s : Stack},
        PrevalidExt (head :: { bound := old, kind := .equ } :: Γ) s →
        ∀ {bound body body' : Term},
          MEqRed ({ bound := bound, kind := .sub } :: head ::
            { bound := old, kind := .equ } :: Γ) (Stack.shift 0 s) body body' →
          MEqRed ({ bound := bound, kind := .sub } :: head ::
            { bound := new, kind := .equ } :: Γ) (Stack.shift 0 s) body body')
    (hFOpBodyReplace :
      ∀ {s : Stack},
        PrevalidExt (head :: { bound := old, kind := .equ } :: Γ) s →
        ∀ {arg body body' : Term} {rest : Stack},
          Term.Scoped (Ctx.depth (head :: { bound := old, kind := .equ } :: Γ)) arg →
          s = arg :: rest →
          MEqRed ({ bound := arg, kind := .equ } :: head ::
            { bound := old, kind := .equ } :: Γ) (Stack.shift 0 rest) body body' →
          MSubStar ({ bound := arg, kind := .equ } :: head ::
            { bound := new, kind := .equ } :: Γ) (Stack.shift 0 rest) body body')
    (h :
      ∀ {s : Stack},
        PrevalidExt (head :: { bound := old, kind := .equ } :: Γ) s →
        MEqRedStar (head :: { bound := old, kind := .equ } :: Γ) s u v) :
    ∀ {s : Stack},
      PrevalidExt (head :: { bound := old, kind := .equ } :: Γ) s →
      MSubStar (head :: { bound := new, kind := .equ } :: Γ) s u v :=
  fun hpvOld =>
    meqRedStar_equ_under_head_replace_with_pro_from_replacements hpvOld
      (PrevalidExt.equ_under_head_replace hpvOld hnew) hnew
      (hOldNewStack hpvOld) (hSelfReplace hpvOld) (hAppOpReplace hpvOld)
      hNilReplace hFunBodyReplace (hBetBodyReplace hpvOld)
      (hFOpBodyReplace hpvOld) (h hpvOld)

/-- Chain-level under-head subtype replacement whose `Ms-Equ` branch is
wired through the canonical under-head equivalence replacement with all
`Me-Pro` cases handled. -/
theorem msubRedStar_equ_under_head_replace_with_pro_from_replacements {Γ : Ctx}
    {s : Stack} {head : CtxEntry} {old new u v : Term}
    (hpvOld : PrevalidExt (head :: { bound := old, kind := .equ } :: Γ) s)
    (hpvNew : PrevalidExt (head :: { bound := new, kind := .equ } :: Γ) s)
    (hnew : Term.Scoped Γ.depth new)
    (hOldNewStack : MEqRed (head :: { bound := new, kind := .equ } :: Γ) s
      (Term.shift 0 (Term.shift 0 old)) (Term.shift 0 (Term.shift 0 new)))
    (hEqSelfReplace :
      ∀ {u v : Term},
        MEqRed (head :: { bound := old, kind := .equ } :: Γ) s u v →
        MSubStar (head :: { bound := new, kind := .equ } :: Γ) s u v)
    (hEqAppOpReplace :
      ∀ {op op' arg : Term},
        MEqRed (head :: { bound := old, kind := .equ } :: Γ) (arg :: s) op op' →
        MEqRed (head :: { bound := new, kind := .equ } :: Γ) (arg :: s) op op')
    (hNilReplace :
      ∀ {arg arg' : Term},
        MEqRed (head :: { bound := old, kind := .equ } :: Γ) [] arg arg' →
        MEqRed (head :: { bound := new, kind := .equ } :: Γ) [] arg arg')
    (hEqFunBodyReplace :
      ∀ {bound body body' : Term},
        MEqRed ({ bound := bound, kind := .sub } :: head ::
          { bound := old, kind := .equ } :: Γ) [] body body' →
        MEqRed ({ bound := bound, kind := .sub } :: head ::
          { bound := new, kind := .equ } :: Γ) [] body body')
    (hEqBetBodyReplace :
      ∀ {bound body body' : Term},
        MEqRed ({ bound := bound, kind := .sub } :: head ::
          { bound := old, kind := .equ } :: Γ) (Stack.shift 0 s) body body' →
        MEqRed ({ bound := bound, kind := .sub } :: head ::
          { bound := new, kind := .equ } :: Γ) (Stack.shift 0 s) body body')
    (hEqFOpBodyReplace :
      ∀ {arg body body' : Term} {rest : Stack},
        Term.Scoped (Ctx.depth (head :: { bound := old, kind := .equ } :: Γ)) arg →
        s = arg :: rest →
        MEqRed ({ bound := arg, kind := .equ } :: head ::
          { bound := old, kind := .equ } :: Γ) (Stack.shift 0 rest) body body' →
        MSubStar ({ bound := arg, kind := .equ } :: head ::
          { bound := new, kind := .equ } :: Γ) (Stack.shift 0 rest) body body')
    (hAppOpReplace :
      ∀ {op op' arg : Term},
        MSubRed (head :: { bound := old, kind := .equ } :: Γ) (arg :: s) op op' →
        Term.Scoped (Ctx.depth (head :: { bound := old, kind := .equ } :: Γ)) arg →
        MSubStar (head :: { bound := new, kind := .equ } :: Γ) (arg :: s) op op')
    (hFunBodyReplace :
      ∀ {bound body body' : Term},
        MSubRed ({ bound := bound, kind := .sub } :: head ::
          { bound := old, kind := .equ } :: Γ) [] body body' →
        MSubRed ({ bound := bound, kind := .sub } :: head ::
          { bound := new, kind := .equ } :: Γ) [] body body')
    (hFOpBodyReplace :
      ∀ {arg body body' : Term} {rest : Stack},
        Term.Scoped (Ctx.depth (head :: { bound := old, kind := .equ } :: Γ)) arg →
        s = arg :: rest →
        MSubRed ({ bound := arg, kind := .equ } :: head ::
          { bound := old, kind := .equ } :: Γ) (Stack.shift 0 rest) body body' →
        MSubStar ({ bound := arg, kind := .equ } :: head ::
          { bound := new, kind := .equ } :: Γ) (Stack.shift 0 rest) body body')
    (h : MSubRedStar (head :: { bound := old, kind := .equ } :: Γ) s u v) :
    MSubStar (head :: { bound := new, kind := .equ } :: Γ) s u v :=
  msubRedStar_equ_under_head_replace_from_replacements hpvOld hnew
    (meqRed_equ_under_head_replace_with_pro_from_replacements hpvOld hpvNew
      hnew hOldNewStack hEqSelfReplace hEqAppOpReplace hNilReplace
      hEqFunBodyReplace hEqBetBodyReplace hEqFOpBodyReplace)
    hAppOpReplace hNilReplace hFunBodyReplace hFOpBodyReplace h

/-- Function-valued form of
`msubRedStar_equ_under_head_replace_with_pro_from_replacements`, packaging
the subtype wrapper over every residual stack while deriving new-context
prevalidity locally. -/
theorem msubRedStar_equ_under_head_replace_with_pro_function_from_replacements
    {Γ : Ctx} {head : CtxEntry} {old new u v : Term}
    (hnew : Term.Scoped Γ.depth new)
    (hOldNewStack :
      ∀ {s : Stack},
        PrevalidExt (head :: { bound := old, kind := .equ } :: Γ) s →
        MEqRed (head :: { bound := new, kind := .equ } :: Γ) s
          (Term.shift 0 (Term.shift 0 old)) (Term.shift 0 (Term.shift 0 new)))
    (hEqSelfReplace :
      ∀ {s : Stack},
        PrevalidExt (head :: { bound := old, kind := .equ } :: Γ) s →
        ∀ {u v : Term},
          MEqRed (head :: { bound := old, kind := .equ } :: Γ) s u v →
          MSubStar (head :: { bound := new, kind := .equ } :: Γ) s u v)
    (hEqAppOpReplace :
      ∀ {s : Stack},
        PrevalidExt (head :: { bound := old, kind := .equ } :: Γ) s →
        ∀ {op op' arg : Term},
          MEqRed (head :: { bound := old, kind := .equ } :: Γ) (arg :: s) op op' →
          MEqRed (head :: { bound := new, kind := .equ } :: Γ) (arg :: s) op op')
    (hNilReplace :
      ∀ {arg arg' : Term},
        MEqRed (head :: { bound := old, kind := .equ } :: Γ) [] arg arg' →
        MEqRed (head :: { bound := new, kind := .equ } :: Γ) [] arg arg')
    (hEqFunBodyReplace :
      ∀ {bound body body' : Term},
        MEqRed ({ bound := bound, kind := .sub } :: head ::
          { bound := old, kind := .equ } :: Γ) [] body body' →
        MEqRed ({ bound := bound, kind := .sub } :: head ::
          { bound := new, kind := .equ } :: Γ) [] body body')
    (hEqBetBodyReplace :
      ∀ {s : Stack},
        PrevalidExt (head :: { bound := old, kind := .equ } :: Γ) s →
        ∀ {bound body body' : Term},
          MEqRed ({ bound := bound, kind := .sub } :: head ::
            { bound := old, kind := .equ } :: Γ) (Stack.shift 0 s) body body' →
          MEqRed ({ bound := bound, kind := .sub } :: head ::
            { bound := new, kind := .equ } :: Γ) (Stack.shift 0 s) body body')
    (hEqFOpBodyReplace :
      ∀ {s : Stack},
        PrevalidExt (head :: { bound := old, kind := .equ } :: Γ) s →
        ∀ {arg body body' : Term} {rest : Stack},
          Term.Scoped (Ctx.depth (head :: { bound := old, kind := .equ } :: Γ)) arg →
          s = arg :: rest →
          MEqRed ({ bound := arg, kind := .equ } :: head ::
            { bound := old, kind := .equ } :: Γ) (Stack.shift 0 rest) body body' →
          MSubStar ({ bound := arg, kind := .equ } :: head ::
            { bound := new, kind := .equ } :: Γ) (Stack.shift 0 rest) body body')
    (hAppOpReplace :
      ∀ {s : Stack},
        PrevalidExt (head :: { bound := old, kind := .equ } :: Γ) s →
        ∀ {op op' arg : Term},
          MSubRed (head :: { bound := old, kind := .equ } :: Γ) (arg :: s) op op' →
          Term.Scoped (Ctx.depth (head :: { bound := old, kind := .equ } :: Γ)) arg →
          MSubStar (head :: { bound := new, kind := .equ } :: Γ) (arg :: s) op op')
    (hFunBodyReplace :
      ∀ {bound body body' : Term},
        MSubRed ({ bound := bound, kind := .sub } :: head ::
          { bound := old, kind := .equ } :: Γ) [] body body' →
        MSubRed ({ bound := bound, kind := .sub } :: head ::
          { bound := new, kind := .equ } :: Γ) [] body body')
    (hFOpBodyReplace :
      ∀ {s : Stack},
        PrevalidExt (head :: { bound := old, kind := .equ } :: Γ) s →
        ∀ {arg body body' : Term} {rest : Stack},
          Term.Scoped (Ctx.depth (head :: { bound := old, kind := .equ } :: Γ)) arg →
          s = arg :: rest →
          MSubRed ({ bound := arg, kind := .equ } :: head ::
            { bound := old, kind := .equ } :: Γ) (Stack.shift 0 rest) body body' →
          MSubStar ({ bound := arg, kind := .equ } :: head ::
            { bound := new, kind := .equ } :: Γ) (Stack.shift 0 rest) body body')
    (h :
      ∀ {s : Stack},
        PrevalidExt (head :: { bound := old, kind := .equ } :: Γ) s →
        MSubRedStar (head :: { bound := old, kind := .equ } :: Γ) s u v) :
    ∀ {s : Stack},
      PrevalidExt (head :: { bound := old, kind := .equ } :: Γ) s →
      MSubStar (head :: { bound := new, kind := .equ } :: Γ) s u v :=
  fun hpvOld =>
    msubRedStar_equ_under_head_replace_with_pro_from_replacements hpvOld
      (PrevalidExt.equ_under_head_replace hpvOld hnew) hnew
      (hOldNewStack hpvOld) (hEqSelfReplace hpvOld)
      (hEqAppOpReplace hpvOld) hNilReplace hEqFunBodyReplace
      (hEqBetBodyReplace hpvOld) (hEqFOpBodyReplace hpvOld)
      (hAppOpReplace hpvOld) hFunBodyReplace (hFOpBodyReplace hpvOld)
      (h hpvOld)

/-- If an old-to-new equivalence has already been lifted under the changed
`.equ` head, ordinary head weakening lifts it one level deeper under a
preserved head. This supplies the old-to-new premise needed by
`msub_equ_under_head_old_bound_to_new_bvar1` in `FOp` body residuals. -/
noncomputable def meq_equ_under_head_stack_lift_from_equ_head_lift {Γ : Ctx}
    {s : Stack} {head : CtxEntry} {old new : Term}
    (hpvTail : PrevalidExt Γ s)
    (hNewScoped : Term.Scoped Γ.depth new)
    (hHeadNew : Prevalid (head :: { bound := new, kind := .equ } :: Γ))
    (hOldNew : MEqRed ({ bound := new, kind := .equ } :: Γ) (Stack.shift 0 s)
      (Term.shift 0 old) (Term.shift 0 new)) :
    MEqRed (head :: { bound := new, kind := .equ } :: Γ)
      (Stack.shift 0 (Stack.shift 0 s))
      (Term.shift 0 (Term.shift 0 old)) (Term.shift 0 (Term.shift 0 new)) := by
  have hpvNewCtx : Prevalid ({ bound := new, kind := .equ } :: Γ) :=
    Prevalid.equ (PrevalidExt.ctx hpvTail) hNewScoped
  have hpvNew : PrevalidExt ({ bound := new, kind := .equ } :: Γ)
      (Stack.shift 0 s) :=
    PrevalidExt.weaken_head hpvTail hpvNewCtx
  exact MEqRed.weaken_head hOldNew hpvNew hHeadNew

/-- One-step consumer for the under-head `Me-Pro` residual: a changed-head
old-to-new lift is weakened under the preserved head and immediately turned
into the diagrammatic join from the old under-head bound to `bvar 1`. -/
theorem msub_equ_under_head_old_bound_to_new_bvar1_of_equ_head_lift {Γ : Ctx}
    {s : Stack} {head : CtxEntry} {old new : Term}
    (hpvTail : PrevalidExt Γ s)
    (hNewScoped : Term.Scoped Γ.depth new)
    (hHeadNew : Prevalid (head :: { bound := new, kind := .equ } :: Γ))
    (hOldNew : MEqRed ({ bound := new, kind := .equ } :: Γ) (Stack.shift 0 s)
      (Term.shift 0 old) (Term.shift 0 new)) :
    MSub (head :: { bound := new, kind := .equ } :: Γ)
      (Stack.shift 0 (Stack.shift 0 s))
      (Term.shift 0 (Term.shift 0 old)) (.bvar 1) := by
  have hpvNewCtx : Prevalid ({ bound := new, kind := .equ } :: Γ) :=
    Prevalid.equ (PrevalidExt.ctx hpvTail) hNewScoped
  have hpvNew : PrevalidExt ({ bound := new, kind := .equ } :: Γ)
      (Stack.shift 0 s) :=
    PrevalidExt.weaken_head hpvTail hpvNewCtx
  exact msub_equ_under_head_old_bound_to_new_bvar1
    (PrevalidExt.weaken_head hpvNew hHeadNew) hNewScoped
    (meq_equ_under_head_stack_lift_from_equ_head_lift
      hpvTail hNewScoped hHeadNew hOldNew)

/-- Converse composed consumer for the under-head `Me-Pro` residual: a
changed-head old-to-new lift is weakened under the preserved head and used to
join `bvar 1` back to the old under-head bound. -/
theorem msub_equ_under_head_new_bvar1_to_old_bound_of_equ_head_lift {Γ : Ctx}
    {s : Stack} {head : CtxEntry} {old new : Term}
    (hpvTail : PrevalidExt Γ s)
    (hNewScoped : Term.Scoped Γ.depth new)
    (hHeadNew : Prevalid (head :: { bound := new, kind := .equ } :: Γ))
    (hOldNew : MEqRed ({ bound := new, kind := .equ } :: Γ) (Stack.shift 0 s)
      (Term.shift 0 old) (Term.shift 0 new)) :
    MSub (head :: { bound := new, kind := .equ } :: Γ)
      (Stack.shift 0 (Stack.shift 0 s))
      (.bvar 1) (Term.shift 0 (Term.shift 0 old)) := by
  have hpvNewCtx : Prevalid ({ bound := new, kind := .equ } :: Γ) :=
    Prevalid.equ (PrevalidExt.ctx hpvTail) hNewScoped
  have hpvNew : PrevalidExt ({ bound := new, kind := .equ } :: Γ)
      (Stack.shift 0 s) :=
    PrevalidExt.weaken_head hpvTail hpvNewCtx
  exact msub_equ_under_head_new_bvar1_to_old_bound
    (PrevalidExt.weaken_head hpvNew hHeadNew) hNewScoped
    (meq_equ_under_head_stack_lift_from_equ_head_lift
      hpvTail hNewScoped hHeadNew hOldNew)

/-- One-step equivalence replacement below a preserved head, at the doubly
shifted residual stack induced by a changed `.equ` entry. The old-to-new
bridge is supplied at the changed head and weakened here under `head`, so the
under-head `Me-Pro` residual is wired automatically. -/
theorem meqRed_equ_under_head_shifted_replace_from_equ_head_lift {Γ : Ctx}
    {s : Stack} {head : CtxEntry} {old new u v : Term}
    (hpvTail : PrevalidExt Γ s)
    (hOldScoped : Term.Scoped Γ.depth old)
    (hNewScoped : Term.Scoped Γ.depth new)
    (hHeadOld : Prevalid (head :: { bound := old, kind := .equ } :: Γ))
    (hHeadNew : Prevalid (head :: { bound := new, kind := .equ } :: Γ))
    (hOldNew : MEqRed ({ bound := new, kind := .equ } :: Γ)
      (Stack.shift 0 s) (Term.shift 0 old) (Term.shift 0 new))
    (hSelfReplace :
      ∀ {u v : Term},
        MEqRed (head :: { bound := old, kind := .equ } :: Γ)
          (Stack.shift 0 (Stack.shift 0 s)) u v →
        MSubStar (head :: { bound := new, kind := .equ } :: Γ)
          (Stack.shift 0 (Stack.shift 0 s)) u v)
    (hAppOpReplace :
      ∀ {op op' arg : Term},
        MEqRed (head :: { bound := old, kind := .equ } :: Γ)
          (arg :: Stack.shift 0 (Stack.shift 0 s)) op op' →
        MEqRed (head :: { bound := new, kind := .equ } :: Γ)
          (arg :: Stack.shift 0 (Stack.shift 0 s)) op op')
    (hNilReplace :
      ∀ {arg arg' : Term},
        MEqRed (head :: { bound := old, kind := .equ } :: Γ) [] arg arg' →
        MEqRed (head :: { bound := new, kind := .equ } :: Γ) [] arg arg')
    (hFunBodyReplace :
      ∀ {bound body body' : Term},
        MEqRed ({ bound := bound, kind := .sub } :: head ::
          { bound := old, kind := .equ } :: Γ) [] body body' →
        MEqRed ({ bound := bound, kind := .sub } :: head ::
          { bound := new, kind := .equ } :: Γ) [] body body')
    (hBetBodyReplace :
      ∀ {bound body body' : Term},
        MEqRed ({ bound := bound, kind := .sub } :: head ::
          { bound := old, kind := .equ } :: Γ)
          (Stack.shift 0 (Stack.shift 0 (Stack.shift 0 s))) body body' →
        MEqRed ({ bound := bound, kind := .sub } :: head ::
          { bound := new, kind := .equ } :: Γ)
          (Stack.shift 0 (Stack.shift 0 (Stack.shift 0 s))) body body')
    (hFOpBodyReplace :
      ∀ {arg body body' : Term} {rest : Stack},
        Term.Scoped (Ctx.depth (head :: { bound := old, kind := .equ } :: Γ)) arg →
        Stack.shift 0 (Stack.shift 0 s) = arg :: rest →
        MEqRed ({ bound := arg, kind := .equ } :: head ::
          { bound := old, kind := .equ } :: Γ) (Stack.shift 0 rest) body body' →
        MSubStar ({ bound := arg, kind := .equ } :: head ::
          { bound := new, kind := .equ } :: Γ) (Stack.shift 0 rest) body body')
    (h : MEqRed (head :: { bound := old, kind := .equ } :: Γ)
      (Stack.shift 0 (Stack.shift 0 s)) u v) :
    MSubStar (head :: { bound := new, kind := .equ } :: Γ)
      (Stack.shift 0 (Stack.shift 0 s)) u v := by
  have hpvOldCtx : Prevalid ({ bound := old, kind := .equ } :: Γ) :=
    Prevalid.equ (PrevalidExt.ctx hpvTail) hOldScoped
  have hpvOldTail : PrevalidExt ({ bound := old, kind := .equ } :: Γ)
      (Stack.shift 0 s) :=
    PrevalidExt.weaken_head hpvTail hpvOldCtx
  have hpvOld : PrevalidExt (head :: { bound := old, kind := .equ } :: Γ)
      (Stack.shift 0 (Stack.shift 0 s)) :=
    PrevalidExt.weaken_head hpvOldTail hHeadOld
  have hpvNewCtx : Prevalid ({ bound := new, kind := .equ } :: Γ) :=
    Prevalid.equ (PrevalidExt.ctx hpvTail) hNewScoped
  have hpvNewTail : PrevalidExt ({ bound := new, kind := .equ } :: Γ)
      (Stack.shift 0 s) :=
    PrevalidExt.weaken_head hpvTail hpvNewCtx
  have hpvNew : PrevalidExt (head :: { bound := new, kind := .equ } :: Γ)
      (Stack.shift 0 (Stack.shift 0 s)) :=
    PrevalidExt.weaken_head hpvNewTail hHeadNew
  exact meqRed_equ_under_head_replace_with_pro_from_replacements
    hpvOld hpvNew hNewScoped
    (meq_equ_under_head_stack_lift_from_equ_head_lift
      hpvTail hNewScoped hHeadNew hOldNew)
    hSelfReplace hAppOpReplace hNilReplace hFunBodyReplace hBetBodyReplace
    hFOpBodyReplace h

/-- Chain-level counterpart of
`meqRed_equ_under_head_shifted_replace_from_equ_head_lift`. -/
theorem meqRedStar_equ_under_head_shifted_replace_from_equ_head_lift {Γ : Ctx}
    {s : Stack} {head : CtxEntry} {old new u v : Term}
    (hpvTail : PrevalidExt Γ s)
    (hOldScoped : Term.Scoped Γ.depth old)
    (hNewScoped : Term.Scoped Γ.depth new)
    (hHeadOld : Prevalid (head :: { bound := old, kind := .equ } :: Γ))
    (hHeadNew : Prevalid (head :: { bound := new, kind := .equ } :: Γ))
    (hOldNew : MEqRed ({ bound := new, kind := .equ } :: Γ)
      (Stack.shift 0 s) (Term.shift 0 old) (Term.shift 0 new))
    (hSelfReplace :
      ∀ {u v : Term},
        MEqRed (head :: { bound := old, kind := .equ } :: Γ)
          (Stack.shift 0 (Stack.shift 0 s)) u v →
        MSubStar (head :: { bound := new, kind := .equ } :: Γ)
          (Stack.shift 0 (Stack.shift 0 s)) u v)
    (hAppOpReplace :
      ∀ {op op' arg : Term},
        MEqRed (head :: { bound := old, kind := .equ } :: Γ)
          (arg :: Stack.shift 0 (Stack.shift 0 s)) op op' →
        MEqRed (head :: { bound := new, kind := .equ } :: Γ)
          (arg :: Stack.shift 0 (Stack.shift 0 s)) op op')
    (hNilReplace :
      ∀ {arg arg' : Term},
        MEqRed (head :: { bound := old, kind := .equ } :: Γ) [] arg arg' →
        MEqRed (head :: { bound := new, kind := .equ } :: Γ) [] arg arg')
    (hFunBodyReplace :
      ∀ {bound body body' : Term},
        MEqRed ({ bound := bound, kind := .sub } :: head ::
          { bound := old, kind := .equ } :: Γ) [] body body' →
        MEqRed ({ bound := bound, kind := .sub } :: head ::
          { bound := new, kind := .equ } :: Γ) [] body body')
    (hBetBodyReplace :
      ∀ {bound body body' : Term},
        MEqRed ({ bound := bound, kind := .sub } :: head ::
          { bound := old, kind := .equ } :: Γ)
          (Stack.shift 0 (Stack.shift 0 (Stack.shift 0 s))) body body' →
        MEqRed ({ bound := bound, kind := .sub } :: head ::
          { bound := new, kind := .equ } :: Γ)
          (Stack.shift 0 (Stack.shift 0 (Stack.shift 0 s))) body body')
    (hFOpBodyReplace :
      ∀ {arg body body' : Term} {rest : Stack},
        Term.Scoped (Ctx.depth (head :: { bound := old, kind := .equ } :: Γ)) arg →
        Stack.shift 0 (Stack.shift 0 s) = arg :: rest →
        MEqRed ({ bound := arg, kind := .equ } :: head ::
          { bound := old, kind := .equ } :: Γ) (Stack.shift 0 rest) body body' →
        MSubStar ({ bound := arg, kind := .equ } :: head ::
          { bound := new, kind := .equ } :: Γ) (Stack.shift 0 rest) body body')
    (h : MEqRedStar (head :: { bound := old, kind := .equ } :: Γ)
      (Stack.shift 0 (Stack.shift 0 s)) u v) :
    MSubStar (head :: { bound := new, kind := .equ } :: Γ)
      (Stack.shift 0 (Stack.shift 0 s)) u v :=
  meqRedStar_replace_from_step_replacement
    (meqRed_equ_under_head_shifted_replace_from_equ_head_lift
      hpvTail hOldScoped hNewScoped hHeadOld hHeadNew hOldNew hSelfReplace
      hAppOpReplace hNilReplace hFunBodyReplace hBetBodyReplace
      hFOpBodyReplace)
    h

/-- One-step subtype replacement below a preserved head, at the doubly
shifted residual stack induced by a changed `.equ` entry. The `Ms-Equ`
branch reuses the shifted under-head equivalence replacement package. -/
theorem msubRed_equ_under_head_shifted_replace_from_equ_head_lift {Γ : Ctx}
    {s : Stack} {head : CtxEntry} {old new u v : Term}
    (hpvTail : PrevalidExt Γ s)
    (hOldScoped : Term.Scoped Γ.depth old)
    (hNewScoped : Term.Scoped Γ.depth new)
    (hHeadOld : Prevalid (head :: { bound := old, kind := .equ } :: Γ))
    (hHeadNew : Prevalid (head :: { bound := new, kind := .equ } :: Γ))
    (hOldNew : MEqRed ({ bound := new, kind := .equ } :: Γ)
      (Stack.shift 0 s) (Term.shift 0 old) (Term.shift 0 new))
    (hEqSelfReplace :
      ∀ {u v : Term},
        MEqRed (head :: { bound := old, kind := .equ } :: Γ)
          (Stack.shift 0 (Stack.shift 0 s)) u v →
        MSubStar (head :: { bound := new, kind := .equ } :: Γ)
          (Stack.shift 0 (Stack.shift 0 s)) u v)
    (hEqAppOpReplace :
      ∀ {op op' arg : Term},
        MEqRed (head :: { bound := old, kind := .equ } :: Γ)
          (arg :: Stack.shift 0 (Stack.shift 0 s)) op op' →
        MEqRed (head :: { bound := new, kind := .equ } :: Γ)
          (arg :: Stack.shift 0 (Stack.shift 0 s)) op op')
    (hNilReplace :
      ∀ {arg arg' : Term},
        MEqRed (head :: { bound := old, kind := .equ } :: Γ) [] arg arg' →
        MEqRed (head :: { bound := new, kind := .equ } :: Γ) [] arg arg')
    (hEqFunBodyReplace :
      ∀ {bound body body' : Term},
        MEqRed ({ bound := bound, kind := .sub } :: head ::
          { bound := old, kind := .equ } :: Γ) [] body body' →
        MEqRed ({ bound := bound, kind := .sub } :: head ::
          { bound := new, kind := .equ } :: Γ) [] body body')
    (hEqBetBodyReplace :
      ∀ {bound body body' : Term},
        MEqRed ({ bound := bound, kind := .sub } :: head ::
          { bound := old, kind := .equ } :: Γ)
          (Stack.shift 0 (Stack.shift 0 (Stack.shift 0 s))) body body' →
        MEqRed ({ bound := bound, kind := .sub } :: head ::
          { bound := new, kind := .equ } :: Γ)
          (Stack.shift 0 (Stack.shift 0 (Stack.shift 0 s))) body body')
    (hEqFOpBodyReplace :
      ∀ {arg body body' : Term} {rest : Stack},
        Term.Scoped (Ctx.depth (head :: { bound := old, kind := .equ } :: Γ)) arg →
        Stack.shift 0 (Stack.shift 0 s) = arg :: rest →
        MEqRed ({ bound := arg, kind := .equ } :: head ::
          { bound := old, kind := .equ } :: Γ) (Stack.shift 0 rest) body body' →
        MSubStar ({ bound := arg, kind := .equ } :: head ::
          { bound := new, kind := .equ } :: Γ) (Stack.shift 0 rest) body body')
    (hAppOpReplace :
      ∀ {op op' arg : Term},
        MSubRed (head :: { bound := old, kind := .equ } :: Γ)
          (arg :: Stack.shift 0 (Stack.shift 0 s)) op op' →
        Term.Scoped (Ctx.depth (head :: { bound := old, kind := .equ } :: Γ)) arg →
        MSubStar (head :: { bound := new, kind := .equ } :: Γ)
          (arg :: Stack.shift 0 (Stack.shift 0 s)) op op')
    (hFunBodyReplace :
      ∀ {bound body body' : Term},
        MSubRed ({ bound := bound, kind := .sub } :: head ::
          { bound := old, kind := .equ } :: Γ) [] body body' →
        MSubRed ({ bound := bound, kind := .sub } :: head ::
          { bound := new, kind := .equ } :: Γ) [] body body')
    (hFOpBodyReplace :
      ∀ {arg body body' : Term} {rest : Stack},
        Term.Scoped (Ctx.depth (head :: { bound := old, kind := .equ } :: Γ)) arg →
        Stack.shift 0 (Stack.shift 0 s) = arg :: rest →
        MSubRed ({ bound := arg, kind := .equ } :: head ::
          { bound := old, kind := .equ } :: Γ) (Stack.shift 0 rest) body body' →
        MSubStar ({ bound := arg, kind := .equ } :: head ::
          { bound := new, kind := .equ } :: Γ) (Stack.shift 0 rest) body body')
    (h : MSubRed (head :: { bound := old, kind := .equ } :: Γ)
      (Stack.shift 0 (Stack.shift 0 s)) u v) :
    MSubStar (head :: { bound := new, kind := .equ } :: Γ)
      (Stack.shift 0 (Stack.shift 0 s)) u v := by
  have hpvOldCtx : Prevalid ({ bound := old, kind := .equ } :: Γ) :=
    Prevalid.equ (PrevalidExt.ctx hpvTail) hOldScoped
  have hpvOldTail : PrevalidExt ({ bound := old, kind := .equ } :: Γ)
      (Stack.shift 0 s) :=
    PrevalidExt.weaken_head hpvTail hpvOldCtx
  have hpvOld : PrevalidExt (head :: { bound := old, kind := .equ } :: Γ)
      (Stack.shift 0 (Stack.shift 0 s)) :=
    PrevalidExt.weaken_head hpvOldTail hHeadOld
  exact msubRed_equ_under_head_replace_from_replacements hpvOld hNewScoped
    (meqRed_equ_under_head_shifted_replace_from_equ_head_lift
      hpvTail hOldScoped hNewScoped hHeadOld hHeadNew hOldNew hEqSelfReplace
      hEqAppOpReplace hNilReplace hEqFunBodyReplace hEqBetBodyReplace
      hEqFOpBodyReplace)
    hAppOpReplace hNilReplace hFunBodyReplace hFOpBodyReplace h

/-- Chain-level counterpart of
`msubRed_equ_under_head_shifted_replace_from_equ_head_lift`. -/
theorem msubRedStar_equ_under_head_shifted_replace_from_equ_head_lift {Γ : Ctx}
    {s : Stack} {head : CtxEntry} {old new u v : Term}
    (hpvTail : PrevalidExt Γ s)
    (hOldScoped : Term.Scoped Γ.depth old)
    (hNewScoped : Term.Scoped Γ.depth new)
    (hHeadOld : Prevalid (head :: { bound := old, kind := .equ } :: Γ))
    (hHeadNew : Prevalid (head :: { bound := new, kind := .equ } :: Γ))
    (hOldNew : MEqRed ({ bound := new, kind := .equ } :: Γ)
      (Stack.shift 0 s) (Term.shift 0 old) (Term.shift 0 new))
    (hEqSelfReplace :
      ∀ {u v : Term},
        MEqRed (head :: { bound := old, kind := .equ } :: Γ)
          (Stack.shift 0 (Stack.shift 0 s)) u v →
        MSubStar (head :: { bound := new, kind := .equ } :: Γ)
          (Stack.shift 0 (Stack.shift 0 s)) u v)
    (hEqAppOpReplace :
      ∀ {op op' arg : Term},
        MEqRed (head :: { bound := old, kind := .equ } :: Γ)
          (arg :: Stack.shift 0 (Stack.shift 0 s)) op op' →
        MEqRed (head :: { bound := new, kind := .equ } :: Γ)
          (arg :: Stack.shift 0 (Stack.shift 0 s)) op op')
    (hNilReplace :
      ∀ {arg arg' : Term},
        MEqRed (head :: { bound := old, kind := .equ } :: Γ) [] arg arg' →
        MEqRed (head :: { bound := new, kind := .equ } :: Γ) [] arg arg')
    (hEqFunBodyReplace :
      ∀ {bound body body' : Term},
        MEqRed ({ bound := bound, kind := .sub } :: head ::
          { bound := old, kind := .equ } :: Γ) [] body body' →
        MEqRed ({ bound := bound, kind := .sub } :: head ::
          { bound := new, kind := .equ } :: Γ) [] body body')
    (hEqBetBodyReplace :
      ∀ {bound body body' : Term},
        MEqRed ({ bound := bound, kind := .sub } :: head ::
          { bound := old, kind := .equ } :: Γ)
          (Stack.shift 0 (Stack.shift 0 (Stack.shift 0 s))) body body' →
        MEqRed ({ bound := bound, kind := .sub } :: head ::
          { bound := new, kind := .equ } :: Γ)
          (Stack.shift 0 (Stack.shift 0 (Stack.shift 0 s))) body body')
    (hEqFOpBodyReplace :
      ∀ {arg body body' : Term} {rest : Stack},
        Term.Scoped (Ctx.depth (head :: { bound := old, kind := .equ } :: Γ)) arg →
        Stack.shift 0 (Stack.shift 0 s) = arg :: rest →
        MEqRed ({ bound := arg, kind := .equ } :: head ::
          { bound := old, kind := .equ } :: Γ) (Stack.shift 0 rest) body body' →
        MSubStar ({ bound := arg, kind := .equ } :: head ::
          { bound := new, kind := .equ } :: Γ) (Stack.shift 0 rest) body body')
    (hAppOpReplace :
      ∀ {op op' arg : Term},
        MSubRed (head :: { bound := old, kind := .equ } :: Γ)
          (arg :: Stack.shift 0 (Stack.shift 0 s)) op op' →
        Term.Scoped (Ctx.depth (head :: { bound := old, kind := .equ } :: Γ)) arg →
        MSubStar (head :: { bound := new, kind := .equ } :: Γ)
          (arg :: Stack.shift 0 (Stack.shift 0 s)) op op')
    (hFunBodyReplace :
      ∀ {bound body body' : Term},
        MSubRed ({ bound := bound, kind := .sub } :: head ::
          { bound := old, kind := .equ } :: Γ) [] body body' →
        MSubRed ({ bound := bound, kind := .sub } :: head ::
          { bound := new, kind := .equ } :: Γ) [] body body')
    (hFOpBodyReplace :
      ∀ {arg body body' : Term} {rest : Stack},
        Term.Scoped (Ctx.depth (head :: { bound := old, kind := .equ } :: Γ)) arg →
        Stack.shift 0 (Stack.shift 0 s) = arg :: rest →
        MSubRed ({ bound := arg, kind := .equ } :: head ::
          { bound := old, kind := .equ } :: Γ) (Stack.shift 0 rest) body body' →
        MSubStar ({ bound := arg, kind := .equ } :: head ::
          { bound := new, kind := .equ } :: Γ) (Stack.shift 0 rest) body body')
    (h : MSubRedStar (head :: { bound := old, kind := .equ } :: Γ)
      (Stack.shift 0 (Stack.shift 0 s)) u v) :
    MSubStar (head :: { bound := new, kind := .equ } :: Γ)
      (Stack.shift 0 (Stack.shift 0 s)) u v :=
  msubRedStar_replace_from_step_replacement
    (msubRed_equ_under_head_shifted_replace_from_equ_head_lift
      hpvTail hOldScoped hNewScoped hHeadOld hHeadNew hOldNew hEqSelfReplace
      hEqAppOpReplace hNilReplace hEqFunBodyReplace hEqBetBodyReplace
      hEqFOpBodyReplace hAppOpReplace hFunBodyReplace hFOpBodyReplace)
    h

/-- Function-valued chain-level under-head equivalence replacement from a
tail-polymorphic changed-head old-to-new lift. -/
theorem meqRedStar_equ_under_head_shifted_replace_function_from_equ_head_lift
    {Γ : Ctx} {head : CtxEntry} {old new u v : Term}
    (hOldScoped : Term.Scoped Γ.depth old)
    (hNewScoped : Term.Scoped Γ.depth new)
    (hHeadOld : Prevalid (head :: { bound := old, kind := .equ } :: Γ))
    (hHeadNew : Prevalid (head :: { bound := new, kind := .equ } :: Γ))
    (hOldNew :
      ∀ {s : Stack},
        PrevalidExt Γ s →
        MEqRed ({ bound := new, kind := .equ } :: Γ)
          (Stack.shift 0 s) (Term.shift 0 old) (Term.shift 0 new))
    (hSelfReplace :
      ∀ {s : Stack},
        PrevalidExt Γ s →
        ∀ {u v : Term},
          MEqRed (head :: { bound := old, kind := .equ } :: Γ)
            (Stack.shift 0 (Stack.shift 0 s)) u v →
          MSubStar (head :: { bound := new, kind := .equ } :: Γ)
            (Stack.shift 0 (Stack.shift 0 s)) u v)
    (hAppOpReplace :
      ∀ {s : Stack},
        PrevalidExt Γ s →
        ∀ {op op' arg : Term},
          MEqRed (head :: { bound := old, kind := .equ } :: Γ)
            (arg :: Stack.shift 0 (Stack.shift 0 s)) op op' →
          MEqRed (head :: { bound := new, kind := .equ } :: Γ)
            (arg :: Stack.shift 0 (Stack.shift 0 s)) op op')
    (hNilReplace :
      ∀ {arg arg' : Term},
        MEqRed (head :: { bound := old, kind := .equ } :: Γ) [] arg arg' →
        MEqRed (head :: { bound := new, kind := .equ } :: Γ) [] arg arg')
    (hFunBodyReplace :
      ∀ {bound body body' : Term},
        MEqRed ({ bound := bound, kind := .sub } :: head ::
          { bound := old, kind := .equ } :: Γ) [] body body' →
        MEqRed ({ bound := bound, kind := .sub } :: head ::
          { bound := new, kind := .equ } :: Γ) [] body body')
    (hBetBodyReplace :
      ∀ {s : Stack},
        PrevalidExt Γ s →
        ∀ {bound body body' : Term},
          MEqRed ({ bound := bound, kind := .sub } :: head ::
            { bound := old, kind := .equ } :: Γ)
            (Stack.shift 0 (Stack.shift 0 (Stack.shift 0 s))) body body' →
          MEqRed ({ bound := bound, kind := .sub } :: head ::
            { bound := new, kind := .equ } :: Γ)
            (Stack.shift 0 (Stack.shift 0 (Stack.shift 0 s))) body body')
    (hFOpBodyReplace :
      ∀ {s : Stack},
        PrevalidExt Γ s →
        ∀ {arg body body' : Term} {rest : Stack},
          Term.Scoped (Ctx.depth (head :: { bound := old, kind := .equ } :: Γ)) arg →
          Stack.shift 0 (Stack.shift 0 s) = arg :: rest →
          MEqRed ({ bound := arg, kind := .equ } :: head ::
            { bound := old, kind := .equ } :: Γ) (Stack.shift 0 rest) body body' →
          MSubStar ({ bound := arg, kind := .equ } :: head ::
            { bound := new, kind := .equ } :: Γ) (Stack.shift 0 rest) body body')
    (h :
      ∀ {s : Stack},
        PrevalidExt Γ s →
        MEqRedStar (head :: { bound := old, kind := .equ } :: Γ)
          (Stack.shift 0 (Stack.shift 0 s)) u v) :
    ∀ {s : Stack},
      PrevalidExt Γ s →
      MSubStar (head :: { bound := new, kind := .equ } :: Γ)
        (Stack.shift 0 (Stack.shift 0 s)) u v :=
  fun hpvTail =>
    meqRedStar_equ_under_head_shifted_replace_from_equ_head_lift hpvTail
      hOldScoped hNewScoped hHeadOld hHeadNew (hOldNew hpvTail)
      (hSelfReplace hpvTail) (hAppOpReplace hpvTail) hNilReplace
      hFunBodyReplace (hBetBodyReplace hpvTail) (hFOpBodyReplace hpvTail)
      (h hpvTail)

/-- Function-valued chain-level under-head subtype replacement from a
tail-polymorphic changed-head old-to-new lift. -/
theorem msubRedStar_equ_under_head_shifted_replace_function_from_equ_head_lift
    {Γ : Ctx} {head : CtxEntry} {old new u v : Term}
    (hOldScoped : Term.Scoped Γ.depth old)
    (hNewScoped : Term.Scoped Γ.depth new)
    (hHeadOld : Prevalid (head :: { bound := old, kind := .equ } :: Γ))
    (hHeadNew : Prevalid (head :: { bound := new, kind := .equ } :: Γ))
    (hOldNew :
      ∀ {s : Stack},
        PrevalidExt Γ s →
        MEqRed ({ bound := new, kind := .equ } :: Γ)
          (Stack.shift 0 s) (Term.shift 0 old) (Term.shift 0 new))
    (hEqSelfReplace :
      ∀ {s : Stack},
        PrevalidExt Γ s →
        ∀ {u v : Term},
          MEqRed (head :: { bound := old, kind := .equ } :: Γ)
            (Stack.shift 0 (Stack.shift 0 s)) u v →
          MSubStar (head :: { bound := new, kind := .equ } :: Γ)
            (Stack.shift 0 (Stack.shift 0 s)) u v)
    (hEqAppOpReplace :
      ∀ {s : Stack},
        PrevalidExt Γ s →
        ∀ {op op' arg : Term},
          MEqRed (head :: { bound := old, kind := .equ } :: Γ)
            (arg :: Stack.shift 0 (Stack.shift 0 s)) op op' →
          MEqRed (head :: { bound := new, kind := .equ } :: Γ)
            (arg :: Stack.shift 0 (Stack.shift 0 s)) op op')
    (hNilReplace :
      ∀ {arg arg' : Term},
        MEqRed (head :: { bound := old, kind := .equ } :: Γ) [] arg arg' →
        MEqRed (head :: { bound := new, kind := .equ } :: Γ) [] arg arg')
    (hEqFunBodyReplace :
      ∀ {bound body body' : Term},
        MEqRed ({ bound := bound, kind := .sub } :: head ::
          { bound := old, kind := .equ } :: Γ) [] body body' →
        MEqRed ({ bound := bound, kind := .sub } :: head ::
          { bound := new, kind := .equ } :: Γ) [] body body')
    (hEqBetBodyReplace :
      ∀ {s : Stack},
        PrevalidExt Γ s →
        ∀ {bound body body' : Term},
          MEqRed ({ bound := bound, kind := .sub } :: head ::
            { bound := old, kind := .equ } :: Γ)
            (Stack.shift 0 (Stack.shift 0 (Stack.shift 0 s))) body body' →
          MEqRed ({ bound := bound, kind := .sub } :: head ::
            { bound := new, kind := .equ } :: Γ)
            (Stack.shift 0 (Stack.shift 0 (Stack.shift 0 s))) body body')
    (hEqFOpBodyReplace :
      ∀ {s : Stack},
        PrevalidExt Γ s →
        ∀ {arg body body' : Term} {rest : Stack},
          Term.Scoped (Ctx.depth (head :: { bound := old, kind := .equ } :: Γ)) arg →
          Stack.shift 0 (Stack.shift 0 s) = arg :: rest →
          MEqRed ({ bound := arg, kind := .equ } :: head ::
            { bound := old, kind := .equ } :: Γ) (Stack.shift 0 rest) body body' →
          MSubStar ({ bound := arg, kind := .equ } :: head ::
            { bound := new, kind := .equ } :: Γ) (Stack.shift 0 rest) body body')
    (hAppOpReplace :
      ∀ {s : Stack},
        PrevalidExt Γ s →
        ∀ {op op' arg : Term},
          MSubRed (head :: { bound := old, kind := .equ } :: Γ)
            (arg :: Stack.shift 0 (Stack.shift 0 s)) op op' →
          Term.Scoped (Ctx.depth (head :: { bound := old, kind := .equ } :: Γ)) arg →
          MSubStar (head :: { bound := new, kind := .equ } :: Γ)
            (arg :: Stack.shift 0 (Stack.shift 0 s)) op op')
    (hFunBodyReplace :
      ∀ {bound body body' : Term},
        MSubRed ({ bound := bound, kind := .sub } :: head ::
          { bound := old, kind := .equ } :: Γ) [] body body' →
        MSubRed ({ bound := bound, kind := .sub } :: head ::
          { bound := new, kind := .equ } :: Γ) [] body body')
    (hFOpBodyReplace :
      ∀ {s : Stack},
        PrevalidExt Γ s →
        ∀ {arg body body' : Term} {rest : Stack},
          Term.Scoped (Ctx.depth (head :: { bound := old, kind := .equ } :: Γ)) arg →
          Stack.shift 0 (Stack.shift 0 s) = arg :: rest →
          MSubRed ({ bound := arg, kind := .equ } :: head ::
            { bound := old, kind := .equ } :: Γ) (Stack.shift 0 rest) body body' →
          MSubStar ({ bound := arg, kind := .equ } :: head ::
            { bound := new, kind := .equ } :: Γ) (Stack.shift 0 rest) body body')
    (h :
      ∀ {s : Stack},
        PrevalidExt Γ s →
        MSubRedStar (head :: { bound := old, kind := .equ } :: Γ)
          (Stack.shift 0 (Stack.shift 0 s)) u v) :
    ∀ {s : Stack},
      PrevalidExt Γ s →
      MSubStar (head :: { bound := new, kind := .equ } :: Γ)
        (Stack.shift 0 (Stack.shift 0 s)) u v :=
  fun hpvTail =>
    msubRedStar_equ_under_head_shifted_replace_from_equ_head_lift hpvTail
      hOldScoped hNewScoped hHeadOld hHeadNew (hOldNew hpvTail)
      (hEqSelfReplace hpvTail) (hEqAppOpReplace hpvTail) hNilReplace
      hEqFunBodyReplace (hEqBetBodyReplace hpvTail)
      (hEqFOpBodyReplace hpvTail) (hAppOpReplace hpvTail) hFunBodyReplace
      (hFOpBodyReplace hpvTail) (h hpvTail)

/-- One-step equivalence replacement below a preserved head, where the
old-to-new changed-head equivalence is already available at the preserved
head's tail stack. Weakening that bridge under `head` supplies the
under-head `Me-Pro` residual automatically. -/
theorem meqRed_equ_under_head_shifted_replace_from_tail_lift {Γ : Ctx}
    {tail : Stack} {head : CtxEntry} {old new u v : Term}
    (hpvOldTail : PrevalidExt ({ bound := old, kind := .equ } :: Γ) tail)
    (hpvNewTail : PrevalidExt ({ bound := new, kind := .equ } :: Γ) tail)
    (hNewScoped : Term.Scoped Γ.depth new)
    (hHeadOld : Prevalid (head :: { bound := old, kind := .equ } :: Γ))
    (hHeadNew : Prevalid (head :: { bound := new, kind := .equ } :: Γ))
    (hOldNewTail : MEqRed ({ bound := new, kind := .equ } :: Γ) tail
      (Term.shift 0 old) (Term.shift 0 new))
    (hSelfReplace :
      ∀ {u v : Term},
        MEqRed (head :: { bound := old, kind := .equ } :: Γ)
          (Stack.shift 0 tail) u v →
        MSubStar (head :: { bound := new, kind := .equ } :: Γ)
          (Stack.shift 0 tail) u v)
    (hAppOpReplace :
      ∀ {op op' arg : Term},
        MEqRed (head :: { bound := old, kind := .equ } :: Γ)
          (arg :: Stack.shift 0 tail) op op' →
        MEqRed (head :: { bound := new, kind := .equ } :: Γ)
          (arg :: Stack.shift 0 tail) op op')
    (hNilReplace :
      ∀ {arg arg' : Term},
        MEqRed (head :: { bound := old, kind := .equ } :: Γ) [] arg arg' →
        MEqRed (head :: { bound := new, kind := .equ } :: Γ) [] arg arg')
    (hFunBodyReplace :
      ∀ {bound body body' : Term},
        MEqRed ({ bound := bound, kind := .sub } :: head ::
          { bound := old, kind := .equ } :: Γ) [] body body' →
        MEqRed ({ bound := bound, kind := .sub } :: head ::
          { bound := new, kind := .equ } :: Γ) [] body body')
    (hBetBodyReplace :
      ∀ {bound body body' : Term},
        MEqRed ({ bound := bound, kind := .sub } :: head ::
          { bound := old, kind := .equ } :: Γ) (Stack.shift 0 (Stack.shift 0 tail))
          body body' →
        MEqRed ({ bound := bound, kind := .sub } :: head ::
          { bound := new, kind := .equ } :: Γ) (Stack.shift 0 (Stack.shift 0 tail))
          body body')
    (hFOpBodyReplace :
      ∀ {arg body body' : Term} {rest : Stack},
        Term.Scoped (Ctx.depth (head :: { bound := old, kind := .equ } :: Γ)) arg →
        Stack.shift 0 tail = arg :: rest →
        MEqRed ({ bound := arg, kind := .equ } :: head ::
          { bound := old, kind := .equ } :: Γ) (Stack.shift 0 rest) body body' →
        MSubStar ({ bound := arg, kind := .equ } :: head ::
          { bound := new, kind := .equ } :: Γ) (Stack.shift 0 rest) body body')
    (h : MEqRed (head :: { bound := old, kind := .equ } :: Γ)
      (Stack.shift 0 tail) u v) :
    MSubStar (head :: { bound := new, kind := .equ } :: Γ)
      (Stack.shift 0 tail) u v := by
  exact meqRed_equ_under_head_replace_with_pro_from_replacements
    (PrevalidExt.weaken_head hpvOldTail hHeadOld)
    (PrevalidExt.weaken_head hpvNewTail hHeadNew)
    hNewScoped
    (MEqRed.weaken_head hOldNewTail hpvNewTail hHeadNew)
    hSelfReplace hAppOpReplace hNilReplace hFunBodyReplace hBetBodyReplace
    hFOpBodyReplace h

/-- Chain-level counterpart of
`meqRed_equ_under_head_shifted_replace_from_tail_lift`. -/
theorem meqRedStar_equ_under_head_shifted_replace_from_tail_lift {Γ : Ctx}
    {tail : Stack} {head : CtxEntry} {old new u v : Term}
    (hpvOldTail : PrevalidExt ({ bound := old, kind := .equ } :: Γ) tail)
    (hpvNewTail : PrevalidExt ({ bound := new, kind := .equ } :: Γ) tail)
    (hNewScoped : Term.Scoped Γ.depth new)
    (hHeadOld : Prevalid (head :: { bound := old, kind := .equ } :: Γ))
    (hHeadNew : Prevalid (head :: { bound := new, kind := .equ } :: Γ))
    (hOldNewTail : MEqRed ({ bound := new, kind := .equ } :: Γ) tail
      (Term.shift 0 old) (Term.shift 0 new))
    (hSelfReplace :
      ∀ {u v : Term},
        MEqRed (head :: { bound := old, kind := .equ } :: Γ)
          (Stack.shift 0 tail) u v →
        MSubStar (head :: { bound := new, kind := .equ } :: Γ)
          (Stack.shift 0 tail) u v)
    (hAppOpReplace :
      ∀ {op op' arg : Term},
        MEqRed (head :: { bound := old, kind := .equ } :: Γ)
          (arg :: Stack.shift 0 tail) op op' →
        MEqRed (head :: { bound := new, kind := .equ } :: Γ)
          (arg :: Stack.shift 0 tail) op op')
    (hNilReplace :
      ∀ {arg arg' : Term},
        MEqRed (head :: { bound := old, kind := .equ } :: Γ) [] arg arg' →
        MEqRed (head :: { bound := new, kind := .equ } :: Γ) [] arg arg')
    (hFunBodyReplace :
      ∀ {bound body body' : Term},
        MEqRed ({ bound := bound, kind := .sub } :: head ::
          { bound := old, kind := .equ } :: Γ) [] body body' →
        MEqRed ({ bound := bound, kind := .sub } :: head ::
          { bound := new, kind := .equ } :: Γ) [] body body')
    (hBetBodyReplace :
      ∀ {bound body body' : Term},
        MEqRed ({ bound := bound, kind := .sub } :: head ::
          { bound := old, kind := .equ } :: Γ) (Stack.shift 0 (Stack.shift 0 tail))
          body body' →
        MEqRed ({ bound := bound, kind := .sub } :: head ::
          { bound := new, kind := .equ } :: Γ) (Stack.shift 0 (Stack.shift 0 tail))
          body body')
    (hFOpBodyReplace :
      ∀ {arg body body' : Term} {rest : Stack},
        Term.Scoped (Ctx.depth (head :: { bound := old, kind := .equ } :: Γ)) arg →
        Stack.shift 0 tail = arg :: rest →
        MEqRed ({ bound := arg, kind := .equ } :: head ::
          { bound := old, kind := .equ } :: Γ) (Stack.shift 0 rest) body body' →
        MSubStar ({ bound := arg, kind := .equ } :: head ::
          { bound := new, kind := .equ } :: Γ) (Stack.shift 0 rest) body body')
    (h : MEqRedStar (head :: { bound := old, kind := .equ } :: Γ)
      (Stack.shift 0 tail) u v) :
    MSubStar (head :: { bound := new, kind := .equ } :: Γ)
      (Stack.shift 0 tail) u v :=
  meqRedStar_replace_from_step_replacement
    (meqRed_equ_under_head_shifted_replace_from_tail_lift
      hpvOldTail hpvNewTail hNewScoped hHeadOld hHeadNew hOldNewTail
      hSelfReplace hAppOpReplace hNilReplace hFunBodyReplace hBetBodyReplace
      hFOpBodyReplace)
    h

/-- One-step subtype replacement below a preserved head, where the
old-to-new changed-head equivalence is already available at the preserved
head's tail stack. The `Ms-Equ` branch reuses the corresponding equivalence
replacement package. -/
theorem msubRed_equ_under_head_shifted_replace_from_tail_lift {Γ : Ctx}
    {tail : Stack} {head : CtxEntry} {old new u v : Term}
    (hpvOldTail : PrevalidExt ({ bound := old, kind := .equ } :: Γ) tail)
    (hpvNewTail : PrevalidExt ({ bound := new, kind := .equ } :: Γ) tail)
    (hNewScoped : Term.Scoped Γ.depth new)
    (hHeadOld : Prevalid (head :: { bound := old, kind := .equ } :: Γ))
    (hHeadNew : Prevalid (head :: { bound := new, kind := .equ } :: Γ))
    (hOldNewTail : MEqRed ({ bound := new, kind := .equ } :: Γ) tail
      (Term.shift 0 old) (Term.shift 0 new))
    (hEqSelfReplace :
      ∀ {u v : Term},
        MEqRed (head :: { bound := old, kind := .equ } :: Γ)
          (Stack.shift 0 tail) u v →
        MSubStar (head :: { bound := new, kind := .equ } :: Γ)
          (Stack.shift 0 tail) u v)
    (hEqAppOpReplace :
      ∀ {op op' arg : Term},
        MEqRed (head :: { bound := old, kind := .equ } :: Γ)
          (arg :: Stack.shift 0 tail) op op' →
        MEqRed (head :: { bound := new, kind := .equ } :: Γ)
          (arg :: Stack.shift 0 tail) op op')
    (hNilReplace :
      ∀ {arg arg' : Term},
        MEqRed (head :: { bound := old, kind := .equ } :: Γ) [] arg arg' →
        MEqRed (head :: { bound := new, kind := .equ } :: Γ) [] arg arg')
    (hEqFunBodyReplace :
      ∀ {bound body body' : Term},
        MEqRed ({ bound := bound, kind := .sub } :: head ::
          { bound := old, kind := .equ } :: Γ) [] body body' →
        MEqRed ({ bound := bound, kind := .sub } :: head ::
          { bound := new, kind := .equ } :: Γ) [] body body')
    (hEqBetBodyReplace :
      ∀ {bound body body' : Term},
        MEqRed ({ bound := bound, kind := .sub } :: head ::
          { bound := old, kind := .equ } :: Γ) (Stack.shift 0 (Stack.shift 0 tail))
          body body' →
        MEqRed ({ bound := bound, kind := .sub } :: head ::
          { bound := new, kind := .equ } :: Γ) (Stack.shift 0 (Stack.shift 0 tail))
          body body')
    (hEqFOpBodyReplace :
      ∀ {arg body body' : Term} {rest : Stack},
        Term.Scoped (Ctx.depth (head :: { bound := old, kind := .equ } :: Γ)) arg →
        Stack.shift 0 tail = arg :: rest →
        MEqRed ({ bound := arg, kind := .equ } :: head ::
          { bound := old, kind := .equ } :: Γ) (Stack.shift 0 rest) body body' →
        MSubStar ({ bound := arg, kind := .equ } :: head ::
          { bound := new, kind := .equ } :: Γ) (Stack.shift 0 rest) body body')
    (hAppOpReplace :
      ∀ {op op' arg : Term},
        MSubRed (head :: { bound := old, kind := .equ } :: Γ)
          (arg :: Stack.shift 0 tail) op op' →
        Term.Scoped (Ctx.depth (head :: { bound := old, kind := .equ } :: Γ)) arg →
        MSubStar (head :: { bound := new, kind := .equ } :: Γ)
          (arg :: Stack.shift 0 tail) op op')
    (hFunBodyReplace :
      ∀ {bound body body' : Term},
        MSubRed ({ bound := bound, kind := .sub } :: head ::
          { bound := old, kind := .equ } :: Γ) [] body body' →
        MSubRed ({ bound := bound, kind := .sub } :: head ::
          { bound := new, kind := .equ } :: Γ) [] body body')
    (hFOpBodyReplace :
      ∀ {arg body body' : Term} {rest : Stack},
        Term.Scoped (Ctx.depth (head :: { bound := old, kind := .equ } :: Γ)) arg →
        Stack.shift 0 tail = arg :: rest →
        MSubRed ({ bound := arg, kind := .equ } :: head ::
          { bound := old, kind := .equ } :: Γ) (Stack.shift 0 rest) body body' →
        MSubStar ({ bound := arg, kind := .equ } :: head ::
          { bound := new, kind := .equ } :: Γ) (Stack.shift 0 rest) body body')
    (h : MSubRed (head :: { bound := old, kind := .equ } :: Γ)
      (Stack.shift 0 tail) u v) :
    MSubStar (head :: { bound := new, kind := .equ } :: Γ)
      (Stack.shift 0 tail) u v := by
  exact msubRed_equ_under_head_replace_from_replacements
    (PrevalidExt.weaken_head hpvOldTail hHeadOld) hNewScoped
    (meqRed_equ_under_head_shifted_replace_from_tail_lift
      hpvOldTail hpvNewTail hNewScoped hHeadOld hHeadNew hOldNewTail
      hEqSelfReplace hEqAppOpReplace hNilReplace hEqFunBodyReplace
      hEqBetBodyReplace hEqFOpBodyReplace)
    hAppOpReplace hNilReplace hFunBodyReplace hFOpBodyReplace h

/-- Chain-level counterpart of
`msubRed_equ_under_head_shifted_replace_from_tail_lift`. -/
theorem msubRedStar_equ_under_head_shifted_replace_from_tail_lift {Γ : Ctx}
    {tail : Stack} {head : CtxEntry} {old new u v : Term}
    (hpvOldTail : PrevalidExt ({ bound := old, kind := .equ } :: Γ) tail)
    (hpvNewTail : PrevalidExt ({ bound := new, kind := .equ } :: Γ) tail)
    (hNewScoped : Term.Scoped Γ.depth new)
    (hHeadOld : Prevalid (head :: { bound := old, kind := .equ } :: Γ))
    (hHeadNew : Prevalid (head :: { bound := new, kind := .equ } :: Γ))
    (hOldNewTail : MEqRed ({ bound := new, kind := .equ } :: Γ) tail
      (Term.shift 0 old) (Term.shift 0 new))
    (hEqSelfReplace :
      ∀ {u v : Term},
        MEqRed (head :: { bound := old, kind := .equ } :: Γ)
          (Stack.shift 0 tail) u v →
        MSubStar (head :: { bound := new, kind := .equ } :: Γ)
          (Stack.shift 0 tail) u v)
    (hEqAppOpReplace :
      ∀ {op op' arg : Term},
        MEqRed (head :: { bound := old, kind := .equ } :: Γ)
          (arg :: Stack.shift 0 tail) op op' →
        MEqRed (head :: { bound := new, kind := .equ } :: Γ)
          (arg :: Stack.shift 0 tail) op op')
    (hNilReplace :
      ∀ {arg arg' : Term},
        MEqRed (head :: { bound := old, kind := .equ } :: Γ) [] arg arg' →
        MEqRed (head :: { bound := new, kind := .equ } :: Γ) [] arg arg')
    (hEqFunBodyReplace :
      ∀ {bound body body' : Term},
        MEqRed ({ bound := bound, kind := .sub } :: head ::
          { bound := old, kind := .equ } :: Γ) [] body body' →
        MEqRed ({ bound := bound, kind := .sub } :: head ::
          { bound := new, kind := .equ } :: Γ) [] body body')
    (hEqBetBodyReplace :
      ∀ {bound body body' : Term},
        MEqRed ({ bound := bound, kind := .sub } :: head ::
          { bound := old, kind := .equ } :: Γ) (Stack.shift 0 (Stack.shift 0 tail))
          body body' →
        MEqRed ({ bound := bound, kind := .sub } :: head ::
          { bound := new, kind := .equ } :: Γ) (Stack.shift 0 (Stack.shift 0 tail))
          body body')
    (hEqFOpBodyReplace :
      ∀ {arg body body' : Term} {rest : Stack},
        Term.Scoped (Ctx.depth (head :: { bound := old, kind := .equ } :: Γ)) arg →
        Stack.shift 0 tail = arg :: rest →
        MEqRed ({ bound := arg, kind := .equ } :: head ::
          { bound := old, kind := .equ } :: Γ) (Stack.shift 0 rest) body body' →
        MSubStar ({ bound := arg, kind := .equ } :: head ::
          { bound := new, kind := .equ } :: Γ) (Stack.shift 0 rest) body body')
    (hAppOpReplace :
      ∀ {op op' arg : Term},
        MSubRed (head :: { bound := old, kind := .equ } :: Γ)
          (arg :: Stack.shift 0 tail) op op' →
        Term.Scoped (Ctx.depth (head :: { bound := old, kind := .equ } :: Γ)) arg →
        MSubStar (head :: { bound := new, kind := .equ } :: Γ)
          (arg :: Stack.shift 0 tail) op op')
    (hFunBodyReplace :
      ∀ {bound body body' : Term},
        MSubRed ({ bound := bound, kind := .sub } :: head ::
          { bound := old, kind := .equ } :: Γ) [] body body' →
        MSubRed ({ bound := bound, kind := .sub } :: head ::
          { bound := new, kind := .equ } :: Γ) [] body body')
    (hFOpBodyReplace :
      ∀ {arg body body' : Term} {rest : Stack},
        Term.Scoped (Ctx.depth (head :: { bound := old, kind := .equ } :: Γ)) arg →
        Stack.shift 0 tail = arg :: rest →
        MSubRed ({ bound := arg, kind := .equ } :: head ::
          { bound := old, kind := .equ } :: Γ) (Stack.shift 0 rest) body body' →
        MSubStar ({ bound := arg, kind := .equ } :: head ::
          { bound := new, kind := .equ } :: Γ) (Stack.shift 0 rest) body body')
    (h : MSubRedStar (head :: { bound := old, kind := .equ } :: Γ)
      (Stack.shift 0 tail) u v) :
    MSubStar (head :: { bound := new, kind := .equ } :: Γ)
      (Stack.shift 0 tail) u v :=
  msubRedStar_replace_from_step_replacement
    (msubRed_equ_under_head_shifted_replace_from_tail_lift
      hpvOldTail hpvNewTail hNewScoped hHeadOld hHeadNew hOldNewTail
      hEqSelfReplace hEqAppOpReplace hNilReplace hEqFunBodyReplace
      hEqBetBodyReplace hEqFOpBodyReplace hAppOpReplace hFunBodyReplace
      hFOpBodyReplace)
    h

/-- Function-valued under-head shifted equivalence replacement from
tail-stack old-to-new lifts. The new tail and preserved-head prevalidity
witnesses are derived from the old tail witness at each residual stack. -/
theorem meqRedStar_equ_under_head_shifted_replace_function_from_tail_lift
    {Γ : Ctx} {head : CtxEntry} {old new u v : Term}
    (hNewScoped : Term.Scoped Γ.depth new)
    (hHeadOld : Prevalid (head :: { bound := old, kind := .equ } :: Γ))
    (hOldNewTail :
      ∀ {tail : Stack},
        PrevalidExt ({ bound := old, kind := .equ } :: Γ) tail →
        MEqRed ({ bound := new, kind := .equ } :: Γ) tail
          (Term.shift 0 old) (Term.shift 0 new))
    (hSelfReplace :
      ∀ {tail : Stack},
        PrevalidExt ({ bound := old, kind := .equ } :: Γ) tail →
        ∀ {u v : Term},
          MEqRed (head :: { bound := old, kind := .equ } :: Γ)
            (Stack.shift 0 tail) u v →
          MSubStar (head :: { bound := new, kind := .equ } :: Γ)
            (Stack.shift 0 tail) u v)
    (hAppOpReplace :
      ∀ {tail : Stack},
        PrevalidExt ({ bound := old, kind := .equ } :: Γ) tail →
        ∀ {op op' arg : Term},
          MEqRed (head :: { bound := old, kind := .equ } :: Γ)
            (arg :: Stack.shift 0 tail) op op' →
          MEqRed (head :: { bound := new, kind := .equ } :: Γ)
            (arg :: Stack.shift 0 tail) op op')
    (hNilReplace :
      ∀ {arg arg' : Term},
        MEqRed (head :: { bound := old, kind := .equ } :: Γ) [] arg arg' →
        MEqRed (head :: { bound := new, kind := .equ } :: Γ) [] arg arg')
    (hFunBodyReplace :
      ∀ {bound body body' : Term},
        MEqRed ({ bound := bound, kind := .sub } :: head ::
          { bound := old, kind := .equ } :: Γ) [] body body' →
        MEqRed ({ bound := bound, kind := .sub } :: head ::
          { bound := new, kind := .equ } :: Γ) [] body body')
    (hBetBodyReplace :
      ∀ {tail : Stack},
        PrevalidExt ({ bound := old, kind := .equ } :: Γ) tail →
        ∀ {bound body body' : Term},
          MEqRed ({ bound := bound, kind := .sub } :: head ::
            { bound := old, kind := .equ } :: Γ)
            (Stack.shift 0 (Stack.shift 0 tail)) body body' →
          MEqRed ({ bound := bound, kind := .sub } :: head ::
            { bound := new, kind := .equ } :: Γ)
            (Stack.shift 0 (Stack.shift 0 tail)) body body')
    (hFOpBodyReplace :
      ∀ {tail : Stack},
        PrevalidExt ({ bound := old, kind := .equ } :: Γ) tail →
        ∀ {arg body body' : Term} {rest : Stack},
          Term.Scoped (Ctx.depth (head :: { bound := old, kind := .equ } :: Γ)) arg →
          Stack.shift 0 tail = arg :: rest →
          MEqRed ({ bound := arg, kind := .equ } :: head ::
            { bound := old, kind := .equ } :: Γ) (Stack.shift 0 rest) body body' →
          MSubStar ({ bound := arg, kind := .equ } :: head ::
            { bound := new, kind := .equ } :: Γ) (Stack.shift 0 rest) body body')
    (h :
      ∀ {tail : Stack},
        PrevalidExt ({ bound := old, kind := .equ } :: Γ) tail →
        MEqRedStar (head :: { bound := old, kind := .equ } :: Γ)
          (Stack.shift 0 tail) u v) :
    ∀ {tail : Stack},
      PrevalidExt ({ bound := old, kind := .equ } :: Γ) tail →
      MSubStar (head :: { bound := new, kind := .equ } :: Γ)
        (Stack.shift 0 tail) u v :=
  fun hpvOldTail =>
    meqRedStar_equ_under_head_shifted_replace_from_tail_lift hpvOldTail
      (PrevalidExt.equ_head_replace hpvOldTail hNewScoped) hNewScoped
      hHeadOld (Prevalid.equ_under_head_replace hHeadOld hNewScoped)
      (hOldNewTail hpvOldTail) (hSelfReplace hpvOldTail)
      (hAppOpReplace hpvOldTail) hNilReplace hFunBodyReplace
      (hBetBodyReplace hpvOldTail) (hFOpBodyReplace hpvOldTail)
      (h hpvOldTail)

/-- Function-valued under-head shifted subtype replacement from tail-stack
old-to-new lifts. This packages the subtype chain replacement at every
residual tail stack, deriving the new-context prevalidity locally. -/
theorem msubRedStar_equ_under_head_shifted_replace_function_from_tail_lift
    {Γ : Ctx} {head : CtxEntry} {old new u v : Term}
    (hNewScoped : Term.Scoped Γ.depth new)
    (hHeadOld : Prevalid (head :: { bound := old, kind := .equ } :: Γ))
    (hOldNewTail :
      ∀ {tail : Stack},
        PrevalidExt ({ bound := old, kind := .equ } :: Γ) tail →
        MEqRed ({ bound := new, kind := .equ } :: Γ) tail
          (Term.shift 0 old) (Term.shift 0 new))
    (hEqSelfReplace :
      ∀ {tail : Stack},
        PrevalidExt ({ bound := old, kind := .equ } :: Γ) tail →
        ∀ {u v : Term},
          MEqRed (head :: { bound := old, kind := .equ } :: Γ)
            (Stack.shift 0 tail) u v →
          MSubStar (head :: { bound := new, kind := .equ } :: Γ)
            (Stack.shift 0 tail) u v)
    (hEqAppOpReplace :
      ∀ {tail : Stack},
        PrevalidExt ({ bound := old, kind := .equ } :: Γ) tail →
        ∀ {op op' arg : Term},
          MEqRed (head :: { bound := old, kind := .equ } :: Γ)
            (arg :: Stack.shift 0 tail) op op' →
          MEqRed (head :: { bound := new, kind := .equ } :: Γ)
            (arg :: Stack.shift 0 tail) op op')
    (hNilReplace :
      ∀ {arg arg' : Term},
        MEqRed (head :: { bound := old, kind := .equ } :: Γ) [] arg arg' →
        MEqRed (head :: { bound := new, kind := .equ } :: Γ) [] arg arg')
    (hEqFunBodyReplace :
      ∀ {bound body body' : Term},
        MEqRed ({ bound := bound, kind := .sub } :: head ::
          { bound := old, kind := .equ } :: Γ) [] body body' →
        MEqRed ({ bound := bound, kind := .sub } :: head ::
          { bound := new, kind := .equ } :: Γ) [] body body')
    (hEqBetBodyReplace :
      ∀ {tail : Stack},
        PrevalidExt ({ bound := old, kind := .equ } :: Γ) tail →
        ∀ {bound body body' : Term},
          MEqRed ({ bound := bound, kind := .sub } :: head ::
            { bound := old, kind := .equ } :: Γ)
            (Stack.shift 0 (Stack.shift 0 tail)) body body' →
          MEqRed ({ bound := bound, kind := .sub } :: head ::
            { bound := new, kind := .equ } :: Γ)
            (Stack.shift 0 (Stack.shift 0 tail)) body body')
    (hEqFOpBodyReplace :
      ∀ {tail : Stack},
        PrevalidExt ({ bound := old, kind := .equ } :: Γ) tail →
        ∀ {arg body body' : Term} {rest : Stack},
          Term.Scoped (Ctx.depth (head :: { bound := old, kind := .equ } :: Γ)) arg →
          Stack.shift 0 tail = arg :: rest →
          MEqRed ({ bound := arg, kind := .equ } :: head ::
            { bound := old, kind := .equ } :: Γ) (Stack.shift 0 rest) body body' →
          MSubStar ({ bound := arg, kind := .equ } :: head ::
            { bound := new, kind := .equ } :: Γ) (Stack.shift 0 rest) body body')
    (hAppOpReplace :
      ∀ {tail : Stack},
        PrevalidExt ({ bound := old, kind := .equ } :: Γ) tail →
        ∀ {op op' arg : Term},
          MSubRed (head :: { bound := old, kind := .equ } :: Γ)
            (arg :: Stack.shift 0 tail) op op' →
          Term.Scoped (Ctx.depth (head :: { bound := old, kind := .equ } :: Γ)) arg →
          MSubStar (head :: { bound := new, kind := .equ } :: Γ)
            (arg :: Stack.shift 0 tail) op op')
    (hFunBodyReplace :
      ∀ {bound body body' : Term},
        MSubRed ({ bound := bound, kind := .sub } :: head ::
          { bound := old, kind := .equ } :: Γ) [] body body' →
        MSubRed ({ bound := bound, kind := .sub } :: head ::
          { bound := new, kind := .equ } :: Γ) [] body body')
    (hFOpBodyReplace :
      ∀ {tail : Stack},
        PrevalidExt ({ bound := old, kind := .equ } :: Γ) tail →
        ∀ {arg body body' : Term} {rest : Stack},
          Term.Scoped (Ctx.depth (head :: { bound := old, kind := .equ } :: Γ)) arg →
          Stack.shift 0 tail = arg :: rest →
          MSubRed ({ bound := arg, kind := .equ } :: head ::
            { bound := old, kind := .equ } :: Γ) (Stack.shift 0 rest) body body' →
          MSubStar ({ bound := arg, kind := .equ } :: head ::
            { bound := new, kind := .equ } :: Γ) (Stack.shift 0 rest) body body')
    (h :
      ∀ {tail : Stack},
        PrevalidExt ({ bound := old, kind := .equ } :: Γ) tail →
        MSubRedStar (head :: { bound := old, kind := .equ } :: Γ)
          (Stack.shift 0 tail) u v) :
    ∀ {tail : Stack},
      PrevalidExt ({ bound := old, kind := .equ } :: Γ) tail →
      MSubStar (head :: { bound := new, kind := .equ } :: Γ)
        (Stack.shift 0 tail) u v :=
  fun hpvOldTail =>
    msubRedStar_equ_under_head_shifted_replace_from_tail_lift hpvOldTail
      (PrevalidExt.equ_head_replace hpvOldTail hNewScoped) hNewScoped
      hHeadOld (Prevalid.equ_under_head_replace hHeadOld hNewScoped)
      (hOldNewTail hpvOldTail) (hEqSelfReplace hpvOldTail)
      (hEqAppOpReplace hpvOldTail) hNilReplace hEqFunBodyReplace
      (hEqBetBodyReplace hpvOldTail) (hEqFOpBodyReplace hpvOldTail)
      (hAppOpReplace hpvOldTail) hFunBodyReplace (hFOpBodyReplace hpvOldTail)
      (h hpvOldTail)

/-- Build the `Me-FOp` body handler expected by the shifted changed-head
replacement package from tail-stack old-to-new lifts. This packages the
common work of extracting prevalidity from `Stack.shift 0 s = operand :: rest`
and weakening the old-to-new bridge under the exposed operand head. -/
theorem meq_equ_head_shifted_fop_body_handler_from_tail_lifts {Γ : Ctx}
    {s : Stack} {old new : Term}
    (hpvOld : PrevalidExt ({ bound := old, kind := .equ } :: Γ) (Stack.shift 0 s))
    (hpvNew : PrevalidExt ({ bound := new, kind := .equ } :: Γ) (Stack.shift 0 s))
    (hNewScoped : Term.Scoped Γ.depth new)
    (hOldNewTail :
      ∀ {operand : Term} {rest : Stack},
        Term.Scoped (Ctx.depth ({ bound := old, kind := .equ } :: Γ)) operand →
        Stack.shift 0 s = operand :: rest →
        MEqRed ({ bound := new, kind := .equ } :: Γ) rest
          (Term.shift 0 old) (Term.shift 0 new))
    (hSelfReplace :
      ∀ {operand : Term} {rest : Stack} {u v : Term},
        Term.Scoped (Ctx.depth ({ bound := old, kind := .equ } :: Γ)) operand →
        Stack.shift 0 s = operand :: rest →
        MEqRed ({ bound := operand, kind := .equ } ::
          { bound := old, kind := .equ } :: Γ) (Stack.shift 0 rest) u v →
        MSubStar ({ bound := operand, kind := .equ } ::
          { bound := new, kind := .equ } :: Γ) (Stack.shift 0 rest) u v)
    (hAppOpReplace :
      ∀ {operand : Term} {rest : Stack} {op op' arg : Term},
        Term.Scoped (Ctx.depth ({ bound := old, kind := .equ } :: Γ)) operand →
        Stack.shift 0 s = operand :: rest →
        MEqRed ({ bound := operand, kind := .equ } ::
          { bound := old, kind := .equ } :: Γ) (arg :: Stack.shift 0 rest) op op' →
        MEqRed ({ bound := operand, kind := .equ } ::
          { bound := new, kind := .equ } :: Γ) (arg :: Stack.shift 0 rest) op op')
    (hNilReplace :
      ∀ {operand : Term} {rest : Stack} {u v : Term},
        Term.Scoped (Ctx.depth ({ bound := old, kind := .equ } :: Γ)) operand →
        Stack.shift 0 s = operand :: rest →
        MEqRed ({ bound := operand, kind := .equ } ::
          { bound := old, kind := .equ } :: Γ) [] u v →
        MEqRed ({ bound := operand, kind := .equ } ::
          { bound := new, kind := .equ } :: Γ) [] u v)
    (hFunBodyReplace :
      ∀ {operand : Term} {rest : Stack} {bound body body' : Term},
        Term.Scoped (Ctx.depth ({ bound := old, kind := .equ } :: Γ)) operand →
        Stack.shift 0 s = operand :: rest →
        MEqRed ({ bound := bound, kind := .sub } ::
          { bound := operand, kind := .equ } ::
          { bound := old, kind := .equ } :: Γ) [] body body' →
        MEqRed ({ bound := bound, kind := .sub } ::
          { bound := operand, kind := .equ } ::
          { bound := new, kind := .equ } :: Γ) [] body body')
    (hBetBodyReplace :
      ∀ {operand : Term} {rest : Stack} {bound body body' : Term},
        Term.Scoped (Ctx.depth ({ bound := old, kind := .equ } :: Γ)) operand →
        Stack.shift 0 s = operand :: rest →
        MEqRed ({ bound := bound, kind := .sub } ::
          { bound := operand, kind := .equ } ::
          { bound := old, kind := .equ } :: Γ) (Stack.shift 0 (Stack.shift 0 rest))
          body body' →
        MEqRed ({ bound := bound, kind := .sub } ::
          { bound := operand, kind := .equ } ::
          { bound := new, kind := .equ } :: Γ) (Stack.shift 0 (Stack.shift 0 rest))
          body body')
    (hFOpBodyReplace :
      ∀ {operand : Term} {rest : Stack} {inner body body' : Term}
          {innerRest : Stack},
        Term.Scoped (Ctx.depth ({ bound := old, kind := .equ } :: Γ)) operand →
        Stack.shift 0 s = operand :: rest →
        Term.Scoped (Ctx.depth ({ bound := operand, kind := .equ } ::
          { bound := old, kind := .equ } :: Γ)) inner →
        Stack.shift 0 rest = inner :: innerRest →
        MEqRed ({ bound := inner, kind := .equ } ::
          { bound := operand, kind := .equ } ::
          { bound := old, kind := .equ } :: Γ) (Stack.shift 0 innerRest) body body' →
        MSubStar ({ bound := inner, kind := .equ } ::
          { bound := operand, kind := .equ } ::
          { bound := new, kind := .equ } :: Γ) (Stack.shift 0 innerRest) body body')
    {operand body body' : Term} {rest : Stack}
    (hOperand : Term.Scoped (Ctx.depth ({ bound := old, kind := .equ } :: Γ)) operand)
    (hStack : Stack.shift 0 s = operand :: rest)
    (hBody : MEqRed ({ bound := operand, kind := .equ } ::
      { bound := old, kind := .equ } :: Γ) (Stack.shift 0 rest) body body') :
    MSubStar ({ bound := operand, kind := .equ } ::
      { bound := new, kind := .equ } :: Γ) (Stack.shift 0 rest) body body' := by
  have hpvOldTail : PrevalidExt ({ bound := old, kind := .equ } :: Γ) rest :=
    PrevalidExt.tail_of_eq_cons hpvOld hStack
  have hpvNewTail : PrevalidExt ({ bound := new, kind := .equ } :: Γ) rest :=
    PrevalidExt.tail_of_eq_cons hpvNew hStack
  have hOperandNew :
      Term.Scoped (Ctx.depth ({ bound := new, kind := .equ } :: Γ)) operand :=
    PrevalidExt.head_scoped_of_eq_cons hpvNew hStack
  have hHeadOld : Prevalid ({ bound := operand, kind := .equ } ::
      { bound := old, kind := .equ } :: Γ) :=
    Prevalid.equ (PrevalidExt.ctx hpvOldTail) hOperand
  have hHeadNew : Prevalid ({ bound := operand, kind := .equ } ::
      { bound := new, kind := .equ } :: Γ) :=
    Prevalid.equ (PrevalidExt.ctx hpvNewTail) hOperandNew
  exact meqRed_equ_under_head_shifted_replace_from_tail_lift
    hpvOldTail hpvNewTail hNewScoped hHeadOld hHeadNew
    (hOldNewTail hOperand hStack)
    (fun h => hSelfReplace hOperand hStack h)
    (fun h => hAppOpReplace hOperand hStack h)
    (fun h => hNilReplace hOperand hStack h)
    (fun h => hFunBodyReplace hOperand hStack h)
    (fun h => hBetBodyReplace hOperand hStack h)
    (fun hInner hInnerStack h =>
      hFOpBodyReplace hOperand hStack hInner hInnerStack h)
    hBody

/-- Build the `Ms-FOp` body handler expected by the shifted changed-head
replacement package from tail-stack old-to-new lifts, reusing the
corresponding equivalence handler for `Ms-Equ` branches. -/
theorem msub_equ_head_shifted_fop_body_handler_from_tail_lifts {Γ : Ctx}
    {s : Stack} {old new : Term}
    (hpvOld : PrevalidExt ({ bound := old, kind := .equ } :: Γ) (Stack.shift 0 s))
    (hpvNew : PrevalidExt ({ bound := new, kind := .equ } :: Γ) (Stack.shift 0 s))
    (hNewScoped : Term.Scoped Γ.depth new)
    (hOldNewTail :
      ∀ {operand : Term} {rest : Stack},
        Term.Scoped (Ctx.depth ({ bound := old, kind := .equ } :: Γ)) operand →
        Stack.shift 0 s = operand :: rest →
        MEqRed ({ bound := new, kind := .equ } :: Γ) rest
          (Term.shift 0 old) (Term.shift 0 new))
    (hEqSelfReplace :
      ∀ {operand : Term} {rest : Stack} {u v : Term},
        Term.Scoped (Ctx.depth ({ bound := old, kind := .equ } :: Γ)) operand →
        Stack.shift 0 s = operand :: rest →
        MEqRed ({ bound := operand, kind := .equ } ::
          { bound := old, kind := .equ } :: Γ) (Stack.shift 0 rest) u v →
        MSubStar ({ bound := operand, kind := .equ } ::
          { bound := new, kind := .equ } :: Γ) (Stack.shift 0 rest) u v)
    (hEqAppOpReplace :
      ∀ {operand : Term} {rest : Stack} {op op' arg : Term},
        Term.Scoped (Ctx.depth ({ bound := old, kind := .equ } :: Γ)) operand →
        Stack.shift 0 s = operand :: rest →
        MEqRed ({ bound := operand, kind := .equ } ::
          { bound := old, kind := .equ } :: Γ) (arg :: Stack.shift 0 rest) op op' →
        MEqRed ({ bound := operand, kind := .equ } ::
          { bound := new, kind := .equ } :: Γ) (arg :: Stack.shift 0 rest) op op')
    (hNilReplace :
      ∀ {operand : Term} {rest : Stack} {u v : Term},
        Term.Scoped (Ctx.depth ({ bound := old, kind := .equ } :: Γ)) operand →
        Stack.shift 0 s = operand :: rest →
        MEqRed ({ bound := operand, kind := .equ } ::
          { bound := old, kind := .equ } :: Γ) [] u v →
        MEqRed ({ bound := operand, kind := .equ } ::
          { bound := new, kind := .equ } :: Γ) [] u v)
    (hEqFunBodyReplace :
      ∀ {operand : Term} {rest : Stack} {bound body body' : Term},
        Term.Scoped (Ctx.depth ({ bound := old, kind := .equ } :: Γ)) operand →
        Stack.shift 0 s = operand :: rest →
        MEqRed ({ bound := bound, kind := .sub } ::
          { bound := operand, kind := .equ } ::
          { bound := old, kind := .equ } :: Γ) [] body body' →
        MEqRed ({ bound := bound, kind := .sub } ::
          { bound := operand, kind := .equ } ::
          { bound := new, kind := .equ } :: Γ) [] body body')
    (hEqBetBodyReplace :
      ∀ {operand : Term} {rest : Stack} {bound body body' : Term},
        Term.Scoped (Ctx.depth ({ bound := old, kind := .equ } :: Γ)) operand →
        Stack.shift 0 s = operand :: rest →
        MEqRed ({ bound := bound, kind := .sub } ::
          { bound := operand, kind := .equ } ::
          { bound := old, kind := .equ } :: Γ) (Stack.shift 0 (Stack.shift 0 rest))
          body body' →
        MEqRed ({ bound := bound, kind := .sub } ::
          { bound := operand, kind := .equ } ::
          { bound := new, kind := .equ } :: Γ) (Stack.shift 0 (Stack.shift 0 rest))
          body body')
    (hEqFOpBodyReplace :
      ∀ {operand : Term} {rest : Stack} {inner body body' : Term}
          {innerRest : Stack},
        Term.Scoped (Ctx.depth ({ bound := old, kind := .equ } :: Γ)) operand →
        Stack.shift 0 s = operand :: rest →
        Term.Scoped (Ctx.depth ({ bound := operand, kind := .equ } ::
          { bound := old, kind := .equ } :: Γ)) inner →
        Stack.shift 0 rest = inner :: innerRest →
        MEqRed ({ bound := inner, kind := .equ } ::
          { bound := operand, kind := .equ } ::
          { bound := old, kind := .equ } :: Γ) (Stack.shift 0 innerRest) body body' →
        MSubStar ({ bound := inner, kind := .equ } ::
          { bound := operand, kind := .equ } ::
          { bound := new, kind := .equ } :: Γ) (Stack.shift 0 innerRest) body body')
    (hAppOpReplace :
      ∀ {operand : Term} {rest : Stack} {op op' arg : Term},
        Term.Scoped (Ctx.depth ({ bound := old, kind := .equ } :: Γ)) operand →
        Stack.shift 0 s = operand :: rest →
        MSubRed ({ bound := operand, kind := .equ } ::
          { bound := old, kind := .equ } :: Γ) (arg :: Stack.shift 0 rest) op op' →
        Term.Scoped (Ctx.depth ({ bound := operand, kind := .equ } ::
          { bound := old, kind := .equ } :: Γ)) arg →
        MSubStar ({ bound := operand, kind := .equ } ::
          { bound := new, kind := .equ } :: Γ) (arg :: Stack.shift 0 rest) op op')
    (hFunBodyReplace :
      ∀ {operand : Term} {rest : Stack} {bound body body' : Term},
        Term.Scoped (Ctx.depth ({ bound := old, kind := .equ } :: Γ)) operand →
        Stack.shift 0 s = operand :: rest →
        MSubRed ({ bound := bound, kind := .sub } ::
          { bound := operand, kind := .equ } ::
          { bound := old, kind := .equ } :: Γ) [] body body' →
        MSubRed ({ bound := bound, kind := .sub } ::
          { bound := operand, kind := .equ } ::
          { bound := new, kind := .equ } :: Γ) [] body body')
    (hFOpBodyReplace :
      ∀ {operand : Term} {rest : Stack} {inner body body' : Term}
          {innerRest : Stack},
        Term.Scoped (Ctx.depth ({ bound := old, kind := .equ } :: Γ)) operand →
        Stack.shift 0 s = operand :: rest →
        Term.Scoped (Ctx.depth ({ bound := operand, kind := .equ } ::
          { bound := old, kind := .equ } :: Γ)) inner →
        Stack.shift 0 rest = inner :: innerRest →
        MSubRed ({ bound := inner, kind := .equ } ::
          { bound := operand, kind := .equ } ::
          { bound := old, kind := .equ } :: Γ) (Stack.shift 0 innerRest) body body' →
        MSubStar ({ bound := inner, kind := .equ } ::
          { bound := operand, kind := .equ } ::
          { bound := new, kind := .equ } :: Γ) (Stack.shift 0 innerRest) body body')
    {operand body body' : Term} {rest : Stack}
    (hOperand : Term.Scoped (Ctx.depth ({ bound := old, kind := .equ } :: Γ)) operand)
    (hStack : Stack.shift 0 s = operand :: rest)
    (hBody : MSubRed ({ bound := operand, kind := .equ } ::
      { bound := old, kind := .equ } :: Γ) (Stack.shift 0 rest) body body') :
    MSubStar ({ bound := operand, kind := .equ } ::
      { bound := new, kind := .equ } :: Γ) (Stack.shift 0 rest) body body' := by
  have hpvOldTail : PrevalidExt ({ bound := old, kind := .equ } :: Γ) rest :=
    PrevalidExt.tail_of_eq_cons hpvOld hStack
  have hpvNewTail : PrevalidExt ({ bound := new, kind := .equ } :: Γ) rest :=
    PrevalidExt.tail_of_eq_cons hpvNew hStack
  have hOperandNew :
      Term.Scoped (Ctx.depth ({ bound := new, kind := .equ } :: Γ)) operand :=
    PrevalidExt.head_scoped_of_eq_cons hpvNew hStack
  have hHeadOld : Prevalid ({ bound := operand, kind := .equ } ::
      { bound := old, kind := .equ } :: Γ) :=
    Prevalid.equ (PrevalidExt.ctx hpvOldTail) hOperand
  have hHeadNew : Prevalid ({ bound := operand, kind := .equ } ::
      { bound := new, kind := .equ } :: Γ) :=
    Prevalid.equ (PrevalidExt.ctx hpvNewTail) hOperandNew
  exact msubRed_equ_under_head_shifted_replace_from_tail_lift
    hpvOldTail hpvNewTail hNewScoped hHeadOld hHeadNew
    (hOldNewTail hOperand hStack)
    (fun h => hEqSelfReplace hOperand hStack h)
    (fun h => hEqAppOpReplace hOperand hStack h)
    (fun h => hNilReplace hOperand hStack h)
    (fun h => hEqFunBodyReplace hOperand hStack h)
    (fun h => hEqBetBodyReplace hOperand hStack h)
    (fun hInner hInnerStack h =>
      hEqFOpBodyReplace hOperand hStack hInner hInnerStack h)
    (fun h hArg => hAppOpReplace hOperand hStack h hArg)
    (fun h => hFunBodyReplace hOperand hStack h)
    (fun hInner hInnerStack h =>
      hFOpBodyReplace hOperand hStack hInner hInnerStack h)
    hBody

/-- A reflexive argument equivalence can always be lifted under a changed
`.equ` head and residual stack. This is the stack-stable base case for the
head `Me-Pro` bridge. -/
noncomputable def meq_equ_head_stack_lift_refl {Γ : Ctx} {s : Stack} {head t : Term}
    (hpvTail : PrevalidExt Γ s)
    (hHeadScoped : Term.Scoped Γ.depth head)
    (ht : Term.Scoped Γ.depth t) :
    MEqRed ({ bound := head, kind := .equ } :: Γ) (Stack.shift 0 s)
      (Term.shift 0 t) (Term.shift 0 t) := by
  have hpvHead : Prevalid ({ bound := head, kind := .equ } :: Γ) :=
    Prevalid.equ (PrevalidExt.ctx hpvTail) hHeadScoped
  exact MEqRed.refl (PrevalidExt.weaken_head hpvTail hpvHead)
    (Term.shift_scoped 0 Γ.depth t (Nat.zero_le _) ht)

/-- The `Me-Top` argument-equivalence step lifts under a changed `.equ` head
and residual stack. -/
noncomputable def meq_equ_head_stack_lift_top {Γ : Ctx} {s : Stack} {head : Term}
    (hpvTail : PrevalidExt Γ s)
    (hHeadScoped : Term.Scoped Γ.depth head) :
    MEqRed ({ bound := head, kind := .equ } :: Γ) (Stack.shift 0 s)
      (Term.shift 0 .top) (Term.shift 0 .top) :=
  meq_equ_head_stack_lift_refl hpvTail hHeadScoped Term.Scoped.top

/-- The `Me-Var` argument-equivalence step lifts under a changed `.equ` head
and residual stack by shifting the variable index through the new head. -/
noncomputable def meq_equ_head_stack_lift_var {Γ : Ctx} {s : Stack} {head : Term}
    {i : Nat}
    (hpvTail : PrevalidExt Γ s)
    (hHeadScoped : Term.Scoped Γ.depth head)
    (hi : i < Γ.depth) :
    MEqRed ({ bound := head, kind := .equ } :: Γ) (Stack.shift 0 s)
      (Term.shift 0 (.bvar i)) (Term.shift 0 (.bvar i)) :=
  meq_equ_head_stack_lift_refl hpvTail hHeadScoped (Term.Scoped.bvar hi)

/-- Recursive `Me-Pro` stack lift under a changed `.equ` head for a variable
coming from the original context. The new head shifts the promoted variable
to index `i + 1`; the looked-up bound reduction is supplied recursively. -/
noncomputable def meq_equ_head_stack_lift_pro {Γ : Ctx} {s : Stack}
    {head α α' : Term} {i : Nat}
    (hpvTail : PrevalidExt Γ s)
    (hHeadScoped : Term.Scoped Γ.depth head)
    (hb : Γ.equBinds i α)
    (hα : MEqRed ({ bound := head, kind := .equ } :: Γ) (Stack.shift 0 s)
      (Term.shift 0 α) (Term.shift 0 α')) :
    MEqRed ({ bound := head, kind := .equ } :: Γ) (Stack.shift 0 s)
      (Term.shift 0 (.bvar i)) (Term.shift 0 α') := by
  have hpvHead : Prevalid ({ bound := head, kind := .equ } :: Γ) :=
    Prevalid.equ (PrevalidExt.ctx hpvTail) hHeadScoped
  have hpv : PrevalidExt ({ bound := head, kind := .equ } :: Γ)
      (Stack.shift 0 s) :=
    PrevalidExt.weaken_head hpvTail hpvHead
  simpa [Ctx.shift_bvar_insertAtIndex] using
    MEqRed.pro hpv (Ctx.equBinds_weaken_head { bound := head, kind := .equ } hb) hα

/-- The `Me-TAp` argument-equivalence step lifts under a changed `.equ` head
and residual stack. -/
noncomputable def meq_equ_head_stack_lift_tAp {Γ : Ctx} {s : Stack} {head u : Term}
    (hpvTail : PrevalidExt Γ s)
    (hHeadScoped : Term.Scoped Γ.depth head)
    (hu : Term.Scoped Γ.depth u) :
    MEqRed ({ bound := head, kind := .equ } :: Γ) (Stack.shift 0 s)
      (Term.shift 0 (.app .top u)) (Term.shift 0 .top) := by
  have hpvHead : Prevalid ({ bound := head, kind := .equ } :: Γ) :=
    Prevalid.equ (PrevalidExt.ctx hpvTail) hHeadScoped
  have hpv : PrevalidExt ({ bound := head, kind := .equ } :: Γ)
      (Stack.shift 0 s) :=
    PrevalidExt.weaken_head hpvTail hpvHead
  exact MEqRed.tAp hpv
    (Term.shift_scoped 0 Γ.depth u (Nat.zero_le _) hu)

/-- Recursive `Me-App` stack lift under a changed `.equ` head. The operator
premise is required at the shifted operand stack, and the argument premise at
the empty stack, matching the de Bruijn `Me-App` constructor. -/
noncomputable def meq_equ_head_stack_lift_app {Γ : Ctx} {s : Stack}
    {head u u' v v' : Term}
    (hOp : MEqRed ({ bound := head, kind := .equ } :: Γ)
      (Term.shift 0 v :: Stack.shift 0 s) (Term.shift 0 u) (Term.shift 0 u'))
    (hArg : MEqRed ({ bound := head, kind := .equ } :: Γ) []
      (Term.shift 0 v) (Term.shift 0 v')) :
    MEqRed ({ bound := head, kind := .equ } :: Γ) (Stack.shift 0 s)
      (Term.shift 0 (.app u v)) (Term.shift 0 (.app u' v')) := by
  simpa [Stack.shift] using MEqRed.app hOp hArg

/-- Empty-stack `Me-Fun` lift under a changed `.equ` head. This is the only
case where a top-level `Me-Fun` step remains a `Me-Fun` step after entering
the changed head context. -/
noncomputable def meq_equ_head_stack_lift_fun_nil {Γ : Ctx}
    {head bound bound' body body' : Term}
    (hBound : MEqRed ({ bound := head, kind := .equ } :: Γ) []
      (Term.shift 0 bound) (Term.shift 0 bound'))
    (hBody : MEqRed ({ bound := Term.shift 0 bound, kind := .sub } ::
        { bound := head, kind := .equ } :: Γ) []
      (Term.shift 1 body) (Term.shift 1 body')) :
    MEqRed ({ bound := head, kind := .equ } :: Γ) []
      (Term.shift 0 (.abs bound body)) (Term.shift 0 (.abs bound' body')) := by
  simpa using MEqRed.fun_ hBound hBody

/-- Nonempty-stack `Me-Fun` lift under a changed `.equ` head. With an operand
on the residual stack, the abstraction step must be rebuilt as `Me-FOp`;
the required body reduction under the operand `.equ` head remains explicit. -/
noncomputable def meq_equ_head_stack_lift_fun_cons_of_fop_body {Γ : Ctx}
    {head α bound bound' body body' : Term} {rest : Stack}
    (hα : Term.Scoped Γ.depth α)
    (hBound : MEqRed ({ bound := head, kind := .equ } :: Γ) []
      (Term.shift 0 bound) (Term.shift 0 bound'))
    (hBody : MEqRed ({ bound := Term.shift 0 α, kind := .equ } ::
        { bound := head, kind := .equ } :: Γ)
      (Stack.shift 0 (Stack.shift 0 rest)) (Term.shift 1 body) (Term.shift 1 body')) :
    MEqRed ({ bound := head, kind := .equ } :: Γ) (Stack.shift 0 (α :: rest))
      (Term.shift 0 (.abs bound body)) (Term.shift 0 (.abs bound' body')) := by
  have hαShift : Term.Scoped (Ctx.depth ({ bound := head, kind := .equ } :: Γ))
      (Term.shift 0 α) := by
    simpa [Ctx.depth] using Term.shift_scoped 0 Γ.depth α (Nat.zero_le _) hα
  simpa [Stack.shift] using MEqRed.fOp hBound hαShift hBody

/-- Recursive `Me-Bet` stack lift under a changed `.equ` head. The body
premise is supplied under the shifted abstraction-bound `.sub` head, and the
argument premise remains empty-stack as required by `Me-Bet`. -/
noncomputable def meq_equ_head_stack_lift_bet {Γ : Ctx} {s : Stack}
    {head t v v' body body' : Term}
    (ht : Term.Scoped Γ.depth t)
    (hBody : MEqRed ({ bound := Term.shift 0 t, kind := .sub } ::
        { bound := head, kind := .equ } :: Γ) (Stack.shift 0 (Stack.shift 0 s))
      (Term.shift 1 body) (Term.shift 1 body'))
    (hArg : MEqRed ({ bound := head, kind := .equ } :: Γ) []
      (Term.shift 0 v) (Term.shift 0 v')) :
    MEqRed ({ bound := head, kind := .equ } :: Γ) (Stack.shift 0 s)
      (Term.shift 0 (.app (.abs t body) v))
      (Term.shift 0 (Term.instantiate 0 v' body')) := by
  have htShift : Term.Scoped (Ctx.depth ({ bound := head, kind := .equ } :: Γ))
      (Term.shift 0 t) := by
    simpa [Ctx.depth] using Term.shift_scoped 0 Γ.depth t (Nat.zero_le _) ht
  have hBet := MEqRed.bet htShift hBody hArg
  simpa [Stack.shift, Term.shift_instantiate_zero 0 v' body'] using hBet

/-- One-step splitter for lifting an empty-stack equivalence step under a
changed `.equ` head and an arbitrary residual stack. Stable leaves are
handled directly; recursive constructor cases and the nonempty-stack `Me-Fun`
case are exposed as explicit handlers. -/
noncomputable def meq_equ_head_stack_lift_from_handlers {Γ : Ctx} {s : Stack}
    {head u v : Term}
    (hpvTail : PrevalidExt Γ s)
    (hHeadScoped : Term.Scoped Γ.depth head)
    (hPro :
      ∀ {i : Nat} {α α' : Term},
        Γ.equBinds i α →
        MEqRed Γ [] α α' →
        MEqRed ({ bound := head, kind := .equ } :: Γ) (Stack.shift 0 s)
          (Term.shift 0 (.bvar i)) (Term.shift 0 α'))
    (hApp :
      ∀ {op op' arg arg' : Term},
        MEqRed Γ (arg :: []) op op' →
        MEqRed Γ [] arg arg' →
        MEqRed ({ bound := head, kind := .equ } :: Γ) (Stack.shift 0 s)
          (Term.shift 0 (.app op arg)) (Term.shift 0 (.app op' arg')))
    (hFunNil :
      ∀ {bound bound' body body' : Term},
        s = [] →
        MEqRed Γ [] bound bound' →
        MEqRed ({ bound := bound, kind := .sub } :: Γ) [] body body' →
        MEqRed ({ bound := head, kind := .equ } :: Γ) []
          (Term.shift 0 (.abs bound body)) (Term.shift 0 (.abs bound' body')))
    (hFunCons :
      ∀ {α : Term} {rest : Stack} {bound bound' body body' : Term},
        s = α :: rest →
        Term.Scoped Γ.depth α →
        MEqRed Γ [] bound bound' →
        MEqRed ({ bound := bound, kind := .sub } :: Γ) [] body body' →
        MEqRed ({ bound := head, kind := .equ } :: Γ) (Stack.shift 0 (α :: rest))
          (Term.shift 0 (.abs bound body)) (Term.shift 0 (.abs bound' body')))
    (hBet :
      ∀ {bound arg arg' body body' : Term},
        Term.Scoped Γ.depth bound →
        MEqRed ({ bound := bound, kind := .sub } :: Γ) (Stack.shift 0 []) body body' →
        MEqRed Γ [] arg arg' →
        MEqRed ({ bound := head, kind := .equ } :: Γ) (Stack.shift 0 s)
          (Term.shift 0 (.app (.abs bound body) arg))
          (Term.shift 0 (Term.instantiate 0 arg' body')))
    (h : MEqRed Γ [] u v) :
    MEqRed ({ bound := head, kind := .equ } :: Γ) (Stack.shift 0 s)
      (Term.shift 0 u) (Term.shift 0 v) := by
  cases h with
  | top _ =>
    exact meq_equ_head_stack_lift_top hpvTail hHeadScoped
  | var _ hi =>
    exact meq_equ_head_stack_lift_var hpvTail hHeadScoped hi
  | pro _ hb hα =>
    exact hPro hb hα
  | app hOp hArg =>
    exact hApp hOp hArg
  | fun_ hBound hBody =>
    cases s with
    | nil =>
      exact hFunNil rfl hBound hBody
    | cons α rest =>
      exact hFunCons rfl (PrevalidExt.head_scoped hpvTail) hBound hBody
  | tAp _ hu =>
    exact meq_equ_head_stack_lift_tAp hpvTail hHeadScoped hu
  | bet ht hBody hArg =>
    exact hBet ht hBody hArg

/-- Canonical `Me-Pro` handler for the changed-head stack-lift splitter. -/
noncomputable def meq_equ_head_stack_lift_pro_handler_of_replacement {Γ : Ctx}
    {s : Stack} {head : Term}
    (hpvTail : PrevalidExt Γ s)
    (hHeadScoped : Term.Scoped Γ.depth head)
    (hReplace :
      ∀ {α α' : Term},
        MEqRed Γ [] α α' →
        MEqRed ({ bound := head, kind := .equ } :: Γ) (Stack.shift 0 s)
          (Term.shift 0 α) (Term.shift 0 α'))
    {i : Nat} {α α' : Term}
    (hb : Γ.equBinds i α)
    (hα : MEqRed Γ [] α α') :
    MEqRed ({ bound := head, kind := .equ } :: Γ) (Stack.shift 0 s)
      (Term.shift 0 (.bvar i)) (Term.shift 0 α') :=
  meq_equ_head_stack_lift_pro hpvTail hHeadScoped hb (hReplace hα)

/-- Canonical `Me-App` handler for the changed-head stack-lift splitter. -/
noncomputable def meq_equ_head_stack_lift_app_handler_of_replacements {Γ : Ctx}
    {s : Stack} {head : Term}
    (hOpReplace :
      ∀ {op op' arg : Term},
        MEqRed Γ (arg :: []) op op' →
        MEqRed ({ bound := head, kind := .equ } :: Γ)
          (Term.shift 0 arg :: Stack.shift 0 s)
          (Term.shift 0 op) (Term.shift 0 op'))
    (hArgReplace :
      ∀ {arg arg' : Term},
        MEqRed Γ [] arg arg' →
        MEqRed ({ bound := head, kind := .equ } :: Γ) []
          (Term.shift 0 arg) (Term.shift 0 arg'))
    {op op' arg arg' : Term}
    (hOp : MEqRed Γ (arg :: []) op op')
    (hArg : MEqRed Γ [] arg arg') :
    MEqRed ({ bound := head, kind := .equ } :: Γ) (Stack.shift 0 s)
      (Term.shift 0 (.app op arg)) (Term.shift 0 (.app op' arg')) :=
  meq_equ_head_stack_lift_app (hOpReplace hOp) (hArgReplace hArg)

/-- Canonical empty-stack `Me-Fun` handler for the changed-head stack-lift
splitter. -/
noncomputable def meq_equ_head_stack_lift_fun_nil_handler_of_replacements {Γ : Ctx}
    {head : Term}
    (hBoundReplace :
      ∀ {bound bound' : Term},
        MEqRed Γ [] bound bound' →
        MEqRed ({ bound := head, kind := .equ } :: Γ) []
          (Term.shift 0 bound) (Term.shift 0 bound'))
    (hBodyReplace :
      ∀ {bound body body' : Term},
        MEqRed ({ bound := bound, kind := .sub } :: Γ) [] body body' →
        MEqRed ({ bound := Term.shift 0 bound, kind := .sub } ::
          { bound := head, kind := .equ } :: Γ) []
          (Term.shift 1 body) (Term.shift 1 body'))
    {bound bound' body body' : Term}
    (hStack : ([] : Stack) = [])
    (hBound : MEqRed Γ [] bound bound')
    (hBody : MEqRed ({ bound := bound, kind := .sub } :: Γ) [] body body') :
    MEqRed ({ bound := head, kind := .equ } :: Γ) []
      (Term.shift 0 (.abs bound body)) (Term.shift 0 (.abs bound' body')) := by
  cases hStack
  exact meq_equ_head_stack_lift_fun_nil (hBoundReplace hBound) (hBodyReplace hBody)

/-- Canonical nonempty-stack `Me-Fun` handler for the changed-head stack-lift
splitter. The body lift under the operand `.equ` head remains explicit. -/
noncomputable def meq_equ_head_stack_lift_fun_cons_handler_of_replacements
    {Γ : Ctx} {head : Term}
    (hBoundReplace :
      ∀ {bound bound' : Term},
        MEqRed Γ [] bound bound' →
        MEqRed ({ bound := head, kind := .equ } :: Γ) []
          (Term.shift 0 bound) (Term.shift 0 bound'))
    (hBodyReplace :
      ∀ {α bound body body' : Term} {rest : Stack},
        Term.Scoped Γ.depth α →
        MEqRed ({ bound := bound, kind := .sub } :: Γ) [] body body' →
        MEqRed ({ bound := Term.shift 0 α, kind := .equ } ::
          { bound := head, kind := .equ } :: Γ)
          (Stack.shift 0 (Stack.shift 0 rest)) (Term.shift 1 body) (Term.shift 1 body'))
    {α : Term} {rest : Stack} {bound bound' body body' : Term}
    (hStack : α :: rest = α :: rest)
    (hα : Term.Scoped Γ.depth α)
    (hBound : MEqRed Γ [] bound bound')
    (hBody : MEqRed ({ bound := bound, kind := .sub } :: Γ) [] body body') :
    MEqRed ({ bound := head, kind := .equ } :: Γ) (Stack.shift 0 (α :: rest))
      (Term.shift 0 (.abs bound body)) (Term.shift 0 (.abs bound' body')) := by
  cases hStack
  exact meq_equ_head_stack_lift_fun_cons_of_fop_body hα
    (hBoundReplace hBound) (hBodyReplace hα hBody)

/-- Canonical `Me-Bet` handler for the changed-head stack-lift splitter. -/
noncomputable def meq_equ_head_stack_lift_bet_handler_of_replacements {Γ : Ctx}
    {s : Stack} {head : Term}
    (hBodyReplace :
      ∀ {bound body body' : Term},
        MEqRed ({ bound := bound, kind := .sub } :: Γ) (Stack.shift 0 []) body body' →
        MEqRed ({ bound := Term.shift 0 bound, kind := .sub } ::
          { bound := head, kind := .equ } :: Γ) (Stack.shift 0 (Stack.shift 0 s))
          (Term.shift 1 body) (Term.shift 1 body'))
    (hArgReplace :
      ∀ {arg arg' : Term},
        MEqRed Γ [] arg arg' →
        MEqRed ({ bound := head, kind := .equ } :: Γ) []
          (Term.shift 0 arg) (Term.shift 0 arg'))
    {bound arg arg' body body' : Term}
    (hBoundScoped : Term.Scoped Γ.depth bound)
    (hBody : MEqRed ({ bound := bound, kind := .sub } :: Γ) (Stack.shift 0 [])
      body body')
    (hArg : MEqRed Γ [] arg arg') :
    MEqRed ({ bound := head, kind := .equ } :: Γ) (Stack.shift 0 s)
      (Term.shift 0 (.app (.abs bound body) arg))
      (Term.shift 0 (Term.instantiate 0 arg' body')) :=
  meq_equ_head_stack_lift_bet hBoundScoped (hBodyReplace hBody) (hArgReplace hArg)

/-- Changed-head stack lift with the canonical constructor handlers wired in.
The remaining premises are the recursive lifts needed by `Me-Pro`, `Me-App`,
`Me-Fun`, and `Me-Bet`. -/
noncomputable def meq_equ_head_stack_lift_from_replacements {Γ : Ctx} {s : Stack}
    {head u v : Term}
    (hpvTail : PrevalidExt Γ s)
    (hHeadScoped : Term.Scoped Γ.depth head)
    (hProReplace :
      ∀ {α α' : Term},
        MEqRed Γ [] α α' →
        MEqRed ({ bound := head, kind := .equ } :: Γ) (Stack.shift 0 s)
          (Term.shift 0 α) (Term.shift 0 α'))
    (hAppOpReplace :
      ∀ {op op' arg : Term},
        MEqRed Γ (arg :: []) op op' →
        MEqRed ({ bound := head, kind := .equ } :: Γ)
          (Term.shift 0 arg :: Stack.shift 0 s)
          (Term.shift 0 op) (Term.shift 0 op'))
    (hNilReplace :
      ∀ {arg arg' : Term},
        MEqRed Γ [] arg arg' →
        MEqRed ({ bound := head, kind := .equ } :: Γ) []
          (Term.shift 0 arg) (Term.shift 0 arg'))
    (hFunNilBodyReplace :
      ∀ {bound body body' : Term},
        MEqRed ({ bound := bound, kind := .sub } :: Γ) [] body body' →
        MEqRed ({ bound := Term.shift 0 bound, kind := .sub } ::
          { bound := head, kind := .equ } :: Γ) []
          (Term.shift 1 body) (Term.shift 1 body'))
    (hFunConsBodyReplace :
      ∀ {α bound body body' : Term} {rest : Stack},
        Term.Scoped Γ.depth α →
        MEqRed ({ bound := bound, kind := .sub } :: Γ) [] body body' →
        MEqRed ({ bound := Term.shift 0 α, kind := .equ } ::
          { bound := head, kind := .equ } :: Γ)
          (Stack.shift 0 (Stack.shift 0 rest)) (Term.shift 1 body) (Term.shift 1 body'))
    (hBetBodyReplace :
      ∀ {bound body body' : Term},
        MEqRed ({ bound := bound, kind := .sub } :: Γ) (Stack.shift 0 []) body body' →
        MEqRed ({ bound := Term.shift 0 bound, kind := .sub } ::
          { bound := head, kind := .equ } :: Γ) (Stack.shift 0 (Stack.shift 0 s))
          (Term.shift 1 body) (Term.shift 1 body'))
    (h : MEqRed Γ [] u v) :
    MEqRed ({ bound := head, kind := .equ } :: Γ) (Stack.shift 0 s)
      (Term.shift 0 u) (Term.shift 0 v) :=
  meq_equ_head_stack_lift_from_handlers hpvTail hHeadScoped
    (meq_equ_head_stack_lift_pro_handler_of_replacement hpvTail hHeadScoped
      hProReplace)
    (meq_equ_head_stack_lift_app_handler_of_replacements hAppOpReplace hNilReplace)
    (by
      intro bound bound' body body' hStack hBound hBody
      subst hStack
      exact meq_equ_head_stack_lift_fun_nil_handler_of_replacements
        hNilReplace hFunNilBodyReplace rfl hBound hBody)
    (by
      intro α rest bound bound' body body' hStack hα hBound hBody
      subst hStack
      exact meq_equ_head_stack_lift_fun_cons_handler_of_replacements
        hNilReplace hFunConsBodyReplace rfl hα hBound hBody)
    (meq_equ_head_stack_lift_bet_handler_of_replacements hBetBodyReplace hNilReplace)
    h

/-- Function-valued changed-head stack lift with canonical handlers wired in
for every residual tail stack. This is the form consumed by commutation
wrappers that need both a top-level shifted argument bridge and recursive
`FOp` tail bridges from the same lifting package. -/
noncomputable def meq_equ_head_stack_lift_function_from_replacements {Γ : Ctx}
    {head u v : Term}
    (hHeadScoped : Term.Scoped Γ.depth head)
    (hProReplace :
      ∀ {s : Stack},
        PrevalidExt Γ s →
        ∀ {α α' : Term},
          MEqRed Γ [] α α' →
          MEqRed ({ bound := head, kind := .equ } :: Γ) (Stack.shift 0 s)
            (Term.shift 0 α) (Term.shift 0 α'))
    (hAppOpReplace :
      ∀ {s : Stack},
        PrevalidExt Γ s →
        ∀ {op op' arg : Term},
          MEqRed Γ (arg :: []) op op' →
          MEqRed ({ bound := head, kind := .equ } :: Γ)
            (Term.shift 0 arg :: Stack.shift 0 s)
            (Term.shift 0 op) (Term.shift 0 op'))
    (hNilReplace :
      ∀ {arg arg' : Term},
        MEqRed Γ [] arg arg' →
        MEqRed ({ bound := head, kind := .equ } :: Γ) []
          (Term.shift 0 arg) (Term.shift 0 arg'))
    (hFunNilBodyReplace :
      ∀ {bound body body' : Term},
        MEqRed ({ bound := bound, kind := .sub } :: Γ) [] body body' →
        MEqRed ({ bound := Term.shift 0 bound, kind := .sub } ::
          { bound := head, kind := .equ } :: Γ) []
          (Term.shift 1 body) (Term.shift 1 body'))
    (hFunConsBodyReplace :
      ∀ {α bound body body' : Term} {rest : Stack},
        Term.Scoped Γ.depth α →
        MEqRed ({ bound := bound, kind := .sub } :: Γ) [] body body' →
        MEqRed ({ bound := Term.shift 0 α, kind := .equ } ::
          { bound := head, kind := .equ } :: Γ)
          (Stack.shift 0 (Stack.shift 0 rest)) (Term.shift 1 body) (Term.shift 1 body'))
    (hBetBodyReplace :
      ∀ {s : Stack},
        PrevalidExt Γ s →
        ∀ {bound body body' : Term},
          MEqRed ({ bound := bound, kind := .sub } :: Γ) (Stack.shift 0 []) body body' →
          MEqRed ({ bound := Term.shift 0 bound, kind := .sub } ::
            { bound := head, kind := .equ } :: Γ) (Stack.shift 0 (Stack.shift 0 s))
            (Term.shift 1 body) (Term.shift 1 body'))
    (h : MEqRed Γ [] u v) :
    ∀ {s : Stack},
      PrevalidExt Γ s →
      MEqRed ({ bound := head, kind := .equ } :: Γ) (Stack.shift 0 s)
        (Term.shift 0 u) (Term.shift 0 v) :=
  fun hpvTail =>
    meq_equ_head_stack_lift_from_replacements hpvTail hHeadScoped
      (hProReplace hpvTail) (hAppOpReplace hpvTail) hNilReplace
      hFunNilBodyReplace hFunConsBodyReplace (hBetBodyReplace hpvTail) h

/-- Lift an empty-stack equivalence-reduction chain under a changed `.equ`
head, given a lift for each single step. -/
theorem meqRedStar_equ_head_stack_lift_from_step_lift {Γ : Ctx} {s : Stack}
    {head u v : Term}
    (hStep :
      ∀ {a b : Term},
        MEqRed Γ [] a b →
        MEqRed ({ bound := head, kind := .equ } :: Γ) (Stack.shift 0 s)
          (Term.shift 0 a) (Term.shift 0 b))
    (h : MEqRedStar Γ [] u v) :
    MEqRedStar ({ bound := head, kind := .equ } :: Γ) (Stack.shift 0 s)
      (Term.shift 0 u) (Term.shift 0 v) := by
  induction h with
  | refl =>
    exact Relation.ReflTransGen.refl
  | @tail mid v hStar hLast ih =>
    exact Relation.ReflTransGen.trans ih (MEqRedStar.single (hStep hLast.some))

/-- Function-valued variant of
`meqRedStar_equ_head_stack_lift_from_step_lift`, for callers that can lift
each single step under every residual tail stack. -/
theorem meqRedStar_equ_head_stack_lift_function_from_step_lift {Γ : Ctx}
    {head u v : Term}
    (hStep :
      ∀ {s : Stack},
        PrevalidExt Γ s →
        ∀ {a b : Term},
          MEqRed Γ [] a b →
          MEqRed ({ bound := head, kind := .equ } :: Γ) (Stack.shift 0 s)
            (Term.shift 0 a) (Term.shift 0 b))
    (h : MEqRedStar Γ [] u v) :
    ∀ {s : Stack},
      PrevalidExt Γ s →
      MEqRedStar ({ bound := head, kind := .equ } :: Γ) (Stack.shift 0 s)
        (Term.shift 0 u) (Term.shift 0 v) :=
  fun hpvTail =>
    meqRedStar_equ_head_stack_lift_from_step_lift (hStep hpvTail) h

/-- Chain-level changed-head stack lift with the canonical constructor
handlers wired in. -/
theorem meqRedStar_equ_head_stack_lift_from_replacements {Γ : Ctx} {s : Stack}
    {head u v : Term}
    (hpvTail : PrevalidExt Γ s)
    (hHeadScoped : Term.Scoped Γ.depth head)
    (hProReplace :
      ∀ {α α' : Term},
        MEqRed Γ [] α α' →
        MEqRed ({ bound := head, kind := .equ } :: Γ) (Stack.shift 0 s)
          (Term.shift 0 α) (Term.shift 0 α'))
    (hAppOpReplace :
      ∀ {op op' arg : Term},
        MEqRed Γ (arg :: []) op op' →
        MEqRed ({ bound := head, kind := .equ } :: Γ)
          (Term.shift 0 arg :: Stack.shift 0 s)
          (Term.shift 0 op) (Term.shift 0 op'))
    (hNilReplace :
      ∀ {arg arg' : Term},
        MEqRed Γ [] arg arg' →
        MEqRed ({ bound := head, kind := .equ } :: Γ) []
          (Term.shift 0 arg) (Term.shift 0 arg'))
    (hFunNilBodyReplace :
      ∀ {bound body body' : Term},
        MEqRed ({ bound := bound, kind := .sub } :: Γ) [] body body' →
        MEqRed ({ bound := Term.shift 0 bound, kind := .sub } ::
          { bound := head, kind := .equ } :: Γ) []
          (Term.shift 1 body) (Term.shift 1 body'))
    (hFunConsBodyReplace :
      ∀ {α bound body body' : Term} {rest : Stack},
        Term.Scoped Γ.depth α →
        MEqRed ({ bound := bound, kind := .sub } :: Γ) [] body body' →
        MEqRed ({ bound := Term.shift 0 α, kind := .equ } ::
          { bound := head, kind := .equ } :: Γ)
          (Stack.shift 0 (Stack.shift 0 rest)) (Term.shift 1 body) (Term.shift 1 body'))
    (hBetBodyReplace :
      ∀ {bound body body' : Term},
        MEqRed ({ bound := bound, kind := .sub } :: Γ) (Stack.shift 0 []) body body' →
        MEqRed ({ bound := Term.shift 0 bound, kind := .sub } ::
          { bound := head, kind := .equ } :: Γ) (Stack.shift 0 (Stack.shift 0 s))
          (Term.shift 1 body) (Term.shift 1 body'))
    (h : MEqRedStar Γ [] u v) :
    MEqRedStar ({ bound := head, kind := .equ } :: Γ) (Stack.shift 0 s)
      (Term.shift 0 u) (Term.shift 0 v) :=
  meqRedStar_equ_head_stack_lift_from_step_lift
    (meq_equ_head_stack_lift_from_replacements hpvTail hHeadScoped hProReplace
      hAppOpReplace hNilReplace hFunNilBodyReplace hFunConsBodyReplace
      hBetBodyReplace)
    h

/-- Function-valued chain-level changed-head stack lift with canonical
handlers wired in for every residual tail stack. -/
theorem meqRedStar_equ_head_stack_lift_function_from_replacements {Γ : Ctx}
    {head u v : Term}
    (hHeadScoped : Term.Scoped Γ.depth head)
    (hProReplace :
      ∀ {s : Stack},
        PrevalidExt Γ s →
        ∀ {α α' : Term},
          MEqRed Γ [] α α' →
          MEqRed ({ bound := head, kind := .equ } :: Γ) (Stack.shift 0 s)
            (Term.shift 0 α) (Term.shift 0 α'))
    (hAppOpReplace :
      ∀ {s : Stack},
        PrevalidExt Γ s →
        ∀ {op op' arg : Term},
          MEqRed Γ (arg :: []) op op' →
          MEqRed ({ bound := head, kind := .equ } :: Γ)
            (Term.shift 0 arg :: Stack.shift 0 s)
            (Term.shift 0 op) (Term.shift 0 op'))
    (hNilReplace :
      ∀ {arg arg' : Term},
        MEqRed Γ [] arg arg' →
        MEqRed ({ bound := head, kind := .equ } :: Γ) []
          (Term.shift 0 arg) (Term.shift 0 arg'))
    (hFunNilBodyReplace :
      ∀ {bound body body' : Term},
        MEqRed ({ bound := bound, kind := .sub } :: Γ) [] body body' →
        MEqRed ({ bound := Term.shift 0 bound, kind := .sub } ::
          { bound := head, kind := .equ } :: Γ) []
          (Term.shift 1 body) (Term.shift 1 body'))
    (hFunConsBodyReplace :
      ∀ {α bound body body' : Term} {rest : Stack},
        Term.Scoped Γ.depth α →
        MEqRed ({ bound := bound, kind := .sub } :: Γ) [] body body' →
        MEqRed ({ bound := Term.shift 0 α, kind := .equ } ::
          { bound := head, kind := .equ } :: Γ)
          (Stack.shift 0 (Stack.shift 0 rest)) (Term.shift 1 body) (Term.shift 1 body'))
    (hBetBodyReplace :
      ∀ {s : Stack},
        PrevalidExt Γ s →
        ∀ {bound body body' : Term},
          MEqRed ({ bound := bound, kind := .sub } :: Γ) (Stack.shift 0 []) body body' →
          MEqRed ({ bound := Term.shift 0 bound, kind := .sub } ::
            { bound := head, kind := .equ } :: Γ) (Stack.shift 0 (Stack.shift 0 s))
            (Term.shift 1 body) (Term.shift 1 body'))
    (h : MEqRedStar Γ [] u v) :
    ∀ {s : Stack},
      PrevalidExt Γ s →
      MEqRedStar ({ bound := head, kind := .equ } :: Γ) (Stack.shift 0 s)
        (Term.shift 0 u) (Term.shift 0 v) :=
  fun hpvTail =>
    meqRedStar_equ_head_stack_lift_from_replacements hpvTail hHeadScoped
      (hProReplace hpvTail) (hAppOpReplace hpvTail) hNilReplace
      hFunNilBodyReplace hFunConsBodyReplace (hBetBodyReplace hpvTail) h

/-- Lift a body equivalence-reduction chain under an `.equ` head into an
abstraction subtype-reduction chain through `FOp`, allowing the abstraction
bound to take the supplied equivalence step first. -/
theorem msubRedStar_abs_fOp_equ_body_star {Γ : Ctx} {s : Stack}
    {α bound bound' body body' : Term}
    (hpvTail : PrevalidExt Γ s)
    (hBound : MEqRed Γ [] bound bound')
    (hα : Term.Scoped Γ.depth α)
    (hBodyScoped : Term.Scoped (Ctx.depth ({ bound := α, kind := .equ } :: Γ)) body)
    (hBody : MEqRedStar ({ bound := α, kind := .equ } :: Γ)
      (Stack.shift 0 s) body body') :
    MSubRedStar Γ (α :: s) (.abs bound body) (.abs bound' body') := by
  have hpvBodyCtx : Prevalid ({ bound := α, kind := .equ } :: Γ) :=
    Prevalid.equ (PrevalidExt.ctx hpvTail) hα
  have hpvBody : PrevalidExt ({ bound := α, kind := .equ } :: Γ)
      (Stack.shift 0 s) :=
    PrevalidExt.weaken_head hpvTail hpvBodyCtx
  have hBodySub : MSubRedStar ({ bound := α, kind := .equ } :: Γ)
      (Stack.shift 0 s) body body' :=
    MSubRedStar.of_MEqRedStar hpvBody hBody
  have hBodyRefl : MEqRed ({ bound := α, kind := .equ } :: Γ)
      (Stack.shift 0 s) body body :=
    MEqRed.refl hpvBody hBodyScoped
  exact MSubRedStar.trans
    (MSubRedStar.single (MSubRed.equ (PrevalidExt.cons hpvTail hα)
      (MEqRed.fOp hBound hα hBodyRefl)))
    (msubRedStar_abs_fOp_body_fixed_bound hBound.scoped_right hα hBodySub)

/-- Star-level variant of
`commute_appAbs_structApp_eqStep_of_body_fOp_replacements`. The replacement
premises may return body chains under the changed `.equ` head; the outer
`FOp` lifting is handled here. -/
theorem commute_appAbs_structApp_eqStep_of_body_fOp_star_replacements {Γ : Ctx}
    {s : Stack} {bound body arg bound₁ body₁ bound₂ body₂ arg' : Term}
    (hpvTail : PrevalidExt Γ s)
    (hcommArg : StrongCommutes Γ (arg :: s))
    (hSubOp : MSubRed Γ (arg :: s) (.abs bound body) (.abs bound₁ body₁))
    (hEqOp : MEqRed Γ (arg :: s) (.abs bound body) (.abs bound₂ body₂))
    (hEqArg : MEqRed Γ [] arg arg')
    (hEquBodyReplace :
      ∀ {joinBound joinBody : Term},
        MEqRed Γ [] bound₂ joinBound →
        MEqRed ({ bound := arg, kind := .equ } :: Γ)
          (Stack.shift 0 s) body₂ joinBody →
        MEqRedStar ({ bound := arg', kind := .equ } :: Γ)
          (Stack.shift 0 s) body₂ joinBody)
    (hSubBodyReplace :
      ∀ {joinBody : Term},
        MSubRed ({ bound := arg, kind := .equ } :: Γ)
          (Stack.shift 0 s) body₂ joinBody →
        MSubRedStar ({ bound := arg', kind := .equ } :: Γ)
          (Stack.shift 0 s) body₂ joinBody) :
    ∃ t₃,
      MEqRedStar Γ s (.app (.abs bound₁ body₁) arg) t₃ ∧
        MSubRedStar Γ s (.app (.abs bound₂ body₂) arg') t₃ := by
  have hArg'Scoped : Term.Scoped Γ.depth arg' := hEqArg.scoped_right
  have hBound₂Scoped : Term.Scoped Γ.depth bound₂ :=
    (Term.Scoped.abs_inv hEqOp.scoped_right).1
  have hBody₂ScopedNew :
      Term.Scoped (Ctx.depth ({ bound := arg', kind := .equ } :: Γ)) body₂ := by
    simpa [Ctx.depth] using (Term.Scoped.abs_inv hEqOp.scoped_right).2
  refine commute_appAbs_structApp_eqStep_of_fOp_handlers hpvTail hcommArg
    hSubOp hEqOp hEqArg ?_ ?_
  · intro joinBound joinBody oldArg rest hStack hBound hBody
    cases hStack
    exact msubRedStar_abs_fOp_equ_body_star hpvTail hBound hArg'Scoped
      hBody₂ScopedNew (hEquBodyReplace hBound hBody)
  · intro joinBody oldArg rest hStack hBody
    cases hStack
    exact msubRedStar_abs_fOp_body_fixed_bound hBound₂Scoped hArg'Scoped
      (hSubBodyReplace hBody)

/-- Side-condition-free wrapper for
`commute_appAbs_structApp_eqStep_of_body_fOp_star_replacements`: the tail
stack prevalidity is recovered from the operator subtype step. -/
theorem commute_appAbs_structApp_eqStep_of_body_fOp_star_replacements_from_left
    {Γ : Ctx} {s : Stack}
    {bound body arg bound₁ body₁ bound₂ body₂ arg' : Term}
    (hcommArg : StrongCommutes Γ (arg :: s))
    (hSubOp : MSubRed Γ (arg :: s) (.abs bound body) (.abs bound₁ body₁))
    (hEqOp : MEqRed Γ (arg :: s) (.abs bound body) (.abs bound₂ body₂))
    (hEqArg : MEqRed Γ [] arg arg')
    (hEquBodyReplace :
      ∀ {joinBound joinBody : Term},
        MEqRed Γ [] bound₂ joinBound →
        MEqRed ({ bound := arg, kind := .equ } :: Γ)
          (Stack.shift 0 s) body₂ joinBody →
        MEqRedStar ({ bound := arg', kind := .equ } :: Γ)
          (Stack.shift 0 s) body₂ joinBody)
    (hSubBodyReplace :
      ∀ {joinBody : Term},
        MSubRed ({ bound := arg, kind := .equ } :: Γ)
          (Stack.shift 0 s) body₂ joinBody →
        MSubRedStar ({ bound := arg', kind := .equ } :: Γ)
          (Stack.shift 0 s) body₂ joinBody) :
    ∃ t₃,
      MEqRedStar Γ s (.app (.abs bound₁ body₁) arg) t₃ ∧
        MSubRedStar Γ s (.app (.abs bound₂ body₂) arg') t₃ :=
  commute_appAbs_structApp_eqStep_of_body_fOp_star_replacements
    (PrevalidExt.tail hSubOp.prevalidExt) hcommArg hSubOp hEqOp hEqArg
    hEquBodyReplace hSubBodyReplace

/-- Diagrammatic variant of
`commute_appAbs_structApp_eqStep_of_body_fOp_star_replacements`. This
matches the replacement splitters above, whose residual replacement output is
`MSubStar` rather than a raw `MSubRedStar`. -/
theorem commute_appAbs_structApp_eqStep_of_body_fOp_msub_replacements {Γ : Ctx}
    {s : Stack} {bound body arg bound₁ body₁ bound₂ body₂ arg' : Term}
    (hpvTail : PrevalidExt Γ s)
    (hcommArg : StrongCommutes Γ (arg :: s))
    (hSubOp : MSubRed Γ (arg :: s) (.abs bound body) (.abs bound₁ body₁))
    (hEqOp : MEqRed Γ (arg :: s) (.abs bound body) (.abs bound₂ body₂))
    (hEqArg : MEqRed Γ [] arg arg')
    (hEquBodyReplace :
      ∀ {joinBound joinBody : Term},
        MEqRed Γ [] bound₂ joinBound →
        MEqRed ({ bound := arg, kind := .equ } :: Γ)
          (Stack.shift 0 s) body₂ joinBody →
        MSubStar ({ bound := arg', kind := .equ } :: Γ)
          (Stack.shift 0 s) body₂ joinBody)
    (hSubBodyReplace :
      ∀ {joinBody : Term},
        MSubRed ({ bound := arg, kind := .equ } :: Γ)
          (Stack.shift 0 s) body₂ joinBody →
        MSubStar ({ bound := arg', kind := .equ } :: Γ)
          (Stack.shift 0 s) body₂ joinBody) :
    ∃ t₃,
      MEqRedStar Γ s (.app (.abs bound₁ body₁) arg) t₃ ∧
        MSubStar Γ s (.app (.abs bound₂ body₂) arg') t₃ := by
  cases commute_appAbs_structApp_eqStep_or_fOp_residual_from_left hcommArg hSubOp
      hEqOp hEqArg with
  | inl hJoin =>
    obtain ⟨t₃, hEqJoin, hSubJoin⟩ := hJoin
    exact ⟨t₃, hEqJoin, MSubStar.of_MSubRedStar hSubJoin⟩
  | inr hResidual =>
    obtain ⟨joinBound, joinBody, hEqJoin, hResidual⟩ := hResidual
    have hArg'Scoped : Term.Scoped Γ.depth arg' := hEqArg.scoped_right
    have hBound₂Scoped : Term.Scoped Γ.depth bound₂ :=
      (Term.Scoped.abs_inv hEqOp.scoped_right).1
    have hBody₂ScopedNew :
        Term.Scoped (Ctx.depth ({ bound := arg', kind := .equ } :: Γ)) body₂ := by
      simpa [Ctx.depth] using (Term.Scoped.abs_inv hEqOp.scoped_right).2
    refine ⟨.app (.abs joinBound joinBody) arg',
      MEqRedStar.single (MEqRed.app hEqJoin.some hEqArg), ?_⟩
    cases hResidual with
    | inl hEqu =>
      obtain ⟨oldArg, rest, hStack, hBound, hBody⟩ := hEqu
      cases hStack
      exact msubStar_app_fixed_arg hpvTail hArg'Scoped
        (msubStar_abs_fOp_equ_bound_body hpvTail hBound.some hArg'Scoped
          hBody₂ScopedNew (hEquBodyReplace hBound.some hBody.some))
    | inr hSub =>
      obtain ⟨oldArg, rest, hStack, hBoundEq, hBody⟩ := hSub
      cases hStack
      cases hBoundEq
      exact msubStar_app_fixed_arg hpvTail hArg'Scoped
        (msubStar_abs_fOp_body_fixed_bound hpvTail hBound₂Scoped hArg'Scoped
          (hSubBodyReplace hBody.some))

/-- Side-condition-free wrapper for
`commute_appAbs_structApp_eqStep_of_body_fOp_msub_replacements`: the tail
stack prevalidity is recovered from the operator subtype step. -/
theorem commute_appAbs_structApp_eqStep_of_body_fOp_msub_replacements_from_left
    {Γ : Ctx} {s : Stack}
    {bound body arg bound₁ body₁ bound₂ body₂ arg' : Term}
    (hcommArg : StrongCommutes Γ (arg :: s))
    (hSubOp : MSubRed Γ (arg :: s) (.abs bound body) (.abs bound₁ body₁))
    (hEqOp : MEqRed Γ (arg :: s) (.abs bound body) (.abs bound₂ body₂))
    (hEqArg : MEqRed Γ [] arg arg')
    (hEquBodyReplace :
      ∀ {joinBound joinBody : Term},
        MEqRed Γ [] bound₂ joinBound →
        MEqRed ({ bound := arg, kind := .equ } :: Γ)
          (Stack.shift 0 s) body₂ joinBody →
        MSubStar ({ bound := arg', kind := .equ } :: Γ)
          (Stack.shift 0 s) body₂ joinBody)
    (hSubBodyReplace :
      ∀ {joinBody : Term},
        MSubRed ({ bound := arg, kind := .equ } :: Γ)
          (Stack.shift 0 s) body₂ joinBody →
        MSubStar ({ bound := arg', kind := .equ } :: Γ)
          (Stack.shift 0 s) body₂ joinBody) :
    ∃ t₃,
      MEqRedStar Γ s (.app (.abs bound₁ body₁) arg) t₃ ∧
        MSubStar Γ s (.app (.abs bound₂ body₂) arg') t₃ :=
  commute_appAbs_structApp_eqStep_of_body_fOp_msub_replacements
    (PrevalidExt.tail hSubOp.prevalidExt) hcommArg hSubOp hEqOp hEqArg
    hEquBodyReplace hSubBodyReplace

/-- Changed-argument structural application commutation specialized to the
shifted replacement packages for the `FOp` body residuals. The supplied
old-to-new shifted equivalence is the bridge produced by lifting the
argument step under the changed `.equ` head. -/
theorem commute_appAbs_structApp_eqStep_of_shifted_fOp_replacements {Γ : Ctx}
    {s : Stack} {bound body arg bound₁ body₁ bound₂ body₂ arg' : Term}
    (hpvTail : PrevalidExt Γ s)
    (hcommArg : StrongCommutes Γ (arg :: s))
    (hSubOp : MSubRed Γ (arg :: s) (.abs bound body) (.abs bound₁ body₁))
    (hEqOp : MEqRed Γ (arg :: s) (.abs bound body) (.abs bound₂ body₂))
    (hEqArg : MEqRed Γ [] arg arg')
    (hOldNewStack : MEqRed ({ bound := arg', kind := .equ } :: Γ)
      (Stack.shift 0 s) (Term.shift 0 arg) (Term.shift 0 arg'))
    (hEqSelfReplace :
      ∀ {u v : Term},
        MEqRed ({ bound := arg, kind := .equ } :: Γ) (Stack.shift 0 s) u v →
        MSubStar ({ bound := arg', kind := .equ } :: Γ) (Stack.shift 0 s) u v)
    (hEqAppOpReplace :
      ∀ {op op' operand : Term},
        MEqRed ({ bound := arg, kind := .equ } :: Γ)
          (operand :: Stack.shift 0 s) op op' →
        MEqRed ({ bound := arg', kind := .equ } :: Γ)
          (operand :: Stack.shift 0 s) op op')
    (hNilReplace :
      ∀ {u v : Term},
        MEqRed ({ bound := arg, kind := .equ } :: Γ) [] u v →
        MEqRed ({ bound := arg', kind := .equ } :: Γ) [] u v)
    (hEqFunBodyReplace :
      ∀ {funBound body body' : Term},
        MEqRed ({ bound := funBound, kind := .sub } ::
          { bound := arg, kind := .equ } :: Γ) [] body body' →
        MEqRed ({ bound := funBound, kind := .sub } ::
          { bound := arg', kind := .equ } :: Γ) [] body body')
    (hEqBetBodyReplace :
      ∀ {funBound body body' : Term},
        MEqRed ({ bound := funBound, kind := .sub } ::
          { bound := arg, kind := .equ } :: Γ) (Stack.shift 0 (Stack.shift 0 s))
          body body' →
        MEqRed ({ bound := funBound, kind := .sub } ::
          { bound := arg', kind := .equ } :: Γ) (Stack.shift 0 (Stack.shift 0 s))
          body body')
    (hEqFOpBodyReplace :
      ∀ {operand body body' : Term} {rest : Stack},
        Term.Scoped (Ctx.depth ({ bound := arg, kind := .equ } :: Γ)) operand →
        Stack.shift 0 s = operand :: rest →
        MEqRed ({ bound := operand, kind := .equ } ::
          { bound := arg, kind := .equ } :: Γ) (Stack.shift 0 rest) body body' →
        MSubStar ({ bound := operand, kind := .equ } ::
          { bound := arg', kind := .equ } :: Γ) (Stack.shift 0 rest) body body')
    (hAppOpReplace :
      ∀ {op op' operand : Term},
        MSubRed ({ bound := arg, kind := .equ } :: Γ)
          (operand :: Stack.shift 0 s) op op' →
        Term.Scoped (Ctx.depth ({ bound := arg, kind := .equ } :: Γ)) operand →
        MSubStar ({ bound := arg', kind := .equ } :: Γ)
          (operand :: Stack.shift 0 s) op op')
    (hFunBodyReplace :
      ∀ {funBound body body' : Term},
        MSubRed ({ bound := funBound, kind := .sub } ::
          { bound := arg, kind := .equ } :: Γ) [] body body' →
        MSubRed ({ bound := funBound, kind := .sub } ::
          { bound := arg', kind := .equ } :: Γ) [] body body')
    (hFOpBodyReplace :
      ∀ {operand body body' : Term} {rest : Stack},
        Term.Scoped (Ctx.depth ({ bound := arg, kind := .equ } :: Γ)) operand →
        Stack.shift 0 s = operand :: rest →
        MSubRed ({ bound := operand, kind := .equ } ::
          { bound := arg, kind := .equ } :: Γ) (Stack.shift 0 rest) body body' →
        MSubStar ({ bound := operand, kind := .equ } ::
          { bound := arg', kind := .equ } :: Γ) (Stack.shift 0 rest) body body') :
    ∃ t₃,
      MEqRedStar Γ s (.app (.abs bound₁ body₁) arg) t₃ ∧
        MSubStar Γ s (.app (.abs bound₂ body₂) arg') t₃ := by
  have hArgScoped : Term.Scoped Γ.depth arg := hEqArg.scoped_left
  have hArg'Scoped : Term.Scoped Γ.depth arg' := hEqArg.scoped_right
  refine commute_appAbs_structApp_eqStep_of_body_fOp_msub_replacements_from_left
    hcommArg hSubOp hEqOp hEqArg ?_ ?_
  · intro joinBound joinBody _hBound hBody
    exact meqRed_equ_head_shifted_replace_from_replacements hpvTail hArgScoped
      hArg'Scoped hOldNewStack hEqSelfReplace hEqAppOpReplace hNilReplace
      hEqFunBodyReplace hEqBetBodyReplace hEqFOpBodyReplace hBody
  · intro joinBody hBody
    exact msubRed_equ_head_shifted_replace_from_replacements hpvTail hArgScoped
      hArg'Scoped hOldNewStack hEqSelfReplace hEqAppOpReplace hNilReplace
      hEqFunBodyReplace hEqBetBodyReplace hEqFOpBodyReplace hAppOpReplace
      hFunBodyReplace hFOpBodyReplace hBody

/-- Side-condition-free wrapper for
`commute_appAbs_structApp_eqStep_of_shifted_fOp_replacements`: the tail
stack prevalidity is recovered from the operator subtype step. -/
theorem commute_appAbs_structApp_eqStep_of_shifted_fOp_replacements_from_left
    {Γ : Ctx} {s : Stack}
    {bound body arg bound₁ body₁ bound₂ body₂ arg' : Term}
    (hcommArg : StrongCommutes Γ (arg :: s))
    (hSubOp : MSubRed Γ (arg :: s) (.abs bound body) (.abs bound₁ body₁))
    (hEqOp : MEqRed Γ (arg :: s) (.abs bound body) (.abs bound₂ body₂))
    (hEqArg : MEqRed Γ [] arg arg')
    (hOldNewStack : MEqRed ({ bound := arg', kind := .equ } :: Γ)
      (Stack.shift 0 s) (Term.shift 0 arg) (Term.shift 0 arg'))
    (hEqSelfReplace :
      ∀ {u v : Term},
        MEqRed ({ bound := arg, kind := .equ } :: Γ) (Stack.shift 0 s) u v →
        MSubStar ({ bound := arg', kind := .equ } :: Γ) (Stack.shift 0 s) u v)
    (hEqAppOpReplace :
      ∀ {op op' operand : Term},
        MEqRed ({ bound := arg, kind := .equ } :: Γ)
          (operand :: Stack.shift 0 s) op op' →
        MEqRed ({ bound := arg', kind := .equ } :: Γ)
          (operand :: Stack.shift 0 s) op op')
    (hNilReplace :
      ∀ {u v : Term},
        MEqRed ({ bound := arg, kind := .equ } :: Γ) [] u v →
        MEqRed ({ bound := arg', kind := .equ } :: Γ) [] u v)
    (hEqFunBodyReplace :
      ∀ {funBound body body' : Term},
        MEqRed ({ bound := funBound, kind := .sub } ::
          { bound := arg, kind := .equ } :: Γ) [] body body' →
        MEqRed ({ bound := funBound, kind := .sub } ::
          { bound := arg', kind := .equ } :: Γ) [] body body')
    (hEqBetBodyReplace :
      ∀ {funBound body body' : Term},
        MEqRed ({ bound := funBound, kind := .sub } ::
          { bound := arg, kind := .equ } :: Γ) (Stack.shift 0 (Stack.shift 0 s))
          body body' →
        MEqRed ({ bound := funBound, kind := .sub } ::
          { bound := arg', kind := .equ } :: Γ) (Stack.shift 0 (Stack.shift 0 s))
          body body')
    (hEqFOpBodyReplace :
      ∀ {operand body body' : Term} {rest : Stack},
        Term.Scoped (Ctx.depth ({ bound := arg, kind := .equ } :: Γ)) operand →
        Stack.shift 0 s = operand :: rest →
        MEqRed ({ bound := operand, kind := .equ } ::
          { bound := arg, kind := .equ } :: Γ) (Stack.shift 0 rest) body body' →
        MSubStar ({ bound := operand, kind := .equ } ::
          { bound := arg', kind := .equ } :: Γ) (Stack.shift 0 rest) body body')
    (hAppOpReplace :
      ∀ {op op' operand : Term},
        MSubRed ({ bound := arg, kind := .equ } :: Γ)
          (operand :: Stack.shift 0 s) op op' →
        Term.Scoped (Ctx.depth ({ bound := arg, kind := .equ } :: Γ)) operand →
        MSubStar ({ bound := arg', kind := .equ } :: Γ)
          (operand :: Stack.shift 0 s) op op')
    (hFunBodyReplace :
      ∀ {funBound body body' : Term},
        MSubRed ({ bound := funBound, kind := .sub } ::
          { bound := arg, kind := .equ } :: Γ) [] body body' →
        MSubRed ({ bound := funBound, kind := .sub } ::
          { bound := arg', kind := .equ } :: Γ) [] body body')
    (hFOpBodyReplace :
      ∀ {operand body body' : Term} {rest : Stack},
        Term.Scoped (Ctx.depth ({ bound := arg, kind := .equ } :: Γ)) operand →
        Stack.shift 0 s = operand :: rest →
        MSubRed ({ bound := operand, kind := .equ } ::
          { bound := arg, kind := .equ } :: Γ) (Stack.shift 0 rest) body body' →
        MSubStar ({ bound := operand, kind := .equ } ::
          { bound := arg', kind := .equ } :: Γ) (Stack.shift 0 rest) body body') :
    ∃ t₃,
      MEqRedStar Γ s (.app (.abs bound₁ body₁) arg) t₃ ∧
        MSubStar Γ s (.app (.abs bound₂ body₂) arg') t₃ :=
  commute_appAbs_structApp_eqStep_of_shifted_fOp_replacements
    (PrevalidExt.tail hSubOp.prevalidExt) hcommArg hSubOp hEqOp hEqArg
    hOldNewStack hEqSelfReplace hEqAppOpReplace hNilReplace
    hEqFunBodyReplace hEqBetBodyReplace hEqFOpBodyReplace hAppOpReplace
    hFunBodyReplace hFOpBodyReplace

/-- Changed-argument structural application commutation specialized to the
shifted replacement packages, with the recursive `FOp` body handlers built
from tail-stack old-to-new lifts. -/
theorem commute_appAbs_structApp_eqStep_of_shifted_fOp_tail_lifts {Γ : Ctx}
    {s : Stack} {bound body arg bound₁ body₁ bound₂ body₂ arg' : Term}
    (hpvTail : PrevalidExt Γ s)
    (hcommArg : StrongCommutes Γ (arg :: s))
    (hSubOp : MSubRed Γ (arg :: s) (.abs bound body) (.abs bound₁ body₁))
    (hEqOp : MEqRed Γ (arg :: s) (.abs bound body) (.abs bound₂ body₂))
    (hEqArg : MEqRed Γ [] arg arg')
    (hOldNewStack : MEqRed ({ bound := arg', kind := .equ } :: Γ)
      (Stack.shift 0 s) (Term.shift 0 arg) (Term.shift 0 arg'))
    (hEqSelfReplace :
      ∀ {u v : Term},
        MEqRed ({ bound := arg, kind := .equ } :: Γ) (Stack.shift 0 s) u v →
        MSubStar ({ bound := arg', kind := .equ } :: Γ) (Stack.shift 0 s) u v)
    (hEqAppOpReplace :
      ∀ {op op' operand : Term},
        MEqRed ({ bound := arg, kind := .equ } :: Γ)
          (operand :: Stack.shift 0 s) op op' →
        MEqRed ({ bound := arg', kind := .equ } :: Γ)
          (operand :: Stack.shift 0 s) op op')
    (hNilReplace :
      ∀ {u v : Term},
        MEqRed ({ bound := arg, kind := .equ } :: Γ) [] u v →
        MEqRed ({ bound := arg', kind := .equ } :: Γ) [] u v)
    (hEqFunBodyReplace :
      ∀ {funBound body body' : Term},
        MEqRed ({ bound := funBound, kind := .sub } ::
          { bound := arg, kind := .equ } :: Γ) [] body body' →
        MEqRed ({ bound := funBound, kind := .sub } ::
          { bound := arg', kind := .equ } :: Γ) [] body body')
    (hEqBetBodyReplace :
      ∀ {funBound body body' : Term},
        MEqRed ({ bound := funBound, kind := .sub } ::
          { bound := arg, kind := .equ } :: Γ) (Stack.shift 0 (Stack.shift 0 s))
          body body' →
        MEqRed ({ bound := funBound, kind := .sub } ::
          { bound := arg', kind := .equ } :: Γ) (Stack.shift 0 (Stack.shift 0 s))
          body body')
    (hOldNewTail :
      ∀ {operand : Term} {rest : Stack},
        Term.Scoped (Ctx.depth ({ bound := arg, kind := .equ } :: Γ)) operand →
        Stack.shift 0 s = operand :: rest →
        MEqRed ({ bound := arg', kind := .equ } :: Γ) rest
          (Term.shift 0 arg) (Term.shift 0 arg'))
    (hEqFOpSelfReplace :
      ∀ {operand : Term} {rest : Stack} {u v : Term},
        Term.Scoped (Ctx.depth ({ bound := arg, kind := .equ } :: Γ)) operand →
        Stack.shift 0 s = operand :: rest →
        MEqRed ({ bound := operand, kind := .equ } ::
          { bound := arg, kind := .equ } :: Γ) (Stack.shift 0 rest) u v →
        MSubStar ({ bound := operand, kind := .equ } ::
          { bound := arg', kind := .equ } :: Γ) (Stack.shift 0 rest) u v)
    (hEqFOpAppOpReplace :
      ∀ {operand : Term} {rest : Stack} {op op' inner : Term},
        Term.Scoped (Ctx.depth ({ bound := arg, kind := .equ } :: Γ)) operand →
        Stack.shift 0 s = operand :: rest →
        MEqRed ({ bound := operand, kind := .equ } ::
          { bound := arg, kind := .equ } :: Γ) (inner :: Stack.shift 0 rest) op op' →
        MEqRed ({ bound := operand, kind := .equ } ::
          { bound := arg', kind := .equ } :: Γ) (inner :: Stack.shift 0 rest) op op')
    (hEqFOpNilReplace :
      ∀ {operand : Term} {rest : Stack} {u v : Term},
        Term.Scoped (Ctx.depth ({ bound := arg, kind := .equ } :: Γ)) operand →
        Stack.shift 0 s = operand :: rest →
        MEqRed ({ bound := operand, kind := .equ } ::
          { bound := arg, kind := .equ } :: Γ) [] u v →
        MEqRed ({ bound := operand, kind := .equ } ::
          { bound := arg', kind := .equ } :: Γ) [] u v)
    (hEqFOpFunBodyReplace :
      ∀ {operand : Term} {rest : Stack} {funBound body body' : Term},
        Term.Scoped (Ctx.depth ({ bound := arg, kind := .equ } :: Γ)) operand →
        Stack.shift 0 s = operand :: rest →
        MEqRed ({ bound := funBound, kind := .sub } ::
          { bound := operand, kind := .equ } ::
          { bound := arg, kind := .equ } :: Γ) [] body body' →
        MEqRed ({ bound := funBound, kind := .sub } ::
          { bound := operand, kind := .equ } ::
          { bound := arg', kind := .equ } :: Γ) [] body body')
    (hEqFOpBetBodyReplace :
      ∀ {operand : Term} {rest : Stack} {funBound body body' : Term},
        Term.Scoped (Ctx.depth ({ bound := arg, kind := .equ } :: Γ)) operand →
        Stack.shift 0 s = operand :: rest →
        MEqRed ({ bound := funBound, kind := .sub } ::
          { bound := operand, kind := .equ } ::
          { bound := arg, kind := .equ } :: Γ) (Stack.shift 0 (Stack.shift 0 rest))
          body body' →
        MEqRed ({ bound := funBound, kind := .sub } ::
          { bound := operand, kind := .equ } ::
          { bound := arg', kind := .equ } :: Γ) (Stack.shift 0 (Stack.shift 0 rest))
          body body')
    (hEqFOpBodyReplace :
      ∀ {operand : Term} {rest : Stack} {inner body body' : Term}
          {innerRest : Stack},
        Term.Scoped (Ctx.depth ({ bound := arg, kind := .equ } :: Γ)) operand →
        Stack.shift 0 s = operand :: rest →
        Term.Scoped (Ctx.depth ({ bound := operand, kind := .equ } ::
          { bound := arg, kind := .equ } :: Γ)) inner →
        Stack.shift 0 rest = inner :: innerRest →
        MEqRed ({ bound := inner, kind := .equ } ::
          { bound := operand, kind := .equ } ::
          { bound := arg, kind := .equ } :: Γ) (Stack.shift 0 innerRest) body body' →
        MSubStar ({ bound := inner, kind := .equ } ::
          { bound := operand, kind := .equ } ::
          { bound := arg', kind := .equ } :: Γ) (Stack.shift 0 innerRest) body body')
    (hAppOpReplace :
      ∀ {op op' operand : Term},
        MSubRed ({ bound := arg, kind := .equ } :: Γ)
          (operand :: Stack.shift 0 s) op op' →
        Term.Scoped (Ctx.depth ({ bound := arg, kind := .equ } :: Γ)) operand →
        MSubStar ({ bound := arg', kind := .equ } :: Γ)
          (operand :: Stack.shift 0 s) op op')
    (hFunBodyReplace :
      ∀ {funBound body body' : Term},
        MSubRed ({ bound := funBound, kind := .sub } ::
          { bound := arg, kind := .equ } :: Γ) [] body body' →
        MSubRed ({ bound := funBound, kind := .sub } ::
          { bound := arg', kind := .equ } :: Γ) [] body body')
    (hFOpAppOpReplace :
      ∀ {operand : Term} {rest : Stack} {op op' inner : Term},
        Term.Scoped (Ctx.depth ({ bound := arg, kind := .equ } :: Γ)) operand →
        Stack.shift 0 s = operand :: rest →
        MSubRed ({ bound := operand, kind := .equ } ::
          { bound := arg, kind := .equ } :: Γ) (inner :: Stack.shift 0 rest) op op' →
        Term.Scoped (Ctx.depth ({ bound := operand, kind := .equ } ::
          { bound := arg, kind := .equ } :: Γ)) inner →
        MSubStar ({ bound := operand, kind := .equ } ::
          { bound := arg', kind := .equ } :: Γ) (inner :: Stack.shift 0 rest) op op')
    (hFOpFunBodyReplace :
      ∀ {operand : Term} {rest : Stack} {funBound body body' : Term},
        Term.Scoped (Ctx.depth ({ bound := arg, kind := .equ } :: Γ)) operand →
        Stack.shift 0 s = operand :: rest →
        MSubRed ({ bound := funBound, kind := .sub } ::
          { bound := operand, kind := .equ } ::
          { bound := arg, kind := .equ } :: Γ) [] body body' →
        MSubRed ({ bound := funBound, kind := .sub } ::
          { bound := operand, kind := .equ } ::
          { bound := arg', kind := .equ } :: Γ) [] body body')
    (hFOpBodyReplace :
      ∀ {operand : Term} {rest : Stack} {inner body body' : Term}
          {innerRest : Stack},
        Term.Scoped (Ctx.depth ({ bound := arg, kind := .equ } :: Γ)) operand →
        Stack.shift 0 s = operand :: rest →
        Term.Scoped (Ctx.depth ({ bound := operand, kind := .equ } ::
          { bound := arg, kind := .equ } :: Γ)) inner →
        Stack.shift 0 rest = inner :: innerRest →
        MSubRed ({ bound := inner, kind := .equ } ::
          { bound := operand, kind := .equ } ::
          { bound := arg, kind := .equ } :: Γ) (Stack.shift 0 innerRest) body body' →
        MSubStar ({ bound := inner, kind := .equ } ::
          { bound := operand, kind := .equ } ::
          { bound := arg', kind := .equ } :: Γ) (Stack.shift 0 innerRest) body body') :
    ∃ t₃,
      MEqRedStar Γ s (.app (.abs bound₁ body₁) arg) t₃ ∧
        MSubStar Γ s (.app (.abs bound₂ body₂) arg') t₃ := by
  have hArgScoped : Term.Scoped Γ.depth arg := hEqArg.scoped_left
  have hArg'Scoped : Term.Scoped Γ.depth arg' := hEqArg.scoped_right
  have hpvOldCtx : Prevalid ({ bound := arg, kind := .equ } :: Γ) :=
    Prevalid.equ (PrevalidExt.ctx hpvTail) hArgScoped
  have hpvNewCtx : Prevalid ({ bound := arg', kind := .equ } :: Γ) :=
    Prevalid.equ (PrevalidExt.ctx hpvTail) hArg'Scoped
  have hpvOld : PrevalidExt ({ bound := arg, kind := .equ } :: Γ)
      (Stack.shift 0 s) :=
    PrevalidExt.weaken_head hpvTail hpvOldCtx
  have hpvNew : PrevalidExt ({ bound := arg', kind := .equ } :: Γ)
      (Stack.shift 0 s) :=
    PrevalidExt.weaken_head hpvTail hpvNewCtx
  exact commute_appAbs_structApp_eqStep_of_shifted_fOp_replacements_from_left
    hcommArg hSubOp hEqOp hEqArg hOldNewStack hEqSelfReplace
    hEqAppOpReplace hNilReplace hEqFunBodyReplace hEqBetBodyReplace
    (meq_equ_head_shifted_fop_body_handler_from_tail_lifts hpvOld hpvNew
      hArg'Scoped hOldNewTail hEqFOpSelfReplace hEqFOpAppOpReplace
      hEqFOpNilReplace hEqFOpFunBodyReplace hEqFOpBetBodyReplace
      hEqFOpBodyReplace)
    hAppOpReplace hFunBodyReplace
    (msub_equ_head_shifted_fop_body_handler_from_tail_lifts hpvOld hpvNew
      hArg'Scoped hOldNewTail hEqFOpSelfReplace hEqFOpAppOpReplace
      hEqFOpNilReplace hEqFOpFunBodyReplace hEqFOpBetBodyReplace
      hEqFOpBodyReplace hFOpAppOpReplace hFOpFunBodyReplace hFOpBodyReplace)

/-- Side-condition-free wrapper for
`commute_appAbs_structApp_eqStep_of_shifted_fOp_tail_lifts`: the tail stack
prevalidity is recovered from the operator subtype step. -/
theorem commute_appAbs_structApp_eqStep_of_shifted_fOp_tail_lifts_from_left
    {Γ : Ctx} {s : Stack}
    {bound body arg bound₁ body₁ bound₂ body₂ arg' : Term}
    (hcommArg : StrongCommutes Γ (arg :: s))
    (hSubOp : MSubRed Γ (arg :: s) (.abs bound body) (.abs bound₁ body₁))
    (hEqOp : MEqRed Γ (arg :: s) (.abs bound body) (.abs bound₂ body₂))
    (hEqArg : MEqRed Γ [] arg arg')
    (hOldNewStack : MEqRed ({ bound := arg', kind := .equ } :: Γ)
      (Stack.shift 0 s) (Term.shift 0 arg) (Term.shift 0 arg'))
    (hEqSelfReplace :
      ∀ {u v : Term},
        MEqRed ({ bound := arg, kind := .equ } :: Γ) (Stack.shift 0 s) u v →
        MSubStar ({ bound := arg', kind := .equ } :: Γ) (Stack.shift 0 s) u v)
    (hEqAppOpReplace :
      ∀ {op op' operand : Term},
        MEqRed ({ bound := arg, kind := .equ } :: Γ)
          (operand :: Stack.shift 0 s) op op' →
        MEqRed ({ bound := arg', kind := .equ } :: Γ)
          (operand :: Stack.shift 0 s) op op')
    (hNilReplace :
      ∀ {u v : Term},
        MEqRed ({ bound := arg, kind := .equ } :: Γ) [] u v →
        MEqRed ({ bound := arg', kind := .equ } :: Γ) [] u v)
    (hEqFunBodyReplace :
      ∀ {funBound body body' : Term},
        MEqRed ({ bound := funBound, kind := .sub } ::
          { bound := arg, kind := .equ } :: Γ) [] body body' →
        MEqRed ({ bound := funBound, kind := .sub } ::
          { bound := arg', kind := .equ } :: Γ) [] body body')
    (hEqBetBodyReplace :
      ∀ {funBound body body' : Term},
        MEqRed ({ bound := funBound, kind := .sub } ::
          { bound := arg, kind := .equ } :: Γ) (Stack.shift 0 (Stack.shift 0 s))
          body body' →
        MEqRed ({ bound := funBound, kind := .sub } ::
          { bound := arg', kind := .equ } :: Γ) (Stack.shift 0 (Stack.shift 0 s))
          body body')
    (hOldNewTail :
      ∀ {operand : Term} {rest : Stack},
        Term.Scoped (Ctx.depth ({ bound := arg, kind := .equ } :: Γ)) operand →
        Stack.shift 0 s = operand :: rest →
        MEqRed ({ bound := arg', kind := .equ } :: Γ) rest
          (Term.shift 0 arg) (Term.shift 0 arg'))
    (hEqFOpSelfReplace :
      ∀ {operand : Term} {rest : Stack} {u v : Term},
        Term.Scoped (Ctx.depth ({ bound := arg, kind := .equ } :: Γ)) operand →
        Stack.shift 0 s = operand :: rest →
        MEqRed ({ bound := operand, kind := .equ } ::
          { bound := arg, kind := .equ } :: Γ) (Stack.shift 0 rest) u v →
        MSubStar ({ bound := operand, kind := .equ } ::
          { bound := arg', kind := .equ } :: Γ) (Stack.shift 0 rest) u v)
    (hEqFOpAppOpReplace :
      ∀ {operand : Term} {rest : Stack} {op op' inner : Term},
        Term.Scoped (Ctx.depth ({ bound := arg, kind := .equ } :: Γ)) operand →
        Stack.shift 0 s = operand :: rest →
        MEqRed ({ bound := operand, kind := .equ } ::
          { bound := arg, kind := .equ } :: Γ) (inner :: Stack.shift 0 rest) op op' →
        MEqRed ({ bound := operand, kind := .equ } ::
          { bound := arg', kind := .equ } :: Γ) (inner :: Stack.shift 0 rest) op op')
    (hEqFOpNilReplace :
      ∀ {operand : Term} {rest : Stack} {u v : Term},
        Term.Scoped (Ctx.depth ({ bound := arg, kind := .equ } :: Γ)) operand →
        Stack.shift 0 s = operand :: rest →
        MEqRed ({ bound := operand, kind := .equ } ::
          { bound := arg, kind := .equ } :: Γ) [] u v →
        MEqRed ({ bound := operand, kind := .equ } ::
          { bound := arg', kind := .equ } :: Γ) [] u v)
    (hEqFOpFunBodyReplace :
      ∀ {operand : Term} {rest : Stack} {funBound body body' : Term},
        Term.Scoped (Ctx.depth ({ bound := arg, kind := .equ } :: Γ)) operand →
        Stack.shift 0 s = operand :: rest →
        MEqRed ({ bound := funBound, kind := .sub } ::
          { bound := operand, kind := .equ } ::
          { bound := arg, kind := .equ } :: Γ) [] body body' →
        MEqRed ({ bound := funBound, kind := .sub } ::
          { bound := operand, kind := .equ } ::
          { bound := arg', kind := .equ } :: Γ) [] body body')
    (hEqFOpBetBodyReplace :
      ∀ {operand : Term} {rest : Stack} {funBound body body' : Term},
        Term.Scoped (Ctx.depth ({ bound := arg, kind := .equ } :: Γ)) operand →
        Stack.shift 0 s = operand :: rest →
        MEqRed ({ bound := funBound, kind := .sub } ::
          { bound := operand, kind := .equ } ::
          { bound := arg, kind := .equ } :: Γ) (Stack.shift 0 (Stack.shift 0 rest))
          body body' →
        MEqRed ({ bound := funBound, kind := .sub } ::
          { bound := operand, kind := .equ } ::
          { bound := arg', kind := .equ } :: Γ) (Stack.shift 0 (Stack.shift 0 rest))
          body body')
    (hEqFOpBodyReplace :
      ∀ {operand : Term} {rest : Stack} {inner body body' : Term}
          {innerRest : Stack},
        Term.Scoped (Ctx.depth ({ bound := arg, kind := .equ } :: Γ)) operand →
        Stack.shift 0 s = operand :: rest →
        Term.Scoped (Ctx.depth ({ bound := operand, kind := .equ } ::
          { bound := arg, kind := .equ } :: Γ)) inner →
        Stack.shift 0 rest = inner :: innerRest →
        MEqRed ({ bound := inner, kind := .equ } ::
          { bound := operand, kind := .equ } ::
          { bound := arg, kind := .equ } :: Γ) (Stack.shift 0 innerRest) body body' →
        MSubStar ({ bound := inner, kind := .equ } ::
          { bound := operand, kind := .equ } ::
          { bound := arg', kind := .equ } :: Γ) (Stack.shift 0 innerRest) body body')
    (hAppOpReplace :
      ∀ {op op' operand : Term},
        MSubRed ({ bound := arg, kind := .equ } :: Γ)
          (operand :: Stack.shift 0 s) op op' →
        Term.Scoped (Ctx.depth ({ bound := arg, kind := .equ } :: Γ)) operand →
        MSubStar ({ bound := arg', kind := .equ } :: Γ)
          (operand :: Stack.shift 0 s) op op')
    (hFunBodyReplace :
      ∀ {funBound body body' : Term},
        MSubRed ({ bound := funBound, kind := .sub } ::
          { bound := arg, kind := .equ } :: Γ) [] body body' →
        MSubRed ({ bound := funBound, kind := .sub } ::
          { bound := arg', kind := .equ } :: Γ) [] body body')
    (hFOpAppOpReplace :
      ∀ {operand : Term} {rest : Stack} {op op' inner : Term},
        Term.Scoped (Ctx.depth ({ bound := arg, kind := .equ } :: Γ)) operand →
        Stack.shift 0 s = operand :: rest →
        MSubRed ({ bound := operand, kind := .equ } ::
          { bound := arg, kind := .equ } :: Γ) (inner :: Stack.shift 0 rest) op op' →
        Term.Scoped (Ctx.depth ({ bound := operand, kind := .equ } ::
          { bound := arg, kind := .equ } :: Γ)) inner →
        MSubStar ({ bound := operand, kind := .equ } ::
          { bound := arg', kind := .equ } :: Γ) (inner :: Stack.shift 0 rest) op op')
    (hFOpFunBodyReplace :
      ∀ {operand : Term} {rest : Stack} {funBound body body' : Term},
        Term.Scoped (Ctx.depth ({ bound := arg, kind := .equ } :: Γ)) operand →
        Stack.shift 0 s = operand :: rest →
        MSubRed ({ bound := funBound, kind := .sub } ::
          { bound := operand, kind := .equ } ::
          { bound := arg, kind := .equ } :: Γ) [] body body' →
        MSubRed ({ bound := funBound, kind := .sub } ::
          { bound := operand, kind := .equ } ::
          { bound := arg', kind := .equ } :: Γ) [] body body')
    (hFOpBodyReplace :
      ∀ {operand : Term} {rest : Stack} {inner body body' : Term}
          {innerRest : Stack},
        Term.Scoped (Ctx.depth ({ bound := arg, kind := .equ } :: Γ)) operand →
        Stack.shift 0 s = operand :: rest →
        Term.Scoped (Ctx.depth ({ bound := operand, kind := .equ } ::
          { bound := arg, kind := .equ } :: Γ)) inner →
        Stack.shift 0 rest = inner :: innerRest →
        MSubRed ({ bound := inner, kind := .equ } ::
          { bound := operand, kind := .equ } ::
          { bound := arg, kind := .equ } :: Γ) (Stack.shift 0 innerRest) body body' →
        MSubStar ({ bound := inner, kind := .equ } ::
          { bound := operand, kind := .equ } ::
          { bound := arg', kind := .equ } :: Γ) (Stack.shift 0 innerRest) body body') :
    ∃ t₃,
      MEqRedStar Γ s (.app (.abs bound₁ body₁) arg) t₃ ∧
        MSubStar Γ s (.app (.abs bound₂ body₂) arg') t₃ :=
  commute_appAbs_structApp_eqStep_of_shifted_fOp_tail_lifts
    (PrevalidExt.tail hSubOp.prevalidExt) hcommArg hSubOp hEqOp hEqArg
    hOldNewStack hEqSelfReplace hEqAppOpReplace hNilReplace
    hEqFunBodyReplace hEqBetBodyReplace hOldNewTail hEqFOpSelfReplace
    hEqFOpAppOpReplace hEqFOpNilReplace hEqFOpFunBodyReplace
    hEqFOpBetBodyReplace hEqFOpBodyReplace hAppOpReplace hFunBodyReplace
    hFOpAppOpReplace hFOpFunBodyReplace hFOpBodyReplace

/-- Changed-argument structural application commutation where both the
top-level shifted old-to-new argument equivalence and the recursive `FOp`
tail old-to-new equivalences are supplied by one reusable stack-lift
function. -/
theorem commute_appAbs_structApp_eqStep_of_argument_stack_lifted_fOp_tail_lifts
    {Γ : Ctx} {s : Stack}
    {bound body arg bound₁ body₁ bound₂ body₂ arg' : Term}
    (hpvTail : PrevalidExt Γ s)
    (hcommArg : StrongCommutes Γ (arg :: s))
    (hSubOp : MSubRed Γ (arg :: s) (.abs bound body) (.abs bound₁ body₁))
    (hEqOp : MEqRed Γ (arg :: s) (.abs bound body) (.abs bound₂ body₂))
    (hEqArg : MEqRed Γ [] arg arg')
    (hArgStackLift :
      ∀ {tail : Stack},
        PrevalidExt Γ tail →
        MEqRed ({ bound := arg', kind := .equ } :: Γ) (Stack.shift 0 tail)
          (Term.shift 0 arg) (Term.shift 0 arg'))
    (hEqSelfReplace :
      ∀ {u v : Term},
        MEqRed ({ bound := arg, kind := .equ } :: Γ) (Stack.shift 0 s) u v →
        MSubStar ({ bound := arg', kind := .equ } :: Γ) (Stack.shift 0 s) u v)
    (hEqAppOpReplace :
      ∀ {op op' operand : Term},
        MEqRed ({ bound := arg, kind := .equ } :: Γ)
          (operand :: Stack.shift 0 s) op op' →
        MEqRed ({ bound := arg', kind := .equ } :: Γ)
          (operand :: Stack.shift 0 s) op op')
    (hNilReplace :
      ∀ {u v : Term},
        MEqRed ({ bound := arg, kind := .equ } :: Γ) [] u v →
        MEqRed ({ bound := arg', kind := .equ } :: Γ) [] u v)
    (hEqFunBodyReplace :
      ∀ {funBound body body' : Term},
        MEqRed ({ bound := funBound, kind := .sub } ::
          { bound := arg, kind := .equ } :: Γ) [] body body' →
        MEqRed ({ bound := funBound, kind := .sub } ::
          { bound := arg', kind := .equ } :: Γ) [] body body')
    (hEqBetBodyReplace :
      ∀ {funBound body body' : Term},
        MEqRed ({ bound := funBound, kind := .sub } ::
          { bound := arg, kind := .equ } :: Γ) (Stack.shift 0 (Stack.shift 0 s))
          body body' →
        MEqRed ({ bound := funBound, kind := .sub } ::
          { bound := arg', kind := .equ } :: Γ) (Stack.shift 0 (Stack.shift 0 s))
          body body')
    (hEqFOpSelfReplace :
      ∀ {operand : Term} {rest : Stack} {u v : Term},
        Term.Scoped (Ctx.depth ({ bound := arg, kind := .equ } :: Γ)) operand →
        Stack.shift 0 s = operand :: rest →
        MEqRed ({ bound := operand, kind := .equ } ::
          { bound := arg, kind := .equ } :: Γ) (Stack.shift 0 rest) u v →
        MSubStar ({ bound := operand, kind := .equ } ::
          { bound := arg', kind := .equ } :: Γ) (Stack.shift 0 rest) u v)
    (hEqFOpAppOpReplace :
      ∀ {operand : Term} {rest : Stack} {op op' inner : Term},
        Term.Scoped (Ctx.depth ({ bound := arg, kind := .equ } :: Γ)) operand →
        Stack.shift 0 s = operand :: rest →
        MEqRed ({ bound := operand, kind := .equ } ::
          { bound := arg, kind := .equ } :: Γ) (inner :: Stack.shift 0 rest) op op' →
        MEqRed ({ bound := operand, kind := .equ } ::
          { bound := arg', kind := .equ } :: Γ) (inner :: Stack.shift 0 rest) op op')
    (hEqFOpNilReplace :
      ∀ {operand : Term} {rest : Stack} {u v : Term},
        Term.Scoped (Ctx.depth ({ bound := arg, kind := .equ } :: Γ)) operand →
        Stack.shift 0 s = operand :: rest →
        MEqRed ({ bound := operand, kind := .equ } ::
          { bound := arg, kind := .equ } :: Γ) [] u v →
        MEqRed ({ bound := operand, kind := .equ } ::
          { bound := arg', kind := .equ } :: Γ) [] u v)
    (hEqFOpFunBodyReplace :
      ∀ {operand : Term} {rest : Stack} {funBound body body' : Term},
        Term.Scoped (Ctx.depth ({ bound := arg, kind := .equ } :: Γ)) operand →
        Stack.shift 0 s = operand :: rest →
        MEqRed ({ bound := funBound, kind := .sub } ::
          { bound := operand, kind := .equ } ::
          { bound := arg, kind := .equ } :: Γ) [] body body' →
        MEqRed ({ bound := funBound, kind := .sub } ::
          { bound := operand, kind := .equ } ::
          { bound := arg', kind := .equ } :: Γ) [] body body')
    (hEqFOpBetBodyReplace :
      ∀ {operand : Term} {rest : Stack} {funBound body body' : Term},
        Term.Scoped (Ctx.depth ({ bound := arg, kind := .equ } :: Γ)) operand →
        Stack.shift 0 s = operand :: rest →
        MEqRed ({ bound := funBound, kind := .sub } ::
          { bound := operand, kind := .equ } ::
          { bound := arg, kind := .equ } :: Γ) (Stack.shift 0 (Stack.shift 0 rest))
          body body' →
        MEqRed ({ bound := funBound, kind := .sub } ::
          { bound := operand, kind := .equ } ::
          { bound := arg', kind := .equ } :: Γ) (Stack.shift 0 (Stack.shift 0 rest))
          body body')
    (hEqFOpBodyReplace :
      ∀ {operand : Term} {rest : Stack} {inner body body' : Term}
          {innerRest : Stack},
        Term.Scoped (Ctx.depth ({ bound := arg, kind := .equ } :: Γ)) operand →
        Stack.shift 0 s = operand :: rest →
        Term.Scoped (Ctx.depth ({ bound := operand, kind := .equ } ::
          { bound := arg, kind := .equ } :: Γ)) inner →
        Stack.shift 0 rest = inner :: innerRest →
        MEqRed ({ bound := inner, kind := .equ } ::
          { bound := operand, kind := .equ } ::
          { bound := arg, kind := .equ } :: Γ) (Stack.shift 0 innerRest) body body' →
        MSubStar ({ bound := inner, kind := .equ } ::
          { bound := operand, kind := .equ } ::
          { bound := arg', kind := .equ } :: Γ) (Stack.shift 0 innerRest) body body')
    (hAppOpReplace :
      ∀ {op op' operand : Term},
        MSubRed ({ bound := arg, kind := .equ } :: Γ)
          (operand :: Stack.shift 0 s) op op' →
        Term.Scoped (Ctx.depth ({ bound := arg, kind := .equ } :: Γ)) operand →
        MSubStar ({ bound := arg', kind := .equ } :: Γ)
          (operand :: Stack.shift 0 s) op op')
    (hFunBodyReplace :
      ∀ {funBound body body' : Term},
        MSubRed ({ bound := funBound, kind := .sub } ::
          { bound := arg, kind := .equ } :: Γ) [] body body' →
        MSubRed ({ bound := funBound, kind := .sub } ::
          { bound := arg', kind := .equ } :: Γ) [] body body')
    (hFOpAppOpReplace :
      ∀ {operand : Term} {rest : Stack} {op op' inner : Term},
        Term.Scoped (Ctx.depth ({ bound := arg, kind := .equ } :: Γ)) operand →
        Stack.shift 0 s = operand :: rest →
        MSubRed ({ bound := operand, kind := .equ } ::
          { bound := arg, kind := .equ } :: Γ) (inner :: Stack.shift 0 rest) op op' →
        Term.Scoped (Ctx.depth ({ bound := operand, kind := .equ } ::
          { bound := arg, kind := .equ } :: Γ)) inner →
        MSubStar ({ bound := operand, kind := .equ } ::
          { bound := arg', kind := .equ } :: Γ) (inner :: Stack.shift 0 rest) op op')
    (hFOpFunBodyReplace :
      ∀ {operand : Term} {rest : Stack} {funBound body body' : Term},
        Term.Scoped (Ctx.depth ({ bound := arg, kind := .equ } :: Γ)) operand →
        Stack.shift 0 s = operand :: rest →
        MSubRed ({ bound := funBound, kind := .sub } ::
          { bound := operand, kind := .equ } ::
          { bound := arg, kind := .equ } :: Γ) [] body body' →
        MSubRed ({ bound := funBound, kind := .sub } ::
          { bound := operand, kind := .equ } ::
          { bound := arg', kind := .equ } :: Γ) [] body body')
    (hFOpBodyReplace :
      ∀ {operand : Term} {rest : Stack} {inner body body' : Term}
          {innerRest : Stack},
        Term.Scoped (Ctx.depth ({ bound := arg, kind := .equ } :: Γ)) operand →
        Stack.shift 0 s = operand :: rest →
        Term.Scoped (Ctx.depth ({ bound := operand, kind := .equ } ::
          { bound := arg, kind := .equ } :: Γ)) inner →
        Stack.shift 0 rest = inner :: innerRest →
        MSubRed ({ bound := inner, kind := .equ } ::
          { bound := operand, kind := .equ } ::
          { bound := arg, kind := .equ } :: Γ) (Stack.shift 0 innerRest) body body' →
        MSubStar ({ bound := inner, kind := .equ } ::
          { bound := operand, kind := .equ } ::
          { bound := arg', kind := .equ } :: Γ) (Stack.shift 0 innerRest) body body') :
    ∃ t₃,
      MEqRedStar Γ s (.app (.abs bound₁ body₁) arg) t₃ ∧
        MSubStar Γ s (.app (.abs bound₂ body₂) arg') t₃ := by
  refine commute_appAbs_structApp_eqStep_of_shifted_fOp_tail_lifts
    hpvTail hcommArg hSubOp hEqOp hEqArg (hArgStackLift hpvTail)
    hEqSelfReplace hEqAppOpReplace hNilReplace hEqFunBodyReplace
    hEqBetBodyReplace ?_ hEqFOpSelfReplace hEqFOpAppOpReplace
    hEqFOpNilReplace hEqFOpFunBodyReplace hEqFOpBetBodyReplace
    hEqFOpBodyReplace hAppOpReplace hFunBodyReplace hFOpAppOpReplace
    hFOpFunBodyReplace hFOpBodyReplace
  intro operand rest _hOperand hStack
  cases s with
  | nil =>
    simp at hStack
  | cons operand₀ tail₀ =>
    injection hStack with _hOperandEq hRestEq
    subst hRestEq
    exact hArgStackLift (PrevalidExt.tail hpvTail)

/-- Side-condition-free wrapper for
`commute_appAbs_structApp_eqStep_of_argument_stack_lifted_fOp_tail_lifts`:
the tail stack prevalidity is recovered from the operator subtype step. -/
theorem commute_appAbs_structApp_eqStep_of_argument_stack_lifted_fOp_tail_lifts_from_left
    {Γ : Ctx} {s : Stack}
    {bound body arg bound₁ body₁ bound₂ body₂ arg' : Term}
    (hcommArg : StrongCommutes Γ (arg :: s))
    (hSubOp : MSubRed Γ (arg :: s) (.abs bound body) (.abs bound₁ body₁))
    (hEqOp : MEqRed Γ (arg :: s) (.abs bound body) (.abs bound₂ body₂))
    (hEqArg : MEqRed Γ [] arg arg')
    (hArgStackLift :
      ∀ {tail : Stack},
        PrevalidExt Γ tail →
        MEqRed ({ bound := arg', kind := .equ } :: Γ) (Stack.shift 0 tail)
          (Term.shift 0 arg) (Term.shift 0 arg'))
    (hEqSelfReplace :
      ∀ {u v : Term},
        MEqRed ({ bound := arg, kind := .equ } :: Γ) (Stack.shift 0 s) u v →
        MSubStar ({ bound := arg', kind := .equ } :: Γ) (Stack.shift 0 s) u v)
    (hEqAppOpReplace :
      ∀ {op op' operand : Term},
        MEqRed ({ bound := arg, kind := .equ } :: Γ)
          (operand :: Stack.shift 0 s) op op' →
        MEqRed ({ bound := arg', kind := .equ } :: Γ)
          (operand :: Stack.shift 0 s) op op')
    (hNilReplace :
      ∀ {u v : Term},
        MEqRed ({ bound := arg, kind := .equ } :: Γ) [] u v →
        MEqRed ({ bound := arg', kind := .equ } :: Γ) [] u v)
    (hEqFunBodyReplace :
      ∀ {funBound body body' : Term},
        MEqRed ({ bound := funBound, kind := .sub } ::
          { bound := arg, kind := .equ } :: Γ) [] body body' →
        MEqRed ({ bound := funBound, kind := .sub } ::
          { bound := arg', kind := .equ } :: Γ) [] body body')
    (hEqBetBodyReplace :
      ∀ {funBound body body' : Term},
        MEqRed ({ bound := funBound, kind := .sub } ::
          { bound := arg, kind := .equ } :: Γ) (Stack.shift 0 (Stack.shift 0 s))
          body body' →
        MEqRed ({ bound := funBound, kind := .sub } ::
          { bound := arg', kind := .equ } :: Γ) (Stack.shift 0 (Stack.shift 0 s))
          body body')
    (hEqFOpSelfReplace :
      ∀ {operand : Term} {rest : Stack} {u v : Term},
        Term.Scoped (Ctx.depth ({ bound := arg, kind := .equ } :: Γ)) operand →
        Stack.shift 0 s = operand :: rest →
        MEqRed ({ bound := operand, kind := .equ } ::
          { bound := arg, kind := .equ } :: Γ) (Stack.shift 0 rest) u v →
        MSubStar ({ bound := operand, kind := .equ } ::
          { bound := arg', kind := .equ } :: Γ) (Stack.shift 0 rest) u v)
    (hEqFOpAppOpReplace :
      ∀ {operand : Term} {rest : Stack} {op op' inner : Term},
        Term.Scoped (Ctx.depth ({ bound := arg, kind := .equ } :: Γ)) operand →
        Stack.shift 0 s = operand :: rest →
        MEqRed ({ bound := operand, kind := .equ } ::
          { bound := arg, kind := .equ } :: Γ) (inner :: Stack.shift 0 rest) op op' →
        MEqRed ({ bound := operand, kind := .equ } ::
          { bound := arg', kind := .equ } :: Γ) (inner :: Stack.shift 0 rest) op op')
    (hEqFOpNilReplace :
      ∀ {operand : Term} {rest : Stack} {u v : Term},
        Term.Scoped (Ctx.depth ({ bound := arg, kind := .equ } :: Γ)) operand →
        Stack.shift 0 s = operand :: rest →
        MEqRed ({ bound := operand, kind := .equ } ::
          { bound := arg, kind := .equ } :: Γ) [] u v →
        MEqRed ({ bound := operand, kind := .equ } ::
          { bound := arg', kind := .equ } :: Γ) [] u v)
    (hEqFOpFunBodyReplace :
      ∀ {operand : Term} {rest : Stack} {funBound body body' : Term},
        Term.Scoped (Ctx.depth ({ bound := arg, kind := .equ } :: Γ)) operand →
        Stack.shift 0 s = operand :: rest →
        MEqRed ({ bound := funBound, kind := .sub } ::
          { bound := operand, kind := .equ } ::
          { bound := arg, kind := .equ } :: Γ) [] body body' →
        MEqRed ({ bound := funBound, kind := .sub } ::
          { bound := operand, kind := .equ } ::
          { bound := arg', kind := .equ } :: Γ) [] body body')
    (hEqFOpBetBodyReplace :
      ∀ {operand : Term} {rest : Stack} {funBound body body' : Term},
        Term.Scoped (Ctx.depth ({ bound := arg, kind := .equ } :: Γ)) operand →
        Stack.shift 0 s = operand :: rest →
        MEqRed ({ bound := funBound, kind := .sub } ::
          { bound := operand, kind := .equ } ::
          { bound := arg, kind := .equ } :: Γ) (Stack.shift 0 (Stack.shift 0 rest))
          body body' →
        MEqRed ({ bound := funBound, kind := .sub } ::
          { bound := operand, kind := .equ } ::
          { bound := arg', kind := .equ } :: Γ) (Stack.shift 0 (Stack.shift 0 rest))
          body body')
    (hEqFOpBodyReplace :
      ∀ {operand : Term} {rest : Stack} {inner body body' : Term}
          {innerRest : Stack},
        Term.Scoped (Ctx.depth ({ bound := arg, kind := .equ } :: Γ)) operand →
        Stack.shift 0 s = operand :: rest →
        Term.Scoped (Ctx.depth ({ bound := operand, kind := .equ } ::
          { bound := arg, kind := .equ } :: Γ)) inner →
        Stack.shift 0 rest = inner :: innerRest →
        MEqRed ({ bound := inner, kind := .equ } ::
          { bound := operand, kind := .equ } ::
          { bound := arg, kind := .equ } :: Γ) (Stack.shift 0 innerRest) body body' →
        MSubStar ({ bound := inner, kind := .equ } ::
          { bound := operand, kind := .equ } ::
          { bound := arg', kind := .equ } :: Γ) (Stack.shift 0 innerRest) body body')
    (hAppOpReplace :
      ∀ {op op' operand : Term},
        MSubRed ({ bound := arg, kind := .equ } :: Γ)
          (operand :: Stack.shift 0 s) op op' →
        Term.Scoped (Ctx.depth ({ bound := arg, kind := .equ } :: Γ)) operand →
        MSubStar ({ bound := arg', kind := .equ } :: Γ)
          (operand :: Stack.shift 0 s) op op')
    (hFunBodyReplace :
      ∀ {funBound body body' : Term},
        MSubRed ({ bound := funBound, kind := .sub } ::
          { bound := arg, kind := .equ } :: Γ) [] body body' →
        MSubRed ({ bound := funBound, kind := .sub } ::
          { bound := arg', kind := .equ } :: Γ) [] body body')
    (hFOpAppOpReplace :
      ∀ {operand : Term} {rest : Stack} {op op' inner : Term},
        Term.Scoped (Ctx.depth ({ bound := arg, kind := .equ } :: Γ)) operand →
        Stack.shift 0 s = operand :: rest →
        MSubRed ({ bound := operand, kind := .equ } ::
          { bound := arg, kind := .equ } :: Γ) (inner :: Stack.shift 0 rest) op op' →
        Term.Scoped (Ctx.depth ({ bound := operand, kind := .equ } ::
          { bound := arg, kind := .equ } :: Γ)) inner →
        MSubStar ({ bound := operand, kind := .equ } ::
          { bound := arg', kind := .equ } :: Γ) (inner :: Stack.shift 0 rest) op op')
    (hFOpFunBodyReplace :
      ∀ {operand : Term} {rest : Stack} {funBound body body' : Term},
        Term.Scoped (Ctx.depth ({ bound := arg, kind := .equ } :: Γ)) operand →
        Stack.shift 0 s = operand :: rest →
        MSubRed ({ bound := funBound, kind := .sub } ::
          { bound := operand, kind := .equ } ::
          { bound := arg, kind := .equ } :: Γ) [] body body' →
        MSubRed ({ bound := funBound, kind := .sub } ::
          { bound := operand, kind := .equ } ::
          { bound := arg', kind := .equ } :: Γ) [] body body')
    (hFOpBodyReplace :
      ∀ {operand : Term} {rest : Stack} {inner body body' : Term}
          {innerRest : Stack},
        Term.Scoped (Ctx.depth ({ bound := arg, kind := .equ } :: Γ)) operand →
        Stack.shift 0 s = operand :: rest →
        Term.Scoped (Ctx.depth ({ bound := operand, kind := .equ } ::
          { bound := arg, kind := .equ } :: Γ)) inner →
        Stack.shift 0 rest = inner :: innerRest →
        MSubRed ({ bound := inner, kind := .equ } ::
          { bound := operand, kind := .equ } ::
          { bound := arg, kind := .equ } :: Γ) (Stack.shift 0 innerRest) body body' →
        MSubStar ({ bound := inner, kind := .equ } ::
          { bound := operand, kind := .equ } ::
          { bound := arg', kind := .equ } :: Γ) (Stack.shift 0 innerRest) body body') :
    ∃ t₃,
      MEqRedStar Γ s (.app (.abs bound₁ body₁) arg) t₃ ∧
        MSubStar Γ s (.app (.abs bound₂ body₂) arg') t₃ :=
  commute_appAbs_structApp_eqStep_of_argument_stack_lifted_fOp_tail_lifts
    (PrevalidExt.tail hSubOp.prevalidExt) hcommArg hSubOp hEqOp hEqArg
    hArgStackLift hEqSelfReplace hEqAppOpReplace hNilReplace
    hEqFunBodyReplace hEqBetBodyReplace hEqFOpSelfReplace
    hEqFOpAppOpReplace hEqFOpNilReplace hEqFOpFunBodyReplace
    hEqFOpBetBodyReplace hEqFOpBodyReplace hAppOpReplace hFunBodyReplace
    hFOpAppOpReplace hFOpFunBodyReplace hFOpBodyReplace

/-- Changed-argument structural application commutation where the reusable
argument stack-lift function is built from the canonical changed-head
stack-lift replacement package. -/
theorem commute_appAbs_structApp_eqStep_of_argument_replacement_fOp_tail_lifts
    {Γ : Ctx} {s : Stack}
    {bound body arg bound₁ body₁ bound₂ body₂ arg' : Term}
    (hpvTail : PrevalidExt Γ s)
    (hcommArg : StrongCommutes Γ (arg :: s))
    (hSubOp : MSubRed Γ (arg :: s) (.abs bound body) (.abs bound₁ body₁))
    (hEqOp : MEqRed Γ (arg :: s) (.abs bound body) (.abs bound₂ body₂))
    (hEqArg : MEqRed Γ [] arg arg')
    (hArgProReplace :
      ∀ {tail : Stack},
        PrevalidExt Γ tail →
        ∀ {α α' : Term},
          MEqRed Γ [] α α' →
          MEqRed ({ bound := arg', kind := .equ } :: Γ) (Stack.shift 0 tail)
            (Term.shift 0 α) (Term.shift 0 α'))
    (hArgAppOpReplace :
      ∀ {tail : Stack},
        PrevalidExt Γ tail →
        ∀ {op op' operand : Term},
          MEqRed Γ (operand :: []) op op' →
          MEqRed ({ bound := arg', kind := .equ } :: Γ)
            (Term.shift 0 operand :: Stack.shift 0 tail)
            (Term.shift 0 op) (Term.shift 0 op'))
    (hArgNilReplace :
      ∀ {u v : Term},
        MEqRed Γ [] u v →
        MEqRed ({ bound := arg', kind := .equ } :: Γ) []
          (Term.shift 0 u) (Term.shift 0 v))
    (hArgFunNilBodyReplace :
      ∀ {funBound body body' : Term},
        MEqRed ({ bound := funBound, kind := .sub } :: Γ) [] body body' →
        MEqRed ({ bound := Term.shift 0 funBound, kind := .sub } ::
          { bound := arg', kind := .equ } :: Γ) []
          (Term.shift 1 body) (Term.shift 1 body'))
    (hArgFunConsBodyReplace :
      ∀ {operand funBound body body' : Term} {rest : Stack},
        Term.Scoped Γ.depth operand →
        MEqRed ({ bound := funBound, kind := .sub } :: Γ) [] body body' →
        MEqRed ({ bound := Term.shift 0 operand, kind := .equ } ::
          { bound := arg', kind := .equ } :: Γ)
          (Stack.shift 0 (Stack.shift 0 rest)) (Term.shift 1 body) (Term.shift 1 body'))
    (hArgBetBodyReplace :
      ∀ {tail : Stack},
        PrevalidExt Γ tail →
        ∀ {funBound body body' : Term},
          MEqRed ({ bound := funBound, kind := .sub } :: Γ) (Stack.shift 0 [])
            body body' →
          MEqRed ({ bound := Term.shift 0 funBound, kind := .sub } ::
            { bound := arg', kind := .equ } :: Γ) (Stack.shift 0 (Stack.shift 0 tail))
            (Term.shift 1 body) (Term.shift 1 body'))
    (hEqSelfReplace :
      ∀ {u v : Term},
        MEqRed ({ bound := arg, kind := .equ } :: Γ) (Stack.shift 0 s) u v →
        MSubStar ({ bound := arg', kind := .equ } :: Γ) (Stack.shift 0 s) u v)
    (hEqAppOpReplace :
      ∀ {op op' operand : Term},
        MEqRed ({ bound := arg, kind := .equ } :: Γ)
          (operand :: Stack.shift 0 s) op op' →
        MEqRed ({ bound := arg', kind := .equ } :: Γ)
          (operand :: Stack.shift 0 s) op op')
    (hNilReplace :
      ∀ {u v : Term},
        MEqRed ({ bound := arg, kind := .equ } :: Γ) [] u v →
        MEqRed ({ bound := arg', kind := .equ } :: Γ) [] u v)
    (hEqFunBodyReplace :
      ∀ {funBound body body' : Term},
        MEqRed ({ bound := funBound, kind := .sub } ::
          { bound := arg, kind := .equ } :: Γ) [] body body' →
        MEqRed ({ bound := funBound, kind := .sub } ::
          { bound := arg', kind := .equ } :: Γ) [] body body')
    (hEqBetBodyReplace :
      ∀ {funBound body body' : Term},
        MEqRed ({ bound := funBound, kind := .sub } ::
          { bound := arg, kind := .equ } :: Γ) (Stack.shift 0 (Stack.shift 0 s))
          body body' →
        MEqRed ({ bound := funBound, kind := .sub } ::
          { bound := arg', kind := .equ } :: Γ) (Stack.shift 0 (Stack.shift 0 s))
          body body')
    (hEqFOpSelfReplace :
      ∀ {operand : Term} {rest : Stack} {u v : Term},
        Term.Scoped (Ctx.depth ({ bound := arg, kind := .equ } :: Γ)) operand →
        Stack.shift 0 s = operand :: rest →
        MEqRed ({ bound := operand, kind := .equ } ::
          { bound := arg, kind := .equ } :: Γ) (Stack.shift 0 rest) u v →
        MSubStar ({ bound := operand, kind := .equ } ::
          { bound := arg', kind := .equ } :: Γ) (Stack.shift 0 rest) u v)
    (hEqFOpAppOpReplace :
      ∀ {operand : Term} {rest : Stack} {op op' inner : Term},
        Term.Scoped (Ctx.depth ({ bound := arg, kind := .equ } :: Γ)) operand →
        Stack.shift 0 s = operand :: rest →
        MEqRed ({ bound := operand, kind := .equ } ::
          { bound := arg, kind := .equ } :: Γ) (inner :: Stack.shift 0 rest) op op' →
        MEqRed ({ bound := operand, kind := .equ } ::
          { bound := arg', kind := .equ } :: Γ) (inner :: Stack.shift 0 rest) op op')
    (hEqFOpNilReplace :
      ∀ {operand : Term} {rest : Stack} {u v : Term},
        Term.Scoped (Ctx.depth ({ bound := arg, kind := .equ } :: Γ)) operand →
        Stack.shift 0 s = operand :: rest →
        MEqRed ({ bound := operand, kind := .equ } ::
          { bound := arg, kind := .equ } :: Γ) [] u v →
        MEqRed ({ bound := operand, kind := .equ } ::
          { bound := arg', kind := .equ } :: Γ) [] u v)
    (hEqFOpFunBodyReplace :
      ∀ {operand : Term} {rest : Stack} {funBound body body' : Term},
        Term.Scoped (Ctx.depth ({ bound := arg, kind := .equ } :: Γ)) operand →
        Stack.shift 0 s = operand :: rest →
        MEqRed ({ bound := funBound, kind := .sub } ::
          { bound := operand, kind := .equ } ::
          { bound := arg, kind := .equ } :: Γ) [] body body' →
        MEqRed ({ bound := funBound, kind := .sub } ::
          { bound := operand, kind := .equ } ::
          { bound := arg', kind := .equ } :: Γ) [] body body')
    (hEqFOpBetBodyReplace :
      ∀ {operand : Term} {rest : Stack} {funBound body body' : Term},
        Term.Scoped (Ctx.depth ({ bound := arg, kind := .equ } :: Γ)) operand →
        Stack.shift 0 s = operand :: rest →
        MEqRed ({ bound := funBound, kind := .sub } ::
          { bound := operand, kind := .equ } ::
          { bound := arg, kind := .equ } :: Γ) (Stack.shift 0 (Stack.shift 0 rest))
          body body' →
        MEqRed ({ bound := funBound, kind := .sub } ::
          { bound := operand, kind := .equ } ::
          { bound := arg', kind := .equ } :: Γ) (Stack.shift 0 (Stack.shift 0 rest))
          body body')
    (hEqFOpBodyReplace :
      ∀ {operand : Term} {rest : Stack} {inner body body' : Term}
          {innerRest : Stack},
        Term.Scoped (Ctx.depth ({ bound := arg, kind := .equ } :: Γ)) operand →
        Stack.shift 0 s = operand :: rest →
        Term.Scoped (Ctx.depth ({ bound := operand, kind := .equ } ::
          { bound := arg, kind := .equ } :: Γ)) inner →
        Stack.shift 0 rest = inner :: innerRest →
        MEqRed ({ bound := inner, kind := .equ } ::
          { bound := operand, kind := .equ } ::
          { bound := arg, kind := .equ } :: Γ) (Stack.shift 0 innerRest) body body' →
        MSubStar ({ bound := inner, kind := .equ } ::
          { bound := operand, kind := .equ } ::
          { bound := arg', kind := .equ } :: Γ) (Stack.shift 0 innerRest) body body')
    (hAppOpReplace :
      ∀ {op op' operand : Term},
        MSubRed ({ bound := arg, kind := .equ } :: Γ)
          (operand :: Stack.shift 0 s) op op' →
        Term.Scoped (Ctx.depth ({ bound := arg, kind := .equ } :: Γ)) operand →
        MSubStar ({ bound := arg', kind := .equ } :: Γ)
          (operand :: Stack.shift 0 s) op op')
    (hFunBodyReplace :
      ∀ {funBound body body' : Term},
        MSubRed ({ bound := funBound, kind := .sub } ::
          { bound := arg, kind := .equ } :: Γ) [] body body' →
        MSubRed ({ bound := funBound, kind := .sub } ::
          { bound := arg', kind := .equ } :: Γ) [] body body')
    (hFOpAppOpReplace :
      ∀ {operand : Term} {rest : Stack} {op op' inner : Term},
        Term.Scoped (Ctx.depth ({ bound := arg, kind := .equ } :: Γ)) operand →
        Stack.shift 0 s = operand :: rest →
        MSubRed ({ bound := operand, kind := .equ } ::
          { bound := arg, kind := .equ } :: Γ) (inner :: Stack.shift 0 rest) op op' →
        Term.Scoped (Ctx.depth ({ bound := operand, kind := .equ } ::
          { bound := arg, kind := .equ } :: Γ)) inner →
        MSubStar ({ bound := operand, kind := .equ } ::
          { bound := arg', kind := .equ } :: Γ) (inner :: Stack.shift 0 rest) op op')
    (hFOpFunBodyReplace :
      ∀ {operand : Term} {rest : Stack} {funBound body body' : Term},
        Term.Scoped (Ctx.depth ({ bound := arg, kind := .equ } :: Γ)) operand →
        Stack.shift 0 s = operand :: rest →
        MSubRed ({ bound := funBound, kind := .sub } ::
          { bound := operand, kind := .equ } ::
          { bound := arg, kind := .equ } :: Γ) [] body body' →
        MSubRed ({ bound := funBound, kind := .sub } ::
          { bound := operand, kind := .equ } ::
          { bound := arg', kind := .equ } :: Γ) [] body body')
    (hFOpBodyReplace :
      ∀ {operand : Term} {rest : Stack} {inner body body' : Term}
          {innerRest : Stack},
        Term.Scoped (Ctx.depth ({ bound := arg, kind := .equ } :: Γ)) operand →
        Stack.shift 0 s = operand :: rest →
        Term.Scoped (Ctx.depth ({ bound := operand, kind := .equ } ::
          { bound := arg, kind := .equ } :: Γ)) inner →
        Stack.shift 0 rest = inner :: innerRest →
        MSubRed ({ bound := inner, kind := .equ } ::
          { bound := operand, kind := .equ } ::
          { bound := arg, kind := .equ } :: Γ) (Stack.shift 0 innerRest) body body' →
        MSubStar ({ bound := inner, kind := .equ } ::
          { bound := operand, kind := .equ } ::
          { bound := arg', kind := .equ } :: Γ) (Stack.shift 0 innerRest) body body') :
    ∃ t₃,
      MEqRedStar Γ s (.app (.abs bound₁ body₁) arg) t₃ ∧
        MSubStar Γ s (.app (.abs bound₂ body₂) arg') t₃ := by
  have hArg'Scoped : Term.Scoped Γ.depth arg' := hEqArg.scoped_right
  exact commute_appAbs_structApp_eqStep_of_argument_stack_lifted_fOp_tail_lifts
    hpvTail hcommArg hSubOp hEqOp hEqArg
    (meq_equ_head_stack_lift_function_from_replacements hArg'Scoped
      hArgProReplace hArgAppOpReplace hArgNilReplace hArgFunNilBodyReplace
      hArgFunConsBodyReplace hArgBetBodyReplace hEqArg)
    hEqSelfReplace hEqAppOpReplace hNilReplace hEqFunBodyReplace
    hEqBetBodyReplace hEqFOpSelfReplace hEqFOpAppOpReplace hEqFOpNilReplace
    hEqFOpFunBodyReplace hEqFOpBetBodyReplace hEqFOpBodyReplace hAppOpReplace
    hFunBodyReplace hFOpAppOpReplace hFOpFunBodyReplace hFOpBodyReplace

/-- Side-condition-free wrapper for
`commute_appAbs_structApp_eqStep_of_argument_replacement_fOp_tail_lifts`:
the tail stack prevalidity is recovered from the operator subtype step. -/
theorem commute_appAbs_structApp_eqStep_of_argument_replacement_fOp_tail_lifts_from_left
    {Γ : Ctx} {s : Stack}
    {bound body arg bound₁ body₁ bound₂ body₂ arg' : Term}
    (hcommArg : StrongCommutes Γ (arg :: s))
    (hSubOp : MSubRed Γ (arg :: s) (.abs bound body) (.abs bound₁ body₁))
    (hEqOp : MEqRed Γ (arg :: s) (.abs bound body) (.abs bound₂ body₂))
    (hEqArg : MEqRed Γ [] arg arg')
    (hArgProReplace :
      ∀ {tail : Stack},
        PrevalidExt Γ tail →
        ∀ {α α' : Term},
          MEqRed Γ [] α α' →
          MEqRed ({ bound := arg', kind := .equ } :: Γ) (Stack.shift 0 tail)
            (Term.shift 0 α) (Term.shift 0 α'))
    (hArgAppOpReplace :
      ∀ {tail : Stack},
        PrevalidExt Γ tail →
        ∀ {op op' operand : Term},
          MEqRed Γ (operand :: []) op op' →
          MEqRed ({ bound := arg', kind := .equ } :: Γ)
            (Term.shift 0 operand :: Stack.shift 0 tail)
            (Term.shift 0 op) (Term.shift 0 op'))
    (hArgNilReplace :
      ∀ {u v : Term},
        MEqRed Γ [] u v →
        MEqRed ({ bound := arg', kind := .equ } :: Γ) []
          (Term.shift 0 u) (Term.shift 0 v))
    (hArgFunNilBodyReplace :
      ∀ {funBound body body' : Term},
        MEqRed ({ bound := funBound, kind := .sub } :: Γ) [] body body' →
        MEqRed ({ bound := Term.shift 0 funBound, kind := .sub } ::
          { bound := arg', kind := .equ } :: Γ) []
          (Term.shift 1 body) (Term.shift 1 body'))
    (hArgFunConsBodyReplace :
      ∀ {operand funBound body body' : Term} {rest : Stack},
        Term.Scoped Γ.depth operand →
        MEqRed ({ bound := funBound, kind := .sub } :: Γ) [] body body' →
        MEqRed ({ bound := Term.shift 0 operand, kind := .equ } ::
          { bound := arg', kind := .equ } :: Γ)
          (Stack.shift 0 (Stack.shift 0 rest)) (Term.shift 1 body) (Term.shift 1 body'))
    (hArgBetBodyReplace :
      ∀ {tail : Stack},
        PrevalidExt Γ tail →
        ∀ {funBound body body' : Term},
          MEqRed ({ bound := funBound, kind := .sub } :: Γ) (Stack.shift 0 [])
            body body' →
          MEqRed ({ bound := Term.shift 0 funBound, kind := .sub } ::
            { bound := arg', kind := .equ } :: Γ) (Stack.shift 0 (Stack.shift 0 tail))
            (Term.shift 1 body) (Term.shift 1 body'))
    (hEqSelfReplace :
      ∀ {u v : Term},
        MEqRed ({ bound := arg, kind := .equ } :: Γ) (Stack.shift 0 s) u v →
        MSubStar ({ bound := arg', kind := .equ } :: Γ) (Stack.shift 0 s) u v)
    (hEqAppOpReplace :
      ∀ {op op' operand : Term},
        MEqRed ({ bound := arg, kind := .equ } :: Γ)
          (operand :: Stack.shift 0 s) op op' →
        MEqRed ({ bound := arg', kind := .equ } :: Γ)
          (operand :: Stack.shift 0 s) op op')
    (hNilReplace :
      ∀ {u v : Term},
        MEqRed ({ bound := arg, kind := .equ } :: Γ) [] u v →
        MEqRed ({ bound := arg', kind := .equ } :: Γ) [] u v)
    (hEqFunBodyReplace :
      ∀ {funBound body body' : Term},
        MEqRed ({ bound := funBound, kind := .sub } ::
          { bound := arg, kind := .equ } :: Γ) [] body body' →
        MEqRed ({ bound := funBound, kind := .sub } ::
          { bound := arg', kind := .equ } :: Γ) [] body body')
    (hEqBetBodyReplace :
      ∀ {funBound body body' : Term},
        MEqRed ({ bound := funBound, kind := .sub } ::
          { bound := arg, kind := .equ } :: Γ) (Stack.shift 0 (Stack.shift 0 s))
          body body' →
        MEqRed ({ bound := funBound, kind := .sub } ::
          { bound := arg', kind := .equ } :: Γ) (Stack.shift 0 (Stack.shift 0 s))
          body body')
    (hEqFOpSelfReplace :
      ∀ {operand : Term} {rest : Stack} {u v : Term},
        Term.Scoped (Ctx.depth ({ bound := arg, kind := .equ } :: Γ)) operand →
        Stack.shift 0 s = operand :: rest →
        MEqRed ({ bound := operand, kind := .equ } ::
          { bound := arg, kind := .equ } :: Γ) (Stack.shift 0 rest) u v →
        MSubStar ({ bound := operand, kind := .equ } ::
          { bound := arg', kind := .equ } :: Γ) (Stack.shift 0 rest) u v)
    (hEqFOpAppOpReplace :
      ∀ {operand : Term} {rest : Stack} {op op' inner : Term},
        Term.Scoped (Ctx.depth ({ bound := arg, kind := .equ } :: Γ)) operand →
        Stack.shift 0 s = operand :: rest →
        MEqRed ({ bound := operand, kind := .equ } ::
          { bound := arg, kind := .equ } :: Γ) (inner :: Stack.shift 0 rest) op op' →
        MEqRed ({ bound := operand, kind := .equ } ::
          { bound := arg', kind := .equ } :: Γ) (inner :: Stack.shift 0 rest) op op')
    (hEqFOpNilReplace :
      ∀ {operand : Term} {rest : Stack} {u v : Term},
        Term.Scoped (Ctx.depth ({ bound := arg, kind := .equ } :: Γ)) operand →
        Stack.shift 0 s = operand :: rest →
        MEqRed ({ bound := operand, kind := .equ } ::
          { bound := arg, kind := .equ } :: Γ) [] u v →
        MEqRed ({ bound := operand, kind := .equ } ::
          { bound := arg', kind := .equ } :: Γ) [] u v)
    (hEqFOpFunBodyReplace :
      ∀ {operand : Term} {rest : Stack} {funBound body body' : Term},
        Term.Scoped (Ctx.depth ({ bound := arg, kind := .equ } :: Γ)) operand →
        Stack.shift 0 s = operand :: rest →
        MEqRed ({ bound := funBound, kind := .sub } ::
          { bound := operand, kind := .equ } ::
          { bound := arg, kind := .equ } :: Γ) [] body body' →
        MEqRed ({ bound := funBound, kind := .sub } ::
          { bound := operand, kind := .equ } ::
          { bound := arg', kind := .equ } :: Γ) [] body body')
    (hEqFOpBetBodyReplace :
      ∀ {operand : Term} {rest : Stack} {funBound body body' : Term},
        Term.Scoped (Ctx.depth ({ bound := arg, kind := .equ } :: Γ)) operand →
        Stack.shift 0 s = operand :: rest →
        MEqRed ({ bound := funBound, kind := .sub } ::
          { bound := operand, kind := .equ } ::
          { bound := arg, kind := .equ } :: Γ) (Stack.shift 0 (Stack.shift 0 rest))
          body body' →
        MEqRed ({ bound := funBound, kind := .sub } ::
          { bound := operand, kind := .equ } ::
          { bound := arg', kind := .equ } :: Γ) (Stack.shift 0 (Stack.shift 0 rest))
          body body')
    (hEqFOpBodyReplace :
      ∀ {operand : Term} {rest : Stack} {inner body body' : Term}
          {innerRest : Stack},
        Term.Scoped (Ctx.depth ({ bound := arg, kind := .equ } :: Γ)) operand →
        Stack.shift 0 s = operand :: rest →
        Term.Scoped (Ctx.depth ({ bound := operand, kind := .equ } ::
          { bound := arg, kind := .equ } :: Γ)) inner →
        Stack.shift 0 rest = inner :: innerRest →
        MEqRed ({ bound := inner, kind := .equ } ::
          { bound := operand, kind := .equ } ::
          { bound := arg, kind := .equ } :: Γ) (Stack.shift 0 innerRest) body body' →
        MSubStar ({ bound := inner, kind := .equ } ::
          { bound := operand, kind := .equ } ::
          { bound := arg', kind := .equ } :: Γ) (Stack.shift 0 innerRest) body body')
    (hAppOpReplace :
      ∀ {op op' operand : Term},
        MSubRed ({ bound := arg, kind := .equ } :: Γ)
          (operand :: Stack.shift 0 s) op op' →
        Term.Scoped (Ctx.depth ({ bound := arg, kind := .equ } :: Γ)) operand →
        MSubStar ({ bound := arg', kind := .equ } :: Γ)
          (operand :: Stack.shift 0 s) op op')
    (hFunBodyReplace :
      ∀ {funBound body body' : Term},
        MSubRed ({ bound := funBound, kind := .sub } ::
          { bound := arg, kind := .equ } :: Γ) [] body body' →
        MSubRed ({ bound := funBound, kind := .sub } ::
          { bound := arg', kind := .equ } :: Γ) [] body body')
    (hFOpAppOpReplace :
      ∀ {operand : Term} {rest : Stack} {op op' inner : Term},
        Term.Scoped (Ctx.depth ({ bound := arg, kind := .equ } :: Γ)) operand →
        Stack.shift 0 s = operand :: rest →
        MSubRed ({ bound := operand, kind := .equ } ::
          { bound := arg, kind := .equ } :: Γ) (inner :: Stack.shift 0 rest) op op' →
        Term.Scoped (Ctx.depth ({ bound := operand, kind := .equ } ::
          { bound := arg, kind := .equ } :: Γ)) inner →
        MSubStar ({ bound := operand, kind := .equ } ::
          { bound := arg', kind := .equ } :: Γ) (inner :: Stack.shift 0 rest) op op')
    (hFOpFunBodyReplace :
      ∀ {operand : Term} {rest : Stack} {funBound body body' : Term},
        Term.Scoped (Ctx.depth ({ bound := arg, kind := .equ } :: Γ)) operand →
        Stack.shift 0 s = operand :: rest →
        MSubRed ({ bound := funBound, kind := .sub } ::
          { bound := operand, kind := .equ } ::
          { bound := arg, kind := .equ } :: Γ) [] body body' →
        MSubRed ({ bound := funBound, kind := .sub } ::
          { bound := operand, kind := .equ } ::
          { bound := arg', kind := .equ } :: Γ) [] body body')
    (hFOpBodyReplace :
      ∀ {operand : Term} {rest : Stack} {inner body body' : Term}
          {innerRest : Stack},
        Term.Scoped (Ctx.depth ({ bound := arg, kind := .equ } :: Γ)) operand →
        Stack.shift 0 s = operand :: rest →
        Term.Scoped (Ctx.depth ({ bound := operand, kind := .equ } ::
          { bound := arg, kind := .equ } :: Γ)) inner →
        Stack.shift 0 rest = inner :: innerRest →
        MSubRed ({ bound := inner, kind := .equ } ::
          { bound := operand, kind := .equ } ::
          { bound := arg, kind := .equ } :: Γ) (Stack.shift 0 innerRest) body body' →
        MSubStar ({ bound := inner, kind := .equ } ::
          { bound := operand, kind := .equ } ::
          { bound := arg', kind := .equ } :: Γ) (Stack.shift 0 innerRest) body body') :
    ∃ t₃,
      MEqRedStar Γ s (.app (.abs bound₁ body₁) arg) t₃ ∧
        MSubStar Γ s (.app (.abs bound₂ body₂) arg') t₃ := by
  have hArg'Scoped : Term.Scoped Γ.depth arg' := hEqArg.scoped_right
  exact commute_appAbs_structApp_eqStep_of_argument_stack_lifted_fOp_tail_lifts_from_left
    hcommArg hSubOp hEqOp hEqArg
    (meq_equ_head_stack_lift_function_from_replacements hArg'Scoped
      hArgProReplace hArgAppOpReplace hArgNilReplace hArgFunNilBodyReplace
      hArgFunConsBodyReplace hArgBetBodyReplace hEqArg)
    hEqSelfReplace hEqAppOpReplace hNilReplace hEqFunBodyReplace
    hEqBetBodyReplace hEqFOpSelfReplace hEqFOpAppOpReplace hEqFOpNilReplace
    hEqFOpFunBodyReplace hEqFOpBetBodyReplace hEqFOpBodyReplace hAppOpReplace
    hFunBodyReplace hFOpAppOpReplace hFOpFunBodyReplace hFOpBodyReplace

/-- Changed-argument structural application commutation where the shifted
old-to-new argument equivalence is produced from the argument step by the
changed-head stack-lift package. -/
theorem commute_appAbs_structApp_eqStep_of_lifted_shifted_fOp_replacements
    {Γ : Ctx} {s : Stack}
    {bound body arg bound₁ body₁ bound₂ body₂ arg' : Term}
    (hpvTail : PrevalidExt Γ s)
    (hcommArg : StrongCommutes Γ (arg :: s))
    (hSubOp : MSubRed Γ (arg :: s) (.abs bound body) (.abs bound₁ body₁))
    (hEqOp : MEqRed Γ (arg :: s) (.abs bound body) (.abs bound₂ body₂))
    (hEqArg : MEqRed Γ [] arg arg')
    (hArgProReplace :
      ∀ {α α' : Term},
        MEqRed Γ [] α α' →
        MEqRed ({ bound := arg', kind := .equ } :: Γ) (Stack.shift 0 s)
          (Term.shift 0 α) (Term.shift 0 α'))
    (hArgAppOpReplace :
      ∀ {op op' operand : Term},
        MEqRed Γ (operand :: []) op op' →
        MEqRed ({ bound := arg', kind := .equ } :: Γ)
          (Term.shift 0 operand :: Stack.shift 0 s)
          (Term.shift 0 op) (Term.shift 0 op'))
    (hArgNilReplace :
      ∀ {u v : Term},
        MEqRed Γ [] u v →
        MEqRed ({ bound := arg', kind := .equ } :: Γ) []
          (Term.shift 0 u) (Term.shift 0 v))
    (hArgFunNilBodyReplace :
      ∀ {funBound body body' : Term},
        MEqRed ({ bound := funBound, kind := .sub } :: Γ) [] body body' →
        MEqRed ({ bound := Term.shift 0 funBound, kind := .sub } ::
          { bound := arg', kind := .equ } :: Γ) []
          (Term.shift 1 body) (Term.shift 1 body'))
    (hArgFunConsBodyReplace :
      ∀ {operand funBound body body' : Term} {rest : Stack},
        Term.Scoped Γ.depth operand →
        MEqRed ({ bound := funBound, kind := .sub } :: Γ) [] body body' →
        MEqRed ({ bound := Term.shift 0 operand, kind := .equ } ::
          { bound := arg', kind := .equ } :: Γ)
          (Stack.shift 0 (Stack.shift 0 rest)) (Term.shift 1 body) (Term.shift 1 body'))
    (hArgBetBodyReplace :
      ∀ {funBound body body' : Term},
        MEqRed ({ bound := funBound, kind := .sub } :: Γ) (Stack.shift 0 [])
          body body' →
        MEqRed ({ bound := Term.shift 0 funBound, kind := .sub } ::
          { bound := arg', kind := .equ } :: Γ) (Stack.shift 0 (Stack.shift 0 s))
          (Term.shift 1 body) (Term.shift 1 body'))
    (hEqSelfReplace :
      ∀ {u v : Term},
        MEqRed ({ bound := arg, kind := .equ } :: Γ) (Stack.shift 0 s) u v →
        MSubStar ({ bound := arg', kind := .equ } :: Γ) (Stack.shift 0 s) u v)
    (hEqAppOpReplace :
      ∀ {op op' operand : Term},
        MEqRed ({ bound := arg, kind := .equ } :: Γ)
          (operand :: Stack.shift 0 s) op op' →
        MEqRed ({ bound := arg', kind := .equ } :: Γ)
          (operand :: Stack.shift 0 s) op op')
    (hNilReplace :
      ∀ {u v : Term},
        MEqRed ({ bound := arg, kind := .equ } :: Γ) [] u v →
        MEqRed ({ bound := arg', kind := .equ } :: Γ) [] u v)
    (hEqFunBodyReplace :
      ∀ {funBound body body' : Term},
        MEqRed ({ bound := funBound, kind := .sub } ::
          { bound := arg, kind := .equ } :: Γ) [] body body' →
        MEqRed ({ bound := funBound, kind := .sub } ::
          { bound := arg', kind := .equ } :: Γ) [] body body')
    (hEqBetBodyReplace :
      ∀ {funBound body body' : Term},
        MEqRed ({ bound := funBound, kind := .sub } ::
          { bound := arg, kind := .equ } :: Γ) (Stack.shift 0 (Stack.shift 0 s))
          body body' →
        MEqRed ({ bound := funBound, kind := .sub } ::
          { bound := arg', kind := .equ } :: Γ) (Stack.shift 0 (Stack.shift 0 s))
          body body')
    (hEqFOpBodyReplace :
      ∀ {operand body body' : Term} {rest : Stack},
        Term.Scoped (Ctx.depth ({ bound := arg, kind := .equ } :: Γ)) operand →
        Stack.shift 0 s = operand :: rest →
        MEqRed ({ bound := operand, kind := .equ } ::
          { bound := arg, kind := .equ } :: Γ) (Stack.shift 0 rest) body body' →
        MSubStar ({ bound := operand, kind := .equ } ::
          { bound := arg', kind := .equ } :: Γ) (Stack.shift 0 rest) body body')
    (hAppOpReplace :
      ∀ {op op' operand : Term},
        MSubRed ({ bound := arg, kind := .equ } :: Γ)
          (operand :: Stack.shift 0 s) op op' →
        Term.Scoped (Ctx.depth ({ bound := arg, kind := .equ } :: Γ)) operand →
        MSubStar ({ bound := arg', kind := .equ } :: Γ)
          (operand :: Stack.shift 0 s) op op')
    (hFunBodyReplace :
      ∀ {funBound body body' : Term},
        MSubRed ({ bound := funBound, kind := .sub } ::
          { bound := arg, kind := .equ } :: Γ) [] body body' →
        MSubRed ({ bound := funBound, kind := .sub } ::
          { bound := arg', kind := .equ } :: Γ) [] body body')
    (hFOpBodyReplace :
      ∀ {operand body body' : Term} {rest : Stack},
        Term.Scoped (Ctx.depth ({ bound := arg, kind := .equ } :: Γ)) operand →
        Stack.shift 0 s = operand :: rest →
        MSubRed ({ bound := operand, kind := .equ } ::
          { bound := arg, kind := .equ } :: Γ) (Stack.shift 0 rest) body body' →
        MSubStar ({ bound := operand, kind := .equ } ::
          { bound := arg', kind := .equ } :: Γ) (Stack.shift 0 rest) body body') :
    ∃ t₃,
      MEqRedStar Γ s (.app (.abs bound₁ body₁) arg) t₃ ∧
        MSubStar Γ s (.app (.abs bound₂ body₂) arg') t₃ := by
  have hArg'Scoped : Term.Scoped Γ.depth arg' := hEqArg.scoped_right
  exact commute_appAbs_structApp_eqStep_of_shifted_fOp_replacements_from_left
    hcommArg hSubOp hEqOp hEqArg
    (meq_equ_head_stack_lift_from_replacements hpvTail hArg'Scoped
      hArgProReplace hArgAppOpReplace hArgNilReplace hArgFunNilBodyReplace
      hArgFunConsBodyReplace hArgBetBodyReplace hEqArg)
    hEqSelfReplace hEqAppOpReplace hNilReplace hEqFunBodyReplace
    hEqBetBodyReplace hEqFOpBodyReplace hAppOpReplace hFunBodyReplace
    hFOpBodyReplace

/-- Side-condition-free wrapper for
`commute_appAbs_structApp_eqStep_of_lifted_shifted_fOp_replacements`: the tail
stack prevalidity is recovered from the operator subtype step. -/
theorem commute_appAbs_structApp_eqStep_of_lifted_shifted_fOp_replacements_from_left
    {Γ : Ctx} {s : Stack}
    {bound body arg bound₁ body₁ bound₂ body₂ arg' : Term}
    (hcommArg : StrongCommutes Γ (arg :: s))
    (hSubOp : MSubRed Γ (arg :: s) (.abs bound body) (.abs bound₁ body₁))
    (hEqOp : MEqRed Γ (arg :: s) (.abs bound body) (.abs bound₂ body₂))
    (hEqArg : MEqRed Γ [] arg arg')
    (hArgProReplace :
      ∀ {α α' : Term},
        MEqRed Γ [] α α' →
        MEqRed ({ bound := arg', kind := .equ } :: Γ) (Stack.shift 0 s)
          (Term.shift 0 α) (Term.shift 0 α'))
    (hArgAppOpReplace :
      ∀ {op op' operand : Term},
        MEqRed Γ (operand :: []) op op' →
        MEqRed ({ bound := arg', kind := .equ } :: Γ)
          (Term.shift 0 operand :: Stack.shift 0 s)
          (Term.shift 0 op) (Term.shift 0 op'))
    (hArgNilReplace :
      ∀ {u v : Term},
        MEqRed Γ [] u v →
        MEqRed ({ bound := arg', kind := .equ } :: Γ) []
          (Term.shift 0 u) (Term.shift 0 v))
    (hArgFunNilBodyReplace :
      ∀ {funBound body body' : Term},
        MEqRed ({ bound := funBound, kind := .sub } :: Γ) [] body body' →
        MEqRed ({ bound := Term.shift 0 funBound, kind := .sub } ::
          { bound := arg', kind := .equ } :: Γ) []
          (Term.shift 1 body) (Term.shift 1 body'))
    (hArgFunConsBodyReplace :
      ∀ {operand funBound body body' : Term} {rest : Stack},
        Term.Scoped Γ.depth operand →
        MEqRed ({ bound := funBound, kind := .sub } :: Γ) [] body body' →
        MEqRed ({ bound := Term.shift 0 operand, kind := .equ } ::
          { bound := arg', kind := .equ } :: Γ)
          (Stack.shift 0 (Stack.shift 0 rest)) (Term.shift 1 body) (Term.shift 1 body'))
    (hArgBetBodyReplace :
      ∀ {funBound body body' : Term},
        MEqRed ({ bound := funBound, kind := .sub } :: Γ) (Stack.shift 0 [])
          body body' →
        MEqRed ({ bound := Term.shift 0 funBound, kind := .sub } ::
          { bound := arg', kind := .equ } :: Γ) (Stack.shift 0 (Stack.shift 0 s))
          (Term.shift 1 body) (Term.shift 1 body'))
    (hEqSelfReplace :
      ∀ {u v : Term},
        MEqRed ({ bound := arg, kind := .equ } :: Γ) (Stack.shift 0 s) u v →
        MSubStar ({ bound := arg', kind := .equ } :: Γ) (Stack.shift 0 s) u v)
    (hEqAppOpReplace :
      ∀ {op op' operand : Term},
        MEqRed ({ bound := arg, kind := .equ } :: Γ)
          (operand :: Stack.shift 0 s) op op' →
        MEqRed ({ bound := arg', kind := .equ } :: Γ)
          (operand :: Stack.shift 0 s) op op')
    (hNilReplace :
      ∀ {u v : Term},
        MEqRed ({ bound := arg, kind := .equ } :: Γ) [] u v →
        MEqRed ({ bound := arg', kind := .equ } :: Γ) [] u v)
    (hEqFunBodyReplace :
      ∀ {funBound body body' : Term},
        MEqRed ({ bound := funBound, kind := .sub } ::
          { bound := arg, kind := .equ } :: Γ) [] body body' →
        MEqRed ({ bound := funBound, kind := .sub } ::
          { bound := arg', kind := .equ } :: Γ) [] body body')
    (hEqBetBodyReplace :
      ∀ {funBound body body' : Term},
        MEqRed ({ bound := funBound, kind := .sub } ::
          { bound := arg, kind := .equ } :: Γ) (Stack.shift 0 (Stack.shift 0 s))
          body body' →
        MEqRed ({ bound := funBound, kind := .sub } ::
          { bound := arg', kind := .equ } :: Γ) (Stack.shift 0 (Stack.shift 0 s))
          body body')
    (hEqFOpBodyReplace :
      ∀ {operand body body' : Term} {rest : Stack},
        Term.Scoped (Ctx.depth ({ bound := arg, kind := .equ } :: Γ)) operand →
        Stack.shift 0 s = operand :: rest →
        MEqRed ({ bound := operand, kind := .equ } ::
          { bound := arg, kind := .equ } :: Γ) (Stack.shift 0 rest) body body' →
        MSubStar ({ bound := operand, kind := .equ } ::
          { bound := arg', kind := .equ } :: Γ) (Stack.shift 0 rest) body body')
    (hAppOpReplace :
      ∀ {op op' operand : Term},
        MSubRed ({ bound := arg, kind := .equ } :: Γ)
          (operand :: Stack.shift 0 s) op op' →
        Term.Scoped (Ctx.depth ({ bound := arg, kind := .equ } :: Γ)) operand →
        MSubStar ({ bound := arg', kind := .equ } :: Γ)
          (operand :: Stack.shift 0 s) op op')
    (hFunBodyReplace :
      ∀ {funBound body body' : Term},
        MSubRed ({ bound := funBound, kind := .sub } ::
          { bound := arg, kind := .equ } :: Γ) [] body body' →
        MSubRed ({ bound := funBound, kind := .sub } ::
          { bound := arg', kind := .equ } :: Γ) [] body body')
    (hFOpBodyReplace :
      ∀ {operand body body' : Term} {rest : Stack},
        Term.Scoped (Ctx.depth ({ bound := arg, kind := .equ } :: Γ)) operand →
        Stack.shift 0 s = operand :: rest →
        MSubRed ({ bound := operand, kind := .equ } ::
          { bound := arg, kind := .equ } :: Γ) (Stack.shift 0 rest) body body' →
        MSubStar ({ bound := operand, kind := .equ } ::
          { bound := arg', kind := .equ } :: Γ) (Stack.shift 0 rest) body body') :
    ∃ t₃,
      MEqRedStar Γ s (.app (.abs bound₁ body₁) arg) t₃ ∧
        MSubStar Γ s (.app (.abs bound₂ body₂) arg') t₃ :=
  commute_appAbs_structApp_eqStep_of_lifted_shifted_fOp_replacements
    (PrevalidExt.tail hSubOp.prevalidExt) hcommArg hSubOp hEqOp hEqArg
    hArgProReplace hArgAppOpReplace hArgNilReplace hArgFunNilBodyReplace
    hArgFunConsBodyReplace hArgBetBodyReplace hEqSelfReplace hEqAppOpReplace
    hNilReplace hEqFunBodyReplace hEqBetBodyReplace hEqFOpBodyReplace
    hAppOpReplace hFunBodyReplace hFOpBodyReplace

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

/-- Type-valued chain form of de Bruijn Lemma 1 lifting. This reuses the
existing Prop-valued star commutation theorem and chooses Type-valued chain
witnesses for its two resulting closures. -/
noncomputable def commute_subChain_eqChain_of
    {Γ : Ctx} {s : Stack} (hcomm : StrongCommutes Γ s)
    {t₀ t₁ t₂ : Term}
    (hsubs : MSubRedChain Γ s t₀ t₁)
    (heqs : MEqRedChain Γ s t₀ t₂) :
    Sigma fun t₃ =>
      MEqRedChain Γ s t₁ t₃ × MSubRedChain Γ s t₂ t₃ := by
  let h := commute_subStar_eqStar_of hcomm hsubs.to_star heqs.to_star
  let t₃ := Classical.choose h
  have hSpec :
      MEqRedStar Γ s t₁ t₃ ∧ MSubRedStar Γ s t₂ t₃ :=
    Classical.choose_spec h
  exact ⟨t₃, MEqRedChain.of_star hSpec.1, MSubRedChain.of_star hSpec.2⟩

/-- Named de Bruijn Lemma 1 lifting in Type-valued chain form. -/
noncomputable def Lemma_1_DeBruijn_StrongCommutativityChain_of
    {Γ : Ctx} {s : Stack} (hcomm : StrongCommutes Γ s)
    {t₀ t₁ t₂ : Term}
    (hsubs : MSubRedChain Γ s t₀ t₁)
    (heqs : MEqRedChain Γ s t₀ t₂) :
    Sigma fun t₃ =>
      MEqRedChain Γ s t₁ t₃ × MSubRedChain Γ s t₂ t₃ :=
  commute_subChain_eqChain_of hcomm hsubs heqs

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

/-- Star-level fixed-bound `FOp` abstraction commutation. A body-level
de Bruijn Lemma-1 premise lifts subtype/equivalence chains under the operand
`.equ` head, then through the abstraction. -/
noncomputable def commute_abs_fOp_body_fixed_bound_star {Γ : Ctx} {s : Stack}
    {α bound body body₁ body₂ : Term}
    (hpvTail : PrevalidExt Γ s)
    (hBoundScoped : Term.Scoped Γ.depth bound)
    (hα : Term.Scoped Γ.depth α)
    (hcommBody : StrongCommutes ({ bound := α, kind := .equ } :: Γ)
      (Stack.shift 0 s))
    (hSubBody : MSubRedStar ({ bound := α, kind := .equ } :: Γ)
      (Stack.shift 0 s) body body₁)
    (hEqBody : MEqRedStar ({ bound := α, kind := .equ } :: Γ)
      (Stack.shift 0 s) body body₂) :
    ∃ t₃,
      MEqRedStar Γ (α :: s) (.abs bound body₁) t₃ ∧
        MSubRedStar Γ (α :: s) (.abs bound body₂) t₃ := by
  obtain ⟨body₃, hLeft, hRight⟩ :=
    commute_subStar_eqStar_of hcommBody hSubBody hEqBody
  exact ⟨.abs bound body₃,
    meqRedStar_abs_fOp_body_fixed_bound hpvTail hBoundScoped hα hLeft,
    msubRedStar_abs_fOp_body_fixed_bound hBoundScoped hα hRight⟩

/-- Star-level fixed-bound `Fun` abstraction commutation. A body-level
de Bruijn Lemma-1 premise lifts subtype/equivalence chains under the `.sub`
head, then through the abstraction. -/
noncomputable def commute_abs_fun_body_fixed_bound_star {Γ : Ctx}
    {bound body body₁ body₂ : Term}
    (hpvNil : PrevalidExt Γ [])
    (hBoundScoped : Term.Scoped Γ.depth bound)
    (hcommBody : StrongCommutes ({ bound := bound, kind := .sub } :: Γ) [])
    (hSubBody : MSubRedStar ({ bound := bound, kind := .sub } :: Γ) [] body body₁)
    (hEqBody : MEqRedStar ({ bound := bound, kind := .sub } :: Γ) [] body body₂) :
    ∃ t₃,
      MEqRedStar Γ [] (.abs bound body₁) t₃ ∧
        MSubRedStar Γ [] (.abs bound body₂) t₃ := by
  obtain ⟨body₃, hLeft, hRight⟩ :=
    commute_subStar_eqStar_of hcommBody hSubBody hEqBody
  exact ⟨.abs bound body₃,
    meqRedStar_abs_fun_body_fixed_bound hpvNil hBoundScoped hLeft,
    msubRedStar_abs_fun_body_fixed_bound hpvNil hBoundScoped hRight⟩

/-- Star-level fixed-body `FOp` abstraction commutation. Bound equivalence
chains lift through the equivalence side, while the subtype side is already at
the same fixed-body endpoint. -/
noncomputable def commute_abs_fOp_bound_fixed_body_star {Γ : Ctx} {s : Stack}
    {α bound bound₂ body : Term}
    (hpvTail : PrevalidExt Γ s)
    (hα : Term.Scoped Γ.depth α)
    (hBodyScoped : Term.Scoped
      (Ctx.depth ({ bound := α, kind := .equ } :: Γ)) body)
    (hEqBound : MEqRedStar Γ [] bound bound₂) :
    ∃ t₃,
      MEqRedStar Γ (α :: s) (.abs bound body) t₃ ∧
        MSubRedStar Γ (α :: s) (.abs bound₂ body) t₃ := by
  exact ⟨.abs bound₂ body,
    meqRedStar_abs_fOp_bound_fixed_body hpvTail hα hBodyScoped hEqBound,
    Relation.ReflTransGen.refl⟩

/-- Star-level fixed-body `Fun` abstraction commutation. Bound equivalence
chain diamonds supply a shared bound target, then both sides lift through the
abstraction with the body unchanged. -/
noncomputable def commute_abs_fun_bound_fixed_body_star {Γ : Ctx}
    {bound bound₁ bound₂ body : Term}
    (hpvNil : PrevalidExt Γ [])
    (hBodyScoped : Term.Scoped (Ctx.depth ({ bound := bound, kind := .sub } :: Γ)) body)
    (hdiamondBound : EqDiamonds Γ [])
    (hSubBound : MEqRedStar Γ [] bound bound₁)
    (hEqBound : MEqRedStar Γ [] bound bound₂) :
    ∃ t₃,
      MEqRedStar Γ [] (.abs bound₁ body) t₃ ∧
        MSubRedStar Γ [] (.abs bound₂ body) t₃ := by
  obtain ⟨bound₃, hLeft, hRight⟩ :=
    diamond_eqStar_eqStar_of hdiamondBound hSubBound hEqBound
  exact ⟨.abs bound₃ body,
    meqRedStar_abs_fun_bound_fixed_body hpvNil hBodyScoped hLeft,
    msubRedStar_abs_fun_bound_fixed_body hpvNil hBodyScoped hRight⟩

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

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

/-- Embed one diagrammatic step into the reflexive-transitive diagrammatic
relation. -/
theorem single {Γ : Ctx} {s : Stack} {u v : Term}
    (h : MSub Γ s u v) : MSubStar Γ s u v :=
  Relation.ReflTransGen.single h

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

/-- De Bruijn single-step strong commutativity at a fixed extended context.
This is the de Bruijn Lemma 1 shape needed by the star-lifting argument for
Theorem 3. The conclusion uses the Prop wrappers for single Type-valued
reduction steps. -/
abbrev StrongCommutes (Γ : Ctx) (s : Stack) : Prop :=
  ∀ {t₀ t₁ t₂ : Term},
    MSubRed Γ s t₀ t₁ →
    MEqRed Γ s t₀ t₂ →
    ∃ t₃, MEqRedJ Γ s t₁ t₃ ∧ MSubRedJ Γ s t₂ t₃

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

end WSubMStar

end DeBruijn
end Pss

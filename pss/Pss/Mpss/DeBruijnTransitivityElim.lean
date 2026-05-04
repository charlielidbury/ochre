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

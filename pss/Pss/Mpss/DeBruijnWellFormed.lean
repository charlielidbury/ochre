import Pss.Mpss.DeBruijnReductions

/-! # `Pss.Mpss.DeBruijnWellFormed` — de Bruijn MPSS well-formed judgments

This module seeds Phase 4 of the de Bruijn refactor. It mirrors the
well-formed, well-subtyping, transitive well-subtyping, well-equivalence, and
transitive well-equivalence judgments from `Pss.Mpss.WellFormed`, but uses raw
de Bruijn terms and nameless contexts.

The key simplification is the binder rule: the locally-nameless cofinite
premise is replaced by a single body derivation under the context extended by
the abstraction bound.
-/

namespace Pss
namespace DeBruijn

/-! ## Mutual well-formedness and well-subtyping judgments -/

mutual

/-- MPSS term well-formedness in de Bruijn form. -/
inductive WfM : Ctx → Term → Type where
  /-- **Wf-PrS**: a variable bound by `≤` is well-formed. -/
  | varSub {Γ : Ctx} {i : Nat} {t : Term} :
      Prevalid Γ → Γ.subBinds i t → WfM Γ (.bvar i)
  /-- **Wf-PrE**: a variable bound by `≡` is well-formed. -/
  | varEqu {Γ : Ctx} {i : Nat} {α : Term} :
      Prevalid Γ → Γ.equBinds i α → WfM Γ (.bvar i)
  /-- **Wf-Top**. -/
  | top {Γ : Ctx} :
      Prevalid Γ → WfM Γ .top
  /-- **Wf-Fun**: descend through the body under the nameless subtype head. -/
  | fun_ {Γ : Ctx} {t body : Term} :
      WfM Γ t →
      WfM ({ bound := t, kind := .sub } :: Γ) body →
      WfM Γ (.abs t body)
  /-- **Wf-App**. -/
  | app {Γ : Ctx} {u v t : Term} :
      WSubMStar Γ u (.abs t .top) →
      WSubMStar Γ v t →
      WfM Γ (.app u v)

/-- MPSS well-subtyping in de Bruijn form. -/
inductive WSubM : Ctx → Term → Term → Type where
  /-- **Ws-Rfl**. -/
  | rfl {Γ : Ctx} {t : Term} :
      WfM Γ t → WSubM Γ t t
  /-- **Ws-Lf1**: prepend an equivalence-reduction step on the left. -/
  | lf1 {Γ : Ctx} {v v' t : Term} :
      MEqRed Γ [] v v' →
      WSubM Γ v' t →
      WSubM Γ v t
  /-- **Ws-Lf2**: prepend a subtype-reduction step on the left. -/
  | lf2 {Γ : Ctx} {v v' t : Term} :
      WfM Γ v →
      MSubRed Γ [] v v' →
      WfM Γ v' →
      WSubM Γ v' t →
      WSubM Γ v t
  /-- **Ws-Rgh**: append an equivalence-reduction step on the right. -/
  | rgh {Γ : Ctx} {v t t' : Term} :
      WSubM Γ v t' →
      MEqRed Γ [] t t' →
      WSubM Γ v t

/-- MPSS transitive well-subtyping in de Bruijn form. -/
inductive WSubMStar : Ctx → Term → Term → Type where
  /-- **Ws-Sub**. -/
  | sub {Γ : Ctx} {v t : Term} :
      WfM Γ v → WSubM Γ v t → WfM Γ t →
      WSubMStar Γ v t
  /-- **Ws-Trs**. -/
  | trs {Γ : Ctx} {v u t : Term} :
      WSubMStar Γ v u → WfM Γ u → WSubMStar Γ u t →
      WSubMStar Γ v t

end

/-- Reflexive transitive well-subtyping for any well-formed term. -/
def WSubMStar.refl_of_wfM {Γ : Ctx} {t : Term} (h : WfM Γ t) :
    WSubMStar Γ t t :=
  WSubMStar.sub h (WSubM.rfl h) h

/-! ## Well-equivalence judgments -/

/-- MPSS well-equivalence in de Bruijn form. -/
inductive WEquM : Ctx → Term → Term → Type where
  /-- **Wse-Rfl**. -/
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

/-- MPSS transitive well-equivalence in de Bruijn form. -/
inductive WEquMStar : Ctx → Term → Term → Type where
  /-- **Wse-Sub**. -/
  | sub {Γ : Ctx} {v t : Term} :
      WfM Γ v → WEquM Γ v t → WfM Γ t →
      WEquMStar Γ v t
  /-- **Wse-Trs**. -/
  | trs {Γ : Ctx} {v u t : Term} :
      WEquMStar Γ v u → WfM Γ u → WEquMStar Γ u t →
      WEquMStar Γ v t

/-- Reflexive transitive well-equivalence for any well-formed term. -/
def WEquMStar.refl_of_wfM {Γ : Ctx} {t : Term} (h : WfM Γ t) :
    WEquMStar Γ t t :=
  WEquMStar.sub h (WEquM.rfl h) h

/-! ## Basic scoping invariants -/

/-- Combined scoping invariant for the three mutual judgments. -/
noncomputable def _scoped_combined :
    (∀ {Γ : Ctx} {t : Term}, WfM Γ t → Term.Scoped Γ.depth t) ×
    (∀ {Γ : Ctx} {v t : Term}, WSubM Γ v t →
      Term.Scoped Γ.depth v × Term.Scoped Γ.depth t) ×
    (∀ {Γ : Ctx} {v t : Term}, WSubMStar Γ v t →
      Term.Scoped Γ.depth v × Term.Scoped Γ.depth t) := by
  refine ⟨?wf, ?sub, ?star⟩
  · intro Γ t h
    exact (WfM.rec
      (motive_1 := fun Γ t _ => Term.Scoped Γ.depth t)
      (motive_2 := fun Γ v t _ => Term.Scoped Γ.depth v × Term.Scoped Γ.depth t)
      (motive_3 := fun Γ v t _ => Term.Scoped Γ.depth v × Term.Scoped Γ.depth t)
      (fun _ hb => Term.Scoped.bvar (Ctx.subBinds_lt hb))
      (fun _ hb => Term.Scoped.bvar (Ctx.equBinds_lt hb))
      (fun _ => Term.Scoped.top)
      (fun _ _ ihT ihBody => Term.Scoped.abs ihT ihBody)
      (fun _ _ ihU ihV => Term.Scoped.app ihU.1 ihV.1)
      (fun _ ih => ⟨ih, ih⟩)
      (fun hred _ ih => ⟨hred.scoped_left, ih.2⟩)
      (fun _ _ _ _ ihV _ ihSub => ⟨ihV, ihSub.2⟩)
      (fun _ hred ih => ⟨ih.1, hred.scoped_left⟩)
      (fun _ _ _ ihV _ ihT => ⟨ihV, ihT⟩)
      (fun _ _ _ ihLeft _ ihRight => ⟨ihLeft.1, ihRight.2⟩)
      h)
  · intro Γ v t h
    exact (WSubM.rec
      (motive_1 := fun Γ t _ => Term.Scoped Γ.depth t)
      (motive_2 := fun Γ v t _ => Term.Scoped Γ.depth v × Term.Scoped Γ.depth t)
      (motive_3 := fun Γ v t _ => Term.Scoped Γ.depth v × Term.Scoped Γ.depth t)
      (fun _ hb => Term.Scoped.bvar (Ctx.subBinds_lt hb))
      (fun _ hb => Term.Scoped.bvar (Ctx.equBinds_lt hb))
      (fun _ => Term.Scoped.top)
      (fun _ _ ihT ihBody => Term.Scoped.abs ihT ihBody)
      (fun _ _ ihU ihV => Term.Scoped.app ihU.1 ihV.1)
      (fun _ ih => ⟨ih, ih⟩)
      (fun hred _ ih => ⟨hred.scoped_left, ih.2⟩)
      (fun _ _ _ _ ihV _ ihSub => ⟨ihV, ihSub.2⟩)
      (fun _ hred ih => ⟨ih.1, hred.scoped_left⟩)
      (fun _ _ _ ihV _ ihT => ⟨ihV, ihT⟩)
      (fun _ _ _ ihLeft _ ihRight => ⟨ihLeft.1, ihRight.2⟩)
      h)
  · intro Γ v t h
    exact (WSubMStar.rec
      (motive_1 := fun Γ t _ => Term.Scoped Γ.depth t)
      (motive_2 := fun Γ v t _ => Term.Scoped Γ.depth v × Term.Scoped Γ.depth t)
      (motive_3 := fun Γ v t _ => Term.Scoped Γ.depth v × Term.Scoped Γ.depth t)
      (fun _ hb => Term.Scoped.bvar (Ctx.subBinds_lt hb))
      (fun _ hb => Term.Scoped.bvar (Ctx.equBinds_lt hb))
      (fun _ => Term.Scoped.top)
      (fun _ _ ihT ihBody => Term.Scoped.abs ihT ihBody)
      (fun _ _ ihU ihV => Term.Scoped.app ihU.1 ihV.1)
      (fun _ ih => ⟨ih, ih⟩)
      (fun hred _ ih => ⟨hred.scoped_left, ih.2⟩)
      (fun _ _ _ _ ihV _ ihSub => ⟨ihV, ihSub.2⟩)
      (fun _ hred ih => ⟨ih.1, hred.scoped_left⟩)
      (fun _ _ _ ihV _ ihT => ⟨ihV, ihT⟩)
      (fun _ _ _ ihLeft _ ihRight => ⟨ihLeft.1, ihRight.2⟩)
      h)

/-- A well-formed de Bruijn MPSS term is scoped in its context. -/
noncomputable def WfM.scoped {Γ : Ctx} {t : Term} (h : WfM Γ t) :
    Term.Scoped Γ.depth t :=
  _scoped_combined.1 h

/-- Well-subtyping relates scoped de Bruijn terms. -/
noncomputable def WSubM.scoped_pair {Γ : Ctx} {v t : Term} (h : WSubM Γ v t) :
    Term.Scoped Γ.depth v × Term.Scoped Γ.depth t :=
  _scoped_combined.2.1 h

/-- Left endpoint scoping for well-subtyping. -/
noncomputable def WSubM.scoped_left {Γ : Ctx} {v t : Term} (h : WSubM Γ v t) :
    Term.Scoped Γ.depth v :=
  h.scoped_pair.1

/-- Right endpoint scoping for well-subtyping. -/
noncomputable def WSubM.scoped_right {Γ : Ctx} {v t : Term} (h : WSubM Γ v t) :
    Term.Scoped Γ.depth t :=
  h.scoped_pair.2

/-- Transitive well-subtyping relates scoped de Bruijn terms. -/
noncomputable def WSubMStar.scoped_pair {Γ : Ctx} {v t : Term}
    (h : WSubMStar Γ v t) :
    Term.Scoped Γ.depth v × Term.Scoped Γ.depth t :=
  _scoped_combined.2.2 h

/-- Left endpoint scoping for transitive well-subtyping. -/
noncomputable def WSubMStar.scoped_left {Γ : Ctx} {v t : Term}
    (h : WSubMStar Γ v t) :
    Term.Scoped Γ.depth v :=
  h.scoped_pair.1

/-- Right endpoint scoping for transitive well-subtyping. -/
noncomputable def WSubMStar.scoped_right {Γ : Ctx} {v t : Term}
    (h : WSubMStar Γ v t) :
    Term.Scoped Γ.depth t :=
  h.scoped_pair.2

/-- Well-equivalence relates scoped de Bruijn terms. -/
noncomputable def WEquM.scoped_pair {Γ : Ctx} {v t : Term} (h : WEquM Γ v t) :
    Term.Scoped Γ.depth v × Term.Scoped Γ.depth t := by
  induction h with
  | rfl hwf =>
    exact ⟨hwf.scoped, hwf.scoped⟩
  | lf1 hred _ ih =>
    exact ⟨hred.scoped_left, ih.2⟩
  | rgh _ hred ih =>
    exact ⟨ih.1, hred.scoped_left⟩

/-- Left endpoint scoping for well-equivalence. -/
noncomputable def WEquM.scoped_left {Γ : Ctx} {v t : Term} (h : WEquM Γ v t) :
    Term.Scoped Γ.depth v :=
  h.scoped_pair.1

/-- Right endpoint scoping for well-equivalence. -/
noncomputable def WEquM.scoped_right {Γ : Ctx} {v t : Term} (h : WEquM Γ v t) :
    Term.Scoped Γ.depth t :=
  h.scoped_pair.2

/-- Transitive well-equivalence relates scoped de Bruijn terms. -/
noncomputable def WEquMStar.scoped_pair {Γ : Ctx} {v t : Term}
    (h : WEquMStar Γ v t) :
    Term.Scoped Γ.depth v × Term.Scoped Γ.depth t := by
  induction h with
  | sub hwfV _ hwfT =>
    exact ⟨hwfV.scoped, hwfT.scoped⟩
  | trs _ _ _ ihLeft ihRight =>
    exact ⟨ihLeft.1, ihRight.2⟩

/-- Left endpoint scoping for transitive well-equivalence. -/
noncomputable def WEquMStar.scoped_left {Γ : Ctx} {v t : Term}
    (h : WEquMStar Γ v t) :
    Term.Scoped Γ.depth v :=
  h.scoped_pair.1

/-- Right endpoint scoping for transitive well-equivalence. -/
noncomputable def WEquMStar.scoped_right {Γ : Ctx} {v t : Term}
    (h : WEquMStar Γ v t) :
    Term.Scoped Γ.depth t :=
  h.scoped_pair.2

/-! ## Basic well-equivalence helpers -/

/-- Symmetry of de Bruijn well-equivalence. -/
noncomputable def WEquM.symm {Γ : Ctx} {u v : Term} (h : WEquM Γ u v) :
    WEquM Γ v u := by
  induction h with
  | rfl hwf =>
    exact WEquM.rfl hwf
  | lf1 hred _ ih =>
    exact WEquM.rgh ih hred
  | rgh _ hred ih =>
    exact WEquM.lf1 hred ih

/-- De Bruijn well-equivalence embeds into de Bruijn well-subtyping. -/
noncomputable def WEquM.toWSubM {Γ : Ctx} {u v : Term} (h : WEquM Γ u v) :
    WSubM Γ u v := by
  induction h with
  | rfl hwf =>
    exact WSubM.rfl hwf
  | lf1 hred _ ih =>
    exact WSubM.lf1 hred ih
  | rgh _ hred ih =>
    exact WSubM.rgh ih hred

end DeBruijn
end Pss

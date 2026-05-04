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

/-! ## Context validity invariants -/

/-- Combined context-prevalidity invariant for the three mutual judgments. -/
noncomputable def _prevalid_combined :
    (∀ {Γ : Ctx} {t : Term}, WfM Γ t → Prevalid Γ) ×
    (∀ {Γ : Ctx} {v t : Term}, WSubM Γ v t → Prevalid Γ) ×
    (∀ {Γ : Ctx} {v t : Term}, WSubMStar Γ v t → Prevalid Γ) := by
  refine ⟨?wf, ?sub, ?star⟩
  · intro Γ t h
    exact (WfM.rec
      (motive_1 := fun Γ _ _ => Prevalid Γ)
      (motive_2 := fun Γ _ _ _ => Prevalid Γ)
      (motive_3 := fun Γ _ _ _ => Prevalid Γ)
      (fun hpv _ => hpv)
      (fun hpv _ => hpv)
      (fun hpv => hpv)
      (fun _ _ ihT _ => ihT)
      (fun _ _ ihU _ => ihU)
      (fun _ ih => ih)
      (fun _ _ ih => ih)
      (fun _ _ _ _ ihV _ _ => ihV)
      (fun _ _ ih => ih)
      (fun _ _ _ ihV _ _ => ihV)
      (fun _ _ _ ihLeft _ _ => ihLeft)
      h)
  · intro Γ v t h
    exact (WSubM.rec
      (motive_1 := fun Γ _ _ => Prevalid Γ)
      (motive_2 := fun Γ _ _ _ => Prevalid Γ)
      (motive_3 := fun Γ _ _ _ => Prevalid Γ)
      (fun hpv _ => hpv)
      (fun hpv _ => hpv)
      (fun hpv => hpv)
      (fun _ _ ihT _ => ihT)
      (fun _ _ ihU _ => ihU)
      (fun _ ih => ih)
      (fun _ _ ih => ih)
      (fun _ _ _ _ ihV _ _ => ihV)
      (fun _ _ ih => ih)
      (fun _ _ _ ihV _ _ => ihV)
      (fun _ _ _ ihLeft _ _ => ihLeft)
      h)
  · intro Γ v t h
    exact (WSubMStar.rec
      (motive_1 := fun Γ _ _ => Prevalid Γ)
      (motive_2 := fun Γ _ _ _ => Prevalid Γ)
      (motive_3 := fun Γ _ _ _ => Prevalid Γ)
      (fun hpv _ => hpv)
      (fun hpv _ => hpv)
      (fun hpv => hpv)
      (fun _ _ ihT _ => ihT)
      (fun _ _ ihU _ => ihU)
      (fun _ ih => ih)
      (fun _ _ ih => ih)
      (fun _ _ _ _ ihV _ _ => ihV)
      (fun _ _ ih => ih)
      (fun _ _ _ ihV _ _ => ihV)
      (fun _ _ _ ihLeft _ _ => ihLeft)
      h)

/-- Context prevalidity from de Bruijn well-formedness. -/
noncomputable def WfM.prevalid {Γ : Ctx} {t : Term} (h : WfM Γ t) :
    Prevalid Γ :=
  _prevalid_combined.1 h

/-- Context prevalidity from de Bruijn well-subtyping. -/
noncomputable def WSubM.prevalid {Γ : Ctx} {v t : Term} (h : WSubM Γ v t) :
    Prevalid Γ :=
  _prevalid_combined.2.1 h

/-- Context prevalidity from de Bruijn transitive well-subtyping. -/
noncomputable def WSubMStar.prevalid {Γ : Ctx} {v t : Term} (h : WSubMStar Γ v t) :
    Prevalid Γ :=
  _prevalid_combined.2.2 h

/-- Context prevalidity from de Bruijn well-equivalence. -/
noncomputable def WEquM.prevalid {Γ : Ctx} {v t : Term} (h : WEquM Γ v t) :
    Prevalid Γ := by
  induction h with
  | rfl hwf =>
    exact hwf.prevalid
  | lf1 _ _ ih =>
    exact ih
  | rgh _ _ ih =>
    exact ih

/-- Context prevalidity from de Bruijn transitive well-equivalence. -/
noncomputable def WEquMStar.prevalid {Γ : Ctx} {v t : Term} (h : WEquMStar Γ v t) :
    Prevalid Γ := by
  induction h with
  | sub hwfV _ _ =>
    exact hwfV.prevalid
  | trs _ _ _ ihLeft _ =>
    exact ihLeft

/-! ## Endpoint well-formedness extractors -/

/-- Left endpoint well-formedness from de Bruijn transitive well-subtyping. -/
noncomputable def WSubMStar.wf_left {Γ : Ctx} {v t : Term} (h : WSubMStar Γ v t) :
    WfM Γ v :=
  WSubMStar.rec
    (motive_1 := fun _ _ _ => PUnit)
    (motive_2 := fun _ _ _ _ => PUnit)
    (motive_3 := fun Γ v _ _ => WfM Γ v)
    (fun _ _ => PUnit.unit)
    (fun _ _ => PUnit.unit)
    (fun _ => PUnit.unit)
    (fun _ _ _ _ => PUnit.unit)
    (fun _ _ _ _ => PUnit.unit)
    (fun _ _ => PUnit.unit)
    (fun _ _ _ => PUnit.unit)
    (fun _ _ _ _ _ _ _ => PUnit.unit)
    (fun _ _ _ => PUnit.unit)
    (fun hwfV _ _ _ _ _ => hwfV)
    (fun _ _ _ ihLeft _ _ => ihLeft)
    h

/-- Right endpoint well-formedness from de Bruijn transitive well-subtyping. -/
noncomputable def WSubMStar.wf_right {Γ : Ctx} {v t : Term} (h : WSubMStar Γ v t) :
    WfM Γ t :=
  WSubMStar.rec
    (motive_1 := fun _ _ _ => PUnit)
    (motive_2 := fun _ _ _ _ => PUnit)
    (motive_3 := fun Γ _ t _ => WfM Γ t)
    (fun _ _ => PUnit.unit)
    (fun _ _ => PUnit.unit)
    (fun _ => PUnit.unit)
    (fun _ _ _ _ => PUnit.unit)
    (fun _ _ _ _ => PUnit.unit)
    (fun _ _ => PUnit.unit)
    (fun _ _ _ => PUnit.unit)
    (fun _ _ _ _ _ _ _ => PUnit.unit)
    (fun _ _ _ => PUnit.unit)
    (fun _ _ hwfT _ _ _ => hwfT)
    (fun _ _ _ _ _ ihRight => ihRight)
    h

/-- Left endpoint well-formedness from de Bruijn transitive well-equivalence. -/
noncomputable def WEquMStar.wf_left {Γ : Ctx} {v t : Term} (h : WEquMStar Γ v t) :
    WfM Γ v := by
  induction h with
  | sub hwfV _ _ =>
    exact hwfV
  | trs _ _ _ ihLeft _ =>
    exact ihLeft

/-- Right endpoint well-formedness from de Bruijn transitive well-equivalence. -/
noncomputable def WEquMStar.wf_right {Γ : Ctx} {v t : Term} (h : WEquMStar Γ v t) :
    WfM Γ t := by
  induction h with
  | sub _ _ hwfT =>
    exact hwfT
  | trs _ _ _ _ ihRight =>
    exact ihRight

/-! ## Insertion weakening -/

private def _InsertWfMotive (Γ : Ctx) (t : Term) (_ : WfM Γ t) : Type :=
  ∀ {cutoff : Nat} {newEntry : CtxEntry},
    cutoff ≤ Γ.depth →
    Prevalid (newEntry :: List.drop cutoff Γ) →
    Prevalid Γ →
    WfM (Ctx.insertAt cutoff newEntry Γ) (Term.shift cutoff t)

private def _InsertWSubMMotive (Γ : Ctx) (v t : Term) (_ : WSubM Γ v t) : Type :=
  ∀ {cutoff : Nat} {newEntry : CtxEntry},
    cutoff ≤ Γ.depth →
    Prevalid (newEntry :: List.drop cutoff Γ) →
    Prevalid Γ →
    WSubM (Ctx.insertAt cutoff newEntry Γ) (Term.shift cutoff v) (Term.shift cutoff t)

private def _InsertWSubMStarMotive (Γ : Ctx) (v t : Term)
    (_ : WSubMStar Γ v t) : Type :=
  ∀ {cutoff : Nat} {newEntry : CtxEntry},
    cutoff ≤ Γ.depth →
    Prevalid (newEntry :: List.drop cutoff Γ) →
    Prevalid Γ →
    WSubMStar (Ctx.insertAt cutoff newEntry Γ) (Term.shift cutoff v) (Term.shift cutoff t)

private noncomputable def _insertAt_varSub : ∀ {Γ : Ctx} {i : Nat} {t : Term}
    (hpv0 : Prevalid Γ) (hb : Γ.subBinds i t),
    _InsertWfMotive Γ (.bvar i) (WfM.varSub hpv0 hb) := by
  intro Γ i t hpv0 hb cutoff newEntry hcut hNew hpv
  rw [Ctx.shift_bvar_insertAtIndex]
  exact WfM.varSub (Prevalid.insertAt hcut hpv hNew) (Ctx.subBinds_insertAt hb)

private noncomputable def _insertAt_varEqu : ∀ {Γ : Ctx} {i : Nat} {α : Term}
    (hpv0 : Prevalid Γ) (hb : Γ.equBinds i α),
    _InsertWfMotive Γ (.bvar i) (WfM.varEqu hpv0 hb) := by
  intro Γ i α hpv0 hb cutoff newEntry hcut hNew hpv
  rw [Ctx.shift_bvar_insertAtIndex]
  exact WfM.varEqu (Prevalid.insertAt hcut hpv hNew) (Ctx.equBinds_insertAt hb)

private noncomputable def _insertAt_top : ∀ {Γ : Ctx} (hpv0 : Prevalid Γ),
    _InsertWfMotive Γ .top (WfM.top hpv0) := by
  intro Γ hpv0 cutoff newEntry hcut hNew hpv
  exact WfM.top (Prevalid.insertAt hcut hpv hNew)

private noncomputable def _insertAt_fun : ∀ {Γ : Ctx} {t body : Term}
    (hT : WfM Γ t)
    (hBody : WfM ({ bound := t, kind := .sub } :: Γ) body),
    _InsertWfMotive Γ t hT →
    _InsertWfMotive ({ bound := t, kind := .sub } :: Γ) body hBody →
    _InsertWfMotive Γ (.abs t body) (WfM.fun_ hT hBody) := by
  intro Γ t body hT hBody ihT ihBody cutoff newEntry hcut hNew hpv
  have hcutBody :
      cutoff + 1 ≤ Ctx.depth ({ bound := t, kind := .sub } :: Γ) := by
    simpa [Ctx.depth, Nat.add_comm] using Nat.succ_le_succ hcut
  have hNewBody :
      Prevalid (newEntry :: List.drop (cutoff + 1)
        ({ bound := t, kind := .sub } :: Γ)) := by
    simpa using hNew
  have hpvBody : Prevalid ({ bound := t, kind := .sub } :: Γ) :=
    Prevalid.sub hpv hT.scoped
  exact WfM.fun_ (ihT hcut hNew hpv) (by
    simpa using ihBody hcutBody hNewBody hpvBody)

private noncomputable def _insertAt_app : ∀ {Γ : Ctx} {u v t : Term}
    (hStarU : WSubMStar Γ u (.abs t .top))
    (hStarV : WSubMStar Γ v t),
    _InsertWSubMStarMotive Γ u (.abs t .top) hStarU →
    _InsertWSubMStarMotive Γ v t hStarV →
    _InsertWfMotive Γ (.app u v) (WfM.app hStarU hStarV) := by
  intro Γ u v t hStarU hStarV ihU ihV cutoff newEntry hcut hNew hpv
  exact WfM.app (by simpa using ihU hcut hNew hpv) (ihV hcut hNew hpv)

private noncomputable def _insertAt_rfl : ∀ {Γ : Ctx} {t : Term}
    (hwf : WfM Γ t),
    _InsertWfMotive Γ t hwf →
    _InsertWSubMMotive Γ t t (WSubM.rfl hwf) := by
  intro Γ t hwf ih cutoff newEntry hcut hNew hpv
  exact WSubM.rfl (ih hcut hNew hpv)

private noncomputable def _insertAt_lf1 : ∀ {Γ : Ctx} {v v' t : Term}
    (hred : MEqRed Γ [] v v')
    (hsub : WSubM Γ v' t),
    _InsertWSubMMotive Γ v' t hsub →
    _InsertWSubMMotive Γ v t (WSubM.lf1 hred hsub) := by
  intro Γ v v' t hred hsub ih cutoff newEntry hcut hNew hpv
  exact WSubM.lf1 (hred.insertAt hcut hNew (PrevalidExt.nil hpv))
    (ih hcut hNew hpv)

private noncomputable def _insertAt_lf2 : ∀ {Γ : Ctx} {v v' t : Term}
    (hwfV : WfM Γ v)
    (hred : MSubRed Γ [] v v')
    (hwfV' : WfM Γ v')
    (hsub : WSubM Γ v' t),
    _InsertWfMotive Γ v hwfV →
    _InsertWfMotive Γ v' hwfV' →
    _InsertWSubMMotive Γ v' t hsub →
    _InsertWSubMMotive Γ v t (WSubM.lf2 hwfV hred hwfV' hsub) := by
  intro Γ v v' t hwfV hred hwfV' hsub ihV ihV' ihSub cutoff newEntry hcut hNew hpv
  exact WSubM.lf2 (ihV hcut hNew hpv)
    (hred.insertAt hcut hNew (PrevalidExt.nil hpv))
    (ihV' hcut hNew hpv) (ihSub hcut hNew hpv)

private noncomputable def _insertAt_rgh : ∀ {Γ : Ctx} {v t t' : Term}
    (hsub : WSubM Γ v t')
    (hred : MEqRed Γ [] t t'),
    _InsertWSubMMotive Γ v t' hsub →
    _InsertWSubMMotive Γ v t (WSubM.rgh hsub hred) := by
  intro Γ v t t' hsub hred ih cutoff newEntry hcut hNew hpv
  exact WSubM.rgh (ih hcut hNew hpv)
    (hred.insertAt hcut hNew (PrevalidExt.nil hpv))

private noncomputable def _insertAt_sub : ∀ {Γ : Ctx} {v t : Term}
    (hwfV : WfM Γ v)
    (hsub : WSubM Γ v t)
    (hwfT : WfM Γ t),
    _InsertWfMotive Γ v hwfV →
    _InsertWSubMMotive Γ v t hsub →
    _InsertWfMotive Γ t hwfT →
    _InsertWSubMStarMotive Γ v t (WSubMStar.sub hwfV hsub hwfT) := by
  intro Γ v t hwfV hsub hwfT ihV ihSub ihT cutoff newEntry hcut hNew hpv
  exact WSubMStar.sub (ihV hcut hNew hpv) (ihSub hcut hNew hpv)
    (ihT hcut hNew hpv)

private noncomputable def _insertAt_trs : ∀ {Γ : Ctx} {v u t : Term}
    (hLeft : WSubMStar Γ v u)
    (hwfMid : WfM Γ u)
    (hRight : WSubMStar Γ u t),
    _InsertWSubMStarMotive Γ v u hLeft →
    _InsertWfMotive Γ u hwfMid →
    _InsertWSubMStarMotive Γ u t hRight →
    _InsertWSubMStarMotive Γ v t (WSubMStar.trs hLeft hwfMid hRight) := by
  intro Γ v u t hLeft hwfMid hRight ihLeft ihMid ihRight cutoff newEntry hcut hNew hpv
  exact WSubMStar.trs (ihLeft hcut hNew hpv) (ihMid hcut hNew hpv)
    (ihRight hcut hNew hpv)

/-- Combined insertion weakening for the three mutual well-formed judgments. -/
noncomputable def _insertAt_combined :
    (∀ {Γ : Ctx} {t : Term} (h : WfM Γ t), _InsertWfMotive Γ t h) ×
    (∀ {Γ : Ctx} {v t : Term} (h : WSubM Γ v t), _InsertWSubMMotive Γ v t h) ×
    (∀ {Γ : Ctx} {v t : Term} (h : WSubMStar Γ v t),
      _InsertWSubMStarMotive Γ v t h) := by
  refine ⟨?wf, ?sub, ?star⟩
  · intro Γ t h
    exact WfM.rec
      (motive_1 := _InsertWfMotive)
      (motive_2 := _InsertWSubMMotive)
      (motive_3 := _InsertWSubMStarMotive)
      @_insertAt_varSub @_insertAt_varEqu @_insertAt_top
      @_insertAt_fun @_insertAt_app
      @_insertAt_rfl @_insertAt_lf1 @_insertAt_lf2 @_insertAt_rgh
      @_insertAt_sub @_insertAt_trs
      h
  · intro Γ v t h
    exact WSubM.rec
      (motive_1 := _InsertWfMotive)
      (motive_2 := _InsertWSubMMotive)
      (motive_3 := _InsertWSubMStarMotive)
      @_insertAt_varSub @_insertAt_varEqu @_insertAt_top
      @_insertAt_fun @_insertAt_app
      @_insertAt_rfl @_insertAt_lf1 @_insertAt_lf2 @_insertAt_rgh
      @_insertAt_sub @_insertAt_trs
      h
  · intro Γ v t h
    exact WSubMStar.rec
      (motive_1 := _InsertWfMotive)
      (motive_2 := _InsertWSubMMotive)
      (motive_3 := _InsertWSubMStarMotive)
      @_insertAt_varSub @_insertAt_varEqu @_insertAt_top
      @_insertAt_fun @_insertAt_app
      @_insertAt_rfl @_insertAt_lf1 @_insertAt_lf2 @_insertAt_rgh
      @_insertAt_sub @_insertAt_trs
      h

/-- General insertion weakening for de Bruijn well-formedness. -/
noncomputable def WfM.insertAt {Γ : Ctx} {t : Term} (h : WfM Γ t)
    {cutoff : Nat} {newEntry : CtxEntry}
    (hcut : cutoff ≤ Γ.depth)
    (hNew : Prevalid (newEntry :: List.drop cutoff Γ))
    (hpv : Prevalid Γ) :
    WfM (Ctx.insertAt cutoff newEntry Γ) (Term.shift cutoff t) :=
  _insertAt_combined.1 h hcut hNew hpv

/-- General insertion weakening for de Bruijn well-subtyping. -/
noncomputable def WSubM.insertAt {Γ : Ctx} {v t : Term} (h : WSubM Γ v t)
    {cutoff : Nat} {newEntry : CtxEntry}
    (hcut : cutoff ≤ Γ.depth)
    (hNew : Prevalid (newEntry :: List.drop cutoff Γ))
    (hpv : Prevalid Γ) :
    WSubM (Ctx.insertAt cutoff newEntry Γ)
      (Term.shift cutoff v) (Term.shift cutoff t) :=
  _insertAt_combined.2.1 h hcut hNew hpv

/-- General insertion weakening for de Bruijn transitive well-subtyping. -/
noncomputable def WSubMStar.insertAt {Γ : Ctx} {v t : Term} (h : WSubMStar Γ v t)
    {cutoff : Nat} {newEntry : CtxEntry}
    (hcut : cutoff ≤ Γ.depth)
    (hNew : Prevalid (newEntry :: List.drop cutoff Γ))
    (hpv : Prevalid Γ) :
    WSubMStar (Ctx.insertAt cutoff newEntry Γ)
      (Term.shift cutoff v) (Term.shift cutoff t) :=
  _insertAt_combined.2.2 h hcut hNew hpv

/-- General insertion weakening for de Bruijn well-equivalence. -/
noncomputable def WEquM.insertAt {Γ : Ctx} {v t : Term} (h : WEquM Γ v t)
    {cutoff : Nat} {newEntry : CtxEntry}
    (hcut : cutoff ≤ Γ.depth)
    (hNew : Prevalid (newEntry :: List.drop cutoff Γ))
    (hpv : Prevalid Γ) :
    WEquM (Ctx.insertAt cutoff newEntry Γ)
      (Term.shift cutoff v) (Term.shift cutoff t) := by
  induction h with
  | rfl hwf =>
    exact WEquM.rfl (hwf.insertAt hcut hNew hpv)
  | lf1 hred _ ih =>
    exact WEquM.lf1 (hred.insertAt hcut hNew (PrevalidExt.nil hpv))
      ih
  | rgh _ hred ih =>
    exact WEquM.rgh ih
      (hred.insertAt hcut hNew (PrevalidExt.nil hpv))

/-- General insertion weakening for de Bruijn transitive well-equivalence. -/
noncomputable def WEquMStar.insertAt {Γ : Ctx} {v t : Term}
    (h : WEquMStar Γ v t) {cutoff : Nat} {newEntry : CtxEntry}
    (hcut : cutoff ≤ Γ.depth)
    (hNew : Prevalid (newEntry :: List.drop cutoff Γ))
    (hpv : Prevalid Γ) :
    WEquMStar (Ctx.insertAt cutoff newEntry Γ)
      (Term.shift cutoff v) (Term.shift cutoff t) := by
  induction h with
  | sub hwfV heq hwfT =>
    exact WEquMStar.sub (hwfV.insertAt hcut hNew hpv)
      (heq.insertAt hcut hNew hpv) (hwfT.insertAt hcut hNew hpv)
  | trs _ hwfMid _ ihLeft ihRight =>
    exact WEquMStar.trs ihLeft (hwfMid.insertAt hcut hNew hpv) ihRight

/-- General insertion weakening for de Bruijn well-formedness, deriving the
original context prevalidity from the judgment. -/
noncomputable def WfM.insertAt' {Γ : Ctx} {t : Term} (h : WfM Γ t)
    {cutoff : Nat} {newEntry : CtxEntry}
    (hcut : cutoff ≤ Γ.depth)
    (hNew : Prevalid (newEntry :: List.drop cutoff Γ)) :
    WfM (Ctx.insertAt cutoff newEntry Γ) (Term.shift cutoff t) :=
  h.insertAt hcut hNew h.prevalid

/-- General insertion weakening for de Bruijn well-subtyping, deriving the
original context prevalidity from the judgment. -/
noncomputable def WSubM.insertAt' {Γ : Ctx} {v t : Term} (h : WSubM Γ v t)
    {cutoff : Nat} {newEntry : CtxEntry}
    (hcut : cutoff ≤ Γ.depth)
    (hNew : Prevalid (newEntry :: List.drop cutoff Γ)) :
    WSubM (Ctx.insertAt cutoff newEntry Γ)
      (Term.shift cutoff v) (Term.shift cutoff t) :=
  h.insertAt hcut hNew h.prevalid

/-- General insertion weakening for de Bruijn transitive well-subtyping,
deriving the original context prevalidity from the judgment. -/
noncomputable def WSubMStar.insertAt' {Γ : Ctx} {v t : Term}
    (h : WSubMStar Γ v t) {cutoff : Nat} {newEntry : CtxEntry}
    (hcut : cutoff ≤ Γ.depth)
    (hNew : Prevalid (newEntry :: List.drop cutoff Γ)) :
    WSubMStar (Ctx.insertAt cutoff newEntry Γ)
      (Term.shift cutoff v) (Term.shift cutoff t) :=
  h.insertAt hcut hNew h.prevalid

/-- General insertion weakening for de Bruijn well-equivalence, deriving the
original context prevalidity from the judgment. -/
noncomputable def WEquM.insertAt' {Γ : Ctx} {v t : Term} (h : WEquM Γ v t)
    {cutoff : Nat} {newEntry : CtxEntry}
    (hcut : cutoff ≤ Γ.depth)
    (hNew : Prevalid (newEntry :: List.drop cutoff Γ)) :
    WEquM (Ctx.insertAt cutoff newEntry Γ)
      (Term.shift cutoff v) (Term.shift cutoff t) :=
  h.insertAt hcut hNew h.prevalid

/-- General insertion weakening for de Bruijn transitive well-equivalence,
deriving the original context prevalidity from the judgment. -/
noncomputable def WEquMStar.insertAt' {Γ : Ctx} {v t : Term}
    (h : WEquMStar Γ v t) {cutoff : Nat} {newEntry : CtxEntry}
    (hcut : cutoff ≤ Γ.depth)
    (hNew : Prevalid (newEntry :: List.drop cutoff Γ)) :
    WEquMStar (Ctx.insertAt cutoff newEntry Γ)
      (Term.shift cutoff v) (Term.shift cutoff t) :=
  h.insertAt hcut hNew h.prevalid

/-- Head-extension weakening for de Bruijn well-formedness. -/
noncomputable def WfM.weaken_head {Γ : Ctx} {t : Term} {newEntry : CtxEntry}
    (h : WfM Γ t)
    (hNew : Prevalid (newEntry :: Γ))
    (hpv : Prevalid Γ) :
    WfM (newEntry :: Γ) (Term.shift 0 t) := by
  simpa using h.insertAt (cutoff := 0) (newEntry := newEntry)
    (Nat.zero_le Γ.depth) hNew hpv

/-- Head-extension weakening for de Bruijn well-subtyping. -/
noncomputable def WSubM.weaken_head {Γ : Ctx} {v t : Term} {newEntry : CtxEntry}
    (h : WSubM Γ v t)
    (hNew : Prevalid (newEntry :: Γ))
    (hpv : Prevalid Γ) :
    WSubM (newEntry :: Γ) (Term.shift 0 v) (Term.shift 0 t) := by
  simpa using h.insertAt (cutoff := 0) (newEntry := newEntry)
    (Nat.zero_le Γ.depth) hNew hpv

/-- Head-extension weakening for de Bruijn transitive well-subtyping. -/
noncomputable def WSubMStar.weaken_head {Γ : Ctx} {v t : Term}
    {newEntry : CtxEntry}
    (h : WSubMStar Γ v t)
    (hNew : Prevalid (newEntry :: Γ))
    (hpv : Prevalid Γ) :
    WSubMStar (newEntry :: Γ) (Term.shift 0 v) (Term.shift 0 t) := by
  simpa using h.insertAt (cutoff := 0) (newEntry := newEntry)
    (Nat.zero_le Γ.depth) hNew hpv

/-- Head-extension weakening for de Bruijn well-equivalence. -/
noncomputable def WEquM.weaken_head {Γ : Ctx} {v t : Term} {newEntry : CtxEntry}
    (h : WEquM Γ v t)
    (hNew : Prevalid (newEntry :: Γ))
    (hpv : Prevalid Γ) :
    WEquM (newEntry :: Γ) (Term.shift 0 v) (Term.shift 0 t) := by
  simpa using h.insertAt (cutoff := 0) (newEntry := newEntry)
    (Nat.zero_le Γ.depth) hNew hpv

/-- Head-extension weakening for de Bruijn transitive well-equivalence. -/
noncomputable def WEquMStar.weaken_head {Γ : Ctx} {v t : Term}
    {newEntry : CtxEntry}
    (h : WEquMStar Γ v t)
    (hNew : Prevalid (newEntry :: Γ))
    (hpv : Prevalid Γ) :
    WEquMStar (newEntry :: Γ) (Term.shift 0 v) (Term.shift 0 t) := by
  simpa using h.insertAt (cutoff := 0) (newEntry := newEntry)
    (Nat.zero_le Γ.depth) hNew hpv

/-- Weakening under one existing head binder for de Bruijn well-formedness. -/
noncomputable def WfM.weaken_tail_head {Γ : Ctx} {t : Term}
    {head newHead : CtxEntry}
    (h : WfM (head :: Γ) t)
    (hNew : Prevalid (head.shift 0 :: newHead :: Γ))
    (hpv : Prevalid (head :: Γ)) :
    WfM (head.shift 0 :: newHead :: Γ) (Term.shift 1 t) := by
  simpa using h.insertAt (cutoff := 1) (newEntry := newHead)
    (by simp [Ctx.depth]) (Prevalid.tail hNew) hpv

/-- Weakening under one existing head binder for de Bruijn well-subtyping. -/
noncomputable def WSubM.weaken_tail_head {Γ : Ctx} {v t : Term}
    {head newHead : CtxEntry}
    (h : WSubM (head :: Γ) v t)
    (hNew : Prevalid (head.shift 0 :: newHead :: Γ))
    (hpv : Prevalid (head :: Γ)) :
    WSubM (head.shift 0 :: newHead :: Γ) (Term.shift 1 v) (Term.shift 1 t) := by
  simpa using h.insertAt (cutoff := 1) (newEntry := newHead)
    (by simp [Ctx.depth]) (Prevalid.tail hNew) hpv

/-- Weakening under one existing head binder for de Bruijn transitive
well-subtyping. -/
noncomputable def WSubMStar.weaken_tail_head {Γ : Ctx} {v t : Term}
    {head newHead : CtxEntry}
    (h : WSubMStar (head :: Γ) v t)
    (hNew : Prevalid (head.shift 0 :: newHead :: Γ))
    (hpv : Prevalid (head :: Γ)) :
    WSubMStar (head.shift 0 :: newHead :: Γ) (Term.shift 1 v) (Term.shift 1 t) := by
  simpa using h.insertAt (cutoff := 1) (newEntry := newHead)
    (by simp [Ctx.depth]) (Prevalid.tail hNew) hpv

/-- Weakening under one existing head binder for de Bruijn well-equivalence. -/
noncomputable def WEquM.weaken_tail_head {Γ : Ctx} {v t : Term}
    {head newHead : CtxEntry}
    (h : WEquM (head :: Γ) v t)
    (hNew : Prevalid (head.shift 0 :: newHead :: Γ))
    (hpv : Prevalid (head :: Γ)) :
    WEquM (head.shift 0 :: newHead :: Γ) (Term.shift 1 v) (Term.shift 1 t) := by
  simpa using h.insertAt (cutoff := 1) (newEntry := newHead)
    (by simp [Ctx.depth]) (Prevalid.tail hNew) hpv

/-- Weakening under one existing head binder for de Bruijn transitive
well-equivalence. -/
noncomputable def WEquMStar.weaken_tail_head {Γ : Ctx} {v t : Term}
    {head newHead : CtxEntry}
    (h : WEquMStar (head :: Γ) v t)
    (hNew : Prevalid (head.shift 0 :: newHead :: Γ))
    (hpv : Prevalid (head :: Γ)) :
    WEquMStar (head.shift 0 :: newHead :: Γ) (Term.shift 1 v) (Term.shift 1 t) := by
  simpa using h.insertAt (cutoff := 1) (newEntry := newHead)
    (by simp [Ctx.depth]) (Prevalid.tail hNew) hpv

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

/-! ## Chain helpers -/

/-- Compose two de Bruijn well-subtyping steps into transitive
well-subtyping. -/
def WSubMStar.WSubM_trans {Γ : Ctx} {a b c : Term}
    (hwfA : WfM Γ a) (hwfB : WfM Γ b) (hwfC : WfM Γ c)
    (h₁ : WSubM Γ a b) (h₂ : WSubM Γ b c) :
    WSubMStar Γ a c :=
  WSubMStar.trs (WSubMStar.sub hwfA h₁ hwfB) hwfB
    (WSubMStar.sub hwfB h₂ hwfC)

/-- Star-on-star transitivity of de Bruijn well-subtyping. -/
def WSubMStar.trans {Γ : Ctx} {a b c : Term}
    (hwfB : WfM Γ b)
    (h₁ : WSubMStar Γ a b) (h₂ : WSubMStar Γ b c) :
    WSubMStar Γ a c :=
  WSubMStar.trs h₁ hwfB h₂

private def _extendLeftWfMotive (Γ : Ctx) (t : Term) (_ : WfM Γ t) : Type :=
  Unit

private def _extendLeftWSubMMotive (Γ : Ctx) (a b : Term) (_ : WSubM Γ a b) : Type :=
  Unit

private def _extendLeftWSubMStarMotive (Γ : Ctx) (a b : Term)
    (_ : WSubMStar Γ a b) : Type :=
  ∀ {c : Term}, MEqRed Γ [] c a → WfM Γ c → WSubMStar Γ c b

/-- Prepend a forward equivalence-reduction step on the left of de Bruijn
transitive well-subtyping. -/
noncomputable def WSubMStar.extend_left_via_MEqRed_fwd
    {Γ : Ctx} {a b c : Term}
    (h : WSubMStar Γ a b)
    (hred : MEqRed Γ [] c a)
    (hwfC : WfM Γ c) :
    WSubMStar Γ c b := by
  exact (WSubMStar.rec
    (motive_1 := _extendLeftWfMotive)
    (motive_2 := _extendLeftWSubMMotive)
    (motive_3 := _extendLeftWSubMStarMotive)
    (fun _ _ => ())
    (fun _ _ => ())
    (fun _ => ())
    (fun _ _ _ _ => ())
    (fun _ _ _ _ => ())
    (fun _ _ => ())
    (fun _ _ _ => ())
    (fun _ _ _ _ _ _ _ => ())
    (fun _ _ _ => ())
    (fun _ hsub hwfT _ _ _ => fun hr hwfC =>
      WSubMStar.sub hwfC (WSubM.lf1 hr hsub) hwfT)
    (fun _ hwfU hRight ihLeft _ _ => fun hr hwfC =>
      WSubMStar.trs (ihLeft hr hwfC) hwfU hRight)
    h) hred hwfC

private def _extendRightWSubMStarMotive (Γ : Ctx) (a b : Term)
    (_ : WSubMStar Γ a b) : Type :=
  ∀ {c : Term}, MEqRed Γ [] c b → WfM Γ c → WSubMStar Γ a c

/-- Prepend a backward equivalence-reduction step on the right of de Bruijn
transitive well-subtyping. Given a forward step `c → b`, the result replaces
the right endpoint `b` by `c`. -/
noncomputable def WSubMStar.extend_right_via_MEqRed_back
    {Γ : Ctx} {a b c : Term}
    (h : WSubMStar Γ a b)
    (hred : MEqRed Γ [] c b)
    (hwfC : WfM Γ c) :
    WSubMStar Γ a c := by
  exact (WSubMStar.rec
    (motive_1 := _extendLeftWfMotive)
    (motive_2 := _extendLeftWSubMMotive)
    (motive_3 := _extendRightWSubMStarMotive)
    (fun _ _ => ())
    (fun _ _ => ())
    (fun _ => ())
    (fun _ _ _ _ => ())
    (fun _ _ _ _ => ())
    (fun _ _ => ())
    (fun _ _ _ => ())
    (fun _ _ _ _ _ _ _ => ())
    (fun _ _ _ => ())
    (fun hwfV hsub _ _ _ _ => fun hr hwfC =>
      WSubMStar.sub hwfV (WSubM.rgh hsub hr) hwfC)
    (fun hLeft hwfU _ _ _ ihRight => fun hr hwfC =>
      WSubMStar.trs hLeft hwfU (ihRight hr hwfC))
    h) hred hwfC

private def _extendLeftWEquMStarMotive (Γ : Ctx) (a b : Term)
    (_ : WEquMStar Γ a b) : Type :=
  ∀ {c : Term}, MEqRed Γ [] c a → WfM Γ c → WEquMStar Γ c b

/-- Prepend a forward equivalence-reduction step on the left of de Bruijn
transitive well-equivalence. -/
noncomputable def WEquMStar.extend_left_via_MEqRed_fwd
    {Γ : Ctx} {a b c : Term}
    (h : WEquMStar Γ a b)
    (hred : MEqRed Γ [] c a)
    (hwfC : WfM Γ c) :
    WEquMStar Γ c b := by
  exact (WEquMStar.rec
    (motive := _extendLeftWEquMStarMotive Γ)
    (fun _ heq hwfT => fun hr hwfC =>
      WEquMStar.sub hwfC (WEquM.lf1 hr heq) hwfT)
    (fun _ hwfU hRight ihLeft _ _ => fun hr hwfC =>
      WEquMStar.trs (ihLeft hr hwfC) hwfU hRight)
    h) hred hwfC

private def _extendRightWEquMStarMotive (Γ : Ctx) (a b : Term)
    (_ : WEquMStar Γ a b) : Type :=
  ∀ {c : Term}, MEqRed Γ [] c b → WfM Γ c → WEquMStar Γ a c

/-- Prepend a backward equivalence-reduction step on the right of de Bruijn
transitive well-equivalence. Given a forward step `c → b`, the result replaces
the right endpoint `b` by `c`. -/
noncomputable def WEquMStar.extend_right_via_MEqRed_back
    {Γ : Ctx} {a b c : Term}
    (h : WEquMStar Γ a b)
    (hred : MEqRed Γ [] c b)
    (hwfC : WfM Γ c) :
    WEquMStar Γ a c := by
  exact (WEquMStar.rec
    (motive := _extendRightWEquMStarMotive Γ)
    (fun hwfV heq _ => fun hr hwfC =>
      WEquMStar.sub hwfV (WEquM.rgh heq hr) hwfC)
    (fun hLeft hwfU _ _ ihRight => fun hr hwfC =>
      WEquMStar.trs hLeft hwfU (ihRight hr hwfC))
    h) hred hwfC

/-- Prepend an equivalence-reduction chain on the left of de Bruijn
well-subtyping. -/
noncomputable def WSubM.left_lf1_chain {Γ : Ctx} {a a' c : Term}
    (hChain : MEqRedStar Γ [] a a')
    (hSub : WSubM Γ a' c) :
    WSubM Γ a c := by
  suffices key : ∀ {x : Term} (h : MEqRedStar Γ [] x a'),
      Nonempty (WSubM Γ a' c → WSubM Γ x c) from (key hChain).some hSub
  intro x h
  refine Relation.ReflTransGen.head_induction_on (b := a')
    (P := fun x (_ : MEqRedStar Γ [] x a') =>
      Nonempty (WSubM Γ a' c → WSubM Γ x c)) h ?_ ?_
  · exact ⟨fun hSub' => hSub'⟩
  · intro x y hHead _ ihY
    exact ⟨fun hSubA' =>
      WSubM.lf1 hHead.some (ihY.some hSubA')⟩

/-- Append an equivalence-reduction chain on the right of de Bruijn
well-subtyping, reading the chain backward through `Ws-Rgh`. -/
noncomputable def WSubM.right_rgh_chain {Γ : Ctx} {a c c' : Term}
    (hSub : WSubM Γ a c')
    (hChain : MEqRedStar Γ [] c c') :
    WSubM Γ a c := by
  suffices key : ∀ {x : Term} (h : MEqRedStar Γ [] x c'),
      Nonempty (WSubM Γ a c' → WSubM Γ a x) from (key hChain).some hSub
  intro x h
  refine Relation.ReflTransGen.head_induction_on (b := c')
    (P := fun x (_ : MEqRedStar Γ [] x c') =>
      Nonempty (WSubM Γ a c' → WSubM Γ a x)) h ?_ ?_
  · exact ⟨fun hSub' => hSub'⟩
  · intro x y hHead _ ihY
    exact ⟨fun hSubC' =>
      WSubM.rgh (ihY.some hSubC') hHead.some⟩

/-- Prepend an equivalence-reduction chain on the left of de Bruijn
well-equivalence. -/
noncomputable def WEquM.left_chain {Γ : Ctx} {a a' c : Term}
    (hChain : MEqRedStar Γ [] a a')
    (hEqu : WEquM Γ a' c) :
    WEquM Γ a c := by
  suffices key : ∀ {x : Term} (h : MEqRedStar Γ [] x a'),
      Nonempty (WEquM Γ a' c → WEquM Γ x c) from (key hChain).some hEqu
  intro x h
  refine Relation.ReflTransGen.head_induction_on (b := a')
    (P := fun x (_ : MEqRedStar Γ [] x a') =>
      Nonempty (WEquM Γ a' c → WEquM Γ x c)) h ?_ ?_
  · exact ⟨fun hEqu' => hEqu'⟩
  · intro x y hHead _ ihY
    exact ⟨fun hEquA' =>
      WEquM.lf1 hHead.some (ihY.some hEquA')⟩

/-- Append an equivalence-reduction chain on the right of de Bruijn
well-equivalence, reading the chain backward through `Wse-Rgh`. -/
noncomputable def WEquM.right_chain_back {Γ : Ctx} {a c c' : Term}
    (hEqu : WEquM Γ a c')
    (hChain : MEqRedStar Γ [] c c') :
    WEquM Γ a c := by
  suffices key : ∀ {x : Term} (h : MEqRedStar Γ [] x c'),
      Nonempty (WEquM Γ a c' → WEquM Γ a x) from (key hChain).some hEqu
  intro x h
  refine Relation.ReflTransGen.head_induction_on (b := c')
    (P := fun x (_ : MEqRedStar Γ [] x c') =>
      Nonempty (WEquM Γ a c' → WEquM Γ a x)) h ?_ ?_
  · exact ⟨fun hEqu' => hEqu'⟩
  · intro x y hHead _ ihY
    exact ⟨fun hEquC' =>
      WEquM.rgh (ihY.some hEquC') hHead.some⟩

/-- Compose two de Bruijn well-equivalence steps into transitive
well-equivalence. -/
def WEquMStar.WEquM_trans {Γ : Ctx} {a b c : Term}
    (hwfA : WfM Γ a) (hwfB : WfM Γ b) (hwfC : WfM Γ c)
    (h₁ : WEquM Γ a b) (h₂ : WEquM Γ b c) :
    WEquMStar Γ a c :=
  WEquMStar.trs (WEquMStar.sub hwfA h₁ hwfB) hwfB
    (WEquMStar.sub hwfB h₂ hwfC)

/-- Star-on-star transitivity of de Bruijn well-equivalence. -/
def WEquMStar.trans {Γ : Ctx} {a b c : Term}
    (hwfB : WfM Γ b)
    (h₁ : WEquMStar Γ a b) (h₂ : WEquMStar Γ b c) :
    WEquMStar Γ a c :=
  WEquMStar.trs h₁ hwfB h₂

/-- Symmetry of de Bruijn transitive well-equivalence. -/
noncomputable def WEquMStar.symm {Γ : Ctx} {u v : Term} (h : WEquMStar Γ u v) :
    WEquMStar Γ v u := by
  induction h with
  | sub hwfU heq hwfV =>
    exact WEquMStar.sub hwfV heq.symm hwfU
  | trs _ hwfMid _ ihLeft ihRight =>
    exact WEquMStar.trs ihRight hwfMid ihLeft

/-- De Bruijn transitive well-equivalence embeds into de Bruijn transitive
well-subtyping. -/
noncomputable def WEquMStar.toWSubMStar {Γ : Ctx} {u v : Term}
    (h : WEquMStar Γ u v) :
    WSubMStar Γ u v := by
  induction h with
  | sub hwfU heq hwfV =>
    exact WSubMStar.sub hwfU heq.toWSubM hwfV
  | trs _ hwfMid _ ihLeft ihRight =>
    exact WSubMStar.trs ihLeft hwfMid ihRight

end DeBruijn
end Pss

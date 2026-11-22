import Ochr.Meaning.Steps.DataBox
import Ochr.Meaning.DataModel.CtorMem

/-!
# A data type with a field: what the data model gives `Box` (lead21, 2026-11-22; docs/31 D148)

A column with a declaration in the context assumes of the data model exactly what `Pre`'s `CtxS` carries: it covers
the declaration and is faithful to it (`CtxFaithful`). For `Box := MkBox(n : Nat)` faithfulness says the most it
says of any column so far: the field type is the reference's reading of the declared field type `Nat`
(`FieldsFaithful` at the one field; the run of `Nat` is defined, so it is not vacuous). From it:
- `shape_box`: the record of `Box` gives its field the shape of a `Nat` leaf;
- `mem_box`: the members of `Box` are exactly `MkBox(m)` for numbers `m` (`DataLib.mem_iff`);
- `datBox_mem`: each such tree is a member (`ctorR_mem`, with `RecordsFaithful.leafOk`).
An instance of the hypothesis: `dmLeafNat` (every record entry the `Nat` leaf), `dataModelBox_leafNat`.
-/

namespace Ochr.Meaning.Steps.Form.ColumnBox

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.Steps.Form

/-- The record of `Box` (no parameter). -/
def boxRec (dm : DataModel) : Rec := dm.recOf declBox []

/-- The meaning of the type `Box`. -/
def tyBoxM (dm : DataModel) : TyM := dm.tyR declBox (boxRec dm)

/-- The meaning of `MkBox(f)`. -/
def datBox (dm : DataModel) (f : Sem) : Sem := .dat "Box" (boxRec dm) 0 [f]

/-- **What a column with `Box` in its context assumes of the data model** (one named hypothesis): it covers `Box`
and is faithful to the declarations `[Box]` at the context `K`. -/
def DataModelBox (K : RunCtx) : Prop := K.dm.covers declBox ∧ CtxFaithful K

theorem fieldTerm_box : fieldTerm declBox 0 0 = some .nat := rfl

/-- **The field type is the reference's reading of `Nat`** (`FieldsFaithful`, at the one field). -/
theorem fieldTy_box {K : RunCtx} (hΓ : K.Γ = [declBox]) (hf : CtxFaithful K) :
    K.dm.fieldTyR declBox (boxRec K.dm) 0 0 [] = TyM.nat := by
  have h := (hf K.Δ (fun _ => .el0 Nat 0)).1 declBox (by rw [hΓ]; simp) [] 0 0 [] .nat rfl
    (fun j h => absurd h (Nat.not_lt_zero _)) (fun j h => absurd h (Nat.not_lt_zero _)) rfl fieldTerm_box
  have hrun := h (.ty TyM.nat, .plain (TyM.univ 1)) (teleFrame K.dm K.D declBox [] 0 []) (by
    show runT { K with Δ := K.Δ } (fun _ => .el0 Nat 0) noFuture false _ .nat _ = _
    rw [runT]; rfl)
  exact hrun.symm

theorem t0_nat_inj {B : Type} {c : Code0 B} (h : TyM.t0 B c = TyM.nat) : B = Nat ∧ HEq c Code0.nat := by
  unfold TyM.nat at h
  injection h with h1 h2
  exact ⟨h1, h2⟩

theorem pempty_ne_nat : PEmpty ≠ Nat := fun e => by
  have : Nonempty PEmpty := e ▸ ⟨0⟩
  exact this.elim (fun x => x.elim)

theorem tyR_ne_nat (dm : DataModel) (d : IndDecl) (r : Rec) : dm.tyR d r ≠ TyM.nat := by
  intro h
  unfold DataModel.tyR at h
  by_cases hs : (d.sort == 0) = true
  · rw [if_pos hs] at h
    unfold TyM.prop at h
    obtain ⟨hB, -⟩ := t0_nat_inj h
    have hsub : ∀ x y : PLift (Nonempty (dm.car d r)), x = y := fun x y => by cases x; cases y; rfl
    have : ∀ x y : Nat, x = y := hB ▸ hsub
    exact absurd (this 0 1) (by decide)
  · rw [if_neg hs] at h
    obtain ⟨hB, hc⟩ := t0_nat_inj h
    revert hc
    generalize dm.car d r = A at hB ⊢
    subst hB; intro hc; cases hc

/-- A shape whose type is `Nat` is the `Nat` leaf. -/
theorem shape_of_nat (dm : DataModel) (s : DataLib.Shape) (h : dm.shapeTy s = TyM.nat) : s = .leaf Nat .nat := by
  cases s with
  | leaf B c =>
    obtain ⟨rfl, hc⟩ := t0_nat_inj h
    cases hc; rfl
  | sub d r =>
    simp only [DataModel.shapeTy] at h
    by_cases hs : (d.sort == 0) = true
    · rw [if_pos hs] at h; exact absurd (t0_nat_inj h).1 pempty_ne_nat
    · rw [if_neg hs] at h; exact absurd h (tyR_ne_nat dm d r)
  | prf d r =>
    simp only [DataModel.shapeTy] at h
    by_cases hs : (d.sort == 0) = true
    · rw [if_pos hs] at h; exact absurd h (tyR_ne_nat dm d r)
    · rw [if_neg hs] at h; exact absurd (t0_nat_inj h).1 pempty_ne_nat

/-- **The record gives the field the shape of a `Nat` leaf.** -/
theorem shape_box {K : RunCtx} (hΓ : K.Γ = [declBox]) (hf : CtxFaithful K) :
    K.dm.sig.shape declBox (boxRec K.dm) 0 0 [] = .leaf Nat .nat :=
  shape_of_nat K.dm _ (by have h := fieldTy_box hΓ hf; unfold DataModel.fieldTyR at h; simpa using h)

/-- **The members of `Box` are exactly `MkBox(m)`**, at a record giving the field the `Nat` leaf. -/
theorem mem_box (dm : DataModel) (hsh : dm.sig.shape declBox (boxRec dm) 0 0 [] = .leaf Nat .nat) {v : Sem}
    (h : v ∈ₛ[dm.read] tyBoxM dm) : ∃ m : Nat, v = datBox dm (.el0 Nat m) := by
  unfold tyBoxM at h
  rw [DataModel.mem_tyR dm declBox (boxRec dm) rfl] at h
  obtain ⟨⟨c, hc⟩, fs, rfl, hf⟩ := (DataLib.mem_iff _ _ _ _).1 h
  have hc0 : c = 0 := by simp [declBox] at hc; omega
  subst hc0
  obtain ⟨f, fs', rfl, hf1, hf2⟩ := hf
  have : fs' = [] := hf2
  subst this
  have hsh' : dm.sig.shape declBox (boxRec dm) 0 0 [] = .leaf Nat .nat := hsh
  rw [hsh'] at hf1
  obtain ⟨m, rfl⟩ := hf1
  exact ⟨m, rfl⟩

/-- **Each `MkBox(m)` is a member of `Box`**, at a record giving the field the `Nat` leaf and keeping no data code as a
leaf (`RecLeafOk`). -/
theorem datBox_mem (dm : DataModel) (hsh : dm.sig.shape declBox (boxRec dm) 0 0 [] = .leaf Nat .nat)
    (hok : dm.RecLeafOk declBox (boxRec dm)) (m : Nat) : datBox dm (.el0 Nat m) ∈ₛ[dm.read] tyBoxM dm := by
  refine dm.ctorR_mem declBox (boxRec dm) 0 [.el0 Nat m] rfl (by decide) rfl (fun i f hi => ?_) hok
  rcases i with _ | i
  · simp only [List.getElem?_cons_zero, Option.some.injEq] at hi; subst hi
    unfold DataModel.fieldTyR
    simp only [List.take_zero, List.map_nil]
    rw [hsh]; exact ⟨m, rfl⟩
  · simp at hi

/-- The record kept by a model faithful to `[Box]` keeps no data code as a leaf at `Box`'s field. -/
theorem recLeafOk_box {K : RunCtx} (hΓ : K.Γ = [declBox]) (hf : CtxFaithful K) :
    K.dm.RecLeafOk declBox (boxRec K.dm) :=
  (hf K.Δ (fun _ => .el0 Nat 0)).2.2.leafOk declBox (by rw [hΓ]; simp) [] rfl (fun j h => absurd h (Nat.not_lt_zero _))

/-! ## An instance -/

/-- A data model whose every record entry is the `Nat` leaf, covering everything, reading every parameter type as
the error type. -/
def dmLeafNat : DataModel :=
  { covers := fun _ => True, recOf := fun _ _ _ => .leaf Nat .nat, paramTy := fun _ _ _ => TyM.err }

theorem fieldTerm_box_none {c i : Nat} (h : ¬ (c = 0 ∧ i = 0)) : fieldTerm declBox c i = none := by
  unfold fieldTerm
  rcases c with _ | c
  · rcases i with _ | i
    · exact absurd ⟨rfl, rfl⟩ h
    · simp [declBox]
  · simp [declBox]

/-- **`DataModelBox` has an instance** at every context whose declarations are `[Box]` and whose data model is
`dmLeafNat`. -/
theorem dataModelBox_leafNat {K : RunCtx} (hdm : K.dm = dmLeafNat) (hΓ : K.Γ = [declBox]) : DataModelBox K := by
  refine ⟨by rw [hdm]; trivial, fun Δ ρ => ⟨?_, ?_, ⟨?_, ?_, ?_, ?_⟩⟩⟩
  · intro d hd ps c i e FT hl _ _ he hft r s' hr
    simp only [hΓ, List.mem_singleton] at hd; subst hd
    by_cases hci : c = 0 ∧ i = 0
    · obtain ⟨rfl, rfl⟩ := hci
      rw [fieldTerm_box] at hft; cases hft
      have : ps = [] := List.eq_nil_of_length_eq_zero hl
      subst this
      have : e = [] := List.eq_nil_of_length_eq_zero he
      subst this
      have hr' : runT { K with Δ := Δ } ρ noFuture false _ .nat _ = some (r, s') := hr
      rw [runT] at hr'
      simp only [pure, Option.some.injEq, Prod.mk.injEq] at hr'
      obtain ⟨rfl, -⟩ := hr'
      show TyM.nat = K.dm.fieldTy declBox [] 0 0 []
      rw [hdm]; rfl
    · rw [fieldTerm_box_none hci] at hft; cases hft
  · intro d hd ps j hn PT _ _ hp
    simp only [hΓ, List.mem_singleton] at hd; subst hd
    simp [declBox] at hp
  · intro d hd ps j A c hl _ _ hps
    simp only [hΓ, List.mem_singleton] at hd; subst hd
    have : ps = [] := List.eq_nil_of_length_eq_zero (by rw [hl]; rfl)
    subst this; simp at hps
  · intro d hd ps j v A c _ _ hpt hmem
    rw [hdm] at hpt hmem
    exact absurd (hpt ▸ hmem) (DataModel.err_mem_false _ _)
  · intro d hd ps ps' hpt hl _
    have hps : ps = [] := by
      rcases ps with _ | ⟨a, ps⟩
      · rfl
      · have := hpt 0 (by simp); rw [hdm] at this; exact absurd this (DataModel.err_mem_false _ _)
    subst hps
    have : ps' = [] := List.eq_nil_of_length_eq_zero hl
    subst this; rfl
  · intro d hd ps _ _ c i e hc hi _
    rw [hdm]
    intro d' r' hdc
    simp [DataLib.uSig, dmLeafNat, Code0.dataCode?] at hdc

end Ochr.Meaning.Steps.Form.ColumnBox

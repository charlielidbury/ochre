import Ochr.Meaning.DataModel.Exists.RunLemmas

/-!
# Piece 3: what keys a record by small readings (proved parts)

The canonical record keys a field's type by the earlier index fields' SMALL readings, while the run
reads their full meanings. On typed earlier fields nothing is lost: two members of one level-0 type
with the same small reading are equal (`memTy_small_inj`), for every model, from the data library's
`mem_small_inj` at data codes over the model's carrier and the injectivity of a leaf's tag elsewhere.
-/

namespace Ochr.Meaning.DataModel.Exists.Piece3

open Ochr Ochr.Meaning Ochr.Meaning.DataLib

/-- **Two members of one level-0 type with the same small reading are equal.** -/
theorem memTy_small_inj (dm : DataModel) {A : Type} (c : Code0 A) {v w : Sem}
    (hv : v ∈ₛ[dm.read] .t0 A c) (hw : w ∈ₛ[dm.read] .t0 A c) (hs : v.small = w.small) : v = w := by
  obtain ⟨a, rfl⟩ := hv
  obtain ⟨b, rfl⟩ := hw
  cases c with
  | prop P => rfl
  | nat => simp only [Code0.enc, Sem.small, Small.el.injEq, heq_eq_eq, true_and] at hs; rw [hs]
  | unit => cases a; cases b; rfl
  | pi C t => simp only [Code0.enc, Sem.small, Small.el.injEq, heq_eq_eq, true_and] at hs; rw [hs]
  | err => exact a.elim
  | data d r =>
    show dm.readFn d r A a = dm.readFn d r A b
    change (dm.readFn d r A a).small = (dm.readFn d r A b).small at hs
    unfold DataModel.readFn at hs ⊢
    split
    · rename_i hB
      simp only [dif_pos hB] at hs
      exact DataLib.mem_small_inj dm.sig d r _ _
        ((DataLib.mem_iff_meanC dm.sig d r _).2 ⟨_, rfl⟩) ((DataLib.mem_iff_meanC dm.sig d r _).2 ⟨_, rfl⟩) hs
    · rename_i hB
      simp only [dif_neg hB, Sem.small, Small.el.injEq, heq_eq_eq, true_and] at hs
      rw [hs]

/-- Every field type is a level-0 code (a shape's type is a leaf's code, a data type's, a
proposition or the error type). -/
theorem fieldTy_t0 (dm : DataModel) (d : IndDecl) (ps : List Sem) (c i : Nat) (e : List Sem) :
    ∃ (A : Type) (cd : Code0 A), dm.fieldTy d ps c i e = .t0 A cd := by
  unfold DataModel.fieldTy DataModel.fieldTyR DataModel.shapeTy
  split
  · exact ⟨_, _, rfl⟩
  · split
    · exact ⟨_, _, rfl⟩
    · unfold DataModel.tyR; split <;> exact ⟨_, _, rfl⟩
  · split
    · unfold DataModel.tyR; split <;> exact ⟨_, _, rfl⟩
    · exact ⟨_, _, rfl⟩

/-- **Earlier fields typed at their field types, with equal small readings, are equal** (field by
field: each field's type is the same at equal earlier fields, so the members agree). A field type of
level 0 is a `.t0` code, which is what typed earlier fields are members of. -/
theorem fields_small_inj (dm : DataModel) (d : IndDecl) (ps : List Sem) (c : Nat) :
    ∀ (e e' : List Sem), FieldsTyped dm d ps c e → FieldsTyped dm d ps c e' → e.length = e'.length →
      e.map Sem.small = e'.map Sem.small → e = e' := by
  intro e e' he he' hl hs
  have key : ∀ n i (hi : i < e.length) (hi' : i < e'.length), i < n → e[i] = e'[i] := by
    intro n
    induction n with
    | zero => intro i _ _ h; omega
    | succ n ihn =>
      intro i hi hi' hin
      have htake : e.take i = e'.take i := by
        apply List.ext_getElem (by simp [hl])
        intro j hj hj'
        simp only [List.length_take] at hj
        simp only [List.getElem_take]
        exact ihn j (by omega) (by omega) (by omega)
      obtain ⟨A, cd, hT⟩ := fieldTy_t0 dm d ps c i (e.take i)
      have h1 := he i hi
      have h2 := he' i hi'
      rw [← htake, hT] at h2
      rw [hT] at h1
      have hsi : e[i].small = e'[i].small := by
        have := congrArg (·[i]?) hs
        simp [List.getElem?_map, hi, hi'] at this
        exact this
      exact memTy_small_inj dm cd h1 h2 hsi
  exact List.ext_getElem hl fun i hi hi' => key (i + 1) i hi hi' (by omega)

/-- A projected small reading, entry by entry: an index field's reading, `.other` elsewhere. -/
theorem projIdx_get (d : IndDecl) (c : Nat) (es : List Small) (j : Nat) :
    (projIdx d c es)[j]? = es[j]?.map (fun s => if (d.indexFields c).contains j then s else .other) := by
  simp [projIdx, List.getElem?_map, List.getElem?_zipIdx]
  rfl

theorem projIdx_take (d : IndDecl) (c : Nat) (es : List Small) (i : Nat) :
    projIdx d c (es.take i) = (projIdx d c es).take i := by
  apply List.ext_getElem?
  intro j
  rw [projIdx_get, List.getElem?_take, List.getElem?_take, projIdx_get]
  by_cases h : j < i <;> simp [h]

/-- **Typed earlier fields whose projected small readings agree agree at every index field**: an
index field's type reads only the index fields before it (the universal signature projects), so the
two are members of one type with one small reading. This is what lets a record keyed by projected
small readings follow the run at the index fields. -/
theorem index_fields_eq (dm : DataModel) (d : IndDecl) (ps : List Sem) (c : Nat) (e e' : List Sem)
    (he : FieldsTyped dm d ps c e) (he' : FieldsTyped dm d ps c e')
    (hp : projIdx d c (e.map Sem.small) = projIdx d c (e'.map Sem.small))
    (i : Nat) (hi : i < e.length) (hi' : i < e'.length) (hidx : (d.indexFields c).contains i = true) :
    e[i] = e'[i] := by
  have hT : dm.fieldTy d ps c i (e.take i) = dm.fieldTy d ps c i (e'.take i) := by
    unfold DataModel.fieldTy DataModel.fieldTyR
    congr 1
    show uShape d _ c i _ = uShape d _ c i _
    apply uShape_idx
    rw [List.map_take, List.map_take, projIdx_take, projIdx_take, hp]
  obtain ⟨A, cd, hA⟩ := fieldTy_t0 dm d ps c i (e.take i)
  have h1 := he i hi
  have h2 := he' i hi'
  rw [hA] at h1
  rw [← hT, hA] at h2
  have hs : e[i].small = e'[i].small := by
    have := congrArg (·[i]?) hp
    simp only [projIdx_get, List.getElem?_map, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hi',
      Option.map_some, hidx, if_true, Option.some.injEq] at this
    exact this
  exact memTy_small_inj dm cd h1 h2 hs

end Ochr.Meaning.DataModel.Exists.Piece3

import Ochr.Meaning.DataModel.Exists.Knot.TruthExists
import Ochr.Meaning.DataModel.Exists.Piece3

/-!
# Piece 6: records that read value parameters only small (exists9)

`RecordsFaithful.smallOnly` asks a declaration's record at a parameter list to be the record at any
list whose level-0 value parameters have the same small readings (the run's constructor clause solves a
value parameter to `ofSmall` of the small reading a record keeps, a junk tree with no name and no
record, and then reads the record there). The knot's records do not: its canonical frame binds a value
parameter that does not vary by its value, and a field type reading it strictly (`Eq(B, b, b)` for
`W (b : B)`, `B` a data type) fails at the junk tree (docs/34 §18.14). So the model's record is the
knot's at the CANONICAL parameters (`canonPs`): each value parameter that does not vary and has a
level-0 type is replaced by the member of its type with its small reading (`rebuildM`). On a list of
members this changes nothing (`canonPs_typed`, members of one level-0 type with one small reading are
equal, `Piece3.memTy_small_inj`); it maps a list and its small-reading variant to related lists
(`canonPs_small`); and it keeps the knot's parametricity (`canonPs_parAgree`) and the truth records'
monotonicity (`canonPs_propLe`), because it rebuilds only at parameters that do not vary, whose types
read only parameters that do not vary (`ParamTyLocalD`).
-/

namespace Ochr.Meaning.DataModel.Exists.Records

open Ochr Ochr.Meaning Ochr.Meaning.DataLib Ochr.Meaning.Canonical Ochr.Meaning.DataModel.Exists.Knot
open Classical

/-- Induction on a list from its end. -/
@[elab_as_elim]
theorem snoc_induction {motive : List Sem → Prop} (nil : motive [])
    (snoc : ∀ qs v, motive qs → motive (qs ++ [v])) (ps : List Sem) : motive ps := by
  rw [← List.reverse_reverse ps]
  generalize ps.reverse = rs
  induction rs with
  | nil => exact nil
  | cons v rs ih => rw [List.reverse_cons]; exact snoc _ _ ih

section
variable (dm : DataModel) (P : Nat → List Sem → TyM) (d : IndDecl)

/-- The member of `T` with the small reading `sm` (`err` when there is none). -/
noncomputable def rebuildM (T : TyM) (sm : Small) : Sem :=
  if h : ∃ v, v ∈ₛ[dm.read] T ∧ v.small = sm then h.choose else .err

/-- The canonical parameter after the canonical earlier ones `acc`. -/
noncomputable def canonStep (acc : List Sem) (v : Sem) : Sem :=
  if paramVaries d acc.length = false then
    match P acc.length acc with
    | .t0 A c => rebuildM dm (.t0 A c) v.small
    | _ => v
  else v

/-- **The canonical parameters.** -/
noncomputable def canonPs (ps : List Sem) : List Sem :=
  ps.foldl (fun acc v => acc ++ [canonStep dm P d acc v]) []

theorem canonPs_append (ps : List Sem) (v : Sem) :
    canonPs dm P d (ps ++ [v]) = canonPs dm P d ps ++ [canonStep dm P d (canonPs dm P d ps) v] := by
  simp [canonPs, List.foldl_append]

theorem canonPs_length (ps : List Sem) : (canonPs dm P d ps).length = ps.length := by
  induction ps using snoc_induction with
  | nil => rfl
  | snoc qs v ih => rw [canonPs_append]; simp [ih]

theorem canonPs_take (ps : List Sem) (j : Nat) : canonPs dm P d (ps.take j) = (canonPs dm P d ps).take j := by
  induction ps using snoc_induction generalizing j with
  | nil => simp [canonPs]
  | snoc qs v ih =>
    rw [canonPs_append]
    by_cases hj : j ≤ qs.length
    · rw [List.take_append_of_le_length hj, List.take_append_of_le_length (by rw [canonPs_length]; exact hj), ih]
    · have h1 : (qs ++ [v]).take j = qs ++ [v] := List.take_of_length_le (by simp; omega)
      have h2 : (canonPs dm P d qs ++ [canonStep dm P d (canonPs dm P d qs) v]).take j =
          canonPs dm P d qs ++ [canonStep dm P d (canonPs dm P d qs) v] :=
        List.take_of_length_le (by simp [canonPs_length]; omega)
      rw [h1, h2, canonPs_append]

/-- Position `j` of the canonical list: the step at the canonical prefix. -/
theorem canonPs_getElem (ps : List Sem) (j : Nat) (hj : j < ps.length) :
    (canonPs dm P d ps)[j]? = some (canonStep dm P d ((canonPs dm P d ps).take j) ps[j]) := by
  have e : ps.take (j + 1) = ps.take j ++ [ps[j]] := List.take_succ_eq_append_getElem hj
  have h := canonPs_take dm P d ps (j + 1)
  rw [e, canonPs_append, canonPs_take] at h
  have hl : ((canonPs dm P d ps).take (j + 1)).length = j + 1 := by
    simp [canonPs_length]; omega
  have := congrArg (·[j]?) h
  rw [List.getElem?_append_right (by simp [canonPs_length]; omega)] at this
  simp only [List.length_take, canonPs_length, Nat.min_eq_left (Nat.le_of_lt hj), Nat.sub_self,
    List.getElem?_cons_zero] at this
  rw [this, List.getElem?_take_of_lt (Nat.lt_succ_self j)]

/-- Members at the declared types (at the earlier parameters). -/
def Typed (ps : List Sem) : Prop := ∀ j (h : j < ps.length), ps[j] ∈ₛ[dm.read] P j (ps.take j)

/-- **On a list of members the canonical parameters are the parameters.** -/
theorem canonPs_typed (ps : List Sem) (h : Typed dm P ps) : canonPs dm P d ps = ps := by
  induction ps using snoc_induction with
  | nil => rfl
  | snoc qs v ih =>
    have hq : Typed dm P qs := fun j hj => by
      have := h j (by simp; omega)
      simp only [List.getElem_append_left hj] at this
      rwa [List.take_append_of_le_length (Nat.le_of_lt hj)] at this
    have hv : v ∈ₛ[dm.read] P qs.length qs := by
      have := h qs.length (by simp)
      simp only [List.getElem_append_right (Nat.le_refl _), Nat.sub_self, List.getElem_cons_zero] at this
      rwa [List.take_left' rfl] at this
    rw [canonPs_append, ih hq]
    congr 2
    unfold canonStep
    split
    · split
      · rename_i A c e
        rw [e] at hv
        have hex : ∃ w, w ∈ₛ[dm.read] TyM.t0 A c ∧ w.small = v.small := ⟨v, hv, rfl⟩
        unfold rebuildM
        rw [dif_pos hex]
        exact Piece3.memTy_small_inj dm c hex.choose_spec.1 hv hex.choose_spec.2
      · rfl
    · rfl

/-- The step at a parameter that does not vary, given its type. -/
noncomputable def stepAt (T : TyM) (v : Sem) : Sem :=
  match T with
  | .t0 A c => rebuildM dm (.t0 A c) v.small
  | _ => v

theorem canonStep_nonvary (acc : List Sem) (v : Sem) (h : paramVaries d acc.length = false) :
    canonStep dm P d acc v = stepAt dm (P acc.length acc) v := by
  unfold canonStep stepAt; rw [if_pos h]

theorem canonStep_vary (acc : List Sem) (v : Sem) (h : paramVaries d acc.length = true) :
    canonStep dm P d acc v = v := by
  unfold canonStep; rw [if_neg (by simp [h])]

/-- A varying parameter is kept. -/
theorem canonPs_vary (ps : List Sem) (j : Nat) (hj : j < ps.length) (hv : paramVaries d j = true) :
    (canonPs dm P d ps)[j]? = some ps[j] := by
  rw [canonPs_getElem dm P d ps j hj, canonStep_vary]
  simpa [canonPs_length, Nat.min_eq_left (Nat.le_of_lt hj)] using hv

/-- The parameter types are local in the varying parameters (`ParamTyLocalD`, for a function). -/
def LocalP : Prop :=
  ∀ (j : Nat) (ps ps' : List Sem), ps.length = j → ps'.length = j → paramVaries d j = false →
    (∀ u, u < j → paramVaries d u = false → ps[u]? = ps'[u]?) → P j ps = P j ps'

/-- **Two lists whose steps agree at each parameter that does not vary have canonical forms equal
there.** -/
theorem canonPs_agree (hP : LocalP P d) (ps ps' : List Sem) (hl : ps.length = ps'.length)
    (hstep : ∀ j (hj : j < ps.length) (hj' : j < ps'.length), paramVaries d j = false →
      stepAt dm (P j ((canonPs dm P d ps).take j)) ps[j] = stepAt dm (P j ((canonPs dm P d ps).take j)) ps'[j]) :
    ∀ j, paramVaries d j = false → (canonPs dm P d ps)[j]? = (canonPs dm P d ps')[j]? := by
  intro j
  induction j using Nat.strongRecOn with
  | ind j ih =>
    intro hv
    by_cases hj : j < ps.length
    · have hj' : j < ps'.length := hl ▸ hj
      have hlen : ((canonPs dm P d ps).take j).length = j := by simp [canonPs_length]; omega
      have hlen' : ((canonPs dm P d ps').take j).length = j := by simp [canonPs_length]; omega
      rw [canonPs_getElem dm P d ps j hj, canonPs_getElem dm P d ps' j hj',
        canonStep_nonvary dm P d _ _ (by rw [hlen]; exact hv), canonStep_nonvary dm P d _ _ (by rw [hlen']; exact hv),
        hlen, hlen']
      have hPe : P j ((canonPs dm P d ps).take j) = P j ((canonPs dm P d ps').take j) := by
        apply hP j _ _ hlen hlen' hv
        intro u hu hvu
        rw [List.getElem?_take, List.getElem?_take, if_pos hu, if_pos hu]
        exact ih u hu hvu
      rw [← hPe, hstep j hj hj' hv]
    · have h1 : (canonPs dm P d ps)[j]? = none := by
        rw [List.getElem?_eq_none_iff, canonPs_length]; omega
      have h2 : (canonPs dm P d ps')[j]? = none := by
        rw [List.getElem?_eq_none_iff, canonPs_length]; omega
      rw [h1, h2]

/-- **Parametricity is kept** (what `knot_exists`' `hpar` reads of an earlier declaration): lists
agreeing below `n` at the nestable parameters and equal elsewhere have canonical forms that do. -/
theorem canonPs_parAgree (hP : LocalP P d) {n : Nat} {ps ps' : List Sem}
    (h : ParAgree (fun j => d.nestable.getD j false) n ps ps') :
    ParAgree (fun j => d.nestable.getD j false) n (canonPs dm P d ps) (canonPs dm P d ps') := by
  have hnv : ∀ j (hj : j < ps.length) (hj' : j < ps'.length), paramVaries d j = false → ps[j] = ps'[j] := by
    intro j hj hj' hv
    have := h.2 j ps[j] ps'[j] (List.getElem?_eq_getElem hj) (List.getElem?_eq_getElem hj')
    have hN : d.nestable.getD j false = false := (paramVaries_false hv).1
    simp only [List.getD_eq_getElem?_getD] at hN
    simpa [hN] using this
  have hag := canonPs_agree dm P d hP ps ps' h.1 (fun j hj hj' hv => by rw [hnv j hj hj' hv])
  refine ⟨by rw [canonPs_length, canonPs_length]; exact h.1, fun j v v' e e' => ?_⟩
  by_cases hv : paramVaries d j = false
  · have := hag j hv
    rw [e, e'] at this
    cases this
    have hN := (paramVaries_false hv).1
    simp only [hN, Bool.false_eq_true, if_false]
  · have hv' : paramVaries d j = true := by simpa using hv
    have hj : j < ps.length := by
      have := (List.getElem?_eq_some_iff.1 e).1; rwa [canonPs_length] at this
    have hj' : j < ps'.length := by
      have := (List.getElem?_eq_some_iff.1 e').1; rwa [canonPs_length] at this
    rw [canonPs_vary dm P d ps j hj hv'] at e
    rw [canonPs_vary dm P d ps' j hj' hv'] at e'
    cases e; cases e'
    exact h.2 j _ _ (List.getElem?_eq_getElem hj) (List.getElem?_eq_getElem hj')

/-- **Monotonicity is kept** (what `truth_exists`' `hmono` reads of an earlier declaration). -/
theorem canonPs_propLe (hP : LocalP P d) {ps ps' : List Sem} (h : PropLe d ps ps') :
    PropLe d (canonPs dm P d ps) (canonPs dm P d ps') := by
  have hnv : ∀ j (hj : j < ps.length) (hj' : j < ps'.length), paramVaries d j = false → ps[j] = ps'[j] := by
    intro j hj hj' hv
    rcases h.2 j ps[j] ps'[j] (List.getElem?_eq_getElem hj) (List.getElem?_eq_getElem hj') with e | ⟨hN, _⟩
    · exact e.symm
    · have := (paramVaries_false hv).1; rw [this] at hN; cases hN
  have hag := canonPs_agree dm P d hP ps ps' h.1.symm (fun j hj hj' hv => by rw [hnv j hj hj' hv])
  refine ⟨by rw [canonPs_length, canonPs_length]; exact h.1, fun j v v' e e' => ?_⟩
  by_cases hv : paramVaries d j = false
  · have := hag j hv
    rw [e, e'] at this
    cases this
    exact .inl rfl
  · have hv' : paramVaries d j = true := by simpa using hv
    have hj : j < ps.length := by
      have := (List.getElem?_eq_some_iff.1 e).1; rwa [canonPs_length] at this
    have hj' : j < ps'.length := by
      have := (List.getElem?_eq_some_iff.1 e').1; rwa [canonPs_length] at this
    rw [canonPs_vary dm P d ps j hj hv'] at e
    rw [canonPs_vary dm P d ps' j hj' hv'] at e'
    cases e; cases e'
    exact h.2 j _ _ (List.getElem?_eq_getElem hj) (List.getElem?_eq_getElem hj')

/-- **A list and its small-reading variant** (`RecordsFaithful.smallOnly`'s hypothesis): the variant's
canonical form equals the members at every parameter that does not vary, and differs at a varying one
only by a value of the same small reading, where the member has a level-0 type. -/
theorem canonPs_small (hP : LocalP P d) {ps ps' : List Sem} (ht : Typed dm P ps) (hl : ps'.length = ps.length)
    (h : ∀ (j : Nat) (v v' : Sem), ps[j]? = some v → ps'[j]? = some v' →
      v' = v ∨ ((∃ (A : Type) (c : Code0 A), P j (ps.take j) = .t0 A c ∧ v ∈ₛ[dm.read] .t0 A c) ∧ v'.small = v.small)) :
    (canonPs dm P d ps').length = ps.length ∧ ∀ j v v', ps[j]? = some v → (canonPs dm P d ps')[j]? = some v' →
      v' = v ∨ (paramVaries d j = true ∧ (∃ (A : Type) (c : Code0 A), P j (ps.take j) = .t0 A c ∧ v ∈ₛ[dm.read] .t0 A c) ∧
        v'.small = v.small) := by
  have hc := canonPs_typed dm P d ps ht
  have hag := canonPs_agree dm P d hP ps ps' hl.symm (by
    intro j hj hj' hv
    rw [hc]
    rcases h j ps[j] ps'[j] (List.getElem?_eq_getElem hj) (List.getElem?_eq_getElem hj') with e | ⟨⟨A, c, hT, hm⟩, hs⟩
    · rw [e]
    · unfold stepAt; rw [hT]; dsimp only; rw [hs])
  refine ⟨by rw [canonPs_length, hl], fun j v v' e e' => ?_⟩
  by_cases hv : paramVaries d j = false
  · have := hag j hv
    rw [hc, e, e'] at this
    cases this
    exact .inl rfl
  · have hv' : paramVaries d j = true := by simpa using hv
    have hj' : j < ps'.length := by
      have := (List.getElem?_eq_some_iff.1 e').1; rwa [canonPs_length] at this
    rw [canonPs_vary dm P d ps' j hj' hv'] at e'
    cases e'
    rcases h j v ps'[j] e (List.getElem?_eq_getElem hj') with e2 | ⟨hT, hs⟩
    · exact .inl e2
    · exact .inr ⟨hv', hT, hs⟩

end

end Ochr.Meaning.DataModel.Exists.Records

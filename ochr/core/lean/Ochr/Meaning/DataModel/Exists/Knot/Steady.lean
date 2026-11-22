import Ochr.Meaning.DataModel.Exists.Knot.Agree
import Ochr.Meaning.DataModel.Exists.Knot.Congr
import Ochr.Meaning.DataModel.Exists.Knot.Swap
import Ochr.Meaning.Strict.Good

/-!
# The knot, part 6: the steady nodes (exists6)

`SteadyAt` for the knot's own records (`steadyAt_knotK`): the run of a steady node of a field type
(an equation, a call, a value argument: `Steady`, it avoids `d` and reads no varying variable) in the
actual frame (`teleFrame` at the knot's model) gives its value at the canonical frame (`canFrame`)
under the earlier model. Three steps:
1. the two frames are one-frame states whose binding lists are equal off a set `X` of indices (the
   earlier fields that vary or are no index, the parameters that vary), each binding at `X` holding a
   whole member of its type in both (`Good`), with the same declared reading;
2. frame locality between them (`Knot.runT_stateOf_swap`, assuming `DecLocal` and label-free
   globals): the term reads no binding at `X`, so its run in the canonical frame is its run in the
   actual one;
3. the model congruence (`Knot.runT_congrR`): the term avoids `d`, so its run under the knot's model
   is its run under the earlier one.
-/

namespace Ochr.Meaning.DataModel.Exists.Knot

open Ochr Ochr.Meaning Ochr.Meaning.DataLib Ochr.Meaning.Canonical
open Classical

/-! ## The two frames' binding lists -/

/-- The actual frame's bindings (`teleFrame`'s). -/
noncomputable def bindsA (dm : DataModel) (D : Decisions) (d : IndDecl) (ps : List Sem) (c : Nat) (e : List Sem) :
    List SBinding :=
  (e ++ List.replicate (arity d c - e.length) Sem.moved).zipIdx.map (fun vi =>
      faithBind (if vi.2 < e.length then dm.fieldTy d ps c vi.2 (e.take vi.2) else TyM.err) vi.1
      (if vi.2 < e.length && fieldProof D d c vi.2 then .prop else .other)) ++
    ps.zipIdx.map (fun vj => faithBind (dm.paramTy d vj.2 (ps.take vj.2)) vj.1 ((paramDecls D d (arity d c)).getD vj.2 .other))

theorem teleFrame_bindsA (dm : DataModel) (D : Decisions) (d : IndDecl) (ps : List Sem) (c : Nat) (e : List Sem) :
    teleFrame dm D d ps c e = stateOf 0 (bindsA dm D d ps c e) := rfl

theorem bindsA_length (dm : DataModel) (D : Decisions) (d : IndDecl) (ps : List Sem) (c : Nat) (e : List Sem)
    (he : e.length ≤ arity d c) : (bindsA dm D d ps c e).length = arity d c + ps.length := by
  simp [bindsA]; omega

theorem bindsA_early (dm : DataModel) (D : Decisions) (d : IndDecl) (ps : List Sem) (c : Nat) (e : List Sem)
    {p : Nat} (hp : p < e.length) (he : e.length ≤ arity d c) :
    (bindsA dm D d ps c e)[p]? = some (faithBind (dm.fieldTy d ps c p (e.take p)) e[p]
      (if fieldProof D d c p then .prop else .other)) := by
  unfold bindsA
  rw [List.getElem?_append_left (by simp; omega)]
  simp [List.getElem?_map, List.getElem?_zipIdx, List.getElem?_append_left hp, hp]

theorem bindsA_late (dm : DataModel) (D : Decisions) (d : IndDecl) (ps : List Sem) (c : Nat) (e : List Sem)
    {p : Nat} (hp : e.length ≤ p) (hpk : p < arity d c) :
    (bindsA dm D d ps c e)[p]? = some (faithBind TyM.err .moved .other) := by
  unfold bindsA
  rw [List.getElem?_append_left (by simp; omega)]
  have h1 : ¬ p < e.length := by omega
  simp [List.getElem?_map, List.getElem?_zipIdx, List.getElem?_append_right hp, h1, List.getElem?_replicate]
  omega

theorem bindsA_param (dm : DataModel) (D : Decisions) (d : IndDecl) (ps : List Sem) (c : Nat) (e : List Sem)
    (he : e.length ≤ arity d c) {j : Nat} (hj : j < ps.length) :
    (bindsA dm D d ps c e)[arity d c + j]? = some (faithBind (dm.paramTy d j (ps.take j)) ps[j]
      ((paramDecls D d (arity d c)).getD j .other)) := by
  unfold bindsA
  rw [List.getElem?_append_right (by simp; omega)]
  have : arity d c + j - (e ++ List.replicate (arity d c - e.length) Sem.moved).zipIdx.length = j := by simp; omega
  rw [List.length_map, this]
  simp [List.getElem?_map, List.getElem?_zipIdx, hj]

/-- The canonical frame's bindings (`canFrame`'s). -/
noncomputable def bindsF (K : RunCtx) (d : IndDecl) (ps : List Sem) (c i : Nat) (es : List Small) (tyOf : Nat → TyM) :
    List SBinding :=
  ((List.range (arity d c)).map fun j =>
      if j < i then
        if fieldVaries d c j = false ∧ (d.indexFields c).contains j = true then
          faithBind (tyOf j) (rebuild K (tyOf j) (es.getD j .other))
            (if fieldProof K.D d c j then .prop else .other)
        else dummyB (if fieldProof K.D d c j then .prop else .other)
      else faithBind TyM.err .moved .other) ++
    (List.range d.params.length).map fun j =>
      if paramVaries d j then dummyB ((paramDecls K.D d (arity d c)).getD j .other)
      else faithBind (if j < ps.length then K.dm.paramTy d j (ps.take j) else TyM.err) (ps.getD j .err)
        ((paramDecls K.D d (arity d c)).getD j .other)

theorem canFrame_bindsF (K : RunCtx) (d : IndDecl) (ps : List Sem) (c i : Nat) (es : List Small) (tyOf : Nat → TyM) :
    canFrame K d ps c i es tyOf = stateOf 0 (bindsF K d ps c i es tyOf) := rfl

theorem bindsF_length (K : RunCtx) (d : IndDecl) (ps : List Sem) (c i : Nat) (es : List Small) (tyOf : Nat → TyM) :
    (bindsF K d ps c i es tyOf).length = arity d c + d.params.length := by
  simp [bindsF]

theorem bindsF_field (K : RunCtx) (d : IndDecl) (ps : List Sem) (c i : Nat) (es : List Small) (tyOf : Nat → TyM)
    {p : Nat} (hp : p < arity d c) :
    (bindsF K d ps c i es tyOf)[p]? = some (if p < i then
        if fieldVaries d c p = false ∧ (d.indexFields c).contains p = true then
          faithBind (tyOf p) (rebuild K (tyOf p) (es.getD p .other))
            (if fieldProof K.D d c p then .prop else .other)
        else dummyB (if fieldProof K.D d c p then .prop else .other)
      else faithBind TyM.err .moved .other) := by
  unfold bindsF
  rw [List.getElem?_append_left (by simp; omega)]
  simp [List.getElem?_map, List.getElem?_range, hp]

theorem bindsF_param (K : RunCtx) (d : IndDecl) (ps : List Sem) (c i : Nat) (es : List Small) (tyOf : Nat → TyM)
    {j : Nat} (hj : j < d.params.length) :
    (bindsF K d ps c i es tyOf)[arity d c + j]? = some (if paramVaries d j then dummyB ((paramDecls K.D d (arity d c)).getD j .other)
      else faithBind (if j < ps.length then K.dm.paramTy d j (ps.take j) else TyM.err) (ps.getD j .err)
        ((paramDecls K.D d (arity d c)).getD j .other)) := by
  unfold bindsF
  rw [List.getElem?_append_right (by simp)]
  simp [List.getElem?_map, List.getElem?_range, hj]

/-! ## Which fields a field type mentions -/

theorem fieldTerm_lt {d : IndDecl} {c i : Nat} {FT : Term} (hFT : fieldTerm d c i = some FT) : i < arity d c := by
  unfold fieldTerm at hFT
  unfold arity
  cases hc : d.ctors[c]? with
  | none => simp [hc] at hFT
  | some cs =>
    simp only [hc, Option.bind_some, Option.map_eq_some_iff] at hFT
    obtain ⟨⟨nm, FT'⟩, h1, -⟩ := hFT
    simp only [Option.map_some, Option.getD_some]
    exact (List.getElem?_eq_some_iff.1 h1).1

/-- A field a field type mentions is an index field. -/
theorem index_of_mentioned {d : IndDecl} {c i : Nat} {FT : Term} (hFT : fieldTerm d c i = some FT)
    {v : Nat} (hv : v ∈ FT.freeVars) (h1 : d.params.length ≤ v) (h2 : v < d.params.length + arity d c) :
    (d.indexFields c).contains (d.params.length + arity d c - 1 - v) = true := by
  unfold fieldTerm at hFT
  cases hc : d.ctors[c]? with
  | none => simp [hc] at hFT
  | some cs =>
    simp only [hc, Option.bind_some, Option.map_eq_some_iff] at hFT
    obtain ⟨⟨nm, FT'⟩, h1', rfl⟩ := hFT
    have har : arity d c = cs.2.length := by simp [arity, hc]
    rw [har] at h2 ⊢
    have hmem : (nm, FT') ∈ cs.2 := List.mem_of_getElem? h1'
    unfold IndDecl.indexFields IndDecl.fieldRefs
    simp only [hc, Option.map_some, Option.getD_some, List.contains_iff_mem, List.mem_filter,
      List.mem_range, List.any_eq_true]
    refine ⟨by omega, (nm, FT'), hmem, ?_⟩
    simp only [List.elem_iff, List.mem_filterMap]
    exact ⟨v, hv, by simp [Bool.and_eq_true, decide_eq_true_eq]; omega⟩

/-! ## The steady nodes -/

theorem good_faithBind {K : RunCtx} {T : TyM} {v : Sem} {dc : DeclInfo} (h : v ∈ₛ[K.dm.read] T) :
    FrameLocal.Good K (faithBind T v dc) :=
  ⟨v, rfl, Strict.mem_whole (DataModel.read_wholeFields K.dm) h, .inl (K.dm.pmem_of_mem K.Γ
    (Strict.mem_whole (DataModel.read_wholeFields K.dm) h) h)⟩

theorem good_dummyB {K : RunCtx} {dc : DeclInfo} : FrameLocal.Good K (dummyB dc) :=
  good_faithBind (K := K) (v := .el0 Nat 0) ⟨0, rfl⟩

/-- The indices at which the actual and the canonical frame may differ: the earlier fields that vary
or are no index, and the parameters that vary. -/
def XS (d : IndDecl) (c n : Nat) (p : Nat) : Prop :=
  (p < n ∧ ¬ (fieldVaries d c p = false ∧ (d.indexFields c).contains p = true)) ∨
    (arity d c ≤ p ∧ paramVaries d (p - arity d c) = true)

/-- **The steady nodes agree, at the knot's own records**: `SteadyAt` for `knotK`, assuming frame
locality's two facts (`DecLocal` on the decisions, label-free globals). -/
theorem steadyAt_knotK (K : RunCtx) (ρ : Assignment) (d : IndDecl) (hs : d.sort ≠ 0) (hdΓ : d ∈ K.Γ)
    (hspine : ∀ c i FT, fieldTerm d c i = some FT → Spine K.Γ d c FT)
    (hpar : ∀ M ∈ K.Γ, M ≠ d → ∀ n, RAgree (fun j => M.nestable.getD j false) n (K.dm.recOf M) (K.dm.recOf M))
    (hpty : ParamTyLocal K.dm K.Γ)
    (hD : FrameLocal.DecLocal K.D) (hK : ∀ g, (K.C.global g).2.label = none) :
    SteadyAt K ρ d (recK (knotK K ρ d hs hdΓ hspine hpar hpty)) := by
  intro ps c i e FT hl hty hft hei hFT t h r s' hts htv hrun
  have hfty : ∀ R ps c i es, (knotK K ρ d hs hdΓ hspine hpar hpty).fty R ps c i es = ftyK K ρ d R ps c i es :=
    fun _ _ _ _ _ => rfl
  generalize knotK K ρ d hs hdΓ hspine hpar hpty = S at hfty hft hrun ⊢
  subst hei
  have hiA : e.length < arity d c := fieldTerm_lt hFT
  have he : e.length ≤ arity d c := Nat.le_of_lt hiA
  -- the actual field types at the earlier fields are the knot's canonical ones
  have hft' : ∀ p (hp : p < e.length), (setRec K.dm d (recK S)).fieldTy d ps c p (e.take p) =
      shapeTyP (shapeOf (ftyK K ρ d (recK S) ps c p ((projIdx d c (e.map Sem.small)).take p))) := by
    intro p hp
    rw [fieldTy_knot S (setRec K.dm d (recK S)) d (setRec_self K.dm d (recK S)) ps c p e (Nat.le_of_lt hp), hfty]
  generalize htyOf : (fun j => if _h : j < e.length then
      shapeTyP (shapeOf (ftyK K ρ d (recK S) ps c j ((projIdx d c (e.map Sem.small)).take j))) else TyM.err) = tyOf
  have htyOf_lt : ∀ p (hp : p < e.length), tyOf p = (setRec K.dm d (recK S)).fieldTy d ps c p (e.take p) := by
    intro p hp; rw [← htyOf, hft' p hp]; simp [hp]
  generalize hR : recK S = R at hft' hft hrun htyOf_lt
  have hlA := bindsA_length (setRec K.dm d R) K.D d ps c e he
  have hlF := bindsF_length K d ps c e.length (projIdx d c (e.map Sem.small)) tyOf
  -- step 2: frame locality
  have hswap := runT_stateOf_swap (KR K d R) ρ noFuture false h t 0 (bindsA (setRec K.dm d R) K.D d ps c e)
    (bindsF K d ps c e.length (projIdx d c (e.map Sem.small)) tyOf) (XS d c e.length) hK hD
    (by rw [hlA, hlF, hl])
    ?hsame ?hgood ?hgood' ?hdecl ?hconst ?hvars
  case hsame =>
    intro p hX
    rcases Nat.lt_or_ge p (arity d c) with hp | hp
    · rw [bindsF_field _ _ _ _ _ _ _ hp]
      by_cases hpi : p < e.length
      · have hnv : fieldVaries d c p = false ∧ (d.indexFields c).contains p = true :=
          Classical.byContradiction fun hc => hX (.inl ⟨hpi, hc⟩)
        rw [bindsA_early _ _ _ _ _ _ hpi he, if_pos hpi, if_pos hnv, htyOf_lt p hpi]
        have hes : (projIdx d c (e.map Sem.small)).getD p .other = e[p].small := by
          rw [List.getD_eq_getElem?_getD, Piece3.projIdx_get]
          simp only [List.getElem?_map, List.getElem?_eq_getElem hpi, Option.map_some, if_pos hnv.2,
            Option.getD_some]
        rw [hes]
        have hm := hft p hpi
        rw [hft' p hpi] at hm ⊢
        rw [rebuild_eq K _ hm]
      · rw [bindsA_late _ _ _ _ _ _ (Nat.le_of_not_lt hpi) hp, if_neg hpi]
    · by_cases hpn : p < arity d c + d.params.length
      · obtain ⟨j, rfl⟩ : ∃ j, p = arity d c + j := ⟨p - arity d c, by omega⟩
        have hj : j < d.params.length := by omega
        have hpv : paramVaries d j = false := by
          cases hv : paramVaries d j
          · rfl
          · exact absurd (.inr ⟨by omega, by rw [Nat.add_sub_cancel_left]; exact hv⟩) hX
        rw [bindsF_param _ _ _ _ _ _ _ hj, bindsA_param _ _ _ _ _ _ he (by omega), if_neg (by simp [hpv]),
          if_pos (show j < ps.length by omega), List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem (show j < ps.length by omega), Option.getD_some]
        rfl
      · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
  case hgood =>
    intro p b hX hb
    rcases hX with ⟨hpi, -⟩ | ⟨hp, -⟩
    · rw [bindsA_early _ _ _ _ _ _ hpi he, Option.some.injEq] at hb
      subst hb
      exact good_faithBind (hft p hpi)
    · have hpl : p < arity d c + ps.length := by
        have := (List.getElem?_eq_some_iff.1 hb).1; rw [hlA] at this; exact this
      obtain ⟨j, rfl⟩ : ∃ j, p = arity d c + j := ⟨p - arity d c, by omega⟩
      have hj : j < ps.length := by omega
      rw [bindsA_param _ _ _ _ _ _ he hj, Option.some.injEq] at hb
      subst hb
      exact good_faithBind (hty j hj)
  case hgood' =>
    intro p b hX hb
    rcases hX with ⟨hpi, hnv⟩ | ⟨hp, hpv⟩
    · rw [bindsF_field _ _ _ _ _ _ _ (by omega), if_pos hpi, if_neg hnv, Option.some.injEq] at hb
      subst hb; exact good_dummyB
    · have hpl : p < arity d c + d.params.length := by
        have := (List.getElem?_eq_some_iff.1 hb).1; rw [hlF] at this; exact this
      obtain ⟨j, rfl⟩ : ∃ j, p = arity d c + j := ⟨p - arity d c, by omega⟩
      have hj : j < d.params.length := by omega
      rw [Nat.add_sub_cancel_left] at hpv
      rw [bindsF_param _ _ _ _ _ _ _ hj, if_pos hpv, Option.some.injEq] at hb
      subst hb; exact good_dummyB
  case hdecl =>
    intro p b b' hX hb hb'
    rcases hX with ⟨hpi, hnv⟩ | ⟨hp, hpv⟩
    · rw [bindsA_early _ _ _ _ _ _ hpi he, Option.some.injEq] at hb
      rw [bindsF_field _ _ _ _ _ _ _ (by omega), if_pos hpi, if_neg hnv, Option.some.injEq] at hb'
      subst hb hb'; rfl
    · have hpl : p < arity d c + d.params.length := by
        have := (List.getElem?_eq_some_iff.1 hb').1; rw [hlF] at this; exact this
      obtain ⟨j, rfl⟩ : ∃ j, p = arity d c + j := ⟨p - arity d c, by omega⟩
      have hj : j < d.params.length := by omega
      rw [Nat.add_sub_cancel_left] at hpv
      rw [bindsA_param _ _ _ _ _ _ he (by omega), Option.some.injEq] at hb
      rw [bindsF_param _ _ _ _ _ _ _ hj, if_pos hpv, Option.some.injEq] at hb'
      subst hb hb'; rfl
  case hconst =>
    intro b hb
    simp only [bindsA, List.mem_append, List.mem_map] at hb
    rcases hb with ⟨vi, -, rfl⟩ | ⟨vj, -, rfl⟩ <;> exact ⟨_, rfl⟩
  case hvars =>
    intro v hv hvl hX
    have hvv := hts.2 v hv
    have hvF := htv v hv
    rw [hlA] at hvl hX
    unfold varVaries at hvv
    rcases hX with ⟨hpi, hnv⟩ | ⟨hp, hpv⟩
    · have h1 : ¬ v < d.params.length := by omega
      rw [if_neg h1, if_pos (by omega)] at hvv
      have heq : d.params.length + arity d c - 1 - v = arity d c + ps.length - 1 - v := by omega
      rw [heq] at hvv
      exact hnv ⟨hvv, by rw [← heq]; exact index_of_mentioned hFT hvF (by omega) (by omega)⟩
    · have h1 : v < d.params.length := by omega
      rw [if_pos h1] at hvv
      have heq : arity d c + ps.length - 1 - v - arity d c = d.params.length - 1 - v := by omega
      rw [heq, hvv] at hpv
      exact absurd hpv (by simp)
  -- step 3: the model congruence
  rw [teleFrame_bindsA] at hrun
  have hrun' : runT (KR K d R) ρ noFuture false h t (stateOf 0 (bindsA (setRec K.dm d R) K.D d ps c e)) = some (r, s') := hrun
  rw [hrun'] at hswap
  have hc := runT_congrR K d R ρ noFuture false t h (stateOf 0 (bindsF K d ps c e.length (projIdx d c (e.map Sem.small)) tyOf)) hts.1
  unfold valOf
  rw [canFrame_bindsF, hc, hswap]
  rfl

end Ochr.Meaning.DataModel.Exists.Knot

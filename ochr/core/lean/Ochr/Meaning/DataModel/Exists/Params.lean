import Ochr.Meaning.DataModel.Exists.Records
import Ochr.Meaning.DataModel.Exists.Knot.Swap
import Ochr.Meaning.Strict.Good

/-!
# Piece 7: a declaration's parameter types, by the run (exists9)

The model's type of parameter `j` of `d` at the earlier parameters `ps` is the reference run's reading
of the declared type term (`pty`), in the frame `Machine.fieldTele`'s parameter frame describes
(`paramFrame`), with one change for a parameter that does not vary: the varying earlier parameters are
masked to a proof at the error type (`frameP … true`). The mask makes the types local in the varying
parameters by construction (`pty_local`, `knot_exists`' `hpty`), whatever the lists; on a list of
members it changes nothing the run reads (`pty_faithful`, by frame locality: a parameter that does not
vary mentions only parameters that do not vary, and a member is a `Good` binding, as is the mask).
Recursion on the length of the list (`ptyN` with fuel, `ptyN_stable`).
-/

namespace Ochr.Meaning.DataModel.Exists.Params

open Ochr Ochr.Meaning Ochr.Meaning.DataLib Ochr.Meaning.Canonical Ochr.Meaning.DataModel.Exists.Knot
open Ochr.Meaning.DataModel.Exists.Records
open Classical

section
variable (d : IndDecl)

/-- The frame a parameter type is read in, at parameter types `P`: each earlier parameter at its type
and its declared reading; with `mask`, a varying one is a proof at the error type. -/
noncomputable def frameP (P : Nat → List Sem → TyM) (D : Decisions) (mask : Bool) (ps : List Sem) : SState :=
  stateOf 0 (ps.zipIdx.map fun vj =>
    if mask && paramVaries d vj.2 then faithBind TyM.err .proof ((paramDecls D d 0).getD vj.2 .other)
    else faithBind (P vj.2 (ps.take vj.2)) vj.1 ((paramDecls D d 0).getD vj.2 .other))

theorem paramFrame_eq (dm : DataModel) (D : Decisions) (ps : List Sem) :
    paramFrame dm D d ps = frameP d (dm.paramTy d) D false ps := by
  unfold paramFrame frameP; simp

theorem frameP_congr {P P' : Nat → List Sem → TyM} (D : Decisions) (m : Bool) (ps : List Sem)
    (h : ∀ u, u < ps.length → P u (ps.take u) = P' u (ps.take u)) : frameP d P D m ps = frameP d P' D m ps := by
  unfold frameP
  congr 1
  apply List.map_congr_left
  intro vj hvj
  have hu : vj.2 < ps.length := by
    obtain ⟨v, u⟩ := vj
    have := List.mem_zipIdx hvj
    simpa using this.2.1
  split
  · rfl
  · rw [h _ hu]

end

/-- The reading of a run (`err` where it is undefined). -/
noncomputable def readTy : Option (Res × SState) → TyM
  | some (r, _) => r.1.asTy
  | none => TyM.err

section
variable (K : RunCtx) (ρ : Assignment) (d : IndDecl)

/-- The parameter types with fuel. -/
noncomputable def ptyN : Nat → Nat → List Sem → TyM
  | 0, _, _ => TyM.err
  | n + 1, j, ps => if j < d.params.length then
      readTy (run K ρ noFuture (.plain (TyM.univ 2)) (paramTerm d j) (frameP d (ptyN n) K.D (!paramVaries d j) ps))
    else TyM.err

/-- **The model's parameter types of `d`.** -/
noncomputable def pty (j : Nat) (ps : List Sem) : TyM := ptyN K ρ d (ps.length + 1) j ps

theorem ptyN_stable : ∀ (n m j : Nat) (ps : List Sem), ps.length + 1 ≤ n → ps.length + 1 ≤ m →
    ptyN K ρ d n j ps = ptyN K ρ d m j ps
  | 0, _, _, _, h, _ => absurd h (by omega)
  | _, 0, _, _, _, h => absurd h (by omega)
  | n + 1, m + 1, j, ps, hn, hm => by
    simp only [ptyN]
    rw [frameP_congr d (P := ptyN K ρ d n) (P' := ptyN K ρ d m) K.D _ ps (fun u hu =>
      ptyN_stable n m u (ps.take u) (by simp; omega) (by simp; omega))]

theorem pty_eq (j : Nat) (ps : List Sem) : pty K ρ d j ps = if j < d.params.length then
    readTy (run K ρ noFuture (.plain (TyM.univ 2)) (paramTerm d j) (frameP d (pty K ρ d) K.D (!paramVaries d j) ps))
    else TyM.err := by
  show ptyN K ρ d (ps.length + 1) j ps = _
  simp only [ptyN]
  rw [frameP_congr d (P := ptyN K ρ d ps.length) (P' := pty K ρ d) K.D _ ps (fun u hu =>
    ptyN_stable K ρ d _ _ u (ps.take u) (by simp; omega) (by simp))]

/-- **The parameter types are local in the varying parameters** (`ParamTyLocalD`, `knot_exists`'
`hpty`), at every list: the mask makes the frames of two lists agreeing at every parameter that does not
vary the same. -/
theorem pty_local : LocalP (pty K ρ d) d := by
  intro j
  induction j using Nat.strongRecOn with
  | ind j ih =>
    intro ps ps' hl hl' hv hag
    rw [pty_eq, pty_eq]
    simp only [hv, Bool.not_false]
    congr 3
    unfold frameP
    congr 1
    apply List.ext_getElem (by simp [hl, hl'])
    intro u h1 h2
    simp only [List.getElem_map, List.getElem_zipIdx, Nat.zero_add]
    have hu : u < j := by simp at h1; omega
    by_cases hvu : paramVaries d u
    · simp [hvu]
    · have hvu' : paramVaries d u = false := by simpa using hvu
      simp only [hvu', Bool.and_false, Bool.false_eq_true, if_false]
      have e1 : ps[u] = ps'[u] := by
        have := hag u hu hvu'
        rwa [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega), Option.some.injEq] at this
      have e2 : pty K ρ d u (ps.take u) = pty K ρ d u (ps'.take u) := by
        apply ih u hu _ _ (by simp; omega) (by simp; omega) hvu'
        intro w hw hvw
        rw [List.getElem?_take, List.getElem?_take, if_pos hw, if_pos hw]
        exact hag w (by omega) hvw
      rw [e1, e2]

/-- **The parameter types are faithful at members**: where the run of a declared parameter type, in the
frame of members at these types, is defined, its reading is `pty`. Assumes `DecLocal` of the context's
decisions and label-free globals (frame locality's). -/
theorem pty_faithful (hK : ∀ g, (K.C.global g).2.label = none) (hD : FrameLocal.DecLocal K.D)
    (ps : List Sem) (j : Nat) (hn : Hint) (PT : Term) (ht : Typed K.dm (pty K ρ d) ps) (hl : ps.length = j)
    (hj : d.params[j]? = some (hn, PT)) (r : Res) (s' : SState)
    (hr : run K ρ noFuture (.plain (TyM.univ 2)) PT (frameP d (pty K ρ d) K.D false ps) = some (r, s')) :
    r.1.asTy = pty K ρ d j ps := by
  have hjl : j < d.params.length := (List.getElem?_eq_some_iff.1 hj).1
  have hPT : paramTerm d j = PT := by simp [paramTerm, hj]
  rw [pty_eq, if_pos hjl, hPT]
  cases hv : paramVaries d j
  · -- masked: frame locality between the frame of members and the masked one
    simp only [Bool.not_false]
    unfold frameP at hr ⊢
    unfold run at hr ⊢
    rw [runT_stateOf_swap K ρ noFuture false _ PT 0 _ _ (fun u => paramVaries d u = true) hK hD]
    · rw [hr]; rfl
    · simp
    · intro i hi
      simp only [List.getElem?_map, List.getElem?_zipIdx]
      cases e : ps[i]? with
      | none => rfl
      | some v => simp [hi]
    · intro i b hi hb
      simp only [List.getElem?_map, List.getElem?_zipIdx] at hb
      cases e : ps[i]? with
      | none => rw [e] at hb; cases hb
      | some v =>
        rw [e] at hb
        simp only [Option.map_some, Option.some.injEq, Nat.zero_add] at hb
        rw [if_neg (by simp [hi])] at hb
        subst hb
        have hil : i < ps.length := (List.getElem?_eq_some_iff.1 e).1
        have hm := ht i hil
        rw [List.getElem?_eq_getElem hil, Option.some.injEq] at e
        rw [e] at hm
        exact ⟨v, rfl, Strict.mem_whole (DataModel.read_wholeFields K.dm) hm, .inl (DataModel.pmem_of_mem K.dm K.Γ
          (Strict.mem_whole (DataModel.read_wholeFields K.dm) hm) hm)⟩
    · intro i b hi hb
      simp only [List.getElem?_map, List.getElem?_zipIdx] at hb
      cases e : ps[i]? with
      | none => rw [e] at hb; cases hb
      | some v =>
        rw [e] at hb
        simp only [Option.map_some, Option.some.injEq, Nat.zero_add] at hb
        rw [if_pos (by simp [hi])] at hb
        subst hb
        exact ⟨.proof, rfl, by simp [Sem.whole], .inr ⟨rfl, .inr rfl⟩⟩
    · intro i b b' hi hb hb'
      simp only [List.getElem?_map, List.getElem?_zipIdx] at hb hb'
      cases e : ps[i]? with
      | none => rw [e] at hb; cases hb
      | some v =>
        rw [e] at hb hb'
        simp only [Option.map_some, Option.some.injEq, Nat.zero_add] at hb hb'
        subst hb hb'
        split <;> split <;> rfl
    · intro b hb
      simp only [List.mem_map] at hb
      obtain ⟨vj, _, rfl⟩ := hb
      exact ⟨vj.1, rfl⟩
    · intro v hvf hvl
      simp only [List.length_map, List.length_zipIdx] at hvl
      have := (paramVaries_false hv).2 v (hPT ▸ hvf) (by omega)
      simp only [List.length_map, List.length_zipIdx, hl]
      simp [this]
  · simp only [Bool.not_true]
    rw [hr]; rfl

/-- **A type parameter's type has no level-0 member** (`recordsFaithful_canon`'s `hTyP`): its
declared type is a sort, which the run reads as a universe (or `err`, which has no member). -/
theorem pty_type (j : Nat) (qs : List Sem) (h : d.paramIsType j = true) (A : Type) (c : Code0 A) (v : Sem)
    (hT : pty K ρ d j qs = .t0 A c) : ¬ v ∈ₛ[K.dm.read] .t0 A c := by
  have herr : ∀ (A : Type) (c : Code0 A), TyM.err = .t0 A c → ¬ v ∈ₛ[K.dm.read] .t0 A c := by
    intro A c e hm
    cases e
    obtain ⟨a, _⟩ := hm
    exact a.elim
  rw [pty_eq] at hT
  split at hT
  · rename_i hj
    have : ∃ hn l, d.params[j]? = some (hn, .sort l) := by
      unfold IndDecl.paramIsType at h
      split at h
      · rename_i hn l e; exact ⟨hn, l, e⟩
      · cases h
      · rename_i e; exact absurd (List.getElem?_eq_none_iff.1 e) (by omega)
    obtain ⟨hn, l, e⟩ := this
    have hPT : paramTerm d j = .sort l := by simp [paramTerm, e]
    rw [hPT] at hT
    unfold run at hT
    rw [runT] at hT
    change TyM.univ l = _ at hT
    unfold TyM.univ at hT
    split at hT
    · cases hT
    · cases hT
    · cases hT
    · exact herr A c hT
  · exact herr A c hT

end

end Ochr.Meaning.DataModel.Exists.Params

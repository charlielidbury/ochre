import Ochr.Meaning.Steps.ColumnTemp

/-!
# Plumbing for `ColumnPlumb`: a top frame modified, on both sides (lead7's proof helper)

The checker's `pushBind` and `popBind` and the reference's `pushBind` and `dropLast` change the top
frame only. The positions are then the other frames' followed by the top frame's, with one binding
position inserted or removed (bindings come before temporaries in each frame, so not at the end):
`allPos_modify_top`, `positions_modify_top`. Lookups at every other position are unchanged.
-/

namespace Ochr.Meaning.Steps.Form

open Ochr Ochr.Meaning Ochr.Meaning.Steps

/-! ## Lists with one element inserted -/

theorem find?_insert {α : Type _} (p : α → Bool) (A B : List α) (x : α) (hx : p x = false) :
    (A ++ x :: B).find? p = (A ++ B).find? p := by
  simp [List.find?_append, hx]

/-! ## The checker's environment with its top frame modified -/

theorem allPos_modify_top (env : Env) (g : Frame → Frame) (fr : Frame) (hfr : env[env.size - 1]? = some fr)
    (hne : 0 < env.size) :
    ∃ P, allPos env = P ++ frameAllPos (env.size - 1) fr ∧
      allPos (env.modify (env.size - 1) g) = P ++ frameAllPos (env.size - 1) (g fr) := by
  rw [allPos_eq, allPos_eq, Array.size_modify]
  generalize hm : env.size - 1 = m at hfr ⊢
  have hsz : env.size = m + 1 := by omega
  rw [hsz, List.range_succ, List.flatMap_append, List.flatMap_append, List.flatMap_singleton,
    List.flatMap_singleton]
  refine ⟨(List.range m).flatMap fun f => (env[f]?.map (frameAllPos f)).getD [], ?_, ?_⟩
  · rw [hfr]; rfl
  · congr 1
    · apply flatMap_congr_mem
      intro f' hf'
      have : m ≠ f' := by simp [List.mem_range] at hf'; omega
      rw [Array.getElem?_modify]; simp only [this, if_false]
    · rw [Array.getElem?_modify]; simp only [if_true, hfr, Option.map_some, Option.getD_some]

theorem bind_modify_ne (env : Env) (g : Frame → Frame) (m f i : Nat) (hf : m ≠ f) :
    (env.modify m g)[f]?.bind (·.binds[i]?) = env[f]?.bind (·.binds[i]?) := by
  rw [Array.getElem?_modify]; simp only [hf, if_false]

theorem temp_modify_ne (env : Env) (g : Frame → Frame) (m f i : Nat) (hf : m ≠ f) :
    (env.modify m g)[f]?.bind (·.temps[i]?) = env[f]?.bind (·.temps[i]?) := by
  rw [Array.getElem?_modify]; simp only [hf, if_false]

theorem bind_modify_eq (env : Env) (g : Frame → Frame) (m i : Nat) (fr : Frame) (hfr : env[m]? = some fr) :
    (env.modify m g)[m]?.bind (·.binds[i]?) = (g fr).binds[i]? := by
  rw [Array.getElem?_modify]; simp only [if_true, hfr, Option.map_some, Option.bind_some]

theorem temp_modify_eq (env : Env) (g : Frame → Frame) (m i : Nat) (fr : Frame) (hfr : env[m]? = some fr) :
    (env.modify m g)[m]?.bind (·.temps[i]?) = (g fr).temps[i]? := by
  rw [Array.getElem?_modify]; simp only [if_true, hfr, Option.map_some, Option.bind_some]

/-- `valAt` through the frame-and-slot lookups. -/
theorem valAt_bind_lookup (env : Env) (f i : Nat) :
    valAt env (.bind f i) = ((env[f]?.bind (·.binds[i]?)).getD default).val := by
  rw [valAt_bind_eq]; cases env[f]? <;> rfl

theorem valAt_temp_lookup (env : Env) (f i : Nat) :
    valAt env (.temp f i) = (env[f]?.bind (·.temps[i]?)).getD default := by
  rw [valAt_temp_eq]; cases env[f]? <;> rfl

/-! ## The reference state with its top frame modified -/

theorem positions_modify_top (s t : SState) (g : SFrame → SFrame) (fr : SFrame) (hfr : s.env[s.topIdx]? = some fr)
    (ht : t.env = s.env.modify s.topIdx g) :
    ∃ P, s.positions = P ++ framePos s.topIdx fr ∧ t.positions = P ++ framePos s.topIdx (g fr) := by
  rw [SState.positions_eq, SState.positions_eq, ht, List.length_modify]
  unfold SState.topIdx at hfr ⊢
  generalize hm : s.env.length - 1 = m at hfr ⊢
  have hlt := (List.getElem?_eq_some_iff.mp hfr).1
  have hsz : s.env.length = m + 1 := by omega
  rw [hsz, List.range_succ, List.flatMap_append, List.flatMap_append, List.flatMap_singleton,
    List.flatMap_singleton]
  refine ⟨(List.range m).flatMap fun f => (s.env[f]?.map (framePos f)).getD [], ?_, ?_⟩
  · rw [hfr]; rfl
  · congr 1
    · apply flatMap_congr_mem
      intro f' hf'
      have : m ≠ f' := by simp [List.mem_range] at hf'; omega
      rw [List.getElem?_modify]; simp only [this, if_false]
      cases s.env[f']? <;> rfl
    · rw [List.getElem?_modify]; simp only [if_true, hfr]; rfl

/-! ## The checker's `pushBind` -/

section PushBindE
variable (env : Env) (h : Hint) (ty : Option Value) (v : Value) (pf : Bool) (d : DeclInfo)

theorem allPos_pushBindE (fr : Frame) (hfr : env[env.size - 1]? = some fr) (hne : 0 < env.size) :
    ∃ A B, allPos env = A ++ B ∧
      allPos (Env.pushBindE env h ty v pf d) = A ++ Pos.bind (env.size - 1) fr.binds.size :: B := by
  obtain ⟨P, h1, h2⟩ := allPos_modify_top env
    (fun fr => { fr with binds := fr.binds.push { hint := h, ty, val := v, proof := pf, decl := d } }) fr hfr hne
  refine ⟨P ++ (List.range fr.binds.size).map (Pos.bind (env.size - 1)),
    (List.range fr.temps.size).map (Pos.temp (env.size - 1)), ?_, h2.trans ?_⟩
  · rw [h1, frameAllPos, List.append_assoc]
  · simp only [frameAllPos, Array.size_push, List.range_succ, List.map_append, List.map_cons, List.map_nil,
      List.append_assoc, List.cons_append, List.nil_append]

theorem bind_pushBindE_ne (fr : Frame) (hfr : env[env.size - 1]? = some fr) (f i : Nat)
    (hq : Pos.bind f i ≠ .bind (env.size - 1) fr.binds.size) :
    (Env.pushBindE env h ty v pf d)[f]?.bind (·.binds[i]?) = env[f]?.bind (·.binds[i]?) := by
  by_cases hf : env.size - 1 = f
  · subst hf
    refine (bind_modify_eq env _ _ i fr hfr).trans ?_
    rw [hfr]
    have hi : i ≠ fr.binds.size := fun e => hq (by rw [e])
    simp only [Option.bind_some, Array.getElem?_push, hi, if_false]
  · exact bind_modify_ne env _ _ f i hf

theorem bind_pushBindE_new (fr : Frame) (hfr : env[env.size - 1]? = some fr) :
    (Env.pushBindE env h ty v pf d)[env.size - 1]?.bind (·.binds[fr.binds.size]?) =
      some { hint := h, ty, val := v, proof := pf, decl := d } := by
  refine (bind_modify_eq env _ _ _ fr hfr).trans ?_
  simp only [Array.getElem?_push, if_true]

theorem temp_pushBindE (fr : Frame) (hfr : env[env.size - 1]? = some fr) (f i : Nat) :
    (Env.pushBindE env h ty v pf d)[f]?.bind (·.temps[i]?) = env[f]?.bind (·.temps[i]?) := by
  by_cases hf : env.size - 1 = f
  · subst hf
    refine (temp_modify_eq env _ _ i fr hfr).trans ?_
    rw [hfr]; rfl
  · exact temp_modify_ne env _ _ f i hf

theorem valAt_pushBindE_ne (fr : Frame) (hfr : env[env.size - 1]? = some fr) (q : Pos)
    (hq : q ≠ .bind (env.size - 1) fr.binds.size) :
    valAt (Env.pushBindE env h ty v pf d) q = valAt env q := by
  cases q with
  | bind f i => rw [valAt_bind_lookup, valAt_bind_lookup, bind_pushBindE_ne env h ty v pf d fr hfr f i hq]
  | temp f i => rw [valAt_temp_lookup, valAt_temp_lookup, temp_pushBindE env h ty v pf d fr hfr f i]

theorem valAt_pushBindE_new (fr : Frame) (hfr : env[env.size - 1]? = some fr) :
    valAt (Env.pushBindE env h ty v pf d) (.bind (env.size - 1) fr.binds.size) = v := by
  rw [valAt_bind_lookup, bind_pushBindE_new env h ty v pf d fr hfr]; rfl

end PushBindE

section PushBindMean
variable (dm : DataModel) (C : CodeMeaning) (Γ : List IndDecl) (ρ : Assignment)
variable (env : Env) (h : Hint) (ty : Option Value) (v : Value) (pf : Bool) (d : DeclInfo)

theorem hintAt_pushBindE_ne (fr : Frame) (hfr : env[env.size - 1]? = some fr) (q : Pos)
    (hq : q ≠ .bind (env.size - 1) fr.binds.size) :
    Env.hintAt dm C Γ ρ (Env.pushBindE env h ty v pf d) q = Env.hintAt dm C Γ ρ env q := by
  cases q with
  | temp => rfl
  | bind f i => simp only [Env.hintAt, bind_pushBindE_ne env h ty v pf d fr hfr f i hq]

theorem hintAt_pushBindE_new (fr : Frame) (hfr : env[env.size - 1]? = some fr) (T : Value) :
    Env.hintAt dm C Γ ρ (Env.pushBindE env h (some T) v pf d) (.bind (env.size - 1) fr.binds.size) =
      Value.tyS dm C Γ ρ T := by
  simp only [Env.hintAt, bind_pushBindE_new env h (some T) v pf d fr hfr]

theorem mean_pushBindE_ne (fr : Frame) (hfr : env[env.size - 1]? = some fr) (φ : Future) (q : Pos)
    (hq : q ≠ .bind (env.size - 1) fr.binds.size) :
    Env.mean dm C Γ ρ φ (Env.pushBindE env h ty v pf d) q = Env.mean dm C Γ ρ φ env q := by
  cases q with
  | bind f i =>
    simp only [Env.mean, hintAt_pushBindE_ne dm C Γ ρ env h ty v pf d fr hfr _ hq,
      bind_pushBindE_ne env h ty v pf d fr hfr f i hq]
  | temp f i =>
    simp only [Env.mean, hintAt_pushBindE_ne dm C Γ ρ env h ty v pf d fr hfr _ hq,
      temp_pushBindE env h ty v pf d fr hfr f i]

theorem mean_pushBindE_new (fr : Frame) (hfr : env[env.size - 1]? = some fr) (φ : Future) (T : Value) :
    Env.mean dm C Γ ρ φ (Env.pushBindE env h (some T) v pf d) (.bind (env.size - 1) fr.binds.size) =
      Value.mean dm C Γ ρ φ (Value.tyS dm C Γ ρ T) v := by
  simp only [Env.mean, hintAt_pushBindE_new dm C Γ ρ env h v pf d fr hfr T,
    bind_pushBindE_new env h (some T) v pf d fr hfr]

end PushBindMean

section PushBindHolders
variable (env : Env) (h : Hint) (ty : Option Value) (v : Value) (pf : Bool) (d : DeclInfo)

theorem shape_pushBindE_ne (fr : Frame) (hfr : env[env.size - 1]? = some fr) (q : Pos)
    (hq : q ≠ .bind (env.size - 1) fr.binds.size) :
    Env.shape (Env.pushBindE env h ty v pf d) q = Env.shape env q := by
  simp only [Env.shape, valAt_pushBindE_ne env h ty v pf d fr hfr q hq]

theorem new_not_mem_pushBindE (fr : Frame)
    {A B : List Pos} (h2 : allPos (Env.pushBindE env h ty v pf d) = A ++ Pos.bind (env.size - 1) fr.binds.size :: B) :
    Pos.bind (env.size - 1) fr.binds.size ∉ A ++ B := by
  have hnd := allPos_nodup (Env.pushBindE env h ty v pf d)
  rw [h2, List.nodup_append] at hnd
  obtain ⟨_, hB, hdisj⟩ := hnd
  intro hm
  rcases List.mem_append.mp hm with hA | hB'
  · exact hdisj _ hA _ (List.mem_cons_self ..) rfl
  · exact (List.nodup_cons.mp hB).1 hB'

theorem findBorrow_pushBindE (fr : Frame) (hfr : env[env.size - 1]? = some fr) (hne : 0 < env.size) (l : Nat)
    (hv : v.holdsBorrow l = false) :
    findBorrow (Env.pushBindE env h ty v pf d) l = findBorrow env l := by
  obtain ⟨A, B, h1, h2⟩ := allPos_pushBindE env h ty v pf d fr hfr hne
  have hn := new_not_mem_pushBindE env h ty v pf d fr h2
  unfold findBorrow
  rw [h2, find?_insert _ _ _ _ (by rw [valAt_pushBindE_new env h ty v pf d fr hfr]; exact hv), h1]
  apply find?_congr_mem
  intro q hq
  rw [valAt_pushBindE_ne env h ty v pf d fr hfr q (fun e => hn (e ▸ hq))]

theorem liveLoan_pushBindE (fr : Frame) (hfr : env[env.size - 1]? = some fr) (hne : 0 < env.size) (l : Nat)
    (hv : v.holdsBorrow l = false) :
    liveLoan (Env.pushBindE env h ty v pf d) l = liveLoan env l := by
  simp only [liveLoan, findBorrow_pushBindE env h ty v pf d fr hfr hne l hv]

theorem sitesOf_pushBindE (fr : Frame) (hfr : env[env.size - 1]? = some fr) (hne : 0 < env.size) (l : Nat)
    (hv : ∀ pos path, v.sitesOf l pos path = []) :
    Env.sitesOf (Env.pushBindE env h ty v pf d) l = Env.sitesOf env l := by
  obtain ⟨A, B, h1, h2⟩ := allPos_pushBindE env h ty v pf d fr hfr hne
  have hn := new_not_mem_pushBindE env h ty v pf d fr h2
  unfold Env.sitesOf
  rw [h2, h1, List.flatMap_append, List.flatMap_cons, List.flatMap_append, valAt_pushBindE_new env h ty v pf d fr hfr,
    hv, List.nil_append]
  congr 1 <;> apply flatMap_congr_mem <;> intro q hq <;>
    rw [valAt_pushBindE_ne env h ty v pf d fr hfr q (fun e => hn (by rw [← e]; simp [hq]))]

theorem mem_values_pushBindE (fr : Frame) (hfr : env[env.size - 1]? = some fr) (hne : 0 < env.size) {w : Value}
    (hw : w ∈ Env.values (Env.pushBindE env h ty v pf d)) : w = v ∨ w ∈ Env.values env := by
  obtain ⟨A, B, h1, h2⟩ := allPos_pushBindE env h ty v pf d fr hfr hne
  have hn := new_not_mem_pushBindE env h ty v pf d fr h2
  simp only [Env.values, List.mem_map] at hw ⊢
  obtain ⟨q, hq, rfl⟩ := hw
  rw [h2, List.mem_append, List.mem_cons] at hq
  rw [h1]
  rcases hq with hq | rfl | hq
  · exact .inr ⟨q, List.mem_append_left _ hq,
      (valAt_pushBindE_ne env h ty v pf d fr hfr q (fun e => hn (by rw [← e]; simp [hq]))).symm⟩
  · exact .inl (valAt_pushBindE_new env h ty v pf d fr hfr)
  · exact .inr ⟨q, List.mem_append_right _ hq,
      (valAt_pushBindE_ne env h ty v pf d fr hfr q (fun e => hn (by rw [← e]; simp [hq]))).symm⟩

end PushBindHolders

/-! ## The reference's `pushBind` -/

section SPushBind
variable (s : SState) (b : SBinding) (frs : SFrame) (hfrs : s.env[s.topIdx]? = some frs)
include hfrs

theorem positions_pushBind' :
    ∃ A B, s.positions = A ++ B ∧ (s.pushBind b).positions = A ++ Pos.bind s.topIdx frs.binds.length :: B := by
  obtain ⟨P, h1, h2⟩ := positions_modify_top s (s.pushBind b) (fun fr => { fr with binds := fr.binds ++ [b] }) frs hfrs rfl
  refine ⟨P ++ (List.range frs.binds.length).map (Pos.bind s.topIdx),
    (List.range frs.temps.length).map (Pos.temp s.topIdx), ?_, h2.trans ?_⟩
  · rw [h1, framePos, List.append_assoc]
  · simp only [framePos, List.length_append, List.length_singleton, List.range_succ, List.map_append, List.map_cons,
      List.map_nil, List.append_assoc, List.cons_append, List.nil_append]

theorem sbind_pushBind_ne (f i : Nat) (hq : Pos.bind f i ≠ .bind s.topIdx frs.binds.length) :
    (s.pushBind b).env[f]?.bind (·.binds[i]?) = s.env[f]?.bind (·.binds[i]?) := by
  simp only [SState.pushBind, List.getElem?_modify]
  by_cases hf : s.topIdx = f
  · subst hf
    simp only [if_true]
    rw [hfrs]
    show (frs.binds ++ [b])[i]? = frs.binds[i]?
    have hi : i ≠ frs.binds.length := fun e => hq (by rw [e])
    rcases Nat.lt_or_ge i frs.binds.length with hlt | hge
    · exact List.getElem?_append_left hlt
    · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none hge]
  · simp only [hf, if_false]
    cases s.env[f]? <;> rfl

theorem sbind_pushBind_new :
    (s.pushBind b).env[s.topIdx]?.bind (·.binds[frs.binds.length]?) = some b := by
  simp only [SState.pushBind, List.getElem?_modify, if_true]
  rw [hfrs]
  show (frs.binds ++ [b])[frs.binds.length]? = some b
  simp

theorem stemp_pushBind (f i : Nat) :
    (s.pushBind b).env[f]?.bind (·.temps[i]?) = s.env[f]?.bind (·.temps[i]?) := by
  simp only [SState.pushBind, List.getElem?_modify]
  by_cases hf : s.topIdx = f
  · subst hf
    simp only [if_true]
    rw [hfrs]; rfl
  · simp only [hf, if_false]
    cases s.env[f]? <;> rfl

theorem valAt_pushBind_ne (q : Pos) (hq : q ≠ .bind s.topIdx frs.binds.length) :
    (s.pushBind b).valAt q = s.valAt q := by
  cases q with
  | bind f i => simp only [SState.valAt, sbind_pushBind_ne s b frs hfrs f i hq]
  | temp f i => simp only [SState.valAt, stemp_pushBind s b frs hfrs f i]

theorem valAt_pushBind_new : (s.pushBind b).valAt (.bind s.topIdx frs.binds.length) = b.val := by
  simp only [SState.valAt, sbind_pushBind_new s b frs hfrs]

theorem tyAt_pushBind_ne (q : Pos) (hq : q ≠ .bind s.topIdx frs.binds.length) :
    (s.pushBind b).tyAt q = s.tyAt q := by
  cases q with
  | bind f i => simp only [SState.tyAt, sbind_pushBind_ne s b frs hfrs f i hq]
  | temp f i => rfl

omit hfrs in
theorem newS_not_mem (frs : SFrame) (hfrs : s.env[s.topIdx]? = some frs) :
    Pos.bind s.topIdx frs.binds.length ∉ s.positions := by
  rw [SState.mem_positions]
  simp [SState.lookup, hfrs]

theorem live_pushBind' (hsh : s.shape (.bind s.topIdx frs.binds.length) = none) (l : Nat) :
    (s.pushBind b).Live l ↔ s.Live l := by
  obtain ⟨A, B, h1, h2⟩ := positions_pushBind' s b frs hfrs
  rw [SState.live_iff, SState.live_iff, h1, h2]
  show (∃ p ∈ A ++ _ :: B, s.shape p = some l) ↔ _
  constructor
  · rintro ⟨p, hp, hs⟩
    rw [List.mem_append, List.mem_cons] at hp
    rcases hp with hp | rfl | hp
    · exact ⟨p, List.mem_append_left _ hp, hs⟩
    · rw [hsh] at hs; cases hs
    · exact ⟨p, List.mem_append_right _ hp, hs⟩
  · rintro ⟨p, hp, hs⟩
    rw [List.mem_append] at hp
    rcases hp with hp | hp
    · exact ⟨p, List.mem_append_left _ hp, hs⟩
    · exact ⟨p, List.mem_append_right _ (List.mem_cons_of_mem _ hp), hs⟩

theorem holderOf_pushBind (hsh : s.shape (.bind s.topIdx frs.binds.length) = none) (l : Nat) :
    (s.pushBind b).holderOf l = s.holderOf l := by
  obtain ⟨A, B, h1, h2⟩ := positions_pushBind' s b frs hfrs
  unfold SState.holderOf
  rw [h1, h2]
  exact find?_insert _ A B _ (by simp [SState.pushBind, hsh])

theorem holderTy_pushBind (hsh : s.shape (.bind s.topIdx frs.binds.length) = none) (l : Nat) :
    holderTy (s.pushBind b) l = holderTy s l := by
  unfold holderTy
  rw [holderOf_pushBind s b frs hfrs hsh l]
  cases hh : s.holderOf l with
  | none => rfl
  | some r =>
    cases r with
    | temp => rfl
    | bind f i =>
      have hm := (SState.holderOf_spec hh).1
      dsimp only
      rw [tyAt_pushBind_ne s b frs hfrs _ (fun e => newS_not_mem s frs hfrs (e ▸ hm))]

end SPushBind

/-! ## The skeletons -/

theorem sskel_pushBind (s : SState) (b : SBinding) :
    (s.pushBind b).env.map (fun fr => fr.binds.map bindSkel) =
      (s.env.map (fun fr => fr.binds.map bindSkel)).modify s.topIdx (· ++ [bindSkel b]) := by
  apply List.ext_getElem?
  intro f
  simp only [SState.pushBind, List.getElem?_map, List.getElem?_modify]
  by_cases hf : s.topIdx = f
  · simp only [hf, if_true]
    cases s.env[f]? <;> simp
  · simp only [hf, if_false]
    cases s.env[f]? <;> rfl

section
variable (K : RunCtx) (ρ : Assignment)

/-- The skeleton of the checker's state read as a reference state, off the environment. -/
theorem skel_eq (st : MState) :
    (SM' K ρ st).env.map (fun fr => fr.binds.map bindSkel) =
      st.env.toList.zipIdx.map (fun (fr, f) =>
        fr.binds.toList.zipIdx.map (fun (b, i) => ((Binding.refTy K.dm K.M K.Γ ρ st.env f i b).m, b.decl))) := by
  simp only [SM', MState.sstate, List.map_map, Function.comp_def, bindSkel]

theorem skel_pushBindE (st : MState) (h : Hint) (T v : Value) (pf : Bool) (d : DeclInfo) (fr : Frame)
    (hfr : st.env[st.env.size - 1]? = some fr) :
    (SM' K ρ { st with env := Env.pushBindE st.env h (some T) v pf d }).env.map (fun fr => fr.binds.map bindSkel) =
      ((SM' K ρ st).env.map (fun fr => fr.binds.map bindSkel)).modify (st.env.size - 1)
        (· ++ [((Value.tyS K.dm K.M K.Γ ρ T).m, d)]) := by
  rw [skel_eq, skel_eq]
  apply List.ext_getElem?
  intro f
  simp only [List.getElem?_map, List.getElem?_zipIdx, Array.getElem?_toList, List.getElem?_modify, Option.map_map]
  by_cases hf : st.env.size - 1 = f
  · subst hf
    simp only [if_true]
    have e : (Env.pushBindE st.env h (some T) v pf d)[st.env.size - 1]? =
        some { fr with binds := fr.binds.push { hint := h, ty := some T, val := v, proof := pf, decl := d } } := by
      simp only [Env.pushBindE, Array.getElem?_modify, if_true, hfr, Option.map_some]
    rw [e, hfr]
    show some _ = some _
    dsimp only [Function.comp]
    congr 1
    rw [Array.toList_push, List.zipIdx_append, List.map_append, List.zipIdx_singleton, List.map_singleton]
    congr 1
    · apply List.map_congr_left
      intro x hx
      have hlt := List.snd_lt_of_mem_zipIdx hx
      simp only [Binding.refTy]
      rw [hintAt_pushBindE_ne K.dm K.M K.Γ ρ st.env h (some T) v pf d fr hfr _ (by
        intro e; injection e with _ e2; simp at hlt; omega)]
    · simp only [Nat.zero_add, Array.length_toList]
      simp only [Binding.refTy, Option.isSome_none, Bool.false_and, Bool.false_eq_true, if_false]
      rw [hintAt_pushBindE_new K.dm K.M K.Γ ρ st.env h v pf d fr hfr T]
  · simp only [hf, if_false]
    have e : (Env.pushBindE st.env h (some T) v pf d)[f]? = st.env[f]? := by
      simp only [Env.pushBindE, Array.getElem?_modify, hf, if_false]
    rw [e]
    cases st.env[f]? with
    | none => rfl
    | some fr0 =>
      show some _ = some _
      dsimp only [Function.comp]
      congr 1
      apply List.map_congr_left
      intro x _
      simp only [Binding.refTy]
      rw [hintAt_pushBindE_ne K.dm K.M K.Γ ρ st.env h (some T) v pf d fr hfr _ (by
        intro e; injection e with e1; exact hf (by omega))]

/-- Related skeletons have the same top frame index and the same number of bindings there. -/
theorem skel_align (st : MState) (s : SState)
    (hsk : (SM' K ρ st).env.map (fun fr => fr.binds.map bindSkel) = s.env.map (fun fr => fr.binds.map bindSkel))
    (fr : Frame) (hfr : st.env[st.env.size - 1]? = some fr) :
    ∃ frs : SFrame, s.env[s.topIdx]? = some frs ∧ s.topIdx = st.env.size - 1 ∧ frs.binds.length = fr.binds.size := by
  rw [skel_eq] at hsk
  have hlen : s.env.length = st.env.size := by
    have := congrArg List.length hsk
    simp only [List.length_map, List.length_zipIdx, Array.length_toList] at this
    exact this.symm
  have htop : s.topIdx = st.env.size - 1 := by simp only [SState.topIdx, hlen]
  have h2 := congrArg (fun L => L[st.env.size - 1]?.map List.length) hsk
  simp only [List.getElem?_map, List.getElem?_zipIdx, Array.getElem?_toList, hfr, Option.map_map,
    Option.map_some, List.length_map, List.length_zipIdx, Array.length_toList] at h2
  rw [htop]
  cases e : s.env[st.env.size - 1]? with
  | none => rw [e] at h2; cases h2
  | some frs =>
    rw [e] at h2
    simp only [Option.map_some, Option.some.injEq, Function.comp_apply, List.length_map] at h2
    exact ⟨frs, rfl, rfl, h2.symm⟩

end

/-! ## The checker's top binding popped

`Env.popBindE` (defined in `ColumnPlumb`) is `env.modify (env.size - 1) popTop`. -/

/-- The top frame's last binding popped. -/
def popTop (fr : Frame) : Frame := { fr with binds := fr.binds.pop }

section PopBindE
variable (env : Env) (fr : Frame) (hfr : env[env.size - 1]? = some fr) (hn : 0 < fr.binds.size)
include hfr

include hn in
theorem allPos_popTop (hne : 0 < env.size) :
    ∃ A B, allPos env = A ++ Pos.bind (env.size - 1) (fr.binds.size - 1) :: B ∧
      allPos (env.modify (env.size - 1) popTop) = A ++ B := by
  obtain ⟨P, h1, h2⟩ := allPos_modify_top env popTop fr hfr hne
  refine ⟨P ++ (List.range (fr.binds.size - 1)).map (Pos.bind (env.size - 1)),
    (List.range fr.temps.size).map (Pos.temp (env.size - 1)), h1.trans ?_, h2.trans ?_⟩
  · have : fr.binds.size = (fr.binds.size - 1) + 1 := by omega
    rw [frameAllPos, this, List.range_succ, Nat.add_sub_cancel]
    simp only [List.map_append, List.map_cons, List.map_nil, List.append_assoc, List.cons_append, List.nil_append]
  · simp only [frameAllPos, popTop, Array.size_pop, List.append_assoc]

theorem bind_popTop_ne (f i : Nat) (hq : Pos.bind f i ≠ .bind (env.size - 1) (fr.binds.size - 1)) :
    (env.modify (env.size - 1) popTop)[f]?.bind (·.binds[i]?) = env[f]?.bind (·.binds[i]?) := by
  by_cases hf : env.size - 1 = f
  · subst hf
    refine (bind_modify_eq env _ _ i fr hfr).trans ?_
    rw [hfr]
    have hi : i ≠ fr.binds.size - 1 := fun e => hq (by rw [e])
    simp only [Option.bind_some, popTop, Array.getElem?_pop]
    split
    · rfl
    · rw [Array.getElem?_eq_none (by omega)]
  · exact bind_modify_ne env _ _ f i hf

theorem bind_popTop_old :
    (env.modify (env.size - 1) popTop)[env.size - 1]?.bind (·.binds[fr.binds.size - 1]?) = none := by
  refine (bind_modify_eq env _ _ _ fr hfr).trans ?_
  simp only [popTop, Array.getElem?_pop, Nat.lt_irrefl, if_false]

theorem temp_popTop (f i : Nat) :
    (env.modify (env.size - 1) popTop)[f]?.bind (·.temps[i]?) = env[f]?.bind (·.temps[i]?) := by
  by_cases hf : env.size - 1 = f
  · subst hf
    refine (temp_modify_eq env _ _ i fr hfr).trans ?_
    rw [hfr]; rfl
  · exact temp_modify_ne env _ _ f i hf

theorem valAt_popTop_ne (q : Pos) (hq : q ≠ .bind (env.size - 1) (fr.binds.size - 1)) :
    valAt (env.modify (env.size - 1) popTop) q = valAt env q := by
  cases q with
  | bind f i => rw [valAt_bind_lookup, valAt_bind_lookup, bind_popTop_ne env fr hfr f i hq]
  | temp f i => rw [valAt_temp_lookup, valAt_temp_lookup, temp_popTop env fr hfr f i]

theorem shape_popTop_ne (q : Pos) (hq : q ≠ .bind (env.size - 1) (fr.binds.size - 1)) :
    Env.shape (env.modify (env.size - 1) popTop) q = Env.shape env q := by
  simp only [Env.shape, valAt_popTop_ne env fr hfr q hq]

end PopBindE

section PopBindMean
variable (dm : DataModel) (C : CodeMeaning) (Γ : List IndDecl) (ρ : Assignment)
variable (env : Env) (fr : Frame) (hfr : env[env.size - 1]? = some fr)
include hfr

theorem hintAt_popTop_ne (q : Pos) (hq : q ≠ .bind (env.size - 1) (fr.binds.size - 1)) :
    Env.hintAt dm C Γ ρ (env.modify (env.size - 1) popTop) q = Env.hintAt dm C Γ ρ env q := by
  cases q with
  | temp => rfl
  | bind f i => simp only [Env.hintAt, bind_popTop_ne env fr hfr f i hq]

theorem mean_popTop_ne (φ : Future) (q : Pos) (hq : q ≠ .bind (env.size - 1) (fr.binds.size - 1)) :
    Env.mean dm C Γ ρ φ (env.modify (env.size - 1) popTop) q = Env.mean dm C Γ ρ φ env q := by
  cases q with
  | bind f i =>
    simp only [Env.mean, hintAt_popTop_ne dm C Γ ρ env fr hfr _ hq, bind_popTop_ne env fr hfr f i hq]
  | temp f i =>
    simp only [Env.mean, hintAt_popTop_ne dm C Γ ρ env fr hfr _ hq, temp_popTop env fr hfr f i]

theorem mean_popTop_old (φ : Future) :
    Env.mean dm C Γ ρ φ (env.modify (env.size - 1) popTop) (.bind (env.size - 1) (fr.binds.size - 1)) = .err := by
  simp only [Env.mean, bind_popTop_old env fr hfr]

end PopBindMean

section PopBindHolders
variable (env : Env) (fr : Frame) (hfr : env[env.size - 1]? = some fr) (hn : 0 < fr.binds.size)
  (hne : 0 < env.size)
include hfr hn hne

omit hfr hn hne in
theorem old_not_mem_popTop {A B : List Pos}
    (h1 : allPos env = A ++ Pos.bind (env.size - 1) (fr.binds.size - 1) :: B) :
    Pos.bind (env.size - 1) (fr.binds.size - 1) ∉ A ++ B := by
  have hnd := allPos_nodup env
  rw [h1, List.nodup_append] at hnd
  obtain ⟨_, hB, hdisj⟩ := hnd
  intro hm
  rcases List.mem_append.mp hm with hA | hB'
  · exact hdisj _ hA _ (List.mem_cons_self ..) rfl
  · exact (List.nodup_cons.mp hB).1 hB'

theorem findBorrow_popTop (l : Nat) (hv : (valAt env (.bind (env.size - 1) (fr.binds.size - 1))).holdsBorrow l = false) :
    findBorrow (env.modify (env.size - 1) popTop) l = findBorrow env l := by
  obtain ⟨A, B, h1, h2⟩ := allPos_popTop env fr hfr hn hne
  have ho := old_not_mem_popTop env fr h1
  unfold findBorrow
  rw [h2, h1, find?_insert (fun p => (valAt env p).holdsBorrow l) _ _ _ hv]
  apply find?_congr_mem
  intro q hq
  rw [valAt_popTop_ne env fr hfr q (fun e => ho (e ▸ hq))]

theorem liveLoan_popTop (l : Nat) (hv : (valAt env (.bind (env.size - 1) (fr.binds.size - 1))).holdsBorrow l = false) :
    liveLoan (env.modify (env.size - 1) popTop) l = liveLoan env l := by
  simp only [liveLoan, findBorrow_popTop env fr hfr hn hne l hv]

theorem sitesOf_popTop (l : Nat)
    (hv : (valAt env (.bind (env.size - 1) (fr.binds.size - 1))).sitesOf l (.bind (env.size - 1) (fr.binds.size - 1)) [] = []) :
    Env.sitesOf (env.modify (env.size - 1) popTop) l = Env.sitesOf env l := by
  obtain ⟨A, B, h1, h2⟩ := allPos_popTop env fr hfr hn hne
  have ho := old_not_mem_popTop env fr h1
  unfold Env.sitesOf
  rw [h2, h1, List.flatMap_append, List.flatMap_append, List.flatMap_cons, hv, List.nil_append]
  congr 1 <;> apply flatMap_congr_mem <;> intro q hq <;>
    rw [valAt_popTop_ne env fr hfr q (fun e => ho (by rw [← e]; simp [hq]))]

theorem mem_values_popTop {w : Value} (hw : w ∈ Env.values (env.modify (env.size - 1) popTop)) :
    w ∈ Env.values env := by
  obtain ⟨A, B, h1, h2⟩ := allPos_popTop env fr hfr hn hne
  have ho := old_not_mem_popTop env fr h1
  simp only [Env.values, List.mem_map] at hw ⊢
  obtain ⟨q, hq, rfl⟩ := hw
  rw [h2] at hq
  refine ⟨q, ?_, (valAt_popTop_ne env fr hfr q (fun e => ho (e ▸ hq))).symm⟩
  rw [h1]
  rcases List.mem_append.mp hq with hq | hq
  · exact List.mem_append_left _ hq
  · exact List.mem_append_right _ (List.mem_cons_of_mem _ hq)

theorem mem_allPos_popTop {q : Pos} (hq : q ∈ allPos (env.modify (env.size - 1) popTop)) :
    q ∈ allPos env ∧ q ≠ .bind (env.size - 1) (fr.binds.size - 1) := by
  obtain ⟨A, B, h1, h2⟩ := allPos_popTop env fr hfr hn hne
  have ho := old_not_mem_popTop env fr h1
  rw [h2] at hq
  refine ⟨?_, fun e => ho (e ▸ hq)⟩
  rw [h1]
  rcases List.mem_append.mp hq with hq | hq
  · exact List.mem_append_left _ hq
  · exact List.mem_append_right _ (List.mem_cons_of_mem _ hq)

end PopBindHolders

/-! ## The reference's `dropLast` -/

section SDropLast
variable (s : SState) (frs : SFrame) (hfrs : s.env[s.topIdx]? = some frs) (hn : 0 < frs.binds.length)
include hfrs

include hn in
theorem positions_dropLast' :
    ∃ A B, s.positions = A ++ Pos.bind s.topIdx (frs.binds.length - 1) :: B ∧ s.dropLast.positions = A ++ B := by
  obtain ⟨P, h1, h2⟩ := positions_modify_top s s.dropLast (fun fr => { fr with binds := fr.binds.dropLast }) frs hfrs rfl
  refine ⟨P ++ (List.range (frs.binds.length - 1)).map (Pos.bind s.topIdx),
    (List.range frs.temps.length).map (Pos.temp s.topIdx), h1.trans ?_, h2.trans ?_⟩
  · have : frs.binds.length = (frs.binds.length - 1) + 1 := by omega
    rw [framePos, this, List.range_succ, Nat.add_sub_cancel]
    simp only [List.map_append, List.map_cons, List.map_nil, List.append_assoc, List.cons_append, List.nil_append]
  · simp only [framePos, List.length_dropLast, List.append_assoc]

theorem sbind_dropLast_ne (f i : Nat) (hq : Pos.bind f i ≠ .bind s.topIdx (frs.binds.length - 1)) :
    s.dropLast.env[f]?.bind (·.binds[i]?) = s.env[f]?.bind (·.binds[i]?) := by
  simp only [SState.dropLast, List.getElem?_modify]
  by_cases hf : s.topIdx = f
  · subst hf
    simp only [if_true]
    rw [hfrs]
    show frs.binds.dropLast[i]? = frs.binds[i]?
    have hi : i ≠ frs.binds.length - 1 := fun e => hq (by rw [e])
    rw [List.getElem?_dropLast]
    split
    · rfl
    · rw [List.getElem?_eq_none (by omega)]
  · simp only [hf, if_false]
    cases s.env[f]? <;> rfl

theorem sbind_dropLast_old :
    s.dropLast.env[s.topIdx]?.bind (·.binds[frs.binds.length - 1]?) = none := by
  simp only [SState.dropLast, List.getElem?_modify, if_true]
  rw [hfrs]
  show frs.binds.dropLast[frs.binds.length - 1]? = none
  rw [List.getElem?_dropLast]
  simp

theorem stemp_dropLast (f i : Nat) :
    s.dropLast.env[f]?.bind (·.temps[i]?) = s.env[f]?.bind (·.temps[i]?) := by
  simp only [SState.dropLast, List.getElem?_modify]
  by_cases hf : s.topIdx = f
  · subst hf
    simp only [if_true]
    rw [hfrs]; rfl
  · simp only [hf, if_false]
    cases s.env[f]? <;> rfl

theorem valAt_dropLast_ne (q : Pos) (hq : q ≠ .bind s.topIdx (frs.binds.length - 1)) :
    s.dropLast.valAt q = s.valAt q := by
  cases q with
  | bind f i => simp only [SState.valAt, sbind_dropLast_ne s frs hfrs f i hq]
  | temp f i => simp only [SState.valAt, stemp_dropLast s frs hfrs f i]

theorem valAt_dropLast_old : s.dropLast.valAt (.bind s.topIdx (frs.binds.length - 1)) = fun _ => .err := by
  simp only [SState.valAt, sbind_dropLast_old s frs hfrs]

theorem tyAt_dropLast_ne (q : Pos) (hq : q ≠ .bind s.topIdx (frs.binds.length - 1)) :
    s.dropLast.tyAt q = s.tyAt q := by
  cases q with
  | bind f i => simp only [SState.tyAt, sbind_dropLast_ne s frs hfrs f i hq]
  | temp f i => rfl

theorem shape_dropLast' (q : Pos) :
    s.dropLast.shape q = if q = .bind s.topIdx (frs.binds.length - 1) then none else s.shape q := by
  have hlast : s.env.getLast? = some frs := by
    rw [List.getLast?_eq_getElem?]; exact hfrs
  simp only [SState.dropLast, hlast]
  by_cases hq : q = .bind s.topIdx (frs.binds.length - 1)
  · simp [hq]
  · simp [hq]

theorem shape_dropLast_eq (hsh : s.shape (.bind s.topIdx (frs.binds.length - 1)) = none) (q : Pos) :
    s.dropLast.shape q = s.shape q := by
  rw [shape_dropLast' s frs hfrs q]
  split
  · next h => rw [h, hsh]
  · rfl

include hn in
theorem live_dropLast' (hsh : s.shape (.bind s.topIdx (frs.binds.length - 1)) = none) (l : Nat) :
    s.dropLast.Live l ↔ s.Live l := by
  obtain ⟨A, B, h1, h2⟩ := positions_dropLast' s frs hfrs hn
  rw [SState.live_iff, SState.live_iff, h1, h2]
  simp only [shape_dropLast_eq s frs hfrs hsh]
  constructor
  · rintro ⟨p, hp, hs⟩
    rcases List.mem_append.mp hp with hp | hp
    · exact ⟨p, List.mem_append_left _ hp, hs⟩
    · exact ⟨p, List.mem_append_right _ (List.mem_cons_of_mem _ hp), hs⟩
  · rintro ⟨p, hp, hs⟩
    rw [List.mem_append, List.mem_cons] at hp
    rcases hp with hp | rfl | hp
    · exact ⟨p, List.mem_append_left _ hp, hs⟩
    · rw [hsh] at hs; cases hs
    · exact ⟨p, List.mem_append_right _ hp, hs⟩

include hn in
theorem holderOf_dropLast (hsh : s.shape (.bind s.topIdx (frs.binds.length - 1)) = none) (l : Nat) :
    s.dropLast.holderOf l = s.holderOf l := by
  obtain ⟨A, B, h1, h2⟩ := positions_dropLast' s frs hfrs hn
  unfold SState.holderOf
  rw [h1, h2, find?_insert (fun p => decide (s.shape p = some l)) A B _ (by simp [hsh])]
  simp only [shape_dropLast_eq s frs hfrs hsh]

include hn in
theorem holderTy_dropLast (hsh : s.shape (.bind s.topIdx (frs.binds.length - 1)) = none) (l : Nat) :
    holderTy s.dropLast l = holderTy s l := by
  unfold holderTy
  rw [holderOf_dropLast s frs hfrs hn hsh l]
  cases hh : s.holderOf l with
  | none => rfl
  | some r =>
    cases r with
    | temp => rfl
    | bind f i =>
      have hs := (SState.holderOf_spec hh).2
      dsimp only
      rw [tyAt_dropLast_ne s frs hfrs _ (fun e => by rw [e, hsh] at hs; cases hs)]

end SDropLast

theorem sskel_dropLast (s : SState) :
    s.dropLast.env.map (fun fr => fr.binds.map bindSkel) =
      (s.env.map (fun fr => fr.binds.map bindSkel)).modify s.topIdx List.dropLast := by
  apply List.ext_getElem?
  intro f
  simp only [SState.dropLast, List.getElem?_map, List.getElem?_modify]
  by_cases hf : s.topIdx = f
  · simp only [hf, if_true]
    cases s.env[f]? <;> simp
  · simp only [hf, if_false]
    cases s.env[f]? <;> rfl

theorem skel_popTop (K : RunCtx) (ρ : Assignment) (st : MState) (fr : Frame) (hfr : st.env[st.env.size - 1]? = some fr) :
    (SM' K ρ { st with env := st.env.modify (st.env.size - 1) popTop }).env.map (fun fr => fr.binds.map bindSkel) =
      ((SM' K ρ st).env.map (fun fr => fr.binds.map bindSkel)).modify (st.env.size - 1) List.dropLast := by
  rw [skel_eq, skel_eq]
  apply List.ext_getElem?
  intro f
  simp only [List.getElem?_map, List.getElem?_zipIdx, Array.getElem?_toList, List.getElem?_modify, Option.map_map]
  by_cases hf : st.env.size - 1 = f
  · subst hf
    simp only [if_true]
    have e : (st.env.modify (st.env.size - 1) popTop)[st.env.size - 1]? = some (popTop fr) := by
      simp only [Array.getElem?_modify, if_true, hfr, Option.map_some]
    rw [e, hfr]
    show some _ = some _
    dsimp only [Function.comp]
    congr 1
    apply List.ext_getElem?
    intro i
    simp only [popTop, Array.toList_pop, List.getElem?_map, List.getElem?_zipIdx, List.getElem?_dropLast,
      List.length_map, List.length_zipIdx, Array.length_toList]
    split
    · next hi =>
      cases fr.binds.toList[i]? with
      | none => rfl
      | some bi =>
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, and_true]
        simp only [Binding.refTy]
        rw [hintAt_popTop_ne K.dm K.M K.Γ ρ st.env fr hfr _ (by
          intro e; injection e with _ e2; omega)]
    · rfl
  · simp only [hf, if_false]
    have e : (st.env.modify (st.env.size - 1) popTop)[f]? = st.env[f]? := by
      simp only [Array.getElem?_modify, hf, if_false]
    rw [e]
    cases st.env[f]? with
    | none => rfl
    | some fr0 =>
      show some _ = some _
      dsimp only [Function.comp]
      congr 1
      apply List.map_congr_left
      intro x _
      simp only [Binding.refTy]
      rw [hintAt_popTop_ne K.dm K.M K.Γ ρ st.env fr hfr _ (by
        intro e; injection e with e1; exact hf (by omega))]

/-! ## No loan, no site -/

mutual
/-- A value with no loan or mark of `l` anywhere (`hasLoan`, which walks recorded readings) has no
site of `l`. -/
theorem sitesOf_nil_of_hasLoan (l : Nat) (pos : Pos) : ∀ (path : List Step) (v : Value),
    v.hasLoan l = false → v.sitesOf l pos path = []
  | path, .loan m, h => by
    simp only [Value.hasLoan, Value.anyAtom, Bool.or_false, beq_eq_false_iff_ne] at h
    simp [Value.sitesOf, h]
  | path, .gloan m w, h => by
    simp only [Value.hasLoan, Value.anyAtom, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at h
    simp only [Value.sitesOf, if_neg h.1]
    exact sitesOf_nil_of_hasLoan l pos path w h.2
  | path, .sealed t, h => by simp [Value.sitesOf, h]
  | path, .borrow _ w, h => by
    simp only [Value.hasLoan, Value.anyAtom, Bool.false_or] at h
    exact sitesOf_nil_of_hasLoan l pos _ w h
  | path, .succ w, h => by
    simp only [Value.hasLoan, Value.anyAtom, Bool.false_or] at h
    exact sitesOf_nil_of_hasLoan l pos _ w h
  | path, .ind ty c _ ps fs, h => by
    simp only [Value.hasLoan, Value.anyAtom, Bool.false_or, Bool.or_eq_false_iff] at h
    exact sitesOfFields_nil_of_hasLoan l pos path ty c 0 fs h.2
  | _, .zero, _ | _, .unit, _ | _, .gfn _, _ | _, .clo _ _ _, _ | _, .bot, _
  | _, .abs _, _ | _, .proof, _ | _, .tNat, _ | _, .tUnit, _ | _, .tEq _ _ _, _
  | _, .tRef _, _ | _, .tPi _ _ _, _ | _, .sort _, _ | _, .tInd _ _, _ => by
    simp [Value.sitesOf]

theorem sitesOfFields_nil_of_hasLoan (l : Nat) (pos : Pos) (path : List Step) (ty : String) (c : Nat) :
    ∀ (i : Nat) (ws : List Value),
      Value.anyAtomList (fun | .loan m | .gloan m _ => m == l | _ => false) ws = false →
      Value.sitesOfFields l pos path ty c i ws = []
  | _, [], _ => by simp [Value.sitesOfFields]
  | i, w :: ws, h => by
    simp only [Value.anyAtomList, Bool.or_eq_false_iff] at h
    simp only [Value.sitesOfFields]
    rw [sitesOf_nil_of_hasLoan l pos _ w h.1, sitesOfFields_nil_of_hasLoan l pos path ty c (i + 1) ws h.2]
    rfl
end

/-- With no loan or mark of `l` in a recorded reading (WF15's clause), `loans = []` excludes every
loan and mark of `l` (`SitesFollow.mem_loans_of_hasLoan`). -/
theorem hasLoan_false_of_loans_nil {v : Value} (hnl : v.loans = []) (l : Nat)
    (hrd : v.anyAtom (Value.rdLoan l) = false) : v.hasLoan l = false := by
  cases e : v.hasLoan l
  · rfl
  · have := mem_loans_of_hasLoan (by rw [rdHasLoan_eq]; exact hrd) e
    rw [hnl] at this; cases this

end Ochr.Meaning.Steps.Form

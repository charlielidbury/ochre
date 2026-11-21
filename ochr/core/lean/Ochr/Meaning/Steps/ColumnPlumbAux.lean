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
        fr.binds.toList.zipIdx.map (fun (b, i) => ((Env.hintAt K.dm K.M K.Γ ρ st.env (.bind f i)).m, b.decl))) := by
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
      rw [hintAt_pushBindE_ne K.dm K.M K.Γ ρ st.env h (some T) v pf d fr hfr _ (by
        intro e; injection e with _ e2; simp at hlt; omega)]
    · simp only [Nat.zero_add, Array.length_toList]
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

end Ochr.Meaning.Steps.Form

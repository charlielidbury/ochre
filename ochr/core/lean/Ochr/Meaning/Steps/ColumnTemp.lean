import Ochr.Meaning.Steps.FormKern
import Ochr.Meaning.Steps.JoinDropLib
import Ochr.Meaning.SitesFollow

/-!
# A number in flight (lead7, the column of `Steps/Form.lean`)

A value built of `Z` and `S` (`Value.Num`) holds no loan, no borrow, no unknown and no code: counting
it as a temporary of the checker's state changes nothing the relation, the context or the assignment
reads (`Rel.withTempT_num`, `Pre.withTempT_num`).
-/

namespace Ochr.Meaning.Steps.Form

open Ochr Ochr.Meaning Ochr.Meaning.Steps

/-- A value built of `Z` and `S`. -/
inductive _root_.Ochr.Value.Num : Value → Prop
  | zero : Value.Num .zero
  | succ {v : Value} : Value.Num v → Value.Num (.succ v)

theorem _root_.Ochr.Value.Num.anyAtom {v : Value} (h : v.Num) {P : Value → Bool} (h0 : P .zero = false)
    (hs : ∀ w, P (.succ w) = false) : v.anyAtom P = false := by
  induction h with
  | zero => simp [Value.anyAtom, h0]
  | succ _ ih => simp [Value.anyAtom, hs, ih]

theorem _root_.Ochr.Value.Num.hasAbs {v : Value} (h : v.Num) (σ : Nat) : v.hasAbs σ = false :=
  h.anyAtom (P := (· == .abs σ)) rfl fun _ => rfl

theorem _root_.Ochr.Value.Num.holdsBorrow {v : Value} (h : v.Num) (l : Nat) : v.holdsBorrow l = false := by
  induction h with
  | zero => rfl
  | succ _ ih => simpa [Value.holdsBorrow] using ih

theorem _root_.Ochr.Value.Num.sitesOf {v : Value} (h : v.Num) (l : Nat) (pos : Pos) (path : List Step) :
    v.sitesOf l pos path = [] := by
  induction h generalizing path with
  | zero => simp [Value.sitesOf]
  | succ _ ih => simp [Value.sitesOf, ih]

theorem _root_.Ochr.Value.Num.not_borrow {v : Value} (h : v.Num) : ∀ l w, v ≠ .borrow l w := by
  intro l w e; subst e; cases h

/-- **A value the relation tracks nothing of**: no unknown, no borrow held or named, no site, no
holder shape. Numbers (`Value.Num.inert`) and `()` (`Value.inert_unit`): what a step leaves in
flight without touching the relation's bookkeeping. -/
structure _root_.Ochr.Value.Inert (v : Value) : Prop where
  anyAtom : ∀ P : Value → Bool, P .zero = false → P .unit = false → (∀ w, P (.succ w) = false) → v.anyAtom P = false
  hasAbs : ∀ σ, v.hasAbs σ = false
  holdsBorrow : ∀ l, v.holdsBorrow l = false
  sitesOf : ∀ l pos path, v.sitesOf l pos path = []
  shape : shapeOf v = none

theorem _root_.Ochr.Value.Num.inert {v : Value} (h : v.Num) : v.Inert :=
  ⟨fun _ h0 _ hs => h.anyAtom h0 hs, h.hasAbs, h.holdsBorrow, h.sitesOf, by cases h <;> rfl⟩

theorem _root_.Ochr.Value.inert_unit : Value.Inert .unit :=
  ⟨fun _ _ hu _ => by simp [Value.anyAtom, hu], fun _ => rfl, fun _ => rfl, fun _ _ _ => by simp [Value.sitesOf], rfl⟩

/-! ## The checker's environment with a temporary pushed -/

/-- `withTemp` and `withTempT` have one environment up to the temporaries' types. -/
theorem erase_withTemp (st : MState) (v : Value) (T? : Option Value) :
    (st.withTemp v).env.erase = (st.withTempT v T?).env.erase := by
  rw [erase_withTempT]
  apply Array.ext_getElem?
  intro f
  simp only [MState.withTemp, Env.erase_get?, Array.getElem?_modify, Env.erase_size]
  split <;> cases st.env[f]? <;> rfl

theorem valAt_pushTempE_bind (env : Env) (v : Value) (f i : Nat) :
    valAt (Env.pushTempE env v) (.bind f i) = valAt env (.bind f i) := by
  rw [valAt_bind_eq, valAt_bind_eq]
  simp only [Env.pushTempE, Array.getElem?_modify]
  split <;> cases env[f]? <;> rfl

theorem valAt_pushTempE_old (env : Env) (v : Value) (fr : Frame) (hfr : env[env.size - 1]? = some fr)
    (f i : Nat) (hq : Pos.temp f i ≠ .temp (env.size - 1) fr.temps.size) :
    valAt (Env.pushTempE env v) (.temp f i) = valAt env (.temp f i) := by
  rw [valAt_temp_eq, valAt_temp_eq]
  simp only [Env.pushTempE, Array.getElem?_modify]
  by_cases hf : env.size - 1 = f
  · subst hf
    simp only [if_true, hfr, Option.map_some, Option.getD_some]
    have hi : i ≠ fr.temps.size := fun h => hq (by subst h; rfl)
    rw [Array.getElem?_push]; simp only [hi, if_false]
  · simp only [hf, if_false]

theorem valAt_pushTempE_new (env : Env) (v : Value) (fr : Frame) (hfr : env[env.size - 1]? = some fr) :
    valAt (Env.pushTempE env v) (.temp (env.size - 1) fr.temps.size) = v := by
  rw [valAt_temp_eq]
  simp only [Env.pushTempE, Array.getElem?_modify, if_true, hfr, Option.map_some, Option.getD_some]
  simp

theorem values_pushTempE (env : Env) (v : Value) (fr : Frame) (hfr : env[env.size - 1]? = some fr)
    (hne : 0 < env.size) : Env.values (Env.pushTempE env v) = Env.values env ++ [v] := by
  simp only [Env.values]
  rw [allPos_pushTempE env v fr hfr hne, List.map_append, List.map_singleton, valAt_pushTempE_new env v fr hfr]
  congr 1
  apply List.map_congr_left
  intro q hq
  cases q with
  | bind f i => exact valAt_pushTempE_bind env v f i
  | temp f i =>
    apply valAt_pushTempE_old env v fr hfr f i
    intro e
    cases e
    obtain ⟨fr', hf', hi⟩ := mem_allPos_temp env _ _ hq
    rw [hfr] at hf'; cases hf'
    exact absurd hi (Nat.lt_irrefl _)

theorem shape_pushTempE_bind (env : Env) (v : Value) (f i : Nat) :
    Env.shape (Env.pushTempE env v) (.bind f i) = Env.shape env (.bind f i) := by
  simp only [Env.shape, valAt_pushTempE_bind]

theorem find?_congr_mem {α : Type _} {p q : α → Bool} :
    ∀ (l : List α), (∀ x ∈ l, p x = q x) → l.find? p = l.find? q
  | [], _ => rfl
  | a :: l, h => by
    have ha := h a (List.mem_cons_self ..)
    have ih := find?_congr_mem l (fun x hx => h x (List.mem_cons_of_mem _ hx))
    cases hp : p a <;> simp [List.find?_cons, hp, ← ha, ih]

theorem findBorrow_pushTempE (env : Env) (v : Value) (fr : Frame) (hfr : env[env.size - 1]? = some fr)
    (hne : 0 < env.size) (l : Nat) (hv : v.holdsBorrow l = false) :
    findBorrow (Env.pushTempE env v) l = findBorrow env l := by
  simp only [findBorrow]
  rw [allPos_pushTempE env v fr hfr hne, List.find?_append]
  have e : (allPos env).find? (fun p => (valAt (Env.pushTempE env v) p).holdsBorrow l) =
      (allPos env).find? (fun p => (valAt env p).holdsBorrow l) := by
    apply find?_congr_mem
    intro q hq
    cases q with
    | bind f i => rw [valAt_pushTempE_bind]
    | temp f i =>
      rw [valAt_pushTempE_old env v fr hfr f i]
      intro e; cases e
      obtain ⟨fr', hf', hi⟩ := mem_allPos_temp env _ _ hq
      rw [hfr] at hf'; cases hf'
      exact absurd hi (Nat.lt_irrefl _)
  rw [e]
  cases (allPos env).find? (fun p => (valAt env p).holdsBorrow l) with
  | some p => rfl
  | none => simp [valAt_pushTempE_new env v fr hfr, hv]

theorem sitesOf_pushTempE (env : Env) (v : Value) (fr : Frame) (hfr : env[env.size - 1]? = some fr)
    (hne : 0 < env.size) (hv : v.Inert) (l : Nat) : Env.sitesOf (Env.pushTempE env v) l = Env.sitesOf env l := by
  simp only [Env.sitesOf]
  rw [allPos_pushTempE env v fr hfr hne, List.flatMap_append, List.flatMap_singleton,
    valAt_pushTempE_new env v fr hfr, hv.sitesOf, List.append_nil]
  apply flatMap_congr_mem
  intro q hq
  cases q with
  | bind f i => rw [valAt_pushTempE_bind]
  | temp f i =>
    rw [valAt_pushTempE_old env v fr hfr f i]
    intro e; cases e
    obtain ⟨fr', hf', hi⟩ := mem_allPos_temp env _ _ hq
    rw [hfr] at hf'; cases hf'
    exact absurd hi (Nat.lt_irrefl _)

section
variable (K : RunCtx) (ρ : Assignment)

/-- The skeleton of the checker's state read as a reference state is unchanged by a temporary. -/
theorem skel_pushTempE (st : MState) (v : Value) :
    (SM' K ρ { st with env := Env.pushTempE st.env v }).env.map (fun fr => fr.binds.map bindSkel) =
      (SM' K ρ st).env.map (fun fr => fr.binds.map bindSkel) := by
  apply List.ext_getElem?
  intro f'
  simp only [SM', MState.sstate, List.getElem?_map, List.getElem?_zipIdx, Option.map_map,
    Array.getElem?_toList, hintAt_pushTempE]
  simp only [Env.pushTempE, Array.getElem?_modify]
  by_cases hf : st.env.size - 1 = f'
  · subst hf
    rcases st.env[st.env.size - 1]? with _ | fr
    · simp
    · simp only [if_true, Option.map_some, Function.comp_apply, List.map_map]; rfl
  · simp only [hf, if_false]
    rcases st.env[f']? with _ | fr
    · rfl
    · simp only [Option.map_some, Function.comp_apply, List.map_map]; rfl

end

/-- **An inert value in flight keeps the relation.** -/
theorem rel_withTemp_inert {K : RunCtx} {ρ : Assignment} {φ : Future} {π : Nat → Nat} {st : MState} {s : SState}
    (hr : Rel K ρ φ π st s) {v : Value} (hv : v.Inert) : Rel K ρ φ π (st.withTemp v) s := by
  rcases hfr : st.env[st.env.size - 1]? with _ | fr
  · -- no frame: nothing is pushed
    have he : (st.withTemp v).env = st.env := by
      simp only [MState.withTemp]
      apply Array.ext_getElem?
      intro f
      rw [Array.getElem?_modify]
      split
      · next h => subst h; rw [hfr]; rfl
      · rfl
    exact hr.of_env he rfl
  have hne : 0 < st.env.size := by
    rcases Nat.eq_zero_or_pos st.env.size with h | h
    · have : st.env[st.env.size - 1]? = none := Array.getElem?_eq_none (by omega)
      rw [this] at hfr; cases hfr
    · exact h
  have henv : (st.withTemp v).env = Env.pushTempE st.env v := rfl
  have hnew : ∀ f i, Pos.temp f i = .temp (st.env.size - 1) fr.temps.size → Env.shape (st.withTemp v).env (.temp f i) = none := by
    intro f i e; cases e
    simp only [henv, Env.shape, valAt_pushTempE_new st.env v fr hfr]
    exact hv.shape
  refine ⟨?_, ?_, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, hr.holders, hr.records, hr.uniq⟩
  · show (SM' K ρ { st with env := Env.pushTempE st.env v }).env.map _ = _
    rw [skel_pushTempE]; exact hr.skel
  · intro l hl ho
    apply hr.fresh l hl
    obtain ⟨w, hw, ha⟩ := ho
    rw [henv, values_pushTempE st.env v fr hfr hne, List.mem_append] at hw
    rcases hw with hw | hw
    · exact ⟨w, hw, ha⟩
    · simp only [List.mem_singleton] at hw; subst hw
      rw [hv.anyAtom _ (by rfl) (by rfl) (fun _ => by rfl)] at ha; cases ha
  · intro ψ hψ p hp
    cases p with
    | temp => exact absurd trivial hp
    | bind f i =>
      show Env.mean K.dm K.M K.Γ ρ _ (st.withTemp v).env (.bind f i) = _
      rw [henv, mean_pushTempE_other K.dm K.M K.Γ ρ st.env v fr hfr _ _ (by intro e; cases e)]
      exact hr.sim.1 ψ hψ (.bind f i) hp
  · intro p l hp h
    cases p with
    | temp => exact absurd trivial hp
    | bind f i =>
      have h' : Env.shape st.env (.bind f i) = some l := by rw [← shape_pushTempE_bind st.env v]; exact h
      exact hr.sim.2.1 _ l hp h'
  · intro p l' hp h
    cases p with
    | temp => exact absurd trivial hp
    | bind f i =>
      obtain ⟨l, h1, h2⟩ := hr.sim.2.2.1 _ l' hp h
      exact ⟨l, by show Env.shape (Env.pushTempE st.env v) _ = _; rw [shape_pushTempE_bind]; exact h1, h2⟩
  · intro f i l h
    by_cases e : Pos.temp f i = .temp (st.env.size - 1) fr.temps.size
    · change Env.shape (st.withTemp v).env (.temp f i) = some l at h
      rw [hnew f i e] at h; cases h
    · have h' : Env.shape st.env (.temp f i) = some l := by
        have : Env.shape (Env.pushTempE st.env v) (.temp f i) = some l := h
        simp only [Env.shape, valAt_pushTempE_old st.env v fr hfr f i e] at this
        exact this
      obtain ⟨j, hj, hjv⟩ := hr.sim.2.2.2.1 f i l h'
      refine ⟨j, hj, fun ψ hψ => ?_⟩
      show Env.mean K.dm K.M K.Γ ρ _ (Env.pushTempE st.env v) (.temp f i) = _
      rw [mean_pushTempE_other K.dm K.M K.Γ ρ st.env v fr hfr _ _ e]
      exact hjv ψ hψ
  · intro f j l' h
    obtain ⟨i, l, h1, h2⟩ := hr.sim.2.2.2.2 f j l' h
    refine ⟨i, l, ?_, h2⟩
    have e : Pos.temp f i ≠ .temp (st.env.size - 1) fr.temps.size := by
      intro e
      have := mem_allPos_of_shape h1
      cases e
      obtain ⟨fr', hf', hi⟩ := mem_allPos_temp st.env _ _ this
      rw [hfr] at hf'; cases hf'
      exact absurd hi (Nat.lt_irrefl _)
    show Env.shape (Env.pushTempE st.env v) _ = _
    simp only [Env.shape, valAt_pushTempE_old st.env v fr hfr f i e]
    exact h1
  · intro l l' hl hl' hπ
    rw [henv] at hl hl'
    simp only [liveLoan, findBorrow_pushTempE st.env v fr hfr hne _ (hv.holdsBorrow _)] at hl hl'
    exact hr.inj l l' hl hl' hπ
  · intro l hl x
    rw [henv] at hl ⊢
    simp only [liveLoan, findBorrow_pushTempE st.env v fr hfr hne _ (hv.holdsBorrow _)] at hl
    rw [sitesOf_pushTempE st.env v fr hfr hne hv]
    exact hr.sites l hl x

/-- `withTemp` and `withTempT` of one state have one kernel. -/
theorem kern_withTemp (st : MState) (v : Value) (T? : Option Value) : Kern (st.withTemp v) (st.withTempT v T?) :=
  ⟨erase_withTemp st v T?, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem rel_withTemp_num {K : RunCtx} {ρ : Assignment} {φ : Future} {π : Nat → Nat} {st : MState} {s : SState}
    (hr : Rel K ρ φ π st s) {v : Value} (hv : v.Num) : Rel K ρ φ π (st.withTemp v) s :=
  rel_withTemp_inert hr hv.inert

theorem rel_withTempT_inert {K : RunCtx} {ρ : Assignment} {φ : Future} {π : Nat → Nat} {st : MState} {s : SState}
    (hr : Rel K ρ φ π st s) {v : Value} (hv : v.Inert) (T? : Option Value) : Rel K ρ φ π (st.withTempT v T?) s :=
  Rel.of_kern (kern_withTemp st v T?) (rel_withTemp_inert hr hv)

theorem rel_withTempT_num {K : RunCtx} {ρ : Assignment} {φ : Future} {π : Nat → Nat} {st : MState} {s : SState}
    (hr : Rel K ρ φ π st s) {v : Value} (hv : v.Num) (T? : Option Value) : Rel K ρ φ π (st.withTempT v T?) s :=
  rel_withTempT_inert hr hv.inert T?

/-! ## The context and the assignment -/

/-- The context's part a step does not change reads only Σ and the declarations. -/
theorem CtxS.of_eq {K : RunCtx} {st st' : MState} (h : CtxS K st) (hi : st'.inds = st.inds)
    (hg : st'.globals = st.globals) : CtxS K st' :=
  ⟨h.inds.trans hi.symm, h.covers, h.faithful, h.noLabel, h.globals.of_globals hg⟩

/-- The assignment's facts carry to a state with the same Δ, records and goal that names no more
unknowns. -/
theorem Asg.of_refd {K : RunCtx} {ρ : Assignment} {st st' : MState} (h : Asg K ρ st)
    (ha : st'.absTy = st.absTy) (hn : st'.neutrals = st.neutrals) (he : st'.etaRefs = st.etaRefs)
    (hr : st'.refs = st.refs) (hg : st'.goal = st.goal) (hR : ∀ σ, st'.Refd σ → st.Refd σ) : Asg K ρ st' := by
  have eA : ∀ σ, MState.absTyM K.dm K.M K.Γ ρ st' σ = MState.absTyM K.dm K.M K.Γ ρ st σ := fun σ => by
    simp only [MState.absTyM, ha]
  have eG : MState.goalM K.dm K.M K.Γ ρ st' = MState.goalM K.dm K.M K.Γ ρ st := by simp only [MState.goalM, hg]
  have eD : deltaOf K ρ st' = deltaOf K ρ st := by funext σ; simp only [deltaOf, ha]
  obtain ⟨⟨hm, hne, het, hrf⟩, hlv, hglv, hd⟩ := h
  refine ⟨⟨fun σ hσ hlt => ?_, fun n σ hmem => ?_, fun σ w hmem => ?_, fun σ r hmem => ?_⟩,
    fun σ hσ hlt => ?_, fun G hG => ?_, fun σ hσ hlt => ?_⟩
  · rw [eA]; rw [ha] at hlt; exact hm σ (hR σ hσ) hlt
  · rw [eA]; rw [hn] at hmem; exact hne n σ hmem
  · rw [eA]; rw [he] at hmem; exact het σ w hmem
  · rw [eA]; rw [hr] at hmem; exact hrf σ r hmem
  · rw [eA]; rw [ha] at hlt; exact hlv σ (hR σ hσ) hlt
  · rw [eG] at hG; exact hglv G hG
  · rw [eD]; rw [ha] at hlt; exact hd σ (hR σ hσ) hlt

theorem binds_withTempT_norm (st : MState) (v : Value) (T? : Option Value) (f i : Nat) :
    (st.withTempT v T?).norm.env[f]?.bind (·.binds[i]?) = st.norm.env[f]?.bind (·.binds[i]?) := by
  simp only [MState.norm, MState.withTempT, Env.erase_get?, Array.getElem?_modify]
  split <;> cases st.env[f]? <;> rfl

theorem values_withTempT_norm (st : MState) (v : Value) (T? : Option Value) (w : Value)
    (hw : w ∈ Env.values (st.withTempT v T?).norm.env) : w ∈ Env.values st.norm.env ∨ w = v := by
  have e1 : Env.values (st.withTempT v T?).norm.env = Env.values (Env.pushTempE st.env v) := by
    show Env.values (st.withTempT v T?).env.erase = _
    rw [← erase_withTemp st v T?, values_erase]; rfl
  have e2 : Env.values st.norm.env = Env.values st.env := values_erase st.env
  rw [e1] at hw; rw [e2]
  rcases hfr : st.env[st.env.size - 1]? with _ | fr
  · left
    have he : Env.pushTempE st.env v = st.env := by
      simp only [Env.pushTempE]
      apply Array.ext_getElem?
      intro f
      rw [Array.getElem?_modify]
      split
      · next h => subst h; rw [hfr]; rfl
      · rfl
    rw [he] at hw; exact hw
  · have hne : 0 < st.env.size := by
      rcases Nat.eq_zero_or_pos st.env.size with h | h
      · have : st.env[st.env.size - 1]? = none := Array.getElem?_eq_none (by omega)
        rw [this] at hfr; cases hfr
      · exact h
    rw [values_pushTempE st.env v fr hfr hne, List.mem_append, List.mem_singleton] at hw
    exact hw

/-- A number in flight names no unknown. -/
theorem refd_withTempT_inert {st : MState} {v : Value} (hv : v.Inert) (T? : Option Value) :
    ∀ σ, (st.withTempT v T?).norm.Refd σ → st.norm.Refd σ := by
  intro σ h
  induction h with
  | val w hw hab =>
    rcases values_withTempT_norm st v T? w hw with hw | rfl
    · exact .val w hw hab
    · rw [hv.hasAbs] at hab; cases hab
  | ty f i b T hb hT hab =>
    rw [binds_withTempT_norm] at hb
    exact .ty f i b T hb hT hab
  | lazyTy f i b P ws j hb hT hab =>
    rw [binds_withTempT_norm] at hb
    exact .lazyTy f i b P ws j hb hT hab
  | goal G hG hab => exact .goal G hG hab
  | neutral n σ' hn hab => exact .neutral n σ' hn hab
  | eta σ' w he hab => exact .eta σ' w he hab
  | dep σ' T _ hT hab ih => exact .dep σ' T ih hT hab

/-- **A number in flight keeps the assignment's facts.** -/
theorem refd_withTempT_num {st : MState} {v : Value} (hv : v.Num) (T? : Option Value) :
    ∀ σ, (st.withTempT v T?).norm.Refd σ → st.norm.Refd σ :=
  refd_withTempT_inert hv.inert T?

theorem asg_withTempT_inert {K : RunCtx} {ρ : Assignment} {st : MState} (h : Asg K ρ st.norm) {v : Value}
    (hv : v.Inert) (T? : Option Value) : Asg K ρ (st.withTempT v T?).norm :=
  h.of_refd rfl rfl rfl rfl rfl (refd_withTempT_inert hv T?)

theorem asg_withTempT_num {K : RunCtx} {ρ : Assignment} {st : MState} (h : Asg K ρ st.norm) {v : Value}
    (hv : v.Num) (T? : Option Value) : Asg K ρ (st.withTempT v T?).norm :=
  asg_withTempT_inert h hv.inert T?

/-- **Removing a number in flight keeps the relation** (the converse of `rel_withTemp_num`). -/
theorem rel_of_withTemp_inert {K : RunCtx} {ρ : Assignment} {φ : Future} {π : Nat → Nat} {st : MState} {s : SState}
    {v : Value} (hv : v.Inert) (hr : Rel K ρ φ π (st.withTemp v) s) : Rel K ρ φ π st s := by
  rcases hfr : st.env[st.env.size - 1]? with _ | fr
  · have he : (st.withTemp v).env = st.env := by
      simp only [MState.withTemp]
      apply Array.ext_getElem?
      intro f
      rw [Array.getElem?_modify]
      split
      · next h => subst h; rw [hfr]; rfl
      · rfl
    exact hr.of_env he.symm rfl
  have hne : 0 < st.env.size := by
    rcases Nat.eq_zero_or_pos st.env.size with h | h
    · have : st.env[st.env.size - 1]? = none := Array.getElem?_eq_none (by omega)
      rw [this] at hfr; cases hfr
    · exact h
  have henv : (st.withTemp v).env = Env.pushTempE st.env v := rfl
  have hold : ∀ f i, Pos.temp f i ∈ allPos st.env → Pos.temp f i ≠ .temp (st.env.size - 1) fr.temps.size := by
    intro f i hq e; cases e
    obtain ⟨fr', hf', hi⟩ := mem_allPos_temp st.env _ _ hq
    rw [hfr] at hf'; cases hf'
    exact absurd hi (Nat.lt_irrefl _)
  have hsk := hr.skel
  have hsim := hr.sim
  refine ⟨?_, ?_, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, hr.holders, hr.records, hr.uniq⟩
  · have : (SM' K ρ { st with env := Env.pushTempE st.env v }).env.map (fun fr => fr.binds.map bindSkel) = _ := hsk
    rw [skel_pushTempE] at this; exact this
  · intro l hl ho
    apply hr.fresh l hl
    obtain ⟨w, hw, ha⟩ := ho
    exact ⟨w, by rw [henv, values_pushTempE st.env v fr hfr hne]; exact List.mem_append_left _ hw, ha⟩
  · intro ψ hψ p hp
    cases p with
    | temp => exact absurd trivial hp
    | bind f i =>
      have := hsim.1 ψ hψ (.bind f i) hp
      show Env.mean K.dm K.M K.Γ ρ _ st.env (.bind f i) = _
      rw [← this]
      show _ = Env.mean K.dm K.M K.Γ ρ _ (Env.pushTempE st.env v) (.bind f i)
      rw [mean_pushTempE_other K.dm K.M K.Γ ρ st.env v fr hfr _ _ (by intro e; cases e)]
  · intro p l hp h
    cases p with
    | temp => exact absurd trivial hp
    | bind f i =>
      apply hsim.2.1 _ l hp
      show Env.shape (Env.pushTempE st.env v) _ = _
      rw [shape_pushTempE_bind]; exact h
  · intro p l' hp h
    cases p with
    | temp => exact absurd trivial hp
    | bind f i =>
      obtain ⟨l, h1, h2⟩ := hsim.2.2.1 _ l' hp h
      refine ⟨l, ?_, h2⟩
      have : Env.shape (Env.pushTempE st.env v) (.bind f i) = some l := h1
      rw [shape_pushTempE_bind] at this; exact this
  · intro f i l h
    have hq := mem_allPos_of_shape h
    have e := hold f i hq
    have h' : Env.shape (Env.pushTempE st.env v) (.temp f i) = some l := by
      simp only [Env.shape, valAt_pushTempE_old st.env v fr hfr f i e]; exact h
    obtain ⟨j, hj, hjv⟩ := hsim.2.2.2.1 f i l h'
    refine ⟨j, hj, fun ψ hψ => ?_⟩
    rw [← hjv ψ hψ]
    show Env.mean K.dm K.M K.Γ ρ _ st.env (.temp f i) = Env.mean K.dm K.M K.Γ ρ _ (Env.pushTempE st.env v) (.temp f i)
    rw [mean_pushTempE_other K.dm K.M K.Γ ρ st.env v fr hfr _ _ e]
  · intro f j l' h
    obtain ⟨i, l, h1, h2⟩ := hsim.2.2.2.2 f j l' h
    refine ⟨i, l, ?_, h2⟩
    have h1' : Env.shape (Env.pushTempE st.env v) (.temp f i) = some l := h1
    by_cases e : Pos.temp f i = .temp (st.env.size - 1) fr.temps.size
    · cases e
      simp only [Env.shape, valAt_pushTempE_new st.env v fr hfr] at h1'
      cases (h1'.symm.trans hv.shape)
    · simp only [Env.shape, valAt_pushTempE_old st.env v fr hfr f i e] at h1'
      exact h1'
  · intro l l' hl hl' hπ
    apply hr.inj l l'
    · show liveLoan (Env.pushTempE st.env v) l = true
      simp only [liveLoan, findBorrow_pushTempE st.env v fr hfr hne _ (hv.holdsBorrow _)]; exact hl
    · show liveLoan (Env.pushTempE st.env v) l' = true
      simp only [liveLoan, findBorrow_pushTempE st.env v fr hfr hne _ (hv.holdsBorrow _)]; exact hl'
    · exact hπ
  · intro l hl x
    have hl' : liveLoan (Env.pushTempE st.env v) l = true := by
      simp only [liveLoan, findBorrow_pushTempE st.env v fr hfr hne _ (hv.holdsBorrow _)]; exact hl
    have := hr.sites l hl' x
    rw [show Env.sitesOf (st.withTemp v).env l = Env.sitesOf st.env l from sitesOf_pushTempE st.env v fr hfr hne hv l] at this
    exact this

theorem rel_of_withTemp_num {K : RunCtx} {ρ : Assignment} {φ : Future} {π : Nat → Nat} {st : MState} {s : SState}
    {v : Value} (hv : v.Num) (hr : Rel K ρ φ π (st.withTemp v) s) : Rel K ρ φ π st s :=
  rel_of_withTemp_inert hv.inert hr

theorem rel_of_withTempT_inert {K : RunCtx} {ρ : Assignment} {φ : Future} {π : Nat → Nat} {st : MState} {s : SState}
    {v : Value} (hv : v.Inert) {T? : Option Value} (hr : Rel K ρ φ π (st.withTempT v T?) s) : Rel K ρ φ π st s :=
  rel_of_withTemp_inert hv (Rel.of_kern (kern_withTemp st v T?).symm hr)

theorem rel_of_withTempT_num {K : RunCtx} {ρ : Assignment} {φ : Future} {π : Nat → Nat} {st : MState} {s : SState}
    {v : Value} (hv : v.Num) {T? : Option Value} (hr : Rel K ρ φ π (st.withTempT v T?) s) : Rel K ρ φ π st s :=
  rel_of_withTempT_inert hv.inert hr

/-- A number means a number, at every context, assignment, future and hint. -/
theorem _root_.Ochr.Value.Num.mean {v : Value} (hv : v.Num) :
    ∃ m : Nat, ∀ (K : RunCtx) (ρ : Assignment) (φ : Future) (hint : TyS), meanV K ρ φ hint v = .el0 Nat m := by
  induction hv with
  | zero => exact ⟨0, fun _ _ _ _ => rfl⟩
  | succ _ ih =>
    obtain ⟨m, hm⟩ := ih
    refine ⟨m + 1, fun K ρ φ hint => ?_⟩
    show (meanV K ρ φ (.plain TyM.nat) _).succ = _
    rw [hm, Sem.succ, Sem.asNat_el0]

end Ochr.Meaning.Steps.Form

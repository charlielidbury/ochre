import Ochr.Meaning.Steps.Machine.InvPos
import Ochr.Meaning.Steps.Machine.PlaceLocal

/-!
# The state-level lemmas of `InvSteps` (machine lane)

Each is "`Inv` before, the exact change, `Inv` after", by `inv_of_posRel` (the change keeps the
positions up to simple values) with the readings' two clauses per change.
-/

namespace Ochr.Meaning.Steps.Machine

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.DecideScope
open Ochr.Meaning.Steps.Form

/-! ## A temporary pushed or popped -/

section PushTemp
variable (E : Env) (v : Value)

theorem binds_pushTempE (f i : Nat) :
    (Env.pushTempE E v)[f]?.bind (fun fr : Frame => fr.binds[i]?) = E[f]?.bind (fun fr : Frame => fr.binds[i]?) := by
  simp only [Env.pushTempE, Array.getElem?_modify]
  split <;> cases E[f]? <;> rfl

theorem size_pushTempE : (Env.pushTempE E v).size = E.size := by simp [Env.pushTempE]

theorem topBinds_pushTempE : (Env.pushTempE E v)[(Env.pushTempE E v).size - 1]!.binds = E[E.size - 1]!.binds := by
  rw [size_pushTempE]
  simp only [Env.pushTempE, getElem!_def, Array.getElem?_modify, if_true]
  cases E[E.size - 1]? <;> rfl

theorem back_pushTempE : (Env.pushTempE E v).back?.map (fun fr : Frame => fr.binds.toList.map (·.decl)) =
    E.back?.map (fun fr : Frame => fr.binds.toList.map (·.decl)) := by
  simp only [Array.back?]
  rw [size_pushTempE]
  simp only [Env.pushTempE, Array.getElem?_modify, if_true]
  cases E[E.size - 1]? <;> rfl

theorem ckVarPos_pushTempE (i : Nat) : ckVarPos (Env.pushTempE E v) i = ckVarPos E i := by
  unfold ckVarPos; rw [topBinds_pushTempE, size_pushTempE]

theorem ckContent_pushTempE (p : Place) : ckContent (Env.pushTempE E v) p = ckContent E p := by
  unfold ckContent; rw [ckVarPos_pushTempE]; unfold ckVarPos; split
  · simp only [Option.bind_some, valAt_pushTempE_bind]
  · rfl

theorem valAt_pushTempE_mem (fr : Frame) (hfr : E[E.size - 1]? = some fr) {q : Pos} (hq : q ∈ allPos E) :
    valAt (Env.pushTempE E v) q = valAt E q := by
  cases q with
  | bind f i => exact valAt_pushTempE_bind E v f i
  | temp f i =>
    refine valAt_pushTempE_old E v fr hfr f i fun e => ?_
    cases e
    obtain ⟨fr', hf', hi⟩ := mem_allPos_temp E _ _ hq
    rw [hfr] at hf'; cases hf'
    exact absurd hi (Nat.lt_irrefl _)

theorem posRel_pushTemp (fr : Frame) (hfr : E[E.size - 1]? = some fr) (hne : 0 < E.size) (hv : v.Bland) :
    PosRel E (Env.pushTempE E v) id where
  fwd p hp := by
    rw [allPos_pushTempE E v fr hfr hne, List.mem_append, List.mem_singleton] at hp
    rcases hp with hp | rfl
    · exact .inr ⟨hp, .inl (valAt_pushTempE_mem E v fr hfr hp).symm, .inl rfl⟩
    · exact .inl (by rw [valAt_pushTempE_new E v fr hfr]; exact hv)
  bwd q hq := .inr ⟨q, by rw [allPos_pushTempE E v fr hfr hne]; exact List.mem_append_left _ hq, rfl,
    .inl (valAt_pushTempE_mem E v fr hfr hq).symm⟩
  inj _ _ _ _ h := h

theorem posRel_popTemp (fr : Frame) (hfr : E[E.size - 1]? = some fr) (hne : 0 < E.size) (hv : v.Bland) :
    PosRel (Env.pushTempE E v) E id where
  fwd p hp := .inr ⟨by rw [allPos_pushTempE E v fr hfr hne]; exact List.mem_append_left _ hp,
    .inl (valAt_pushTempE_mem E v fr hfr hp), .inl rfl⟩
  bwd q hq := by
    rw [allPos_pushTempE E v fr hfr hne, List.mem_append, List.mem_singleton] at hq
    rcases hq with hq | rfl
    · exact .inr ⟨q, hq, rfl, .inl (valAt_pushTempE_mem E v fr hfr hq)⟩
    · exact .inl (by rw [valAt_pushTempE_new E v fr hfr]; exact hv)
  inj _ _ _ _ h := h

theorem pushTempE_of_empty (h : E.size = 0) : Env.pushTempE E v = E := by
  have : E = #[] := Array.eq_empty_of_size_eq_zero h
  subst this; rfl

end PushTemp

theorem tabSame_env (s : MState) (e : Env) : TabSame s { s with env := e } :=
  ⟨Nat.le_refl _, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem tabSame_env' (s : MState) (e : Env) : TabSame { s with env := e } s :=
  ⟨Nat.le_refl _, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- A bland temporary pushed keeps `Inv`, and popped too. -/
theorem inv_pushTemp {D : Decisions} {Γ : List IndDecl} {s : MState} {v : Value} (hv : v.Bland) :
    Inv D Γ s ↔ Inv D Γ { s with env := Env.pushTempE s.env v } := by
  by_cases h0 : s.env.size = 0
  · rw [pushTempE_of_empty _ _ h0]
  obtain ⟨fr, hfr⟩ : ∃ fr, s.env[s.env.size - 1]? = some fr :=
    ⟨_, Array.getElem?_eq_getElem (Nat.sub_lt (Nat.pos_of_ne_zero h0) Nat.one_pos)⟩
  have hne := Nat.pos_of_ne_zero h0
  have hR : topReadings { s with env := Env.pushTempE s.env v } = topReadings s := by
    unfold topReadings; exact congrArg (fun x => (x.getD []).reverse) (back_pushTempE s.env v)
  constructor
  · intro hi
    obtain ⟨hf, hp⟩ := readClauses_of (b := { s with env := Env.pushTempE s.env v }) hi hR
      (fun p w h => .inl (by rw [← ckContent_pushTempE s.env v]; exact h))
    exact inv_of_posRel hi (posRel_pushTemp s.env v fr hfr hne hv) (tabSame_env _ _)
      (fun f i bb h => .inl ⟨f, i, bb, by rw [← binds_pushTempE s.env v]; exact h, rfl, rfl⟩) hf hp
  · intro hi
    obtain ⟨hf, hp⟩ := readClauses_of (b := s) hi hR.symm
      (fun p w h => .inl (by rw [ckContent_pushTempE s.env v]; exact h))
    exact inv_of_posRel hi (posRel_popTemp s.env v fr hfr hne hv) (tabSame_env' _ _)
      (fun f i bb h => .inl ⟨f, i, bb, by rw [binds_pushTempE s.env v]; exact h, rfl, rfl⟩) hf hp

theorem invPushInert : InvPushInert := by
  intro D Γ st v T? hv hi
  rw [norm_withTempT]
  exact (inv_pushTemp (hv.elim (fun h => .inl h) (fun h => .inr (.inl h)))).mp hi

theorem invPopInert : InvPopInert := by
  intro D Γ st v T? hv hi
  rw [norm_withTempT] at hi
  exact (inv_pushTemp (hv.elim (fun h => .inl h) (fun h => .inr (.inl h)))).mpr hi

/-! ## A binding's value written -/

section SetAt
variable (E : Env) (f j : Nat) (w : Value)

theorem size_setAtE : (Env.setAtE E (.bind f j) w).size = E.size := by simp [Env.setAtE]

theorem frame_setAtE (k : Nat) : (Env.setAtE E (.bind f j) w)[k]? =
    E[k]?.map (fun fr => if f = k then { fr with binds := fr.binds.modify j ({ · with val := w }) } else fr) := by
  simp only [Env.setAtE, Array.getElem?_modify]
  split <;> cases E[k]? <;> simp_all

theorem decls_modify_val (bs : Array Binding) :
    (bs.modify j ({ · with val := w })).toList.map (·.decl) = bs.toList.map (·.decl) := by
  apply List.ext_getElem?
  intro n
  simp only [List.getElem?_map, Array.getElem?_toList, Array.getElem?_modify]
  split <;> cases bs[n]? <;> rfl

theorem back_setAtE : (Env.setAtE E (.bind f j) w).back?.map (fun fr : Frame => fr.binds.toList.map (·.decl)) =
    E.back?.map (fun fr : Frame => fr.binds.toList.map (·.decl)) := by
  simp only [Array.back?]
  rw [size_setAtE, frame_setAtE]
  cases E[E.size - 1]? with
  | none => rfl
  | some fr =>
    simp only [Option.map_some]
    split
    · exact congrArg some (decls_modify_val j w fr.binds)
    · rfl

theorem topBindsSize_setAtE : (Env.setAtE E (.bind f j) w)[(Env.setAtE E (.bind f j) w).size - 1]!.binds.size =
    E[E.size - 1]!.binds.size := by
  rw [size_setAtE, getElem!_def, getElem!_def, frame_setAtE]
  cases E[E.size - 1]? with
  | none => rfl
  | some fr => simp only [Option.map_some]; split <;> simp

theorem ckVarPos_setAtE (i : Nat) : ckVarPos (Env.setAtE E (.bind f j) w) i = ckVarPos E i := by
  unfold ckVarPos; rw [topBindsSize_setAtE, size_setAtE]

theorem binds_setAtE_from {k i : Nat} {bb : Binding}
    (h : (Env.setAtE E (.bind f j) w)[k]?.bind (fun fr : Frame => fr.binds[i]?) = some bb) :
    ∃ ba, E[k]?.bind (fun fr : Frame => fr.binds[i]?) = some ba ∧ ba.ty = bb.ty ∧ ba.lazyTy = bb.lazyTy := by
  rw [frame_setAtE] at h
  cases hk : E[k]? with
  | none => rw [hk] at h; cases h
  | some fr =>
    rw [hk] at h
    simp only [Option.map_some, Option.bind_some] at h ⊢
    split at h
    · rw [Array.getElem?_modify] at h
      split at h
      · cases e : fr.binds[i]? with
        | none => rw [e] at h; cases h
        | some ba => rw [e] at h; cases h; exact ⟨ba, rfl, rfl, rfl⟩
      · exact ⟨bb, h, rfl, rfl⟩
    · exact ⟨bb, h, rfl, rfl⟩

theorem valAt_setAtE_self {E : Env} {f j : Nat} {w : Value} (hp : Pos.bind f j ∈ allPos E) :
    valAt (Env.setAtE E (.bind f j) w) (.bind f j) = w := by
  obtain ⟨fr, b, hf, hb⟩ := mem_allPos_bind E f j hp
  exact valAt_setAtE_bind E f j w fr b hf hb

theorem posRel_setAtE (hve : VEq (valAt E (.bind f j)) w) : PosRel E (Env.setAtE E (.bind f j) w) id where
  fwd p hp := by
    rw [allPos_setAtE] at hp
    by_cases e : p = .bind f j
    · subst e; exact .inr ⟨hp, by rw [valAt_setAtE_self hp]; exact hve, .inl rfl⟩
    · exact .inr ⟨hp, .inl (valAt_setAtE_other E _ _ w e).symm, .inl rfl⟩
  bwd q hq := by
    refine .inr ⟨q, by rw [allPos_setAtE]; exact hq, rfl, ?_⟩
    by_cases e : q = .bind f j
    · subst e; rw [valAt_setAtE_self hq]; exact hve
    · exact .inl (valAt_setAtE_other E _ _ w e).symm
  inj _ _ _ _ h := h

theorem ckVarPos_mem {i : Nat} {pos : Pos} (h : ckVarPos E i = some pos) : pos ∈ allPos E := by
  unfold ckVarPos at h
  split at h
  · rename_i hi
    cases h
    have hne : 0 < E.size := by
      rcases Nat.eq_zero_or_pos E.size with e | e
      · rw [e, getElem!_neg E (0 - 1) (by omega)] at hi; exact absurd hi (Nat.not_lt_zero _)
      · exact e
    rw [getElem!_pos E (E.size - 1) (by omega)] at hi ⊢
    exact bind_mem_allPos E _ _ _ _ (Array.getElem?_eq_getElem _) (Array.getElem?_eq_getElem (by omega))
  · cases h

theorem ckContent_setAtE (p : Place) : ckContent (Env.setAtE E (.bind f j) w) p =
    if ckVarPos E p.steps.1 = some (.bind f j) then w.follow p.steps.2 else ckContent E p := by
  unfold ckContent; rw [ckVarPos_setAtE]
  cases h : ckVarPos E p.steps.1 with
  | none => rfl
  | some pos =>
    simp only [Option.bind_some]
    by_cases e : pos = .bind f j
    · subst e; rw [if_pos rfl, valAt_setAtE_self (ckVarPos_mem E h)]
    · rw [if_neg (fun h' => e (Option.some.inj h')), valAt_setAtE_other E _ _ w e]

end SetAt

theorem _root_.Ochr.Value.Num.follow {v : Value} (h : v.Num) : ∀ {path : List Step} {x : Value},
    v.follow path = some x → x.Num := by
  induction h with
  | zero =>
    intro path x hx
    cases path with
    | nil => cases hx; exact .zero
    | cons s ss => cases s <;> simp [Value.follow, stepV] at hx
  | succ hw ih =>
    intro path x hx
    cases path with
    | nil => cases hx; exact .succ hw
    | cons s ss =>
      cases s with
      | proj i => cases i with
        | zero => simp only [Value.follow, stepV, Option.bind_some] at hx; exact ih hx
        | succ k => simp [Value.follow, stepV] at hx
      | _ => simp [Value.follow, stepV] at hx

theorem bot_follow {path : List Step} {x : Value} (h : Value.bot.follow path = some x) : x = .bot := by
  cases path with
  | nil => cases h; rfl
  | cons s ss => cases s <;> simp [Value.follow, stepV] at h

theorem numBorrow_follow {l : Nat} {w : Value} (hw : w.Num) {path : List Step} {x : Value}
    (h : (Value.borrow l w).follow path = some x) : x = .borrow l w ∨ x.Num := by
  cases path with
  | nil => cases h; exact .inl rfl
  | cons s ss =>
    cases s with
    | deref => simp only [Value.follow, stepV, Option.bind_some] at h; exact .inr (hw.follow h)
    | proj i => cases i <;> simp [Value.follow, stepV] at h
    | field g => simp [Value.follow, stepV] at h

theorem ckVarPos_binding {E : Env} {i f j : Nat} (h : ckVarPos E i = some (.bind f j)) :
    ∃ b, E[f]?.bind (fun fr : Frame => fr.binds[j]?) = some b := by
  obtain ⟨fr, b, hf, hb⟩ := mem_allPos_bind E f j (ckVarPos_mem E h)
  exact ⟨b, by rw [hf, Option.bind_some, hb]⟩

theorem binds_norm (st : MState) (f j : Nat) :
    st.norm.env[f]?.bind (fun fr : Frame => fr.binds[j]?) = st.env[f]?.bind (fun fr : Frame => fr.binds[j]?) := by
  show (Env.erase st.env)[f]?.bind _ = _
  rw [Env.erase_get?]; cases st.env[f]? <;> rfl

/-- A binding's value written keeps `Inv` where the old and new values read alike and every new
content fits its place's reading and is no proof. -/
theorem inv_setAt {D : Decisions} {Γ : List IndDecl} {s : MState} {f j : Nat} {w : Value} (hi : Inv D Γ s)
    (hve : VEq (valAt s.env (.bind f j)) w)
    (hc : ∀ p x, ckVarPos s.env p.steps.1 = some (.bind f j) → w.follow p.steps.2 = some x →
      x ≠ .proof ∧ ∀ n args, D.placeDecl (topReadings s) p = .ind n args → (Γ.find? (·.name == n)).isSome →
        x.fitsInd n = true) :
    Inv D Γ { s with env := Env.setAtE s.env (.bind f j) w } := by
  have hR : topReadings { s with env := Env.setAtE s.env (.bind f j) w } = topReadings s := by
    unfold topReadings; exact congrArg (fun x => (x.getD []).reverse) (back_setAtE s.env f j w)
  obtain ⟨hf, hp⟩ := readClauses_of (b := { s with env := Env.setAtE s.env (.bind f j) w }) hi hR (fun p x h => by
    rw [ckContent_setAtE] at h
    split at h
    · exact .inr (hc p x ‹_› h)
    · exact .inl h)
  exact inv_of_posRel hi (posRel_setAtE s.env f j w hve) (tabSame_env _ _)
    (fun k i bb h => let ⟨ba, h1, h2, h3⟩ := binds_setAtE_from s.env f j w h; .inl ⟨k, i, ba, h1, h2, h3⟩) hf hp

/-- Under `PlaceLocal`, no place rooted at a binding read `r` reads an inductive, for `r` one of the
two readings the columns bind. -/
theorem PlaceLocal.noInd {D : Decisions} (hL : PlaceLocal D) {st : MState} {f j : Nat} {r : DeclInfo}
    (hr : r = .other ∨ r = .ref .other)
    (hd : ∀ b, st.env[f]?.bind (fun fr : Frame => fr.binds[j]?) = some b → b.decl = r)
    {p : Place} (h : ckVarPos st.env p.steps.1 = some (.bind f j)) (n : String) (args : List DeclInfo) :
    D.placeDecl (topReadings st) p ≠ .ind n args := by
  obtain ⟨b, hb⟩ := ckVarPos_binding h
  rw [hL.at_binding h hb, hd b hb]
  rcases hr with rfl | rfl
  · exact hL.other _ n args
  · exact hL.ref _ n args

theorem invSetBot : InvSetBot := by
  intro D Γ st f j hn hi
  rw [norm_withEnv, erase_setAtE]
  have hva : valAt st.norm.env (.bind f j) = valAt st.env (.bind f j) := valAt_erase _ _
  refine inv_setAt (s := st.norm) hi (.inr (.inl ⟨.inl (hva ▸ hn), .inr (.inr rfl)⟩)) fun p x _ hx => ?_
  rw [bot_follow hx]
  exact ⟨fun e => (by cases e), fun _ _ _ _ => rfl⟩

/-- `InvSetNum` with the fix (machine3, 2026-11-21): the decisions local to the root, the binding
read `.other`. -/
theorem invSetNum' (D : Decisions) (Γ : List IndDecl) (st : MState) (f j : Nat) (v₀ : Value) (hL : PlaceLocal D)
    (hd : ∀ b, st.env[f]?.bind (fun fr : Frame => fr.binds[j]?) = some b → b.decl = .other)
    (hn : (valAt st.env (.bind f j)).Num) (hv₀ : v₀.Num) (hi : Inv D Γ st.norm) :
    Inv D Γ { st with env := Env.setAtE st.env (.bind f j) v₀ }.norm := by
  rw [norm_withEnv, erase_setAtE]
  have hva : valAt st.norm.env (.bind f j) = valAt st.env (.bind f j) := valAt_erase _ _
  refine inv_setAt (s := st.norm) hi (.inr (.inl ⟨.inl (hva ▸ hn), .inl hv₀⟩)) fun p x hp hx => ⟨fun e => (by have := hv₀.follow hx; rw [e] at this; cases this),
      fun n args e => absurd e (hL.noInd (.inl rfl) (fun b h => hd b (by rw [← binds_norm]; exact h)) hp n args)⟩

/-- `InvWriteDeref` with the fix (machine3, 2026-11-21): the decisions local to the root, the borrow
binding read `.ref .other`. -/
theorem invWriteDeref' (D : Decisions) (Γ : List IndDecl) (st : MState) (f j l : Nat) (w v₀ : Value)
    (hL : PlaceLocal D)
    (hd : ∀ b, st.env[f]?.bind (fun fr : Frame => fr.binds[j]?) = some b → b.decl = .ref .other)
    (hy : valAt st.env (.bind f j) = .borrow l w) (hw : w.Num) (hv₀ : v₀.Num) (hi : Inv D Γ st.norm) :
    Inv D Γ { st with env := Env.setAtE st.env (.bind f j) (.borrow l v₀) }.norm := by
  rw [norm_withEnv, erase_setAtE]
  have hva : valAt st.norm.env (.bind f j) = valAt st.env (.bind f j) := valAt_erase _ _
  refine inv_setAt (s := st.norm) hi (.inr (.inr ⟨l, w, v₀, hva.trans hy, rfl, hw, hv₀⟩)) fun p x hp hx => ⟨fun e => ?_,
      fun n args e => absurd e (hL.noInd (.inr rfl) (fun b h => hd b (by rw [← binds_norm]; exact h)) hp n args)⟩
  rcases numBorrow_follow hv₀ hx with h | h
  · rw [e] at h; cases h
  · rw [e] at h; cases h

end Ochr.Meaning.Steps.Machine

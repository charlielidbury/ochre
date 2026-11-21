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
theorem _root_.Ochr.Meaning.Steps.Form.PlaceLocal.noInd {D : Decisions} (hL : PlaceLocal D) {st : MState} {f j : Nat} {r : DeclInfo}
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

/-! ## A binding pushed (the value in flight moved into it) -/

section PushBind
variable (E : Env) (h : Hint) (ty : Option Value) (v : Value) (pf : Bool) (d : DeclInfo)
  (fr : Frame) (hfr : E[E.size - 1]? = some fr)
include hfr

theorem top_pushBindE : (Env.pushBindE E h ty v pf d)[E.size - 1]? =
    some { fr with binds := fr.binds.push { hint := h, ty, val := v, proof := pf, decl := d } } := by
  simp only [Env.pushBindE, Array.getElem?_modify, if_true, hfr, Option.map_some]

theorem ckVarPos_pushBindE (i : Nat) : ckVarPos (Env.pushBindE E h ty v pf d) i =
    if i = 0 then some (.bind (E.size - 1) fr.binds.size) else ckVarPos E (i - 1) := by
  have hs : (Env.pushBindE E h ty v pf d).size = E.size := by simp [Env.pushBindE]
  unfold ckVarPos
  rw [hs, getElem!_def, getElem!_def, top_pushBindE E h ty v pf d fr hfr, hfr]
  simp only [Array.size_push]
  by_cases h0 : i = 0
  · subst h0; simp
  · rw [if_neg h0]
    by_cases h1 : i < fr.binds.size + 1
    · rw [if_pos h1, if_pos (by omega)]; congr 2; omega
    · rw [if_neg h1, if_neg (by omega)]

theorem topReadings_pushBindE (s : MState) (hs : s.env = E) :
    topReadings { s with env := Env.pushBindE E h ty v pf d } = d :: topReadings s := by
  unfold topReadings
  have hsz : (Env.pushBindE E h ty v pf d).size = E.size := by simp [Env.pushBindE]
  simp only [Array.back?, hsz, top_pushBindE E h ty v pf d fr hfr, hs, hfr, Option.map_some, Option.getD_some,
    Array.toList_push, List.map_append, List.map_cons, List.map_nil, List.reverse_append, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.singleton_append]

theorem posRel_pushBind (hne : 0 < E.size) (hv : v.Bland ∨ v.NumBorrow) :
    PosRel (Env.pushTempE E v) (Env.pushBindE E h ty v pf d)
      (fun q => if q = .bind (E.size - 1) fr.binds.size then .temp (E.size - 1) fr.temps.size else q) := by
  obtain ⟨A, B, h1, h2⟩ := allPos_pushBindE E h ty v pf d fr hfr hne
  have hn := new_not_mem_pushBindE E h ty v pf d fr h2
  have ht := allPos_pushTempE E v fr hfr hne
  have htn : Pos.temp (E.size - 1) fr.temps.size ∉ allPos E := fun hm => by
    obtain ⟨fr', hf', hi⟩ := mem_allPos_temp E _ _ hm
    rw [hfr] at hf'; cases hf'; exact Nat.lt_irrefl _ hi
  have hvb : valAt (Env.pushBindE E h ty v pf d) (.bind (E.size - 1) fr.binds.size) = v :=
    valAt_pushBindE_new E h ty v pf d fr hfr
  have hvt : valAt (Env.pushTempE E v) (.temp (E.size - 1) fr.temps.size) = v := valAt_pushTempE_new E v fr hfr
  refine ⟨fun p hp => ?_, fun q hq => ?_, fun p hp p' hp' e => ?_⟩
  · rw [h2, List.mem_append, List.mem_cons] at hp
    by_cases ep : p = .bind (E.size - 1) fr.binds.size
    · subst ep
      rcases hv with hb | hb
      · exact .inl (by rw [hvb]; exact hb)
      · refine .inr ⟨by rw [if_pos rfl, ht]; simp, by rw [if_pos rfl, hvt, hvb]; exact .inl rfl, .inr (by rw [hvb]; exact hb)⟩
    · have hpE : p ∈ allPos E := by
        rw [h1, List.mem_append]; rcases hp with hp | hp | hp
        · exact .inl hp
        · exact absurd hp ep
        · exact .inr hp
      rw [if_neg ep]
      exact .inr ⟨by rw [ht]; exact List.mem_append_left _ hpE,
        .inl ((valAt_pushTempE_mem E v fr hfr hpE).trans (valAt_pushBindE_ne E h ty v pf d fr hfr p ep).symm), .inl rfl⟩
  · rw [ht, List.mem_append, List.mem_singleton] at hq
    rcases hq with hq | rfl
    · have eq : q ≠ .bind (E.size - 1) fr.binds.size := fun e => hn (by rw [← h1, ← e]; exact hq)
      have hqb : q ∈ allPos (Env.pushBindE E h ty v pf d) := by
        rw [h2]; rw [h1] at hq
        rcases List.mem_append.mp hq with hq | hq
        · exact List.mem_append_left _ hq
        · exact List.mem_append_right _ (List.mem_cons_of_mem _ hq)
      exact .inr ⟨q, hqb, by rw [if_neg eq],
        .inl ((valAt_pushTempE_mem E v fr hfr hq).trans (valAt_pushBindE_ne E h ty v pf d fr hfr q eq).symm)⟩
    · exact .inr ⟨.bind (E.size - 1) fr.binds.size, by rw [h2]; simp, by rw [if_pos rfl], by rw [hvt, hvb]; exact .inl rfl⟩
  · have notb : ∀ x ∈ allPos (Env.pushBindE E h ty v pf d), x ≠ .temp (E.size - 1) fr.temps.size := by
      intro x hx e; subst e
      rw [h2, List.mem_append, List.mem_cons] at hx
      exact htn (by rw [h1, List.mem_append]; rcases hx with hx | hx | hx
                    · exact .inl hx
                    · cases hx
                    · exact .inr hx)
    by_cases ep : p = .bind (E.size - 1) fr.binds.size <;> by_cases ep' : p' = .bind (E.size - 1) fr.binds.size
    · rw [ep, ep']
    · rw [if_pos ep, if_neg ep'] at e; exact absurd e.symm (notb p' hp')
    · rw [if_neg ep, if_pos ep'] at e; exact absurd e (notb p hp)
    · rw [if_neg ep, if_neg ep'] at e; exact e

end PushBind

theorem tabSame_envs (s : MState) (e₁ e₂ : Env) : TabSame { s with env := e₁ } { s with env := e₂ } :=
  ⟨Nat.le_refl _, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **A binding pushed with the value in flight** (a number at `Nat` read `.other`, or a borrow of a
number at `&Nat` read `.ref .other`) keeps `Inv`, the decisions local to the root. -/
theorem inv_pushBind {D : Decisions} {Γ : List IndDecl} {s : MState} {h : Hint} {ty : Option Value} {v : Value}
    {pf : Bool} {d : DeclInfo} (hL : PlaceLocal D) (hne : 0 < s.env.size) (hv : v.Num ∨ v.NumBorrow)
    (hd : d = .other ∨ d = .ref .other) (hty : ty = some .tNat ∨ ty = some (.tRef .tNat))
    (hi : Inv D Γ { s with env := Env.pushTempE s.env v }) :
    Inv D Γ { s with env := Env.pushBindE s.env h ty v pf d } := by
  obtain ⟨fr, hfr⟩ : ∃ fr, s.env[s.env.size - 1]? = some fr := ⟨_, Array.getElem?_eq_getElem (by omega)⟩
  obtain ⟨A, B, h1, h2⟩ := allPos_pushBindE s.env h ty v pf d fr hfr hne
  have hn := new_not_mem_pushBindE s.env h ty v pf d fr h2
  have hRa : topReadings { s with env := Env.pushTempE s.env v } = topReadings s := by
    unfold topReadings; exact congrArg (fun x => (x.getD []).reverse) (back_pushTempE s.env v)
  have hRb := topReadings_pushBindE s.env h ty v pf d fr hfr s rfl
  obtain ⟨hf, hp⟩ := readClauses_reroot (a := { s with env := Env.pushTempE s.env v })
    (b := { s with env := Env.pushBindE s.env h ty v pf d }) hi hL 1 (fun i => i - 1)
    (fun i hi1 => by
      show ckVarPos (Env.pushBindE s.env h ty v pf d) i = ckVarPos (Env.pushTempE s.env v) (i - 1)
      rw [ckVarPos_pushBindE s.env h ty v pf d fr hfr, ckVarPos_pushTempE, if_neg (by omega)])
    (fun i hi1 => by
      rw [hRb, hRa]
      obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
      simp)
    (fun i pos hi1 hpos => by
      show valAt (Env.pushBindE s.env h ty v pf d) pos = valAt (Env.pushTempE s.env v) pos
      rw [ckVarPos_pushTempE] at hpos
      have hm := ckVarPos_mem s.env hpos
      rw [valAt_pushTempE_mem s.env v fr hfr hm]
      exact valAt_pushBindE_ne s.env h ty v pf d fr hfr pos (fun e => hn (by rw [← h1, ← e]; exact hm)))
    (fun p x hp hc => by
      have h0 : p.steps.1 = 0 := by omega
      have hpos : ckVarPos (Env.pushBindE s.env h ty v pf d) p.steps.1 = some (.bind (s.env.size - 1) fr.binds.size) := by
        rw [ckVarPos_pushBindE s.env h ty v pf d fr hfr, if_pos h0]
      refine ⟨fun e => ?_, fun n args => PlaceLocal.noInd hL hd (st := { s with env := Env.pushBindE s.env h ty v pf d })
        (fun b' hb' => ?_) hpos n args⟩
      · unfold ckContent at hc
        rw [hpos, Option.bind_some, valAt_pushBindE_new s.env h ty v pf d fr hfr, e] at hc
        rcases hv with hv | ⟨l, w, rfl, hw⟩
        · have := hv.follow hc; cases this
        · rcases numBorrow_follow hw hc with h' | h' <;> cases h'
      · have := bind_pushBindE_new s.env h ty v pf d fr hfr
        rw [this] at hb'; cases hb'; rfl)
  refine inv_of_posRel hi (posRel_pushBind s.env h ty v pf d fr hfr hne
    (hv.elim (fun h => .inl (.inl h)) .inr)) (tabSame_envs _ _ _) (fun k i bb hbb => ?_) hf hp
  by_cases e : Pos.bind k i = .bind (s.env.size - 1) fr.binds.size
  · cases e
    rw [bind_pushBindE_new s.env h ty v pf d fr hfr] at hbb
    cases hbb
    exact .inr ⟨rfl, hty⟩
  · rw [bind_pushBindE_ne s.env h ty v pf d fr hfr k i e] at hbb
    exact .inl ⟨k, i, bb, by rw [binds_pushTempE]; exact hbb, rfl, rfl⟩

/-- `InvBindNum` with the fix (machine3): the decisions local to the root. -/
theorem invBindNum' (D : Decisions) (Γ : List IndDecl) (st : MState) (h : Hint) (v : Value) (T? : Option Value) (p : Bool)
    (hL : PlaceLocal D) (hv : v.Num) (hne : 0 < st.env.size) (hi : Inv D Γ (st.withTempT v T?).norm) :
    Inv D Γ { st with env := Env.pushBindE st.env h (some .tNat) v p .other }.norm := by
  rw [norm_withTempT] at hi
  rw [norm_withEnv, erase_pushBindE]
  exact inv_pushBind (s := st.norm) hL (by show 0 < (Env.erase st.env).size; rw [Env.erase_size]; exact hne)
    (.inl hv) (.inl rfl) (.inl rfl) hi

/-- `InvBindBorrow` with the fix (machine3): the decisions local to the root. -/
theorem invBindBorrow' (D : Decisions) (Γ : List IndDecl) (st : MState) (h : Hint) (l : Nat) (w : Value)
    (T? : Option Value) (p : Bool) (hL : PlaceLocal D) (hw : w.Num) (hne : 0 < st.env.size)
    (hi : Inv D Γ (st.withTempT (.borrow l w) T?).norm) :
    Inv D Γ { st with env := Env.pushBindE st.env h (some (.tRef .tNat)) (.borrow l w) p (.ref .other) }.norm := by
  rw [norm_withTempT] at hi
  rw [norm_withEnv, erase_pushBindE]
  exact inv_pushBind (s := st.norm) hL (by show 0 < (Env.erase st.env).size; rw [Env.erase_size]; exact hne)
    (.inr ⟨l, w, rfl, hw⟩) (.inr rfl) (.inr rfl) hi

/-! ## The top binding popped -/

section PopBind
variable (E : Env) (fr : Frame) (hfr : E[E.size - 1]? = some fr) (hn : 0 < fr.binds.size)
include hfr hn

theorem ckVarPos_popBindE (i : Nat) : ckVarPos (Env.popBindE E) i = ckVarPos E (i + 1) := by
  have hs : (Env.popBindE E).size = E.size := by simp [Env.popBindE]
  have ht : (Env.popBindE E)[E.size - 1]? = some { fr with binds := fr.binds.pop } := by
    simp only [Env.popBindE, Array.getElem?_modify, if_true, hfr, Option.map_some]
  unfold ckVarPos
  rw [hs, getElem!_def, getElem!_def, ht, hfr]
  simp only [Array.size_pop]
  by_cases h1 : i + 1 < fr.binds.size
  · rw [if_pos (by omega), if_pos h1]; congr 2; omega
  · rw [if_neg (by omega), if_neg h1]

theorem topReadings_popBindE (s : MState) (hs : s.env = E) :
    topReadings { s with env := Env.popBindE E } = (topReadings s).tail := by
  have hsz : (Env.popBindE E).size = E.size := by simp [Env.popBindE]
  have ht : (Env.popBindE E)[E.size - 1]? = some { fr with binds := fr.binds.pop } := by
    simp only [Env.popBindE, Array.getElem?_modify, if_true, hfr, Option.map_some]
  unfold topReadings
  simp only [Array.back?, hsz, ht, hs, hfr, Option.map_some, Option.getD_some, Array.toList_pop, List.map_dropLast,
    List.tail_reverse]

theorem inv_popBind {D : Decisions} {Γ : List IndDecl} {s : MState} (hs : s.env = E) (hL : PlaceLocal D)
    (hb : (valAt E (.bind (E.size - 1) (fr.binds.size - 1))).Bland) (hi : Inv D Γ s) :
    Inv D Γ { s with env := Env.popBindE E } := by
  subst hs
  have hne : 0 < s.env.size := by
    rcases Nat.eq_zero_or_pos s.env.size with e | e
    · simp [e] at hfr
    · exact e
  obtain ⟨A, B, h1, h2⟩ := allPos_popTop s.env fr hfr hn hne
  have ho := old_not_mem_popTop s.env fr h1
  have hR := topReadings_popBindE s.env fr hfr hn s rfl
  obtain ⟨hf, hp⟩ := readClauses_reroot (a := s) (b := { s with env := Env.popBindE s.env }) hi hL 0 (fun i => i + 1)
    (fun i _ => ckVarPos_popBindE s.env fr hfr hn i)
    (fun i _ => by rw [hR]; cases topReadings s <;> simp)
    (fun i pos _ hpos => by
      show valAt (Env.popBindE s.env) pos = valAt s.env pos
      refine valAt_popTop_ne s.env fr hfr pos fun e => ?_
      subst e
      unfold ckVarPos at hpos
      split at hpos
      · rename_i hlt
        have e2 := (Pos.bind.inj (Option.some.inj hpos)).2
        rw [getElem!_def, hfr] at hlt e2
        dsimp only at hlt e2
        omega
      · cases hpos)
    (fun p x hp _ => absurd hp (Nat.not_lt_zero _))
  have hpe : allPos (Env.popBindE s.env) = A ++ B := h2
  refine inv_of_posRel hi ⟨fun p hp => ?_, fun q hq => ?_, fun _ _ _ _ e => e⟩ (tabSame_env _ _) (fun k i bb hbb => ?_) hf hp
  · rw [hpe] at hp
    have hne' : p ≠ .bind (s.env.size - 1) (fr.binds.size - 1) := fun e => ho (e ▸ hp)
    exact .inr ⟨by rw [h1]; rcases List.mem_append.mp hp with h | h
                   · exact List.mem_append_left _ h
                   · exact List.mem_append_right _ (List.mem_cons_of_mem _ h),
      .inl (valAt_popTop_ne s.env fr hfr p hne').symm, .inl rfl⟩
  · by_cases e : q = .bind (s.env.size - 1) (fr.binds.size - 1)
    · subst e; exact .inl hb
    · refine .inr ⟨q, ?_, rfl, .inl (valAt_popTop_ne s.env fr hfr q e).symm⟩
      rw [hpe]; rw [h1] at hq
      rcases List.mem_append.mp hq with h | h
      · exact List.mem_append_left _ h
      · rcases List.mem_cons.mp h with h | h
        · exact absurd h e
        · exact List.mem_append_right _ h
  · by_cases e : Pos.bind k i = .bind (s.env.size - 1) (fr.binds.size - 1)
    · cases e
      have := bind_popTop_old s.env fr hfr
      rw [show (Env.popBindE s.env) = s.env.modify (s.env.size - 1) popTop from rfl, this] at hbb
      cases hbb
    · rw [show (Env.popBindE s.env) = s.env.modify (s.env.size - 1) popTop from rfl,
        bind_popTop_ne s.env fr hfr k i e] at hbb
      exact .inl ⟨k, i, bb, hbb, rfl, rfl⟩

end PopBind

/-- `InvPopBind` with the fix (machine3): the decisions local to the root. -/
theorem invPopBind' (D : Decisions) (Γ : List IndDecl) (st : MState) (fr : Frame) (b : Binding) (hL : PlaceLocal D)
    (hfr : st.env[st.env.size - 1]? = some fr) (hb : fr.binds.back? = some b) (hv : b.val = .bot ∨ b.val.Num)
    (hi : Inv D Γ st.norm) : Inv D Γ { st with env := Env.popBindE st.env }.norm := by
  rw [norm_withEnv, erase_popBindE]
  have hfr' : st.norm.env[st.norm.env.size - 1]? = some fr.erase := by
    show (Env.erase st.env)[(Env.erase st.env).size - 1]? = _
    rw [Env.erase_size, Env.erase_get?, hfr]; rfl
  have hn : 0 < fr.erase.binds.size := by
    show 0 < fr.binds.size
    rcases Nat.eq_zero_or_pos fr.binds.size with e | e
    · simp [Array.back?, e] at hb
    · exact e
  refine inv_popBind st.norm.env fr.erase hfr' hn rfl hL ?_ hi
  have hb' : fr.binds[fr.binds.size - 1]? = some b := hb
  rw [valAt_bind_lookup, hfr', Option.bind_some]
  show (((fr.binds[fr.binds.size - 1]?).getD default).val).Bland
  rw [hb']
  exact hv.elim (fun h => .inr (.inr h)) .inl

/-! ## A number binding lent where nothing is lent (`&x`) -/

theorem occ_loan (n l : Nat) :
    (Value.loan n).anyAtom (fun a => a == .loan l || (match a with | .borrow l' _ => l' == l | _ => false)) = (n == l) := by
  have e : (Value.loan n == Value.loan l) = (n == l) := rfl
  simp only [Value.anyAtom, e, Bool.or_false]

theorem holdsBorrow_false_of_noLive {E : Env} (h : ∀ l, liveLoan E l = false) {p : Pos} (hp : p ∈ allPos E) (l : Nat) :
    (valAt E p).holdsBorrow l = false := by
  cases e : (valAt E p).holdsBorrow l
  · rfl
  · have := h l; rw [← Bool.not_eq_true] at this; exact absurd (liveLoan_iff.mpr ⟨p, hp, e⟩) this

theorem not_borrow_of_noLive {E : Env} (h : ∀ l, liveLoan E l = false) {p : Pos} (hp : p ∈ allPos E) (m : Nat)
    (w : Value) : valAt E p ≠ .borrow m w := fun e => by
  have := holdsBorrow_false_of_noLive h hp m; rw [e] at this; simp [Value.holdsBorrow] at this

theorem inv_lend {D : Decisions} {Γ : List IndDecl} {s : MState} {f j : Nat} {bv : Value} (hbv : bv.Num)
    (hfj : Pos.bind f j ∈ allPos s.env) (hnl : ∀ l, liveLoan s.env l = false) (hi : Inv D Γ s) :
    Inv D Γ { s with
      env := Env.pushTempE (Env.setAtE s.env (.bind f j) (.loan s.nextLoan)) (.borrow s.nextLoan bv)
      nextLoan := s.nextLoan + 1 } := by
  have hi' := hi
  obtain ⟨⟨-, -⟩, ⟨w2a, -⟩, -, -, -, -, -, -, -, -, w15, -, sf, -⟩ := hi'
  obtain ⟨fr, b0, hfE, -⟩ := mem_allPos_bind s.env f j hfj
  have hne : 0 < (Env.setAtE s.env (.bind f j) (.loan s.nextLoan)).size := by
    rw [size_setAtE]; rcases Nat.eq_zero_or_pos s.env.size with e | e
    · simp [Array.getElem?_eq_none (by omega : s.env.size ≤ f)] at hfE
    · exact e
  have hP1 : allPos (Env.setAtE s.env (.bind f j) (.loan s.nextLoan)) = allPos s.env := allPos_setAtE ..
  have hR1 : topReadings { s with env := Env.setAtE s.env (.bind f j) (.loan s.nextLoan) } = topReadings s := by
    unfold topReadings; exact congrArg (fun x => (x.getD []).reverse) (back_setAtE s.env f j _)
  have hc1 := ckContent_setAtE s.env f j (.loan s.nextLoan)
  have hb1 := @binds_setAtE_from s.env f j (.loan s.nextLoan)
  have hvs : valAt (Env.setAtE s.env (.bind f j) (.loan s.nextLoan)) (.bind f j) = .loan s.nextLoan :=
    valAt_setAtE_self hfj
  have hvo : ∀ p, p ≠ .bind f j → valAt (Env.setAtE s.env (.bind f j) (.loan s.nextLoan)) p = valAt s.env p :=
    fun p e => valAt_setAtE_other s.env _ _ _ e
  generalize Env.setAtE s.env (.bind f j) (.loan s.nextLoan) = E1 at hne hP1 hR1 hc1 hb1 hvs hvo ⊢
  obtain ⟨fr1, hfr1⟩ : ∃ fr, E1[E1.size - 1]? = some fr := ⟨_, Array.getElem?_eq_getElem (by omega)⟩
  have hP : allPos (Env.pushTempE E1 (.borrow s.nextLoan bv)) = allPos s.env ++ [.temp (E1.size - 1) fr1.temps.size] := by
    rw [allPos_pushTempE E1 _ fr1 hfr1 hne, hP1]
  have hnew : valAt (Env.pushTempE E1 (.borrow s.nextLoan bv)) (.temp (E1.size - 1) fr1.temps.size) =
      .borrow s.nextLoan bv := valAt_pushTempE_new E1 _ fr1 hfr1
  -- every position of the new Ω
  have hcls : ∀ p ∈ allPos (Env.pushTempE E1 (.borrow s.nextLoan bv)),
      (p = .temp (E1.size - 1) fr1.temps.size ∧ valAt (Env.pushTempE E1 (.borrow s.nextLoan bv)) p = .borrow s.nextLoan bv) ∨
      (p = .bind f j ∧ valAt (Env.pushTempE E1 (.borrow s.nextLoan bv)) p = .loan s.nextLoan) ∨
      (p ∈ allPos s.env ∧ valAt (Env.pushTempE E1 (.borrow s.nextLoan bv)) p = valAt s.env p) := by
    intro p hp
    rw [hP, List.mem_append, List.mem_singleton] at hp
    rcases hp with hp | rfl
    · have h1 := valAt_pushTempE_mem E1 (.borrow s.nextLoan bv) fr1 hfr1 (by rw [hP1]; exact hp)
      by_cases e : p = .bind f j
      · subst e; exact .inr (.inl ⟨rfl, by rw [h1, hvs]⟩)
      · exact .inr (.inr ⟨hp, by rw [h1, hvo p e]⟩)
    · exact .inl ⟨rfl, hnew⟩
  -- the old values hold no label
  have hoL : ∀ q ∈ allPos s.env, (valAt s.env q).loans = [] := fun q hq => by
    cases e : (valAt s.env q).loans with
    | nil => rfl
    | cons l ls =>
      have := sf.loans _ (mem_values_iff.mpr ⟨q, hq, rfl⟩) l (by rw [e]; exact List.mem_cons_self ..)
      rw [hnl l] at this; cases this
  have hoO : ∀ q ∈ allPos s.env, (valAt s.env q).outerLoans = [] := fun q hq => by
    cases e : (valAt s.env q).outerLoans with
    | nil => rfl
    | cons l ls =>
      have := w2a _ (mem_values_iff.mpr ⟨q, hq, rfl⟩) l (by rw [e]; exact List.mem_cons_self ..)
      rw [hnl l] at this; cases this
  have hoS : ∀ q ∈ allPos s.env, ∀ l pos path, (valAt s.env q).sitesOf l pos path = [] := fun q hq l pos path =>
    sitesOf_nil_of_hasLoan l pos path _
      (hasLoan_false_of_loans_nil (hoL q hq) l (w15 _ (mem_values_iff.mpr ⟨q, hq, rfl⟩) l))
  have hlive : ∀ k, liveLoan (Env.pushTempE E1 (.borrow s.nextLoan bv)) k = true ↔ k = s.nextLoan := by
    intro k
    rw [liveLoan_iff]
    constructor
    · rintro ⟨p, hp, h⟩
      rcases hcls p hp with ⟨-, e⟩ | ⟨-, e⟩ | ⟨hp', e⟩
      · rw [e] at h; simp [Value.holdsBorrow, hbv.holdsBorrow] at h; exact h.symm
      · rw [e] at h; simp [Value.holdsBorrow] at h
      · rw [e, holdsBorrow_false_of_noLive hnl hp'] at h; cases h
    · rintro rfl
      exact ⟨.temp (E1.size - 1) fr1.temps.size, by rw [hP]; simp, by rw [hnew]; simp [Value.holdsBorrow]⟩
  have hbinds2 := binds_pushTempE E1 (.borrow s.nextLoan bv)
  have hck2 := ckContent_pushTempE E1 (.borrow s.nextLoan bv)
  have hR2 : topReadings { s with env := Env.pushTempE E1 (.borrow s.nextLoan bv), nextLoan := s.nextLoan + 1 } =
      topReadings s := by
    rw [← hR1]; unfold topReadings; exact congrArg (fun x => (x.getD []).reverse) (back_pushTempE E1 _)
  generalize Env.pushTempE E1 (.borrow s.nextLoan bv) = E2 at hP hnew hcls hlive hbinds2 hck2 hR2 ⊢
  obtain ⟨hf, hp⟩ := readClauses_of (b := { s with env := E2, nextLoan := s.nextLoan + 1 }) hi hR2 (fun p x h => by
    rw [hck2, hc1] at h
    split at h
    · right
      cases e : p.steps.2 with
      | nil => rw [e] at h; cases h; exact ⟨fun e => (by cases e), fun _ _ _ _ => rfl⟩
      | cons st ss => rw [e] at h; cases st <;> simp [Value.follow, stepV] at h
    · exact .inl h)
  refine inv_step hi ⟨Nat.le_succ _, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (fun v hv => ?_) (fun l hl => ?_)
    (fun k i bb h => ?_) (fun p hp q hq l h h' => ?_) ⟨fun v hv l hl => ?_, fun l => ?_⟩ ?_ ?_ (fun v hv l hl => ?_) hf hp
  · obtain ⟨p, hp, rfl⟩ := mem_values_iff.mp hv
    rcases hcls p hp with ⟨-, e⟩ | ⟨-, e⟩ | ⟨hp', e⟩
    · exact .inr (Value.NumBorrow.simple ⟨_, bv, e, hbv⟩)
    · exact .inr (.inr (.inr ⟨_, e⟩))
    · exact .inl (mem_values_iff.mpr ⟨p, hp', e.symm⟩)
  · obtain ⟨v, hv, h⟩ := hl
    obtain ⟨p, hp, rfl⟩ := mem_values_iff.mp hv
    rcases hcls p hp with ⟨-, e⟩ | ⟨-, e⟩ | ⟨hp', e⟩
    · rw [e] at h
      have h2 : (s.nextLoan == l) = true := (occ_numBorrow hbv).symm.trans h
      rw [beq_iff_eq] at h2; subst h2; exact .inr (Nat.lt_succ_self _)
    · rw [e] at h
      have h2 : (s.nextLoan == l) = true := (occ_loan _ _).symm.trans h
      rw [beq_iff_eq] at h2; subst h2; exact .inr (Nat.lt_succ_self _)
    · exact .inl ⟨_, mem_values_iff.mpr ⟨p, hp', rfl⟩, by rw [← e]; exact h⟩
  · rw [hbinds2] at h
    obtain ⟨ba, h1, h2, h3⟩ := hb1 h
    exact .inl ⟨k, i, ba, h1, h2, h3⟩
  · rw [shape_eq_shapeOf] at h h'
    have key : ∀ x ∈ allPos E2, shapeOf (valAt E2 x) = some l → x = .temp (E1.size - 1) fr1.temps.size := by
      intro x hx hs
      rcases hcls x hx with ⟨rfl, -⟩ | ⟨-, e⟩ | ⟨hx', e⟩
      · rfl
      · rw [e] at hs; cases hs
      · rw [e] at hs
        cases ev : valAt s.env x with
        | borrow m w => exact absurd ev (not_borrow_of_noLive hnl hx' m w)
        | _ => rw [ev] at hs; cases hs
    rw [key p hp h, key q hq h']
  · obtain ⟨p, hp, rfl⟩ := mem_values_iff.mp hv
    rcases hcls p hp with ⟨-, e⟩ | ⟨-, e⟩ | ⟨hp', e⟩
    · rw [e] at hl; simp [Value.outerLoans, hbv.outerLoans] at hl
    · rw [e] at hl; simp [Value.outerLoans] at hl; rw [hl]; exact (hlive _).mpr rfl
    · rw [e, hoO p hp'] at hl; cases hl
  · refine Nat.le_trans ?_ (List.count_le_length (a := l) (l := [s.nextLoan]))
    simp only [Env.values, List.flatMap_map, List.count_flatMap]
    refine Nat.le_trans (sum_le_of_inj id _ (fun _ => List.count l [s.nextLoan]) _ [Pos.bind f j] (allPos_nodup _)
      (fun p hp h0 => ?_) (fun _ _ _ _ e => e)) (by simp)
    rcases hcls p hp with ⟨-, e⟩ | ⟨rfl, e⟩ | ⟨hp', e⟩
    · simp [Function.comp, e, Value.outerLoans, hbv.outerLoans] at h0
    · exact ⟨List.mem_singleton_self _, by simp [Function.comp, e, Value.outerLoans]⟩
    · simp [Function.comp, e, hoO p hp'] at h0
  · intro k l hk hl x hx hf y hy hpos hpre
    obtain rfl := (hlive k).mp hk
    obtain rfl := (hlive l).mp hl
    exact ⟨x, hx, rfl, rfl, hf⟩
  · intro pos path hfol l hl x hx hpos k hk
    obtain rfl := (hlive l).mp hl
    have hxv := mem_sitesOf_at hx hpos
    have hp : pos ∈ allPos E2 := by
      obtain ⟨p, hp, hx'⟩ := List.mem_flatMap.mp hx
      rw [← hpos, (sitesOf_prefix _ p [] _ x hx').1]; exact hp
    rcases hcls pos hp with ⟨-, e⟩ | ⟨-, e⟩ | ⟨hp', e⟩
    · rw [e] at hxv; exact absurd hxv (by rw [Value.NumBorrow.sitesOf ⟨_, bv, rfl, hbv⟩]; simp)
    · rw [e] at hfol
      cases path with
      | nil => cases hfol
      | cons st ss => cases st <;> simp [Value.follow, stepV] at hfol
    · rw [e, hoS pos hp'] at hxv; cases hxv
  · obtain ⟨p, hp, rfl⟩ := mem_values_iff.mp hv
    rcases hcls p hp with ⟨-, e⟩ | ⟨-, e⟩ | ⟨hp', e⟩
    · rw [e] at hl; simp [Value.loans, hbv.loans] at hl
    · rw [e] at hl; simp [Value.loans] at hl; rw [hl]; exact (hlive _).mpr rfl
    · rw [e, hoL p hp'] at hl; cases hl

theorem mem_allPos_of_binding {E : Env} {f j : Nat} {b : Binding}
    (h : E[f]?.bind (fun fr : Frame => fr.binds[j]?) = some b) : Pos.bind f j ∈ allPos E := by
  cases e : E[f]? with
  | none => rw [e] at h; cases h
  | some fr => rw [e, Option.bind_some] at h; exact bind_mem_allPos E f j fr b e h

theorem invLend : InvLend := by
  intro D Γ st f j b T? hb hn _ hnl hi
  rw [norm_withTempT]
  have e : ({ st with env := Env.setAtE st.env (.bind f j) (.loan st.nextLoan), nextLoan := st.nextLoan + 1 } : MState).norm =
      { st.norm with env := (Env.setAtE st.env (.bind f j) (.loan st.nextLoan)).erase, nextLoan := st.nextLoan + 1 } := rfl
  rw [e, erase_setAtE]
  have hm : Pos.bind f j ∈ allPos st.norm.env := by
    show _ ∈ allPos (Env.erase st.env); rw [allPos_erase]; exact mem_allPos_of_binding hb
  exact inv_lend (s := st.norm) hn hm (fun l => by show liveLoan (Env.erase st.env) l = false; rw [liveLoan_erase]; exact hnl l) hi

/-- `Inv` of a state every value of whose Ω is bland: no label anywhere, so the clauses on labels
hold outright. -/
theorem inv_of_allBland {D : Decisions} {Γ : List IndDecl} {a b : MState} (hi : Inv D Γ a) (ht : TabSame a b)
    (hb : BindsFrom a b) (hall : ∀ v ∈ Env.values b.env, v.Bland)
    (hfits : ∀ p v n args, ckContent b.env p = some v → D.placeDecl (topReadings b) p = .ind n args →
      (Γ.find? (·.name == n)).isSome → v.fitsInd n = true)
    (hpc : ∀ p, GrainOk D Γ (topReadings b) p → ckContent b.env p = some .proof →
      D.copy (D.placeDecl (topReadings b) p) = true) : Inv D Γ b := by
  have hall' : ∀ p ∈ allPos b.env, (valAt b.env p).Bland := fun p hp => hall _ (mem_values_iff.mpr ⟨p, hp, rfl⟩)
  have hnl : ∀ l, liveLoan b.env l = false := fun l => by
    cases e : liveLoan b.env l
    · rfl
    · obtain ⟨p, hp, h⟩ := liveLoan_iff.mp e; rw [(hall' p hp).holdsBorrow] at h; cases h
  have hfl : (Env.values b.env).flatMap Value.outerLoans = [] :=
    List.flatMap_eq_nil_iff.mpr fun v hv => (hall v hv).outerLoans
  refine inv_step hi ht (fun v hv => .inr (hall v hv).simple) (fun l ⟨v, hv, h⟩ => ?_) hb
    (fun p hp _ _ l h _ => ?_) ⟨fun v hv l hl => ?_, fun l => by rw [hfl]; simp⟩
    (fun k _ hk => by rw [hnl k] at hk; cases hk) (fun _ _ _ l hl => by rw [hnl l] at hl; cases hl)
    (fun v hv l hl => by rw [(hall v hv).loans] at hl; cases hl) hfits hpc
  · rw [(hall v hv).anyAtom rfl (fun _ => rfl) rfl rfl] at h; cases h
  · rw [shape_eq_shapeOf, (hall' p hp).shapeOf] at h; cases h
  · rw [(hall v hv).outerLoans] at hl; cases hl

/-- `InvEndRead` with the fix (machine3): the decisions local to the root, the lender `x` read
`.other`. -/
theorem invEndRead' (D : Decisions) (Γ : List IndDecl) (st : MState) (l : Nat) (w xv : Value) (hL : PlaceLocal D)
    (hd : ∀ b, st.env[0]?.bind (fun fr : Frame => fr.binds[0]?) = some b → b.decl = .other)
    (hpos : allPos st.env = [.bind 0 0, .bind 0 1]) (hx : valAt st.env (.bind 0 0) = .loan l)
    (hy : valAt st.env (.bind 0 1) = .borrow l w) (hw : w.Num) (hxv : xv = w ∨ xv = .bot) (hi : Inv D Γ st.norm) :
    Inv D Γ { st with env := Env.setAtE (Env.setAtE st.env (.bind 0 1) .bot) (.bind 0 0) xv }.norm := by
  rw [norm_withEnv, erase_setAtE, erase_setAtE]
  have hP : allPos st.norm.env = [.bind 0 0, .bind 0 1] := by
    show allPos (Env.erase st.env) = _; rw [allPos_erase, hpos]
  have h00 : Pos.bind 0 0 ∈ allPos (Env.setAtE (Env.erase st.env) (.bind 0 1) .bot) := by
    rw [allPos_setAtE, allPos_erase, hpos]; simp
  have h01 : Pos.bind 0 1 ∈ allPos (Env.erase st.env) := by rw [allPos_erase, hpos]; simp
  have hne : Pos.bind 0 1 ≠ Pos.bind 0 0 := by simp
  have hxvb : xv.Bland := hxv.elim (fun e => .inl (e ▸ hw)) (fun e => .inr (.inr e))
  have hR : topReadings { st.norm with env := Env.setAtE (Env.setAtE st.norm.env (.bind 0 1) .bot) (.bind 0 0) xv } =
      topReadings st.norm := by
    unfold topReadings
    rw [back_setAtE, back_setAtE]
  obtain ⟨hf, hp⟩ := readClauses_of (a := st.norm)
    (b := { st.norm with env := Env.setAtE (Env.setAtE st.norm.env (.bind 0 1) .bot) (.bind 0 0) xv }) hi hR
    (fun p x h => by
      show _ ∨ _
      rw [ckContent_setAtE, ckVarPos_setAtE, ckContent_setAtE] at h
      split at h
      · rename_i hp0
        right
        rcases hxv with rfl | rfl
        · exact ⟨fun e => (by have := hw.follow h; rw [e] at this; cases this),
            fun n args e => absurd e (hL.noInd (.inl rfl) (fun b hb => hd b (by rw [← binds_norm]; exact hb)) hp0 n args)⟩
        · rw [bot_follow h]; exact ⟨fun e => (by cases e), fun _ _ _ _ => rfl⟩
      · split at h
        · right; rw [bot_follow h]; exact ⟨fun e => (by cases e), fun _ _ _ _ => rfl⟩
        · exact .inl h)
  refine inv_of_allBland hi (tabSame_env _ _) (fun k i bb h => ?_) (fun v hv => ?_) hf hp
  · obtain ⟨b1, h1, h2, h3⟩ := binds_setAtE_from _ _ _ _ h
    obtain ⟨b0, h0, h2', h3'⟩ := binds_setAtE_from _ _ _ _ h1
    exact .inl ⟨k, i, b0, h0, h2'.trans h2, h3'.trans h3⟩
  · obtain ⟨p, hp', rfl⟩ := mem_values_iff.mp hv
    rw [allPos_setAtE, allPos_setAtE, allPos_erase, hpos] at hp'
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl
    · rw [valAt_setAtE_self h00]; exact hxvb
    · rw [valAt_setAtE_other _ _ _ _ hne, valAt_setAtE_self h01]; exact .inr (.inr rfl)

end Ochr.Meaning.Steps.Machine

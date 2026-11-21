import Ochr.Meaning.RunCongr

/-!
# Frame locality, part 1: replacing the bindings at a set of positions (exists3, 2026-11-21)

Frame locality compares a run at a state `s` with the run at `qset Q β' s`: `s` with the bindings at
the positions `Q` replaced by `β'` (and no borrow held there). The theorem (`FrameLocal/Run.lean`)
is an EQUATION: the run at `qset Q β' s` is the run at `s` with `qset Q β'` applied to its final state.
Stated so, it carries its own invariant: at `β' := β`, where `qset Q β s = s`, it says the run's final
state is again fixed by `qset Q β` (the bindings at `Q` unchanged and no borrow held there), with no
separate preservation lemma.

This file: the transform, and how it meets the state's primitives.
-/

namespace Ochr.Meaning.DataModel.Exists.FrameLocal

open Ochr Ochr.Meaning SState
open Classical

section
variable (Q : Pos → Prop) (β : Pos → SBinding)

/-- Frame `f` with its bindings at `Q` replaced by `β`. -/
noncomputable def qframe (f : Nat) (fr : SFrame) : SFrame :=
  { fr with binds := fr.binds.zipIdx.map fun bi => if Q (.bind f bi.2) then β (.bind f bi.2) else bi.1 }

/-- **The transform**: every binding at a position of `Q` replaced by `β`, and no borrow held at
`Q`. Positions of `Q` that do not exist are left alone. -/
noncomputable def qset (s : SState) : SState :=
  { s with env := s.env.zipIdx.map (fun fi => qframe Q β fi.2 fi.1),
           shape := fun p => if Q p then none else s.shape p }

variable {Q β}

@[simp] theorem qframe_temps (f : Nat) (fr : SFrame) : (qframe Q β f fr).temps = fr.temps := rfl

theorem qframe_binds_get (f : Nat) (fr : SFrame) (i : Nat) :
    (qframe Q β f fr).binds[i]? = (fr.binds[i]?).map fun b => if Q (.bind f i) then β (.bind f i) else b := by
  simp only [qframe, List.getElem?_map, List.getElem?_zipIdx]
  cases fr.binds[i]? <;> simp

@[simp] theorem qframe_binds_length (f : Nat) (fr : SFrame) : (qframe Q β f fr).binds.length = fr.binds.length := by
  simp [qframe]

theorem qset_env_get (s : SState) (f : Nat) : (qset Q β s).env[f]? = (s.env[f]?).map (qframe Q β f) := by
  simp only [qset, List.getElem?_map, List.getElem?_zipIdx]
  cases s.env[f]? <;> simp

@[simp] theorem qset_env_length (s : SState) : (qset Q β s).env.length = s.env.length := by simp [qset]
@[simp] theorem qset_shape (s : SState) : (qset Q β s).shape = fun p => if Q p then none else s.shape p := rfl
@[simp] theorem qset_nextLoan (s : SState) : (qset Q β s).nextLoan = s.nextLoan := rfl
@[simp] theorem qset_lent (s : SState) : (qset Q β s).lent = s.lent := rfl
@[simp] theorem qset_heldTy (s : SState) : (qset Q β s).heldTy = s.heldTy := rfl
@[simp] theorem qset_heldMem (s : SState) : (qset Q β s).heldMem = s.heldMem := rfl

@[simp] theorem qset_topIdx (s : SState) : (qset Q β s).topIdx = s.topIdx := by
  show (qset Q β s).env.length - 1 = s.env.length - 1
  rw [qset_env_length]

theorem qset_bind (s : SState) (f i : Nat) :
    ((qset Q β s).env[f]?.bind (·.binds[i]?)) =
      (s.env[f]?.bind (·.binds[i]?)).map fun b => if Q (.bind f i) then β (.bind f i) else b := by
  rw [qset_env_get]
  cases s.env[f]? with
  | none => rfl
  | some fr => simp only [Option.map_some, Option.bind_some, qframe_binds_get]

theorem qset_temp (s : SState) (f i : Nat) :
    ((qset Q β s).env[f]?.bind (·.temps[i]?)) = s.env[f]?.bind (·.temps[i]?) := by
  rw [qset_env_get]
  cases s.env[f]? <;> rfl

theorem qset_getLast (s : SState) : (qset Q β s).env.getLast? = s.env.getLast?.map (qframe Q β s.topIdx) := by
  rw [List.getLast?_eq_getElem?, List.getLast?_eq_getElem?, qset_env_length, qset_env_get]; rfl

theorem qset_varPos (s : SState) (i : Nat) : (qset Q β s).varPos i = s.varPos i := by
  unfold SState.varPos
  rw [qset_getLast, qset_topIdx]
  cases s.env.getLast? <;> simp

theorem qset_resolve (s : SState) (p : Place) : resolve (qset Q β s) p = resolve s p := by
  simp only [resolve, qset_varPos]

theorem qset_positions (s : SState) : (qset Q β s).positions = s.positions := by
  rw [positions_eq, positions_eq, qset_env_length]
  congr 1; funext f
  rw [qset_env_get]
  cases s.env[f]? with
  | none => rfl
  | some fr => simp [framePos]

theorem qset_lookup (s : SState) (p : Pos) :
    (qset Q β s).lookup p = match p with
      | .bind f i => (s.lookup p).map fun v => if Q (.bind f i) then (β (.bind f i)).val else v
      | .temp _ _ => s.lookup p := by
  cases p with
  | bind f i =>
    simp only [lookup, qset_bind]
    cases s.env[f]?.bind (·.binds[i]?) with
    | none => rfl
    | some b => by_cases h : Q (.bind f i) <;> simp [h]
  | temp f i => simp only [lookup, qset_temp]

end

section
variable {Q : Pos → Prop} {β : Pos → SBinding}

theorem qset_valAt_not (s : SState) {p : Pos} (h : ¬ Q p) : (qset Q β s).valAt p = s.valAt p := by
  cases p with
  | bind f i => simp only [SState.valAt, qset_bind]; cases s.env[f]?.bind (·.binds[i]?) <;> simp [h]
  | temp f i => simp only [SState.valAt, qset_temp]

theorem bind_isSome_of_mem {s : SState} {f i : Nat} (hp : Pos.bind f i ∈ s.positions) :
    ∃ b, s.env[f]?.bind (·.binds[i]?) = some b := by
  rw [mem_positions] at hp
  simp only [SState.lookup] at hp
  cases e : s.env[f]?.bind (·.binds[i]?) with
  | none => rw [e] at hp; cases hp
  | some b => exact ⟨b, rfl⟩

theorem qset_valAt_of (s : SState) {f i : Nat} (h : Q (.bind f i)) (hp : Pos.bind f i ∈ s.positions) :
    (qset Q β s).valAt (.bind f i) = (β (.bind f i)).val := by
  obtain ⟨b, hb⟩ := bind_isSome_of_mem hp
  simp only [SState.valAt, qset_bind, hb, Option.map_some, if_pos h]

theorem qset_tyAt_not (s : SState) {p : Pos} (h : ¬ Q p) : (qset Q β s).tyAt p = s.tyAt p := by
  cases p with
  | bind f i => simp only [SState.tyAt, qset_bind]; cases s.env[f]?.bind (·.binds[i]?) <;> simp [h]
  | temp f i => rfl

theorem qset_tyAt_of (s : SState) {f i : Nat} (h : Q (.bind f i)) (hp : Pos.bind f i ∈ s.positions) :
    (qset Q β s).tyAt (.bind f i) = (β (.bind f i)).ty := by
  obtain ⟨b, hb⟩ := bind_isSome_of_mem hp
  simp only [SState.tyAt, qset_bind, hb, Option.map_some, if_pos h]

/-- Two states' frames are the same when their bindings and temporaries are. -/
theorem env_ext {s t : SState} (hlen : s.env.length = t.env.length)
    (hb : ∀ f i : Nat, s.env[f]?.bind (·.binds[i]?) = t.env[f]?.bind (·.binds[i]?))
    (ht : ∀ f i : Nat, s.env[f]?.bind (·.temps[i]?) = t.env[f]?.bind (·.temps[i]?)) : s.env = t.env := by
  apply List.ext_getElem?
  intro f
  cases hs : s.env[f]? with
  | none =>
    rw [List.getElem?_eq_none_iff] at hs
    exact (List.getElem?_eq_none_iff.mpr (by omega)).symm
  | some fr =>
    cases ht' : t.env[f]? with
    | none =>
      rw [List.getElem?_eq_none_iff] at ht'
      have := (List.getElem?_eq_some_iff.mp hs).1
      omega
    | some fr' =>
      have h1 : fr.temps = fr'.temps := List.ext_getElem? fun i => by
        have := ht f i; rw [hs, ht'] at this; exact this
      have h2 : fr.binds = fr'.binds := List.ext_getElem? fun i => by
        have := hb f i; rw [hs, ht'] at this; exact this
      cases fr; cases fr'
      simp_all

theorem state_eq {s t : SState} (he : s.env = t.env) (hs : s.shape = t.shape) (hn : s.nextLoan = t.nextLoan)
    (hl : s.lent = t.lent) (hT : s.heldTy = t.heldTy) (hM : s.heldMem = t.heldMem) : s = t := by
  cases s; cases t; simp_all

/-- A frame modification that commutes with the transform at its frame. -/
theorem qset_modify (s : SState) (f : Nat) (g : SFrame → SFrame)
    (hg : ∀ fr, s.env[f]? = some fr → qframe Q β f (g fr) = g (qframe Q β f fr)) :
    (qset Q β s).env.modify f g = (qset Q β { s with env := s.env.modify f g }).env := by
  apply List.ext_getElem?
  intro k
  rw [List.getElem?_modify, qset_env_get, qset_env_get]
  simp only [List.getElem?_modify]
  by_cases hk : f = k
  · subst hk
    cases e : s.env[f]? with
    | none => simp
    | some fr => simp [hg fr e]
  · simp [hk]

theorem frame_ext {a b : SFrame} (hb : ∀ i : Nat, a.binds[i]? = b.binds[i]?) (ht : a.temps = b.temps) : a = b := by
  cases a; cases b; simp only at hb ht; rw [List.ext_getElem? hb, ht]

theorem qset_setAt (s : SState) {p : Pos} (h : ¬ Q p) (v : SVal) :
    (qset Q β s).setAt p v = qset Q β (s.setAt p v) := by
  cases p with
  | bind f i =>
    refine state_eq ?_ rfl rfl rfl rfl rfl
    show (qset Q β s).env.modify f _ = _
    rw [qset_modify s f (fun fr => { fr with binds := fr.binds.modify i fun b => { b with val := v } })
      (fun fr _ => frame_ext (fun j => ?_) rfl)]
    · rfl
    · simp only [qframe_binds_get, List.getElem?_modify]
      by_cases hj : i = j
      · subst hj; cases fr.binds[i]? <;> simp [h]
      · simp [hj]
  | temp f i =>
    refine state_eq ?_ rfl rfl rfl rfl rfl
    show (qset Q β s).env.modify f _ = _
    rw [qset_modify s f (fun fr => { fr with temps := fr.temps.set i v }) (fun fr _ => rfl)]
    rfl

/-- Appending a binding at a position outside `Q`. -/
theorem qframe_append (f : Nat) (fr : SFrame) (b : SBinding) (h : ¬ Q (.bind f fr.binds.length)) :
    qframe Q β f { fr with binds := fr.binds ++ [b] } = { qframe Q β f fr with binds := (qframe Q β f fr).binds ++ [b] } := by
  refine frame_ext (fun j => ?_) rfl
  simp only [qframe_binds_get, List.getElem?_append, qframe_binds_length]
  by_cases hj : j < fr.binds.length
  · simp [hj]
  · simp only [hj, if_false]
    by_cases he : j - fr.binds.length = 0
    · have : j = fr.binds.length := by omega
      subst this; simp [h]
    · simp [List.getElem?_cons, he]

theorem not_q_new {s : SState} (hQ : ∀ p, Q p → p ∈ s.positions) {f : Nat} {fr : SFrame} (hf : s.env[f]? = some fr) :
    ¬ Q (.bind f fr.binds.length) := fun hq => by
  have hp := hQ _ hq
  rw [mem_positions] at hp
  simp [SState.lookup, hf] at hp

theorem qset_pushBind (s : SState) (hQ : ∀ p, Q p → p ∈ s.positions) (b : SBinding) :
    (qset Q β s).pushBind b = qset Q β (s.pushBind b) := by
  refine state_eq ?_ rfl rfl rfl rfl rfl
  show (qset Q β s).env.modify (qset Q β s).topIdx _ = _
  rw [qset_topIdx, qset_modify s s.topIdx (fun fr => { fr with binds := fr.binds ++ [b] })
    (fun fr hf => qframe_append _ _ _ (not_q_new hQ hf))]
  rfl

theorem qset_pushCell (s : SState) (hQ : ∀ p, Q p → p ∈ s.positions) (b : SBinding) :
    (qset Q β s).pushCell b = qset Q β (s.pushCell b) := by
  refine state_eq ?_ rfl rfl rfl rfl rfl
  show (qset Q β s).env.modify 0 _ = _
  rw [qset_modify s 0 (fun fr => { fr with binds := fr.binds ++ [b] })
    (fun fr hf => qframe_append _ _ _ (not_q_new hQ hf))]
  rfl

theorem qset_pushTemp (s : SState) (v : SVal) : (qset Q β s).pushTemp v = qset Q β (s.pushTemp v) := by
  refine state_eq ?_ rfl rfl rfl rfl rfl
  show (qset Q β s).env.modify (qset Q β s).topIdx _ = _
  rw [qset_topIdx, qset_modify s s.topIdx (fun fr => { fr with temps := fr.temps ++ [v] }) (fun fr _ => rfl)]
  rfl

theorem qset_dropLast (s : SState) : (qset Q β s).dropLast = qset Q β s.dropLast := by
  have hg : ∀ fr : SFrame, qframe Q β s.topIdx { fr with binds := fr.binds.dropLast } =
      { qframe Q β s.topIdx fr with binds := (qframe Q β s.topIdx fr).binds.dropLast } := fun fr =>
    frame_ext (fun j => by
      simp only [qframe_binds_get, List.getElem?_dropLast, qframe_binds_length]
      by_cases hj : j < fr.binds.length - 1 <;> simp [hj]) rfl
  refine state_eq ?_ ?_ rfl rfl rfl rfl
  · show (qset Q β s).env.modify (qset Q β s).topIdx _ = _
    rw [qset_topIdx, qset_modify s s.topIdx (fun fr => { fr with binds := fr.binds.dropLast }) (fun fr _ => hg fr)]
    rfl
  · funext p
    simp only [SState.dropLast, qset_shape, qset_getLast, qset_topIdx]
    cases s.env.getLast? with
    | none => simp
    | some fr => simp only [Option.map_some, qframe_binds_length]; split <;> split <;> simp_all

/-- `mapVals` across the transform: a map that keeps `β`'s value at `Q` and is `G` elsewhere. -/
theorem qset_mapVals (X : SState) (G G' : Pos → SVal → SVal) (hT : ∀ f i, ¬ Q (.temp f i))
    (hQ : ∀ f i b, X.env[f]?.bind (·.binds[i]?) = some b → Q (.bind f i) →
      G' (.bind f i) (β (.bind f i)).val = (β (.bind f i)).val)
    (hN : ∀ p v, ¬ Q p → G' p v = G p v) :
    (qset Q β X).mapVals G' = qset Q β (X.mapVals G) := by
  refine state_eq (env_ext (by simp [SState.mapVals]) (fun f i => ?_) (fun f i => ?_)) rfl rfl rfl rfl rfl
  · have e1 := bindAt?_mapVals (qset Q β X) G' f i
    have e2 := bindAt?_mapVals X G f i
    simp only [bindAt?] at e1 e2
    rw [e1, qset_bind, qset_bind, e2]
    cases hb : X.env[f]?.bind (·.binds[i]?) with
    | none => rfl
    | some b =>
      by_cases hq : Q (.bind f i)
      · simp only [Option.map_some, if_pos hq, hQ f i b hb hq]
      · simp only [Option.map_some, if_neg hq, hN _ _ hq]
  · have e1 := tempAt?_mapVals (qset Q β X) G' f i
    have e2 := tempAt?_mapVals X G f i
    simp only [tempAt?] at e1 e2
    rw [e1, qset_temp, qset_temp, e2, show G' (.temp f i) = G (.temp f i) from funext fun v => hN _ v (hT f i)]

theorem qset_shape_eq {s : SState} (hsh : ∀ p, Q p → s.shape p = none) : (qset Q β s).shape = s.shape := by
  funext p; by_cases h : Q p <;> simp [h, hsh]

/-- [End] across the transform: no borrow is held at `Q`, and `β`'s values there are constant. -/
theorem qset_endLabel (s : SState) (hT : ∀ f i, ¬ Q (.temp f i)) (hsh : ∀ p, Q p → s.shape p = none)
    (hc : ∀ p, Q p → ∃ c, (β p).val = fun _ => c) (l : Nat) :
    (qset Q β s).endLabel l = qset Q β (s.endLabel l) := by
  have hS := qset_shape_eq (β := β) hsh
  have hfind : (qset Q β s).positions.find? (fun p => decide ((qset Q β s).shape p = some l)) =
      s.positions.find? (fun p => decide (s.shape p = some l)) := by rw [qset_positions, hS]
  cases hf : s.positions.find? (fun p => decide (s.shape p = some l)) with
  | none =>
    rw [endLabel_of_find_none s l hf, endLabel_of_find_none _ l (hfind.trans hf)]
  | some r =>
    have hr : ¬ Q r := fun hq => by
      have := List.find?_some hf
      simp [hsh r hq] at this
    rw [endLabel_of_find s l r hf, endLabel_of_find _ l r (hfind.trans hf)]
    rw [← qset_mapVals _ _ (fun p _ => (((qset Q β s).toMean.semEnd r l).val · p)) hT]
    · refine congrArg (fun t => SState.mapVals t _) (state_eq rfl ?_ rfl rfl rfl rfl)
      funext p
      simp only [Mean.semEnd, SState.toMean, qset_shape]
      by_cases hp : Q p
      · have hpr : p ≠ r := fun e => hr (e ▸ hp)
        simp [hp, hpr, hsh p hp]
      · simp [hp]
    · intro f i b hb hq
      have hpr : Pos.bind f i ≠ r := fun e => hr (e ▸ hq)
      have hmem : Pos.bind f i ∈ s.positions := by rw [mem_positions]; simp [SState.lookup, hb]
      obtain ⟨c, hc⟩ := hc _ hq
      funext φ
      simp only [Mean.semEnd, SState.toMean, if_neg hpr, qset_valAt_of s hq hmem, hc]
    · intro p v hp
      funext φ
      by_cases hpr : p = r
      · simp [Mean.semEnd, hpr]
      · simp only [Mean.semEnd, SState.toMean, if_neg hpr, qset_valAt_not s hp, qset_valAt_not s hr]

theorem endLabel_shape_none {s : SState} (hsh : ∀ p, Q p → s.shape p = none) (l : Nat) :
    ∀ p, Q p → (s.endLabel l).shape p = none := by
  intro p hp
  cases hf : s.positions.find? (fun p => decide (s.shape p = some l)) with
  | none => rw [endLabel_of_find_none s l hf]; exact hsh p hp
  | some r =>
    rw [endLabel_shape s l r hf]
    show (if p = r then none else s.shape p) = none
    split <;> simp_all

theorem qset_foldl_endLabel (hT : ∀ f i, ¬ Q (.temp f i)) (hc : ∀ p, Q p → ∃ c, (β p).val = fun _ => c) :
    ∀ (ls : List Nat) (s : SState), (∀ p, Q p → s.shape p = none) →
      ls.foldl SState.endLabel (qset Q β s) = qset Q β (ls.foldl SState.endLabel s)
  | [], _, _ => rfl
  | l :: ls, s, hsh => by
    simp only [List.foldl_cons]
    rw [qset_endLabel s hT hsh hc l]
    exact qset_foldl_endLabel hT hc ls _ (endLabel_shape_none hsh l)

theorem foldl_endLabel_shape_none : ∀ (ls : List Nat) {s : SState}, (∀ p, Q p → s.shape p = none) →
    ∀ p, Q p → (ls.foldl SState.endLabel s).shape p = none
  | [], _, h => h
  | l :: ls, _, h => foldl_endLabel_shape_none ls (endLabel_shape_none h l)

theorem qset_liveLabels {s : SState} (hsh : ∀ p, Q p → s.shape p = none) :
    (qset Q β s).liveLabels = s.liveLabels := by
  simp only [SState.liveLabels, qset_positions, qset_shape_eq hsh]

theorem qset_reached (s : SState) : (qset Q β s).reached = s.reached := rfl

theorem qset_typedFuture {s : SState} (hsh : ∀ p, Q p → s.shape p = none) (φ : Future) :
    (qset Q β s).typedFuture φ = s.typedFuture φ := by
  unfold SState.typedFuture; rw [qset_liveLabels hsh]; rfl

theorem qset_access (hT : ∀ f i, ¬ Q (.temp f i)) (hc : ∀ p, Q p → ∃ c, (β p).val = fun _ => c)
    (p : Pos) (hit : List Step → Bool) (s : SState) (hsh : ∀ q, Q q → s.shape q = none) :
    (qset Q β s).access p hit = qset Q β (s.access p hit) := by
  unfold SState.access
  dsimp only
  rw [qset_liveLabels hsh]
  generalize List.range s.liveLabels.length = xs
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rw [qset_liveLabels hsh, qset_reached, qset_foldl_endLabel hT hc _ s hsh]
    exact ih _ (foldl_endLabel_shape_none _ hsh)

theorem access_shape_none (p : Pos) (hit : List Step → Bool) :
    ∀ (s : SState), (∀ q, Q q → s.shape q = none) → ∀ q, Q q → (s.access p hit).shape q = none := by
  intro s hsh
  unfold SState.access
  dsimp only
  generalize List.range s.liveLabels.length = xs
  induction xs generalizing s with
  | nil => exact hsh
  | cons x xs ih => exact ih _ (foldl_endLabel_shape_none _ hsh)

theorem qset_holderOf {s : SState} (hsh : ∀ p, Q p → s.shape p = none) (l : Nat) :
    (qset Q β s).holderOf l = s.holderOf l := by
  unfold SState.holderOf; rw [qset_positions, qset_shape_eq hsh]

theorem not_q_of_shape {s : SState} (hsh : ∀ p, Q p → s.shape p = none) {r : Pos} {l : Nat}
    (h : s.shape r = some l) : ¬ Q r := fun hq => by rw [hsh r hq] at h; cases h

/-- A shape update at a position outside `Q`. -/
theorem qset_setShape (s : SState) {pos : Pos} (h : ¬ Q pos) (o : Option Nat) :
    { qset Q β s with shape := fun q => if q = pos then o else (qset Q β s).shape q } =
      qset Q β { s with shape := fun q => if q = pos then o else s.shape q } := by
  refine state_eq rfl ?_ rfl rfl rfl rfl
  funext q
  by_cases hq : q = pos
  · subst hq; simp [h]
  · simp [hq]

theorem qset_takeLabel {s : SState} (hsh : ∀ p, Q p → s.shape p = none) (l : Nat) :
    (qset Q β s).takeLabel l = qset Q β (s.takeLabel l) := by
  unfold SState.takeLabel
  rw [qset_holderOf hsh]
  cases hr : s.holderOf l with
  | none => rfl
  | some r =>
    have hq : ¬ Q r := not_q_of_shape hsh (holderOf_spec hr).2
    dsimp only
    rw [qset_setAt s hq]
    refine state_eq rfl ?_ rfl rfl rfl rfl
    funext q
    by_cases e : q = r <;> by_cases h2 : Q q <;> simp [e, h2, hsh q]

theorem takeLabel_shape_none {s : SState} (hsh : ∀ p, Q p → s.shape p = none) (l : Nat) :
    ∀ p, Q p → (s.takeLabel l).shape p = none := by
  intro p hp
  unfold SState.takeLabel
  cases s.holderOf l with
  | none => exact hsh p hp
  | some r => show (if p = r then none else s.shape p) = none; split <;> simp_all

theorem qset_pushTempShaped (s : SState) (hT : ∀ f i, ¬ Q (.temp f i)) (v : SVal) (l : Nat) :
    (qset Q β s).pushTempShaped v l = qset Q β (s.pushTempShaped v l) := by
  unfold SState.pushTempShaped
  dsimp only
  rw [qset_pushTemp, qset_getLast, qset_topIdx]
  cases (s.pushTemp v).env.getLast? with
  | none => rfl
  | some fr =>
    simp only [Option.map_some, qframe_temps]
    exact qset_setShape _ (hT _ _) _

theorem pushBind_getLast (s : SState) (b : SBinding) :
    (s.pushBind b).env.getLast? = s.env.getLast?.map fun fr => { fr with binds := fr.binds ++ [b] } := by
  rw [List.getLast?_eq_getElem?, List.getLast?_eq_getElem?]
  simp only [SState.pushBind, List.length_modify, List.getElem?_modify]
  simp [SState.topIdx]

theorem qset_pushBindShaped (s : SState) (hQ : ∀ p, Q p → p ∈ s.positions)
    (hsh : ∀ p, Q p → s.shape p = none) (b : SBinding) :
    pushBindShaped (qset Q β s) b = qset Q β (pushBindShaped s b) := by
  unfold pushBindShaped
  cases hl : b.ty.label with
  | none => exact qset_pushBind s hQ b
  | some l =>
    dsimp only
    have hQ' : ∀ p, Q p → p ∈ (s.takeLabel l).positions := fun p hp => by rw [takeLabel_positions]; exact hQ p hp
    rw [qset_takeLabel hsh, qset_pushBind _ hQ', qset_getLast, qset_topIdx, pushBind_getLast]
    cases hg : (s.takeLabel l).env.getLast? with
    | none => rfl
    | some fr =>
      simp only [Option.map_some, qframe_binds_length, List.length_append, List.length_singleton,
        Nat.add_sub_cancel, topIdx_pushBind']
      refine qset_setShape _ (not_q_new hQ' ?_) _
      rw [List.getLast?_eq_getElem?] at hg; exact hg

@[simp] theorem qset_setLent (s : SState) (l : Nat) (xs : List Site) :
    (qset Q β s).setLent l xs = qset Q β (s.setLent l xs) := rfl
@[simp] theorem qset_setHeldTy (s : SState) (l : Nat) (T : TyM) :
    (qset Q β s).setHeldTy l T = qset Q β (s.setHeldTy l T) := rfl
@[simp] theorem qset_setHeldMem (s : SState) (l : Nat) (v : Sem) :
    (qset Q β s).setHeldMem l v = qset Q β (s.setHeldMem l v) := rfl
theorem qset_freshLoan (s : SState) : (qset Q β s).freshLoan = (s.freshLoan.1, qset Q β s.freshLoan.2) := rfl

end

/-! ## Under a fresh bottom frame: `Q` moves up -/

/-- `Q` one frame up (`SState.under`'s numbering). -/
def Qup (Q : Pos → Prop) : Pos → Prop := fun p => match p.down? with | some q => Q q | none => False
/-- `β` one frame up. -/
def βup (β : Pos → SBinding) : Pos → SBinding := fun p => match p.down? with | some q => β q | none => β p

section
variable {Q : Pos → Prop} {β : Pos → SBinding}

theorem qset_under (s : SState) : (qset Q β s).under = qset (Qup Q) (βup β) s.under := by
  by_cases he : s.env = []
  · have he' : (qset Q β s).env = [] := List.eq_nil_of_length_eq_zero (by rw [qset_env_length, he]; rfl)
    refine state_eq ?_ ?_ rfl rfl rfl rfl
    · simp only [SState.under, he, List.isEmpty_nil, if_true, qset]
      simp [List.zipIdx, qframe]
    · funext p
      simp only [SState.under, qset_shape, Qup]
      rcases p with ⟨_ | f, i⟩ | ⟨_ | f, i⟩ <;> simp [Pos.down?] <;> congr
  · have he' : (qset Q β s).env ≠ [] := fun h => he (List.eq_nil_of_length_eq_zero (by
      rw [← qset_env_length (Q := Q) (β := β), h]; rfl))
    refine state_eq (env_ext ?_ (fun f i => ?_) (fun f i => ?_)) ?_ rfl rfl rfl rfl
    · rw [qset_env_length, under_env_ne _ he', under_env_ne _ he]; simp
    · rw [qset_bind, under_env_ne _ he', under_env_ne _ he]
      rcases f with _ | f
      · simp
      · simp only [List.getElem?_cons_succ, qset_bind, Qup, βup, Pos.down?]
        congr 1
    · rw [qset_temp, under_env_ne _ he', under_env_ne _ he]
      rcases f with _ | f
      · simp
      · simp only [List.getElem?_cons_succ, qset_temp]
    · funext p
      simp only [SState.under, qset_shape, Qup]
      rcases p with ⟨_ | f, i⟩ | ⟨_ | f, i⟩ <;> simp [Pos.down?] <;> congr

end

end Ochr.Meaning.DataModel.Exists.FrameLocal

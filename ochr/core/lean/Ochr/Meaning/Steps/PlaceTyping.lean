import Ochr.Meaning.Steps.Statements
import Ochr.Meaning.SitesFollow
import Ochr.Meaning.BotWrite

/-!
# Places along a path, and the checker's typing of them (docs/31 D40, D44)

A place's parent and the steps between them; the join's grain at each step (`GrainOk`, `StepOk`);
the checker's content of a place one step below another (`ckContent_snoc`) and the value of Ω it is
reached from (`ckContent_root`); and the reference's scope as the checker's top frame's readings
(`rel_scopeOf`). Moved here from `MovedPlace.lean` and `DropOneAsm.lean` so that the drop's own
obligations (`DropOne.content_follow`) can read a place's typing step by step.
-/

namespace Ochr.Meaning.Steps

open Ochr.Meaning

/-- A place's parent (`Machine.movedPlace`'s local `parent`). -/
def parentOf : Place → Option Place
  | .deref p | .proj _ p | .field _ p => some p
  | .var _ => none

theorem steps_parent {q p : Place} (h : parentOf q = some p) :
    ∃ x, q.steps = (p.steps.1, p.steps.2 ++ [x]) ∧ ((x = .deref) ∨ (∃ i, x = .proj i) ∨ ∃ g, x = .field g) := by
  cases q with
  | var i => simp [parentOf] at h
  | deref p' =>
    simp only [parentOf, Option.some.injEq] at h; subst h
    exact ⟨.deref, by simp only [Place.steps], .inl rfl⟩
  | proj j p' =>
    simp only [parentOf, Option.some.injEq] at h; subst h
    exact ⟨.proj j, by simp only [Place.steps], .inr (.inl ⟨j, rfl⟩)⟩
  | field g p' =>
    simp only [parentOf, Option.some.injEq] at h; subst h
    exact ⟨.field g, by simp only [Place.steps], .inr (.inr ⟨g, rfl⟩)⟩

theorem ckVarPos_mem {env : Env} {i : Nat} {pos : Pos} (h : ckVarPos env i = some pos) : pos ∈ allPos env := by
  unfold ckVarPos at h
  split at h
  · rename_i hi
    simp only [Option.some.injEq] at h
    subst h
    have hne : env.size ≠ 0 := by
      intro h0
      have hd : env[env.size - 1]! = (default : Frame) := by simp [h0]
      rw [hd] at hi
      have : (default : Frame).binds.size = 0 := rfl
      omega
    have hf : env[env.size - 1]? = some env[env.size - 1]! := by
      rw [Array.getElem?_eq_getElem (by omega), getElem!_pos env (env.size - 1) (by omega)]
    generalize hfr : env[env.size - 1]! = fr at hi hf
    have hb : fr.binds[fr.binds.size - 1 - i]? = some fr.binds[fr.binds.size - 1 - i]! := by
      rw [Array.getElem?_eq_getElem (by omega), getElem!_pos _ _ (by omega)]
    exact bind_mem_allPos env _ _ _ _ hf hb
  · cases h

theorem grain_parent {D : Decisions} {Γ : List IndDecl} {sc : List DeclInfo} {q p : Place}
    (hpar : parentOf q = some p) (h : GrainOk D Γ sc q) : GrainOk D Γ sc p := by
  obtain ⟨x, hx, -⟩ := steps_parent hpar
  intro p' y rest h1 h2
  apply h p' y (rest ++ [x])
  · rw [h1, hx]
  · rw [hx]; simp [h2]

/-- The grain at the parent step itself. -/
theorem grain_step {D : Decisions} {Γ : List IndDecl} {sc : List DeclInfo} {q p : Place} {x : Step}
    (hx : q.steps = (p.steps.1, p.steps.2 ++ [x])) (h : GrainOk D Γ sc q) : StepOk Γ (D.placeDecl sc p) x :=
  h p x [] (by rw [hx]) (by rw [hx])

/-- The reference's declared readings in scope, as a list expression. -/
theorem scope_decls (s : SState) : scopeOf s = ((s.env.getLast?.map fun fr => fr.binds.map (·.decl)).getD []).reverse := by
  unfold scopeOf; cases s.env.getLast? <;> rfl

/-- **The reference's readings in scope are the checker's top frame's** (`Rel`'s skeleton): the
scope `GrainOk` and the aligned decisions are read at is the one `ShapeFacts` is stated at. -/
theorem rel_scopeOf (K : RunCtx) (ρ : Assignment) (φ : Future) {st : MState} {s : SState} {π : Nat → Nat}
    (hs : Rel K ρ φ π st s) : scopeOf s = DecideScope.topReadings st := by
  have hk := congrArg (fun l => (l.getLast?).map fun bs => bs.map fun x : TyM × Option (List PiParam × PiOut) × Option (String × List Sem) × DeclInfo => x.2.2.2) hs.skel
  simp only [List.getLast?_map, Option.map_map, Function.comp_def, List.map_map] at hk
  rw [scope_decls]
  unfold DecideScope.topReadings
  have e2 : ((SM' K ρ st).env.getLast?.map fun fr => fr.binds.map (·.decl)) = st.env.back?.map (·.binds.toList.map (·.decl)) := by
    simp only [SM', MState.sstate]
    rw [List.getLast?_map, Option.map_map]
    have hf : ∀ (l : List Frame), (l.zipIdx).getLast?.map Prod.fst = l.getLast? := fun l => by
      rw [← List.getLast?_map]; simp
    have e3 : Array.back? st.env = st.env.toList.getLast? := by simp [Array.back?, List.getLast?_eq_getElem?]
    rw [e3, ← hf st.env.toList, Option.map_map]
    congr 1
    funext x
    simp only [Function.comp_def, List.map_map]
    have hz : ∀ (l : List Binding), l.zipIdx.map (fun y => y.1.decl) = l.map (·.decl) := fun l => by
      rw [show (fun y : Binding × Nat => y.1.decl) = (fun b : Binding => b.decl) ∘ Prod.fst from rfl, ← List.map_map]
      simp
    exact hz _
  simp only [bindSkel] at hk
  rw [← e2, hk]

/-- The content of a place one step below another. -/
theorem ckContent_snoc {env : Env} {q p : Place} {x : Step} (hx : q.steps = (p.steps.1, p.steps.2 ++ [x])) :
    ckContent env q = (ckContent env p).bind (stepV x) := by
  unfold ckContent
  rw [hx]
  cases ckVarPos env p.steps.1 with
  | none => rfl
  | some pos =>
    simp only [Option.bind_some]
    rw [follow_append]
    cases (valAt env pos).follow p.steps.2 with
    | none => rfl
    | some w => simp only [Option.bind_some, Value.follow]; cases stepV x w <;> rfl

/-- A place's content is reached from a value of Ω. -/
theorem ckContent_root {env : Env} {p : Place} {v : Value} (h : ckContent env p = some v) :
    ∃ root ∈ Env.values env, root.follow p.steps.2 = some v := by
  unfold ckContent at h
  cases hv : ckVarPos env p.steps.1 with
  | none => simp [hv] at h
  | some pos =>
    rw [hv, Option.bind_some] at h
    exact ⟨valAt env pos, List.mem_map.mpr ⟨pos, ckVarPos_mem hv, rfl⟩, h⟩


/-! ## Following a path on a meaning, step by step -/

theorem sem_follow_append (dm : DataModel) (Γ : List IndDecl) :
    ∀ (T : TyS) (s : Sem) (a b : List Step),
      Sem.follow dm Γ T s (a ++ b) = (Sem.follow dm Γ T s a).bind fun p => Sem.follow dm Γ p.2 p.1 b
  | T, s, [], b => by simp [Sem.follow]
  | T, s, x :: a, b => by
    simp only [List.cons_append, Sem.follow]
    cases Sem.step dm Γ T x s with
    | none => rfl
    | some p => simp only [Option.bind_some]; exact sem_follow_append dm Γ p.2 p.1 a b

theorem sem_asNat_proof : Sem.asNat .proof = none := by
  cases h : Sem.asNat .proof with
  | none => rfl
  | some n => exact absurd (Sem.asNat_some h) (by simp)

/-- A step on `⋆` stays at `⋆` (every field of a proof is a proof). -/
theorem sem_step_proof (dm : DataModel) (Γ : List IndDecl) (T : TyS) (x : Step) :
    ∃ T', Sem.step dm Γ T x .proof = some (.proof, T') := by
  cases x with
  | deref => exact ⟨T, rfl⟩
  | proj i =>
    rcases i with _ | i
    · refine ⟨.plain .err, ?_⟩
      simp only [Sem.step, sem_asNat_proof, Sem.stepField]
    · exact ⟨.plain .err, by simp [Sem.step, Sem.stepField]⟩
  | field g => exact ⟨.plain .err, by simp [Sem.step, Sem.stepField]⟩

/-- `.0` into a constructor value of constructor `0` is its first field (not a number's predecessor). -/
theorem sem_step_proj0_dat (dm : DataModel) (Γ : List IndDecl) (T : TyS) (nm : String) (ps fs : List Sem)
    (el : Option ((A : Type) × A)) :
    Sem.step dm Γ T (.proj 0) (.dat nm ps 0 fs el) = Sem.stepField dm Γ 0 0 (.dat nm ps 0 fs el) := by
  simp only [Sem.step, Sem.asNat_dat]

/-- A field of a constructor value, by its constructor. -/
theorem stepField_dat (dm : DataModel) (Γ : List IndDecl) (nm : String) (ps fs : List Sem) (c i : Nat)
    (el : Option ((A : Type) × A)) {x : Sem} (h : fs[i]? = some x) :
    ∃ T', Sem.stepField dm Γ c i (.dat nm ps c fs el) = some (x, T') := by
  exact ⟨contentTyS dm Γ nm ps c i (fs.take i) x, by simp [Sem.stepField, h]⟩

/-- A constructor's fields' meanings, one by one, each at some hint. -/
theorem meanFields_get (dm : DataModel) (C : CodeMeaning) (Γ : List IndDecl) (ρ : Assignment) (φ : Future)
    (d : IndDecl) (ps : List Sem) (c : Nat) :
    ∀ (fs : List Value) (j : Nat) (earlier : List Sem) (i : Nat) (v : Value), fs[i]? = some v →
      ∃ H, (Value.meanFields dm C Γ ρ φ d ps c j earlier fs)[i]? = some (Value.mean dm C Γ ρ φ H v)
  | [], _, _, i, v, h => by simp at h
  | w :: ws, j, earlier, i, v, h => by
    rw [Value.meanFields]
    rcases i with _ | i
    · simp only [List.getElem?_cons_zero, Option.some.injEq] at h ⊢
      subst h; exact ⟨_, rfl⟩
    · simp only [List.getElem?_cons_succ] at h ⊢
      exact meanFields_get dm C Γ ρ φ d ps c ws _ _ i v h

/-- `ctorM` is the constructor value describing itself. -/
theorem ctorM_dat (dm : DataModel) (d : IndDecl) (ps : List Sem) (c : Nat) (fs : List Sem) :
    ∃ el, dm.ctorM d ps c fs = .dat d.name ps c fs el := by
  unfold DataModel.ctorM
  split
  · split
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

section
variable (dm : DataModel) (C : CodeMeaning) (Γ : List IndDecl) (ρ : Assignment) (f : Future)

/-- The step into a field of a constructor value of a declared inductive that is not bare. -/
theorem step_mean_ind {n : String} {d : IndDecl} (c : Nat) (hh : Hint) (ps fs' : List Value) (x : Step) (i : Nat)
    (v : Value) (H T : TyS) (hd : Γ.find? (·.name == n) = some d)
    (hb : (Value.ind n c hh ps fs').anyAtom (Value.bareCtor Γ) = false) (hv : fs'[i]? = some v)
    (hx : (x = .proj i ∧ c = 0) ∨ ∃ g, x = .field g ∧ g.idx = i ∧ g.ctor = c) :
    ∃ s' T', Sem.step dm Γ T x (Value.mean dm C Γ ρ f H (.ind n c hh ps fs')) = some (s', T') ∧
      (s' = .proof ∨ ∃ H', s' = Value.mean dm C Γ ρ f H' v) := by
  rw [Value.anyAtom] at hb
  simp only [Bool.or_eq_false_iff] at hb
  have hps : (ps.isEmpty && !d.params.isEmpty) = false := by
    cases ps with
    | nil => have := hb.1; simp [Value.bareCtor, hd] at this; simp [this]
    | cons _ _ => rfl
  rw [Value.mean]
  simp only [hd, hps, Bool.false_eq_true, ↓reduceIte]
  split
  · obtain ⟨T', hT'⟩ := sem_step_proof dm Γ T x
    exact ⟨.proof, T', hT', .inl rfl⟩
  · obtain ⟨el, hel⟩ := ctorM_dat dm d (Value.meanParams dm C Γ ρ f d 0 [] ps) c
      (Value.meanFields dm C Γ ρ f d (Value.meanParams dm C Γ ρ f d 0 [] ps) c 0 [] fs')
    rw [hel]
    obtain ⟨H', hH'⟩ := meanFields_get dm C Γ ρ f d (Value.meanParams dm C Γ ρ f d 0 [] ps) c fs' 0 [] i v hv
    obtain ⟨T', hT'⟩ := stepField_dat dm Γ d.name (Value.meanParams dm C Γ ρ f d 0 [] ps)
      (Value.meanFields dm C Γ ρ f d (Value.meanParams dm C Γ ρ f d 0 [] ps) c 0 [] fs') c i el hH'
    refine ⟨_, T', ?_, .inr ⟨H', rfl⟩⟩
    rcases hx with ⟨rfl, rfl⟩ | ⟨g, rfl, rfl, hgc⟩
    · rcases i with _ | i
      · rw [sem_step_proj0_dat]; exact hT'
      · simpa [Sem.step] using hT'
    · simpa [Sem.step, hgc] using hT'

/-- **One step of a place, on the checker's value and on its meaning** (at the join's grain, by
the checker's typing of the place): the reference's step from the value's meaning is the meaning of
the value the checker's step reaches, or `⋆` (a step inside a proof). -/
theorem step_mean (r : DeclInfo) (x : Step) (hx : StepOk Γ r x) :
    ∀ (w v : Value) (H T : TyS), stepV x w = some v →
      (∀ n args, r = .ind n args → (Γ.find? (·.name == n)).isSome → w.fitsInd n = true) →
      w.anyAtom (Value.bareCtor Γ) = false →
      ∃ s' T', Sem.step dm Γ T x (Value.mean dm C Γ ρ f H w) = some (s', T') ∧
        (s' = .proof ∨ ∃ H', s' = Value.mean dm C Γ ρ f H' v)
  | .gloan l w, v, H, T, h, hf, hb => by
    have e : stepV x (.gloan l w) = stepV x w := by cases x <;> rfl
    rw [e] at h
    rw [Value.anyAtom] at hb
    simp only [Bool.or_eq_false_iff] at hb
    obtain ⟨s', T', h1, h2⟩ := step_mean r x hx w v H T h
      (fun n args e hn => by have := hf n args e hn; simpa [Value.fitsInd] using this) hb.2
    exact ⟨s', T', by simpa [Value.mean] using h1, h2⟩
  | .proof, v, H, T, h, _, _ => by
    cases x with
    | deref => simp [stepV] at h
    | proj i | field g =>
      simp only [stepV, Option.some.injEq] at h; subst h
      obtain ⟨T', hT'⟩ := sem_step_proof dm Γ T _
      exact ⟨.proof, T', by simpa [Value.mean] using hT', .inl rfl⟩
  | .borrow l w, v, H, T, h, hf, _ => by
    cases x with
    | deref =>
      simp only [stepV, Option.some.injEq] at h; subst h
      exact ⟨_, T, by simp [Sem.step, Value.mean], .inr ⟨H, rfl⟩⟩
    | proj i | field g => simp [stepV] at h
  | .ind ty c hh ps fs', v, H, T, h, hf, hb => by
    cases x with
    | deref => simp [stepV] at h
    | proj i =>
      obtain ⟨n, args, d, rfl, hd, -⟩ := hx
      have hty := hf n args rfl (by simp [hd])
      simp only [Value.fitsInd, beq_iff_eq] at hty; subst hty
      rcases c with _ | c
      · exact step_mean_ind dm C Γ ρ f 0 hh ps fs' (.proj i) i v H T hd hb (by simpa [stepV] using h) (.inl ⟨rfl, rfl⟩)
      · simp [stepV] at h
    | field g =>
      obtain ⟨n, args, d, rfl, hd, -⟩ := hx
      have hty := hf n args rfl (by simp [hd])
      simp only [Value.fitsInd, beq_iff_eq] at hty; subst hty
      simp only [stepV] at h
      split at h
      · rename_i hc
        simp only [Bool.and_eq_true, beq_iff_eq] at hc
        exact step_mean_ind dm C Γ ρ f c hh ps fs' (.field g) g.idx v H T hd hb h (.inr ⟨g, rfl, rfl, hc.2.symm⟩)
      · cases h
  | .bot, _, _, _, h, _, _ | .loan _, _, _, _, h, _, _ | .abs _, _, _, _, h, _, _
  | .sealed _, _, _, _, h, _, _ | .zero, _, _, _, h, _, _ | .unit, _, _, _, h, _, _
  | .gfn _, _, _, _, h, _, _ | .clo .., _, _, _, h, _, _ | .tNat, _, _, _, h, _, _
  | .tUnit, _, _, _, h, _, _ | .tEq .., _, _, _, h, _, _ | .tRef _, _, _, _, h, _, _
  | .tPi .., _, _, _, h, _, _ | .sort _, _, _, _, h, _, _ | .tInd .., _, _, _, h, _, _ => by
    cases x <;> simp [stepV] at h
  | .succ w, v, H, T, h, hf, _ => by
    cases x with
    | deref => simp [stepV] at h
    | proj i => obtain ⟨n, args, d, rfl, hd, -⟩ := hx; have := hf n args rfl (by simp [hd]); simp [Value.fitsInd] at this
    | field g => obtain ⟨n, args, d, rfl, hd, -⟩ := hx; have := hf n args rfl (by simp [hd]); simp [Value.fitsInd] at this

end

/-- The meaning at the position a variable resolves to is its value's meaning, at some hint. -/
theorem envMean_ck (dm : DataModel) (C : CodeMeaning) (Γ : List IndDecl) (ρ : Assignment) (f : Future)
    {env : Env} {i : Nat} {pos : Pos} (h : ckVarPos env i = some pos) :
    ∃ H, Env.mean dm C Γ ρ f env pos = Value.mean dm C Γ ρ f H (valAt env pos) := by
  unfold ckVarPos at h
  split at h
  · rename_i hi
    simp only [Option.some.injEq] at h
    subst h
    have hne : env.size ≠ 0 := by
      intro h0
      have hd : env[env.size - 1]! = (default : Frame) := by simp [h0]
      rw [hd] at hi
      have : (default : Frame).binds.size = 0 := rfl
      omega
    have hf : env[env.size - 1]? = some env[env.size - 1]! := by
      rw [Array.getElem?_eq_getElem (by omega), getElem!_pos env (env.size - 1) (by omega)]
    refine ⟨Env.hintAt dm C Γ ρ env (.bind (env.size - 1) (env[env.size - 1]!.binds.size - 1 - i)), ?_⟩
    simp only [Env.mean, hf, Option.bind_some, valAt]
    generalize env[env.size - 1]! = fr at hi ⊢
    have hb : fr.binds[fr.binds.size - 1 - i]? = some fr.binds[fr.binds.size - 1 - i]! := by
      rw [Array.getElem?_eq_getElem (by omega), getElem!_pos _ _ (by omega)]
    simp only [hb]
  · cases h

/-- What a place's meaning is, by its checker value, along the join's grain. -/
def FollowMeanP (K : RunCtx) (ρ : Assignment) (st : MState) (f : Future) (pos : Pos) (q : Place) : Prop :=
  GrainOk K.D K.Γ (DecideScope.topReadings st) q → ckVarPos st.env q.steps.1 = some pos →
    ∀ v, ckContent st.env q = some v → ∀ T,
    ∃ s' T', Sem.follow K.dm K.Γ T (Env.mean K.dm K.M K.Γ ρ f st.env pos) q.steps.2 = some (s', T') ∧
      (s' = .proof ∨ ∃ H, s' = Value.mean K.dm K.M K.Γ ρ f H v)

theorem followMean_snoc (K : RunCtx) (ρ : Assignment) {st : MState} (hctx : CtxOk K ρ st)
    (hwf10 : WF10 K.Γ st) (f : Future) (pos : Pos) {q p : Place} (hpar : parentOf q = some p)
    (ih : FollowMeanP K ρ st f pos p) : FollowMeanP K ρ st f pos q := by
  intro hgr hck v hv T
  obtain ⟨x, hx, -⟩ := steps_parent hpar
  have hck' : ckVarPos st.env p.steps.1 = some pos := by rw [hx] at hck; exact hck
  rw [ckContent_snoc hx] at hv
  obtain ⟨w, hw, hwv⟩ := Option.bind_eq_some_iff.mp hv
  obtain ⟨s₁, T₁, h1, h2⟩ := ih (grain_parent hpar hgr) hck' w hw T
  rw [hx, sem_follow_append, h1, Option.bind_some]
  have hst := grain_step hx hgr
  rcases h2 with rfl | ⟨H, rfl⟩
  · obtain ⟨T', hT'⟩ := sem_step_proof K.dm K.Γ T₁ x
    exact ⟨.proof, T', by simp [Sem.follow, hT'], .inl rfl⟩
  · obtain ⟨root, hroot, hfr⟩ := ckContent_root hw
    have hbc : w.anyAtom (Value.bareCtor K.Γ) = false := by
      cases e : w.anyAtom (Value.bareCtor K.Γ)
      · rfl
      · have := anyAtom_of_follow _ _ _ hfr e
        rw [hwf10 root hroot] at this; exact absurd this (by simp)
    obtain ⟨s', T', h3, h4⟩ := step_mean K.dm K.M K.Γ ρ f _ x hst w v H T₁ hwv
      (fun n args e hn => hctx.shapes.fits p w n args hw e hn) hbc
    exact ⟨s', T', by simp [Sem.follow, h3], h4⟩

/-- **The reference's reading of a place at the join's grain is the meaning of the checker's
value there**, or `⋆` (a place inside a proof), at every future. -/
theorem followMean (K : RunCtx) (ρ : Assignment) {st : MState} (hctx : CtxOk K ρ st)
    (hg : Good K.dm K.M K.Γ ρ st) (f : Future) (pos : Pos) : ∀ q, FollowMeanP K ρ st f pos q
  | .var i => by
    intro _ hck v hv T
    simp only [Place.steps] at hck
    have hv' : valAt st.env pos = v := by
      unfold ckContent at hv
      simp only [Place.steps, hck, Option.bind_some, Value.follow, Option.some.injEq] at hv; exact hv
    obtain ⟨H, hH⟩ := envMean_ck K.dm K.M K.Γ ρ f hck
    exact ⟨Env.mean K.dm K.M K.Γ ρ f st.env pos, T, by simp [Place.steps, Sem.follow],
      .inr ⟨H, by rw [hH, hv']⟩⟩
  | .deref p => followMean_snoc K ρ hctx hg.2.2.2.2.2.2.2.2.2.2.1 f pos rfl (followMean K ρ hctx hg f pos p)
  | .proj _ p => followMean_snoc K ρ hctx hg.2.2.2.2.2.2.2.2.2.2.1 f pos rfl (followMean K ρ hctx hg f pos p)
  | .field _ p => followMean_snoc K ρ hctx hg.2.2.2.2.2.2.2.2.2.2.1 f pos rfl (followMean K ρ hctx hg f pos p)

/-! ## The write of `⊥` along a place at the grain -/

theorem jdExtend_steps : ∀ (p : Place) (ss : List Step), (Ochr.jdExtend p ss).steps = (p.steps.1, p.steps.2 ++ ss)
  | p, [] => by simp [Ochr.jdExtend]
  | p, .deref :: ss => by
    rw [Ochr.jdExtend, jdExtend_steps]; simp [Place.steps]
  | p, .proj i :: ss => by
    rw [Ochr.jdExtend, jdExtend_steps]; simp [Place.steps]
  | p, .field g :: ss => by
    rw [Ochr.jdExtend, jdExtend_steps]; simp [Place.steps]

/-- The grain and the content read a place's steps only. -/
theorem grainOk_of_steps {D : Decisions} {Γ : List IndDecl} {sc : List DeclInfo} {q q' : Place}
    (he : q'.steps = q.steps) (h : GrainOk D Γ sc q) : GrainOk D Γ sc q' := by
  intro p x rest h1 h2; rw [he] at h1 h2; exact h p x rest h1 h2

theorem ckContent_of_steps {env : Env} {q q' : Place} (he : q'.steps = q.steps) : ckContent env q' = ckContent env q := by
  unfold ckContent; rw [he]

/-- The place one step below `p`. -/
def _root_.Ochr.Place.stepTo (p : Place) : Step → Place
  | .deref => .deref p
  | .proj i => .proj i p
  | .field g => .field g p

theorem stepTo_steps (p : Place) (x : Step) : (p.stepTo x).steps = (p.steps.1, p.steps.2 ++ [x]) := by
  cases x <;> simp [Place.stepTo, Place.steps]

theorem jdExtend_cons (p : Place) (x : Step) (ss : List Step) :
    Ochr.jdExtend p (x :: ss) = Ochr.jdExtend (p.stepTo x) ss := by
  cases x <;> rfl

section
variable (dm : DataModel) (C : CodeMeaning) (Γ : List IndDecl) (ρ : Assignment) (ψ : Future)

/-- **`NatAlong` at one node of a place at the grain**: the step is through a declared borrow
holding a borrow, or a declared one-constructor data inductive holding its constructor with the
field (marks transparent), so the write's path conditions hold there. -/
theorem natAlong_node (r : DeclInfo) (x : Step) (hx : StepOk Γ r x) (ss : List Step) (f : Value → Value) :
    ∀ (w : Value), (∀ n args, r = .ind n args → (Γ.find? (·.name == n)).isSome → w.fitsInd n = true) →
      w.anyAtom (dataCtorBad Γ) = false →
      (∀ c, stepV x w = some c → (Value.updAt f ss c).isSome → NatAlong dm C Γ ρ ψ ss c) →
      (Value.updAt f (x :: ss) w).isSome → NatAlong dm C Γ ρ ψ (x :: ss) w
  | .gloan l w, hf, hn, ih, hu => by
    have e : stepV x (.gloan l w) = stepV x w := by cases x <;> rfl
    rw [Value.anyAtom] at hn
    simp only [Bool.or_eq_false_iff] at hn
    have hu' : (Value.updAt f (x :: ss) w).isSome := by
      simp only [Value.updAt, Option.isSome_map] at hu; exact hu
    have := natAlong_node r x hx ss f w
      (fun n args e hm => by have := hf n args e hm; simpa [Value.fitsInd] using this) hn.2
      (fun c hc => ih c (by rw [e]; exact hc)) hu'
    cases x <;> simpa [NatAlong] using this
  | .borrow l w, _, _, ih, hu => by
    cases x with
    | deref =>
      simp only [Value.updAt, Option.isSome_map] at hu
      simp only [NatAlong]
      exact ih w rfl hu
    | proj i | field g => simp [Value.updAt] at hu
  | .ind ty c hh ps fs, hf, hn, ih, hu => by
    cases x with
    | deref => simp [Value.updAt] at hu
    | proj i =>
      obtain ⟨n, args, d, rfl, hd, -⟩ := hx
      have hty := hf n args rfl (by simp [hd])
      simp only [Value.fitsInd, beq_iff_eq] at hty; subst hty
      rw [Value.anyAtom] at hn; simp only [Bool.or_eq_false_iff] at hn
      have hn1 := hn.1
      simp only [dataCtorBad, hd, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at hn1
      rcases c with _ | c
      · simp only [NatAlong]
        refine ⟨d, hd, hn1.1, hn1.2, fun w hw => ?_⟩
        obtain ⟨-, w₁, w₁', hw₁, hu₁, -⟩ := updAt_ind_inv (Option.get_mem hu)
        simp only [Step.fieldIdx] at hw hw₁
        rw [hw] at hw₁; cases hw₁
        exact ih w (by simpa [stepV] using hw) (by rw [hu₁]; rfl)
      · simp [Value.updAt] at hu
    | field g =>
      obtain ⟨n, args, d, rfl, hd, -⟩ := hx
      have hty := hf n args rfl (by simp [hd])
      simp only [Value.fitsInd, beq_iff_eq] at hty; subst hty
      rw [Value.anyAtom] at hn; simp only [Bool.or_eq_false_iff] at hn
      have hn1 := hn.1
      simp only [dataCtorBad, hd, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at hn1
      have hc : (ty == g.ty && c == g.ctor) = true := by
        cases e : (ty == g.ty && c == g.ctor)
        · simp [Value.updAt, e] at hu
        · rfl
      simp only [NatAlong]
      refine ⟨d, hd, hn1.1, hn1.2, fun w hw => ?_⟩
      obtain ⟨-, w₁, w₁', hw₁, hu₁, -⟩ := updAt_ind_inv (Option.get_mem hu)
      simp only [Step.fieldIdx] at hw hw₁
      rw [hw] at hw₁; cases hw₁
      exact ih w (by simp [stepV, hc, hw]) (by rw [hu₁]; rfl)
  | .succ w, hf, _, _, hu => by
    cases x with
    | deref => simp [Value.updAt] at hu
    | proj i =>
      obtain ⟨n, args, d, rfl, hd, -⟩ := hx
      have := hf n args rfl (by simp [hd]); simp [Value.fitsInd] at this
    | field g =>
      obtain ⟨n, args, d, rfl, hd, -⟩ := hx
      have := hf n args rfl (by simp [hd]); simp [Value.fitsInd] at this
  | .bot, _, _, _, hu | .loan _, _, _, _, hu | .abs _, _, _, _, hu | .sealed _, _, _, _, hu
  | .proof, _, _, _, hu | .zero, _, _, _, hu | .unit, _, _, _, hu | .gfn _, _, _, _, hu
  | .clo .., _, _, _, hu | .tNat, _, _, _, hu | .tUnit, _, _, _, hu | .tEq .., _, _, _, hu
  | .tRef _, _, _, _, hu | .tPi .., _, _, _, hu | .sort _, _, _, _, hu | .tInd .., _, _, _, hu => by
    cases x <;> simp [Value.updAt] at hu

end

/-- **`NatAlong` along a place at the grain** (the write of `⊥`'s path conditions, `mean_updAt_botS`):
by the checker's typing of places at every prefix (V, R, A, N), where the write's path exists. -/
theorem natAlong_grain (K : RunCtx) (ρ : Assignment) {st : MState} (hctx : CtxOk K ρ st) (ψ : Future)
    (f : Value → Value) : ∀ (ss : List Step) (p : Place) (w : Value),
      GrainOk K.D K.Γ (DecideScope.topReadings st) (Ochr.jdExtend p ss) → ckContent st.env p = some w →
      (Value.updAt f ss w).isSome → NatAlong K.dm K.M K.Γ ρ ψ ss w
  | [], _, _, _, _, _ => by simp [NatAlong]
  | x :: ss, p, w, hgr, hw, hu => by
    rw [jdExtend_cons] at hgr
    have hst : StepOk K.Γ (K.D.placeDecl (DecideScope.topReadings st) p) x := by
      apply hgr p x ss
      · rw [jdExtend_steps, stepTo_steps]
      · rw [jdExtend_steps, stepTo_steps]; simp
    obtain ⟨root, hroot, hfr⟩ := ckContent_root hw
    have hsub : ∀ P : Value → Bool, root.anyAtom P = false → w.anyAtom P = false := fun P h => by
      cases e : w.anyAtom P
      · rfl
      · have := anyAtom_of_follow _ _ _ hfr e; rw [h] at this; cases this
    refine natAlong_node K.dm K.M K.Γ ρ ψ _ x hst ss f w
      (fun n args e hn => hctx.shapes.fits p w n args hw e hn)
      (hsub _ (hctx.shapes.ctors root hroot)) ?_ hu
    intro c hc huc
    have hcc : ckContent st.env (p.stepTo x) = some c := by
      rw [ckContent_snoc (stepTo_steps p x), hw, Option.bind_some, hc]
    exact natAlong_grain K ρ hctx ψ f ss (p.stepTo x) c hgr hcc huc

theorem hasBorrow_of_holdsBorrow (l : Nat) : ∀ (v : Value), v.holdsBorrow l = true → v.hasBorrow = true
  | .borrow m w, _ => by simp [Value.hasBorrow, Value.anyAtom]
  | .succ w, h => by
    simp only [Value.holdsBorrow] at h
    have := hasBorrow_of_holdsBorrow l w h
    simp only [Value.hasBorrow] at this ⊢
    rw [Value.anyAtom]; simp [this]
  | .zero, h | .unit, h | .gfn _, h | .clo _ _ _, h | .gloan _ _, h | .loan _, h | .bot, h | .abs _, h
  | .sealed _, h | .proof, h | .tNat, h | .tUnit, h | .tEq _ _ _, h | .tRef _, h | .tPi _ _ _, h
  | .sort _, h | .ind _ _ _ _ _, h | .tInd _ _, h => by simp [Value.holdsBorrow] at h


end Ochr.Meaning.Steps

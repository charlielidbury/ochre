import Ochr.Meaning.DataModel.Exists.FrameLocal.Qset

/-!
# Frame locality, part 2: the run's primitives across the transform (exists3, 2026-11-21)

Each primitive of the run, at `qset Q β s`, is the primitive at `s` with `qset Q β` applied to its
final state (`Comm`), where the places it reaches are outside `Q`; each test it makes has the same
answer at both. The hypotheses (`Pre`): `Q` holds bindings only, which exist, hold no borrow, and
whose values under `β` do not read the future.
-/

namespace Ochr.Meaning.DataModel.Exists.FrameLocal

open Ochr Ochr.Meaning SState
open Classical

/-- The transform on a run's outcome. -/
noncomputable def qmap {α : Type 3} (Q : Pos → Prop) (β : Pos → SBinding) :
    Option (α × SState) → Option (α × SState) :=
  Option.map fun x => (x.1, qset Q β x.2)

/-- A computation commutes with the transform at `s`. -/
def Comm {α : Type 3} (Q : Pos → Prop) (β : Pos → SBinding) (x : SM α) (s : SState) : Prop :=
  x (qset Q β s) = qmap Q β (x s)

/-- What the primitives need: `Q` is bindings that exist, no borrow is held there, and `β`'s values
there do not read the future. -/
structure Pre (Q : Pos → Prop) (β : Pos → SBinding) (s : SState) : Prop where
  temp : ∀ f i, ¬ Q (.temp f i)
  pos : ∀ p, Q p → p ∈ s.positions
  shape : ∀ p, Q p → s.shape p = none
  const : ∀ p, Q p → ∃ c, (β p).val = fun _ => c

section
variable {Q : Pos → Prop} {β : Pos → SBinding}

/-! ## Combinators -/

theorem comm_pure {α : Type 3} (a : α) (s : SState) : Comm Q β (pure a : SM α) s := rfl

theorem comm_fail {α : Type 3} (s : SState) : Comm Q β (SM.fail : SM α) s := rfl

theorem comm_bind {α γ : Type 3} {x : SM α} {f : α → SM γ} {s : SState} (hx : Comm Q β x s)
    (hf : ∀ a s₁, x s = some (a, s₁) → Comm Q β (f a) s₁) : Comm Q β (x >>= f) s := by
  show (match x (qset Q β s) with | some (a, s') => f a s' | none => none) =
    qmap Q β (match x s with | some (a, s') => f a s' | none => none)
  rw [hx]
  cases h : x s with
  | none => rfl
  | some y => obtain ⟨a, s₁⟩ := y; exact hf a s₁ h

theorem comm_onCopy {α : Type 3} {x : SM α} {s : SState} (hx : Comm Q β x s) : Comm Q β (SM.onCopy x) s := by
  unfold Comm SM.onCopy; rw [hx]
  cases x s <;> rfl

theorem comm_stmtIf {b : Bool} {x : SM (Sem × TyS)} {s : SState} (hx : Comm Q β x s) : Comm Q β (SM.stmtIf b x) s := by
  unfold Comm SM.stmtIf; rw [hx]
  cases b <;> cases x s <;> rfl

theorem comm_erasedIf {fl : Bool × Bool} {x : SM (Sem × TyS)} {s : SState} (hx : Comm Q β x s) :
    Comm Q β (SM.erasedIf fl x) s := by
  unfold Comm SM.erasedIf
  split
  · rw [hx]
    cases h : x s with
    | none => rfl
    | some y =>
      obtain ⟨⟨v, R⟩, s₁⟩ := y
      cases v <;> rfl
  · exact comm_stmtIf hx

theorem comm_strictS {R : DataRead} {x : SM (Sem × TyS)} {s : SState} (hx : Comm Q β x s) :
    Comm Q β (SM.strictS R x) s := by
  unfold Comm SM.strictS; rw [hx]
  cases x s with
  | none => rfl
  | some y => simp only [qmap, Option.map_some]; split <;> rfl

theorem comm_guarded {α : Type 3} {ok : SState → Prop} {x : SM α} {s : SState} (hok : ok (qset Q β s) ↔ ok s)
    (hx : ok s → Comm Q β x s) : Comm Q β (SM.guarded ok x) s := by
  unfold Comm SM.guarded
  by_cases h : ok s
  · rw [if_pos (hok.2 h), if_pos h]; exact hx h
  · rw [if_neg (fun h' => h (hok.1 h')), if_neg h]; rfl

theorem comm_guardMod {ok : SState → Prop} {f : SState → SState} {s : SState} (hok : ok (qset Q β s) ↔ ok s)
    (hf : ok s → f (qset Q β s) = qset Q β (f s)) : Comm Q β (SM.guardMod ok f) s := by
  unfold Comm SM.guardMod
  by_cases h : ok s
  · rw [if_pos (hok.2 h), if_pos h, hf h]; rfl
  · rw [if_neg (fun h' => h (hok.1 h')), if_neg h]; rfl

theorem comm_anyArm {n : Nat} {f : Nat → SM (Sem × TyS)} {s : SState} (hf : ∀ c, Comm Q β (f c) s) :
    Comm Q β (SM.anyArm n f) s := by
  unfold Comm SM.anyArm
  have e : ∀ c, SM.ranProof (f c (qset Q β s)) = SM.ranProof (f c s) := fun c => by
    rw [hf c]; cases f c s with
    | none => rfl
    | some y => obtain ⟨⟨v, R⟩, s₁⟩ := y; cases v <;> rfl
  simp only [e]
  cases (List.range n).find? (fun c => SM.ranProof (f c s)) with
  | none => rfl
  | some c => dsimp only; rw [hf c]; cases f c s <;> rfl

theorem comm_headOf {f : Term} {rd : Place → SM (Sem × TyS)} {rn : SM (Sem × TyS)} {s : SState}
    (h1 : ∀ p, f = .place p → Comm Q β (rd p) s) (h2 : (∀ p, f ≠ .place p) → Comm Q β rn s) :
    Comm Q β (SM.headOf f rd rn) s := by
  cases f
  case place p => exact h1 p rfl
  all_goals exact h2 (fun p h => by cases h)

/-- A test of the state that is the same at both. -/
theorem comm_ite {α : Type 3} {P : SState → Prop} {x y : SM α} {s : SState} (hP : P (qset Q β s) ↔ P s)
    (hx : P s → Comm Q β x s) (hy : ¬ P s → Comm Q β y s) :
    Comm Q β (fun s => if P s then x s else y s) s := by
  unfold Comm
  by_cases h : P s
  · simp only [if_pos (hP.2 h), if_pos h]; exact hx h
  · simp only [if_neg (fun h' => h (hP.1 h')), if_neg h]; exact hy h

end

/-! ## The state's primitives -/

section
variable {Q : Pos → Prop} {β : Pos → SBinding}

theorem Pre.of_envLe {s t : SState} (h : Pre Q β s) (he : EnvLe s t) (hsh : ∀ p, Q p → t.shape p = none) :
    Pre Q β t := ⟨h.temp, fun p hp => he.mem (h.pos p hp), hsh, h.const⟩

theorem Pre.endLabel {s : SState} (h : Pre Q β s) (l : Nat) : Pre Q β (s.endLabel l) :=
  h.of_envLe (envLe_endLabel s l) (endLabel_shape_none h.shape l)

theorem Pre.foldl_endLabel : ∀ (ls : List Nat) {s : SState}, Pre Q β s → Pre Q β (ls.foldl SState.endLabel s)
  | [], _, h => h
  | l :: ls, _, h => Pre.foldl_endLabel ls (h.endLabel l)

theorem Pre.access {s : SState} (h : Pre Q β s) (p : Pos) (hit : List Step → Bool) : Pre Q β (s.access p hit) :=
  h.of_envLe (envLe_access s p hit) (access_shape_none p hit s h.shape)

theorem qset_endLabel' {s : SState} (h : Pre Q β s) (l : Nat) : (qset Q β s).endLabel l = qset Q β (s.endLabel l) :=
  qset_endLabel s h.temp h.shape h.const l

theorem qset_access' {s : SState} (h : Pre Q β s) (p : Pos) (hit : List Step → Bool) :
    (qset Q β s).access p hit = qset Q β (s.access p hit) := qset_access h.temp h.const p hit s h.shape

theorem qset_accRounds (p : Pos) (hit : List Step → Bool) : ∀ (xs : List Nat) (s : SState), Pre Q β s →
    xs.foldl (fun t _ => accRound p hit t) (qset Q β s) = qset Q β (xs.foldl (fun t _ => accRound p hit t) s) ∧
      Pre Q β (xs.foldl (fun t _ => accRound p hit t) s)
  | [], _, h => ⟨rfl, h⟩
  | x :: xs, s, h => by
    simp only [List.foldl_cons]
    have e : accRound p hit (qset Q β s) = qset Q β (accRound p hit s) := by
      unfold accRound
      rw [qset_liveLabels h.shape, qset_reached, qset_foldl_endLabel h.temp h.const _ s h.shape]
    rw [e]
    exact qset_accRounds p hit xs _ (Pre.foldl_endLabel _ h)

end

section
variable (K : RunCtx) (φ : Future) {Q : Pos → Prop} {β : Pos → SBinding}

theorem typedFut_qset {s : SState} (h : Pre Q β s) : TypedFut K φ (qset Q β s) = TypedFut K φ s := by
  funext ψ; simp only [TypedFut, qset_liveLabels h.shape, qset_heldTy]

theorem endOk_qset {s : SState} (h : Pre Q β s) (l : Nat) : EndOk K φ (qset Q β s) l ↔ EndOk K φ s l := by
  unfold EndOk
  rw [qset_holderOf h.shape, typedFut_qset K φ h]
  constructor
  · intro H r hr ψ hψ
    have := H r hr ψ hψ
    rwa [qset_valAt_not s (not_q_of_shape h.shape (holderOf_spec hr).2)] at this
  · intro H r hr ψ hψ
    rw [qset_valAt_not s (not_q_of_shape h.shape (holderOf_spec hr).2)]
    exact H r hr ψ hψ

theorem endsOk_qset : ∀ (ls : List Nat) {s : SState}, Pre Q β s → (EndsOk K φ ls (qset Q β s) ↔ EndsOk K φ ls s)
  | [], _, _ => Iff.rfl
  | l :: ls, s, h => by
    show (EndOk K φ (qset Q β s) l ∧ EndsOk K φ ls ((qset Q β s).endLabel l)) ↔
      (EndOk K φ s l ∧ EndsOk K φ ls (s.endLabel l))
    rw [endOk_qset K φ h, qset_endLabel' h, endsOk_qset ls (h.endLabel l)]

theorem accessOk_qset {s : SState} (h : Pre Q β s) (p : Pos) (hit : List Step → Bool) :
    AccessOk K φ (qset Q β s) p hit ↔ AccessOk K φ s p hit := by
  unfold AccessOk
  rw [qset_liveLabels h.shape]
  refine forall_congr' fun k => imp_congr_right fun _ => ?_
  obtain ⟨e, hk⟩ := qset_accRounds p hit (List.range k) s h
  rw [e, qset_liveLabels hk.shape, qset_reached, endsOk_qset K φ _ hk]

/-- A place whose root is outside `Q`. -/
def RAvoid (Q : Pos → Prop) (s : SState) (p : Place) : Prop :=
  ∀ pos steps, resolve s p = some (pos, steps) → ¬ Q pos

theorem contentOk_qset {s : SState} (h : Pre Q β s) (p : Place) :
    ContentOk K φ p (qset Q β s) ↔ ContentOk K φ p s := by
  unfold ContentOk; rw [qset_resolve]
  cases resolve s p with
  | none => exact Iff.rfl
  | some ps => exact accessOk_qset K φ h _ _

theorem tagOk_qset {s : SState} (h : Pre Q β s) (p : Place) : TagOk K φ p (qset Q β s) ↔ TagOk K φ p s := by
  unfold TagOk; rw [qset_resolve]
  cases resolve s p with
  | none => exact Iff.rfl
  | some ps => exact accessOk_qset K φ h _ _

theorem contentOf_qset {s : SState} (h : Pre Q β s) {p : Place} (hp : RAvoid Q s p) :
    Comm Q β (contentOf K φ p) s := by
  unfold Comm contentOf
  rw [qset_resolve]
  cases hr : resolve s p with
  | none => rfl
  | some ps =>
    obtain ⟨pos, steps⟩ := ps
    have hq := hp pos steps hr
    have ha := h.access pos (dataHit steps)
    dsimp only
    rw [qset_access' h, qset_tyAt_not s hq, qset_valAt_not _ hq, qset_typedFuture ha.shape, qset_tyAt_not _ hq]
    cases Sem.follow K.dm K.Γ (s.tyAt pos) ((s.access pos (dataHit steps)).valAt pos
      ((s.access pos (dataHit steps)).typedFuture φ)) steps <;> rfl

theorem tagOf_qset {s : SState} (h : Pre Q β s) {p : Place} (hp : RAvoid Q s p) (tag : Sem → TyS → Sem) :
    Comm Q β (tagOf K φ p tag) s := by
  unfold Comm tagOf
  rw [qset_resolve]
  cases hr : resolve s p with
  | none => rfl
  | some ps =>
    obtain ⟨pos, steps⟩ := ps
    have hq := hp pos steps hr
    have ha := h.access pos (tagHit steps)
    dsimp only
    rw [qset_access' h, qset_tyAt_not s hq, qset_valAt_not _ hq, qset_typedFuture ha.shape]
    rfl

theorem contentOf_some {s s₁ : SState} {p : Place} {x : Sem × TyS × Pos × List Step}
    (h : contentOf K φ p s = some (x, s₁)) :
    resolve s p = some (x.2.2.1, x.2.2.2) ∧ s₁ = s.access x.2.2.1 (dataHit x.2.2.2) := by
  unfold contentOf at h
  cases hr : resolve s p with
  | none => rw [hr] at h; cases h
  | some ps =>
    obtain ⟨pos, steps⟩ := ps
    rw [hr] at h
    dsimp only at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, rfl⟩
    · cases h

theorem setContent_qset {s : SState} {pos : Pos} (hq : ¬ Q pos) (h : Pre Q β s) (steps : List Step) (v : Sem) :
    Comm Q β (setContent K φ pos steps v) s := by
  unfold Comm setContent
  dsimp only
  rw [qset_tyAt_not s hq, qset_valAt_not s hq, typedFut_qset K φ h]
  split
  · simp only [qmap, Option.map_some, qset_setAt s hq]
  · rfl

theorem Pre.setAt {s : SState} (h : Pre Q β s) (p : Pos) (v : SVal) : Pre Q β (s.setAt p v) :=
  h.of_envLe (envLe_setAt s p v) (by cases p <;> exact h.shape)

theorem setContent_state {s s' : SState} {pos : Pos} {steps : List Step} {v : Sem} {u : PUnit}
    (hs : setContent K φ pos steps v s = some (u, s')) : ∃ g, s' = s.setAt pos g := by
  unfold setContent at hs
  dsimp only at hs
  split at hs
  · simp only [Option.some.injEq, Prod.mk.injEq] at hs; exact ⟨_, hs.2.symm⟩
  · cases hs

theorem Pre.takeLabel {s : SState} (h : Pre Q β s) (l : Nat) : Pre Q β (s.takeLabel l) :=
  h.of_envLe (envLe_takeLabel s l) (takeLabel_shape_none h.shape l)

theorem readPlace_qset {s : SState} (h : Pre Q β s) {p : Place} (hp : RAvoid Q s p) (copy : Bool) :
    Comm Q β (readPlace K φ p copy) s := by
  unfold Comm readPlace
  show Option.bind (contentOf K φ p (qset Q β s)) _ = qmap Q β (Option.bind (contentOf K φ p s) _)
  rw [contentOf_qset K φ h hp]
  cases hc : contentOf K φ p s with
  | none => rfl
  | some y =>
    obtain ⟨⟨v, T, pos, steps⟩, s₁⟩ := y
    obtain ⟨hr, rfl⟩ := contentOf_some K φ hc
    have hq : ¬ Q pos := hp pos steps hr
    have h₁ := h.access pos (dataHit steps)
    simp only [qmap, Option.map_some, Option.bind_some]
    split
    · rfl
    · split
      · rfl
      · split
        · rfl
        · show Option.bind (setContent K φ pos steps .moved (qset Q β (s.access pos (dataHit steps)))) _ =
            Option.map _ (Option.bind (setContent K φ pos steps .moved (s.access pos (dataHit steps))) _)
          rw [setContent_qset K φ hq h₁]
          cases hs : setContent K φ pos steps .moved (s.access pos (dataHit steps)) with
          | none => rfl
          | some z =>
            obtain ⟨u, s₂⟩ := z
            obtain ⟨g, rfl⟩ := setContent_state K φ hs
            have h₂ := h₁.setAt pos g
            simp only [qmap, Option.map_some, Option.bind_some, qset_shape, if_neg hq]
            cases (s.access pos (dataHit steps)).shape pos with
            | none => simp
            | some l =>
              cases steps with
              | nil =>
                simp only [List.isEmpty_nil, if_true, Option.some.injEq]
                rw [qset_takeLabel h₂.shape, qset_pushTempShaped _ h.temp]
              | cons _ _ => simp

/-! ## Layout, folds, and the whole-state tests -/

theorem varPos_of_envLe {s t : SState} (h : EnvLe s t) : t.varPos = s.varPos := by
  funext i
  unfold SState.varPos
  rw [List.getLast?_eq_getElem?, List.getLast?_eq_getElem?, h.1]
  have htop : t.topIdx = s.topIdx := by simp [SState.topIdx, h.1]
  rw [htop]
  cases hs : s.env[s.env.length - 1]? with
  | none =>
    have : t.env[s.env.length - 1]? = none := by
      have := h.1
      rw [List.getElem?_eq_none_iff] at hs ⊢; omega
    rw [this]
  | some fr =>
    obtain ⟨fr', h1, h2, -⟩ := h.2 _ fr hs
    rw [h1]; simp [h2, SState.topIdx]

theorem resolve_of_envLe {s t : SState} (h : EnvLe s t) (p : Place) : resolve t p = resolve s p := by
  simp only [resolve, varPos_of_envLe h]

theorem RAvoid.of_envLe {s t : SState} {p : Place} (hp : RAvoid Q s p) (h : EnvLe s t) : RAvoid Q t p := by
  intro pos steps hr; rw [resolve_of_envLe h] at hr; exact hp pos steps hr

/-- A fold of steps that commute, from states where they do. -/
theorem foldl_qset {α : Type} (g : SState → α → SState) (P : SState → Prop) (A : α → Prop)
    (hP : ∀ s a, P s → A a → P (g s a)) (hg : ∀ s a, P s → A a → g (qset Q β s) a = qset Q β (g s a)) :
    ∀ (as : List α) (s : SState), P s → (∀ a ∈ as, A a) → as.foldl g (qset Q β s) = qset Q β (as.foldl g s)
  | [], _, _, _ => rfl
  | a :: as, s, h, ha => by
    simp only [List.foldl_cons]
    rw [hg s a h (ha a (by simp))]
    exact foldl_qset g P A hP hg as _ (hP s a h (ha a (by simp))) fun b hb => ha b (by simp [hb])

theorem foldOk_qset {α : Type} (g : SState → α → SState) (ok : SState → α → Prop) (P : SState → Prop) (A : α → Prop)
    (hP : ∀ s a, P s → A a → P (g s a)) (hg : ∀ s a, P s → A a → g (qset Q β s) a = qset Q β (g s a))
    (hok : ∀ s a, P s → A a → (ok (qset Q β s) a ↔ ok s a)) :
    ∀ (as : List α) (s : SState), P s → (∀ a ∈ as, A a) → (FoldOk g ok as (qset Q β s) ↔ FoldOk g ok as s)
  | [], _, _, _ => Iff.rfl
  | a :: as, s, h, ha => by
    show (ok (qset Q β s) a ∧ FoldOk g ok as (g (qset Q β s) a)) ↔ (ok s a ∧ FoldOk g ok as (g s a))
    rw [hok s a h (ha a (by simp)), hg s a h (ha a (by simp)),
      foldOk_qset g ok P A hP hg hok as _ (hP s a h (ha a (by simp))) fun b hb => ha b (by simp [hb])]

/-- The state's invariant while the run's primitives act on a state with layout `s₀`'s. -/
def Inv (Q : Pos → Prop) (β : Pos → SBinding) (s₀ s : SState) : Prop := Pre Q β s ∧ EnvLe s₀ s

theorem Inv.refl {s : SState} (h : Pre Q β s) : Inv Q β s s := ⟨h, EnvLe.refl s⟩

theorem invalidateOne_qset {s₀ s : SState} (h : Inv Q β s₀ s) {q : Place} (hq : RAvoid Q s₀ q) :
    invalidateOne K φ (qset Q β s) q = qset Q β (invalidateOne K φ s q) ∧ Inv Q β s₀ (invalidateOne K φ s q) := by
  unfold invalidateOne
  rw [qset_resolve]
  cases hr : resolve s q with
  | none => exact ⟨rfl, h⟩
  | some ps =>
    obtain ⟨pos, steps⟩ := ps
    have hn : ¬ Q pos := (hq.of_envLe h.2) pos steps hr
    have ha := h.1.access pos (dataHit steps)
    have hea : EnvLe s₀ (s.access pos (dataHit steps)) := h.2.trans (envLe_access _ _ _)
    dsimp only
    rw [qset_access' h.1]
    have hc := setContent_qset K φ hn ha steps .moved
    unfold Comm at hc
    rw [hc]
    cases hs : setContent K φ pos steps .moved (s.access pos (dataHit steps)) with
    | none => exact ⟨rfl, ha, hea⟩
    | some z =>
      obtain ⟨u, s₂⟩ := z
      obtain ⟨g, rfl⟩ := setContent_state K φ hs
      exact ⟨rfl, ha.setAt pos g, hea.trans (envLe_setAt _ _ _)⟩

theorem invalOneOk_qset {s₀ s : SState} (h : Inv Q β s₀ s) (q : Place) :
    InvalOneOk K φ (qset Q β s) q ↔ InvalOneOk K φ s q := by
  unfold InvalOneOk; rw [qset_resolve]
  cases resolve s q with
  | none => exact Iff.rfl
  | some ps => exact accessOk_qset K φ h.1 _ _

theorem invalidate_qset {s₀ s : SState} (h : Inv Q β s₀ s) {p : Place}
    (hq : ∀ q ∈ K.D.invalidated (scopeOf s) p, RAvoid Q s₀ q) (hsc : scopeOf (qset Q β s) = scopeOf s) :
    invalidate K φ p (qset Q β s) = qset Q β (invalidate K φ p s) ∧ Inv Q β s₀ (invalidate K φ p s) ∧
      (InvalidateOk K φ p (qset Q β s) ↔ InvalidateOk K φ p s) := by
  unfold invalidate InvalidateOk
  rw [hsc]
  refine ⟨foldl_qset _ (Inv Q β s₀) (RAvoid Q s₀) (fun s a h ha => (invalidateOne_qset K φ h ha).2)
    (fun s a h ha => (invalidateOne_qset K φ h ha).1) _ _ h hq, ?_,
    foldOk_qset _ _ (Inv Q β s₀) (RAvoid Q s₀) (fun s a h ha => (invalidateOne_qset K φ h ha).2)
    (fun s a h ha => (invalidateOne_qset K φ h ha).1) (fun s a h _ => invalOneOk_qset K φ h a) _ _ h hq⟩
  clear hsc
  generalize K.D.invalidated (scopeOf s) p = qs at hq
  induction qs generalizing s with
  | nil => exact h
  | cons q qs ih =>
    exact ih (invalidateOne_qset K φ h (hq q (by simp))).2 (fun b hb => hq b (by simp [hb]))

end

/-- A binding frame locality may vary: a constant value, whole, that the strict whole-state test
(`StateOk`) admits at its type. -/
def Good (K : RunCtx) (b : SBinding) : Prop :=
  ∃ c, b.val = (fun _ => c) ∧ c.whole ∧
    (K.dm.pmem K.Γ c b.ty.m ∨ (b.ty.m = TyM.err ∧ ((∃ X, c = .ty X) ∨ c = .proof)))

section
variable (K : RunCtx) (φ : Future) {Q : Pos → Prop} {β β' : Pos → SBinding}

theorem Good.ok {K : RunCtx} {b : SBinding} (hb : Good K b) (ψ : Future) :
    K.dm.pmem K.Γ (b.val ψ) b.ty.m ∨ (b.ty.m = TyM.err ∧ ((∃ X, b.val ψ = .ty X) ∨ b.val ψ = .proof)) := by
  obtain ⟨c, hc, -, h⟩ := hb; rw [hc]; exact h

theorem fix_valAt {s : SState} (hfix : qset Q β s = s) {f i : Nat} (hq : Q (.bind f i)) (hp : Pos.bind f i ∈ s.positions) :
    s.valAt (.bind f i) = (β (.bind f i)).val := by
  rw [← hfix, qset_valAt_of s hq hp]

theorem fix_tyAt {s : SState} (hfix : qset Q β s = s) {f i : Nat} (hq : Q (.bind f i)) (hp : Pos.bind f i ∈ s.positions) :
    s.tyAt (.bind f i) = (β (.bind f i)).ty := by
  rw [← hfix, qset_tyAt_of s hq hp]

theorem stateOk_qset {s : SState} (h : Pre Q β' s) (hfix : qset Q β s = s) (hg : ∀ p, Q p → Good K (β p))
    (hg' : ∀ p, Q p → Good K (β' p)) : StateOk K φ (qset Q β' s) ↔ StateOk K φ s := by
  unfold StateOk
  rw [typedFut_qset K φ h, qset_positions, qset_shape_eq h.shape]
  refine forall_congr' fun ψ => imp_congr_right fun _ => and_congr ?_ ?_
  · refine forall_congr' fun f => forall_congr' fun i => imp_congr_right fun hp => ?_
    by_cases hq : Q (.bind f i)
    · rw [qset_valAt_of s hq hp, qset_tyAt_of s hq hp, fix_valAt hfix hq hp, fix_tyAt hfix hq hp]
      exact ⟨fun _ => (hg _ hq).ok ψ, fun _ => (hg' _ hq).ok ψ⟩
    · rw [qset_valAt_not s hq, qset_tyAt_not s hq]
  · refine forall_congr' fun q => forall_congr' fun l => imp_congr_right fun hs => ?_
    rw [qset_valAt_not s (not_q_of_shape h.shape hs), qset_heldTy]

theorem lentOk_qset {s : SState} (h : Pre Q β' s) (hfix : qset Q β s = s) (hg : ∀ p, Q p → Good K (β p))
    (hg' : ∀ p, Q p → Good K (β' p)) (p : Place) : lentOk K φ p (qset Q β' s) ↔ lentOk K φ p s := by
  unfold lentOk; rw [qset_resolve]
  cases resolve s p with
  | none => exact Iff.rfl
  | some ps => dsimp only; rw [stateOk_qset K φ h hfix hg hg']

theorem placeTy_qset {s : SState} (h : Pre Q β s) {p : Place} (hp : RAvoid Q s p) :
    placeTy K φ p (qset Q β s) = placeTy K φ p s := by
  unfold placeTy
  have hc := contentOf_qset K φ h hp
  unfold Comm at hc
  rw [hc]
  cases contentOf K φ p s <;> rfl

theorem letLenders_qset {s : SState} (h : Pre Q β s) : letLenders (qset Q β s) = qset Q β (letLenders s) := by
  unfold letLenders
  rw [qset_getLast, qset_topIdx]
  cases s.env.getLast? with
  | none => rfl
  | some fr => simp only [Option.map_some, qframe_binds_length]; exact qset_access' h _ _

theorem letLendersOk_qset {s : SState} (h : Pre Q β s) : LetLendersOk K φ (qset Q β s) ↔ LetLendersOk K φ s := by
  unfold LetLendersOk
  rw [qset_getLast, qset_topIdx]
  cases s.env.getLast? with
  | none => exact Iff.rfl
  | some fr => simp only [Option.map_some, qframe_binds_length]; exact accessOk_qset K φ h _ _

theorem discardEnd_qset {s : SState} (h : Pre Q β s) (R : TyS) : discardEnd R (qset Q β s) = qset Q β (discardEnd R s) := by
  unfold discardEnd; cases R.label with
  | none => rfl
  | some l => exact qset_endLabel' h l

theorem discardOk_qset {s : SState} (h : Pre Q β s) (R : TyS) : DiscardOk K φ R (qset Q β s) ↔ DiscardOk K φ R s := by
  unfold DiscardOk; cases R.label with
  | none => exact Iff.rfl
  | some l => exact endOk_qset K φ h l

theorem Pre.letLenders {s : SState} (h : Pre Q β s) : Pre Q β (letLenders s) := by
  unfold Ochr.Meaning.letLenders; cases s.env.getLast? with
  | none => exact h
  | some fr => exact h.access _ _

theorem Pre.discardEnd {s : SState} (h : Pre Q β s) (R : TyS) : Pre Q β (discardEnd R s) := by
  unfold Ochr.Meaning.discardEnd; cases R.label with
  | none => exact h
  | some l => exact h.endLabel l

theorem Pre.of_env {s t : SState} (h : Pre Q β s) (he : t.env = s.env) (hs : t.shape = s.shape) : Pre Q β t :=
  h.of_envLe (EnvLe.of_env he) (fun p hp => by rw [hs]; exact h.shape p hp)

theorem borrowPlace_qset {s : SState} (h : Pre Q β s) {p : Place} (hp : RAvoid Q s p) :
    Comm Q β (borrowPlace K φ p) s := by
  unfold Comm borrowPlace
  show Option.bind (contentOf K φ p (qset Q β s)) _ = qmap Q β (Option.bind (contentOf K φ p s) _)
  rw [contentOf_qset K φ h hp]
  cases hc : contentOf K φ p s with
  | none => rfl
  | some y =>
    obtain ⟨⟨v, T, pos, steps⟩, s₁⟩ := y
    obtain ⟨hr, rfl⟩ := contentOf_some K φ hc
    have hq : ¬ Q pos := hp pos steps hr
    have h₁ := h.access pos (dataHit steps)
    simp only [qmap, Option.map_some, Option.bind_some]
    split
    · rfl
    · rw [qset_freshLoan]
      dsimp only
      have h₂ : Pre Q β (s.access pos (dataHit steps)).freshLoan.2 := h₁.of_env rfl rfl
      rw [qset_tyAt_not _ hq, qset_valAt_not _ hq, qset_setAt _ hq, qset_pushTempShaped _ h.temp]
      rfl

theorem qset_ifAccess {s : SState} (h : Pre Q β s) (c : Bool) (pos : Pos) (hit : List Step → Bool) :
    (if c then qset Q β s else (qset Q β s).access pos hit) = qset Q β (if c then s else s.access pos hit) := by
  cases c
  · simp only [Bool.false_eq_true, if_false]; exact qset_access' h pos hit
  · rfl

theorem Pre.ifAccess {s : SState} (h : Pre Q β s) (c : Bool) (pos : Pos) (hit : List Step → Bool) :
    Pre Q β (if c then s else s.access pos hit) := by
  cases c
  · exact h.access pos hit
  · exact h

theorem assignOk_qset {s : SState} (h : Pre Q β s) {p : Place} (hp : RAvoid Q s p) :
    AssignOk K φ p (qset Q β s) ↔ AssignOk K φ p s := by
  unfold AssignOk
  rw [qset_resolve]
  cases hr : resolve s p with
  | none => exact Iff.rfl
  | some ps =>
    obtain ⟨pos, steps⟩ := ps
    have hq : ¬ Q pos := hp pos steps hr
    dsimp only
    have hsh : (qset Q β s).shape pos = s.shape pos := by simp [hq]
    rw [hsh, qset_ifAccess h, accessOk_qset K φ h]
    have h₁ := h.ifAccess (steps.isEmpty && (s.shape pos).isSome) pos (dataHit steps)
    refine and_congr Iff.rfl (imp_congr_right fun _ => forall_congr' fun l => ?_)
    simp only [qset_shape, if_neg hq]
    rw [endOk_qset K φ h₁]

theorem assignAt_qset {s : SState} (h : Pre Q β s) {p : Place} (hp : RAvoid Q s p) (v : Sem) (lab : Option Nat) :
    Comm Q β (assignAt K φ p v lab) s := by
  unfold Comm assignAt
  rw [qset_resolve]
  cases hr : resolve s p with
  | none => rfl
  | some ps =>
    obtain ⟨pos, steps⟩ := ps
    have hq : ¬ Q pos := hp pos steps hr
    dsimp only
    have hsh : (qset Q β s).shape pos = s.shape pos := by simp [hq]
    rw [hsh, qset_ifAccess h]
    have h₁ := h.ifAccess (steps.isEmpty && (s.shape pos).isSome) pos (dataHit steps)
    generalize (if (steps.isEmpty && (s.shape pos).isSome) = true then s else s.access pos (dataHit steps)) = s₁ at h₁
    have hs1 : (qset Q β s₁).shape pos = s₁.shape pos := by simp [hq]
    cases hst : steps.isEmpty
    · simp only [hst, Bool.false_eq_true, if_false]
      have h₂ := h₁
      generalize s₁ = s₂ at h₂ ⊢
      have hc := setContent_qset K φ hq h₂ steps v
      unfold Comm at hc
      rw [hc]
      cases hs : setContent K φ pos steps v s₂ with
      | none => rfl
      | some z =>
        obtain ⟨u, s₃⟩ := z
        obtain ⟨g, rfl⟩ := setContent_state K φ hs
        have h₃ := h₂.setAt pos g
        simp only [qmap, Option.map_some]
        cases lab with
        | none => rfl
        | some l =>
          cases steps with
          | nil =>
            simp only [Option.some.injEq, Prod.mk.injEq, true_and]
            rw [qset_takeLabel h₃.shape]
            refine state_eq rfl ?_ rfl rfl rfl rfl
            funext q
            by_cases e : q = pos
            · subst e; simp [hq]
            · simp [e]
          | cons _ _ => rfl
    · simp only [hst, if_true]
      rw [hs1]
      cases hsl : s₁.shape pos with
      | none =>
        dsimp only
        have h₂ := h₁
        generalize s₁ = s₂ at h₂ ⊢
        have hc := setContent_qset K φ hq h₂ steps v
        unfold Comm at hc
        rw [hc]
        cases hs : setContent K φ pos steps v s₂ with
        | none => rfl
        | some z =>
          obtain ⟨u, s₃⟩ := z
          obtain ⟨g, rfl⟩ := setContent_state K φ hs
          have h₃ := h₂.setAt pos g
          simp only [qmap, Option.map_some]
          cases lab with
          | none => rfl
          | some l =>
            cases steps with
            | nil =>
              simp only [Option.some.injEq, Prod.mk.injEq, true_and]
              rw [qset_takeLabel h₃.shape]
              refine state_eq rfl ?_ rfl rfl rfl rfl
              funext q
              by_cases e : q = pos
              · subst e; simp [hq]
              · simp [e]
            | cons _ _ => rfl
      | some l =>
        dsimp only
        rw [qset_endLabel' h₁ l]
        have h₂ := h₁.endLabel l
        generalize s₁.endLabel l = s₂ at h₂ ⊢
        have hc := setContent_qset K φ hq h₂ steps v
        unfold Comm at hc
        rw [hc]
        cases hs : setContent K φ pos steps v s₂ with
        | none => rfl
        | some z =>
          obtain ⟨u, s₃⟩ := z
          obtain ⟨g, rfl⟩ := setContent_state K φ hs
          have h₃ := h₂.setAt pos g
          simp only [qmap, Option.map_some]
          cases lab with
          | none => rfl
          | some l =>
            cases steps with
            | nil =>
              simp only [Option.some.injEq, Prod.mk.injEq, true_and]
              rw [qset_takeLabel h₃.shape]
              refine state_eq rfl ?_ rfl rfl rfl rfl
              funext q
              by_cases e : q = pos
              · subst e; simp [hq]
              · simp [e]
            | cons _ _ => rfl

theorem labTyOk_qset (s : SState) (lab : Option Nat) (T : TyM) : labTyOk (qset Q β s) lab T ↔ labTyOk s lab T :=
  Iff.rfl

theorem borrowArgsTyped_qset {s : SState} (h : Pre Q β s) (R : DataRead) (fv : Res) (args : List Res) :
    BorrowArgsTyped R fv args (qset Q β s) ↔ BorrowArgsTyped R fv args s := by
  unfold BorrowArgsTyped; rw [qset_liveLabels h.shape, qset_heldTy]

theorem qset_mapVals_const {X : SState} (h : Pre Q β X) (F : Pos → SVal → SVal)
    (hF : ∀ p c, F p (fun _ => c) = fun _ => c) : (qset Q β X).mapVals F = qset Q β (X.mapVals F) :=
  qset_mapVals X F F h.temp (fun f i _ _ hq => by
    obtain ⟨c, hc⟩ := h.const _ hq; rw [hc, hF]) (fun _ _ _ => rfl)

theorem Pre.mapVals {X : SState} (h : Pre Q β X) (F : Pos → SVal → SVal) : Pre Q β (X.mapVals F) :=
  h.of_envLe (envLe_mapVals X F) h.shape

theorem Pre.freshLoan {X : SState} (h : Pre Q β X) : Pre Q β X.freshLoan.2 := h.of_env rfl rfl

theorem qset_foldl_takeLabel : ∀ (ls : List Nat) {s : SState}, Pre Q β s →
    ls.foldl SState.takeLabel (qset Q β s) = qset Q β (ls.foldl SState.takeLabel s) ∧
      Pre Q β (ls.foldl SState.takeLabel s)
  | [], _, h => ⟨rfl, h⟩
  | l :: ls, s, h => by
    simp only [List.foldl_cons]
    rw [qset_takeLabel h.shape]
    exact qset_foldl_takeLabel ls (h.takeLabel l)

theorem callOfL_qset.{u} {s : SState} (h : Pre Q β s) (Lv : Lvl.{u}) {C : Type u} (t : Tel Lv.Code PUnit C)
    (fv : Sem) (args : List Res) : Comm Q β (callOfL Lv t fv args) s := by
  unfold Comm callOfL
  dsimp only
  rw [(qset_foldl_takeLabel _ h).1]
  split
  · rw [qset_mapVals_const (qset_foldl_takeLabel _ h).2 _ (fun _ _ => rfl)]; rfl
  · rw [qset_freshLoan]
    dsimp only
    rw [qset_mapVals_const (qset_foldl_takeLabel _ h).2.freshLoan _ (fun p c => by funext φ'; split <;> rfl)]
    rw [qset_pushTempShaped _ h.temp]
    rfl
  · rfl

theorem callOf_qset {s : SState} (h : Pre Q β s) (R : DataRead) (fv : Res) (args : List Res) :
    Comm Q β (callOf R fv args) s := by
  unfold Comm callOf
  split
  · exact callOfL_qset h _ _ _ _
  · exact callOfL_qset h _ _ _ _
  · exact callOfL_qset h _ _ _ _
  · rfl

end

/-! ## Moved places, the scope, the join's drop -/

mutual
theorem movedIn_whole : (v : Sem) → (q : Place) → v.whole → Sem.movedIn v q = []
  | .el0 _ _, _, _ => by simp [Sem.movedIn]
  | .el1 _ _, _, _ => by simp [Sem.movedIn]
  | .el2 _ _, _, _ => by simp [Sem.movedIn]
  | .ty _, _, _ => by simp [Sem.movedIn]
  | .proof, _, _ => by simp [Sem.movedIn]
  | .err, _, _ => by simp [Sem.movedIn]
  | .moved, _, h => absurd h (by simp [Sem.whole])
  | .dat t r c fs, q, h => by
    have h' : ∀ f ∈ fs, f.whole := by simpa [Sem.whole] using h
    rw [Sem.movedIn]
    split
    · exact movedInNat_whole fs q h'
    · exact movedInFields_whole t c q 0 fs h'
theorem movedInFields_whole (t : String) (c : Nat) (q : Place) :
    (i : Nat) → (fs : List Sem) → (∀ f ∈ fs, f.whole) → Sem.movedInFields t c q i fs = []
  | _, [], _ => by simp [Sem.movedInFields]
  | i, w :: ws, h => by
    rw [Sem.movedInFields, movedIn_whole w _ (h w (by simp)),
      movedInFields_whole t c q (i + 1) ws (fun f hf => h f (by simp [hf]))]
    rfl
theorem movedInNat_whole : (fs : List Sem) → (q : Place) → (∀ f ∈ fs, f.whole) → Sem.movedInNat fs q = []
  | [], _, _ => by simp [Sem.movedInNat]
  | w :: _, q, h => by rw [Sem.movedInNat]; exact movedIn_whole w _ (h w (by simp))
end

section
variable (K : RunCtx) (φ : Future) {Q : Pos → Prop} {β β' : Pos → SBinding}

theorem Good.whole {K : RunCtx} {b : SBinding} (hb : Good K b) (ψ : Future) : (b.val ψ).whole := by
  obtain ⟨c, hc, hw, -⟩ := hb; rw [hc]; exact hw

theorem pos_bind {s : SState} {p : Pos} (h : Pre Q β s) (hq : Q p) : ∃ f i, p = .bind f i := by
  cases p with
  | bind f i => exact ⟨f, i, rfl⟩
  | temp f i => exact absurd hq (h.temp f i)

theorem movedPlaces_qset {s : SState} (h : Pre Q β' s) (hfix : qset Q β s = s) (hg : ∀ p, Q p → Good K (β p))
    (hg' : ∀ p, Q p → Good K (β' p)) : movedPlaces φ (qset Q β' s) = movedPlaces φ s := by
  unfold movedPlaces
  have hlf : (qset Q β' s).lentFuture φ = s.lentFuture φ := by
    unfold SState.lentFuture; rw [qset_liveLabels h.shape]
  rw [qset_getLast, hlf, qset_shape_eq h.shape]
  cases s.env.getLast? with
  | none => rfl
  | some fr =>
    simp only [Option.map_some, qframe_binds_length, qset_varPos]
    congr 1; funext i
    cases hv : s.varPos i with
    | none => rfl
    | some pos =>
      dsimp only
      by_cases hq : Q pos
      · obtain ⟨f, j, rfl⟩ := pos_bind h hq
        have hp := h.pos _ hq
        rw [qset_valAt_of s hq hp, fix_valAt hfix hq hp, movedIn_whole _ _ ((hg' _ hq).whole _),
          movedIn_whole _ _ ((hg _ hq).whole _)]
      · rw [qset_valAt_not s hq]

theorem scopeOf_qset_decl (s : SState) (hd : ∀ p, Q p → (β' p).decl = (β p).decl) :
    scopeOf (qset Q β' s) = scopeOf (qset Q β s) := by
  unfold scopeOf
  rw [qset_getLast, qset_getLast]
  cases s.env.getLast? with
  | none => rfl
  | some fr =>
    simp only [Option.map_some]
    congr 1
    apply List.ext_getElem?
    intro i
    simp only [List.getElem?_map, qframe_binds_get]
    cases fr.binds[i]? with
    | none => rfl
    | some b =>
      by_cases hq : Q (.bind s.topIdx i)
      · simp [hq, hd _ hq]
      · simp [hq]

theorem scopeOf_qset {s : SState} (hfix : qset Q β s = s) (hd : ∀ p, Q p → (β' p).decl = (β p).decl) :
    scopeOf (qset Q β' s) = scopeOf s := by
  rw [scopeOf_qset_decl s hd, hfix]

theorem lentPrefix_qset {s : SState} (h : Pre Q β s) (pos : Pos) (steps : List Step) :
    lentPrefix (qset Q β s) pos steps = lentPrefix s pos steps := by
  unfold lentPrefix; rw [qset_liveLabels h.shape, qset_reached]

theorem accessLentPrefix_qset {s : SState} (h : Pre Q β s) (pos : Pos) (steps : List Step) :
    accessLentPrefix pos steps (qset Q β s) = qset Q β (accessLentPrefix pos steps s) := by
  unfold accessLentPrefix; rw [lentPrefix_qset h]
  cases lentPrefix s pos steps with
  | none => rfl
  | some ψ => exact qset_access' h _ _

theorem Pre.accessLentPrefix {s : SState} (h : Pre Q β s) (pos : Pos) (steps : List Step) :
    Pre Q β (accessLentPrefix pos steps s) := by
  unfold Ochr.Meaning.accessLentPrefix
  cases lentPrefix s pos steps with
  | none => exact h
  | some ψ => exact h.access _ _

theorem lentPrefixOk_qset {s : SState} (h : Pre Q β s) (pos : Pos) (steps : List Step) :
    LentPrefixOk K φ pos steps (qset Q β s) ↔ LentPrefixOk K φ pos steps s := by
  unfold LentPrefixOk; rw [lentPrefix_qset h]
  cases lentPrefix s pos steps with
  | none => exact Iff.rfl
  | some ψ => exact accessOk_qset K φ h _ _

theorem dropAt_qset {s : SState} (h : Pre Q β s) {pos : Pos} (hq : ¬ Q pos) (hsc : scopeOf (qset Q β s) = scopeOf s)
    (q : Place) (steps : List Step) :
    dropAt K φ q pos steps (qset Q β s) = qset Q β (dropAt K φ q pos steps s) ∧ Pre Q β (dropAt K φ q pos steps s) := by
  unfold dropAt
  have hsh : (qset Q β s).shape pos = s.shape pos := by simp [hq]
  rw [hsh, hsc]
  have ha := h.access pos (dataHit steps)
  rcases steps with _ | ⟨st, sts⟩
  · cases hl : s.shape pos with
    | some l => exact ⟨qset_endLabel' h l, h.endLabel l⟩
    | none =>
      dsimp only
      rw [qset_access' h, qset_tyAt_not _ hq, typedFut_qset K φ ha]
      simp only [qset_valAt_not _ hq]
      split
      · exact ⟨rfl, h⟩
      · split
        · exact ⟨qset_setAt _ hq _, ha.setAt _ _⟩
        · exact ⟨rfl, h⟩
  · dsimp only
    rw [qset_access' h, qset_tyAt_not _ hq, typedFut_qset K φ ha]
    simp only [qset_valAt_not _ hq]
    split
    · exact ⟨rfl, h⟩
    · split
      · exact ⟨qset_setAt _ hq _, ha.setAt _ _⟩
      · exact ⟨rfl, h⟩

theorem dropOk_qset {s : SState} (h : Pre Q β s) {pos : Pos} (hq : ¬ Q pos) (hsc : scopeOf (qset Q β s) = scopeOf s)
    (q : Place) (steps : List Step) : DropOk K φ q pos steps (qset Q β s) ↔ DropOk K φ q pos steps s := by
  unfold DropOk
  have hsh : (qset Q β s).shape pos = s.shape pos := by simp [hq]
  rw [hsh, hsc]
  have ha := h.access pos (dataHit steps)
  rcases steps with _ | ⟨st, sts⟩
  · cases hl : s.shape pos with
    | some l => exact endOk_qset K φ h l
    | none =>
      dsimp only
      rw [qset_access' h, qset_tyAt_not _ hq, typedFut_qset K φ ha, accessOk_qset K φ h]
      simp only [qset_valAt_not _ hq]
  · dsimp only
    rw [qset_access' h, qset_tyAt_not _ hq, typedFut_qset K φ ha, accessOk_qset K φ h]
    simp only [qset_valAt_not _ hq]

end

/-! ## Roots of places -/

theorem steps_fst : ∀ q : Place, q.steps.1 = q.root
  | .var _ => rfl
  | .deref p => by simp only [Place.steps, Place.root]; exact steps_fst p
  | .proj _ p => by simp only [Place.steps, Place.root]; exact steps_fst p
  | .field _ p => by simp only [Place.steps, Place.root]; exact steps_fst p

theorem rAvoid_of_root {Q : Pos → Prop} {s : SState} {q : Place} (h : ∀ pos, s.varPos q.root = some pos → ¬ Q pos) :
    RAvoid Q s q := by
  intro pos steps hr
  simp only [resolve, steps_fst] at hr
  cases hv : s.varPos q.root with
  | none => rw [hv] at hr; cases hr
  | some pos' =>
    rw [hv] at hr
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hr
    exact hr.1 ▸ h pos' hv

mutual
theorem movedIn_root : (v : Sem) → (q : Place) → ∀ x ∈ Sem.movedIn v q, x.root = q.root
  | .moved, q, x, hx => by simp [Sem.movedIn] at hx; rw [hx]
  | .dat t r c fs, q, x, hx => by
    rw [Sem.movedIn] at hx
    split at hx
    · exact movedInNat_root fs q x hx
    · exact movedInFields_root t c q 0 fs x hx
  | .el0 _ _, _, _, hx | .el1 _ _, _, _, hx | .el2 _ _, _, _, hx | .ty _, _, _, hx | .proof, _, _, hx
  | .err, _, _, hx => by simp [Sem.movedIn] at hx
theorem movedInFields_root (t : String) (c : Nat) (q : Place) :
    (i : Nat) → (fs : List Sem) → ∀ x ∈ Sem.movedInFields t c q i fs, x.root = q.root
  | _, [], x, hx => by simp [Sem.movedInFields] at hx
  | i, w :: ws, x, hx => by
    rw [Sem.movedInFields, List.mem_append] at hx
    rcases hx with hx | hx
    · rw [movedIn_root w _ x hx]; rfl
    · exact movedInFields_root t c q (i + 1) ws x hx
theorem movedInNat_root : (fs : List Sem) → (q : Place) → ∀ x ∈ Sem.movedInNat fs q, x.root = q.root
  | [], _, x, hx => by simp [Sem.movedInNat] at hx
  | w :: _, q, x, hx => by rw [Sem.movedInNat] at hx; rw [movedIn_root w _ x hx]; rfl
end

/-- A place already moved is rooted at a variable whose binding is not whole there. -/
theorem mem_movedPlaces {φ : Future} {s : SState} {x : Place} (hx : x ∈ movedPlaces φ s) :
    ∃ pos, s.varPos x.root = some pos ∧ ∃ q, x ∈ Sem.movedIn (s.valAt pos (s.lentFuture φ)) q := by
  unfold movedPlaces at hx
  cases hl : s.env.getLast? with
  | none => rw [hl] at hx; cases hx
  | some fr =>
    rw [hl] at hx
    simp only [List.mem_flatMap, List.mem_range] at hx
    obtain ⟨i, -, hx⟩ := hx
    cases hv : s.varPos i with
    | none => rw [hv] at hx; cases hx
    | some pos =>
      rw [hv] at hx
      dsimp only at hx
      have hr := movedIn_root _ _ x hx
      refine ⟨pos, ?_, _, hx⟩
      rw [hr]; split <;> exact hv

theorem rAvoid_of_moved {K : RunCtx} {φ : Future} {Q : Pos → Prop} {β : Pos → SBinding} {s : SState}
    (h : Pre Q β s) (hfix : qset Q β s = s) (hg : ∀ p, Q p → Good K (β p)) {x : Place}
    (hx : x ∈ movedPlaces φ s) : RAvoid Q s x := by
  obtain ⟨pos, hv, q, hq⟩ := mem_movedPlaces hx
  refine rAvoid_of_root fun pos' hv' hQ => ?_
  rw [hv] at hv'; cases hv'
  obtain ⟨f, i, rfl⟩ := pos_bind h hQ
  rw [fix_valAt hfix hQ (h.pos _ hQ), movedIn_whole _ _ ((hg _ hQ).whole _)] at hq
  cases hq

end Ochr.Meaning.DataModel.Exists.FrameLocal

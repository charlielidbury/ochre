import Ochr.Meaning.RunPres

/-!
# The run's layout: bindings kept, temporaries only added

`EnvLe s s'`: `s'` has the frames of `s`, each with as many bindings and at least as many
temporaries. Every primitive the run uses is such a step, and a `let` pushes one binding and
drops it again; so a position stays a position across a sub-run (an assignment's target, after
the run of its right-hand side, is still a position: `ShapeAt` for the hold).
-/

namespace Ochr.Meaning

open SState

/-- The layout of `s'` extends that of `s`: same frames, same bindings, more temporaries. -/
def EnvLe (s s' : SState) : Prop :=
  s'.env.length = s.env.length ∧ ∀ (f : Nat) (fr : SFrame), s.env[f]? = some fr →
    ∃ fr' : SFrame, s'.env[f]? = some fr' ∧ fr'.binds.length = fr.binds.length ∧ fr.temps.length ≤ fr'.temps.length

theorem EnvLe.refl (s : SState) : EnvLe s s :=
  ⟨rfl, fun _ fr h => ⟨fr, h, rfl, Nat.le_refl _⟩⟩

theorem EnvLe.trans {a b c : SState} (h₁ : EnvLe a b) (h₂ : EnvLe b c) : EnvLe a c := by
  refine ⟨h₂.1.trans h₁.1, fun f fr h => ?_⟩
  obtain ⟨fr', h', hb, ht⟩ := h₁.2 f fr h
  obtain ⟨fr'', h'', hb', ht'⟩ := h₂.2 f fr' h'
  exact ⟨fr'', h'', hb'.trans hb, Nat.le_trans ht ht'⟩

theorem EnvLe.of_env {s s' : SState} (h : s'.env = s.env) : EnvLe s s' := by
  unfold EnvLe; rw [h]; exact EnvLe.refl s

theorem EnvLe.congr_left {s₁ s₂ t : SState} (h : s₁.env = s₂.env) (h' : EnvLe s₁ t) : EnvLe s₂ t := by
  unfold EnvLe at h' ⊢; rw [← h]; exact h'

/-- A frame-wise change keeping the bindings' count and not removing temporaries. -/
theorem envLe_modify {s s' : SState} (k : Nat) (g : SFrame → SFrame) (he : s'.env = s.env.modify k g)
    (hg : ∀ fr, (g fr).binds.length = fr.binds.length ∧ fr.temps.length ≤ (g fr).temps.length) :
    EnvLe s s' := by
  unfold EnvLe; rw [he, List.length_modify]
  refine ⟨rfl, fun f fr h => ?_⟩
  rw [List.getElem?_modify, h]
  by_cases e : k = f
  · exact ⟨g fr, by simp [e], (hg fr).1, (hg fr).2⟩
  · exact ⟨fr, by simp [e], rfl, Nat.le_refl _⟩

theorem envLe_mapVals (s : SState) (g : Pos → SVal → SVal) : EnvLe s (s.mapVals g) := by
  refine ⟨by simp [SState.mapVals], fun f fr h => ?_⟩
  refine ⟨_, by simp only [SState.mapVals, List.getElem?_map, List.getElem?_zipIdx, h]; rfl, ?_, ?_⟩
  · simp
  · simp

theorem envLe_setAt (s : SState) (p : Pos) (v : SVal) : EnvLe s (s.setAt p v) := by
  cases p with
  | bind f i => exact envLe_modify f _ rfl fun fr => ⟨by simp, Nat.le_refl _⟩
  | temp f i => exact envLe_modify f _ rfl fun fr => ⟨rfl, by simp⟩

theorem envLe_pushTemp (s : SState) (v : SVal) : EnvLe s (s.pushTemp v) :=
  envLe_modify s.topIdx _ rfl fun fr => ⟨rfl, by simp⟩

theorem envLe_pushTempShaped (s : SState) (v : SVal) (l : Nat) : EnvLe s (s.pushTempShaped v l) := by
  unfold SState.pushTempShaped
  dsimp only
  split
  · exact (envLe_pushTemp s v).trans (EnvLe.of_env rfl)
  · exact envLe_pushTemp s v

theorem envLe_takeLabel (s : SState) (l : Nat) : EnvLe s (s.takeLabel l) := by
  unfold SState.takeLabel
  split
  · exact (envLe_setAt s _ _).trans (EnvLe.of_env rfl)
  · exact EnvLe.refl s

theorem envLe_endLabel (s : SState) (l : Nat) : EnvLe s (s.endLabel l) := by
  cases e : s.holderOf l with
  | none => rw [endLabel_of_none e]; exact EnvLe.refl s
  | some r =>
    rw [endLabel_eq e]
    unfold endAt
    exact EnvLe.congr_left rfl (envLe_mapVals _ _)

theorem envLe_foldl_endLabel : ∀ (ls : List Nat) (s : SState), EnvLe s (ls.foldl endLabel s)
  | [], s => EnvLe.refl s
  | l :: ls, s => (envLe_endLabel s l).trans (envLe_foldl_endLabel ls _)

theorem envLe_access (s : SState) (p : Pos) : EnvLe s (s.access p) := by
  rw [access_eq, foldl_range_iterR]
  generalize s.liveLabels.length = k
  induction k with
  | zero => exact EnvLe.refl s
  | succ k ih => exact ih.trans (envLe_foldl_endLabel _ _)

/-- A position stays a position. -/
theorem EnvLe.mem {s s' : SState} (h : EnvLe s s') {q : Pos} (hq : q ∈ s.positions) : q ∈ s'.positions := by
  rw [mem_positions] at hq ⊢
  cases q with
  | bind f i =>
    simp only [lookup] at hq ⊢
    cases e : s.env[f]? with
    | none => rw [e] at hq; cases hq
    | some fr =>
      rw [e] at hq
      obtain ⟨fr', e', hb, _⟩ := h.2 f fr e
      rw [e']
      simp only [Option.bind_some, Option.isSome_map] at hq ⊢
      rw [List.getElem?_eq_getElem (by rw [hb]; simpa using hq)]
      rfl
  | temp f i =>
    simp only [lookup] at hq ⊢
    cases e : s.env[f]? with
    | none => rw [e] at hq; cases hq
    | some fr =>
      rw [e] at hq
      obtain ⟨fr', e', _, ht⟩ := h.2 f fr e
      rw [e']
      simp only [Option.bind_some] at hq ⊢
      rw [List.getElem?_eq_getElem (Nat.lt_of_lt_of_le (by simpa using hq) ht)]
      rfl

/-! ## The primitives -/

section
variable (K : RunCtx) (φ : Future)

theorem contentOf_envLe {p : Place} {s s' : SState} {x : Sem × TyS × Pos × List Step}
    (h : contentOf K φ p s = some (x, s')) : EnvLe s s' := by
  unfold contentOf at h
  cases hr : resolve s p with
  | none => rw [hr] at h; cases h
  | some ps =>
    rw [hr] at h
    dsimp only at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.2]; exact envLe_access s _
    · cases h

theorem setContent_envLe {pos : Pos} {steps : List Step} {v : Sem} {s s' : SState}
    (h : setContent K φ pos steps v s = some (⟨⟩, s')) : EnvLe s s' := by
  unfold setContent at h
  simp only at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.2]; exact envLe_setAt s _ _
  · cases h

theorem readPlace_envLe {p : Place} {copy : Bool} {s s' : SState} {r : Res}
    (h : readPlace K φ p copy s = some (r, s')) : EnvLe s s' := by
  unfold readPlace at h
  cases hc : contentOf K φ p s with
  | none => rw [hc] at h; cases h
  | some x =>
    obtain ⟨⟨v, T, pos, steps⟩, s₁⟩ := x
    rw [hc] at h
    have e₁ := contentOf_envLe K φ hc
    simp only [Bind.bind, Option.bind] at h
    split at h
    · cases h
    · split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        rw [← h.2]; exact e₁
      · cases hs : setContent K φ pos steps .moved s₁ with
        | none => rw [hs] at h; cases h
        | some y =>
          obtain ⟨⟨⟩, s₂⟩ := y
          rw [hs] at h
          have e₂ := e₁.trans (setContent_envLe K φ hs)
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          rw [← h.2]
          split
          · exact e₂.trans ((envLe_takeLabel _ _).trans (envLe_pushTempShaped _ _ _))
          · exact e₂

theorem borrowPlace_envLe {p : Place} {s s' : SState} {r : Res}
    (h : borrowPlace K φ p s = some (r, s')) : EnvLe s s' := by
  unfold borrowPlace at h
  cases hc : contentOf K φ p s with
  | none => rw [hc] at h; cases h
  | some x =>
    obtain ⟨⟨v, T, pos, steps⟩, s₁⟩ := x
    rw [hc] at h
    have e₁ := contentOf_envLe K φ hc
    simp only [Bind.bind, Option.bind] at h
    split at h
    · cases h
    simp only [SState.freshLoan, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.2]
    exact e₁.trans ((EnvLe.of_env (s' := { s₁ with nextLoan := s₁.nextLoan + 1 }) rfl).trans
      ((envLe_setAt _ _ _).trans (envLe_pushTempShaped _ _ _)))

theorem joinDrop_envLe (t : Term) (s : SState) : EnvLe s (joinDrop K φ t s) := by
  unfold joinDrop
  generalize K.D.joinMoves (scopeOf s) (movedPlaces φ s) t = qs
  induction qs generalizing s with
  | nil => exact EnvLe.refl s
  | cons q qs ih =>
    simp only [List.foldl_cons]
    refine EnvLe.trans ?_ (ih _)
    split
    · exact EnvLe.refl s
    · split
      · rename_i pos steps hr
        have ea := envLe_access s pos
        split
        · exact ea
        · exact ea
        · exact ea
        · have ee : EnvLe s (if steps.isEmpty = true then
              (match (s.access pos).shape pos with | some l => (s.access pos).endLabel l | none => s.access pos)
              else s.access pos) := by
            split
            · split
              · exact ea.trans (envLe_endLabel _ _)
              · exact ea
            · exact ea
          generalize (if steps.isEmpty = true then
              (match (s.access pos).shape pos with | some l => (s.access pos).endLabel l | none => s.access pos)
              else s.access pos) = s₂ at ee ⊢
          exact ee.trans (envLe_setAt _ _ _)
      · exact EnvLe.refl s

theorem foldl_takeLabel_envLe : ∀ (ls : List Nat) (s : SState), EnvLe s (ls.foldl SState.takeLabel s)
  | [], s => EnvLe.refl s
  | l :: ls, s => (envLe_takeLabel s l).trans (foldl_takeLabel_envLe ls _)

theorem callOfL_envLe.{u} (Lv : Lvl.{u}) (ps : List PiParam) (out : PiOut) (fv : Sem) (args : List Res)
    {s s' : SState} {r : Res} (h : callOfL Lv ps out fv args s = some (r, s')) : EnvLe s s' := by
  cases happ : applyFnL Lv ps out fv (args.map (·.1)) with
  | none =>
    unfold callOfL at h; dsimp only at h; rw [happ] at h; cases h
  | some res =>
    cases res with
    | data r' finals =>
      unfold callOfL at h; dsimp only at h; rw [happ] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.2]
      exact (foldl_takeLabel_envLe _ _).trans (envLe_mapVals _ _)
    | ref U fwd back =>
      unfold callOfL at h; dsimp only at h; rw [happ] at h
      simp only [SState.freshLoan, Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.2]
      refine EnvLe.trans ?_ (envLe_pushTempShaped _ _ _)
      refine EnvLe.trans ?_ (envLe_mapVals _ _)
      exact (foldl_takeLabel_envLe _ s).trans (EnvLe.of_env rfl)

end

/-! ## A `let`: one binding pushed, then dropped -/

/-- `s'` is `s` with one more binding in the top frame, up to `EnvLe`. -/
def EnvPush (s s' : SState) : Prop :=
  s'.env.length = s.env.length ∧ ∀ (f : Nat) (fr : SFrame), s.env[f]? = some fr →
    ∃ fr' : SFrame, s'.env[f]? = some fr' ∧
      fr'.binds.length = fr.binds.length + (if f = s.topIdx then 1 else 0) ∧ fr.temps.length ≤ fr'.temps.length

theorem EnvPush.trans_le {a b c : SState} (h₁ : EnvPush a b) (h₂ : EnvLe b c) : EnvPush a c := by
  refine ⟨h₂.1.trans h₁.1, fun f fr h => ?_⟩
  obtain ⟨fr', h', hb, ht⟩ := h₁.2 f fr h
  obtain ⟨fr'', h'', hb', ht'⟩ := h₂.2 f fr' h'
  exact ⟨fr'', h'', hb'.trans hb, Nat.le_trans ht ht'⟩

theorem EnvLe.trans_push {a b c : SState} (h₁ : EnvLe a b) (h₂ : EnvPush b c) : EnvPush a c := by
  have ht : b.topIdx = a.topIdx := by simp only [SState.topIdx, h₁.1]
  refine ⟨h₂.1.trans h₁.1, fun f fr h => ?_⟩
  obtain ⟨fr', h', hb, ht1⟩ := h₁.2 f fr h
  obtain ⟨fr'', h'', hb', ht'⟩ := h₂.2 f fr' h'
  exact ⟨fr'', h'', by rw [hb', hb, ht], Nat.le_trans ht1 ht'⟩

theorem envPush_pushBind (s : SState) (b : SBinding) : EnvPush s (s.pushBind b) := by
  refine ⟨by simp [SState.pushBind], fun f fr h => ?_⟩
  simp only [SState.pushBind, List.getElem?_modify, h]
  by_cases e : s.topIdx = f
  · subst e; exact ⟨_, rfl, by simp, by simp⟩
  · exact ⟨fr, by simp [e], by simp [Ne.symm e], Nat.le_refl _⟩

theorem envPush_pushBindShaped (s : SState) (b : SBinding) : EnvPush s (pushBindShaped s b) := by
  unfold pushBindShaped
  split
  · rename_i l _
    dsimp only
    refine (envLe_takeLabel s l).trans_push ?_
    split
    · exact (envPush_pushBind _ b).trans_le (EnvLe.of_env rfl)
    · exact envPush_pushBind _ b
  · exact envPush_pushBind s b

theorem envLe_dropLast_of_push {s a : SState} (h : EnvPush s a) : EnvLe s a.dropLast := by
  have ht : a.topIdx = s.topIdx := by simp only [SState.topIdx, h.1]
  refine ⟨by simp [SState.dropLast, h.1], fun f fr hf => ?_⟩
  obtain ⟨fr', h', hb, htm⟩ := h.2 f fr hf
  simp only [SState.dropLast, List.getElem?_modify, h']
  by_cases e : a.topIdx = f
  · have e' : f = s.topIdx := by rw [← e, ht]
    refine ⟨{ binds := fr'.binds.dropLast, temps := fr'.temps }, by simp [e], ?_, htm⟩
    simp only [e', if_true] at hb
    simp [List.length_dropLast, hb]
  · rw [ht] at e
    simp only [Ne.symm e, if_false, Nat.add_zero] at hb
    exact ⟨fr', by rw [ht]; simp [e], hb, htm⟩

/-- The `let`'s drop after its body: the binding's borrow ended, then the binding forgotten. -/
theorem envLe_letDrop {s s₃ : SState} (h : EnvPush s s₃) (held : Option Nat) :
    EnvLe s (match held with | some l => s₃.endLabel l | none => s₃).dropLast := by
  apply envLe_dropLast_of_push
  cases held with
  | none => exact h
  | some l => exact h.trans_le (envLe_endLabel _ _)

/-- An assignment's hold changes no frame. -/
theorem envLe_hold (s : SState) (l : Nat) (pos : Pos) :
    EnvLe s { s.takeLabel l with shape := fun q => if q = pos then some l else (s.takeLabel l).shape q } :=
  (envLe_takeLabel s l).trans (EnvLe.of_env rfl)

theorem envLe_foldl {α : Type} (g : SState → α → SState) (hg : ∀ s a, EnvLe s (g s a)) :
    ∀ (xs : List α) (s : SState), EnvLe s (xs.foldl g s)
  | [], s => EnvLe.refl s
  | x :: xs, s => (hg s x).trans (envLe_foldl g hg xs _)

/-! ## An assignment's pieces -/

theorem valAt_setAt_self (s : SState) (p : Pos) (v : SVal) (hp : p ∈ s.positions) : (s.setAt p v).valAt p = v := by
  rw [mem_positions] at hp
  cases p with
  | bind f i =>
    simp only [lookup] at hp
    cases e : s.env[f]? with
    | none => rw [e] at hp; cases hp
    | some fr =>
      rw [e] at hp
      simp only [Option.bind_some, Option.isSome_map] at hp
      obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp hp
      simp [SState.setAt, SState.valAt, List.getElem?_modify, e, hb]
  | temp f i =>
    simp only [lookup] at hp
    cases e : s.env[f]? with
    | none => rw [e] at hp; cases hp
    | some fr =>
      rw [e] at hp
      simp only [Option.bind_some] at hp
      have hi : i < fr.temps.length := by simpa using hp
      simp [SState.setAt, SState.valAt, List.getElem?_modify, e, hi]

theorem setContent_eq (K : RunCtx) (φ : Future) {pos : Pos} {steps : List Step} {v : Sem} {s s' : SState}
    (h : setContent K φ pos steps v s = some (⟨⟩, s')) :
    s' = s.setAt pos fun φ' => (Sem.updAt K.dm K.Γ (s.tyAt pos).m (fun _ => v) steps (s.valAt pos φ')).getD .err := by
  unfold setContent at h
  simp only at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    exact h.2.symm
  · cases h

end Ochr.Meaning

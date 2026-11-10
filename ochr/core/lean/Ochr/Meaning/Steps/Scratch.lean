import Ochr.Meaning.Steps.Borrow
open Ochr Ochr.Meaning Ochr.Meaning.Steps

def natB (x : String) (v : Value) : Binding := { hint := ⟨x⟩, ty := some .tNat, val := v }
def refB (x : String) (v : Value) : Binding := { hint := ⟨x⟩, ty := some (.tRef .tNat), val := v }
def S1 : MState := { env := #[{ binds := #[natB "a" .zero] }] }

section
variable (dm : DataModel) (C : CodeMeaning) (Γ : List IndDecl) (ρ : Assignment)

theorem ta_empty (st : MState) (h1 : st.absTy = #[]) (h2 : st.neutrals = []) (h3 : st.etaRefs = []) :
    TypedAssignment dm C Γ ρ st :=
  ⟨fun σ h => by simp [h1] at h, fun n σ h => by simp [h2] at h, fun σ v h => by simp [h3] at h⟩

theorem posTyM_S1 (p : Pos) (T : TyM) (h : MState.posTyM dm C Γ ρ S1 p = some T) :
    p = .bind 0 0 ∧ T = .ty0 Nat := by
  cases p with
  | temp f i => simp [MState.posTyM] at h
  | bind f i =>
    rcases f with _ | f <;> rcases i with _ | i
    · simp [MState.posTyM, S1, natB, Value.tyM, Value.mean, Sem.asTy] at h
      exact ⟨rfl, h.symm⟩
    all_goals simp [MState.posTyM, S1] at h
end

section
variable (dm : DataModel) (C : CodeMeaning) (Γ : List IndDecl) (ρ : Assignment)

theorem wf3_of_empty (env : Env) (h : ∀ l m, ¬ loanUnder env l m) : WF3 env :=
  ⟨fun a => ⟨a, fun b hb => absurd hb (h b a)⟩⟩

theorem bindAt_S1 (f i : Nat) (b : Binding) (h : S1.env[f]?.bind (fun fr => fr.binds[i]?) = some b) :
    f = 0 ∧ i = 0 ∧ b = natB "a" .zero := by
  rcases f with _ | f <;> rcases i with _ | i
  · simp [S1] at h; exact ⟨rfl, rfl, h.symm⟩
  all_goals simp [S1] at h

theorem good_S1 : Good dm C Γ ρ S1 := by
  have hA : allPos S1.env = [.bind 0 0] := by decide +kernel
  have hV : Env.values S1.env = [.zero] := by rw [Env.values, hA]; rfl
  refine ⟨ta_empty dm C Γ ρ S1 rfl rfl rfl, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro φ _ p T hp
    obtain ⟨rfl, rfl⟩ := posTyM_S1 dm C Γ ρ p T hp
    have e : Env.mean dm C Γ ρ φ S1.env (.bind 0 0) = .el0 Nat 0 := rfl
    rw [e]; exact Sem.pmem_of_mem (by simp [Sem.whole]) rfl
  · intro σ h; simp [S1] at h
  · intro G h; simp [MState.goalM, S1] at h
  · refine ⟨?_, ?_⟩
    · rw [hA]; intro p hp; simp at hp; subst hp; show ¬ (Value.zero.hasBorrow = true); decide
    · rw [hA]; intro p hp q hq _ _ _; simp at hp hq; rw [hp, hq]
  · unfold WF2; rw [hV]; refine ⟨?_, ?_⟩
    · intro v hv l hl; simp at hv; subst hv; simp [Value.outerLoans] at hl
    · intro l; simp [Value.outerLoans]
  · apply wf3_of_empty; rintro l m ⟨p, hp, w, hw, _⟩; rw [hA] at hp; simp at hp; subst hp; cases hw
  · unfold WF4; rw [hV]; intro v hv; simp at hv; subst hv; decide
  · unfold WF6; rw [hV]; refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro v hv σ h; simp at hv; subst hv; simp [Value.hasAbs, Value.anyAtom, BEq.beq, Value.beq] at h
    · intro T hT; simp [S1] at hT
    · intro G hG; simp [S1] at hG
    · simp [S1]
    · intro v hv l hl; simp at hv; subst hv; simp [Value.loans] at hl
  · intro p T _ f i b _ hb A hA'
    obtain ⟨_, _, rfl⟩ := bindAt_S1 f i b hb
    simp [natB] at hA'
  · unfold WF8; rw [hV]; refine ⟨?_, ?_, ?_, ?_⟩
    · intro v hv; simp at hv; subst hv; decide
    · intro f i b hb T hT
      obtain ⟨_, _, rfl⟩ := bindAt_S1 f i b hb
      simp [natB] at hT; subst hT; decide
    · intro T hT; simp [S1] at hT
    · intro G hG; simp [S1] at hG
end

def outSt {α : Type} (f : M α) (st : MState) (fuel : Nat) : MState :=
  match runMachine f st fuel with
  | (.ok _ s, _, _) => s
  | _ => default
def outVal {α : Type} [Inhabited α] (f : M α) (st : MState) (fuel : Nat) : α :=
  match runMachine f st fuel with
  | (.ok a _, _, _) => a
  | _ => default
def isOk {α : Type} (f : M α) (st : MState) (fuel : Nat) : Bool :=
  match runMachine f st fuel with
  | (.ok _ _, _, _) => true
  | _ => false

theorem runs_out {α : Type} [Inhabited α] (f : M α) (st : MState) (fuel : Nat)
    (h : isOk f st fuel = true) : Runs f st fuel (outVal f st fuel) (outSt f st fuel) := by
  unfold isOk at h; unfold Runs outVal outSt
  rcases e : runMachine f st fuel with ⟨o, left, log⟩
  rw [e] at h
  cases o with
  | ok a s => exact ⟨left, log, rfl⟩
  | fail _ => simp at h
  | exhausted _ => simp at h

theorem not_wf2_of (env : Env)
    (h : ((Env.values env).any fun v => v.outerLoans.any fun l => !liveLoan env l) = true) : ¬ WF2 env := by
  intro ⟨h1, _⟩
  simp only [List.any_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h
  obtain ⟨v, hv, l, hl, hlive⟩ := h
  have := h1 v hv l hl; simp_all

theorem not_good_of_not_wf2 (dm : DataModel) (C : CodeMeaning) (Γ : List IndDecl) (ρ : Assignment)
    (st : MState) (h : ¬ WF2 st.env) : ¬ Good dm C Γ ρ st :=
  fun ⟨_, _, _, h2, _⟩ => h h2

theorem unit_ne_nat : (Unit : Type) ≠ Nat := fun h => by
  have : ∀ x y : Nat, x = y := h ▸ fun (x y : Unit) => rfl
  exact absurd (this 0 1) (by decide)

theorem not_below_at (m' m : Mean) (p : Pos) (h : ∀ φ' φ, ¬ (m'.val φ' p ⊑ m.val φ p)) : ¬ Below m' m :=
  fun hb => by obtain ⟨φ, h1, _⟩ := hb (fun _ => .err); exact h _ _ (h1 p)

theorem borrowPlace_step_false (K : RunCtx) (ρ : Assignment) (φ : Future) :
    ¬ ∀ (st st' : MState) (fuel : Nat) (p : Place) (v : Value),
      Good K.dm K.C K.Γ ρ st → Runs (Ochr.borrowPlace fuel p) st fuel v st' →
      ∃ r s', Ochr.Meaning.borrowPlace K φ p (SM' K ρ st) = some (r, s') ∧
        meanV K ρ φ r.2 v = r.1 ∧
        Below (MState.mean K.dm K.C K.Γ ρ st') s'.toMean ∧ Good K.dm K.C K.Γ ρ st' := by
  intro hstep
  obtain ⟨_, _, _, _, _, hgood⟩ :=
    hstep S1 _ 10 (.var 0) _ (good_S1 ..) (runs_out _ _ _ (by decide +kernel))
  exact not_good_of_not_wf2 _ _ _ _ _ (not_wf2_of _ (by decide +kernel)) hgood

theorem dropTopBind_step_false (K : RunCtx) (ρ : Assignment) :
    ¬ ∀ (st st' : MState) (fuel : Nat),
      Good K.dm K.C K.Γ ρ st → Runs (Ochr.dropTopBind fuel) st fuel () st' →
      Below (MState.mean K.dm K.C K.Γ ρ st') ((SM' K ρ st).dropLast).toMean ∧
      Good K.dm K.C K.Γ ρ st' := by
  intro hstep
  obtain ⟨hb, _⟩ := hstep S1 _ 10 (good_S1 ..) (runs_out _ _ _ (by decide +kernel))
  refine not_below_at _ _ (.bind 0 0) (fun φ' φ h => ?_) hb
  have e1 : (MState.mean K.dm K.C K.Γ ρ (outSt (Ochr.dropTopBind 10) S1 10)).val φ' (.bind 0 0) = .el0 Unit () := rfl
  have e2 : ((SM' K ρ S1).dropLast).toMean.val φ (.bind 0 0) = .err := rfl
  rw [e1, e2] at h; cases h

theorem el0_le_el0 {A B : Type} {a : A} {b : B} (h : Sem.el0 A a ⊑ Sem.el0 B b) : A = B :=
  (Sem.el0.inj (Sem.le_eq_of_whole h (by simp [Sem.whole]))).1

theorem popFrame_step_false (K : RunCtx) (ρ : Assignment) :
    ¬ ∀ (st st' : MState) (fuel : Nat),
      Good K.dm K.C K.Γ ρ st → Runs (Ochr.popFrame fuel) st fuel () st' →
      Below (MState.mean K.dm K.C K.Γ ρ st') (MState.mean K.dm K.C K.Γ ρ st) ∧
      Good K.dm K.C K.Γ ρ st' := by
  intro hstep
  obtain ⟨hb, _⟩ := hstep S1 _ 10 (good_S1 ..) (runs_out _ _ _ (by decide +kernel))
  refine not_below_at _ _ (.bind 0 0) (fun φ' φ h => ?_) hb
  have hs : (outSt (Ochr.popFrame 10) S1 10).env = #[] := Array.eq_empty_of_size_eq_zero (by decide +kernel)
  have e1 : (MState.mean K.dm K.C K.Γ ρ (outSt (Ochr.popFrame 10) S1 10)).val φ' (.bind 0 0) = .el0 Unit () := by
    simp only [MState.mean, hs]; rfl
  have e2 : (MState.mean K.dm K.C K.Γ ρ S1).val φ (.bind 0 0) = .el0 Nat 0 := rfl
  rw [e1, e2] at h; exact unit_ne_nat (el0_le_el0 h)

theorem assignPlace_step_false (K : RunCtx) (ρ : Assignment) (φ : Future) :
    ¬ ∀ (st st' : MState) (fuel : Nat) (p : Place) (v : Value) (pos : Pos),
      Good K.dm K.C K.Γ ρ st → resolve (SM' K ρ st) p = some (pos, (p.steps).2) →
      Runs (Ochr.assignPlace fuel p v) st fuel () st' →
      ∃ s', setContent K φ pos (p.steps).2 (meanV K ρ φ (.plain .err) v) ((SM' K ρ st).access pos) = some (⟨⟩, s') ∧
        Below (MState.mean K.dm K.C K.Γ ρ st') s'.toMean ∧ Good K.dm K.C K.Γ ρ st' := by
  intro hstep
  obtain ⟨_, _, _, hgood⟩ := hstep S1 _ 10 (.var 0) (.loan 5) (.bind 0 0) (good_S1 ..) rfl
    (runs_out _ _ _ (by decide +kernel))
  exact not_good_of_not_wf2 _ _ _ _ _ (not_wf2_of _ (by decide +kernel)) hgood

/-- `a : Nat ↦ va`, `t : &Nat ↦ borrow_0 0`. -/
def S23 (va : Value) : MState :=
  { env := #[{ binds := #[natB "a" va, refB "t" (.borrow 0 .zero)] }], nextLoan := 1 }

section
variable (dm : DataModel) (C : CodeMeaning) (Γ : List IndDecl) (ρ : Assignment) (va : Value)

theorem bindAt_S23 (f i : Nat) (b : Binding)
    (h : (S23 va).env[f]?.bind (fun fr => fr.binds[i]?) = some b) :
    f = 0 ∧ ((i = 0 ∧ b = natB "a" va) ∨ (i = 1 ∧ b = refB "t" (.borrow 0 .zero))) := by
  rcases f with _ | f <;> rcases i with _ | _ | i
  · simp [S23] at h; exact ⟨rfl, .inl ⟨rfl, h.symm⟩⟩
  · simp [S23] at h; exact ⟨rfl, .inr ⟨rfl, h.symm⟩⟩
  all_goals simp [S23] at h

theorem posTyM_S23 (p : Pos) (T : TyM) (h : MState.posTyM dm C Γ ρ (S23 va) p = some T) :
    (p = .bind 0 0 ∨ p = .bind 0 1) ∧ T = .ty0 Nat := by
  cases p with
  | temp f i => simp [MState.posTyM] at h
  | bind f i =>
    simp only [MState.posTyM] at h
    split at h
    · rename_i b hb
      obtain ⟨rfl, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩ := bindAt_S23 va f i b hb
      · simp [natB, Value.tyM, Value.mean, Sem.asTy] at h; exact ⟨.inl rfl, h.symm⟩
      · simp [refB, Value.tyM, Value.mean, Sem.asTy] at h; exact ⟨.inr rfl, h.symm⟩
    · cases h

theorem shape_S23 (hb : ∀ l w, va ≠ .borrow l w)
    (p : Pos) (l : Nat) (h : Env.shape (S23 va).env p = some l) : p = .bind 0 1 ∧ l = 0 := by
  cases p with
  | temp f i =>
    rcases f with _ | f <;> cases h
  | bind f i =>
    rcases f with _ | f <;> rcases i with _ | _ | i
    · simp only [Env.shape] at h; split at h
      · rename_i l' w e; exact absurd e (hb l' w)
      · cases h
    · simp [Env.shape, valAt, S23, refB] at h; exact ⟨rfl, h.symm⟩
    all_goals cases h

theorem good_S23 (hA : allPos (S23 va).env = [.bind 0 0, .bind 0 1])
    (hlive : liveLoan (S23 va).env 0 = true)
    (hnb : ∀ l w, va ≠ .borrow l w) (hb : va.hasBorrow = false)
    (hol : va.outerLoans = [] ∨ va.outerLoans = [0]) (habs : ∀ σ, va.hasAbs σ = false)
    (hl : ∀ l ∈ va.loans, l < 1) (hbad : va.anyAtom Value.badCapture = false)
    (href : va.typeHasRef = false)
    (hmem : ∀ φ, φ 0 ∈ₛ .ty0 Nat →
      (Env.mean dm C Γ ρ φ (S23 va).env (.bind 0 0)).pmem (.ty0 Nat)) :
    Good dm C Γ ρ (S23 va) := by
  have hV : Env.values (S23 va).env = [va, .borrow 0 .zero] := by rw [Env.values, hA]; rfl
  have hpt : MState.posTyM dm C Γ ρ (S23 va) (.bind 0 1) = some (.ty0 Nat) := rfl
  refine ⟨ta_empty dm C Γ ρ _ rfl rfl rfl, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro φ hφ p T hp
    obtain ⟨rfl | rfl, rfl⟩ := posTyM_S23 dm C Γ ρ va p T hp
    · exact hmem φ (hφ (.bind 0 1) 0 rfl _ hpt)
    · have e : Env.mean dm C Γ ρ φ (S23 va).env (.bind 0 1) = .el0 Nat 0 := rfl
      rw [e]; exact Sem.pmem_of_mem (by simp [Sem.whole]) rfl
  · intro σ h; simp [S23] at h
  · intro G h; simp [MState.goalM, S23] at h
  · refine ⟨?_, ?_⟩
    · rw [hA]; intro p hp; simp at hp
      rcases hp with rfl | rfl
      · have e : valAt (S23 va).env (.bind 0 0) = va := rfl
        rw [e]; split
        · rename_i l w; exact absurd rfl (hnb l w)
        · simp [hb]
      · show ¬ (Value.zero.hasBorrow = true); decide
    · intro p _ q _ l hp hq
      rw [(shape_S23 va hnb p l hp).1, (shape_S23 va hnb q l hq).1]
  · unfold WF2; rw [hV]; refine ⟨?_, ?_⟩
    · intro v hv l hl'; simp at hv
      rcases hv with rfl | rfl
      · rcases hol with h | h <;> rw [h] at hl' <;> simp at hl'; subst hl'; exact hlive
      · simp [Value.outerLoans] at hl'
    · intro l; rcases hol with h | h <;>
        simp [Value.outerLoans, h, List.count_cons] <;> split <;> simp
  · apply wf3_of_empty; rintro l m ⟨p, hp, w, hw, hl'⟩; rw [hA] at hp; simp at hp
    rcases hp with rfl | rfl
    · exact hnb m w hw
    · cases hw; simp [Value.loans] at hl'
  · unfold WF4; rw [hV]; intro v hv; simp at hv
    rcases hv with rfl | rfl
    · simp [hbad]
    · decide
  · unfold WF6; rw [hV]; refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro v hv σ h; simp at hv
      rcases hv with rfl | rfl
      · simp [habs] at h
      · simp [Value.hasAbs, Value.anyAtom, BEq.beq, Value.beq] at h
    · intro T hT; simp [S23] at hT
    · intro G hG; simp [S23] at hG
    · simp [S23]
    · intro v hv l hl'; simp at hv
      rcases hv with rfl | rfl
      · exact hl l hl'
      · simp [Value.loans] at hl'
  · intro p T _ f i b _ hb' A hA'
    obtain ⟨_, (⟨_, rfl⟩ | ⟨_, rfl⟩)⟩ := bindAt_S23 va f i b hb'
    · simp [natB] at hA'
    · simp [refB] at hA'; subst hA'; rfl
  · unfold WF8; rw [hV]; refine ⟨?_, ?_, ?_, ?_⟩
    · intro v hv; simp at hv
      rcases hv with rfl | rfl
      · simp [href]
      · decide
    · intro f i b hb' T hT
      obtain ⟨_, (⟨_, rfl⟩ | ⟨_, rfl⟩)⟩ := bindAt_S23 va f i b hb'
      · simp [natB] at hT; subst hT; decide
      · simp [refB] at hT; subst hT; decide
    · intro T hT; simp [S23] at hT
    · intro G hG; simp [S23] at hG
end

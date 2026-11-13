import Ochr.Meaning.Steps.Statements

/-!
# A counterexample to `popFrame_step_stmt` (pilot prover, round 2, base 5dc7710b)

Not imported by the library root; check with `lake env lean Ochr/Meaning/Steps/BorrowCE.lean`.
The checker run is evaluated by the kernel (`decide +kernel`), no `native_decide`.

`popFrame` pops the top frame with its temporaries (`popFrameRaw`) and drops only its bindings.
A temporary of the popped frame holding `borrow_0` whose lender lives below is discarded without
an [End], so the lender's `loan_0` is left without its borrow and (WF2) fails: `Good st'` is
false. The state `Ωp` (frame 0: temporary `loan_0`; frame 1: temporary `borrow_0 0`) is `Good`
for every `dm`, `C`, `Γ`, `ρ`: no position has a stored type, so membership is vacuous. (With
the lender in a typed binding, the state is not `Good`: the future at a label held by an untyped
temporary is untyped. So the counterexample needs an untyped lender, which a reachable state
may never have; the missing fact is a reachable-state invariant, see the report.)
-/

namespace Ochr.Meaning.Steps.BorrowCE

/-! ## The statements as they stood at 5dc7710b

The three refutations below are against these forms. The spine's fix (the commit after
ae5daec9): the in-flight value is typed by the result's flight (`GoodF`, `flightOf` in
`Statements.lean`, `WF.lean`), and `popFrame_step_stmt` takes `htemps` (the popped frame's
temporaries hold no borrow). The refutations are kept as the record of why. -/

def readPlace_step_stmt_old (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (p : Place) (v : Value) (copy : Bool)
    (hg : Good K.dm K.C K.Γ ρ st) (hΔ : K.Δ = deltaOf K ρ φ st)
    (hcopy : K.D.copy (K.D.placeDecl (scopeOf (SM' K ρ st)) p) = copy)
    (h : Runs (Ochr.readPlace fuel p) st fuel v st'),
    ∃ r s', Ochr.Meaning.readPlace K φ p copy (SM' K ρ st) = some (r, s') ∧
      meanV K ρ φ r.2 v = r.1 ∧
      Below (MState.mean K.dm K.C K.Γ ρ (st'.withTemp v)) s'.toMean ∧ Good K.dm K.C K.Γ ρ (st'.withTemp v)

def borrowPlace_step_stmt_old (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)  (p : Place) (v : Value)
    (hg : Good K.dm K.C K.Γ ρ st) (hΔ : K.Δ = deltaOf K ρ φ st)
    (h : Runs (Ochr.borrowPlace fuel p) st fuel v st'),
    ∃ r s', Ochr.Meaning.borrowPlace K φ p (SM' K ρ st) = some (r, s') ∧
      meanV K ρ φ r.2 v = r.1 ∧
      Below (MState.mean K.dm K.C K.Γ ρ (st'.withTemp v)) s'.toMean ∧ Good K.dm K.C K.Γ ρ (st'.withTemp v)

def popFrame_step_stmt_old (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) : Prop :=
  ∀ (st st' : MState)
    (hg : Good K.dm K.C K.Γ ρ st) (hΔ : K.Δ = deltaOf K ρ φ st) (h : Runs (Ochr.popFrame fuel) st fuel () st'),
    Below (MState.mean K.dm K.C K.Γ ρ st') (MState.mean K.dm K.C K.Γ ρ st) ∧
    Good K.dm K.C K.Γ ρ st'


open Ochr Ochr.Meaning Ochr.Meaning.Steps

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

theorem wf3_of_empty (env : Env) (h : ∀ l m, ¬ loanUnder env l m) : WF3 env :=
  ⟨fun a => ⟨a, fun b hb => absurd hb (h b a)⟩⟩

/-- Frame 0 holds the lender `loan_0` as a temporary, frame 1 the borrow `borrow_0 0`. -/
def Ωp : MState := { env := #[{ temps := #[.loan 0] }, { temps := #[.borrow 0 .zero] }], nextLoan := 1 }

section
variable (dm : DataModel) (C : CodeMeaning) (Γ : List IndDecl) (ρ : Assignment)

theorem posTyM_Ωp (p : Pos) : MState.posTyM dm C Γ ρ Ωp p = none := by
  cases p with
  | temp f i => rfl
  | bind f i => rcases f with _ | _ | f <;> rfl

/-- **(WF9) excludes `Ωp`**: its loan sits in an untyped temporary. At 5dc7710b `Ωp` was `Good`
(`good_Ωp`, since removed) and refuted `popFrame_step_stmt_old`: popping frame 1 discarded
`borrow_0` without ending it. The fixed statement takes `htemps` (`popFrame_htemps_fails_Ωp`),
and (WF9) forbids the state outright. -/
theorem not_wf9_Ωp : ¬ WF9 dm C Γ ρ Ωp := by
  intro h
  have hA : allPos Ωp.env = [.temp 0 0, .temp 1 0] := by decide +kernel
  obtain ⟨T, hT⟩ := h (.temp 0 0) (by rw [hA]; simp) (by decide +kernel)
  rw [posTyM_Ωp] at hT; cases hT
end

/-- **The fixed statement excludes `Ωp`**: its popped frame's temporary holds a borrow, so
`htemps` fails. (`popFrame_step_stmt` at a state whose top temporaries are borrow-free is a
positive obligation for the provers, not a counterexample.) -/
theorem popFrame_htemps_fails_Ωp :
    ¬ ∀ fr, Ωp.env[Ωp.env.size - 1]? = some fr → ∀ v ∈ fr.temps, v.hasBorrow = false := by
  intro h
  have := h _ rfl (.borrow 0 .zero) (by simp [Ωp])
  simp [Value.hasBorrow, Value.anyAtom] at this

/- `popFrame_step_false` (at 5dc7710b: `¬ popFrame_step_stmt_old K ρ φ 10` from `good_Ωp`) is
retired with `good_Ωp`: (WF9) excludes `Ωp`. -/

/-! ## `borrowPlace_step_stmt`: a borrow in flight leaves its lender untyped

`TypedFuture` types the future only at labels held at a *typed* position. The borrow
`borrowPlace` returns is counted as an untyped temporary (`withTemp`), so in
`st'.withTemp v` the future at the fresh label is unconstrained, and the lender, a typed
binding reading `φ ℓ`, holds `err` under the typed future `fun _ => err`: membership fails, so
`Good (st'.withTemp v)` is false whenever a typed place is borrowed. -/

def natB (x : String) (v : Value) : Binding := { hint := ⟨x⟩, ty := some .tNat, val := v }
/-- `a : Nat ↦ 0`. -/
def S1 : MState := { env := #[{ binds := #[natB "a" .zero] }] }

theorem err_not_pmem (T : TyM) : ¬ Sem.err.pmem T := by
  rintro (h | ⟨t, hw, hle, _⟩)
  · cases h
  · cases hle; simp [Sem.whole] at hw

end Ochr.Meaning.Steps.BorrowCE

namespace Ochr.Meaning.Steps.BorrowCE
open Ochr Ochr.Meaning Ochr.Meaning.Steps

abbrev Sb : MState := (outSt (Ochr.borrowPlace 10 (.var 0)) S1 10).withTemp (outVal (Ochr.borrowPlace 10 (.var 0)) S1 10)

theorem shape_Sb (p : Pos) (l : Nat) (h : Env.shape Sb.env p = some l) : p = .temp 0 0 := by
  cases p with
  | bind f i => rcases f with _ | f <;> rcases i with _ | i <;> cases h
  | temp f i => rcases f with _ | f <;> rcases i with _ | i <;> first | rfl | cases h

theorem not_good_Sb (dm : DataModel) (C : CodeMeaning) (Γ : List IndDecl) (ρ : Assignment) :
    ¬ Good dm C Γ ρ Sb := by
  rintro ⟨_, hmem, _⟩
  have htf : TypedFuture dm C Γ ρ Sb (fun _ => .err) := by
    intro p l hp T hT
    rw [shape_Sb p l hp] at hT; cases hT
  have := hmem.pos _ htf (.bind 0 0) (.ty0 Nat) rfl
  exact err_not_pmem _ this


section
variable (dm : DataModel) (C : CodeMeaning) (Γ : List IndDecl) (ρ : Assignment)

theorem posTyM_S1 (p : Pos) (T : TyM) (h : MState.posTyM dm C Γ ρ S1 p = some T) :
    p = .bind 0 0 ∧ T = .ty0 Nat := by
  cases p with
  | temp f i => simp [MState.posTyM] at h
  | bind f i =>
    rcases f with _ | f <;> rcases i with _ | i
    · simp [MState.posTyM, S1, natB, Value.tyM, Value.mean, Sem.asTy] at h
      exact ⟨rfl, h.symm⟩
    all_goals simp [MState.posTyM, S1] at h

theorem bindAt_S1 (f i : Nat) (b : Binding) (h : S1.env[f]?.bind (fun fr => fr.binds[i]?) = some b) :
    f = 0 ∧ i = 0 ∧ b = natB "a" .zero := by
  rcases f with _ | f <;> rcases i with _ | i
  · simp [S1] at h; exact ⟨rfl, rfl, h.symm⟩
  all_goals simp [S1] at h

theorem good_S1 : Good dm C Γ ρ S1 := by
  have hA : allPos S1.env = [.bind 0 0] := by decide +kernel
  have hV : Env.values S1.env = [.zero] := by rw [Env.values, hA]; rfl
  refine ⟨⟨fun σ h => by simp [S1] at h, fun n σ h => by simp [S1] at h, fun σ v h => by simp [S1] at h⟩,
    ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
  · intro p hp _; rw [hA] at hp; simp at hp; subst hp; exact ⟨_, rfl⟩
  · intro v hv; rw [hV] at hv; simp at hv; subst hv; rfl
end

/-- `borrowPlace_step_stmt` is false at fuel 10, for every run context, assignment and future:
borrowing `a : Nat ↦ 0` gives a state `st'.withTemp v` that is not `Good`. -/
theorem borrowPlace_step_false (K : RunCtx) (ρ : Assignment) (φ : Future)
    (hΔ : K.Δ = deltaOf K ρ φ S1) : ¬ borrowPlace_step_stmt_old K ρ φ 10 := by
  intro hstep
  obtain ⟨_, _, _, _, _, hgood⟩ := hstep S1 _ (.var 0) _ (good_S1 ..) hΔ (runs_out _ _ _ (by decide +kernel))
  exact not_good_Sb _ _ _ _ hgood


/-! ## `readPlace_step_stmt`: the same gap when a borrow is moved out of a typed holder -/

def refB (x : String) (v : Value) : Binding := { hint := ⟨x⟩, ty := some (.tRef .tNat), val := v }

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
    (hrec : va.anyAtom (Value.bareCtor Γ) = false)
    (href : va.typeHasRef = false)
    (hmem : ∀ φ, φ 0 ∈ₛ .ty0 Nat →
      (Env.mean dm C Γ ρ φ (S23 va).env (.bind 0 0)).pmem (.ty0 Nat)) :
    Good dm C Γ ρ (S23 va) := by
  have hV : Env.values (S23 va).env = [va, .borrow 0 .zero] := by rw [Env.values, hA]; rfl
  have hpt : MState.posTyM dm C Γ ρ (S23 va) (.bind 0 1) = some (.ty0 Nat) := rfl
  refine ⟨⟨fun σ h => by simp [S23] at h, fun n σ h => by simp [S23] at h, fun σ v h => by simp [S23] at h⟩, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
  · intro p hp _; rw [hA] at hp; simp at hp
    rcases hp with rfl | rfl <;> exact ⟨_, rfl⟩
  · intro v hv; rw [hV] at hv; simp at hv
    rcases hv with rfl | rfl
    · exact hrec
    · rfl
end


theorem mem_nat_pmem (s : Sem) (h : s ∈ₛ .ty0 Nat) : s.pmem (.ty0 Nat) := by
  cases s <;> simp [Sem.mem] at h
  exact Sem.pmem_of_mem (by simp [Sem.whole]) (by simp [Sem.mem, h])

abbrev Sr : MState := (outSt (Ochr.readPlace 10 (.var 0)) (S23 (.loan 0)) 10).withTemp
  (outVal (Ochr.readPlace 10 (.var 0)) (S23 (.loan 0)) 10)

theorem shape_Sr (p : Pos) (l : Nat) (h : Env.shape Sr.env p = some l) : p = .temp 0 0 := by
  cases p with
  | bind f i => rcases f with _ | f <;> rcases i with _ | _ | i <;> cases h
  | temp f i => rcases f with _ | f <;> rcases i with _ | i <;> first | rfl | cases h

/-- `readPlace_step_stmt` is false at fuel 10: reading `t : &Nat ↦ borrow_0 0` moves the borrow
into an untyped temporary, and the lender `a : Nat ↦ loan_0` is no longer typed. -/
theorem readPlace_step_false (K : RunCtx) (ρ : Assignment) (φ : Future)
    (hΔ : K.Δ = deltaOf K ρ φ (S23 (.loan 0))) : ¬ readPlace_step_stmt_old K ρ φ 10 := by
  intro hstep
  have hg : Good K.dm K.C K.Γ ρ (S23 (.loan 0)) :=
    good_S23 _ _ _ _ _ (by decide +kernel) (by decide +kernel) (fun _ _ h => by cases h) rfl
      (.inr rfl) (fun _ => rfl) (by simp [Value.loans]) rfl rfl rfl (fun φ h => mem_nat_pmem _ h)
  obtain ⟨_, _, _, _, _, hgood⟩ := hstep (S23 (.loan 0)) _ (.var 0) _ _ hg hΔ rfl
    (runs_out _ _ _ (by decide +kernel))
  obtain ⟨_, hmem, _⟩ := hgood
  have htf : TypedFuture K.dm K.C K.Γ ρ Sr (fun _ => .err) := by
    intro p l hp T hT
    rw [shape_Sr p l hp] at hT; cases hT
  exact err_not_pmem _ (hmem.pos _ htf (.bind 0 0) (.ty0 Nat) rfl)

end Ochr.Meaning.Steps.BorrowCE

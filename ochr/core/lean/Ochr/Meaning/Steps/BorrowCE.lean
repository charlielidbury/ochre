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

theorem good_Ωp : Good dm C Γ ρ Ωp := by
  have hA : allPos Ωp.env = [.temp 0 0, .temp 1 0] := by decide +kernel
  have hV : Env.values Ωp.env = [.loan 0, .borrow 0 .zero] := by rw [Env.values, hA]; rfl
  refine ⟨⟨fun σ h => by simp [Ωp] at h, fun n σ h => by simp [Ωp] at h, fun σ v h => by simp [Ωp] at h⟩,
    ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro φ _ p T hp; rw [posTyM_Ωp] at hp; cases hp
  · intro σ h; simp [Ωp] at h
  · intro G h; simp [MState.goalM, Ωp] at h
  · refine ⟨?_, ?_⟩
    · rw [hA]; intro p hp; simp at hp
      rcases hp with rfl | rfl
      · show ¬ ((Value.loan 0).hasBorrow = true); decide
      · show ¬ (Value.zero.hasBorrow = true); decide
    · rw [hA]; intro p hp q hq l h1 h2; simp at hp hq
      rcases hp with rfl | rfl <;> rcases hq with rfl | rfl <;> first | rfl | (cases h1 <;> cases h2)
  · unfold WF2; rw [hV]; refine ⟨?_, ?_⟩
    · intro v hv l hl; simp at hv
      rcases hv with rfl | rfl
      · simp [Value.outerLoans] at hl; subst hl; decide +kernel
      · simp [Value.outerLoans] at hl
    · intro l; simp [Value.outerLoans, List.count_cons]; split <;> simp
  · apply wf3_of_empty; rintro l m ⟨p, hp, w, hw, hl⟩; rw [hA] at hp; simp at hp
    rcases hp with rfl | rfl
    · cases hw
    · cases hw; simp [Value.loans] at hl
  · unfold WF4; rw [hV]; intro v hv; simp at hv
    rcases hv with rfl | rfl <;> decide
  · unfold WF6; rw [hV]; refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro v hv σ h; simp at hv
      rcases hv with rfl | rfl <;> simp [Value.hasAbs, Value.anyAtom, BEq.beq, Value.beq] at h
    · intro T hT; simp [Ωp] at hT
    · intro G hG; simp [Ωp] at hG
    · simp [Ωp]
    · intro v hv l hl; simp at hv
      rcases hv with rfl | rfl <;> simp [Value.loans] at hl <;> simp [hl, Ωp]
  · intro p T hp; rw [posTyM_Ωp] at hp; cases hp
  · unfold WF8; rw [hV]; refine ⟨?_, ?_, ?_, ?_⟩
    · intro v hv; simp at hv
      rcases hv with rfl | rfl <;> decide
    · intro f i b hb; rcases f with _ | _ | f <;> simp [Ωp] at hb
    · intro T hT; simp [Ωp] at hT
    · intro G hG; simp [Ωp] at hG
end

/-- `popFrame_step_stmt` is false at fuel 10, for every run context, assignment and future
(with `K.Δ` read off `Ωp`, as the statement assumes): popping frame 1 discards `borrow_0`
without ending it. -/
theorem popFrame_step_false (K : RunCtx) (ρ : Assignment) (φ : Future)
    (hΔ : K.Δ = deltaOf K ρ φ Ωp) : ¬ popFrame_step_stmt K ρ φ 10 := by
  intro hstep
  obtain ⟨_, hgood⟩ := hstep Ωp _ (good_Ωp ..) hΔ (runs_out _ _ _ (by decide +kernel))
  exact (not_wf2_of _ (by decide +kernel)) hgood.2.2.2.1

end Ochr.Meaning.Steps.BorrowCE

import Ochr.Meaning.Steps.Statements
import Ochr.Meaning.PosLib

/-!
# `exitWorld`, flipped: an unknown a discarded arm created owes no element (built)

`Regress/ExitWorld_f32a7048.lean` (unbuilt) records `exitWorld_step_stmt` false: `exitWorld` keeps
the types of the unknowns an arm created, and `TypedAssignment.mem` asked an element of every
`σ < absTy.size`. With `mem` over the unknowns the state references (`MState.Refd`), the state
after `exitWorld` in that record is `Good` at the very assignment that refuted it (`good_after`):
nothing references the arm's unknown.
-/

namespace Ochr.Meaning.Regress.ExitWorldFlip
open Ochr Ochr.Meaning Ochr.Meaning.Steps

/-- The snapshot: the empty state. -/
def saved : MState := {}
/-- The arm's end state: one unknown `σ₀ : Nat` was created. -/
def cur : MState := { absTy := #[.tNat], nextAbs := 1 }
/-- What `exitWorld` leaves: the snapshot, keeping the arm's unknown. -/
def after : MState := { saved with absTy := #[.tNat], nextAbs := 1 }

theorem allPos_after : allPos after.env = [] := by
  rw [allPos_eq]; rfl

theorem runs_exit : Runs (exitWorld ⟨saved⟩) cur 0 () after := ⟨_, _, rfl⟩

theorem noBind (f i : Nat) : (after.env[f]?.bind fun fr => fr.binds[i]?) = none := by
  cases f with
  | zero => rfl
  | succ f => rfl

/-- Nothing references an unknown in the state after `exitWorld`: no value, no type, no goal, no
record. -/
theorem not_refd (σ : Nat) : ¬ after.Refd σ := by
  intro h
  induction h with
  | val v hv _ => simp [Env.values, allPos_after] at hv
  | ty f i b T hb _ _ => rw [noBind] at hb; cases hb
  | lazyTy f i b P ws j hb _ _ => rw [noBind] at hb; cases hb
  | goal G hG _ => simp [after, saved] at hG
  | neutral n σ' hn _ => simp [after, saved] at hn
  | eta σ' v he _ => simp [after, saved] at he
  | dep σ' T _ _ _ ih => exact ih

variable (K : RunCtx)

/-- The state after `exitWorld` is `Good` at every assignment, the one that gives the arm's
unknown `err` included. -/
theorem good_after (ρ : Assignment) : Good K.dm K.M K.Γ ρ after := by
  have hv : Env.values after.env = [] := by simp [Env.values, allPos_after]
  have hpos : ∀ p T, MState.posTyM K.dm K.M K.Γ ρ after p ≠ some T := by
    intro p T h
    cases p with
    | bind f i => simp only [MState.posTyM, noBind] at h; cases h
    | temp f i => cases h
  refine ⟨⟨fun σ h _ => absurd h (not_refd σ), fun n σ h => absurd h (by simp [after, saved]),
      fun σ v h => absurd h (by simp [after, saved])⟩, ⟨fun φ _ p T h => absurd h (hpos p T),
      fun σ h _ => absurd h (not_refd σ), fun G h => by simp [MState.goalM, after, saved] at h⟩, ?_⟩
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro p hp; rw [allPos_after] at hp; cases hp
  · intro p hp; rw [allPos_after] at hp; cases hp
  · intro v hvv; rw [hv] at hvv; cases hvv
  · intro l; rw [hv]; simp
  · exact ⟨fun a => ⟨a, fun b ⟨p, hp, _⟩ => by rw [allPos_after] at hp; cases hp⟩⟩
  · intro v hvv; rw [hv] at hvv; cases hvv
  · intro v hvv; rw [hv] at hvv; cases hvv
  · intro T hT σ hσ
    simp only [after, saved, List.mem_singleton] at hT
    subst hT
    simp only [Value.hasAbs, Value.anyAtom] at hσ
    first
      | cases hσ
      | exact absurd hσ (by simp [BEq.beq, Value.beq])
      | exact absurd hσ (by rfl)
  · intro G hG; simp [after, saved] at hG
  · simp [after]
  · intro v hvv; rw [hv] at hvv; cases hvv
  · intro p T h; exact absurd h (hpos p T)
  · intro v hvv; rw [hv] at hvv; cases hvv
  · intro f i b hb; rw [noBind] at hb; cases hb
  · intro T hT
    simp only [after, saved, List.mem_singleton] at hT
    subst hT
    simp [Value.typeHasRef, Value.anyAtom]
  · intro G hG; simp [after, saved] at hG
  · intro p hp; rw [allPos_after] at hp; cases hp
  · intro v hvv; rw [hv] at hvv; cases hvv

end Ochr.Meaning.Regress.ExitWorldFlip

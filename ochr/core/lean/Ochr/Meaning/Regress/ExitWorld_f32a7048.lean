import Ochr.Meaning.Steps.Statements
import Ochr.Meaning.PosLib
/-!
# `exitWorld_step_stmt` was false as stated (archived record; NOT built: kernel-checked against
# spine f32a7048, axioms propext, Classical.choice, Quot.sound)

`exitWorld_stmt_false`: at every run context, future and fuel, `exitWorld_step_stmt K (fun _ =>
.err) φ fuel` fails. The statement concludes `Good ρ st'` at the assignment it was given, and
`TypedAssignment.mem` asked an element of `⟦Δ(σ)⟧` for every `σ < absTy.size`; `exitWorld` keeps
the types of the unknowns the arm created (D37), where `ρ` is unconstrained. Here the arm created
`σ₀ : Nat` and `ρ σ₀ = err`.

A fault of `TypedAssignment` (docs/31 D20, item 8), not of the checker: an assignment owes an
element only to an unknown the state references (`MState.Refd`), fixed after f32a7048. The
flipped check is `Regress/ExitWorld_flipped.lean` (built): the same state is `Good` at that
assignment.
-/
open Ochr Ochr.Meaning Ochr.Meaning.Steps

namespace ExitWorldCE

/-- The snapshot: the empty state. -/
def saved : MState := {}
/-- The arm's end state: one unknown `σ₀ : Nat` was created. -/
def cur : MState := { absTy := #[.tNat], nextAbs := 1 }
/-- What `exitWorld` leaves: the snapshot, keeping the arm's unknown. -/
def after : MState := { saved with absTy := #[.tNat], nextAbs := 1 }

theorem allPos_saved : allPos saved.env = [] := by
  rw [allPos_eq]; rfl

theorem runs_exit : Runs (exitWorld ⟨saved⟩) cur 0 () after := ⟨_, _, rfl⟩

theorem noBind (f i : Nat) : (saved.env[f]?.bind fun fr => fr.binds[i]?) = none := by
  cases f with
  | zero => rfl
  | succ f => rfl

variable (K : RunCtx)

theorem good_saved (ρ : Assignment) : Good K.dm K.M K.Γ ρ saved := by
  have hv : Env.values saved.env = [] := by simp [Env.values, allPos_saved]
  have hpos : ∀ p T, MState.posTyM K.dm K.M K.Γ ρ saved p ≠ some T := by
    intro p T h
    cases p with
    | bind f i => simp only [MState.posTyM, noBind] at h; cases h
    | temp f i => cases h
  refine ⟨⟨fun σ h => absurd h (by simp [saved]), fun n σ h => absurd h (by simp [saved]),
      fun σ v h => absurd h (by simp [saved])⟩, ⟨fun φ _ p T h => absurd h (hpos p T),
      fun σ h => absurd h (by simp [saved]), fun G h => by simp [MState.goalM, saved] at h⟩, ?_⟩
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro p hp; rw [allPos_saved] at hp; cases hp
  · intro p hp; rw [allPos_saved] at hp; cases hp
  · intro v hvv; rw [hv] at hvv; cases hvv
  · intro l; rw [hv]; simp
  · exact ⟨fun a => ⟨a, fun b ⟨p, hp, _⟩ => by rw [allPos_saved] at hp; cases hp⟩⟩
  · intro v hvv; rw [hv] at hvv; cases hvv
  · intro v hvv; rw [hv] at hvv; cases hvv
  · intro T hT; simp [saved] at hT
  · intro G hG; simp [saved] at hG
  · simp [saved]
  · intro v hvv; rw [hv] at hvv; cases hvv
  · intro p T h; exact absurd h (hpos p T)
  · intro v hvv; rw [hv] at hvv; cases hvv
  · intro f i b hb; rw [noBind] at hb; cases hb
  · intro T hT; simp [saved] at hT
  · intro G hG; simp [saved] at hG
  · intro p hp; rw [allPos_saved] at hp; cases hp
  · intro v hvv; rw [hv] at hvv; cases hvv

/-- **`exitWorld_step_stmt` is false as stated**, at every run context, future and fuel: it
concludes `Good ρ st'` at the assignment it was given, which nothing constrains at the unknowns the
arm created and `exitWorld` keeps (D37). Here the arm created `σ₀ : Nat` and `ρ σ₀ = err`. -/
theorem exitWorld_stmt_false (φ : Future) (fuel : Nat) : ¬ exitWorld_step_stmt K (fun _ => .err) φ fuel := by
  intro h
  obtain ⟨-, -, -, -, -, hg, -, -⟩ := h cur after ⟨saved⟩ (good_saved K _) runs_exit
  have hm := hg.mem 0 (by simp [after])
  simp [MState.absTyM, after, Value.tyM, Value.mean, Sem.asTy, Sem.mem] at hm
end ExitWorldCE

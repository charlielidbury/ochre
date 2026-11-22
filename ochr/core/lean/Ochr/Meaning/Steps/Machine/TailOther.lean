import Ochr.Meaning.Steps.MasterTail
import Ochr.Meaning.Steps.Machine.Inv

/-!
# `TailOtherInv`, proved (machine9)

`checkTail` of a term it does not treat by shape: `locatedTail` (the editor's notes and the arm's record, which
change only `locs`, inside `located`, which changes only `locs` around its body: `Runs.located_inv`), then
`checkTailAt`'s default case (every other case is a shape `tailShaped` names), the typed `eval` at the goal and the
continuation. The run's end is the continuation's but for `locs` (the restatement of 2026-11-22).
-/

namespace Ochr.Meaning.Steps.Machine
open Ochr Ochr.Meaning Ochr.Meaning.Steps

theorem LocsEq.trans {a b c : MState} (h₁ : LocsEq a b) (h₂ : LocsEq b c) : LocsEq a c := by
  unfold LocsEq at *; rw [← h₂, ← h₁]

set_option maxHeartbeats 4000000 in
/-- `locatedTail`'s editor prefix changes only the editor's fields. -/
theorem Runs.locatedTail_inv {t : Term} {x : M Unit} {st st' : MState} {b : Nat}
    (h : Runs (locatedTail t x) st b () st') :
    ∃ st₀ b₀ st₁, LocsEq st st₀ ∧ Runs x st₀ b₀ () st₁ ∧ LocsEq st₁ st' := by
  unfold locatedTail at h
  obtain ⟨st₀, b₀, st₁, hl0, hx, hl1⟩ := Runs.located_inv h
  simp only [runs_get_bind] at hx
  split at hx
  · repeat (any_goals first
      | (split at hx)
      | (with_reducible replace hx := Runs.log_bind hx)
      | (simp only [noteAt, noteLoc, placeContent?, bind_assoc, runs_get_bind, runs_modify_bind, runs_pure_bind',
          pure_bind] at hx))
    all_goals exact ⟨_, _, st₁, hl0.trans (by unfold LocsEq; rfl), hx, hl1⟩
  · exact ⟨st₀, b₀, st₁, hl0, hx, hl1⟩

set_option maxHeartbeats 4000000 in
theorem tailOtherInv : Form.Master.TailOtherInv := by
  intro n t k st st' bh ht h
  cases n with
  | zero => unfold Ochr.checkTail at h; simp only [runs_exhausted_iff] at h
  | succ n =>
  unfold Ochr.checkTail at h
  obtain ⟨st₀, b₀, st₁, hl0, hx, hl1⟩ := Runs.locatedTail_inv h
  cases n with
  | zero => unfold Ochr.checkTailAt at hx; simp only [runs_exhausted_iff] at hx
  | succ m =>
  unfold Ochr.checkTailAt at hx
  split at hx
  all_goals first
    | (simp [Form.Master.tailShaped] at ht)
    | skip
  rw [runs_get_bind] at hx
  obtain ⟨⟨v, T?⟩, s₂, b₂, hev, hk⟩ := Runs.bind_inv hx
  have hg : st₀.goal = st.goal := by rw [← hl0]
  cases T? with
  | none => exact absurd hk (fun h => runs_err_false h)
  | some T =>
    refine ⟨m, st₀, s₂, st₁, v, T, b₀, b₂, by omega, ?_, ?_, by rw [← hl0], by rw [← hl0], hg, by rw [← hg]; exact hev,
      hk, hl1⟩
    · rw [← hl0]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · rw [← hl0]; exact ⟨rfl, rfl, rfl, rfl⟩

/-- **The tail step for every term `checkTail` does not treat by shape, with nothing assumed of the checker.** -/
theorem tStepOther_free (K : RunCtx) (φ : Future) : Form.Master.TStepOther K φ :=
  Form.Master.tStepOther tailOtherInv K φ

end Ochr.Meaning.Steps.Machine

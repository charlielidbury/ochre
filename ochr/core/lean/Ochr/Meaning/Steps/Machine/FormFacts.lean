import Ochr.Meaning.Steps.FormMachine
import Ochr.Meaning.Steps.DropOne
import Ochr.Meaning.Steps.ColumnC
import Ochr.Meaning.Steps.Machine.EvalInv

/-!
# The column's facts about the checker alone (`Steps/FormMachine.lean`), proved

`FormMachine.lean` states, as `Prop`s, the facts about the checker's runs that the first column
(`ColumnC.column_C_ff`) assumes. This file proves those that are true as written; the others are
mis-stated (the machine lane's report of 2026-11-21: an entry with `tailNext` set, a lazily typed
binding, a lent place, `tailDecl`) and are to be proved here in corrected form. Proved so far:
`ZeroInv` (the run computed by `rfl`). `DropNoopInv` is true but its inversion is not done (see
`Steps/Machine/HANDOFF.md`).

This file is downstream of `FormMachine.lean` (which imports `MachineMono` through `StrictSim`), so
`Ochr/Meaning.lean` imports it (the lead's line).
-/

namespace Ochr.Meaning.Steps.Machine

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.Steps.Form

/-- **`ZeroInv`**: `Z` evaluates to `Z` at `Nat`, the state as it was (the run is computed). -/
theorem zeroInv : ZeroInv := by
  intro n typed hint st st' bh v T? h
  obtain ⟨L, left, log, h⟩ := h
  cases bh with
  | zero =>
    have e : runMachineL (Ochr.evalCore (n + 1) typed .zero hint) st 0 L = (.exhausted "out of fuel", 0, L) := rfl
    rw [e] at h; cases h
  | succ k =>
    have e : runMachineL (Ochr.evalCore (n + 1) typed .zero hint) st (k + 1) L =
        (.ok (.zero, some .tNat) st, k, L) := rfl
    rw [e] at h
    simp only [Prod.mk.injEq, Outcome.ok.injEq] at h
    obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, -⟩ := h
    exact ⟨rfl, rfl, Kern.rfl' _, id⟩

/-- **`DecBack`**: alignment at a larger table is alignment at a smaller one (`DecTab.back`, proved in
`DecBack.lean`). -/
theorem decBack : ColumnC.DecBack := fun _ _ _ hd hg => DecTab.back hd hg

open Ochr.Meaning.DecideScope Ochr.Meaning.Steps.Slice in
theorem liveLoansIn_nil {env : Env} {v : Value} (h : v.loans = []) : liveLoansIn env v = [] := by
  simp [liveLoansIn, h]

open Ochr.Meaning.DecideScope Ochr.Meaning.Steps.Slice in
theorem runs_endLoansOfTopBind_noop {k f : Nat} {st st' : MState} {bh : Nat} {b : Binding}
    (hb : (st.env[f]!).binds.back? = some b) (hl : b.val.loans = [])
    (h : Runs (Ochr.endLoansOfTopBind k f) st bh () st') : st' = st := by
  cases k with
  | zero => unfold Ochr.endLoansOfTopBind at h; simp only [runs_exhausted_iff] at h
  | succ j =>
    rw [Ochr.endLoansOfTopBind.eq_1] at h
    peel h
    rw [hb] at h
    peel h
    rw [liveLoansIn_nil hl] at h
    peel h
    exact (runs_pure_inv h).2

open Ochr.Meaning.DecideScope Ochr.Meaning.Steps.Slice in
/-- **`DropNoopInv`**: [Drop] of a binding that holds no loan and no borrow ends nothing and pops it
(`endLoansOfTopBind` finds no live loan in a value with no loan). -/
theorem dropNoopInv : DropNoopInv := by
  intro n st st' bh fr b hfr hb hl hnb hhb h
  cases n with
  | zero => unfold Ochr.dropTopBind at h; simp only [runs_exhausted_iff] at h
  | succ k =>
    rw [Ochr.dropTopBind.eq_1] at h
    obtain ⟨f, s₁, b₁, hf, h₁⟩ := Runs.bind_inv h
    clear h
    obtain ⟨hf1, hs⟩ := runs_topIdx_inv hf
    clear hf
    subst hf1
    rw [hs] at h₁
    clear hs
    have hb' : (st.env[st.env.size - 1]!).binds.back? = some b := by
      rw [getElem!_def, hfr]; exact hb
    peel h₁
    rw [hb'] at h₁
    peel h₁
    split at h₁
    · simp only [runs_err_bind] at h₁
    · first
        | (split at h₁
           · exact absurd ‹_› (hnb _ _)
           · skip)
        | skip
      obtain ⟨u, s₂, b₂, he, h₂⟩ := Runs.bind_inv h₁
      have := runs_endLoansOfTopBind_noop hb' hl he
      subst this
      unfold modifyFrame at h₂
      have := runs_modify_inv h₂
      subst this
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
#print axioms decBack
#print axioms dropNoopInv

end Ochr.Meaning.Steps.Machine

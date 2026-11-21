import Ochr.Meaning.Steps.FormMachine
import Ochr.Meaning.Steps.DropOne
import Ochr.Meaning.Steps.ColumnC

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

theorem runs_modify_inv {g : MState → MState} {st st' : MState} {b : Nat} {u : Unit}
    (h : Runs (modify g : M Unit) st b u st') : st' = g st := by
  obtain ⟨L, left, log, h⟩ := h
  simp only [runMachineL_modify, Prod.mk.injEq, Outcome.ok.injEq] at h
  exact h.1.2.symm

theorem runs_err_bind_false {α β : Type} {m : String} {k : α → M β} {st st' : MState} {b : Nat} {y : β}
    (h : Runs (err m >>= k) st b y st') : False := by
  obtain ⟨_, s₁, b₁, h₁, -⟩ := Runs.bind_inv h
  exact runs_err_false h₁

theorem runs_topIdx_inv {st st' : MState} {b f : Nat} (h : Runs (topIdx : M Nat) st b f st') :
    f = st.env.size - 1 ∧ st' = st := by
  unfold topIdx at h
  obtain ⟨_, s₁, b₁, h₁, h⟩ := Runs.bind_inv h
  obtain ⟨rfl, rfl⟩ := runs_get_inv h₁
  exact runs_pure_inv h

#print axioms decBack

end Ochr.Meaning.Steps.Machine

import Ochr.Meaning.Steps.FormMachine
import Ochr.Meaning.Steps.DropOne
import Ochr.Meaning.Steps.ColumnC
import Ochr.Meaning.Steps.Machine.InvShape
import Ochr.Meaning.Steps.Machine.InvSteps
import Ochr.Meaning.Steps.Machine.PlaceLocalFF
import Ochr.Meaning.Steps.Machine.SeqInv
import Ochr.Meaning.Steps.Machine.VarEndInv

/-!
# The column's facts about the checker alone (`Steps/FormMachine.lean`), proved

`FormMachine.lean` states, as `Prop`s, the facts about the checker's runs that the first column
(`ColumnC.column_C_ff`) assumes. Proved as stated: `ZeroInv`, `DropNoopInv`, `ColumnC.DecBack`
(`MachineMono.DecTab.back`), `VarNumInv` (`ReadInv.lean`), `BorrowNumInv` (`BorrowInv.lean`). Proved in the form proposed to the lead where the stated one is not
provable from the checker's code alone (`Steps/Machine/EvalInv.lean`, `StepInv.lean`; each docstring
says what differs and why): `EvalInvR`, `SuccInvR`, `LetInvR`.

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
/-- The type check of a value without a type does nothing. -/
theorem runs_expectTy_none {n : Nat} {w : String} {A : Value} {st st' : MState} {b : Nat}
    (h : Runs (Ochr.expectTy n w none A) st b () st') : st' = st := by
  cases n with
  | zero => unfold Ochr.expectTy at h; simp only [runs_exhausted_iff] at h
  | succ k => unfold Ochr.expectTy at h; peel h; exact (runs_pure_inv h).2

/-- `InvExpectTy` for a type `==` the expected one (machine3's proposed form, 2026-11-21): the check
is the identity. For arbitrary types it is the whole-machine fact that a comparison makes only clean
unknowns and keeps `absTy.size = nextAbs` and `absDecl` sorted (not state-level, unscheduled). -/
theorem invExpectTyEq (n : Nat) (w : String) (T : Option Value) (A : Value) (st st' : MState) (bh : Nat)
    (hT : ∀ T₀, T = some T₀ → (T₀ == A) = true) (h : Runs (Ochr.expectTy n w T A) st bh () st') : KeepsInv st st' := by
  cases T with
  | none => rw [runs_expectTy_none h]; exact fun _ _ h => h
  | some T₀ => rw [runs_expectTy_of_beq (hT T₀ rfl) h]; exact fun _ _ h => h

/-- **The state-level lemmas, all proved** (`InvSteps.lean`; the six of the machine lane's review in
the forms `FormMachine.lean` adopted, 2026-11-21). -/
theorem invSteps : InvSteps :=
  ⟨invPushInert, invPopInert, invSetBot, invSetNum', invBindNum', invBindBorrow', invPopBind', invLend,
    invWriteDeref', invEndRead', invExpectTyEq⟩

/-- **`SeqInv`, proved** (the statement as restated by machine3 with the lead's permission). -/
theorem seqInv : SeqInv := seqInvR

#print axioms decBack
#print axioms dropNoopInv
#print axioms evalInvR
#print axioms succInvR
#print axioms letInvR
#print axioms varNumInv
#print axioms borrowNumInv
#print axioms runs_expectTy_of_beq
#print axioms invExpectTyEq
#print axioms invPushInert
#print axioms invPopInert
#print axioms invSetBot
#print axioms invLend
#print axioms invSetNum'
#print axioms invWriteDeref'
#print axioms invBindNum'
#print axioms invBindBorrow'
#print axioms invPopBind'
#print axioms invEndRead'
#print axioms invSteps
#print axioms placeLocal_ff
#print axioms seqInvR
#print axioms varEndInv

end Ochr.Meaning.Steps.Machine

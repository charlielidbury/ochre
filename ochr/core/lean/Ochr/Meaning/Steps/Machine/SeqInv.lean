import Ochr.Meaning.Steps.Machine.StepInv
import Ochr.Meaning.Steps.Machine.ReadInv

/-!
# `SeqInv`: the inversion of a typed `u; w` (machine lane)

`Machine.evalCore`'s `.seq`: `u` evaluated with no hint; its value dropped (`dropValue`: pushed as a
temporary, its borrowers ended, popped; for a value holding no borrow and no loan nothing ends, so
the drop is a push and a pop); the tail's reading set to the sequence's own (`tailDecl := curDecl`),
the type demand restored, the tail flag set to the sequence's (`tailNext := curTail`); `w` evaluated
with no hint (typed).
-/

namespace Ochr.Meaning.Steps.Machine

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.DecideScope Ochr.Meaning.Steps.Slice

theorem popTempE_pushTempTyE (env : Env) (v : Value) (T : Option Value) :
    Env.popTempE (Env.pushTempTyE env v T) = env := by
  apply _root_.Array.ext_getElem?
  intro i
  simp only [Env.popTempE, Env.pushTempTyE, Array.getElem?_modify, Array.size_modify]
  split
  · cases env[i]? with
    | none => rfl
    | some fr => simp
  · rfl

theorem topTemp_withTempT {st : MState} {v v' : Value} {T : Option Value}
    (h : ((st.withTempT v T).env[(st.withTempT v T).env.size - 1]!).temps.back? = some v') : v' = v := by
  have hs : (st.withTempT v T).env.size = st.env.size := by simp [MState.withTempT]
  rw [hs] at h
  by_cases h0 : st.env.size = 0
  · have : st.env = #[] := Array.eq_empty_of_size_eq_zero h0
    simp [MState.withTempT, this] at h
    have e : (default : Frame).temps = #[] := rfl
    rw [e] at h; simp at h
  · rw [getElem!_pos _ _ (by rw [hs]; omega)] at h
    simp only [MState.withTempT, Array.getElem_modify, if_true, Array.back?_push] at h
    exact (Option.some.inj h).symm

theorem runs_endLoansOfTopTemp_noop {k : Nat} {st st' : MState} {bh : Nat}
    (hv : ∀ v, (st.env[st.env.size - 1]!).temps.back? = some v → v.loans = [])
    (h : Runs (Ochr.endLoansOfTopTemp k) st bh () st') : st' = st := by
  cases k with
  | zero => unfold Ochr.endLoansOfTopTemp at h; simp only [runs_exhausted_iff] at h
  | succ j =>
    rw [Ochr.endLoansOfTopTemp.eq_1] at h
    unfold topIdx at h
    peel h
    cases e : (st.env[st.env.size - 1]!).temps.back? with
    | none => rw [e] at h; peel h; exact (runs_pure_inv h).2
    | some v =>
      rw [e] at h
      peel h
      rw [liveLoansIn_nil (hv v e)] at h
      peel h
      exact (runs_pure_inv h).2

theorem runs_dropValue_inert {n : Nat} {v : Value} {T : Option Value} {st st' : MState} {b : Nat}
    (hb : ∀ l, v.holdsBorrow l = false) (hl : v.loans = []) (h : Runs (Ochr.dropValue n v T) st b () st') :
    st' = st := by
  cases n with
  | zero => unfold Ochr.dropValue at h; simp only [runs_exhausted_iff] at h
  | succ k =>
    unfold Ochr.dropValue at h
    obtain ⟨_, s₁, b₁, hp, h⟩ := Runs.bind_inv h
    have := runs_pushTemp_inv hp; subst this
    simp only [] at h
    split at h
    · obtain ⟨_, _, _, he, _⟩ := Runs.bind_inv h; simp only [runs_err_iff] at he
    · have hbor : ¬ ∃ l w, v = .borrow l w := fun ⟨l, w, e⟩ => by
        have := hb l; rw [e] at this; simp [Value.holdsBorrow] at this
      split at h
      · exact absurd ⟨_, _, rfl⟩ hbor
      · obtain ⟨_, s₂, b₂, hel, h⟩ := Runs.bind_inv h
        have hs₂ := runs_endLoansOfTopTemp_noop (fun v' hv' => by rw [topTemp_withTempT hv']; exact hl) hel
        subst hs₂
        have h' : Runs ((fun _ => ()) <$> popTemp) (st.withTempT v T) b₂ () st' := h
        obtain ⟨pv, hpop, -⟩ := Runs.map_inv h'
        obtain ⟨-, rfl⟩ := runs_popTemp_inv hpop
        show { st.withTempT v T with env := Env.popTempE (Env.pushTempTyE st.env v T) } = st
        rw [popTempE_pushTempTyE]
        rfl

theorem grows_dropValue (n : Nat) (v : Value) (T : Option Value) : GrowsM (Ochr.dropValue n v T) :=
  growsM_of_growsIn fun _ => (machineGrows n).dropValue v T

/-- **`SeqInv` in the provable form** (machine3, 2026-11-21; reported to the lead): as `Form.SeqInv`,
with the mode kept from `u`'s end to `w`'s start (`ModeEq st₁ stW`) under the same antecedent as the
kernel (a first value holding no borrow and no loan, whose drop is a push and a pop). Unconditional it
asks the drop of an arbitrary value (the ending machinery: `endBorrow`, `endTopLoan`, which reach
`eval`, which resets `headEval`) to keep the mode: a whole-machine fact. -/
def SeqInvR : Prop :=
  ∀ (n : Nat) (u w : Term) (hint : Option Value) (st st' : MState) (bh : Nat) (v : Value) (T? : Option Value)
    (D : Decisions),
    Form.Mode st → st.tailNext = false → st.tailDecl = none → DecTab D st' →
    Runs (Ochr.evalCore (n + 1) true (.seq u w) hint) st bh (v, T?) st' →
    ∃ (st₀ st₁ stW : MState) (v₀ : Value) (T₀ : Option Value) (bh₁ bh₂ : Nat),
      Form.Kern st st₀ ∧ Form.Mode st₀ ∧ st₀.tailNext = false ∧ st₀.tailDecl = none ∧
      (stW.tailDecl = none ∨ stW.tailDecl = st.curDecl) ∧ Runs (Ochr.eval n true u none) st₀ bh₁ (v₀, T₀) st₁ ∧
      DecTab D st₁ ∧ ((∀ l, v₀.holdsBorrow l = false) → v₀.loans = [] → Form.Kern st₁ stW ∧ Form.ModeEq st₁ stW) ∧
      stW.tailNext = st.curTail ∧
      Runs (Ochr.eval n true w none) stW bh₂ (v, T?) st'

theorem seqInvR : SeqInvR := by
  intro n u w hint st st' bh v T? D hm htn htd hD h
  unfold Ochr.evalCore at h
  obtain ⟨b₁, h⟩ := Runs.tick_bind h
  obtain ⟨want, s₁, b₂, hw, h⟩ := Runs.bind_inv (runs_get_bind.mp h)
  obtain ⟨hw1, hw2⟩ := runs_wanted_inv hw
  subst hw1 hw2
  simp only [Term.placeOperand?] at h
  rw [runs_get_bind] at h
  obtain ⟨⟨v₀, T₀⟩, s₃, b₃, hu, h₁⟩ := Runs.bind_inv h
  clear h
  obtain ⟨_, s₄, b₄, hdv, h₂⟩ := Runs.bind_inv h₁
  clear h₁
  unfold demand at h₂
  peel h₂
  simp only [Bool.true_or, if_true] at h₂
  simp only at hdv
  refine ⟨_, s₃, { s₄ with tailDecl := _, tailNext := _, wantTy := _ }, v₀, T₀, _, b₄, Form.Kern.rfl' _, hm, htn, htd,
    .inr rfl, hu, ?_, fun hb hl => ?_, rfl, h₂⟩
  · exact DecTab.back hD ((Runs.grows (grows_dropValue _ _ _) hdv).trans
      ((TablesGrow.of_fields (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)).trans (Runs.grows (grows_eval _ _ _ _) h₂)))
  · have := runs_dropValue_inert hb hl hdv
    subst this
    exact ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl⟩⟩

end Ochr.Meaning.Steps.Machine

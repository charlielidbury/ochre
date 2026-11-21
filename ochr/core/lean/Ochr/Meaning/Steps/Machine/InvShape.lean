import Ochr.Meaning.Steps.Machine.BorrowInv

/-!
# The checker's invariant along the columns' state changes (state-level; the orchestrator's ruling)

`InvCore` (the invariant kept by every run of `evalCore` on the column's terms) is DROPPED (ruled
2026-11-21): it quantified over states and paths no step uses. The invariant `Inv` is carried by
state-level lemmas `Inv D Γ st.norm → Inv D Γ st'.norm`, one per kernel shape an inversion fact
concludes. Here: `Inv` under `Kern` (free: `Kern a b` is `a.norm = b.norm`), and the comparison's
small fact the column needs (`conv` on `==`-equal values is the identity, so the type check of a
value at its expected type changes nothing). The other shapes (a number binding set to `⊥`, a binding
pushed at `Nat` holding a number, the top binding popped, a number temporary pushed,
`setAtE (.succ v₀)`; the borrow column's five in `OPEN.md`) are stated by the lead; NOTE for whoever
proves them: `ShapeFacts.fits` reads `D.placeDecl` at the state's TOP READINGS, so a push or a pop of
a binding changes the scope it is read in and needs the table aligned at the new state (`DecTab`,
`decTab_placeDecl_at`), and the setting of a number where a place is read `.ind n _` violates `fits`
(a number does not `fitsInd`): state those lemmas with the place's reading as a hypothesis.

The general comparison fact (every run keeps `absTy.size = nextAbs`, WF6's equation, through a
private computation's exit) is a whole-machine induction of `machineGrows`' size: scheduled only when
a step needs a comparison on values that are not `==`.
-/

namespace Ochr.Meaning.Steps.Machine

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.DecideScope Ochr.Meaning.Steps.Slice
open Ochr.Meaning.Steps.Form

theorem inv_of_kern {D : Decisions} {Γ : List IndDecl} {a b : MState} (h : Kern a b) (hi : Inv D Γ a.norm) :
    Inv D Γ b.norm := h.norm ▸ hi

theorem restoreNames_self (st : MState) :
    { st with nextAbs := st.nextAbs, nextLoan := st.nextLoan, nextRecUid := st.nextRecUid, absTy := st.absTy ++ st.absTy.extract st.absTy.size st.absTy.size, absDecl := st.absDecl } = st := by
  simp

theorem runs_conv_of_beq {n : Nat} {v w : Value} (hv : (v == w) = true) {st st' : MState} {b : Nat} {r : Bool}
    (h : Runs (Ochr.conv n v w) st b r st') : r = true ∧ st' = st := by
  cases n with
  | zero => unfold Ochr.conv at h; simp only [runs_exhausted_iff] at h
  | succ k =>
    rw [Ochr.conv.eq_1] at h
    obtain ⟨r', s₁, b₁, h₁, h₂⟩ := Runs.bind_inv (runs_get_bind.mp h)
    clear h
    replace h₁ := Runs.onFail_inv h₁
    rw [if_pos hv] at h₁
    obtain ⟨rfl, rfl⟩ := runs_pure_inv h₁
    unfold restoreNames at h₂
    rw [runs_modify_bind] at h₂
    obtain ⟨rfl, rfl⟩ := runs_pure_inv h₂
    exact ⟨rfl, restoreNames_self _⟩

/-- **The type check of a value already at the expected type changes nothing** (the column's `S(u)`
with `u : Nat`: `expectTy … (some .tNat) .tNat`, `(.tNat == .tNat) = true` by `rfl`). -/
theorem runs_expectTy_of_beq {n : Nat} {w : String} {T A : Value} (hv : (T == A) = true) {st st' : MState} {b : Nat}
    (h : Runs (Ochr.expectTy n w (some T) A) st b () st') : st' = st := by
  cases n with
  | zero => unfold Ochr.expectTy at h; simp only [runs_exhausted_iff] at h
  | succ k =>
    unfold Ochr.expectTy at h
    peel h
    obtain ⟨c, s₁, b₁, hc, h₂⟩ := Runs.bind_inv h
    obtain ⟨rfl, rfl⟩ := runs_conv_of_beq hv hc
    simp only [Bool.not_true, Bool.false_eq_true, if_false] at h₂
    exact (runs_pure_inv h₂).2

end Ochr.Meaning.Steps.Machine

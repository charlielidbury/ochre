import Ochr.Meaning.Mono

/-!
# D14's holder invariant, and the missing half of (WF6)

* `DropHolderCounterexample`: D14's "every live label has exactly one holder, from creation to
  its end" is not kept by `run`'s `.letIn` clause. Its [Drop] ends `T.label`, the label of the
  bound *type*; when the body re-pointed the binding (`x := &b` at a root makes `x` the holder of
  `b`'s label, D13), the label `x` holds at the drop is a different one, which is not ended, and
  `dropLast` removes the position without clearing its shape entry. The label then has no live
  holder although nothing fixed its final content, and the next `pushBind` at that position
  resurrects it as a holder of a borrow it never made.
* `WF6Borrow`, `shapeBelow_sstate`: the clause (WF6) lacks, every borrow's own label below the
  counter, and `ShapeBelow` of the checker's state from it.
-/

namespace Ochr.Meaning

open Classical

namespace DropHolderCounterexample

/-- The state just before `let x = &a; x := &b; ()` drops `x`: `x` (position `bind 0 0`) holds
`b`'s label `1`; the bound type's label is `a`'s label `0`, already ended by the assignment. -/
def s₀ : SState :=
  { env := [{ binds := [{ ty := .plain .err, val := fun _ => .el0 Nat 5 }] }],
    shape := fun p => if p = .bind 0 0 then some 1 else none, nextLoan := 2 }

theorem positions_s₀ : s₀.positions = [.bind 0 0] := by
  simp [SState.positions, s₀, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]

/-- The `.letIn` drop: end the type's label `0`, then `dropLast`. -/
noncomputable def dropped : SState := (s₀.endLabel 0).dropLast

theorem endLabel_s₀ : s₀.endLabel 0 = s₀ :=
  SState.endLabel_of_find_none s₀ 0 (by rw [positions_s₀]; rfl)

theorem positions_dropped : dropped.positions = [] := by
  rw [dropped, endLabel_s₀]
  simp [SState.dropLast, SState.positions, s₀, SState.topIdx,
    Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]

/-- **Label `1` leaves the live set without being ended** (nothing fixed `b`'s final content),
and **a fresh binding at the same position resurrects it**: the new binding holds `1`, a borrow it
never made. So "every live label has exactly one holder, from creation to its end" fails across
`.letIn`. Fix: end the label the position holds at the drop (`s.shape pos`), not `T.label`, and
clear the shape entry of every position `dropLast`/`popFrame` removes. -/
theorem dropped_resurrects (b : SBinding) :
    1 ∉ dropped.liveLabels ∧ 1 ∈ (dropped.pushBind b).liveLabels := by
  refine ⟨fun h => ?_, ?_⟩
  · obtain ⟨p, hp, _⟩ := (SState.mem_liveLabels _ _).mp h
    rw [positions_dropped] at hp
    cases hp
  · refine (SState.mem_liveLabels _ _).mpr ⟨.bind 0 0, ?_, by rw [dropped, endLabel_s₀]; rfl⟩
    have : (dropped.pushBind b).positions = [.bind 0 0] := by
      rw [dropped, endLabel_s₀]
      simp [SState.dropLast, SState.pushBind, SState.positions, s₀,
        SState.topIdx, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
    rw [this]; simp

end DropHolderCounterexample

/-- The half of (WF6) it lacks: every borrow's own label is below the label counter. (WF6 bounds
`Value.loans`, and `Value.loans (.borrow _ w) = w.loans` omits the borrow's label.) Stated at every
position; at a non-position `valAt` reads the default value, which is not a borrow. -/
def WF6Borrow (st : MState) : Prop := ∀ p l w, valAt st.env p = .borrow l w → l < st.nextLoan

/-- With the missing clause, the checker's state read as a semantic state has every held label
below its counter (milestone 3: the base case of `ShapeBelow` for the step lemmas, from `Good`). -/
theorem shapeBelow_sstate (dm : DataModel) (C : CodeMeaning) (Γ : List IndDecl) (ρ : Assignment)
    (st : MState) (h : WF6Borrow st) : (st.sstate dm C Γ ρ).ShapeBelow := by
  intro p l hp
  change Env.shape st.env p = some l at hp
  show l < st.nextLoan
  unfold Env.shape at hp
  split at hp
  · rename_i l' w hv
    cases hp; exact h p _ w hv
  · cases hp

end Ochr.Meaning

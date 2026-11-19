import Ochr.Meaning.Steps.BotWriteRel

/-!
# The checker's drop of one place, taken apart (for `dropOne_step`'s assembly)

Inversions of the runs `dropOne_step` meets: `content?` (a read of the place, changing nothing),
`movedPlace` where the place exists (it returns it, changing nothing), and `dropAtJoin`'s cases.
-/

namespace Ochr.Meaning.Steps

open Ochr.Meaning

theorem runs_getAt_inv {pos : Pos} {st st' : MState} {b : Nat} {v : Value}
    (h : Runs (Ochr.getAt pos) st b v st') : st' = st ∧ v = valAt st.env pos := by
  obtain ⟨L, left, log, h⟩ := h
  cases pos <;> simp only [Ochr.getAt, runMachineL_bind, runMachineL_get, runMachineL_pure, Prod.mk.injEq,
    Outcome.ok.injEq] at h <;> exact ⟨h.1.2.symm, by rw [← h.1.1]; rfl⟩

/-- `content?` reads the place and changes nothing. -/
theorem runs_content?_inv {q : Place} {st st' : MState} {b : Nat} {o : Option Value}
    (h : Runs (Ochr.content? q) st b o st') :
    st' = st ∧ ∃ pos, ckVarPos st.env q.steps.1 = some pos ∧ o = (valAt st.env pos).follow q.steps.2 := by
  unfold Ochr.content? at h
  rcases hq : q.steps with ⟨i, ss⟩
  rw [hq] at h
  obtain ⟨pos, st₁, b₁, hv, h2⟩ := Runs.bind_inv h
  obtain ⟨hst₁, hpos⟩ := runs_varPos_inv hv
  subst hst₁
  obtain ⟨v, st₂, b₂, hg, h3⟩ := Runs.bind_inv h2
  obtain ⟨hst₂, hvv⟩ := runs_getAt_inv hg
  subst hst₂; subst hvv
  obtain ⟨L, left, log, h4⟩ := h3
  simp only [runMachineL_pure, Prod.mk.injEq, Outcome.ok.injEq] at h4
  exact ⟨h4.1.2.symm, pos, hpos, h4.1.1.symm⟩

/-- **The place exists: `movedPlace` returns it and changes nothing.** -/
theorem movedPlace_exists' (fuel : Nat) {st st₁ : MState} {q q' : Place} {pos : Pos} {w : Value} {b : Nat}
    (hpos : ckVarPos st.env q.steps.1 = some pos) (hw : (valAt st.env pos).follow q.steps.2 = some w)
    (h : Runs (Ochr.movedPlace (fuel + 1) q) st b q' st₁) : q' = q ∧ st₁ = st := by
  unfold Ochr.movedPlace at h
  obtain ⟨o, st₂, b₂, hc, h⟩ := Runs.bind_inv h
  obtain ⟨rfl, pos', hpos', rfl⟩ := runs_content?_inv hc
  rw [hpos] at hpos'
  cases hpos'
  rw [hw] at h
  obtain ⟨L, left, log, h⟩ := h
  simp only [Option.isSome_some, ↓reduceIte, runMachineL_pure, Prod.mk.injEq, Outcome.ok.injEq] at h
  exact ⟨h.1.1.symm, h.1.2.symm⟩

end Ochr.Meaning.Steps

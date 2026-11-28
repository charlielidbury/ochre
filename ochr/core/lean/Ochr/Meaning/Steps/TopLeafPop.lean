import Ochr.Meaning.Steps.TopLeafConv
import Ochr.Meaning.Steps.Machine.StepInv

/-!
# The goal read after the pop is the leaf's: `LeafGoalPopG` from two facts about two machine functions (lead48; docs/31 D293)

`Top.Leaf.LeafGoalPopG`, the one fact of the leaf about the checker alone, inverted along `fixCont`: [Return]'s first
check (`wholeReturned`, which tests and writes nothing), [Return]'s repack (`bodyReturns`), the result parked as a
temporary (`pushTempAt`, which writes the frame), the frame's pop (`popFrame`), the temporary taken back (`popTemp`), the
goal read, the trace, and the comparison. PROVED from two facts about the two machine functions that reach far:
`bodyReturns` and `popFrame` keep the goal (`BodyReturnsKeepsGoal`, `PopFrameKeepsGoal`; CHECKER, read true: they reach
substitution with `types := false`, the re-run of sealed programs, `nfSealed`, which restores the goal, conversion, which
restores the state but for names, and field-type evaluation, the conversion lane's `FieldTysKept`). Each is a statement in
the machine lane's form (`KeepsTab`'s), to be proved over the mutual block as `MachineGrows` is.
-/

namespace Ochr.Meaning.Steps.Form.Top.Leaf

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.Steps.Form Ochr.Meaning.Steps.Machine

/-- **[Return]'s repack keeps the goal** (CHECKER; READ TRUE; at no lent place, as `fixCont` calls it). -/
def BodyReturnsKeepsGoal : Prop :=
  ∀ (n : Nat) (w : String) (v T : Value) (st : MState) (b : Nat) (st' : MState),
    Runs (Ochr.bodyReturns n w v T [] "") st b () st' → st'.goal = st.goal

/-- **The frame's pop keeps the goal** (CHECKER; READ TRUE). -/
def PopFrameKeepsGoal : Prop :=
  ∀ (n : Nat) (st : MState) (b : Nat) (st' : MState), Runs (Ochr.popFrame n) st b () st' → st'.goal = st.goal

theorem runs_wholeReturned_inv {v : Value} {st st' : MState} {b : Nat} {u : PUnit}
    (h : Runs (Ochr.wholeReturned v) st b u st') : st' = st := by
  unfold Ochr.wholeReturned at h
  split at h
  · split at h
    · simp only [runs_err_iff] at h
    · exact (runs_pure_inv h).2
  · exact (runs_pure_inv h).2

theorem runs_pushTempAt_goal {f : Nat} {v : Value} {T : Option Value} {site : String} {st st' : MState} {b : Nat}
    {u : PUnit} (h : Runs (pushTempAt f v T site) st b u st') : st'.goal = st.goal := by
  unfold pushTempAt notePush at h
  peel h
  split at h <;> peel h <;> (unfold modifyFrame at h; peel h; rw [(runs_pure_inv h).2])

/-- **`LeafGoalPopG` from the two facts** (PROVED: `fixCont` inverted step by step). -/
theorem leafGoalPopG_of (hb : BodyReturnsKeepsGoal) (hp : PopFrameKeepsGoal) : LeafGoalPopG := by
  intro n name v T stl stk bk h
  unfold fixCont at h
  obtain ⟨_, s₁, b₁, h₁, h⟩ := Runs.bind_inv h
  obtain ⟨_, s₂, b₂, h₂, h⟩ := Runs.bind_inv h
  obtain ⟨i, s₃, b₃, h₃, h⟩ := Runs.bind_inv h
  obtain ⟨_, s₄, b₄, h₄, h⟩ := Runs.bind_inv h
  obtain ⟨_, s₅, b₅, h₅, h⟩ := Runs.bind_inv h
  obtain ⟨_, s₆, b₆, h₆, h⟩ := Runs.bind_inv h
  -- the goal read is the leaf's
  have e₁ : s₁ = stl := runs_wholeReturned_inv h₁
  have e₂ : s₂.goal = s₁.goal := hb _ _ _ _ _ _ _ h₂
  have e₃ : s₃ = s₂ := (runs_topIdx_inv h₃).2
  have e₄ : s₄.goal = s₃.goal := runs_pushTempAt_goal h₄
  have e₅ : s₅.goal = s₄.goal := hp _ _ _ _ h₅
  have e₆ : s₆.goal = s₅.goal := by
    obtain ⟨u, hu, -⟩ := Runs.map_inv h₆
    rw [(runs_popTemp_inv hu).2]
  have hg : s₆.goal = stl.goal := by rw [e₆, e₅, e₄, e₃, e₂, e₁]
  -- the read, the trace, the comparison
  rw [runs_get_bind] at h
  obtain ⟨_, s₇, b₇, h₇, h⟩ := Runs.bind_inv h
  have e₇ : s₇ = s₆ := runs_trace_inv h₇
  obtain ⟨c, s₈, b₈, h₈, h⟩ := Runs.bind_inv h
  cases c with
  | true => rw [e₇, hg] at h₈; exact ⟨_, _, _, h₈⟩
  | false => simp only [Bool.false_eq_true, if_false, runs_err_iff] at h

end Ochr.Meaning.Steps.Form.Top.Leaf

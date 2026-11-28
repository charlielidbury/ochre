import Ochr.Meaning.Steps.TopLeafConv
import Ochr.Meaning.Steps.Machine.StepInv

/-!
# The goal read after the pop is the leaf's: `LeafGoalPopG` from two facts about two machine functions (lead48; docs/31 D293)

`Top.Leaf.LeafGoalPopG`, the one fact of the leaf about the checker alone, inverted along `fixCont`: [Return]'s first
check (`wholeReturned`, which tests and writes nothing), [Return]'s repack (`bodyReturns`), the result parked as a
temporary, the frame's pop and the temporary taken back (`popBody` since main's D142: for an erased function the start's
environment put back first, which writes the environment only), the goal read, the trace, and the comparison. PROVED from two facts about the two machine functions that reach far:
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

/-- **`popBody` keeps the goal** (from `PopFrameKeepsGoal`; main's D142): putting back an erased body's start
environment writes the environment only, then the pop as before. -/
theorem runs_popBody_goal (hp : PopFrameKeepsGoal) {n : Nat} {start : Option Env} {v : Value} {T : Option Value}
    {site : String} {st st' : MState} {b : Nat} {r : Value} (h : Runs (Ochr.popBody n start v T site) st b r st') :
    st'.goal = st.goal := by
  unfold Ochr.popBody at h
  rcases n with _ | n
  · simp only [runs_exhausted_iff] at h
  cases start with
  | none =>
    dsimp only at h
    have e₀ : st.goal = st.goal := rfl
    generalize st = s₀ at e₀ h ⊢
    obtain ⟨i, s₁, b₁, h₁, h⟩ := Runs.bind_inv h
    obtain ⟨_, s₂, b₂, h₂, h⟩ := Runs.bind_inv h
    obtain ⟨_, s₃, b₃, h₃, h⟩ := Runs.bind_inv h
    have e₁ : s₁ = s₀ := (runs_topIdx_inv h₁).2
    have e₂ : s₂.goal = s₁.goal := runs_pushTempAt_goal h₂
    have e₃ : s₃.goal = s₂.goal := hp _ _ _ _ h₃
    rw [(runs_popTemp_inv h).2, e₃, e₂, e₁]
  | some e =>
    dsimp only at h
    obtain ⟨_, s₀, b₀, h₀, h⟩ := Runs.bind_inv h
    have e₀ : s₀.goal = st.goal := by have := runs_modify_inv h₀; subst this; rfl
    obtain ⟨i, s₁, b₁, h₁, h⟩ := Runs.bind_inv h
    obtain ⟨_, s₂, b₂, h₂, h⟩ := Runs.bind_inv h
    obtain ⟨_, s₃, b₃, h₃, h⟩ := Runs.bind_inv h
    have e₁ : s₁ = s₀ := (runs_topIdx_inv h₁).2
    have e₂ : s₂.goal = s₁.goal := runs_pushTempAt_goal h₂
    have e₃ : s₃.goal = s₂.goal := hp _ _ _ _ h₃
    rw [(runs_popTemp_inv h).2, e₃, e₂, e₁, e₀]

/-- **`LeafGoalPopG` from the two facts** (PROVED: `fixCont` inverted step by step; since main's D142 the pop is
`popBody`, which keeps the goal at every `start`). -/
theorem leafGoalPopG_of (hb : BodyReturnsKeepsGoal) (hp : PopFrameKeepsGoal) : LeafGoalPopG := by
  intro n name start v T stl stk bk h
  unfold fixCont at h
  obtain ⟨_, s₁, b₁, h₁, h⟩ := Runs.bind_inv h
  obtain ⟨_, s₂, b₂, h₂, h⟩ := Runs.bind_inv h
  obtain ⟨_, s₆, b₆, h₆, h⟩ := Runs.bind_inv h
  -- the goal read is the leaf's
  have e₁ : s₁ = stl := runs_wholeReturned_inv h₁
  have e₂ : s₂.goal = s₁.goal := hb _ _ _ _ _ _ _ h₂
  have e₆ : s₆.goal = s₂.goal := by
    obtain ⟨u, hu, -⟩ := Runs.map_inv h₆
    exact runs_popBody_goal hp hu
  have hg : s₆.goal = stl.goal := by rw [e₆, e₂, e₁]
  -- the read, the trace, the comparison
  rw [runs_get_bind] at h
  obtain ⟨_, s₇, b₇, h₇, h⟩ := Runs.bind_inv h
  have e₇ : s₇ = s₆ := runs_trace_inv h₇
  obtain ⟨c, s₈, b₈, h₈, h⟩ := Runs.bind_inv h
  cases c with
  | true => rw [e₇, hg] at h₈; exact ⟨_, _, _, h₈⟩
  | false => simp only [Bool.false_eq_true, if_false, runs_err_iff] at h

end Ochr.Meaning.Steps.Form.Top.Leaf

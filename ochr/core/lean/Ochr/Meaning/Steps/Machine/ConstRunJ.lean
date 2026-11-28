import Ochr.Meaning.Steps.Machine.CallJEval

/-!
# `ConstRunJ`, proved (machine8)

`checkDef defJ` from the state holding only `I`'s global: the name is new, the type mentions no own
name, `&` sits nowhere, the declared readings (`declOf`) and D118's `undeclaredCheck` read the state and
write nothing, and the constant branch sets one empty frame, no goal, no [Rec] context, no refinement,
evaluates the goal `Nat` (a statement on a private copy: the state as it was but for the [Rec]
records) and then runs the body's typed `eval` at the goal `Nat`, from a state with `stJ`'s kernel in
the plain mode, not in tail position, no reading handed down, outside any private copy.
-/

namespace Ochr.Meaning.Steps.Machine

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.DecideScope Ochr.Meaning.Steps.Slice
open Ochr.Meaning.Steps.Form

theorem keep_declared (n : String) : Keep (declared n) := by unfold declared; keep_go

theorem keep_fuelLeft : Keep fuelLeft := by unfold fuelLeft; keep_go; all_goals exact keep_getThe_fuel

theorem keep_undeclaredCheck (self : Option String) (ts : List Term) (own : Option String := none) :
    Keep (undeclaredCheck self ts own) := by
  unfold undeclaredCheck; keep_go
  all_goals (intro s f l a s' f' l' h; cases h)

set_option maxHeartbeats 4000000 in
/-- **`ConstRunJ`, proved**: `checkDef`'s acceptance of the constant `J` ran the body's typed `eval` at
the goal `Nat` from a state with `stJ`'s kernel, in the plain mode, not in tail position, no reading
handed down, outside any private copy. -/
theorem constRunJ : ColumnJ.ConstRunJ := by
  intro fuel st₁ h
  unfold checkDef at h
  obtain ⟨dcl, s₁, b₁, hd, h₁⟩ := Runs.bind_inv h
  clear h
  have := runs_keep (keep_declared _) hd; subst this
  dsimp only at h₁
  have e1 : ((CallGuards.defJ.cod :: CallGuards.defJ.doms).any (Term.mentionsConst CallGuards.defJ.name)) = false := by
    rfl
  have e2 : (!((CallGuards.defJ.cod :: CallGuards.defJ.doms).all Term.refTopOk && CallGuards.defJ.body.refsOk)) = false := by
    rfl
  by_cases hd1 : dcl = true
  · simp only [hd1, if_true] at h₁
    exact absurd h₁ (fun h => by obtain ⟨_, _, _, he, _⟩ := Runs.bind_inv h; exact runs_err_false he)
  simp only [hd1, e1, e2, Bool.false_eq_true, if_false] at h₁
  obtain ⟨fl, s₂, b₂, hfl, h₂⟩ := Runs.bind_inv h₁
  clear h₁
  have := runs_keep keep_fuelLeft hfl; subst this
  obtain ⟨_, s₃, b₃, hdo, h₃⟩ := Runs.bind_inv h₂
  clear h₂
  have := runs_keep (keep_discard ((decideKeep _).2.2.2.2.2.2.2.2.1 _ _ _ _)) hdo; subst this
  obtain ⟨_, s₄, b₄, hu, h₄⟩ := Runs.bind_inv h₃
  clear h₃
  have := runs_keep (keep_undeclaredCheck _ _) hu; subst this
  simp only [CallGuards.defJ, List.isEmpty_nil, if_true] at h₄
  peel h₄
  obtain ⟨fl2, s₅, b₅, hfl2, h₅⟩ := Runs.bind_inv h₄
  clear h₄
  have := runs_keep keep_fuelLeft hfl2; subst this
  obtain ⟨g, s₆, b₆, hg, h₆⟩ := Runs.bind_inv h₅
  clear h₅
  obtain ⟨rfl, nr, rfl⟩ := runs_evalType_nat_nil hg rfl rfl rfl
  obtain ⟨fl3, s₇, b₇, hfl3, h₇⟩ := Runs.bind_inv h₆
  clear h₆
  have := runs_keep keep_fuelLeft hfl3; subst this
  obtain ⟨⟨v, T⟩, s₈, b₈, hev, -⟩ := Runs.bind_inv h₇
  refine ⟨_, _, _, _, v, T, ?_, ?_, ?_, ?_, ?_, hev⟩
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · exact ⟨rfl, rfl, rfl, rfl⟩
  all_goals rfl

end Ochr.Meaning.Steps.Machine

import Ochr.Meaning.Steps.IH

/-!
# Step lemmas, calls: `callFn`, `runBody`, `closeCall`, `callType`, `recCheck` (milestone 3)

A call in the checker runs the callee's body (`runBody`) or, when the body is stuck, closes off
(`closeCall`, three rows). The reference run applies the callee's meaning (`callOf`). So:
* a direct call is *below* the reference (the body's run is below the function's meaning, by the
  induction hypothesis on the body: docs/18 "a call of a closure, run directly");
* closing off is *exact*: a sealed program means its run, which is the reference's call
  (docs/18 (C1)–(C9)); the row for `&T` is `callOf`'s `.ref` case; η at `Unit` is membership
  (`⟦f⟧(ā) ∈ ⟦Unit⟧`, the one-element set);
* `callType`/`declCallType` compute the codomain at the arguments, the reference's `TyS` of the
  result;
* `recCheck`'s accepting direction is the stabilisation of the stages (the semantic [Rec]).
-/

namespace Ochr.Meaning.Steps

open Ochr.Meaning

section
variable (K : RunCtx) (ρ : Assignment) (φ : Future)

/-- A direct call (`callFn`, untyped or typed): below the reference's `callOf` on the callee's
meaning, and `Good` kept. The arguments are loan-free (WF5, `ArgsLoanFree`). -/
theorem callFn_step (fuel : Nat) (ih : ∀ ρ φ, StepsIH K ρ φ fuel) : callFn_step_stmt K ρ φ (fuel + 1) := by
  sorry

/-- Running a body (`runBody`): the frame pushed with the captures and parameters, the body run,
the frame popped: below the function's meaning applied (the induction hypothesis on the body). -/
theorem runBody_step (fuel : Nat) (ih : ∀ ρ φ, StepsIH K ρ φ fuel) : runBody_step_stmt K ρ φ (fuel + 1) := by
  sorry

/-- [Close] (`closeCall`), every row: exact against `callOf`. The result is a sealed program (or
`()` at a declared `Unit`, or a borrow of one), and each lent place a fill: both mean what the
reference's call gives them, since a sealed program means its run. -/
theorem closeCall_step (fuel : Nat) (ih : ∀ ρ φ, StepsIH K ρ φ fuel) : closeCall_step_stmt K ρ φ (fuel + 1) := by
  sorry

/-- [Call-type] (`callType`, `declCallType`): the codomain at the arguments is the reference's
result type. -/
theorem callType_step (fuel : Nat) (ih : ∀ ρ φ, StepsIH K ρ φ fuel) : callType_step_stmt K ρ φ (fuel + 1) := by
  sorry

/-- [Rec]'s accepting direction (`recCheck`), semantically: for a recursive function whose every
recursive call passes a strict subterm of the entry value, the stages of the `fix` clause
stabilise, so the closure's meaning is not `err` and the guard never fires (docs/24 §4, the
semantic form of [Rec]; `Slice.stage_stable` generalised). Stated on the closure value: its
meaning is a member of its Π-type. -/
theorem recCheck_sound (fuel : Nat) (ih : ∀ ρ φ, StepsIH K ρ φ fuel) : recCheck_sound_stmt K ρ φ (fuel + 1) := by
  sorry

end

end Ochr.Meaning.Steps

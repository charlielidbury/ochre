import Ochr.Meaning.Steps.IH

/-!
# Step lemmas, types: `evalType`, `piSort`, `capture`, `evalTInd`, `evalCtor`, `fieldTypes`,
`repackCheck`, `lentUnknown`, `valType?` (milestone 3; docs/18 "Five lemmas behind same")

Types are formed by running code on private copies, so `evalType` is the run of the type term
with the state unchanged. `piSort` must agree with `Decisions.piSort` (aligned, D55). `capture`
rewrites a closure's term so that its free places become capture slots: running the rewritten
body with the captures bound means running the original in the forming frame (the `.fix`
clause reads the original). Constructor values and `D(ā)` are the run's `.ctor`/`.tind`
clauses; `fieldTypesOf`/`fieldTypeAt` compute `DataModel.fieldTy`. The wholeness checks
(`repackCheck`, `repackAt`, `bodyReturns`, `lentUnknown`) are checks: their accepting direction
establishes membership of the checked value under every future of the holes still lent from it
(D73, docs/25 case 1). `valType?` soundness is the second of the five lemmas: the meaning of a
value lies in the meaning of the type the checker reads off it.
-/

namespace Ochr.Meaning.Steps

open Ochr.Meaning

section
variable (K : RunCtx) (ρ : Assignment) (φ : Future)

/-- `evalType` (a type term, on a private copy): the result means the run's result, and the
state's core is unchanged. -/
theorem evalType_step (fuel : Nat) (ih : StepsIH K ρ φ fuel) : evalType_step_stmt K ρ φ (fuel + 1) := by
  sorry

/-- `piSort` agrees with the aligned decision (D55: a type's declared sort is its computed sort). -/
theorem piSort_aligned (fuel : Nat) (ih : StepsIH K ρ φ fuel) : piSort_aligned_stmt K ρ φ (fuel + 1) := by
  sorry

/-- `capture`: the closure value the checker forms (captures by value, the term rewritten to read
them as slots) means what the run's `.fix` clause gives the original term in the forming state. -/
theorem capture_step (fuel : Nat) (ih : StepsIH K ρ φ fuel) : capture_step_stmt K ρ φ (fuel + 1) := by
  sorry

/-- `evalCtor` (a constructor value, its parameters written or inferred): the run's `.ctor`
clause at the hint the context gives. -/
theorem evalCtor_step (fuel : Nat) (ih : StepsIH K ρ φ fuel) : evalCtor_step_stmt K ρ φ (fuel + 1) := by
  sorry

/-- `evalTInd`: `D(ā)` means the run's `.tind` clause. -/
theorem evalTInd_step (fuel : Nat) (ih : StepsIH K ρ φ fuel) : evalTInd_step_stmt K ρ φ (fuel + 1) := by
  sorry

/-- `fieldTypesOf`: the checker's field types at parameters and fields mean `DataModel.fieldTy`
at their meanings (the telescope, D64). -/
theorem fieldTypesOf_step (fuel : Nat) (ih : StepsIH K ρ φ fuel) : fieldTypesOf_step_stmt K ρ φ (fuel + 1) := by
  sorry

/-- [Repack]'s accepting direction (`repackCheck`): a value checked whole against `T`, with each
part still lent read as an unknown of its type (D73), is a member of `T` under every typed
future. -/
theorem repackCheck_sound (fuel : Nat) (ih : StepsIH K ρ φ fuel) : repackCheck_sound_stmt K ρ φ (fuel + 1) := by
  sorry

/-- [Return]'s accepting direction (`bodyReturns`): the returned value is a member of its type
and every place held by borrow is whole, under every typed future. -/
theorem bodyReturns_sound (fuel : Nat) (ih : StepsIH K ρ φ fuel) : bodyReturns_sound_stmt K ρ φ (fuel + 1) := by
  sorry

/-- `valType?` is sound (the second of the five lemmas): the meaning of a value lies in the
meaning of the type the checker reads off it. -/
theorem valType_sound (fuel : Nat) (ih : StepsIH K ρ φ fuel) : valType_sound_stmt K ρ φ (fuel + 1) := by
  sorry

end

end Ochr.Meaning.Steps

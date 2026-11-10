import Ochr.Meaning.Steps.IH

/-!
# Step lemmas, matches and worlds: `evalMatch`, `evalMatchInd`, `evalMatchByType`,
`splitThenClose`, `generalizeNeutral`, `closeBlock`, `enterWorld`/`exitWorld` (milestone 3)

A match on a known constructor runs one arm, as the reference run does (`run`'s `.matchNat`/
`.matchInd` clauses, with D84's drop at the join). A match on an unknown `σ` *splits*
([Split]): each arm is checked in its own world under the refinement `σ := Cᵢ(σ̄ᵢ)`; the
reference run does not split, since under an assignment `ρ σ` has one tag. The two meet through
**coverage**: every typed assignment selects exactly one arm and extends to that arm's fresh
field unknowns, and the arm's refinement is then a substitution that changes no meaning
(`Steps/Subst.refine_step`). A match on a sealed program first generalises it to a fresh `σ`
with the record `n := σ`, the path condition `ρ σ = ⟦n⟧` (`TypedAssignment.neutral`). After the
arms, the match is closed off as a stuck block, an anonymous function of its captures, which
means the match (a sealed program means its run, and the run of the block's call is the run of
the match: docs/18 (C9), (K1)–(K3)). Worlds: leaving an arm restores the snapshot except names
and the types of unknowns created inside (X1)–(X4), so the restored state means the snapshot.
-/

namespace Ochr.Meaning.Steps

open Ochr.Meaning

section
variable (K : RunCtx) (ρ : Assignment) (φ : Future)

/-- [Match] on `Nat` with a known constructor (`evalMatch`): below the run's `.matchNat` clause. -/
theorem evalMatch_step (fuel : Nat) (ih : StepsIH K ρ φ fuel) : evalMatch_step_stmt K ρ φ (fuel + 1) := by
  sorry

/-- [Match] on a declared inductive with a known constructor (`evalMatchInd`): below the run's
`.matchInd` clause. -/
theorem evalMatchInd_step (fuel : Nat) (ih : StepsIH K ρ φ fuel) : evalMatchInd_step_stmt K ρ φ (fuel + 1) := by
  sorry

/-- A match on a proof, by its type (`evalMatchByType`, D45): the one arm of a one-constructor
proposition, its proof fields `⋆` and its data fields fresh unknowns; below the run's clause for
a proof scrutinee under an assignment extended at those unknowns by the fields of the proof's
witness (the proposition is inhabited, since the scrutinee is a member of it). -/
theorem evalMatchByType_step (fuel : Nat) (ih : StepsIH K ρ φ fuel) : evalMatchByType_step_stmt K ρ φ (fuel + 1) := by
  sorry

/-- [Split] coverage: at a place whose content is the unknown `σ` of a data type, every typed
assignment selects a constructor `c` (exactly one: distinct constructors mean distinct tags), and extends to the arm's fresh field unknowns
(`ctorRefinement`) so that `σ`'s refinement is satisfied. -/
theorem split_coverage (fuel : Nat) (ih : StepsIH K ρ φ fuel) : split_coverage_stmt K ρ φ (fuel + 1) := by
  sorry

/-- [Split-gen] (`generalizeNeutral`): the sealed program `n` at place `p` becomes a fresh `σ`
with the record `n := σ`; under `ρ` extended at `σ` by `⟦n⟧`, the state means the same and the
assignment is typed (the path condition). -/
theorem generalizeNeutral_step (fuel : Nat) (ih : StepsIH K ρ φ fuel) : generalizeNeutral_step_stmt K ρ φ (fuel + 1) := by
  sorry

/-- A stuck block closed off (`closeBlock`): the block is a call of an anonymous function of its
captures, so its sealed result and fills mean what running the match means: below the run's
match clause (the capture by move of a place the selected arm keeps is D84's join, exact; a
split less fine than the arm's own is an over-approximation). The arms are given as the
match term `mt`; `B?` is the match's annotated type. -/
theorem closeBlock_step (fuel : Nat) (ih : StepsIH K ρ φ fuel) : closeBlock_step_stmt K ρ φ (fuel + 1) := by
  sorry

/-- Worlds (X1)–(X4), `exitWorld`: the restored state means the snapshot (every component but
the name counters and the types of unknowns created inside the arm is the snapshot's), and is
`Good` for any assignment the snapshot was. -/
theorem exitWorld_step (fuel : Nat) (ih : StepsIH K ρ φ fuel) : exitWorld_step_stmt K ρ φ (fuel + 1) := by
  sorry

end

end Ochr.Meaning.Steps

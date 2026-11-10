import Ochr.Meaning.Steps.IH

/-!
# Step lemmas, substitution: `substV`, `substEnv`, `nfSealed`, `canonNeutral`, `renormAll`,
`refine` (milestone 3)

The checker's substitution replaces a loan, an abstract value or a sealed program by a value and
re-normalises every sealed program it changes (`Machine.substV`, through `mapState`). On
meanings these are three facts, each exact:
* filling a loan is fixing the future (`Lemmas.run_substLoan`, the pure half) and a sealed
  program's re-run means what its program means (the run's own `.sealed` clause), so the
  checker's substitution of `loan ℓ := w` reads the state under `φ[ℓ ↦ ⟦w⟧]`;
* a refinement `σ := r` is a substitution that changes no meaning under an assignment with
  `ρ σ = ⟦r⟧` (docs/18 §"For a split, every assignment has an arm"), and generalising a sealed
  program `n` to `σ` with the record `n := σ` is the path condition `ρ σ = ⟦n⟧`
  (`TypedAssignment.neutral`);
* re-normalisation (`nfSealed`, `renormAll`) keeps every meaning: a sealed program means its run.
-/

namespace Ochr.Meaning.Steps

open Ochr.Meaning

section
variable (K : RunCtx) (ρ : Assignment) (φ : Future)

/-- `substV` of a loan: the result means the value read under the future fixed at `ℓ` to the
filling value's meaning (the pure lemma plus re-normalisation). -/
theorem substV_loan_step (fuel : Nat) (ih : StepsIH K ρ φ fuel) : substV_loan_step_stmt K ρ φ (fuel + 1) := by
  sorry

/-- `substV` of an abstract value by a refinement `r` it means: exact. -/
theorem substV_abs_step (fuel : Nat) (ih : StepsIH K ρ φ fuel) : substV_abs_step_stmt K ρ φ (fuel + 1) := by
  sorry

/-- `substEnv` of a loan (the state-wide half of [End] and of [Close]'s fills): every position
reads the fixed future; stored types are untouched (`types = false`: no type holds a loan). -/
theorem substEnv_loan_step (fuel : Nat) (ih : StepsIH K ρ φ fuel) : substEnv_loan_step_stmt K ρ φ (fuel + 1) := by
  sorry

/-- `substEnv` of an abstract value by a refinement it means (`types = true`: stored types, Δ
and the goal are refined too): exact, and `Good` is kept. -/
theorem substEnv_abs_step (fuel : Nat) (ih : StepsIH K ρ φ fuel) : substEnv_abs_step_stmt K ρ φ (fuel + 1) := by
  sorry

/-- [Seal]: a re-run of a sealed program means the sealed program (its run), and changes nothing
of the state's core (it runs on a private copy). -/
theorem nfSealed_step (fuel : Nat) (ih : StepsIH K ρ φ fuel) : nfSealed_step_stmt K ρ φ (fuel + 1) := by
  sorry

/-- `canonNeutral`: a sealed program already generalised in this world is its `σ`, which the
path condition makes mean the same. -/
theorem canonNeutral_step (fuel : Nat) (ih : StepsIH K ρ φ fuel) : canonNeutral_step_stmt K ρ φ (fuel + 1) := by
  sorry

/-- `renormAll`: re-running every sealed program of the state keeps every meaning. -/
theorem renormAll_step (fuel : Nat) (ih : StepsIH K ρ φ fuel) : renormAll_step_stmt K ρ φ (fuel + 1) := by
  sorry

/-- [Split]'s refinement `σ := r` (`refine`): under an assignment that gives `σ` the meaning of
`r` (the arm the assignment selects, with its fields assigned), the substitution is exact and
`Good` is kept; the record in `refs` states no fact. -/
theorem refine_step (fuel : Nat) (ih : StepsIH K ρ φ fuel) : refine_step_stmt K ρ φ (fuel + 1) := by
  sorry

end

end Ochr.Meaning.Steps

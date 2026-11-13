import Ochr.Meaning.Steps.IH

/-!
# Step lemmas, `evalCore` (milestone 3): the run of a term is below the reference run

`evalCore` is the machine's one entry point per term form; the files `Borrow`, `Subst`, `Call`,
`Match`, `Obs`, `Types` state its pieces. This file states the per-form clauses it dispatches to
that are not covered there, and the induction step itself (`evalCore_step`): the checker's run
of a term, at a `Good` state, is below the reference run of the term at the type the context
expects, with the result's meaning below the reference's result, and `Good` is kept for an
assignment extending the given one to the unknowns the run created. This is docs/18 Theorem
14 (a), (b), (c) for one term, and the assembly (milestone 4) applies it along `checkTail`.
-/

namespace Ochr.Meaning.Steps

open Ochr.Meaning

section
variable (K : RunCtx) (ρ : Assignment) (φ : Future)

/-- The induction step. For every `Good` assignment `ρ`, following at each split the arm it
selects, the run of `t` reaches a value below the reference's result, a state below the
reference's, for an assignment `ρ'` extending `ρ` to the unknowns created, and `Good` is kept;
the reference run does not fail. -/
theorem evalCore_step (fuel : Nat) (ih : ∀ ρ φ, StepsIH K ρ φ fuel) : evalCore_step_stmt K ρ φ (fuel + 1) := by
  sorry

/-- The induction step as the checker recurses: `Machine.eval` (`evalAt`: the term classified, an
erased one on a private copy) against the run, which does the same at `Decisions.flags`. -/
theorem eval_step (fuel : Nat) (ih : ∀ ρ φ, StepsIH K ρ φ fuel) : eval_step_stmt K ρ φ (fuel + 1) := by
  sorry

/-- [Let]: the binding is pushed at the right-hand side's type and dropped after the tail
(`dropTopBind`); the run's `.letIn` clause. -/
theorem letIn_step (fuel : Nat) (ih : ∀ ρ φ, StepsIH K ρ φ fuel) : letIn_step_stmt K ρ φ (fuel + 1) := by
  sorry

/-- `Eq` (the `.eq` form): both sides on private copies, the type a statement; the result means
`⟦a⟧ = ⟦b⟧` (`Steps/Eq.mkEqM_step`), and the state's core is unchanged. -/
theorem eq_step (fuel : Nat) (ih : ∀ ρ φ, StepsIH K ρ φ fuel) : eq_step_stmt K ρ φ (fuel + 1) := by
  sorry

/-- `J`, both outcomes: computed at convertible endpoints (the transported term runs in place)
or closed off as a stuck block whose one arm is the transported term ([T-J-stuck]); each means
the transported term (docs/24 C9). -/
theorem J_step (fuel : Nat) (ih : ∀ ρ φ, StepsIH K ρ φ fuel) : J_step_stmt K ρ φ (fuel + 1) := by
  sorry

/-- A proof position (a proof-returning call, a proof primitive, a proof `let`): its value is
`⋆`, which is a member of its proposition exactly when the proposition is true; the state is
unchanged (a statement runs on a copy). Membership here is where "a proof's value is `⋆`"
(docs/26 row 1, *same* given membership) is discharged. -/
theorem proof_step (fuel : Nat) (ih : ∀ ρ φ, StepsIH K ρ φ fuel) : proof_step_stmt K ρ φ (fuel + 1) := by
  sorry

/-- η at `Unit` (D80): where a position's declared reading is `Unit`, the value is `()`, and
`()` is the one element of `⟦Unit⟧`, so the normalisation keeps meaning given membership. -/
theorem etaUnit_step (fuel : Nat) (ih : ∀ ρ φ, StepsIH K ρ φ fuel) : etaUnit_step_stmt K ρ φ (fuel + 1) := by
  sorry

end

end Ochr.Meaning.Steps

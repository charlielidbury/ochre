import Ochr.Meaning.Steps.Statements
/-!
# The knot at one fixed future (archived record; NOT built: checked against spine 406891db)

`codeMeaning K ρ φ₀` ignored the assignment and future it was passed, and `StepsIH` assumed
`K.C = codeMeaning K ρ φ₀`. So a state's meaning read every sealed program, closure and Π-closure
at `φ₀`, whatever future it was asked at, while `Below` (`∀ φ', ∃ φ`), `Mean.semEnd`
(`m.val (φ.upd ℓ _)`) and `Membership` (every typed future) all read a state at other futures.

Consequence for [End] on a lender holding a fill. Take `x ↦ ⌈loan_ℓ⌉` and `r ↦ borrow_ℓ c` with
`⟦c⟧ = 5` and `φ₀ ℓ = 7`. The checker's [End ℓ] gives `x ↦ c`, meaning `5` at every future.
`semEnd` reads `x` in the state before at `φ.upd ℓ 5`, which by the theorem below is `φ₀ ℓ = 7`
for every `φ`. So `endBorrow_step_stmt`'s `Below` conjunct has no witness. A definition fault.

Fixed in the commit after 406891db: `codeMeaning K` passes its assignment and future through, and
the statements read a state through `K.M = codeMeaning K` with no knot hypothesis (docs/31 D18).
The positive form is `Run.lean`'s `mean_sealed_at_future`.
-/
open Ochr Ochr.Meaning

/-- With the knot tied at `φ₀`, a sealed program in a state is read at `φ₀`, at every future. -/
theorem knot_fixed_future (K : RunCtx) (ρ : Assignment) (φ₀ φ : Future) (hint : TyS) (l : Nat)
    (hK : K.C = codeMeaning K ρ φ₀) :
    Value.mean K.dm K.C K.Γ ρ φ hint (.sealed (.val (.loan l))) = φ₀ l := by
  rw [hK]
  show meanV K ρ φ₀ hint (.sealed (.val (.loan l))) = φ₀ l
  simp [meanV, run]

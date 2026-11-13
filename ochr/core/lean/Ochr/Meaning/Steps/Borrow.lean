import Ochr.Meaning.Steps.IH

/-!
# Step lemmas, borrows: [End], [Access], [Read], [Borrow], [Assign], [Drop] (milestone 3)

The shape of every step lemma of the skeleton (docs/18 Thm. 14, one rule at a time). A checker
step is a monadic action `f : M α` run by `runMachine` from a state `st` that is `Good` for an
assignment `ρ` (membership and well-formedness, `WF.lean`). If it returns `ok a st'`, then for
the extended assignment `ρ'` (here the same `ρ`: these steps create no unknowns) the meaning of
`st'` is below the semantic step applied to the meaning of `st`, and `st'` is `Good` again.
"Below" is `Below` of `State.lean`; an *exact* step has equality at every position. Each lemma
says which of the three kinds it is: exact, an end (below by `semEnd_below`), or an
over-approximation.

Conventions for provers: the checker's state is read through `MState.sstate` and `MState.mean`
(`State.lean`, `SState.lean`); the semantic side is `SState`'s primitives; `K` is the run
context whose `C` is the knot `codeMeaning` and whose `D` is the checker's `Decide` functions
(instantiated in milestone 3's `Decisions.lean`, not yet written). A lemma may assume `Good`
and nothing else about the state: four natural statements about the checker are false at
arbitrary states (docs/18 §"Facts that hold only at reachable states").
-/

namespace Ochr.Meaning.Steps

open Ochr.Meaning

section
variable (K : RunCtx) (ρ : Assignment) (φ : Future)

/-- [End ℓ] (`Machine.endBorrow`): with `ℓ`'s borrow held whole at `r`, the result is `semEnd`
exactly, so it is below (`Mean.semEnd_below`); `Good` is kept. The content must be whole, which
the checker checks outside an observation (D53 (h), D68). -/
theorem endBorrow_step (fuel : Nat) (ih : ∀ ρ φ, StepsIH K ρ φ fuel) : endBorrow_step_stmt K ρ φ (fuel + 1) := by
  sorry

/-- [Access] as the checker performs it before a read (`accessPath` then `accessInside`): a
sequence of [End]s, each below; the ended labels include every label the accessed position's
meaning depends on, so the result is below the reference's `SState.access`, and the accessed
content no longer depends on the future (`Lemmas.meanV_congr`). (`accessPath` alone ends only
the path: the pilot prover's finding, so it is not stated on its own.) -/
theorem access_step (fuel : Nat) (ih : ∀ ρ φ, StepsIH K ρ φ fuel) : access_step_stmt K ρ φ (fuel + 1) := by
  sorry

/-- [Read] (`readPlace`): after its access, the result is the place's meaning (future-free), and
the place is unchanged (a copy, by the declared reading, D80) or `moved` (a move); exact against
the run's `readPlace` with the same copy decision (`Decisions.copy`, aligned). -/
theorem readPlace_step (fuel : Nat) (ih : ∀ ρ φ, StepsIH K ρ φ fuel) : readPlace_step_stmt K ρ φ (fuel + 1) := by
  sorry

/-- [Borrow] (`borrowPlace`): exact against the run's `borrowPlace` with the same fresh label
(`nextLoan`): the place means the label's final content and the borrow the old content. -/
theorem borrowPlace_step (fuel : Nat) (ih : ∀ ρ φ, StepsIH K ρ φ fuel) : borrowPlace_step_stmt K ρ φ (fuel + 1) := by
  sorry

/-- [Assign] (`assignPlace`): the owned access (D67, ends), the old content's borrows end
([Drop], ends), then the place means the new value: below the run's `setContent` after
`access`. The written value's meaning is given. -/
theorem assignPlace_step (fuel : Nat) (ih : ∀ ρ φ, StepsIH K ρ φ fuel) : assignPlace_step_stmt K ρ φ (fuel + 1) := by
  sorry

/-- [Drop] of the top binding (`dropTopBind`): its borrows end, each live loan in it ends its
borrower when held in a binding (D65), then the binding is gone: ends followed by `forget`,
below. -/
theorem dropTopBind_step (fuel : Nat) (ih : ∀ ρ φ, StepsIH K ρ φ fuel) : dropTopBind_step_stmt K ρ φ (fuel + 1) := by
  sorry

/-- Popping a frame (`popFrame`): each binding dropped in turn; below. -/
theorem popFrame_step (fuel : Nat) (ih : ∀ ρ φ, StepsIH K ρ φ fuel) : popFrame_step_stmt K ρ φ (fuel + 1) := by
  sorry

end

end Ochr.Meaning.Steps

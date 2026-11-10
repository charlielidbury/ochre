import Ochr.Meaning.Steps.IH

/-!
# Step lemmas, definitions: `checkTail`, `checkFix`, `checkDef`, `checkInd` (milestone 3;
docs/18 Corollary "an accepted definition means an element of its type")

[Def] checks a definition at its generic call: a fresh unknown per parameter (a borrow
parameter's in a cell behind a borrow, a proof parameter's `⋆`), the goal the codomain there,
the body in tail position producing a case tree whose every leaf converts to the goal. Under
every typed assignment of the generic state, following the arms it selects, `evalCore_step`
along the tree gives a leaf whose value is a member of the goal (`conv_sound` at the leaf and
`bodyReturns_sound` for wholeness); so the definition's meaning, the function from assignments
to leaf meanings, is an element of its Π-type. `checkInd` establishes that the data model covers
the declaration ((I1)–(I9) make the fixed point exist).
-/

namespace Ochr.Meaning.Steps

open Ochr.Meaning

section
variable (K : RunCtx) (ρ : Assignment) (φ : Future)

/-- The generic state of a `fix` is `Good` for every assignment that gives each parameter's
unknown an element of its type (and the goal is a type). -/
theorem generic_good (fuel : Nat) (ih : StepsIH K ρ φ fuel) : generic_good_stmt K ρ φ (fuel + 1) := by
  sorry

/-- `checkTail` with a leaf continuation: every typed assignment of the start state reaches a
leaf (coverage along splits), where the continuation's hypotheses hold for the leaf's value and
type, and the leaf's value means the reference run's result at the start. -/
theorem checkTail_step (fuel : Nat) (ih : StepsIH K ρ φ fuel) : checkTail_step_stmt K ρ φ (fuel + 1) := by
  sorry

/-- [Def]/[Fix] (`checkFix`): an accepted `fix` means an element of its Π-type (docs/18
Corollary 15): under every assignment of its parameters, the body's reference run gives a
member of the goal, so `mkTele` succeeds and the closure's meaning is in the carrier. -/
theorem checkFix_sound (fuel : Nat) (ih : StepsIH K ρ φ fuel) : checkFix_sound_stmt K ρ φ (fuel + 1) := by
  sorry

/-- [Const]: an accepted constant's value is a member of its goal, under the empty assignment. -/
theorem checkConst_sound (fuel : Nat) (ih : StepsIH K ρ φ fuel) : checkConst_sound_stmt K ρ φ (fuel + 1) := by
  sorry

/-- [Ind-decl] (`checkInd`): an accepted declaration satisfies (I1)–(I9), so the data model covers
it (the least fixed point exists in the sort's universe; docs/18 Lemma 2). -/
theorem checkInd_sound (fuel : Nat) (ih : StepsIH K ρ φ fuel) : checkInd_sound_stmt K ρ φ (fuel + 1) := by
  sorry

end

end Ochr.Meaning.Steps

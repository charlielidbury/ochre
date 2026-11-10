import Ochr.Meaning.Steps.IH

/-!
# The aligned decisions equal the checker's (milestone 3; docs/18 "Decisions, by kind",
*aligned*)

`Decisions` (`Places.lean`) is what the reference run reads from syntax. "Aligned" is discharged
by showing each field equals the checker's `Decide` function, run from a state holding the same
declarations: whether a term is a statement and a proof (`preFlags`), a place's and a term's
declared-type reading (`placeDecl`, `declOf`), copy-ness (`declCopy`), a Π-term's sort
(`sortOf`/`piSort`), and D84's join set (`jdMoves`, on branch `d84`; stated here against the
field only, to be tied to `Decide.jdMoves` when it lands). The instance itself,
`Decisions` built from `Decide.lean`, is `DecisionsInst.lean` (implementer prog-decisions);
these statements are about that instance.
-/

namespace Ochr.Meaning.Steps

open Ochr.Meaning

section
variable (K : RunCtx) (ρ : Assignment) (φ : Future)

/-- The scope of readings the checker uses at `st`'s top frame is `scopeOf` of its semantic
state (each binding's `decl`, innermost first). -/
theorem scopeOf_sstate (fuel : Nat) (ih : StepsIH K ρ φ fuel) : scopeOf_sstate_stmt K ρ φ (fuel + 1) := by
  sorry

/-- `Decisions.flags` is `Decide.preFlags` where the latter answers. -/
theorem flags_aligned (fuel : Nat) (ih : StepsIH K ρ φ fuel) : flags_aligned_stmt K ρ φ (fuel + 1) := by
  sorry

/-- `Decisions.placeDecl` is `Decide.placeDecl`. -/
theorem placeDecl_aligned (fuel : Nat) (ih : StepsIH K ρ φ fuel) : placeDecl_aligned_stmt K ρ φ (fuel + 1) := by
  sorry

/-- `Decisions.declOf` is `Decide.declOf` (unchecked mode). -/
theorem declOf_aligned (fuel : Nat) (ih : StepsIH K ρ φ fuel) : declOf_aligned_stmt K ρ φ (fuel + 1) := by
  sorry

/-- `Decisions.copy` is `Decide.declCopy`. -/
theorem copy_aligned (fuel : Nat) (ih : StepsIH K ρ φ fuel) : copy_aligned_stmt K ρ φ (fuel + 1) := by
  sorry

/-- `Decisions.piSort` is `Decide.sortOf` of the Π-type value (D55: declared sort = computed). -/
theorem piSort_aligned' (fuel : Nat) (ih : StepsIH K ρ φ fuel) : piSort_aligned'_stmt K ρ φ (fuel + 1) := by
  sorry

/-- D84 [Join]: `Decisions.joinMoves` is `Decide.jdMoves` as `Machine.staticJoin` calls it (the
places already `⊥` at the match as its `entry`). -/
theorem joinMoves_aligned (fuel : Nat) (ih : StepsIH K ρ φ fuel) : joinMoves_aligned_stmt K ρ φ (fuel + 1) := by
  sorry

/-- D84 [Id-typestate]/[Obs-ref]: `Decisions.rePointed` is the `repointed` component of
`Decide.typeState`, as `Machine.idType` reads it. -/
theorem rePointed_aligned (fuel : Nat) (ih : StepsIH K ρ φ fuel) : rePointed_aligned_stmt K ρ φ (fuel + 1) := by
  sorry

end

end Ochr.Meaning.Steps

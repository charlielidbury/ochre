import Ochr.Meaning.Steps.IH

/-!
# Step lemmas, observation and `Id`: `observe`, `idType`, footprint coverage (milestone 3;
docs/18 (O1)–(O5), docs/27 Def. 5)

The checker observes a side of `Id` on a private copy, ends every borrow left, and reads the
result and the contents of the footprint's owners (`observe`); `Id` then computes to the
conjunction of the equations over the result and the owners (`idType`). The reference run's
`observation` reads the result and *every* position after ending every borrow. They agree by
**footprint coverage**: a position outside the footprint has the same meaning after either
side (a side changes a position only by writing it or a borrow it owns, or by moving it, and
under D84 moves are in the footprint too), so its equation is true and dropping it loses
nothing. So `idType` is exact.
-/

namespace Ochr.Meaning.Steps

open Ochr.Meaning

section
variable (K : RunCtx) (ρ : Assignment) (φ : Future)

/-- `observe` (a side on a private copy, a fresh `σ` written through each re-pointed binding
([Obs-ref]), every borrow ended, the result and the owners read): for the written values `ws`
the fresh unknowns mean under the extended assignment, the result and each observed owner mean
their components of the reference observation at the owners' positions; the state is unchanged
(a copy). -/
theorem observe_step (fuel : Nat) (ih : ∀ ρ φ, StepsIH K ρ φ fuel) : observe_step_stmt K ρ φ (fuel + 1) := by
  sorry

/-- Footprint coverage (docs/18 "Footprint coverage", the third of the five lemmas): a position
outside the footprint of the two sides means the same after either side. -/
theorem footprint_coverage (fuel : Nat) (ih : ∀ ρ φ, StepsIH K ρ φ fuel) : footprint_coverage_stmt K ρ φ (fuel + 1) := by
  sorry

/-- `Id` computes (`idType`): the conjunction over the result and the footprint's owners means
the reference's `Id`, the equality of the two observations; exact, and the state's core is
unchanged. -/
theorem idType_step (fuel : Nat) (ih : ∀ ρ φ, StepsIH K ρ φ fuel) : idType_step_stmt K ρ φ (fuel + 1) := by
  sorry

/-- Owners (RULES §4): every position `owners env l` lists holds, directly or through the content
of a borrow it holds, a loan of `l`; and conversely every position whose meaning depends on `l`
is among them (`Mean.dependsOn`). -/
theorem owners_sound (fuel : Nat) (ih : ∀ ρ φ, StepsIH K ρ φ fuel) : owners_sound_stmt K ρ φ (fuel + 1) := by
  sorry

end

end Ochr.Meaning.Steps

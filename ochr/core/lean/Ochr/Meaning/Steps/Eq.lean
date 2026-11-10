import Ochr.Meaning.Steps.IH

/-!
# Step lemmas, `Eq` and conversion: `mkEqM`, `conv`, `convPi`, `convFn`, `rewriteGoal`
(milestone 3; docs/18 Lemma "conversion respects meaning", (V1)–(V9))

`Eq` computes (`mkEqM`) to `True`, `False`, a conjunction of field equations, or stays stuck:
every outcome means the proposition `⟦a⟧ = ⟦b⟧` (docs/24 C10, `Eq` reads no type; distinct
tags are distinct meanings; whole constructor values are equal iff their fields are, by
`DataModel.pack_fields`; under D84 a moved field is a definite value, so a partly moved value is
equal only to one with the same moved fields, `Sem.ctor`). Conversion is a *check*: only its
accepting direction carries an obligation, that convertible values have equal meanings, for
two values that are members of one type (their recorded parameters then mean the same). The
statements are monotone-free: under D84 nothing is identified that may stand for different
values ([Conv-bot] is retired), so no clause about `⊥` is needed beyond definiteness.
-/

namespace Ochr.Meaning.Steps

open Ochr.Meaning

section
variable (K : RunCtx) (ρ : Assignment) (φ : Future)

/-- `Eq` computes soundly: whatever `mkEqM` returns means `⟦a⟧ = ⟦b⟧` at `A`, and the state's
core is unchanged. -/
theorem mkEqM_step (fuel : Nat) (ih : StepsIH K ρ φ fuel) : mkEqM_step_stmt K ρ φ (fuel + 1) := by
  sorry

/-- Conversion is sound: two values convertible at a state, both (partly moved) members of one
type, have equal meanings under every future. The accepting direction only; `convStack` only
makes `conv` answer `false` more often, so no hypothesis on it. -/
theorem conv_sound (fuel : Nat) (ih : StepsIH K ρ φ fuel) : conv_sound_stmt K ρ φ (fuel + 1) := by
  sorry

/-- [Conv-pi]: convertible Π-type values have equal type meanings (equal Lean carriers), by
`funext` over the generic arguments, which range over the whole domain (docs/18 (V4)). -/
theorem convPi_sound (fuel : Nat) (ih : StepsIH K ρ φ fuel) : convPi_sound_stmt K ρ φ (fuel + 1) := by
  sorry

/-- [Conv-fun]: two function values with convertible observations of their generic calls mean
the same function (extensionality on good carriers, docs/18 (V5), `Slice.pi_ext`). -/
theorem convFn_sound (fuel : Nat) (ih : StepsIH K ρ φ fuel) : convFn_sound_stmt K ρ φ (fuel + 1) := by
  sorry

/-- [Rewrite]: when the equation `h : Eq(A, a, b)` is true, the rewritten goal is true iff the
goal is (the occurrences replaced mean the same). -/
theorem rewriteGoal_step (fuel : Nat) (ih : StepsIH K ρ φ fuel) : rewriteGoal_step_stmt K ρ φ (fuel + 1) := by
  sorry

/-- The meaning of a type value does not depend on the future (docs/27 Lemma 5: no stored type
holds a live loan), at every state the checker reaches. Used to read types under `noFuture`. -/
theorem type_futureFree (fuel : Nat) (ih : StepsIH K ρ φ fuel) : type_futureFree_stmt K ρ φ (fuel + 1) := by
  sorry

end

end Ochr.Meaning.Steps

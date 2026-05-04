import Pss.Syntax.DeBruijn
import Mathlib.Logic.Relation

/-! # `Pss.Reduction.DeBruijnOperational` — de Bruijn operational reduction

This module ports the plain operational small-step relation to de Bruijn
terms. The relation is indexed by ambient de Bruijn depth so congruence under
abstractions can be stated directly at `depth + 1`, without locally-nameless
cofinite quantification.
-/

namespace Pss
namespace DeBruijn

/-- Small-step operational reduction for de Bruijn terms at an ambient
variable depth. The closed relation is `Step`, i.e. `StepAt 0`.

The β target uses `Term.instantiate 0 arg body`, substituting the operand for
the abstraction body's nearest bound variable and decrementing outer indices.
-/
inductive StepAt : Nat → Term → Term → Prop where
  | beta {depth : Nat} {bound body arg : Term} :
      Term.Scoped depth (.abs bound body) →
      Term.Scoped depth arg →
      StepAt depth (.app (.abs bound body) arg) (Term.instantiate 0 arg body)
  | appL {depth : Nat} {t t' u : Term} :
      StepAt depth t t' →
      Term.Scoped depth u →
      StepAt depth (.app t u) (.app t' u)
  | appR {depth : Nat} {t u u' : Term} :
      Term.Scoped depth t →
      StepAt depth u u' →
      StepAt depth (.app t u) (.app t u')
  | absBound {depth : Nat} {bound bound' body : Term} :
      StepAt depth bound bound' →
      Term.Scoped (depth + 1) body →
      StepAt depth (.abs bound body) (.abs bound' body)
  | absBody {depth : Nat} {bound body body' : Term} :
      Term.Scoped depth bound →
      StepAt (depth + 1) body body' →
      StepAt depth (.abs bound body) (.abs bound body')

/-- Closed de Bruijn operational reduction. -/
abbrev Step : Term → Term → Prop := StepAt 0

namespace StepAt

/-! ## Scoping invariants -/

/-- A reducible de Bruijn term is scoped at the relation's ambient depth. -/
theorem scoped_left_J {depth : Nat} {t t' : Term}
    (h : StepAt depth t t') : Nonempty (Term.Scoped depth t) := by
  induction h with
  | beta hAbs hArg =>
      exact ⟨Term.Scoped.app hAbs hArg⟩
  | appL _ hArg ih =>
      exact ⟨Term.Scoped.app ih.some hArg⟩
  | appR hFn _ ih =>
      exact ⟨Term.Scoped.app hFn ih.some⟩
  | absBound _ hBody ih =>
      exact ⟨Term.Scoped.abs ih.some hBody⟩
  | absBody hBound _ ih =>
      exact ⟨Term.Scoped.abs hBound ih.some⟩

/-- Type-valued accessor for source scoping of de Bruijn operational steps. -/
noncomputable def scoped_left {depth : Nat} {t t' : Term}
    (h : StepAt depth t t') : Term.Scoped depth t :=
  h.scoped_left_J.some

/-- De Bruijn operational reduction preserves scoping. -/
theorem scoped_right_J {depth : Nat} {t t' : Term}
    (h : StepAt depth t t') : Nonempty (Term.Scoped depth t') := by
  induction h with
  | @beta depth bound body arg hAbs hArg =>
      have hBody : Term.Scoped (depth + 1) body := hAbs.abs_inv.2
      exact ⟨Term.instantiate_scoped 0 depth arg body (Nat.zero_le depth) hArg hBody⟩
  | appL _ hArg ih =>
      exact ⟨Term.Scoped.app ih.some hArg⟩
  | appR hFn _ ih =>
      exact ⟨Term.Scoped.app hFn ih.some⟩
  | absBound _ hBody ih =>
      exact ⟨Term.Scoped.abs ih.some hBody⟩
  | absBody hBound _ ih =>
      exact ⟨Term.Scoped.abs hBound ih.some⟩

/-- Type-valued accessor for target scoping of de Bruijn operational steps. -/
noncomputable def scoped_right {depth : Nat} {t t' : Term}
    (h : StepAt depth t t') : Term.Scoped depth t' :=
  h.scoped_right_J.some

/-! ## Application inversion -/

/-- Inversion for a de Bruijn operational step whose source is an application. -/
theorem app_inv {depth : Nat} {t u e' : Term}
    (h : StepAt depth (.app t u) e') :
    (∃ bound body, t = .abs bound body ∧ e' = Term.instantiate 0 u body) ∨
    (∃ t', e' = .app t' u ∧ StepAt depth t t') ∨
    (∃ u', e' = .app t u' ∧ StepAt depth u u') := by
  cases h with
  | beta _ _ =>
      exact Or.inl ⟨_, _, rfl, rfl⟩
  | appL hstep _ =>
      exact Or.inr (Or.inl ⟨_, rfl, hstep⟩)
  | appR _ hstep =>
      exact Or.inr (Or.inr ⟨_, rfl, hstep⟩)

/-! ## Reflexive-transitive closure -/

/-- Many-step de Bruijn operational reduction at an ambient depth. -/
abbrev Star (depth : Nat) : Term → Term → Prop :=
  Relation.ReflTransGen (StepAt depth)

namespace Star

/-- Multi-step de Bruijn operational reduction preserves target scoping from a
scoped source. -/
theorem scoped_right_J {depth : Nat} {t t' : Term}
    (h : StepAt.Star depth t t') (ht : Term.Scoped depth t) :
    Nonempty (Term.Scoped depth t') := by
  induction h with
  | refl => exact ⟨ht⟩
  | tail _ hstep _ =>
      exact ⟨hstep.scoped_right⟩

end Star

end StepAt

namespace Step

/-- Closed de Bruijn operational reduction preserves closedness of the target. -/
theorem closed_right_J {t t' : Term} (h : Step t t') :
    Nonempty (Term.Closed t') :=
  h.scoped_right_J

/-- Type-valued accessor for closedness preservation by closed steps. -/
noncomputable def closed_right {t t' : Term} (h : Step t t') :
    Term.Closed t' :=
  h.closed_right_J.some

/-- Many-step closed de Bruijn operational reduction. -/
abbrev Star : Term → Term → Prop := StepAt.Star 0

end Step

end DeBruijn
end Pss

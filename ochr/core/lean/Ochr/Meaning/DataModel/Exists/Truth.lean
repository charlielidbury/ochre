import Ochr.Meaning.DataModel.Exists.PropMono

/-!
# Truth first, part 1: the least fixed point (exists6)

The truth-first construction of a `Prop`-sorted declaration `d` (piece 5, docs/34 §18.9): its truth
predicate is the least fixed point of the one-step operator `Φ` (`Φ T ps`: some constructor of `d` has
fields fitting the shapes of the record built from `T`, `d`'s own occurrences read as proposition
leaves of `T`). `Φ` is monotone when every shape `T` reaches is a proposition leaf, which rule (A*) and
the earlier records' monotonicity (`mono_prop`'s hypothesis) give. This file holds the fixed point
itself, for any monotone operator on predicates over parameter lists (Knaster–Tarski, impredicative).
-/

namespace Ochr.Meaning.DataModel.Exists

open Ochr Ochr.Meaning

/-- A monotone operator on predicates over parameter lists. -/
def MonoOp (Φ : (List Sem → Prop) → List Sem → Prop) : Prop :=
  ∀ X Y : List Sem → Prop, (∀ ps, X ps → Y ps) → ∀ ps, Φ X ps → Φ Y ps

/-- **The least fixed point**: what every predicate closed under `Φ` holds. -/
def lfpP (Φ : (List Sem → Prop) → List Sem → Prop) : List Sem → Prop :=
  fun ps => ∀ X : List Sem → Prop, (∀ qs, Φ X qs → X qs) → X ps

theorem lfpP_least (Φ : (List Sem → Prop) → List Sem → Prop) (X : List Sem → Prop)
    (hX : ∀ qs, Φ X qs → X qs) : ∀ ps, lfpP Φ ps → X ps :=
  fun _ h => h X hX

theorem lfpP_closed {Φ : (List Sem → Prop) → List Sem → Prop} (hm : MonoOp Φ) :
    ∀ ps, Φ (lfpP Φ) ps → lfpP Φ ps :=
  fun ps h X hX => hX ps (hm (lfpP Φ) X (lfpP_least Φ X hX) ps h)

/-- **It is a fixed point** (as propositions: `Φ (lfpP Φ) = lfpP Φ`). -/
theorem lfpP_fixed {Φ : (List Sem → Prop) → List Sem → Prop} (hm : MonoOp Φ) : Φ (lfpP Φ) = lfpP Φ := by
  funext ps
  apply propext
  refine ⟨lfpP_closed hm ps, fun h => ?_⟩
  exact h (Φ (lfpP Φ)) (fun qs hq => hm (Φ (lfpP Φ)) (lfpP Φ) (lfpP_closed hm) qs hq)

end Ochr.Meaning.DataModel.Exists

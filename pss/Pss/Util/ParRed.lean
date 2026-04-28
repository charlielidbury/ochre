import Mathlib.Logic.Relation

/-! # Generic Takahashi-style parallel reduction infrastructure

This module provides a *reusable* API for proving confluence of a
context-indexed reduction relation `step : Ctx → α → α → Prop` via the
Takahashi strategy: exhibit an auxiliary "parallel" reduction `par`
sandwiched between `step` and its reflexive-transitive closure, then
show `par` enjoys the diamond property. Confluence of `step` follows.

Two downstream modules will instantiate this:

* `Pss.Algo.Confluence` — confluence of Hutchins' `⟶^≡`.
* `Pss.Mpss.Diamond`   — diamond of MPSS's `Me-*` reductions.

The module is deliberately *generic*: no concrete reduction is defined
here. The context type `Ctx` is carried as a parameter so callers can
keep using the natural ternary form `step Γ a b`; internally we partially
apply at `Γ` and reuse Mathlib's `Relation.ReflTransGen` /
`Relation.church_rosser` machinery (Risk 2 mitigation in `PLAN.md` §5).
-/

namespace Pss.Util.ParRed

universe u v

variable {Ctx : Type u} {α : Type v}

/-- Reflexive-transitive closure of a context-indexed relation, taken
pointwise in the context. We re-export `Relation.ReflTransGen` partially
applied at `Γ` so the rest of the development can write `Star r Γ a b`
ergonomically while still benefiting from every Mathlib lemma about
`ReflTransGen`. -/
abbrev Star (r : Ctx → α → α → Prop) (Γ : Ctx) : α → α → Prop :=
  Relation.ReflTransGen (r Γ)

/-- Diamond property for a context-indexed relation: from a peak we can
close the diagram with one `r`-step on each side. -/
def HasDiamond (r : Ctx → α → α → Prop) : Prop :=
  ∀ Γ a b c, r Γ a b → r Γ a c → ∃ d, r Γ b d ∧ r Γ c d

/-- Confluence of the reflexive-transitive closure of a context-indexed
relation. Equivalent to `Confluent (r Γ)` for every `Γ` when stated via
Mathlib's nameless predicate, but kept as a thin wrapper so downstream
agents can pattern-match on the ternary form. -/
def Confluent (r : Ctx → α → α → Prop) : Prop :=
  ∀ Γ a b c, Star r Γ a b → Star r Γ a c → ∃ d, Star r Γ b d ∧ Star r Γ c d

/-- A Takahashi *sandwich* between a base reduction `step` and a parallel
reduction `par`: one `step` is one `par`, and one `par` is many `step`s.
This is the only structural assumption the headline theorem requires. -/
structure Sandwich (step par : Ctx → α → α → Prop) : Prop where
  step_to_par : ∀ Γ a b, step Γ a b → par Γ a b
  par_to_star : ∀ Γ a b, par Γ a b → Star step Γ a b

namespace Star

variable {r : Ctx → α → α → Prop} {Γ : Ctx} {a b c : α}

/-- One step is many steps. -/
theorem single (h : r Γ a b) : Star r Γ a b :=
  Relation.ReflTransGen.single h

/-- Reflexivity. -/
theorem refl : Star r Γ a a :=
  Relation.ReflTransGen.refl

/-- Transitivity. -/
theorem trans (hab : Star r Γ a b) (hbc : Star r Γ b c) : Star r Γ a c :=
  Relation.ReflTransGen.trans hab hbc

end Star

/-- Pointwise containment between two context-indexed relations lifts to
their reflexive-transitive closures. Internally this is `ReflTransGen.mono`
applied at the fixed context `Γ`. -/
theorem star_mono {r p : Ctx → α → α → Prop}
    (h : ∀ Γ a b, r Γ a b → p Γ a b) :
    ∀ Γ a b, Star r Γ a b → Star p Γ a b := by
  intro Γ a b hab
  exact Relation.ReflTransGen.mono (h Γ) hab

/-- If every step of `r` can be expanded into a `Star`-sequence of `p`-steps
then so can every `Star r`. -/
theorem star_closed {r p : Ctx → α → α → Prop}
    (h : ∀ Γ a b, r Γ a b → Star p Γ a b) :
    ∀ Γ a b, Star r Γ a b → Star p Γ a b := by
  intro Γ a b hab
  exact Relation.reflTransGen_closed (h Γ) hab

/-- Under a `Sandwich`, the reflexive-transitive closures coincide. -/
theorem star_eq_of_sandwich {step par : Ctx → α → α → Prop}
    (sw : Sandwich step par) :
    ∀ Γ a b, Star step Γ a b ↔ Star par Γ a b := by
  intro Γ a b
  refine ⟨?_, ?_⟩
  · exact star_mono sw.step_to_par Γ a b
  · exact star_closed sw.par_to_star Γ a b

/-- The diamond property for `par` lifts to confluence of its own
reflexive-transitive closure. This is the standard "tile-the-grid"
argument; we let Mathlib's `Relation.church_rosser` do the work. -/
theorem confluent_of_hasDiamond {par : Ctx → α → α → Prop}
    (diamond : HasDiamond par) : Confluent par := by
  intro Γ a b c hab hac
  -- Strengthen the diamond hypothesis to the form `church_rosser` expects:
  -- the joining `b`-side step is allowed to be reflexive.
  have hcr :
      ∀ x y z, par Γ x y → par Γ x z →
        ∃ w, Relation.ReflGen (par Γ) y w ∧ Relation.ReflTransGen (par Γ) z w := by
    intro x y z hxy hxz
    obtain ⟨w, hyw, hzw⟩ := diamond Γ x y z hxy hxz
    exact ⟨w, Relation.ReflGen.single hyw, Relation.ReflTransGen.single hzw⟩
  obtain ⟨d, hbd, hcd⟩ := Relation.church_rosser hcr hab hac
  exact ⟨d, hbd, hcd⟩

/-- **Headline theorem.** Takahashi's strategy: a parallel reduction with
the diamond property, sandwiched by a base reduction, suffices to prove
the base reduction confluent.

Proof sketch:
1. From `Sandwich`, `Star step` and `Star par` agree pointwise.
2. `HasDiamond par` gives `Confluent par` (`confluent_of_hasDiamond`).
3. Confluence transports back through the equality of (1). -/
theorem confluent_of_diamond
    {step par : Ctx → α → α → Prop}
    (sw : Sandwich step par)
    (diamond : HasDiamond par) :
    Confluent step := by
  intro Γ a b c hab hac
  have hStarIff := star_eq_of_sandwich sw
  -- Move both legs of the peak into the `par` world.
  have habp : Star par Γ a b := (hStarIff Γ a b).mp hab
  have hacp : Star par Γ a c := (hStarIff Γ a c).mp hac
  -- Close the peak using diamond ⇒ confluent on `par`.
  obtain ⟨d, hbd, hcd⟩ := confluent_of_hasDiamond diamond Γ a b c habp hacp
  -- Transport the join back to `step`.
  refine ⟨d, ?_, ?_⟩
  · exact (hStarIff Γ b d).mpr hbd
  · exact (hStarIff Γ c d).mpr hcd

end Pss.Util.ParRed

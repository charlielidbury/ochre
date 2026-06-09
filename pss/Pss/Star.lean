/-!
# Reflexive-transitive closure

Small self-contained closure operators for abstract reduction systems, used
for `⟶*` (multi-step reduction), `⊲→*` (reduction sequences, §6) and the
symmetric-transitive closure `=` of §7. Mathlib-free by design.
-/

namespace Pss

/-- Reflexive-transitive closure of a relation (`R*`). -/
inductive Star {α : Sort _} (R : α → α → Prop) : α → α → Prop where
  | refl {a : α} : Star R a a
  | head {a b c : α} : R a b → Star R b c → Star R a c

namespace Star

variable {α : Sort _} {R : α → α → Prop} {a b c : α}

theorem single (h : R a b) : Star R a b := .head h .refl

theorem trans (hab : Star R a b) (hbc : Star R b c) : Star R a c := by
  induction hab with
  | refl => exact hbc
  | head h _ ih => exact .head h (ih hbc)

theorem tail (hab : Star R a b) (hbc : R b c) : Star R a c :=
  hab.trans (single hbc)

/-- Monotonicity: a closure of a smaller relation embeds in the closure of a
larger one. -/
theorem mono {S : α → α → Prop} (hRS : ∀ {x y}, R x y → S x y)
    (h : Star R a b) : Star S a b := by
  induction h with
  | refl => exact .refl
  | head h _ ih => exact .head (hRS h) ih

/-- Map a closure through a relation-preserving function. -/
theorem map {β : Sort _} {S : β → β → Prop} (f : α → β)
    (hf : ∀ {x y}, R x y → S (f x) (f y)) (h : Star R a b) :
    Star S (f a) (f b) := by
  induction h with
  | refl => exact .refl
  | head h _ ih => exact .head (hf h) ih

end Star

/-- Symmetric closure of a relation. -/
inductive Sym {α : Sort _} (R : α → α → Prop) : α → α → Prop where
  | fwd {a b : α} : R a b → Sym R a b
  | bwd {a b : α} : R b a → Sym R a b

/-- Symmetric-transitive-reflexive closure (the `=` of §7). -/
abbrev EqClosure {α : Sort _} (R : α → α → Prop) : α → α → Prop := Star (Sym R)

end Pss

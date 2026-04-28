import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Fintype.Card

/-! # `pick_fresh` tactic

Provides a single tactic, `pick_fresh`, used pervasively in locally-nameless
proofs with cofinite quantification.

## Surface

```
pick_fresh x avoiding S₁, S₂, ..., Sₙ
```

introduces:

* `x : String`,
* `x_fresh : x ∉ S₁ ∪ S₂ ∪ ... ∪ Sₙ`,
* `hx₁ : x ∉ S₁`, `hx₂ : x ∉ S₂`, ..., `hxₙ : x ∉ Sₙ`
  (split out by `simp [Finset.not_mem_union]`).

The named hypotheses `hx₁ … hxₙ` are derived from the conjuncts of the
`simp`-normalized `x_fresh`, so the user can `exact ⟨x, hx₁, hx₂⟩` etc.
The "raw union" hypothesis `x_fresh` is also kept for cases where you want
to feed `pick_fresh` a single avoidance set yourself.

## Mathlib API used

* `Finset.exists_not_mem (s : Finset α) [Infinite α] : ∃ a, a ∉ s`
  (from `Mathlib.Data.Set.Finite.Basic`; requires `[Infinite α]`,
  satisfied for `String` via `String.infinite` from `Mathlib.Data.Fintype.Card`).
* `Finset.not_mem_union : a ∉ s ∪ t ↔ a ∉ s ∧ a ∉ t`.

## Implementation notes

Mathlib v4.16.0 exposes BOTH `Finset.exists_not_mem` (in
`Mathlib.Data.Set.Finite.Basic`, requires `[Infinite α]`) and
`Infinite.exists_not_mem_finset` (in `Mathlib.Data.Fintype.Card`, also
requires `[Infinite α]`). We use the former because its name doesn't
depend on remembering which namespace it lives in.
-/

namespace Pss.Util

open Lean Elab Tactic Meta

/-- Auxiliary: build `S₁ ∪ S₂ ∪ ... ∪ Sₙ` as a syntax tree, left-associated.
    Requires the input list to be non-empty (the `pick_fresh` syntax enforces
    `(term),+`, so this is safe at the call site). -/
private def combineUnion (sets : Array (TSyntax `term)) : MacroM (TSyntax `term) := do
  if sets.size = 0 then
    Macro.throwError "pick_fresh: need at least one avoidance set"
  let mut acc := sets[0]!
  for i in [1:sets.size] do
    acc ← `($acc ∪ $(sets[i]!))
  return acc

/-- `pick_fresh x avoiding S₁ S₂ ... Sₙ` introduces a fresh `x : String`
    along with `x_fresh : x ∉ S₁ ∪ ... ∪ Sₙ` and split conjuncts
    `hx₁ : x ∉ S₁`, ..., `hxₙ : x ∉ Sₙ`. -/
syntax (name := pickFresh) "pick_fresh " ident " avoiding " (term),+ : tactic

macro_rules
  | `(tactic| pick_fresh $x:ident avoiding $sets,*) => do
    let setArr : Array (TSyntax `term) := sets.getElems
    let union ← combineUnion setArr
    let xFresh := Lean.mkIdent `x_fresh
    `(tactic| (
        obtain ⟨$x:ident, $xFresh:ident⟩ := Finset.exists_not_mem ($union : Finset String)
        try simp only [Finset.not_mem_union, not_or, and_assoc] at $xFresh:ident))

/-! ### Self-tests -/

section Tests

example (s t : Finset String) : ∃ x : String, x ∉ s ∧ x ∉ t := by
  pick_fresh x avoiding s, t
  exact ⟨x, x_fresh.1, x_fresh.2⟩

example (s t u : Finset String) : ∃ x : String, x ∉ s ∧ x ∉ t ∧ x ∉ u := by
  pick_fresh x avoiding s, t, u
  exact ⟨x, x_fresh.1, x_fresh.2.1, x_fresh.2.2⟩

example (s : Finset String) : ∃ x : String, x ∉ s := by
  pick_fresh x avoiding s
  exact ⟨x, x_fresh⟩

end Tests

end Pss.Util

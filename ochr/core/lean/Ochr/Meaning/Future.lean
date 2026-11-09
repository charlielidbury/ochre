import Ochr.Meaning.Sem

/-!
# Assignments and futures (docs/18 Def. "assignment", docs/27 Def. "future")

An *assignment* `ρ` says what each abstract value `σ` stands for: an element of the meaning of
its type `Δ(σ)` (`absTy`), in the order the unknowns were created. A *future* `φ` says what each
live borrow finally holds: the final content of label `ℓ`. The meaning of a state is a function
of both; the conditions that make them well typed (`ρ σ ∈ₛ ⟦Δ(σ)⟧_ρ`, `φ ℓ ∈ₛ ⟦T_ℓ⟧`) need the
meaning of types and are stated in `State.lean` and `WF.lean`.

Both are total functions on `Nat`: what they say about names not in the state is never read
(`Value.mean` reads `ρ` only at the abstract values of the value, `φ` only at its loans).
-/

namespace Ochr.Meaning

/-- An assignment: a meaning for each abstract value `σ`. Nothing requires it to be
computable: for `σ : Π(n : Nat). Nat` it ranges over every Lean function `Nat → Nat`. -/
abbrev Assignment : Type 3 := Nat → Sem

/-- A future: the final content of each borrow label. -/
abbrev Future : Type 3 := Nat → Sem

/-- The future that fixes label `l` to `s` (ending `l` with content `s`). -/
def Future.upd (φ : Future) (l : Nat) (s : Sem) : Future := fun l' => if l' = l then s else φ l'

theorem Future.upd_same (φ : Future) (l : Nat) (s : Sem) : φ.upd l s l = s := by
  simp [Future.upd]

theorem Future.upd_other (φ : Future) {l l' : Nat} (s : Sem) (h : l' ≠ l) : φ.upd l s l' = φ l' := by
  simp [Future.upd, h]

/-- The assignment extended at a fresh abstract value `σ` (a split's field, a generalised
program, a generic parameter). -/
def Assignment.ext (ρ : Assignment) (σ : Nat) (s : Sem) : Assignment := fun σ' => if σ' = σ then s else ρ σ'

end Ochr.Meaning

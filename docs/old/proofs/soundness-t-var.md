# Soundness: T-Var Case

## Theorem (Soundness)
If Γ ⊢ M ⇒ A and M ⟶ V, then Γ ⊢ V ⊑ A.

## Case T-Var
M ≔ x, where x: A ∈ Γ.

Goal: If Γ ⊢ x ⇒ A and x ⟶ V, then Γ ⊢ V ⊑ A.
  by vacuous truth ✓

There is no concrete evaluation rule for bare variables — concrete evaluation is defined only on closed terms, and a bare variable x is not closed. Therefore x ⟶ V is not derivable for any V, and the premise x ⟶ V is never satisfied. The implication holds vacuously.

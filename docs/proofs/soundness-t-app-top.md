# Soundness: T-App-Top Case

**Theorem (Soundness).** If Γ ⊢ M ⇒ A and M ⟶ V, then Γ ⊢ V ⊑ A.

**Case** T-App-Top: M ≔ M₁ M₂, A ≔ ⊤, with premise Γ ⊢ M₁ ⇒ ⊤.

Γ ⊢ V ⊑ ⊤
  by S-Top ✓

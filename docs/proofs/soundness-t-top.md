# Soundness: T-Top Case

**Theorem (Soundness):** If `Γ ⊢ M ⇒ A` and `M ⟶ V`, then `Γ ⊢ V ⊑ A`.

**Case** T-Top: M ≔ ⊤, A ≔ ⊤.

By E-Top, V ≔ ⊤.

```
Γ ⊢ ⊤ ⊑ ⊤
  by S-Refl ✓
```

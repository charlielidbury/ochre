# Soundness — T-Fun Case

**Theorem (Soundness).** If `Γ ⊢ M ⇒ A` and `M ⟶ V`, then `Γ ⊢ V ⊑ A`.

**Case T-Fun.**

Assume:
- By T-Fun: M ≔ (x: A) → B, and Γ ⊢ (x: A) → B ⇒ (x: A) → B
- By E-Fun: (x: A) → B ⟶ (x: ⊤) → B, so V ≔ (x: ⊤) → B

Goal: Γ ⊢ (x: ⊤) → B ⊑ (x: A) → B

  by S-Fun, need:
  1. Γ ⊢ A ⊑ ⊤
     by S-Top ✓
  2. Γ, x: A ⊢ B ⊑ B
     by S-Refl ✓

∎

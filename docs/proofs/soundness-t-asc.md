# Soundness — T-Asc Case

## Theorem (Soundness)
If `Γ ⊢ M ⇒ A` and `M ⟶ V`, then `Γ ⊢ V ⊑ A`.

Proof by structural induction on the typing derivation.

## Case T-Asc

The term has the form `(M : A)` with typing derived by T-Asc.

```
Goal: Γ ⊢ V ⊑ A'
  given (M : A) ⟶ V and Γ ⊢ (M : A) ⇒ A'

  by T-Asc, we have premises:
  1. Γ ⊢ M ⇒ M'
  2. Γ ⊢ A ⇒ A'
  3. Γ ⊢ M' ⊑ A'

  by E-Asc on (M : A) ⟶ V, need:
  1. M ⟶ V ✓

  by IH on (1) and M ⟶ V:
  1. Γ ⊢ V ⊑ M' ✓

  by S-Trans, need:
  1. Γ ⊢ V ⊑ M'   — by IH ✓
  2. Γ ⊢ M' ⊑ A'   — by T-Asc premise (3) ✓
  ∴ Γ ⊢ V ⊑ A' ✓
```

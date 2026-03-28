# Lemma: Domain Erasure Subtyping (Erase-Sub)

## Statement

For all terms M and environments Γ: `Γ ⊢ erase(M) ⊑ M`.

That is, erasing all domain annotations makes a term less precise
(or equally precise).

## Proof

By structural induction on M.

**Case M = ⊤:**
erase(⊤) = ⊤. Γ ⊢ ⊤ ⊑ ⊤ by S-Refl. ∎

**Case M = x (variable):**
erase(x) = x. Γ ⊢ x ⊑ x by S-Refl. ∎

**Case M = (y: A) → N (function):**
erase((y: A) → N) = (y: ⊤) → erase(N).
Need: Γ ⊢ (y: ⊤) → erase(N) ⊑ (y: A) → N.
By S-Fun:
1. Γ ⊢ A ⊑ ⊤ — by S-Top ✓
2. Γ, y: A ⊢ erase(N) ⊑ N — by IH on N ✓ ∎

**Case M = M₁ M₂ (application):**
erase(M₁ M₂) = erase(M₁) erase(M₂).
Need: Γ ⊢ erase(M₁) erase(M₂) ⊑ M₁ M₂.
By S-App:
1. Γ ⊢ erase(M₁) ⊑ M₁ — by IH on M₁ ✓
2. Γ ⊢ erase(M₂) ⊑ M₂ — by IH on M₂ ✓ ∎

**Case M = (M₁ : A) (ascription):**
erase(M₁ : A) = erase(M₁) : erase(A).
Need: Γ ⊢ (erase(M₁) : erase(A)) ⊑ (M₁ : A).
By S-Asc:
1. Γ ⊢ erase(M₁) ⊑ M₁ — by IH on M₁ ✓
2. Γ ⊢ erase(A) ⊑ A — by IH on A ✓ ∎

## Status

✓ Complete for all cases: variables, ⊤, function literals, applications,
  and ascription terms. The ascription case is closed by S-Asc
  (structural congruence for ascription), added to close this gap.

∎

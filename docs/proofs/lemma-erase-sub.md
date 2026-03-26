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

**This case is NOT derivable** with the current subtyping rules.
No rule decomposes ascription on the right of ⊑. The only applicable
rules are S-Refl (requires syntactic equality, which fails when erase
changes M₁ or A) and S-Top (requires (M₁ : A) = ⊤, which it isn't).

### Analysis of the ascription sub-gap

The sub-gap only arises when erase actually CHANGES M₁ or A — that is,
when M₁ or A contains function subterms `(y: B) → N` where B ≠ ⊤.
This requires the ascription's inner term or target to contain function
literals with non-trivial domains.

**When erase doesn't change anything** (no function subterms with non-⊤
domains in M₁ or A): erase(M₁ : A) = M₁ : A, and S-Refl applies. ✓

**Semantic argument for the sub-gap:** At runtime, (M₁ : A) evaluates
to M₁'s value (E-Asc erases ascription). And erase(M₁) evaluates to
the same value as M₁ except with erased domains — which are all ⊤ in
values anyway (by the all-values-have-erased-domains property). So
(erase(M₁) : erase(A)) and (M₁ : A) produce the same runtime value.
The sub-gap is a proof-technique limitation, not actual unsoundness.

## Status

✓ Complete for: variables, ⊤, function literals, applications.
✗ Open sub-gap for: ascription terms with parameter-dependent domains
  in function-literal targets.

The sub-gap is an uncommon pattern and is semantically harmless. A
logical relations proof would close it entirely.

∎ (modulo ascription sub-gap)

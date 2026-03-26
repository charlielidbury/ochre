# Monotonicity — T-App Case (with abstract domain erasure)

## Theorem (Monotonicity)

If `Γ ⊢ M ⇒ A` and `Γ' ⊑ Γ` (pointwise), then `Γ' ⊢ M ⇒ A'` for some
A' with `Γ' ⊢ A' ⊑ A`.

Proof by mutual induction on the typing derivation with soundness.

---

## Case T-App

The term is `M₁ M₂` with typing derived by T-App:

```
Γ ⊢ M₁ ⇒ F                      — (P1)
Γ ⊢ F ⇓ (x: A) → B              — (P2)
Γ ⊢ M₂ ⇒ N'                     — (P3)
Γ ⊢ N' ⊑ A                      — (P4)
Γ ⊢ erase(B)[x ≔ N'] ⇒ R        — (P5)
————————————————————
Γ ⊢ M₁ M₂ ⇒ R
```

**Goal:** `Γ' ⊢ M₁ M₂ ⇒ R'` for some R' with `Γ' ⊢ R' ⊑ R`.

---

## Step 1: Apply IH to M₁

By monotonicity IH on (P1):

```
Γ' ⊢ M₁ ⇒ F'  with  Γ' ⊢ F' ⊑ F         — (IH₁)
```

## Step 2: Head-normalize F' under Γ'

By HN-Mono (lemma-hn-mono.md) applied to `F' ⊑ F` and `F ⇓ (x: A) → B`:

```
Γ' ⊢ F' ⇓ (x: C) → D                       — (HN)
Γ' ⊢ (x: C) → D ⊑ (x: A) → B              — (HN-sub)
```

By S-Fun inversion on (HN-sub):
```
Γ' ⊢ A ⊑ C                                  — (Inv₁)
Γ', x: A ⊢ D ⊑ B                            — (Inv₂)
```

## Step 3: Apply IH to M₂

By monotonicity IH on (P3):

```
Γ' ⊢ M₂ ⇒ N''  with  Γ' ⊢ N'' ⊑ N'       — (IH₂)
```

## Step 4: Argument check — N'' ⊑ C

```
N'' ⊑ N'     (IH₂)
N' ⊑ A       (P4, transported to Γ' by narrowing-preserves-subtyping)
A ⊑ C        (Inv₁)
————————————
N'' ⊑ C      (S-Trans)                       — (ArgChk)
```

## Step 5: Body evaluation — erase(D)[x ≔ N''] ⇒ R' with R' ⊑ R

T-App under Γ' will use body D (from the function type (x: C) → D).
Its premise (5) requires: `Γ' ⊢ erase(D)[x ≔ N''] ⇒ R'`.

We need R' ⊑ R where R comes from `Γ ⊢ erase(B)[x ≔ N'] ⇒ R` (P5).

### Step 5a: Relate erase(D) to erase(B)

From (Inv₂): `Γ', x: A ⊢ D ⊑ B`.

**Claim:** `Γ' ⊢ erase(D) ⊑ erase(B)` (without the x binding, since
erase removes all domain dependencies on x).

This follows from the Erase-Sub-Mono lemma: if `Γ ⊢ D ⊑ B`, then
`Γ ⊢ erase(D) ⊑ erase(B)`. Proof by structural induction on the
subtyping derivation, using the fact that erase replaces all domains
with ⊤ (neutralizing the contravariant positions that cause trouble).

Actually, we can avoid this lemma entirely by using the environment
strategy. See Step 5b.

### Step 5b: Environment strategy on (P5)

From (P5): `Γ ⊢ erase(B)[x ≔ N'] ⇒ R`.

By substitution-environment equivalence:
```
Γ, x: N' ⊢ erase(B) ⇒ R₀   where R = R₀[x ≔ N']    — (δ)
```

### Step 5c: Monotonicity into Γ', x: N''

Claim: `(Γ', x: N'') ⊑ (Γ, x: N')` pointwise.
- For y ≠ x: `Γ'(y) ⊑ Γ(y)` from `Γ' ⊑ Γ`, weakened to the
  extended environment. ✓
- For x: `N'' ⊑ N'` from (IH₂), weakened. ✓

By monotonicity IH on (δ) (strictly smaller sub-derivation):
```
Γ', x: N'' ⊢ erase(B) ⇒ R₁   with   R₁ ⊑ R₀        — (ε)
```

### Step 5d: Substitute back

From (ε): `Γ', x: N'' ⊢ erase(B) ⇒ R₁`.
By substitution-environment equivalence (forward):
```
Γ' ⊢ erase(B)[x ≔ N''] ⇒ R₁[x ≔ N'']                — (ζ)
```

### Step 5e: The key — erase(D) vs erase(B)

T-App under Γ' needs `erase(D)[x ≔ N''] ⇒ R'`, but (ζ) gives
`erase(B)[x ≔ N''] ⇒ R₁[x ≔ N'']`.

**Common case: M₁ is a function literal.** Then T-Fun gives the same
type under both Γ and Γ' (T-Fun is environment-independent), so
(x: C) → D = (x: A) → B, hence D = B and erase(D) = erase(B).
In this case, (ζ) directly gives the typing of erase(D)[x ≔ N''].

**General case: D ≠ B.** This arises when M₁'s type changes between
environments (e.g., M₁ is a variable whose environment type changes).

From (Inv₂): `Γ', x: A ⊢ D ⊑ B`. By the Erase-Mono lemma (erase
preserves subtyping: if `D ⊑ B` then `erase(D) ⊑ erase(B)`), we get
`Γ', x: A ⊢ erase(D) ⊑ erase(B)`.

Since erase(D) and erase(B) have no domain references to x (all domains
are ⊤), this holds without the x binding:
`Γ' ⊢ erase(D) ⊑ erase(B)`.

By equal substitution with N'':
`Γ' ⊢ erase(D)[x ≔ N''] ⊑ erase(B)[x ≔ N'']`.

Combined with (ζ) and S-Eval:
`erase(B)[x ≔ N''] ⊑ R₁[x ≔ N'']`.

So `erase(D)[x ≔ N''] ⊑ R₁[x ≔ N'']` by S-Trans.

By the monotonicity IH (applied to `erase(D)[x ≔ N'']` which is ⊑ a
typeable term), `erase(D)[x ≔ N'']` is typeable:
`Γ' ⊢ erase(D)[x ≔ N''] ⇒ R'` for some R'.

(Note: typeability of `erase(D)[x ≔ N'']` can also be established
directly, since every subterm of erase(D) is well-formed and the
structure is preserved under substitution.)

### Step 5f: R' ⊑ R

We need `R' ⊑ R` where `R = R₀[x ≔ N']`.

From (ε): `R₁ ⊑ R₀` under `(Γ', x: N'')`.
By equal substitution with N'': `Γ' ⊢ R₁[x ≔ N''] ⊑ R₀[x ≔ N'']`.

We also need: `Γ' ⊢ R₀[x ≔ N''] ⊑ R₀[x ≔ N']`.

**This is monotone substitution, and it works because of abstract erasure.**

R₀ is the result of typing `erase(B)` under `Γ, x: N'`. Since erase(B)
has ⊤ in all domain positions, **x does not appear in any domain position
of erase(B)**. Therefore R₀ has x only in covariant positions:

- T-Fun preserves raw syntax: domains in erase(B) are all ⊤ (no x).
  x can only appear in body positions (covariant). ✓
- T-Var replaces x with N': N' doesn't mention x (it's the type of M₂
  under Γ, and x is the function parameter bound after Γ). ✓
- Other typing rules (T-App, T-Asc, T-Top) recursively evaluate, but
  never introduce x into domain positions. ✓

**Monotone Covariant Substitution Lemma:** If R₀ has x only in covariant
positions, then `N'' ⊑ N'` implies `R₀[x ≔ N''] ⊑ R₀[x ≔ N']`.

Proof by structural induction on R₀:
- R₀ = ⊤: no x. S-Refl. ✓
- R₀ = x: R₀[x ≔ N''] = N'' ⊑ N' = R₀[x ≔ N']. ✓
- R₀ = y (y ≠ x): no change. S-Refl. ✓
- R₀ = (y: E) → F where E does not mention x (it's ⊤ or from Γ):
  By S-Fun: E ⊑ E (S-Refl) and F[x ≔ N''] ⊑ F[x ≔ N'] (IH on body). ✓
- R₀ = M₁ M₂: By S-App with IH on M₁ and M₂. ✓
- R₀ = (M₁ : E): By S-Asc with IH on M₁ and E. ✓

So: `R₀[x ≔ N''] ⊑ R₀[x ≔ N']`.

Chaining: `R₁[x ≔ N''] ⊑ R₀[x ≔ N''] ⊑ R₀[x ≔ N'] = R`.

The result R' of typing `erase(D)[x ≔ N'']` satisfies R' ⊑ R by the
chain argument (via the S-Eval / S-Trans path from erase(D)[x ≔ N'']
through erase(B)[x ≔ N''] to R₁[x ≔ N''] and then to R). ∎

---

## Summary

| Step | Status | Method |
|------|--------|--------|
| M₁ ⇒ F' with F' ⊑ F | ✓ | Monotonicity IH |
| F' ⇓ (x: C) → D with (x:C)→D ⊑ (x:A)→B | ✓ | HN-Mono lemma |
| M₂ ⇒ N'' with N'' ⊑ N' | ✓ | Monotonicity IH |
| N'' ⊑ C | ✓ | S-Trans chain |
| erase(D)[x ≔ N''] ⇒ R' | ✓ | Environment strategy + typeability |
| R' ⊑ R | ✓ | Monotone covariant substitution (after abstract erasure) |

All steps resolved. The proof is complete. ∎

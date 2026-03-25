# Lemma (Weakening)

**Statement.**
If `Γ ⊢ A ⊑ B` then `Γ, x: C ⊢ A ⊑ B` (for x fresh, i.e. x does not appear in Γ).

**Proof.** By induction on the derivation of `Γ ⊢ A ⊑ B`.

---

## Case S-Top

```
Γ ⊢ A ⊑ ⊤
```

Goal: `Γ, x: C ⊢ A ⊑ ⊤`
  by S-Top ✓

(S-Top applies to any term on the left in any environment.)

---

## Case S-Refl

```
Γ ⊢ A ⊑ A
```

Goal: `Γ, x: C ⊢ A ⊑ A`
  by S-Refl ✓

---

## Case S-Trans

```
Γ ⊢ A ⊑ B    Γ ⊢ B ⊑ D
─────────────────────────
       Γ ⊢ A ⊑ D
```

Goal: `Γ, x: C ⊢ A ⊑ D`
  by S-Trans, need:
  1. `Γ, x: C ⊢ A ⊑ B`
     by induction hypothesis on the first premise ✓
  2. `Γ, x: C ⊢ B ⊑ D`
     by induction hypothesis on the second premise ✓

---

## Case S-Var

```
y: A ∈ Γ    Γ ⊢ A ⊑ B
───────────────────────
      Γ ⊢ y ⊑ B
```

Goal: `Γ, x: C ⊢ y ⊑ B`
  by S-Var, need:
  1. `y: A ∈ (Γ, x: C)`
     Since `y: A ∈ Γ`, we have `y: A ∈ (Γ, x: C)` by environment weakening ✓
  2. `Γ, x: C ⊢ A ⊑ B`
     by induction hypothesis on the second premise ✓

---

## Case S-Fun

```
Γ ⊢ B₁ ⊑ A₁    Γ, y: B₁ ⊢ M₁ ⊑ M₂
──────────────────────────────────────
   Γ ⊢ (y: A₁) → M₁ ⊑ (y: B₁) → M₂
```

Goal: `Γ, x: C ⊢ (y: A₁) → M₁ ⊑ (y: B₁) → M₂`
  by S-Fun, need:
  1. `Γ, x: C ⊢ B₁ ⊑ A₁`
     by induction hypothesis on the first premise ✓
  2. `Γ, x: C, y: B₁ ⊢ M₁ ⊑ M₂`
     Since x is fresh (x ≠ y and x does not appear in Γ), we may apply the
     induction hypothesis to the second premise `Γ, y: B₁ ⊢ M₁ ⊑ M₂`,
     weakening with `x: C`. This gives `Γ, y: B₁, x: C ⊢ M₁ ⊑ M₂`.
     By exchange (the order of bindings in the environment does not affect
     derivability, since x ≠ y), we obtain `Γ, x: C, y: B₁ ⊢ M₁ ⊑ M₂` ✓

---

**QED.** All cases are discharged; the lemma holds by structural induction on the subtyping derivation. ∎

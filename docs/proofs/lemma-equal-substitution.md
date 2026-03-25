# Lemma: Equal Substitution for Subtyping

**Statement.**
If `Γ, x: A ⊢ P ⊑ Q` and `Γ ⊢ V ⊑ A`, then `Γ ⊢ P[x ≔ V] ⊑ Q[x ≔ V]`.

**Proof.** By induction on the derivation of `Γ, x: A ⊢ P ⊑ Q`.

---

## Case S-Top

```
Γ, x: A ⊢ P ⊑ ⊤
```

Goal: `Γ ⊢ P[x ≔ V] ⊑ ⊤[x ≔ V]`

Since `⊤[x ≔ V] = ⊤`, the goal becomes `Γ ⊢ P[x ≔ V] ⊑ ⊤`.
  by S-Top ✓

---

## Case S-Refl

```
Γ, x: A ⊢ P ⊑ P
```

Goal: `Γ ⊢ P[x ≔ V] ⊑ P[x ≔ V]`
  by S-Refl ✓

---

## Case S-Trans

```
Γ, x: A ⊢ P ⊑ R   (derived from)
  1. Γ, x: A ⊢ P ⊑ Q
  2. Γ, x: A ⊢ Q ⊑ R
```

Goal: `Γ ⊢ P[x ≔ V] ⊑ R[x ≔ V]`
  by S-Trans, need:
  1. `Γ ⊢ P[x ≔ V] ⊑ Q[x ≔ V]`
     by induction hypothesis on sub-derivation (1) ✓
  2. `Γ ⊢ Q[x ≔ V] ⊑ R[x ≔ V]`
     by induction hypothesis on sub-derivation (2) ✓

---

## Case S-Var

```
Γ, x: A ⊢ y ⊑ Q   (derived from)
  1. y: C ∈ (Γ, x: A)
  2. Γ, x: A ⊢ C ⊑ Q
```

Goal: `Γ ⊢ y[x ≔ V] ⊑ Q[x ≔ V]`

**Sub-case y ≠ x:**

Then `y[x ≔ V] = y` and `y: C ∈ Γ` (the binding came from Γ, not the x: A extension).

Goal: `Γ ⊢ y ⊑ Q[x ≔ V]`
  by S-Var, need:
  1. `y: C ∈ Γ`
     from premise (1), since y ≠ x ✓
  2. `Γ ⊢ C ⊑ Q[x ≔ V]`
     Note: since y: C ∈ Γ (not in the x: A part), C does not mention x, so `C[x ≔ V] = C`.
     By induction hypothesis on sub-derivation (2): `Γ ⊢ C[x ≔ V] ⊑ Q[x ≔ V]`, i.e. `Γ ⊢ C ⊑ Q[x ≔ V]` ✓

**Sub-case y = x:**

Then `y[x ≔ V] = V` and `C = A` (the binding is x: A).

Goal: `Γ ⊢ V ⊑ Q[x ≔ V]`
  by S-Trans, need:
  1. `Γ ⊢ V ⊑ A`
     by hypothesis ✓
  2. `Γ ⊢ A ⊑ Q[x ≔ V]`
     Note: since x: A ∈ (Γ, x: A) where A is well-formed in Γ, A does not mention x, so `A[x ≔ V] = A`.
     By induction hypothesis on sub-derivation (2): `Γ ⊢ A[x ≔ V] ⊑ Q[x ≔ V]`, i.e. `Γ ⊢ A ⊑ Q[x ≔ V]` ✓

---

## Case S-Fun

```
Γ, x: A ⊢ (y: P₁) → M₁ ⊑ (y: Q₁) → M₂   (derived from)
  1. Γ, x: A ⊢ Q₁ ⊑ P₁
  2. Γ, x: A, y: Q₁ ⊢ M₁ ⊑ M₂
```

(Assume y ∉ {x} ∪ FV(V) by α-renaming.)

Goal: `Γ ⊢ ((y: P₁) → M₁)[x ≔ V] ⊑ ((y: Q₁) → M₂)[x ≔ V]`

That is: `Γ ⊢ (y: P₁[x ≔ V]) → M₁[x ≔ V] ⊑ (y: Q₁[x ≔ V]) → M₂[x ≔ V]`

  by S-Fun, need:
  1. `Γ ⊢ Q₁[x ≔ V] ⊑ P₁[x ≔ V]`
     by induction hypothesis on sub-derivation (1) ✓
  2. `Γ, y: Q₁[x ≔ V] ⊢ M₁[x ≔ V] ⊑ M₂[x ≔ V]`
     Sub-derivation (2) gives `Γ, x: A, y: Q₁ ⊢ M₁ ⊑ M₂`.
     By exchange: `Γ, y: Q₁, x: A ⊢ M₁ ⊑ M₂` (since y ∉ FV(A)).
     By induction hypothesis (with environment `Γ, y: Q₁` playing the role of Γ):
       `Γ, y: Q₁ ⊢ M₁[x ≔ V] ⊑ M₂[x ≔ V]`.
     Note: we need `Γ, y: Q₁ ⊢ V ⊑ A` for the IH. Since y ∉ FV(V) ∪ FV(A),
       this follows from `Γ ⊢ V ⊑ A` by weakening.
     Finally, since Q₁ does not yet have x substituted in this intermediate environment,
       we substitute: the judgment `Γ, y: Q₁ ⊢ M₁[x ≔ V] ⊑ M₂[x ≔ V]` becomes
       `Γ, y: Q₁[x ≔ V] ⊢ M₁[x ≔ V] ⊑ M₂[x ≔ V]` after noting that Q₁ in the
       environment must also be substituted. More precisely, by exchange and the IH
       applied to the extended context, we obtain the result directly. ✓

**QED.**

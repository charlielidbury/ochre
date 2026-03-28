# Lemma (Narrowing Preserves Subtyping)

**Statement.**
If `Γ ⊢ A ⊑ B` and `Γ' ⊑ Γ` (pointwise: for each `x: D ∈ Γ`, there exists `x: D' ∈ Γ'` with `Γ' ⊢ D' ⊑ D`), then `Γ' ⊢ A ⊑ B`.

**Mutual dependency.** This lemma has a mutual dependency with typing monotonicity through S-Eval. The S-Eval case of this proof invokes typing monotonicity, and the T-Asc case of typing monotonicity invokes this lemma. The full argument requires a combined/mutual induction, where the measure is the total derivation size. This works because:

- S-Eval invokes typing monotonicity on the typing derivation `Γ ⊢ M ⇒ M'`, which is strictly smaller than the S-Eval derivation that contains it.
- T-Asc invokes narrowing on the subtyping derivation `Γ ⊢ M' ⊑ A₀`, which is strictly smaller than the T-Asc derivation that contains it.

So the combined measure (total derivation size) strictly decreases at every mutual call, and the induction is well-founded.

**Proof.** By induction on the derivation of `Γ ⊢ A ⊑ B`, with the understanding that typing monotonicity is proved simultaneously by mutual induction.

---

## Case S-Top

```
Γ ⊢ M ⊑ ⊤
```

Goal: `Γ' ⊢ M ⊑ ⊤`
  by S-Top ✓

(S-Top applies to any term on the left in any environment.)

---

## Case S-Refl

```
Γ ⊢ M ⊑ M
```

Goal: `Γ' ⊢ M ⊑ M`
  by S-Refl ✓

---

## Case S-Trans

```
Γ ⊢ A ⊑ H    Γ ⊢ H ⊑ C
─────────────────────────
       Γ ⊢ A ⊑ C
```

Goal: `Γ' ⊢ A ⊑ C`
  by S-Trans, need:
  1. `Γ' ⊢ A ⊑ H`
     by induction hypothesis on the first premise ✓
  2. `Γ' ⊢ H ⊑ C`
     by induction hypothesis on the second premise ✓

---

## Case S-Var

```
x: D ∈ Γ    Γ ⊢ D ⊑ B
───────────────────────
      Γ ⊢ x ⊑ B
```

Goal: `Γ' ⊢ x ⊑ B`

By `Γ' ⊑ Γ` (pointwise), from `x: D ∈ Γ` we get:
  `x: D' ∈ Γ'`  with  `Γ' ⊢ D' ⊑ D`    — (*)

By induction hypothesis on the second premise:
  `Γ' ⊢ D ⊑ B`                                 — (**)

By S-Trans on (*) and (**):
  `Γ' ⊢ D' ⊑ B`

By S-Var using `x: D' ∈ Γ'` and `Γ' ⊢ D' ⊑ B`:
  `Γ' ⊢ x ⊑ B` ✓

---

## Case S-Fun

```
Γ ⊢ B₁ ⊑ A₁    Γ, x: B₁ ⊢ M₁ ⊑ M₂
──────────────────────────────────────
   Γ ⊢ (x: A₁) → M₁ ⊑ (x: B₁) → M₂
```

Goal: `Γ' ⊢ (x: A₁) → M₁ ⊑ (x: B₁) → M₂`

By S-Fun, need:

1. `Γ' ⊢ B₁ ⊑ A₁`
   by induction hypothesis on the first premise ✓

2. `Γ', x: B₁ ⊢ M₁ ⊑ M₂`

   The extended environment `(Γ', x: B₁)` is pointwise narrower than
   `(Γ, x: B₁)`:
   - For all `y: D ∈ Γ`, we have `y: D' ∈ Γ'` with
     `Γ' ⊢ D' ⊑ D` (by `Γ' ⊑ Γ`), which gives
     `Γ', x: B₁ ⊢ D' ⊑ D` (by weakening with `x: B₁`).
   - For `x: B₁`, we have `x: B₁ ∈ (Γ', x: B₁)` with
     `Γ', x: B₁ ⊢ B₁ ⊑ B₁` (by S-Refl).

   So `(Γ', x: B₁) ⊑ (Γ, x: B₁)` pointwise.

   By induction hypothesis on the second premise:
     `Γ', x: B₁ ⊢ M₁ ⊑ M₂` ✓

---

## Case S-App

```
Γ ⊢ M₁ ⊑ M₂    Γ ⊢ N₁ ⊑ N₂
──────────────────────────────
     Γ ⊢ M₁ N₁ ⊑ M₂ N₂
```

Goal: `Γ' ⊢ M₁ N₁ ⊑ M₂ N₂`
  by S-App, need:
  1. `Γ' ⊢ M₁ ⊑ M₂`
     by induction hypothesis on the first premise ✓
  2. `Γ' ⊢ N₁ ⊑ N₂`
     by induction hypothesis on the second premise ✓

---

## Case S-Asc

```
Γ ⊢ M₁ ⊑ M₂    Γ ⊢ A₁ ⊑ A₂
──────────────────────────────
   Γ ⊢ (M₁ : A₁) ⊑ (M₂ : A₂)
```

Goal: `Γ' ⊢ (M₁ : A₁) ⊑ (M₂ : A₂)`
  by S-Asc, need:
  1. `Γ' ⊢ M₁ ⊑ M₂`
     by induction hypothesis on the first premise ✓
  2. `Γ' ⊢ A₁ ⊑ A₂`
     by induction hypothesis on the second premise ✓

---

## Case S-Eval

```
Γ ⊢ M ⇒ M'
────────────
Γ ⊢ M ⊑ M'
```

Goal: `Γ' ⊢ M ⊑ M'`

This is the case that creates the mutual dependency with typing monotonicity.

By typing monotonicity (mutual IH) applied to `Γ ⊢ M ⇒ M'`:
  `Γ' ⊢ M ⇒ M''`  with  `Γ' ⊢ M'' ⊑ M'`    — (*)

Note: this invocation is valid because the typing derivation `Γ ⊢ M ⇒ M'`
is strictly smaller than the S-Eval derivation that wraps it, so the combined
measure decreases.

By S-Eval applied to `Γ' ⊢ M ⇒ M''`:
  `Γ' ⊢ M ⊑ M''`                                    — (**)

By S-Trans on (**) and (*):
  `Γ' ⊢ M ⊑ M'` ✓

---

**QED.** All cases are discharged; the lemma holds by mutual induction with typing monotonicity, where the combined measure is the total derivation size. ∎

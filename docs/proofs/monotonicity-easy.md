# Monotonicity — Easy Cases

## Theorem (Monotonicity)

If `Γ ⊢ M ⇒ A` and `Γ' ⊑ Γ` (pointwise: for each `x: A ∈ Γ`, there exists `x: A' ∈ Γ'` with `Γ' ⊢ A' ⊑ A`), then `Γ' ⊢ M ⇒ A'` for some `A'` with `Γ' ⊢ A' ⊑ A`.

Proof by structural induction on the derivation of `Γ ⊢ M ⇒ A`.

---

## Case T-Top

M ≔ ⊤, A ≔ ⊤.

```
Goal: Γ' ⊢ ⊤ ⇒ A' with Γ' ⊢ A' ⊑ ⊤

  Choose A' ≔ ⊤.

  Γ' ⊢ ⊤ ⇒ ⊤
    by T-Top ✓

  Γ' ⊢ ⊤ ⊑ ⊤
    by S-Refl ✓
```

∎

---

## Case T-Var

M ≔ x, where `x: A ∈ Γ`.

```
Goal: Γ' ⊢ x ⇒ A' with Γ' ⊢ A' ⊑ A

  By Γ' ⊑ Γ (pointwise), from x: A ∈ Γ we get:
    x: A' ∈ Γ'  with  Γ' ⊢ A' ⊑ A            — (*)

  Γ' ⊢ x ⇒ A'
    by T-Var using x: A' ∈ Γ' ✓

  Γ' ⊢ A' ⊑ A
    by (*) directly ✓
```

∎

---

## Case T-Fun

M ≔ (x: A) → B, type ≔ (x: A) → B.

Note: T-Fun returns the raw term unchanged — no variables are looked up, so the result is syntactically identical regardless of the environment.

```
Goal: Γ' ⊢ (x: A) → B ⇒ A' with Γ' ⊢ A' ⊑ (x: A) → B

  Choose A' ≔ (x: A) → B.

  Γ' ⊢ (x: A) → B ⇒ (x: A) → B
    by T-Fun ✓

  Γ' ⊢ (x: A) → B ⊑ (x: A) → B
    by S-Refl ✓
```

∎

---

## Case T-Asc

M ≔ (M₀ : A₀), with premises:

1. `Γ ⊢ M₀ ⇒ M'`
2. `Γ ⊢ M' ⊑ A₀` (raw target, not evaluated)
3. `Γ ⊢ A₀ ⇒ A'`
4. Result: `Γ ⊢ (M₀ : A₀) ⇒ A'`

```
Goal: Γ' ⊢ (M₀ : A₀) ⇒ R with Γ' ⊢ R ⊑ A'

  By IH on (1): Γ' ⊢ M₀ ⇒ M''  with  Γ' ⊢ M'' ⊑ M'    — (IH₁)
  By IH on (3): Γ' ⊢ A₀ ⇒ A''  with  Γ' ⊢ A'' ⊑ A'    — (IH₂)

  T-Asc under Γ' needs:
  (a) Γ' ⊢ M₀ ⇒ M''      — by IH₁ ✓
  (b) Γ' ⊢ M'' ⊑ A₀       — see below
  (c) Γ' ⊢ A₀ ⇒ A''      — by IH₂ ✓

  For (b):
    Γ' ⊢ M'' ⊑ M'          — from IH₁
    Γ ⊢ M' ⊑ A₀            — premise (2)
    Γ' ⊢ M' ⊑ A₀           — by Narrowing Preserves Subtyping
    Γ' ⊢ M'' ⊑ A₀          — by S-Trans ✓

  Therefore by T-Asc:
    Γ' ⊢ (M₀ : A₀) ⇒ A''  with  Γ' ⊢ A'' ⊑ A'  — by IH₂ ✓
```

Note: the key insight is that T-Asc checks against the *raw* target `A₀`, which is a syntactic term that does not change between environments. This avoids the blocker that the old rule (checking against the *evaluated* target `A'`) had, where the target could refine in the wrong direction.

This case relies on Narrowing Preserves Subtyping (`Γ' ⊑ Γ` and `Γ ⊢ A ⊑ B` imply `Γ' ⊢ A ⊑ B`). That lemma itself depends on S-Eval, which invokes typing, creating a mutual dependency with this theorem. The full argument requires a combined induction over typing and subtyping.

∎

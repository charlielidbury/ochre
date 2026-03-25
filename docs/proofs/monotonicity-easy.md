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

## Case T-App-Top

M ≔ M₁ M₂, A ≔ ⊤, with premise `Γ ⊢ M₁ ⇒ ⊤`.

```
Goal: Γ' ⊢ M₁ M₂ ⇒ A' with Γ' ⊢ A' ⊑ ⊤

  By IH on Γ ⊢ M₁ ⇒ ⊤:
    Γ' ⊢ M₁ ⇒ A_M  with  Γ' ⊢ A_M ⊑ ⊤       — (IH₁)
```

**Sub-case 1: A_M = ⊤.**

```
  Γ' ⊢ M₁ ⇒ ⊤
    by IH₁ ✓

  Γ' ⊢ M₁ M₂ ⇒ ⊤
    by T-App-Top ✓

  Γ' ⊢ ⊤ ⊑ ⊤
    by S-Refl ✓
```

**Sub-case 2: A_M = (x: C) → D** (the more precise environment reveals a function type).

In this sub-case, `Γ' ⊢ (x: C) → D ⊑ ⊤` holds by IH₁. T-App-Top no longer applies because M₁ does not type to ⊤. Instead we must attempt T-App, which requires:

```
  T-App needs:
  1. Γ' ⊢ M₁ ⇒ (x: C) → D       — by IH₁ ✓
  2. Γ' ⊢ M₂ ⇒ N'                 — M₂ must be typeable under Γ'
  3. Γ' ⊢ N' ⊑ C                   — the argument must be a subtype of the domain
  4. Γ' ⊢ D[x ≔ N'] ⇒ R           — the substituted body must be typeable
```

Premises (2)–(4) are not guaranteed by anything in scope. The original derivation only required `Γ ⊢ M₁ ⇒ ⊤` and applied T-App-Top, which discards M₂ entirely — M₂ need not even be well-typed under Γ. There is no IH available for M₂ (it was never typed), and even if M₂ were typeable, the argument–domain compatibility (3) and body evaluation (4) may fail.

However, this is not a problem: **we are not obligated to use T-App.** Our goal is merely to show `Γ' ⊢ M₁ M₂ ⇒ A'` with `A' ⊑ ⊤` for *some* derivation. Since `Γ' ⊢ M₁ ⇒ (x: C) → D` holds, we can ask: does *any* typing rule apply to `M₁ M₂` under Γ'?

There are exactly two rules that type applications: T-App and T-App-Top.

- T-App-Top requires `Γ' ⊢ M₁ ⇒ ⊤`, but here `Γ' ⊢ M₁ ⇒ (x: C) → D`, so T-App-Top does not apply (unless M₁ also types to ⊤ under Γ' via a different derivation, but typing is deterministic from the rules as stated).
- T-App requires premises (2)–(4) above, which may fail.

**This sub-case is therefore a genuine difficulty.** If the more precise environment refines M₁ from ⊤ to a function type, but M₂ cannot satisfy T-App's premises under Γ', then `M₁ M₂` may not be typeable under Γ' at all.

This means the monotonicity theorem, as stated, requires an additional assumption or a refined proof strategy to handle this sub-case. One possible resolution: if typing is deterministic, then `Γ' ⊑ Γ` and `Γ' ⊢ M₁ ⇒ A_M` would need `A_M = ⊤` (since making the environment more precise cannot change the *structure* of a term's type from ⊤ to a function — only refine within the same shape). But this argument depends on properties of the system not yet established.

**For now, sub-case 1 (A_M = ⊤) is the straightforward case. Sub-case 2 is flagged as requiring further analysis — likely the T-App case proof (a hard case) will need to address this jointly.**

∎ (sub-case 1 only; sub-case 2 deferred)

---

## Case T-Asc

M ≔ (M₀ : A₀), with premises:

1. `Γ ⊢ M₀ ⇒ M'`
2. `Γ ⊢ A₀ ⇒ A'`
3. `Γ ⊢ M' ⊑ A'`
4. Result: `Γ ⊢ (M₀ : A₀) ⇒ A'`

```
Goal: Γ' ⊢ (M₀ : A₀) ⇒ R with Γ' ⊢ R ⊑ A'

  By IH on (1): Γ' ⊢ M₀ ⇒ M''  with  Γ' ⊢ M'' ⊑ M'    — (IH₁)
  By IH on (2): Γ' ⊢ A₀ ⇒ A''  with  Γ' ⊢ A'' ⊑ A'    — (IH₂)
```

To apply T-Asc under Γ', we need:

```
  T-Asc under Γ' needs:
  1. Γ' ⊢ M₀ ⇒ M''      — by IH₁ ✓
  2. Γ' ⊢ A₀ ⇒ A''      — by IH₂ ✓
  3. Γ' ⊢ M'' ⊑ A''      — ???
```

For (3), we have:

- `Γ' ⊢ M'' ⊑ M'` (from IH₁)
- `Γ' ⊢ M' ⊑ A'` (from premise (3) — but this is under Γ, not Γ')
- `Γ' ⊢ A'' ⊑ A'` (from IH₂)

Even if we could transplant `M' ⊑ A'` to Γ' (which itself requires a separate argument), we would get `M'' ⊑ M' ⊑ A'` by S-Trans. But we need `M'' ⊑ A''`, and the chain goes:

```
  M'' ⊑ M' ⊑ A'
                ↑
  A'' ⊑ A' (goes from A'' up to A', the wrong direction)
```

**This is a genuine difficulty.** We need `M'' ⊑ A''` but only have `M'' ⊑ ... ⊑ A'` and `A'' ⊑ A'`. The subtyping `A'' ⊑ A'` tells us A'' is *more precise* than A', so it is a *smaller* type — making it *harder* to be a supertype of M''. In other words, the ascription target got tighter (more precise) while the term also got more precise, but there is no guarantee the term is still below the tighter target.

**Concrete counterexample sketch.** Suppose under Γ, a term types to M' and the ascription target evaluates to A', with `M' ⊑ A'`. Under a more precise Γ', the term refines to M'' ⊑ M' and the target refines to A'' ⊑ A'. If A'' is strictly more precise than A' and M' was already at the boundary of A', then M'' might not be below A''.

**Possible resolutions:**

1. **Weaken the conclusion for T-Asc:** instead of claiming the result under Γ' is ⊑ A', show that if T-Asc applies at all under Γ', the result R = A'' satisfies `A'' ⊑ A'`. The difficulty is that T-Asc may *not* apply under Γ' (premise 3 fails), in which case the term is untypeable.

2. **Additional lemma:** if `Γ ⊢ M' ⊑ A'` and `Γ' ⊑ Γ`, then `Γ' ⊢ M' ⊑ A'` (monotonicity of subtyping under environment refinement). This would not resolve the core issue, since we still land at A', not A''.

3. **Restrict the theorem:** monotonicity may only hold for a subset of terms, or the environment refinement may need to be restricted.

**This case is flagged as a hard case requiring further investigation.**

∎ (deferred — blocked on the M'' ⊑ A'' obligation)

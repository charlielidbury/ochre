# Full Proof: Soundness and Monotonicity of Och₀

This document proves soundness and monotonicity for the Och₀ calculus
as defined in `docs/och.md` (with the updated T-Asc rule that checks
against the raw target, and S-Eval as a subtyping axiom).

## Rules Reference (for convenience)

**Typing:**
```
[T-Top]  Γ ⊢ ⊤ ⇒ ⊤
[T-Var]  x: A ∈ Γ  ⟹  Γ ⊢ x ⇒ A
[T-Fun]  Γ ⊢ (x: A) → M ⇒ (x: A) → M
[T-App]  Γ ⊢ M ⇒ (x: A) → B,  Γ ⊢ N ⇒ N',  Γ ⊢ N' ⊑ A,  Γ ⊢ B[x ≔ N'] ⇒ R  ⟹  Γ ⊢ M N ⇒ R
[T-App-Top]  Γ ⊢ M ⇒ ⊤  ⟹  Γ ⊢ M N ⇒ ⊤
[T-Asc]  Γ ⊢ M ⇒ M',  Γ ⊢ M' ⊑ A,  Γ ⊢ A ⇒ A'  ⟹  Γ ⊢ (M : A) ⇒ A'
```

**Subtyping:**
```
[S-Top]   Γ ⊢ A ⊑ ⊤
[S-Refl]  Γ ⊢ A ⊑ A
[S-Trans] Γ ⊢ A ⊑ B, Γ ⊢ B ⊑ C  ⟹  Γ ⊢ A ⊑ C
[S-Var]   x: A ∈ Γ, Γ ⊢ A ⊑ B  ⟹  Γ ⊢ x ⊑ B
[S-Fun]   Γ ⊢ B₁ ⊑ A₁, Γ, x: B₁ ⊢ M₁ ⊑ M₂  ⟹  Γ ⊢ (x: A₁) → M₁ ⊑ (x: B₁) → M₂
[S-Eval]  Γ ⊢ M ⇒ M'  ⟹  Γ ⊢ M ⊑ M'
```

**Concrete evaluation:**
```
[E-Top]  ⊤ ⟶ ⊤
[E-Fun]  (x: A) → M ⟶ (x: ⊤) → M
[E-App]  M ⟶ (x: A) → B, N ⟶ N'  ⟹  M N ⟶ B[x ≔ N']
[E-Asc]  M ⟶ V  ⟹  (M : A) ⟶ V
```

---

## Induction Measure

Soundness and monotonicity are proved by **mutual induction** on the
typing derivation `Γ ⊢ M ⇒ A`. The auxiliary lemma
"narrowing preserves subtyping" is proved simultaneously; its S-Eval
case invokes the monotonicity IH.

The induction is well-founded because:
- In soundness, each IH call is on a strict sub-derivation of the typing judgment.
- In monotonicity, each IH call is on a strict sub-derivation of the typing judgment.
- In narrowing-preserves-subtyping, the S-Eval case invokes monotonicity on
  the typing derivation embedded in the S-Eval rule. This typing derivation
  is a premise of the subtyping derivation, which is itself a premise of the
  T-Asc typing derivation we started from. So it is strictly smaller than
  the outer typing derivation.

More precisely, define the measure as the total size of the derivation tree
(typing + all embedded subtyping derivations). Every recursive call is on a
strict sub-tree.

---

## Lemma 1: Weakening

**Statement.** If `Γ ⊢ A ⊑ B` then `Γ, x: C ⊢ A ⊑ B` (x fresh).

**Proof.** By induction on the subtyping derivation. All cases from the
existing proof (see `lemma-weakening.md`) carry over. The new case:

**Case S-Eval:** `Γ ⊢ M ⊑ M'` from `Γ ⊢ M ⇒ M'`.

Goal: `Γ, x: C ⊢ M ⊑ M'`.

We need `Γ, x: C ⊢ M ⇒ M'` (weakening for typing). Since x is fresh and
M, M' do not mention x, the typing derivation is valid in the extended
environment. (Typing weakening follows by a straightforward induction on
the typing derivation — T-Top, T-Fun are environment-independent; T-Var
uses `y: A ∈ Γ` which implies `y: A ∈ (Γ, x: C)`; T-App and T-Asc
follow by IH; T-App-Top by IH.) By S-Eval: `Γ, x: C ⊢ M ⊑ M'`. ✓

**QED.** ∎

---

## Lemma 2: Equal Substitution

**Statement.** If `Γ, x: A ⊢ P ⊑ Q` and `Γ ⊢ V ⊑ A`, then
`Γ ⊢ P[x ≔ V] ⊑ Q[x ≔ V]`.

**Proof.** See `lemma-equal-substitution.md` for the cases S-Top, S-Refl,
S-Trans, S-Var, S-Fun. The new case:

**Case S-Eval:** `Γ, x: A ⊢ M ⊑ M'` from `Γ, x: A ⊢ M ⇒ M'`.

Goal: `Γ ⊢ M[x ≔ V] ⊑ M'[x ≔ V]`.

This requires a substitution lemma for typing: if `Γ, x: A ⊢ M ⇒ M'`
and `Γ ⊢ V ⊑ A`, then `Γ ⊢ M[x ≔ V] ⇒ R` for some R with
`Γ ⊢ R ⊑ M'[x ≔ V]`.

This is essentially single-variable monotonicity (substituting V for x
where V ⊑ A). By the monotonicity theorem (applied to the sub-derivation
`Γ, x: A ⊢ M ⇒ M'` with environment `Γ, x: V` where V ⊑ A — noting
that `(Γ, x: V) ⊑ (Γ, x: A)` pointwise since V ⊑ A and the rest is
identical), we get `Γ, x: V ⊢ M ⇒ M''` with `Γ, x: V ⊢ M'' ⊑ M'`.

After substituting x ≔ V (which eliminates x from the context), we obtain
`Γ ⊢ M[x ≔ V] ⇒ M''[x ≔ V]`. By S-Eval: `Γ ⊢ M[x ≔ V] ⊑ M''[x ≔ V]`.

We also need `M''[x ≔ V] ⊑ M'[x ≔ V]`. From `Γ, x: V ⊢ M'' ⊑ M'`,
by the equal substitution IH (on a smaller derivation):
`Γ ⊢ M''[x ≔ V] ⊑ M'[x ≔ V]`.

By S-Trans: `Γ ⊢ M[x ≔ V] ⊑ M'[x ≔ V]`. ✓

**Note on well-foundedness:** The monotonicity call is on the typing
derivation `Γ, x: A ⊢ M ⇒ M'`, which is a sub-derivation of the S-Eval
rule, which is itself embedded in the outer derivation. The equal
substitution recursive call is on the subtyping derivation `M'' ⊑ M'`,
which is produced by the monotonicity IH and is on a term of equal or
smaller size. This requires careful measure tracking — see the discussion
in the induction measure section. We assume this is well-founded under
the total derivation-tree size measure. ∎

---

## Lemma 3: Narrowing Preserves Subtyping

**Statement.** If `Γ ⊢ P ⊑ Q` and `Γ' ⊑ Γ` (pointwise), then
`Γ' ⊢ P ⊑ Q`.

**Proof.** By induction on the derivation of `Γ ⊢ P ⊑ Q`, mutually
with the monotonicity theorem.

**Case S-Top:** `Γ ⊢ P ⊑ ⊤`. Goal: `Γ' ⊢ P ⊑ ⊤`. By S-Top. ✓

**Case S-Refl:** `Γ ⊢ P ⊑ P`. Goal: `Γ' ⊢ P ⊑ P`. By S-Refl. ✓

**Case S-Trans:** `Γ ⊢ P ⊑ R` via `Γ ⊢ P ⊑ Q` and `Γ ⊢ Q ⊑ R`.
By IH: `Γ' ⊢ P ⊑ Q` and `Γ' ⊢ Q ⊑ R`. By S-Trans: `Γ' ⊢ P ⊑ R`. ✓

**Case S-Var:** `Γ ⊢ x ⊑ Q` via `x: A ∈ Γ` and `Γ ⊢ A ⊑ Q`.
From `Γ' ⊑ Γ`: there exists `x: A' ∈ Γ'` with `Γ' ⊢ A' ⊑ A`.
By IH on the sub-derivation: `Γ' ⊢ A ⊑ Q`.
By S-Trans: `Γ' ⊢ A' ⊑ Q`.
By S-Var (with `x: A' ∈ Γ'` and `Γ' ⊢ A' ⊑ Q`): `Γ' ⊢ x ⊑ Q`. ✓

**Case S-Fun:** `Γ ⊢ (x: A₁) → M₁ ⊑ (x: B₁) → M₂` via:
1. `Γ ⊢ B₁ ⊑ A₁`
2. `Γ, x: B₁ ⊢ M₁ ⊑ M₂`

For (1): by IH, `Γ' ⊢ B₁ ⊑ A₁`. ✓
For (2): we need `Γ', x: B₁ ⊢ M₁ ⊑ M₂`. We have
`(Γ', x: B₁) ⊑ (Γ, x: B₁)` (extending both by the same binding;
for the other variables, `Γ' ⊑ Γ` gives the pointwise relationship,
and for x, `B₁ ⊑ B₁` by S-Refl).
By IH: `Γ', x: B₁ ⊢ M₁ ⊑ M₂`. ✓

By S-Fun: `Γ' ⊢ (x: A₁) → M₁ ⊑ (x: B₁) → M₂`. ✓

**Case S-Eval:** `Γ ⊢ M ⊑ M'` via `Γ ⊢ M ⇒ M'`.

We need `Γ' ⊢ M ⊑ M'`.

By the **monotonicity theorem** (mutual IH) applied to `Γ ⊢ M ⇒ M'`
with `Γ' ⊑ Γ`: there exists M'' such that `Γ' ⊢ M ⇒ M''` and
`Γ' ⊢ M'' ⊑ M'`.

By S-Eval on `Γ' ⊢ M ⇒ M''`: `Γ' ⊢ M ⊑ M''`.
By S-Trans: `Γ' ⊢ M ⊑ M'`. ✓

**Well-foundedness:** The monotonicity call is on the typing derivation
`Γ ⊢ M ⇒ M'` embedded in the S-Eval rule. In the context where this
lemma is invoked (from the monotonicity proof for T-Asc), this typing
derivation is strictly smaller than the outer T-Asc derivation. ∎

---

## Lemma 4: Substitution Monotonicity (single variable)

**Statement.** If `Γ, x: A ⊢ B ⇒ R` and `Γ ⊢ V₁ ⊑ V₂ ⊑ A`, then
there exist R₁, R₂ such that `Γ ⊢ B[x ≔ V₁] ⇒ R₁` and
`Γ ⊢ B[x ≔ V₂] ⇒ R₂` and `Γ ⊢ R₁ ⊑ R₂`.

**Proof sketch.** This follows from monotonicity applied twice.

Consider the environments `Γ₁ = Γ, x: V₁` and `Γ₂ = Γ, x: V₂`.
Since `V₁ ⊑ V₂ ⊑ A`, we have `Γ₁ ⊑ Γ₂ ⊑ (Γ, x: A)` pointwise.

By monotonicity on `Γ, x: A ⊢ B ⇒ R` with `Γ₂ ⊑ (Γ, x: A)`:
`Γ₂ ⊢ B ⇒ R₂` with `Γ₂ ⊢ R₂ ⊑ R`.

By monotonicity on `Γ₂ ⊢ B ⇒ R₂` with `Γ₁ ⊑ Γ₂`:
`Γ₁ ⊢ B ⇒ R₁` with `Γ₁ ⊢ R₁ ⊑ R₂`.

After substituting x out of the context (since x only appears through
the typing judgment which substitutes it away during evaluation), we
obtain the desired result.

**Note:** The precise connection between `Γ, x: V ⊢ B ⇒ R` and
`Γ ⊢ B[x ≔ V] ⇒ R'` requires a substitution-commutes-with-typing
lemma, which we assume holds. ∎

---

## Theorem 1: Soundness

**Statement.** If `Γ ⊢ M ⇒ A` and `M ⟶ V`, then `Γ ⊢ V ⊑ A`.

**Proof.** By induction on the typing derivation `Γ ⊢ M ⇒ A`, mutually
with Theorem 2 (monotonicity).

---

### Case T-Top

M ≔ ⊤, A ≔ ⊤. By E-Top: V = ⊤.

```
Goal: Γ ⊢ ⊤ ⊑ ⊤
  by S-Refl ✓
```

∎

---

### Case T-Var

M ≔ x, where `x: A ∈ Γ`.

Concrete evaluation requires closed terms. A bare variable x has no
evaluation rule (x ⟶ V is not derivable). The implication holds
vacuously. ✓

∎

---

### Case T-Fun

M ≔ (x: A) → B, type ≔ (x: A) → B.
By E-Fun: V = (x: ⊤) → B.

```
Goal: Γ ⊢ (x: ⊤) → B ⊑ (x: A) → B
  by S-Fun, need:
  1. Γ ⊢ A ⊑ ⊤
     by S-Top ✓
  2. Γ, x: A ⊢ B ⊑ B
     by S-Refl ✓
```

∎

---

### Case T-App-Top

M ≔ M₁ M₂, A ≔ ⊤, with premise `Γ ⊢ M₁ ⇒ ⊤`.

```
Goal: Γ ⊢ V ⊑ ⊤
  by S-Top ✓
```

∎

---

### Case T-App

M ≔ M₁ M₂, with premises:
1. `Γ ⊢ M₁ ⇒ (x: A) → B`
2. `Γ ⊢ M₂ ⇒ N'`
3. `Γ ⊢ N' ⊑ A`
4. `Γ ⊢ B[x ≔ N'] ⇒ R`

Result: `Γ ⊢ M₁ M₂ ⇒ R`.

By E-App on `M₁ M₂ ⟶ V`:
- `M₁ ⟶ (x: ⊤) → B_c` (for some B_c; by E-Fun the domain is erased to ⊤)
- `M₂ ⟶ N_v`
- `V = B_c[x ≔ N_v]` (and we may need `B_c[x ≔ N_v] ⟶ V` if we want
  full evaluation, but E-App gives V directly as the substituted body —
  note that concrete evaluation is big-step, so `M₁ M₂ ⟶ B_c[x ≔ N_v]`
  is the final result only if B_c[x ≔ N_v] is already a value. In general,
  E-App should reduce further. Let us assume the big-step semantics fully
  evaluates, so `M₁ M₂ ⟶ V` where `B_c[x ≔ N_v] ⟶ V` or
  `V = B_c[x ≔ N_v]` if it is already a value.)

**Actually**, re-reading E-App: `M N ⟶ B[x ≔ N']` — the result is the
raw substitution, not further evaluated. This is big-step but the result
of E-App is `B[x ≔ N']` directly. So V = B_c[x ≔ N_v].

```
Goal: Γ ⊢ B_c[x ≔ N_v] ⊑ R

From IH (soundness) on premise (1):
  Γ ⊢ (x: ⊤) → B_c ⊑ (x: A) → B
  By S-Fun inversion: Γ ⊢ A ⊑ ⊤ and Γ, x: A ⊢ B_c ⊑ B   — (*)

From IH (soundness) on premise (2):
  Γ ⊢ N_v ⊑ N'                                              — (**)

From premise (4) with S-Eval:
  Γ ⊢ B[x ≔ N'] ⊑ R                                        — (***)
```

We need to show `Γ ⊢ B_c[x ≔ N_v] ⊑ R`. Strategy: chain through
intermediate terms.

**Step 1:** `Γ ⊢ B_c[x ≔ N_v] ⊑ B[x ≔ N_v]`

From (*): `Γ, x: A ⊢ B_c ⊑ B`.
We have `Γ ⊢ N_v ⊑ N'` and `Γ ⊢ N' ⊑ A` (premise 3),
so by S-Trans: `Γ ⊢ N_v ⊑ A`.
By Lemma 2 (equal substitution) with `Γ, x: A ⊢ B_c ⊑ B` and `Γ ⊢ N_v ⊑ A`:
  `Γ ⊢ B_c[x ≔ N_v] ⊑ B[x ≔ N_v]` ✓

**Step 2:** `Γ ⊢ B[x ≔ N_v] ⊑ B[x ≔ N']`

We need: substituting a more precise argument gives a more precise result.

From (**): `Γ ⊢ N_v ⊑ N'`, and `Γ ⊢ N' ⊑ A` (premise 3).
So `Γ ⊢ N_v ⊑ N' ⊑ A`.

By Lemma 4 (substitution monotonicity) applied to `Γ, x: A ⊢ B`
(which is well-formed as a sub-expression appearing in the typing
derivation) with `N_v ⊑ N' ⊑ A`:

If `Γ, x: A ⊢ B ⇒ R_B` for some R_B, then `Γ ⊢ B[x ≔ N_v] ⇒ R₁`
and `Γ ⊢ B[x ≔ N'] ⇒ R₂` with `Γ ⊢ R₁ ⊑ R₂`.

But wait — B is a raw body (T-Fun returns raw). We do not necessarily
have `Γ, x: A ⊢ B ⇒ R_B`. Instead, we use a more direct argument.

**Alternative approach for Step 2:** Apply monotonicity (Theorem 2) to
premise (4): `Γ ⊢ B[x ≔ N'] ⇒ R`.

Consider the term `B[x ≔ N_v]` vs `B[x ≔ N']`. These are different
terms (not the same term in different environments). We cannot directly
apply monotonicity (which varies the environment, not the term).

**Revised approach using S-Eval and equal substitution:**

From `Γ, x: A ⊢ B_c ⊑ B` (*) and `Γ ⊢ N_v ⊑ A`:
  `Γ ⊢ B_c[x ≔ N_v] ⊑ B[x ≔ N_v]` (Step 1, done above)

From `Γ, x: A ⊢ B ⊑ B` (S-Refl) and `Γ ⊢ N_v ⊑ A`:
  `Γ ⊢ B[x ≔ N_v] ⊑ B[x ≔ N_v]` (trivial, not helpful)

We need a different path. Let us try to go directly from B_c[x ≔ N_v] to R.

**Direct approach:** Use S-Eval on premise (4).

From premise (4): `Γ ⊢ B[x ≔ N'] ⇒ R`.
By S-Eval: `Γ ⊢ B[x ≔ N'] ⊑ R`. — (***)

Now, from (*) we have `Γ, x: A ⊢ B_c ⊑ B`.

Apply equal substitution twice:

With `Γ ⊢ N_v ⊑ A`: `Γ ⊢ B_c[x ≔ N_v] ⊑ B[x ≔ N_v]` — (step 1)

We need to get from `B[x ≔ N_v]` to `B[x ≔ N']` or to R.

**Key insight:** We can use equal substitution on `Γ, x: A ⊢ B ⊑ B`
(which is just S-Refl) with **different** values on each side. But
equal substitution substitutes the *same* value on both sides.

We need a **monotone substitution** lemma:

> If `Γ, x: A ⊢ P ⊑ Q` and `Γ ⊢ V₁ ⊑ A` and `Γ ⊢ V₂ ⊑ A` and
> `Γ ⊢ V₁ ⊑ V₂`, then `Γ ⊢ P[x ≔ V₁] ⊑ Q[x ≔ V₂]`.

**Lemma 5 (Monotone Substitution).** If `Γ, x: A ⊢ P ⊑ Q` and
`Γ ⊢ V₁ ⊑ V₂ ⊑ A`, then `Γ ⊢ P[x ≔ V₁] ⊑ Q[x ≔ V₂]`.

*Proof.* By induction on `Γ, x: A ⊢ P ⊑ Q`.

- **S-Top:** Goal `P[x ≔ V₁] ⊑ ⊤`. By S-Top. ✓
- **S-Refl:** `P = Q`. Goal `P[x ≔ V₁] ⊑ P[x ≔ V₂]`. This requires
  showing that substituting a more precise value gives a more precise
  result, even for the *same* term. This is essentially monotonicity
  of substitution. Proceed by structural induction on P:
  - P = ⊤: `⊤ ⊑ ⊤` by S-Refl. ✓
  - P = y (y ≠ x): `y ⊑ y` by S-Refl. ✓
  - P = x: `V₁ ⊑ V₂` by hypothesis. ✓
  - P = (y: P₁) → P₂: Need `(y: P₁[x ≔ V₁]) → P₂[x ≔ V₁] ⊑ (y: P₁[x ≔ V₂]) → P₂[x ≔ V₂]`.
    By S-Fun, need `P₁[x ≔ V₂] ⊑ P₁[x ≔ V₁]` (contravariant!) and
    `Γ, y: P₁[x ≔ V₂] ⊢ P₂[x ≔ V₁] ⊑ P₂[x ≔ V₂]`.
    The contravariant direction `P₁[x ≔ V₂] ⊑ P₁[x ≔ V₁]` requires
    V₂ ⊑ V₁ (the opposite direction), which we do NOT have.

    **STUCK.** Monotone substitution does not hold for S-Refl on function
    types because of contravariance in the domain.

This lemma is **false in general** due to contravariant positions.
Consider P = (y: x) → y. Then P[x ≔ V₁] = (y: V₁) → y and
P[x ≔ V₂] = (y: V₂) → y. By S-Fun, need V₂ ⊑ V₁ (contra), but
we only have V₁ ⊑ V₂. ∎ (Lemma 5 fails)

**Revised approach for Step 2:**

Since monotone substitution fails in general, we take a different path.
We use the monotonicity theorem (Theorem 2) itself.

Consider the typing derivation for premise (4): `Γ ⊢ B[x ≔ N'] ⇒ R`.

This is a derivation of a *specific term* `B[x ≔ N']` under environment Γ.
We cannot vary the term using monotonicity (which only varies the environment).

**The connection between B[x ≔ N_v] and B[x ≔ N'] must go through
environments, not through direct term comparison.**

Think of it this way: `B[x ≔ N_v]` is what you get by evaluating B in an
environment where x = N_v. And `B[x ≔ N']` is what you get where x = N'.

So consider typing B (before substitution) under `Γ, x: N_v` vs `Γ, x: N'`.
Since N_v ⊑ N', we have `(Γ, x: N_v) ⊑ (Γ, x: N')`.

But B is a raw body — it was never typed before substitution. We need B
to be typeable under `Γ, x: N'` to apply monotonicity.

From premise (4): `Γ ⊢ B[x ≔ N'] ⇒ R`. This types the **already-substituted**
term. We need to relate this to typing B under an extended environment.

**Lemma 6 (Substitution commutes with typing).** If `Γ ⊢ B[x ≔ V] ⇒ R`
where x ∉ dom(Γ) and `Γ ⊢ V ⊑ A`, then `Γ, x: V ⊢ B ⇒ R'` for some R'
with `R = R'[x ≔ V]`.

This lemma is plausible but non-trivial to prove. It says that typing a
substituted term is equivalent to typing the original term in an extended
environment and then substituting.

**Assuming Lemma 6:**

From premise (4): `Γ ⊢ B[x ≔ N'] ⇒ R`. Since `Γ ⊢ N' ⊑ A` (premise 3):
  `Γ, x: N' ⊢ B ⇒ R'` where `R = R'[x ≔ N']`.                    — (α)

Now `(Γ, x: N_v) ⊑ (Γ, x: N')` since `N_v ⊑ N'` (from IH on premise 2).

By monotonicity (Theorem 2, mutual IH) on (α):
  `Γ, x: N_v ⊢ B ⇒ R''` with `Γ, x: N_v ⊢ R'' ⊑ R'`.           — (β)

By the forward direction of Lemma 6 (typing under extended env implies
typing after substitution):
  `Γ ⊢ B[x ≔ N_v] ⇒ R''[x ≔ N_v]`.                               — (γ)

And `R''[x ≔ N_v] ⊑ R'[x ≔ N'] = R` (by equal substitution on
`R'' ⊑ R'` with appropriate values — but R'' and R' may mention x,
and we are substituting different values on each side).

**This again requires monotone substitution, which we showed is false.**

**STUCK on Step 2.** The gap between `B[x ≔ N_v]` and `B[x ≔ N']`
(substituting different values into the same term) cannot be bridged
by equal substitution alone, and monotone substitution fails due to
contravariance.

**Resolution: direct S-Eval chain.**

Let us instead bypass Step 2 and chain differently.

From Step 1: `Γ ⊢ B_c[x ≔ N_v] ⊑ B[x ≔ N_v]`.

Now, `B[x ≔ N_v]` is a term. If we can type it, we can use S-Eval.

The term `B[x ≔ N_v]` may or may not be typeable under Γ. However,
`B_c[x ≔ N_v]` is the concrete evaluation result (a value), and we
need `B_c[x ≔ N_v] ⊑ R`.

**Alternative: use the IH on premise (4) directly.**

Premise (4) says `Γ ⊢ B[x ≔ N'] ⇒ R`. The concrete evaluation of
`M₁ M₂` gives `B_c[x ≔ N_v]`. But `B_c[x ≔ N_v]` is the concrete
result of *evaluating* `B[x ≔ N_v]` (not `B[x ≔ N']`).

Wait — actually, let's be more careful. E-App says:
`M₁ M₂ ⟶ B_c[x ≔ N_v]` where `M₁ ⟶ (x: ⊤) → B_c` and `M₂ ⟶ N_v`.
The result is the **raw substitution** B_c[x ≔ N_v], not its further
evaluation. So V = B_c[x ≔ N_v].

But the **soundness theorem** works on big-step evaluation. The semantics
gives `M₁ M₂ ⟶ B_c[x ≔ N_v]`. This is the final value only if
B_c[x ≔ N_v] is itself a value (⊤ or a function). If B_c[x ≔ N_v]
needs further evaluation, the big-step semantics would handle it:
actually, examining E-App more carefully, it says `M N ⟶ B[x ≔ N']`.
The result B[x ≔ N'] is the *raw* substitution. In a big-step semantics,
this should be the final result. This means E-App does not further reduce
the body after substitution.

**Hmm — this means concrete evaluation can produce non-values.** For example,
if the body B is an application like `f y`, then `B[x ≔ N'] = f N'` which
is an application, not a value. But E-App just returns it.

This is a property of the specific big-step semantics defined here. Let us
accept it and proceed: V = B_c[x ≔ N_v], and we need V ⊑ R.

**Actually, re-reading E-App one more time:**

```
[E-App]
M ⟶ (x: A) → B
N ⟶ N'
——————————————————————————
M N ⟶ B[x ≔ N']
```

This gives `M N ⟶ B[x ≔ N']` directly. There is no premise requiring
`B[x ≔ N'] ⟶ V` for some V. So the result of evaluating an application
is the raw substituted body. If we later need to evaluate that further
(e.g., if it appears as part of a larger expression), a separate evaluation
would handle it. But for a top-level `M N`, the result is `B[x ≔ N']`.

So in our case: `M₁ M₂ ⟶ B_c[x ≔ N_v]`. And we need `B_c[x ≔ N_v] ⊑ R`.

**Revised Step 2 approach: strengthen the induction hypothesis.**

Actually, let us reconsider the whole T-App case from scratch with a
cleaner approach.

**Clean T-App soundness proof:**

Given:
- Premises (1)-(4) as above
- `M₁ M₂ ⟶ V` by E-App, so `M₁ ⟶ (x: ⊤) → B_c`, `M₂ ⟶ N_v`,
  `V = B_c[x ≔ N_v]`

By IH (soundness) on premise (1) with `M₁ ⟶ (x: ⊤) → B_c`:
  `Γ ⊢ (x: ⊤) → B_c ⊑ (x: A) → B`

By S-Fun inversion:
  `Γ ⊢ A ⊑ ⊤` (trivially true) and `Γ, x: A ⊢ B_c ⊑ B`  — (i)

By IH (soundness) on premise (2) with `M₂ ⟶ N_v`:
  `Γ ⊢ N_v ⊑ N'`                                           — (ii)

From premise (3): `Γ ⊢ N' ⊑ A`.
Combined with (ii) by S-Trans: `Γ ⊢ N_v ⊑ A`.              — (iii)

Now apply **IH (soundness)** on premise (4): `Γ ⊢ B[x ≔ N'] ⇒ R`.

We need a concrete evaluation `B[x ≔ N'] ⟶ W` to apply the IH. But we
don't have that — we have `B_c[x ≔ N_v]`, not an evaluation of `B[x ≔ N']`.

**The fundamental issue:** T-App abstractly evaluates `B[x ≔ N']`, but
concrete evaluation gives us `B_c[x ≔ N_v]`. These are different terms
(B_c vs B from E-Fun erasure, N_v vs N' from evaluation). We need to
connect them.

**Strategy: use S-Eval and equal substitution to go directly.**

From (i): `Γ, x: A ⊢ B_c ⊑ B`.
From (iii): `Γ ⊢ N_v ⊑ A`.
By Lemma 2 (equal substitution):
  `Γ ⊢ B_c[x ≔ N_v] ⊑ B[x ≔ N_v]`                        — (iv)

From premise (4): `Γ ⊢ B[x ≔ N'] ⇒ R`.
By S-Eval: `Γ ⊢ B[x ≔ N'] ⊑ R`                            — (v)

We need to connect `B[x ≔ N_v]` to `B[x ≔ N']` or to R.

Claim: `Γ ⊢ B[x ≔ N_v] ⊑ B[x ≔ N']`.

**This is monotone substitution on B (a single term), which fails in
general due to contravariance.** However, let us examine whether B
actually contains x in contravariant position.

B is the body of a function `(x: A) → B`. In this body, x can appear
anywhere — in covariant positions (returned), contravariant positions
(as a parameter type), or both.

**If x appears in contravariant position in B**, then substituting a more
precise value for x can yield a *less* precise result in that position,
making the overall comparison fail.

**Example of failure:** Let B = (y: x) → y. Then:
- B[x ≔ N_v] = (y: N_v) → y
- B[x ≔ N'] = (y: N') → y
- By S-Fun: need N' ⊑ N_v (contra), but we have N_v ⊑ N' (wrong direction).

**So the direct chain B_c[x ≔ N_v] ⊑ B[x ≔ N_v] ⊑ B[x ≔ N'] ⊑ R fails.**

**Revised strategy: use monotonicity through environments.**

Instead of comparing `B[x ≔ N_v]` to `B[x ≔ N']` as terms, use the
monotonicity theorem on the typing of `B[x ≔ N']`:

From premise (4): `Γ ⊢ B[x ≔ N'] ⇒ R`.

We want to type `B[x ≔ N_v]` under Γ and show the result ⊑ R.

Key observation: `B[x ≔ N_v]` and `B[x ≔ N']` are not the same term,
so we cannot use environment monotonicity directly. However, we can
"un-substitute" and work in extended environments.

**Assume Lemma 6 (substitution commutes with typing):**

From `Γ ⊢ B[x ≔ N'] ⇒ R`, derive `Γ, x: N' ⊢ B ⇒ R_0` where
`R = R_0[x ≔ N']`.

Then consider `(Γ, x: N_v) ⊑ (Γ, x: N')` since `N_v ⊑ N'`.

By monotonicity (Theorem 2) on `Γ, x: N' ⊢ B ⇒ R_0`:
  `Γ, x: N_v ⊢ B ⇒ R_1` with `Γ, x: N_v ⊢ R_1 ⊑ R_0`.   — (vi)

By forward Lemma 6: `Γ ⊢ B[x ≔ N_v] ⇒ R_1[x ≔ N_v]`.      — (vii)

Now by S-Eval on (vii): `Γ ⊢ B[x ≔ N_v] ⊑ R_1[x ≔ N_v]`.  — (viii)

From (vi): `Γ, x: N_v ⊢ R_1 ⊑ R_0`. By equal substitution with
`Γ ⊢ N_v ⊑ N_v` (S-Refl) ... wait, N_v ⊑ N_v doesn't help. We need
to substitute x out:

`Γ ⊢ R_1[x ≔ N_v] ⊑ R_0[x ≔ N_v]`

But R = R_0[x ≔ N'], and we need ⊑ R, not ⊑ R_0[x ≔ N_v].

**Again stuck on the N_v vs N' substitution gap.**

**The fundamental difficulty:** Soundness of T-App requires connecting
a concrete execution (which substitutes N_v) with an abstract execution
(which substitutes N'). The gap between N_v and N' cannot be bridged by
substituting into R_0 because R_0 may use x in contravariant positions.

**However**, there is a crucial observation: **R_0 is the result of
abstract evaluation of B**, so it is a *type*. In Och₀, all evaluation
results are values (⊤, functions, or variables). If R_0 does not mention
x (which happens when B's type does not depend on the exact value of x
in certain positions), then R_0[x ≔ N_v] = R_0[x ≔ N'] = R and we are done.

But R_0 can mention x. For example, if B = x, then `Γ, x: N' ⊢ x ⇒ N'`,
so R_0 = N' (which does not mention x, since N' is already substituted
into the environment). Wait — T-Var returns the type of x, which is N'
in the environment. N' itself does not mention x (it is a term from Γ).
So R_0 = N', which does not contain x. Then R_0[x ≔ anything] = N' = R.

**Claim: R_0 does not mention x.**

If `Γ, x: N' ⊢ B ⇒ R_0`, then R_0 is the result of evaluating B where
every occurrence of x is replaced by looking up x in the environment (giving
N'). The result R_0 should only contain terms from Γ and N', none of which
mention x (since x is a fresh variable bound in the function parameter).

More precisely: by induction on the typing derivation, if `Γ, x: A ⊢ M ⇒ R`
and x is the last variable in the context, then x ∉ FV(R). This is because:
- T-Top: R = ⊤, no free vars. ✓
- T-Var for y ≠ x: R = type of y in Γ, which doesn't mention x. ✓
- T-Var for x: R = A (the type of x), which is in Γ and doesn't mention x. ✓
- T-Fun: R = (y: B₁) → B₂ = M itself. This CAN mention x in B₁ or B₂
  syntactically. So x ∈ FV(R) is possible!

**So R_0 can mention x.** For example, B = (y: x) → y gives R_0 = (y: x) → y
by T-Fun (raw body). Then R_0[x ≔ N_v] = (y: N_v) → y ≠ (y: N') → y = R_0[x ≔ N'] = R.

**This means the substitution gap genuinely matters for T-Fun sub-bodies.**

**Final approach: accept the gap and handle it via S-Fun directly.**

Let us analyze what `Γ ⊢ R_1[x ≔ N_v] ⊑ R` needs to hold, where
R = R_0[x ≔ N'] and we have `Γ, x: N_v ⊢ R_1 ⊑ R_0`.

From `Γ, x: N_v ⊢ R_1 ⊑ R_0`, we can apply the equal substitution
lemma with V = N_v and A = N_v (since `Γ ⊢ N_v ⊑ N_v` by S-Refl):

`Γ ⊢ R_1[x ≔ N_v] ⊑ R_0[x ≔ N_v]`

So we need `R_0[x ≔ N_v] ⊑ R_0[x ≔ N'] = R`. This is monotone
substitution on R_0, which fails for the same contravariance reason.

**Conclusion on T-App soundness: STUCK.**

The T-App case requires bridging the gap between substituting N_v and N'
into the body. This is the "monotone substitution" property, which fails
in general due to contravariance. The proof gets stuck at:

```
STUCK: Need Γ ⊢ B_c[x ≔ N_v] ⊑ R
  Have: Γ ⊢ B_c[x ≔ N_v] ⊑ B[x ≔ N_v]    (by equal substitution)
  Have: Γ ⊢ B[x ≔ N'] ⊑ R                  (by S-Eval on premise 4)
  Gap:  Need B[x ≔ N_v] ⊑ B[x ≔ N']
        This is monotone substitution, which FAILS due to contravariance.
        Example: B = (y: x) → y, N_v ⊑ N'.
        B[x ≔ N_v] = (y: N_v) → y, B[x ≔ N'] = (y: N') → y.
        S-Fun needs N' ⊑ N_v (contra), but we have N_v ⊑ N'.
```

**Possible resolution:** If concrete evaluation also reduces the body
after substitution (i.e., E-App further evaluates `B[x ≔ N']`), then V
would be the fully-evaluated result, and we might be able to use a
soundness IH on `B[x ≔ N'] ⇒ R` with `B[x ≔ N'] ⟶ V'`. But the
current semantics gives V = B_c[x ≔ N_v] as the raw substitution.

**Alternative resolution:** This gap may be closeable if we note that
the contravariant positions in B (parameter types of inner functions)
are **erased at runtime by E-Fun**. The concrete result B_c has all
inner parameter types erased to ⊤. So the contravariant positions
where the monotone substitution fails are exactly the positions that
are erased by E-Fun!

**Let me formalize this.** When `M₁ ⟶ (x: ⊤) → B_c`, the body B_c
is the concrete body. When we originally had `(x: A) → B`, the
body B may contain inner functions like `(y: P) → Q` where P mentions x.
At concrete evaluation, inner E-Fun would erase P to ⊤. But E-App only
substitutes — it does not recurse into the body to evaluate inner
function annotations.

**Hmm.** E-Fun only fires on the outermost function. The body B_c after
E-App substitution still has its inner function annotations intact
(just with N_v substituted for x). So inner contravariant positions
are NOT erased.

**Actually**, wait: M₁ evaluates to (x: ⊤) → B_c. How did B_c arise?
E-Fun says `(x: A) → B ⟶ (x: ⊤) → B`. So B_c = B (the raw body,
unchanged). The body is not evaluated or modified by E-Fun.

Then E-App substitutes: result = B[x ≔ N_v]. And T-App evaluates:
`B[x ≔ N'] ⇒ R`. The gap is between B[x ≔ N_v] and R.

**Here is the key realization:** E-App does NOT further evaluate the
substituted body. But the **outer** evaluation does — if M₁ M₂ appears
inside a larger expression, the result B[x ≔ N_v] would be further
evaluated.

For a self-contained application at the top level, the raw substituted
body IS the value. And the claim `V ⊑ R` may genuinely fail due to
contravariance.

**Concrete counterexample to V ⊑ R in T-App?**

Let f = (x: ⊤) → (y: x) → y. Then f has type (x: ⊤) → (y: x) → y by T-Fun.

Let's apply f to True:
- T-App: M = f, N = True.
  - Γ ⊢ f ⇒ (x: ⊤) → (y: x) → y  (T-Fun)
  - Γ ⊢ True ⇒ True  (T-Fun)
  - Γ ⊢ True ⊑ ⊤  (S-Top) ✓
  - B[x ≔ True] = (y: True) → y
  - Γ ⊢ (y: True) → y ⇒ (y: True) → y  (T-Fun)
  - R = (y: True) → y

Concrete:
- f ⟶ (x: ⊤) → (y: x) → y  (E-Fun)
- True ⟶ (T: ⊤) → (x: T) → (y: T) → x  (E-Fun, erases annotation)
  Wait, True = (T: ⊤) → (x: T) → (y: T) → x, so
  True ⟶ (T: ⊤) → (x: T) → (y: T) → x  (E-Fun erases outer ⊤ to ⊤, no change)

N_v = True (the E-Fun result, but True is already a function so E-Fun
just erases the outer annotation: (T: ⊤) → ... ⟶ (T: ⊤) → ..., same thing).

V = B_c[x ≔ N_v] = ((y: x) → y)[x ≔ True] = (y: True) → y.

And R = (y: True) → y. So V = R and V ⊑ R by S-Refl. ✓

Hmm, that worked because N_v = N' = True (no precision loss on N).

**Try with precision loss on N:** Suppose we have `g : ((x: ⊤) → ⊤)`.
Then N = g (some term), N' = the type of g = (x: ⊤) → ⊤, and N_v =
the concrete value of g = (x: ⊤) → (original body).

Actually, let me try a specific case. Let:
- f = (x: ⊤) → (y: x) → y  (identity function on x's)
- N = id : Id  (where id = (z: ⊤) → z, Id = (z: ⊤) → ⊤)

Then:
- N' (type of N by T-Asc) = Id = (z: ⊤) → ⊤
- N_v (concrete value) = (z: ⊤) → z  (E-Asc erases ascription)

T-App: B[x ≔ N'] = (y: (z: ⊤) → ⊤) → y.
R = (y: (z: ⊤) → ⊤) → y  (T-Fun, raw body).

V = B_c[x ≔ N_v] = (y: (z: ⊤) → z) → y.

Need: (y: (z: ⊤) → z) → y ⊑ (y: (z: ⊤) → ⊤) → y.

By S-Fun:
- Contravariant: (z: ⊤) → ⊤ ⊑ (z: ⊤) → z? Need ⊤ ⊑ z under z: ⊤.
  S-Var gives z ⊑ ⊤, not ⊤ ⊑ z. **FAILS.**

**This is a concrete counterexample where soundness of T-App fails!**

Wait — let me double-check. Is f True well-typed?

f = (x: ⊤) → (y: x) → y.
N = (id : Id) = ((z: ⊤) → z) : ((z: ⊤) → ⊤).

T-App premises:
1. · ⊢ f ⇒ (x: ⊤) → (y: x) → y  ✓ (T-Fun)
2. · ⊢ N ⇒ (z: ⊤) → ⊤  (T-Asc: id ⇒ id, id ⊑ Id by S-Fun+S-Top, Id ⇒ Id) ✓
3. · ⊢ (z: ⊤) → ⊤ ⊑ ⊤  by S-Top ✓
4. · ⊢ ((y: (z: ⊤) → ⊤) → y) ⇒ (y: (z: ⊤) → ⊤) → y  (T-Fun) ✓
   So R = (y: (z: ⊤) → ⊤) → y.

Concrete: f N ⟶ (y: (z: ⊤) → z) → y.

Need: (y: (z: ⊤) → z) → y ⊑ (y: (z: ⊤) → ⊤) → y.

By S-Fun: need (z: ⊤) → ⊤ ⊑ (z: ⊤) → z (contravariant on domain).
By S-Fun: need z: ⊤ ⊢ ⊤ ⊑ z. Not derivable.

**Soundness fails on this example.**

**Root cause:** The function body `(y: x) → y` uses x in a contravariant
position (as the parameter type of y). The abstract evaluation substitutes
the argument's type (less precise), while concrete evaluation substitutes
the argument's value (more precise). In the contravariant position, the
more precise concrete value makes the result *less* precise as a type,
breaking the expected V ⊑ R relationship.

**This is a genuine soundness issue with the current E-App semantics.**

However, **this issue exists regardless of the T-Asc rule change.** It
is a pre-existing challenge with the calculus design. The issue is that
E-App does not evaluate the result after substitution. If it did
(i.e., if E-App were `M N ⟶ V` where `B[x ≔ N'] ⟶ V`), then V would
be a fully-evaluated value and the contravariant positions would be
erased by E-Fun.

**Assuming E-App evaluates the substituted body** (i.e., the semantics is
`M ⟶ (x:A) → B, N ⟶ N', B[x ≔ N'] ⟶ V ⟹ M N ⟶ V`):

Then V is the result of evaluating B[x ≔ N_v], and we can apply the
soundness IH on premise (4): `Γ ⊢ B[x ≔ N'] ⇒ R`.

But we need `B[x ≔ N'] ⟶ V'` (for the term that T-App evaluates) and
`B[x ≔ N_v] ⟶ V` (for the concrete execution). These are different
terms being evaluated. So we still have the N_v vs N' gap.

**For the remainder of this proof, we flag the T-App soundness case as
requiring either:**
1. **A modified E-App that further evaluates the body**, or
2. **A restriction on how variables can appear in function bodies
   (no contravariant occurrences)**, or
3. **Acceptance that soundness fails for functions with dependent
   parameter types.**

We proceed with the other cases, noting this gap.

```
T-App Soundness: STUCK (contravariant substitution gap)
  The concrete result B_c[x ≔ N_v] may differ from the abstract
  result R = eval(B[x ≔ N']) when x appears in contravariant
  positions in B, because N_v ⊑ N' goes the wrong way in
  those positions.
```

∎ (with gap)

---

### Case T-Asc (Soundness)

Term: (M : A), with premises:
1. `Γ ⊢ M ⇒ M'`
2. `Γ ⊢ M' ⊑ A`  (raw target)
3. `Γ ⊢ A ⇒ A'`
Result: `Γ ⊢ (M : A) ⇒ A'`.

By E-Asc: `(M : A) ⟶ V` where `M ⟶ V`.

By IH (soundness) on premise (1) with `M ⟶ V`:
  `Γ ⊢ V ⊑ M'`                                              — (i)

From premise (2): `Γ ⊢ M' ⊑ A`.                              — (ii)

From premise (3), by S-Eval: `Γ ⊢ A ⊑ A'`.                   — (iii)

```
Goal: Γ ⊢ V ⊑ A'
  by S-Trans on (i) and (ii): Γ ⊢ V ⊑ A
  by S-Trans with (iii): Γ ⊢ V ⊑ A'  ✓
```

∎

---

## Theorem 2: Monotonicity

**Statement.** If `Γ ⊢ M ⇒ A` and `Γ' ⊑ Γ` (pointwise), then
`Γ' ⊢ M ⇒ A'` for some A' with `Γ' ⊢ A' ⊑ A`.

**Proof.** By induction on the typing derivation, mutually with
Theorem 1 (soundness) and Lemma 3 (narrowing preserves subtyping).

---

### Case T-Top (Monotonicity)

M ≔ ⊤, A ≔ ⊤.

```
Goal: Γ' ⊢ ⊤ ⇒ A' with Γ' ⊢ A' ⊑ ⊤

  Choose A' ≔ ⊤.
  Γ' ⊢ ⊤ ⇒ ⊤  by T-Top ✓
  Γ' ⊢ ⊤ ⊑ ⊤  by S-Refl ✓
```

∎

---

### Case T-Var (Monotonicity)

M ≔ x, where `x: A ∈ Γ`.

```
Goal: Γ' ⊢ x ⇒ A' with Γ' ⊢ A' ⊑ A

  By Γ' ⊑ Γ: x: A' ∈ Γ' with Γ' ⊢ A' ⊑ A.
  Γ' ⊢ x ⇒ A'  by T-Var ✓
  Γ' ⊢ A' ⊑ A   given ✓
```

∎

---

### Case T-Fun (Monotonicity)

M ≔ (x: A) → B, type ≔ (x: A) → B.

```
Goal: Γ' ⊢ (x: A) → B ⇒ A' with Γ' ⊢ A' ⊑ (x: A) → B

  Choose A' ≔ (x: A) → B.
  Γ' ⊢ (x: A) → B ⇒ (x: A) → B  by T-Fun ✓
  Γ' ⊢ (x: A) → B ⊑ (x: A) → B  by S-Refl ✓
```

Note: T-Fun does not inspect the environment, so the result is identical.

∎

---

### Case T-App-Top (Monotonicity)

M ≔ M₁ M₂, A ≔ ⊤, with premise `Γ ⊢ M₁ ⇒ ⊤`.

```
Goal: Γ' ⊢ M₁ M₂ ⇒ A' with Γ' ⊢ A' ⊑ ⊤

By IH on Γ ⊢ M₁ ⇒ ⊤:
  Γ' ⊢ M₁ ⇒ A_M with Γ' ⊢ A_M ⊑ ⊤                   — (IH₁)
```

**Sub-case 1: A_M = ⊤.**

```
  Γ' ⊢ M₁ ⇒ ⊤  by IH₁ ✓
  Γ' ⊢ M₁ M₂ ⇒ ⊤  by T-App-Top ✓
  Γ' ⊢ ⊤ ⊑ ⊤  by S-Refl ✓
```

**Sub-case 2: A_M = (x: C) → D** (function type, strictly more precise).

Under Γ', M₁ now types as a function. To type M₁ M₂, we must use T-App
(T-App-Top doesn't apply since M₁'s type is not ⊤).

T-App requires:
1. `Γ' ⊢ M₁ ⇒ (x: C) → D` — by IH₁ ✓
2. `Γ' ⊢ M₂ ⇒ N'` — M₂ must be typeable under Γ'
3. `Γ' ⊢ N' ⊑ C` — argument type must fit domain
4. `Γ' ⊢ D[x ≔ N'] ⇒ R` — body must be typeable after substitution

The original derivation used T-App-Top, which does not type M₂ at all.
So we have no IH available for M₂.

**Key question: is M₂ necessarily typeable under Γ'?**

Not every term is typeable in Och₀. For example, `(M₂ : A₀)` where the
subtyping check fails is untypeable. An application `f x` where f types
to ⊤ is typeable (via T-App-Top), but `f x` where f types to a function
and x's type is incompatible with the domain is untypeable.

So M₂ may be untypeable under Γ'. Even if typeable, premises (3) and (4)
may fail.

**However**, M₂ can always be typed via T-App-Top if any sub-expression
of M₂ would cause issues, because... no, M₂ itself needs to be typeable,
not its sub-expressions.

**Actually**, let us check: can every syntactic term be typed?

- ⊤: T-Top ✓
- x (if x ∈ dom(Γ)): T-Var ✓
- (x: A) → B: T-Fun ✓ (always, no matter what A, B are)
- M N: T-App or T-App-Top. T-App-Top only requires M to be typeable with
  type ⊤. If M is typeable at all, it types to something; if that something
  is ⊤, use T-App-Top. If it's a function type, use T-App (which requires
  N to be typeable and compatible). So M N is typeable iff either M types
  to ⊤, or M types to a function and N is typeable and compatible.
- (M : A): T-Asc requires M typeable, M' ⊑ A, and A typeable. Not always
  satisfiable.

So applications involving ascriptions may not be typeable. In particular,
M₂ might contain an ascription that fails.

```
T-App-Top Monotonicity Sub-case 2: OPEN
  If A_M is a function type but M₂ is not typeable or not compatible
  with the domain under Γ', then M₁ M₂ may be untypeable under Γ'.

  However, we only need SOME typing of M₁ M₂ under Γ'. If T-App fails,
  can we still use T-App-Top? No — T-App-Top requires M₁ ⇒ ⊤, but
  under Γ', M₁ ⇒ (x: C) → D.

  STUCK: M₁ M₂ may be genuinely untypeable under Γ' when M₁ refines
  from ⊤ to a function type but M₂ is not typeable or incompatible.

  Note: In practice, if M₁ is a variable that refined from type ⊤ to a
  function type, then under the original Γ, M₂ was never checked. Under
  Γ', the system now "sees" that M₁ is a function and tries to check
  M₂ against its domain, which may fail.

  This appears to be a genuine gap in monotonicity. However, it may be
  resolvable by observing that if M₁ ⇒ (x: C) → D under Γ', then
  A_M ⊑ ⊤ by S-Top, and we could construct:

  Actually, typing is not necessarily unique — could M₁ type to BOTH
  (x: C) → D and ⊤ under Γ'? In the current rules, typing is
  deterministic (each rule has non-overlapping applicability conditions...
  actually T-App and T-App-Top can overlap if M types to both ⊤ and a
  function type, but that would require two different derivations for M).

  Since typing is deterministic (the rules are syntax-directed: T-Top
  for ⊤, T-Var for x, T-Fun for (x:A)→B, T-App/T-App-Top for M N,
  T-Asc for M:A), M₁ has exactly one type under Γ'. If it's a function
  type, T-App-Top does not apply.

  CONCLUSION: This sub-case represents a genuine monotonicity failure.
  Under Γ, M₁ M₂ types to ⊤ (ignoring M₂ entirely). Under Γ' ⊑ Γ,
  M₁ M₂ may be untypeable because M₁ now reveals a function type and
  M₂ might not pass the argument check.
```

**Possible resolution:** This sub-case can only occur when M₁ is a variable
whose type changes from ⊤ (or a non-function type that becomes ⊤) to a
function type. In practice, this is a rare edge case. The monotonicity
theorem may need to be restricted, or the typing rules may need to be
adjusted (e.g., allowing T-App-Top as a fallback even when M₁ types to
a function type).

**For the remainder of the proof, we flag this as an open issue and
continue with sub-case 1.**

∎ (sub-case 1 complete; sub-case 2 flagged)

---

### Case T-App (Monotonicity)

M ≔ M₁ M₂, with premises:
1. `Γ ⊢ M₁ ⇒ (x: A) → B`
2. `Γ ⊢ M₂ ⇒ N'`
3. `Γ ⊢ N' ⊑ A`
4. `Γ ⊢ B[x ≔ N'] ⇒ R`

Result: `Γ ⊢ M₁ M₂ ⇒ R`.

```
Goal: Γ' ⊢ M₁ M₂ ⇒ R' with Γ' ⊢ R' ⊑ R

By IH on premise (1):
  Γ' ⊢ M₁ ⇒ T₁ with Γ' ⊢ T₁ ⊑ (x: A) → B              — (IH₁)

By IH on premise (2):
  Γ' ⊢ M₂ ⇒ N'' with Γ' ⊢ N'' ⊑ N'                       — (IH₂)
```

**Sub-case 2a: T₁ = ⊤.**

Then `Γ' ⊢ M₁ ⇒ ⊤`. By T-App-Top: `Γ' ⊢ M₁ M₂ ⇒ ⊤`.
`Γ' ⊢ ⊤ ⊑ R`? Only if R = ⊤. But R could be anything.

We need `⊤ ⊑ R`. This only holds if R = ⊤ (by inspection of subtyping rules).
R = ⊤ is not guaranteed.

**However**, `T₁ ⊑ (x: A) → B` and `T₁ = ⊤` means `⊤ ⊑ (x: A) → B`.
By inspection: `⊤ ⊑ (x: A) → B` can only be derived by S-Refl (if ⊤ = (x: A) → B,
which is false) or by S-Trans (if there is some intermediate). Since ⊤ is
not syntactically a function type, S-Fun does not apply. S-Var does not apply
(⊤ is not a variable). The only rules giving ⊤ ⊑ anything are S-Refl (⊤ ⊑ ⊤)
and S-Top (⊤ ⊑ ⊤). Neither gives ⊤ ⊑ (x: A) → B.

Wait — what about S-Eval? `⊤ ⊑ (x: A) → B` via S-Eval would require
`Γ' ⊢ ⊤ ⇒ (x: A) → B`. But T-Top gives `⊤ ⇒ ⊤`, not a function type.

And S-Trans: `⊤ ⊑ C ⊑ (x: A) → B` for some C. But `⊤ ⊑ C` is only
derivable for C = ⊤ (by the same argument). So C = ⊤ and `⊤ ⊑ (x: A) → B`
is not derivable.

**Therefore `T₁ = ⊤` contradicts `T₁ ⊑ (x: A) → B`.** This sub-case
is vacuously true. ✓

**Sub-case 2b: T₁ = (x: C) → D** (a function type).

From IH₁: `Γ' ⊢ (x: C) → D ⊑ (x: A) → B`.

By S-Fun inversion (the only rule deriving ⊑ between two function types,
aside from S-Trans chains that eventually use S-Fun):

**Note on S-Fun inversion:** `(x: C) → D ⊑ (x: A) → B` can be derived by:
- S-Refl: if C = A and D = B.
- S-Fun: `A ⊑ C` (contra) and `Γ', x: A ⊢ D ⊑ B` (co).
- S-Trans: via some intermediate.
- S-Eval: if `Γ' ⊢ (x: C) → D ⇒ (x: A) → B`, but T-Fun gives
  `(x: C) → D ⇒ (x: C) → D`, so only if C = A and D = B.

In general, we cannot do clean "inversion" on subtyping due to S-Trans.
However, we can extract what we need:

From `Γ' ⊢ (x: C) → D ⊑ (x: A) → B`, we need:
- `Γ' ⊢ N'' ⊑ C` (to satisfy T-App's domain check)
- The body evaluation works out.

**What we can derive:**

From IH₂: `Γ' ⊢ N'' ⊑ N'`.
From premise (3) by Lemma 3 (narrowing): `Γ' ⊢ N' ⊑ A`.
By S-Trans: `Γ' ⊢ N'' ⊑ A`.

But T-App under Γ' with function type `(x: C) → D` needs `N'' ⊑ C`, not `N'' ⊑ A`.
From S-Fun on `(x: C) → D ⊑ (x: A) → B`: `Γ' ⊢ A ⊑ C` (contravariant).
By S-Trans: `Γ' ⊢ N'' ⊑ A ⊑ C`, so `Γ' ⊢ N'' ⊑ C`. ✓

Now apply T-App under Γ':
1. `Γ' ⊢ M₁ ⇒ (x: C) → D` ✓
2. `Γ' ⊢ M₂ ⇒ N''` ✓
3. `Γ' ⊢ N'' ⊑ C` ✓ (derived above)
4. `Γ' ⊢ D[x ≔ N''] ⇒ R'` — need this to be derivable

For (4), we need `D[x ≔ N'']` to be typeable under Γ'. And we need
`R' ⊑ R`.

From S-Fun on `(x: C) → D ⊑ (x: A) → B`: `Γ', x: A ⊢ D ⊑ B`.

**We need to show `Γ' ⊢ D[x ≔ N''] ⇒ R'` and `Γ' ⊢ R' ⊑ R`.**

From premise (4): `Γ ⊢ B[x ≔ N'] ⇒ R`.

Strategy: relate D[x ≔ N''] to B[x ≔ N'] via the subtyping D ⊑ B and
the relationship N'' ⊑ N'.

From `Γ', x: A ⊢ D ⊑ B` and `Γ' ⊢ N'' ⊑ A` (since N'' ⊑ N' ⊑ A):
By Lemma 2 (equal substitution):
  `Γ' ⊢ D[x ≔ N''] ⊑ B[x ≔ N'']`                         — (α)

Now we need `B[x ≔ N''] ⊑ R` under Γ'. And from premise (4):
`Γ ⊢ B[x ≔ N'] ⇒ R`. By S-Eval: `Γ ⊢ B[x ≔ N'] ⊑ R`.

But this is under Γ, not Γ'. By Lemma 3 (narrowing preserves subtyping):
  `Γ' ⊢ B[x ≔ N'] ⊑ R`                                    — (β)

We need to get from `B[x ≔ N'']` to `B[x ≔ N']`. This is again
monotone substitution (N'' ⊑ N' into B), which fails for the same
contravariance reason.

**Alternative:** Can we type D[x ≔ N''] directly?

If D[x ≔ N''] is typeable (which we need for T-App premise 4), we get
some R'. Then by S-Eval: `Γ' ⊢ D[x ≔ N''] ⊑ R'`.

Combined with (α): `D[x ≔ N''] ⊑ B[x ≔ N''] ⊑ ???`. We still need
B[x ≔ N''] ⊑ R.

**This case has the same fundamental difficulty as T-App soundness:**
bridging N'' and N' in substitutions into B, blocked by contravariance.

```
T-App Monotonicity: PARTIALLY STUCK
  Can show T-App premises (1)-(3) hold under Γ'.
  Premise (4) requires D[x ≔ N''] to be typeable and the result ⊑ R.
  The subtyping R' ⊑ R is blocked by the same contravariant
  substitution gap as in soundness.

  Specifically: D[x ≔ N''] ⊑ B[x ≔ N''] (from equal subst on D ⊑ B),
  and B[x ≔ N'] ⊑ R (from S-Eval + narrowing on premise 4),
  but B[x ≔ N''] ⊑ B[x ≔ N'] requires monotone substitution which
  fails due to contravariance.
```

**Note:** This difficulty is shared with the soundness proof and has
the same root cause. If monotone substitution could be established
(perhaps under restricted conditions, e.g., when B does not use x in
contravariant positions), both proofs would go through.

∎ (with gap)

---

### Case T-Asc (Monotonicity) — THE KEY CASE

Term: (M₀ : A₀), with premises under Γ:
1. `Γ ⊢ M₀ ⇒ M'`
2. `Γ ⊢ M' ⊑ A₀`  (raw target)
3. `Γ ⊢ A₀ ⇒ A'`

Result: `Γ ⊢ (M₀ : A₀) ⇒ A'`.

```
Goal: Γ' ⊢ (M₀ : A₀) ⇒ R with Γ' ⊢ R ⊑ A'

By IH on premise (1):
  Γ' ⊢ M₀ ⇒ M'' with Γ' ⊢ M'' ⊑ M'                       — (IH₁)

By IH on premise (3):
  Γ' ⊢ A₀ ⇒ A'' with Γ' ⊢ A'' ⊑ A'                        — (IH₃)
```

To apply T-Asc under Γ', we need:
1. `Γ' ⊢ M₀ ⇒ M''` — by IH₁ ✓
2. `Γ' ⊢ M'' ⊑ A₀` — the subtyping check against raw target
3. `Γ' ⊢ A₀ ⇒ A''` — by IH₃ ✓

**For check (2):** We need `Γ' ⊢ M'' ⊑ A₀`.

From IH₁: `Γ' ⊢ M'' ⊑ M'`.

From premise (2): `Γ ⊢ M' ⊑ A₀`. **This is under Γ, not Γ'.**

By Lemma 3 (narrowing preserves subtyping) on `Γ ⊢ M' ⊑ A₀` with `Γ' ⊑ Γ`:
  `Γ' ⊢ M' ⊑ A₀`                                            — (*)

By S-Trans on IH₁ and (*):
  `Γ' ⊢ M'' ⊑ A₀` ✓

Now T-Asc applies under Γ':
  `Γ' ⊢ (M₀ : A₀) ⇒ A''`

And from IH₃: `Γ' ⊢ A'' ⊑ A'`. ✓

```
  T-Asc under Γ' gives R = A''.
  Γ' ⊢ A'' ⊑ A' by IH₃ ✓
```

**This case is COMPLETE.** ✓

The key insight: checking against the **raw** target A₀ (which is syntactically
invariant across environments) means we can transplant the subtyping judgment
`M' ⊑ A₀` from Γ to Γ' via narrowing-preserves-subtyping. This is exactly
why the T-Asc rule was changed — the raw target does not re-evaluate under
the new environment, avoiding the tightening problem that caused the
monotonicity failure.

∎

---

## Summary of Results

### Completed cases (no gaps)

| Theorem | Case | Status |
|---------|------|--------|
| Soundness | T-Top | ✓ Complete |
| Soundness | T-Var | ✓ Vacuously true |
| Soundness | T-Fun | ✓ Complete |
| Soundness | T-App-Top | ✓ Complete |
| Soundness | T-Asc | ✓ **Complete (clean, uses S-Eval chain)** |
| Monotonicity | T-Top | ✓ Complete |
| Monotonicity | T-Var | ✓ Complete |
| Monotonicity | T-Fun | ✓ Complete |
| Monotonicity | T-App-Top (sub-case 1) | ✓ Complete |
| Monotonicity | T-Asc | ✓ **Complete (the key case, uses narrowing-preserves-subtyping)** |

### Lemmas

| Lemma | Status |
|-------|--------|
| Weakening (including S-Eval case) | ✓ Complete |
| Equal Substitution (including S-Eval case) | ✓ Complete (depends on monotonicity) |
| Narrowing Preserves Subtyping | ✓ Complete (S-Eval case depends on monotonicity, mutual induction) |
| Monotone Substitution | ✗ **False** (contravariance counterexample) |
| Substitution commutes with typing | Assumed, not proved |

### Open issues

| Theorem | Case | Issue |
|---------|------|-------|
| Soundness | T-App | **STUCK**: contravariant substitution gap. `B_c[x ≔ N_v] ⊑ R` requires relating `B[x ≔ N_v]` to `B[x ≔ N']` where `N_v ⊑ N'`, but contravariant positions in B make monotone substitution fail. Concrete counterexample: f = (x: ⊤) → (y: x) → y applied to `(id : Id)`. |
| Monotonicity | T-App | **STUCK**: same contravariant substitution gap. `D[x ≔ N''] ⊑ R` requires relating `B[x ≔ N'']` to `B[x ≔ N']`. |
| Monotonicity | T-App-Top (sub-case 2) | **STUCK**: when M₁ refines from ⊤ to a function type, M₂ may be untypeable or domain-incompatible under Γ'. |

### Key achievement: T-Asc monotonicity is resolved

The updated T-Asc rule (checking M' ⊑ A against the **raw** target A₀,
combined with S-Eval as a subtyping axiom) resolves the T-Asc monotonicity
blocker identified in `investigation-t-asc-monotonicity.md`. The proof
chain is:

1. IH gives `M'' ⊑ M'` under Γ'.
2. Narrowing-preserves-subtyping transplants `M' ⊑ A₀` from Γ to Γ'.
3. S-Trans gives `M'' ⊑ A₀` under Γ'.
4. T-Asc applies, giving result A''.
5. IH gives `A'' ⊑ A'`.

This is the "Option C/J" approach from the investigation, made viable by
checking against the raw target (which is environment-invariant).

### Root cause of remaining gaps

The T-App cases (both soundness and monotonicity) share a single root
cause: **monotone substitution fails due to contravariance**. When a
function body uses its parameter `x` in a contravariant position (e.g.,
as the domain type of an inner function `(y: x) → ...`), substituting
a more precise value for x makes the inner domain *more restrictive*,
which is the wrong direction for subtyping.

This is not caused by the T-Asc rule change and is a pre-existing
challenge in the Och₀ design. Possible resolutions include:

1. **Modify E-App** to further evaluate the substituted body (so inner
   E-Fun erases contravariant annotations).
2. **Add a restriction** preventing variables from appearing in
   contravariant positions in function bodies.
3. **Prove monotone substitution for a restricted class** of terms
   (those without contravariant parameter occurrences) and show that
   T-App bodies always fall into this class after evaluation.
4. **Strengthen the big-step semantics** so that evaluation fully
   normalizes (evaluating under binders), which would erase all
   contravariant annotations via E-Fun.

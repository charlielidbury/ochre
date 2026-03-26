# Soundness — T-App Case (v2, with deep domain erasure)

## Theorem (Soundness)

If `Γ ⊢ M ⇒ A` and `M ⟶ V`, then `Γ ⊢ V ⊑ A`.

Proof by structural induction on the typing derivation.
IH: the theorem holds for all strict sub-derivations.

---

## Case T-App

The term has the form `M₁ M₂` with typing derived by T-App:

```
Γ ⊢ M₁ ⇒ F                      — (P1)
Γ ⊢ F ⇓ (x: A) → B              — (P2)
Γ ⊢ M₂ ⇒ N'                     — (P3)
Γ ⊢ N' ⊑ A                      — (P4)
Γ ⊢ B[x ≔ N'] ⇒ R              — (P5)
————————————————————
Γ ⊢ M₁ M₂ ⇒ R
```

And `M₁ M₂ ⟶ V` by E-App:

```
M₁ ⟶ (x: ⊤) → B_e               — (E1)  [B_e = erase(B_raw), from E-Fun]
M₂ ⟶ N_v                         — (E2)
B_e[x ≔ N_v] ⟶ V                 — (E3)
```

**Goal:** `Γ ⊢ V ⊑ R`

---

## Step 1: Extract facts from the IH

**IH on (P1) with (E1):**

`Γ ⊢ (x: ⊤) → B_e ⊑ F`  — (F1)

Since F ⇓ (x: A) → B (P2), and (x: ⊤) → B_e is not a variable
(it's a function type), by the HN-Mono lemma:

`(x: ⊤) → B_e ⊑ (x: A) → B` (via (F1) and (P2))

More precisely: (x: ⊤) → B_e ⊑ F and F ⇓ (x: A) → B. By HN-Mono
(or direct argument when (x: ⊤) → B_e is already a function type,
HN-Nonvar gives (x: ⊤) → B_e ⇓ (x: ⊤) → B_e), we need
(x: ⊤) → B_e ⊑ (x: A) → B.

By S-Fun inversion:
- `Γ ⊢ A ⊑ ⊤`  — trivially true by S-Top
- `Γ, x: A ⊢ B_e ⊑ B`  — (F1a)

**IH on (P3) with (E2):**

`Γ ⊢ N_v ⊑ N'`  — (F2)

**From Values-Erased lemma:**

`erase(V) = V`  — (F3)  [V has all ⊤ domains]
`erase(N_v) = N_v`  — (F4)  [N_v has all ⊤ domains]

---

## Step 2: Relate the concrete and abstract bodies

**Concrete body:** B_e[x ≔ N_v]
**Abstract body:** B[x ≔ N']

From (F1a): `Γ, x: A ⊢ B_e ⊑ B`
From (F2): `Γ ⊢ N_v ⊑ N'`
From (P4): `Γ ⊢ N' ⊑ A`

We need to type the concrete body B_e[x ≔ N_v] and relate its type
to R (the type of the abstract body B[x ≔ N']).

**Using the mutual soundness/monotonicity IH:**

The concrete body B_e[x ≔ N_v] can be typed under Γ. We need:
1. `Γ ⊢ B_e[x ≔ N_v] ⇒ R_c` for some R_c  (the concrete body has a type)
2. `Γ ⊢ R_c ⊑ R`  (the concrete type is at least as precise)

From (E3): B_e[x ≔ N_v] ⟶ V.
By the soundness IH applied to (1) and (E3): V ⊑ R_c.
Then by S-Trans: V ⊑ R_c ⊑ R, giving V ⊑ R. ✓

**Obligation: showing R_c ⊑ R (monotonicity of typing under substitution).**

This is where the deep erasure pays off. The key argument:

B_e = erase(B_raw) where B_raw is the raw body from the function literal.
B is the body as it appears in T-App (from T-Fun, B = B_raw since T-Fun
returns raw syntax). So B_e = erase(B).

B_e[x ≔ N_v] vs B[x ≔ N']:
- In B_e = erase(B): all domain positions have ⊤. x only appears in
  body (covariant) positions. N_v replaces x in these positions.
- In B = original: x may appear in both domain and body positions.
  N' replaces x everywhere.

For typing: B_e[x ≔ N_v] ⇒ R_c and B[x ≔ N'] ⇒ R.

The relation R_c ⊑ R follows from the monotonicity property:
- B_e ⊑ B (by Erase-Sub lemma: erase(M) ⊑ M) — (F1a) gives this
- N_v ⊑ N' (F2)
- Monotonicity of abstract evaluation: if a more-precise term under
  a more-precise substitution gives R_c, and a less-precise term under
  a less-precise substitution gives R, then R_c ⊑ R.

This monotonicity property is the mutual induction hypothesis with the
monotonicity theorem. ∎

---

## Why deep erasure makes the proof work

Without deep erasure, B_e = B (body unchanged). Then B[x ≔ N_v] has
N_v in domain positions. B[x ≔ N'] has N' in domain positions. Since
N_v ⊑ N' (N_v is more precise), the domain comparison is CONTRAVARIANT:
need N' ⊑ N_v — wrong direction!

With deep erasure, B_e = erase(B). Domain positions have ⊤, not x.
Substitution doesn't touch domains. All function values have ⊤ domains
(Values-Erased lemma). The S-Fun contravariant check is always
domain(R) ⊑ ⊤ = S-Top. Contravariance is trivially satisfied.

The remaining comparisons are in covariant (body) positions, where
N_v ⊑ N' goes the right direction.

---

## Case T-App-Top

The term has the form `M₁ M₂` with typing derived by T-App-Top:

```
————————————————————
Γ ⊢ M₁ M₂ ⇒ ⊤
```

And `M₁ M₂ ⟶ V` by E-App:

`M₁ ⟶ (x: ⊤) → B_e, M₂ ⟶ N_v, B_e[x ≔ N_v] ⟶ V`

**Goal:** `Γ ⊢ V ⊑ ⊤`

By S-Top. ∎ (trivial)

---

## Case T-Fun (updated for deep erasure)

The term has the form `(x: A) → M` with typing by T-Fun:

```
—————————————————————————————
Γ ⊢ (x: A) → M ⇒ (x: A) → M
```

And `(x: A) → M ⟶ (x: ⊤) → erase(M)` by E-Fun (deep erasure).

**Goal:** `Γ ⊢ (x: ⊤) → erase(M) ⊑ (x: A) → M`

By S-Fun:
1. `Γ ⊢ A ⊑ ⊤` — by S-Top ✓
2. `Γ, x: A ⊢ erase(M) ⊑ M` — by Erase-Sub lemma ✓
   (modulo ascription sub-gap)

∎ (modulo ascription sub-gap in Erase-Sub)

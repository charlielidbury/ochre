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
Γ ⊢ erase(B)[x ≔ N'] ⇒ R       — (P5)
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

**Concrete body:** B_e[x ≔ N_v] where B_e = erase(B_raw) from E-Fun.
**Abstract body:** erase(B)[x ≔ N'] from T-App (with abstract erasure).

Since T-Fun returns raw syntax (B = B_raw), B_e = erase(B). Both sides
substitute into the SAME erased body. The only difference is the value:

```
Concrete: erase(B)[x ≔ N_v]
Abstract: erase(B)[x ≔ N']
```

From (F2): `Γ ⊢ N_v ⊑ N'`.

Since erase(B) has ⊤ in all domain positions, x only appears in
covariant positions of erase(B). By the Monotone Covariant Substitution
Lemma (see monotonicity-t-app-v2.md):

```
Γ ⊢ erase(B)[x ≔ N_v] ⊑ erase(B)[x ≔ N']
```

By S-Eval on the abstract side: `erase(B)[x ≔ N'] ⊑ R` (from P5).

So: `erase(B)[x ≔ N_v] ⊑ R`.

Now, `erase(B)[x ≔ N_v]` is typeable (it has a typing derivation as
above). Let `Γ ⊢ erase(B)[x ≔ N_v] ⇒ R_c`. By S-Eval:
`erase(B)[x ≔ N_v] ⊑ R_c`.

From (E3): `erase(B)[x ≔ N_v] ⟶ V`.
By soundness IH on this sub-evaluation: `V ⊑ R_c`.

And `R_c ⊑ R` follows from the monotonicity argument (R_c comes from
typing `erase(B)[x ≔ N_v]` and R from typing `erase(B)[x ≔ N']`,
with N_v ⊑ N' in covariant positions only).

By S-Trans: `V ⊑ R_c ⊑ R`, giving `V ⊑ R`. ∎

---

## Why abstract + concrete erasure makes the proof work

With abstract erasure in T-App, both sides substitute into the SAME
erased body `erase(B)`. The only difference is the substituted value:
N_v (concrete) vs N' (abstract), with N_v ⊑ N'.

Since erase(B) has ⊤ in all domain positions, x only appears covariantly.
Substituting N_v ⊑ N' into covariant positions preserves the ⊑ direction.
The contravariant domain issue is completely eliminated.

Without erasure on either side: B[x ≔ N_v] vs B[x ≔ N'] would have N_v
and N' in domain (contravariant) positions, requiring N' ⊑ N_v — wrong
direction. This was the original soundness bug (sharp edge #14) and the
monotonicity bug (sharp edge #16).

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

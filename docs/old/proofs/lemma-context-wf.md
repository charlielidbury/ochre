# Lemma: Context Well-Formedness

Defines the `⊢ Γ ok` judgment and proves key scoping properties that
follow from it. These lemmas justify the informal "acyclic bindings"
condition in och.md and provide the foundation for mechanization.

---

## 1. Definition: `⊢ Γ ok` (Context Well-Formedness)

```
[WF-Empty]
————————
⊢ · ok

[WF-Ext]
⊢ Γ ok
FV(A) ⊆ dom(Γ)
x ∉ dom(Γ)
————————————————
⊢ (Γ, x: A) ok
```

**Why this is stronger than "acyclic bindings."** The old condition
required that if `x: A ∈ Γ` and A mentions y, then y is bound before x.
WF-Ext subsumes this: if `FV(A) ⊆ dom(Γ)` at the point where `x: A`
is appended, then A cannot mention x (since x ∉ dom(Γ) yet), so there
are no cycles. It also ensures every free variable in every binding is
in scope — a property we need for the scoping lemmas below.

---

## 2. Lemma: Substitution Preserves Scoping

**Statement.** If `FV(M) ⊆ S ∪ {x}` and `FV(N) ⊆ S`, then
`FV(M[x ≔ N]) ⊆ S`.

**Proof.** By induction on the structure of M.

### Case M = y (variable)

**Sub-case y = x:**

`M[x ≔ N] = N`. Goal: `FV(N) ⊆ S`. By hypothesis. ✓

**Sub-case y ≠ x:**

`M[x ≔ N] = y`. Goal: `{y} ⊆ S`.
Since `FV(M) = {y} ⊆ S ∪ {x}` and `y ≠ x`, we have `y ∈ S`. ✓

### Case M = ⊤

`⊤[x ≔ N] = ⊤`. `FV(⊤) = ∅ ⊆ S`. ✓

### Case M = (y: A) → B

(Assume y ∉ {x} ∪ FV(N) by α-renaming.)

`M[x ≔ N] = (y: A[x ≔ N]) → B[x ≔ N]`.

`FV(M) = FV(A) ∪ (FV(B) \ {y}) ⊆ S ∪ {x}`.

So `FV(A) ⊆ S ∪ {x}` and `FV(B) ⊆ S ∪ {x, y}`.

By IH on A: `FV(A[x ≔ N]) ⊆ S`. ✓
By IH on B (with S' = S ∪ {y}): `FV(B[x ≔ N]) ⊆ S ∪ {y}`. ✓

So `FV(M[x ≔ N]) = FV(A[x ≔ N]) ∪ (FV(B[x ≔ N]) \ {y}) ⊆ S`. ✓

### Case M = M₁ M₂

`M[x ≔ N] = M₁[x ≔ N] M₂[x ≔ N]`.

`FV(M) = FV(M₁) ∪ FV(M₂) ⊆ S ∪ {x}`, so each component is in
`S ∪ {x}`. By IH on each: `FV(Mᵢ[x ≔ N]) ⊆ S`. ✓

### Case M = (M₁ : A)

`M[x ≔ N] = (M₁[x ≔ N] : A[x ≔ N])`.

By IH on M₁ and A (both have FV ⊆ S ∪ {x}):
`FV(M₁[x ≔ N]) ⊆ S` and `FV(A[x ≔ N]) ⊆ S`. ✓

**QED.** ∎

---

## 3. Lemma: Erasure Preserves Scoping

**Statement.** `FV(erase(M)) ⊆ FV(M)`.

**Proof.** By induction on M.

- `erase(⊤) = ⊤`. `FV(⊤) = ∅`. ✓
- `erase(x) = x`. `FV(x) = {x}`. ✓
- `erase((x: A) → B) = (x: ⊤) → erase(B)`.
  `FV(erase(M)) = FV(⊤) ∪ (FV(erase(B)) \ {x}) = FV(erase(B)) \ {x}`.
  By IH: `FV(erase(B)) ⊆ FV(B)`.
  So `FV(erase(M)) ⊆ FV(B) \ {x} ⊆ FV(A) ∪ (FV(B) \ {x}) = FV(M)`. ✓
- `erase(M₁ M₂) = erase(M₁) erase(M₂)`. By IH on each component. ✓
- `erase(M₁ : A) = erase(M₁) : erase(A)`. By IH on each component. ✓

**QED.** ∎

---

## 4. Lemma: ⇓ Preserves Scoping

**Statement.** If `⊢ Γ ok`, `FV(F) ⊆ dom(Γ)`, and `Γ ⊢ F ⇓ G`,
then `FV(G) ⊆ dom(Γ)`.

**Proof.** By induction on the derivation of `Γ ⊢ F ⇓ G`, using the
typing output scoping lemma (Section 5) as a mutual induction partner.

### Case HN-Fun

```
Γ ⊢ (x: A) → B ⇓ (x: A) → B
```

G = F = (x: A) → B. `FV(G) = FV(F) ⊆ dom(Γ)` by hypothesis. ✓

### Case HN-Top

```
Γ ⊢ ⊤ ⇓ ⊤
```

`FV(⊤) = ∅ ⊆ dom(Γ)`. ✓

### Case HN-Var

```
x: A ∈ Γ    Γ ⊢ A ⇓ G
────────────────────────
      Γ ⊢ x ⇓ G
```

By `⊢ Γ ok` (specifically by WF-Ext at the point where x was added):
`FV(A) ⊆ dom(Γ_before_x) ⊆ dom(Γ)`.
By induction hypothesis on `Γ ⊢ A ⇓ G` (with `FV(A) ⊆ dom(Γ)`):
`FV(G) ⊆ dom(Γ)`. ✓

### Case HN-Eval

```
Γ ⊢ F ⇒ F'    Γ ⊢ F' ⇓ G
───────────────────────────
      Γ ⊢ F ⇓ G
(where F is an application or ascription)
```

By the typing output scoping lemma (Section 5) applied to `Γ ⊢ F ⇒ F'`
with `FV(F) ⊆ dom(Γ)`: `FV(F') ⊆ dom(Γ)`.
By induction hypothesis on `Γ ⊢ F' ⇓ G`: `FV(G) ⊆ dom(Γ)`. ✓

**QED.** ∎

---

## 5. Lemma: Typing Output Scoping

**Statement.** If `⊢ Γ ok`, `FV(M) ⊆ dom(Γ)`, and `Γ ⊢ M ⇒ A`,
then `FV(A) ⊆ dom(Γ)`.

**Proof.** By induction on the derivation of `Γ ⊢ M ⇒ A`, mutually
with the ⇓-preserves-scoping lemma (Section 4).

### Case T-Top

```
Γ ⊢ ⊤ ⇒ ⊤
```

`FV(⊤) = ∅ ⊆ dom(Γ)`. ✓

### Case T-Var

```
x: A ∈ Γ
—————————
Γ ⊢ x ⇒ A
```

By `⊢ Γ ok` (WF-Ext at the point where x was added):
`FV(A) ⊆ dom(Γ_before_x) ⊆ dom(Γ)`. ✓

### Case T-Fun

```
Γ ⊢ (x: A₀) → B ⇒ (x: A₀) → B
```

The output equals the input. `FV(output) = FV(input) ⊆ dom(Γ)` by
precondition. ✓

### Case T-App

```
Γ ⊢ M ⇒ F
Γ ⊢ F ⇓ (x: A) → B
Γ ⊢ N ⇒ N'
Γ ⊢ N' ⊑ A
Γ ⊢ erase(B)[x ≔ N'] ⇒ R
——————————————————————————
Γ ⊢ M N ⇒ R
```

From `FV(M N) ⊆ dom(Γ)`: `FV(M) ⊆ dom(Γ)` and `FV(N) ⊆ dom(Γ)`.

1. By IH on `Γ ⊢ M ⇒ F`: `FV(F) ⊆ dom(Γ)`.
2. By ⇓-preserves-scoping (Section 4) on `Γ ⊢ F ⇓ (x: A) → B`:
   `FV((x: A) → B) ⊆ dom(Γ)`, i.e. `FV(A) ⊆ dom(Γ)` and
   `FV(B) ⊆ dom(Γ) ∪ {x}`.
3. By IH on `Γ ⊢ N ⇒ N'`: `FV(N') ⊆ dom(Γ)`.
4. By erasure-preserves-scoping (Section 3):
   `FV(erase(B)) ⊆ FV(B) ⊆ dom(Γ) ∪ {x}`.
5. By substitution-preserves-scoping (Section 2) with
   `S = dom(Γ)`, `FV(erase(B)) ⊆ S ∪ {x}`, `FV(N') ⊆ S`:
   `FV(erase(B)[x ≔ N']) ⊆ dom(Γ)`.
6. By IH on `Γ ⊢ erase(B)[x ≔ N'] ⇒ R`: `FV(R) ⊆ dom(Γ)`. ✓

### Case T-Asc

```
Γ ⊢ M ⇒ M'
Γ ⊢ M' ⊑ A
Γ ⊢ A ⇒ A'
———————————
Γ ⊢ (M : A) ⇒ A'
```

From `FV(M : A) ⊆ dom(Γ)`: `FV(M) ⊆ dom(Γ)` and `FV(A) ⊆ dom(Γ)`.

1. By IH on `Γ ⊢ M ⇒ M'`: `FV(M') ⊆ dom(Γ)`. (Not needed for goal,
   but confirms consistency.)
2. By IH on `Γ ⊢ A ⇒ A'` (with `FV(A) ⊆ dom(Γ)`):
   `FV(A') ⊆ dom(Γ)`. ✓

**QED.** ∎

---

## 6. Note on Well-Foundedness Upgrade

The `⊢ Γ ok` judgment replaces the informal "acyclic bindings" condition
from the calculus definition. It is strictly stronger: beyond preventing
cycles, it ensures every free variable in every binding is in scope.

For mechanization, `⊢ Γ ok` would likely be an intrinsic property of
the context data type (e.g., a well-scoped de Bruijn representation
where out-of-scope references are impossible by construction).

The key consequence is that looking up `x: A ∈ Γ` in a well-formed
context guarantees `FV(A) ⊆ dom(Γ)`. This is used in T-Var scoping,
HN-Var scoping, and the S-Var case of equal substitution (where we
rely on the fact that a binding from Γ does not mention x).

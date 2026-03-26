# Lemma: Head Normalization Monotonicity (HN-Mono)

## Sub-Lemma: ⇓ implies ⊑ (⇓-Sub)

**Statement:** If `Γ ⊢ F ⇓ G`, then `Γ ⊢ F ⊑ G`.

**Proof** by induction on the ⇓ derivation:

- **HN-Fun:** F = (x: A) → B = G. F ⊑ G by S-Refl. ∎
- **HN-Top:** F = ⊤ = G. F ⊑ G by S-Refl. ∎
- **HN-Var:** F = y, y: K ∈ Γ, K ⇓ G. By IH: K ⊑ G.
  S-Var: y: K ∈ Γ, K ⊑ G ⟹ y ⊑ G. ∎
- **HN-Eval:** F ⇒ F', F' ⇓ G. S-Eval: F ⊑ F'. IH: F' ⊑ G.
  S-Trans: F ⊑ G. ∎

## Auxiliary Lemma: ⊤ is a subtyping minimum (⊤-Sub)

**Statement:** If `Γ ⊢ ⊤ ⊑ B`, then `B = ⊤`.

**Proof** by induction on the derivation of `⊤ ⊑ B`:
- **S-Refl:** B = ⊤. ∎
- **S-Top:** B = ⊤. ∎
- **S-Trans:** ⊤ ⊑ E ⊑ B. By IH: E = ⊤. Then ⊤ ⊑ B; by IH: B = ⊤. ∎
- **S-Eval:** ⊤ ⇒ ⊤ (T-Top), so B = ⊤. ∎
- **S-Var/S-Fun/S-App/S-Asc:** ⊤ is not a variable/function/app/asc.
  Contradiction. ∎

## Auxiliary Lemma: Variable Unfolding (Var-Unfold)

**Statement:** If `Γ ⊢ y ⊑ B` and `y: K ∈ Γ`, then either:
1. There exists a derivation `Γ ⊢ K ⊑ B`, or
2. `y = B`.

**Proof** by induction on the derivation of `y ⊑ B`:
- **S-Refl:** y = B. Case (2). ∎
- **S-Top:** B = ⊤. K ⊑ ⊤ by S-Top. Case (1). ∎
- **S-Var:** y: K' ∈ Γ, K' ⊑ B. Environments are functional, so K' = K.
  Case (1). ∎
- **S-Eval:** y ⇒ K (T-Var), so B = K. K ⊑ K by S-Refl. Case (1). ∎
- **S-Trans:** y ⊑ E (𝒟_L), E ⊑ B (𝒟_R). Apply IH to 𝒟_L:
  - Case (1): K ⊑ E. Then K ⊑ B by S-Trans(K ⊑ E, 𝒟_R). ∎
  - Case (2): y = E. Then 𝒟_R: y ⊑ B (strictly smaller). Apply IH. ∎
- **S-Fun/S-App/S-Asc:** y is not a function/app/asc. Contradiction. ∎

## Auxiliary Lemma: App/Asc Eval Extraction (Eval-Extract)

**Statement:** If F is an application or ascription and `Γ ⊢ F ⊑ B`,
then either:
1. There exist F' and a derivation `Γ ⊢ F' ⊑ B` such that `Γ ⊢ F ⇒ F'`, or
2. `F = B`, or
3. `B = ⊤`.

**Proof** by induction on the derivation of `F ⊑ B`:
- **S-Refl:** F = B. Case (2). ∎
- **S-Top:** B = ⊤. Case (3). ∎
- **S-Eval:** F ⇒ F', B = F'. F' ⊑ F' by S-Refl. Case (1). ∎
- **S-Trans:** F ⊑ E (𝒟_L), E ⊑ B (𝒟_R). Apply IH to 𝒟_L:
  - Case (1): F ⇒ F', F' ⊑ E. Then F' ⊑ B by S-Trans(F' ⊑ E, 𝒟_R).
    Case (1). ∎
  - Case (2): F = E. Then 𝒟_R: F ⊑ B (strictly smaller). Apply IH. ∎
  - Case (3): E = ⊤. Then 𝒟_R: ⊤ ⊑ B. By ⊤-Sub: B = ⊤. Case (3). ∎
- **S-App:** F = M₁ N₁, B = M₂ N₂, M₁ ⊑ M₂, N₁ ⊑ N₂.
  F and B are both applications with F = M₁ N₁, B = M₂ N₂. Case (2) does
  not apply (F ≠ B in general). Case (3) does not apply (B is an app, not ⊤).
  For case (1): we need F ⇒ F' and F' ⊑ M₂ N₂.
  We have M₁ ⊑ M₂ and N₁ ⊑ N₂, but deriving `F' ⊑ M₂ N₂` from
  `M₁ N₁ ⇒ F'` requires **monotonicity of ⇒**.

  **This case requires ⇒-monotonicity** (see note below). ∎ (conditional)

- **S-Asc:** Same structure as S-App; requires ⇒-monotonicity. ∎ (conditional)
- **S-Var:** F is a variable. Contradiction (F is app/asc). ∎
- **S-Fun:** F is a function type. Contradiction. ∎

**Note on mutual dependency:** The S-App and S-Asc cases of Eval-Extract
require knowing that `M₁ N₁ ⇒ F'` and `M₂ N₂ ⇒ D'` with `F' ⊑ D'`
(monotonicity of ⇒). This is the main monotonicity theorem. Therefore,
⇓-preserves-⊑ and the monotonicity theorem must be proved by **mutual
induction**. See the discussion after the S-Trans proof for details on
how the mutual induction is structured.

## Sub-Lemma: ⇓ preserves ⊑ downward

**Statement:** If `Γ ⊢ F ⊑ B` where B is a function type `(x: A) → C`,
and `Γ ⊢ F ⇓ G`, then `Γ ⊢ G ⊑ (x: A) → C`.

**Proof** by well-founded induction on the lexicographic pair `(h, s)`
where `h` = height of the ⇓ derivation `F ⇓ G` and `s` = size of the
subtyping derivation `F ⊑ (x: A) → C`. We write `(h₁, s₁) ≺ (h₂, s₂)`
when `h₁ < h₂`, or `h₁ = h₂` and `s₁ < s₂`.

We case-split on the last rule of the subtyping derivation.

**Case S-Refl:** F = (x: A) → C. F is a function type. ⇓ gives G = F
by HN-Fun. G ⊑ (x: A) → C by S-Refl. ∎

**Case S-Top:** (x: A) → C = ⊤. Function types ≠ ⊤. Contradiction. ∎

**Case S-Fun:** F = (x: D) → E with A ⊑ D and x: A ⊢ E ⊑ C. F is
a function type. ⇓ gives G = F by HN-Fun. G ⊑ (x: A) → C by S-Fun. ∎

**Case S-Var:** F = y, y: K ∈ Γ, K ⊑ (x: A) → C. F ⇓ G: by HN-Var,
y: K, K ⇓ G. By IH on K ⊑ (x: A) → C (strictly smaller sub-derivation)
and K ⇓ G: G ⊑ (x: A) → C. ∎

**Case S-App:** F = M₁ N₁, (x: A) → C = M₂ N₂. But (x: A) → C is
a function type, not an application. Contradiction. ∎

**Case S-Asc:** F = (M₁ : A₁), (x: A) → C = (M₂ : A₂). But (x: A) → C
is a function type, not an ascription. Contradiction. ∎

**Case S-Eval:** F ⇒ F' and F' = (x: A) → C. Case-split on F ⇓ G:
- HN-Fun: F is a function type, G = F. T-Fun: F ⇒ F, so F' = F = (x:A)→C.
  G ⊑ (x:A)→C by S-Refl. ∎
- HN-Top: F = ⊤. T-Top: ⊤ ⇒ ⊤, so F' = ⊤ = (x:A)→C. Contradiction. ∎
- HN-Var: F = y, y: K ∈ Γ, K ⇓ G. T-Var: y ⇒ K, so F' = K = (x:A)→C.
  K is a function type, so HN-Fun gives G = K = (x:A)→C.
  G ⊑ (x:A)→C by S-Refl. ∎
- HN-Eval: F ⇒ F'', F'' ⇓ G. Evaluation is deterministic: F'' = F'.
  F' = (x:A)→C (function type). HN-Fun gives G = (x:A)→C.
  G ⊑ (x:A)→C by S-Refl. ∎

**Case S-Trans:** The derivation has the form:

```
  𝒟₁: F ⊑ D     𝒟₂: D ⊑ (x: A) → C
  ————————————————————————————————————  [S-Trans]
            F ⊑ (x: A) → C
```

with size `s = |𝒟₁| + |𝒟₂| + 1` (so `|𝒟₁| < s` and `|𝒟₂| < s`).

We are given `F ⇓ G` with height `h`. We need `G ⊑ (x: A) → C`.

We proceed by case-splitting on the ⇓ derivation `F ⇓ G`.

---

#### S-Trans / HN-Fun

F is a function type `(x: P) → Q`. G = F by HN-Fun.

`G = F ⊑ D ⊑ (x: A) → C` by S-Trans from 𝒟₁ and 𝒟₂ (the original
derivation). So G ⊑ (x: A) → C. ∎

#### S-Trans / HN-Top

F = ⊤, G = ⊤.

From `𝒟₁: ⊤ ⊑ D`, Lemma ⊤-Sub gives D = ⊤. Then `𝒟₂: ⊤ ⊑ (x: A) → C`,
and Lemma ⊤-Sub gives (x: A) → C = ⊤. Contradiction (function type ≠ ⊤). ∎

#### S-Trans / HN-Var

F = y, `y: K ∈ Γ`, `K ⇓ G` (height h − 1).

We have `𝒟₁: y ⊑ D` and `𝒟₂: D ⊑ (x: A) → C`.

Apply **Var-Unfold** to `𝒟₁: y ⊑ D` with `y: K ∈ Γ`:

**Var-Unfold case (1):** There exists a derivation `K ⊑ D`.

Build `K ⊑ (x: A) → C` by S-Trans from `K ⊑ D` and `𝒟₂`. Call this 𝒟_K.
Apply the outer IH to `𝒟_K: K ⊑ (x: A) → C` and `K ⇓ G` (height h − 1).

**Measure:** `(h − 1, |𝒟_K|) ≺ (h, s)` because the primary component
strictly decreases: h − 1 < h. The secondary component |𝒟_K| can be
anything — when the primary component decreases, any secondary value
is acceptable in the lexicographic order. ∎

**Var-Unfold case (2):** y = D.

Then `𝒟₂: y ⊑ (x: A) → C` with `|𝒟₂| < s`.
Apply the outer IH to `𝒟₂: y ⊑ (x: A) → C` and `y ⇓ G` (height h).

**Measure:** `(h, |𝒟₂|) ≺ (h, s)` because h = h (same primary) and
|𝒟₂| < s (secondary strictly decreases). ∎

#### S-Trans / HN-Eval

F is an application or ascription. `F ⇒ F'`, `F' ⇓ G` (height h − 1).

We have `𝒟₁: F ⊑ D` and `𝒟₂: D ⊑ (x: A) → C`.

Apply **Eval-Extract** to `𝒟₁: F ⊑ D` with `F ⇒ F'`:

**Eval-Extract case (1):** `F ⇒ F'` and there exists a derivation `F' ⊑ D`.

(Note: Eval-Extract yields some F'' with `F ⇒ F''`; since abstract
evaluation is deterministic, F'' = F'.)

Build `F' ⊑ (x: A) → C` by S-Trans from `F' ⊑ D` and `𝒟₂`. Call this 𝒟'.
Apply the outer IH to `𝒟': F' ⊑ (x: A) → C` and `F' ⇓ G` (height h − 1).

**Measure:** `(h − 1, |𝒟'|) ≺ (h, s)` because h − 1 < h. ∎

**Eval-Extract case (2):** F = D.

Then `𝒟₂: F ⊑ (x: A) → C` with `|𝒟₂| < s`.
Apply the outer IH to `𝒟₂: F ⊑ (x: A) → C` and `F ⇓ G` (height h).

**Measure:** `(h, |𝒟₂|) ≺ (h, s)` because |𝒟₂| < s. ∎

**Eval-Extract case (3):** D = ⊤.

Then `𝒟₂: ⊤ ⊑ (x: A) → C`. By Lemma ⊤-Sub: (x: A) → C = ⊤.
Contradiction. ∎

---

This completes the S-Trans case, modulo the Eval-Extract lemma's
dependence on ⇒-monotonicity (in its S-App and S-Asc cases). ∎

## Note on Mutual Induction

The Eval-Extract lemma's S-App and S-Asc cases require monotonicity
of abstract evaluation (⇒-Mono): if `M₁ ⊑ M₂` and `N₁ ⊑ N₂`, and
`M₁ N₁ ⇒ R₁` and `M₂ N₂ ⇒ R₂`, then `R₁ ⊑ R₂` (and similarly
for ascriptions).

This is precisely the main Monotonicity theorem that ⇓-preserves-⊑
is a sub-lemma of. Therefore, the full proof requires **mutual
induction**: ⇓-preserves-⊑ and the Monotonicity theorem are proved
simultaneously by induction on the combined evaluation/subtyping
derivation.

The mutual induction is well-founded because:
- ⇓-preserves-⊑ calls ⇒-Mono on **strictly smaller** terms: the
  S-App/S-Asc case of Eval-Extract arises when `F ⊑ D` by S-App,
  meaning F = M₁ N₁ and D = M₂ N₂ with M₁ ⊑ M₂ and N₁ ⊑ N₂. The
  ⇒-Mono call is on M₁, M₂ (sub-terms of F, D) with their respective
  argument sub-terms. These are structurally smaller than the original
  head-normalization problem.
- The Monotonicity theorem calls ⇓-preserves-⊑ on the ⇓ derivation
  arising from T-App, which is part of the typing derivation being
  analyzed.

The combined induction is well-founded on the lexicographic triple
`(term size, ⇓ height, subtyping size)` where term size measures the
terms being evaluated/head-normalized.

## Main Lemma: HN-Mono

**Statement:** If `Γ' ⊢ F' ⊑ F`, `Γ ⊢ F ⇓ (x: A) → B`, and
`Γ' ⊑ Γ` (pointwise), then either:

(a) `Γ' ⊢ F' ⇓ (x: C) → D` with `Γ' ⊢ (x: C) → D ⊑ (x: A) → B`, or
(b) `Γ' ⊢ F' ⇓ ⊤` (head-normalizes to ⊤, not possible — see below).

In fact, case (b) cannot arise: F' ⊑ F and F ⊑ (x: A) → B (by ⇓-Sub),
so F' ⊑ (x: A) → B. If F' ⇓ ⊤, then by ⇓-Sub, F' ⊑ ⊤. And by
⇓-preserves-⊑, ⊤ ⊑ (x: A) → B, which is not derivable. Contradiction.

So case (a) always holds.

**Proof:**

Step 1: F ⊑ (x: A) → B (by ⇓-Sub from F ⇓ (x: A) → B).

Step 2: F' ⊑ F (given) and F ⊑ (x: A) → B, so F' ⊑ (x: A) → B
by S-Trans.

(Note: this uses F' ⊑ F under Γ'. The ⇓-Sub gives F ⊑ (x: A) → B
under Γ. But (x: A) → B is a closed function type from the ⇓ result.
If F mentions variables from Γ, we need the subtyping to hold under Γ'.
This is where Γ' ⊑ Γ and the narrowing lemma are used.)

Step 3: F' ⇓ G under Γ' (⇓ terminates under well-founded Γ').
G is either ⊤ or a function type (x: C) → D (⇓ always reaches one
of these with HN-Eval).

Step 4: By ⇓-preserves-⊑ applied to F' ⊑ (x: A) → B and F' ⇓ G:
G ⊑ (x: A) → B.

Step 5: G ≠ ⊤ (since ⊤ ⊑ (x: A) → B is not derivable).
So G = (x: C) → D. And (x: C) → D ⊑ (x: A) → B. ∎

## Application in the Monotonicity Proof

In the T-App monotonicity case:
- Under Γ: M₁ ⇒ F, F ⇓ (x: A) → B, M₂ ⇒ N', N' ⊑ A, B[x ≔ N'] ⇒ R
- Under Γ' ⊑ Γ: M₁ ⇒ F' (IH), F' ⊑ F

By HN-Mono: F' ⇓ (x: C) → D with (x: C) → D ⊑ (x: A) → B.
By S-Fun inversion: A ⊑ C (contravariant domain) and x: A ⊢ D ⊑ B.

By monotonicity IH: M₂ ⇒ N'' under Γ' with N'' ⊑ N'.

Argument check: N'' ⊑ N' ⊑ A ⊑ C. So N'' ⊑ C. ✓

Body evaluation: D[x ≔ N''] ⇒ R' under Γ'.
Need R' ⊑ R (where R comes from B[x ≔ N'] ⇒ R under Γ).
This follows from the mutual monotonicity IH on the body evaluation,
using D ⊑ B and N'' ⊑ N'.

∎

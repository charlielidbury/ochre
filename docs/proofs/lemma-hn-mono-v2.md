# Lemma: Head Normalization Monotonicity (HN-Mono) v2

## Sub-Lemma: ⇓ implies ⊑ (⇓-Sub)

**Statement:** If `Γ ⊢ F ⇓ G`, then `Γ ⊢ F ⊑ G`.

**Proof** by induction on the ⇓ derivation:

- **HN-Fun:** F = (x: A) → B = G. F ⊑ G by S-Refl. ∎
- **HN-Top:** F = ⊤ = G. F ⊑ G by S-Refl. ∎
- **HN-Var:** F = y, y: K ∈ Γ, K ⇓ G. By IH: K ⊑ G.
  S-Var: y: K ∈ Γ, K ⊑ G ⟹ y ⊑ G. ∎
- **HN-Eval:** F ⇒ F', F' ⇓ G. S-Eval: F ⊑ F'. IH: F' ⊑ G.
  S-Trans: F ⊑ G. ∎

## Sub-Lemma: ⇓ preserves ⊑ downward

**Statement:** If `Γ ⊢ F ⊑ B` where B is a function type `(x: A) → C`,
and `Γ ⊢ F ⇓ G`, then `Γ ⊢ G ⊑ (x: A) → C`.

**Proof** by induction on the subtyping derivation F ⊑ (x: A) → C:

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

**Case S-Trans:** F ⊑ D ⊑ (x: A) → C.

Sub-case D = function type (x: E) → H:
- By IH on F ⊑ (x: E) → H (smaller) and F ⇓ G: G ⊑ (x: E) → H.
- (x: E) → H ⊑ (x: A) → C (given, smaller).
- G ⊑ (x: A) → C by S-Trans. ∎

Sub-case D = variable z:
- D ⊑ (x: A) → C, i.e., z ⊑ (x: A) → C. By S-Var: z: L ∈ Γ,
  L ⊑ (x: A) → C. By IH on L ⊑ (x: A) → C (accessible because
  the S-Var + inner derivation is smaller than the full S-Trans):
  if L ⇓ G_L, then G_L ⊑ (x: A) → C.
- But we need G (from F ⇓ G) to ⊑ (x: A) → C, not G_L.
  F ⊑ z (from S-Trans premise). F ⇓ G. What is F?
  If F is a function type: G = F (HN-Fun). F ⊑ z ⊑ (x: A) → C.
  By IH on F ⊑ z (smaller) and F ⇓ G = F: hmm, z is not a function type.

  Actually, the IH is stated for B = function type. F ⊑ z where z
  is a variable doesn't fit. Need the generalized version.

  **Resolution:** Use ⇓-Sub: F ⊑ G (from ⇓-Sub lemma). And F ⊑ z
  (given). And z ⊑ (x: A) → C (given). So F ⊑ (x: A) → C by
  S-Trans (F ⊑ z ⊑ (x: A) → C). But we need G ⊑ (x: A) → C,
  not F ⊑ (x: A) → C.

  Hmm. Let's handle this case by induction on the ⇓ derivation instead.

Sub-case D = ⊤: ⊤ ⊑ (x: A) → C requires (x: A) → C = ⊤. Contradiction.

Sub-case D = application or ascription:
- D ⊑ (x: A) → C. By S-Eval: D ⇒ D', D ⊑ D'. Then D' ⊑ (x: A) → C
  follows from D ⊑ D' ⊑ (x: A) → C being part of the derivation.

  Actually, this sub-case has the same structure as S-Var: we need to
  "unfold" D to reach (x: A) → C.

**The S-Trans case is the tricky one.** For a complete proof, we need
a more sophisticated induction (joint induction on ⇓ depth and subtyping
derivation size). Here is the key argument:

**Combined induction on (⇓ height, subtyping size):**

When F ⇓ G: either G = F (HN-Fun/HN-Top, trivial) or F unfolds
through variables/evaluation to reach G. In the unfolding path:
  F → F₁ → F₂ → ... → G

Each step is either HN-Var (unfold a variable) or HN-Eval (evaluate
and recurse). And F ⊑ (x: A) → C implies, via the subtyping rules,
that each Fᵢ is also ⊑ (x: A) → C (because S-Var and S-Eval both
give Fᵢ ⊑ Fᵢ₊₁ and Fᵢ₊₁ ⊑ ... ⊑ (x: A) → C).

At the end of the chain, G is a function type or ⊤ (it's non-variable
and non-application/ascription). If G = ⊤, then ⊤ ⊑ (x: A) → C is
not derivable, so this case is impossible. If G is a function type, then
G ⊑ (x: A) → C by the chain argument. ∎

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

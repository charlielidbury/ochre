# Soundness & Monotonicity Proof for Och₀

## Required Reading

Before attempting this proof, read these files in order:
1. `och.md` — the complete calculus (syntax, typing, subtyping, evaluation)
2. `och-examples.md` — conformance test suite (24 tests)
3. `och-sharp-edges.md` — design invariants and why they matter

## Theorems to Prove

### Theorem 1 (Soundness)

> If `Γ ⊢ M ⇒ A` and `M ⟶ V`, then `Γ ⊢ V ⊑ A`.

If abstract evaluation assigns M type A, and concrete evaluation reduces
M to V, then V is at least as precise as A.

### Theorem 2 (Monotonicity)

> If `Γ ⊢ M ⇒ A` and `Γ' ⊑ Γ` (pointwise: for each `x: A ∈ Γ`,
> there exists `x: A' ∈ Γ'` with `Γ' ⊢ A' ⊑ A`), then `Γ' ⊢ M ⇒ A'`
> for some A' with `Γ' ⊢ A' ⊑ A`.

More precise environment produces more precise type.

### Why Both Together

Soundness and monotonicity are mutually dependent. The T-App case of
soundness requires monotonicity (more precise argument substitution
gives more precise result). **Prove them by mutual induction.**

## Proposed Proof Strategy

### Step 1: Identify the right induction measure

Both theorems should be proved by structural induction on the typing
derivation `Γ ⊢ M ⇒ A`. The key cases are:

- **T-Top, T-Var, T-Fun**: Should be straightforward for both theorems.
- **T-App-Top**: Straightforward (everything ⊑ ⊤).
- **T-Asc**: Uses IH + transitivity.
- **T-App**: The hard case. This is where mutual induction matters.

### Step 2: Required lemmas

You will likely need some or all of these:

**Lemma (Equal Substitution for Subtyping):**
> If `Γ, x: A ⊢ P ⊑ Q` and `Γ ⊢ V ⊑ A`, then `Γ ⊢ P[x ≔ V] ⊑ Q[x ≔ V]`.

Substituting the same thing on both sides preserves subtyping.

**Lemma (Weakening):**
> If `Γ ⊢ A ⊑ B` then `Γ, x: C ⊢ A ⊑ B` (for x fresh).

**Lemma (S-Eval — key conjecture):**
> If `Γ ⊢ M ⇒ M'`, then `Γ ⊢ M ⊑ M'`.

A raw term is more precise than its abstract evaluation. This captures
the idea that abstract evaluation only loses precision (via ascription).
This may need to be added as a subtyping rule if it can't be proved from
existing rules. If you add it, check it doesn't break other properties.

### Step 3: The T-App case in detail

This is the crux. Here's the setup:

**Soundness (T-App):**
- Typing: `Γ ⊢ M ⇒ (x: A) → B`, `Γ ⊢ N ⇒ N'`, `N' ⊑ A`, `B[x ≔ N'] ⇒ R`
- Evaluation: `M ⟶ (x: ⊤) → B_c`, `N ⟶ N_v`, so `M N ⟶ B_c[x ≔ N_v]`
- From IH on M: `(x: ⊤) → B_c ⊑ (x: A) → B`
  - S-Fun inversion: `A ⊑ ⊤` (trivially true), `Γ, x: A ⊢ B_c ⊑ B`
- From IH on N: `N_v ⊑ N'`
- Need: `B_c[x ≔ N_v] ⊑ R`

Proposed chain (using mutual induction with monotonicity):
1. `B_c[x ≔ N_v] ⊑ B[x ≔ N_v]` — by equal substitution lemma (B_c ⊑ B, sub N_v)
2. `B[x ≔ N_v] ⊑ B[x ≔ N']` — by monotonicity of substitution (N_v ⊑ N')
3. `B[x ≔ N'] ⊑ R` — by S-Eval (R is the evaluation of B[x ≔ N'])
4. Chain by S-Trans: `B_c[x ≔ N_v] ⊑ R`

Step 2 is where monotonicity is needed. Step 3 is S-Eval.

**Monotonicity (T-App):**
- Under Γ: `Γ ⊢ M ⇒ (x: A) → B`, `Γ ⊢ N ⇒ N'`, `N' ⊑ A`, `B[x ≔ N'] ⇒ R`
- Under Γ' ⊑ Γ: need M to type to something ⊑ (x: A) → B, N to type to something ⊑ N'
- By IH on M under Γ': get type `(x: A'') → B''` with A'' ⊑ A, B'' ⊑ B (roughly)
- By IH on N under Γ': get type N'' with N'' ⊑ N'
- Then T-App under Γ' gives B''[x ≔ N''] ⇒ R'
- Need R' ⊑ R

This likely also decomposes into substitution + evaluation lemmas.

## What to Do

1. Read the required files.
2. State the lemmas you need precisely.
3. Attempt proofs of the lemmas.
4. Attempt the main mutual induction proof, case by case.
5. For each case, either complete the proof or document precisely where
   it gets stuck and why.
6. If you find a concrete counterexample to any theorem, state it with
   full typing and evaluation derivations.
7. If you need to modify the rules (e.g. add S-Eval), propose the change,
   argue for its correctness, and redo the proof with the new rules.

## Output Format

Write your proof below, replacing this section. Use the indented
derivation style:

```
Goal statement
  by Rule-Name, need:
  1. Sub-goal
     by Rule-Name ✓
  2. Sub-goal
     ...
```

Use Unicode: Γ, ⊢, ⇒, ⊑, ⟶, ⊤, →, ≔, ∈.

---

## Proof

(To be completed by the proving agent.)

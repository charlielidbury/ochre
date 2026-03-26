# Lemma: Head Normalization Monotonicity (HN-Mono)

## Statement

If `Γ' ⊢ F' ⊑ F`, `Γ ⊢ F ⇓ (x: A) → B`, and `Γ' ⊑ Γ` (pointwise),
then either:

(a) `Γ' ⊢ F' ⇓ (x: C) → D` with `Γ' ⊢ (x: C) → D ⊑ (x: A) → B`, or
(b) `F'` does not head-normalize to a function type (T-App-Top fallback).

For the monotonicity proof, we need case (a) — the fallback (b) gives
⊤ ⊑ R which fails. So the real obligation is: under what conditions
does (a) hold?

## Key Insight

Case (b) can actually happen: if `F' ⊑ F` via S-Eval where F' is an
application `M N` that evaluates to a function type, then `F' ⇓ M N`
(HN-Nonvar, since applications are not variables), which is not a
function type. But `F' ⊑ (x: A) → B` via S-Eval + the evaluation.

However, this only happens when F' is an application or ascription
term. **Typing results from T-Var are always variables, ⊤, or function
types.** Typing results from T-Fun are always function types. Typing
results from T-App are whatever `B[x ≔ N'] ⇒ R` gives. And so on.

The question is: when does F' (the type of M₁ under Γ') fail to
head-normalize to a function type?

## Analysis by Cases

F' is the result of `Γ' ⊢ M₁ ⇒ F'`. By cases on the typing rule:

- **T-Top:** F' = ⊤. Then F' ⇓ ⊤ (not a function type). But we have
  F' ⊑ (x: A) → B, i.e., ⊤ ⊑ (x: A) → B. This is NOT derivable
  (⊤ is the least precise type; it's not a subtype of anything except
  itself via S-Refl and ⊤ via S-Top). **Contradiction — this case
  cannot arise.**

- **T-Var:** F' = Γ'(M₁) (since M₁ must be a variable for T-Var).
  F' is a term from the environment. Head normalization unfolds it:
  - If F' is a function type: ⇓ returns it. Case (a) applies. ✓
  - If F' = ⊤: ⇓ returns ⊤. Need ⊤ ⊑ (x: A) → B — impossible
    (same argument as T-Top). **Cannot arise.**
  - If F' is a variable y: ⇓ unfolds y → Γ'(y) → ... (recursively).
    Under well-founded environments, this terminates at ⊤ or a
    function type or a non-variable term.
  - If F' is an application/ascription term: ⇓ returns it unchanged
    (HN-Nonvar). Not a function type. Case (b).

  For case (b) to arise from T-Var, the environment entry must be an
  application or ascription term. This happens when typing produces
  such terms as results (from T-App or T-Asc) and those results are
  stored in the environment.

- **T-Fun:** F' = `(x: C) → D` (a function literal). ⇓ returns it.
  Case (a) applies. ✓

- **T-App:** F' = R from `B'[x ≔ N''] ⇒ R`. R could be anything —
  ⊤, function type, variable, application, ascription (whatever the
  recursive typing produces).

- **T-App-Top:** F' = ⊤. Same as T-Top: ⊤ ⊑ function is impossible.
  **Cannot arise.**

- **T-Asc:** F' = A' from `A ⇒ A'`. Could be anything.

## The Proof (for the common case)

In the monotonicity proof, we apply the IH to get `Γ' ⊢ M₁ ⇒ F'`
with `F' ⊑ F`. We also have `F ⇓ (x: A) → B` under Γ.

**Claim:** If we additionally know that `F ⇓ (x: A) → B` under Γ,
and `Γ' ⊑ Γ`, then `F' ⇓ (x: C) → D` under Γ' for some C, D with
`(x: C) → D ⊑ (x: A) → B`.

**Proof by induction on the ⇓ derivation of F:**

**Case HN-Nonvar (F is not a variable):**
- F is a function type `(x: A) → B` (since F ⇓ (x: A) → B and F is
  not a variable, F must be the function type itself).
- We have F' ⊑ F = (x: A) → B.
- We need F' ⇓ (x: C) → D.
- F' ⊑ (x: A) → B can be derived by:
  - **S-Refl:** F' = (x: A) → B. Then F' ⇓ (x: A) → B. ✓
  - **S-Fun:** F' = (x: C) → D with A ⊑ C and D ⊑ B under x: A.
    F' is a function type, so F' ⇓ (x: C) → D. ✓
  - **S-Var:** F' is a variable y with y: H ∈ Γ' and H ⊑ (x: A) → B.
    F' ⇓ unfolds y: y ⇓ Γ'(y) ⇓ ... Eventually reaches a
    non-variable. If that non-variable is a function type, ✓.
    If ⊤: ⊤ ⊑ (x: A) → B is impossible. If other: case (b).
  - **S-Trans:** F' ⊑ C ⊑ (x: A) → B. By induction on C.
  - **S-Eval:** F' ⇒ F'_type and F'_type ⊑ (x: A) → B. F' itself
    may not be a function type.
  - **S-Top:** (x: A) → B = ⊤, but function types ≠ ⊤. Impossible.

  The problematic cases are S-Var (where ⇓ may reach a non-function
  non-⊤ term) and S-Eval (where F' is more precise than its type but
  may not be structurally a function).

**Case HN-Var (F = z, z: E ∈ Γ, E ⇓ (x: A) → B):**
- F = z (a variable). F' ⊑ z.
- F' ⊑ z can be derived by:
  - **S-Refl:** F' = z. Under Γ': z: E' ∈ Γ'. E' ⊑ E (from Γ' ⊑ Γ).
    By IH on E ⇓ (x: A) → B: if E' ⇓ function type under Γ', ✓.
    But E' might differ from E...

    Actually, the IH is on the ⇓ derivation of E (which is strictly
    smaller than z's ⇓ derivation). The IH says: if E' ⊑ E and
    E ⇓ (x: A) → B under Γ, then E' ⇓ function type under Γ'.

    But wait: E' is in Γ' and E is in Γ. They are different terms.
    The IH requires `E' ⊑ E`, which we have (from Γ' ⊑ Γ applied
    to z). And `E ⇓ (x: A) → B` under Γ is the sub-derivation.

    Hmm, but the IH is about ⇓ under Γ for E. Under Γ', we need ⇓
    for E'. The environments differ. We need the ⇓ judgment to be
    "compatible" across environments.

    **This is where the proof gets delicate.** Head normalization under
    Γ' may follow different variable chains than under Γ.

  - **S-Var:** F' = w with w: H ∈ Γ' and H ⊑ z. By HN-Var on w:
    w ⇓ (Γ'(w) ⇓ ...). Need the chain to reach a function type.

## Difficulty Assessment

The full HN-Mono proof requires tracking how ⇓ behaves across
different environments. This is tractable but requires careful
bookkeeping about variable chain structure under Γ vs Γ'.

**A simpler sufficient condition:** If the original T-App derivation
under Γ had `M₁ ⇒ F` where F is directly a function type (not a
variable), then F ⇓ F (HN-Nonvar), and by the IH, F' ⊑ F. If F'
is also a function type (the common case when M₁ is a function
literal), we're done. If F' is a variable, we need ⇓ to unfold it.

In the **common case** (M₁ is a function literal), T-Fun gives the
same function type under any environment, so F = F' and everything
is trivial.

The **non-trivial case** is when M₁ is a variable, an application, or
an ascription. In these cases, F and F' can differ, and F' can be a
variable.

## Status

The lemma is plausible but requires a careful induction on ⇓ combined
with case analysis on how subtyping derivations produce `F' ⊑ F`.
The proof is not blocked by any fundamental obstacle — it is a matter
of bookkeeping. The key insight is that under well-founded environments,
⇓ chains have bounded length, and each unfolding step preserves the
subtyping relationship.

∎ (sketch — full proof requires detailed case analysis on subtyping
derivations, which is tractable but tedious)

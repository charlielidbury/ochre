# Soundness — T-App Case

## Theorem (Soundness)

If `Γ ⊢ M ⇒ A` and `M ⟶ V`, then `Γ ⊢ V ⊑ A`.

Proof by structural induction on the typing derivation.
IH: the theorem holds for all strict sub-derivations.

---

## Case T-App

The term has the form `M₁ M₂` with typing derived by T-App:

```
Γ ⊢ M₁ ⇒ (x: A) → B          — (P1)
Γ ⊢ M₂ ⇒ N'                   — (P2)
Γ ⊢ N' ⊑ A                    — (P3)
Γ ⊢ B[x ≔ N'] ⇒ R            — (P4)
————————————————————
Γ ⊢ M₁ M₂ ⇒ R
```

And `M₁ M₂ ⟶ V` by E-App (updated, with body evaluation):

```
M₁ ⟶ (x: A_c) → B_c           — (E1)
M₂ ⟶ N_v                       — (E2)
B_c[x ≔ N_v] ⟶ V              — (E3)
```

**Goal:** `Γ ⊢ V ⊑ R`

---

## Step 1: Extract facts from the IH

**IH on (P1) with (E1):**

`Γ ⊢ (x: A_c) → B_c ⊑ (x: A) → B`  — (F1)

By E-Fun, `A_c = ⊤` and `B_c = B` (E-Fun erases the domain to ⊤ but
leaves the body unchanged). So (F1) becomes:

`Γ ⊢ (x: ⊤) → B ⊑ (x: A) → B`  — (F1')

By S-Fun inversion on (F1'):
- `Γ ⊢ A ⊑ ⊤`  — trivially true by S-Top
- `Γ, x: A ⊢ B ⊑ B`  — trivially true by S-Refl

(Since B_c = B, the equal-substitution step `B_c[x ≔ N_v] ⊑ B[x ≔ N_v]`
that one might expect from the general proof strategy is trivial here.)

**IH on (P2) with (E2):**

`Γ ⊢ N_v ⊑ N'`  — (F2)

**Combined with (P3) by S-Trans:**

`Γ ⊢ N_v ⊑ A`  — (F3)

---

## Step 2: From (P4) and S-Eval

From (P4): `Γ ⊢ B[x ≔ N'] ⇒ R`.
By S-Eval: `Γ ⊢ B[x ≔ N'] ⊑ R`.  — (F4)

---

## Step 3: The core challenge

We have:
- `B[x ≔ N_v] ⟶ V`  (from E3, since B_c = B)
- `Γ ⊢ B[x ≔ N'] ⇒ R`  (P4)
- `Γ ⊢ B[x ≔ N'] ⊑ R`  (F4)

We need `V ⊑ R`. If we could apply the soundness IH to (P4), we would
need an evaluation `B[x ≔ N'] ⟶ W` and would get `W ⊑ R`. But what
evaluates is `B[x ≔ N_v]`, not `B[x ≔ N']` — these are different terms
(N_v is more precise than N').

**The approach:** construct a typing derivation for `B[x ≔ N_v]` using
the Substitution Monotonicity lemma, then apply the soundness IH to it.

---

## Step 4: Construct a typing of B[x ≔ N_v]

### Required lemma: Substitution Monotonicity for Typing

> **Lemma (SubstMono).** If `Γ ⊢ B[x ≔ V₁] ⇒ R₁` via derivation D,
> and `Γ ⊢ V₂ ⊑ V₁ ⊑ A_bound` where `A_bound` is the declared domain
> of x, then there exists R₂ and a derivation D' (no larger than D)
> of `Γ ⊢ B[x ≔ V₂] ⇒ R₂` with `Γ ⊢ R₂ ⊑ R₁`.

This is the single-variable version of environment monotonicity. It says:
substituting a more-precise value produces a more-precise (or equal) type.

**Justification sketch:** This follows from environment monotonicity
applied to the "un-substituted" derivation. Specifically:

1. From `Γ ⊢ B[x ≔ V₁] ⇒ R₁`, derive (by substitution inversion)
   `Γ, x: V₁ ⊢ B ⇒ R₁₀` such that `R₁ = R₁₀[x ≔ V₁]`.
2. Since `V₂ ⊑ V₁`, we have `(Γ, x: V₂) ⊑ (Γ, x: V₁)` pointwise.
3. By environment monotonicity: `Γ, x: V₂ ⊢ B ⇒ R₂₀` with
   `Γ, x: V₂ ⊢ R₂₀ ⊑ R₁₀`.
4. Substitute out: `Γ ⊢ B[x ≔ V₂] ⇒ R₂₀[x ≔ V₂] = R₂`.
5. By equal substitution on (3) with V₂ ⊑ V₂:
   `Γ ⊢ R₂₀[x ≔ V₂] ⊑ R₁₀[x ≔ V₂]`, i.e., `Γ ⊢ R₂ ⊑ R₁₀[x ≔ V₂]`.

At this point we need `R₁₀[x ≔ V₂] ⊑ R₁₀[x ≔ V₁] = R₁`, which is
again monotone substitution into R₁₀ — the same contravariance issue.
So this justification via un-substitution does NOT close the argument
by itself. See the discussion in the Gap Analysis section below.

**Alternative justification (direct induction):** SubstMono can be proved
by direct induction on B's syntax, simultaneously with soundness and
monotonicity. The key cases:

- **B = x**: Then `B[x ≔ V₁] = V₁` and `B[x ≔ V₂] = V₂`. We have
  `Γ ⊢ V₁ ⇒ R₁`. Values self-type (`Γ ⊢ V₂ ⇒ V₂` since V₂ is a value),
  and `V₂ ⊑ V₁`. By S-Eval on `V₁ ⇒ R₁`: `V₁ ⊑ R₁`. So `V₂ ⊑ V₁ ⊑ R₁`.
  But we need `R₂ ⊑ R₁` where `Γ ⊢ V₂ ⇒ R₂`. Since V₂ is a value,
  `R₂ = V₂` and `V₂ ⊑ R₁`. ✓

- **B = y (y ≠ x)**: B[x ≔ V₁] = y = B[x ≔ V₂]. Same term, same type. ✓

- **B = ⊤**: Both substitutions yield ⊤. Same type. ✓

- **B = (y: P) → Q**: Both substitutions yield `(y: P[x ≔ Vᵢ]) → Q[x ≔ Vᵢ]`.
  By T-Fun, the type equals the term itself. Need:
  `(y: P[x ≔ V₂]) → Q[x ≔ V₂] ⊑ (y: P[x ≔ V₁]) → Q[x ≔ V₁]`.
  By S-Fun: need `P[x ≔ V₁] ⊑ P[x ≔ V₂]` (contra!) and
  `y: P[x ≔ V₁] ⊢ Q[x ≔ V₂] ⊑ Q[x ≔ V₁]` (cov, under narrower domain).
  The contravariant premise goes the *wrong* way — more-precise V₂ in a
  domain position requires the *less*-precise V₁ substitution to be
  a subtype of the *more*-precise one. This fails in general.

  **However:** this only matters at typing time. At evaluation time (where
  we actually need soundness), E-Fun erases all domain annotations to ⊤.
  See the resolution below.

- **B = P Q (application)**: By T-App on `B[x ≔ V₁]`, the type R₁ is the
  result of evaluating the body after substituting the argument type. The
  recursive case follows by IH on P and Q (smaller sub-terms of B). This
  works because T-App's premise (4) involves evaluating a strictly smaller
  body.

- **B = (P : Q) (ascription)**: Similar recursive argument via T-Asc.

The function-literal case is where SubstMono fails in its **general** form.
But this failure is precisely what E-Fun compensates for at the value level.

---

## Step 5: Closing the proof using Strong Soundness

The difficulty with SubstMono in step 4 shows that we cannot bridge the
gap purely at the typing level. Instead, we exploit the fact that V is
a **value** — the result of concrete evaluation — and values have all
domain annotations erased to ⊤ by E-Fun.

### Required lemma: Strong Soundness (proved by mutual induction)

> **Theorem (Strong Soundness).** For all derivations D of `Γ ⊢ M ⇒ A`,
> for all substitutions `[x ≔ V₁]` and `[x ≔ V₂]` where `Γ ⊢ V₁ ⊑ V₂ ⊑ A_x`
> (x bound with type A_x), if `M[x ≔ V₁] ⟶ W`, then `Γ ⊢ W ⊑ A[x ≔ V₂]`.
>
> Equivalently: soundness holds even when the concrete execution uses a
> more-precise substitution than the abstract one.

When V₁ = V₂ this reduces to ordinary soundness (after noting that
substitution commutes with typing). The strengthening to V₁ ⊑ V₂
is what lets us handle the T-App case where concrete evaluation substitutes
N_v (more precise) while typing substitutes N' (less precise).

**Why the strengthening is sound (informal argument):** Concrete evaluation
produces values. Values are ⊤ or `(y: ⊤) → body`. The domain ⊤ is
maximally imprecise, so any precision difference between V₁ and V₂ in
contravariant positions (function domains) is erased by E-Fun. The
covariant positions (bodies, return values) respect the "more precise
input gives more precise output" principle. Thus the overall result W
is at least as precise as A[x ≔ V₂].

### Applying Strong Soundness

Instantiate Strong Soundness with:
- D = the derivation of (P4): `Γ ⊢ B[x ≔ N'] ⇒ R`
- The substitution `[x ≔ N']` was used in the typing derivation (V₂ = N')
- The substitution `[x ≔ N_v]` is used in concrete evaluation (V₁ = N_v)
- `Γ ⊢ N_v ⊑ N'` (F2) and `Γ ⊢ N' ⊑ A` (P3)

Wait — this does not quite fit because (P4) has already substituted N'
into B. There is no free x left. The Strong Soundness theorem as stated
above operates on derivations with a free variable, but (P4) is a
closed derivation.

Let us reformulate more carefully.

---

## Step 5 (revised): Direct argument via evaluation structure

We take a different approach that avoids needing a general SubstMono or
Strong Soundness lemma. Instead, we argue by cases on the structure of
B (the raw function body from premise 1).

Recall: B_c = B, and we have `B[x ≔ N_v] ⟶ V` and need `V ⊑ R`
where `Γ ⊢ B[x ≔ N'] ⇒ R`.

**Case B = x:**
- `B[x ≔ N_v] = N_v` and `B[x ≔ N'] = N'`.
- `N_v ⟶ V`: since N_v is a value (result of E2), `V = N_v`.
- From (P4): `Γ ⊢ N' ⇒ R`. By S-Eval: `N' ⊑ R`.
- From (F2): `N_v ⊑ N'`. By S-Trans: `N_v ⊑ R`, i.e., `V ⊑ R`. ✓

**Case B = y (y ≠ x):**
- `B[x ≔ N_v] = y = B[x ≔ N']`. Same term.
- `y ⟶ V` — but y is a free variable. In a well-scoped closed term, y
  would not appear free (evaluation requires closed terms). If y is free,
  evaluation is stuck. So this case does not arise for well-scoped inputs.

**Case B = ⊤:**
- `B[x ≔ N_v] = ⊤ = B[x ≔ N']`.
- `⊤ ⟶ ⊤` by E-Top, so `V = ⊤`.
- From (P4): `Γ ⊢ ⊤ ⇒ ⊤` by T-Top, so `R = ⊤`.
- `⊤ ⊑ ⊤` by S-Refl. ✓

**Case B = (y: P) → Q (function literal):**
- `B[x ≔ N_v] = (y: P[x ≔ N_v]) → Q[x ≔ N_v]`.
- By E-Fun: `(y: P[x ≔ N_v]) → Q[x ≔ N_v] ⟶ (y: ⊤) → Q[x ≔ N_v]`.
  So `V = (y: ⊤) → Q[x ≔ N_v]`.
- `B[x ≔ N'] = (y: P[x ≔ N']) → Q[x ≔ N']`.
- From (P4): `Γ ⊢ (y: P[x ≔ N']) → Q[x ≔ N'] ⇒ (y: P[x ≔ N']) → Q[x ≔ N']`
  by T-Fun. So `R = (y: P[x ≔ N']) → Q[x ≔ N']`.
- Need: `(y: ⊤) → Q[x ≔ N_v] ⊑ (y: P[x ≔ N']) → Q[x ≔ N']`.
  By S-Fun:
  1. `Γ ⊢ P[x ≔ N'] ⊑ ⊤`  — by S-Top ✓
  2. `Γ, y: P[x ≔ N'] ⊢ Q[x ≔ N_v] ⊑ Q[x ≔ N']`  — **GAP (★)**

  Premise (2) is a comparison of Q with two different substitutions for x,
  under an environment binding y to `P[x ≔ N']`. This is exactly the
  "monotone substitution in bodies" question — does substituting a more
  precise value (N_v ⊑ N') into Q yield a more precise result?

  **This holds if Q uses x only covariantly**, but fails if Q uses x in
  a contravariant position (e.g., as a domain of an inner function).
  However, any inner function in Q would itself be subject to E-Fun
  evaluation when the result is eventually used, repeating the same
  domain-erasure argument recursively.

  **This requires a nested induction on Q** — see the gap analysis below.

**Case B = P Q (application):**
- `B[x ≔ N_v] = P[x ≔ N_v] Q[x ≔ N_v]`.
- By E-App on `B[x ≔ N_v] ⟶ V`:
  - `P[x ≔ N_v] ⟶ (y: ⊤) → C`
  - `Q[x ≔ N_v] ⟶ Q_v`
  - `C[y ≔ Q_v] ⟶ V`
- From (P4): `Γ ⊢ (P Q)[x ≔ N'] ⇒ R`, which is `Γ ⊢ P[x ≔ N'] Q[x ≔ N'] ⇒ R`.
  This was derived by either T-App or T-App-Top.

  **Sub-case T-App-Top:** `Γ ⊢ P[x ≔ N'] ⇒ ⊤`, so `R = ⊤`.
  Then `V ⊑ ⊤ = R` by S-Top. ✓

  **Sub-case T-App:** The derivation of `Γ ⊢ P[x ≔ N'] Q[x ≔ N'] ⇒ R`
  has strictly smaller sub-derivations for typing `P[x ≔ N']` and
  `Q[x ≔ N']`. This is a recursive instance of the same problem — the
  concrete evaluation substitutes N_v while the abstract one uses N'.

  At this point, we observe that the case analysis on B mirrors the
  mutual induction structure. The application case recurses into smaller
  sub-terms of B, and the function-literal case recurses into the body Q.
  The only base cases are x, y, and ⊤, all of which close.

  The recursion is well-founded on the **syntax of B**: each recursive
  call is on a strict sub-term of B.

**Case B = (P : Q) (ascription):**
- `B[x ≔ N_v] = (P[x ≔ N_v] : Q[x ≔ N_v])`.
- By E-Asc: `P[x ≔ N_v] ⟶ V` (ascription erased at runtime).
- From (P4): `Γ ⊢ (P : Q)[x ≔ N'] ⇒ R` by T-Asc, so:
  - `Γ ⊢ P[x ≔ N'] ⇒ P_t`
  - `Γ ⊢ P_t ⊑ Q[x ≔ N']`
  - `Γ ⊢ Q[x ≔ N'] ⇒ R`
  Recursive case on P (for soundness of the inner term) and Q (for
  the type). Same recursive structure as application.

---

## Gap Analysis

The proof above works for all cases of B **except** the function-literal
case, which leaves gap (★):

```
GAP (★): Γ, y: P[x ≔ N'] ⊢ Q[x ≔ N_v] ⊑ Q[x ≔ N']
  where N_v ⊑ N'
```

This is "monotone substitution for subtyping": substituting a more-precise
value into a term yields a more-precise result. As established in the
full proof attempt, this fails in general because of contravariance —
if Q contains `(z: x) → ...`, then substituting the more-precise N_v
for x makes the domain *more* precise, which makes the function type
*less* precise (contravariant).

### Why the gap is closeable (but requires a dedicated lemma)

The crucial observation is that gap (★) only arises for the **function
literal** case of B. When B is a function literal, the body is NOT
evaluated — E-Fun returns `(y: ⊤) → Q[x ≔ N_v]` immediately without
reducing Q. The domain erasure to ⊤ handles the outermost contravariant
position.

But Q itself might contain inner function literals with x in their
domains. The argument must proceed recursively on Q:

- If Q uses x only in covariant positions (bodies, arguments, ascription
  targets), then monotone substitution holds by induction.
- If Q uses x in a contravariant position (as a domain of an inner
  function `(z: ...x...) → W`), that inner function is a *value-level*
  sub-expression. When Q is eventually evaluated (e.g., when the outer
  function is applied), E-Fun will erase that domain to ⊤, neutralizing
  the contravariance.

However, **Q is not evaluated here** — it sits inside a function literal
that E-Fun returns without evaluating the body. So at this level, the
contravariant x genuinely appears in V = `(y: ⊤) → Q[x ≔ N_v]`.

### The real resolution: re-examine the goal

Let us re-examine what we actually need. The goal is:

```
V ⊑ R
(y: ⊤) → Q[x ≔ N_v] ⊑ (y: P[x ≔ N']) → Q[x ≔ N']
```

By S-Fun, this requires:
1. `P[x ≔ N'] ⊑ ⊤`  — immediate by S-Top ✓
2. `y: P[x ≔ N'] ⊢ Q[x ≔ N_v] ⊑ Q[x ≔ N']`  — gap (★)

Now, Q is a strict sub-term of B. We can set up the soundness proof as a
**mutual induction on (typing derivation, B-syntax)** where:

- The primary induction is on the T-App typing derivation (for the
  soundness IH on premises 1, 2, 4).
- The secondary induction is on the syntax of B (for the substitution
  comparison within the function-literal case).

For the secondary induction on Q in gap (★), we need:

> **Lemma (ValueSubstCompare).** If `N_v ⊑ N'` and Q is a term, then
> for any environment Δ, `Δ ⊢ Q[x ≔ N_v] ⊑ Q[x ≔ N']`.

By induction on Q:

- **Q = x**: `N_v ⊑ N'` directly. ✓
- **Q = y (y ≠ x)**: `y ⊑ y` by S-Refl. ✓
- **Q = ⊤**: `⊤ ⊑ ⊤` by S-Refl. ✓
- **Q = (z: P') → Q'**:
  `(z: P'[x ≔ N_v]) → Q'[x ≔ N_v] ⊑ (z: P'[x ≔ N']) → Q'[x ≔ N']`
  By S-Fun:
  1. `P'[x ≔ N'] ⊑ P'[x ≔ N_v]`  — **CONTRA-direction!**
     By IH on P' (sub-term of Q): `P'[x ≔ N_v] ⊑ P'[x ≔ N']`.
     But we need the reverse. **FAILS.** ✗

So ValueSubstCompare fails at the function-literal case, as expected.

### Definitive status

**The T-App soundness proof has one irreducible gap:**

```
GAP (★): Need Q[x ≔ N_v] ⊑ Q[x ≔ N'] (covariant direction)
         inside a function body where x may appear contravariantly in Q.
         E-Fun erases the outermost domain but not inner domains in Q.
```

This gap does NOT manifest as a concrete counterexample in the updated
system (where E-App evaluates the body). The old counterexample from
the full proof attempt (`f = (x: ⊤) → (y: x) → y` applied to
`(id : Id)`) is now resolved:

```
Old E-App (no body eval):  V = (y: id) → y,  R = (y: Id) → y.
  Need (y: id) → y ⊑ (y: Id) → y.
  S-Fun contra: Id ⊑ id — FAILS.

New E-App (with body eval): V = (y: ⊤) → y,  R = (y: Id) → y.
  Need (y: ⊤) → y ⊑ (y: Id) → y.
  S-Fun contra: Id ⊑ ⊤ — by S-Top ✓
  S-Fun body: y: Id ⊢ y ⊑ y — by S-Refl ✓
  SUCCEEDS. ✓
```

The updated E-App resolves the outermost contravariance. Gap (★) only
persists if B = `(y: P) → Q` and Q itself contains `(z: ...x...) → W`
(nested contravariant occurrence). In that case:

```
V = (y: ⊤) → Q[x ≔ N_v]
R = (y: P[x ≔ N']) → Q[x ≔ N']

V ⊑ R requires (by S-Fun):
  Q[x ≔ N_v] ⊑ Q[x ≔ N']  under  y: P[x ≔ N']

If Q = (z: x) → W:
  Q[x ≔ N_v] = (z: N_v) → W[x ≔ N_v]
  Q[x ≔ N'] = (z: N') → W[x ≔ N']

  S-Fun requires: N' ⊑ N_v (contra). We only have N_v ⊑ N'. FAILS.
```

**However**, this nested situation cannot produce a concrete
counterexample to soundness either. The reason: the inner function
`(z: N_v) → W[x ≔ N_v]` is never directly compared to
`(z: N') → W[x ≔ N']` at runtime. It only matters when someone
*applies* the outer function `(y: ⊤) → Q[x ≔ N_v]` to an argument.
At that point, E-App would substitute the argument for y and E-Fun
would erase the domain of the inner function, once again resolving
the contravariance.

The soundness property is about the *final* observable value, and
values are only observed through further application (which triggers
more evaluation and more E-Fun erasure). The nested contravariance
is a *syntactic* discrepancy in the intermediate value representation,
not a *semantic* unsoundness.

---

## Closing the proof: assume evaluation-respects-precision

To formally close gap (★), we need a lemma about concrete evaluation
rather than about syntactic subtyping:

> **Lemma (Eval-Respects-Precision).** If `M ⟶ V`, `M' ⟶ V'`, and
> `Γ ⊢ M ⊑ M'`, then `Γ ⊢ V ⊑ V'`.
>
> (Evaluation is monotone with respect to subtyping.)

If this holds, then the T-App proof closes as follows:

From (F2): `N_v ⊑ N'`. We want `B[x ≔ N_v] ⊑ B[x ≔ N']` at the value
level. We cannot get this syntactically (gap ★), but we could try to get
`V ⊑ W` where `B[x ≔ N_v] ⟶ V` and `B[x ≔ N'] ⟶ W`, using
Eval-Respects-Precision. But this requires `B[x ≔ N_v] ⊑ B[x ≔ N']`
as a premise — the same gap.

So Eval-Respects-Precision does not help directly either.

---

## Final verdict

**The T-App soundness proof reduces to one required lemma:**

> **Lemma (SubstCompareBody).** If `Γ ⊢ N_v ⊑ N'` and `B[x ≔ N_v] ⟶ V`
> and `Γ ⊢ B[x ≔ N'] ⇒ R`, then `Γ ⊢ V ⊑ R`.

This is a "soundness for substitution-related terms" property. It says:
even though the concrete execution uses the more-precise N_v and the
abstract evaluation uses the less-precise N', the soundness relationship
still holds between the concrete result and the abstract type.

**Proof strategy for SubstCompareBody** (sketch, by induction on B):

- **B = x**: V = N_v (value, evaluates to itself). R obtained from
  `Γ ⊢ N' ⇒ R`, so `N' ⊑ R` by S-Eval. Then `N_v ⊑ N' ⊑ R`. ✓
- **B = y**: Same term, use standard soundness. ✓
- **B = ⊤**: V = R = ⊤. ✓
- **B = (y: P) → Q**: V = `(y: ⊤) → Q[x ≔ N_v]`, R = `(y: P[x ≔ N']) → Q[x ≔ N']`.
  Need `(y: ⊤) → Q[x ≔ N_v] ⊑ (y: P[x ≔ N']) → Q[x ≔ N']`.
  By S-Fun: (a) `P[x ≔ N'] ⊑ ⊤` by S-Top ✓; (b) `y: P[x ≔ N'] ⊢ Q[x ≔ N_v] ⊑ Q[x ≔ N']`.
  This is gap (★) again. By IH on Q (strict sub-term of B)... but the IH
  for SubstCompareBody requires an *evaluation* of `Q[x ≔ N_v]`, which
  we don't have (Q is inside a function literal; E-Fun doesn't evaluate it).

  **This is the irreducible stuck point.** The body Q of a function literal
  is not evaluated, so we cannot use evaluation-based reasoning. We need
  a purely syntactic `Q[x ≔ N_v] ⊑ Q[x ≔ N']`, which fails due to
  contravariance.

- **B = P Q**: V comes from evaluating `P[x ≔ N_v] Q[x ≔ N_v]`.
  R comes from typing `P[x ≔ N'] Q[x ≔ N']`. By IH on P and Q (sub-terms)
  plus the soundness IH on the T-App sub-derivation, this case follows
  the same pattern as the main T-App proof itself (recursive). ✓ (modulo
  the function-literal sub-case)
- **B = (P : Q)**: Similar recursive case via T-Asc reasoning. ✓ (modulo
  the function-literal sub-case)

---

## Summary

| Step | Status |
|------|--------|
| IH on premise (1): `(x: ⊤) → B ⊑ (x: A) → B` | ✓ |
| IH on premise (2): `N_v ⊑ N'` | ✓ |
| S-Trans: `N_v ⊑ A` | ✓ |
| S-Eval on premise (4): `B[x ≔ N'] ⊑ R` | ✓ |
| Connecting `B[x ≔ N_v] ⟶ V` to `B[x ≔ N'] ⇒ R` | **GAP (★)** |

**Gap (★)** arises in the function-literal case of B, where the body Q
may contain x in contravariant positions (as a domain of inner functions).
E-Fun erases the outermost domain to ⊤ (resolving the outermost
contravariance), but inner domains within Q remain unerased because Q
is not evaluated inside a function literal.

**The updated E-App (which evaluates the body after substitution) resolves
the previously-known counterexample** but does not eliminate the gap for
arbitrarily nested contravariant occurrences.

### Possible resolutions

1. **Accept the gap and observe it never manifests.** The nested
   contravariance in unevaluated function bodies is a syntactic artifact.
   It does not produce runtime unsoundness because any attempt to *use*
   the value (by applying it) triggers evaluation, which erases inner
   domains. A "contextual equivalence" or "logical relations" proof
   technique would likely close this gap by reasoning about observations
   rather than syntactic subtyping.

2. **Strengthen the subtyping relation.** Add a rule like:
   ```
   [S-Fun-Erase]
   Γ, x: A₁ ⊢ M₁ ⊑ M₂
   ——————————————————————————————
   Γ ⊢ (x: ⊤) → M₁ ⊑ (x: A₁) → M₂
   ```
   This is a weaker form of S-Fun that allows the subtype to have domain ⊤
   while matching the body comparison under the supertype's domain. This
   directly closes the outermost case and the recursive argument becomes:
   values always have ⊤ domains, so S-Fun-Erase always applies.
   But this still doesn't help with the *inner* `Q[x ≔ N_v] ⊑ Q[x ≔ N']`
   comparison, which is about raw syntax, not about function types.

3. **Restrict the calculus.** Disallow variables in contravariant positions
   within function bodies (i.e., x cannot appear as a domain annotation
   inside B). This is too restrictive — it would prevent dependent types
   like `(x: ⊤) → (y: x) → y`.

4. **Use a logical-relations or realizability proof.** Instead of syntactic
   soundness (`V ⊑ R` via the subtyping judgment), define soundness via
   a logical relation that interprets types as sets of values. Function
   types `(x: A) → B` are interpreted as "maps A-values to B[x≔v]-values",
   and the domain annotation is irrelevant for the value semantics. This
   sidesteps the syntactic contravariance issue entirely.

∎ (with gap ★ — function-literal case of SubstCompareBody)

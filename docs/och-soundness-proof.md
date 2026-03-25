# Soundness Proof Attempt for Och₀

## Theorem (Soundness)

> If `Γ ⊢ M ⇒ A` and `M ⟶ V`, then `Γ ⊢ V ⊑ A`.

That is: if abstract evaluation assigns M the type A, and concrete evaluation
reduces M to V, then V is at least as precise as A (V is a subtype of A).

---

## Preliminary Observations

### On open terms and evaluation

The concrete evaluation judgment `M ⟶ V` has no environment — it is a
substitution-based big-step semantics. Variables have no evaluation rule, so
`x ⟶ V` is never derivable. The theorem is vacuously true for terms that
do not evaluate (the premise `M ⟶ V` simply fails). In practice, the
interesting cases are closed terms or terms where all free variables have
been substituted away before evaluation.

However, the typing judgment uses an environment Γ that may be non-empty.
The theorem as stated allows Γ to be arbitrary, which means we must handle
the case where M contains free variables that happen not to block evaluation.
For example, `(M : A) ⟶ V` fires E-Asc regardless of free variables in A,
as long as M evaluates.

### On the evaluation semantics

E-App does NOT further reduce the body after substitution:

```
[E-App]
M ⟶ (x: A) → B
N ⟶ N'
——————————————————————————
M N ⟶ B[x ≔ N']
```

The result `B[x ≔ N']` is the final answer — it is not recursively
evaluated. This is a single beta-step semantics (weak head normal form
style). The result of evaluation can be an application, a variable, or
any other term — not just syntactic values like ⊤ or functions.

---

## Required Lemmas

### Lemma 1 (Subtyping Reflexivity)

> For all Γ, A: `Γ ⊢ A ⊑ A`.

**Status**: Axiom (S-Refl).

### Lemma 2 (Subtyping Transitivity)

> If `Γ ⊢ A ⊑ B` and `Γ ⊢ B ⊑ C`, then `Γ ⊢ A ⊑ C`.

**Status**: Axiom (S-Trans).

### Lemma 3 (Substitution for Typing)

> If `Γ, x: A ⊢ M ⇒ B` and `Γ ⊢ V ⊑ A`, then `Γ ⊢ M[x ≔ V] ⇒ B'`
> for some B' with `Γ ⊢ B' ⊑ B[x ≔ V]`.

This lemma says: if M types to B under an assumption x: A, and we substitute
a value V (which is a subtype of A) for x, then the substituted term has a
type at least as precise as B with V substituted in.

**Status**: NOT PROVED. This lemma is highly non-trivial and may not hold
as stated. See discussion in the T-App case below.

Actually, the lemma we need is more specific. Let me state what T-App
actually requires and revisit this after the case analysis.

### Lemma 4 (Monotone Substitution for Subtyping)

> If `Γ, x: C ⊢ B₁ ⊑ B₂` and `Γ ⊢ V₁ ⊑ V₂` and `Γ ⊢ V₁ ⊑ C` and
> `Γ ⊢ V₂ ⊑ C`, then `Γ ⊢ B₁[x ≔ V₁] ⊑ B₂[x ≔ V₂]`.

This says: subtyping is preserved under substitution, and moreover,
substituting more-precise terms into the more-precise side and less-precise
terms into the less-precise side preserves the ordering.

**Status**: NOT PROVED. This is the key lemma needed for T-App and is
where the proof encounters serious difficulties. See detailed discussion below.

### Lemma 5 (Substitution for Subtyping — equal substitution)

A simpler variant:

> If `Γ, x: C ⊢ B₁ ⊑ B₂` and `Γ ⊢ V ⊑ C`, then
> `Γ ⊢ B₁[x ≔ V] ⊑ B₂[x ≔ V]`.

**Status**: NOT PROVED, but more plausible than Lemma 4. This says subtyping
is preserved when we perform the same substitution on both sides. Even this
is non-trivial because subtyping derivations may use S-Var with x in scope,
and after substitution, those uses must be replaced by direct reasoning about V.

### Lemma 6 (Weakening)

> If `Γ ⊢ A ⊑ B` then `Γ, x: C ⊢ A ⊑ B` (for x not free in Γ, A, B).

**Status**: Assumed. Standard structural property.

---

## Main Proof Attempt

By induction on the derivation of `Γ ⊢ M ⇒ A`.

---

### Case T-Top

```
[T-Top]
———————————
Γ ⊢ ⊤ ⇒ ⊤
```

We have M = ⊤ and A = ⊤. The only evaluation rule for ⊤ is:

```
[E-Top]
———————————
⊤ ⟶ ⊤
```

So V = ⊤. We need `Γ ⊢ ⊤ ⊑ ⊤`, which holds by S-Refl. **QED.**

---

### Case T-Var

```
[T-Var]
x: A ∈ Γ
———————————
Γ ⊢ x ⇒ A
```

We have M = x. There is no evaluation rule for variables, so `x ⟶ V` is
never derivable. The case is **vacuously true**. **QED.**

---

### Case T-Fun

```
[T-Fun]
—————————————————————————————————————————
Γ ⊢ (x: A) → M ⇒ (x: A) → M
```

We have M₀ = (x: A) → M (the outer term) and A₀ = (x: A) → M (the type
— they are identical). The evaluation rule is:

```
[E-Fun]
———————————
(x: A) → M ⟶ (x: A) → M
```

So V = (x: A) → M = A₀. We need `Γ ⊢ (x: A) → M ⊑ (x: A) → M`,
which holds by S-Refl. **QED.**

---

### Case T-Asc

```
[T-Asc]
Γ ⊢ M ⇒ M'
Γ ⊢ M' ⊑ A
———————————
Γ ⊢ (M : A) ⇒ A
```

We have the outer term (M : A) and the type is A. By E-Asc:

```
[E-Asc]
M ⟶ V
———————————
(M : A) ⟶ V
```

So `(M : A) ⟶ V` where `M ⟶ V`.

By the induction hypothesis on `Γ ⊢ M ⇒ M'` with `M ⟶ V`:
we get `Γ ⊢ V ⊑ M'`.

We have `Γ ⊢ M' ⊑ A` from the typing premise.

By S-Trans: `Γ ⊢ V ⊑ A`. **QED.**

---

### Case T-App-Top

```
[T-App-Top]
Γ ⊢ M ⇒ ⊤
——————————————————————————
Γ ⊢ M N ⇒ ⊤
```

We have the term `M N` and the type ⊤. We assume `M N ⟶ V`.

For `M N ⟶ V` to be derivable, the only applicable evaluation rule is E-App
(since M N is an application). E-App requires M to evaluate to a function:

```
[E-App]
M ⟶ (x: A') → B'
N ⟶ N'
——————————————————————————
M N ⟶ B'[x ≔ N']
```

So `M ⟶ (x: A') → B'` for some A', B'.

By the induction hypothesis on `Γ ⊢ M ⇒ ⊤` with `M ⟶ (x: A') → B'`:
we get `Γ ⊢ (x: A') → B' ⊑ ⊤`.

This holds (by S-Top, any term is a subtype of ⊤), which is consistent
but tells us nothing useful about the function.

We need `Γ ⊢ V ⊑ ⊤` where V = B'[x ≔ N']. This holds by S-Top. **QED.**

---

### Case T-App (THE CRITICAL CASE)

```
[T-App]
Γ ⊢ M ⇒ (x: A) → B
Γ ⊢ N ⇒ N'
Γ ⊢ N' ⊑ A
——————————————————————————
Γ ⊢ M N ⇒ B[x ≔ N']
```

We have the term `M N` and the type `B[x ≔ N']`. We assume `M N ⟶ V`.

By E-App:
```
M ⟶ (x: A_c) → B_c
N ⟶ N_c
——————————————————————————
M N ⟶ B_c[x ≔ N_c]
```

So V = B_c[x ≔ N_c], and we need to show:

> **Goal**: `Γ ⊢ B_c[x ≔ N_c] ⊑ B[x ≔ N']`

**Step 1: Apply IH to M.**

From the first premise, `Γ ⊢ M ⇒ (x: A) → B`, and `M ⟶ (x: A_c) → B_c`,
by the induction hypothesis:

> `Γ ⊢ (x: A_c) → B_c ⊑ (x: A) → B`

By inversion on S-Fun (the only rule that can derive a subtyping between
two function types):

> (i) `Γ ⊢ A ⊑ A_c`  (contravariant in domain)
> (ii) `Γ, x: A ⊢ B_c ⊑ B`  (covariant in body, under the supertype's domain)

**Step 2: Apply IH to N.**

From the second premise, `Γ ⊢ N ⇒ N'`, and `N ⟶ N_c`, by the IH:

> (iii) `Γ ⊢ N_c ⊑ N'`

**Step 3: Establish what we know about N_c.**

From the typing premises we have `Γ ⊢ N' ⊑ A` (premise 3).
From (iii): `Γ ⊢ N_c ⊑ N'`.
By S-Trans: `Γ ⊢ N_c ⊑ A`.
By (i) and S-Trans: `Γ ⊢ N_c ⊑ A_c`.

So N_c is a subtype of both A and A_c.

**Step 4: The substitution gap.**

We have:
- (ii): `Γ, x: A ⊢ B_c ⊑ B`
- (iii): `Γ ⊢ N_c ⊑ N'`
- `Γ ⊢ N_c ⊑ A`
- `Γ ⊢ N' ⊑ A`

We need: `Γ ⊢ B_c[x ≔ N_c] ⊑ B[x ≔ N']`

This requires a **monotone substitution lemma** (Lemma 4 above):

> If `Γ, x: A ⊢ B_c ⊑ B` and `Γ ⊢ N_c ⊑ N'` and `Γ ⊢ N_c ⊑ A` and
> `Γ ⊢ N' ⊑ A`, then `Γ ⊢ B_c[x ≔ N_c] ⊑ B[x ≔ N']`.

This is the lemma we need. Let us examine whether it holds.

#### Analysis of the Monotone Substitution Lemma

The lemma must handle all the ways x can appear in B_c and B. Let us
consider what happens when we substitute into the various subtyping
derivation rules.

**Sub-case: x appears in a variable position via S-Var.**

Suppose the derivation of `Γ, x: A ⊢ B_c ⊑ B` uses S-Var at some point
with the variable x. S-Var says:

```
x: A ∈ (Γ, x: A)
Γ, x: A ⊢ A ⊑ B₀
———————————————
Γ, x: A ⊢ x ⊑ B₀
```

After substitution with N_c on the left and N' on the right, this
becomes a need to show `Γ ⊢ N_c ⊑ B₀[x ≔ N']`.

The original derivation had `Γ, x: A ⊢ A ⊑ B₀`. After substituting:
we would need `Γ ⊢ A[x ≔ N_c] ⊑ B₀[x ≔ N']`.

But wait — the original derivation routed through A (the type of x in
the context). After substitution, we have N_c (not A). We know
`Γ ⊢ N_c ⊑ A`, but we need to go from N_c to B₀[x ≔ N'] via A[x ≔ ...].

This is where things get subtle. The derivation relied on the fact that x
has type A, but after substitution, x is replaced by N_c which is more
precise than A. The S-Var rule used `A` as an intermediary, but now we
need the chain:

```
N_c ⊑ A (known)
A[x ≔ ???] ⊑ B₀[x ≔ N'] (need to establish)
```

But A might itself contain x, and on the left we're substituting N_c
while on the right we're substituting N'. This is a recursive dependency.

**Sub-case: S-Refl on a term containing x.**

If the derivation uses `Γ, x: A ⊢ C ⊑ C` by S-Refl, where C contains x,
then after substitution we need `Γ ⊢ C[x ≔ N_c] ⊑ C[x ≔ N']`. But
N_c ≠ N' in general (N_c is more precise), so C[x ≔ N_c] ≠ C[x ≔ N'],
and S-Refl does not apply.

We would need to know that substituting a more-precise term gives a
more-precise result — which is essentially the **monotonicity** property
for arbitrary terms. But monotonicity is a separate desired property
(Property 2 in och.md) and is NOT something we can assume.

In fact, **monotonicity is known to fail** for certain terms involving
ascription (the counterexample in och.md Section "Monotonicity
Counterexample"). So the monotone substitution lemma is FALSE in general.

#### Counterexample to the Monotone Substitution Lemma

Consider B_c = B = `(M₀ : x)` where M₀ is some fixed closed term.

We have `Γ, x: A ⊢ (M₀ : x) ⊑ (M₀ : x)` by S-Refl.

After substitution on left with N_c and right with N':
we need `Γ ⊢ (M₀ : N_c) ⊑ (M₀ : N')`.

But subtyping of ascription terms is not directly addressed by the
rules — ascription is a typing construct, not a subtyping form. In fact,
`(M₀ : N_c)` and `(M₀ : N')` are terms, and the subtyping rules only
decompose ⊤, variables, and function types. There is no subtyping rule
for ascription terms.

This means `(M₀ : N_c) ⊑ (M₀ : N')` is only derivable via S-Refl
(if N_c = N') or S-Top (if the right side is ⊤). Since N_c and N'
may differ, and N' may not be ⊤, this is **not derivable in general**.

#### Can we avoid the monotone substitution lemma?

The monotone lemma is needed because T-App substitutes N' (the type of
the argument) into B, while E-App substitutes N_c (the concrete value)
into B_c. These are DIFFERENT substitutions on DIFFERENT bodies.

If N_c = N' and B_c = B, then we'd just need the simple substitution
lemma (Lemma 5), which only substitutes the same thing on both sides.
But in general, N_c is more precise than N', and B_c may differ from B.

**Could we weaken the theorem?** If we only considered closed terms
(where Γ = ·) and values that are ⊤ or functions, then the bodies
B_c and B would be syntactically constrained. But even for closed terms,
the issue persists because the abstract and concrete evaluations
substitute different things.

**The core tension**: Abstract evaluation substitutes the *type* of the
argument (N') into the *type* of the body (B). Concrete evaluation
substitutes the *value* of the argument (N_c) into the *body* (B_c).
These diverge because:
1. N_c is more precise than N' (concrete vs abstract argument).
2. B_c may be more precise than B (concrete vs abstract body).

Soundness requires that these two divergences cancel out or compound
in a way that preserves the subtyping direction. This amounts to
monotonicity — and we know monotonicity can fail.

#### However: does a concrete counterexample to soundness exist?

The monotonicity counterexample in och.md involves `False : b`, which
requires `False ⊑ b` — and the document notes this is already rejected
by the typing rules (tests 23, 24). So that specific counterexample
does NOT produce a soundness violation (the typing premise fails).

Let us search for an actual soundness counterexample. We need:
- `Γ ⊢ M ⇒ A` is derivable (typing succeeds)
- `M ⟶ V` is derivable (evaluation succeeds)
- `Γ ⊢ V ⊑ A` is NOT derivable (the result is not a subtype of the type)

**Attempt 1: Simple application.**

```
M = ((x: ⊤) → x) ⊤
```

Typing: `· ⊢ ((x: ⊤) → x) ⊤ ⇒ x[x ≔ ⊤] = ⊤` (by T-App, ⊤ ⊑ ⊤ by S-Refl)
Evaluation: `((x: ⊤) → x) ⊤ ⟶ x[x ≔ ⊤] = ⊤`
Check: `· ⊢ ⊤ ⊑ ⊤` by S-Refl. OK.

**Attempt 2: Higher-order application.**

```
M = ((f: (x: ⊤) → ⊤) → f ⊤) ((x: ⊤) → x)
```

Typing of M:
- The function `(f: (x: ⊤) → ⊤) → f ⊤` has type `(f: (x: ⊤) → ⊤) → f ⊤` by T-Fun.
- To apply T-App, we check the argument's type against the domain:
  - `· ⊢ (x: ⊤) → x ⇒ (x: ⊤) → x` by T-Fun, so N' = (x: ⊤) → x.
  - Need `· ⊢ (x: ⊤) → x ⊑ (x: ⊤) → ⊤`? By S-Fun: need ⊤ ⊑ ⊤ (OK)
    and x: ⊤ ⊢ x ⊑ ⊤ (by S-Var + S-Top, OK). Yes, this holds.
- Result type: `(f ⊤)[f ≔ (x: ⊤) → x] = ((x: ⊤) → x) ⊤`.

So `· ⊢ M ⇒ ((x: ⊤) → x) ⊤`.

Note: the result type `((x: ⊤) → x) ⊤` is itself an application — it
is NOT further reduced/normalized by the typing rules. T-App produces
`B[x ≔ N']`, which here is `(f ⊤)[f ≔ (x: ⊤) → x]` = `((x: ⊤) → x) ⊤`.

Evaluation of M:
- `(f: (x: ⊤) → ⊤) → f ⊤ ⟶ (f: (x: ⊤) → ⊤) → f ⊤` by E-Fun
- `(x: ⊤) → x ⟶ (x: ⊤) → x` by E-Fun
- `M ⟶ (f ⊤)[f ≔ (x: ⊤) → x] = ((x: ⊤) → x) ⊤` by E-App

So V = ((x: ⊤) → x) ⊤ = A. Check: V ⊑ A by S-Refl. OK.

This example works because B_c = B (the function is its own type) and
N_c = N' (the argument is a closed value equal to its own type). In this
specific case, the substitution is identical on both sides.

**Attempt 3: Ascription in the argument.**

```
M = ((x: ⊤) → x) (((y: ⊤) → y) : (y: ⊤) → ⊤)
```

The argument is `((y: ⊤) → y) : (y: ⊤) → ⊤`.

Typing the argument:
- `· ⊢ (y: ⊤) → y ⇒ (y: ⊤) → y` (T-Fun)
- `· ⊢ (y: ⊤) → y ⊑ (y: ⊤) → ⊤` (S-Fun, as before)
- By T-Asc: `· ⊢ ((y: ⊤) → y) : (y: ⊤) → ⊤ ⇒ (y: ⊤) → ⊤`

So N' = (y: ⊤) → ⊤.

Typing M:
- Function type: (x: ⊤) → x, domain A = ⊤, body B = x.
- `· ⊢ (y: ⊤) → ⊤ ⊑ ⊤` by S-Top. OK.
- Result: `x[x ≔ (y: ⊤) → ⊤] = (y: ⊤) → ⊤`.

So `· ⊢ M ⇒ (y: ⊤) → ⊤`.

Evaluation of M:
- Argument evaluates: `((y: ⊤) → y) : (y: ⊤) → ⊤ ⟶ (y: ⊤) → y` by E-Asc + E-Fun.
  So N_c = (y: ⊤) → y.
- Function evaluates: `(x: ⊤) → x ⟶ (x: ⊤) → x` by E-Fun.
- Body substitution: `x[x ≔ (y: ⊤) → y] = (y: ⊤) → y`.

So V = (y: ⊤) → y.

Check: `· ⊢ (y: ⊤) → y ⊑ (y: ⊤) → ⊤`?
By S-Fun: need `· ⊢ ⊤ ⊑ ⊤` (OK) and `y: ⊤ ⊢ y ⊑ ⊤` (by S-Top, OK). Yes.

So V ⊑ A. **Soundness holds here**, and in fact V is MORE precise than A.
This is the expected scenario: concrete evaluation gives back the actual
identity function, which is more precise than the ascribed type (y: ⊤) → ⊤.

**Attempt 4: Constructing a real counterexample.**

For soundness to fail, we need the concrete evaluation to produce something
LESS precise than the static type. Since concrete evaluation is "more
precise" (it has the actual values), this seems unlikely for well-typed
terms. The question is whether the abstract evaluation can be "too optimistic"
— i.e., compute a type that is more precise than warranted.

Consider: can T-App compute an overly-precise result?

T-App substitutes N' (the type of the argument) into B (the abstract body).
E-App substitutes N_c (the value of the argument) into B_c (the concrete body).

We know:
- B_c ⊑ B (from IH on M, via S-Fun)
- N_c ⊑ N' (from IH on N)

The question is: does `B_c[x ≔ N_c] ⊑ B[x ≔ N']` follow?

In the case where B is a simple term not involving x, both substitutions
are no-ops and B_c ⊑ B directly gives us the result.

In the case where B = x, we need N_c ⊑ N', which is (iii). OK.

In the case where B = (y: C) → D (a function type involving x), we need
structural analysis. After substitution:
- Left: (y: C[x ≔ N_c]) → D[x ≔ N_c]
- Right: (y: C[x ≔ N']) → D[x ≔ N']

And the original `Γ, x: A ⊢ B_c ⊑ B` by S-Fun would give us:
- `Γ, x: A ⊢ C ⊑ C_c` (contravariance)
- `Γ, x: A, y: C ⊢ D_c ⊑ D` (covariance)

After substitution we need:
- `Γ ⊢ C[x ≔ N'] ⊑ C_c[x ≔ N_c]` (contravariance)
- `Γ, y: C[x ≔ N'] ⊢ D_c[x ≔ N_c] ⊑ D[x ≔ N']` (covariance)

The contravariant case needs C[x ≔ N'] ⊑ C_c[x ≔ N_c]. From
`Γ, x: A ⊢ C ⊑ C_c`, substituting with the MORE precise N_c on the
right side (the C_c side) could make C_c[x ≔ N_c] more precise, which
would help the contravariant direction. And substituting the LESS precise
N' on the left (the C side) could make C[x ≔ N'] less precise, also
helping. So the directions work in our favor for contravariance.

The covariant case needs D_c[x ≔ N_c] ⊑ D[x ≔ N']. From
`Γ, x: A, y: C ⊢ D_c ⊑ D`, we need the more precise substitution (N_c)
on the more precise side (D_c) and the less precise (N') on the less
precise side (D). This also goes in the right direction for covariance —
but only if the body is monotone in x.

**And this is exactly the monotonicity property.** The proof of the
substitution lemma requires monotonicity, and monotonicity is the very
thing that can fail.

#### The fundamental obstacle

The proof of soundness for T-App reduces to proving a monotone
substitution lemma, which in turn requires the bodies B and B_c to be
**monotone** in x — that is, substituting a more precise value yields
a more precise result.

The document explicitly notes that monotonicity can fail for terms
involving ascription. However, examining this more carefully:

The S-Fun rule compares bodies under the context `Γ, x: B₁` (the
supertype's domain). The IH gives us `Γ, x: A ⊢ B_c ⊑ B`. After
substitution with values that are subtypes of A, we need the subtyping
to be preserved.

**The question is whether B_c and B, as they appear in the bodies of
functions that result from evaluation, can contain ascriptions that
create non-monotone behavior.**

Functions that result from concrete evaluation (via E-Fun) have the form
`(x: A_c) → B_c` where B_c is the UNEVALUATED body. B_c can contain
arbitrary terms, including ascriptions. For example:

```
(x: ⊤) → (⊤ : x)
```

This is a valid function. Its body `⊤ : x` ascribes ⊤ to type x. When
x is ⊤, this is fine (⊤ ⊑ ⊤). When x is a function type, this fails
(⊤ is not a function). However, this term has a specific type behavior
that depends on what x is instantiated to.

But wait — for this function to appear as the result of evaluating M
where `Γ ⊢ M ⇒ (x: A) → B`, we need B to be the abstract body. And
T-Fun says the function IS its own type, so B would be `⊤ : x`. Then
`B[x ≔ N'] = (⊤ : N')` and `B_c[x ≔ N_c] = (⊤ : N_c)`.

For soundness we'd need `(⊤ : N_c) ⊑ (⊤ : N')`. But the subtyping
rules have no rule for ascription terms, so this is only derivable by
S-Refl (if N_c = N') or S-Top (if right side is ⊤).

**However**, note that in this specific scenario, M evaluates to itself
(E-Fun), so B_c = B and A_c = A. The IH gives us the function is a
subtype of itself (S-Refl), which is trivially true. The issue is that
B_c = B, but we're substituting DIFFERENT things: N_c on one side,
N' on the other.

Let me try to construct a CONCRETE soundness violation:

```
Let f = (x: ⊤) → (⊤ : x)

· ⊢ f ((y: ⊤) → y) ⇒ ???
```

Typing:
- `· ⊢ f ⇒ (x: ⊤) → (⊤ : x)` by T-Fun.
- `· ⊢ (y: ⊤) → y ⇒ (y: ⊤) → y` by T-Fun. So N' = (y: ⊤) → y.
- Need N' ⊑ ⊤, which holds by S-Top.
- Result: `(⊤ : x)[x ≔ (y: ⊤) → y] = ⊤ : ((y: ⊤) → y)`.

But wait — is `⊤ : ((y: ⊤) → y)` a well-typed result? The typing
says the result is `⊤ : ((y: ⊤) → y)`. Now let's evaluate:

```
f ((y: ⊤) → y) ⟶ (⊤ : x)[x ≔ (y: ⊤) → y] = ⊤ : ((y: ⊤) → y)
```

V = `⊤ : ((y: ⊤) → y)` = A (the type). V ⊑ A by S-Refl. OK.

Hmm, in this case V = A exactly because B_c = B and N_c = N' (the
argument is a closed function that is its own type).

Let me try with ascription on the argument to create a gap:

```
Let f = (x: ⊤) → (⊤ : x)
Let g = ((y: ⊤) → y) : ((y: ⊤) → ⊤)

· ⊢ f g ⇒ ???
```

Typing of g:
- `· ⊢ (y: ⊤) → y ⇒ (y: ⊤) → y` by T-Fun
- `(y: ⊤) → y ⊑ (y: ⊤) → ⊤` (yes, S-Fun)
- By T-Asc: `· ⊢ g ⇒ (y: ⊤) → ⊤`. So N' = (y: ⊤) → ⊤.

Typing of f g:
- f has type `(x: ⊤) → (⊤ : x)`.
- N' = (y: ⊤) → ⊤, and N' ⊑ ⊤ by S-Top.
- Result: `(⊤ : x)[x ≔ (y: ⊤) → ⊤] = ⊤ : ((y: ⊤) → ⊤)`.

So `· ⊢ f g ⇒ ⊤ : ((y: ⊤) → ⊤)`.

Evaluation of f g:
- f ⟶ (x: ⊤) → (⊤ : x) by E-Fun
- g = ((y: ⊤) → y) : ((y: ⊤) → ⊤) ⟶ (y: ⊤) → y by E-Asc + E-Fun
  So N_c = (y: ⊤) → y.
- f g ⟶ (⊤ : x)[x ≔ (y: ⊤) → y] = ⊤ : ((y: ⊤) → y)

So V = `⊤ : ((y: ⊤) → y)` and A = `⊤ : ((y: ⊤) → ⊤)`.

Need: `· ⊢ (⊤ : ((y: ⊤) → y)) ⊑ (⊤ : ((y: ⊤) → ⊤))`.

These are ascription terms. The subtyping rules have NO structural rule
for ascription. So the only options are:
- S-Refl: fails because the terms are syntactically different.
- S-Top: only if the right side is ⊤, which it is not.

**SOUNDNESS FAILS.**

---

## The Soundness Counterexample

### Setup

```
f = (x: ⊤) → (⊤ : x)
g = ((y: ⊤) → y) : ((y: ⊤) → ⊤)
```

### Typing

```
· ⊢ f g ⇒ ⊤ : ((y: ⊤) → ⊤)
```

Derivation:
1. `· ⊢ f ⇒ (x: ⊤) → (⊤ : x)` by T-Fun.
2. `· ⊢ g ⇒ (y: ⊤) → ⊤` by T-Asc (since (y:⊤)→y ⊑ (y:⊤)→⊤).
3. `· ⊢ (y: ⊤) → ⊤ ⊑ ⊤` by S-Top.
4. By T-App: `· ⊢ f g ⇒ (⊤ : x)[x ≔ (y: ⊤) → ⊤] = ⊤ : ((y: ⊤) → ⊤)`.

### Evaluation

```
f g ⟶ ⊤ : ((y: ⊤) → y)
```

Derivation:
1. `f ⟶ (x: ⊤) → (⊤ : x)` by E-Fun.
2. `g ⟶ (y: ⊤) → y` by E-Asc (erasing the ascription).
3. By E-App: `f g ⟶ (⊤ : x)[x ≔ (y: ⊤) → y] = ⊤ : ((y: ⊤) → y)`.

### Soundness check

Need: `· ⊢ (⊤ : ((y: ⊤) → y)) ⊑ (⊤ : ((y: ⊤) → ⊤))`.

The subtyping rules can decompose:
- **⊤** (via S-Top)
- **Variables** (via S-Var)
- **Functions** (via S-Fun)

There is **no subtyping rule for ascription terms**. The only applicable
rules are S-Refl (requires syntactic equality — fails) and S-Top (requires
right side to be ⊤ — fails).

Therefore `· ⊢ V ⊑ A` is **not derivable**, and **soundness fails**.

### Root cause analysis

There are two distinct issues exposed by this counterexample:

**Issue 1: Missing subtyping rules for ascription terms.**

The subtyping judgment has no rule to compare ascription terms structurally.
A natural candidate would be:

```
[S-Asc] (hypothetical)
Γ ⊢ M₁ ⊑ M₂
Γ ⊢ A₁ ⊑ A₂
—————————————————————
Γ ⊢ (M₁ : A₁) ⊑ (M₂ : A₂)
```

But this is not clearly correct — ascription is supposed to lose
precision, so comparing the inner terms may not give the right semantics.
Another option:

```
[S-Asc-Eval] (hypothetical)
Γ ⊢ M ⇒ M'
Γ ⊢ M' ⊑ B
—————————————————
Γ ⊢ (M : A) ⊑ B
```

This would "look through" ascription during subtyping, using the type
of the inner term. But this mixes typing into subtyping, creating a
mutual dependency.

**Issue 2: The evaluation/typing mismatch for ascription.**

The deeper issue is that E-Asc erases the ascription (returning the inner
value), but T-App preserves ascriptions in the result type (because it
just substitutes syntactically). This means:

- The concrete result `V` can contain ascriptions with more-precise
  annotation terms (because the concrete value of the argument was
  substituted).
- The abstract result `A` contains ascriptions with less-precise
  annotation terms (because the type of the argument was substituted).
- These two ascription terms cannot be compared by the subtyping rules.

Even if we added subtyping rules for ascription, the comparison would
need to handle the fact that the inner annotation differs. The ascribed
value is ⊤ in both cases, so `⊤ ⊑ (y:⊤)→y` would need to hold for
the inner term comparison — which fails.

Actually, a more natural subtyping rule for ascription might be:

```
[S-Asc-Type]
Γ ⊢ A ⊑ B
—————————————————
Γ ⊢ (M : A) ⊑ B
```

This says: an ascription term `(M : A)` is a subtype of B whenever A ⊑ B,
since the ascription promises the result has type A. With this rule:

`· ⊢ (⊤ : ((y: ⊤) → y)) ⊑ (⊤ : ((y: ⊤) → ⊤))`

We'd need `(y: ⊤) → y ⊑ (⊤ : ((y: ⊤) → ⊤))`, which would require
S-Asc-Type again on the right, giving `(y: ⊤) → y ⊑ (y: ⊤) → ⊤`.
Wait, no — the right side `(⊤ : ((y: ⊤) → ⊤))` is an ascription, not
a function. We'd need the rule to work on the right too.

A cleaner approach might be to reduce ascription terms before subtyping,
or to define subtyping on normal forms. But this is a significant design
change.

---

## Summary

### What works

| Case | Status | Notes |
|------|--------|-------|
| T-Top | **Proved** | Trivial: V = ⊤, ⊤ ⊑ ⊤ by S-Refl. |
| T-Var | **Proved** | Vacuously true: variables don't evaluate. |
| T-Fun | **Proved** | Trivial: V = the function itself = A, by S-Refl. |
| T-Asc | **Proved** | Uses IH + S-Trans. Clean. |
| T-App-Top | **Proved** | V ⊑ ⊤ by S-Top. |
| T-App | **FAILS** | Requires monotone substitution lemma, which does not hold. |

### What doesn't work

**The T-App case fails.** The proof requires showing that if
`Γ, x: A ⊢ B_c ⊑ B` and `Γ ⊢ N_c ⊑ N'`, then
`Γ ⊢ B_c[x ≔ N_c] ⊑ B[x ≔ N']`. This is a monotone substitution
lemma that does not hold in general.

### Concrete counterexample to soundness

```
f = (x: ⊤) → (⊤ : x)
g = ((y: ⊤) → y) : ((y: ⊤) → ⊤)

Typing:  · ⊢ f g ⇒ ⊤ : ((y: ⊤) → ⊤)
Eval:    f g ⟶ ⊤ : ((y: ⊤) → y)

V = ⊤ : ((y: ⊤) → y)
A = ⊤ : ((y: ⊤) → ⊤)

V ⊑ A is NOT DERIVABLE.
```

### Issues found in the rules

1. **No subtyping rule for ascription terms.** The subtyping judgment
   can decompose ⊤, variables, and functions, but not ascription.
   When evaluation produces terms containing ascription (which happens
   because E-App does not reduce the body after substitution), subtyping
   cannot compare them.

2. **Evaluation does not reduce ascription terms in function bodies.**
   E-App substitutes into the body but does not further evaluate.
   This means the result of evaluation can contain unreduced ascription
   terms, which creates a mismatch with the abstract evaluation (which
   also does not reduce them, but substitutes different values).

3. **The T-App rule substitutes the argument's TYPE, while E-App
   substitutes the argument's VALUE.** When the argument has been
   ascribed (losing precision), the type and value diverge. This
   divergence propagates into the body, creating terms that differ
   only in subexpressions (the substituted argument), and the
   subtyping rules cannot structurally compare these.

### Possible fixes

1. **Add subtyping rules for ascription.** The simplest addition
   would be a rule like:
   ```
   [S-Asc]
   Γ ⊢ A ⊑ B
   ————————————————
   Γ ⊢ (M : A) ⊑ B
   ```
   This "looks through" ascription on the left, using the ascription's
   type. Combined with a similar rule for the right, or with S-Trans,
   this might suffice. However, it requires careful analysis to ensure
   it doesn't break other properties.

2. **Make E-App fully reduce its result.** Change E-App to:
   ```
   [E-App']
   M ⟶ (x: A) → B
   N ⟶ N'
   B[x ≔ N'] ⟶ V
   ——————————————————
   M N ⟶ V
   ```
   This would ensure the result is always fully evaluated, so ascription
   terms in the body would be erased. However, this changes the semantics
   significantly and may cause non-termination.

3. **Normalize during subtyping.** Allow subtyping to evaluate/normalize
   terms before comparing them. This is hinted at in the "Open question"
   note in och.md.

4. **Restrict function bodies.** Disallow ascription inside function
   bodies, or require bodies to be in some normal form. This would be
   very restrictive.

The cleanest fix is likely option 1 — adding a subtyping rule that looks
through ascription, since the runtime semantics already erases it.

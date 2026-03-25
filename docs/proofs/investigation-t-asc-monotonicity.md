# Investigation: T-Asc Monotonicity Blocker

## 1. The Problem Restated

The monotonicity theorem says: if `Γ ⊢ M ⇒ A` and `Γ' ⊑ Γ` (pointwise),
then `Γ' ⊢ M ⇒ A'` for some A' with `Γ' ⊢ A' ⊑ A`.

In the T-Asc case, the term is `(M₀ : A₀)`. Under Γ:

1. `Γ ⊢ M₀ ⇒ M'`
2. `Γ ⊢ A₀ ⇒ A'`
3. `Γ ⊢ M' ⊑ A'`
4. Result: `Γ ⊢ (M₀ : A₀) ⇒ A'`

By IH under Γ' ⊑ Γ:

- `Γ' ⊢ M₀ ⇒ M''` with `Γ' ⊢ M'' ⊑ M'` — (IH₁)
- `Γ' ⊢ A₀ ⇒ A''` with `Γ' ⊢ A'' ⊑ A'` — (IH₂)

To apply T-Asc under Γ', we need `Γ' ⊢ M'' ⊑ A''`. But we have:

- `M'' ⊑ M'` (IH₁)
- `M' ⊑ A'` (premise 3 — under Γ, not Γ')
- `A'' ⊑ A'` (IH₂ — wrong direction: A'' is more precise, so *harder* to be above M'')

The chain is `M'' ⊑ M' ⊑ A'`, but we need `M'' ⊑ A''`, and `A'' ⊑ A'`
goes the wrong way.

---

## 2. Searching for a Concrete Counterexample

### Attempt 1: Church booleans with variable ascription target

Let:
```
Bool  = (T: ⊤) → (x: T) → (y: T) → T
True  = (T: ⊤) → (x: T) → (y: T) → x
False = (T: ⊤) → (x: T) → (y: T) → y
```

Consider `(M₀ : A₀)` where M₀ and A₀ both mention a variable from the
environment.

**Try:** `M₀ = x`, `A₀ = y`, under Γ = {x: True, y: Bool}.

- `Γ ⊢ x ⇒ True` (T-Var)
- `Γ ⊢ y ⇒ Bool` (T-Var)
- Need `Γ ⊢ True ⊑ Bool` — yes, by S-Fun (proved in och.md) ✓
- Result: `Γ ⊢ (x : y) ⇒ Bool`

Now under Γ' = {x: True, y: True} (narrowing y from Bool to True):

- `Γ' ⊢ x ⇒ True` (T-Var)
- `Γ' ⊢ y ⇒ True` (T-Var)
- Need `Γ' ⊢ True ⊑ True` — yes, by S-Refl ✓
- Result: `Γ' ⊢ (x : y) ⇒ True`

Check: `Γ' ⊢ True ⊑ Bool` — yes ✓. Monotonicity holds. No counterexample
here because the term (True) happens to be below the narrowed target (True).

### Attempt 2: Term at the boundary

We need a case where M' is barely below A' but not below a more precise A''.

**Try:** `M₀ = x`, `A₀ = y`, under Γ = {x: Bool, y: Bool}.

- `Γ ⊢ x ⇒ Bool`, `Γ ⊢ y ⇒ Bool`
- `Bool ⊑ Bool` by S-Refl ✓
- Result: `Γ ⊢ (x : y) ⇒ Bool`

Now Γ' = {x: Bool, y: True}:

- `Γ' ⊢ x ⇒ Bool`, `Γ' ⊢ y ⇒ True`
- Need `Γ' ⊢ Bool ⊑ True`?

Is `Bool ⊑ True`? Expanding:
```
(T: ⊤) → (x: T) → (y: T) → T  ⊑  (T: ⊤) → (x: T) → (y: T) → x
```

By S-Fun: need `⊤ ⊑ ⊤` (✓) and then under T: ⊤:
```
(x: T) → (y: T) → T  ⊑  (x: T) → (y: T) → x
```

By S-Fun: need `T ⊑ T` (✓) and under T: ⊤, x: T:
```
(y: T) → T  ⊑  (y: T) → x
```

By S-Fun: need `T ⊑ T` (✓) and under T: ⊤, x: T, y: T:
```
T ⊑ x
```

We need `T ⊑ x`. We have `x: T` in the context. S-Var gives `x ⊑ T` (variable
on the left), not `T ⊑ x`. There is no rule to derive `T ⊑ x`:

- S-Refl: T ≠ x syntactically, fails.
- S-Var: T: ⊤ in context, gives T ⊑ ⊤, not T ⊑ x.
- S-Top: gives T ⊑ ⊤, not T ⊑ x.

So `Bool ⊑ True` is **not derivable**. Therefore T-Asc fails under Γ': the
premise `Γ' ⊢ Bool ⊑ True` cannot be established.

**This means `(x : y)` is typeable under Γ = {x: Bool, y: Bool} but NOT
under Γ' = {x: Bool, y: True}.** This is a genuine counterexample to
monotonicity!

### Verification of the counterexample

Under Γ = {x: Bool, y: Bool}:
```
Γ ⊢ (x : y) ⇒ Bool
  Γ ⊢ x ⇒ Bool       (T-Var, x: Bool ∈ Γ)
  Γ ⊢ y ⇒ Bool        (T-Var, y: Bool ∈ Γ)
  Γ ⊢ Bool ⊑ Bool     (S-Refl)
  Result: Bool ✓
```

Under Γ' = {x: Bool, y: True} where `Γ' ⊑ Γ` (Bool ⊑ Bool by S-Refl,
True ⊑ Bool as proved above):
```
Γ' ⊢ (x : y) ⇒ ???
  Γ' ⊢ x ⇒ Bool      (T-Var)
  Γ' ⊢ y ⇒ True       (T-Var)
  Need: Γ' ⊢ Bool ⊑ True   — NOT DERIVABLE
```

T-Asc is the only typing rule for ascription, so `(x : y)` is **untypeable**
under Γ'. Monotonicity fails: Γ' ⊑ Γ, the term is typeable under Γ, but not
under Γ'.

### Counterexample simplified

The essential structure is:
- A term M₀ whose type does not change when the environment narrows (or
  gets more precise only within the same "level").
- A target A₀ whose evaluation gets strictly more precise under Γ'.
- The subtyping `type(M₀) ⊑ eval(A₀)` holds in Γ (because eval(A₀) is
  coarse) but fails in Γ' (because eval(A₀) is now too precise).

The counterexample is minimal: just two variables, one ascription, and the
Church boolean encoding.

---

## 3. Root Cause Analysis

### Why this happens

The problem is fundamental to how T-Asc interacts with monotonicity. T-Asc
says: "the result type is what the target *evaluates to*." When the environment
gets more precise:

- The target evaluates to something **more precise** (by monotonicity of
  abstract evaluation on the target).
- The term's type also gets **more precise** (by monotonicity of abstract
  evaluation on the term).
- But the subtyping check `M' ⊑ A'` is a *constraint*, not a consequence.
  Making both sides more precise does not preserve constraints.

Concretely: `Bool ⊑ Bool` holds trivially, but making the right side more
precise to `True` gives `Bool ⊑ True`, which fails because Bool is strictly
less precise than True.

### The variance mismatch

In T-Asc, the target A' appears in a **covariant** position in the output
(the result type is A') but a **contravariant** position in the premise
(M' must be ⊑ A', so a larger A' is easier to satisfy). For monotonicity,
we want the result to get more precise (A' goes down) — but going down
in the constraint position makes the constraint harder to satisfy.

This is the classic problem with subsumption/ascription in the presence of
monotonicity: the ascription target plays a dual role as both the output type
(covariant) and the upper bound on the term (contravariant).

### Diagnosis

**(b) T-Asc is defined wrong** — or at least, it is incompatible with the
monotonicity theorem as stated. The other rules (T-Top, T-Var, T-Fun) pose
no problems. T-App has its own difficulties but they are of a different
nature (the T-App-Top → T-App transition). The T-Asc problem is the crux.

The subtyping rules are not the issue: `Bool ⊑ True` *should* fail (Bool
really is less precise than True). The issue is that T-Asc re-evaluates
the ascription target under the new environment, getting a tighter bound
that the term may no longer satisfy.

---

## 4. Investigation: "Narrowing Preserves Subtyping"

### Statement

If `Γ ⊢ P ⊑ Q` and `Γ' ⊑ Γ`, then `Γ' ⊢ P ⊑ Q`.

### Proof attempt by induction on `Γ ⊢ P ⊑ Q`

**Case S-Top:** `Γ ⊢ P ⊑ ⊤`. Goal: `Γ' ⊢ P ⊑ ⊤`. By S-Top. ✓

**Case S-Refl:** `Γ ⊢ P ⊑ P`. Goal: `Γ' ⊢ P ⊑ P`. By S-Refl. ✓

**Case S-Trans:** `Γ ⊢ P ⊑ R` via `Γ ⊢ P ⊑ Q` and `Γ ⊢ Q ⊑ R`.
By IH: `Γ' ⊢ P ⊑ Q` and `Γ' ⊢ Q ⊑ R`. By S-Trans: `Γ' ⊢ P ⊑ R`. ✓

**Case S-Var:** `Γ ⊢ x ⊑ Q` via `x: A ∈ Γ` and `Γ ⊢ A ⊑ Q`.

From Γ' ⊑ Γ: there exists `x: A' ∈ Γ'` with `Γ' ⊢ A' ⊑ A`.
By IH on the sub-derivation: `Γ' ⊢ A ⊑ Q`.
By S-Trans: `Γ' ⊢ A' ⊑ Q`.
By S-Var: `Γ' ⊢ x ⊑ Q`. ✓

**Case S-Fun:** `Γ ⊢ (x: A₁) → M₁ ⊑ (x: B₁) → M₂` via:
1. `Γ ⊢ B₁ ⊑ A₁`
2. `Γ, x: B₁ ⊢ M₁ ⊑ M₂`

For (1): by IH, `Γ' ⊢ B₁ ⊑ A₁`. ✓

For (2): we need `Γ', x: B₁ ⊢ M₁ ⊑ M₂`. This requires showing
`(Γ', x: B₁) ⊑ (Γ, x: B₁)`. For variables other than x, this follows
from `Γ' ⊑ Γ`. For x itself, we need `B₁ ⊑ B₁`, which holds by S-Refl.
So `(Γ', x: B₁) ⊑ (Γ, x: B₁)`. By IH: `Γ', x: B₁ ⊢ M₁ ⊑ M₂`. ✓

By S-Fun: `Γ' ⊢ (x: A₁) → M₁ ⊑ (x: B₁) → M₂`. ✓

**Case S-Eval:** `Γ ⊢ M ⊑ M'` via `Γ ⊢ M ⇒ M'`.

We need `Γ' ⊢ M ⊑ M'`. We know `Γ ⊢ M ⇒ M'`. Can we conclude `Γ' ⊢ M ⊑ M'`?

By monotonicity (the very theorem we are trying to prove), `Γ' ⊢ M ⇒ M''`
with `Γ' ⊢ M'' ⊑ M'`. By S-Eval: `Γ' ⊢ M ⊑ M''`. By S-Trans: `Γ' ⊢ M ⊑ M'`.

**This case is circular** — it depends on the monotonicity theorem, which
is exactly what we are trying to use narrowing-preserves-subtyping to prove.

However, if we prove narrowing-preserves-subtyping and monotonicity by
**mutual induction**, this case may be closeable. The S-Eval sub-derivation
involves a typing derivation, which is strictly smaller than the T-Asc
derivation we started from (assuming the S-Eval derivation is on a
sub-term). This needs careful analysis of the induction measure.

### Verdict on narrowing-preserves-subtyping

The lemma holds for all cases except S-Eval, which requires monotonicity.
A mutual induction might work, but there's a deeper problem: **even if
narrowing-preserves-subtyping holds, it does not solve the T-Asc blocker.**

Narrowing-preserves-subtyping would give us `Γ' ⊢ M' ⊑ A'` (transplanting
premise 3 from Γ to Γ'). Combined with IH₁ (`M'' ⊑ M'`), we get
`Γ' ⊢ M'' ⊑ A'` by S-Trans. But T-Asc under Γ' needs `M'' ⊑ A''`
(where A'' ⊑ A'), and we still cannot bridge from A' down to A''.

So narrowing-preserves-subtyping helps us reach `M'' ⊑ A'` but not `M'' ⊑ A''`.

---

## 5. Investigation: Stronger "Downward Closed" Lemma

### Statement (FALSE)

If `Γ ⊢ P ⊑ Q` and `Γ' ⊑ Γ`, and `Γ' ⊢ P' ⊑ P`, and `Γ' ⊢ Q' ⊑ Q`,
then `Γ' ⊢ P' ⊑ Q'`.

### Why this is false

The counterexample from section 2 disproves this directly. Take:
- Γ = Γ' = any context (narrowing is not even needed).
- P = Q = Bool.
- P' = Bool, Q' = True.
- `Bool ⊑ Bool` holds.
- `Bool ⊑ Bool` holds (P' ⊑ P).
- `True ⊑ Bool` holds (Q' ⊑ Q).
- But `Bool ⊑ True` does NOT hold.

The lemma fails because subtyping is not "downward closed" on the right
side. Making the right side more precise (Q' ⊑ Q) makes the relation harder
to satisfy, not easier.

### Restricted versions

**Restricting to values (no variables):** Does not help. Bool and True are
both closed function literals — no variables involved.

**Restricting Q' = Q (target does not change):** This is just
narrowing-preserves-subtyping plus transitivity on the left, which works
but does not address T-Asc (where the target *does* change).

**Restricting to P' = P (term does not change):** Would need
`P ⊑ Q and Q' ⊑ Q implies P ⊑ Q'`. This is false for the same reason.

No useful restriction of this lemma holds.

---

## 6. Proposed Fixes

### Option A: T-Asc returns the *original* A' (unevaluated under Γ'), not the re-evaluated A''

**Precise change:** Modify the monotonicity proof strategy (not the rule
itself) to have T-Asc under Γ' use a different ascription target.

This does not work because T-Asc is a fixed rule — it always evaluates the
target. We cannot choose to "not re-evaluate." The typing judgment is
deterministic: `Γ' ⊢ A₀ ⇒ A''` is forced.

### Option B: Change T-Asc to return M' instead of A'

**Precise change:**
```
[T-Asc-new]
Γ ⊢ M ⇒ M'
Γ ⊢ A ⇒ A'
Γ ⊢ M' ⊑ A'
———————————
Γ ⊢ (M : A) ⇒ M'    ← changed from A' to M'
```

**Does it resolve T-Asc monotonicity?** Under Γ': by IH₁, `Γ' ⊢ M₀ ⇒ M''`
with `Γ' ⊢ M'' ⊑ M'`. We need `Γ' ⊢ M'' ⊑ A''` to apply T-Asc-new.
Same problem — the check is still there.

Actually wait — the check `M' ⊑ A'` is still a premise. If M'' fails to
be ⊑ A'', T-Asc-new still cannot be applied. This does not help.

Moreover, returning M' defeats the purpose of ascription (which is to
deliberately lose precision). **Rejected.**

### Option C: Change T-Asc to not re-evaluate the target

**Precise change:**
```
[T-Asc-raw]
Γ ⊢ M ⇒ M'
Γ ⊢ M' ⊑ A
———————————
Γ ⊢ (M : A) ⇒ A
```

The target A is used as-is (raw syntax), not evaluated.

**Does it resolve T-Asc monotonicity?** Under Γ': by IH₁,
`Γ' ⊢ M₀ ⇒ M''` with `Γ' ⊢ M'' ⊑ M'`. Need `Γ' ⊢ M'' ⊑ A₀`.
We have `M'' ⊑ M'` and need to bridge to `A₀`. From the original premise
`Γ ⊢ M' ⊑ A₀` (now against raw A₀, not evaluated A'), we need to
transplant this to Γ'. This requires narrowing-preserves-subtyping.

But more fundamentally: the result type is now A₀ (raw syntax) in both
environments, so the monotonicity conclusion just needs `Γ' ⊢ A₀ ⊑ A₀`
which is S-Refl. The result type does not change!

Wait — that is almost too easy. Let me re-examine. Under Γ, T-Asc-raw
gives `Γ ⊢ (M₀ : A₀) ⇒ A₀`. Under Γ', T-Asc-raw would give
`Γ' ⊢ (M₀ : A₀) ⇒ A₀`, provided the premise `Γ' ⊢ M'' ⊑ A₀` holds.

The monotonicity conclusion needs `Γ' ⊢ A₀ ⊑ A₀`, which is S-Refl. ✓

But we still need `Γ' ⊢ M'' ⊑ A₀` (the premise of T-Asc-raw under Γ').
We have:
- `Γ' ⊢ M'' ⊑ M'` (IH₁)
- `Γ ⊢ M' ⊑ A₀` (original premise)

By narrowing-preserves-subtyping: `Γ' ⊢ M' ⊑ A₀`. Then by S-Trans:
`Γ' ⊢ M'' ⊑ A₀`. ✓

**This resolves the T-Asc case!** But at a cost.

**Impact on the rest of the system:**

- The ascription target is no longer evaluated. This means `(M : x)` where
  `x: Bool` produces type `x`, not `Bool`. Subtyping can still handle this
  via S-Var (`x ⊑ Bool`), but the types in the system now contain raw
  variable references instead of their evaluated forms.
- This conflicts with sharp edge #7: "T-Asc evaluates the ascription
  target." The stated reason is that without evaluation, variables in
  targets behave unpredictably.
- The result type `A₀` may contain free variables, applications, and
  other unevaluated syntax. Other rules that receive this type (as input
  to further typing) would need to handle unevaluated forms.
- In particular, if `A₀` is an application (e.g. `M : f x`), the result
  type would be the raw application `f x`, which subtyping cannot decompose
  (no S-App rule). This would break the system elsewhere.

**Verdict: resolves the T-Asc case but causes serious problems elsewhere.
Not viable without further changes (adding S-App or S-Eval to handle raw
types in subtyping).** Partially viable if combined with S-Eval as a
subtyping rule.

### Option D: Weaken the monotonicity theorem to allow untypeability

**Precise change:** Restate monotonicity as:

> If `Γ ⊢ M ⇒ A` and `Γ' ⊑ Γ`, then **either** `Γ' ⊢ M ⇒ A'` with
> `Γ' ⊢ A' ⊑ A`, **or** M is untypeable under Γ'.

This is trivially true but useless — the whole point of monotonicity is
to guarantee that more precise inputs give more precise outputs, not that
programs might stop working.

**Verdict: Defeats the purpose. Rejected.**

### Option E: Restrict environment narrowing to not affect ascription targets

**Precise change:** Monotonicity only holds for terms where no ascription
target contains a variable that is being narrowed.

This is ad hoc and hard to state formally. It would not help with the
practical use case (the whole point is that environments narrow during
type inference).

**Verdict: Too restrictive, defeats the purpose. Rejected.**

### Option F: Change T-Asc to check against the *wider* of M' and A'

This is not well-defined in a general subtyping lattice. **Rejected.**

### Option G: Add a "subsumption-like" rule so the result can be A' instead of A''

**Precise change:** Allow T-Asc to return any B such that `M' ⊑ B` and
`B ⊑ A'`:

```
[T-Asc-sub]
Γ ⊢ M ⇒ M'
Γ ⊢ A ⇒ A'
Γ ⊢ M' ⊑ A'
Γ ⊢ M' ⊑ B
Γ ⊢ B ⊑ A'
———————————
Γ ⊢ (M : A) ⇒ B
```

This does not help because the monotonicity proof would still need to
find a B under Γ' that works. The same fundamental problem applies.

**Verdict: Does not help. Rejected.**

### Option H: Make T-Asc evaluate the target but return the *unevaluated* target

**Precise change:**
```
[T-Asc-check-eval-return-raw]
Γ ⊢ M ⇒ M'
Γ ⊢ A ⇒ A'
Γ ⊢ M' ⊑ A'
———————————
Γ ⊢ (M : A) ⇒ A      ← return raw A, but check against evaluated A'
```

This evaluates the target for the purpose of checking (so the check is
against a sensible fully-evaluated type), but returns the raw syntax as
the result type.

**Does it resolve T-Asc monotonicity?** Under Γ':
- `Γ' ⊢ M₀ ⇒ M''` with `M'' ⊑ M'` (IH₁)
- `Γ' ⊢ A₀ ⇒ A''` with `A'' ⊑ A'` (IH₂)
- Need `Γ' ⊢ M'' ⊑ A''` for the T-Asc premise — **SAME PROBLEM**.

The check is still `M'' ⊑ A''`. Changing what we return does not change
what we need to check.

**Verdict: Does not resolve the core issue. Rejected.**

### Option I: Evaluate the target, check M' ⊑ A', but return the *max* of M' and A'

Not well-defined. **Rejected.**

### Option J: Change T-Asc to check against the raw target

**Precise change:**
```
[T-Asc-raw-check]
Γ ⊢ M ⇒ M'
Γ ⊢ M' ⊑ A
———————————
Γ ⊢ (M : A) ⇒ A
```

Evaluate M, check M' ⊑ A (raw), return A (raw). The target is never
evaluated.

**Does it resolve T-Asc monotonicity?** Same as Option C (T-Asc-raw). The
analysis above applies: it resolves T-Asc but leaves raw syntax in types.

**Same as Option C. See analysis there.**

### Option K: Keep T-Asc as-is but add S-Eval to subtyping

**Precise change:** Add to subtyping:
```
[S-Eval]
Γ ⊢ M ⇒ M'
————————————
Γ ⊢ M ⊑ M'
```

**Does it resolve T-Asc monotonicity?** No. The problem is not about
subtyping rules — it is about the T-Asc *premise* `M'' ⊑ A''` being
unprovable. Adding S-Eval gives us `M₀ ⊑ M''` and `A₀ ⊑ A''`, but
these do not help derive `M'' ⊑ A''`.

**Verdict: Does not address the T-Asc blocker. Rejected as a standalone fix.**

### Option L: Change T-Asc to not re-evaluate the target, and add S-Eval to subtyping

**Precise change:** Combine Option C/J with Option K:

```
[T-Asc-raw]
Γ ⊢ M ⇒ M'
Γ ⊢ M' ⊑ A
———————————
Γ ⊢ (M : A) ⇒ A

[S-Eval]
Γ ⊢ M ⇒ M'
————————————
Γ ⊢ M ⊑ M'
```

**Does it resolve T-Asc monotonicity?** Yes, per the Option C analysis.

**Does S-Eval help with raw types in subtyping?** Yes! When a result type
is raw `A₀` and someone needs to compare `A₀ ⊑ B`, they can use S-Eval
to first get `A₀ ⊑ A'` (where A' is the evaluated form), then use
structural subtyping on A'. This means raw syntax in types is "transparent"
to subtyping.

For example, if the result type is `x` (raw variable, not evaluated) and
we need `x ⊑ Bool`, S-Var already handles this (if `x: Bool ∈ Γ`). If the
result type is `f x` (raw application), S-Eval with the typing derivation
`Γ ⊢ f x ⇒ R` gives `f x ⊑ R`, and then we compare R structurally.

**Impact on the rest of the system:**
- The monotonicity counterexample from Section 2 is defused: under Γ, the
  check is `Bool ⊑ y` (raw). S-Var gives `y ⊑ Bool` but we need
  `Bool ⊑ y`. This is not derivable (same one-directional S-Var issue).
  So `(x : y)` is actually **rejected under Γ too** with this rule!

Wait — that's a problem. Let me re-check. Under T-Asc-raw with
Γ = {x: Bool, y: Bool}: we need `Γ ⊢ Bool ⊑ y`. Can we derive this?

- S-Refl: Bool ≠ y, no.
- S-Var: y: Bool ∈ Γ gives y ⊑ Bool, not Bool ⊑ y. No.
- S-Trans: need an intermediate. No useful intermediate.
- S-Eval: need `Γ ⊢ Bool ⇒ y`. But Bool = `(T: ⊤) → (x: T) → (y: T) → T`
  evaluates to itself by T-Fun. No.

So `Bool ⊑ y` is not derivable. The term `(x : y)` is **rejected** under
T-Asc-raw in all environments. The ascription target `y` cannot be used
as a raw target because subtyping cannot "see through" a variable to its
type on the right side of ⊑.

This is too restrictive. The example `(M : x)` where `x: SomeType` should
be expressible. This is sharp edge #7's concern: not evaluating the target
means variables in ascription targets become useless.

**Verdict: Resolves T-Asc monotonicity but makes ascription to variable
targets impossible. This severely limits usability.**

### Option M: Change T-Asc to not re-evaluate, add S-Eval, and add "reverse S-Var"

Adding a reverse S-Var `(x: A ∈ Γ) ⟹ Γ ⊢ A ⊑ x` would let
`Bool ⊑ y` be derived (via `Bool ⊑ Bool` by S-Refl and then `Bool ⊑ y`
if `y: Bool`... wait, reverse S-Var gives `A ⊑ x` when `x: A`. So
`Bool ⊑ y` from `y: Bool`).

But sharp edge #6 warns: a reverse S-Var immediately re-enables the
Ochre monotonicity bug. If we can derive `A ⊑ x` whenever `x: A`, then
`False ⊑ b` is derivable when `b: Bool` (via `False ⊑ Bool` and
`Bool ⊑ b`). The whole point of one-directional S-Var was to prevent this.

**Verdict: Re-enables the original monotonicity bug. Rejected.**

### Option N: Make T-Asc evaluate the target and use S-Eval to check, but return raw target

This is Option H again with S-Eval. Already shown to not resolve the core
issue — the check `M'' ⊑ A''` is still required.

### Option O: Change T-Asc to check M' ⊑ A (raw) using S-Eval implicitly

**Precise change:**
```
[T-Asc-eval-check]
Γ ⊢ M ⇒ M'
Γ ⊢ A ⇒ A'
Γ ⊢ M' ⊑ A'
———————————
Γ ⊢ (M : A) ⇒ A'
```

This is the CURRENT rule. The problem persists. Not a fix.

### Option P: Decouple the checked type from the returned type

**Precise change:**
```
[T-Asc-decouple]
Γ ⊢ M ⇒ M'
Γ ⊢ A ⇒ A'
Γ ⊢ M' ⊑ A'
———————————
Γ ⊢ (M : A) ⇒ A       ← return raw A, but check against evaluated A'
```

This evaluates for checking but returns raw. Under Γ': we still need
`Γ' ⊢ M'' ⊑ A''` for the check. **Same problem.**

But wait — the *result* is A (raw), which is the same in both environments.
So the monotonicity conclusion would need `Γ' ⊢ A ⊑ A` (S-Refl ✓). The
issue is only whether T-Asc can be applied at all (the premise check).

This has the same failure mode as the current rule: the premise may fail.

### Option Q: Remove the ascription check entirely (unsound direction)

```
[T-Asc-unsafe]
Γ ⊢ A ⇒ A'
———————————
Γ ⊢ (M : A) ⇒ A'
```

No check that M is compatible with A. Clearly unsound. **Rejected.**

### Option R: Use A' from the *original* environment Γ, not Γ'

This is not possible — we need a derivation under Γ', and we can't use
Γ's evaluation result as a type in Γ'. The typing rules require everything
to be derived in the current environment.

---

## 7. The Most Promising Direction

After exhausting the design space, the most promising options are:

### Primary recommendation: Option C/J/L variant — don't evaluate the target, but add S-Eval to bridge

The core idea is:

1. **T-Asc checks and returns the raw target** (not evaluated).
2. **S-Eval is added as a subtyping rule** so that raw types can be
   "seen through" by subtyping when needed.
3. The check uses S-Eval internally: to check `M' ⊑ A` (raw), the prover
   can use S-Eval to get `A ⊑ A'` and then check `M' ⊑ A'` via S-Trans...
   wait, that goes the wrong way. S-Eval gives `A ⊑ A'` (raw term is
   more precise than evaluated form), but we need the chain
   `M' ⊑ A ⊑ ???`. Actually, we need `M' ⊑ A`, and the only way to
   get there is if `M' ⊑ A` is directly derivable.

Let me reconsider. With the raw-target rule:

```
[T-Asc-raw]
Γ ⊢ M ⇒ M'
Γ ⊢ M' ⊑ A
———————————
Γ ⊢ (M : A) ⇒ A
```

The check is `M' ⊑ A` where A is raw syntax. For this to be practical,
we need subtyping to handle raw A. Currently:

- If A is ⊤: S-Top handles it.
- If A is a variable x: S-Var gives x ⊑ B, but we need M' ⊑ x. **Stuck**
  without reverse S-Var (which is forbidden).
- If A is a function literal: S-Fun handles it.
- If A is an application: **Stuck** without S-App.

So the raw-target approach fundamentally cannot handle variable ascription
targets without some way to derive `M' ⊑ x`.

### The real question: can we allow `M' ⊑ x` without enabling the monotonicity bug?

The Ochre bug required `False ⊑ b` where `b: Bool`. This was blocked by
the absence of reverse S-Var. But what if we add a *restricted* reverse
rule?

**Candidate: S-Var-Right (restricted)**
```
[S-Var-Right]
x: A ∈ Γ
Γ ⊢ M ⊑ A
M is not a variable      ← key restriction
———————————
Γ ⊢ M ⊑ x
```

This lets `Bool ⊑ y` (when y: Bool) but blocks `y ⊑ x` (because y is
a variable). Does this prevent the monotonicity bug?

The bug needs `False ⊑ b` where b: Bool. False is a function literal,
not a variable. So S-Var-Right would derive:
- `False ⊑ Bool` (by S-Fun, proved above)
- Therefore `False ⊑ b` (by S-Var-Right, since False is not a variable)

**The restriction "M is not a variable" does NOT prevent the bug.**
False is a non-variable term. **Rejected.**

What about restricting to "M is a value that evaluates to itself"? This
also does not help — False evaluates to (the E-Fun erased version of)
itself.

### The fundamental tension

The problem is inescapable with the current architecture:

1. **Evaluating the ascription target** makes the monotonicity check
   `M'' ⊑ A''` fail when the target gets more precise.
2. **Not evaluating the target** makes the subtyping check `M' ⊑ A`
   fail when A is a variable (because we can't derive `M' ⊑ x` without
   reverse S-Var).
3. **Reverse S-Var** (in any form that allows `nonvar ⊑ x`) re-enables
   the Ochre monotonicity bug.

This is a trilemma. Any two of {evaluated targets, monotonicity,
no reverse S-Var} seem achievable, but not all three.

---

## 8. Deeper Analysis: Is the Counterexample Realistic?

The counterexample from Section 2 uses `(x : y)` under Γ = {x: Bool, y: Bool},
narrowed to Γ' = {x: Bool, y: True}.

In practice, when does an ascription target variable get *narrowed* in the
environment? This happens during type application: if a function has a
parameter `y: Bool` and is called with argument `True`, the body is checked
under `y: True` (a narrowing of `y: Bool`).

The term `(x : y)` inside such a function body says "treat x as having
type y." Under `y: Bool`, this widens x to Bool. Under `y: True`, this
tries to widen x to True — but x has type Bool, which is not ⊑ True.

**Is this the correct behavior?** Arguably yes! If x: Bool and y: True,
then ascribing x to type y *should* fail — Bool really is not a subtype
of True. The ascription is promising that x has type True, but Bool values
may be False, which is not True. The failure is semantically correct.

The question is whether we want the *monotonicity theorem* to hold despite
this, or whether we accept that ascription can cause typeability to fail
under narrowing.

### A weaker monotonicity statement

**Option S: Monotonicity holds for ascription-free terms.**

If `Γ ⊢ M ⇒ A` and `Γ' ⊑ Γ` and M contains no ascriptions, then
`Γ' ⊢ M ⇒ A'` with `Γ' ⊢ A' ⊑ A`.

This is clean, provable, and captures the key property (more precise
environment → more precise type) for the "natural" fragment of the
language. Ascription is the only construct that loses precision, so it
makes sense that it is the only construct that can break monotonicity.

**Pros:**
- No rule changes needed.
- The theorem is true and provable.
- Captures the useful direction: runtime values (which have no ascriptions
  after E-Asc erasure) have monotone typing.

**Cons:**
- The soundness proof for T-App may need monotonicity for terms that
  contain ascriptions (since function bodies can contain ascriptions).
  If so, this weaker theorem is insufficient.

### Checking whether soundness needs full monotonicity

The soundness theorem says: if `Γ ⊢ M ⇒ A` and `M ⟶ V`, then `· ⊢ V ⊑ A`.

In the T-App case:
```
Γ ⊢ M ⇒ (x: A) → B
Γ ⊢ N ⇒ N'
Γ ⊢ N' ⊑ A
Γ ⊢ B[x ≔ N'] ⇒ R
```

At runtime: `M ⟶ (x: ⊤) → B_body`, `N ⟶ N_v`, result is `B_body[x ≔ N_v]`.

The soundness gap is between `B[x ≔ N']` (abstract) and `B_body[x ≔ N_v]`
(concrete). We know `N_v ⊑ N'` (by IH on N). We need the evaluation of
`B[x ≔ N_v]` to give a result ⊑ R.

This requires a substitution + monotonicity argument: substituting a more
precise value (N_v ⊑ N') into B gives a more precise result. This is
monotonicity applied to `B[x ≔ _]`. If B contains ascriptions, we need
full monotonicity, not just ascription-free monotonicity.

**So soundness does require monotonicity for terms with ascriptions.**
The weaker theorem is likely insufficient for the full soundness proof.

---

## 9. Summary and Conclusions

### The counterexample

The term `(x : y)` under Γ = {x: Bool, y: Bool} types to Bool, but under
Γ' = {x: Bool, y: True} (with Γ' ⊑ Γ), it is untypeable. This is a genuine
counterexample to monotonicity of abstract evaluation.

### Root cause

T-Asc's ascription target is evaluated under the current environment. When
the environment narrows, the target evaluates to something more precise.
The subtyping check (term ⊑ target) may fail because the target became too
tight. This is a variance mismatch: the target is covariant in the output
but contravariant in the check.

### The trilemma

The three properties {evaluated targets, monotonicity, no reverse S-Var}
cannot all hold simultaneously. The current system chooses evaluated targets
and no reverse S-Var, sacrificing monotonicity.

### What does NOT work

| Option | Why it fails |
|--------|-------------|
| Not evaluating the target (C/J) | Variables in ascription targets become unusable (can't derive `M' ⊑ x`) |
| Reverse S-Var (M) | Re-enables the Ochre monotonicity bug |
| Restricted reverse S-Var | Still enables the bug (non-variable terms like False) |
| Returning M' instead of A' (B) | Defeats the purpose of ascription; same check problem |
| Weakening the theorem (D) | Trivially true but useless |
| Stronger lemmas (Section 5) | False in general |
| Narrowing-preserves-subtyping alone (Section 4) | Gets us M'' ⊑ A' but not M'' ⊑ A'' |

### What might work — directions for further research

1. **Accept the counterexample and restructure the soundness proof.** If
   soundness can be proved without full monotonicity (perhaps using a
   more specialized substitution lemma that avoids the T-Asc case), then
   monotonicity-for-ascription-free-terms may be sufficient. This requires
   a careful re-examination of the soundness proof for T-App to see exactly
   what property of substitution is needed.

2. **Change T-Asc to not evaluate the target, return raw A, and add S-Eval
   as a subtyping axiom.** Then restructure the system so that subtyping
   can compare raw terms by evaluating them on-the-fly (via S-Eval). The
   check `M' ⊑ A` where A is a variable x with x: T would go:
   `M' ⊑ ???`. We still cannot derive `M' ⊑ x` directly. But we could
   add S-Eval-Right:
   ```
   [S-Eval-Right]
   Γ ⊢ B ⇒ B'
   Γ ⊢ A ⊑ B'
   ———————————
   Γ ⊢ A ⊑ B
   ```
   This says: if B evaluates to B' and A ⊑ B', then A ⊑ B. Intuitively:
   B is at least as precise as B' (S-Eval), and A ⊑ B' means A is ⊑ the
   less-precise form, so A ⊑ B (which is even more precise). Wait — that
   is the wrong direction. B ⊑ B' (by S-Eval), so B is MORE precise than B'.
   If A ⊑ B', and B ⊑ B', that gives us nothing about A vs B.

   Actually, what we want is the opposite: if B evaluates to B', then B'
   is less precise than B, so `B' ⊑ B`... no, S-Eval says `B ⊑ B'` (term
   is more precise than its type). Hmm.

   Actually, let's reconsider the direction. Abstract evaluation *loses*
   precision (via ascription). So the evaluated form B' is *less* precise
   than B. That means `B' ⊑ B` would be wrong — `B ⊑ B'` is the correct
   direction (B is more precise, a subtype of B').

   Wait — that's what S-Eval says: `Γ ⊢ M ⇒ M'` gives `M ⊑ M'`. But
   this seems backwards: if M' is the type (less precise), then M ⊑ M'
   means M is "at least as precise as" M', i.e., M is a subtype. Yes,
   that's right: ⊑ means "at least as precise," and terms are at least as
   precise as their types.

   So for S-Eval-Right: we have B ⊑ B'. If A ⊑ B' (A is below B'), we
   want A ⊑ B. But B ⊑ B' means B is below B', and A ⊑ B' means A is
   also below B'. There's no reason A should be below B — B could be
   more precise in a way incompatible with A.

   This direction does not work.

3. **Explore a "semantic" subtyping rule for ascription terms.** Add:
   ```
   [S-Asc-Left]
   Γ ⊢ M ⇒ M'
   Γ ⊢ A ⇒ A'
   Γ ⊢ M' ⊑ A'
   Γ ⊢ A' ⊑ B
   ———————————
   Γ ⊢ (M : A) ⊑ B
   ```
   This lets subtyping "see through" ascription on the left. Combined
   with S-Eval, this could give enough machinery to handle raw types.
   But this is just embedding T-Asc into subtyping, and does not directly
   address the monotonicity problem.

4. **Rethink what the ascription target means.** Perhaps the target should
   be a *syntactic bound*, not an evaluated type. That is, `(M : A)` means
   "M, but I promise not to use more precision than the syntactic form A
   provides." Under this reading, evaluating A is wrong — the promise is
   about the syntax. This aligns with Option C/J and avoids the need for
   variable targets (you would write `(M : Bool)` directly, not `(M : x)`).
   Whether this is practical for Ochre depends on whether ascription to
   variable targets is needed.

5. **Most promising: change how T-App uses monotonicity in the soundness proof.**
   Instead of requiring full monotonicity, prove a *substitution-respects-
   subtyping* lemma directly:

   > If `Γ, x: A ⊢ B ⇒ R` and `Γ ⊢ V₁ ⊑ V₂ ⊑ A`, then
   > `Γ ⊢ B[x ≔ V₁] ⇒ R₁` and `Γ ⊢ B[x ≔ V₂] ⇒ R₂` with `Γ ⊢ R₁ ⊑ R₂`.

   This is a specialized form of monotonicity that only varies one variable
   at a time. It might be provable even in the T-Asc case because substitution
   into an ascription target `A₀[x ≔ V₁]` vs `A₀[x ≔ V₂]` with V₁ ⊑ V₂ might
   preserve the subtyping check. But this needs a careful proof — the same
   variance issue could appear here too.

---

## 10. Concrete Recommendation

The counterexample is real and minimal. The T-Asc rule as currently defined
is incompatible with full monotonicity of abstract evaluation.

**Immediate next step:** Determine whether the soundness proof truly requires
full monotonicity, or whether a weaker substitution lemma suffices. If the
latter, the system may be viable as-is with a weaker monotonicity theorem
(holding for ascription-free terms or for single-variable substitution).

**If full monotonicity is required:** The most viable path appears to be
Option C/J (raw target) combined with S-Eval as a subtyping axiom,
accepting that ascription targets must be syntactic types rather than
variables. This requires rethinking how variable-target ascriptions are
handled — possibly by requiring users to write explicit types rather than
variable references in ascription positions. Whether this is acceptable
for Ochre depends on the intended use cases.

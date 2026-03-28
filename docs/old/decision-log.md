# Och₀ Decision Log

Design decisions made during the development and proof of Och₀.
Each entry records what changed, why, and what alternative was rejected.

---

## 1. S-Eval added as axiom

**Decision:** Add `Γ ⊢ M ⇒ M' ⟹ Γ ⊢ M ⊑ M'` as a subtyping axiom.

**Why:** Cannot be derived from the other subtyping rules. Needed for
T-App soundness — the concrete body (after substitution and evaluation)
must be related to the abstract body (after substitution and typing).
S-Eval bridges the gap: a term is at least as precise as its type.

**Alternative rejected:** Deriving it from existing rules. Impossible
because ascription terms have no structural subtyping decomposition
on the left without S-Eval.

---

## 2. T-Asc checks raw target

**Decision:** T-Asc checks `M' ⊑ A` (raw target syntax), not `M' ⊑ A'`
(evaluated target).

**Why:** Checking against the evaluated target breaks monotonicity.
Under a narrower environment, A might evaluate to something more precise
(A'' ⊑ A'), making M'' ⊑ A'' harder to satisfy than M' ⊑ A'. The raw
target A is syntax — it doesn't change under narrowing. (Sharp edge #10)

**Alternative rejected:** Checking `M' ⊑ A'`. Concrete counterexample:
`x: Bool, y: Bool ⊢ (x : y)` would need `Bool ⊑ eval(y) = Bool` (works),
but under `y: True`, `Bool ⊑ eval(y) = True` fails.

---

## 3. E-App evaluates body after substitution

**Decision:** E-App evaluates `B[x ≔ N'] ⟶ V` (substitution then
evaluation), not just `B[x ≔ N']` as the final result.

**Why:** Without evaluation, substitution can place values into
contravariant (domain) positions of the body, and the result is not
a proper value. Concrete soundness counterexample. (Sharp edge #11)

---

## 4. T-App-Top added then REMOVED

**Decision (original):** Add unconditional rule `Γ ⊢ M N ⇒ ⊤` with
no premises. (Sharp edge #12)

**Why it was added:** Believed necessary for monotonicity — if M₁ types
to ⊤ under Γ, we needed some way to type M₁ M₂.

**Why it was removed:** The monotonicity proof doesn't use it. When the
premise is "M₁ M₂ typed via T-App under Γ", the proof uses IH + HN-Mono
to construct a T-App derivation under Γ'. When the premise would be
"M₁ M₂ typed via T-App-Top", removing the rule just removes the premise
— monotonicity is vacuously true. Meanwhile T-App-Top types nonsensical
programs (applying non-functions), introduces non-determinism, and would
cause problems with atoms/match (where applying a non-function genuinely
fails at runtime).

---

## 5. T-App uses head normalization (⇓)

**Decision:** T-App's premise is `Γ ⊢ F ⇓ (x: A) → B` (head-normalize
F to a function type), not `F = (x: A) → B` (syntactic check).

**Why:** Under narrowing, M₁'s type may become a variable alias for a
function type. Without ⇓, T-App can't see through the alias and fails.
(Sharp edges #12, #13)

**Alternative rejected:** T-Var normalization (evaluating environment
entries in T-Var). Breaks test 28 because T-Asc's raw target check
needs `eval(x) ⊑ T`, and `⊤ ⊑ T` is not derivable.

---

## 6. Well-founded environments

**Decision:** Variable bindings in Γ must be acyclic.

**Why:** ⇓ termination. HN-Var looks up a variable's type and recurses.
Cycles would cause ⇓ to diverge.

---

## 7. E-Fun deep domain erasure

**Decision:** `(x: A) → M ⟶ (x: ⊤) → erase(M)` — erase ALL domain
annotations in the body, not just the outermost parameter.

**Why:** Without deep erasure, E-App substitutes precise concrete values
into inner domain (contravariant) positions, creating a mismatch with
abstract evaluation. Concrete soundness counterexample:
`((x: ⊤) → (y: ⊤) → (z: x) → z) arg` — the inner domain `x` gets
a precise value at runtime but a less precise type abstractly, and the
contravariant comparison goes wrong. (Sharp edge #14)

**Alternative rejected:** Shallow erasure (only outermost domain). Fails
for nested functions with parameter-dependent inner domains.

---

## 8. S-App congruence added

**Decision:** Add `M₁ ⊑ M₂, N₁ ⊑ N₂ ⟹ M₁ N₁ ⊑ M₂ N₂`.

**Why:** Needed for the Erase-Sub lemma (`erase(M) ⊑ M`) on application
terms: `erase(M₁ M₂) = erase(M₁) erase(M₂)`, and S-App with IH on
both components gives the result. (Sharp edge #14)

---

## 9. HN-Eval added to ⇓

**Decision:** When ⇓ encounters an application or ascription, first
abstractly evaluate it (⇒), then ⇓ the result.

**Why:** Environment entries that are application or ascription terms
(which arise from S-Eval in narrowed environments) couldn't be resolved
to function types without this. Concrete monotonicity counterexample.
(Sharp edge #15)

---

## 10. T-App abstract domain erasure

**Decision:** T-App substitutes into `erase(B)` instead of raw `B`:
`Γ ⊢ erase(B)[x ≔ N'] ⇒ R`.

**Why:** Without erasure, the argument type N' lands in contravariant
(domain) positions of B. Under monotonicity, a more precise N'' ⊑ N'
produces a LESS precise result at those positions (contravariance).
Concrete counterexample: `((x: ⊤) → (y: x) → y) a` where `a`'s type
gets more precise. (Sharp edge #16)

This mirrors E-Fun's deep erasure and aligns abstract and concrete
evaluation: both substitute into the same erased body, differing only
in the substituted value (which is in covariant positions).

**Precision lost:** Domain annotations in the body that depend on the
parameter. E.g., `(y: x) → y` becomes `(y: ⊤) → y` — we no longer
track that y has the same type as the argument. But this was always
erased at runtime.

---

## 11. S-Asc structural congruence added

**Decision:** Add `M₁ ⊑ M₂, A₁ ⊑ A₂ ⟹ (M₁ : A₁) ⊑ (M₂ : A₂)`.

**Why:** Needed for the Erase-Sub lemma (`erase(M) ⊑ M`) on ascription
terms, analogous to S-App for applications. Without it, the ascription
case was an open sub-gap.

**Alternative rejected:** S-Asc-R (`M ⊑ A ⟹ M ⊑ (N : A)`) — conflates
the inner term with the target and mixes compile-time semantics into
structural subtyping. S-Asc-Struct is cleaner.

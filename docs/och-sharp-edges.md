# Och Sharp Edges

Things that are important about the Och₀ design and how changing them
breaks things. Read this before modifying the rules in och.md.

## 1. Terms and types are the same syntax

The whole point of Och. There is one grammar. Functions are simultaneously
lambdas and pi types. Introducing any syntactic phase distinction
(separate type language, universe annotations, level markers) undermines
the core hypothesis being tested.

**If you break this:** You're no longer testing the "terms are types"
idea. You're building a conventional dependently typed language.

## 2. T-Fun returns the raw body, NOT an evaluated body

Previous versions had T-Fun abstractly evaluate the body:
`Γ, x: A ⊢ M ⇒ M'` giving `(x: A) → M'`. This caused two problems:

- **Soundness gap (Gap 1):** E-Fun returns the raw body M, so the value
  `(x: ⊤) → M` must be ⊑ the type `(x: A) → M'`. The body comparison
  `M ⊑ M'` requires an S-Eval rule and is hard to prove.

- **Soundness gap (Gap 2):** When T-App substitutes the argument type into
  the pre-evaluated body, and E-App substitutes the concrete argument value,
  the results diverge. In contravariant positions (e.g. a parameter type
  inside the body that mentions x), substituting a wider type makes the
  result claim to accept more inputs than it actually does at runtime.

The fix: T-Fun returns raw syntax, T-App evaluates *after* substitution.
This way the body is always evaluated with the actual argument type, and
ascription checks happen at the right precision.

**If you re-add body evaluation to T-Fun:** Both gaps reopen. You need
either S-Eval or a monotone substitution lemma, both of which are
non-trivial and may not hold.

## 3. T-App evaluates the substituted body

T-App does `B[x ≔ N'] ⇒ R`. The extra `⇒ R` step is essential.
Without it, the result of T-App is the raw substituted term `B[x ≔ N']`,
which may contain unresolved ascriptions. These ascription terms can't
be compared by subtyping (no structural rule for ascription), causing
soundness failures.

**If you remove the evaluation step from T-App:** Ascription terms
appear in types, subtyping can't decompose them, soundness fails.
The previous proof attempt found a concrete counterexample:
`f = (x: ⊤) → (⊤ : x)`, `g = ((y: ⊤) → y) : ((y: ⊤) → ⊤)`,
`f g` produces incomparable ascription terms.

## 4. E-Fun erases the parameter annotation to ⊤

At runtime, `(x: A) → M ⟶ (x: ⊤) → M`. This is type erasure —
the runtime doesn't need the parameter type because checking already
happened at compile time.

This is important for soundness of T-Fun. The value is `(x: ⊤) → M`,
the type is `(x: A) → M`. By S-Fun, need `A ⊑ ⊤` (contravariant) —
trivially true. Without erasure, you'd need `A ⊑ A` (fine in this case
via S-Refl, but the erasure makes the contravariant direction always free).

**If you keep the annotation at runtime:** The soundness proof still works
for T-Fun (via S-Refl instead of S-Top), but you lose the property that
two functions differing only in annotation are the same runtime value.
This becomes important when you add features later.

## 5. E-Asc erases ascription at runtime

`(M : A) ⟶ V` where `M ⟶ V`. The ascription is gone. This is the
other half of type erasure (along with E-Fun).

This is the sole source of divergence between abstract and concrete
evaluation. Without ascription, abstract and concrete evaluation would
always agree (both just substitute and apply). With ascription, abstract
evaluation loses precision (returns the target type) while concrete
evaluation preserves it (returns the inner value).

**If you keep ascription at runtime:** The concrete result would be
`(V : A)` instead of `V`. Then you need subtyping rules for ascription
terms, which is messy. Keeping erasure is simpler.

## 6. S-Var is one-directional

S-Var says: if `x: A ∈ Γ` and `A ⊑ B`, then `x ⊑ B`. The variable
is always on the LEFT of ⊑. There is no rule for `A ⊑ x`.

This is what prevents the Ochre monotonicity bug from occurring. If you
could derive `False ⊑ b` (via `False ⊑ Bool` and `b: Bool`), then
narrowing `b` to `True` would break the judgment. But since S-Var only
goes left-to-right, `False ⊑ b` is never derivable.

**If you add a reverse S-Var:** The monotonicity bug returns immediately.
`False : b` becomes typeable under `b: Bool` but not under `b: True`.

## 7. T-Asc evaluates the ascription target for the result, but checks against raw

T-Asc checks `M' ⊑ A` (raw target), then evaluates `A ⇒ A'` for the
result type. The check uses raw A; the result uses evaluated A'.

The check `M' ⊑ A` against raw A means variable targets require
syntactic subtyping: `(x : T)` works when x: T (S-Refl on M' = T ⊑ T),
but `(x : y)` with independent x, y is rejected. This is correct —
see sharp edge #10.

**If you check against the evaluated target instead:** Monotonicity
breaks — see sharp edge #10 for the counterexample.

## 8. Subtyping now has S-Asc (structural congruence for ascription)

S-Asc says `(M₁ : A₁) ⊑ (M₂ : A₂)` when `M₁ ⊑ M₂` and `A₁ ⊑ A₂`.
This is the ascription analogue of S-App — structural congruence for
the compound form. It was added to close the ascription sub-gap in
the domain erasure lemma (`erase(M) ⊑ M`).

**Why it's safe:** S-Asc only fires when both sides are ascription
terms. It does not enable `False ⊑ b` or any other judgment that
would re-enable the Ochre monotonicity bug. It is semantically sound:
(M : A) as a type evaluates to A' (evaluated A), so structural
monotonicity of ascription follows from monotonicity of evaluation.

**What NOT to add instead:** The rule `(M : A) ⊑ B if A ⊑ B`
(S-Asc-R) is tempting but mixes the semantics of ascription (a
compile-time operation) into subtyping in a way that conflates the
inner term with the target. S-Asc-Struct is cleaner because it
preserves the structural decomposition pattern used by S-Fun and
S-App.

## 9. Soundness requires monotonicity

The soundness proof for T-App requires showing that substituting a more
precise argument and then evaluating gives a more precise result. This
is exactly the monotonicity property. The two properties are not
independent — they should be proved by mutual induction.

**If you try to prove soundness without monotonicity:** The T-App case
gets stuck at the substitution lemma. You need to know that abstract
evaluation is monotone in its inputs to close the gap between what
T-App computes (using the argument's type) and what E-App computes
(using the argument's value).

## 10. T-Asc checks against the raw target, not the evaluated target

Previous versions had T-Asc check `M' ⊑ A'` (evaluated type of M against
evaluated target). This broke monotonicity: under a more precise
environment, the target evaluates to something tighter, and the check
can fail even though it passed before.

**Concrete counterexample:** `(x : y)` under `Γ = {x: Bool, y: Bool}`
types to Bool (since `Bool ⊑ Bool`). Under `Γ' = {x: Bool, y: True}`,
the target evaluates to True, requiring `Bool ⊑ True` — which fails.
The term becomes untypeable under narrowing, violating monotonicity.

**Root cause:** The ascription target plays a dual role — covariant in
the output (the result type is the evaluated target) and contravariant
in the check (the term's type must be below the target). When the
environment narrows, the target gets tighter in both positions. The
output getting tighter is good (more precise result), but the check
getting tighter can cause failure.

**The fix:** Check `M' ⊑ A` (raw target syntax) instead of `M' ⊑ A'`
(evaluated target). Raw syntax is invariant under environment changes,
so the check is stable. The result is still the evaluated A', preserving
precision in the output.

**Consequence:** You cannot ascribe to a variable target like `(x : y)`
where x and y are independent variables. This is correct — narrowing y
could make it incompatible with x. You CAN ascribe `(x : T)` where
x: T (S-Refl), `(x : ⊤)` (S-Top), or `(x : SomeLiteral)` where x's
type is ⊑ that literal (S-Fun etc.).

**Design connection:** `:` is the phase boundary between compile-time
and runtime. The raw target is the developer's syntactic annotation —
a deliberate "stop evaluating here" marker. Checking against raw syntax
respects this boundary. Re-evaluating the target under a narrowed
environment effectively re-interprets the developer's annotation, which
breaks the contract.

**If you check against the evaluated target:** The monotonicity
counterexample returns. The trilemma is: {evaluated target check,
monotonicity, no reverse S-Var} — pick two.

## 11. E-App evaluates the body after substitution

Previous versions had E-App return the raw substituted body `B[x ≔ N']`.
This broke soundness: substitution can place precise values into
contravariant positions (parameter annotations of inner functions),
making the result less precise as a type.

**Concrete counterexample:** `f = (x: ⊤) → (y: x) → y` applied to
`(id : Id)` where `id = (z: ⊤) → z`, `Id = (z: ⊤) → ⊤`.
- Concrete: substitutes `id` for x → `(y: id) → y`. Domain is `id`.
- Abstract: substitutes `Id` for x → `(y: Id) → y`. R = `(y: Id) → y`.
- Need: `(y: id) → y ⊑ (y: Id) → y`. Contravariant check: `Id ⊑ id`.
  Fails because `(z:⊤)→⊤ ⊑ (z:⊤)→z` requires `⊤ ⊑ z`.

**The fix:** E-App evaluates `B[x ≔ N'] ⟶ V`. E-Fun fires on the
intermediate function, erasing the domain to ⊤. Now `V = (y: ⊤) → y`
and the contravariant check becomes `Id ⊑ ⊤` (S-Top). Trivially true.

**Why this works in general:** Values always have ⊤ domains (E-Fun
erases them). The S-Fun contravariant check on values is always
`domain(R) ⊑ ⊤`, which is S-Top. Contravariance becomes free.

**If you don't evaluate after substitution:** The raw substituted body
keeps precise domain annotations, and the counterexample above breaks
soundness. This is the whole reason E-Fun erases domains — but without
the extra evaluation step in E-App, E-Fun never gets the chance to fire
on intermediate results.

## 12. T-App-Top was removed (no longer in the calculus)

T-App-Top was a rule that gave any application `M N` the type ⊤
unconditionally (no premises). It went through several iterations:

**History:** The original version required `Γ ⊢ M ⇒ ⊤` as a premise.
This broke monotonicity in two ways:

- *Typeability gap:* Under a wide environment Γ (where M₁ ⇒ ⊤),
  T-App-Top fired without checking M₂. Under a narrower Γ' (where
  M₁ ⇒ (x: A) → B), T-App required M₂ to be typeable. If M₂ contained
  a failing ascription, the term became untypeable under Γ'.

- *Variable-type gap:* Under Γ, M₁ types to a function so T-App fires.
  Under Γ' ⊑ Γ, M₁ types to a variable alias. Neither T-App (needs
  syntactic function type) nor old T-App-Top (needs ⊤) applied.

The variable-type gap was resolved by head normalization (⇓) in T-App,
which unfolds variable aliases to extract function structure. The
typeability gap was temporarily resolved by making T-App-Top
unconditional (no premises).

**Why it was removed:** The unconditional T-App-Top typed nonsensical
programs (e.g., `⊤ ⊤ ⇒ ⊤`, applying a non-function) and introduced
non-determinism (every application had at least two derivations). The
monotonicity and soundness proofs turned out not to need it:

- The variable-type gap is fully handled by head normalization (⇓).
- The typeability gap doesn't arise: if a term was typeable under Γ via
  T-App (head normalizes to a function), narrowing Γ to Γ' preserves
  head normalization via HN-Mono.
- Terms that were ONLY typeable via T-App-Top (e.g., `⊤ ⊤`) are
  genuinely ill-typed — applying a non-function should be rejected.

**Current state:** T-App is the only rule for typing applications. If
the head does not normalize to a function type, the application is
rejected. The typing judgment is deterministic. Head normalization
handles all the cases that motivated T-App-Top.

**If you re-add T-App-Top:** The calculus becomes non-deterministic
and types nonsensical programs. The proofs don't need it.

## 13. T-Var must NOT normalize its result

A tempting fix for the variable-type gap (#12) is to change T-Var to
evaluate the environment entry: `x ⇒ eval(Γ(x))` instead of `x ⇒ Γ(x)`.

**This breaks T-Asc.** Consider `{T: ⊤, x: T} ⊢ (x : T)`. Under
current T-Var: `x ⇒ T`, then T-Asc checks `T ⊑ T` (raw target) via
S-Refl. Under normalizing T-Var: `x ⇒ ⊤` (since T: ⊤), then T-Asc
checks `⊤ ⊑ T` (raw target) — **not derivable**. The term becomes
untypeable.

**Root cause:** T-Asc checks against the RAW target (sharp edge #10).
If T-Var normalizes, the type `⊤` can't match the raw variable `T`.
The raw target check is essential for monotonicity (#10), so we can't
change it. And T-Var normalization destroys the variable identity that
S-Refl needs.

**The fix:** Use head normalization (⇓) in T-App instead. This only
unfolds variables at the application site, preserving variable identity
elsewhere in the system.

## 14. E-Fun must use deep domain erasure, not shallow

Previous versions had E-Fun erase only the outermost parameter
annotation: `(x: A) → M ⟶ (x: ⊤) → M` (body unchanged). This is
unsound when the body contains inner function literals whose domains
reference the parameter x.

**Concrete counterexample:**

```
M = ((x: ⊤) → (y: ⊤) → (z: x) → z) (((w: ⊤) → w) : (w: ⊤) → ⊤)

Concrete: substitute (w: ⊤) → w for x in body
  V = (y: ⊤) → (z: (w: ⊤) → w) → z

Abstract: substitute (w: ⊤) → ⊤ for x in body
  R = (y: ⊤) → (z: (w: ⊤) → ⊤) → z

Soundness check V ⊑ R fails:
  Inner domain: need (w: ⊤) → ⊤ ⊑ (w: ⊤) → w (contravariant)
  This requires w: ⊤ ⊢ ⊤ ⊑ w — NOT DERIVABLE
```

**Root cause:** With shallow erasure, the body retains raw domain
annotations mentioning x. When E-App substitutes a concrete value for x,
the precise value appears in a domain position. Abstract evaluation
substitutes the less-precise type instead. The contravariant comparison
then requires the abstract domain ⊑ the concrete domain — the wrong
direction.

**The fix:** Deep domain erasure: `(x: A) → M ⟶ (x: ⊤) → erase(M)`,
where `erase` recursively replaces all domain annotations with ⊤. This
removes x from all domain positions in the body BEFORE substitution.
After deep erasure, substitution only places values in body (covariant)
positions, where the more-precise concrete value helps rather than hurts.

**Key property of deep erasure:** All values produced by ⟶ have ⊤ in
every domain position. This makes all contravariant (domain) comparisons
in the soundness proof trivially satisfiable via S-Top.

Proof sketch (all values have erased domains):
- E-Top: ⊤ has no domains. ✓
- E-Fun: outer domain is ⊤; body domains are ⊤ via erase. ✓
- E-App: the function body has erased domains (from E-Fun). The argument
  is a value with erased domains (by IH). Substituting an erased value
  into an erased body keeps all domains ⊤ (x only appears in body
  positions after erasure). Then ⟶ on the result applies E-Fun again. ✓
- E-Asc: inherits from M. ✓

**If you revert to shallow erasure:** The counterexample above breaks
soundness. Any function whose body contains `(z: x) → ...` (a function
with a parameter-dependent domain) will produce unsound types when
applied to a concretely-precise argument.

**Semantic justification:** Domain annotations are only used at compile
time (T-App checks `N' ⊑ A`). At runtime, function application never
inspects the domain — E-App just substitutes into the body. Deep erasure
reflects this: the runtime truly carries no domain information at all.
This aligns with Ochre's "full type erasure" philosophy.

**Previously remaining sub-gap (NOW RESOLVED):** The soundness proof for
T-Fun needs `erase(M) ⊑ M` (the erased body is at least as precise as
the raw body). This now holds for ALL cases: variables (S-Refl),
⊤ (S-Refl), function literals (S-Fun with S-Top on domain), applications
(S-App congruence), and ascription terms (S-Asc congruence with IH on
both components). See lemma-erase-sub.md.

## 15. Head normalization must evaluate applications and ascriptions

Previous versions had ⇓ only unfold variables (HN-Var) and return
non-variables unchanged (HN-Nonvar). This breaks monotonicity when
environment entries are application or ascription terms that evaluate
to function types.

**Concrete counterexample:**

```
Γ  = {z: (x: ⊤) → (y: ⊤) → y}
Γ' = {z: ((f: ⊤) → (x: ⊤) → (y: ⊤) → y) ⊤}

Γ'(z) ⊑ Γ(z) via S-Eval: the application evaluates to
(x: ⊤) → (y: ⊤) → y.  ✓ (Γ' ⊑ Γ)

Under Γ:  z ⊤ ⇒ (y: ⊤) → y  (T-App fires: z types to function)
Under Γ': z ⊤ ⇒ ???          (old ⇓ can't see through the application
                               term, T-App fails, term is untypeable)

Monotonicity broken: term is typeable under Γ but not Γ'.
```

**Root cause:** Under Γ' ⊑ Γ, the narrowed environment may contain
entries that are application terms (from S-Eval subtyping). These
application terms evaluate to function types, but the old ⇓ (which
only unfolds variables) couldn't resolve them.

**The fix:** Add HN-Eval: when ⇓ encounters an application or ascription
term, first abstractly evaluate it (⇒), then ⇓ the result. This gives ⇓
the power to see through evaluated application terms.

```
[HN-Eval]
Γ ⊢ F ⇒ F'
Γ ⊢ F' ⇓ G
————————————————————————————
Γ ⊢ F ⇓ G
(where F is an application or ascription)
```

**Termination:** In Och₀ without recursive types, ⇒ always terminates.
The result F' is "more evaluated" — the chain converges. Well-founded
environments ensure HN-Var terminates. Together, ⇓ terminates.

**If you remove HN-Eval:** The counterexample above breaks monotonicity.
Any environment where entries are application terms (which arise naturally
from S-Eval narrowing) will fail to head-normalize to function types.

## 16. T-App must erase domains in the body before substitution

**If you substitute into raw B (without erasing):** The argument type N'
lands in domain (contravariant) positions of B. Under monotonicity, a more
precise N'' ⊑ N' produces a result type with a more precise domain, which
is LESS precise as a function type (contravariance). Monotonicity fails.

**Concrete counterexample:**

```
Γ  = { a: (w: ⊤) → ⊤ }
Γ' = { a: (w: ⊤) → w }
Γ' ⊑ Γ  (since (w: ⊤) → w ⊑ (w: ⊤) → ⊤)

M = ((x: ⊤) → (y: x) → y) a

Under Γ:  B = (y: x) → y, N' = (w: ⊤) → ⊤
  B[x ≔ N'] = (y: (w: ⊤) → ⊤) → y
  R = (y: (w: ⊤) → ⊤) → y

Under Γ': B = (y: x) → y, N'' = (w: ⊤) → w
  B[x ≔ N''] = (y: (w: ⊤) → w) → y
  R' = (y: (w: ⊤) → w) → y

R' ⊑ R requires (w: ⊤) → ⊤ ⊑ (w: ⊤) → w (contra in domain),
which requires ⊤ ⊑ w — NOT DERIVABLE.
```

**Root cause:** The argument type x appears in a domain position of the
body B = (y: x) → y. Substituting different values of x into this domain
creates a contravariant comparison that goes the wrong direction.

This is the abstract-evaluation analogue of sharp edge #14 (E-Fun deep
domain erasure for soundness). The concrete evaluation side was fixed by
E-Fun erasing all domains. The abstract evaluation side has the same
issue and needs the same fix.

**The fix:** T-App substitutes into `erase(B)` instead of `B`:

```
[T-App]
Γ ⊢ M ⇒ F
Γ ⊢ F ⇓ (x: A) → B
Γ ⊢ N ⇒ N'
Γ ⊢ N' ⊑ A
Γ ⊢ erase(B)[x ≔ N'] ⇒ R
——————————————————————————
Γ ⊢ M N ⇒ R
```

After erasure, x only appears in body (covariant) positions of erase(B).
Substituting N'' ⊑ N' into covariant positions preserves the ⊑ direction.

**Precision loss:** Domain annotations in the body that depend on the
function parameter are lost. For example, `(y: x) → y` becomes
`(y: ⊤) → y` — we no longer track that y has the same type as the
argument. But this information was always erased at runtime (E-Fun deep
erasure), so the abstract side was over-promising. The types now match
the runtime behavior.

**If you remove the erasure:** The counterexample above breaks
monotonicity. Any function body that places the parameter in a domain
position will exhibit the wrong-direction comparison under narrowing.

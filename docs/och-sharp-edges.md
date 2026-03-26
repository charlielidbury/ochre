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

## 8. Subtyping has no structural rule for ascription

There is no rule to compare `(M₁ : A₁) ⊑ (M₂ : A₂)`. Ascription terms
in subtyping position can only be handled by S-Refl (syntactic equality)
or S-Top (right side is ⊤).

This is currently OK because T-App evaluates the body after substitution,
which resolves ascriptions before they appear in types. If ascription
terms ever appear in types (e.g. from a T-App that doesn't evaluate),
subtyping breaks.

**If you add S-Asc:** Be very careful about what it means. The obvious
`(M : A) ⊑ B if A ⊑ B` is tempting but mixes the semantics of
ascription (a compile-time operation) into subtyping (a structural
relation). It might be fine, but needs careful analysis.

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

## 12. T-App-Top is unconditional (no premises)

Previous versions required `Γ ⊢ M ⇒ ⊤` as a premise of T-App-Top.
This broke monotonicity in two ways:

**Problem 1 — Typeability gap:** Under a wide environment Γ (where
M₁ ⇒ ⊤), T-App-Top fires without checking M₂. Under a narrower Γ'
(where M₁ ⇒ (x: A) → B), T-App requires M₂ to be typeable. If M₂
contains a failing ascription, the term is untypeable under Γ'.

Concrete counterexample: `f ((⊤ : (x: ⊤) → x))` under `{f: ⊤}` types
to ⊤ (T-App-Top skips the argument), but under `{f: (y: ⊤) → ⊤}` the
argument is untypeable.

**Problem 2 — Variable-type gap:** Under Γ, M₁ ⇒ (x: A) → B (a
function type) so T-App fires. Under Γ' ⊑ Γ, M₁ ⇒ g (a variable that
is a subtype of a function type via S-Var). Neither T-App (needs
syntactic function type) nor old T-App-Top (needs ⊤) applies.

Concrete counterexample: `f ((z: ⊤) → z)` under `{g: ⊤, f: (x: ⊤) → x}`
types to `(z: ⊤) → z`, but under `{g: (x: ⊤) → x, f: g}` is untypeable
(f ⇒ g, a variable).

**The fix:** Make T-App-Top unconditional. Any application `M N` always
has type ⊤ as a fallback. This makes the typing judgment non-deterministic
(T-App and T-App-Top can both fire), but every derivation is sound
(V ⊑ ⊤ by S-Top), and monotonicity can always fall back to ⊤ ⊑ ⊤.

**If you add premises back to T-App-Top:** Both gaps reopen. The typing
judgment becomes partial (some well-formed terms are untypeable), and
narrowing can make previously-typeable terms untypeable.

**Design connection:** This aligns with Ochre's "everything has a type"
philosophy. Applications always produce at least ⊤ (no information).
Precision is controlled by ascription (`:`) — if you want to assert that
`f x` returns a specific type, write `(f x : T)`. The ascription check
catches incompatible applications.

**Remaining limitation:** The unconditional T-App-Top fixes monotonicity
for T-App-Top and T-App-Stuck cases, but when the original derivation
used T-App (giving precise R), and under Γ' only T-App-Top applies
(giving ⊤), we need ⊤ ⊑ R which fails. This happens when M₁'s type
degrades from a function type to a variable under narrowing. Fully
resolving this requires T-Var to normalize its result (evaluate the
environment entry) — see discussion in proof-status.md.

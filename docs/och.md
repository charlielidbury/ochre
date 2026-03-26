# Och

A minimal core calculus for testing the semantic typing idea behind Ochre.
See ./what-is-och.md for motivation and context.

## Syntax

```
Terms:
  M, N, A, B ::=
    | x                — variable
    | (x: A) → M       — function (lambda and pi are the same thing)
    | M N              — application
    | ⊤                — top type (maximally approximate, no information)
    | M : A            — ascription (deliberately lose precision)

Environments:
  Γ ::= · | Γ, x: A

Well-foundedness (⊢ Γ ok):
  Contexts must be well-formed: for each binding x: A in Γ, every
  free variable of A must already be in scope (FV(A) ⊆ dom(Γ_before_x)).
  Formally this is defined by WF-Empty and WF-Ext in
  proofs/lemma-context-wf.md. This is strictly stronger than mere
  acyclicity: it ensures all free variables in bindings are in scope,
  which is needed for the scoping lemmas and for ⇓ termination.
```

### Notes

- **Terms and types share one syntax.** There is no separate grammar for
  types. A function `(x: A) → M` is simultaneously a lambda (computable)
  and a pi type (classifies functions). This is the core "terms are types"
  idea — there is no phase distinction.

- **No atoms, unions, pairs, or match yet.** This is Och₀ — the absolute
  minimum needed to test whether the abstract/concrete interpretation
  story is sound and monotone for higher-order functions.

- **Ascription `M : A` is the only way to lose precision.** Without it,
  every term's type is maximally precise (i.e. the term itself). Ascription
  widens `M` to type `A`, provided `M ⊑ A`.

- **`⊤` is the least precise type.** Every term is a subtype of `⊤`.
  It represents "I know nothing about this value." It also serves as the
  unit/trivial value when used at runtime.

- **One function form.** `(x: A) → M` is both a computable function and
  a type. At runtime, E-Fun erases the parameter annotation to ⊤ and
  E-App substitutes the concrete argument into the body. At compile time,
  T-Fun returns the function as-is, and T-App substitutes the argument's
  type into the body then abstractly evaluates the result. The body is
  only evaluated at application time, when the argument type is known.
  Runtime and compile-time diverge at two points: ascription (`:` loses
  precision at compile time but is erased at runtime) and parameter
  annotations (carried at compile time but erased to ⊤ at runtime).

### Examples

```
— The identity function (also its own most-precise type)
id = (x: ⊤) → x

— A less precise type for id, losing the "returns its argument" info
Id = (x: ⊤) → ⊤

— Ascription: widen a precise term to a less precise type
((x: ⊤) → x) : (x: ⊤) → ⊤

— A constant function
const = (x: ⊤) → (y: ⊤) → x
```

## Abstract Evaluation (Typing)

The judgment `Γ ⊢ M ⇒ A` means "under environment Γ, the most precise
type of M is A." Since types are terms, A is a term too. The typing
judgment is deterministic: each term has at most one type under a given
environment (and some terms are untypeable, e.g., applying a non-function).

```
[T-Top]
———————————
Γ ⊢ ⊤ ⇒ ⊤

[T-Var]
x: A ∈ Γ
———————————
Γ ⊢ x ⇒ A

[T-Fun]
—————————————————————————————————————————
Γ ⊢ (x: A) → M ⇒ (x: A) → M

[T-App]
Γ ⊢ M ⇒ F
Γ ⊢ F ⇓ (x: A) → B
Γ ⊢ N ⇒ N'
Γ ⊢ N' ⊑ A
Γ ⊢ erase(B)[x ≔ N'] ⇒ R
——————————————————————————
Γ ⊢ M N ⇒ R

[T-Asc]
Γ ⊢ M ⇒ M'
Γ ⊢ M' ⊑ A
Γ ⊢ A ⇒ A'
———————————
Γ ⊢ (M : A) ⇒ A'
```

### Head Normalization

The judgment `Γ ⊢ F ⇓ G` resolves F to a "head normal form" — either
⊤ or a function type `(x: A) → B`. Used by T-App to extract function
structure from types that may be variable aliases, application terms,
or ascription terms that evaluate to function types.

```
[HN-Fun]
————————————
Γ ⊢ (x: A) → B ⇓ (x: A) → B

[HN-Top]
————————————
Γ ⊢ ⊤ ⇓ ⊤

[HN-Var]
x: A ∈ Γ
Γ ⊢ A ⇓ G
————————————
Γ ⊢ x ⇓ G

[HN-Eval]
Γ ⊢ F ⇒ F'
Γ ⊢ F' ⇓ G
————————————————————————————
Γ ⊢ F ⇓ G
(where F is an application or ascription)
```

**Termination:** HN-Fun and HN-Top are base cases. HN-Var terminates
under well-founded environments (acyclic variable bindings). HN-Eval
terminates because abstract evaluation (⇒) always terminates in Och₀
(no recursive types or fixpoints), and the result F' is "more evaluated"
than F — the chain of ⇒ results converges to a function type or ⊤.

**Why HN-Eval is needed:** Without it, environment entries that are
application or ascription terms (which arise from S-Eval in narrowed
environments) cannot be resolved to function types. This breaks
monotonicity: under a narrower Γ', a variable's type might become an
application term that evaluates to a function type, but the old ⇓
couldn't see through it (see sharp edge #15).

### Notes on typing

- **T-Fun**: A function literal is its own type. The body is NOT
  abstractly evaluated at definition time — it remains as raw syntax.
  Evaluation of the body happens at application time (in T-App), when
  the actual argument type is known.

- **T-App**: First types M to get F, then head-normalizes F to extract
  the function structure `(x: A) → B`. Head normalization unfolds
  variable aliases, evaluates application/ascription terms, and recurses
  until a function type or ⊤ is reached. Then **erases** the body B
  (replacing all domain annotations with ⊤) before substituting the
  argument's type (N') and abstractly evaluating the result. The erasure
  mirrors E-Fun's deep domain erasure at runtime and is essential for
  monotonicity: without it, the argument type N' lands in contravariant
  (domain) positions of B, and a more-precise N' produces a LESS precise
  result type at those positions (see sharp edge #16). Head normalization
  is also essential for monotonicity: under a narrower environment, M₁'s
  type may become a variable alias or an application term that evaluates
  to a function type (see sharp edges #12, #15). Without ⇓, T-App would
  fail on these, breaking monotonicity. T-App is the ONLY rule for
  typing applications — if the head does not normalize to a function
  type, the application is untypeable (rejected).

- **T-Asc**: Abstractly evaluates M to get M', checks M' ⊑ A (the raw
  target, not evaluated), then evaluates A to get the result type A'.
  The check uses raw A so that it is stable under environment narrowing
  (see sharp edge #10). The target is still evaluated for the result
  type, so downstream typing sees a clean evaluated form.

## Subtyping

The judgment `Γ ⊢ A ⊑ B` means "A is at least as precise as B under Γ."
Equivalently: every value described by A is also described by B.

```
[S-Top]
———————————
Γ ⊢ A ⊑ ⊤

[S-Refl]
———————————
Γ ⊢ A ⊑ A

[S-Trans]
Γ ⊢ A ⊑ B
Γ ⊢ B ⊑ C
———————————
Γ ⊢ A ⊑ C

[S-Var]
x: A ∈ Γ
Γ ⊢ A ⊑ B
———————————
Γ ⊢ x ⊑ B

[S-Fun]
Γ ⊢ B₁ ⊑ A₁
Γ, x: B₁ ⊢ M₁ ⊑ M₂
——————————————————————————————
Γ ⊢ (x: A₁) → M₁ ⊑ (x: B₁) → M₂

[S-App]
Γ ⊢ M₁ ⊑ M₂
Γ ⊢ N₁ ⊑ N₂
——————————————————————————————
Γ ⊢ M₁ N₁ ⊑ M₂ N₂

[S-Asc]
Γ ⊢ M₁ ⊑ M₂
Γ ⊢ A₁ ⊑ A₂
——————————————————————————————
Γ ⊢ (M₁ : A₁) ⊑ (M₂ : A₂)

[S-Eval]
Γ ⊢ M ⇒ M'
———————————
Γ ⊢ M ⊑ M'
```

### Notes on subtyping

- **S-Fun**: Contravariant in domain, covariant in body. The body
  comparison happens under the *narrower* domain (B₁, from the
  supertype). This means: "if the supertype accepts B₁'s, then
  for any such input, the subtype's body must be at least as
  precise as the supertype's body."

- **S-App**: Application is monotone in both function and argument.
  If M₁ ⊑ M₂ (more precise function) and N₁ ⊑ N₂ (more precise
  argument), then M₁ N₁ ⊑ M₂ N₂ (more precise application). This
  rule is needed for the domain erasure lemma: `erase(M) ⊑ M` requires
  comparing application subterms structurally.

- **S-Asc**: Ascription is monotone (covariant) in both the inner term
  and the target type. If M₁ ⊑ M₂ and A₁ ⊑ A₂, then (M₁ : A₁) ⊑
  (M₂ : A₂). This is the ascription analogue of S-App — structural
  congruence for the other compound form. Needed for the domain erasure
  lemma: `erase(M : A) = erase(M) : erase(A)`, and by IH
  `erase(M) ⊑ M` and `erase(A) ⊑ A`, so S-Asc gives the result.
  **Soundness:** S-Asc does not re-enable the Ochre monotonicity bug.
  The bug requires deriving `False ⊑ b` (a value below a variable),
  and S-Asc only applies when both sides are ascription terms. It also
  does not enable any false subtyping judgments: semantically, (M : A)
  as a type evaluates to A' (evaluated A), so (M₁ : A₁) ⊑ (M₂ : A₂)
  requires A₁' ⊑ A₂', which follows from A₁ ⊑ A₂ by monotonicity
  of evaluation.

- **S-Eval**: A term is at least as precise as its abstract evaluation.
  This cannot be proved from the other rules alone, so it is added as
  an axiom.
  It does not enable the monotonicity counterexample because no typing
  rule produces a variable as the type of a function literal.

- **Open question**: S-Fun compares bodies structurally (after
  substitution via the context). This may not be enough computation
  to catch the monotonicity bug once we add atoms/match. At that
  point we may need to normalize bodies before comparing, or move
  toward evaluation-based subtyping.

## Domain Erasure

The function `erase(M)` recursively replaces all domain annotations with ⊤.

```
erase(⊤) = ⊤
erase(x) = x
erase((x: A) → M) = (x: ⊤) → erase(M)
erase(M N) = erase(M) erase(N)
erase(M : A) = erase(M) : erase(A)
```

This is used by E-Fun to perform deep type erasure: not only is the
outermost parameter annotation erased, but all domain annotations inside
the body are erased too. This prevents substitution in E-App from placing
precise values into contravariant (domain) positions of inner functions,
which would break soundness (see sharp edge #14).

## Concrete Evaluation

The judgment `M ⟶ V` means "M reduces to V at runtime."

```
[E-Top]
———————————
⊤ ⟶ ⊤

[E-Fun]
———————————
(x: A) → M ⟶ (x: ⊤) → erase(M)

[E-App]
M ⟶ (x: A) → B
N ⟶ N'
B[x ≔ N'] ⟶ V
——————————————————————————
M N ⟶ V

[E-Asc]
M ⟶ V
———————————
(M : A) ⟶ V
```

### Notes on concrete evaluation

- **E-Fun**: Deep type erasure at runtime. The parameter annotation is
  erased to ⊤, AND all domain annotations inside the body are
  recursively erased to ⊤ via `erase(M)`. This reflects full type
  erasure: the runtime doesn't need any parameter type information.
  Deep erasure is essential for soundness: without it, E-App substitution
  places precise concrete values into inner domain positions, creating
  a mismatch with abstract evaluation where the less-precise argument
  type is substituted instead. The contravariant domain comparison
  then goes the wrong direction (see sharp edge #14).

- **E-App**: Standard big-step beta reduction — substitute the evaluated
  argument into the body, then evaluate the result. This ensures the
  result is always a value (⊤ or a function with erased domain). The
  extra evaluation step is critical: without it, substitution can place
  precise values into contravariant positions (parameter annotations),
  which breaks soundness (see sharp edge #11).

- **E-Asc**: Ascription is erased at runtime. It only affects typing.

- This is a big-step semantics. No environment needed because we
  substitute eagerly.

## Desired Properties

1. **Soundness**: If `Γ ⊢ M ⇒ A` and `M ⟶ V`, then `Γ ⊢ V ⊑ A`.
   (The runtime result is at least as precise as the static type.)

2. **Monotonicity**: If `Γ ⊢ M ⇒ A` and `Γ' ⊑ Γ` (pointwise),
   then `Γ' ⊢ M ⇒ A'` where `Γ' ⊢ A' ⊑ A`.
   (More precise environment → more precise type. THIS IS THE ONE
   THAT BROKE IN OCHRE.)

## Monotonicity Counterexample (Resolved)

The original Ochre bug (Prop. 5.2.9) used atoms and match. The same
bug structure can be expressed in Och₀ using Church booleans:

```
Bool  = (T: ⊤) → (x: T) → (y: T) → T
True  = (T: ⊤) → (x: T) → (y: T) → x
False = (T: ⊤) → (x: T) → (y: T) → y
```

Consider the term `False : b`. For this to type-check under T-Asc,
we need `False ⊑ b` (after evaluating the target `b` to its type).
But S-Var only gives `b ⊑ Bool` (variable on the left of ⊑). No
rule derives `False ⊑ b` or `anything ⊑ b` (except `b ⊑ b` via
S-Refl). So `False : b` is **rejected in all environments**.

This means the Ochre monotonicity bug cannot occur — the dangerous
program is rejected before narrowing even enters the picture. The
one-directional nature of S-Var prevents it.

## Examples

### Church Booleans

```
Bool  = (T: ⊤) → (x: T) → (y: T) → T
True  = (T: ⊤) → (x: T) → (y: T) → x
False = (T: ⊤) → (x: T) → (y: T) → y
```

`Bool` is the type: "give me any type T, then two values of that type,
and I'll return something of type T." `True` and `False` are more precise:
they commit to returning the first or second argument respectively.

**Proof: `True ⊑ Bool`**

```
· ⊢ (T: ⊤) → (x: T) → (y: T) → x ⊑ (T: ⊤) → (x: T) → (y: T) → T
  by S-Fun, need:
  1. · ⊢ ⊤ ⊑ ⊤
     by S-Refl ✓
  2. T: ⊤ ⊢ (x: T) → (y: T) → x ⊑ (x: T) → (y: T) → T
     by S-Fun, need:
     2a. T: ⊤ ⊢ T ⊑ T
         by S-Refl ✓
     2b. T: ⊤, x: T ⊢ (y: T) → x ⊑ (y: T) → T
         by S-Fun, need:
         2b-i.  T: ⊤, x: T ⊢ T ⊑ T
                by S-Refl ✓
         2b-ii. T: ⊤, x: T, y: T ⊢ x ⊑ T
                by S-Var, x: T ∈ Γ, need:
                T: ⊤, x: T, y: T ⊢ T ⊑ T
                  by S-Refl ✓
```

`False ⊑ Bool` is symmetric, with `y ⊑ T` at the leaf instead of `x ⊑ T`.

### If-then-else

Since Church booleans *are* if-then-else, we can apply them directly.
Given some `b : Bool`:

```
· ⊢ b ⊤ M N ⇒ ???
```

Typing step by step:

```
· ⊢ b ⊤ M N
  b has type Bool = (T: ⊤) → (x: T) → (y: T) → T

  · ⊢ b ⊤ ⇒ (x: ⊤) → (y: ⊤) → ⊤
    by T-App: substitute T ≔ ⊤ into (x: T) → (y: T) → T

  · ⊢ b ⊤ M ⇒ (y: ⊤) → ⊤
    by T-App: substitute x ≔ M' into (y: ⊤) → ⊤ (M' ⊑ ⊤ by S-Top)

  · ⊢ b ⊤ M N ⇒ ⊤
    by T-App: substitute y ≔ N' into ⊤ (N' ⊑ ⊤ by S-Top)
```

The result type is ⊤ — we lost all information. This is because `Bool`
only promises to return "something of type T", and we instantiated T
with ⊤. If we had a more precise type for `b` (e.g. `True`), we'd get
a more precise result:

```
· ⊢ b ⊤ M N  where b : True
  b has type True = (T: ⊤) → (x: T) → (y: T) → x

  · ⊢ b ⊤ ⇒ (x: ⊤) → (y: ⊤) → x
    by T-App: substitute T ≔ ⊤

  · ⊢ b ⊤ M ⇒ (y: ⊤) → M'
    by T-App: substitute x ≔ M' (where M' is the type of M)

  · ⊢ b ⊤ M N ⇒ M'
    by T-App: substitute y ≔ N'... but the body is M', which
    doesn't mention y, so the result is just M'.
```

When b is `True`, we get back the type of the first argument. This is
the precision-by-default story working: more precise input ⇒ more precise
output. This is also exactly the monotonicity property we want.

## TODO

- Prove soundness and monotonicity (see och-soundness-proof.md)
- Determine whether S-Eval needs to be added as a rule
- Think about what happens when we add unions and atoms

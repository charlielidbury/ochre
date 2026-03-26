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
type of M is A." Since types are terms, A is a term too.

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
Γ ⊢ M ⇒ (x: A) → B
Γ ⊢ N ⇒ N'
Γ ⊢ N' ⊑ A
Γ ⊢ B[x ≔ N'] ⇒ R
——————————————————————————
Γ ⊢ M N ⇒ R

[T-App-Top]
Γ ⊢ M ⇒ ⊤
——————————————————————————
Γ ⊢ M N ⇒ ⊤

[T-Asc]
Γ ⊢ M ⇒ M'
Γ ⊢ M' ⊑ A
Γ ⊢ A ⇒ A'
———————————
Γ ⊢ (M : A) ⇒ A'
```

### Notes on typing

- **T-Fun**: A function literal is its own type. The body is NOT
  abstractly evaluated at definition time — it remains as raw syntax.
  Evaluation of the body happens at application time (in T-App), when
  the actual argument type is known.

- **T-App**: Substitutes the argument's type (N') into the raw body B,
  then abstractly evaluates the result. This means ascription checking
  and precision loss happen at the call site, with the actual argument
  type in scope. This avoids the problem of pre-evaluating the body
  with only the parameter type, which would substitute a potentially
  too-wide type into contravariant positions.

- **T-App-Top**: If we apply something of type ⊤ (we don't know it's
  a function), the result is ⊤. This is the "no information in, no
  information out" case.

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

- **S-Eval**: A term is at least as precise as its abstract evaluation.
  This cannot be proved from the other rules (application and ascription
  terms have no structural subtyping rules), so it is added as an axiom.
  It does not enable the monotonicity counterexample because no typing
  rule produces a variable as the type of a function literal.

- **Open question**: S-Fun compares bodies structurally (after
  substitution via the context). This may not be enough computation
  to catch the monotonicity bug once we add atoms/match. At that
  point we may need to normalize bodies before comparing, or move
  toward evaluation-based subtyping.

## Concrete Evaluation

The judgment `M ⟶ V` means "M reduces to V at runtime."

```
[E-Top]
———————————
⊤ ⟶ ⊤

[E-Fun]
———————————
(x: A) → M ⟶ (x: ⊤) → M

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

- **E-Fun**: The parameter annotation is erased to ⊤ at runtime. This
  reflects the fact that type checking has already happened at compile
  time — the runtime doesn't need to know what type the parameter was
  declared as. Two functions that differ only in their parameter
  annotation evaluate to the same runtime value.

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

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

- **One function form.** `(x: A) → M` is both "the function that takes
  `x` of type `A` and returns `M`" and "the type of functions that take
  an `A` and return something in `M`". When used as a type, `M` is the
  body interpreted abstractly; when applied at runtime, `M` is the body
  executed concretely. The difference is in the semantics, not the syntax.

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
——————————————————————————
Γ ⊢ M N ⇒ B[x ≔ N']

[T-App-Top]
Γ ⊢ M ⇒ ⊤
——————————————————————————
Γ ⊢ M N ⇒ ⊤

[T-Asc]
Γ ⊢ M ⇒ M'
Γ ⊢ M' ⊑ A
———————————
Γ ⊢ (M : A) ⇒ A
```

### Notes on typing

- **T-Fun**: A function is its own most precise type. No need to evaluate
  the body — the function literal *is* the type.

- **T-App**: To type an application, we get the type of the function,
  check the argument is in the domain, then substitute the argument's
  type into the body. This is the "abstract evaluation" — we're running
  the function on the *type* of the argument, not the argument itself.

- **T-App-Top**: If we apply something of type ⊤ (we don't know it's
  a function), the result is ⊤. This is the "no information in, no
  information out" case.

- **T-Asc**: Ascription evaluates M, checks the result is a subtype
  of A, then returns A (losing precision).

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
```

### Notes on subtyping

- **S-Fun**: Contravariant in domain, covariant in body. The body
  comparison happens under the *narrower* domain (B₁, from the
  supertype). This means: "if the supertype accepts B₁'s, then
  for any such input, the subtype's body must be at least as
  precise as the supertype's body."

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
(x: A) → M ⟶ (x: A) → M

[E-App]
M ⟶ (x: A) → B
N ⟶ N'
——————————————————————————
M N ⟶ B[x ≔ N']

[E-Asc]
M ⟶ V
———————————
(M : A) ⟶ V
```

### Notes on concrete evaluation

- **E-App**: Standard beta reduction — substitute the evaluated argument
  into the body. No type checking at runtime.

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

## Monotonicity Counterexample

The original Ochre bug (Prop. 5.2.9) used atoms and match. Here is the
same bug reproduced in Och₀ using only Church booleans.

```
Bool  = (T: ⊤) → (x: T) → (y: T) → T
True  = (T: ⊤) → (x: T) → (y: T) → x
False = (T: ⊤) → (x: T) → (y: T) → y
```

Consider the term `False : b` under two environments:

**Wide environment: `b: Bool`**

```
b: Bool ⊢ (False : b) ⇒ b
  by T-Asc, need:
  1. b: Bool ⊢ False ⇒ False
     by T-Fun ✓
  2. b: Bool ⊢ False ⊑ b
     by S-Var (b: Bool ∈ Γ) + S-Trans, need:
     b: Bool ⊢ False ⊑ Bool
       (see proof below in Church Booleans section) ✓
```

This holds: `False ⊑ Bool`, and `b` has type `Bool`, so `False ⊑ b`.

**Narrow environment: `b: True`**

```
b: True ⊢ (False : b) ⇒ b
  by T-Asc, need:
  1. b: True ⊢ False ⇒ False
     by T-Fun ✓
  2. b: True ⊢ False ⊑ b
     by S-Var (b: True ∈ Γ), need:
     b: True ⊢ False ⊑ True
       at the leaf: T: ⊤, x: T, y: T ⊢ y ⊑ x
       by S-Var (y: T ∈ Γ), need: T ⊑ x
       no rule gives us T ⊑ x — we only have x ⊑ T, not the reverse.
       ✗ FAILS
```

**This is the monotonicity bug.** We narrowed the environment from
`b: Bool` to `b: True` (and `True ⊑ Bool`), but the judgment broke.
A previously valid ascription became invalid under a more precise context.

The root cause is S-Var: `b ⊑ B` holds when `B` is wide enough to
contain all of `b`'s type, but when `b`'s type narrows, the thing we're
ascribing to also narrows, and the ascription target becomes too precise
for the value.

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

- Determine whether S-Fun needs normalization of bodies
- Think about what happens when we add unions and atoms
- Try to prove soundness and monotonicity for Och₀

# Och

A minimal core calculus for testing the semantic typing idea behind Ochre.
See ./what-is-och.md for motivation and context.

## Syntax

```
Terms:
  M, N, A, B ::=
    | x                -- variable
    | (x: A) -> M      -- function (lambda and pi are the same thing)
    | M N              -- application
    | Top              -- top type (maximally approximate, no information)
    | M : A            -- ascription (deliberately lose precision)

Values:
  V ::=
    | (x: A) -> M      -- closure
    | Top

Environments:
  G ::= . | G, x: A
```

### Notes

- **Terms and types share one syntax.** There is no separate grammar for
  types. A function `(x: A) -> M` is simultaneously a lambda (computable)
  and a pi type (classifies functions). This is the core "terms are types"
  idea -- there is no phase distinction.

- **No atoms, unions, pairs, or match yet.** This is Och_0 -- the absolute
  minimum needed to test whether the abstract/concrete interpretation
  story is sound and monotone for higher-order functions.

- **Ascription `M : A` is the only way to lose precision.** Without it,
  every term's type is maximally precise (i.e. the term itself). Ascription
  widens `M` to type `A`, provided `M <: A`.

- **`Top` is the least precise type.** Every term is a subtype of `Top`.
  It represents "I know nothing about this value." It also serves as the
  unit/trivial value when used at runtime.

- **One function form.** `(x: A) -> M` is both "the function that takes
  `x` of type `A` and returns `M`" and "the type of functions that take
  an `A` and return something in `M`". When used as a type, `M` is the
  body interpreted abstractly; when applied at runtime, `M` is the body
  executed concretely. The difference is in the semantics, not the syntax.

### Examples

```
-- The identity function (also its own most-precise type)
id = (x: Top) -> x

-- A less precise type for id, losing the "returns its argument" info
Id = (x: Top) -> Top

-- Ascription: widen a precise term to a less precise type
((x: Top) -> x) : (x: Top) -> Top

-- A constant function
const = (x: Top) -> (y: Top) -> x
```

## TODO

- Subtyping rules
- Abstract evaluation (typing) rules
- Concrete evaluation (runtime) rules
- Soundness and monotonicity theorem statements

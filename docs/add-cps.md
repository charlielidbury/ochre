# Och Extension: CPS Bind Operator (`?`)

## Prerequisites

This extension builds on the core Och calculus defined in och-spec.md. All typing
rules, properties, and test cases from that document are assumed. This extension
adds one syntactic form and proves it is a conservative extension (it accepts
strictly more programs without invalidating any existing judgments).

---

## 1. Motivation

Church-encoded data types are eliminated via continuation-passing style. For
example, unpacking a dependent pair:

```
s ResultType (λ(n: Nat). λ(arr: Array n T). <body using n and arr>)
```

With deeply nested eliminations, this becomes unwieldy:

```
v1 (Vec T) (λ(n1: Nat). λ(arr1: Array n1 T).
  v2 (Vec T) (λ(n2: Nat). λ(arr2: Array n2 T).
    mkVec T (add n1 n2) (appendArrays T n1 n2 arr1 arr2)))
```

The `?` operator converts this CPS into direct style, making the code linear
rather than nested.

---

## 2. Syntax Extension

Add one new syntactic form:

```
e ::= ... | e?                  -- CPS bind
```

And a block delimiter that determines the scope of `?` captures:

```
e ::= ... | { e₁; e₂; ...; eₙ }   -- block (delimits ? scope)
```

All Och files are implicitly wrapped in a block.

---

## 3. Desugaring

The `?` operator is **pure syntactic sugar**. It desugars into lambda abstractions
and applications, which are already in the core calculus.

### 3.1 Basic Rule

Within a block, `x = e?; rest` desugars to `e(λ(x: T). rest)`, where `T` is
inferred from the type of `e`.

Specifically, if `e` has type `λ(X: Type). λ(_: T → R). S` (a Church-encoded
eliminator), then:
- `X` is inferred from the expected return type of the block
- `x` is bound with type `T`
- `rest` (the remainder of the block) becomes the continuation body, with type `R`
- The whole expression has type `S`

### 3.2 `id?` for Curried Arguments

When `?` is applied to the identity function, it constructs a lambda:

`x = id?; rest` desugars to `id(λ(x: T). rest)` which equals `λ(x: T). rest`.

This allows peeling curried arguments one at a time. A Church-encoded pair
eliminator takes a two-argument continuation `(A → B → X) → X`. Using `?` twice:

```
a = p?;       -- desugars to: p(λa. rest₁)
b = id?;      -- desugars to: id(λb. rest₂) = λb. rest₂
```

Combined: `p(λa. λb. rest₂)`, which is exactly the CPS elimination.

### 3.3 Block Scoping

The `?` operator captures everything until the end of the enclosing `{ }` block.
This means:

```
{ (foo?) + 1 }       -- ? captures "+ 1", result is foo(λx. x + 1)
{ { foo? } + 1 }     -- ? captures only inner block, foo? = foo(λx. x), then + 1
```

### 3.4 Complete Desugaring Example

The `appendVec` function from och-spec.md:

```
-- Core calculus form (from och-spec.md):
appendVec = λ(T: Type). λ(v1: Vec T). λ(v2: Vec T).
            v1 (Vec T) (λ(n1: Nat). λ(arr1: Array n1 T).
              v2 (Vec T) (λ(n2: Nat). λ(arr2: Array n2 T).
                mkVec T (add n1 n2) (appendArrays T n1 n2 arr1 arr2)));

-- With ? operator:
appendVec = λ(T: Type). λ(v1: Vec T). λ(v2: Vec T). {
            n1   = v1?;
            arr1 = id?;
            n2   = v2?;
            arr2 = id?;
            mkVec T (add n1 n2) (appendArrays T n1 n2 arr1 arr2) };
```

These are definitionally equal after desugaring.

---

## 4. Typing

Since `?` desugars into core forms, no new typing rules are needed. The desugaring
pass transforms `?` expressions into applications and lambdas, and the existing
typing rules handle those.

The only obligation is that the desugaring is **type-preserving**: if the desugared
form is well-typed, the original `?` form is well-typed with the same type, and
vice versa.

---

## 5. Properties

### 5.1 Conservative Extension

For any program `P` using `?`, let `D(P)` be its desugaring. Then:
- `Γ ⊢ P ⇝ τ` if and only if `Γ ⊢ D(P) ⇝ τ`

### 5.2 Preservation of Core Properties

Since `?` is sugar, soundness, monotonicity, ascription soundness, and
transparency preservation all follow from the core calculus proofs.

---

## 6. Open Questions

### 6.1 Empty Continuations

What does `{ e? }` mean when there is nothing after the `?`? The continuation
would be the identity function, so `{ e? }` should equal `e id`. This needs a
precise scoping rule.

### 6.2 Type Inference for X

When `e : λ(X: Type). λ(_: T → X). X`, the `?` desugaring needs to infer `X` from
the expected type of the enclosing block. This is an inference obligation that
the desugaring pass must handle, potentially requiring bidirectional type checking
or contextual information.

### 6.3 Interaction with `fix`

Inside a `fix` body, `?` should work normally — it just desugars into lambdas.
But the interaction with the termination checker needs verification: does the
desugared form preserve the structural descent property?
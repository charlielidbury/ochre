# Universes for Och

## Motivation

Och currently has a single syntactic category — types and terms coincide.
This means `Type`, `Bot`, and iota values are legitimate runtime results,
even though they're only meaningful at the type level. The runtime
(`concEval`) can't distinguish "running a program" from "computing a type."

Adding universes would let us:
1. Reject programs that return types instead of values
2. Ensure `concEval` only runs object-level terms
3. Move toward consistency (Girard's paradox stems from impredicativity)

## PSS's approach (§3.6)

PSS (docs/papers/pss.pdf, p5) adds universes as a lightweight orthogonal
layer. Two universes: `0` (objects) and `1` (types). Variables are tagged
with their universe: `x^0` for object variables, `x^1` for type variables.

The universe judgment `t ∈ U(K)` is:

```
x^K           ∈  U(K)
Top           ∈  U(1)
λx^J ≤ t. u  ∈  U(K)    if u ∈ U(K)
t(u)          ∈  U(K)    if t ∈ U(K)
```

A function is in universe K if its body is in K — regardless of the
argument's universe. This means a function in any universe can quantify
over any other universe, supporting both parametric polymorphism (objects
depending on types) and dependent types (types depending on objects).

Well-formedness for application adds a universe check:

```
Γ ⊢ t ≤_wf (λx^K ≤ s. Top),  u ≤_wf s,  u ∈ U(K)
─────────────────────────────────────────────────────
                    Γ ⊢ t(u) wf
```

## What this would look like in Och

### Syntax change

Tag binders with a universe level:

```
e, τ ::= ...
       | λ(x^K : τ). e      // K ∈ {0, 1}
       | ι(self^K : τ). e
       | fix(self^K : τ). e
```

Or simpler: infer universes rather than annotating. Since `Type ∈ U(1)`
and `3 ∈ U(0)`, the universe of a term is determined by its structure.

### Key classifications

```
U(0): zero_, one_, unit_, true_, false_, pair_ ...  (runtime values)
U(1): Nat_, Type, Bot, Unit_, Bool, Pair ...        (types)
```

Lambdas inherit their body's universe:
- `λx:Nat_. x` ∈ U(0) (returns an object)
- `λx:Type. x` ∈ U(1) (returns a type)

### Impact on concEval

`concEval` would only accept `U(0)` terms. Attempting to evaluate a
`U(1)` term (like `Type` or `Nat_`) would be a universe error, not a
stuck computation.

### Impact on subtyping

None — PSS notes "the presence or absence of universes does not affect
any of the results." Subtyping crosses universe boundaries. The universe
check is a separate well-formedness pass.

### Impact on soundness

The soundness theorem strengthens from:
- "synth-accepted programs don't get stuck"

to:
- "synth-accepted U(0) programs produce U(0) values"

The existing `Subtype'` relation and all its proofs are unchanged.

## Consistency considerations

With a single universe (Och's current `Type : Type`), Girard's paradox
is still admissible. Two universes are the first step toward consistency
but don't automatically give it — PSS §4.2 notes that impredicativity
(a Π-type whose variable quantifies over the Π-type itself) is the real
source, not universe confusion.

Full consistency would require either:
- Predicative universes (like Agda's `Set₀ : Set₁ : Set₂ : ...`)
- Restricted impredicativity (like Coq's `Prop` being impredicative but `Set` being predicative)

Both are substantial changes beyond the scope of a universe annotation.

## Implementation effort

Moderate. The universe check is a separate judgment that can be
implemented as a standalone pass after `synthCore`, reusing the existing
AST. No changes to `evalSubst`, `subCheckSubst`, or `Subtype'`.

Steps:
1. Add universe inference (walk the term, classify each subterm)
2. Add universe checking to `synthCore`'s app arm
3. Gate `concEval` on `U(0)`
4. Update soundness theorem statement

The proofs are unaffected — universes are orthogonal to subtyping.

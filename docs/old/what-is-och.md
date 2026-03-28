# What is Och?

Och is a **minimal research calculus** designed to isolate and test the core semantic idea behind Ochre, free from the noise of mutation and ownership.

For more info on Ochre, see ./what-is-ochre.md

## Purpose

When attempting to prove soundness of Ochre's type system, key properties like **monotonicity** (more approximate typing context => more approximate conclusion) were extremely difficult to work with. Mutation and ownership introduced so much proof complexity that it was impossible to tell whether the core idea was broken or just obscured.

Och strips all of that away. It is not a standalone language and is not meant to be useful for writing software. It is a **proof instrument** -- the smallest calculus that still faithfully tests whether the foundational idea works.

## The Core Idea Being Tested

> Can a language where terms are their own most precise types support a sound, monotone notion of typing via abstract interpretation?

Concretely:

- **Types are sets of values.** The most precise type of a term is the term itself.
- **Typing is abstract interpretation.** Instead of syntax-directed typing rules, you abstractly execute the program over sets of values.
- **Subtyping is set inclusion.**
- **Precision by default.** Type annotations only *lose* information (widen); without them, the system tracks maximal precision.

## What Och Includes

Och is a pure, read-only, higher-order lambda calculus with:

- Variables
- Lambda abstraction / application
- Top (the maximally approximate type -- represents "no information")
- Type ascription (the mechanism for deliberately losing precision)
- A subtyping preorder
- Two semantics: **concrete evaluation** (ordinary execution) and **abstract evaluation** (computes an approximating type)

## What Och Deliberately Excludes

- Mutation and assignment
- Ownership and borrowing
- Pairs and dependent pairs
- Atoms and unions (initially)
- Match / pattern matching (initially)
- Write judgments
- Compile-time vs runtime distinction
- Code generation

These are excluded not because they are unimportant to Ochre, but because each adds complexity that could mask whether the core idea itself is sound.

## Key Properties To Prove

1. **Monotonicity**: Widening the input environment widens the abstract result.
2. **Soundness**: If concrete evaluation gives value `v` and abstract evaluation gives type `t`, then `v` is in `t`.
3. **Substitution lemmas** and other standard metatheoretic properties.

## The Known Bug That Motivated Och

Ochre's Proposition 5.2.9 (Expression Subtyping Preservation) was shown to be false:

```
Not = (X: 'true | 'false) -> match X { 'true => 'false, 'false => 'true };
F = (B: 'true | 'false) -> Not B: B;   // holds
B = 'true; Not B: B;                    // does not hold
```

Narrowing the environment from `B: 'true | 'false` to `B: 'true` broke the subtyping judgment. This demonstrated that **precision-sensitive type-level computation can be anti-monotone** -- narrowing the context can invalidate previously valid relations rather than refining them. This is a problem in the core semantic idea, not just in the mutation/ownership layer, which is exactly what Och is designed to diagnose.

## Planned Staging

Features are to be re-introduced incrementally, each stage answering a distinct research question:

| Stage | Adds | Tests |
|-------|------|-------|
| Och_0 | Pure lambda core + top + ascription + subtyping | Is the base idea sound and monotone at all? |
| Och_1 | Unions | Do joins and precision behave well? |
| Och_2 | Atoms | Singleton precision, case distinctions |
| Och_3 | Match / flow sensitivity | Branch refinement, environment narrowing |
| Och_4 | Dependent pairs | "Left determines right" dependency |
| Ochr  | Ownership / immutable borrowing | Can the core coexist with resource tracking? |
| Ochre | Mutable references | The full system |

## Academic Positioning

In PL terminology, Och is best described as:

> A proof-oriented core calculus for semantic typing by abstract interpretation. It combines a pure higher-order language with semantic subtyping and precision-sensitive typing, in order to isolate metatheoretic properties such as soundness and monotonicity before reintroducing ownership and mutation.

Closest prior art families: semantic subtyping (Castagna/Frisch), occurrence typing (Typed Scheme), refinement/liquid types, Dependent ML, and abstracting definitional interpreters (Van Horn/Might, Darais et al.).

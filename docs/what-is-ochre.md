# What is Ochre?

Ochre is a work-in-progress **systems theorem prover** -- roughly **Rust + Dependent Types**.

## Core Idea

Instead of runtime code and types being expressed in different languages, Ochre expresses both in the same language. Types are a special case of programs where the program has "ambiguity" -- i.e. a type is a set of possible values, and the most precise type of a term is the term itself.

This makes **typing equivalent to abstract interpretation**: rather than applying syntax-directed typing rules, Ochre abstractly executes a program over sets of values to determine its type. Type annotations exist only to *lose* information (widen), not to add it.

## Why?

The goal is to allow programmers to write in a language very similar to Rust while having access to the power of a dependent type system. This would enable:

1. **Proving properties currently assumed** -- e.g. removing the need for `unsafe` in `RefCell` and `Vec`.
2. **Proving properties currently ignored by compilers** -- e.g. a financial exchange never creates nor destroys money, or a compiler respects its formal specification.

Existing verified-programming options are either pure functional (Lean, Agda -- poor ergonomics and performance) or multi-language stacks (Low\*/F\* -- require unnatural coding patterns). Ochre aims to be a single language that is natural to write and powerful enough to verify.

## How?

The key mechanisms are:

1. **Rust-style ownership + borrow checking** controls mutation, ensuring exclusive access when mutating.
2. **Strong mutation** updates the static type of a variable after assignment (e.g. after `x = 5`, the type of `x` becomes the singleton `5`, not just `Nat`).
3. **Structural subtyping** with precise unions preserves fine-grained type information.
4. **Unified computation model** -- type-level and runtime computation use nearly the same model, so the type level can capture almost any desired runtime property.
5. **Functions as types** -- the type of a function is itself a function (an approximation of the function being typed). Non-constant type functions yield dependent function types.

## Why It Should Be Possible

Aeneas demonstrated that Rust programs can be translated to F\* (a pure functional dependently typed language), showing Rust has the right "shape" for dependent reasoning. In principle, a Rust-plus-annotations surface language could support both performance and verification. Ochre collapses that multi-language pipeline into one native language and type system.

## Current Status

Ochre was formally specified and partially implemented as a masters thesis. However:

- The formal specification is **unsound** (a counterexample was found where subtyping preservation under environment narrowing fails).
- The implementation is **partial** and does not generate code.
- Major rework is needed before it can verify useful software.

The unsoundness and the difficulty of diagnosing it in the full system (with mutation, ownership, and dependent types all interacting) motivated the creation of **Och** as a simpler research vehicle to isolate and fix the core semantic idea.

## Relationship to Och and Ochr

The research programme is staged:

- **Och**: Strip away mutation and ownership. Test whether the core semantic idea (terms-as-types, typing-as-abstract-interpretation) is sound and monotone.
- **Ochr**: Add ownership / immutable borrowing. Test whether the core can coexist with linear resource tracking.
- **Ochre**: Reintroduce mutable references. The full system.

Each stage answers a different research question, and a failure at any stage localises the problem.

#import "../style.typ": *

Ochr is a dependent type theory in the style of Lean's kernel @theory-of-lean, extended with places, mutable borrows and sequencing. This section gives its syntax and the runtime structures of its evaluator. We keep the core small: the only inductive types are natural numbers and the unit type, plus pairs and the propositional connectives needed by equality. @sec-discussion discusses what generalises directly and what does not.

== Syntax

#figure(kind: image, supplement: [Figure],
  ```
  terms  t, u, A, B ::= x | Prop | Typeᵢ
                      | Π(x₁:A₁ … xₙ:Aₙ). B                  dependent function type
                      | fix f (x₁:A₁ … xₙ:Aₙ) : B by xⱼ := t  function (recursive on xⱼ, or not at all)
                      | t(u₁, …, uₙ)                          saturated call
                      | Nat | Z | S t | Unit | () | A × B | (t, u) | t.1 | t.2
                      | Eq A t u | refl | J(A, a, b, P, h, t) | ⊤ | P ∧ Q | ⟨h, k⟩
                      | &A                                     borrow type
                      | p | &p | p := t | let x = t; u | t; u
                      | match p { Z => t | S y => u }
                      | Id A t u                               equality of computations
  places p ::= x | *p | p.1
  ```,
  caption: [Syntax of Ochr. `Eq`, `⊤` and `∧` live in `Prop`. A `fix` without `by` is an ordinary λ.],
) <fig-syntax>

@fig-syntax gives the syntax. Types and terms share one grammar, as in any pure type system. Functions are n-ary and calls are saturated: a partial application would be a closure capturing its arguments, and a closure capturing a borrow is outside the core. A recursive function names the parameter it recurses on.

The imperative fragment is small. A _place_ `p` is a variable, a dereference `*p`, or the predecessor field `p.1` of a number. A place used as a term reads it; `&p` borrows it; `p := t` assigns it; `let x = t; u` introduces a new place `x`. The pattern variable of a `match` is a _sub-place_: in `match p { S y => u }`, `y` stands for `p.1`, and nothing is copied.

`&A` is the type of a mutable borrow of an `A`. In the core, borrow types occur only as the types of variables, parameters and results, never inside another type: there are no borrows stored in data structures and no borrows of borrows. There are no shared borrows and no loops. Recursion is structural.

The propositional fragment is Lean's: `Prop` is an impredicative universe with definitional proof irrelevance, erased at runtime, and `Eq` is its equality. `Id A t u` compares two _computations_ `t` and `u` of type `A`; @sec-obs shows that it is not a new primitive.

== Values and environments

#figure(kind: image, supplement: [Figure],
  ```
  values        v, w ::= Z | S v | () | (v, w) | ⋆ | closures | types
                       | borrow_ℓ v | loan_ℓ | ⊥ | n
  neutrals      n    ::= σ | ⌈t⌉
  environments  Ω    ::= a stack of frames of bindings  x : A ↦ v
  ```,
  caption: [Runtime structures.],
) <fig-values>

The evaluator manipulates the values of @fig-values. Following the low-level borrow calculus of Aeneas @aeneas, a borrow carries the borrowed content with it: `borrow_ℓ v` is a borrow, identified by `ℓ`, whose current content is `v`, and `loan_ℓ` is the placeholder left at the place it was taken from. When the borrow ends, its content is put back where the loan is. We depart from Aeneas in one respect: *a loan is a variable bound by its borrow*. It may occur anywhere inside a value, including inside a sealed program, and inside sealed programs it may occur more than once; ending the borrow substitutes its content for every occurrence. `⊥` marks a place whose content has been moved out, and `⋆` is the value of a proof.

Neutral values are stuck computations. An _abstract value_ `σ` is an unknown value of a known type, playing the role of a free variable in Lean's kernel: the checker introduces one for every parameter of a definition it checks, and nowhere else. A _sealed program_ `⌈t⌉` is a closed program whose run is stuck on an abstract value. Sealed programs are produced by closing off stuck calls (@sec-eval) and are the only neutral form besides abstract values. A value is _borrow-free_ if it contains no borrow and no live loan.

An environment Ω is a stack of frames, one per active call, each binding variables to values. `content(Ω, p)` follows a place through variables, borrows (`*p` looks inside `borrow_ℓ v` at `v`) and successors (`p.1` looks inside `S v` at `v`). We write `Ω[p ↦ v]` for the environment with the content of `p` replaced.

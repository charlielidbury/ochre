#import "../style.typ": *

Ochr is a dependent type theory in the style of Lean's kernel @theory-of-lean, extended with places, mutable borrows and sequencing. This section gives its syntax and the runtime structures of its evaluator. We present the rules for natural numbers and the unit type, plus pairs and the propositional connectives needed by equality; user-declared inductive types with several constructors and fields change only the grammar of patterns and places, and @sec-appendix gives the general definition.

== Syntax

#figure(kind: image, supplement: [Figure],
  block(width: 100%, inset: (y: 4pt), grammar(
    ($t, u, A, B$, $x | ty("Prop") | ty("Type")_i$, [variables, universes]),
    ([], $Pi(x_1 : A_1 ... x_n : A_n). B | kw("fix") f (x_1 : A_1 ... x_n : A_n) : B space kw("by") x_j := t | t(u_1, ..., u_n)$, [functions, calls]),
    ([], $ty("Nat") | ty("Z") | ty("S") t | ty("Unit") | () | A times B | (t, u) | t.1 | t.2$, [data]),
    ([], $ty("Eq") A space t space u | kw("refl") | ty("J")(A, a, b, P, h, t) | top | P and Q | chevron.l h, k chevron.r$, [propositions]),
    ([], $\&A | p | \&p | p := t | kw("let") x = t; u | kw("let") x : A = t; u | t; u$, [places and borrows]),
    ([], $kw("match") p space {ty("Z") => t | ty("S") y => u}$, [case analysis]),
    ([], $ty("Id") A space t space u$, [computation equality]),
    ($p$, $x | *p | p.1$, [places]),
  )),
  caption: [Syntax of Ochr. $ty("Eq")$, $top$ and $and$ live in $ty("Prop")$. A $kw("fix")$ without $kw("by")$ is an ordinary $lambda$.],
) <fig-syntax>

@fig-syntax gives the syntax. Types and terms share one grammar, as in any pure type system. Functions are n-ary and calls are saturated: a partial application would be a closure capturing its arguments, and a closure capturing a borrow is outside the core. A recursive function names the parameter it recurses on.

The imperative fragment is small. A _place_ `p` is a variable, a dereference `*p`, or the predecessor field `p.1` of a number. A place used as a term reads it; `&p` borrows it; `p := t` assigns it; `let x = t; u` introduces a new place `x`. The pattern variable of a `match` is a _sub-place_: in `match p { S y => u }`, `y` stands for `p.1`, and nothing is copied.

`&A` is the type of a mutable borrow of an `A`. In the core, borrow types occur only as the types of variables, parameters and results, never inside another type: there are no borrows stored in data structures and no borrows of borrows. There are no shared borrows and no loops. Recursion is structural.

The propositional fragment is Lean's: `Prop` is an impredicative universe with definitional proof irrelevance, erased at runtime, and `Eq` is its equality. `Id A t u` compares two _computations_ `t` and `u` of type `A`; @sec-obs shows that it is not a new primitive.

== Values and environments

#figure(kind: image, supplement: [Figure],
  block(width: 100%, inset: (y: 4pt), grammar(
    ($v, w$, $ty("Z") | ty("S") v | () | (v, w) | star | "closures" | "types"$, [data, proofs, closures, types]),
    ([], $"borrow"_ell v | "loan"_ell | bot$, [borrows, loans, moved-out]),
    ([], $n$, [neutrals]),
    ($n$, $sigma | seal(t)$, [abstract values, sealed programs]),
    ($Omega$, $dot.c | Omega, x : A |-> v | Omega | Omega'$, [bindings, grouped in frames]),
  )),
  caption: [Runtime structures.],
) <fig-values>

The evaluator manipulates the values of @fig-values. Following the low-level borrow calculus of Aeneas @aeneas, a borrow carries the borrowed content with it: `borrow_ℓ v` is a borrow, identified by `ℓ`, whose current content is `v`, and `loan_ℓ` is the placeholder left at the place it was taken from. When the borrow ends, its content is put back where the loan is. We depart from Aeneas in one respect: *a loan is a variable bound by its borrow*. It may occur anywhere inside a value, including inside a sealed program, and inside sealed programs it may occur more than once; ending the borrow substitutes its content for every occurrence. `⊥` marks a place whose content has been moved out, and `⋆` is the value of a proof.

Neutral values are stuck computations. An _abstract value_ `σ` is an unknown value of a known type, playing the role of a free variable in Lean's kernel: the checker introduces one for every parameter of a definition it checks, and nowhere else. A _sealed program_ `⌈t⌉` is a closed program whose run is stuck on an abstract value. Sealed programs are produced by closing off stuck calls (@sec-eval) and are the only neutral form besides abstract values. A value is _borrow-free_ if it contains no borrow and no live loan.

An environment Ω is a stack of frames, one per active call, each binding variables to values. `content(Ω, p)` follows a place through variables, borrows (`*p` looks inside `borrow_ℓ v` at `v`) and successors (`p.1` looks inside `S v` at `v`). We write `Ω[p ↦ v]` for the environment with the content of `p` replaced.

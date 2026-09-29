#import "../style.typ": *

Ochr is a dependent type theory in the style of Lean's kernel @theory-of-lean, extended with places, mutable borrows and sequencing. This section gives its syntax and the runtime structures of its evaluator. Data and the logical connectives are introduced alike, by inductive declarations; the rules in the body are illustrated on natural numbers, and @sec-appendix gives the general definition.

== Syntax

#figure(kind: image, supplement: [Figure], placement: auto,
  block(width: 100%, inset: (y: 4pt), {
    grammar(
      ($t, u, A, B$, $x | ty("Prop") | ty("Type")_i$, [variables, universes]),
      ([], $Pi(x_1 : A_1 ... x_n : A_n). B | kw("fix") f (x_1 : A_1 ... x_n : A_n) : B space kw("by") x_j := t | t(u_1, ..., u_n)$, [functions, calls]),
      ([], $ty("D")(a_1, ..., a_m) | ty("C")(t_1, ..., t_k)$, [inductive types, constructors]),
      ([], $ty("Eq") A space t space u | ty("J")(A, a, b, P, h, t)$, [equality]),
      ([], $\&A | p | \&p | p := t | kw("let") x = t; u | kw("let") x : A = t; u | t; u$, [places and borrows]),
      ([], $kw("match") p space {ty("C")_1 (overline(y)_1) => t_1, ..., ty("C")_n (overline(y)_n) => t_n} quad (n >= 0)$, [case analysis]),
      ([], $ty("Id") A space t space u$, [computation equality]),
      ($p$, $x | *p | p.g$, [places ($g$ a field)]),
      ($d$, $kw("inductive") ty("D") (x_1 : A_1 ... x_m : A_m) : s := ty("C")_1 (overline(g_1 : B_1)) | ... | ty("C")_n (overline(g_n : B_n))$, [declarations]),
    )
    v(6pt)
    align(center, grid(columns: 2, column-gutter: 2.4em, row-gutter: 6pt, align: left,
      $kw("inductive") ty("Nat") : ty("Type")_0 := ty("Z") | ty("S")("pred" : ty("Nat"))$,
      $kw("inductive") ty("Unit") : ty("Type")_0 := ty("Tt")$,
      $kw("inductive") ty("False") : ty("Prop")$,
      $kw("inductive") ty("True") : ty("Prop") := ty("I")$,
      grid.cell(colspan: 2, align: center, $kw("inductive") ty("Pair") (A : ty("Type")_0) (B : ty("Type")_0) : ty("Type")_0 := ty("Mk")("fst" : A, "snd" : B)$),
      grid.cell(colspan: 2, align: center, $kw("inductive") ty("And") (P : ty("Prop")) (Q : ty("Prop")) : ty("Prop") := ty("Intro")(l : P, r : Q)$),
    ))
  }),
  caption: [Syntax of Ochr, and the library declarations. A declaration has sort $s in {ty("Type")_0, ty("Prop")}$ and $n >= 0$ constructors. $ty("S") t$ abbreviates $ty("S")(t)$; $()$, $A times B$, $(a, b)$, $top$, $kw("refl")$, $P and Q$ and $chevron.l h, k chevron.r$ are notation for $ty("Tt")$, $ty("Pair")(A, B)$, $ty("Mk")(a, b)$, $ty("True")$, $ty("I")$, $ty("And")(P, Q)$ and $ty("Intro")(h, k)$, and $p.1$, $p.2$ name a place's first and second fields. A $kw("fix")$ without $kw("by")$ is an ordinary $lambda$.],
) <fig-syntax>

@fig-syntax gives the syntax. Types and terms share one grammar, as in any pure type system. Functions are n-ary and calls are saturated: a partial application would be a closure capturing its arguments, and a closure capturing a borrow is outside the core (@sec-eval-closures). A recursive function names the parameter it recurses on.

*Inductive definitions.* Every type of data and every logical connective is an inductive declaration: a name, uniform parameters, a sort (`Type₀` for data, `Prop` for propositions) and any number of constructors with named fields. Natural numbers, the unit type and pairs are declarations (the checker builds `Nat` and `Unit` in, with the same behaviour), and so are `False`, the proposition with no constructors, `True`, with one constructor and no fields, and `And(P, Q)`, with one constructor whose two fields are proofs of `P` and of `Q`. `⊤`, `P ∧ Q`, `⟨h, k⟩` and `refl` are notation for them. Their eliminations are matches: ex falso is the match with no arms, `match h {}`, and a proof of `P ∧ Q` is taken apart by `match h { Intro(l, r) => … }`. Constructors also take their declaration's parameters as leading arguments, `Intro(P, Q; h, k)`, which we omit when they can be inferred. Fields are first-order: they may mention the type being declared, other declared types and the parameters, but not `Π` or `&`, which is strict positivity in its simplest form.

`Eq` is the one primitive proposition. It is not an inductive family, for two reasons: it computes by the structure of the values it compares, as in observational type theory (@sec-obs), and the core has no indexed families.

The imperative fragment is small. A _place_ `p` is a variable, a dereference `*p`, or a field `p.g` of a constructor value, such as the predecessor field `p.1` of a number. A place used as a term reads it; `&p` borrows it; `p := t` assigns it; `let x = t; u` introduces a new place `x`. The pattern variables of a `match` are _sub-places_: in `match p { S y => u }`, `y` stands for `p.1`, and nothing is copied.

`&A` is the type of a mutable borrow of an `A`, and `A` must be data: an inductive type in `Type₀`, never a universe, a Π-type or a proposition. `&` occurs only at the top of a type as written, as the type of a variable, parameter or result; never inside another type, and never as the result of computing one. So there are no borrows stored in data structures and no borrows of borrows. Shared borrows, loops and `'static` borrows are absent (@fig-scope), and recursion is structural.

The propositional fragment is Lean's: `Prop` is an impredicative universe with definitional proof irrelevance, erased at runtime, and `Eq` is its equality. `Id A t u` compares two _computations_ `t` and `u` of type `A`; it is a derived proposition whose computation rule is observation (@sec-obs).

== Values and environments

#figure(kind: image, supplement: [Figure],
  block(width: 100%, inset: (y: 4pt), grammar(
    ($v, w$, $ty("C")(v_1, ..., v_k) | star | f | chevron.l overline(kappa) tack.r kw("fix") f (overline(x) : overline(A)) : B dots := t chevron.r | "types"$, [data, proofs, functions, closures, types]),
    ([], $"borrow"_ell v | "loan"_ell | bot$, [borrows, loans, moved-out]),
    ([], $n$, [neutrals]),
    ($n$, $sigma | seal(t)$, [abstract values, sealed programs]),
    ($Omega$, $dot.c | Omega, x : A |-> v | Omega | Omega'$, [bindings, grouped in frames]),
  )),
  caption: [Runtime structures. A closure is code with its captured values $overline(kappa)$, and a Π-type is one too, $chevron.l overline(kappa) tack.r Pi(overline(x) : overline(A)). B chevron.r$ (@sec-eval-closures).],
) <fig-values>

The evaluator manipulates the values of @fig-values. Following the low-level borrow calculus of Aeneas @aeneas, a borrow carries the borrowed content with it: `borrow_ℓ v` is a borrow, identified by `ℓ`, whose current content is `v`, and `loan_ℓ` is the placeholder left at the place it was taken from. When the borrow ends, its content is put back where the loan is. We depart from Aeneas in one respect: *a loan is a variable bound by its borrow*. It may occur anywhere inside a value, including inside a sealed program, and inside sealed programs it may occur more than once; ending the borrow substitutes its content for every occurrence. `⊥` marks a place whose content has been moved out, and `⋆` is the value of a proof.

Neutral values are stuck computations. An _abstract value_ `σ` is an unknown value of a known type, playing the role of a free variable in Lean's kernel: the checker introduces one for each parameter of a definition it checks, and for each field that a case split or a generalisation exposes; concrete evaluation never introduces one. A _sealed program_ `⌈t⌉` is a closed program whose run is stuck on an abstract value. Sealed programs are produced by closing off stuck calls (@sec-eval) and are the only neutral form besides abstract values. A value is _borrow-free_ if it contains no borrow and no live loan.

An environment Ω is a stack of frames, one per active call, each binding variables to values. `content(Ω, p)` follows a place through variables, borrows (`*p` looks inside `borrow_ℓ v` at `v`) and fields (`p.1` looks inside `S v` at `v`). We write `Ω[p ↦ v]` for the environment with the content of `p` replaced.

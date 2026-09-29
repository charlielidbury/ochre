#import "../style.typ": *

Typing is the machine run on abstract inputs, with case splitting where the checked program itself inspects an abstract value. The judgement `Ω ⊢ t ⇓ v : A ⊣ Ω'` says that from `Ω` the term `t` runs to the value `v` of type `A`, leaving `Ω'`. It returns the value, not just the type, because later types may depend on it: after `let z = (let y = &x; *y := 2; x)`, the type `Id Nat z 2` holds by `refl` only because the checker knows that `z` is `2`. The rules for the basic forms are the evident ones, each the corresponding machine rule annotated with types, and we omit them. @fig-typing gives the rules that are particular to Ochr.

#figure(kind: image, supplement: [Figure],
  block(width: 100%)[
    *[Call-type]* At the point where the arguments of `f(ā)` have been evaluated, with `f : Π(x̄ : Ā). B`: push a frame binding each `xᵢ` to `aᵢ`'s value, evaluate `B` there on a private copy of the environment, and pop. The result is the type of the call. Each `aᵢ` must have type `Aᵢ`, evaluated with the earlier parameters bound.

    *[Def]* `fix f (x̄ : Ā) : B by xⱼ := b` is checked at its _generic call_: from an environment with a fresh owned place `cᵢ ↦ σᵢ` for each borrow parameter `xᵢ : &Tᵢ`, the call `f(ā)` with `aᵢ = &cᵢ` for borrow parameters, `aᵢ = ⋆` for proof parameters, and `aᵢ = σᵢ` otherwise; parameter types are evaluated left to right, with the earlier parameters bound, and stored with their bindings. The goal is the [Call-type] of this call. The body runs in the pushed frame, which is then dropped; its result's type must be convertible to the goal, as refined by the splits on the way.

    *[Split]* When the checked program matches on a place whose content has an abstract head `σ`, each arm is checked with the refinement `σ := Z`, respectively `σ := S σ'` for fresh `σ'`, applied to the environment, the goal and every stored type. If the head is a sealed program, every occurrence of it is first replaced by a fresh `σ`. If the match is followed by more code, that code is checked once, from the state in which the match has been closed off as a stuck block. A match on a proof is decided by the proof's type instead, with no refinement (@sec-typing-prop).

    *[Rec]* In the body of `fix f … by xⱼ`, including inside nested functions and block arms, `f` occurs only as the head of a call, and each recursive call passes in position `j` a value, or a borrow of a value, that is a strict subterm of `xⱼ`'s entry value `σⱼ` as refined so far.
  ],
  caption: [The typing rules particular to Ochr.],
) <fig-typing>

== One rule for goals and induction hypotheses

A definition is checked by running it at its most general call [Def]. For `AddMZero(x : &Nat)` that is `AddMZero(&c)` from `{ c ↦ σ }`: the parameter becomes a borrow of a fresh owned place, which stands for whatever the real caller lends. The goal is then computed by [Call-type], the rule that types every call.

The same rule types the recursive call in the successor case, at a different environment. There the argument `&p` borrows the predecessor field of `c`'s content, so evaluating the callee's statement at the call site observes `c` through the successor that surrounds the field. This is how the induction hypothesis arrives already wrapped in `S`. The generic call and the recursive call are two instances of one rule, which is why the goal and the hypothesis meet without a congruence step. That the callee's statement, proved at its generic call, remains true at every call site rests on the frame property (@sec-meta): a call affects only what it is passed, so the caller's observation is the callee's, placed in a context.

== Types are formed once

A type is evaluated once, when it is formed, on a private copy of the environment, and becomes a closed statement about values. Later mutation cannot change it. This includes the codomain of a Π-type, which is a closure over the values of the variables it mentions; only its parameters are bound later, at each call. The goal of a definition is formed at its generic call, before the body runs, so a body that mutates its argument and then proves something about the new contents does not prove the goal: `λ(x : &Nat). (*x := 5; refl)` does not have type `Π(x : &Nat). Id Nat (*x) 5`.

== Case splitting and joins

A `match` in the checked program on an abstract value cannot pick an arm, so each arm is checked with the abstract value refined [Split]. What follows the match is checked once, from a state in which the match itself has been closed off as a stuck block. The closed-off match is precise: its sealed programs contain the match, and they reduce as soon as a later split decides it. There is no join of environments and no loss of information, and a borrow whose origin depends on the branch is handled like any other returned borrow. `AddToOne` of @sec-overview is accepted, and so is any function whose body is split into a helper at a match: a match and a call to a function containing it are treated alike. Errors in the code after a match are reported once, at the line where they occur, not once per arm.

== Erased terms leave no trace

Types and proofs are erased at runtime. The machine mirrors this exactly: it evaluates an erased term on a private copy of the environment, argument evaluation included, and discards the copy. A term is erased when it stands in a type position, when its declared type has sort `Prop`, or when it is a call to a function whose codomain term is a sort or has declared sort `Prop`; the decision never looks at a normal form. Two things follow. A formed type is a closed statement about values, as described above. And a proof can have no effect on the program around it: it may mutate places it creates itself, on its own copy. Running a proof and skipping it are therefore indistinguishable, and the machine skips proofs, which is what the compiled program does too.

Erased terms are also checked not to write, borrow or move a place that outlives them, except by handing it to another erased call. With the private copy this is redundant for a correctly classified term, and it is there as a partial fail-safe: if the two evaluation paths disagreed about whether an inline term is erased, the path that erases it would reject it rather than silently discard its effects. For calls and stuck blocks the fail-safe does not reach inside the callee's body, and soundness rests on the classification being syntactic (@sec-impl). This is one principle, not a restriction on programs. `AddMZero`'s successor case borrows the field `p` to pass it to the induction hypothesis; the borrow happens on the private copy, and the real environment is untouched. Nothing in a program is marked pure, and any program may appear in a statement.

== Proofs are matched by their type <sec-typing-prop>

`False`, `True` and `And` are inductive declarations, and a proof of one of them is matched like any other constructor value, with one difference: a proof cannot be inspected. Its value is `⋆`, whether it is a parameter (bound to `⋆` at the generic call) or the result of an erased call, so there is no constructor to select an arm and no abstract value to refine. A match on a place whose type is an inductive `D(ā)` of sort `Prop` is therefore decided by that type alone, never by the content. `False` has no constructors, so `match h {}` has no arms, and it is well typed at any result type: this is ex falso. `True` and `And` have one constructor, so the match has one arm, whose fields are places holding `⋆`, of the field types (`l : P` and `r : Q` for `h : And(P, Q)`). A declaration with several constructors, such as a user's `Or`, gets one arm per constructor, each checked with its proof fields holding `⋆` and its data fields, if any, holding fresh abstract values; by the rule below every arm is then a proof, so the match is erased and never runs. The machine, which has no types, recognises a match on a proof from the constructors its arms name, which is a fact about declarations.

This keeps the two evaluation paths in agreement. The decision depends only on the scrutinee's type being an inductive declared in `Prop`, and refinement never changes that: substituting for abstract values can change a type's parameters, never its head. A type that is still a neutral, such as `Le(σ, σ')` before a split, does not license a match on a proof at all, so a match accepted at the generic call is decided the same way at every instance. A match with no arms is unreachable when run, and is erased, with value `⋆` at any type: vacuously, every one of its arms is a proof.

*Subsingleton elimination.* A match on a proof may produce data or a type only if the inductive has no constructors, or one constructor whose fields are all proofs. `False`, `True` and `And` qualify. This is Lean's rule @theory-of-lean. With `inductive Or (P Q : Prop) : Prop := Inl(p : P) | Inr(q : Q)`, the function `IsL(h : Or(True, True)) : Bool := match h { Inl(p) => true, Inr(q) => false }` would mean `true` on `Inl(refl)` and `false` on `Inr(refl)`, two proofs that proof irrelevance identifies. In Ochr this alone gives no closed proof of `False`: every proof is `⋆`, so no match can see which constructor built one, and the closed proof appears only if proofs also keep their constructors. Subsingleton elimination is needed all the same. Without it `IsL` has no meaning in the set model, where `Eq Bool (IsL(Inl(refl))) (IsL(Inr(refl)))`, provable by `refl`, would read `Eq Bool true false`; `IsL(Inl(refl))` would be a closed `Bool` that is stuck for ever, against canonicity; and a match with two constructors would have no arm to take unless every arm is a proof. For the inductives that qualify there is nothing to tell apart: the type determines the arm, and the fields are `⋆`.

== Why each condition is there <sec-why>

Each side condition was added in response to a concrete counterexample: a closed proof of false, an accepted program that goes wrong when run, or a definition with no set-theoretic meaning. All but subsingleton elimination, which is Lean's, were found while designing the calculus. Each counterexample is a regression test in the implementation, and the ledger records what switching each condition off lets back in (@sec-impl). Most of them guard one invariant: a statement is evaluated once through closing off, at a definition's generic call, and again directly at each instance, and [Call-type] and [Split] equate the two, so every decision the two paths must agree on is made from syntax (@lem-stable).

#figure(kind: image, supplement: [Figure], placement: auto,
  block(breakable: false, { set text(size: 8.5pt); table(columns: (32%, 68%), stroke: none, inset: (x: 4pt, y: 3pt), align: (left, left),
    table.hline(stroke: 0.5pt),
    [*Condition*], [*What goes wrong without it*],
    table.hline(stroke: 0.4pt),
    [Π-types capture values], [`h : Π(_ : Unit). Id Nat x Z` proved when `x` was `Z` is re-read after `x := S x`, proving `Id Nat (S Z) Z`.],
    [Recursion on entry values; `f` only as a call head; no `f` without `by`], [`*x := S *x; match *x { S p => f(&p) }` recurses on the original value; passing `f` to a helper or calling it in a `by`-less body avoids the check; each proves `False`.],
    [Erased terms run on a private copy, and may not affect outside places], [Proof irrelevance identifies `λx. ⋆` with `λx. (*x := 7; ⋆)`; skipping only proof _calls_ lets a closed-off proof block and the same block run inline disagree.],
    [Erasure read from syntax, never from normal forms; universes not cumulative], [A call `W(&c, n) : U(n)` with `U(n) := match n {Z => Prop, …}` runs at the generic `n` but is erased at `n = Z`; the same for a local function whose codomain mentions captured values, and for a type-valued match erased only when closed off.],
    [Functions compared by their observation], [Comparing results alone identifies `λx. (*x := S Z)` with `λx. ()`; comparing borrow-returning functions without writing through the result identifies `λ(x, y). x` with `λ(x, y). y`.],
    [Pattern variables are places], [A stuck block that writes through `p` in `match *x { S p => p := Z }` captures `*x` by copy.],
    [All owners observed], [A borrow returned into one of two arguments leaves its hole in both; observing one proves `Eq Nat 0 1`.],
    [Exclusive access; loan-free closing off; matches end loans in neutral heads], [A live loan copied into a sealed program, or a hole generalised away by a split, lets an accepted program write through an ended borrow.],
    [Generalisations are global; fresh names never reused], [A generalisation made while forming a type is lost with its private copy, and its name is reissued for a different computation.],
    [Borrows only of data, and `&` only at the top of a declared type], [`Π(x : &Type₀)(a : *x). *x : Type₀` makes `Type₀` impredicative, embedding System U⁻; a codomain that computes to `&Nat` is closed off as data at the generic call but returns a live borrow at an instance, and an accepted program reads a moved borrow.],
    [A borrow-returning function type takes a borrow], [A call of `g : Π(n : Nat). &Nat` returns a borrow observed by no owner, so Ochr refutes a type that safe Rust inhabits with a leaked `'static` borrow, and any opaque inhabitant proves `False`.],
    [Strict positivity], [`inductive Bad := Mk(f : Π(x : Bad). False)` gives a closed proof of `False` that is never run.],
    [Subsingleton elimination], [`match h { Inl(p) => true, Inr(q) => false }` on `h : Or(True, True)` has no set-theoretic meaning and leaves `IsL(Inl(refl))` a closed `Bool` stuck for ever; if proofs also kept their constructors, it would prove `False`.],
    table.hline(stroke: 0.5pt),
  )}),
  caption: [The side conditions of Ochr and the counterexamples that forced them.],
) <fig-why>

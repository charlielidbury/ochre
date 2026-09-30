#import "../style.typ": *

Here is an in-place addition on Peano numerals. It walks down the successors of `*x` until it reaches the final `Z` and moves `y` into that spot:

```
AddM(x : &Nat, y : Nat) : Unit by x :=
  match *x { Z => *x := y, S p => AddM(&p, y) }
```

`&Nat` is a mutable borrow in the sense of Rust: a unique, temporary right to read and write a `Nat` owned by someone else. In the successor case the pattern variable `p` names the predecessor field in place, and `&p` reborrows it for the recursive call. Here is a theorem about `AddM`, stated and proved in the same language:

```
AddMZero(x : &Nat) : Id Unit (AddM(x, 0)) () by x :=
  match *x { Z => refl, S p => AddMZero(&p) }
```

The statement says that running `AddM(x, 0)` is indistinguishable from doing nothing: both return `()`, and both leave the number behind `x` as it was. The proof is structural recursion and nothing else. There is no pure model of `AddM`, no refinement relation, no loop invariant, no separation-logic assertion and no translation into another language. The checker accepts the recursive call as a proof of the successor case by running both sides of the equation on a symbolic input and comparing what they leave behind.

This paper is about the type theory that makes that possible.

== The two-language problem <sec-intro-two>

Verified software is usually built in one of two ways. In the first, everything is written in a pure proof assistant such as Lean or Coq, and performance comes from the compiler's ability to turn functional updates into in-place ones where it can prove the old value is dead. In the second, the efficient program is written in an imperative language, and a separate pure specification is related to it by a refinement proof: Verus @verus and Creusot @creusot check Rust against specifications discharged by SMT, VeriFast checks C against separation-logic contracts, and Aeneas @aeneas translates safe Rust into a pure Lean program about which the user then proves theorems.

Both routes keep two artifacts. In the second route this is visible: there is a program and there is a specification, and the proof is about their relationship. In the first route it is hidden but present: the program the proof is about is not the program that runs, and the gap is bridged by an optimisation the programmer cannot state or rely on.

Aeneas comes closest to closing the gap. Its insight is that Rust's ownership discipline makes mutation equivalent to state passing: a function taking `x : &mut T` is a pure function returning, besides its result, a _backward function_ that computes the final value of `*x`. Aeneas performs this translation once, eagerly, for a whole program, and the user proves theorems about the translated Lean code, where the backward functions appear as ordinary definitions. The user therefore works in two languages at once, and must understand how one maps onto the other.

We show that this translation can be performed *inside the type checker, lazily, as definitional equality, and in the source language itself*.

Two lines of work already use one language. Low\* @lowstar writes low-level code in F\* against an explicit memory model and reasons about it with pre- and postconditions, and Cogent @cogent gives in-place code a purely functional semantics through linear types and generates that semantics for proofs. The claim behind Ochr is stronger: in one system where the in-place algorithm itself appears in types and is unfolded by conversion, a development needs no model and no agreement proof, and so, even without automation, is of comparable size to the three pieces of the usual approach, a specification, an implementation and a proof that they agree (@sec-eval-hashmap). This paper presents the calculus that makes such developments possible, and the evidence that it is sound.

== Three ideas

*Observational equality.* The type `Id A t u` compares two computations `t` and `u` of result type `A`, run from the current state. It holds when they return equal values and leave equal contents in every place they may write. `Id` is a derived proposition, with no introduction or elimination rules of its own: at a given environment it computes to a conjunction of ordinary equations between two _observations_, the tuples of result and final contents, and these compute further by the structure of the data, in the manner of observational type theory @ott. The places a computation may write are read off its syntax, so they are an output of the computation like its result. This is the sense in which Ochr has no pure/impure divide: any program may appear in a type, and what it does to its environment is part of what the type talks about.

*Closing off.* Definitional equality in Ochr is normalisation by a deterministic symbolic machine: two terms are equal when the machine sends them to the same normal form. On symbolic inputs the machine gets stuck, and a dependent type theory needs a name, a _neutral term_, for every stuck computation. A stuck pure computation names itself: Lean's `Nat.add n 0` is its own normal form. A stuck effectful call does not, because part of what it produces lives in the places it borrowed. We _close off_ such a call: its result and the final content of each borrowed place are replaced by _sealed programs_, closed source programs that own their state. For `AddM` on an unknown `σ`, the borrowed place receives #seal(`let c = σ; AddM(&c, 0); c`), which is the pure wrapper a programmer would write anyway. When a later case split refines `σ`, the sealed program runs again. Sealed programs play the role of Aeneas's backward functions for one call (@sec-eval), but they are source programs generated on demand, and a returned borrow leaves a hole in them awaiting its final value.

*Induction hypotheses at the call site.* When the checker types the recursive call `AddMZero(&p)`, it evaluates the callee's statement in the caller's environment, where `&p` points into the predecessor field of the caller's number. The statement is about the place the callee borrowed, but it is observed through the caller's owner, successor included, so the induction hypothesis is literally the goal. Relating a callee's statement about _its_ borrowed place to the caller's data is the frame argument that a proof about a state-passing translation makes by hand; here evaluation makes it. Soundness rests on the frame property that Rust's ownership discipline provides: a call can affect only what it is passed.

== Why this is not impossible <sec-intro-why>

Pédrot and Tabareau's fire triangle @fire-triangle shows that a type theory with substitution of arbitrary terms, dependent elimination and observable effects is inconsistent. Their observable effects concern closed terms, and ownership rules them out: a closed Ochr program can mutate only places it created itself, so it behaves like the value it computes. For open terms Ochr keeps dependent elimination and lets only values into types, sealed programs among them, as in their call-by-value analysis (@sec-related). The price is that a statement is evaluated along two paths, once at a definition's generic call, where stuck calls close off, and again directly at each instance, and any decision on which the two paths disagree is a proof of false. Keeping them in agreement is what most of the typing rules are for (@sec-typing-two).

== Contributions

- A core calculus, Ochr, combining mutable borrows with a dependent type theory with inductive definitions and a universe of proof-irrelevant propositions, whose logical connectives are themselves inductive definitions and whose definitional equality unfolds imperative code (@sec-calculus, @sec-eval).
- _Closing off_, which gives every stuck effectful call a neutral form made of sealed source programs, including calls that return borrows (@sec-eval).
- An observational equality between computations, a derived proposition that computes to ordinary equations (@sec-obs).
- The properties Ochr is designed to have, each with its evidence (@sec-meta). Mechanised, for a first-order fragment of an earlier version of the rules (version 1.3, without types, erasure, closures or stuck blocks): the machine preserves well-formedness, a call affects only what it is passed, and sealed programs compute the call's results and backward function. Conjectured, with sketches: consistency in a set-theoretic model in the style of Carneiro's model of Lean, and the agreement of the checker's two evaluation paths. Whether type checking terminates is open.
- An executable checker in Lean 4 that checks every example in the paper, with a regression test for every false proof found while designing the calculus and a ledger of which rule each depends on; and two case studies, a hash map compared with Aeneas's development and an in-place quicksort (@sec-impl).

== Scope <sec-intro-scope>

Ochr is a core calculus, and it covers a small part of Rust (@fig-scope). Its borrow checking is also not modular in the way Rust's is. Checking is by running, so whether a caller checks can depend on its callee's body and on which of its inputs are concrete: a callee that gets stuck leaves every borrowed argument borrowed until its returned borrow ends, while one that runs to completion releases them. A call to an opaque definition, or to a function parameter, is stuck at once and behaves according to its signature alone. Conversion likewise unfolds callees, so extracting a helper function can change which equations hold by `refl` (@sec-typing).

#figure(kind: image, supplement: [Figure], placement: auto,
  block(breakable: false, { set text(size: 8.5pt); set par(justify: false); table(columns: (30%, 70%), stroke: none, inset: (x: 4pt, y: 2.5pt), align: (left, left),
    table.hline(stroke: 0.5pt),
    [*Rust feature*], [*In Ochr*],
    table.hline(stroke: 0.4pt),
    [`&mut`, reborrowing], [Yes, with exclusivity enforced by running the program (@sec-eval).],
    [Returned borrows], [Yes, with one region per call: the hole goes into every borrowed argument, so a call that returns a borrow into its first argument keeps its second borrowed too, where Rust would accept a lifetime on the first alone.],
    [Shared borrows `&T`], [No.],
    [Loops], [No; structural recursion only.],
    [Borrows in data], [No: no `Option<&mut T>`, `iter_mut` or `split_at_mut`, and no pair of borrows as a result.],
    [Two-phase borrows], [No: an argument that reads a place an earlier argument borrows needs a temporary.],
    [Generic `&A`], [No: `A` must be known to be data, so there is no generic `swap` (@sec-discussion).],
    [`'static` borrows], [No: a returned borrow derives from a borrow argument (@sec-discussion).],
    [Moves, `Copy`, `clone`], [Yes: runtime reads of non-copy data move, `clone` copies, and closures follow `Fn` (@sec-eval).],
    [Integers, arrays], [Peano numbers only; arrays as a library, borrowed in parts only through a continuation (@sec-eval-qs).],
    [`unsafe`, interior mutability], [No.],
    table.hline(stroke: 0.5pt),
  )}),
  caption: [The part of Rust that Ochr covers.],
) <fig-scope>

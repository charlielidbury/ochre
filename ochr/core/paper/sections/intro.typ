#import "../style.typ": *

Here is an addition on Peano numerals that allocates nothing. It walks down the successors of `*x` until it reaches the final `Z` and moves `y` into that spot:

```
AddM : Π(x : &Nat) (y : Nat). Unit
AddM x y := match *x { Z => *x := y | S p => AddM &p y }
```

`&Nat` is a mutable borrow in the sense of Rust: a unique, temporary right to read and write a `Nat` owned by someone else. In the successor case the pattern variable `p` names the predecessor field in place, and `&p` reborrows it for the recursive call. Here is a theorem about `AddM`, stated and proved in the same language:

```
AddMZero : Π(x : &Nat). Id Unit (AddM x 0) ()
AddMZero x := match *x { Z => refl | S p => AddMZero &p }
```

The statement says that running `AddM x 0` is indistinguishable from doing nothing: both return `()`, and both leave the number behind `x` as it was. The proof is structural recursion and nothing else. There is no pure model of `AddM`, no refinement relation, no loop invariant, no separation-logic assertion and no translation into another language. The checker accepts the recursive call as a proof of the successor case by running both sides of the equation on a symbolic input and comparing what they leave behind.

This paper is about the type theory that makes that possible.

== The two-language problem

Verified software is usually built in one of two ways. In the first, everything is written in a pure proof assistant such as Lean or Coq, and performance comes from the compiler's ability to turn functional updates into in-place ones where it can prove the old value is dead. In the second, the efficient program is written in an imperative language, and a separate pure specification is related to it by a refinement proof: Verus @verus and Creusot @creusot check Rust against specifications discharged by SMT, VeriFast checks C against separation-logic contracts, and Aeneas @aeneas translates safe Rust into a pure Lean program about which the user then proves theorems.

Both routes keep two artifacts. In the second route this is visible: there is a program and there is a specification, and the proof is about their relationship. In the first route it is hidden but present: the program the proof is about is not the program that runs, and the gap is bridged by an optimisation the programmer cannot state or rely on.

Aeneas comes closest to closing the gap. Its insight is that Rust's ownership discipline makes mutation equivalent to state passing: a function taking `x : &mut T` is a pure function returning, besides its result, a _backward function_ that computes the final value of `*x`. Aeneas performs this translation once, eagerly, for a whole program, and the user proves theorems about the translated Lean code, where the backward functions appear as ordinary definitions. The user therefore works in two languages at once, and must understand how one maps onto the other.

We show that this translation can be performed *inside the type checker, lazily, as definitional equality, and in the source language itself*.

== Three ideas

*Observational equality.* The type `Id A t u` compares two computations `t` and `u` of result type `A`, run from the current state. It holds when they return equal values and leave equal contents in every place they may write. `Id` is not a new primitive with its own introduction and elimination rules. At a given environment it computes to an ordinary propositional equality between two _observations_, the tuples of result and final contents, and that equality computes further by the structure of the data in the manner of observational type theory @ott. The places a computation may write are read off its syntax, so they are an output of the computation like its result. This is the sense in which Ochr has no pure/impure divide: any program may appear in a type, and what it does to its environment is part of what the type talks about.

*Closing off.* Definitional equality in Ochr is normalisation by a deterministic symbolic machine: two terms are equal when the machine sends them to the same normal form. On symbolic inputs the machine gets stuck, and a dependent type theory needs a name, a _neutral term_, for every stuck computation. A stuck pure computation names itself: Lean's `Nat.add n 0` is its own normal form. A stuck effectful call does not, because part of what it produces lives in the places it borrowed. We _close off_ such a call: its result and the final content of each borrowed place are replaced by _sealed programs_, closed source programs that own their state. For `AddM` on an unknown `σ`, the borrowed place receives #seal(`let c = σ; AddM &c 0; c`), which is the pure wrapper a programmer would write anyway. When a later case split refines `σ`, the sealed program runs again. Sealed programs are exactly Aeneas's backward functions, but they are written in the source language and generated on demand, so the programmer never writes or reads a second language. A function that returns a borrow is closed off into a sealed program with a hole awaiting the final value of the returned borrow; this is Aeneas's region abstraction, in the same form.

*The environment does the congruence.* When the checker types the recursive call `AddMZero &p`, it evaluates the callee's statement in the caller's environment, where `&p` points into the predecessor field of the caller's number. The observation therefore sees the successor that surrounds the recursive call, and the induction hypothesis arrives already wrapped in `S`: it is literally the goal. The step `cong S ih` that a pure proof writes by hand has been performed by the borrow structure. Soundness rests on a frame property that Rust's ownership discipline provides: a call can affect only what it is passed.

== Why this is not impossible

Pédrot and Tabareau's fire triangle @fire-triangle shows that a type theory cannot have substitution of arbitrary terms, dependent elimination and observable effects at once without becoming inconsistent. Ochr is call-by-value, keeps dependent elimination, and restricts what may be substituted into a type: a type only ever contains values. A computation mentioned in a type is run on a private copy of the environment, and only its observation, a value, enters the type. Ownership is what makes this restriction cheap. A closed Ochr program can mutate only places it created, so every closed program behaves like a value, and the observation of an open program is a value of a known shape.

== Contributions

- A core calculus, Ochr, combining mutable borrows with a dependent type theory with a universe of proof-irrelevant propositions, whose definitional equality unfolds imperative code (@sec-calculus, @sec-eval).
- _Closing off_, which gives every stuck effectful call a neutral form made of sealed source programs, including calls that return borrows (@sec-eval).
- An observational equality between computations that is derived rather than primitive (@sec-obs).
- Worked examples, among them the equivalence of `AddM` with a version that first obtains a borrow of the final node and then writes through it, each proved by bare structural recursion (@sec-overview).
- A translation into the calculus of inductive constructions, in which the backward functions reappear, establishing consistency, and an adequacy theorem relating symbolic and concrete evaluation (@sec-meta).
- An executable implementation of the checker in Lean 4 that checks every example in the paper (@sec-impl).

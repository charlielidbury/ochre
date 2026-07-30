#import "../style.typ": *

= Introduction <intro>

Type systems are the most widely deployed form of static verification, and the guarantees they offer span a wide range: from freedom from runtime type errors, through Rust's ownership-based memory safety, to the full functional correctness of Lean, Agda, and Rocq. The strongest of these guarantees rest on _dependent types_ --- the mechanism by which a type may mention a value, so that a signature can state "this function returns a sorted permutation of its input" and the compiler checks it as a condition of compilation.

There is a large and consequential intersection between software that demands low-level control and software whose correctness is critical: operating-system kernels @klein-2009, cryptographic primitives @hacl-2017, network stacks @project-everest-2017, allocators. Yet the languages that supply the control (C, C++, Rust) lack the type-theoretic machinery for dependent verification, and the languages that supply dependent types (Lean, Agda, F#super[\*]) lack control over layout, allocation, and in-place mutation. A program that needs both is written twice --- once in the systems language, once in the proof assistant --- with a translation between them that must itself be trusted or verified.

DLLBC, the Dependent Low-Level Borrow Calculus, is a core calculus built to test one way of closing this gap: put dependent types and Rust-style ownership in _one_ language, and let _one_ symbolic interpreter serve as both the borrow checker and the dependent type checker. The move that makes this possible is to erase the syntactic wall between terms and types. There is a single syntactic category; types are terms of universe sort; and the ownership constructs --- borrow, loan, dereference --- are ordinary term formers within it. Type checking is then not a discipline layered over evaluation but the _same evaluator run on symbolic inputs_: to check a function body, the interpreter runs it over symbolic arguments, watching ownership flow and computing types by the very reduction rules the runtime uses. Borrow checking and type checking become two readings of one execution.

== The headline artifact

The calculus is driven by a target program: an imperative, in-place quicksort over a mutable borrow, written in the shape a Rust programmer would write it. The mechanization verifies it twice, under the two architectures @sec-architectures compares, and the pair is the paper's central artifact.

The first is _conformance_: the quicksort carries a signature tying it to a pure specification, and it _type-checks as an implementation of its pure model_ `sortRangeL` --- a check that fuses the ownership audit (the borrows are used safely) with dependent conversion (the mutated value matches the model's result). What that route leaves open is the model's _own_ correctness, that `sortRangeL` returns a sorted permutation, which reduces to ordinary lemmas in the pure fragment. #status("open")

The second removes the model. Each function is described _only_ by its return type --- a postcondition over the value the borrow holds at exit --- and every proof step is built inside the imperative body from its callees' postconditions. Its quicksort's return type is sortedness of the exit list paired with count-preservation against the entry list, and there is no pure model of the partition or of the sort anywhere in that development; the properties one wants are proved where the mutation happens. #status("green") This is the route the project chose, and carrying it to completion is what the paper reports.

Two caveats bound both. Recursion is guarded by a _declared_ decreasing argument, and with a sufficiency hypothesis discharging the out-of-fuel path the guarded recursion is total --- but the guard is per-declaration and mutual recursion is rejected rather than supported. And because the v0 mechanization collapses the universe hierarchy to type-in-type --- surrendering strong normalization to Girard's paradox --- everything here is "verified modulo Girard." Consistency is deferred project-wide, and the hierarchy returns with it.

== The money test

The claim that _both_ machineries are indispensable is best made by a program that only their fusion rejects. Take a length-indexed vector paired with its length as a dependent $Sigma$-type, borrow it mutably, and push an element by mutating both fields in place --- but _forget_ to increment the stored length:

```rust
fn push (e : T, v : &mut Σ (l : Nat). Vec T l) = {
  match v { Pair(l, xs) => {
    *xs := VCons(*l, e, *xs);   // xs now holds a Vec T (S l)
    // *l := S(*l);             ← forgotten
  }}
}
```

No borrow checker rejects this: every write is memory-safe, the two field borrows are disjoint, nothing dangles. No _pure_ dependent type checker rejects it either, because there is no mutation for one to watch. It is caught only by the single interpreter that, at the function boundary, audits the mutated value against the type it now owes --- and that type must _compute_. The second field is expected at `Vec T *l`; with the length left at `l`, the deref `*l` is the unknown snapshot $sym("l")$, the expected type is stuck at `Vec T` $space sym("l")$, and no constructor inhabits a stuck type, so the field --- which now carries a `Vec T (S` $space sym("l")$`)` --- fails to convert. The rejection is not a bespoke rule but conversion having nothing to say yes to (@fig-typing). Restore the increment and the two types meet by arithmetic. This program --- accepted the instant the update is present, rejected the instant it is dropped --- is the calculus's evidence that ownership and dependency do distinct, non-redundant work inside one checker.

== Contributions

- *The calculus and its presentation* (@calculus): one grammar and four evaluation arrows --- runtime read and write, comptime read and write --- that carry all behavioral variation, organized by a construct/arrow table that serves as the map of the language.

- *The founding identification, and fording* (@identification): the observation that the symbolic refinement of a matched scrutinee in LLBC @ho-fromherz-protzenko-2024 _is_ Agda-style dependent pattern matching --- one substitution mechanism --- together with its architectural payoff. The kernel implements only the unification _solution_ transition and its occurs check; no-confusion, constructor injectivity, UIP, and conflict discharge are a _derived library_ inside the calculus, built from the identity eliminators and mechanically checked (@fig-match, @fig-typing). The account is completed by _branch equations_: substitution rewrites a scrutinee's occurrences, but where the scrutinee is a stuck spine the checker must first _abstract_ it, and abstraction is what leaves a body unable to name what it just learned. Binding the branch's own equation restores it, and costs nothing at the splits where substitution already sufficed.

- *Declared-and-checked backward specifications.* Where Aeneas @aeneas-2022 synthesizes a backward function to describe what flows back out through a borrow, DLLBC lets the programmer _declare_ that description in the signature and checks the body against it. A lying declaration is rejected; the checked conformance of quicksort to `sortRangeL` is the payoff.

- *The case study, twice* (@sec-casestudy): the in-place quicksort type-checked end to end as an implementation of its pure model, and then re-posed and re-proved with no model at all, its postcondition discharged inside the bodies. The second required three things the first never did --- branch equations, a $Sigma$-eliminator so that a caller can take a returned certificate apart, and the recursion guard below --- and each of the three is a place where removing the model exposed something it had been hiding.

- *A declared decreasing-argument guard, closing a live unsoundness.* Because a call is checked against a signature alone, a self-call was admitted at the function's own declared return type with no side condition: Hoare's recursion rule with its side condition deleted, under which `fn bad () -> Id Nat Z (S Z) { bad() }` was accepted. The hole was unreachable under the conformance architecture and immediate under the direct one, which is itself the paper's sharpest evidence for building both (@sec-lessons).

- *Empirical metatheory:* a validated differential harness relating the symbolic checker to a concrete evaluator, and verified invariants of the checker itself --- notably the discipline that refinement propagates _knowledge_ (constructor shapes, equation solutions) and never _state_ (holes, loan markers, mutation results), which instrumentation found violated exactly zero times and which is now asserted at its single substitution site.

- *A measured comparison of two verification architectures* (@sec-architectures): routing correctness through a pure model (the conformance route --- effectively the Aeneas pipeline rebuilt inside one language) versus proving _propositional_ postconditions directly in imperative bodies over exit snapshots. Both are landed on the same problem --- though not, as @sec-casestudy is careful to say, as the same program --- so the comparison rests on two working developments rather than a projection; two of its findings --- that the direct route does not merely relocate the pure model, and that it is cheaper to check by a wide margin --- were not arguments the project had when it chose that route.

== Roadmap and lineage

@calculus presents the grammar, the four arrows, and the first programs run on the machine; @identification develops the identification of refinement with dependent matching and the fording library it makes possible. The remainder of the paper takes up the boundary discipline and the audit at return (@sec-boundaries), works the quicksort case study twice, once under each architecture (@sec-casestudy), reports the differential harness and the verified invariants (@sec-empirics), sets the two verification architectures side by side (@sec-architectures), and closes with lessons (@sec-lessons) and related work (@sec-related). The complete rule set, each figure ending in a rule-to-implementation-to-test correspondence table, is @rules.

DLLBC is the mutation-stage vehicle of a longer program. It supersedes an earlier staging --- a pure core with equirecursive subtyping and self-types @hutchins-2010, then an ownership layer, then mutation --- by carrying ownership and dependency together from the start, which is where their interaction, the object of study, actually lives.

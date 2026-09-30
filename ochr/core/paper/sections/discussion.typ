#import "../style.typ": *

== Limitations and directions

*Opaque definitions.* A call through an abstract function value is stuck at once and closed off, so it behaves according to its signature alone, as every callee does in Aeneas @aeneas; but there is not yet a way to check a body once and then hide it from conversion, which is what modular verification needs.

*No `'static` borrows.* Safe Rust lets a `fn(&mut u64) -> &mut u64` return `Box::leak(Box::new(0))`, whose backward function is constant, while Ochr proves that every `Π(x : &Nat). &Nat` has an injective one (@sec-meta-model); an opaque or foreign definition of a borrow-returning type is therefore an unchecked injectivity assumption.

*Borrows stored in data.* Borrow types never occur inside other types, which rules out an iterator `IterM : &(List Nat) → List (&Nat)`: the number of borrows it returns is unknown on symbolic input, so no fixed set of holes can stand for their final values. The natural generalisation is a hole for a whole structure of final values, the neutral form of an Aeneas region abstraction with a borrow projector. A fixed number of returned borrows is easier, and would give `split_at_mut`.

*Other directions.* A generic `&A` for `A : Type₀`, which might be a universe or a proposition, needs a universe of data types below `Type₀`. A shared borrow needs no sealed program of its own, since its final value is its initial one, but its interaction with mutable borrows through reborrowing and two-phase borrows is not designed. A loop would be a tail-recursive local function whose type is its invariant. Global state, interior mutability and unsafe aliasing would each break the frame property, and would have to be confined behind interfaces. With indexed families, `Eq` could be declared rather than built in.

== The checked machine and the compiled program

The machine that the checker runs, and that the proofs are about, moves data as Rust does, so `AddM` allocates nothing, and among the programs the fuzzer generates, its execution oracle finds none that is accepted and goes wrong when run, though a probe has found one outside them (@sec-meta-nat). What remains is the relation to compiled code: the machine runs types and proofs on discarded private copies, and keeps ghosts of moved values for them, where a compiled program omits both. That the compiled program behaves as the checked one is, for now, an assumption. The gap is narrower than the one @sec-intro-two criticises in the pure route, since where the program mutates in place is written and checked. Erased reads do not count as uses, which is what lets `x + x = 2 · x` be stated without `clone`, as in quantitative type theory @qtt.

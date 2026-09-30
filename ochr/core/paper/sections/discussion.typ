#import "../style.typ": *

== Limitations and directions

*Opaque definitions.* A definition may be declared with a type and no body, or used through an abstract function value. A call to it is stuck at once and closed off, so it behaves according to its signature alone, as every callee does in Aeneas @aeneas. Such a definition is an axiom: there is not yet a way to check a body once and then hide it from conversion, which is what modular verification needs.

*No `'static` borrows.* Safe Rust lets a `fn(&mut u64) -> &mut u64` return `Box::leak(Box::new(0))`, whose backward function is constant, while Ochr proves that every `Π(x : &Nat). &Nat` has an injective one (@sec-meta-model); an opaque or foreign definition of a borrow-returning type is therefore an unchecked injectivity assumption.

*Borrows stored in data.* Borrow types never occur inside other types, which rules out an iterator returning a list of borrows into a list, `IterM : &(List Nat) → List (&Nat)`. The number of borrows returned is unknown on symbolic input, so no fixed set of holes can stand for their final values. The natural generalisation is a hole standing for a whole structure of final values, filled when the last borrow in it ends, which is the neutral form of an Aeneas region abstraction with a borrow projector. A fixed number of returned borrows is easier, and would give `split_at_mut`.

*Other directions.* A generic `&A` for `A : Type₀`, which might be a universe or a proposition, needs a universe of data types below `Type₀`. A shared borrow needs no sealed program of its own, since its final value is its initial one, but its interaction with mutable borrows through reborrowing and two-phase borrows is not designed. A loop would be a tail-recursive local function whose type is its invariant. Global state, interior mutability and unsafe aliasing would each break the frame property, and would have to be confined behind interfaces. With indexed families, `Eq` could be declared rather than built in.

== Costs

*Checking cost.* Type checking runs programs: each stuck call is closed off once, and each refinement re-runs the sealed programs that mention the refined value. Sealed programs are closed and canonical, so their normal forms could be cached; our implementation does no caching (@sec-impl).

*The checked machine is not yet the compiled program.* The machine that the checker runs, and that the proofs are about, moves data as Rust does, so `AddM` allocates nothing, and the fuzzer's execution oracle finds no accepted program that goes wrong when run (@sec-meta-nat). What remains is the relation to compiled code: the machine runs types and proofs on discarded private copies, and keeps ghosts of moved values for them, where a compiled program omits both. That the compiled program behaves as the checked one is, for now, an assumption. The gap is narrower than the one @sec-intro-two criticises in the pure route, since where the program mutates in place is written in its text and checked, but it is a gap. Erased reads do not count as uses, which is what lets `x + x = 2 · x` be stated without `clone`, as in quantitative type theory @qtt.

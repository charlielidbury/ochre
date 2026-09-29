#import "../style.typ": *

== Limitations and directions

*Opaque definitions.* A definition may be declared with a type and no body, or used through an abstract function value. A call to it is stuck at once and closed off, so it behaves according to its signature alone, as every callee does in Aeneas @aeneas. Such a definition is an axiom: there is not yet a way to check a body once and then hide it from conversion, which is what modular verification needs.

*No `'static` borrows.* Every borrow a function returns derives from one of its borrow arguments: Rust's lifetime-elision rule, made a restriction. Safe Rust lets a `fn(&mut u64) -> &mut u64` return `Box::leak(Box::new(0))`, whose backward function is constant, while Ochr proves that every `Π(x : &Nat). &Nat` has an injective one (@sec-meta-model). An opaque or foreign definition of a borrow-returning type is therefore an unchecked injectivity assumption.

*Borrows stored in data.* Borrow types never occur inside other types, which rules out an iterator returning a list of borrows into a list, `IterM : &(List Nat) → List (&Nat)`. The number of borrows returned is unknown on symbolic input, so no fixed set of holes can stand for their final values. The natural generalisation is a hole standing for a whole structure of final values, filled when the last borrow in it ends, which is the neutral form of an Aeneas region abstraction with a borrow projector. A fixed number of returned borrows is easier, and would give `split_at_mut`.

*Borrows of an arbitrary type.* A function cannot take `&A` for a type parameter `A : Type₀`, which might be instantiated at a universe, a Π-type or a proposition (@fig-why), so a generic in-place swap is not expressible. A universe of data types below `Type₀` would bring it back.

*Shared borrows, loops and unsafe code.* A shared borrow has no final value different from its initial one, so it needs no sealed program of its own, but it interacts with mutable borrows through reborrowing and two-phase borrows, which we have not designed. A loop would be a tail-recursive local function whose type is its invariant. Global state, interior mutability and unsafe aliasing would each break the frame property that closing off rests on, and would have to be confined behind interfaces, as Rust confines unsafe code. Indexed families are also future work; with them `Eq` could be declared rather than built in, if its computation rules survive.

== Costs

*Checking cost.* Type checking runs programs. On symbolic data each stuck call is closed off once, and each refinement re-runs the sealed programs that mention the refined value. Sealed programs are closed and canonical, so their normal forms could be cached and shared. Our implementation does no caching and decides every example of this paper in milliseconds (@sec-impl); we have not measured large programs.

*The checked machine is not yet the compiled program.* The machine that the checker runs, and that the proofs are about, copies borrow-free data on every read, and runs types on a discarded private copy. A compiled program should move instead, so that `AddM` allocates nothing, and omit types and proofs. An affine usage discipline on runtime code would license the moves, since a copy never used again cannot be told apart from a move, but we have not defined it, nor related a compiled program to the machine: that the compiled program behaves as the checked one is, for now, an assumption. The gap is narrower than the one @sec-intro-two criticises in the pure route, since where the program mutates in place is written in its text and checked, but it is a gap. Types are exempt from the affine discipline, which is what lets `x + x = 2 · x` be stated without a copy operation, as in quantitative type theory @qtt.

*What the programmer sees.* Every value in a goal is data, an abstract value named after the parameter it came from, or a sealed program, which is source code and can be printed as the user's own wrapper when one exists (`⌈let c = σ; AddM(&c, 0); c⌉` is `Add(x, 0)`). Goals mention loans only as the holes of sealed programs, and never mention borrows, environments or backward functions.

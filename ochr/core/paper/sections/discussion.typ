#import "../style.typ": *

== What generalises directly

*Inductive types.* The rules are stated for natural numbers, but nothing in them is specific to numbers, and the implementation supports user-declared inductive types (@sec-overview, @sec-impl): a constructor with several fields gives several sub-places, [Split] refines an abstract value to a constructor applied to fresh abstract values, and [Rec] asks for a strict subterm of the entry value. Indexed families are future work.

*Opaque definitions.* A definition may be declared with a type and no body, or used through an abstract function value. A call to it is stuck at once and closed off, so its effects are recorded as sealed programs mentioning it, and every theorem about its callers remains available. This is how Ochr recovers the modularity of Aeneas's symbolic execution @aeneas, which never unfolds a callee: the programmer chooses, per definition, whether conversion may look inside. One caveat carries over from the model (@sec-meta): an opaque definition that returns a borrow is an _assumption_ that its backward function is injective, so binding it to an arbitrary external function is unsound in general.

*Shared borrows.* Immutable borrows are simpler than mutable ones in this setting: a shared borrow never has a final value different from its initial one, so closing off a call that takes one needs no sealed program for it. We omitted them to keep the core small.

== The frontier

*Borrows stored in data.* The central restriction of the core is that borrow types never occur inside other types. It rules out an iterator that returns a list of borrows into a list, `IterM : &(List Nat) → List (&Nat)`. There, the number of borrows returned is itself unknown on symbolic input, so no fixed set of holes can stand for their final values. The natural generalisation is a hole that stands for a whole data structure of final values, filled when the last borrow in the structure ends, which is the neutral form of an Aeneas region abstraction over a symbolic value with a borrow projector. The same restriction excludes closures that capture borrows.

*Loops.* A loop is a tail-recursive local function, and its type is its invariant. Closing off a loop that is stuck on an abstract value is closing off that function. We have not designed the surface form, nor checked whether the invariants that arise are the ones programmers expect to write.

*Interior mutability and unsafe code.* Closing off is sound because a call can affect only what it is passed. Global state, interior mutability or unsafe aliasing would each break this frame property, and with it the rule. They would need to be confined, as Rust confines unsafe code behind safe interfaces, and given sealed-program semantics through their interfaces.

== Costs

*Checking cost.* Type checking runs programs. On concrete data this is the cost of running them; on symbolic data each stuck call is closed off once, and each refinement re-runs the sealed programs that mention the refined value. Sealed programs are closed and canonical, so their normal forms can be cached and shared, and a refinement only re-runs what mentions it. Our implementation does no caching and decides every example of this paper in about 9 ms in total; we have not measured large programs.

*Copying.* The calculus copies borrow-free data on reads. A compiled program should move instead, and an affine usage discipline on runtime code, outside the core, licenses implementing each last-use copy as a move. Types are exempt from that discipline, which is what lets `x + x = 2 · x` be stated for a type without a copy operation; this is the same separation between runtime usage and erased usage as quantitative type theory @qtt.

*What the programmer sees.* Goals and hypotheses are propositions about values, and every value that appears in them is either data, an abstract value named after the parameter it came from, or a sealed program, which is source code. A sealed program can be printed as the user's own wrapper when one exists (`⌈let c = σ; AddM(&c, 0); c⌉` is `Add(x, 0)`). Nothing in a goal mentions loans, borrows, environments or backward functions. We regard this as a design invariant, and it is a useful test for extensions: a feature whose goals cannot be printed as source code is one the programmer would need a new concept to reason about.

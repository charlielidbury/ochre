#import "../style.typ": *

= Two architectures for verification <sec-architectures>

The declared-back machinery of @sec-boundaries admits two very different ways of
verifying an imperative program, and this project has built both. They differ in
what the signature promises and in where the proof burden lands. The first routes
all reasoning through a pure model and keeps the imperative body proof-free; it is
landed and green. The second proves properties _directly_ in the body, over the
value the borrow holds at exit; its semantics is decided and its implementation is
in flight. This section measures the two against each other, because the choice
between them is the live decision of the project, and the choice was made
deliberately and recently in favour of the second.

== Architecture A: conformance to a pure model

A declared back can be the whole story. Give an in-place mutator a `back` that
_is_ a pure function computing the same result, and the audit (@sec-boundaries,
#smallcaps[B-Back0]/#smallcaps[B-BackN]) checks the imperative body against that
pure model by a single conversion — the body's suspension tree is definitionally
the model's unfold. The flagship instance is in the mechanization and green: the
in-place, swap-based quicksort type-checks as an implementation of its pure model,
with `back = sortRangeL fuel lo cnt` $ast.op v$:

```rust
fn quicksort (v : &mut List Nat, fuel : Nat, lo : Nat, cnt : Nat, hbnd : …) -> Unit
  back = sortRangeL fuel lo cnt (*v) = { … }
```

Three properties define this architecture, and all three are checked. The body
carries _zero_ proof obligations: partition and the two recursive calls compose
their declared backs, and that composition converts against `sortRangeL`'s own
unfold — conformance _is_ conversion, nothing more. The caller recovers an
_exact value_, not merely a property: ending the loan releases `sortRangeL`
applied to the entry snapshot, so a caller that sorts a concrete list gets that
concrete sorted list back. And correctness — that `sortRangeL` sorts, that it
permutes — becomes a set of lemmas about the _pure model_, proved in the comptime
fragment by ordinary type theory, entirely apart from the borrows. Verification
splits cleanly into _conformance_ (mechanical, the back audit) and _model
correctness_ (ordinary dependent-type reasoning). The full walkthrough is the
quicksort case study; here we only record what the architecture _is_.

What it is, honestly stated, is Aeneas rebuilt inside one language. Aeneas
verifies Rust by extracting a pure functional model and reasoning about that; this
architecture does the same, except the extraction is a declared `back` and the
conformance is a conversion rather than a translation. The consequence is the
point: the imperative body never carries a proof, so the interaction this calculus
exists to study — dependent types _crossing_ mutation, a proof about a value that
is being mutated through a borrow — is never exercised where it is hard. All the
hard reasoning has been exported to a pure model that could have been written in
any prover. Architecture A is real, it is green, and it is deliberately the
_comparison baseline_ rather than the mission.

== Architecture B: direct propositional proving

The mission, set by the project in favour of exactly the interaction A avoids, is
to prove postconditions _directly in the body_, over the value the borrow holds
at exit:

```rust
fn quicksort (v : &mut List Nat) -> Sorted (*v) ∧ Perm (old *v) (*v)
```

The parameter stays a plain `List Nat`; the evidence rides the return type. Two
snapshot readings make this well-formed, and both are decided (@sec-boundaries
records the rule-gap where the implementation still pins entry wholesale).
$ast.op v$ _in return position_ denotes the *exit snapshot* — the value the borrow
holds at the audit. It is canonical for the same reason the calculus has no
lifetime annotations: with no lifetimes, the callee's exclusive access ends
_exactly_ at the audit, and the audit already computes the collapsed final
payload, so "the value at the end" names one well-defined tree. `old` $ast.op v$
denotes the *entry snapshot* — `old` is an operator, not a binder, sugar over the
telescope's existing entry snapshot, so nothing scoped escapes its bracket. A
postcondition can therefore relate exit to entry (`Perm (old *v) (*v)`: the exit
list is a permutation of the entry list) without either becoming stale.

The proofs are threaded through the body from callees' postconditions. A call to
partition returns evidence about the partitioned list; the caller opens that
evidence and uses it to discharge its own obligations, exactly as one composes
lemmas — except the "lemmas" are the postconditions of imperative calls, and the
subject they speak about is a value being mutated in place. Caller-side, a single
symbolic value is shared between the loan's eventual release and the returned
evidence's subject, so the proof _attaches_ to the recovered value rather than
floating beside it.

This is the architecture that walks into the hard interaction on purpose, and the
friction it meets there is the research object, not an obstacle to be smoothed
over before publication. The project keeps a _pain diary_: each contortion the
programmer is forced into is logged as a candidate calculus feature — a missing
sugar, an absent rule, an implicit that should have been inferred. The exit-
snapshot reading and the `old` operator are the first two entries promoted from
diary to design; the milestone that carries them, together with swap, partition,
and quicksort re-specced and re-proved in this propositional style, is in flight.
*[Status: in-flight]* The return-type snapshot machine it needs — $ast.op v$ read
at exit rather than entry — is decided but not yet mechanized. *[Status: proposed]*

Architecture B is a research direction with a mechanized skeleton, not vaporware.
Two fragments of it are already green. The M16 proof-of-concept `swapS01` — a
spec-carrying in-place swap whose $arrow.r.curve$-obligation is a $Sigma$ pairing
the swapped list with an `Id`-proof of length preservation — checks, and its
caller opens the pair to recover _the list and a proof about it_, evidence
surviving a boundary and attaching to the recovered value. Building on it,
`certSwapCount` in the S19 partition listing carries a count-preservation
certificate over a _symbolic_ list, threading a `swapS` call's postcondition into
a caller's obligation. Both pass by `native_decide`; they are the existing
propositional fragments the full case study extends.

== The comparison

#table(
  columns: (auto, 1fr, 1fr),
  align: (left, left, left),
  inset: 7pt,
  table.header(
    [],
    [*A — pure-model conformance*],
    [*B — direct propositional*],
  ),
  [Return type],
  [borrow stays a borrow; a declared `back` names the pure model],
  [borrow stays a borrow; postcondition over the exit snapshot $ast.op v$, `old` for entry],

  [Body proof burden],
  [none — conformance is one conversion of the composed backs],
  [proofs threaded through the body from callees' postconditions ($Sigma$/evidence plumbing)],

  [Caller recovers],
  [the _exact value_ — the model applied to the entry snapshot],
  [the _property_ (`Sorted`, `Perm`), attached to the recovered value],

  [Correctness proof],
  [lemmas about the pure model, proved separately in the comptime fragment],
  [proved in place, directly, as the body is checked],

  [Reformulation problem],
  [present — a back that reformulates its tree is outside conversion's reach (@sec-boundaries); bridging-equation close deferred],
  [absent — there is no back to reformulate; the postcondition is proved directly],

  [Status],
  [landed, green (quicksort conforms to `sortRangeL`)],
  [semantics decided; implementation in flight (fragments green)],
)

The trade is legible in the table. A costs nothing in the body and yields the
exact value, but pays in a pure model that must be written and kept in step, and
inherits the reformulation gap of @sec-boundaries — the moment a declared back is
stated in any form other than the raw suspension tree, conversion may not see the
equality, and the audit must fall back to differential validation. B pays in the
body — every property must be plumbed through as evidence — but yields the
property one actually wants, over the value one actually has, with no separate
model to maintain and so no reformulation problem to inherit. B's discipline is
the `ensures`-clause of a Floyd–Hoare verifier such as Dafny, recovered here
without a separate specification language: the postcondition is an ordinary
dependent type over the exit snapshot, checked by the same interpreter that runs
the body. That the calculus can express either architecture from the _same_
boundary machinery — a declared `back` for A, a postcondition over $ast.op v$ for
B — is itself the finding; that the project has chosen B, and treats the friction
of proving over mutated state as the contribution rather than the cost, is the
direction the rest of this work pursues.

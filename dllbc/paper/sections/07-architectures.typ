#import "../style.typ": *

= Two architectures for verification <sec-architectures>

The declared-back machinery of @sec-boundaries admits two very different ways of
verifying an imperative program, and this project has built both, to completion.
They differ in what the signature promises and in where the proof burden lands.
The first routes all reasoning through a pure model and keeps the imperative body
proof-free. The second proves properties _directly_ in the body, over the value
the borrow holds at exit. Both are landed and green at the pin, on the same
_problem_, which is what makes the comparison below a measurement rather than a
prediction: @sec-casestudy works each of them as a full in-place quicksort. The
two are not the same _program_ — how the problem is posed differs with the
architecture, and @sec-directroute says how — which bounds what the comparison can attribute. The
project chose the second, deliberately, as its mission; the first remains as the
baseline the choice was made against.

== Architecture A: conformance to a pure model

A declared back can be the whole story. Give an in-place mutator a `back` that
_is_ a pure function computing the same result, and the audit (@sec-boundaries,
#smallcaps[B-Back0]/#smallcaps[B-BackN]) checks the imperative body against that
pure model by a single conversion — the body's suspension tree is definitionally
the model's unfold. The flagship instance is in the mechanization and green: the
in-place, swap-based quicksort type-checks as an implementation of its pure model,
with `back = sortRangeL fuel lo cnt` $ast.op v$:

```rust
fn quicksort [fuel] (v : &mut List Nat, fuel : Nat, lo : Nat, cnt : Nat, hbnd : …) -> Unit
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

What it is, honestly stated, is Aeneas @aeneas-2022 rebuilt inside one language. Aeneas
verifies Rust by extracting a pure functional model and reasoning about that; this
architecture does the same, except the extraction is a declared `back` and the
conformance is a conversion rather than a translation. The consequence is the
point: the imperative body never carries a proof, so the interaction this calculus
exists to study — dependent types _crossing_ mutation, a proof about a value that
is being mutated through a borrow — is never exercised where it is hard. All the
hard reasoning has been exported to a pure model that could have been written in
any prover. Architecture A is real, it is green, and it is deliberately the
_comparison baseline_ rather than the mission.

*Reproducibility of A.* "It is green" was true continuously up to commit
`113f1634` and is a historical claim after it. A's programs are still in the
corpus as source, but they are no longer machine-checked, and the reason is
structural rather than incidental: A's cursors recurse through a borrow's payload,
which has no recursor form, so they do not elaborate to the sealed-`let` form that
became the calculus's only checking path when the declaration form was deleted.
The paper's account of A is therefore reproducible at `113f1634`, the last commit
at which a checker exists that admits it. B is unaffected, and the comparison
below is between what A _was_ measured to be and what B _is_.

== Architecture B: direct propositional proving

The mission, set by the project in favour of exactly the interaction A avoids, is
to prove postconditions _directly in the body_, over the value the borrow holds
at exit. In the mechanization at the pin the shape is:

```rust
fn quicksort [fuel] (fuel : Nat, v : &mut List Nat, hfuel : Le (len *v) fuel)
  -> Σ (hs : Sorted (*v)) → Π n. Id Nat (count n (*v)) (count n (old *v))
```

The parameter stays a plain `List Nat`; the evidence rides the return type, as a
$Sigma$ of sortedness over the exit snapshot and count-preservation against the
entry. Permutation is stated by counting rather than by an indexed `Perm` family
— a multiset equality is what the swap and partition lemmas actually establish,
and it is closed under the rearrangements a sort performs. Two snapshot readings
make this well-formed, and both are implemented.
$ast.op v$ _in return position_ denotes the *exit snapshot* — the value the borrow
holds at the audit. It is canonical for the same reason the calculus has no
lifetime annotations: with no lifetimes, the callee's exclusive access ends
_exactly_ at the audit, and the audit already computes the collapsed final
payload, so "the value at the end" names one well-defined tree. `old` $ast.op v$
denotes the *entry snapshot* — `old` is an operator, not a binder, sugar over the
telescope's existing entry snapshot, so nothing scoped escapes its bracket. A
postcondition can therefore relate exit to entry — the count conjunct above says
that every value occurs as often in the exit list as in the entry list — without
either reading becoming stale.

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
sugar, an absent rule, an implicit that should have been inferred. Three entries
have been promoted from diary to design, and the order is instructive. The
exit-snapshot reading and the `old` operator came first, and are what make the
return type above well-formed. _Branch equations_ (@identification) came third and
were the one the architecture could not proceed without: a body that must produce
evidence has to turn "the comparison said yes" into an order fact, and under
architecture A no body ever needed to.

One entry remains open, and it is the residual cost of the architecture rather
than a gap in it. #status("open") A body can name the value a place holds _now_,
and — for a borrow parameter — the value it held at entry; it cannot name the
value a _consumed_ binder held, nor an intermediate exit that a later mutation has
superseded. So a proof spanning two mutations must be built _before_ the second and
applied after, as a function of values that do not exist yet. The mechanization's
quicksort carries four such staged builders; none of them does mathematical work,
and all four would collapse into ordinary lemma applications given an `old` that
extended to consumed things. Six independent instances of the pattern are logged
across the last two milestones — enough that the diary now reads as a
specification for the feature rather than a list of complaints, which is what the
diary discipline is for.

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

  [Body's branch knowledge],
  [occurrence rewriting suffices — no body cites a branch fact],
  [needs _branch equations_: the order fact is produced, not merely assumed (@identification)],

  [Recursion],
  [structural on the model's own `fuel`; conformance is per-path],
  [the declared `[k]` guard, with a sufficiency hypothesis discharging the out-of-fuel path],

  [Cost to check],
  [#status("green") 181 ms for the conformance audit, after the substitution fix (@sec-lessons)],
  [#status("green") 21 ms — a different program, and the encoding is why (@sec-lessons)],

  [Status],
  [#status("green") landed — quicksort conforms to `sortRangeL`],
  [#status("green") landed — quicksort proves `Sorted` $and$ count-preservation, zero declared backs],
)

The trade is legible in the table. A costs nothing in the body and yields the
exact value, but pays in a pure model that must be written and kept in step, and
inherits the reformulation gap of @sec-boundaries — the moment a declared back is
stated in any form other than the raw suspension tree, conversion may not see the
equality, and the audit must fall back to differential validation. B pays in the
body — every property must be plumbed through as evidence — but yields the
property one actually wants, over the value one actually has, with no separate
model to maintain and so no reformulation problem to inherit. B's discipline is
the `ensures`-clause of a Floyd–Hoare verifier such as Dafny @leino-2010, recovered here
without a separate specification language: the postcondition is an ordinary
dependent type over the exit snapshot, checked by the same interpreter that runs
the body. That the calculus can express either architecture from the _same_
boundary machinery — a declared `back` for A, a postcondition over $ast.op v$ for
B — is itself the finding.

*B has since been carried out twice, over different containers, and the second
instance sharpens what the architecture costs.* The array quicksort (@sec-arrays) is
this same architecture — postconditions over the exit snapshot, zero declared backs —
on a representation where a sub-range is a place. Two things follow that the `List`
instance could not have shown. The first is the cross-differential
(@sec-crossdiff): two implementations sharing a specification and nothing else,
agreeing, which is evidence about the _specification_ that no single verified program
can supply. The second is a correction to B's cost model. The array design predicted
that making sub-ranges into places would delete positional reasoning outright; it
deletes it _within a body_ and hands it back at every _function boundary_, because a
signature must describe a split that only the caller's carve can name. So B's ledger
reads: one stratum deleted, one inherited, and one invented at the leaf's interface —
smaller than the one deleted, but not nothing, and not predicted.

Two further results from carrying B to completion sharpen the trade beyond what the
table shows, and neither was predicted. The first is that B does _not_ merely relocate
A's pure model: the mechanization's back-less quicksort has no model function of
the partition anywhere, only _observation_ vocabulary — `count`, `len`, `take`,
`drop`, `append`, `Ub`, `Lb`, `Sorted` — functions that say what a list _is_ rather
than what a body _does_. An earlier reading of the evidence held that direct
proving eliminated conversion-based verification while the model functions survived
as the only provable exit shapes; carrying the architecture to the end refuted it,
and the refutation is recorded in @sec-lessons because the diagnosis it replaced was
a reasonable inference from a partial result. The second is that B is _cheaper to
check_, by a wide margin, for a reason that has nothing to do with either
architecture: the spec encoding, not the checker, dominates the cost (@sec-lessons).
Both findings favour B, and neither is an argument the project made when it chose B
— which is the most one can ask of a comparison one has prejudged.

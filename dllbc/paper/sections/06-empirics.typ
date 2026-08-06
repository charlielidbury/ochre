#import "../style.typ": *

= Metatheory by Empiricism <sec-empirics>

The case study is checked, but the checker is not proved. No soundness theorem
for DLLBC's borrow machinery exists today, and this section does not pretend
otherwise. What it reports instead is the discipline the project keeps in the
theorem's absence: a set of _validated empirical instruments_ and
_machine-verified invariants_ that, between them, state with some precision what
a proof would have to establish. The differential harnesses are counterexample
finders that have been shown to find their counterexample; the refinement
invariant is instrumented across the whole corpus and asserted at its source;
the strategy is a determinization of a nondeterministic rule set whose one known
incompleteness is ledgered. The section closes with the conjecture list a future
soundness proof must discharge, and with the known holes any quantified
statement of it must first close.

== The differential harness

The core instrument is a differential between the symbolic checker and concrete
execution, in two generations. Both are _program_-shaped at this pin: a subject is
a `prog{ … }` let-chain with its callees declared inside it, accepted or rejected
by `progOk`, with no declaration wrapper and no call table — which is a change in
the harness's plumbing rather than in what it measures, since a declaration was
always the thing being checked and is now a binding.

The first generation tests the callee side. Its property: _if the checker accepts
a body, then every small concrete run of it completes — is not stuck — and passes
the concrete audit._ This is the simulation theorem — the symbolic checker
over-approximates concrete execution — in the form of a bounded,
exhaustively-checked `native_decide` proposition over a generated enumeration of
bodies. Across three telescopes it generates 136 bodies, of which the checker
accepts 75, exercised by 238 concrete runs; all complete and audit, with no
counterexample. The per-telescope figures are 91/47/141 for
`(v : &mut List Nat)`, 32/15/45 for `(n : Nat)`, and 13/13/52 for
`(b : &mut Nat, c : Bool)`. All six numbers are `native_decide` assertions in the
suite rather than a comment, so a drift goes red instead of quietly falsifying
this paragraph; they are unchanged across both campaigns, which is itself the
claim that the surface collapse did not move what the generator generates or what
the checker accepts.

The second generation upgrades to whole-program simulation, so that it catches
wrong-_value_ refinements and not merely stuckness. Its property: for every
accepted caller, the caller's _concrete_ final environment (run in executing mode,
where calls run the callee's actual body) is a $sigma$-_instance_ of some accepted
_symbolic_ path's final environment (run in checking mode, where calls use the
signature rule). The instance relation is first-order matching — a symbolic
$sigma$ matches any concrete value _consistently_ (the same $sigma$ maps to one
value throughout), constructors match structurally, loans and borrows up to
canonical renumbering — which is the simulation relation proper. The caller set is
four programs, shaped on `through`, `advance`, `choose` and `push`; all four are
accepted and all four hold.

The essential part is not that these pass but that they have been _validated_: a
counterexample finder that has never found its counterexample is worthless as
evidence. *And the validation was downgraded at this pin, which the paper's own
standard requires stating before anything else about it.* It used to reintroduce
the bug in order to catch it: a flag flipped the kernel back to the unsound
signature-inferred `constrained` wire, and the `advance`-caller differential was
asserted to go _red_ with the flag on and _green_ with it off. That is the
strongest form the claim can take. It cost kernel surface carried for one test —
the flag and the group field it drove — and both were deleted, so the same content
is now stated one level down, at the *comparator*: the wrong refinement's
environment is written directly (the owner recovering the surrendered tail) and
asserted _not_ to be an instance of the real concrete run, with the honest opaque
$sigma$ asserted to be one, under both relations. What that keeps is the exact
discrimination — the relation says no to the wrong refinement and yes to the right
one, so it is not a relation that says no to everything. What it gives up is the
demonstration that the _finder_, driven by a kernel that really is buggy, arrives
at that comparison at all. That is a real reduction in the instrument's strength,
and it is the price of not carrying a kernel field for a test.

== The polarity finding: when the machine is the broken one <sec-polarity>

The differential has always been justified defensively — as insurance that the
checker does not accept something execution cannot do. That justification is
incomplete, and the array development is what showed it.

Every previously-known divergence between the two sides has had the checker as the
_approximating_ one. @sec-boundaries records the canonical instance: a loan group
releases its captured loans atomically at a fresh existential, where concrete
execution ends each lazily, per owner, so a symbolic environment can hold a released
value where the concrete one still holds a suspended loan. The checker is coarser;
execution is the ground truth the checker is a safe abstraction of. A metatheory
written from that assumption would say so, and every member of the family had
confirmed it.

The array quicksort broke that pattern. It type-checked and _could not be run_: in
executing mode a carving callee left the caller's array segmented, and the caller's
next carve then read the wrong leaf. Checking mode never saw the fault, because a
call re-mints the callee's payload as a fresh symbolic value at the declared type
(@sec-boundaries's opacity), so the checker always sees an _uncarved_ array. The
temptation is to read that as one more over-approximation. It is the opposite:

#block(inset: 8pt, stroke: 0.5pt + luma(150), radius: 3pt, width: 100%)[
  The re-mint is not an approximation of what execution does. It is a *repair* of it.
  The checker was right and the machine was wrong — and no amount of checking could
  have revealed that.
]

This matters beyond the bug. A design document can reason about whether the checker
over-approximates the machine; it cannot discover that the machine is the one that is
broken, because the machine is what it would be reasoning _from_. Only running both
and comparing can. That makes the differential harness part of the central claim
rather than an assurance activity attached to it — and it means the reconciliation a
future soundness proof owes is not "the checker over-approximates" but a genuine
two-sided relation, since at least one member of the family runs the other way.

The fault's _root_ carries the transferable lesson. It was a normalization that
discards a zero-extent segment and unwraps a lone survivor — reasonable, and wrong,
in four independent places, because the rest of the machine depends on structure it
was throwing away. Every one of the four is *unreachable symbolically*, since a
residue is never _known_ to be zero, and *routine concretely*, since a runtime-computed
split has an empty side constantly. That asymmetry is exactly why the symbolic suite
stayed green throughout. Generalized: _a normalization justified on symbolic values,
applied to concrete ones_ — and the reason it took four rounds to finish is that each
site looked like the last one.

== The cross-differential: two implementations, one specification <sec-crossdiff>

The harnesses above compare the checker with the machine. The array development makes
a third comparison available, and it is of a different kind: two _implementations_,
checked against each other.

The `List` and `Array` quicksorts share a specification — sortedness of the exit
snapshot with count-preservation against the entry — and share nothing else. Not the
program (take-and-rebuild versus an in-place carved scan), not the partition, not the
predicates, not the container, not one line of proof. Run on eleven shared inputs,
they agree with each other _and_ with a reference sort. The conjunction is
deliberate: a two-way agreement on a wrong answer still goes red, so the test does not
reward the two implementations for sharing a mistake — and a failure to run on either
side cannot masquerade as agreement.

What that buys is evidence about the _specification_ rather than about either
implementation. A single verified program tells you it satisfies the postcondition you
wrote; it tells you nothing about whether the postcondition says what you meant. Two
programs sharing only the postcondition, disagreeing, would indict the postcondition
or one of the proofs. Agreeing, they are weak evidence that the shared statement is
the one intended — weak because eleven inputs is eleven inputs, but it is a kind of
evidence the project could not previously produce at all.

#block(inset: (left: 1em))[
  #text(size: 8.5pt)[
  *A fence, because this paper now reports three measurement sets and they are not
  comparable.* (i) The *conformance* audit's 465× speedup (84,121 ms to 181 ms) is a
  _checker_ change — a substitution fix — measured on architecture A's program.
  (ii) The *positional-versus-whole-list* gap (21.8 s to 21 ms) is two direct-proving
  `List` programs differing in both specification encoding and partition program, with
  no checker work between them; @sec-lessons states why the honest attribution is to
  the pair rather than to the encoding alone. (iii) The *cross-differential* is not a
  performance measurement at all — it is an agreement check between two
  implementations, and its number (eleven inputs) is a count of test cases, not of
  time. Combining any two of the three into one comparison would be wrong.

  *Reproducibility of (i).* The conformance number is measured by a compiled timing
  harness over architecture A's back-carrying declarations (`lake exe bench`), and
  that architecture was retired to history when the declaration form was deleted;
  the harness went with it, having nothing left to time. (i) is therefore
  reproducible at commit `2f94aa6d`, the last at which the harness exists. (ii) and
  (iii) are unaffected — both are measured on the direct-proving programs, which
  are the current ones.
  ]
]

== Discovered preconditions

The harness does more than pass; it has told the design what the theorem needs.
The clearest case is _exhaustiveness_. A symbolic `match` missing a constructor
was, at one point, accepted by the checker (inductive-declaration exhaustiveness
having been deferred) yet concretely _stuck_ on the missing branch — precisely an
accepted-but-unsafe program, the differential's target. Exhaustiveness is now
checked at the symbolic match fork (@fig-match): a branch set must cover the
scrutinee type's constructors. With that, "accepted $arrow.r.double.long$
concrete-safe" becomes unconditional over the generator's grammar, and the
suite's non-exhaustive bodies are all rejected. The lesson is general: a
precondition of the simulation theorem was made _syntactic_, moved from an
informal caveat into a rule the checker enforces.

== The knowledge/state invariant

The refinement arrow $arrow.l.squiggly$ carries an invariant with two halves,
both now machine-checked. It propagates _knowledge_ — constructor shapes and
equation solutions, facts true of a value timelessly — and never _state_ — a
hole, a loan marker, or a mutation's result, which are facts about a slot at a
moment. The _reach_ half: a single $arrow.l.squiggly$ substitutes into every
$sigma$-bearing component of the whole checker state — the environment, the
$sigma$-context, the boundary obligations, the loan groups, and the pinned return
type (@fig-boundaries) — because any component that snapshots a $sigma$-typed
thing at seed time and consults it later goes stale otherwise. One component is
deliberately _outside_ the reach, and the exception proves the rule: the
exit-snapshot table, which the audit defines by substituting each borrow's
collapsed final payload, is written by a dedicated audit-local pass and not by
$arrow.l.squiggly$ — precisely because what it carries is a mutation's result,
which is the one thing the _carry_ half forbids a refinement to move. (A fifth
component the reach used to name, the reflected backward specs, went with the
machinery.) The _carry_ half: no substitution for a $sigma$ may contain a
hole, a marker, or a mutation result — recording a take, a fill, or a swap's
arrangement by rewriting a $sigma$ would make a snapshot track the present, so
that a pinned `partIdxL n *v` would come to mean the index of the
_already-partitioned_ list, the one staleness the whole snapshot discipline
exists to forbid.

Stated first as a diagnosis, the invariant became prophylaxis: instrumenting the
entire mechanization found _zero_ violations — no substitution ever carried a
hole, marker, or mutation result — so it is verified rather than aspirational,
and it is asserted at the substitution site to keep it verified as the corpus
grows. (The bug that prompted the audit was elsewhere and mundane: a comptime
read of a consumed variable returned $bot$ silently, where the runtime read
rejects use-after-move.)

== Nondeterministic rules, and a lazy strategy

The rule figures are presented _nondeterministically_: a reorganization may fire
wherever its premises hold. The implementation is one deterministic scheduling of
them — a lazy, fuel-bounded strategy that fires a reorganization only when some
rule's premise demands it. The determinization is explicit: a
continuation-pushing pre-pass makes every `match` terminal, `explore` enumerates
the derivations, and the lazy collapse is one scheduling of the
reorganization-closure premise. The relationship between the two is _not_ proved
complete, and one gap is ledgered: there is a rules-admissible ending order —
ending a live reborrow before the group it belongs to ends — that the
implemented order rejects when an issued payload is suspended. Soundness is
unaffected, because this is a _rejection_ and not an unsound acceptance; but it
is a strategy-completeness question that a full metatheory owes an answer to, and
it is recorded as such rather than glossed.

== What a proof must establish

The instruments and invariants above converge on a short list of obligations a
soundness proof of the machinery — as distinct from correctness of the pure
models, which is ordinary type theory — would have to discharge.

First, the _simulation relation_ of the differential must be proved, not merely
tested: that every accepted program's concrete runs are instances of its accepted
symbolic paths. Exhaustiveness is a precondition (now syntactic),
and one modelling choice is forced by the group-end over-approximation the
differential surfaced. The symbolic group-end releases each captured loan
atomically with a fresh existential, whereas concrete ending is lazy and
per-owner, so a symbolic environment can hold a released existential where the
concrete one still holds a suspended loan. A proof must reconcile these — either
by a fully-collapsed-at-observation hypothesis, or by letting a value still out
on loan stand as an instance of the existential — and the differential cannot
decide between them; the choice is the proof's.

The obligation is *two-sided*, and stating it one-sidedly would now be a known error.
It is tempting to phrase the whole relation as "the checker over-approximates the
machine", since every member of the divergence family did that until one did not
(@sec-polarity). A relation built on that assumption cannot express the case where
the re-mint _repairs_ execution rather than abstracting it, and would have to treat a
genuine machine defect as a soundness counterexample. Whatever form the relation
takes, it has to admit that the two sides can disagree in either direction and that
which one is wrong is not determined by which is coarser.

A second obligation the array era added is easy to miss because it is an obligation on
the _harness_ rather than on the calculus. Arrays are the first values whose state form
is coarser than their value — a carved-and-rejoined array holds a segment list where an
untouched one holds a run — so the simulation relation's array case is _defined_ by
splitting a concrete run along the symbolic extents. That is sound exactly when the
merge normalization preserves values. If it does not, the harness does not go red; it
goes silently _green_ on a mismatch. A nice-to-have on the obligation list has thereby
become a premise of the counterexample finder's own correctness, which is the thing to
know before trusting the differential over array bodies.

Second, _audit soundness_ — that a passed $arrow.r.curve$ audit implies the
caller's recovered value genuinely satisfies the obligation. The previous pin
qualified this obligation _modulo_ three named audit-strategy holes; two of them
were holes in the declared-`back` audit and are closed by that machinery's
deletion, and the paper declines to bank them as progress. Nothing was learned
about how to audit a declared specification correctly; the question stopped being
asked, and a soundness statement over this calculus simply no longer quantifies
over declared specifications because there are none. The third survives, and it
was re-verified in the source at this pin rather than carried over: the read/write
asymmetry on group-captured owners rejects a program the rules admit — a strategy
gap of the same kind as the ending-order one above, threatening completeness
rather than soundness.

What has replaced them on the frontier is narrower and sharper. Three positions
were found in which a stated claim would be judged by nobody, and each was closed
by making the position unwritable (@sec-boundaries). A proof owes an argument that
the three refusals are _sufficient_ — that no fourth position combines a skipped
check with a caller-side mint — and the paper has no such argument, only the
observation that adversarial probing found three in one campaign and stopped
because the campaign did.

Third, _recursion_. A self-call is admitted at the function's own declared return
type — signature-only checking forces that — so with no side condition the rule is
Hoare's recursion rule with its side condition deleted, and any false
postcondition proves itself. The previous pin closed that with a structural guard
in the kernel and listed the guard's well-foundedness as the proof obligation. The
guard is gone, and the obligation has moved rather than vanished. Two things now
carry it. Inside the kernel: that a recursive occurrence really is a _binder_ — the
recursor's induction hypothesis at the predecessor — so that there is no self-call
to guard, which is a statement about the eliminators and is as well-founded as
they are. Outside it: that the elaboration is _faithful_, that the recursor it
builds computes the function the source wrote. The kernel re-derives the term, so
this is not a soundness obligation on the checker; it is a correctness obligation
on a translation, of exactly the kind the case study's own architecture A was
built to avoid, arriving at the level below. The three refusals the macro makes
are the argument that it is faithful, and they are tests rather than a proof.

The honest summary is the one this section opened with: the checker is not
proved, but its behavior is instrumented, its central invariant is verified and
enforced at its source, its counterexample finders are validated against the bug
class they target, and the remaining gaps are enumerated rather than hidden. That
inventory is what a proof would start from, and stating it precisely is the work
this section claims to have done.

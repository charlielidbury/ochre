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
execution, in two generations. The first (`S8Diff`) tests the callee side. Its
property: _if `checkFn` accepts a declaration, then every small concrete run of
its body completes — is not stuck — and passes the concrete audit._ This is the
simulation theorem — the symbolic checker over-approximates concrete execution —
in the form of a bounded, exhaustively-checked `native_decide` proposition over a
generated enumeration of bodies. Across three telescopes it generates 136
bodies, of which `checkFn` accepts 75, exercised by 238 concrete runs; all
complete and audit, with no counterexample. Any accepted body with a stuck or
audit-failing instantiation would fail the `native_decide` and stand as a
soundness counterexample to be minimized and reported.

The second generation (`S9Diff`) upgrades to whole-program simulation, so that it
catches wrong-_value_ refinements and not merely stuckness. Its property: for
every `checkFn`-accepted caller, the caller's _concrete_ final environment (run
in executing mode, where calls run the callee's actual body) is a
$sigma$-_instance_ of some accepted _symbolic_ path's final environment (run in
checking mode, where calls use the signature rule). The instance relation is
first-order matching — a symbolic $sigma$ matches any concrete value
_consistently_ (the same $sigma$ maps to one value throughout), constructors
match structurally, loans and borrows up to canonical renumbering — which is the
simulation relation proper.

The essential part is not that these pass but that they have been _validated_: a
counterexample finder that has never found its counterexample is worthless as
evidence. The harness carries its own positive control. With the removed,
unsound `constrained`-wire inference forced back on, the `advance`-caller
differential goes _red_; with it off, _green_. The `advance` cursor shares the
signature of the identity-shaped `through` but writes only the tail, so the
constrained refinement — releasing the owner as the surrendered tail — is a
provably-wrong fact, exactly the bug class the relation is meant to catch. The
finder demonstrably catches its target when the target is reintroduced, and only
then.

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
$sigma$-context, the boundary obligations, the loan groups, the pinned return
type, and the reflected backward specs (@fig-boundaries) — because any component
that snapshots a $sigma$-typed thing at seed time and consults it later goes
stale otherwise. The _carry_ half: no substitution for a $sigma$ may contain a
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
tested: that every `checkFn`-accepted program's concrete runs are instances of
its accepted symbolic paths. Exhaustiveness is a precondition (now syntactic),
and one modelling choice is forced by the group-end over-approximation the
differential surfaced. The symbolic group-end releases each captured loan
atomically with a fresh existential, whereas concrete ending is lazy and
per-owner, so a symbolic environment can hold a released existential where the
concrete one still holds a suspended loan. A proof must reconcile these — either
by a fully-collapsed-at-observation hypothesis, or by letting a value still out
on loan stand as an instance of the existential — and the differential cannot
decide between them; the choice is the proof's.

Second, _audit soundness_ — that a passed $arrow.r.curve$/`back` audit implies
the caller's recovered value genuinely satisfies the obligation — but only
_modulo_ the audit-strategy holes the extraction has already named, which any
quantified statement must close. Two are known. A declared `back` on a call that
captures two or more borrows is silently ignored: the group end matches a
backward spec only against a single captured loan and otherwise degrades to
opaque _without rejection_, so a declared promise can go silently unused. And
both back checks take the first qualifying obligation and pass _vacuously_ when
none qualifies, so a declared `back` can go entirely unaudited on such a path.
These are holes in the audit's strategy, not in the pure models, and until they
are closed "audited" means less than it appears — a soundness statement that
quantifies over declared specifications must fix them first.

The honest summary is the one this section opened with: the checker is not
proved, but its behavior is instrumented, its central invariant is verified and
enforced at its source, its counterexample finders are validated against the bug
class they target, and the remaining gaps are enumerated rather than hidden. That
inventory is what a proof would start from, and stating it precisely is the work
this section claims to have done.

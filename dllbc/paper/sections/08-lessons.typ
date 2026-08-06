#import "../style.typ": *

= Lessons <sec-lessons>

Five methodological lessons carried more weight than any single rule in
building DLLBC. Each was earned against a wrong first guess, and each left a
mark on how the calculus is now developed.

== Measure before you architect

The final assembly's conformance check — the quicksort audit that closes the
case study — was, at first, unusable. A from-scratch build of the test suite,
under the `native_decide` kernel reduction that is the mechanization's
acceptance surface, took *38m49s* wall (2326s CPU), essentially all of it in
that one check.

The instinct was that the check re-examined the same enormous proof terms many
times, so it should be *cached*. Four content-addressed accelerations were
implemented and measured, and every one was a wash or worse. A coarse per-call
convert cache bought *no win* — the redundancy lived inside a single large
normalization, below the granularity a top-level memo can see. A per-node
structural memo of certified-rigid terms was a *wash* (33m41s CPU). Keying that
memo on pointer identity instead — hashing structural nodes is itself
$O("subtree")$ per probe, the very quadratic a cache is meant to remove — *made
it ~40% worse* (48m17s CPU): pointer identity misses the fresh structural
duplicates that substitution mints per occurrence, exactly the hits the
structural set had been converting into wins. Interning nodes at their
construction sites *recovered nothing* (49m11s CPU) and, worse, destabilized the
suite into a `SIGSEGV` across eight modules. The residual truth these four
negatives established is a general asymptotic one: on *unshared* trees,
content-addressed acceleration re-introduces the quadratic it targets, and no
addressing scheme repairs a cost that is *construction*, not lookup.

What did work was refusing to architect further and profiling instead.
`perf(1)`, run against a compiled bench harness that isolated the check from the
suite's elaboration (a two-minute iteration in place of forty), attributed *~93%
of all cycles to one line*: the eager de Bruijn re-lifting inside substitution.
The textbook recursion re-shifts the substituend at *every* binder it crosses —
$O("binders" times |"substituend"|)$ — and at quicksort scale the substituends
are $10^5$-node *closed* proof values, so each shift is a structurally-identity
rebuild ($"Val.shiftPure"$ alone was 62% of cycles, with ~28% more in the
allocator and reference-count churn on the copies). The repair was a 52-line
diff: carry the number of binders crossed and lift only at an actual occurrence,
skipping even that when the substituend is closed. The isolated check fell from
84,121ms to 181ms — *465×* — and the full suite from *38m49s to roughly 13
seconds*. The moral is not that caching is bad; it is that the four negative
results were *load-bearing*. They are what proved the cost was construction
rather than lookup, and so what pointed the profiler at the one line that
mattered. Architecture is the reward for a measurement, not a substitute for it.

The array era supplied the same lesson in a diagnostic register, and the shape is
worth recording because it transfers. A defect that made a verified program
unrunnable was attacked three times with three different mechanisms, and all three
failed; each failure was read as evidence that the problem was _architectural_ — that
the mechanism was wrong in kind rather than incomplete. The investigation twice wrote
down a conclusion a later probe refuted. What broke the loop was instrumenting the
failure to _name the dying borrow_ rather than reasoning further about the design,
after which the fault turned out to be one normalization firing at four independent
sites, each of them small. The rule extracted: *count sites rather than estimate
effort — each is small, and there is reliably one more than you think.*
"Architectural" is what a multi-site bug looks like from the inside when you are
estimating instead of counting.

== How the problem is posed is a performance decision

The lesson above is about the checker. Its sequel is about the _statement being
checked_, and it was measured after the profiler had already done its work.

The mechanization contains two direct-proving quicksorts. Both sort in place through
a `&mut List Nat` and both prove the same shape of postcondition — sortedness of the
exit snapshot, paired with count-preservation against the entry. The earlier is
_positional_: sortedness is a bounded $Pi$-predicate `SortedR cnt lo` over range
offsets, the pivot index is a pure `partIdxL`, every lemma is indexed by an offset
into the whole list, and the partition is a swap-based Lomuto scan over a range. The
later is _whole-list_: `Sorted` is a $Sigma$-chain down the spine, the partition
returns two lists, and the vocabulary is `count`, `append`, `take`, `drop`. The
positional check takes *21.8 s*; the whole-list one takes *21 ms* — same machine,
same checker, same build configuration, no performance work of any kind between
them.

The honest scope of that number needs stating, because it is easy to overclaim. The
two differ in _both_ the specification's encoding and the partition's program, and
the two differences are not independent: the positional specification exists because
a swap-based scan mutates a range in place, and the whole-list specification is what
makes a two-list partition natural. No experiment here isolates one from the other,
so the factor of roughly a thousand is a property of the _pair_ — of how the problem
is posed, program and statement together — and not a measurement of encoding alone.

What can be said about the mechanism is what the first lesson established: cost in
this checker is _construction_, and conversion is full normal-form equality. A
predicate indexed by an offset carries that offset's arithmetic into every subterm,
so positional normal forms are large; structural ones are small. Whatever the split
between program and statement, the difference is in the size of the terms conversion
must build, which is precisely the cost no cache and no addressing scheme repairs.
The architected next step at the time — $delta$-constants for the pure library, so
that proofs become constant-spines and checks scale with the program rather than the
proof — would have been aimed past this.

The design corollary is worth more than the number. The standing rule for this
calculus is _naturalness first_: write the program a systems programmer would write,
and if the checker rejects it, fix the calculus rather than the program. That rule is
usually assumed to trade efficiency for fidelity. Here it did the opposite — the
formulation one would use to explain the algorithm aloud is also the one the checker
finds cheap. When a verification effort is slow, how the problem has been posed is
worth suspecting before the engine that checks it.

== Run the differential at both extremes, and default to neither

The array era produced a testing rule sharp enough to state, and it came from noticing
that every defect which hid until late hid the same way.

`Array` values have two regimes. Extents can be _concrete_ — the lengths a first
milestone naturally writes tests at, because they let you print the answer — or
_symbolic_, which is what every program with a runtime-computed split point is made
of. The two exercise disjoint machinery. A carve at concrete extents rejoins to a plain
run and never needs the normalization that folds a segment list back to a value; a
symbolic segment cannot merge and always needs it. Conversely, a residue is never
_known_ to be zero symbolically, so the entire zero-extent path — four separate
defects — is unreachable in a symbolic suite and constant in a concrete one.

The consequence is that *every late-hiding defect in the era was invisible at one
regime and routine at the other*, in one direction or the other. The exit snapshot
arriving in the wrong form: invisible concretely. The carve failing to collapse a
suspended node: needs a recursive program, so invisible in a suite of straight-line
tests. All four zero-extent sites: invisible symbolically. Each suite was green
throughout while the other regime was broken, and neither suite was negligent.

So: *arrays need the differential run at both, and neither is the default.* The
generalizable form is worth more than the instance. Whenever a representation admits a
normalization that is justified on one class of values, the class it is _not_ justified
on is where the defects will be, and a test suite written in the natural style will
sit entirely inside the safe class without anyone choosing that.

== One negative test per rule branch, not per feature

Every genuine soundness bug the project has found was caught the same way: by a
*lying twin* — a program written to be rejected — that the checker instead
accepted, a negative test refusing to fail. There are three, and the lesson
sharpened at each one.

The first was a signature-inferred "constrained wire": at a call whose loan
group released a captured owner, the checker inferred the released value from
the surrendered field payload. But `through(b) = b` and an `advance` that steps
a cursor share a signature and differ only in body, so the inference let the
checker refine an owner to its own tail — unsound. The fix removed the inference
entirely; a captured release under an opaque call is now always a fresh
existential, and `through`'s lost precision is recovered only through a
*declared* backward spec.

The second bug exists because the first one's lesson was generalized. A declared
`back` was checked at the audit only on the *borrow-returning* branch of the
callee rule; a *value-returning* body's declared `back` was never checked at
all, and a lying `partScanL` variant passed clean. The lesson from the first bug
had been "test the feature"; the sharper statement it forced was *one negative
test per rule branch, not per feature* — and applying that statement is what
surfaced the unchecked value-returning branch, which was then closed as its own
audit (the zero-hole case, converting the declared spec directly against the
mutated argument's resolved suspension tree).

The third is the starkest, and it sharpened the statement once more. A call is
checked against a signature alone — recursion forces that — so a *self*-call was
admitted at the function's own declared return type with no side condition
anywhere. That is Hoare's rule for recursion with its side condition deleted, and
the lying twin is two lines long:

```rust
fn bad () -> Id Nat Z (S Z) { bad() }        // was ACCEPTED
```

Any false postcondition proved itself. The fix, at the time, was a declared
decreasing position `[k]` guarding the self-call. It has since been superseded by
something that is not a check at all — a definition is a `let`, a `let` is not in
scope in its own right-hand side, and `bad` therefore does not resolve
(@sec-boundaries) — and the supersession is worth a sentence here rather than only
there, because it is the clearest case the project has of a *hole closed twice, the
second time by making the program unwritable*. A guard is a rule that has to be
right; unwritability is a consequence of the scoping the language already had.
What is instructive is *why the hole survived so long in a corpus
with per-branch negative tests*: reaching it needs a declaration that is
recursive *and* back-less, and the corpus had many of each but never one that was
both — every recursive declaration carried a `back` whose conversion did the real
work, and every back-less one was a straight-line delegator. The hole sat in the
uncovered *square* of a two-feature grid, not on an untested branch of one rule.
So the statement generalizes again: *one negative test per reachable combination of
features*, which is a larger obligation than per-branch and the reason the
architecture comparison of @sec-architectures was worth building twice over — a
second architecture exercises combinations the first never forms.

The class has a fourth member, caught not by a test but by writing this paper.
Extracting the boundary rules from the implementation for @fig-boundaries surfaced
that both back-checks take the *first* qualifying obligation and pass *vacuously*
when none qualifies — so on such a path a declared `back` can go entirely
unaudited. The rule extraction was, in effect, another kind of negative test, one
that reads every branch of a rule by construction. It was never fixed: the
machinery it was a hole in has since been deleted, and the finding is recorded as
closed-by-deletion rather than closed. That distinction is the point of keeping it
here — a hole that stops existing because its feature stopped existing teaches
nothing about how to audit the feature, and a ledger that scored it as a fix would
be reporting progress the project did not make.

== The document is the single source of truth

DLLBC's calculus document and its mechanization were developed as one artifact.
The document's annotated environment traces *are* the test suite — each is a
golden final state, checked up to loan and symbol renaming — and every
milestone's report closed with a list of doc-vs-code ambiguities that were
folded back into the document the same day. When a coordination conflict arose
between a message and the document, the standing tiebreak was that *the document
wins*.

Two disciplines make this trustworthy. First, retractions are *logged, never
silently edited*. Three claims have been formally withdrawn in the progress record.
The "write order forced by the types" argument did not survive the switch to a
recursive-family encoding of vectors. A "convergence crux discharged inside the
checker" claim was false because the check it relied on did not run at the time —
its discovery is precisely the second bug above. And the *delegation discipline*
was withdrawn at this pin: the finding that an in-place leaf's exit is opaque, so
that every direct-proving body must delegate its mutation to a callee carrying a
pure model, was half wrong. Opacity belongs to borrows *issued by a call* — the
call rule mints their payloads as fresh existentials, having nothing in a signature
to say what they hold — and not to inline mutation at all. A leaf that does its own
cursor work through the body's *own* match-field borrows writes into a suspension
the audit itself collapses, so its exit is a constructor tree over known snapshots
and is fully provable. The retraction mattered: three features had been filed
forward on the strength of the wrong half, and two of them evaporated with it.
The inference had been reasonable from the evidence then available, which is the
usual shape of a retraction worth logging.

The array era added two more, and they differ in kind from the three above in a way
worth naming: they did not need _refining_, they _reversed_, and they are struck
through in the design note where they stood rather than quietly rewritten. That note
recommended carving inline and reaching for a function boundary only when abstraction
was wanted; the truth is the opposite, and a body following the advice cannot be
written at all. It claimed the migration would delete one stratum of reasoning,
inherit one, and invent none; one _is_ invented, at the partition's interface, because
a signature must describe a split that only the caller's carve can name. Both are the
same fact seen from two sides — carving is a within-body mechanism, and boundaries are
where its guarantees stop and start again — and neither was visible from the desk. The
discipline that makes them useful rather than embarrassing is the strike-through: a
reader can see what was believed, what replaced it, and that the replacement came from
running the thing. Second, the
rule-figure extraction for *this paper* functioned as an audit in its own right.
Reading the six figures out of the implementation, doc in hand, produced 20
recorded findings, several load-bearing: the vacuous back-audit paths above; a
`seq`-discard that drops an owning value without running `drop`, a real
semantics fork rather than the sugar the document claimed; and a comptime
`match` that today holds only through the recursor constants it would elaborate
to. Writing the paper found gaps the mechanization's own green test suite had
not — which is the strongest argument we have for keeping specification and
implementation close enough that either can audit the other.

The discipline has since been exercised three more times, and the later runs are
the better evidence. Re-extracting the figures against a later pin — the paper had
to be brought current after a second verification architecture landed — closed two
of those twenty and left the rest standing; the array era added a seventh figure
and its own findings; and the most recent re-extraction, after the calculus
collapsed its declaration form into an ordinary sealed binding, closed two more
_by deleting the machinery they were holes in_ and left exactly one of the
original three audit-strategy holes standing. Re-reading each _remaining_ finding
against the implementation rather than carrying it forward is what made the
difference between a ledger and a habit: the surviving hole was re-verified in the
source at the current pin, not assumed. The numbering is deliberately sealed to
the first extraction: findings are not renumbered when they close, because a claim
this paper made about its own audit should stay checkable against the audit it
made it about.

One artifact of that second pass deserves to be stated plainly, because it is the
cleanest evidence available that a paper about a moving mechanization decays
silently. *The quicksort listing in @sec-casestudy would have been rejected by the
checker it describes.* Between the two pins the recursion guard arrived, every
recursive declaration in the corpus acquired the `[k]` annotation that admits its
self-calls — and the paper's transcription of that declaration, correct when it was
made, quietly became a program the mechanization no longer accepts. It happened
again, in the same place, at the next pin but one: two declarations that had
recursed through a borrow's payload were rewritten to thread fuel when the guard
that admitted such a decrease was replaced by an eliminator that has no form for
it, and the paper's transcriptions of both went stale in the same silent way.
Nothing failed.
No test covered it, because the listing is prose; the extraction's findings ledger
did not catch it, because the ledger tracks _rules_ against the implementation and
this was a _quotation_ going stale. It was found by re-reading the source with the
listing in hand. The lesson is not that transcription is dangerous but that a
document is only as current as its last _verification_, and the interval at which
that must happen is set by the artifact, not by the writing.

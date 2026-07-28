#import "../style.typ": *

= Lessons

Three methodological lessons carried more weight than any single rule in
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

== One negative test per rule branch, not per feature

Both genuine soundness bugs the project has found were caught the same way: by a
*lying twin* — a program written to be rejected — that the checker instead
accepted, a negative test refusing to fail.

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

The class has a third member, and it was caught not by a test but by writing
this paper. Extracting the boundary rules from the implementation for
@fig-boundaries surfaced that both back-checks take the *first* qualifying
obligation and pass *vacuously* when none qualifies — so on such a path a
declared `back` can go entirely unaudited. The rule extraction was, in effect, a
fourth kind of negative test, one that reads every branch of a rule by
construction; it remains an open theory-line fix.

== The document is the single source of truth

DLLBC's calculus document and its mechanization were developed as one artifact.
The document's annotated environment traces *are* the test suite — each is a
golden final state, checked up to loan and symbol renaming — and every
milestone's report closed with a list of doc-vs-code ambiguities that were
folded back into the document the same day. When a coordination conflict arose
between a message and the document, the standing tiebreak was that *the document
wins*.

Two disciplines make this trustworthy. First, retractions are *logged, never
silently edited*: two claims were formally withdrawn in the progress record — the
"write order forced by the types" argument, which did not survive the switch to
a recursive-family encoding of vectors, and a "convergence crux discharged
inside the checker" claim, which was false because the check it relied on did not
run at the time (its discovery is precisely the second bug above). Second, the
rule-figure extraction for *this paper* functioned as an audit in its own right.
Reading the six figures out of the implementation, doc in hand, produced 20
recorded findings, several load-bearing: the vacuous back-audit paths above; a
`seq`-discard that drops an owning value without running `drop`, a real
semantics fork rather than the sugar the document claimed; and a comptime
`match` that today holds only through the recursor constants it would elaborate
to. Writing the paper found gaps the mechanization's own green test suite had
not — which is the strongest argument we have for keeping specification and
implementation close enough that either can audit the other.

#import "../style.typ": *

= Ownership across boundaries <sec-boundaries>

Inside a function body, borrowing is contract-free. The checker is a symbolic
interpreter running the very rules the program will run, so it simply watches
each move, write, and reborrow go by; no borrow needs to announce what it will
become, because the checker already knows. Contracts exist for the one thing the
checker cannot watch: *opacity*. There are exactly two opaque sites. A *function
boundary* is checked once, against a signature, and every caller sees only that
signature — never the body. And a *borrow stored under a type constructor* — an
element of `List (&mut T)`, a field of a pair — needs a type that stands on its
own, apart from the environment that would otherwise track it. Only at these two
sites does a borrow's type carry an obligation.

This section is the contract layer. It builds up in three moves: the shape of
the obligation (the #borrowT($s$, $tau$, $S$) type); how a call installs one and
later collects it (calls as wires, and then, when borrows entangle, as groups);
and how a body discharges it (the audit at return — the _single_ check in the
whole borrow story). The rules live in @fig-boundaries, the reorganizations they
lean on in @fig-reorg; we cite rule names and do not restate them.

== The obligation as interface

$ #borrowT($s$, $tau$, $S$) $

reads: exclusive access to a value of type $tau$, and across this boundary a
value of type $S$ is owed. The binder $s$ names the payload _at entry_, for use
in $S$ — which is checked at _exit_, when the entry payload is otherwise long
gone. The obligation is type-changing: $S$ need not be $tau$. A push signature

```rust
fn push (n : Nat, e : T, v : &mut (Vec T n ↝ Vec T (S n))) = …
```

tells the caller, from the signature alone, that the vector behind `v` is one
longer at exit. We write $amp"mut" (tau arrow.r.curve S)$ when $S$ ignores the
binder $s$, and plain $amp"mut" tau$ when moreover $S = tau$.

This is the paper's first inversion of the Aeneas pipeline, and the cleanest.
Where Aeneas _synthesizes_ a backward function per borrow — a pure function
describing what flows back through it — DLLBC moves that description into the
signature and makes it the programmer's to state: the $arrow.r.curve$ obligation
is the backward function's _type_ (#smallcaps[B-Seed-Borrow] installs it at
function entry, instantiating the binder $s$ at the entry snapshot). A
structuring observation, worth stating because it recurs in the case study: the
$Sigma$-paired presentation of a length-carrying vector, $amp"mut" Sigma (l :
"Nat"). "Vec" T l$, sidesteps $arrow.r.curve$ entirely — it owes back exactly
the type it received, the length change riding _inside_ the invariant type rather
than _across_ it. Both forms are legitimate; the $Sigma$ form buys an invariant
obligation at the price of carrying the index in the data, and $arrow.r.curve$
earns its keep when the changing index lives outside the borrow, in the
telescope.

*Snapshots in signatures.* A signature is a telescope: each argument's type may
mention earlier arguments. For borrow arguments, later types reach the payload
with the comptime deref $ast.op b$, evaluated ($arrow.r.squiggly$) wherever the
type is consulted, so it denotes the entry snapshot:

```rust
fn nth (b : &mut List T, i : Fin (len *b)) -> &mut T
```

Out-of-bounds is unrepresentable: `Fin (len` $ast.op b$`)` replaces the error
monad. The division of labor is exact — $ast.op b$ means _the payload now_
(projected wherever the type is read), while $s$ means _the payload at entry_
(bound once, for the one position that must outlive its moment). The projection
is sound precisely because this is a value semantics: a borrow _carries_ its
payload, so $ast.op ("borrow"_m ell space v) arrow.r.squiggly v$ is a pure
projection, never a store lookup and so never stale (its one proviso: a
suspended borrow, its payload mid-reborrow, has no meaningful snapshot, and the
projection is stuck until the reborrows end).

One convention the mechanization pinned down and #smallcaps[B-Seed] encodes: a
later parameter's type mentions an earlier argument by its _runtime variable_,
resolved to the snapshot by $arrow.r.squiggly$ each time the type is consulted —
the telescope performs no cross-parameter substitution at seed time. A pure
binder substituted eagerly at seed time would sit unsubstituted under
weak-head evaluation, read as a rigid neutral, and be mistaken for rigid at a
refl-match that should have seen it as flexible. The caller side mirrors this
(#smallcaps[B-Inst]): each checked actual is bound into the running
instantiation before the remaining parameter types are consulted, so `Fin (len`
$ast.op b$`)` at a call site means the `b` just passed. A practical corollary the
mechanization hit: because arguments are consumed left to right, a later argument
may not mention a borrow an earlier argument of the same call already consumed —
a bounds proof about $ast.op v$ must be `let`-bound _before_ the call that
consumes `v`.

== Calls as wires, then as groups

A call is checked against the signature alone — recursion forces this, the
checker cannot unroll a call to itself, and all calls get the same treatment
uniformly. The rule (#smallcaps[B-Call]) is: consume the arguments; for each
argument borrow, annotate its loan with the owed type from the signature,
instantiated at the actuals; mint a fresh symbolic result. In the simplest case
each returned or retained borrow corresponds to exactly one argument loan, and
the $arrow.r.curve$ obligation says everything — a *wire*. Ending a wire
(@fig-reorg, #smallcaps[G-EndOwed]) is where the caller learns what the callee
did: a fresh value arrives at the owed type, an existential opened at loan-end,
and _how much_ the caller learns is exactly how much the signature says. Under
$amp"mut"$ `List T`, only that a list came back; under the `Vec` signature above,
its precise new length. The spec is the type; precision is bought by
strengthening it.

Some functions break the one-borrow-one-loan correspondence:

```rust
fn choose (c : Bool, x : &mut T, y : &mut T) -> &mut T = match c { True => x, False => y }
```

The returned borrow points into `x` or `y` depending on `c`, and no per-borrow
promise can say which. Treating the loans independently is _unsound_: if `x`'s
loan could end while the returned borrow still lived, the caller would recover
`x` while an exclusive borrow into (possibly) `x` was still active. What must be
recorded is the *grouping* and an ending *order*. A call whose borrows entangle
mints a *loan group* (#smallcaps[B-Call]): a node tying the loans it captured to
the borrows it issued. Its whole content is its ending discipline (@fig-reorg,
#smallcaps[G-EndGroupOpaque]): every issued borrow ends first, then the group
ends atomically, releasing each captured loan with a fresh existential. The order
_is_ the soundness argument made structural — `x` cannot recover while the result
lives, because the group holds `x`'s loan and cannot end until the result's does.
A wire is simply the degenerate group, one captured and one issued, so the two
sections are one mechanism at two precisions.

This is where DLLBC pays for having _no lifetime annotations anywhere_. Rust ties
a returned reference to its inputs by naming lifetimes and threading them through
the signature; DLLBC names nothing. The loan group _is_ the tie, minted
automatically from the signature at the call, and the ending is demand-driven —
nothing in the program marks _when_ a group ends; a later demand for a captured
owner forces it. The honest cost is precision. A single group ties _all_ captured
loans to _all_ issued borrows and releases them together; a system with named
lifetimes could free a captured owner whose borrow provably never reached the
result, where the group must hold it until every issued borrow dies. The atomic
release also over-approximates the concrete dynamics, where each captured loan
ends only when its own owner is demanded — a symbolic environment can hold a
released existential where the concrete one still holds a suspended loan, an
obligation any simulation relation must reconcile (@fig-reorg records it). The
trade is deliberate: no annotation burden, the coarsest sound tie.

== The audit at return

The callee's side is symmetric, and it is the only check in the whole borrow
story. Before returning, every argument borrow must hold a value of its owed
type, verified by conversion (#smallcaps[B-Audit-Val], and its borrow-returning
reshaping #smallcaps[B-Audit-Borrow]). One step hides inside "holds a value": the
audit is itself a demand, and it _collapses first_. The suspension tree a
borrow-mode match built — field loans parked in the parent, unobservable through
the whole body because nothing before the boundary can demand them — is ended
here by #smallcaps[G-EndMut] (@fig-reorg), the boundary being the canonical demander of an
argument borrow that has no owner to demand it. Then conversion judges the
collapsed payload. The audit is _collapse-then-convert_: it assembles the final
value out of the body's strong updates, reassemblies, and holes, and checks the
assembled thing once, against the type the signature owes. A hole ($bot$)
satisfies no type, so a function cannot return one, and a broken invariant left
mid-body must be mended by here — a body may pass through any number of states
its signature could never describe, because the signature only ever speaks about
this one.

The return type itself is fixed at _entry_, while the parameters it may mention
are still live (#smallcaps[B-Pin]): a dependent return type over a consumed
parameter means that parameter's _entry_ value, since re-reading at return would
find $bot$. (One deliberate exception — a borrow parameter's payload deref in
the return type reading the _exit_ snapshot, with `old` as the entry operator —
is the propositional main line's central move, taken up in @sec-architectures;
the rules of @fig-boundaries follow the current implementation, which pins entry
wholesale, and flag the gap.) One admission rule rides along
(#smallcaps[B-ExFalso]): a branch whose result is an eliminator applied to a
verified inhabitant of $bot$ is dead, and the audit admits it at _any_ return
type — the $bot$-witness is the only thing checked. This is how a bounds-checked
cursor's `Nil` branch "returns" a borrow it cannot have: it does not, and need
not.

== Declared backward specs

Opacity is real: after a write through the result of `choose`, the caller cannot
prove which input received it — that is exactly what the group forgot. The
general remedy indexes precision by the status of the callee's _backward flow_,
what the group does at its end, and the trichotomy is the familiar one from proof
assistants. It may be a *parameter* — the opaque group above, an abstraction
boundary where the caller learns only types; a *definition* — transparent, the
flow being definitionally the callee's body, full precision, no annotation; or a
*spec* — a stated obligation, checked against the body and hiding the rest. This
document's core is the parameter case; the other two are sharpenings of the
group-end rule.

The spec case completes the Aeneas inversion. If $arrow.r.curve$ is the backward
function's _type_, a declared `back` is the backward function _itself_, moved
into the signature and audited against the body that claims to implement it,
rather than synthesized from it. The check is almost free, and for a structural
reason: the suspension tree the body actually built — the captured borrow's final
payload, with the issued loans' markers read as holes — _is_ the backward
function the body implements. Auditing the declaration is therefore one
conversion, the declared `back` applied to its holes against the resolved tree
(#smallcaps[B-BackN]). At the caller, a spec-carrying group ends by _computing_
each captured release — the declared back applied to the surrendered payloads —
instead of minting a fresh existential (@fig-reorg's #smallcaps[G-EndGroupBack],
consuming the spec that @fig-boundaries's #smallcaps[B-Call] instantiated). And composition falls out of the same resolution:
the tree resolves _through sub-calls' declared backs_, so a captured loan of a
sub-call resolves to _that_ call's back applied to its issued borrows — exactly
LLBC's backward-function composition, here as a checked declaration rather than a
synthesized term. Composition is all-or-nothing: a spec-carrying function's whole
call tree must be spec'd, since an opaque sub-group leaves an unresolvable marker
no spec converts against (recursion is fine — a recursive call resolves through
the function's own declaration).

That declared backs must be _audited_ and cannot be _inferred_ is the load-bearing
soundness fact, and it earns a statement of its own.

#block(stroke: 0.5pt, inset: 9pt, radius: 4pt, width: 100%)[
  *Backward flow is not a function of the signature.* Consider
  `through (b :` $amp"mut"$ `List T)` $arrow.r$ $amp"mut"$ `List T = b`, which
  returns its whole argument borrow, and an `advance` of the _same_ signature
  that returns a field reborrow of the tail. At the caller, the two demand
  different releases: ending `through`'s group should restore the owner to the
  value written through the result, while ending `advance`'s should restore only
  the field that was reborrowed and leave the rest. The signatures are identical;
  only the bodies differ. Any rule that reads a constrained backward flow off the
  signature is therefore unsound — and an early version of this calculus did
  exactly that, inferring the constrained wire from the signature, and was
  refuted by this pair. The correction is not a cleverer inference but a
  different discipline: backward flow must be _promised_ (a declared `back`) and
  _audited_ (#smallcaps[B-BackN] against the body). A promise the checker
  verifies is sound where an inference the checker guesses is not.
]

The audit has a value-returning dual, and stating it precisely matters because
its reach is limited. An in-place mutator that returns a plain value issues no
borrows, so its declared back is the _zero-hole_ case — the spec applied to no
holes, converted directly against the argument borrow's resolved suspension tree
(#smallcaps[B-Back0]). Until this dual was implemented, a value-returning body's
back went unchecked at its own audit; a lying variant of a partition scan passed
because only the borrow-returning branch ever looked. The lesson generalized to a
testing discipline — a negative test per rule _branch_, not per feature. The
dual's reach is precise: it checks a back authored _as the raw tree_ — a scan
that is literally the composition of its sub-calls' declared backs converts —
while a back that _reformulates_ the tree (a swap declared as $"swapL" i j
ast.op v$ against the set-based composition it actually implements: semantically
equal, never definitionally so) falls outside conversion's reach and is left to
the differential harness to validate. Complementary, not redundant. The
principled close is deferred: admit a reformulated back with a _cited bridging
equation_ and have the audit rewrite along the proved `Id`, so reformulation
becomes checked rather than trusted. #status("proposed")

== The precision spectrum, and its open holes

The spectrum — opaque parameter, checked spec, transparent definition — is the
organizing picture, and the checked parts of it are green in the mechanization:
the wire and opaque group ends, the $arrow.r.curve$ audit, and the declared-back
audit in both its borrow-returning and value-returning forms all discharge on the
test corpus. What a full soundness statement would additionally need is _not_ yet
green, and the extraction recorded three audit-strategy holes precisely so that
no soundness claim quantifies over declared specs before they are closed. Stating
them is a feature of this paper, not an embarrassment.

These three are current behaviors of the green mechanization, stated as the
limitations they are. First, a declared back on a call that captures _two or
more_ borrows is silently _ignored_: the group-end matches its spec branch only
against a single captured loan and otherwise falls through to the opaque arm,
degrading to an existential without rejecting. A declared promise silently unused
is a bug class — the fix is to reject or to support, never to drop. Second, there
is a read/write asymmetry on group-captured owners: _reading_ such an owner
demand-ends its group, but _overwriting_ it is rejected as in-flight, because
drop kills the captured borrow without routing through the group's ending. The
locatability phrasing that governs ordinary ends does not predict the split.
Third, and most soundness-relevant: both declared-back checks take the first
qualifying obligation and pass _vacuously_ when none qualifies — and the
value-returning check also passes when the argument borrow was consumed whole
into a sub-call, so a declared back can go entirely _unaudited_ on such a path.
None of the three is exercised by a current test; each is an identified hole in
the audit strategy that any
soundness statement over declared specs must close first. The conformance
architecture that @sec-architectures measures rests on exactly this declared-back
machinery, which is one reason the paper treats it as a baseline to be
scrutinized rather than a settled result.

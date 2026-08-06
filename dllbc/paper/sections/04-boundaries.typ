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
fn push (n : Nat, e : T, v : &mut (Vec T n ↝ Vec T (S n))) -> Unit { … }
```

tells the caller, from the signature alone, that the vector behind `v` is one
longer at exit. We write $amp"mut" (tau arrow.r.curve S)$ when $S$ ignores the
binder $s$, and plain $amp"mut" tau$ when moreover $S = tau$.

This is the paper's first inversion of the Aeneas pipeline @aeneas-2022, and the cleanest.
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
fn choose (c : Bool, x : &mut T, y : &mut T) -> &mut T { match c { True => x, False => y } }
```

The returned borrow points into `x` or `y` depending on `c`, and no per-borrow
promise can say which. Treating the loans independently is _unsound_: if `x`'s
loan could end while the returned borrow still lived, the caller would recover
`x` while an exclusive borrow into (possibly) `x` was still active. What must be
recorded is the *grouping* and an ending *order*. A call whose borrows entangle
mints a *loan group* (#smallcaps[B-Call]): a node tying the loans it captured to
the borrows it issued. Its whole content is its ending discipline (@fig-reorg,
#smallcaps[G-EndGroupOpaque]): every issued borrow ends first, then the group
ends atomically, releasing each captured loan at its owed type and nothing more.
The order _is_ the soundness argument made structural — `x` cannot recover while
the result lives, because the group holds `x`'s loan and cannot end until the
result's does.
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

*Self-calls need a side condition — and then they stopped needing one.* Checking
a call against the signature alone has one consequence that is invisible until a
return type carries real content: a _self_-call is admitted at the function's own
declared return type. That is Hoare's rule for recursion with its side condition
deleted, and under a propositional postcondition every false postcondition proves
itself (@sec-lessons gives the two-line witness). For most of this calculus's
life the side condition was a _declared_ decreasing position `[k]`, checked
structurally against the parameter's current snapshot — cheap, because a symbolic
interpreter already holds that snapshot, and inside `match n { S(m) => … }` it is
already `S` $space sym("m")$ while the actual is $sym("m")$.

At this pin there is no such rule, and the reason is worth more than the rule
was. A definition is no longer a table entry but a `let` binding a sealed λ
(@fig-boundaries), and *a `let` is not in scope in its own right-hand side*. So
`fn bad () -> Id Nat Z (S Z) { bad() }` — the witness that made the guard
necessary — is not rejected by a side condition; it fails to resolve, exactly as
any other forward reference does. Mutual recursion falls out identically: `f`
$arrow.r$ `g` $arrow.r$ `f` needs `f` to name a binding below it, and there is
none, so the call-graph reachability check that used to catch it has nothing left
to catch. Genuine recursion, meanwhile, is not a call at all: `fn` elaborates a
recursing definition to a *recursor* whose arms are the body, with each self-call
rewritten to an application of `ih`, the sealed self-view at the predecessor.
A binder cannot be a self-call, so there is no premise for a side condition to
guard, and the decrease is the eliminator's.

What this trades is stated plainly, because it is a real trade and not a free
win. The obligation moved _out_ of the kernel and into the elaboration: `ih` is
the self-view at the *predecessor*, so rewriting a self-call into one is honest
only when the call recurses on the predecessor, and the macro must refuse
otherwise. It does — a self-call at any other argument, a self-call in the base
branch, and a decrease through a borrow's *payload* (which has no recursor form
at all) are all refused, each with a distinctive sentinel the checking path then
surfaces. The kernel re-derives everything about the elaborated term, so the
macro is not in the trusted base for _soundness_; what it is trusted for is
_faithfulness_ — that the function checked is the function written. A macro that
silently rewrote a non-terminating source into a terminating recursor would
produce a term that checks and a claim about a different function, and the
corpus's rejected witnesses (`recSame`, `recWrongIdx`, `recGrow`) exist to pin
that it does not.

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
find $bot$. One position is deliberately excepted, and it is the propositional
main line's central move (@sec-architectures): a _borrow_ parameter's payload
deref reads the *exit* snapshot, with `old` $ast.op v$ as the entry operator. The
justification is the loan structure itself — with no lifetimes the callee's access
ends exactly at the audit, which already computes the collapsed final payload, so
"the value at the end" names one well-defined tree — and caller-side the call
mints one symbolic value shared between the loan's eventual release and the
returned evidence's subject, so a returned proof _attaches_ to the recovered
value. Both readings are implemented at this pin; earlier versions of these rules
pinned entry wholesale and flagged the difference as a gap. One admission rule
rides along
(#smallcaps[B-ExFalso]): a branch whose result is an eliminator applied to a
verified inhabitant of $bot$ is dead, and the audit admits it at _any_ return
type — the $bot$-witness is the only thing checked. This is how a bounds-checked
cursor's `Nil` branch "returns" a borrow it cannot have: it does not, and need
not.

== The spectrum, and the tier that was removed from it

Opacity is real: after a write through the result of `choose`, the caller cannot
prove which input received it — that is exactly what the group forgot. The
general remedy indexes precision by the status of the callee's _backward flow_,
what the group does at its end, and the trichotomy is the familiar one from proof
assistants. It may be a *parameter* — the opaque group above, an abstraction
boundary where the caller learns only types; a *definition* — transparent, the
flow being definitionally the callee's body, full precision, no annotation; or a
*spec* — a stated obligation, checked against the body and hiding the rest.

For two of this calculus's three eras the spec case was implemented, and it
completed the Aeneas inversion the cleanest way available: if $arrow.r.curve$ is
the backward function's _type_, a declared `back` is the backward function
_itself_, moved into the signature and audited against the body that claims to
implement it. The check was almost free, for a structural reason worth recording
even now — the suspension tree the body actually built (the captured borrow's
final payload, with the issued loans' markers read as holes) _is_ the backward
function the body implements, so auditing a declaration was one conversion. LLBC's
backward-function composition fell out of the same resolution, a captured loan of
a sub-call resolving to that call's own declared back.

*The spec tier has been removed from the language.* Not deprecated within it: the
surface `back = …`, the declaration field, the group's spec-carrying end, the
resolution function and both callee-side checks were deleted. The ratified
position is that the *ensures is the contract* — what a caller keeps is what the
callee ascribed, and nothing else — so the precision a declared back bought is
either bought by the $arrow.r.curve$ obligation and a $Sigma$-pinned return type,
or not bought at all. Two things make that affordable, and neither existed when
the spec tier was designed. A call's return type may now be a dependent $Sigma$
whose tail mentions the components already built (#smallcaps[B-Res-Pair]), which
is how a callee states a postcondition about the value it returns. And the group
end now releases a captured owner to *the same symbolic value the returned
evidence is about* — one σ′ minted at the call, read by the return type's exit
$ast.op v$ and pinned as that loan's release (@fig-reorg) — which is what makes a
returned proof attach to the recovered owner rather than float beside it.

The removal is a genuine loss of expressiveness in one direction and a gain in
another, and @sec-architectures is where the two are measured against each other
rather than asserted. What survives intact is the *principle* the spec tier was
the first application of, and it earns a statement of its own because it has
since decided a case it was not written for.

#block(stroke: 0.5pt, inset: 9pt, radius: 4pt, width: 100%)[
  *Backward flow is not a function of the signature.* Consider
  `fn through (b :` $amp"mut"$ `List T) ->` $amp"mut"$ `List T { b }`, which
  returns its whole argument borrow, and an `advance` of the _same_ signature
  that returns a field reborrow of the tail. At the caller, the two demand
  different releases: ending `through`'s group should restore the owner to the
  value written through the result, while ending `advance`'s should restore only
  the field that was reborrowed and leave the rest. The signatures are identical;
  only the bodies differ. Any rule that reads a constrained backward flow off the
  signature is therefore unsound — and an early version of this calculus did
  exactly that, inferring the constrained wire from the signature, and was
  refuted by this pair. The correction is not a cleverer inference but a
  different discipline: backward flow must be _promised_ and _audited_, never
  guessed. A promise the checker verifies is sound where an inference the checker
  makes is not. (The promise this argument produced — the declared `back` — has
  since been removed for unrelated reasons, above. The argument is unaffected: it
  rules out _inference_, and says nothing about which of the surviving promises a
  signature is made of.)

  *The principle has since decided a case it was not written for.* The array era's
  carve (@fig-carve) must decompose a segment's extent, and where that extent is a
  telescope parameter's symbolic value, solving the decomposition by refinement
  silently constrains the function's _callers_ — a body carving `[Z ; i ; S j]` out of
  `Array n` was accepted, and so was a caller passing $n = 2$ with $i = j = 5$, which
  execution then got stuck on. Different mechanism, different milestone, same sin:
  a body imposing a cross-boundary constraint that its signature does not record.
  The ruling followed from the precedent rather than from fresh analysis — the carve
  may not refine a parameter's extent, and must instead have the decomposition hold by
  conversion or _cite_ it as a checked equation. What makes the precedent worth stating
  as a principle rather than a fix is that it arrived pre-argued for a rule nobody had
  imagined when it was set.
]

== Three positions made unwritable

The spec tier's removal pointed the whole language at ensures-carrying signatures,
and doing that walked into three positions where a claim would be _stated_ and
_judged by nobody_. All three were found by adversarial probing rather than by a
failing corpus program, and all three are closed by *refusal* rather than by a
new check — which is the honest move where the thing a check would examine is a
value the checker itself just minted.

First, a return type may not mix borrow and value components. A borrow-carrying
return type is audited structurally — each issued borrow against its owed type —
and the value check is skipped for the whole type, so a non-borrow component of
such a type is judged by nothing. That is unsound, not merely imprecise: the
caller mints a symbolic value at the stated leaf type regardless, receives the
unearned claim as a proof, and may return it at its own value return type, where
the checking path does run and passes. The witness is a nullary function returning
$bot$. Second, a borrow consumed into the result must owe back what it was lent.
The audit exempts such a borrow — correctly, since it has no payload here to
audit — and the exemption takes the owed _type_ with it while the caller's group
end mints the release _at_ that type, so a non-trivial $arrow.r.curve$ on a
consumed parameter is checked at neither end. A cursor that hands its borrow
onward owes back the type it was lent; a richer claim belongs on a parameter the
body keeps. Third, a function may not be read out of its slot into a second
binding. This one is a statement about the model rather than a patch: functions
are reached by *name*, so calling where bound and passing as an argument are
name-uses, while reading one into a second binding is the move that turns a name
into a value. It was found as a mechanism defect — a borrow-taking function's
symbol has no value form, so the checker moved it where the concrete machine
copied it, a simulation break on a program *both machines accept* — and then
deliberately generalized past its mechanism, refusing the borrow-free case too,
which had been measured as sound. Soundness was never what made it wrong.

Two of the three are worth noticing as a pattern rather than as three fixes: a
mechanism that _skips_ a check for a good local reason (the borrow audit does not
run `hasType`; the exemption does not audit a payload) will silently skip
everything else that rode on it, and the caller-side mint is what turns the
silence into a proof.

== Opacity, twice discovered to be doing work

Everything above treats opacity as a cost: the thing contracts exist to compensate
for, and the reason a caller learns only what a signature says. The array era found it
twice in the opposite role, and both times the finding inverted a claim this project
had written down.

The first is @sec-polarity's: a call re-mints the callee's payload at the declared
type, and that re-mint turned out to _repair_ an executing machine that had lost the
structure its borrows were pinned to. Forgetting was correct and remembering was
broken.

The second decides a program's shape. A body that peels an element must first match
its own length, which rigidifies the extent; but a rigid extent cannot then be carved
at a symbolic offset. So one body cannot both choose a split point and carve at it —
not as a transparency-versus-abstraction trade, but as a dead end. The way out is a
function boundary, because the re-mint hands the array back _uncarved and with a flex
length_, which is exactly the state a carve needs. The array partition is a separate
declaration for that reason and not for modularity, and the design note's own advice —
carve inline, reach for a function only when you want abstraction — was withdrawn
rather than qualified.

The corrected statement generalizes past arrays: *carving is a within-body mechanism,
and function boundaries are where its guarantees stop and start again.* Cross a
boundary to change rigidity regimes. That a calculus's opacity mechanism should be
load-bearing for expressiveness, rather than only for modularity, is not what
@sec-architectures's framing would predict, and it is worth holding onto as a caution
against reading opacity purely as loss.

== The open hole, and the two that closed by deletion

The spectrum — opaque parameter, checked spec, transparent definition — was the
organizing picture, and the paper's previous pin recorded *three* audit-strategy
holes in it, precisely so that no soundness claim would quantify over declared
specs before they were closed. Two of the three were holes in the declared-spec
machinery, and they are closed at this pin *by its removal*. That is a weaker
result than a fix and the paper says so: a declared back on a call capturing two
or more borrows can no longer be silently ignored, and a declared back can no
longer go vacuously unaudited, because there is no declared back. Nothing was
learned about how to audit one correctly; the question stopped being asked.

The third is not in that class, and it survives untouched. There is a read/write
asymmetry on group-captured owners: _reading_ such an owner demand-ends its
group, but _overwriting_ it is rejected as in-flight, because drop kills the
captured borrow directly instead of routing through the group's ending. The
locatability phrasing that governs ordinary ends does not predict the split. It
is a rejection rather than an unsoundness — a completeness gap — and it is
re-verified rather than carried over at this pin: the two paths still reach
different functions.

What has replaced the closed holes as the live soundness frontier is the
containment discipline of the preceding subsection. Three positions were found
where a stated claim would be judged by nobody, and each was made unwritable; the
honest reading of that is not that the boundary layer is now airtight but that
adversarial probing found three in one campaign, and the mechanism they shared —
a skipped check plus a caller-side mint — has no argument yet that it has no
fourth instance. @sec-empirics states what the differential does and does not
cover here, and @sec-architectures no longer rests on the declared-back machinery
at all, which changes what it is measuring.

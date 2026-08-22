# Plan: point hovers — what the checker knew *here*

**The design, in one sentence.** *A tooltip shows what the checker knew when its
cursor was where your cursor is.*

Everything below is a consequence of taking that sentence literally, and the
parts that look like machinery are mostly parts where the sentence had to be made
precise about "when" and "where".

**What exists already.** `docs/16` shipped hover types at BINDER granularity: one
fact per binder, recorded at `letStep`, joined against occurrence spans. It
works, it is merged, and this plan does not discard it — see §8, where it becomes
one sampling site of the general mechanism rather than a mechanism of its own.

**What is wrong with binder granularity, in one specimen.** `docs/16`'s pinned
case (12):

```
let b = &m x;          -- b ≡ borrowₘ ℓ0 (Cons (S Z) Nil)
*b := Cons(2, Nil);    -- the payload changes
let d = *b;            -- d ≡ Cons (S (S Z)) Nil    ← Ω as it is now
                       -- b ≡ borrowₘ ℓ0 (Cons (S Z) Nil)  ← Ω as it was at the binding
```

Two tooltips on one line disagree about the same memory. Under `docs/16` both are
correct and the disagreement is documented honestly. Under THIS plan the second
one is a bug, and fixing it is the acceptance criterion (§9): hovering `b` below
the write must show the payload the write put there.

---

## 1. Immutable point-facts

**A fact is recorded against a point and is never edited afterwards.** When
refinement narrows a σ, that is a new fact at a later point; the earlier fact
stays exactly as it was.

This is not a simplification, it is the correct semantics. A fact recorded at
point P is a claim about what the checker knew AT P. Retroactively rewriting it
to reflect what was learned at Q > P would make it a claim about something else —
it would *falsify history*, and it would do so precisely in the cases where the
history is what the reader is asking about (why did this branch reject; what did
the checker think here). The tooltip's whole value is that it answers about a
place, and a place-answer that silently reflects a different place is worse than
no answer.

It also gets the ergonomics right for free, which is the sign that the principle
is the real one. A reader hovering an occurrence BELOW a narrowing sits at a
later point, so they pick up the narrowed fact by construction. Nobody has to
special-case "show the refined type here" — the point does it.

`docs/16` already holds this principle at coarser grain and says so: binding-time
honesty. This plan is the same principle at finer grain, and case (12) is the
specimen that connects them.

## 2. Where facts are recorded: the mutation primitives

Facts are recorded **at the primitives that mutate the checker's state**, tagged
with the breadcrumb current at the moment of the mutation. Not at walkers, not at
boundaries.

That choice is what makes §3's carry-forward sound rather than approximate, and
the argument is in §3. What matters here is that the set is small and known.

**Ω funnels through eleven primitives**, and the codebase already enumerates them
for an unrelated reason — `St.scopeMarks`' docstring, which needs the same list to
argue that a watermark index survives a drop sweep:

> "Every Ω-writing primitive preserves the invariant (`bindSlot` appends;
> `setSlot`, `writeC`, `refineSym`, `killBorrowInΩ`, `sendPayloadToLoan`,
> `endIssued`, `mergeRoot` all `map` over Ω and so are length- and
> order-preserving) … **The one site that is neither** is `readCWith`, which
> APPENDS a callee's actuals and restores Ω exactly before returning."

**That enumeration was checked against the code and holds** (audit, this lane's
charter round). Ten sites write `St.env`; one is the general setter `setEnv`,
whose only callers are `setSlot`, `killBorrowInΩ`, `sendPayloadToLoan`,
`endIssued`, `popScope`; the direct writers are `bindSlot`, `refineSym`,
`cookForGen`, `abstractInto`, `readCWith`, `checkRFnBody`'s seal wipe, and
`initSt`.

**Having a second reader is the point.** A list maintained only for this feature
would rot silently. This one is load-bearing for the scope-watermark invariant
too, so a primitive added without joining it breaks something else first.

**`sctx` has exactly two mutating sites**, and that is §3's subject.

## 3. Carry-forward is sound, and the argument is smaller than it looks

The obvious objection to point-facts: they are **sparse** (recorded where
something happens) while identifier occurrences are **dense** (everywhere). So an
occurrence usually sits at a point with no fact of its own, and showing the most
recent preceding fact is an INTERPOLATION — exactly the guess that `docs/16`'s
decline-don't-guess property forbids.

The answer is that it is not an interpolation if nothing can change between two
recorded facts. Recording at every mutation primitive makes that true **by
construction**: between consecutive facts, no primitive ran, so the state is the
same state. Carry-forward stops being inference and becomes the definition of
"the state here".

That reduces soundness to *"the primitive list is complete"* — a checklist-shaped
invariant, and this corpus's own history says enumerating mutation sites is where
silent bugs live. Two things make it tractable, and the second is the one that
matters.

**(i) The list is two greps, not a survey.**

* Every `St.env` write goes through the eleven primitives of §2.
* Every `sctx` write is a fresh-σ cons, one of two sweeps, or a seed.

**(ii) 26 of the 29 `sctx` writes CANNOT falsify an earlier fact, so they need no
instrumentation at all.** Measured on the tree at `b4e971e7`:

| `sctx` writes | count | can it falsify an earlier point-fact? |
|---|---|---|
| cons of a **fresh** σ — `(σ, τ) :: s.sctx` | 26 | **no** |
| rewrite of existing entries — `refineSym` (M:1290), `abstractInto` (M:1336) | 2 | yes |
| `seedPure`, an entry-point constructor | 1 | n/a |

The reason is §1 recursing one level down into the implementation: **a fact
recorded at point P mentions only σs that existed at P**, so a σ minted after P is
invisible to it and adding one cannot change what it says. Monotone growth is not
mutation for this purpose.

So the checklist is two sweeps plus eleven Ω primitives — not twenty-nine plus
eleven. The gate opens on that.

**The failure mode is bounded, and that is why the gate opens rather than merely
narrows.** An incomplete list yields a STALE tooltip — the reader sees the last
recorded fact instead of the current one — corrected at the next recorded fact.
It cannot produce a false rejection, because none of this is read by any rule. A
checklist whose worst case is "briefly out of date" is a different risk class from
one whose worst case is "wrongly rejects a program".

**It ships as an assertion, not as a claim.** The audit above is a grep over one
day's tree; it is a snapshot, not a theorem. The lane ships an `sctxWrite`
helper that makes the fresh-σ addition the only spellable form and the two sweeps
explicit, so the invariant is enforced where it is stated rather than re-verified
by whoever next reads this file.

## 4. The key: `(breadcrumb, arm-trail, binder)`

A point is not a source position. It is a position **on a path**, because a
statement inside a recursive body is walked many times in different states, and
those are genuinely different points with genuinely different facts.

So the key is the breadcrumb (which statement or argument), the arm trail (which
branch choices got here) and the binder. All three already exist — the breadcrumb
and the trail are `docs/05`'s, built for error localization and maintained at
`letStep`/`assignStep`/`seqStep`, `processArgs` and the four arm entries.

**`(differs per path)` does not retire, it gets finer**, and this plan must not
be sold as removing it. Under binder granularity a σ that refines per branch
produces one binder with several facts. Under point granularity it produces one
POINT with several facts — one per path reaching it — which is fewer collisions
per key but more keys, and the suffix stays for the cases that remain. Expect it
to appear MORE often in absolute terms and to mean something sharper when it
does: not "this binder is ambiguous somewhere" but "these paths disagree here".

## 5. Pattern binders and match narrowing, by construction

`docs/16` files two limits, and both dissolve here rather than being fixed:

* **Pattern binders get no tooltip** because they are bound by the match rather
  than by `letStep`, and `letStep` was the only recording site. Under §2 the
  recording is at the mutation primitives, and an arm entry binds through
  `writeC`/`mintFieldSyms` like everything else — so pattern binders are recorded
  because they are state changes, not because anyone added a case for them.
* **Narrowing is invisible** because a binder had one fact and refinement did not
  update it. Under §1 refinement produces a new fact at a later point, and an
  occurrence below the arm entry reads it.

Neither is a feature this plan adds. They are consequences of moving the
recording site, which is the sign that the move is the right one.

## 6. `fn` names need no table of their own — VERIFIED

**The claim.** A `fn` lowers to an ordinary comptime `let` binding a SEALED body
(`docs/10`, functions-are-comptime), and in checking mode the seal yields a σ
typed by the signature. So a `fn` name's binding-time fact is an ordinary σ fact
and the general `x : τ` form covers it, with no signature table.

**Verified against the code rather than assumed**, since it is a premise about
what the machine holds. Probing `checkProgramHover` on
`fn F (b : Bool) -> Unit { let c = b; () }; let r = F(True); ()` gives:

```
binder=(id 1, c)                ty?=(some Bool)                  val=σ0
binder=(id 281474976710654, F)  ty?=(some (Π(§0 : Bool). Unit))  val=σ1
binder=(id 0, r)                ty?=(some Unit)                  val=σ2
```

`F` is there, at the `declSlot` id, carrying its signature as an ordinary σ type.
The claim holds and the special case can go.

**One thing it costs, and the plan says so rather than discovering it later.**
The general form would render `F : Π(§0 : Bool). Unit`. The shipped S1 form
renders `F : (b : Bool) -> Unit`. The parameter NAME is gone — `§0` is
`readbackName`, generated at readback, so `b` is not recoverable from the lowered
Π. That is a real regression in a tooltip a reader looks at often.

So the unification is structural, not presentational, and the plan takes it that
way: **one lookup, and a rendering hint for `fn` bindings.** The surface already
holds the source text at the `fn` row; keeping it as *how to render this fact* is
not a second source of truth, because the fact still comes from the checker and
the hint cannot change what is shown to be a different fact. That is the
distinction the shipped `fsigs` map failed to draw and this plan draws: `fsigs`
was a parallel ANSWER; the hint is a parallel SPELLING of the same answer.

The static complement therefore shrinks to true globals — kernel vocabulary and
lemma constants, which are not let-bound, not state, and answer by constant
lookup.

## 7. What this does NOT change

`Term`/`Val` unchanged. Accept/reject unchanged — nothing here is read by any
rule, and `checkProgramDiag`/`checkProgramHover` stay the same walk sharing
`programPaths`/`programVerdict`. No new monad layers. No test assertion changes.
Decline-don't-guess is preserved and strengthened: an occurrence with no fact in
scope shows nothing, and §3 is the argument that "in scope" now means what it
says.

## 8. Supersession: `docs/16` is absorbed, not replaced

`letStep`'s table becomes **one sampling site of the general recording** — the
binding-time fact, which is still the fact a binder's own occurrence wants. The
three tooltip forms (`x : τ`, `x ≡ v` comptime-known, `x ≡ v` binding-time shape
with inline σ types) are unchanged and carry over verbatim; what changes is WHICH
fact an occurrence selects, not how a fact is rendered.

Concretely, `docs/16`'s 37 pinned positions should keep their expected outputs
except where a point genuinely differs from a binding — and the diff between the
two files is therefore itself a test: any case that changes without a stated
reason is a regression.

## 9. THE GO/NO-GO: cost, measured before the surface work

**This is the one thing that can sink the lane, and it is measured first.**

Recording hangs off `refineSym`, and `refineSym` fires during ARRAY PLACE
EVALUATION — `carveAt`/`carveBody`/`elementize` — not only at arm boundaries
(established in the charter round, against an initial premise that said
otherwise). That is the hot path of the flagship. `docs/16`'s recording was one
cons per `let`; this is one record per refinement in array-heavy code, which is a
different order of frequency.

**The measurement, before any surface work**, and the protocol has to match the
COST SHAPE rather than be inherited:

> **A distributed cost is measured per module; a concentrated cost needs a
> harness aimed at the checker.** `docs/16`'s cost was spread over every block it
> elaborated, so per-module timing suited it. This one is concentrated in the few
> blocks that actually check — 18 of 279 in the flagship — so per-module timing
> dilutes it below noise and reports nothing either way. Reusing the inherited
> protocol here produced two uninformative readings before the mismatch was
> noticed.

Reported as a checkpoint before implementation continues.

**Doctrine, earned here rather than quoted:** *a number that flatters beyond
plausibility is a bug in the harness until proven otherwise.* This harness
reported 0 ms for 20 array-flagship checks, which is not a fast result but an
impossible one.

**The REPLAY cost is deferred, not deleted.** §2's O(1) delta moves work from
recording to reading: recovering a binder's fact at a point means replaying the
deltas up to it. That is the join's cost, it is paid per hover rather than per
check, and it lands in the final measurement table as its own line — otherwise
the lane's cost claim covers one end of the design and calls it the whole.

> **THE REPLAY ROW, FILLED — and it forced a design change.** Measured on the
> array flagship (433 deltas, 433 keyed statements): 89 212 replays in 359 977 ms,
> i.e. **≈4.0 ms per replay**.
>
> Four milliseconds is nothing for a hover and a great deal for a hundred of
> them. The first implementation built every tooltip EAGERLY at elaboration, so a
> block with a hundred occurrences would have paid ~400 ms to compute text nobody
> asked for — the recording end free and the reading end quietly charged to the
> build.
>
> **`mkDocString?` is a thunk, and this is what it is for.** Its own
> documentation says "computed only when it is used"; the text is now built
> inside the closure, so a hover costs one replay and a non-hover costs nothing.
> Re-measured after the change, elaboration with point recording ON versus OFF:
> `Tests/Direct` 5355 ms against 5384, `Tests/ArraySort` 13481 against 13467 —
> noise in both directions, as with the recording end.
>
> So the completed claim is: **recording is free, reading is ~4 ms and lazy.**
> The docs/16 mechanism note said the laziness was "better than hoped"; it turns
> out to be load-bearing rather than a bonus, and a design that computed tooltips
> eagerly would have been the wrong one all along without anyone noticing at
> binder granularity, where a fact was a table lookup.

Gated behind an option (`dllbc.pointHover`) exactly as `dllbc.hover` is, for the
same reason: this is the part collected on the SUCCESS path, so "what does it
cost" must stay answerable rather than being settled once.

**If it is expensive, the lane's answer is not to optimize first.** The honest
fallbacks, in order: sample at breadcrumb changes rather than at every primitive
(cheaper, and turns carry-forward back into an interpolation — so it would have
to be stated as such); or keep binder granularity for values and point
granularity only for σ types; or stop, and leave `docs/16` shipped. Deciding that
with numbers in hand is the checkpoint's job.

> **CHECKPOINT RESULT — GO. The recording is free at corpus scale, and the first
> two ways of measuring it were both wrong.**
>
> **The number that answers the question.** `Tests/PointCost`, timing the
> checker directly on the two flagships, 50 checks each:
>
> | program | recording off | recording on | Δ | deltas per check |
> |---|---|---|---|---|
> | array flagship (`S25ArrSort.arrChain`) | 19761 ms | 19703 ms | **−58 ms** | 433 |
> | list flagship (`S23Direct.flagship`) | 8414 ms | 8448 ms | **+34 ms** | 239 |
>
> That is 395 ms and 168 ms per check, and the deltas cost nothing measurable —
> one figure negative, one positive, both about 0.3%. 433 deltas against a 395 ms
> check is not a cost, and the O(1)-delta shape (§2) is why: the swept Ω is never
> recorded, only the σ and its replacement.
>
> **FIRST WRONG MEASUREMENT: per-module elaboration timings, which measure the
> wrong thing on today's corpus.** `docs/16`'s protocol was applied first —
> `Tests/HashMap` and `Tests/ArraySort`, recording on vs off — and reported
> +1.15% on HashMap, then nothing on a repeat. Both readings are uninformative,
> because **`Tests/HashMap` has 261 `prog_parse` blocks against 18 checked
> ones** and records 431 deltas in the whole module; `ArraySort` records 253. Those
> modules' minutes are `native_decide` and compilation, not elaboration-time
> checking. A protocol that was right for `docs/16` — whose cost was spread over
> every block — is wrong here, where the cost is concentrated in the few blocks
> that actually check.
>
> **SECOND WRONG MEASUREMENT: the harness timed nothing.** `let r := f ()` is a
> lazy binding, so the timed region built a thunk and the work happened later,
> inside the `println`. It reported **0 ms for 20 array-flagship checks** — a
> number that should have been rejected on sight and instead was briefly believed.
> The tell was a follow-up run at N=5000 taking twenty minutes at 99% CPU for work
> that had supposedly cost nothing. `IO.lazyPure` forces inside the timed region;
> the harness says so at its head.
>
> **AND THE SEAL ATE THE DELTAS, on the third channel in a row.** The first
> instrumented run reported **1 delta** for a program with a three-statement `fn`
> body. `checkRFnBody` discards the sealed body's state, so everything inside any
> function was being dropped — and every earlier measurement was therefore an
> undercount of an already-uninformative number. Fixed as `letTypes` was, carried
> out by `auditAllPathsD` with its own base length; the same program then reported
> 4.
>
> This is the door `docs/16` documents and names, written up by the same author
> who then walked into it again on the next channel. **A signpost its own author
> misses is not working as a signpost**, which is an argument for making the
> carry structural rather than for adding a fourth warning.
>
> **DONE, and before the surface work rather than after** — so the surface builds
> on the final shape instead of migrating onto it. The ledgers are one record
> (`Ledgers`), `auditAllPathsD` carries one thing, and a fourth channel is a field
> plus two lines in `Ledgers.own`/`Ledgers.append`, adjacent to the field, with
> nothing to remember at the seal. All three existing channels were migrated in
> the same commit. The breadcrumb stays out of the record on purpose: it is a
> CURSOR (overwritten as the walk moves, copied out on the failing path), not a
> LEDGER (append-only, accumulated, carried out on success) — same door, opposite
> direction, different rule.

## 10. Acceptance

The demo file grows per-point cases, MCP-verified as `docs/16`'s were, and the
headline is `docs/16` case (12) INVERTED:

> `let b = &m x; *b := Cons(2, Nil); let d = *b;` — hovering `b` on the last line
> shows the payload the write put there, not the one it had at its binding.

That is the user's own requirement, and it is the one case that cannot pass under
the shipped design. It is the acceptance test for the whole lane.

The stated limitation carries over unchanged: there is no `#guard_msgs` analogue
for hover, so `lake build` asserts that the cases elaborate and the pinned
comments plus one tool call per case assert what they show.

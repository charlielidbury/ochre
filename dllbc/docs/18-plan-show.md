# Plan: `show` — a value made visible, where you put it

**The user's request, verbatim.** *"a `show` primitive which takes an identifier
and shows its value in the environment. To the IDE, it would show up as an info
tooltip (blue underline), like an error squiggle but not an error. This would be
useful for demos to highlight individual values at various points in the program
and how they evolve."*

**The design, in one sentence.** *`show x` prints, at its own position, exactly
what hovering `x` there would say — but without being hovered.*

That is the whole of it, and it is why this is a small plan rather than a large
one. `docs/17` already answers "what did the checker know at this point"; `show`
changes only WHO ASKS. A hover asks lazily, one identifier at a time, when a
reader points at it. A `show` asks eagerly, at a site the author chose, and the
answer lands in the diagnostic stream where it is visible without interaction and
survives into `lake build` output.

**Three surfaces over one ledger**, and this is the third:

| surface | asks | when | rendered |
|---|---|---|---|
| `docs/16` hover-on-binder | what was `x` bound to | on hover | lazily |
| `docs/17` hover-at-point | what is `x` here | on hover | lazily |
| **this** `show x` | what is `x` here | at elaboration | eagerly, as a diagnostic |

---

## 1. One renderer, or it is a bug

**`show x` must emit character-for-character what a point hover at that same
occurrence would emit.** Three forms (`x : τ`, `x ≡ v` comptime-known, `x ≡ v`
binding-time shape with inline σ types), per-path answers labelled with their arm
trails, capped at three with the remainder counted.

This is not a convention to maintain; it is a call to the same function. The
precedent is `checkProgramDiag`/`checkProgramHover` sharing `programPaths` and
`programVerdict` so that accept/reject cannot diverge by construction
(`docs/16`, §Invariants). If `show` and hover could ever disagree at one point,
a reader would have to know which to believe, and the answer would be "measure
them" — which is the state this project treats as a defect.

So the surface is: the existing renderer, a different sink.

## 2. Semantic transparency — the hard constraint

`show x` must be **invisible to the calculus**:

* it does not move `x`, does not borrow it, and is not a read — copy-on-read
  must not fire, because a `show` that consumed an index-kind value would change
  which programs check;
* it does not touch Ω, mint a loan, or affect any path;
* `Term` gains **no node**. The kernel never learns the word.

The last one is the strong form and it is what the next section is about: the
statement is **erased at elaboration**, so the emitted term is byte-identical to
the same program with the `show` lines deleted. `docs/16`'s zero-kernel-bytes
story survives intact, and the pinned demonstration is an `==` between a program
with `show`s and the same program without.

## 3. THE HARD QUESTION: how does an erased site get a point key?

Raised by team-lead and answered here, because it decides whether the erasure
above is affordable.

**The problem.** `docs/17` keys a point by the STATEMENT the occurrence sits in:
the walker tags each occurrence with its statement's key, the checker files
deltas under the same key, and the replay stops at the first delta filed there.
An erased statement is never walked, so it files no delta, so its key matches
nothing and the replay declines. A `show` that is invisible to the checker is
invisible to the thing that would answer it.

**The answer, and it is exact rather than a near-miss: anchor to the NEXT
statement.** `replayTo` reconstructs the state ENTERING a statement — that
instant was chosen in `docs/17` for the hover, and it is the same instant a
`show` written just above that statement is asking about. The state entering the
next statement IS the state at the show site. So a `show` needs no key of its
own; it borrows the one immediately after it, and the answer is not an
approximation of what it wants but literally it.

**A `show` at the end of a block still has a next statement**, which is what
makes this total rather than nearly-total: `show x; ()` anchors to `()`, and a
final expression is a statement the walker files a span for.

This survived the grammar change that let any statement end a block. A block need
no longer end in a final expression, so `show x` with no tail has no next
statement written — and the row supplies one, emitting the `()` the author would
have written. `show x` and `show x; ()` are then the same term filed the same
way, and the anchor above is unchanged rather than special-cased.

The honest limit, which the `; ()` spelling already had: `replayTo` answers only
where a delta is filed under the key, and a `()` changes nothing, so it files
none. A `show` anchored to a `()` therefore falls back to the binder fact —
what the name held at its binding — rather than the state at the show site. A
`show` followed by a real statement gets the point answer.

**The plumbing, and one gap it exposed.** A show's occurrence is filed before the
statement it will be keyed to has been walked, so `SpanAcc` grows a small list of
PENDING occurrence indices; `tagOccsFrom` tags those along with its own range and
clears the list. That is four lines.

The gap: **`tagOccsFrom` is not called by the final-expression row today**
(established by reading `Uni.lean` — that row calls `spanOfStmt` and stops). So
occurrences in a block's final expression currently carry no statement and always
fall back to binder granularity. This is a pre-existing hole in `docs/17`'s
surface, not a new one, and it is fixed here because `show` needs that row to
anchor against. It is hard to demonstrate at runtime — a final expression can
rarely mention a variable whose value has changed and still check (returning a
live borrow is rejected) — which is presumably why it survived; it is plain in
the source.

## 4. Grammar — checked, and `show` is free

`show` appears in this corpus only in PROSE. No `prog{ }` block binds or
references an identifier of that name, so the row collides with nothing
(`grep`ped, this tree).

**And the reservation does not widen**, which is the question `ElabCheck`'s own
invariant note says to ask before adding a leading atom: declaring `prog` made
`prog` a reserved token downstream, and the note asks that no future placement
widen that. `show` is **already a Lean keyword** (`show t from e`), so the token
exists in the table before this row is written and nothing downstream loses an
identifier it could previously use.

The row, in the statement layer beside the others:

```
syntax "show" ident ";" ublk : ublk
```

An unknown identifier at a `show` site gets the ordinary unbound-identifier
error, because it goes through the same `resolveName`/`noteIdent` path as every
other occurrence — no special case, no second error message to keep in step.

## 5. The sink: `logInfoAt`

Info severity is precisely "visible, not an error": a blue underline in the
IDE, an entry in the InfoView, a line in `lake build` output, and — the part
that matters for testing — something `lean_diagnostic_messages` returns
directly.

**That makes acceptance CHEAPER than it was for hover.** `docs/16` and `docs/17`
both carry the same stated limitation: there is no `#guard_msgs` analogue for
hover, so their pinned positions are verifiable only through a language server,
one tool call per case. A `show` is a diagnostic, and diagnostics are exactly what
`#guard_msgs` pins. So this surface can assert its output IN THE BUILD, which
neither of the two before it could.

That is worth stating as a design consequence rather than a convenience: the same
answer becomes cheaply testable purely by changing where it is delivered.

## 6. Cost

Eager, so it is paid per `show` site rather than per hover: one replay, measured
at ~4 ms on the array flagship (`docs/17` §9). Shows are sparse and opt-in — a
site exists only because an author typed it — so the expected bill is
(number of `show`s) × 4 ms, and a demo file with a dozen of them pays under a
tenth of a second.

**Measured, not asserted**, per the doctrine this lane earned: the demo file's
elaboration is timed with the `show`s present and with them deleted, and a
number that flatters beyond plausibility is a bug in the harness until proven
otherwise.

## 7. What ships

* the `show` row, erased, with the pending-occurrence anchor and the
  final-expression fix;
* `logInfoAt` carrying the point renderer's own output;
* a demo file whose star is `docs/17`'s four-points-four-answers borrow — the
  same variable `show`n at each of the four points, so the evolution the user
  asked to demonstrate is the file's whole content;
* `#guard_msgs` on those outputs, which is the first time this family of features
  can be asserted by `lake build`;
* an `==` pinning that a program with `show`s is the same `Term` as one without.

---

## 8. AS BUILT

> **SHIPPED.** Everything above held. Three additions from contact with the
> machine, none of them corrections to the design.

**The `#guard_msgs` claim is real, and it is the biggest thing this surface
buys.** `Tests/ShowSpans` asserts its own output in `lake build` — four cases,
including the evolution trace verbatim. Neither `docs/16` nor `docs/17` can do
that, and the difference is not effort but the sink: the same answer delivered as
a diagnostic instead of a tooltip is a testable answer.

**The erasure pin passes:** a program with `show`s `==` the same program without,
by `native_decide`.

**A σ can print BARE, and that is immutability being obeyed rather than a gap.**
`show v` on the first statement of a `fn` body renders `borrowₘ ℓ0 σ0`, not
`borrowₘ ℓ0 (σ0 : List Nat)`. A delta carries the σ-context as it stood AT that
change, and a borrow parameter's binding is filed by `bindSlot` during
`seedTelescopeV` before the σ's type is registered — so at that instant the
checker genuinely did not know it. One statement later the annotation appears.
Printing the type there would report a fact from the future, which §1 of
`docs/17` forbids. Reordering the seed so the type lands first would fix the
cosmetics by changing the checker, and is not taken. Pinned as case (S3) with the
reason beside it, so nobody "fixes" it later.

**Cost, measured not asserted.** `Tests/ShowSpans` with its six `show`s against
the same file with them commented out: 853 ms vs 862 ms, best of two each — the
`show` build faster than the bare one, i.e. noise. The ~4 ms replay figure from
`docs/17` §9 is the array flagship's, and replay scales with the delta stream, so
a `show` in a small program costs far less than that. The honest statement is:
per-site, proportional to the program's delta count, and invisible at demo scale.
(Load average was ~3.3 on 20 cores during this measurement rather than the ~1.5
of earlier rounds; the delta is inside noise either way, but the figure is not
comparable to the from-scratch numbers in `docs/16`.)

**One thing `show` inherited for free**, worth naming because it is the argument
for one renderer: the mid-move `⊥`. Nobody designed a demo case for "the payload
is out of the borrow right now"; it appears in the evolution trace because the
point renderer already told that truth, and `show` is the same call.

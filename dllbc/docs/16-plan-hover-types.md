# Plan: hover types — `x : τ` tooltips for DLLBC variables

> **STATUS — SHIPPED, both stages, on the branch `dllbc-hover`.** The design
> survived implementation; what follows below is the plan as written, with
> corrections marked in place in blockquotes labelled like this one.
>
> **What is CORRECT and shipped as written:** the mechanism (`Info.ofDelabTermInfo`
> with `mkDocString?`, and the custom text being the *entire* hover content); the
> two-source split and its staging; every invariant in §"Invariants"; the
> first-path v1 rule with its `(differs per path)` suffix; `defer_check` getting
> S1 and not S2; and the testing loop, including its stated limit.
>
> **What is WRONG and corrected below**, each at the paragraph that makes the
> claim: the shadowing argument (§S2's third bullet — *the premise is false*, and
> the conclusion survives for another reason); the registry (§S1's last sentence —
> there isn't one, and scope answers instead); and what S2 records (§S2's opening
> — a concrete value has no type, and `x ≡ S Z` is the BETTER tooltip rather than
> a fallback for a missing one).
>
> **One thing the plan does not mention at all** cost the most time and is added
> as §"What the seal eats". It is the second diagnostic channel in a row to need
> carriage across `checkRFnBody`, so that section now states it as a pattern with
> a signposted door rather than as this feature's own bug.
>
> **The measurement came out at the good end**, and the option the plan asks for
> is shipped anyway; see §"Cost, measured not assumed" for the numbers.

**Goal.** Hovering a variable inside a `prog{ }` block shows its DLLBC-level type —
`v : &mut List Nat`, `hi : Le (S i) (Len *v)` — the way hovering a Lean variable shows
its Lean type, in the IDE and through `textDocument/hover` generally.

**The mechanism is proven, not proposed.** An elaborator may attach arbitrary hover
text to any syntax span by pushing `Info.ofDelabTermInfo` with `mkDocString?`
(`Lean/Elab/InfoTree/Types.lean:209` on 4.33: "Text to use to override the docstring …
may be dynamic … computed only when it is used"). The end-to-end probe lives at
`Dllbc/Tests/HoverProbe.lean` (untracked seed): a 20-line `term_elab` pushed a custom
markdown string at an identifier and the language server returned it verbatim through a
real hover request — and, better than hoped, the custom text is the **entire** hover
content; no Lean-level type line renders above it. `prog{ }` being a term elaborator
(the elab-time-checking port) is what makes this reachable at all; a `macro_rules`
cannot push info.

## Two sources of truth, two stages

**S1 — parameters, at elaboration time.** A telescope binder's type is written in the
source — `(v : &mut List Nat)` — and the `Uni.lean` walker holds both the ident's and
the type's `TSyntax`. Hover for a parameter renders the **annotation's source text**
(exact, zero computation, no checker involvement). Consequences worth stating: S1
hovers work in `prog_parse { }` blocks too, and for every *occurrence* of the
parameter, not just the binder — the walker resolves every ident to its variable id
(`resolveName`), so it can emit an (occurrence-span, var-id) pair wherever the name
appears. Cheap extension in the same pass: hovering a **callee name** shows its
signature from the registry.

> **AMENDED — there is no registry, and scope answers instead.** `docs/05` §1.A
> deleted the registry before it was written, for a reason that applies here
> unchanged: *a callee is a binding lexically above the call*, so scope IS the
> call table. The walker therefore carries `fsigs` — `fn` name ↦ its signature's
> source text — pushed at the `fn` row and scoped to exactly `rest`, which is the
> callee's own scope: not visible inside the body (a `fn` is not in scope in its
> own right-hand side, §8) and not after the block. This is smaller than a
> registry and correct for the same reason a registry would have been unnecessary.
>
> The filing is done by `noteIdent`, which **mirrors `resolveName`'s precedence
> and must keep mirroring it**: pure binder, then runtime slot, then `fn` slot,
> then nothing. The two are separate functions (one is `MacroM` and makes a term,
> the other is `UM` and makes metadata) so the shared discipline is stated in a
> comment rather than factored out. A tooltip that skipped the `pctx`-first test
> would describe a `let` the occurrence does not refer to.

**S2 — `let` binders and their occurrences, from the checker.** A `let x = e` carries
no annotation; `x`'s type exists only in Ω at the binding step, and only the ⇒-walk
knows it. The port's machinery extends rather than duplicates: `letStep` (the one
shared binding site, already breadcrumb-aware) records `(variable id ↦ rendered Ω-type
of the bound value)` into a diagnostic side table on `St`; after a green `checkFn`, the
elaborator joins that table against the (occurrence-span, var-id) pairs and pushes one
info leaf per occurrence. Three honest edges, all documented rather than papered over:
- **Path-sensitivity**: a σ's type refines per branch. v1 records the FIRST path's
  binding-time type; if a later path disagrees, the tooltip appends "(differs per
  path)" and nothing more. No merging, no per-path lists in v1.
- **`defer_check` blocks get no S2 hovers** — no check ran, so no Ω existed. This is
  the design's own line (checking is where types come from), not a gap.
- **Shadowing is a non-issue by construction**: runtime ids are globally unique (M30),
  so keying by id — not name — is correct under shadowing, and every occurrence
  already resolves to its binder's id.

> **AMENDED — the shadowing premise is FALSE, and the conclusion survives for a
> different reason.** Runtime ids are not globally unique, in two ways that both
> matter here:
>
> * **A `fn` body numbers its locals from its own parameter count.** The `fn` row
>   walks the body with `elabUBlk … n body` where `n` is the number of parameters
>   (§5.2's positional convention), and the enclosing block's counter is not
>   consulted, so two sibling one-parameter bodies both mint id 1 for their first
>   `let`. The `fn` row says so in its own comment — "the positional ids collide
>   with the enclosing block's counter and that is fine … Ω resolves by NAME (M32
>   R1)" — so the corpus knew this and the plan did not.
> * **A parameter and a `let` shadowing it differ in id but share the NAME**,
>   which is the case this bullet is actually about.
>
> Keys are therefore **(id, name) pairs**, and S1's table additionally requires
> the occurrence to resolve to the parameter's own positional id. That second
> condition is what makes shadowing come out right: under `fn H (v : Bool) { let
> v = S(Z); let q = v; … }` the body's `let` prepends `("v", 1)` to `rctx`, so the
> occurrence resolves to 1 while the parameter's entry says 0, S1 declines, and
> the occurrence falls through to the checker's table. Pinned as case (7) of
> `Tests/HoverSpans.lean`: the parameter reports `v : Bool`, and both the
> shadowing binder and its use report `v ≡ S Z`.
>
> **THE DESIGN PROPERTY, stated on its own because it is the point and not a
> detail of the fix: an uncertain lookup DECLINES, it does not guess.** S1 answers
> only when the occurrence resolves to the very binder whose annotation it holds;
> anything else is handed to the checker, and if the checker has nothing either,
> no DLLBC tooltip is pushed and the reader gets Lean's ordinary one. So the
> failure direction is *silence*, never a confident mislabel.
>
> That direction is chosen, and it is the opposite of the one the span table
> takes. A missing SPAN is reported loudly ("this is a span-table gap, please
> report it") because every rejection was written somewhere and a gap is a defect.
> A missing TYPE is the ordinary case — a `defer_check` block, a splice, a binder
> no path reached, a match pattern binder — so reporting it would send readers
> after bugs that are not there. **Loud where absence implies a defect, silent
> where absence is normal**; the two tables differ because the two absences mean
> different things.
>
> A tooltip is read at a glance and believed. Silence costs a reader one hover;
> a wrong type costs them the debugging session that follows.
>
> **What the false premise still costs**, stated because it is the one place this
> feature can be wrong rather than merely silent: two sibling `fn` bodies whose
> binders collide in id AND name are indistinguishable to the join. Where their
> recorded values differ the tooltip says `(differs per path)` — the honest suffix
> path-sensitivity earns, arrived at from a different cause — and where they agree
> it is correct anyway. So it is never confidently wrong, but the suffix does
> conflate two causes, and that is a v1 limit rather than a design position. The
> fix, if it ever bites, is a hover slot minted per binder by the walker; not
> built, because nothing has asked for it.

> **AMENDED — `x ≡ S Z` IS THE BETTER TOOLTIP, and it is not a fallback.** This
> paragraph asks for "the rendered Ω-type of the bound value", which assumes every
> bound value has a type to render. A **symbolic** one does: a σ is a reserved
> pure name and `sctx` holds its type, which is the whole of that case and gives
> the `x : Nat` the plan is named for. A **concrete** one does not — this is a
> bidirectional checker, `hasType` checks and nothing synthesizes, so there is no
> function to ask and no entry to look up.
>
> The temptation is to read this as a gap and print something type-shaped anyway.
> It is the reverse. **A type is what you say when you do not know the value; the
> checker here knows the value.** `x : Nat` would be strictly less information
> than `x ≡ S Z`, and it would be information the checker had to infer rather than
> information it holds. So the two cases are spelled differently on purpose, and
> the spelling says which question was answered:
>
> | what the checker holds | tooltip | why this spelling |
> |---|---|---|
> | a σ, typed in `sctx` | ``**x : `Nat`**`` | a type is genuinely all there is |
> | a concrete value | ``**x ≡ `S Z`** — comptime-known value`` | the value is MORE than a type, and `≡` says so |
> | a σ-bearing TREE | ``**x ≡ `Cons (σ0 : Nat) (σ1 : List Nat)`** — binding-time shape`` | the SHAPE is known and the components are not |
>
> **The third row was a two-row table until the corpus was asked a question it
> had not been asked**, and the failure was one of LABELLING rather than of
> rendering. `Cons(h, t)` over two parameters is not a σ (so nothing to look up)
> and not concrete (so "comptime-known value" claimed knowledge of parts the
> checker does not have). The value rendered correctly the whole time —
> `Cons σ0 σ1` — under a caption that contradicted it.
>
> The fix says what is true, "binding-time **shape**", and gives each σ its type
> INLINE, because a bare `σ0` is an internal name and a reader owes nothing to it.
>
> **Inline is the user's ruling, and the alternative was shipped first.** A
> trailing legend (``Cons σ0 σ1`` … ``σ0 : Nat, σ1 : List Nat``) went out and was
> put to them against the inline form, with the tradeoff stated: inline puts the
> type where its σ is and needs no cross-referencing, and it grows with the tree,
> where a legend stays one short line however deep the value goes. They chose
> inline. Recorded because the tradeoff is real and a future deep-tree complaint
> should find the decision rather than re-derive it.
>
> **Neither form needs a parallel renderer, and the shipped one needs no new
> traversal at all.** Each σ is replaced by `substSym` — the kernel's own §3.2
> refinement substitution, already written and already tested — carrying a
> `.const` whose name is the annotated text, and the REAL `Val.pretty` prints the
> result. `Term.prettyPrec` renders a `.const` as its bare name at every
> precedence, so the parens that appear are the ones in the text. The scan that
> decides WHICH σs to substitute reads the rendered string, which is the right
> question to ask (*which σs does the reader see?*) rather than the convenient
> one, and it can only leave a σ bare, never mangle a value.
>
> Cost: `LetNote` carries the `sctx` as it stood at the binding, which is a
> POINTER COPY — the list is immutable and already in hand — so the third form
> costs nothing the other two did not.
>
> Recorded because it generalizes past this feature: **a renderer can be right and
> its caption wrong, and the caption is what a reader believes.** Nothing in the
> value output was ever incorrect; the sentence around it was, and only asking for
> a case nobody had asked for surfaced it.
>
> The `≡` rather than `:` is doing real work: it tells the reader which of the two
> they are looking at without their having to know this rule. And it is the
> honest half of the same discipline the shadowing note states — printing a
> guessed type would replace a fact with an inference, which this project treats
> as a defect rather than a convenience.
>
> This also happens to be the shape a comptime language should want. §"functions
> are comptime" is the neighbouring document's whole subject: what is known at ⇝
> is knowledge, not merely a type, and a tooltip that flattened the two would be
> hiding the distinction the calculus is built on.
>
> **Nothing is rendered at `letStep`.** The table stores the `sctx` lookup and the
> value as they already exist in hand, and the surface renders on demand:
> `Term.pretty` on the binding path would be a real cost paid for a string almost
> nobody reads. It is also what lets the first-path/`differs` comparison be done
> on raw entries, so the flag costs no pretty-printing either.

## What the seal eats (added by the implementation; not anticipated by the plan)

**A `fn` body is checked inside a seal, on its own `St`, which `checkRFnBody`
discards.** So the plan as written gives `x : τ` tooltips to top-level `let`s and
to nothing inside a function — which is to say, to toy programs and not to the
corpus.

This is `docs/05` pillar B's breadcrumb lesson repeating, and it repeated in
every particular, which is the part worth recording:

* **The same cause.** `checkRFnBody` ends with `set { saved with … }`, keeping the
  fresh-supply counters and `sealSites` and dropping everything else.
* **The same fix.** `auditAllPathsD` carries it out, as it already carries the
  breadcrumb. It gained a `base` parameter — the entry length of `letTypes` — so
  each path contributes only its own entries and the enclosing ones are not copied
  once per path.
* **The same soundness argument, and it is not a coincidence that it transfers.**
  The table is a binder ↦ description map. No value is observed through it, and
  the frame isolation the seal audit exists to enforce is about Ω, obligations and
  groups, none of which it touches. Crossing a seal with a σ would be a real
  violation; crossing one with diagnostic metadata is not.
* **The same way of finding it.** Not by reading the code — by pointing the
  feature at a `fn` and asking the server. The parameter beside it answered and
  the `let` returned nothing, which is exactly the shape docs/05 describes.

### This is now a PATTERN, and the next channel will hit it too

Two diagnostic channels have been added to `St`, in two separate pieces of work,
and **both needed carriage across `checkRFnBody` and neither anticipated it**:

| channel | added by | what it keys | crossed the seal |
|---|---|---|---|
| the breadcrumb (`stmtKey`/`argKey`/`trail`) | docs/05 pillar B | source spans | at the second attempt — the reference implementation dropped it on purpose |
| the hover type table (`letTypes`) | this plan | binder descriptions | at the second attempt — this plan did not mention the seal at all |

Two for two is a pattern rather than a coincidence, and the reason is structural:
**a diagnostic channel is about the SOURCE, and a function body is source like
any other, while the seal exists to isolate the machine state that source
produces.** Anything that follows the program's text rather than its Ω wants to
cross; the isolation was never aimed at it.

So the prescription, and it is more useful than "remember the seal":

> **A new diagnostic side table on `St` has TWO sites, not one — where it is
> written, and where the seal would otherwise eat it.** `checkRFnBody`'s closing
> `set { saved with … }` is the door; `auditAllPathsD` is how you get through it.
> Enumerate the fields that cross there before writing the table, not after the
> first probe comes back empty.

The door is now known and signposted from both ends — this section, and the
comments at both sites. A third channel that still forgets it will have had to
ignore three warnings, which is a different kind of mistake from the two that
have already been made.

## Invariants (the port's, inherited verbatim)

`Term`/`Val` change by zero bytes. The checker's accept/reject behaviour is
byte-identical — the S2 table is diagnostic metadata on `St`, written at `letStep`,
never read by any rule (the swept-state principle does not apply: no value is observed
across a refinement). No test assertion changes. No new monad-transformer layers
anywhere near a hot path — the StateT lesson is standing doctrine; the S2 table rides
the existing `St` diagnostic fields.

> **CONFIRMED, and one of them was made structural rather than merely observed.**
> `Term`/`Val` are untouched; no test assertion changed and the full 120-job build
> is green; no monad layer was added (the walker rides `SpanAcc`, the checker
> rides `St`).
>
> The accept/reject invariant is worth more than a claim, so it is enforced by
> construction: `checkProgramDiag` and `checkProgramHover` are **the same walk**.
> `programPaths` and `programVerdict` were split out and are shared, and the two
> entry points differ only in the seed's `hover` flag and in what they do with the
> paths afterwards. There is no second verdict to keep in step with the first, so
> the two cannot diverge — which is a stronger guarantee than a differential test
> and cost less.
>
> Scoping the walker's parameter tables is done by **save-and-restore on the
> accumulator** (`withHoverScope`), not by threading a new argument through a
> 30-call mutual block. The restore is skipped on the throwing path, which costs
> nothing: a block that failed to elaborate has no tooltips.

## Cost, measured not assumed

Hover info differs from error spans in one structural way: it must be pushed on the
**success** path (errors only pay on failure). Expected costs are one info leaf per
identifier occurrence (elaborator side) and one small write per `let` (checker side) —
both should be noise, but the ledger of this feature's history says MEASURE: per-module
elaboration timings on the flagship before/after, and a from-scratch suite number. If
the S2 write is measurable, it gates behind an option (`set_option dllbc.hover` — the
collection-flag pattern, a gate on metadata collection, not a semantic mode).

> **MEASURED. It is not measurable, and the option shipped anyway.**
>
> **Per-module, collection ON vs OFF**, best of two runs each, same tree, the only
> difference being a `set_option dllbc.hover false` after the imports (which forces
> a real rebuild — Lake keys its cache on content, so a `touch` replays instead).
>
> **This protocol suits a DISTRIBUTED cost and should not be reused for a
> concentrated one** (added by `docs/17`, which tried): it works here because
> collection touches every block the module elaborates. Where a cost falls on only
> the few blocks that check, per-module timing dilutes it below noise and reports
> nothing in either direction — that case needs a harness aimed at the checker.
>
> | module | hover on | hover off | Δ |
> |---|---|---|---|
> | `Tests/HashMap` (the flagship, 6083 lines) | 47117 ms | 47006 ms | +111 ms (+0.2%) |
> | `Tests/ArraySort` (quicksort) | 13467 ms | 13469 ms | −2 ms |
> | `Tests/Direct` | 5282 ms | 5265 ms | +17 ms (+0.3%) |
> | `Tests/Functions` | 3156 ms | 3187 ms | −31 ms |
> | `Tests/Programs` | 2797 ms | 2745 ms | +52 ms |
>
> Two of the five come out NEGATIVE, which is how you know the rest is noise:
> repeat runs of the same configuration differ by up to 0.45% (`HashMap` 47117 vs
> 47331), so every figure in that column is inside run-to-run variation.
>
> **From-scratch suite**, two independent pairs, alternating trees:
>
> | | run 1 | run 2 |
> |---|---|---|
> | this branch (120 jobs) | 295 s | 295 s |
> | `origin/main` (117 jobs) | 293 s | 292 s |
>
> **+2 to +3 s, about +0.9%** — small, but REPRODUCIBLE in a way the per-module
> figures are not, so it is reported as a real delta rather than as noise. Most of
> it is attributable: the three extra jobs are the new demo module's own
> `olean`/`c.o`/`dynlib`, measured at **855 ms**, and as a DAG leaf imported only
> by `Dllbc.lean` it runs last with nothing to overlap it (docs/05 §7's
> serialization point), so close to all of that lands end-to-end. What remains for
> the feature itself is roughly **1.5 s spread over 120 modules**, which is the
> same answer the per-module table gives from the other direction.
>
> Load average held between 1.35 and 1.74 on a 20-core machine across every
> from-scratch measurement, so these are uncontended numbers; the only other
> process of consequence was the language server at well under one core. (Load
> rose to ~2.7 afterwards, during the 855 ms measurement — a figure small enough
> that it is quoted as compute rather than as wall time, and it repeated to within
> 2 ms.)
>
> **The measurement is only worth as much as the switch it flips, so the switch
> was checked first**: with `set_option dllbc.hover false` in
> `Tests/HoverSpans.lean`, `lean_hover_info` at the pinned positions returns the
> block's plain `Term` and no DLLBC tooltip, S1 and S2 alike. The option gates real
> work, so the timings above are measuring something.
>
> **Why it is this cheap, stated so the number is believable rather than
> surprising.** The elaborator side is one info leaf per identifier occurrence,
> pushed on a tree Lean is building anyway. The checker side is one `sctx` lookup
> and one cons per `let` — deliberately **no rendering**, since `Term.pretty` at
> the binding site would be the one genuinely expensive thing available, and it is
> deferred to the surface where at most a handful of entries are ever printed.
> When the flag is off both sides are a boolean test.

## Testing — the MCP loop, and its limit

Development is test-first through the language server: `lean_hover_info` at exact
positions is the same code path the IDE uses, and the probe demonstrated the full loop
(write elaborator → diagnostics clean → hover → assert content). Acceptance artifact: a
demo file (`Tests/HoverSpans.lean` in the ElabSpans style) with the expected hover
content and positions recorded as comments beside each case — parameter binder,
parameter occurrence, let binder, let occurrence, occurrence in a later statement,
shadowed name, a `defer_check` block (asserting S1-present/S2-absent), a callee name.
Stated limitation, recorded rather than hidden: there is no `#guard_msgs` analogue for
hover, so these cases are machine-checkable only through the server (the MCP tools or
any LSP client), not by `lake build`. The demo file's comments are the pinned record;
re-verification is one tool call per case.

> **CONFIRMED, and the loop earned its keep three times.** `Tests/HoverSpans.lean`
> ships with sixteen cases and **37 pinned positions**, every one verified
> through `textDocument/hover`; the responses recorded in it are the tool's, not
> predictions. All eight cases the plan names are there, plus six the plan does
> not: the borrow shape `v : &mut List Nat` (the spec's own headline), a `let a =
> *v` beside it that the checker types `List Nat`, a path-sensitivity case that
> actually produces the `(differs per path)` suffix rather than merely providing
> for it, a let-bound borrow, a reborrow, and the match trio.
>
> **Case (12) is the sharpest statement of the S2 semantics in the file**, and it
> was not designed — it fell out of being asked to show what a borrow renders as.
> A borrow hovers as `borrowₘ ℓ0 (Cons (S Z) Nil)`, both parts. Then `*b := …`
> changes the payload, and on the NEXT line two tooltips disagree about the same
> memory: `b` still renders the pre-write payload, `d` (bound from `*b`) renders
> the post-write value. Both are right, because the table records at `letStep` and
> never updates. The plan says "binding-time type" in prose; this is that sentence
> made visible without the eye leaving the line.
>
> The file is in the default target, so a case that stops **elaborating** fails
> the build even though its tooltip cannot. That is the honest half of the
> guarantee and worth having: the cheap failure mode is caught cheaply.
>
> **Two things the loop found that reading would not have.** The seal (see above),
> which returned an empty tooltip where a parameter beside it answered. And a
> **stale language server**: after the seal fix the tooltips were still empty,
> because the server had the pre-fix `Machine.olean` in memory. The build was
> green and the checker was right — verified by `#eval`-ing `checkProgramHover`
> directly, which showed the table populated — and only the server disagreed.
> Restarting it fixed it. Worth writing down, because "the fix did not work" and
> "the server has not seen the fix" look identical through this loop, and the
> discriminator is to ask the checker directly rather than to change the code
> again.

## End state

The seed probe (`HoverProbe.lean`) is absorbed into the real implementation and
deleted. The feature ships as: S1 always on; S2 on green checks, first-path, gated only
if measurement demands it; the demo file as the acceptance record; this plan amended in
place with what implementation taught, in the house style.

> **AS SHIPPED.** The probe is deleted; its technique lives in
> `ElabCheck.pushHover`, which is the same six fields with a real span and a real
> string. S1 is always on and reaches parameter binders, every occurrence, callee
> names at both the declaration and the call, and `defer_check` blocks. S2 is on
> green checks, first-path, with `(differs per path)` where paths disagree.
>
> **The option ships even though the measurement did not demand it**, which is a
> deviation from the sentence above and is deliberate. `dllbc.hover` defaults to
> true. The plan makes the gate conditional on cost; the reason to have it anyway
> is that hover metadata is the one part of this machinery collected on the
> SUCCESS path, so "what did it cost" has to stay an answerable question rather
> than a one-time measurement — and the answer above was obtained by flipping
> exactly this switch. A gate that is also the measurement instrument earns its
> place at zero cost.
>
> **The module map, as built:**
>
> | Piece | Where |
> |---|---|
> | `hover`/`hovers`/`occs`/`ptypes`/`fsigs` on `SpanAcc`; `srcText`, `noteHover`, `noteOcc`, `withHoverScope`, `noteIdent` | `Uni.lean` |
> | The filing sites: `fn` row (binders, signature, scope), imperative-λ binders, `let` binder, the three ident occurrences | `Uni.lean` |
> | `St.hover`, `St.letTypes`, `noteLetType`, the `letStep` write | `Machine.lean` |
> | The seal crossing (`auditAllPathsD`'s `base` parameter, `checkRFnBody`'s carry-out) | `Machine.lean` |
> | `programPaths`/`programVerdict`/`checkProgramHover` | `Program.lean` |
> | `dllbc.hover`, `letTooltip`, `letIndex`, `pushHover`, `pushHovers` | `ElabCheck.lean` |
> | 16 cases, 37 pinned positions | `Tests/HoverSpans.lean` |
>
> **What is deliberately not built.** Match pattern binders get no S2 tooltip:
> they are bound by the match rather than by `letStep`, so the one shared binding
> site does not see them. Their *occurrences* fall through silently, which is the
> right failure — a missing type is the ordinary case for a block that was never
> checked, so unlike a missing SPAN it is not reported as a defect. Extending to
> them means filing at the arm-entry sites, which is the same shape as the
> breadcrumb's four arm entries and is a small, separate change.
>
> **The scrutinee, by contrast, WAS a defect and is fixed.** `elabScrut` handles
> the plain-variable path itself and never reaches `elabUTerm`'s ident row, so a
> parameter hovered everywhere except in `match n { … }` — an inconsistency a
> reader meets immediately, since match scrutinees are everywhere. One
> `noteIdent` call at that row. Found by probing, not by reading: `n` answered
> `Nat` at its binder and nothing one line below. Pinned as case (14b).
>
> **FILED, with its boundary — showing a REFINED value is a design step, not an
> extension.** The obvious next ask is that a binder's tooltip reflect what a
> branch *learned* about it. Two halves, and they are not the same size:
>
> * *Binding-time entries for pattern binders* are the small half: record at the
>   four arm-entry doors (`ownedSelect`, `borrowSelect`, `symOwnedSetup`,
>   `symBorrowSetup`) exactly as `letStep` records, reusing the breadcrumb's own
>   shape. This is the "small, separate change" above.
> * *Refined* values are the large half, and the reason is structural rather than
>   effortful. **`refineSym` is a destructive rewrite over occurrences**, so once
>   refinements are in scope "the type of `x`" stops being one fact per binder and
>   becomes one fact per *program point*. That is a different data structure — a
>   table keyed by breadcrumb × binder rather than by binder — and it changes what
>   the join at the surface has to do, since an occurrence would then select the
>   entry for *its* point rather than the binder's single entry.
>
> The evidence that the small half does not get you the large one is in the demo
> file, case (14e): `let q = m` inside `S(m) => …` goes through `letStep` and so
> answers, with `Nat` — m's own `sctx` type, correct and unnarrowed. The narrowing
> lives in the relation between `n` and `S m`, not in m's type, so no amount of
> recording *at binders* surfaces it.
>
> There is also a semantic question to answer before building, not after: with a
> per-point table, **which** point does hovering a binder show — its binding, or
> the reader's cursor position? Both are defensible and they disagree, and the
> current design sidesteps it only because one fact per binder makes the question
> unaskable. Case (12) is the same tension in miniature and shows the current
> answer is binding-time: after `*b := …`, `b` still renders its pre-write
> payload while `d` renders the post-write value. Both right; both on one line.
>
> > **ANSWERED — the cursor's point**, by the user, and the successor plan is
> > `docs/17`. This paragraph existed to stop anyone building before the question
> > was settled; leaving it as written would now do the opposite and send a reader
> > hunting for an answer that exists. Kept rather than deleted because the
> > question is the right one to have asked and the reasoning above still explains
> > why it had to be asked first.
> >
> > **Case (12) therefore inverts**: what this file pins as correct behaviour —
> > `b` rendering its pre-write payload below the write — is the specimen
> > `docs/17` must make wrong, and is that lane's acceptance test. Nothing here
> > becomes false; the granularity the answer is stated at changes. Binding-time
> > honesty at binder granularity was right for one fact per binder, and it is the
> > same principle `docs/17` §1 carries to one fact per point.

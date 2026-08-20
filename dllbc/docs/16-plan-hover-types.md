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
> claim: the shadowing argument (§S2's third bullet — *the premise is false*), the
> registry (§S1's last sentence — there isn't one), the description of what S2
> records (§S2's opening — a concrete value has no type), and one thing the plan
> does not mention at all, which cost the most time and is added as §"What the
> seal eats".
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
hovers work in `prog defer_check { }` blocks too, and for every *occurrence* of the
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
> **What the false premise still costs**, stated because it is the one place this
> feature can be wrong rather than merely silent: two sibling `fn` bodies whose
> binders collide in id AND name are indistinguishable to the join. Where their
> recorded values differ the tooltip says `(differs per path)` — the honest suffix
> path-sensitivity earns, arrived at from a different cause — and where they agree
> it is correct anyway. So it is never confidently wrong, but the suffix does
> conflate two causes, and that is a v1 limit rather than a design position. The
> fix, if it ever bites, is a hover slot minted per binder by the walker; not
> built, because nothing has asked for it.

> **AMENDED — "the rendered Ω-type of the bound value" does not always exist, and
> nothing is invented when it doesn't.** This paragraph's opening assumes every
> bound value has a type to render. A **symbolic** one does: a σ is a reserved
> pure name and `sctx` holds its type, which is the whole of that case and gives
> the `x : Nat` the plan is named for. A **concrete** one does not — this is a
> bidirectional checker, `hasType` checks and nothing synthesizes, so there is no
> function to ask and no entry anywhere to look up.
>
> So the two cases are spelled differently on purpose:
>
> | the value | tooltip |
> |---|---|
> | symbolic (a σ) | ``**x : `Nat`**`` |
> | concrete | ``**x ≡ `S Z`** — comptime-known value`` |
>
> The second is not a weaker answer standing in for a type; it is a stronger one.
> The checker knows the value. Printing a guessed type instead would replace a
> fact with an inference, which is the kind of thing this project treats as a
> defect rather than a convenience.
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

The prescription that falls out, and it is more useful than "remember the seal":
**a new diagnostic side table on `St` has two sites, not one — where it is
written, and where the seal would otherwise eat it.** Both of the tables that now
exist needed both.

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
> a real rebuild — Lake keys its cache on content, so a `touch` replays instead):
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

> **CONFIRMED, and the loop earned its keep twice.** `Tests/HoverSpans.lean` ships
> with eleven cases and **21 pinned positions**, every one verified through
> `textDocument/hover`; the responses recorded in it are the tool's, not
> predictions. All eight cases the plan names are there, plus three the plan does
> not: the borrow shape `v : &mut List Nat` (the spec's own headline), a `let a =
> *v` beside it that the checker types `List Nat`, and a path-sensitivity case
> that actually produces the `(differs per path)` suffix rather than merely
> providing for it.
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
> | 11 cases, 21 pinned positions | `Tests/HoverSpans.lean` |
>
> **What is deliberately not built.** Match pattern binders get no S2 tooltip:
> they are bound by the match rather than by `letStep`, so the one shared binding
> site does not see them. Their *occurrences* fall through silently, which is the
> right failure — a missing type is the ordinary case for a block that was never
> checked, so unlike a missing SPAN it is not reported as a defect. Extending to
> them means filing at the arm-entry sites, which is the same shape as the
> breadcrumb's four arm entries and is a small, separate change.

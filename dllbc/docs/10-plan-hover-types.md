# Plan: hover types — `x : τ` tooltips for DLLBC variables

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

## Invariants (the port's, inherited verbatim)

`Term`/`Val` change by zero bytes. The checker's accept/reject behaviour is
byte-identical — the S2 table is diagnostic metadata on `St`, written at `letStep`,
never read by any rule (the swept-state principle does not apply: no value is observed
across a refinement). No test assertion changes. No new monad-transformer layers
anywhere near a hot path — the StateT lesson is standing doctrine; the S2 table rides
the existing `St` diagnostic fields.

## Cost, measured not assumed

Hover info differs from error spans in one structural way: it must be pushed on the
**success** path (errors only pay on failure). Expected costs are one info leaf per
identifier occurrence (elaborator side) and one small write per `let` (checker side) —
both should be noise, but the ledger of this feature's history says MEASURE: per-module
elaboration timings on the flagship before/after, and a from-scratch suite number. If
the S2 write is measurable, it gates behind an option (`set_option dllbc.hover` — the
collection-flag pattern, a gate on metadata collection, not a semantic mode).

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

## End state

The seed probe (`HoverProbe.lean`) is absorbed into the real implementation and
deleted. The feature ships as: S1 always on; S2 on green checks, first-path, gated only
if measurement demands it; the demo file as the acceptance record; this plan amended in
place with what implementation taught, in the house style.

# 21 — Marked twins: the honest program is the original, the liars are mutations of it

Status: plan agreed in discussion 2026-08-21; mechanism built in this lane, flagship pilot DEFERRED (see §6). The user's idea, refined twice in review.

## 1. The problem this replaces

The twin-template pattern (ArraySort's `arrUnder` is the exemplar) shares one body between an honest program and its lying twins by Lean-level splicing: the body is a Lean function of the return types, and each instantiation supplies honest or lying `%sret`/`%pret`/…. Costs, all paid at the flagship:

* A spliced template has no closed value, so it is **silently deferred** — never walked, never checked at its own site. Hover, `show`, and span-level errors have nothing to answer with anywhere inside the file's main content (user report, 2026-08-21, reproduced: the closed `c6*` probes hover; the 400-line template does not).
* The sharing is a construction property the reader trusts, not a value-level fact.
* The plumbing: template-as-Lean-function, five spliced parameters, per-instantiation defs.

## 2. The replacement

Write the honest program ONCE, closed, no splices — walked, checked at elaboration, hoverable, showable. Derive each lying twin by **mutating the honest `Term` value** and assert the mutation is rejected:

```
def qsHonest : Term := prog{ … fully closed … }          -- checks, hovers
def qsLie1 : Term := mutate "perm" ty{ …the lie… } qsHonest
example : progRejects qsLie1 "does not have its owed type" = true := by native_decide
```

Precedent: the M22 reject twins were already rebuilt as "one-token mutations of the landed quicksortSorted". This makes that the standing pattern, and makes "same body, one lie" a value-level fact rather than a trusted construction.

## 3. Markers: addressing without needles

Structural find-and-replace needles are name-sensitive and go ambiguous silently. Instead the honest program NAMES its claim sites with a marker node (the user's proposal):

* Surface: `@name(E)` anywhere a term is written. Semantics: identity — `@name(E)` *is* `E`.
* `Term.marker : String → Term → Term` in the grammar.
* `Term.replaceMarked? name repl t : Except String Term` — swaps the BODY of the marker named `name` (the marker stays, so twins remain addressable and strip-transparency covers them). **Fails unless exactly one** marker of that name exists — zero hits and multiple hits are loud errors, not silent wrong tests (the Edit-tool contract, the user's refinement; subsumes the mutation-changed guard).

The honest program thereby declares its attack surface: every `@perm(…)`, `@sorted(…)` names a claim a twin will lie about, and the twin table collapses to marker × replacement × expected-rejection-needle. Needles retire from ADDRESSING; they stay as assertions that a twin rejects for the meaningful reason (`progRejects twin "owed type"`), never because the mutation produced garbage.

## 4. Why this is NOT kernel surface for tests

The e2e rule refuses kernel machinery that exists for tests. The design honors it structurally, by the `numberSeals` precedent:

* **Strip at the boundary.** `Machine.atBoundary` (the one function every program walk enters through) becomes `pushContinuations ∘ numberSeals ∘ stripMarkers`. No eval rule, no checking rule, no `Val` form: a marker provably never reaches the machine, by the same argument that a seal's site is assigned before any rule sees it.
* Rows the compiler forces elsewhere (`beq`, `freeRVars`, `pretty`, `numberSeals`, `imperative`, …) are written transparent-or-structural; any machine-side match with a catch-all treats a leaked marker as an error, never as silent acceptance.
* Markers are **test scaffolding only** — ruled at spec time to forestall the annotation-mechanism temptation (provenance, doc labels). Anything more re-opens the kernel-surface question properly.

Guarantee scope, stated honestly: the strip is claimed through the program boundary. A `Term` checked by side entries that bypass `atBoundary` (library `chk*` batteries) meets marker rows structurally; mark inside `prog` blocks.

## 5. Hover/span seam

Surface statement keys are built from EMITTED syntax (markers included); the machine's keys come from the stripped walk. Two elaborator-side joins therefore normalize with `stripMarkers`: the point-hover key evaluation and the error-span lookup. Statement keys that are binder-only (`let`, `match`) were never exposed.

## 6. Interaction with docs/20 (module states) — why the pilot waits

Built now, in parallel (this lane): the node, the strip, `replaceMarked?`, surface syntax, and a pinned demo on a small closed block — St-agnostic, disjoint from the module lane's ground but for two seams (`atBoundary`, the ElabCheck key joins), partitioned by file.

Deferred until docs/20 stages 1–2: the ArraySort rewrite. The honest quicksort IS a module block — it wants `prog (arrLemmas.env) { fn SplitA … }` with lemmas resolving from the seeded state, no `open` lists, no `%` lemma splices. Writing it against today's plumbing means stage 4 rewrites 400 surface lines immediately; write it once, in its final shape.

Two requests INTO docs/20, so they are designed in rather than bolted on:
1. Expose a **seeded rejection check** — "check this `Term` against this seed `St`, expect failure" — as a callable function, not elaborator-internal. Twins under module states are mutated `Checked.term`s re-checked against the same seed.
2. State the boundary ordering once: strip markers, then number seals, counters continuing from the seed.

## 7. Acceptance (this lane)

* Transparency pinned: `stripMarkers markedT == plainT` by `native_decide`, and the marked program `progOk`.
* Contract pinned: `replaceMarked?` errors on zero and on duplicate hits.
* One mutated twin rejected with a meaningful needle.
* `show`/hover behave identically in marked code (a `#guard_msgs` show beside a marker).
* Full suite green.

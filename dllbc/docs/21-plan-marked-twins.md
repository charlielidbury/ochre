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

* Surface: `@name E` anywhere a term is written — LOOSE binding, a λ-style prefix that takes the maximal term to its right, so `@claim Id Nat r (S Z)` marks the whole spine bare (user request 2026-08-21; the first cut required brackets). `@name(E)` is the same single grammar row reading a grouped term, not a second spelling. Semantics: identity — `@name E` *is* `E`.
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

**The deferral condition has been met** (2026-08-22): docs/20 stages 1–2 (and through stage 6) merged to main, this lane rebased onto it, and both requests are delivered — see §8. The ArraySort pilot is therefore unblocked and is the NEXT lane; it is not started here.

## 7. Acceptance (this lane)

* Transparency pinned: `stripMarkers markedT == plainT` by `native_decide`, and the marked program `progOk`.
* Contract pinned: `replaceMarked?` errors on zero and on duplicate hits.
* One mutated twin rejected with a meaningful needle.
* `show`/hover behave identically in marked code (a `#guard_msgs` show beside a marker).
* Full suite green.

## 8. As built (2026-08-21, this lane) — where the build filled in the plan

All of the above landed (`Tests/MarkedTwins.lean`); the record here is what the plan left open and the build decided, plus one wording drift a twin-writer must know:

* The one traversal is `Term.mapMarkersGo` (Syntax.lean) — non-monadic, a polymorphic accumulator threaded exactly as `numberSealsGo` threads its counter, and TOTAL: structural recursion goes through, so no `partial` and no `Inhabited` obligations. `stripMarkers` and `replaceMarked?` are its two instantiations; the row list lives once and mirrors `numberSealsGo`'s row for row.
* Two machine-side matches turned out to have NO catch-all for §4's catch-all sentence to cover (`reflectC`, `readR` — the compiler surfaced both as missing-cases). Each got an explicit loud-error row ("marker reached the machine — stripped at the program boundary; a side entry must pre-strip"), which is §4's never-silent rule applied to the stronger case.
* §2's sketch needle "does not have its owed type" is not what a return-type lie produces. The audit's actual message is `result (…) does not have return type (…the lie…)`, and the acceptance twin pins that real message with the strengthened claim in it — so the pin cannot be met by a twin rejected for being garbage.
* §5's seam was verified counterfactually rather than assumed: with the elaborator's key strip stubbed out, the acceptance `show` beside the marked `:=` statement silently declined its point answer and fell back to the binder fact, failing the `#guard_msgs` pin; restored, it answers `⊥` identically to the unmarked program. The discriminating probe is an ASSIGN statement on purpose — `stmtKeyOf` keeps an assign's rhs (where the marker sits) but reduces a `let` to its binder, so a marked `let` would never have exercised the seam.
* Span-lookup normalization strips BEFORE `stmtKeyOf`, not after: a marker wrapping a whole statement would push `stmtKeyOf` into its catch-all and keep the continuation the machine's key dropped.

Second pass, same day — brackets become optional (user request):

* ONE grammar row, `syntax:10 "@" noWs ident uterm:10`, replaced the dedicated parenthesized row. The extent of a bare marker is MAXIMAL — everything a level-10 parse absorbs, application spines and arrows included (`@m Nat → Nat` marks the arrow, not its domain) — stopping only at a real delimiter: `,` `)` `;` `{`. So `Cons(@m Z, Nil)` marks `Z` alone, and a bare claim in a `fn` return type runs to the body's `{`. All pinned as `Term` equalities in Tests/MarkedTwins §T5, and the three spellings `@m E` / `@m(E)` / `@m (E)` are pinned equal.
* Kernel-spelling collisions, verified rather than assumed, and the two cases DIFFER: `@old …` never parses, because `old` is already a keyword of the grammar (the `old *v` row) — refused by the parser as "expected identifier". `res` is an ordinary identifier, so `@res …` parses under the generic row and the ELABORATOR refuses the name loudly (a marker named `res` would silently mean its body's current value where `*res` means the exit payload). The parser refusal has no `#guard_msgs` pin — a term that fails to parse fails the whole command before `#guard_msgs` can guard it (tried) — so it is recorded here and in the test's prose; the elaborator refusal pins.

Third pass, 2026-08-22 — rebased onto main's module-states merge (docs/20, through stage 6), and what that met:

* **There are now TWO boundaries, and the strip lives in both.** The root's `atBoundary` (which main had already reduced to seal numbering alone — docs/19 v2 dropped `pushContinuations`, the one merge conflict, resolved by keeping main's text and adding the strip) and the seeded `moduleBoundary`, which every `prog (seed) { … }` walk and every `*From` helper enters through, bypassing the root's entirely. Request #2 is delivered as `moduleBoundary`'s docstring sentence and its one line: strip markers, then number seals from `seed.nextSite`.
* **Request #1 was delivered as asked, with one improvement**: `progRejectsFrom`/`progOkFrom`/`checkProgramFrom` take a `Checked` (both twins) rather than a bare `St`, so a caller cannot hand the executing twin to the checking machine. A twin under a module state is exactly the mutated `Checked.term` re-checked against the same seed (Tests/MarkedTwins §T7, the seeded golden/twin pair, real message pinned). `Checked.term` is persisted BEFORE the boundary, so its markers survive into the value a twin is minted from.
* **A third key join** appeared with module states: the persisted span channel (`SpanNote.mk (stmtKeyOf k) …`, the elaborator quoting surface statement keys into the module's ledgers for later localization). Same seam, same fix: strip before `stmtKeyOf`.
* **`FnMacro.retarget` has a catch-all** and runs BEFORE the boundary, so without a row a `.call` inside a marked claim would have been left unresolved — silently, as the kernel's "unknown function". It gained a transparent marker row. This is the §4 catch-all hazard met in practice: a catch-all in a pass that runs pre-strip is not "treats a leaked marker as an error", it is "skips the marker's body", and every such pass needs the row.
* Main's raw-term migration made `letIn`/`assign` two-field; `mapMarkersGo` re-mirrored `numberSealsGo` row for row, as its header says it must.

## 9. The pilot (2026-08-24) — ArraySort rewritten honest, and what the flagship taught

The §6 deferral was real and the pilot landed, twice: built first against the pre-one-var world (preserved on tag `arrsort-prevar-backup`), then re-landed from main after docs/22 merged — the honest chain, the twins, the pins and the needles carried over verbatim but for `Term.pvar` → `Term.var`, which is itself evidence the design sits above the identity refactor. `Tests/ArraySort.lean` is now the honest chain `arrSort : Checked := prog (Dllbc.std) { fn SplitA …; fn PartitionA …; fn QuicksortA …; () }`, ten claim sites marked, every lying twin minted from the persisted `Checked.term` and rejected from the same seed, `arrUnder` and its five spliced return types and the positional telescope vocabulary deleted. `show e` inside `QuicksortA`'s body answers and is `#guard_msgs`-pinned — the user report §1 opens with, closed. The findings, each now load-bearing:

* **The old body twin was VACUOUS.** `splitANoSwap` — "the one that matters most" — called itself as `splitANoSwap(…)`, the Lean def's name rather than the `fn`'s, an unresolvable `.call`; its `progOk = false` passed on `call: unknown function 'splitANoSwap'` and the deleted swap was never what was tested (probed before deletion). Re-probed on the one-var base after the re-land (the retired def reconstructed in a scratch probe, deleted after reading): the rejection is still exactly `call: unknown function 'splitANoSwap'`, same spelling. The marker form replaces it with a twin that CROSSES the two marked write values (`@wmid`/`@whd` — each cell written back what it held) and is rejected at the swap branch's own result audit. §3's "silent wrong tests" concern was not hypothetical; it had already happened, at the flagship, in the most-commented twin in the file.
* **The `fn` lowering FANS OUT a claim site.** A `[fuel]`-hoisted fn's return type is copied into the recursor motive, the ih's type and the seal (3 copies); a hoisted PARAMETER type fans to 5. One surface site, several lowered copies — `replaceMarked?`'s exactly-one contract refuses, correctly and loudly (pinned). The companion `Term.editMarked name edit t : Nat × Term` edits every copy of the one site in its own context and returns the count for the twin to pin — zero-hit loudness preserved, the lowering's fan-out a stated fact. Exactly-one remains the default for un-fanned sites (`PartitionA`'s, the body writes').
* **The pre-strip traversals ALL need the transparent row**, and the pre-var pilot proved it the hard way: `FnMacro.absVar` — the id-world telescope abstraction — hit its catch-all on a marked `*t` and left the raw runtime var where the plain elaboration abstracts to `§p`; the visible symptom was three layers downstream (`Arr⟨…⟩ is state` at the fn audit) with no marker in any message, found only by structural term-diff of stripped-marked against plain. One-var then DELETED `absVar` (`telePi` binds the parameter's own name), resolving that instance structurally — one fewer pass that can miss a marker is one fewer hazard. The rows that remain on this base: `Term.substP` (the hoist's motive/arm substitutions), `absOcc`/`freePNamesGo` (§18's occurrence abstraction and its shadow set), `hasBorrowT`, and FnMacro's `renameVar`/`resolveScrut`/`branchBinders`/`selfScrutArgs` (a self-call under a marker must still reach the termination check)/`renameSelf`/`selfToIh`. The §4 catch-all sentence is a rule with teeth: EVERY traversal that can run before the boundary strip needs the marker row, and the compiler only finds the ones without catch-alls.
* **A module-states residual, isolated:** a SEED-BOUND former (`let CountA = …` in `std`) cited in an imperative fn's return type dies at the audit (`readC (⇝): a call is not in the comptime fragment`) where the spliced `StdChainRaw` constant checks — switched resolution mode alone, same block, green-vs-red. Simple consumer types resolve seed formers fine (ModuleStates §7); an imperative fn's audit does not yet. Until that lands, a flagship module writes its types the way StdChain's own links do — qualified constants — which is also why the links were already written that way (the formers bind LAST, below the links).

Measured (the risk §6 flagged): the module builds in 45 s against the old file's 18 s on the same base — seconds, not a wall; the delta is the chain's elaboration-time check plus the per-`native_decide` std re-derivations the seeded helpers pay. Residuals pinned for later lanes: the seed-former audit residual; the `#guard_msgs` show pin numbers its σ from the end of the std supply (re-pins trivially when the chain grows — a canary, not a defect); the census's A1 entry (`arrUnder`, the twin-template class) is retired by this section — the census doc itself never landed on main, so this is its record.

## 10. The train, stage 1 (2026-08-24) — Direct.lean honest, and the twin the id world couldn't mint

The list-side flagship follows the pilot: `Tests/Direct.lean`'s three twin-templates (`soUnder`, `setSwapUnder`, `qsUnder`) are now three seeded modules (`splitOffM`, `setSwapM`, `qsM`), return types inline with markers, the D1/D4 telescope vocabulary (`vT`/`dvT`/`oldvT`/`iT`/`xT`/`jT`, `vfT`/`pT`/`fuelT`) and the per-twin retype skeletons deleted, ten twins minted, the executing differentials seeded (`runProgramFrom`), a guarded `show` answering inside `Quicksort`'s body. Module cost 14 s against the old file's 5 s on the same base — seconds. Stage findings:

* **One-var turned body-twin minting from impossible to trivial.** The old file transcribed its body twins in full and SAID why: "a `%` splice is a Lean `Term` written outside the macro — it has no way to say 'the `hub` this match will bind'". Under one-var a replacement cites any binder in scope at the marked site BY NAME: `qsStaleBound` is two one-line edits (`@qsub Hub2` → `Term.var "Hub0"`, likewise `Hlb0`), `partitionLoses` is the marked write's `Cons(x, lo)` collapsed to its own second argument, `splitOffLieHead` is the congruence motive's `@socong` body replaced by its λ-binder `A`. Three ~90-line transcriptions became three one-line mints. This composes the two lanes: names-as-identity is what makes claims-as-markers reach inside bodies.
* **A fanned cross-replacement must be POSITIONAL.** The swapped-conjuncts twin under a `[i]`-hoist: the claim mentions the hoisted scrutinee, so the motive/ih/seal copies differ per arm (`Take i …` is `Take Z …` in the base-arm copy), and replanting one extracted body would quietly unify arms. `crossOn` pairs copy k of one marker with copy k of the other (one traversal order serves both), count pinned.
* **The stripped module terms are CLOSED** — formers qualified, proofs spliced, calls retargeted at elaboration — so `Term.stripMarkers m.term` checks from `initSt`, and the unseeded harnesses (Measure's corpus, PointCost, MatchJoinSweep) keep closed flagship subjects instead of losing them to the seeding. Programs.lean's flagship census re-pinned on the stripped term with every count UNCHANGED — the honest module elaborates to the same program the closed chain did.
* **The vacuity sweep, run before the transcriptions were deleted:** all three of Direct's old body twins rejected at the audit (`audit: result (…)`), honest — the `splitANoSwap` class did not recur here.
* The old file's 15 `chk`-battery rows definition-checking StdLemmas raws against StdLemmas types are SUBSUMED: each lemma is a chain `fn` whose elaboration checks raw-against-stated-type at the declaration. The negative controls (lying types) keep `chk` with inline-written types. Direct.lean no longer imports StdLemmas — stage 3's condition for it.
* Rider done: `EagerRec` imports `ElabCheck` instead of `StdChain` (it never used the chain).

## 11. The train, stage 2 (2026-08-24) — HashMap honest, and the lowering's other lessons

The 7980-line corpus follows: `hmS1Under` (three spliced return types, 1100 lines) becomes TWO chained modules — `hmM0 : Checked := prog (Dllbc.std) { InsertInList; RemoveL; SlotOfE; NewHM; SlotUpd; SlotRem; () }` and `hmM := prog (hmM0) { SlotPush; MoveBktR; MoveOne; MoveSlots; InsertHM; RemoveHM; () }` — plus `hmPinM` (the pinned GetMut ops) and `hmOrM := prog (hmPinM) { … }` (or_insert, A MODULE SEEDED FROM A MODULE — the chain composing as designed). The `keyIv`/`selfIv`/`keyRv`/`selfRv` vocabulary, the per-twin retypes, and the `twinNoOverwrite`/`twinNoBumpUnder`/`twinNoResizeUnder` transcriptions (60–670 lines each) are DELETED; nine spec twins and three body twins are minted; the callers and the executing differential run seeded (`runProgramFromF` at the hashmap's 2·10⁶ fuel); a `#guard_msgs show key` answers inside `InsertHM`. Stage findings:

* **The eleven-links cut is a LAW of big modules, not a StdChain quirk.** One module of the whole S1 chain dies in the code generator ("maximum recursion depth", the Std FnT constants inlined into one giant initializer — the exact failure 55ccca6e recorded); two chained modules compile. The seam is free: a seeded module resolves its callees from the seed.
* **An ARM BODY is a claim site, via docs/22 fragments.** `twinNoResize`'s lie replaces a whole 150-line arm; no marker can wrap a multi-statement block in place, but a fragment CAN carry the arm (`else { (@igrow %growArm) }`, free names binding at the splice site per docs/22 §6), and then the arm is one marked term. The twin is `markedBody? "inogrow"` planted over `@igrow` — a 670-line transcription became a three-line mint. The fragments are the honest single copies; nothing is written twice.
* **A ⇒-position lie must be spelled with runtime vocabulary.** The no-overwrite twin's first cut replaced the marked write with the comptime snapshot `V0` and was rejected by the §6 fence ("a COMPTIME binder cannot be ⇒-moved") — a true rejection of the wrong thing. The honest lie writes back the cell's own runtime read (`*vv`), and rejects at the return type. Mutation-quality is part of the twin's statement.
* **Two audits, two needles**: a lie in a RETURN TYPE rejects as "does not have return type"; a lie whose damage lands in the borrowed pack rejects at the payload audit as "does not have its owed type" (`ibump`, `igrow`). The old file's `progOk = false` pins could not tell these apart; the minted twins pin the distinction.
* The checker-rejected GetMut chain (the known kernel gap) keeps the ONE surviving tail-carrier — a rejected chain cannot be a module — but loses its 1100-line prefix to the `hmM` seed: the carrier is now just the six GetMut fns, and both its rejection pin and its executing tests run From the module.
* Measured, same base both sides: the module builds in 251 s against the old file's 100 s (the delta is the twins' seeded re-walks of the chain); the def elaborations themselves are a fraction of it. Not a wall; recorded.

## 12. The train, stage 3 (2026-08-24) — `StdLemmas.lean` deleted

Both flagships came off the old pure library in stages 1 and 2, which was the condition this stage waited on. The file is now gone (1,939 lines), and what it uniquely still provided turned out to be four live citations and one paragraph of prose:

* **`Measure.lean`'s `lemmaEntries`** — ten `StdLemmas.XRaw` proof terms feeding the phase-C proof-mass census — retargeted to `StdChainRaw`. Verified a no-op the only way that means anything: the whole `phasec` census was captured before and after and diffed, and every static number is identical, node counts included (`LeTrans` 1653, `LePredL` 2643, `CountConsR` 2853, …). The chain's raw terms are the verbatim copies stage 4 claimed they were.
* **`Tests/Parse.lean`** — `import Dllbc.StdLemmas` → `import Dllbc.StdChain`, `open Dllbc.StdLemmas (LeReflRaw)` → `open Dllbc.StdChainRaw (LeReflRaw)`. Its two assertions are about the identifier fallback resolving a name Lean knows, so any library constant serves; the ground-truth pins are unchanged.
* **`Dllbc.lean`** — the import line, deleted. `StdChain` was already imported below it.
* **`Uni.lean`'s fn-shadow guard** (`lemmaShadowCheckAt`) — the collision family retargeted from the `Dllbc.StdLemmas` namespace to `Dllbc.StdChainRaw`. **This narrows the guard, by exactly the 110 `XTy` stated types**: the two namespaces agree on all 110 `XRaw` proof terms and all 25 spec formers, and differ only in that the old file also held the `XTy` halves. A `fn` named for a stated type was never the hazard the guard is about, so the narrowing is deliberate — but it IS a narrowing, not a rename.
* **The Div-free load-ledger note** — the one piece of prose that existed only in the deleted file (why the 4/5 load factor is carried as `5·n ≤ 4·cap` with no floor-division lemmas) — moved verbatim onto `StdChain.lean`'s `LedgerGrowRaw`, which is what it explains. `HashMap.lean`'s "see the StdLemmas ledger note" now points there.

Green: `lake build` 117 jobs, `lake build phasec` 121 jobs. Both counts are 3 below the pre-deletion 120/124, which is the deleted module's own lean/`c.o`/dynlib jobs and nothing else.

**On the grep attestation.** `grep StdLemmas` over `*.lean` is EMPTY — no code, no docstring, no import anywhere in the package cites the file. It is not empty over `docs/` and `paper/`, and deliberately so. 28 mentions were already there as dated plan and measurement records — `20-plan-module-states.md` 13, `05-plan-elab-time-checking.md` 6, `11-suspensions.md` 5, `10-functions-are-comptime.md` 2, `paper/NOTES.md` 1, this file 1 — where the file's name is part of what was measured or planned on a date. Rewriting those to say `StdChain` would make the record claim measurements that were never taken. Every *current-state* pointer was retargeted instead — the language reference's "the standard library is …", DELTAS' array-library and bounds-vocabulary pointers, the hashmap flagship's port instruction and line-count table, `01-design-arrays-slices`' dangling `StdLemmas.lean:3657` citation, `12-design-borrow-refounding`'s `StdLemmas.Set`, and the paper's f7-carve figure row. `20-plan-module-states.md` carries a banner at its first mention saying the file is deleted and that everything below is record. That banner and this entry name the file too, which is why the count over `docs/` + `paper/` reads 36 rather than 28 after this commit: 28 inherited, 8 added here to explain the deletion.

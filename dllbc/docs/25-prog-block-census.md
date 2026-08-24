# 25 — Census: what every program block in the tree is for

**Input to a decision, not a plan.** The question asked was whether the pattern "build a `Term` with `prog{ }`, then assert `progOk` on it" can collapse into one `prog () { }`, on the hypothesis that *"there isn't much use case for a `Term` which is never checked, so every use case comes under this category."*

Short answers, in order of how much they change the picture:

1. **The redundancy is real but partial.** `prog{ }` checks at elaboration, so the ⇒-**walk** does run twice. The **audit** does not: elaboration runs it with no return type. `progOk t = true` therefore asserts something elaboration never asserted — and `prog () { }` does not assert it either, so the naive collapse *loses* it.
2. **Measured payoff: 5–9% of a file's build.** Not nothing, not transformative.
3. **The hypothesis does not hold.** Terms that are never ⇒-checked are not a rump; they are the **majority of program blocks in the tree** (~1250 `prog_parse { }` sites against ~419 `prog{ }`), and their largest single use is not rejection twins — it is 256 defs holding *pure terms typed comptime*, which are not programs at all.

## 1. The redundancy, precisely

`ElabCheck.elabChecked`, which is what `prog{ }` elaborates through:

```lean
let res := if hover then checkProgramHover v none pointHover
           else (checkProgramDiag v none).map (fun _ => ([], []))
```

The second argument is `retType? = none`, and `Program.programVerdict` documents that case as **WALK ONLY**:

> every rejection the ⇒-walk itself raises is still caught and still localized, and only the audit — the one check that needs a return type — is left to whoever states one.

`progOk t` is `checkProgram t (retType := ty{ Unit })` → `programVerdict (some retType)` → `auditPathsD`. So:

| | ⇒-walk | audit at `Unit` |
|---|---|---|
| `prog{ }` at elaboration | yes | **no** |
| `progOk t` | yes (again) | yes |
| `prog () { }` at elaboration | yes | **no** |

Two consequences. The walk is genuinely duplicated, so the build-time argument is sound. And `prog () { }` is **not** a drop-in for `prog{ }` + `progOk`: it reproduces the half that was already happening and drops the half that was not.

**How much is the audit worth?** Empirically, in this corpus, nothing yet. Every one of the 259 walk-asserted `prog{ }` defs passes it, and all 18 `example : progOk X = false` assertions in the suite are on `prog_parse` terms — never on a `prog{ }` term, because a `prog{ }` term that failed the walk would have failed the build. So the audit is a live regression guard that has never fired. Dropping it is a judgement call about future coverage, not a silent equivalence.

**Two further differences worth knowing before migrating:**

* `prog () { }` **requires a single path** ("a module must be single-path, so its one ending state is well-defined"). This turned out to be far less restrictive than it sounds: statement-position matches JOIN (docs/19), so a module-level `match` on a symbolic does not fork the module walk. Probed directly — a block with a module-level match on an opaque call's result, arms binding *different* names, converts and checks. 33 of the 334 named `prog{ }` defs have a `match`/`if` outside every `fn` body; on this evidence that is not a blocker list.
* `prog () { }` produces a **`Checked`, not a `Term`**, so every `Term`-typed use site (`Term.beq`, `impLams`, `Term.pretty`, splices into other blocks) needs `.term`.

## 2. Build-time payoff, measured

Delete only the assertions that are genuinely doubled — `example : progOk X = true` where `X` is `prog{ }`-built — and rebuild the file.

| file | baseline | doubled assertions removed | after | delta |
|---|---|---|---|---|
| `Tests/Programs.lean` | 5.7 s | 84 | 5.2 s | −0.5 s (−9%) |
| `Tests/HashMap.lean` | 267 s | 14 | 252 s | −15 s (−5.6%) |

`lake build <module>`, warm dependency cache. HashMap's cost is dominated by rejection twins (`prog_parse` + `progRejectsFrom`), which are **not** doubled and would not move.

## 3. The census

Sites, comments stripped. `Uni.lean`, `ElabCheck.lean` and `ProgMacro.lean` are excluded — they *define* this syntax, so their occurrences are not uses.

| form | sites | named defs | written inline in an `example` |
|---|---|---|---|
| `prog{ }` | 419 | 334 | 57 |
| `prog_parse { }` | 1250 | 780 | 363 |
| `prog (…) { }` | 45 | 41 | 1 |
| `ty{ }` | 114 | — | — |

Named defs by what is actually **asserted** on them (transitively; "indirect" = spliced into or cited by something that is itself asserted):

**`prog{ }` — 334 defs, 259 (78%) carry a ⇒-walk assertion**

| assertion | defs |
|---|---|
| walk only | 185 |
| walk + run | 36 |
| walk + shape | 18 |
| walk + run + shape | 11 |
| walk + reject | 4 |
| **shape only** | **31** |
| **run only** | **15** |
| run + shape | 5 |
| indirect | 18 |
| nothing found | 2 |
| rarer combinations | 9 |

**`prog_parse { }` — 780 defs, only 64 (8%) carry a ⇒-walk assertion**

| assertion | defs |
|---|---|
| **comptime typing** (`chkL`/`chk`/`chkS`: `readC` + `hasTypeT`) | **256** |
| **rejection** (`progRejects`/`progRejectsFrom`/`expectErr`) | 173 |
| indirect (spliced into a checked block) | 159 |
| nothing found | 52 |
| shape | 49 |
| walk | 39 |
| reject + walk | 11 |
| reject + shape | 10 |
| other combinations | 31 |

**`prog (…) { }` — 41 defs**: 24 walk-asserted, 10 used only as another block's seed, the rest shape/reject mixes.

## 4. The categories that were asked for

**(a) Constructed then immediately checked — collapsible.** 185 `prog{ }` defs assert nothing but the walk; another 69 assert the walk plus a run or a shape fact, so the walk assertion collapses but the `Term` is still wanted. Plus 13 inline `progOk (prog{ … })` in examples. **Call it ~185 clean collapses and ~70 partial.**

**(b) `prog_parse { }` twinned with a rejection.** 173 defs plus ~21 inline. These cannot become `prog{ }`, let alone `prog () { }`: the block must NOT be checked at elaboration, because it is the failure that is the assertion.

*Would `#guard_msgs` on a failing `prog () { }` be better?* No, on three counts. `progRejects t needle` asserts a **substring**; `#guard_msgs` asserts the **whole** message, path prefix included — and the suite's one existing whole-message assertion (`Tests/Direct.lean:1060`) broke during an unrelated experiment purely because a path prefix changed. Second, a block that fails to elaborate leaves **no definition behind**, so the failing term cannot be held as a value — and rejection twins are routinely compared against their golden sibling. Third, docs/20 §6 already ruled on this: `prog_parse` stays seed-free and the seed belongs to the assertion helper, with `#guard_msgs` available where exact text is wanted (ModuleStates test 5). Both forms exist; the default is already chosen.

**(c) Library terms checked elsewhere.** 159 `prog_parse` defs are spliced into something that is checked — chiefly `StdChainRaw`'s `XRaw` proof terms, which are checked when their chain block elaborates. docs/20 §5 records why they must be spliced constants rather than bound values, and docs/24 generalises it.

**(d) Genuinely needing an unchecked `Term` — NOT empty, and it is the biggest category in the tree.**

The single largest population is **256 `prog_parse` defs asserted with `chkL`/`chk`/`chkS`** — `readC` then `hasTypeT`, a *comptime typing judgement*, not a program walk. These are types, proofs and pure functions. `prog{ }` is wrong for them by construction: it would ⇒-walk a Π. They are written `prog_parse` rather than `ty{ }` for a concrete reason — `ty{ }` refuses free names and `prog_parse` admits them, so an open fragment can be typed against a context.

Three smaller but real sub-populations:

* **31 `prog{ }` defs whose only assertion is about the term's SHAPE.** The clearest are the macro-output tests: `Tests/Sugar.lean:167` `flatLet` / `pyramidLet` with `example : flatLet = pyramidLet := by rfl`, and `Tests/KernelFloor.lean:1243` `twoSeals` / `twoSealsRenamed`. The subject is what the macro emitted; the elaboration check is incidental. These survive a migration only by writing `.term` everywhere, which makes the assertion read worse.
* **15 `prog{ }` defs asserted only by running** (`progRunsTo`, `expectEnv`) — the claim is the final Ω, not the verdict.
* **~54 defs no assertion reaches at all.** Most are `StdChainRaw` `XRaw` constants that the chain no longer cites (`AddCommRaw`, `LenSwapLRaw`, `MulSuccRaw`, …) — dead weight worth a separate look — plus a handful of documentation-only programs.

**(e) `ty{ }` — 114 sites.** Types and pure terms. Out of scope, and the boundary with (d) is the interesting part: `ty{ }` and `prog_parse { }` are both "a `Term`, unchecked", differing only in whether free names are admitted.

## 5. What this says about the migration

The collapsible core is real and worth doing on its merits: **~185 clean sites**, a 5–9% build-time saving on the files measured, and one construct instead of two. The single-path worry does not materialise.

But it is a **tidying of one quarter of the program blocks in the tree**, not a unification. `prog_parse { }` outnumbers `prog{ }` three to one and has three independent reasons to exist that no amount of `prog () { }` addresses — rejection twins, comptime typing of pure fragments, and library terms checked at their splice site. The hypothesis that "every use case comes under [construct-then-check]" is true of 78% of `prog{ }` and of 8% of everything else.

Two things to decide deliberately rather than inherit:

* the `Unit` **audit** that `progOk` performs and neither brace does — keep it as an explicit assertion, add it to the module form, or drop it knowingly;
* the ~54 unreferenced `XRaw` constants, which are a separate cleanup and would be found by nothing else.

# Plan: elaboration-time checking, and errors that point at source

> **STATUS — SHIPPED, on the third target it was aimed at.** This plan has been
> implemented three times against three architectures, and the design survived all
> three unchanged. What moved was the surface it attaches to.
>
> 1. **`dllbc-elab-check-preM27`** — six commits, against `decl{}`/`Decl`/`checkFn`
>    and a name-keyed registry that assembled call tables.
> 2. **`dllbc-elab-check`, tip `1ddc328d`** — re-applied against post-M27, where
>    `checkFn` and `Decl` are gone and "scope is the call table" makes the registry
>    pointless. `git rebase` could not carry it; the design was re-applied.
> 3. **`dllbc-elab-port`, this one** — ported onto main 242 commits later. Rebase
>    was measured and refused again: of the three commits on the reference branch,
>    the first (the "one surface" collapse) had already been done independently by
>    main in the opposite direction, and the third edited a file main deleted. One
>    commit of real content remained, and it was re-applied rather than replayed.
>
> **What is CORRECT in this plan and shipped as written:** the three pillars —
> checker inside the elaborator, positions on a side channel with `Term`/`Val`
> unchanged, and the error surface; the statement-and-argument granularity of S2;
> every invariant in §3; and the two risks in §4 that materialized.
>
> **What is SUPERSEDED** is marked in place below, in blockquotes labelled like
> this one. Two things moved: the *registry* (§1.A) was deleted rather than built,
> and the *surface* (§6, default 1) is now opt-in rather than default-on. Both are
> consequences of the architecture moving under the plan, not corrections to it.
>
> One thing the plan did not anticipate at all — **splice-aware auto-deferral** —
> is added as §2a.

**Goal.** A DLLBC type error should surface the way an unbound-variable error already does: as a Lean diagnostic attached to the offending span of surface syntax, in `lake build` output and as an IDE squiggle — not as a string inside an `#eval` result three declarations away.

**Why the good case works today, and why it stops where it stops.** `decl{}` and `pure{}` are `MacroM` *syntax-to-syntax* transformers: they walk the surface `TSyntax` and emit the quotation `Dllbc.Decl.mk "name" [...] ...`. While they walk, they hold the source nodes, so every error they can detect themselves — unbound identifiers, malformed parameters, unknown match scrutinees — is thrown with `Macro.throwErrorAt stx`, and Lean does the rest. But the `Decl` **value** does not exist at macro time; it exists only after Lean elaborates the emitted quotation. `checkFn` therefore runs in a separate, later world — an `#eval` or `native_decide` over a positionless de Bruijn term — and its `Err : String` can only ever attach to the `#eval` line. The macro layer localizes everything it can see; the checker sees everything but can localize nothing.

**The claim of this plan:** both halves can be had, in stages, without touching the kernel term representation, the checker's semantics, or the trust story.

---

## 1. The three pillars

### A. Run the checker inside the elaborator

Upgrade `decl{}` from a `macro` to a **command elaborator**. The elaboration of one declaration becomes:

1. Elaborate the surface syntax exactly as today (the existing `elabUTerm`/`elabUBlk` pipeline, unchanged), producing the `Decl.mk …` expression.
2. **Evaluate it to a `Decl` value** in the elaborator (`evalExpr Decl` — `unsafe` in the standard, contained way every reflective elaborator uses it). This is the step the macro architecture cannot do and a command elaborator can.
3. **Look up the call table** in an environment extension (see below) and **run `checkFn`** on the value, right there. With `precompileModules := true` already on, the checker runs *native* inside the elaborator and the language server — this is the same mechanism that made `#eval checkFn` fast, now applied at elab time. The direct-proving quicksort's 21 ms check is imperceptible during elaboration.
4. On `ok`: `addDecl` the definition as today, and **register** the `Decl` in the environment extension keyed by name.
5. On error: `throwErrorAt` — at the declaration header in stage S1, at the offending statement from stage S2 on.

The environment extension is the piece that pays for itself twice: registered decls mean **call tables assemble themselves** — the checker resolves callee names against the registry instead of a hand-maintained `[nthS, swapSN, …]` list at every use site. (The explicit-list form stays available for negative tests that deliberately check against a wrong table.)

> **AMENDED — the registry was never built, and is not missed.** An earlier draft
> (this paragraph, and pillar A's steps 1, 4 and 5) has the elaborator be a
> **command** elaborator that `addDecl`s a definition and **registers** it in an
> environment extension keyed by name; the registry's stated purpose is to
> assemble call tables. Neither survived, for one reason each:
>
> * There is nothing to register. M27 §8 made a program a term and scope the
>   let-chain, so **a callee is a binding lexically above the call** — "scope is
>   the call table, so there is no table at all, not an empty one"
>   (`Program.lean`). A let-chain assembles the table by being a let-chain. The
>   `EnvExt.lean` this section calls for is a module that would have had no
>   readers.
> * There is nothing to `addDecl`. The form that checks is a **term** elaborator,
>   not a command one, so it produces a `Term` in expression position and the
>   surrounding `def` (or `example`, or argument) does the binding as it always
>   did. This is strictly simpler than the plan and reaches more places: a
>   checked program can appear anywhere a term can.
>
> What survived verbatim is the rest of pillar A: elaborate as today, `evalExpr`
> the assembled `Term` to a value, run the checker right there, `throwErrorAt` on
> rejection. The `precompileModules := true` claim in step 3 held — the check is
> ms-class inside the elaborator.

### B. Positions on a side channel — the kernel term stays position-free

The tempting design — a span on every `Term` node — is the wrong one: it bloats the representation, threatens `beq`/`alphaEq`/every cache keyed on terms, and makes conversion answer questions about metadata. **Invariant of this plan: `Term` and `Val` change by zero bytes.**

The observation that makes this cheap: the checker is a *statement-driven interpreter*. `readR` walks the body's `letIn`/`seq` spine structurally, and forks at `matchE` arms — so **the checker's position in that walk already identifies a statement**, and its existing path-sensitivity already records the arm choices. A breadcrumb `(spine-index list, arm-trail)` is derivable from the walk the interpreter performs anyway:

- The elaborator, while walking `ublk` statements (it holds each statement's `TSyntax` today — that is where `throwErrorAt` already gets its spans), additionally emits a **span table**: `(statement path ↦ source span)`, carried alongside the emitted `Decl` (a parallel array; not inside the `Decl`).
- The checker's `St` gains a diagnostic breadcrumb field — the current statement path — updated at exactly one site (the spine-walk step in `readR`, plus the arm entry in the match dispatch). `throwErr` includes it. This is *diagnostic metadata, not σ-bearing state*: no value is observed across a refinement, so the swept-state principle does not apply and `refineSym` is untouched.
- The elaborator catches `(breadcrumb, message)`, maps the breadcrumb through the span table, and throws at the right `Syntax`.

Statement granularity is the 90% win: "this `let`, this call, this match arm" — with the **path trail in the message body** ("on the path where `leb x p ⇒ True`, `n ⇒ S _`…"), because under path-sensitive checking the same statement checks many times and the trail is half the diagnosis.

> **AMENDED — the breadcrumb is the statement's TERM, not its position.** An
> earlier draft has the breadcrumb be a `(spine-index list, arm-trail)` path,
> derived from the walk the interpreter performs anyway. That is not implementable
> as stated, and the reason is `atBoundary`: `pushContinuations` **duplicates each
> continuation into every match arm** before the checker walks anything. A
> statement's position in the walked term is therefore neither its position in the
> source nor the same across arms — while its *term* is the same term in every
> copy.
>
> So the key is the statement itself, normalized by `stmtKeyOf`, which drops
> exactly the part `pushContinuations` rewrites (the continuation) and keeps
> exactly the part it does not (the statement). A `let` reduces further, to its
> binder alone, because runtime ids are globally unique. Matching on terms is
> invariant under the normalization for free and needs no second implementation of
> the fork logic.
>
> Everything else in pillar B is as written, and the plan's central claim — "the
> checker's position in that walk already identifies a statement" — is what makes
> the term key work at all. The arm trail survives unchanged and is exactly the
> "path trail in the message body" this paragraph asks for.
>
> **Where the update sites are, today.** The plan's "exactly two update sites
> (spine step, arm entry)" is now *three plus five*, and the count went up for a
> good reason: main made "one rule per statement former, three drivers" true
> (`letStep`/`assignStep`/`seqStep` are shared by `readR`, `readRTail` and
> `explore`), so the breadcrumb is filed inside those three steps and all three
> drivers inherit it. The others are `processArgs` (per argument) and the four arm
> entries (`ownedSelect`, `borrowSelect`, `symOwnedSetup`, `symBorrowSetup`), plus
> the terminal expression in `exploreD` and the statement-position match in
> `exploreMatch`. Filing at the shared steps rather than per driver is what keeps
> §4's discipline holdable: a fourth driver gets the breadcrumb for free.
>
> **THE BREADCRUMB MUST CROSS THE SEAL, and the reference was wrong about this.**
> A function body is checked inside a seal, on its own `St`, and the audit throws
> a plain `String` into the enclosing state — whose breadcrumb points at the `fn`
> statement. The reference implementation dropped the `Diag` at that site on
> purpose, reasoning that "a rejection inside a sealed body is reported at the
> seal's own statement". For this corpus that is the wrong call, and it is not a
> small one: **a `fn` body is where essentially all real DLLBC code lives**, so
> dropping the breadcrumb there means the feature localizes toy programs and
> nothing else. `auditAllPathsD` carries it out, at both throw sites.
>
> This is sound for exactly the reason pillar B gives for the breadcrumb in
> general: it is **not σ-bearing**. It is a key into a source table, no value is
> observed through it, and the frame isolation the seal audit exists to enforce is
> about Ω, obligations and groups — none of which it touches. Crossing a seal with
> a σ would be a real violation; crossing one with a source key is not.
>
> **How it was found is the point.** The bug did not appear in the demo file,
> which is written in top-level programs. It appeared the first time the feature
> was pointed at the corpus — a real closed program from `Tests/Programs.lean`
> with one argument broken — and it appeared as this section's own
> fail-loudly-never-guess rule firing: "no span for the failing statement — this
> is a span-table gap, please report it". A mechanism that had guessed a nearby
> position instead would have hidden it.

### C. The error surface

`Err` stays `String` at the boundary everyone knows; internally `checkFn` gains a variant returning `Except (Breadcrumb × String) …`. The audit's errors (return-type conversion failures) attribute to the **return-type syntax** — the elaborator has that span — with the conjunct's path in the message. Telescope errors attribute to the parameter binder. Nothing about what the checker *rejects* changes; only where the rejection lands.

---

## 2. Staged delivery

**S1 — decl-granularity (small; do first).** Command elaborator + `evalExpr` + registry + `checkFn` at elab time + `throwErrorAt` on the declaration header. No span plumbing at all. Already transformative for the workflow: a failing decl is a red squiggle on its own name, in the IDE, at edit time — no `#eval` round-trip; and call tables come from the registry.

**S2 — statement and call-argument granularity (the payoff).** The span table from the `ublk` walker, the `St` breadcrumb, the path trail in messages. One elaborator site emits spans; one interpreter site maintains the breadcrumb.

S2 includes **argument-level attribution at runtime calls**, because both halves come free where general sub-term spans would not. In `f(x + y, z)` with `z` failing its parameter type, the squiggle lands on `z` alone: the elaborator holds each argument's own `TSyntax` while walking the call (the span table key just grows an argument index alongside the statement path), and the checker's call rule (`processArgs`) checks actuals *positionally* against the telescope, one at a time, threading the instantiated substitution — so at the moment argument `k` fails, the checker already knows `k` and already holds the *instantiated* expected type. The diagnostic is therefore exactly the wanted shape: squiggle on the offending argument expression, message stating the parameter's expected type *after* instantiation with the earlier arguments (which, in a dependent telescope, is half the information). The same applies to the borrow-shape and move errors `processArgs` raises per argument.

The boundary with S3, stated exactly: S2 points at *which argument* is wrong; it does not point *inside* one. If the mismatch is within a pure sub-expression — the error being at `y` inside `x + y` — attribution stops at the whole argument until S3's pure-fragment breadcrumbs exist.

> **AMENDED — S1 and S2 shipped in one commit, and S4 is deliberately not
> started.** The staging was right about difficulty and wrong about separability.
> S1's "no span plumbing at all" is not actually less work than S2's, because the
> hard parts of S2 — deciding the key (see pillar B, amended) and threading the
> `UM` monad through the walker — are the same work whether the spans are consumed
> or discarded, and a decl-header-only error is not worth a release of its own.
> Both shipped together, in two commits split by *layer* (checker, then surface)
> rather than by granularity.
>
> **S4 is not started, on purpose.** With checking opt-in (§6, default 1,
> amended), migration is no longer forced by the feature: nothing breaks if no
> site is ever converted. That makes S4 a separate, reviewable, file-at-a-time
> pass rather than a prerequisite, and it is the right shape for it — §2b counts
> 213 immediate candidates.

**S3 — sub-term granularity for types and pure proofs (only on demonstrated pain).** `hasType` errors inside a big cited proof term currently point at, at best, the statement that consumed it. Extending spans into the pure fragment means span-tagging binder/`elim`-arm/application-spine positions from `pure{}`'s walker and threading a breadcrumb through `hasType`. Heavier, and S2 may make it unnecessary in practice — StdLemmas authors get their errors at the `chk` probe for the lemma itself, which is already local. Decide after living with S2.

**S4 — suite migration.**
- *Positives*: elaboration **is** the check; the `#eval … = OK` lines become redundant and are dropped (a handful kept as CI belt-and-braces).
- *Negatives — the suite's soul*: a lying twin must now *fail to elaborate*, which is asserted with Lean's own `#guard_msgs` idiom (or a thin `decl_rejected! "needle" { … }` wrapper command around it, matching on the error substring exactly as `checkFnErr` needles do today). Mechanical migration, roughly two dozen twins.
- *Heavy checks*: the M22 conformance baseline (54 s compiled per check) must not run on every elaboration of its module. Two tools, both existing patterns: a per-decl `(defer_check)` attribute that keeps the legacy emit-value-only behaviour (check stays in an explicit `native_decide` as today), and — if wanted later — an elab-time cache keyed on `alphaEq` of the decl + its table, the exact trick the S19 `native_decide` cache already proved.
- *Kernel artifacts* (**default taken, flag to veto**): the headline theorems — both quicksorts' `checkFnOk … := by native_decide` — are **kept** as kernel-checked artifacts even after elab-time checking subsumes their UX role. Elab-time checking is ephemeral (an elaboration side effect); the flagship claims keep their durable, kernel-accepted form. Cost: those checks run twice; both are milliseconds.

---

## 2a. Splice-aware auto-deferral (added by the port; not anticipated by the plan)

**The rule.** Elaboration-time checking fires exactly when the program is **comptime-known**. If the assembled value is closed, it is checked at elaboration. If it is not, the check is deferred *automatically and silently*, with a `trace.Dllbc.check` line saying so. No marker is written for this case and none should be.

This is the meta level mirroring the object level. The calculus's whole subject is which things are known at ⇝ and which only at ⇒; the elaborator is subject to the same distinction about its own input, and the test suite's comptime/runtime staging split is the same split one level up. A program that is not comptime-known to the elaborator is not something the elaborator can be asked about.

**What triggers it, concretely.** The surface supports splices — `%name` antiquotes a Lean-level `Term` into the block. The corpus uses this for **twin templates**: one shared body, with the return type spliced per instantiation, so that a program and its lying twin share the body *verbatim* and the only difference between them is the claim being made. `Tests/ArraySort.lean` is written this way.

A spliced template is not checkable at its definition and *should not be*. It has no closed value; and more importantly, it exists precisely to be instantiated several ways, **some of which are expected to be rejected**. Checking it where it is written would either fail (there is nothing to evaluate) or check one arbitrary instantiation. Such a template is inherently instantiation-checked, and that is a feature of the pattern rather than a limitation of the mechanism.

**The test is semantic, not syntactic.** The elaborator asks the assembled `Expr` whether it is closed (`hasFVar || hasMVar`) rather than scanning the surface for `%`. This is better in both directions:

- it catches **unsolved metavariables**, which no syntactic scan could see; and
- it does **not** defer `%SwapL` — a splice of a *global constant*, which has no free variable, assembles to a closed value, and checks perfectly well. Syntactic detection would have wrongly fenced every one of those.

The test must cover the **return type as well as the body**, and that is not obvious: the twin shape `prog check -> %ret { … }` has a perfectly closed body and an open type. Testing the body alone sends an open `Expr` to `evalExpr` and takes the kernel's "declaration has free variables" instead of deferring. This was found by running the demo, not by reasoning about it.

**Graceful degradation, and the natural S2.5.** Because the span table is keyed by statement *term* rather than by path or by byte offset, it degrades gracefully rather than going wrong under splicing: a template's non-spliced statements still have valid keys, and only the spliced ones would fall back loudly to the header. A future check at the *instantiation site* could therefore still localize an error to the template statement that caused it. Not built; filed here as the natural next step, because the keying that makes it possible is already paid for.

## 2b. The fencing inventory, re-derived against today's suite

The old branch's 73 `defer_check` markers were an inventory of the *old* suite, under default-on checking. Under opt-in (§6, default 1, amended) the arithmetic inverts: nothing needs a fence, because not writing `check` **is** the fence. What is worth counting instead is the population of real programs and how each would be treated.

Measured on this branch (`progOk`/`progRejects` are how the suite names a program):

| class | count | treatment |
|---|---|---|
| named defs asserted `progOk` | 310 | candidates for `check` |
|  — closed and unparameterised | 213 | **checkable at elaboration today** |
|  — body splices (`%`) | 49 | auto-deferred |
|  — parameterised template | 11 | auto-deferred |
|  — not a `def N : Term := prog{ … }` | 37 | assembled some other way; case by case |
| named defs asserted `progRejects` | 203 | **must stay bare** — the rejection is the assertion |
| asserted BOTH ways (twins) | 17 | the template pattern, by construction |

So the honest headline is **213 of 310** — about two thirds of the programs the suite asserts as good could carry `check` today, and the auto-deferral absorbs 60 of the remainder without anyone writing a marker. The 203 rejection twins are the class the old branch fenced by hand; under opt-in they need nothing, which is the single largest reduction in ceremony the surface change buys.

This is a migration progress bar and not a limit. The number rises as programs move off helper-assembled forms, and the conversion itself is mechanical and reviewable one file at a time — which is why this port **converts nothing**: it adds the form, demonstrates it, and leaves the corpus at 1701 unchanged `prog{ }` sites for a separate, reviewable pass.

> **AMENDED — the table above counts the wrong thing, and the count that matters
> is 275.** With `prog{ }` auto-checking (§6, amended again), the question stopped
> being "how many could carry `check`" and became "how many must carry
> `defer_check`". Every fence in the shipped tree was placed by MEASUREMENT on the
> live elaborator — build, read what was actually rejected, fence exactly those,
> repeat to fixpoint — never by predicting from a class. The result, 275 across 18
> files:
>
> | class | count |
> |---|---|
> | `progRejects` only — the rejection IS the assertion | 176 |
> | fed to a Lean-level assembler; no direct assertion | 45 |
> | `progOk` only — honest, but not checkable where written | 39 |
> | asserted both ways (the twin-template pattern) | 13 |
> | not inside a `def` | 2 |
>
> **The 84 in the middle two rows are a class this section did not have: program
> FRAGMENTS.** `Tests/Diff.lean` is the specimen — `def withPool (rest : Term) :
> Term := prog{ fn Through …; %rest }`, applied as `withPool (prog{ … Push(7, b) … })`.
> The inner brace is closed, contains no `fn`, and is a perfectly good program that
> is only HALF of one: its callees arrive from the wrapper at the Lean level. 52 of
> the observed rejections are literally `call: unknown function 'Push'`.
>
> The general statement, which is a limit of the feature rather than a defect of
> the corpus: **auto-checking can only check a block that is a WHOLE program.**
> Where programs are assembled above the brace, the check belongs at the assembly
> site — the same boundary §2a drew for splices, reached from the other side.
>
> **Ten twins need no fence at all**, and they are not the audit-only cases one
> would guess. See `Tests/AmbiguousMiddle.lean`: `readC` ACCEPTS them (they are
> pure by the kernel's own judgment), `needsRuntime` agrees, and `checkProgram`
> REJECTS them. All three are correct, because ⇝ and ⇒ are different arrows. The
> surface takes the ⇝ reading and asks nothing; the suite's `progRejects` supplies
> the ⇒ reading explicitly. **No classifier could have decided these** — it would
> mean deciding which arrow the author meant, and M29 γ is explicit that this is
> not a property of the term.

## 3. Invariants and non-goals

- **Checker semantics byte-identical.** The breadcrumb is written and read only for diagnostics; every accept/reject decision is unchanged. The differential harness must not notice any of this.
- **Kernel representation unchanged.** No positions in `Term`/`Val`; `alphaEq`, `beq`, caches, conversion all untouched.
- **Trust story unchanged.** `checkFn` is the same function; running it earlier proves nothing different. The executing machine and differential are unaffected.
- **Non-goal:** error *recovery* (checking past the first error to report several). Path-sensitive interpretation makes multi-error reporting a genuine design problem (which paths continue?); not in scope.

## 4. Costs and risks, stated

- **Elaboration latency**: every edit re-checks the module's decls in the server. Current direct-proving checks are ms-class (native via precompile); the deferred-check attribute fences the heavy legacy baselines. If a future decl crosses ~1 s at elab time, that is a measurement to report, not a reason to pre-build caching.
- **`evalExpr` is `unsafe`**: standard for reflective elaborators, contained in one function, and the value it produces is immediately re-checked by the very checker it feeds.
- **Negative-suite migration** is the largest mechanical cost (est. one focused session) and the highest-value hygiene: after it, a lying decl failing to elaborate is *tested by the build itself*.
- **Breadcrumb discipline**: exactly two update sites (spine step, arm entry). A third site added ad hoc without a span-table entry silently misattributes — the span table lookup should therefore fail loudly (attribute to the decl header and say "unmapped path"), never guess.

> **ADDENDUM — the traps, carried forward from all three implementations.** These
> cost real time each round and are cheap to avoid if read first.
>
> 1. **Heartbeats count ALLOCATIONS, not seconds.** A heavy check inside the
>    elaborator dies as a `maximum recursion`/`isDefEq` timeout that names
>    something unrelated. The message misdirects; the cause is the check.
> 2. **A `#guard_msgs`-guarded FAILING `def` still gets added, with a `sorryAx`
>    body, and panics on import under `precompileModules := true`.** So a
>    should-fail probe must not bind a constant. Use
>    `#guard_msgs in #check (prog check{ … } : Term)`. The demo file is written
>    entirely in that shape for this reason.
> 3. **Lean 4.16: a quotation in argument position inside a `partial mutual` block
>    makes the kernel reject the whole block** with "unknown free variable
>    `_kernel_fresh.N`". Keep the key builders outside the walker's mutual block —
>    which is better structure anyway, since it puts the key normal forms in one
>    place.
>
> The lookup-fails-loudly rule in the bullet above is implemented as written: an
> unmatched breadcrumb reports at the program with "no span for the failing
> statement — this is a span-table gap, please report it", and a key that matches
> twice reports the first occurrence and says so. It never guesses.
>
> **`evalExpr` is `unsafe`** (the bullet above): unchanged and uneventful across
> three implementations. It is contained in two functions and the value it
> produces is handed straight to the checker that validates it. The one hazard is
> not unsafety but **openness** — see §2a: an open `Expr` reaching `evalExpr` takes
> a kernel error, so the closedness test is what stands between the two, and it has
> to cover the return type as well as the body.

## 5. Module map

| Piece | Where |
|---|---|
| Command elaborator, `evalExpr`, registry write, check-then-`addDecl` | `DeclMacro.lean` → grows an elab entry point (surface syntax unchanged — same `decl{}`) |
| Span-table emission (statement walk) | `Uni.lean` (`elabUBlk` — already holds each statement's `TSyntax`) |
| Registry (name ↦ `Decl`) | new small `EnvExt.lean` |
| `St` breadcrumb + two update sites + `throwErr` carrying it | `Machine.lean` |
| Diag-returning `checkFn` variant | `Boundary.lean` |
| `decl_rejected!` should-fail wrapper | with the elaborator |

> **AMENDED — the map as built.** Three of the six rows named files that no longer
> exist (`DeclMacro.lean`, and `Decl`/`checkFn` with them), and one named a file
> that was never written (`EnvExt.lean`, see §1.A). The shipped map:
>
> | Piece | Where |
> |---|---|
> | Term elaborator, `evalExpr`, check, `throwErrorAt` | **new `ElabCheck.lean`** — declares `prog check { … }` |
> | Span side channel (`SpanAcc`, `UM`, the filing helpers) and its emission | `Uni.lean` (`elabUBlk`/`elabUTerm` — they hold each statement's and argument's `TSyntax`) |
> | `St` breadcrumb, `Diag`, `stmtKeyOf`, the note helpers, `exploreD`/`explore` | `Machine.lean` |
> | `auditPathsD`/`auditPaths` | `Boundary.lean` |
> | `checkProgramDiag`/`checkProgram` | `Program.lean` |
> | Should-fail assertions | no wrapper needed — `#guard_msgs in #check (prog check{ … } : Term)` |
>
> **`ElabCheck.lean` is a new module and could not have been anything else.**
> `Program.lean` uses `prog{ Unit }` as a default argument, so it already imports
> `ProgMacro`; putting the checking elaborator in `ProgMacro` — where the plan's
> "same file, grows an elab entry point" would put it — is an import cycle,
> because the elaborator calls `checkProgramDiag`. Above `Program`, not beside
> `prog{ }`, is the honest layering.
>
> **`stmtKeyOf` is applied at lookup, not in the emitted key**, for the same class
> of reason: `Uni.lean` is above `Machine.lean`, so a quotation naming
> `Dllbc.stmtKeyOf` there produces an identifier that cannot resolve where the key
> is finally elaborated (it survives as `Dllbc.stmtKeyOf✝`). Keys are filed raw and
> normalized by the consumer, which is free — `stmtKeyOf` is idempotent — and
> applies to statement keys only, since an argument that happens to be a `match` is
> an expression and not a statement whose continuation should be dropped.

## 6. Defaults taken (veto here if wrong)

1. **Same surface, upgraded in place** — `decl{}` stays `decl{}`; no parallel `decl!{}` era, because the suite conversion history says two surfaces means a reader must learn both.
2. **Headline kernel artifacts kept** alongside elab-time checking (see S4) — durability over minimalism, at millisecond cost.

> **AMENDED — default 1 is REVERSED, and the reason is a change in what the brace
> means.** An earlier draft takes "same surface, upgraded in place": elaborating a
> program checks it, with `defer_check` to opt out. That was right while `prog{ }`
> meant *a program* and `pure{ }` meant *a term*. **M29 γ merged them.** The
> surviving brace delimits an arbitrary term — and in its own header's words, "a
> term's fragment is not a property of where it was WRITTEN, it is a property of
> which arrow CONSUMES it".
>
> Measured before deciding: **1701 `prog{ }` sites**, of which `StdLemmas` alone
> is 450 types and proof terms. `checkProgram` has no business ⇒-walking a `Π`, so
> upgrading the brace in place would reject most of the corpus for a reason that
> has nothing to do with the corpus being wrong. The brace can no longer say
> "check me". The word `check` says it:
>
> * `prog{ … }` — unchanged, at all 1701 sites. This port converts nothing.
> * `prog check { … }` — the ⇒-walk, where moves, borrows, argument types and
>   calls are rejected. This is where essentially all the localization value is.
> * `prog check -> τ { … }` — the walk **and** the audit, since the audit is the
>   one check that needs a return type.
>
> The reference branch's own decision "the walk is the default; the audit needs a
> type" is preserved exactly; only the thing that opts *in* to the walk moved from
> the brace to a word. **`defer_check` is therefore gone**, and not replaced: under
> opt-in, the fence is declining to write `check`, so a lying twin, a heavy check
> and a never-checked scaffold all need no marker at all. §2b counts what that is
> worth — 203 rejection twins that the old branch fenced by hand now need nothing.
>
> Default 2 (headline kernel artifacts kept) stands, and is now structural rather
> than a choice: elaboration-time checking is ephemeral, the `native_decide`
> artifacts are durable, and with checking opt-in the two never contend.

> **AMENDED AGAIN — default 1 is RESTORED, and the amendment above is the one
> that was wrong. `prog{ }` checks.** The opt-in design shipped and was then
> superseded, so this doc has now argued both sides; what follows is why the
> second argument beats the first, since a reader is owed that rather than just
> the verdict.
>
> The opt-in argument's premise was that the brace cannot say "check me" because
> most of its 1701 sites are types and proofs. True — but it does not follow that
> the AUTHOR must say it. **The content already says it.** `Term.needsRuntime`
> reads `readC`'s refusal list structurally, and that list *is* this calculus's
> definition of the pure sub-grammar (§1.3). So the brace does not have to carry
> the information and neither does the author: the block is classified, and the
> checker it gets follows from what is in it. This is the **information rule**:
>
> | content | ascription | check |
> |---|---|---|
> | classifies as a program | none | the ⇒-walk |
> | classifies as a program | `-> τ` | the walk AND the audit at `τ` |
> | pure | `-> τ` | `hasTypeT` against `τ` |
> | pure | none | nothing — no specification exists anywhere |
>
> The last row is the one that dissolves the opt-in argument entirely: a `Π` in
> `StdLemmas` is not ⇒-walked, not because it declined to write `check`, but
> because it is pure and states no type, so **there is no question to ask**. That
> is information absence, not policy.
>
> **What it costs, measured, and this is the honest part.** The annotation does
> not disappear, it INVERTS: `prog defer_check { … }` is now written at **275
> sites across 18 files**. §2b predicted 107. The gap is a class §2b did not have
> — *program fragments*, blocks that are closed and syntactically programs but
> whose callee prefix is supplied by a Lean-level assembler (`withPool (prog{ … })`),
> so checking them where they are written asks about a program that has not been
> assembled yet. 84 of the 275 are that class.
>
> **So the trade is 275 fences against 1701 unannotated sites**, and it is worth
> taking for a reason the count does not show: under opt-in, a program that was
> never converted is silently unchecked, and nothing anywhere says so. Under
> auto-checking, the unchecked set is *enumerated in the source* — every one of
> the 275 is visible, greppable, and has to be justified when it is added. The
> failure mode moves from invisible to explicit, which is the same trade §2b's
> own "migration progress bar" was reaching for and could not get.
>
> **`defer_check` is therefore back**, and it is the only annotation the design
> asks anyone to write. `prog check` is retired and not replaced: one surface.

## 7. Review checklist — what a merge must run

The default build is not the whole gate. One target is deliberately outside it and
must be run by hand (or by CI) before this branch merges, and before any later
change to the fragment boundary merges.

**REQUIRED: `lake build Dllbc.Tests.FragmentAgreement`.**

*What it asserts.* That `Term.needsRuntime` — the structural classifier the
surface uses to decide which checker a block gets — and `readC`'s refusal list —
the kernel's own ⇝ judgment — give the same verdict on the `prog{ … }` blocks it
enumerates, in the one direction where they must (no over-fire), and that every
disagreement is a *state* refusal rather than a *grammar* one. Two readings of one
boundary drift unless something asserts they agree; this is that something.

*Its scope is a hand-written list, and the list is stale.* `corpus` names 1096
defs one at a time and there is no generator, so it does not grow when the corpus
does. The rebase onto main's hashmap flagship added roughly 340 blocks it does not
name — the whole `Dllbc.Tests.HashMap` namespace, plus `HashMapDiff` and
`HashMapPin`. Passing therefore means "the two readings agree on those 1096", not
"on every block". **Open review item:** extend the list (≈340 more reflector runs
on top of the current 32 s) or write the generator that keeps it honest. Not taken
unilaterally because it changes what the merge check costs.

*Why it is not in the default build.* It costs **+65 s on a from-scratch suite**
(314 s → 379 s, +21%) because it runs the reflector over all 1096 blocks. The
thing it watches — `readC`'s refusal list — changes when someone deliberately
edits the fragment boundary, which is a **once-a-milestone event, not a
once-an-edit one**. A guard against a deliberate, rare, reviewed change belongs at
the point where changes are reviewed. Charging every incremental build 21% to
watch for it puts the cost on the wrong side of the frequency, and the cheaper
alternatives considered (sampling the corpus, dropping the guard for a comment)
both weaken the assertion rather than relocating it. Relocation keeps the guard at
full strength and moves only *when* it is paid for.

*The failure it must not be allowed to have.* Being outside the default target
means it can rot silently. That is the trade being made, and the mitigation is
this checklist entry plus the note in `Dllbc.lean` where the import would
otherwise be — both of which point at the target by name.

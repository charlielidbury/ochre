# Plan: elaboration-time checking, and errors that point at source

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

### B. Positions on a side channel — the kernel term stays position-free

The tempting design — a span on every `Term` node — is the wrong one: it bloats the representation, threatens `beq`/`alphaEq`/every cache keyed on terms, and makes conversion answer questions about metadata. **Invariant of this plan: `Term` and `Val` change by zero bytes.**

The observation that makes this cheap: the checker is a *statement-driven interpreter*. `readR` walks the body's `letIn`/`seq` spine structurally, and forks at `matchE` arms — so **the checker's position in that walk already identifies a statement**, and its existing path-sensitivity already records the arm choices. A breadcrumb `(spine-index list, arm-trail)` is derivable from the walk the interpreter performs anyway:

- The elaborator, while walking `ublk` statements (it holds each statement's `TSyntax` today — that is where `throwErrorAt` already gets its spans), additionally emits a **span table**: `(statement path ↦ source span)`, carried alongside the emitted `Decl` (a parallel array; not inside the `Decl`).
- The checker's `St` gains a diagnostic breadcrumb field — the current statement path — updated at exactly one site (the spine-walk step in `readR`, plus the arm entry in the match dispatch). `throwErr` includes it. This is *diagnostic metadata, not σ-bearing state*: no value is observed across a refinement, so the swept-state principle does not apply and `refineSym` is untouched.
- The elaborator catches `(breadcrumb, message)`, maps the breadcrumb through the span table, and throws at the right `Syntax`.

Statement granularity is the 90% win: "this `let`, this call, this match arm" — with the **path trail in the message body** ("on the path where `leb x p ⇒ True`, `n ⇒ S _`…"), because under path-sensitive checking the same statement checks many times and the trail is half the diagnosis.

### C. The error surface

`Err` stays `String` at the boundary everyone knows; internally `checkFn` gains a variant returning `Except (Breadcrumb × String) …`. The audit's errors (return-type conversion failures) attribute to the **return-type syntax** — the elaborator has that span — with the conjunct's path in the message. Telescope errors attribute to the parameter binder. Nothing about what the checker *rejects* changes; only where the rejection lands.

---

## 2. Staged delivery

**S1 — decl-granularity (small; do first).** Command elaborator + `evalExpr` + registry + `checkFn` at elab time + `throwErrorAt` on the declaration header. No span plumbing at all. Already transformative for the workflow: a failing decl is a red squiggle on its own name, in the IDE, at edit time — no `#eval` round-trip; and call tables come from the registry.

**S2 — statement-granularity (the payoff).** The span table from the `ublk` walker, the `St` breadcrumb, the path trail in messages. One elaborator site emits spans; one interpreter site maintains the breadcrumb.

**S3 — sub-term granularity for types and pure proofs (only on demonstrated pain).** `hasType` errors inside a big cited proof term currently point at, at best, the statement that consumed it. Extending spans into the pure fragment means span-tagging binder/`elim`-arm/application-spine positions from `pure{}`'s walker and threading a breadcrumb through `hasType`. Heavier, and S2 may make it unnecessary in practice — StdLemmas authors get their errors at the `chk` probe for the lemma itself, which is already local. Decide after living with S2.

**S4 — suite migration.**
- *Positives*: elaboration **is** the check; the `#eval … = OK` lines become redundant and are dropped (a handful kept as CI belt-and-braces).
- *Negatives — the suite's soul*: a lying twin must now *fail to elaborate*, which is asserted with Lean's own `#guard_msgs` idiom (or a thin `decl_rejected! "needle" { … }` wrapper command around it, matching on the error substring exactly as `checkFnErr` needles do today). Mechanical migration, roughly two dozen twins.
- *Heavy checks*: the M22 conformance baseline (54 s compiled per check) must not run on every elaboration of its module. Two tools, both existing patterns: a per-decl `(defer_check)` attribute that keeps the legacy emit-value-only behaviour (check stays in an explicit `native_decide` as today), and — if wanted later — an elab-time cache keyed on `alphaEq` of the decl + its table, the exact trick the S19 `native_decide` cache already proved.
- *Kernel artifacts* (**default taken, flag to veto**): the headline theorems — both quicksorts' `checkFnOk … := by native_decide` — are **kept** as kernel-checked artifacts even after elab-time checking subsumes their UX role. Elab-time checking is ephemeral (an elaboration side effect); the flagship claims keep their durable, kernel-accepted form. Cost: those checks run twice; both are milliseconds.

---

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

## 5. Module map

| Piece | Where |
|---|---|
| Command elaborator, `evalExpr`, registry write, check-then-`addDecl` | `DeclMacro.lean` → grows an elab entry point (surface syntax unchanged — same `decl{}`) |
| Span-table emission (statement walk) | `Uni.lean` (`elabUBlk` — already holds each statement's `TSyntax`) |
| Registry (name ↦ `Decl`) | new small `EnvExt.lean` |
| `St` breadcrumb + two update sites + `throwErr` carrying it | `Machine.lean` |
| Diag-returning `checkFn` variant | `Boundary.lean` |
| `decl_rejected!` should-fail wrapper | with the elaborator |

## 6. Defaults taken (veto here if wrong)

1. **Same surface, upgraded in place** — `decl{}` stays `decl{}`; no parallel `decl!{}` era, because the suite conversion history says two surfaces means a reader must learn both.
2. **Headline kernel artifacts kept** alongside elab-time checking (see S4) — durability over minimalism, at millisecond cost.

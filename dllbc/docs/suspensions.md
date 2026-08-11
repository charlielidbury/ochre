# M32: One syntax, one semantic domain — closures are the only suspensions

**Status: UNDER CONSTRUCTION — design under review with the user; this revision
records the capture model the user stated and the review converged on (raw closures
at rest; cooking derived, not chosen). Depends on: M31 Stage A (merged), Stage C
(at the merge gate).**

## 0. Motivation: three inherited problems, and what does NOT need fixing

M32 is the representation milestone extracted from M31 (functions-are-comptime.md §5).
It exists to fix three things:

  1. **The mixed domain.** `Val` embeds the pure syntax so that normalized-but-open
     terms have somewhere to live at rest; every value traversal walks a tree that is
     sometimes semantics and sometimes syntax; E3 existed only because of this blur.
  2. **Two λ species.** Pure λs evaluate to Pure.lean closures; imperative λs to
     `Val.rfn`. One language-level λ wants one value form — and gets one (§2).
  3. **The id machinery** (E2): frame windows, `shiftVars`, `progBase` arithmetic —
     replaced by name-keyed newest-wins Ω, made safe by Stage 0's pop-with-drop.

Two things explicitly do NOT need fixing:

  * **Nothing except a λ captures.** A non-binder right-hand side (`let L = Len l`)
    evaluates at its own event — snake_case citations resolved to snapshots, which
    the snapshot semantics REQUIRES — and stores a value. Only a λ body awaits
    something (its arguments; for an imperative body, its ⇒-entry), so only a λ
    suspends.
  * **Nothing benefits from lazy *bindings*.** Stored non-λ knowledge is normalized
    at rest; `convert` is `==`/`alphaEq` on canonical forms; the sweeps run over
    material occurrences. (λ *bodies* are different — §2.2 — and that difference is
    the whole design.)

**The model in one sentence: `Term` is the only syntax; `Val` is a small semantic
domain used transiently; every λ value is a closure `(ρ, raw body)` — the one
suspension form, replacing Pure.lean closures AND `rfn` — where ρ is the comptime
slice of Ω at formation; and cooking is driven entirely by demand, with exactly one
persistent case, derived in §3.**

## 1. What dies here

The mixed domain (Val's syntax embedding); `Term.lamR` and `Val.rfn`; `callV` (app
spines; nullary `fn` desugars to `λ (U : Unit)`); `Var.comptimeRhs`'s carve-outs (the
let-arrow invariant becomes exceptionless); Stage A's backstop scatter (one
structural fact, §2.5); the pure lift's λ case; the modeless-pure-binder exemption
(§2.1); and E2's id machinery.

## 2. Target representation and semantics

### 2.1 The universal binder convention (user ruling)

The capitalisation convention reaches EVERY binder — λ and Π binders included; the
old exemption ("pure binders are modeless") dies. **A capital binder is comptime**:
erased, its argument snapshot-read (⇝) at application, capturable by inner λs. **A
lowercase binder is runtime**: its argument ⇒-read (moved/consumed or loan-seeded) at
entry, NOT capturable — the capture rule with no special cases. `λ N. λ M. Add N M`;
the inner λ captures `N` because it is capital, by the same rule as everything else.
A lowercase-binder λ remains meaningful — `λ (l : List Nat). …` consumes its data
argument where `λ (L : List Nat). …` snapshot-reads it — so binder case is
load-bearing at argument-reading uniformly (M31 §2.2's rule reaching its last
position). Migration: the stdlib's pure binders capitalise (mechanical; elim motives
included).

### 2.2 The capture model (user's two rules)

  1. **Formation**: when ⇝ evaluation reaches a λ, the closure captures ρ — the
     evaluation environment, which began as the comptime-filtered slice of Ω and
     grew binder entries as evaluation descended. Formation-time evaluation of the
     body is a CHECK (the body type-checks against its binders/ascription); the
     stored value is `(ρ, raw body)` — the syntax as written, not a cooked form.
     The capture guard becomes a capture *filter*: knowledge-only by construction.
  2. **Application, both fragments**: evaluate the body under captured-ρ plus the
     arguments. For a pure body that is ⇝ evaluation; for an imperative body it is
     ⇒-entry — a fresh frame in the LIVE store (effects act on the world at call
     time; captured ρ supplies knowledge only, state arrives through arguments).

There is no difference between the fragments in the closure or application
mechanics; the single irreducible difference is what evaluating the body MEANS
(pure reduction vs the effectful walk), recomputed by body classification at
application and seal — a property, never a species tag, never a substitution.

Store-wide REFINEMENT sweeps (σ := v) rewrite captured ρ's like everything else,
and later evaluation agrees — substitution commutes with evaluation (§3).

### 2.3 At rest: canonical Terms for knowledge, raw closures for λs

Non-λ knowledge at rest is a canonical Term (σ's as reserved `§`-names; comparison
by `alphaEq`/`==`; swept by Term-level `substP`/abstraction). λ values at rest are
closures per §2.2. Conversion involving a λ value cooks TRANSIENTLY (evaluate the
body under ρ + a fresh `§`-binder, read back, compare) — on demand, cost measured
as noise (checker = 1.3% of build).

### 2.4 One λ, the let-arrow invariant, ⇝-sealing

One λ former; formation is ⇝ (closure creation — ⇒ cannot construct a function).
**Capital `let` ⇝-reads its RHS, lowercase `let` ⇒-reads it — zero carve-outs.**
The seal is ⇝-evaluable: check half by conversion (pure) or the audit invoked as a
judgment (imperative — it already runs in its own fresh store); forget half by
structure — the sealed value is the **seal SITE applied to its captured inputs**, a
structured neutral, deterministic and distinguishing (`fsig` keys by site).

### 2.5 No function in a runtime slot — structurally

λ formation is ⇝-only, so the invariant needs ONE enforcement point: the pure
lift's result must be data, not a function (`let f = Add 1` fails there). Stage A's
backstop is deleted; the corpus's lowercase partial-application bindings migrate
capital in the same commit.

### 2.6 Application surface: spines only

`callV` retires for app spines (nullary via Unit-desugar), preserving the
arrow-keyed mint-vs-remember split (§12 decision 5) and saturation for imperative
entry (§12 decision 4). Capture reaches M31-deferred generality — a fn body cites
enclosing comptime data, escape-safe because the closure carries its knowledge
(Stage C's measured narrowing: program-scope citation already works today; the
closure is what makes the ESCAPING case safe). Requires the fn body scope fix
(params-only elaboration context retires; the id-collision that gated it is void
under name-keying).

## 3. The cooking schedule — derived, not chosen

**The criterion: a store-wide sweep is safe iff it commutes with evaluation, and a
sweep may only rewrite occurrences that are material when it runs.**

  * **Substitution (refinement, σ := v) commutes** — atom-keyed; every
    representation preserves atoms; rewriting ρ and re-evaluating later agrees with
    cooking first. Raw closures are fully correct under it. This is most sweeps.
  * **X-Gen's generalization (spine ↦ fresh σ) does not commute** — compound-keyed;
    a raw body + ρ holds the spine's INGREDIENTS and can re-mint the spine after
    the sweep has passed, speaking pre-generalization vocabulary while the branch
    speaks σb: propositionally linked by the branch equation, definitionally
    divergent — the corpus's `Refl`s die. This is M30's measured count-equation
    failure mode, and it is the ONLY non-commuting operation in the system.

The schedule follows as the criterion's minimal fixpoint: **cooking is persistent
exactly at generalization events, and nowhere else.** When a generalization sweep
fires (a stuck-scrutinee split — the system's rarest sweep), the λ closures it
reaches are cooked (body evaluated under ρ + fresh `§`-binders), swept in cooked
form, and the cooked form written back; every other closure, and every closure
before its first generalization, lives raw and revives its original syntax at every
application, per §2.2. Imperative bodies are exempt entirely — they never
participate in conversion (audited once at formation, then only entered), so they
are never cooked, ever.

Rejected alternatives, for the record: cook-at-formation (pre-bakes everything;
user-rejected); normalize-at-every-split (pays at commuting sweeps that need
nothing); assumption-indexed evaluation (smart case/Zombie — coherent, never
mainstream, makes conversion path-relative; rejected with precedent at #19);
propositional-only generalization (M30's wall). Optimization note, not requirement:
a generalization need only cook closures whose ρ mentions σ's in the abstracted
spine's support. **Canary: quicksort's count equation.**

## 4. Also landing here (from the M31 ledger)

The `piAgree` agreement path for passing borrow-moded-signature functions (E4's
measured gap); `sealFn` renamed to the audit half of ascription, seal dispatch by
body classification; the L-suffix lemma/fn namespace condition (Stage C: currently
an unenforced convention — under name-keying it becomes a real check).

## 5. Staging

Corpus green at every stage; representation stages differential to exactly zero;
rule stages have enumerated flips only.

**Stage V — viability probe (before any dispatch).** One agent, three cheap bets:
(a) newest-wins name-keyed Ω against `checkRFnBody` + the executing differential
(E2; fallback dual-key `Var`); (b) readback-to-Term with `§`-σ-names against the
comparison sites and one X-Gen path; (c) raw-closure conversion-on-demand against
the three `alphaEq` sites (cook-transiently correctness + cost).

**Stage R1 — the domain split.** Readback emits Terms; at-rest non-λ knowledge
becomes canonical Terms; sweeps re-target to Term level; Val loses its syntax
embedding. Zero differential.

**Stage R2 — one λ, one closure.** `lamR`/`rfn` fold into `(ρ, raw body)`;
formation captures the filtered slice; application per §2.2; cook-at-generalization
with write-back; universal binder convention + stdlib binder migration; capture
generality + body scope fix. Zero differential except enumerated flips (binder-case
migrations, capture legality).

**Stage R3 — arrows exceptionless.** ⇝-sealing (site-σ); `comptimeRhs` carve-outs
deleted; no-⇒-λ + backstop demolition + the partial-application migration.

**Stage R4 — spines + sweep.** `callV` retires; §1's deletion list completed; E2's
id machinery removed; docs/logs currency.

## 6. Sharp edges to interrogate before dispatch

  * **σ-names in Terms**: reserved-namespace unwritability end to end; `substP`'s
    rebinding guard vacuous for `§`-names (nothing rebinds them) — verify.
  * **Seal-site identity**: stable across macro expansion and α-canonicalization.
  * **Audit-from-⇝ reentrancy**: state isolation of the audit's fresh store.
  * **Cook-at-generalization mechanics**: cooking evaluates bodies mid-sweep —
    confirm it cannot cascade (cooking normalizes; it cannot trigger a split) and
    that write-back composes with the sweep's own traversal order; post-cook, the
    raw form is gone — confirm nothing (error messages, pretty-printing) depended
    on showing source syntax for cooked closures.
  * **Obligations**: owed types swept wherever they live — the Term-level sweep
    must reach O (Stage 0's `firstHeldBorrow` precedent: enumerate the traversal
    set, don't assume it).
  * **Executing mode**: never converts — confirm no executing path compares, so
    closures in executing state are entry-only.
  * **Universal binder migration**: stdlib λ/Π binders capitalise — mechanical, but
    elim arms bind `ih`-style names the macro mints; confirm minted binders follow
    the convention or are `§`-reserved.

## 7. Non-goals

Borrow refounding (shape/contract split, store-relative types — SUGGESTIONS.md,
post-M32); surface juxtaposition syntax (interacts with R4's spines — decide there
or defer); consistency proofs; lazy *bindings* (only λ bodies suspend — §0);
assumption-indexed evaluation (rejected with precedent, §3).

# M32: One syntax, one semantic domain — closures are the only suspensions

**Status: UNDER CONSTRUCTION — design under review with the user. This revision
supersedes the doc's first draft, which proposed lazy `(Term, ρ)` storage for ALL
comptime bindings; the user's review dissolved that ("why does anything apart from λ
need to capture? why evaluate anything else lazily?") and the answers below are the
corrected architecture. Depends on: M31 Stage A (merged), Stage C (in flight).**

## 0. Motivation: three inherited problems, and what does NOT need fixing

M32 is the representation milestone extracted from M31 (functions-are-comptime.md §5).
It exists to fix three things:

  1. **The mixed domain.** `Val` embeds the pure syntax (`pvar`, `pi`, `lam`, `app`,
     … as Val constructors) so that normalized-but-open terms — a λ's body under its
     binder, a stuck spine — have somewhere to live at rest. Every value traversal in
     the checker therefore walks a tree that is sometimes semantics and sometimes
     syntax; E3's whole payload question existed only because of this blur.
  2. **Two λ species.** Pure λs evaluate to Pure.lean closures; imperative λs to
     `Val.rfn` (names + suspended `Term`). One language-level λ (M31's model) wants
     one value form.
  3. **The id machinery** (E2): frame windows, `shiftVars`, `progBase` arithmetic —
     replaceable by name-keyed newest-wins Ω now that Stage 0's pop-with-drop
     guarantees ended scopes leave no stale entries.

Two things explicitly do NOT need fixing, and the design refuses to touch them:

  * **Nothing except a binder body needs capture.** A closure `(ρ, body)` is forced
    exactly where evaluation must stop at a binder: a pure λ/Π/Σ body (evaluation
    waits for the argument) and an imperative body (evaluation IS ⇒-entry, a later
    event). A non-binder right-hand side — `let L = len l` — has nothing to capture:
    it evaluates at its own event, snake_case citations resolved to snapshots
    (eagerness the snapshot semantics REQUIRES), result stored as a value.
  * **Nothing benefits from laziness.** Stored knowledge is normalized at rest today,
    and that eagerness is load-bearing: `convert` is `==` on canonical forms, and the
    store-wide sweeps (refinement, X-Gen abstraction) are correct because every
    occurrence they must rewrite is materialized when they run (see §3 — abstraction
    does not commute with evaluation, so anything unevaluated at sweep time is a
    silent miss, M30's measured count-equation failure mode). Laziness would buy
    unmeasurable time (the checker is 1.3% of the build) and cost a
    normalize-at-splits/write-back apparatus purely to repair what eager-at-rest
    gives free. Dropped.

**The model in one sentence: `Term` becomes the only syntax — EVERY at-rest value is
a self-contained canonical Term (pure λs with normalized bodies, imperative λs with
raw ones) — and `Val` shrinks to a true semantic domain whose closures exist only
transiently inside the evaluator, replacing both Pure.lean closures and `rfn`.**
#19(a)'s confinement becomes a totality rather than a policy: closures never leave
the evaluator at all.

## 1. What dies here

The mixed domain (Val's syntax embedding — `pvar`/`pi`/`sigmaT`/`lam`-with-syntax-
bodies/`idT`-as-stored-syntax leave Val); `Term.lamR` and `Val.rfn` (one λ, one
closure); `callV` (app spines; nullary `fn` desugars to `λ (U : Unit)` per the E6
ruling); `Var.comptimeRhs`'s seal/λ carve-outs (the let-arrow invariant becomes
exceptionless); Stage A's backstop scatter (replaced by one structural fact, §2.5);
the pure lift's λ case (⇒ can no longer construct a function); and E2's id machinery
(minting, frame windows, `shiftVars`/`shiftBindersK`, `progBase` arithmetic, `keep`
sets).

## 2. Target representation and semantics

### 2.1 The two domains

**`Term`** — the whole language, plus one addition: σ's appear in Terms as reserved
`§`-names (M30's reserved namespace, elaborator-unwritable), so a canonical Term can
mention a symbol (`Len «§σ42»`) without a machine-value leak. **`Val`** — the
semantic domain: constructors; neutral spines (head = a name, a σ-name, a seal-site,
or a recursor constant; arguments = values); closures `(ρ, Term)` with knowledge-only
environments; borrow/loan markers; ⊥. No syntax embedding.

### 2.2 At rest: canonical Terms, eagerly

A comptime binding's RHS is evaluated at the binding event (as today) and stored in
**readback form: a canonical Term** — closure-free, binder names canonicalized
(`§0, §1, …`), σ's as reserved names. Comparison is `Term.alphaEq`/`==` on canonical
forms (three sites already exist). The store-wide sweeps re-target from Val trees to
Terms: refinement is `substP` at a σ-name (atom-keyed, commutes with evaluation, §3);
X-Gen abstraction is Term-spine abstraction (the Term-level machinery `substP`,
`alphaEq` already exists; `abstractInto` gains a Term twin and loses its Val
original). Runtime bindings hold runtime `Val`s (data, markers) — never a function
(§2.5).

There is NO at-rest closure — not even for imperative λs (user review: the species
distinction dies entirely, not mostly). An imperative λ's captured environment is
**discharged at formation**: `substP` its PascalCase names by their canonical-Term
values into the body. This is not the substitution M30 banned (index arithmetic
under runtime ids); it is name-keyed splicing of knowledge at canonical `§`-names,
capture-free by the reserved namespace, and for immutable bindings it is
observationally identical to env capture (§2.4 of functions-are-comptime.md). The
stored imperative λ is therefore a self-contained Term whose body is raw (never
normalized — entering it is ⇒'s job); it is opaque to conversion by design — the
audited-not-conversed line — and fully sweepable as the Term tree it is. What
distinguishes pure from imperative at rest is only how cooked the body is; nothing
structural. The pure-vs-imperative fork is recomputed where it matters — at
application and at the seal — by BODY CLASSIFICATION (does the body contain
effectful formers), a property, not a species tag.

### 2.3 Evaluation: eval : ρ → Term → Val, readback : Val → Term

Classic NbE shape. `eval` produces semantic values (closures at binders); `readback`
canonicalizes at the store boundary — exactly today's discipline with "canonical
form" changing type from Val-syntax to Term. Transient closures inside one evaluation
are unchanged from M30's machinery in spirit; what changes is that they never need a
syntax-embedded Val to be read back INTO.

### 2.4 One λ, the let-arrow invariant, ⇝-sealing

One λ former; formation is ⇝ (closure creation — knowledge). **Capital `let` ⇝-reads
its RHS, lowercase `let` ⇒-reads it — zero carve-outs.** For `fn F = (λ… : Π…)` this
requires the seal be ⇝-evaluable:

  * Check half: conversion for pure bodies; for imperative bodies the audit
    (`checkRFnBody`) becomes a judgment invocable from ⇝ (it already runs in its own
    fresh store).
  * Forget half — generativity resolved by structure: the sealed value is the **seal
    SITE applied to its captured inputs**, a structured neutral (readback: a Term
    spine headed by the site's reserved name). Deterministic — evaluation stays a
    function, no counter under ⇝ — and distinguishing (a binder-nested seal at
    different instantiations yields different values; the user's correction of
    occurrence-only keying). `fsig` keys by site.

### 2.5 No function in a runtime slot — structurally

λ formation is ⇝-only, so ⇒ cannot construct a function value; the invariant needs
ONE enforcement point (the pure lift's result must be data, not a function —
`let f = Add 1` fails there with the capitalise message). Stage A's backstop is
deleted, not extended; the corpus's remaining lowercase partial-application bindings
migrate capital in the same commit.

### 2.6 Application: spines only; capture at full generality

`callV` retires for app spines (nullary via Unit-desugar), preserving the arrow-keyed
mint-vs-remember split (§12 decision 5): ⇒ call results mint fresh existentials at
the instantiated codomain; ⇝ remembers structured neutrals. Saturation for imperative
entry survives (§12 decision 4). Capture reaches M31-deferred generality: a fn body
may cite enclosing comptime DATA, discharged into the body at formation (§2.2) —
escape-safe trivially, since the stored value is self-contained. Requires the
**fn body scope fix** (bodies elaborate seeing sibling and enclosing bindings; the
`fnElab` id-collision that gated it is void under name-keying).

## 3. The safety criterion (why at-rest stays eager)

**A store-wide sweep is safe only against material occurrences: abstraction does not
commute with evaluation.** Substitution (σ := v) is atom-keyed and commutes — it
propagates through environments and later evaluation is right. X-Gen's abstraction
(spine ↦ fresh σ) is compound-keyed and does not — an unevaluated body can mint the
spine AFTER the sweep passed, leaving later evaluations speaking pre-abstraction
vocabulary: propositionally linked by the branch equation, definitionally divergent,
presenting as flagship proofs failing (M30's count-equation mode — measured, silent).
This criterion is WHY §0 refuses laziness: eager canonical Terms at rest make every
sweep total over what exists, with no normalize-at-splits apparatus. The one
remaining unevaluated thing at rest is the imperative λ's raw body, and it is
hazard-free by construction: it never participates in conversion (audited once, at
formation, with its knowledge already discharged in), and as a Term tree it is fully
material to every sweep. Pure λ values at rest are in readback form (bodies
normalized under their binder — today's discipline, kept). **Canary: quicksort's
count equation.**

## 4. Also landing here (from the M31 ledger)

The `piAgree` agreement path for passing borrow-moded-signature functions (E4's
measured gap); `sealFn` renamed to the audit half of ascription, with seal dispatch
by body classification (meaningful once one former exists); the `fn` refusal
sentinel's diagnosis (already fixed in Stage A) kept working through the spine
transition.

## 5. Staging

Corpus green at every stage; representation stages differential to exactly zero; rule
stages have enumerated flips only.

**Stage V — viability probe (before any dispatch).** One agent, two bets tested
cheaply: (a) newest-wins name-keyed Ω against `checkRFnBody` + the executing
differential (E2's bet; fallback dual-key `Var`); (b) readback-to-Term with σ's as
reserved names against the three comparison sites + one X-Gen path (the §2.2 bet;
fallback is a small syntax embedding retained in Val, which would be a finding, not a
failure).

**Stage R1 — the domain split.** Readback emits Terms; at-rest knowledge becomes
canonical Terms; sweeps re-target (substP-at-σ-name; Term abstraction); Val loses its
syntax embedding. The big rewrite — the E3 traversal set is the checklist. Zero
differential.

**Stage R2 — one λ.** `lamR`/`rfn` fold into the one former; imperative λ values
become self-contained Terms via formation-time discharge (no at-rest closure);
frame-bind-and-walk enters the body with its knowledge already spliced in; capture
generality + body scope fix. Zero differential except enumerated capture-legality
flips.

**Stage R3 — arrows exceptionless.** ⇝-sealing (site-σ); `comptimeRhs` carve-outs
deleted; no-⇒-λ + backstop demolition + the partial-application migration
(enumerated flips: the `let f = Add 1` class).

**Stage R4 — spines + sweep.** `callV` retires; §1's deletion list completed; E2's id
machinery removed; docs/logs currency.

## 6. Sharp edges to interrogate before dispatch

  * **σ-names in Terms**: the reserved namespace now carries load in the one syntax —
    confirm elaborator-unwritability end to end, and that `substP`'s
    stop-at-rebinding-binder semantics is vacuous for `§`-names (nothing rebinds
    them).
  * **Seal-site identity**: stable across macro expansion and α-canonicalization —
    minted at elaboration as a reserved name?
  * **Audit-from-⇝ reentrancy**: state isolation of the audit's fresh store from the
    caller's Ω.
  * **Obligations**: owed types stored as canonical Terms — sweeps must reach O (they
    do today as Vals; the re-target must not skip it).
  * **Executing mode**: never converts; confirm no executing path compares, so
    closures in executing state need entry only.
  * **Term-level sweep completeness**: `abstractInto`'s Term twin must sweep
    everywhere the Val original did — Ω, sctx, O (Stage 0's `firstHeldBorrow`
    precedent: the traversal set grows; enumerate, don't assume).
  * **Formation-time discharge at scale**: splicing captured knowledge into a body
    duplicates trees (a builder citing a large snapshot n times stores n copies) —
    measure on the flagship before declaring it free; and confirm `substP`'s
    stop-at-rebinding semantics does the right thing inside imperative bodies
    (shadowing a PascalCase name inside a body is refused by §2.1 anyway, which
    should make the guard vacuous — verify, don't assume).

## 7. Non-goals

Borrow refounding (shape/contract split, store-relative types — SUGGESTIONS.md,
post-M32, `split_at_mut` as its test); surface juxtaposition syntax (interacts with
R4's spines — decide there or defer); consistency proofs (unchanged scope); laziness
anywhere (refused on the record, §0).

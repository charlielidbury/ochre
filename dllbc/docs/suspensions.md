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
(pure reduction vs the effectful walk), recomputed at application and seal by
**binder-AND-body classification** (R2 correction: a λ is imperative when its body
contains effectful formers OR when a binder names an Ω slot — `fn UseTrans (a,b,c,
p,q) { LeTrans a b c p q }` has a spine-only body and is still ⇒'s, which four
programs caught) — a property, never a species tag, never a substitution.

**ρ's type, corrected by R2 (R1 predicted why without predicting where): ρ is an Ω
SLICE, not a name→Term list.** A λ captures `SetAt`, and `SetAt` is a recursor over
runtime arms — a function value with no Term form (§2.3's §rec) — and a λ captures
λs. For the Term leaves, knowledge-only holds by construction; for the two function
forms it holds by CHECK at the capture (`hasStateMarker`, refused by name). R1's
purchase survives; the "by construction" sentence is scoped to leaves.

Store-wide REFINEMENT sweeps (σ := v) rewrite captured ρ's like everything else,
and later evaluation agrees — substitution commutes with evaluation (§3).

### 2.3 At rest: canonical Terms for knowledge, raw closures for λs

Non-λ KNOWLEDGE at rest is a canonical Term (σ's as reserved `§`-names; comparison
by `alphaEq`/`==`; swept by Term-level `substP`/abstraction). λ values at rest are
closures per §2.2. Conversion involving a λ value cooks TRANSIENTLY (evaluate the
body under ρ + a fresh `§`-binder, read back, compare) — on demand; Stage V measured
it a wash (the raw pair was fastest — `convert` normalizes both sides either way).

**NAMING, as built (R1; coordinator-ratified):** the store skeleton kept the name
`Val` (Machine.lean's 4,600 lines are about store values) and the transient semantic
domain is `Sem` (eleven call sites, all in Pure.lean). Read this doc's "Val shrinks
to a semantic domain" with the two names exchanged: the STRUCTURE is as specified;
the semantic domain is `Sem`, the skeleton is `Val`.

**R1 DECISION — MADE (user ruling): `Term` does NOT grow state formers.** ⊥, loan
markers, and borrow values reach store-wide sweeps, and giving `Term` formers for
them would make a marker grammatically writable — the objection that killed the
union-tree horizon. Instead the store-value type is the **state skeleton**:
constructor structure, ⊥, `loanM ℓ`, `borrowM ℓ ·`, closures `(ρ, Term)`,
**recursor spines over runtime arms** (R1 finding: a function value whose arms are
bodies — no Term can hold it; never-collapsing, index-kind so it copies on read,
`hasType`-rejected as a neutral), and Term LEAVES wherever marker-free knowledge
sits. The collapse is a smart-constructor invariant, not a discipline (R1's
`Val.ctor`: an all-knowledge node collapses to one `know` leaf). Realized deletion:
`capturedMarkers`/`hasStateMarkerEnv` are gone — nbe.md §3.2's capture assertion is
a fact about the types. Sweeps are two-layered (walk the
skeleton; switch to `substP`/Term-abstraction at leaves); a value with no live
markers collapses to a bare Term leaf and re-splits only when state intrudes (a
borrow-mode match pushing field loans in), so the skeleton is exactly as large as
the live state. Consequence, type-enforced: **knowledge cannot contain state** —
the capture filter and the knowledge-only environment invariant become theorems of
the representation, not guards. State containing knowledge (the leaves) remains
possible, which is the correct asymmetry — §3.2's doctrine as a datatype.
Relatedly: the Term-level sweep is mode-SENSITIVE with `.stripCmp` at comparison
sites (the house pattern `piAgree` already uses), where `Val.beq` was mode-blind.

### 2.4 One λ, the let-arrow invariant, ⇝-sealing

One λ former; formation is ⇝ (closure creation — ⇒ cannot construct a function).
**Capital `let` ⇝-reads its RHS, lowercase `let` ⇒-reads it — zero carve-outs.**
The seal is ⇝-evaluable: check half by conversion (pure) or the audit invoked as a
judgment (imperative — it already runs in its own fresh store); forget half by
structure — the sealed value is the **seal SITE applied to its captured inputs**, a
structured neutral, deterministic and distinguishing (`fsig` keys by site).

### 2.5 No function in a runtime slot — REFUTED as stated (R3 finding), subsumed into R3b

**The premise "⇒ can no longer construct a function value" is false: a proof of a
∀-statement IS a λ.** Measured twice by R3, both built and reverted: refusing the
pure lift's function results reds quicksort's count equation (the count-preservation
proof is `λ(§0 : Nat). …`, a proof of a Π), and refusing `readR`'s λ arm reds the
programs that carry proof-λs in Σ components and constructor fields as DATA. The
corpus's lowercase function-valued bindings number SEVEN (measured), all partial
applications of proof-builders (`let cnt = MkL lo hi hcnt`) — and capitalising them
TODAY walls at the fence (`Cnt cannot be ⇒-moved`) because Σ components and argument
positions still ⇒-read; nothing separates them from `let f = Add 1`.

So the invariant's enforcement and the §2.1 binder migration are blocked on the SAME
fact and cannot land separately: a returned proof needs a capital binder, which
needs Σ-component and parameter binder modes to change — which IS the migration.
**§2.5 is subsumed into R3b**, attempted terminally there; `S32Backstop` pins two
accepted programs as tripwires against anyone concluding the rule already holds.
What R3's demolition DID buy at zero cost: three enforcement sites became one
(`refuseFnBinding` at the `let`; `fenceComptime` owns the rule and its advice).

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

**Stage V sharpened the criterion: the split is MATERIALIZED-vs-LATENT, not
raw-vs-cooked.** `abstractInto` already descends captured environments, so a spine
materialized in ρ survives the sweep and raw agrees with cooked; only a spine the
body RE-MINTS from ρ's ingredients diverges (measured: cooked gives `Add σ99 7`,
raw gives `Add (Len σ5) 7` — the pre-generalization vocabulary; cooking before the
sweep repairs it). Consequence: "cook only closures whose ρ mentions σ's in the
abstracted spine's support" is THE rule, not an optimization.

Rejected alternatives, for the record: cook-at-formation (pre-bakes everything;
user-rejected); normalize-at-every-split (pays at commuting sweeps that need
nothing); assumption-indexed evaluation (smart case/Zombie — coherent, never
mainstream, makes conversion path-relative; rejected with precedent at #19);
propositional-only generalization (M30's wall). **Canary: quicksort's count
equation — run by Stage V through the Term-level path with a positive control (the
sabotaged twin goes red at 22 assertions including the count equation itself).**

## 4. Also landing here (from the M31 ledger)

The `piAgree` agreement path for passing borrow-moded-signature functions (E4's
measured gap); `sealFn` renamed to the audit half of ascription, seal dispatch by
body classification; the L-suffix lemma/fn namespace condition (Stage C: currently
an unenforced convention — under name-keying it becomes a real check).

## 5. Staging

Corpus green at every stage; representation stages differential to exactly zero;
rule stages have enumerated flips only.

**Stage V — viability probe: RUN, all three bets VIABLE** (branch `m32-stage-v` @
3a0102d7 — probe artifacts, not for merge; findings addendum there). Highlights that
amend the plan: (a) newest-wins is nine sites, one non-local (`readCWith` flips from
prepend to append — the id collision that forced prepending is void under names);
the frame shift is name-preserving, so **bet (a) rides with R1** while the
id-machinery deletion stays its own commit with its own differential; cost measured
at noise (~1%). The lemma/fn L-suffix convention goes from style to SOUNDNESS
CONDITION under name-keying — R1 adds the check. (b) The `alphaEq` comparison sites
are FOUR, not three (`trivialOwedT` is the fourth — live at R3 where owed types
are). (c) `convert` already cooks transiently — the mechanics need no new code.
**Every representation stage carries a SABOTAGE RUN alongside its green corpus**
(Stage V's zero-divergence result meant something only because the sabotaged twin
went red at 22 assertions — M30's failure mode is silent by construction).

**Stage R1 — the domain split.** Readback emits Terms; at-rest non-λ knowledge
becomes canonical Terms; sweeps re-target to Term level; Val loses its syntax
embedding. Zero differential.

**Stage R2 — one λ, one closure: RUN** (branch `m32-r2` @ 09b18152, stacked on R1;
corpus green; canary run both directions, sabotage control re-run — 21 red including
the flagship). As landed: `lamR`/`rfn` gone; `Val.closure ρ node` the one suspension,
body raw, formation a check; `admitGlobals` revealed as ALREADY the capture filter;
cook-at-generalization support-scoped with write-back; capture generality + scope
fix (the id collision verified-not-assumed — `freeRVars` re-keyed by name, λ binders
bind there only when they bind a SLOT); nullary `fn` Unit-desugar pulled forward
from R4 (forced: `lamTel [] body` = the body, so nullary `fn` and ascription became
one term — the binder is the unwritable `U§ : ⇝Unit`). Known limit recorded, not
new at R2: `abstractInto` matches by binder-NAME `beq` while readback names by
level, so a generalized spine containing a binder misses its own occurrence one
binder deeper — the fix is an α-insensitive key at the abstraction site; filed as a
demand.

**The §2.1 binder migration did NOT land in R2 and becomes its own stage (R3b,
coordinator decision):** R2 measured it — 10,777 lowercase comptime binders in the
flagship alone, ~3,700 λ/Π binders in source — and correctly refused to run it
blind: each rename is scope-sensitive, and capitalising a Π binder in a spec
position deliberately flips `valBinderModes` at every ⇒-application of that type —
§2.1's intent, therefore a behaviour change wanting its own enumerated differential,
not a rider on a representation stage. Sequencing: R3b after R3, before R4 (R4's
`Var.bindsSlot` replacement can only become a case test after the migration — the
coupling is now measured). Meanwhile the fragment keys on `Var.bindsSlot`.

**Stage R3 — arrows exceptionless: RUN** (branch `m32-r3` @ fdb83166, stacked on
R2; corpus green; goldens BYTE-UNCHANGED across six files including σ numbering).
Items 1–2 landed at zero differential: the seal has a SITE (assigned by a boundary
pass — stable across macros and α by construction, asserted); the "structured
neutral" landed INTERNED (a (site, inputs) → σ table, so rendering is identical to
the ⇒-seal's and the audit runs once per (site, inputs) — recorded deviation);
`sealNode` is one rule with two callers and the audit's isolation carries
`sealSites` out with the supplies; **`Var.comptimeRhs` is DELETED** and the
invariant is one sentence, no footnote: *"A capital `let` ⇝-reads its right-hand
side; a lowercase `let` ⇒-reads it."* The executing machine is byte-for-byte the
pre-R3 call. Items 3–4 (no-⇒-λ, backstop derivability) REFUTED as stated — see
§2.5 — and re-staged onto R3b; the demolition's consolidation (three sites → one)
kept. Controls: sabotage red at 21 including flagship and both canary directions;
seal determinism §B with its §C control (same site + different inputs distinguishes
— without which a site-only table would pass §B).

**Stage R3b — the binder migration, now carrying §2.5.** The §2.1 universal-binder
migration (measured: 10,777 flagship binders, ~3,700 source sites, seven
function-valued lowercase bindings), executed as the deliberate behaviour-change
stage it is: capital = binds comptime knowledge (proofs, types, specs,
pure-function values), lowercase = runtime data/borrows; scope-sensitive renames,
per-class enumerated differentials (stdlib pure binders; signature Σ/Π binders —
these flip component/argument reading, which is the intent; telescope proof
parameters; the seven §2.5 bindings). TERMINAL ATTEMPT: with the migration landed,
retry no-⇒-λ and the one-boundary rule; the `S32Backstop` tripwires must flip
deliberately or the attempt reverts and the residual is reported as a finding.

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

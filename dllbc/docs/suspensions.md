# M32: Suspensions everywhere — Term the only syntax, Val a semantic domain

**Status: UNDER CONSTRUCTION — design consolidated from the M31 review
(functions-are-comptime.md's M32 scope ledger and E3's M32 section); not yet
user-ratified as a dispatchable plan. Depends on: M31 Stage A (merged), Stage C
(in flight). Written to interrogate, not to glaze.**

## 0. The model in one sentence

**`Term` is the language's only syntax; `Val` is a small semantic domain; Ω stores
knowledge as suspensions `(Term, ρ)` normalized on demand; and one λ, formed only by
⇝, is the language's one function former.** This is the classic NbE split, arrived at
by the M31 review's chain: skip the `Val ⊕ Term` waypoint (double-touching), then skip
nothing else — the representation lands once, in final form.

## 1. What dies here

The mixed domain (Val embedding pure syntax — the fact that generated M31's E3);
`Term.lamR` and `Val.rfn` (one λ, one closure form); `callV` (app spines; nullary `fn`
desugars to `λ (U : Unit)` per the E6 ruling); `Var.comptimeRhs`'s seal/λ carve-outs
(the let-arrow invariant becomes exceptionless); Stage A's backstop scatter
(`backstopFnRhs`/`backstopFnBinding`/species test — replaced by one structural fact,
§2.4); the pure lift's λ case (⇒ can no longer construct a function); and, via E2's
newest-wins keying: id minting, frame windows (`nextFrame + 128`),
`shiftVars`/`shiftBindersK`, `progBase` arithmetic, `applyRFn`'s `keep` sets.

## 2. Target semantics

### 2.1 The two domains

`Term`: the whole language, elaborated once by the surface. `Val`: constructors,
neutral spines (head + arguments; heads are pvars, seal-sites, recursor constants),
closures `(ρ, Term)` with knowledge-only environments, borrow/loan markers, ⊥. No
`pvar`-as-syntax-tree, no `pi`/`lam`-with-syntax-bodies — binder bodies are closures,
full stop. Readback produces `Term`s (canonical binder names `§0, §1, …` as today).

### 2.2 Ω stores suspensions; the store is name-keyed, newest-wins

A comptime binding holds `(Term, ρ)` — its RHS unevaluated, its knowledge environment
captured (self-contained by M31's citation rule: the Term is σ-free and cites only
PascalCase names, which ρ carries). A runtime binding holds a runtime `Val` (data,
markers) — never a function (§2.4). Keying is E2's option (i): duplicates allowed,
newest entry wins; sound because a body may name only its own binders (capture rule)
and everything crossing frames is ℓ-keyed; made safe by Stage 0's pop-with-drop (an
ended scope's entries are gone, so stale shadowing cannot occur). Checking mode never
has two live frames (calls are abstract), so newest-wins is an executing-machine
change; `fn` slots live in the never-popping outermost scope and are untouched by all
of it.

### 2.3 The one λ, the let-arrow invariant, and ⇝-sealing

One λ former; formation is a ⇝ operation (closure creation — knowledge). The
let-arrow invariant holds with zero carve-outs: **capital `let` ⇝-reads its RHS,
lowercase `let` ⇒-reads it.** For that to cover `fn F = (λ… : Π…)`, the seal must be
⇝-evaluable:

  * **Check half**: conversion for pure bodies (already ⇝-natural); for imperative
    bodies, the audit becomes a judgment invocable from ⇝ (`checkRFnBody` as a
    sub-judgment — it already runs in its own fresh store).
  * **Forget half — σ generativity, resolved by structure**: the sealed value is the
    **seal SITE applied to its captured inputs** — a structured neutral
    `sealσ(site, v₁…vₙ)` over the free variables' values, compared like any stuck
    spine. Deterministic (evaluation stays a function; `convert` stays `==` on
    canonical forms; no counter under ⇝) and distinguishing (a binder-nested seal at
    different instantiations yields different values — the user's correction of
    occurrence-only keying). `fsig` keys by site.

### 2.4 No function ever lands in a runtime slot — structurally

λ formation is ⇝-only and ⇒ cannot construct a function value, so the invariant "no
runtime-moded binding holds a function" needs exactly ONE enforcement point: the pure
lift's result must be data, not a function (`let f = Add 1` fails there, with the
capitalise-the-binder message). Stage A's backstop is deleted, not extended. The
remaining lowercase bindings of pure-function values in the corpus (partial
applications) migrate capital in the same commit.

### 2.5 Application: spines only

`callV` retires; every call is an app spine with the M31 rule (head by ⇝, arguments by
binder modes, enter-or-abstract). Two things carry over with their reasons: saturation
for imperative entry (§12 decision 4), and the **mint-vs-remember split** — a call
result in ⇒ mints a fresh existential at the instantiated codomain, while ⇝ remembers
the structured neutral. That split is arrow-keyed (§12 decision 5), not node-keyed;
the spine rule must preserve it or stuck spines change meaning in bodies.

### 2.6 Capture, full generality

With value-carried environments, §2.4-of-M31's restriction lifts: a fn body may cite
enclosing comptime *data*, not just sibling functions — escape-via-return is safe
because the closure carries its knowledge. This also requires the **fn body scope
fix**: bodies elaborate seeing sibling and enclosing bindings (the decl{}-era
params-only context retires); the `fnElab` fresh-binder collision that gated it is
void under name-keying.

## 3. The safety criterion (the one design obligation)

**A store-wide sweep is safe on suspensions iff it commutes with evaluation.**
Substitution (refinement, σ := v) commutes — atom-keyed, propagates through captured
environments. X-Gen's abstraction (spine ↦ fresh σ) does not — the env holds a spine's
ingredients, and evaluation can mint the spine after the sweep has passed, leaving
later evaluations speaking pre-abstraction vocabulary: propositionally linked by the
branch equation but definitionally divergent, presenting as flagship proofs failing
(M30's count-equation mode — measured, silent). The answer: **normalize at splits,
with write-back** — `refineSym` already sweeps the whole store at every symbolic
split; evaluating suspensions during that sweep (and *keeping* the normalized form —
re-deriving from the original suspension replays old vocabulary) materializes every
occurrence exactly where the non-commuting sweep needs it, at a cost the split already
pays. Between splits, everything stays lazy. Convert-site comparisons are timing-only
(the checker measured at 1.3% of the build). **Canary: quicksort's count equation.**

## 4. Also landing here (from the M31 ledger)

  * **The agreement path**: passing a borrow-moded-signature function as an argument
    checks by `piAgree`-style signature-Term agreement (E4's measured gap; today an
    honest refusal).
  * The `fn` sentinel's diagnosis, `sealFn`'s rename to "the audit half of
    ascription", and the seal dispatch by body classification (meaningful only now
    that one former exists).

## 5. Staging

Each stage lands with the corpus green; representation stages differential to exactly
zero; rule stages have enumerated flips only.

**Stage V — viability probe (before any dispatch).** One agent: merged λ former +
newest-wins Ω against `checkRFnBody` and the executing differential only. This is
where E2's bet on mechanical-ness is tested; fallback is dual-key `Var` binders.

**Stage R1 — the domain split.** Val loses its syntax embedding; suspensions in Ω;
readback to Term; normalize-at-splits with write-back. The big rewrite (every consumer
of Val's syntax embedding — the E3 traversal set is the checklist). Zero differential.

**Stage R2 — one λ.** `lamR`/`rfn` fold into the closure; `applyRFn`'s rule re-keyed
(knowledge env in scope for the body's ⇝-reads); capture generality + body scope fix.
Zero differential except the enumerated capture-legality flips.

**Stage R3 — the arrows made exceptionless.** ⇝-sealing (site-σ spines); the
let-arrow invariant (comptimeRhs carve-outs deleted); no-⇒-λ + backstop demolition +
the partial-application migration. Enumerated flips (the `let f = Add 1` class).

**Stage R4 — spines + sweep.** `callV` retires (Unit-desugar for nullary); the
deletions list from §1 completed; docs/logs/paper currency.

## 6. Sharp edges to interrogate before dispatch

  * **Site-σ under readback**: seal-site heads must be stable across α/canonical
    renaming, and two sites must never collide after macro expansion (site identity =
    what, exactly — a stable id minted at elaboration?).
  * **Audit-from-⇝ reentrancy**: the ⇝ evaluator invoking the ⇒ symbolic walker as a
    sub-judgment — state isolation of the audit's fresh store from the caller's Ω.
  * **Obligations under suspensions**: owed types are stored normalized today
    (`Val.nfV` at seeding); as suspensions they must still be sweep-correct — the §3
    criterion applies to O's contents too.
  * **The write-back's representation**: glued (suspension + cached normal form) or
    replacing — and what `==` sees.
  * **Executing mode**: never converts, so suspensions in executing state need only
    entry, not normalization — confirm no executing path compares.

## 7. Non-goals

Borrow refounding (shape/contract split, store-relative types — SUGGESTIONS.md,
post-M32, `split_at_mut` as its test); surface juxtaposition syntax (interacts with
R4's spines — decide there or defer, flagged as an open sequencing note); consistency
proofs (unchanged scope).

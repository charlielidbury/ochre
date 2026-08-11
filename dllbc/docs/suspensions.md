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

Non-λ KNOWLEDGE at rest is a canonical Term (σ's as reserved `§`-names; comparison
by `alphaEq`/`==`; swept by Term-level `substP`/abstraction). λ values at rest are
closures per §2.2. Conversion involving a λ value cooks TRANSIENTLY (evaluate the
body under ρ + a fresh `§`-binder, read back, compare) — on demand; Stage V measured
it a wash (the raw pair was fastest — `convert` normalizes both sides either way).

**R1 DECISION — MADE (user ruling): `Term` does NOT grow state formers.** ⊥, loan
markers, and borrow values reach store-wide sweeps, and giving `Term` formers for
them would make a marker grammatically writable — the objection that killed the
union-tree horizon. Instead the store-value type is the **state skeleton**:
constructor structure, ⊥, `loanM ℓ`, `borrowM ℓ ·`, closures `(ρ, Term)`, and Term
LEAVES wherever marker-free knowledge sits. Sweeps are two-layered (walk the
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

### 2.5 No function in a runtime slot — REFUTED TWICE (R3, R3b); residual named

λ formation is ⇝-only, so the invariant needs ONE enforcement point: the pure
lift's result must be data, not a function (`let f = Add 1` fails there). Stage A's
backstop is deleted; the corpus's lowercase partial-application bindings migrate
capital in the same commit.

**R3 CORRECTION — this section's premise is false, measured.** ⇒ still constructs
function values, because **a proof of a ∀-statement is a λ** and this calculus
returns them in Σ tails; refusing at the pure lift or at `readR`'s λ arm rejects
quicksort's count equation and `sort2`. And the migration cannot run yet: the
seven lowercase bindings that hold a function are mostly partial applications of
staged proof-builders, and capitalising one makes it unreadable where it is
RETURNED (a Σ component is ⇒-read; the erasure fence refuses a ⇒-read of a
capital binding). What R3 delivers is the SCATTER: three enforcement sites become
one (`refuseFnBinding`, at the `let`). Derivability, and the migration, need
§2.1's binder migration first — **R3b subsumes both**.

**R3b CORRECTION — the migration ran, and §2.5 is false for a SMALLER reason.**
R3's blocker (a Σ component is ⇒-read) is gone: a Σ binder's mode now rides on
its domain and `readResult` reads it at a body's tail, so a proof at a capital Σ
binder is ⇝-read and the fence is not in the way. What still makes ⇒ construct a
function value is two SPELLINGS, not a missing distinction: **a λ written
literally in a constructor argument** (no type in hand at that site) and **a Σ
chain's TAIL, which has no binder and therefore no mode** — which is exactly
where quicksort's `cnt` sits. Closing §2.5 is now a surface question: give a Σ's
tail a way to say it is comptime, or spell a proof-carrying tail
`Σ (X : A) → Σ (P : B) → Unit`. `S32Backstop.sigmaTailProof` pins it.

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

> **Implementation addendum (R1, landed on `m32-r1`).** Two commits, corpus green
> at each. Recorded where the plan is, in the order the plan would be read.
>
> **0. THE NAMES ARE SWAPPED against §2.3, deliberately.** The doc reserves `Val`
> for the transient semantic domain and calls the other "the store-value type".
> As built, **`Val` is the state skeleton and `Sem` is the semantic domain**,
> because `Machine.lean`'s 4,600 lines are about store values and that is the
> name they should keep, while the transient domain has eleven call sites and all
> of them are in `Pure.lean`. Read §2.3 with the two names exchanged; the
> structure is the one it specifies. As landed:
>
>     Val ::= know Term | node String (List Val) | bot | loanM ℓ
>           | borrowM ℓ Val | rfn (List Var) Term
>
> `Val.ctor` is a smart CONSTRUCTOR that collapses an all-knowledge node into one
> `know` leaf — which is §2.3's "collapses to a bare Term leaf" as a datatype
> invariant, and is also why the trace suite's expected environments are spelled
> exactly as they were.
>
> **1. The ruling held, and it paid the deletion it promised.** No path needed a
> state former inside a `Term`. `Val.capturedMarkers` and `hasStateMarkerEnv` —
> nbe.md §3.2's capture assertion, carried as whole-corpus instrumentation and
> then as a live guard in `mkClosure` — are GONE, because a captured environment
> binds `Sem` values and `Sem` has no ⊥, no loan marker and no borrow. The
> knowledge-only environment invariant is a fact about the types now.
>
> **2. THREE things are state that the ruling's list does not name, and each was
> found by the corpus rather than predicted.** `§segs`/`§seg` (a carve is state
> even when every body in it is owned — collapsing one would put a carve history
> inside a knowledge leaf) and, the genuine surprise, **a recursor spine over
> RUNTIME arms**: `natRec P z (λr(k, ih, v){…})` is a function value whose arms
> are BODIES, so no `Term` can hold it. `§rec` is its skeleton form, and it
> needed three separate consequences chased — it renders as the spine it is (so
> `slotOf`'s golden is unchanged), it is INDEX-KIND so it copies on read (a body
> may name `ih` twice; found by executing-mode `m1` zeroing half a list), and
> `hasType` rejects it with "cannot type neutral", the same sentence the `.app`
> case gave it before. **§2.3's list should read: constructor structure, ⊥,
> loanM, borrowM, closures, recursor spines over runtime arms, and Term leaves.**
>
> **3. `whnf` and `nf` COINCIDE at Term level, and that is the cost line.**
> `readback` begins with `whnfN`, so there is no way to expose a head as a `Term`
> without reading the result back — and reading back normalizes. `Pure.whnf` is
> `Pure.nf` under a name kept for what the call sites mean. Clean build 4:45
> against a 4:03 baseline, ~17%, not clawed back (checker-perf debt is parked by
> house rule until a workload demands it). R2 should expect the same shape.
>
> **4. §6's first sharp edge is answered YES, and the reason is not the guard.**
> A `§σ`-name is unwritable end to end — but `Surface.reservedBinder`, which M30's
> note credits with closing the escaped-identifier route, NEVER FIRES on it:
> `Name.toString` re-escapes, so a program writing `«§σ0»` binds a name that is
> literally `«§σ0»`, guillemets and all, which is a different name and not in the
> reserved namespace. A reader who checked only the guard would conclude the
> opposite. `substP`'s rebinding guard is correspondingly vacuous for σ-names,
> asserted as behaviour in `KernelFloor`'s new `S32Sigma` battery over the whole
> minted-binder inventory rather than argued.
>
> **5. The sabotage run, both directions.** With `Term.abstractInto` sabotaged to
> abstract nothing, the corpus goes RED at **19 assertions**, `Direct.lean:1592`
> (`progOk flagship`, quicksort's count equation) among them. Green with it
> restored. The count is lower than Stage V's 22 for a mechanical reason worth
> knowing: a Lean module that fails stops its dependents from building at all, so
> `Direct`'s failure hides whatever `Functions`/`ArraySort` would have added.
> The control is the flagship, not the count.
>
> **6. Two seams where a store value must become knowledge, and neither is a
> conversion.** `buildResult`'s dependent Σ tail used to push the `borrowₘ ℓ σ`
> NODE into the substitution for the binder — a loan marker in a type. It pushes
> the payload σ now, which is the only reading a type could have meant
> (unreachable in this corpus: `retMixesBorrow` refuses a return type mixing
> borrow and value components). And the differential harness needs a σ to stand
> for a runtime function value (`F ↦ σ0` faces `F ↦ λr(v){…}`), so its
> substitution is at the STORE level: knowledge replacements go through
> `Term.substSym` at the leaves, a non-knowledge replacement can only fill a whole
> leaf. Both are the same seam — `subsKnowledge`, the one-way door from skeleton
> to knowledge — and R2 inherits it, because a closure `(ρ, Term)` is the third
> thing that is a value and not a `Term`.
>
> **7. Bet (a) landed first, as its own commit** (`M32 R1 α`): the nine sites,
> `readCWith`'s prepend→append flip among them, plus the L-suffix condition made
> a real check at the `fn` declaration (`Surface.lemmaShadowCheckAt`, against
> `Dllbc.StdLemmas` specifically — "any Lean global" would refuse `fn` names that
> shadow nothing writable). Silent on the corpus, positive control run.

**Stage R2 — one λ, one closure.** `lamR`/`rfn` fold into `(ρ, raw body)`;
formation captures the filtered slice; application per §2.2; cook-at-generalization
with write-back; universal binder convention + stdlib binder migration; capture
generality + body scope fix. Zero differential except enumerated flips (binder-case
migrations, capture legality).

**Stage R3 — arrows exceptionless: RUN, with one item REFUTED** (branch
`m32-r3` @ b5f94934, stacked on R2; corpus green at each commit; sabotage control
re-run, 21 red including the flagship). ⇝-sealing landed (site assigned by a
boundary pass; the "structured neutral" landed INTERNED — see the addendum) and
`comptimeRhs` is deleted, both at ZERO differential. **§2.5's no-⇒-λ did not
land, and its premise is false**: a proof of a ∀-statement is a λ, so ⇒ must
still construct function values, and the partial-application migration cannot run
until §2.1 gives a RETURNED proof a capital binder. Three enforcement sites
became one; the migration and the derivability claim move to R3b.

**Stage R3b — the binder migration, carrying §2.5: RUN, with §2.5 REFUTED a
second time** (branch `m32-r3b` @ γ, stacked on R3; corpus green at each commit;
sabotage control re-run, 21 red including the flagship and both canary
directions). The migration LANDED: `lowerComptime flagship` is **0**, from
10,777. §2.1's Σ half was found INERT and made real — a Σ binder's mode now
rides on its domain, as λ's and Π's do, because `readback` destroys a binder's
NAME and preserves its domain — and `readResult` reads it at the one site that
has a type in hand, the tail of a body against its return type. §2.5's wall is
down for every Σ component with a binder; it survives at a λ written literally
in a constructor argument and at a Σ chain's TAIL, which has no binder to carry
a mode, and which is where quicksort's `cnt` sits. See the addendum.

**Stage R4 — spines + sweep.** `callV` retires; §1's deletion list completed; E2's
id machinery removed; docs/logs currency. **R4 inherits a measured coupling**:
`keyDisagree` is 4 on the flagship, all of one shape (a capital telescope
parameter binds an Ω slot), so the case test is not a drop-in for `bindsSlot` at
`Term.lamImperative` — a `fn` all of whose parameters are capital would flip from
imperative to pure.

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

> **Implementation addendum (R2, landed on `m32-r2`).** Four commits, corpus
> green at each. Recorded in the order the plan would be read.
>
> **0. THE SPECIES IS A PROPERTY, and it needed TWO halves.** `Term.lamImperative`
> is what replaces the second λ former, and it is true when what sits under the
> binders is a BODY (`Term.imperative`: the forms `reflectC` refuses by name)
> **or when some binder names an Ω slot**. The second half is not redundant and
> was found by the corpus rather than predicted: `fn UseTrans (a, b, c, p, q) ->
> Le a c { LeTrans a b c p q }` has a body both arrows can read, so on body
> classification alone it is comptime, and its seal takes `hasType` instead of
> §5.4's audit. Four corpus programs found it. §2.2's "recomputed by body
> classification" should read **by binder-and-body classification**.
>
> **1. `noSlot` is the fold's load-bearing detail.** One former means one binder
> type, and a `Var` is the one that carries both things a binder can need — the
> NAME (what every resolution keys on since R1) and the SLOT id (which only a
> binder whose argument lands in Ω has any use for). A comptime binder is written
> `"x"` and read as `⟨noSlot, "x"⟩` through a `Coe`. The sentinel is not
> cosmetic: `Term.freeRVars` asks which of a term's binders bind a `.var`, and a
> comptime binder must bind NOTHING there while an imperative λ's binder must
> bind its own, exactly as `lamR`'s telescope did.
>
> **2. ρ CANNOT BE `List (Var × Term)`, and R1 predicted the reason.** A λ
> captures `SetAt`, and `SetAt` is a `natRec` over runtime arms — R1's §rec
> finding: a function value with no `Term` form. A λ also captures a λ. So ρ is
> an **Ω slice**, and §2.2's "knowledge-only by construction" is, for the two
> function forms, knowledge-only by CHECK (`Val.hasStateMarker` at the capture,
> refused by name). What R1 bought is not lost — the leaves are still `Term`s and
> still cannot hold a marker. Found by executing-mode `runSetAt` going red at
> formation, not by reading.
>
> **3. THE CAPTURE FILTER WAS ALREADY WRITTEN.** `admitGlobals` — §8's globals
> rule and §2.4's citation rule — decides which bindings a body may name, at
> exactly the point a λ becomes a value, and R2 keeps its RESULT. Nothing new
> decides what a λ may capture. Closedness stops being a separate premise: it
> existed because a body was entered under a fresh id window carrying nothing, so
> a free variable would be silently rebound to whatever the shift landed on.
>
> **4. Cooking is not a new judgment.** ρ binds knowledge; `eval`'s `letIn` rule
> binds a runtime slot's reserved pure name and resolves `.var` through it; so
> "evaluate the body under ρ" is `Term.underRho` — a `let`-chain `foldr` — plus
> `Pure.nf`. No `.var`-substitution had to be written, and cooking deliberately
> does NOT go through `readC`, which would otherwise have to become a fuelled
> recursion to call something that calls it.
>
> **5. §3's rule landed support-scoped, written back, imperative-exempt** —
> `cookForGen`, run as a pass over Ω before `abstractInto`. Both controls run
> (`Dllbc.Tests.S32Cook`): a closure with a LATENT spine agrees with the eager
> answer when cooking is on (`λ(§0 : Nat). σ99`) and DIVERGES when it is off
> (`λ(§0 : Nat). leb σ5 σ6`), which is Stage V's measurement in this canary's
> vocabulary. §6's two questions are answered: cooking cannot cascade (a split is
> a ⇒ event, cooking is ⇝), and nothing depended on showing source syntax for a
> cooked closure (the renderer prints binders and elides bodies).
>
> **6. A LIMIT of the sweep, found by building that canary.** `abstractInto`
> matches by `Term.beq`, which compares binder NAMES, and readback names a binder
> by its LEVEL — so a generalized spine that itself contains a binder does not
> match its own occurrence one binder deeper. `len σ5` is such a spine. Not new
> at R2 (a λ at rest was normalized knowledge before it was a closure, with the
> same shift) and not what cooking is about; asserted as behaviour and left as a
> demand, whose fix is an α-insensitive key at the abstraction site.
>
> **7. THE NULLARY `fn` COLLIDES WITH THE SURFACE ASCRIPTION.** `Term.lamTel []
> body` is the body, so `fn F () -> T { … }` and `(e : T)` elaborate to the same
> term and the seal can no longer tell a nullary FUNCTION from an ascribed
> expression. Dispatching on "the sealed term is a body" gets it wrong the other
> way — it would give `(match n { … } : Nat)` frame isolation and an audit. §1's
> Unit-desugar is therefore an R2 item, not an R4 one: `fnElab` gives a nullary
> `fn` the comptime, unwritable binder `U§ : ⇝Unit` and `retarget` supplies the
> `()` at every no-argument call site.
>
> **8. §2.6 needed `freeRVars` re-keyed, and that was VERIFIED not assumed.** The
> telescope is numbered `0 … n-1` positionally while the enclosing block numbers
> from its own counter, so letting a `fn` body see its scope makes the two id
> spaces overlap. Measured with id keying in place: the citation is treated as
> bound by whichever parameter shares its number, drops out of ρ, and the sealed
> body's fresh Ω has nothing to resolve it against. `Term.freeRVars` is keyed by
> NAME now — R1's question, asked of the term — with one case stated rather than
> inherited: **a λ binder binds there only when it binds a SLOT**, or a pure
> `λ (N : Nat). …` would shadow a citation of the runtime slot `N`.
>
> **9. §2.1's corpus migration did NOT land, and is sized instead**
> (`Dllbc.Tests.S32Binders`): 10,777 comptime binders spelled lowercase in the
> flagship alone, 5 in `len`, 9 in `Le`. It is not a spelling sweep — each rename
> is scope-sensitive, and capitalising a Π binder in a SPEC position deliberately
> changes argument reading at every ⇒-application of a value of that type, which
> is §2.1's intent and therefore a behaviour change to make on purpose. R2 keys
> the fragment on `Var.bindsSlot` meanwhile, which is the fact that is true today
> and precisely the one R4's id deletion must replace with the case test.

> **Implementation addendum (R3, landed on `m32-r3`).** Two commits, corpus green
> at each, stacked on R2 @ 09b18152. Recorded in the order the plan would be read.
>
> **0. THE HEADLINE, because it is a correction and not a completion.** §2.4's
> ⇝-sealing and §2.4's exceptionless let-arrow LANDED, with zero differential —
> not one golden, verdict, rejection needle or trace moved. **§2.5 did not, and
> its premise is refuted by the corpus**: "⇒ can no longer construct a function
> value" is false, because **a proof of a ∀-statement is a λ**. Details at 4.
>
> **1. The seal has a SITE, assigned at the program boundary.** `Term.seal` grows
> a first field; `Term.numberSeals` numbers them in traversal order; `atBoundary`
> is the one function every entry point goes through. A pass rather than a counter
> in the elaborator, which answers §6's sharp edge by construction: it runs after
> every macro (so `fnElab`, where most seals come from and which is not in
> `Uni.elabUTerm`'s monad at all, cannot move one) and it reads structure, never a
> name (so α-canonicalization cannot either). Both asserted, plus that two
> identical seals at two program points keep DISTINCT sites — which is what makes
> this a site and not a content hash (`S32Seal` §D). Numbering runs BEFORE
> `pushContinuations`, which duplicates a continuation into each match arm: the
> copies are one program point, on paths that are alternatives.
>
> **2. §2.4's structured neutral landed INTERNED, and that is a deviation.** The
> doc says the sealed value is "the seal SITE applied to its captured inputs — a
> structured neutral". As built, `St.sealSites` maps (site, inputs) to a σ and the
> value is that σ. The two agree on everything a judgment can ask; they differ in
> whether the value is a spine or an atom. The atom was chosen because `fsig`,
> `sctx`, `callV`, `hasType` and every golden are σ-keyed — a spine needs both
> contexts re-keyed by `Term` and a sealed function's signature stored abstracted
> over its captured inputs — and because it is what made the flip
> behaviour-identical rather than moving every `.sym` golden in the corpus. **The
> inputs are the seal's free runtime variables' values**, which is exactly what
> its check consults (`readC u`, `readC t`, and `checkRFnBody`'s `admitGlobals`
> over the same set), so a table hit skips a check whose answer is already
> determined — the argument that makes it a memo rather than a cache with a hole.
> Deterministic and distinguishing both asserted (`S32Seal` §B/§C), the second
> being the control the first needs.
>
> **3. `Var.comptimeRhs` is DELETED, not simplified.** The invariant is
> **"a capital `let` ⇝-reads its right-hand side; a lowercase `let` ⇒-reads
> it"**, and the two reading sites say `x.isComptime` so there is no predicate
> left to grow a footnote. `readComptimeVal` is "⇝ at a binding" — three cases,
> because ⇝ produces two things with no `Term` to be read back to (a closure, a
> sealed σ) and everything else is knowledge. **`reflectC` still refuses the seal**
> and R3 did not weaken that: what became ⇝-evaluable is the seal at a BINDING,
> where the σ has a slot to land in; a seal inside a TYPE has no reading, because
> a type is consumed at its own event. `sealNode` is ONE rule with two callers,
> which is the honest content of "the seal becomes ⇝-evaluable".
>
> **4. §2.5 IS REFUTED, twice, by programs.** The pure lift was given the refusal
> §2.5 specifies and quicksort's count equation went red: what it returns at
> `Direct.lean:1592` is `λ(§0 : Nat). boolRec … (j Nat … Refl …) …`, the proof of
> `Π (n : Nat) → Id Nat (Count n …) (Count n …)`. `readR`'s λ arm was given it too
> and `sort2` and the flagship went red: `Pair(SplitANil …, λ (q : Nat). Refl)`
> puts the λ in a constructor argument. **The species-test extension was then run
> and MEASURED**: seven corpus bindings — `cnt`, `cnt1`, `cnt2`, `top1` (partial
> applications of staged proof-builders), `f`, `c`, `g` — and capitalising them
> fails at the RETURN, because a Σ component is read by ⇒ and `fenceComptime`
> refuses a ⇒-read of a capital binding. Nothing separates `let cnt = MkL lo hi
> hcnt` from `let f = Add 1`: both bind a partial application at a Π type, and
> there is no Prop/Type split. **§2.5 should read: the invariant is enforced at
> ONE site (the `let`), and becomes derivable only after §2.1's migration gives a
> returned proof a capital binder — i.e. after R3b, which therefore has to
> subsume it.** Pinned as two accepted programs in `S32Backstop`.
>
> **5. What §2.5 DID buy: three enforcement sites become one.**
> `backstopFnRhs` went (it existed only to improve a message; `fenceComptime` owns
> the rule and its advice was widened instead — the one enumerated flip, two
> needles); `bindFields`' site went as UNREACHABLE, asserted as a program;
> `checkLamCitation` went because `mkClosure` asks its question.
> `backstopFnBinding` survives as `refuseFnBinding`, at the `let`.
>
> **6. The executing machine gained nothing, and it took two tries to keep it
> that way.** Routing the capital `let` onto ⇝ sent `fn` declarations into the
> checking-mode seal while `executing` was true (three trace/differential
> assertions red); and the restated transparency must be `readR`'s read, not
> `readComptimeArg`'s, because a RECURSIVE `fn` seals an `.app` — §7's `natRec P z
> s` — which ⇝ refuses by name (three more). The line is byte-for-byte the call
> the node made before R3. Asserted: `sealSites` is empty when an executing
> program ends, with the `fn` asserted reached (`S32Seal` §E).
>
> **7. Controls.** The sabotage run (`abstractInto` abstracting nothing) goes RED
> at **21** assertions including `progOk flagship` and BOTH `S32Cook` canary
> directions — the same count and shape as R2's, so the sweep is still attached
> and the cook canary is live enough to notice.

> **Implementation addendum (R3b, landed on `m32-r3b`).** Three commits, corpus
> green at each, stacked on R3 @ fdb83166. R3b is §2.1's binder migration
> carrying §2.5, and it is the pipeline's deliberate behaviour-change stage.
>
> **0. THE HEADLINE IS A NUMBER, AND A SECOND REFUTATION.**
> `lowerComptime flagship`, the counter R2 introduced to size the migration,
> goes **10,777 → 0**: every comptime binder in the largest program in the
> corpus now spells its mode. **§2.5 is refuted a second time**, but the
> residual has shrunk from a rule to two spellings — details at 4.
>
> **1. The sweep is a scanner that models `resolveName`, checked by a
> FINGERPRINT.** `pctx` first (a pure binder outranks a runtime local, a
> constructor, a kernel constant, an alias and a Lean global), and the one place
> it loses is `let`, which filters the name out of `pctx` for the rest of its
> block. For every identifier occurrence inside a `prog{ … }` the scanner records
> the binder SITE it resolves to; a rename is correct iff that sequence is
> unchanged, which is α-equivalence stated as something a script can verify.
> `StdLemmas` alone: 3,836 binder sites, 20,476 occurrences, 35,179 resolutions
> identical. It earned its keep on captures the eye missed — `s → S` and
> `z → Z` are CONSTRUCTORS, and `lb → Lb` shadows the `Lb` PREDICATE, which
> showed up as a single `none → site` flip. House rule for a colliding target: a
> `0` suffix (`S0`, `Z0`, `Bound0`, `Lb0`), four names out of 229.
>
> **2. A hand-written `Term` must write BOTH halves of a comptime binder**, so
> `Term.clam`/`Term.cpi` exist: capital name and `⇝` domain, unspellable apart.
> The kernel library (`Std`, `Pure`'s `kAddFn`/`kLeFn`) migrated with them, which
> is a real mode flip — `Len`, `Count`, `Le`, `Add`, `Sorted` now declare their
> arguments comptime — measured at ZERO changed verdicts, because the library is
> only ever applied in ⇝ positions. Unused binders take §6's other branch: `§_`,
> the reserved name the surface already mints, which carries no mode because
> nothing can cite it.
>
> **3. §2.1's Σ HALF WAS INERT, and the reason is `readback`.** `Uni`'s Σ rows
> emitted `.sigmaT x τ b` with no `binderDom`, so a Σ's mode lived in its NAME —
> and `Pure.readback` names every binder it reaches by its LEVEL. A return type
> is normalized before any rule reads it, so the case was gone before it could be
> consulted; λ and Π survive only because `⇝` rides on the domain. **Σ binders
> now carry their mode on their domain**, and `readResult` is the site that reads
> it: the tail of a body, checked against its return type, reads a `Pair` at a
> `Σ` by each component's binder — capital ⇒ comptime ⇒ ⇝-read. Asserted as two
> programs differing in one character, with the lowercase one REJECTED as the
> control. **§2.5's wall is therefore down for every Σ component that has a
> binder**, which was R3's named blocker.
>
> **4. §2.5 IS STILL FALSE, and the residual is two named shapes.** The no-⇒-λ
> refusal was rebuilt (checking-mode-gated — ungated it reds the executing
> machine's own differentials) and reverted: 13 red, the flagship at
> `readR (⇒): a λ is a function value`, `sort2` with it. What survives the
> migration:
>
>   * **a λ written literally in a constructor argument** — `Pair(SplitANil …,
>     λ (Q : Nat). Refl)` is not a body's tail, so no type is in hand;
>   * **a Σ chain's TAIL, which has no binder** and therefore no mode. This is
>     exactly where quicksort's `cnt` sits (`Σ (hi : List Nat) → … → Π n. Id …`).
>     Pinned as `sigmaTailProof`, with the fix named: a surface marker for a Σ's
>     tail, or spelling a proof-carrying tail `Σ (X : A) → Σ (P : B) → Unit`.
>
> **§2.5 should now read**: ⇒ still constructs function values, at two sites, and
> closing them is a SURFACE question (how a component with no binder says it is
> comptime) rather than the "nothing separates a proof from a computation"
> impasse R3 recorded.
>
> **5. Three couplings a rename must not break**, each found by a red assertion:
> a hand-written signature's Π binders track the λ they ascribe (47 assertions in
> `Functions`, 10 more in `Programs`); a recursor motive is derived from its
> signature, and `alphaEq` is mode-sensitive; a sealed recursor's scrutinee
> parameter must stay runtime, because ι splits on it. `fn` cannot hit the first
> — `telePi` builds the Π from the parameters.
>
> **6. What R4 inherits, measured.** `keyDisagree` counts the binders on which
> `Var.bindsSlot` and the case test disagree: **4 in the whole flagship**, all
> one construct — a capital telescope parameter binds an Ω slot. So the rename
> backlog is gone and what is left is a rule about telescopes: under a case test,
> a `fn` all of whose parameters are capital flips from imperative to pure, which
> is R4's differential to own.
>
> **7. What R3b did NOT finish**, stated so it is not mistaken for done: the test
> files' spec Σ binders are still lowercase (four assertions are not green with
> them capital, and the reason is the CONSUMER — a match-arm binder's case is
> unchecked against the Σ's); Class 3 landed in `ArraySort` and `Arrays` only,
> because capitalising a proof parameter makes every onward hand-off a ⇒-read and
> the migration is a fixpoint over the call graph.
>
> **8. Controls.** Sabotage (`abstractInto` abstracting nothing): **21** red at
> every commit, including `progOk flagship`, `sort2` and both `S32Cook` canary
> directions — same count and shape as R2's and R3's. One methodological
> correction: an ABSENT failure is not a pass. An early run of the terminal
> attempt looked far better than it was because the build had not reached
> `Direct` at all.

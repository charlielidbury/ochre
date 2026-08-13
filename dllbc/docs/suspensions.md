# M32: One syntax, one semantic domain — closures are the only suspensions

**Status: IMPLEMENTED, except the residuals named below.** Six stages ran — V
(viability probe, not for merge), R1, R2, R3, R3b, R4 — each with the whole corpus
green, each carrying the sabotage control, and every stage's implementation
addendum is at the bottom of this file. The model of §2 is built: `Term` is the
only syntax, `Val` is the state skeleton over `Sem`, every λ value is one closure,
cooking is persistent exactly at generalization, arrows are exceptionless, every
binder spells its mode, and there is one application node.

**The residuals, all post-M32, all pinned by tests rather than remembered. ALL
FOUR ARE NOW CLOSED** — 4 at M33 α, 2 and 3 at M33a, and 1 at M33 Σ0 — and each
is struck through rather than deleted, so the enumeration a reader met in M32
stays legible.

**§2.5's invariant is LAW: ⇒ cannot construct a function value.** It took three
attempts (R3, R3b, M33), and the third did not succeed by finding the
distinction the first two said did not exist — it succeeded by making the
distinction unnecessary. See §2.7 and the M33 Σ0 addendum.

  1. ~~**§2.5's two spellings**~~ (`S32Backstop.sigmaTailProof`) — **CLOSED at
     M33 Σ0.** ⇒ constructed function values at exactly two sites — a λ written
     literally in a constructor argument, and a Σ chain's TAIL, which had no
     binder to carry a mode. The fix was correctly identified as a SURFACE design
     question, and it is `Σ0` (§2.7): the tail carries the mode on the Σ's
     CODOMAIN, so every position that holds a function can say so, and the rule
     becomes "a function value must arrive somewhere read by ⇝" rather than "tell
     a proof from a computation". All three tripwires flipped deliberately, each
     with a one-character accepting twin.
  2. ~~**Match-arm binder mode checking**~~ — **CLOSED at M33a, and R3b's
     DIAGNOSIS was wrong.** The four assertions were not blocked by the consumer;
     they were blocked by `markExit` having no `.cmpT` case, so a comptime Σ
     component's type kept its `*v` unmarked and read the ENTRY payload. The arm
     check landed anyway (the user ruled it desirable, and it is: it refuses the
     mis-moded state at the last binder position that was not reading its own
     spelling), but it is not what unblocked the migration.
  3. ~~**The Class-3 call-graph fixpoint**~~ — **CLOSED at M33a**, and it could
     not be a commit of its own: capitalising a Σ component forces the consumer's
     `let`s, which force the callee's telescope parameter, in one fixpoint that
     no cut leaves green. `comptimeSlotParams flagship` 4 → 6.
  4. ~~**`abstractInto`'s α-insensitive key**~~ — **CLOSED at M33 α** (branch
     `m33-alpha-key`; addendum at the bottom of this file). The key is
     `Term.alphaEq`, the reproduction is an accepted program with a rejected
     twin, and the corpus moved no other verdict.

Depends on: M31 Stage A (merged), Stage C (merged).

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

The list, with each item's verdict as of R4's close (re-walked against the tree,
not against this list — every stage found the enumeration incomplete):

  * **the mixed domain** (Val's syntax embedding) — DEAD (R1). The store skeleton
    is `Val`, the transient semantic domain is `Sem`; the names are swapped
    against §2.3 deliberately, and R1's addendum says why.
  * **`Term.lamR` and `Val.rfn`** — DEAD (R2). `Val.closure ρ node` is the one
    suspension, body raw.
  * **`callV`** — DEAD (R4). `f(a, b)` is sugar for the spine; the nullary
    Unit-desugar arrived early, at R2, because `lamTel [] body` is the body and
    the seal could no longer tell a nullary `fn` from an ascription.
  * **`Var.comptimeRhs`'s carve-outs** — DEAD (R3). The invariant is one sentence
    with no footnote.
  * **Stage A's backstop scatter** — **DELETED (M33b)**, after two milestones of
    being REDUCED. R3/R3b took three enforcement sites to one (`refuseFnBinding`
    at the `let`) and recorded that it could not become derivable while §2.5's two
    spellings survived; Σ0 closed those and MEASURED that it still did not, at one
    assertion — `let g = ih`, a function COPIED rather than constructed. M33b
    spells that binder `Ih`, which makes the copy a ⇒-move of a capital binding,
    and the rule is gone with `isFnValue`. What enforces §2.1 is three refusals,
    one per way a function can arrive: WRITTEN, COMPUTED, COPIED.
  * **the pure lift's λ case** — SURVIVES, and this entry is REFUTED rather than
    unfinished (R3, twice). A proof of a ∀-statement IS a λ; refusing function
    results at the lift rejects quicksort's count equation. See §2.5.
  * **the modeless-pure-binder exemption** — DEAD (R3b). `lowerComptime
    flagship` is 0, from 10,777.
  * **E2's id machinery** — DEAD (R4). The frame shift, the `keep` sets,
    `progBase`'s arithmetic and its collision check. What survives is two TAGS
    (`noSlot`, `declSlot`) and the elaborator's own binder identity; nothing in
    the kernel compares, orders, offsets or windows an id.

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

**CORRECTION — a hard bound on this section's reach (M33a follow-up, measured):
"a proof parameter capitalises" and "a proof parameter is ι-SPLIT" are mutually
exclusive today.** ι-splitting an equation (`match p { Refl => … }`) is how the
checker LEARNS from it (refineSym), and the match fence refuses a capital
scrutinee — so every equation-consuming function must keep a lowercase proof
parameter (eight corpus sites, structurally unable to capitalise; measured by
flipping one and reading the fence). The design question this opens — a
⇝-consuming match/elim on a comptime equation, so learning does not require a
runtime-moded proof — is FILED, not designed; it is independent of the Σ-tail
question. Separately: ~59 further lowercase proof params in the list-corpus test
files are cosmetic (they receive freshly-constructed proof terms, so the fixpoint
exerts no pressure through them; nine are unused; several are halves of
negative-control twins whose lowercase spelling is the asserted rejection) —
deliberately NOT swept, coordinator-ratified, to avoid silently deleting controls.

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

### 2.5 No function in a runtime slot — refuted twice, **LAW at M33 Σ0**

**CLOSED.** The two refutations below are correct history and are kept; this
paragraph is the answer. **⇒ can no longer construct a function value**, enforced
at two refusals — `readR`'s λ arm for a λ that is WRITTEN (the destination rule)
and the pure lift for one that is COMPUTED (`Add 1` is a spine until it is
evaluated) — with the whole corpus green and all three `S32Backstop` tripwires
flipped deliberately, each with a one-character accepting twin.

**The win was not finding the distinction the two refutations say does not
exist.** It is §2.7's `Σ0`: the one position that held a function and had no way
to say so — a Σ chain's tail, which has no binder — says it on the type now, and
once every position that legitimately holds a function DOES say so, the rule
stops being *tell a proof from a computation* and becomes ***a function value
must arrive somewhere that reads by ⇝***. That is a question about the
DESTINATION, and both machines can answer it.

One thing this does NOT buy, measured rather than assumed: **`refuseFnBinding`
is not derivable.** Neutralising it with everything else in place reds exactly
one assertion — `let g = ih`, where an imperative function value is COPIED from
one runtime slot to another. Nothing constructs a function there, so no rule
about ⇒ constructing one can reach it. "⇒ cannot construct a function" and "a
runtime binding may not hold one" are different claims, and the second is
strictly stronger. Addendum item 6.

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
What R3's demolition DID buy at zero cost: three enforcement sites became one
(`refuseFnBinding` at the `let`; `fenceComptime` owns the rule and its advice).

**R3b ran the migration and the terminal attempt: RE-REFUTED, residual now two
precise spellings.** With 10,777 → 0 lowercase comptime binders in the flagship and
Σ components operative, R3's named blocker is gone — and no-⇒-λ still reds 13,
because two shapes remain that carry a proof-λ with no binder to mode: **a λ
written literally in a constructor argument** (no type in hand), and **a Σ chain's
TAIL** (no binder at all — exactly where quicksort's `cnt` proof sits, pinned as
`S32Backstop.sigmaTailProof`). The fix is named at the site: a surface marker for a
Σ's tail, or spelling trailing proofs as components over a Unit tail — a SURFACE
design question, post-M32. The tripwires stay accepted and unflipped; the invariant
remains one-boundary-SHY of enforceable, and the doc says so rather than rounding
up.

### 2.6 Application surface: spines only — RUN (R4), with one correction

`callV` retires for app spines (nullary via Unit-desugar), preserving the
arrow-keyed mint-vs-remember split (§12 decision 5) and saturation for imperative
entry (§12 decision 4).

**R4 CORRECTION — "saturation for imperative entry" is the whole of it, and the
word IMPERATIVE is load-bearing.** With two application nodes, `f(2)` on a
comptime λ was refused as unsaturated while `f 2` β'd, and the difference was
invisible. With one node the corpus decides: the flagship applies its staged
proof-builders PARTIALLY and goes red under the refusal. §12 decision 4's reason
is that "a partial application at runtime is a closure holding its arguments —
including, in general, borrows — while it waits", and a comptime capture is
knowledge-only, so there is no borrow to hold. **A comptime λ's partial
application is a value**; saturation is enforced at the two sites that ENTER (an
imperative closure, an abstract `σ : Π`). Two corpus assertions flipped to
accepts and say so in place.

**And the split is arrow-keyed as promised, but it needed the callee's VALUE to
stay that way.** `reflectC` refused `.callV` BY NAME, so deleting the node deleted
⇝'s refusal to read a CALL — silently. Restated on the value (`calleeMustEnter`):
a sealed function or an imperative closure is ENTERED, entering is an event, and
⇝ has none; an ABSTRACT function still reflects as the structured neutral, which
is what the old message told the programmer to write instead. Capture reaches M31-deferred generality — a fn body cites
enclosing comptime data, escape-safe because the closure carries its knowledge
(Stage C's measured narrowing: program-scope citation already works today; the
closure is what makes the ESCAPING case safe). Requires the fn body scope fix
(params-only elaboration context retires; the id-collision that gated it is void
under name-keying).

### 2.7 Σ0 — the comptime tail (M33 design, user-proposed, ratified in review) — **RUN**

**Status: IMPLEMENTED** (branch `m33-sigma0`, five commits, corpus green at each;
addendum at the bottom of this file). The spelling is `Σ0`, the prerequisite
landed first and found a second source of the asymmetry the doc did not name, and
**the terminal attempt LANDED** — §2.5's invariant is enforced, at two refusals
which are one rule seen at the two ways a function can arrive.

**The problem it closes**: a Σ chain's TAIL has no binder, hence no mode marker —
§2.5's second escape hatch, and where quicksort's `cnt` proof sits. **The design**:
`Σ0 (x : A) → P` is the pair whose second projection is comptime — DLLBC's subset
type, with the standard precedent (Lean's `Subtype {x : A // P}`, Coq's `sig`,
NuPRL/PVS set types), and with comptime as the erasure axis where those systems use
Prop/irrelevance.

**Representation: NOT a new former.** Σ0 is surface sugar for the existing `sigmaT`
with the existing `cmpT` mode marker on its CODOMAIN — exactly how λ/Π domains
carry modes, routed by the machinery R3b already built (`readResult` dispatches on
domain modes; the codomain is one more site). Same `Pair` constructor serves both
(the marker lives on the type; the read routes off it). No new value former, no new
constructor, no new eliminator. Rules:

  * **Construction**: `Pair(a, p)` at a Σ0 reads `a` by the first binder's mode and
    `p` by ⇝ — non-consuming, and a λ literal there is legal (it lands in a ⇝
    channel). Where no Σ0 type is in hand (a bare un-ascribed Pair), the λ literal
    is refused with the destination rule's message (below).
  * **Destruction**: `match p { Pair(x, H) => … }` — the arm binder receiving the
    Σ0 component MUST be capital (M33a's arm check extended to the tail position;
    the two features enforce each other).
  * **Erasure**: the component is comptime knowledge — evaluated today, dropped by
    compilation, exactly as capital Σ components already are. The executing machine
    is untouched.
  * **Chains**: intermediate Σs' RHS is another Σ (mode structural); Σ0 only ever
    matters as the innermost former, marking the final tail.

**The destination rule** (the surface statement of no-⇒-λ, taught in the error
message and language.md): *a λ is knowledge and needs a comptime destination — a
capital `let`, a capital/⇝ parameter, a Σ0 component or tail, or an ascription.*
Kernel-side this is ONE refusal (the pure lift's λ case); every destination is a
position read by ⇝.

**PREREQUISITE (M33a finding, do FIRST): both machines must be able to read the
tail's mode.** Today only the checking machine has a return type at a body's tail
(`readResult` reads `St.retTyVal`, set only by `checkRFnBody`); the executing
machine's `applyClosure` has none — the ascription is dropped at the seal. Any tail
mode `readResult` consults is invisible to execution unless an executing closure
CARRIES ITS ASCRIPTION — a small representation change, landed before the Σ0
routing, not discovered after (M33a had to checking-side-gate the ⇒-move fence for
exactly this asymmetry).

**Alternative recorded with at-scale UX data (M33a's recommendation), decision held
by the user**: spelling trailing proofs as components over a `Unit` tail — no new
surface former at all, the position becomes ordinary rather than special, consumers
destructure one level deeper (~10 sites). M33a's migration experience: the friction
is that today's tail is INVISIBLY special (a six-component chain reads uniformly for
five and silently reverts to ⇒ at the sixth, and the error names the consequence,
not the tail). Σ0-as-marker also fixes the visibility (the last former is spelled
differently); the Unit-tail fixes it by removing the special position. If the
marker wins, the thing to get right is the MESSAGE at the tail.

**Acceptance = the terminal no-⇒-λ attempt, third and final**: with Σ0 landed and
M33a's migration complete, quicksort's `cnt` spells its type with Σ0, the
`S32Backstop` tripwires flip DELIBERATELY, and the pure lift's λ refusal lands
green — or the residual is reported precisely and the doc says one-boundary-shy a
third time rather than rounding up.

**MET.** Quicksort's ensures spells its tail `Σ0`, all three tripwires flipped
with accepting twins, and the pure lift's refusal is green with the whole corpus.
The enforcement is TWO refusals rather than one, and that is a correction to this
paragraph rather than a compromise: a function arrives at ⇒ two ways, WRITTEN (a λ
literal — `readR`'s λ arm, the destination rule) and COMPUTED (a spine whose value
is a λ — the pure lift), and `Add 1` is only visible to the second because it is a
spine until it is evaluated. **`refuseFnBinding` does NOT become derivable**, and
the residual is one measured shape rather than a suspicion — see the addendum's
item 6.

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

**Stage R3b — RUN** (branch `m32-r3b` @ c360d359, stacked on R3; corpus green;
controls at 21 red both times, restored). Per-class: StdLemmas 3,836 binder sites /
20,476 occurrences; hand-written kernel terms via new `Term.clam`/`cpi`; spec λ/Π
549 sites; telescope proof params in the array corpus; **flagship
`lowerComptime` = 0**. The behaviour flips landed as intended: the library declares
its arguments comptime (zero changed verdicts — it is only ⇝-applied), and a Σ
component's binder became OPERATIVE — which surfaced the finding that §2.1's Σ half
was INERT all along (`readback` names binders by level, so name-carried Σ modes
were destroyed before any rule could consult them; fixed by putting the mode on the
Σ domain + `readResult`, DECISION-LOG'd with the rejected alternative). Method note
carried forward: **an absent failure is not a pass** — grep that the module BUILT
before reading its absence from the failure list. Judgment calls recorded (proof
components capitalise, data do not, decided by domain head and measured both ways).
Residuals stated, not hidden: test-file spec Σ binders (blocked on match-arm binder
mode checking) and the Class-3 call-graph fixpoint — both post-M32 items.

**Stage R4 — spines + sweep: RUN, and the LAST** (branch `m32-r4` @ δ, stacked on
R3b; corpus green at each commit; sabotage control re-run after BOTH the spine
change and the id deletion, 21 red each time including the flagship, `sort2` and
both `S32Cook` canary directions). `callV` retired and the mint-vs-remember split
survived it, keyed on the callee's VALUE (`S32Spine` §A–§E; §A asserts the two
spellings are one `Term`). E2's id machinery is gone — the frame shift, the
`keep` sets, `progBase`'s arithmetic and its collision check — with `progBase`
replaced by the tag `Var.declSlot`, which the three harness projections need.
**Two of the plan's own predictions were refuted**: the `keep` sets are not
empty-by-construction (they hold §8's globals) but INERT, which is a different
claim with its own differential; and `Var.bindsSlot` does NOT become the case
test, because the telescope rule says the two answer different questions — see
the addendum.

**M33b — eager recursion: RUN** (branch `m33-eager`, based on main @ d8004156;
six commits, corpus green at each). Not a stage of M32 either — it is a user
RULING about evaluation order, and the reason it lands in this document is that
the fix is §0's own sentence applied one position further: *closures are the only
suspensions*, so an arm that suspends nothing is not a λ, and an arm that is not
a λ is evaluated at the wrong time. **DLLBC is an eager language: nothing
unevaluated leaves a recursion.** The bug it closes is a measured differential
violation — `let r = Build(1); let L = Len r` was ACCEPTED by `checkProgram` and
could not be RUN — and the enforcement is three changes that are one change:
every arm is a λ (an arm the motive owes nothing binds the unwritable `U§ :
⇝Unit`), ι applies such an arm to `unit`, and the `ih` at a DATA motive is the
recursion at the predecessor already run. At a Π motive it stays the applicable
self-view, because a function value IS finished. **`refuseFnBinding` — Stage A's
last surviving backstop, which §2.5 predicted would become derivable and Σ0
measured as not — is DELETED**, and the thing that made it derivable is `Ih`:
addendum at the bottom of this file.

**M33c — recursor moded signatures: RUN** (branch `m33c-rec-sigs`, based on main
@ a43047b9). M33b's own follow-on, and like it a milestone rather than a stage of
the M32 plan: a recursor's spine carries binder modes the way λ and Π have since
M31 Stage A, so that the three things the machine knew about a recursor by
POSITION become things it reads off a TYPE. Two of the three special cases
dissolve — `recLayout`'s numeric triple and Σ0's fifth destination — and the
third, `erasedMotive`, is a WALL with its reason upgraded from a position table
to a rule stated on the signature's own domain. What it buys is M33b's filed
repair: **`Ih` is unconditional and a recursion may return a proof.** Addendum at
the bottom of this file.

**M33 α — residual 4's close-out, not a stage** (branch `m33-alpha-key`, based on
R4 @ ab6921ae and rebased onto main at merge; two commits, corpus green at each).
**"M33 α" to distinguish it from §2.7's Σ0 design, which the doc also calls
M33** — they are separate lanes that happen to share a milestone number: §2.7 is
surface design for residual 1, this is a kernel key closing residual 4. R2 filed
the α-insensitive key as a demand and named its fix; this ran it.
`Term.abstractInto` compares with
`Term.alphaEq` at all nine of its comparison points, the reproduction is an
ACCEPTED program whose depth-0 twin was already accepted and whose lying twin is
still rejected, and **no other verdict in the corpus moved**. Addendum at the
bottom of this file. What it constrains for later sweeps: the key is a pure
function of (needle, σb, term) — no depth, no context — which is what keeps it
exactly as available as substitution's sweep, cooked closure bodies included.

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

> **Implementation addendum (R4, landed on `m32-r4`).** Four commits, corpus
> green at each, stacked on R3b @ c360d359. R4 is the milestone's last stage, and
> two of the plan's own predictions did not survive contact with the corpus.
>
> **0. THE HEADLINE: the mint-vs-remember split was never the node's, and three
> other things WERE.** `Term.callV` is gone; `f(a, b)` is surface sugar for
> `.app (.app f a) b`, asserted as `Term.beq spelledCall spelledJux = true` —
> literally the same term, which is the strongest form the claim has and makes
> every assertion about calls apply to juxtaposition automatically. §12 decision
> 5's split survived, keyed on the callee's VALUE. But `callV` had quietly been
> carrying three rules that the arrows were NOT, each found by a red assertion:
> §12 decision 4's saturation applied to a COMPTIME λ (§2.6's correction), ⇝'s
> refusal to read a CALL (`reflectC` refused the node by name, so deleting it
> deleted the refusal — restated on `calleeMustEnter`), and §5.2's demand
> collapse plus the ⊥ rejection at the callee slot.
>
> **1. The strengthening, and its four needles.** Routing comptime closures
> through the call rule means their applications are ARITY- and DOMAIN-checked,
> where juxtaposition handed them to the normalizer unchecked. Four spec-lie
> controls — two in `Direct`, two in `ArraySort` — are still REJECTED but now die
> at the ARGUMENT rather than at the return, so their needles move from "does not
> have return type" to "does not have its parameter type". Verdicts unchanged;
> the honest flagships still check, which is what says the rejection
> discriminates. **`Traces.lean` is byte-unchanged and no golden moved anywhere**:
> the executing machine's every trace, environment and comparison is what it was.
>
> **2. `Term.imperative` needs the `.var`-HEADED SPINE by name.** Read off the
> arguments alone, a nullary `fn F () { g() }` — whose only binder is R2's
> comptime `U§` Unit-desugar, and whose body is now `.app (.var g) .unit` — would
> classify PURE. `Term.appSpineVar?` moved into `Syntax.lean` for this.
>
> **3. `keep` IS NOT EMPTY-BY-CONSTRUCTION. It is INERT, which is a different
> claim.** §5's R4 block says to verify the first ("§2.4's capture rule is what
> empties them"). Asserted as a hard failure and run: the corpus goes red, and
> `swap` reports `keep = [901]` — §8's globals are exactly what a body has free.
> What is true is that emptying `keep` while KEEPING the shift is green, because
> since R1 no lookup reads an id, and THAT is the differential that licensed
> deleting `freshFrame`/`shiftVarsK`/`nextFrame` outright. Also green, at zero
> differential.
>
> **4. `progBase` becomes a TAG, and its collision check retires as spurious.**
> Of its three jobs, two were about id resolution and are void under name-keying;
> the third — *is this Ω entry a declaration?* — is `Var.declSlot`. The tag exists
> rather than the ids simply going because of the three harness projections
> (`tailEnvs`, `runExec`, `symEnvs`): deleting the filter puts every `fn` into the
> corpus's expected environments, and keying it on the VALUE would also drop
> `let F = (λ… : Π…)`, which is a σ a program deliberately leaves. **`bindFn`'s
> two-chain refusal is deleted**: the collision was on the ID and never the NAME
> (`withA (withB …)` collided `A` with `B`), so it had been refusing a working
> program since R1. `FnStmt` §A asserts the composition ACCEPTS, with the two
> declarations given DIFFERENT ARITIES so the accept is discriminating.
>
> **5. `Var.bindsSlot` does NOT become the case test, and the telescope rule is
> why.** R4 named R3b's four: all are `Hf`, one `fn`'s proof parameter, capital,
> `⇝`-domained, slotted. **A telescope binder binds a slot regardless of case;
> capital marks the READ MODE, not the LOCATION.** The two keys answer different
> questions, and swapping them would classify an all-capital-parameter `fn` pure
> — taking away its §5.4 audit. So R2's `keyDisagree` splits: the direction that
> is an invariant (lowercase with no slot — an argument with nowhere to land) is
> **0**, and the direction that is the rule (`comptimeSlotParams`) is **4** and is
> content. `impLams flagship = 22` is asserted as the count the rule protects, so
> a later swap made from the name rather than the docstring is loud.
>
> **6. The re-grep found two beyond the list**, which is the fifth stage in a row
> to find the enumeration incomplete. `maxVarId` needed `declSlot` excluded as
> `noSlot` already was (a sentinel would swamp the maximum). And
> `entrySyms`/`exitSyms` and `reflectC`'s `lets` are still id-keyed and STAY —
> they are per-seal maps over a telescope's own positional ids, minted and
> consumed inside one seeding, resolving nothing in Ω. Named so the next reader
> does not re-derive that they were considered.
>
> **7. Controls.** Sabotage (`abstractInto` abstracting nothing) re-run after the
> spine change AND after the id deletion: **21** red both times, including
> `progOk flagship`, `progOk sort2` and both `S32Cook` canary directions — the
> same count and shape as R2's, R3's and R3b's. `S32Cook`'s two directions and
> `S32Seal`'s §B determinism with its §C control are green throughout.

> **Implementation addendum (M33 α, landed on `m33-alpha-key`).** Two commits,
> corpus green at each, based on R4 @ ab6921ae and rebased onto main at merge.
> This closes residual 4 and is not a stage — the fix R2 named, run. ("M33 α"
> because §2.7's Σ0 design carries the same milestone number and is a different
> lane; see §5.)
>
> **0. THE HEADLINE IS NINE CHARACTERS, and the interesting part is the two
> numbers.** `Term.abstractInto` compares with `Term.alphaEq` instead of
> `Term.beq`, at all nine of its comparison points. Nothing else in the kernel
> moved. `beq` compares binder NAMES and `readback` names a binder by its LEVEL,
> so a needle normalized at depth 0 missed its own occurrence one binder deeper —
> and corpus spines bind routinely, `Leb a b` alone unfolding to a `natRec` over
> λ arms.
>
> **1. The reproduction is a PROGRAM, and it was pinned REJECTED before it was
> fixed** (`S32Cook`, next to R2's unit-level limit assertion). Two programs
> split on the same `Leb (Len L) 2` and differ in one thing: whether the
> occurrence sits under a binder. `alphaControlDepth0` holds the spine in a
> comptime `let` — its knowledge leaf is at binder depth zero, the depth the
> needle was normalized at, so the names agreed and it was accepted all along.
> `alphaRepro` holds it in a comptime λ, whose cooked body puts the spine one
> binder deeper; it was rejected at "does not have its parameter type" and is now
> accepted. `alphaReproLie` — the same program asking the True branch to show the
> spine is `False` — is still rejected, because an accept a rubber-stamping sweep
> would also produce says nothing about the key.
>
> **2. A REFUTED first attempt at the control, recorded so it is not re-run.**
> The control was first written with a "binder-free" spine (`Leb N 2`), on the
> reading that `Len` was what contributed the binders — R2's note names `len σ5`
> as "such a spine". Measured: that control is also rejected, because `Leb`
> alone unfolds to a `natRec` whose arms are λs. **Binder-freeness is not a
> property this corpus's spines have.** What discriminates is the DEPTH of the
> occurrence, not the shape of the needle, and the control is the depth-0 twin.
>
> **3. THE COST MEASUREMENTS POINT OPPOSITE WAYS, and both are the answer.** On
> the compiled `phasec` exe. The key in isolation is dearer, as the plan
> predicted: applied at every node of the flagship's 64,729-node term, 73 µs with
> `beq` against 104 µs with `alphaEq` (+42%); over a synthetic tree that is
> nothing but occurrences, 96 µs finding 0 against 156 µs finding 201. End to end
> on the corpus it is FASTER: list flagship 189 → 186 ms, array flagship 493 →
> 482 ms, means of 50 checks, two runs each, run-to-run noise under 1%. The
> mechanism — a match replaces a subtree with one σ atom, so matching more
> shrinks what everything downstream normalizes — is an INFERENCE from the two
> numbers, not itself measured. **The first isolated reading was "100 µs vs
> 100 µs, a wash", and it was quantization** (20 iterations against a millisecond
> clock); re-measured at 2000. The wash is the reading a reader would expect to
> have been stopped at.
>
> **4. Two alternatives rejected, one on correctness rather than cost.**
> Shifting the needle's `§`-names as the traversal descends assumes every binder
> the traversal crosses was counted by readback at the same depth — and the swept
> state MIXES declared syntax with normalized spines (`retTyVal` and `sctx` hold
> source-named binders above depth-0 normalized subterms), so the assumption
> fails exactly where the state is most mixed; it would also have to thread a
> depth through `Machine.abstractInto`'s Val traversal, which records no such
> thing. A de-Bruijn key computed on the fly is SUBSUMED: `Term.alphaEq` is
> de-Bruijn-on-the-fly already — it exists because deleting the indices deleted
> the α-insensitivity they had given for free.
>
> **5. Two invariants checked rather than assumed.** The key must stay
> MODE-SENSITIVE (§2.3: `absOcc` has to see a `⇝` marker, and a mode-blind key
> would abstract the marker away with the domain) — `alphaEq` has no case
> unwrapping `cmpT` on one side only and it compares a binder's DOMAIN, measured
> as `alphaEq (⇝Nat) Nat = false` where `convEq` says true. And it stays exactly
> as available as substitution's sweep (R1's two-layer discipline): the key is a
> pure function of (needle, σb, term) with no depth, context or state, so it
> behaves identically at an Ω leaf, in `sctx`, in an owed type, and inside
> `cookForGen`'s cooked closure bodies — which is the one place the old key's
> answer differed from its answer everywhere else, and the whole reason the gap
> existed.
>
> **6. ZERO other flips, and the red list was collected BEFORE any assertion was
> touched** — so it is the flip inventory rather than a confirmation of one.
> Exactly two assertions moved, both intended: the reproduction, and R2's
> unit-level limit assertion, which is kept and FLIPPED rather than deleted (the
> line that said "the sweep finds nothing here" now says "the sweep finds it",
> and they are the same measurement). All ten test modules reached the compiler;
> only `KernelFloor` failed and only the root imports it, so nothing hid behind
> it — R3b's absent-failure lesson applied rather than recited.
>
> **7. Controls.** Sabotage (`abstractInto` abstracting nothing): **21**
> pre-existing assertions red — the same count and shape as R2's, R3's, R3b's and
> R4's — including `progOk flagship` (Direct.lean:1601) and both `S32Cook` canary
> directions, plus 5 of this stage's own assertions; green with the key restored.
> `S32Cook` both directions and `S32Seal`'s §B determinism with its §C control
> green throughout. **`Traces.lean` is byte-unchanged**: the executing machine's
> every trace, environment and comparison is what it was.

> **Implementation addendum (M33a, landed on `m33-arm-modes`).** Four commits,
> corpus green at each, based on R4 @ ab6921ae and rebased onto main over the
> M32 merge and M33 α. M33a closes residuals 2 and 3, and the first thing it
> found is that residual 2 was misdiagnosed.
>
> **0. THE HEADLINE IS A REFUTATION OF A DIAGNOSIS, not of a rule.** R3b recorded
> "the reason is the CONSUMER — a match-arm binder's case is unchecked against
> the Σ's". It is not. `Term.cmpT` has been a λ/Π domain marker since M31 and
> Syntax.lean's traversals all have a case for it; Machine.lean's do not, and
> three of those end in a `| t => t` fallthrough, so R3b's new `⇝` on a Σ DOMAIN
> was not rejected — it was treated as a leaf and its subterm skipped in silence.
> `markExit` is the one with teeth: §5.4's exit-snapshot transform never reached a
> comptime component's type, so that component alone read the ENTRY payload while
> every sibling read the exit. The smallest witness is one character —
> capitalising `splitOff`'s single proof binder made the `Z` arm's `Refl` at
> `Id Nil Nil` face a demand for `Id σ0 Nil`, in a branch containing no match at
> all. With the three cases added, R3b's four assertions go green with their arm
> binders untouched and still lowercase. `collapseCDerefs` and `calleeNames` are
> the same class, found by the same grep, and are NOT exercised by the corpus —
> said here rather than implied.
>
> **1. The arm check landed anyway, and `Pair` is the only constructor that needs
> a type to decide it.** `Pure.ctorSig` is the fixed basis and it splits: `Cons`'
> head and tail, `S`'s predecessor, `Arr`'s elements are DATA at every type there
> is, so "a capital arm binder over data" is refusable from the constructor NAME
> alone. `Pair`'s first field is a Σ component and takes that Σ binder's mode —
> and the mode is already ON THE FIELD, because a component σ's `sctx` entry is
> `⇝τ` exactly when the component is comptime (`buildResult` has been writing it
> since R3b; `reattachSigmaMode` makes the symbolic path agree, so ONE rule reads
> both). Both directions are refused, with `.unknown` kept as an honest third
> answer for a `Pair` field that is not a σ. Eight `Term.stripCmp`s went in at the
> `sctx` readers that inspect a type structurally — needed anyway, since R3b's
> writes were one capital array-typed component away from a wrong answer.
>
> **2. The prediction was recorded before the work and held exactly.** The check's
> refusal enumeration — 40 arm binders, listed per site in the β commit message —
> is the γ rename list, to the name. The agreement is two-sided rather than a
> count: the check refuses in both directions, so a missing rename reds at
> "Capitalise the arm binder" and a spurious one at "lower-case the arm binder",
> and a green corpus after exactly the predicted set proves the set. Numbers, now
> asserted (`S32Binders`): `capArms flagship` 0 → **10**, `lowerArms` **26**,
> `cmpSigmas` **91**. The 26 is what a one-way rule would not have earned.
>
> **3. RESIDUAL 3 IS NOT A SEPARATE COMMIT, and the corpus is what says so.**
> Capitalising a Σ component forces the consumer's `let`s (`hub2 → Hub2` and its
> family), which force the callee's telescope parameter (`hfuel → Hfuel`), in one
> fixpoint. `comptimeSlotParams flagship` 4 → 6, the arrivals named
> (`[Hf, Hf, Hf, Hf, Hfuel, Hfuel]`). **Where it STOPS is the interesting part**:
> `cnt`, `cnt1`, `cnt2`, `top1` — R3's "seven bindings" — stay lowercase, because
> each is returned in a Σ chain's TAIL and a tail is ⇒-read. The fixpoint closes
> exactly at the boundary §2.5's residual names, which downgrades those seven from
> a backlog to the shadow of one missing surface spelling.
>
> **4. THE MIGRATION DELETED CODE, which had not happened before in this arc.**
> `let Hs1 = hs1` (×2) is gone. The name collision that surfaced it is the
> finding: that §2.4 snapshot existed ONLY because a match arm bound a comptime
> component at a lowercase name, and a runtime binding is not capturable — so the
> proof-builder λ could not cite the proof and a capital `let` had to re-read it.
> With the arm binder spelling its mode, the λ cites it. `Hub0`/`Hlb0` and
> friends are the same shape and survive only because they do not collide.
>
> **5. A REPRESENTATION GAP, stated rather than gated away.** `readResult` — the
> only rule that reads a Σ component by its binder's mode — takes its return type
> from `St.retTyVal`, which `checkRFnBody` sets. The EXECUTING machine enters a
> callee through `applyClosure`, which has no signature in hand (a closure is
> `(ρ, node)`; the ascription was dropped at the seal), so it ⇒-reads the same
> tail. With the flagship's components capital, nine executing differentials died
> on a discipline the checker had already enforced on that very program. M33a
> makes the ⇒-move fence checking-side — `refuseFnBinding`'s own gate and its own
> sentence, "refusing there would break running programs to protect a checker" —
> and no rejection weakens, because every "cannot be ⇒-moved" needle in the corpus
> is a `progRejects`. But the honest reading is that an executing closure should
> CARRY its ascription, and the Σ-tail design will meet this again: any answer
> that gives a tail a mode has to be read by both machines, and only one of them
> currently has a return type to read it from.
>
> **5b. Where §2.7's Σ0 hooks into this, named so it is not re-derived.** §2.7's
> destruction rule ("the arm binder receiving the Σ0 component MUST be capital")
> is `checkArmModes`, and the one line to change is `componentMode`'s `Pair`
> case: it answers for the FIRST field off the component σ's `sctx` type, and
> returns `.data` for the second — the tail — because a tail has no mode today.
> Under Σ0 that second answer comes from the `cmpT` on the Σ's CODOMAIN, exactly
> as the first comes from the domain, and the refusal message already reads
> correctly for it. Nothing else in the check moves; `lowerArms` (26) is the
> counter that will register the flip.
>
> **6. Enumerated flips: two, both verdict-unchanged.** `quicksortA`'s two spec
> lies still REJECT and their needle moves from "does not have its parameter type"
> to "does not have return type" — with `Hs` capital the component is ⇝-read at
> `readResult`, so the lie is caught where it is written rather than one call
> later. Direct.lean's twins of the same two did NOT move, because quicksort's
> caller re-checks the conjunct either way; recorded at the site.
> **`Traces.lean` is byte-unchanged** and no golden moved anywhere.
>
> **7. Controls.** Sabotage (`abstractInto` abstracting nothing): **21** red on
> the pre-rebase base — the same count and shape as R2's, R3's, R3b's and R4's —
> including `progOk flagship`, `progOk sort2` and both `S32Cook` canary
> directions. **Re-run after the rebase over M33 α: 26**, which is M33 α's own
> number unchanged (its 21 + its 5), and that is the semantic check on the two
> lanes composing — M33a adds NOTHING to the sabotage surface, because nothing
> here touches the generalization sweep. The α-key's α-insensitive matching is
> likewise inert for this stage: no assertion of M33a's assumed name-keyed
> matching, and the flagship, `sort2` and both cook directions remain in the red
> set. Every Σ rename went through R3b's scope-aware scanner with the resolution
> FINGERPRINT verified identical (Direct 4,486 resolutions, Functions 2,181,
> ArraySort 2,507, Arrays 1,314). The new `⇝`-transparency test was verified
> DISCRIMINATING by removing the `markExit` case again: exactly one of its three
> assertions reds, and the lowercase control and the lie both stay green.

> **Implementation addendum (M33 Σ0, landed on `m33-sigma0`).** Five commits,
> corpus green at each, based on main @ 478cadb8 (M32 + M33 α + M33a). This is
> §2.7 run, and with it residual 1 and the whole M31–M33 "functions are comptime"
> arc close.
>
> **0. THE HEADLINE: §2.5 IS LAW, at the third attempt, and it was not won by
> finding what R3 said did not exist.** R3's diagnosis was right and is worth
> keeping: "there is no reformulation that separates them from `Add 1` here,
> because there is nothing to separate: both are functions, and only one of them
> is being BOUND at a runtime binder", and this calculus still has no Prop/Type
> split. What Σ0 changed is the other side of the question. The one position that
> held a function and had no way to say so — a Σ chain's tail, with no binder —
> can say so now, and once every position that legitimately holds a function DOES
> say so, the rule stops being "tell a proof from a computation" and becomes **"a
> function value must arrive somewhere that reads by ⇝"**, which is a question
> about the DESTINATION and one both machines can answer.
>
> **1. THE PREREQUISITE FOUND A SECOND SOURCE OF THE ASYMMETRY, and it is the one
> that mattered.** §2.7 and M33a's item 5 name one: an executing closure drops its
> ascription at the seal, so `applyClosure` has no return type and cannot read a
> tail's mode. `Val.closure` grows a third field (`Option Term`) and `sealExec`
> fills it — and with only that, all nine of M33a's executing differentials STILL
> died on the un-gated fence. **A recursive `fn` does not seal a λ**: `fn [k]
> Partition …` elaborates to `natRec P z s` over runtime arms, and the ARMS are
> the bodies. That is the road quicksort's own tail takes (`cnt` is returned from
> `Partition`), so it is not a corner — Σ0 would have been a rule the executing
> machine could not read for exactly the program it exists for.
> `recArmPis`/`ascribeRecArms` close it with `sealRec`'s own derivation (peel the
> scrutinee off the ascribed Π; the codomain IS the motive's body; an arm's
> contract is that at the arm's constructor, under the leading binders the
> recursor's premise gives it), differing from `checkArm` only in not checking it.
> With both halves the ⇒-move fence is **both-machine again** and M33a's gate is
> deleted with its reason.
>
> **2. Σ0 IS ONE ARM, and it deleted a special case rather than adding one.**
> `Σ0 (x : A) → P` elaborates to `.sigmaT x dom (.cmpT P)` — no `Term` former, no
> `Val` form, no constructor, no eliminator. `readResult`'s first component used to
> be routed by an explicit `Term.domComptime dom` test and its tail by nothing;
> both are now one arm at the top of `readResult`: **a position is comptime iff its
> type carries `⇝`**. One sentence covers a λ's argument, a Π's, a Σ's component
> and a Σ's tail, where it covered three and left the fourth silently runtime.
>
> **3. THE M33a HOOK NOTE IS ONE STEP OFF, and the correction is worth having.**
> §5b predicted the destruction change would be `componentMode`'s `Pair` case. It
> is not: `componentMode` already asks `sctx` per field and needed no case at all.
> What moved are the two places that WRITE the mode — `reattachSigmaMode`
> (symbolic), which now re-attaches at BOTH ends, and `buildResult` (concrete),
> which gets the codomain's `⇝` for free through `readCWith`. `Pure.ctorSig
> "Pair"` strips the codomain as it has stripped the domain since R3b.
> `lowerArms flagship` **26 → 22** and `capArms` **10 → 14**, which is the flip
> §5b said that counter would register, and the four that moved are the tails.
>
> **4. A FIFTH DESTINATION, found by the corpus: a RECURSOR ARM.** Stated at
> `readR`'s λ arm alone, the destination rule refused every runtime recursor's
> arms — 46 assertions red, four executing differentials among them — because
> `readRecArgs` reads arms with `readR` and an arm is a λ. An arm has a contract
> (the seal ascribes the spine; `checkArm` checks it; `ascribeRecArms` now hands
> the executing machine the same Π), so `readRecArgs` FORMS its arms. 46 → 24. The
> programmer-facing list in the error message is the other four.
>
> **5. THE MESSAGE AT THE TAIL was a first-class deliverable and earned it.**
> M33a's UX finding — a six-component chain reads uniformly for five and silently
> reverts to ⇒ at the sixth, and `fenceComptime` names the consequence and advises
> lower-casing a proof — is answered by `tailFence`, which fires only at the second
> component of the INNERMOST Σ and says the position and the spelling. It is also
> what made the corpus migration mechanical: every rename in commits 2–4 was
> demanded by name, by a message that said which binder and which fix.
>
> **6. `refuseFnBinding` DOES NOT BECOME DERIVABLE, and the residual is one
> measured shape.** §2.5 promised the backstop would be deleted once ⇒ could not
> construct a function. Measured by neutralising it with everything else in place:
> the corpus goes red at **exactly one** assertion, `Functions.m1` — `let g = ih`,
> where `ih` is a recursor arm's lowercase self-view holding an imperative
> function value. Nothing CONSTRUCTS a function there; the σ is COPIED out of one
> runtime slot into another. So the two claims are genuinely different, and the
> doc should say so: **"⇒ cannot construct a function value" is now law and is
> enforced by two refusals; "a runtime binding may not hold a function" is
> strictly stronger, because a function can also arrive by being copied, and it
> keeps its one site.** (The deeper fix is §2.1's: `ih` is a binder holding a
> function and should be `Ih`. `m1` is a negative control whose whole subject is
> that `let g = ih` is refused, so capitalising it there would delete the test;
> the sweep is a separate item.)
>
> **7. Controls.** `abstractInto` sabotage (its nine `alphaEq` tests forced
> false): **26** red at commits 1, 2 and 4 — the same count and the same shape as
> M33a's re-measurement (Direct 18, KernelFloor 7, Arrays 1), with `progOk
> flagship` (Direct.lean:1605) and both `S32Cook` directions confirmed present
> each time; green with it restored. So Σ0 adds NOTHING to the sabotage surface,
> which is the semantic check that none of this touches the generalization sweep.
> `S32Cook` both directions, `S32Seal` §B/§C and M33a's arm-check discriminator
> green throughout. Ten test modules built at every measurement (R3b's
> absent-failure lesson applied, not recited). **`Traces.lean` byte-unchanged.**
>
> **8. Enumerated flips, the whole list.** Commit 0: one, a value shape —
> `KernelFloor`'s S32Seal §E golden spells `Inc`'s closure, which now carries
> `some (Π(§p0 : Nat). Nat)`. Commit 1: one — `sigmaTailProof`'s needle moves to
> the tail message, verdict unchanged. Commits 2+3: `lamValued` flips to rejected;
> 20 return types take `Σ0`; 8 tail arm binders, 11 λ-valued bindings and 4
> function-typed parameters capitalise; `lowerArms`/`capArms` move. Commit 4:
> `computePartial` flips to rejected; the seven §2.5 bindings capitalise; ONE
> spec-lie needle moves ("does not have its parameter type" → "does not have
> return type", verdict unchanged) for the same reason M33a recorded for
> `quicksortA`'s two lies — with `Cnt` capital the lie is caught where it is
> written rather than one call later. No other verdict in the corpus moved.

> **Implementation addendum (M33b, landed on `m33-eager`).** Six commits, corpus
> green at each, based on main @ d8004156 (the full merged M31–M33 arc). This is
> a user RULING run, not a stage of the M32 plan, and it belongs in this document
> because the fix is §0's own sentence applied one position further.
>
> **0. THE RULING, and the sentence that turned out to be doing the work.**
> *"Passing a Nat to natRec causes the Nat to get recursed over all the way to the
> end — this means it will definitely call the zero case, passing it unit and
> evaluating the contents. I don't see why we would want anything unevaluated
> leaving the natRec; this is not a lazy language."* The interesting part is
> **"passing it unit"**: the ruling names the mechanism, and the mechanism is
> forced by §0. Closures are the only suspensions, so an arm the motive owes
> nothing — `Term.lamTel [] body` IS `body` — could not be a suspension at all,
> and `readRecArgs` ⇒-READ it when the SPINE was formed. The bug and its fix are
> the same fact: an arm that is not a λ runs at the wrong event.
>
> **1. THE BUG WAS A CLEAN DIFFERENTIAL VIOLATION, and it had been there since
> the macro existed.** `fn Build [n] (n : Nat) -> List Nat { match n { Z =>
> Cons(1, Nil), S(k) => Cons(0, Build(k)) } }` left `Cons Z ⟨natRec … Z⟩` — R1's
> `§rec`, a state form with no `Term`, inside a constructor the program declared
> `List Nat`. `let r = Build(1); let L = Len r` was ACCEPTED by `checkProgram` (to
> the checker `r` is a σ) and REFUSED by `runProgram` ("readC: … is state, not
> knowledge"). **The corpus had never noticed because no program in it consumes a
> data-motive recursion's result** — every recursive `fn` here writes through a
> borrow and returns `Unit`. Pinned BROKEN at commit 1, flipped at commit 3.
>
> **2. THE UNIT BINDER IS ONE BINDER, SHARED.** `FnMacro.nullaryVar` moved to
> `Syntax.unitBinder`, because the kernel has to recognize it now: ι asks whether
> an arm owes a `()` and both contract derivations (`checkArm`, `recArmPis`) ask
> whether its Π gains a `Unit`, through one `Term.unitPi`. Its unwritability
> answers an ambiguity `S26Rec` §A4 had recorded as unanswerable — "at ι there is
> no way to tell *the arm applied to no arguments* from *the arm with nothing
> owed*". There is now: they are different TERMS, and only the elaboration can
> write the first.
>
> **3. THE SURFACE DECISION WENT TO REFUSAL, and the reason is two-machine rather
> than aesthetic.** A bare-term arm is REFUSED, not silently wrapped. Cost
> measured by installing the refusal: **one** hand-written term
> (`Ledger.deepBaseArm`), which its author had already written as `Term.lamTel []`
> — so the migration is naming the binder the fold ate, and the old spelling is
> kept as the rejected twin. A silent wrap would have to happen TWICE, once per
> machine, and a form that two machines wrap independently is exactly the
> asymmetry M33a item 5 and Σ0 item 1 spent two stages closing.
>
> **4. THE EAGER/LAZY LINE IS THE UNIT BINDER, and it is not a heuristic.** `ih`
> is eager iff the base arm binds `U§`, which by (2) means the motive owes the arm
> nothing, which means the recursion at the predecessor runs to a FINISHED value.
> At a Π motive it cannot — the arms take the residual telescope, and nobody has
> those arguments yet — so the spine at the predecessor stays what §7's
> convergence argument says a recursive occurrence is. **That is not laziness
> surviving in a corner: a function value IS finished**, which is the same
> sentence the ruling makes about data. `stuckRec` at a symbolic scrutinee is
> untouched for the same reason from the other side.
>
> **5. `Ih` IS CONDITIONAL, and the three programs that forced that are worth
> naming.** §2.1 says capital binds comptime knowledge, so the question is what
> the binder HOLDS, and the answer splits exactly where (4) does: a Π motive gives
> `Ih` a function (§2.5 law), a data motive with an empty residual telescope gives
> `ih` the recursive RESULT — ordinary runtime data since commit 3. Renaming
> unconditionally reds `recGood`, `recList` and `recCaller`, all at `fence: 'Ih' …
> cannot be ⇒-moved`, all for one reason: their self-call `RecGood(m)` drops its
> only argument and IS the bare `.var ih` the arm returns. Legalising that return
> needs the recursor's SIGNATURE to carry modes — filed as its own milestone, and
> deliberately not smuggled in here. `comptimeSlotParams flagship` **6 → 9**.
>
> **6. `refuseFnBinding` IS DELETED, and §2.5's residual is closed.** Σ0 item 6
> measured the rule as NOT derivable — neutralising it red exactly one assertion,
> `m1`'s `let g = ih`, a function COPIED rather than constructed — and named the
> repair in the same breath. With `Ih` capital the copy is a ⇒-move of a capital
> binding, `fenceComptime` refuses it a layer earlier, and re-measuring leaves the
> whole corpus green with the rule neutralised. **Stage A's backstop scatter is
> not reduced but GONE.** What enforces §2.1 is three refusals, each at the event
> it is about: WRITTEN (`readR`'s λ arm), COMPUTED (the pure lift), COPIED
> (`fenceComptime`). §1's entry "Stage A's backstop scatter — REDUCED, not
> deleted" should now read DELETED.
>
> **7. AN ABSENT FAILURE IS NOT A PASS, and here it is the main finding.** The
> corpus is green at every commit with only the enumerated flips — but the eager
> path was measured directly, by making it throw: **5** assertions red, ALL in
> M33b's own battery. No pre-existing corpus program has a data motive with an
> empty residual telescope. So the corpus's greenness says this is
> non-regressive and the battery is what says it works, and `defaultFuel` did not
> move because the eager path is not on any pre-existing program's road.
>
> **7b. COST: none measurable, A/B on `phasec` against the base tree.** The one
> thing M33b adds to every recursor's road is `Val.armTakesUnit` — a `peelLams`
> over the arm's telescope, ≤4 binders here — so it was measured rather than
> reasoned about, on the compiled harness at 50 iterations (the count M33 α's
> item 3 established, after its own first reading turned out to be clock
> quantization). CHECKING: list flagship 163 → 164 ms mean, array flagship 382 →
> 382 ms. EXECUTION (`runQsA`, which §5 of that harness calls the suite's actual
> hotspot): 2060.7 → 2056.7 ms mean at 9 elements, 461.7 → 453.3 ms at 7. Every
> figure is inside the run-to-run noise the same addendum measured at under 1%,
> and the two directions disagree in sign, which is what noise looks like.
>
> **8. Enumerated flips, the whole list.** Commit 2: one addition
> (`recDeepBare`, rejected); no existing verdict moved. Commit 3: the two commit-1
> pins (`demandMatch`, `demandLen`) flip `progRuns` false → true. Commit 5: `m1`'s
> needle moves from "capitalise the binder" to "cannot be ⇒-moved" (verdict
> unchanged, FOURTH reason), `runExec m1` flips from zeroing the list to erroring
> — **the machines agree about `m1` now**, which retires the divergence M27's
> third containment existed to manage — `slotOf b1 "f"`'s golden takes `Ih`, and
> `comptimeSlotParams flagship` 6 → 9. Nothing else.
>
> **9. Controls.** `abstractInto` sabotage at commits 2, 3 and 5: **26** red every
> time — Direct 18, KernelFloor 7, Arrays 1 — the same count AND shape as M33 Σ0's
> and M33a's, with `progOk flagship` (Direct.lean:1605), `progOk sort2`
> (Arrays.lean:1445) and both `S32Cook` directions (KernelFloor 918/922, 977/981)
> confirmed present each time; green with it restored. M33b adds nothing to the
> sabotage surface. `S32Cook` both directions, `S32Seal` §B/§C and M33a's
> arm-check discriminator green throughout. **`Traces.lean` is byte-unchanged**:
> the executing machine's every trace, environment and comparison is what it was,
> and the shape this milestone expected to move there — a spine render becoming a
> finished list — never materialized, for (7)'s reason. Two goldens DID move, both
> outside `Traces` and both named in (8): `slotOf b1 "f"` takes `Ih`, and
> `runExec m1` goes from a zeroed list to an error. Said this way rather than as
> "no golden moved", which would be false.

> **Implementation addendum (M33c, landed on `m33c-rec-sigs`).** Six commits,
> corpus green at each, based on main @ a43047b9 (the fully merged M31–M33 arc).
> M33c is M33b's filed follow-on: the recursor's spine gets binder modes the way
> λ and Π have had them since M31 Stage A, so that what the machine knew about a
> recursor by POSITION becomes what it reads off a TYPE.
>
> **0. THE HEADLINE IS TWO DISSOLUTIONS AND ONE WALL, and the wall is the part
> worth having read.** `recLayout`'s numeric triple is GONE and Σ0's
> fifth-destination arm rule is GONE — both read off `recSig`, the recursor's own
> moded Π. `erasedMotive` STAYS, and the reason is the sharp edge the dispatch
> named: **"never read" is not "⇝-read", and this language has no marker for the
> difference.**
>
> **1. The signature, and why a type rather than a wider table.** The alternative
> was to keep the triple and add a fourth field of modes. A type subsumes all
> four and is answerable in a way a table is not:
>
>     natRec : Π (P  : ⇝(Π (§n : Nat) → Type))
>            → Π (Z§ : ⇝(P Z))
>            → Π (S§ : ⇝(Π (k : Nat) → Π (Ih : ⇝(P k)) → P (S k)))
>            → Π (n  : Nat) → P n
>
> The motive is a BOUND binder, so the schema is closed and can be read without
> instantiating anything. Every binder spells its mode on both halves, exactly as
> `Term.clam`/`Term.cpi` make a hand-written comptime binder do (R3b): the motive
> because a type is knowledge, the arms because §2.5 is law that a function value
> arrives only where ⇝ reads it, the scrutinee runtime because it is what ι splits
> on. Read off it: `recPreScrut` (every binder but the last), `recMotiveIdx` (via
> `recMotiveDom` — **the argument whose type is a family over the scrutinee**,
> which is what a motive IS rather than where it sits; `listRec`'s `A` is a type
> and not a family, and that is what separates the two comptime non-arms),
> `recBaseArmIdx` (the position after the motive), `recArgDoms` (the modes).
> Measured against the table it replaces: `natRec (3, 0, 1)`, `listRec (4, 1, 2)`,
> `boolRec (3, 0, 1)`, to the number.
>
> **2. THE WALL, measured, with the mechanism named.** Routing the motive through
> the ordinary comptime reader reds **34** assertions — Boundaries 2, Direct 32,
> the build halting at Direct so that is a FLOOR and not a total. The mechanism is
> not the reading but the FORMATION check: §2.2 has `mkClosure` ⇝-evaluate a pure
> λ's body as a check, `reflectC` descends λ bodies and Π domains, and it refuses
> `borrowT` by name. The probe's own words:
>
>     readC (⇝): borrow type `&mut (τ ↝ S)` is only valid at a telescope position
>
> The three precedents were weighed and none reaches it. A **third marker**
> ("erased", beside `⇝`) is a new grammatical form for one position, which is what
> this milestone exists to remove. **fsig-only σs** ("callable but not
> conversion-typeable") is the right SHAPE and is what the motive already is — a
> signature position that is MET (the seal checks the written motive against the
> derived one) and never READ — but it gives no way to say so in the type. **Σ0's
> move** (the mode on the type where no binder exists) is inapplicable: the motive
> HAS a binder; the problem is not where to put a mode but that no mode means
> "unreadable". So the motive stays special and its reason is upgraded from a
> POSITION TABLE to a STATED RULE on its own domain, read where every other
> position's mode is read. A partial dissolution, scoped honestly.
>
> **3. THE FIFTH DESTINATION WAS NEVER A DESTINATION RULE — it was a position
> rule.** Σ0 item 4 found that stating "a λ needs a comptime destination" at
> `readR`'s λ arm alone refused every runtime recursor's arms (46 red), and
> answered it by making `readRecArgs` FORM its arms as a special case. The arm
> position says `⇝` now, and ⇝-reading a λ IS forming it — `readComptimeVal`'s own
> λ case is `mkClosure`, the same call the special case was making by hand. One
> sentence covers a capital `let`, a ⇝ parameter, a Σ0 component or tail and an
> arm. A λ that is COMPUTED into an arm became legal for the same reason a WRITTEN
> one is, where the pure lift used to refuse it; the programmer-facing list in the
> error message is still the four a programmer can write.
>
> **4. THE ARM CONTRACT IS ONE DERIVATION WITH TWO PROJECTIONS.**
> `recArmContracts` returns, per spine position, the premise binders the recursor
> gives the arm paired with the type the rest of it must have. `sealRec`/`checkArm`
> CHECK the pair; `recArmPis`/`ascribeRecArms` WRAP it. M33b had added the unit
> binder to each of them by hand — that is the duplication SUGGESTIONS names, and
> it is gone. What stayed in `sealRec` is the arms' SHAPE, because those are its
> messages and the corpus asserts three of them.
>
> **5. `Ih` IS UNCONDITIONAL, AND THE CONDITION WAS THE ARM'S MISSING RESULT
> MODE.** M33b minted `Ih` capital iff `ihTy` was a Π and measured that dropping
> the condition red `recGood`, `recList` and `recCaller` at `fence: 'Ih' … cannot
> be ⇒-moved`. Re-measured on this base before anything was touched: the same
> three, Direct 292/362/422, and nothing else (the build halts at `Direct`, so
> `Ledger`'s `progOk S23Direct.recGood` would have been a fourth). The two cases
> were never two. `Ih` holds the motive at the PREDECESSOR and the arm PRODUCES
> the motive at its own constructor — the same type, so the same mode — and the
> motive is comptime whichever thing it delivers: a FUNCTION by §2.5 when it still
> owes the arm a telescope, the recursion's own finished KNOWLEDGE when it owes
> nothing. What differed between the cases is the ARM's result mode, said once in
> `recArmContracts`. One question — *does the motive owe this arm anything?*,
> which is also M33b's eager/lazy line and its unit binder — now answers four
> things.
>
> **6. A RECURSION MAY RETURN A PROOF**, which is (5) from the programmer's end:
> an arm may return `Ih` bare, because the arm's result position is comptime
> exactly when the recursion delivers a finished value there. Pinned as
> `Ledger.recDeepCapProg` with `recDeepProg` — the same recursor with the binder
> spelled `ih` — unchanged beside it, and a lying-ascription twin for each, so the
> accept is the arms inhabiting the type rather than the marker waving them
> through.
>
> **7. `applyRest`'s Π-motive case: KEEP, and now for a reason the type states.**
> M33b kept it on a measurement (green with it throwing) and said deleting it
> would turn a live shape into a partial-application error. `recSig` ends `… → Π
> (n : τ) → P n`: the recursor's result at the scrutinee IS the motive there, so
> when the motive computes a function type the recursor's own codomain is one, and
> a recursor applied to nothing beyond its scrutinee is a VALUE of it. That is
> this line. It stopped being a corner the corpus happens not to reach and became
> the signature's codomain read literally.

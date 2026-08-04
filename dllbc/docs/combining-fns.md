# Combining `fn` and λ

**Goal.** DLLBC currently has two notions of function: the runtime `fn` (declared at top level, called as `f(x)`, checked once per declaration by the symbolic interpreter) and the comptime λ (a first-class pure term, applied as `f x`, β-reduced by conversion). This document lays out how to combine them into **one function type with one declaration form and one application form**, for two reasons. The first is simplification: a language should not make its user learn two function calculi, and functions like `add` that make sense in both worlds should be defined once and used everywhere. The second is the project's own mission: dependent types and mutability integrate exactly where proofs talk about runtime functions and runtime code carries proofs, and every place the two function worlds currently meet is special-cased machinery (the pure lift, `toTerm` splicing, the ensures convention). One former makes the interaction compositional instead of case-by-case.

This document is about **semantics**. It assumes that once the precise semantics are decided, the implementation is worked out separately; nothing here depends on how `Term`/`Val`/`Decl` are represented today, and no staging or migration plan is given.

---

## 1. The diagnosis: what actually differs

Strip away syntax (`f(x)` vs `f x` is nothing — the unified surface grammar could collapse it immediately) and the two notions differ in five real ways:

1. **Binder modes.** An `fn` telescope binds owned values, mutable borrows, and proofs; a λ binds only unrestricted comptime terms.
2. **Transparency.** Applying a λ β-reduces definitionally; calling an `fn` is opaque — the call site consults only the signature, never the body.
3. **Recursion.** `fn` recurses under the `[k]` snapshot-subterm guard; the pure fragment has no `fix` — recursion is expressed through eliminators.
4. **The boundary audit.** An `fn` body is checked against its declared return type at its boundary, with exit snapshots (`*v` reads the exit, `old *v` the entry) and the ensures convention; a λ body is just a term, checked by `hasType`.
5. **First-classness.** λ's are values — they can be passed, returned, stored; `fn`s are top-level declarations that cannot.

The claim of this document: differences 1, 3, 4 unify naturally under one Π-former with moded binders; difference 2 is a **semantic dial that must survive unification** (it cannot be dropped, only made explicit); difference 5 splits into an easy case (unrestricted closures) and a genuinely open one (borrow-capturing closures, already deferred in §10 of the main note) that unification does not need to solve first.

---

## 2. The conceptual foundation: two representations of a function

Ω stores every other type of value in two representations — a literal (`5`, `Cons 1 σₜ`) that computes, and an abstract σ (`σ : Nat`) typed in the σ-context that does not. Functions come in the same two representations:

1. **A literal λ** — `λ (x : Nat). x`. Application β-reduces: the body is known, so unfold it.
2. **An abstract function** — `σ : Π (x : Nat) → Nat`. The body does not exist; application cannot unfold anything.

The design question is entirely about what rule 2 produces, and the answer is **different in the two worlds**, for reasons this project has now measured from both sides:

**At comptime, abstract application must produce the *structured neutral* `σf a` — never a fresh σ.** The structured neutral remembers what was applied to what; a fresh σ forgets. Three things depend on the memory, and all of them are load-bearing for the existing lemma library. *Congruence*: two citations of `ih b` (an induction hypothesis is precisely a Π-typed abstract function) must be definitionally equal, or inductive proofs collapse — the IH's `add k m` and the goal's `add k m` must be the same open expression for the one to discharge the other. *Statability*: `count_append` relates three applications at symbolic arguments; under fresh-σ semantics its two sides are unrelated existentials and the statement is meaningless before it is unprovable. *Resumability*: a stuck expression computes further when its abstract parts refine — which is what an induction *is*: a plan for making stuck expressions compute one constructor layer at a time (each `elim` branch instantiates the scrutinee and the ι-rule resumes).

Note that for functions whose body is known, the neutral in practice sits *inside* the unfolded body, not at the application node: today's kernel has no named function constants, so `add σₙ σₘ` unfolds immediately and sticks at the recursor — `natRec _ σₘ (λ k ih. S ih) σₙ` — and conversion compares open recursor expressions. That is exactly the current pure fragment, and `add_comm` is its worked example: the two sides of commutativity are the same function stuck on *different* arguments, which is why the equation is true but not definitional, why `Refl` appears only where all arguments are constructor-headed, and why the auxiliaries (`add_zero`, `add_succ`) are precisely the mirror images of the definitional equations for the argument the recursion does not inspect. Comparison of open expressions is semantically complete but *spelling-sensitive* — which argument a function recurses on decides which side of every equation sticks (the same fact that forced the array era's successor-unrolled obligations).

**At runtime, an opaque call produces a fresh σ per result and re-minted payload — plus declared knowledge.** Here forgetting is deliberate, and it is sound because something compensates: the return type's ensures (and the exit-snapshot convention) attach exactly the promised facts to exactly the minted σs. The project has built **both** semantics for calls and chosen between them knowingly: the M22 model architecture gave calls spine semantics (the exit payload was literally the spine `sortRangeL fuel lo cnt σₚ`, and lemmas about the model reached it), and the M23 redirect replaced it with fresh-σ-plus-ensures, demoting models to a comparison baseline. The choice is not incidental — it is the project's thesis that the postcondition should be the caller's only knowledge.

So the unified model is two rules per world, with no third primitive:

| | body known | body unknown / withheld |
|---|---|---|
| **comptime (⇝)** | unfold (β) | structured neutral `σf a`, typed by Π-instantiation |
| **runtime (⇒), opaque call** | — (opacity withholds the body by choice) | fresh σs per the type: minted result, re-minted borrow payloads, ensures attached |

---

## 3. The unifying principle: application-by-type

The two right-hand cells are one principle at two type richnesses: **applying an abstract function yields exactly what its Π-type promises and nothing more.** For a pure `Π (x : Nat) → Nat`, the promise is only "a Nat depending on x" — the structured neutral is that promise verbatim. For a borrow-moded `Π (v : &mut List Nat) → Σ (Sorted (*v)) → …`, the promise is richer — an exit payload for the borrow, evidence about it — and the call rule's minting-plus-ensures is *that* promise verbatim. Today's "call rule" is not a separate concept from application; it is abstract application at a moded Π.

What makes this legitimate — and this is special to DLLBC, not a general fact about imperative languages — is the value semantics. In a heap language, "call as application" is unsound: two calls with equal arguments needn't agree because the world changed between them. Here the world *is* the arguments: borrows carry their payloads, so a call is semantically a pure function of (arguments + entry payloads) to (result + exit payloads) — which is what the backward-function/ensures story has said since M17. Runtime calls are *applicative*, and the σ-model extends to them soundly **because of §0's value semantics**. This is the deep reason the unification is principled rather than notational.

---

## 4. Approaches

### Approach A — surface unification only

One declaration form and one application syntax, elaborating to the existing two guts by inspecting the binder types: any borrow/owned binder ⟹ today's `Decl` machinery; all-comptime binders ⟹ today's pure term. No semantic change at all.

*Assessment*: cheap, worth doing regardless of anything else, and honest about being cosmetic. It removes the irritant (two spellings) without removing the two notions. Its main value is as the first step of Approach B, which subsumes it.

### Approach B — one Π-former with binder modes (recommended)

λ becomes the only function former; each binder carries a **mode** (comptime/erased, owned, borrow — the arrows ⇝/⇒/⇐ read as binder annotations rather than as separate function worlds). Application is typed uniformly; the checker dispatches on the modes present:

- **All-comptime binders**: today's pure λ. β when the body is consulted; structured neutral when abstract. First-class, copyable, no audit, no guard needed until it recurses.
- **Any runtime-moded binder**: the audit activates at the *binding* (check the body once against the declared Π — exactly today's per-declaration `checkFn`), opacity activates at *use sites* (callers see the Π only), the guard activates if it recurses. The degenerate case — a runtime-moded function with no borrows and no recursion — collapses toward the pure case, which is the smell test that the unification is real.

`fn f [k] (…) -> R { body }` survives as pure sugar for **an opaque, guarded, audited binding of a λ at a declared Π-type**: `let f : Π… = λ…` plus attributes. The fn-ness is four attributes of a binding — mode-rich telescope, opacity-at-use, audit-at-binding, recursion guard — not a second kind of function.

The intersection case, which is the everyday payoff: **a λ with no runtime-moded binders is one definition callable under both arrows.** This is not a new mechanism — it is the M11 pure lift (⇒ ⊇ ⇝ on the borrow-free fragment) promoted from theorem to surface rule. `add` already works this way operationally (runtime bodies evaluate `add` spines through the lift today); the unification makes the declaration form say so. This is Rust's `const fn` obtained by theorem rather than by annotation.

### Approach C — λ-only with full transparency (rejected)

Make every function a transparent let-λ; every call β-inlines. Rejected for two independent reasons, both measured in this repo:

1. **Opacity is load-bearing for expressiveness, not just abstraction hygiene.** The array era's R12: one body cannot both select a pivot (which forces `match n`, rigidifying the length) and carve at the returned index (which needs the length flex) — the call boundary's re-mint is *the only way to reset the rigidity regime*, and the array quicksort is unwritable without it. "Carving is a within-body mechanism, and function boundaries are where its guarantees stop and start again."
2. **Modular checking.** Path-sensitive checking of an inlined call tree is whole-program symbolic execution; path counts multiply per inlined call. Opacity is what makes checking per-declaration and calls O(signature).

Approach C's kernel of value — one former — is exactly what Approach B keeps; what C wrongly discards is the dial.

---

## 5. The transparency dial

Unification therefore does not eliminate the λ/σ distinction; it turns it into a **per-definition (and potentially per-use) dial** with three positions, each already exercised somewhere in this project:

1. **Transparent** — the λ is consulted; application unfolds. The pure library lives here.
2. **Abstract-but-structured** — the body is withheld but applications are remembered (`σf a`). Induction hypotheses and higher-order parameters live here *necessarily*; named definitions could optionally live here for proof-engineering reasons (a lemma about `quicksortSpec` may want its defining equations, not its normal form).
3. **Opaque-with-contract** — the body is withheld, applications are forgotten (fresh σ), and the declared type/ensures is the entire interface. Runtime calls live here by the M23 thesis; `Qed`-style sealed proofs are the comptime analogue.

This is precisely Lean/Coq **reducibility** (`@[reducible]` / default / `@[irreducible]` / `opaque`; Coq's `Transparent`/`Opaque`, `Qed` vs `Defined`, and module-type ascription = position 3 with declared equations, which is §6.2's "spec" point). Two facts keep the dial honest:

- If named definitions are always *willing* to unfold on demand (lazy δ), convertibility is identical to today's always-splice semantics — the dial's positions 1↔2 are then a representation/cost choice, not a semantic fork. (The cost is real and measured: always-unfold compares normal forms whose size tracks the definition, not the use site — the 55M-node certificate descent — which is why δ-constants is filed. But it is a cost choice.)
- Position 3 *is* a semantic fork, and it is the point: it changes what callers may know, and R12 shows that restriction is sometimes the enabling mechanism. DLLBC's novel claim in this space is exactly that: an opacity dial that is load-bearing for *expressiveness*, where every prior system's dial is for abstraction hygiene or proof-term size.

The precision spectrum of §6.2 (parameter / transparent definition / sealed spec) was this dial before we had the vocabulary for it.

---

## 6. Constraints any solution must respect

Collected from this project's own findings; these are the tripwires for whoever writes the precise semantics.

1. **Comptime abstract application is the structured neutral, never fresh-σ** (§2). Congruence, statability, resumability all die otherwise.
2. **Opacity must remain available and per-definition** (R12 + modular checking). Transparent-by-default for the pure fragment, opaque-by-default for runtime-moded definitions, is the natural polarity.
3. **Recursion stays tied to a named, guarded binding.** An anonymous recursive λ reopens `fn bad () -> Id Z (S Z) { bad() }` through a side door; the `[k]` guard is per-declaration and must remain so. Unnamed λ's don't recurse; that is a feature.
4. **The audit is a property of the binding, not the call.** Check the body once against its declared Π (with exit snapshots and ensures when borrow modes are present); use sites consult the Π. This is today's architecture restated, and it is what makes checking scale.
5. **Borrow-capturing closures are not a prerequisite and should come last.** A closure capturing a borrow is a linear value whose loan must travel with it and return — the §10 capture rule, genuinely new machinery. Unrestricted closures (capturing only comptime values) are easy and can come early. Nothing in Approach B requires either.
6. **Both machines, both extent-kinds.** Every unification choice must run in the executing machine and be exercised by the differential at both concrete and symbolic arguments — the array era's standing doctrine, and doubly so here since the polarity finding showed the concrete machine can be the wrong one.

---

## 7. Recursion: `fn` as sugar for recursors

The observation that `fn` is "basically sugar for recursors" is adopted here as the **soundness strategy for the guard**, not just an intuition. The `[k]` snapshot-subterm condition is "recursive occurrences apply only to structural predecessors," which is what an eliminator provides by construction; self-ensures admission is dependent elimination where the motive is the postcondition (the IH *is* the ensures at the predecessor). The metatheory should justify the guard by exhibiting the elaboration: guarded `fn` ⟹ definable as an eliminator term ⟹ sound. Two caveats, neither an objection: the elaboration is a proof device, not an implementation (M11's wall showed raw eliminator terms are ergonomically impractical — the sugar is load-bearing in the other direction); and one guard mode outruns a vanilla recursor — decreasing through a borrow's payload snapshot — where the eliminator reading must thread through the mutation story. Mutual recursion remains rejected (per-declaration guards would admit `f → g → f`); general well-founded measures remain §8's future.

---

## 8. Prior art

- **Idris 2 / QTT**: one function type with per-binder quantities (0/1/ω); quantity 0 is erased/comptime ≈ our ⇝-moded binders. The closest existing shape to Approach B's Π-with-modes.
- **Rust `const fn`**: one definition usable in both worlds, gated by a restriction analysis. Approach B's intersection case is this obtained by theorem (the M11 lift) rather than annotation.
- **Lean/Coq reducibility, `Qed`/`Defined`, module ascription**: the transparency dial, positions 1–3, battle-tested. What none of them have is a dial position that is load-bearing for expressiveness (R12) — that is the part DLLBC would be saying that is new.
- **This repo's own M22→M23 transition**: the only place we know of where spine-semantics calls and fresh-σ+ensures calls were both mechanized over the same programs and the choice between them made on explicit grounds. The unified design should cite it as the evidence that position 3 is a choice, not a necessity.

---

## 9. Open decisions

For whoever turns this into precise semantics; none are blocking for discussion, all are blocking for implementation.

1. **The binder-mode inventory.** Minimum: comptime (erased), owned, `&mut`-borrow. Is `⇜` a mode or a judgment-only arrow? Do proof binders need a mode distinct from comptime (they are comptime, but copyability of proofs is its own §2.1 story)?
2. **Dial granularity.** Per-definition is the floor. Per-use-site transparency (a caller asking to unfold a willing definition — Lean's `unfold`) is probably wanted for proofs about pure functions; per-conversion-problem is how Lean actually implements it. Position 3 must be per-definition only (a caller cannot un-seal an opaque function).
3. **The recursion surface for local functions.** `let rec f [k] : Π… = λ…` with the guard, or top-level-only recursion retained? (Constraint 3 applies either way.)
4. **Whether runtime calls may *opt into* position 2** (spine semantics — a remembered `f x σₚ` application). The M22→M23 history says no for the mission; the applicative-calls observation (§3) says it would be sound. Recommended: keep the door closed until something needs it, and record that it is a door, not a wall.
5. **The ensures of the intersection case.** A pure λ used at runtime has no borrows and hence no exit snapshots — its "ensures" is just its return type. Confirm the audit degenerates to `hasType` exactly (it should; this is the smell test of §4B).
6. **Closures and capture** — deferred wholesale to §10 of the main note; nothing above depends on it.

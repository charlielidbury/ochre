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

How the rest of this document disposes of the five: difference 1 becomes per-binder **modes** (§6); difference 2 becomes a syntax node, the **seal** (§5); differences 3 and 4 dissolve together — recursion is eliminators and the audit is the checking of the seal (§7); difference 5 splits into an easy case the recursion plan needs (closed function values, §7) and a genuinely open one (borrow-capturing closures, already deferred in §10 of the main note) that unification does not need to solve first.

---

## 2. The conceptual foundation: two representations of a function

Ω stores every other type of value in two representations — a literal (`5`, `Cons 1 σₜ`) that computes, and an abstract σ (`σ : Nat`) typed in the σ-context that does not. Functions come in the same two representations:

1. **A literal λ** — `λ (x : Nat). x`. Application β-reduces: the body is known, so unfold it.
2. **An abstract function** — `σ : Π (x : Nat) → Nat`. The body does not exist; application cannot unfold anything.

The design question is entirely about what rule 2 produces, and the answer is **different in the two worlds**. The best way to see it is one example of each, both real and both in the repo, so the two behaviours can be pointed at separately before observing they are not the same thing.

### 2.1 The comptime example: `id_congr`

The smallest real example is in the repo's J-kit. `id_congr` is congruence — "if `x` equals `y`, then `f x` equals `f y`": applying any function to both sides of an equation preserves it. Formally `Π A B (f : A → B) (x y : A) → Id A x y → Id B (f x) (f y)`, and its body is a single `j`:

```
j A x                                        -- eliminate p : Id A x y
  (λ (y' : A). λ (h : Id A x y').
     Id B (f x) (f y'))                      -- motive: mentions the ABSTRACT application f x
  Refl                                       -- base case: must inhabit the motive at x,
                                             --   i.e.  Id B (f x) (f x)
  y p
```

Here `f` is exactly rule 2's case: a λ-binder of Π type with **no body anywhere** — applying it cannot unfold anything. The base case is the whole story: `Refl` inhabits an `Id` only if the endpoints convert, so the two occurrences of `f x` — arising from two different positions in the motive — must be **one term**. Under the structured-neutral rule they are: each is the remembered application `.app σ_f x`, syntactically identical, and `id_congr` checks. *This is the behaviour to point at for comptime*: applying an abstract function yields a structured expression that remembers its parts, so the same application arising anywhere is the same term, and can be equated with itself.

The counterfactual: mint a fresh σ per application and the two occurrences are σ₁ and σ₂ — `Refl` is rejected, `id_congr` is unprovable, and everything citing it (`add_zero`, `add_succ`, `add_comm`, the congruence-using library wholesale) dies transitively. The same shape recurs at every abstract type family: `list_rw`'s `Π (P : List Nat → Type) → …`, and even `λ (h : P x). h` fails to check at `P x → P x`. (Note what the counterfactual does *not* break: applications of *known* functions like `add a' b` unfold under rule 1 regardless, stick inside their bodies at a recursor, and are compared as open recursor expressions — rule 2 never fires on them.)

Beneath the example sits the principled reason, which is the real content of the comptime rule: **"fresh per application" has no coherent trigger at comptime.** ⇝ is a pure judgment — conversion evaluates the same term as often as it pleases, substitution copies applications into types, and normalization must be a *function of the term*. There is no event to hang a minting on; re-evaluating `f x` twice would disagree with itself. Minting needs an **event**, and comptime application is a *term*, not an event. Runtime application *is* an event — it happens once, in order, in Ω — which is why the fresh-σ rule is coherent there and only there (§2.2).

### 2.2 The runtime example: calling `partition`

M23's relational partition (S23Direct) has this signature — no model function of it exists anywhere; the return type is the entire interface:

```
fn partition [v] (v : &mut List Nat, p : Nat)
  -> Σ (hi : List Nat) → Σ (hub : Ub p (*v)) → Σ (hlb : Lb p hi)
       → Π n. Id Nat (add (count n (*v)) (count n hi)) (count n (old *v))
```

At a call site — `quicksort`'s body, say — the caller holds `v ↦ borrowₘ ℓ σ_entry` and executes `let r = partition(&mut *v, p)`. What the checker does is the **opposite** of §2.1: it does *not* form a remembered application `partition σ_entry p`. It **mints a fresh σ'** for the borrow's payload — `*v` is now σ', an opaque list with no computational relationship to σ_entry — and attaches to it exactly the knowledge the return type declares: `Ub p σ'`, `Lb p hi`, and the count equation relating σ' and `hi` to the *entry* snapshot (`old *v` resolves to σ_entry). Everything `quicksort` subsequently proves about its own exit, it proves **from those facts alone**: it cannot compute `count n σ'` (σ' is opaque), it can only cite the returned `Π n. Id …` and chain it with its recursive calls' equations. *This is the behaviour to point at for runtime*: the call **forgets the application and compensates with a contract**.

And the forgetting is wanted, twice over. First, it is the M23 thesis itself: the postcondition should be the caller's *only* knowledge — if the caller could see through the call, the ensures would never be exercised and verification would silently lean on bodies (which is the M22 model architecture, deliberately retired). Second, the array era found forgetting to be *enabling*, not merely acceptable (R12): the re-mint returns the payload **uncarved and flex-lengthed**, which is the only state from which the caller can carve at the returned pivot index — a body that saw through the call could not be written at all. Note also what must *not* hold here: two calls `partition(&mut *v, p)` at different moments must **not** be identified — under fresh-σ they are σ'₁ and σ'₂ with separate contract instances, which is correct, since the payload differs between the calls. (Value semantics is what keeps even this honest: because borrows carry their payloads, the entry state is *part of the arguments*, so the forgetting discards provenance the type system could in principle have kept — see §3 — rather than papering over hidden state.)

### 2.3 The observation: these are two different answers to the same question

Both examples answer "what does applying a function-without-a-consultable-body yield?" — and they answer it oppositely:

- In §2.1, knowledge flows **through structure**: `f x` is usable *because* every occurrence is the same remembered term. Identification of repeated applications is the mechanism of proof.
- In §2.2, knowledge flows **through contract**: `partition(…)` is usable *because* the declared ensures attaches facts to a deliberately memoryless σ. Non-identification of repeated applications is correct, and the forgetting is itself load-bearing.

Neither can do the other's job: run §2.1 with fresh-σ and the lemma library dies; run §2.2 with remembered spines and you have rebuilt M22 (the exit payload as the spine `sortRangeL fuel lo cnt σ_entry`, lemmas reaching through the call) — coherent, mechanized, and deliberately retired in favour of the contract discipline. The unified calculus therefore does not pick one; it assigns them to their worlds. Two rules per world, no third primitive:

| | body known | body unknown / withheld |
|---|---|---|
| **comptime (⇝)** | unfold (β) | structured neutral `σf a`, typed by Π-instantiation |
| **runtime (⇒), sealed call** | — (the seal withholds the body, §5) | fresh σs per the type: minted result, re-minted borrow payloads, ensures attached |

The right way to say *why* the comptime side gets its rule — and the soundness condition on the whole design — is as a **closure property of the judgment, policed by modes**. `id_congr` for *all* `f` is legitimate at comptime because the mode system guarantees no effectful function can ever be a *value* of comptime function type: a borrow-taking function has no ⇝-applicable form at all. Determinism is not an assumption made about functions; it is a property of the room, enforced by the fence around it. Congruence therefore attaches to the **judgment of use, not the kind of variable**: an erased family `P : Nat → Type` and the runtime-capable `add` both enjoy it whenever they are evaluated under ⇝ — they merely enter the room through different doors. `P` enters by *mode* (it exists only there, guaranteed erased, never observable by ⇒); `add` enters by the *purity of its type* (no runtime-moded binders ⟹ admissible under ⇝ — the M11 lift as an admission ticket). Two doors, one room, one equality. Drawing the line by variable kind instead — congruence only for erased things — would sever the observation vocabulary (`count`, `add`, `len` are runtime-capable functions used pervasively inside types) from the equality that specs are written in. Symmetrically, at runtime there is no equality *judgment* for congruence to live in: there are call *events*, never identified, and Id-facts about their results exist only as declared ensures — determinism purchasable per-function, by contract, which is the honest discipline where effects and linearity make the free one false.

---

## 3. The unifying principle: application-by-type

The two right-hand cells are one principle at two type richnesses: **applying an abstract function yields exactly what its Π-type promises and nothing more.** For a pure `Π (x : Nat) → Nat`, the promise is only "a Nat depending on x" — the structured neutral is that promise verbatim. For a borrow-moded `Π (v : &mut List Nat) → Σ (Sorted (*v)) → …`, the promise is richer — an exit payload for the borrow, evidence about it — and the call rule's minting-plus-ensures is *that* promise verbatim. Today's "call rule" is not a separate concept from application; it is abstract application at a moded Π.

What makes this legitimate — and this is special to DLLBC, not a general fact about imperative languages — is the value semantics. In a heap language, "call as application" is unsound: two calls with equal arguments needn't agree because the world changed between them. Here the world *is* the arguments: borrows carry their payloads, so a call is semantically a pure function of (arguments + entry payloads) to (result + exit payloads) — which is exactly the reading the ensures convention is built on: `old *v` names the entry payload as an input, the exit-snapshot `*v` names the exit payload as an output. Runtime calls are *applicative*, and the σ-model extends to them soundly **because of §0's value semantics**. This is the deep reason the unification is principled rather than notational.

---

## 4. The design, and its rejected dual

### The design — one Π-former with binder modes

λ becomes the only function former; each binder — Π/λ parameters and `let` alike — carries a **mode** (comptime or runtime, with borrows visible in the type), denoted by capitalisation: erased/comptime binders are capitalized (`Hfuel`, `P`, `let X = …`), runtime binders lowercase (§6). Application is typed uniformly; the checker dispatches on the modes present:

- **All-comptime binders**: today's pure λ. β when the body is consulted; structured neutral when abstract. First-class, copyable, no audit, no recursion except through eliminators.
- **Any runtime-moded binder**: opacity and the audit arrive together as the **seal** (§5) — the body is checked once against the sealed Π (exactly today's per-declaration `checkFn`), and use sites see the Π only. Recursion is a recursor term under the seal (§7). The degenerate case — runtime-moded, no borrows, no recursion — collapses toward the pure case, which is the smell test that the unification is real.

The modes are not bookkeeping — they are what makes §2.3's split *sound*: comptime congruence-for-all-`f` is a closure property of ⇝ only because the modes guarantee nothing effectful can ever be a value of comptime function type, and the intersection rule below is precisely the judgment's admission ticket.

The intersection case, which is the everyday payoff: **a λ with no runtime-moded binders is one definition callable under both arrows.** There is an implicit restriction here worth stating: such definitions are necessarily *pure* — a `&mut T` argument could never be formed by ⇝ in the first place, so borrow-taking functions are excluded from the intersection by construction (and the body must itself stay in the borrow-free fragment: a pure-bindered λ that borrows a local and calls a mutator has no ⇝-evaluation either). This is not a new mechanism — it is the M11 pure lift (⇒ ⊇ ⇝ on the borrow-free fragment) promoted from theorem to surface rule. `add` already works this way operationally (runtime bodies evaluate `add` spines through the lift today); the unification makes the declaration form say so. This is Rust's `const fn` obtained by theorem rather than by annotation.

### The rejected dual — λ-only with full transparency

Make every function a transparent let-λ; every call β-inlines. Rejected for two independent reasons, both measured in this repo:

1. **Opacity is load-bearing for expressiveness, not just abstraction hygiene.** The array era's R12: one body cannot both select a pivot (which forces `match n`, rigidifying the length) and carve at the returned index (which needs the length flex) — the call boundary's re-mint is *the only way to reset the rigidity regime*, and the array quicksort is unwritable without it. "Carving is a within-body mechanism, and function boundaries are where its guarantees stop and start again."
2. **Modular checking.** Path-sensitive checking of an inlined call tree is whole-program symbolic execution; path counts multiply per inlined call. Opacity is what makes checking per-declaration and calls O(signature).

The rejection's kernel of value — one former — is exactly what the design keeps; what it wrongly discards is opacity, which §5 makes into syntax instead.

---

## 5. The seal: opacity as syntax

Opacity stops being a stance or an attribute and becomes **one AST node**: `.seal t u`. Its semantics is programmer-invoked generalization — "forget everything about this value except its type" — and its two readings are the two machines':

- **Concrete evaluation (⇒, executing)**: evaluate `t`. The body exists and runs; execution is always transparent.
- **Checking (⇒, symbolic)**: verify `t : u` **once, at the node** — this check *is* the audit; when `u` is a borrow-moded Π with ensures, it is exactly today's `checkFn`, exit snapshots and all — then yield a **fresh σ : u**. Everything downstream sees only the type.

Scoping is what keeps the kernel simple: `.seal` is legal **anywhere ⇒ evaluates** (every ⇒-evaluation is an event, so minting is coherent even for a seal passed directly as a call argument) and is **absent from the pure term grammar** — ⇝ never meets the node, so no comptime rule for it exists at all. There is no freeze semantics, no term-level identity question, nothing: the problem §2.1 would pose (mint-per-reduction making a term disagree with itself) is made unaskable by the grammar. Term-level references to sealed things are ordinary variable references to the binding's σ — atomic, self-identical, free.

What the seal delivers, in order of everyday impact:

1. **`fn` is not a primitive** (§7): `fn f (…) -> R { body }` ≡ a binding of `.seal ⟨body-term⟩ ⟨Π with ensures⟩`. Audit-at-binding and opacity-at-use are just what the seal means.
2. **Sealed proofs are `Qed`**: `let cert = seal ⟨enormous proof⟩ ⟨statement⟩` mints one σ at the statement; citations are σ-references; `hasType` reads the statement without ever descending the proof. The measured certificate costs — the 55M-node audit descents, "a reject costs the same as an accept" — become O(statement). This is the semantic form of what the δ-constants filing wanted representationally.
3. **Sealed interfaces**: a function sealed at its Π, exported alongside chosen lemmas about it — ML-module information hiding available inside the language.
4. **The seal type is the contract; what you keep is what you write.** Seal the identity function at `Π (x : Nat) → Nat` and callers know nothing about results — sound, honest, useless. To keep knowledge across a seal you must ascribe at a richer type — Σ-conjuncts, `old`/exit facts. The M23 ensures discipline stops being a convention and becomes a consequence of the syntax.

Relation to the transparency spectrum (the main note's §6.2 named it first: parameter / transparent definition / sealed spec): the seal is position 3, per-definition by construction — a caller cannot un-seal. Positions 1↔2 (transparent definitions, unfold-on-demand for *cost* rather than eagerly-spliced) are a separate, optional, purely representational design — the δ-constants filing — which the seal needs nothing from: if adopted it changes no convertibility, only who pays for normal forms. Keeping these two apart is the resolution of an earlier conflation: **seals are semantic and need zero new kernel beyond the node; δ is representational and optional.**

DLLBC's novel claim in this space stands as before, sharpened: every prior system's opacity dial (Lean/Coq reducibility, `Qed`/`Defined`, ML's `:>`) serves abstraction hygiene or proof-term size; R12 makes DLLBC's seal **load-bearing for expressiveness** — programs exist that cannot be written without it.

---

## 6. Binder modes: capital is comptime

Every binder — λ, Π, and `let` alike — carries a **mode**; the working surface convention marks it by case:

- **Capitalized binder** (`P`, `Hfuel`, `N`) — **comptime**: at a ⇒-call, the argument expression is evaluated under **⇝** — a pure, non-consuming read. The binder is erased (never observable by ⇒), never moved, citable after any call, and usable in the body **only in ⇝-positions** (types, proofs, capital arguments of other calls). A runtime match on it is rejected — the per-binder fence, Idris-2-style erasure checking, and the enforcement mechanism behind §2.3's closure property.
- **Lowercase binder** (`x`, `v`, `fuel`) — **runtime**: evaluated under ⇒ at calls (moved, or loan-captured for borrow types), present at runtime. Borrow-typed binders must be lowercase (a ⇝-read of `&mut` is meaningless); this is checked, not assumed.

This one convention deletes two existing mechanisms and subsumes a third:

1. **The proof-consumption half of the index-kind heuristic retires — and only that half** (corrected 2026-08-05, M27-P3; the original claim, "the index-kind copy-on-read heuristic retires", is preserved here as what was believed and is superseded by measurement). Today `readR` moves everything, so comptime-ish arguments kept being consumed — patched by a kind-based classification (M20) after M19 explicitly filed "a copyable/comptime class that `readR` doesn't move" as an open design question. Capital-marked binders evaluated under ⇝ *are* that class for **call arguments**, declared rather than inferred — the M7→M17 grain again, and R16's pain genuinely fixed.

   What modes do **not** retire is copy-on-read at a body's own **slot read**, because it is a different judgment reached at a different place. `readR`'s `.var` case runs the comptime fence *before* the slot lookup, so a capital binder's runtime read is **rejected**, not copied: capitalisation removes the read rather than turning a move into a copy. Any binder whose value must genuinely exist at runtime and be read more than once therefore has no mode-shaped substitute — and two corpus sites cannot be capitalized on grounds this document itself supplies, `storeProof`'s `a` being *returned* in a `Pair` (§12 decision 3: a capital binder is not returnable) and `S7Group`'s `a` being *borrowed* (§6: borrow-typed binders must be lowercase).

   The decisive reason is not precision but the **differential**. `indexKindV` classifies by value shape, and a concrete `Nat` is a constructor tree that copies unconditionally; if a σ of type `Nat` moved while its concrete counterpart copied, the two machines would diverge on ordinary programs. Measured: turning the symbolic half off reddens ~80 assertions across 13 files, and the first two to fall are S9Diff's whole-program simulation assertions. Deleting the heuristic does not cost precision — it breaks the simulation relation, and no capitalisation sweep can repair that, because the concrete side has no binders to capitalize.
2. **The proof-consumption staging pains shrink.** "Passing a proof to a call moves it" (R16) forced capture-before-call staging (`mkTop` and friends). A capital `Hfuel` is ⇝-read: never consumed, citable after the call it was passed to. Several of the six snapshot-naming filings get cheaper.
3. **The spec-vs-runtime distinction for function-typed binders** — the one place kind cannot decide the mode — is the same convention: `map_spec (G : Nat → Nat, v)` (caller may supply an abstract or sealed function with no runtime existence; erased) versus `map_apply (g : Nat → Nat, v)` (caller owes a runtime function value). Congruence is *not* what the case decides — any pure-typed application in a ⇝-position is congruent regardless (§2.3); the case decides **runtime existence**: what callers must supply, what is erased, what the body may do with it.

One genuinely new capability comes along: **erased data** (`N : Nat` used only in types — QTT's quantity 0), which kind-derivation alone cannot express.

**Case is inert under ⇝, which is why both-worlds functions need no capitals.** In a type or proof position the whole spine is evaluated purely — there is nothing to move — so `add` stays all-lowercase: its binders are honest runtime data when it is *called*, and the M11 lift admits the whole definition into ⇝ when it is *cited*. You never capitalize a definition to use it in specs. Capitals mark binders whose **arguments stay comptime even while the function itself runs under ⇒**: proofs, families, erased indices, spec-only function parameters. The flagship signature reads `quicksort (fuel, v, Hfuel)` — `fuel` lowercase (the body branches on it), `v` lowercase (borrow), `Hfuel` capital (cited in certificates, never scrutinized, never consumed).

**The same convention extends to `let`.** `let X = e` is a **comptime binding**: `e` evaluated under ⇝, `X` erased, non-consuming, usable only in ⇝-positions — local spec abbreviations, locally-derived certificates, intermediate type computations, all without a new form. `let x = e` remains today's runtime let. (Top-level declarations are events, which is where seals live; a comptime `let X` is transparent by nature — sealing is a ⇒-form.)

One practical wrinkle, resolved by prescription: capitalized identifiers would collide with constructor names (`S`, `Z`, `Cons`, `True`), so **constructor names are special-cased as keywords** — the fixed basis makes the set closed and small, and reserving it costs nothing. Any other capitalized identifier is then unambiguously a comptime variable; capitalisation is the mode marker, full stop.

---

## 7. Recursion: recursors all the way down

The earlier observation that guarded `fn`-recursion is "sugar for recursors" is here **promoted from soundness argument to semantics**: recursion *is* eliminators, and `fn` is a macro.

**The elaboration, concretely.** `fn quicksort [fuel] (fuel, v, Hfuel) -> ⟨ensures⟩ { body }` elaborates to a binding of `.seal ⟨recursor term⟩ ⟨the Π⟩`, where the recursor term is mechanical:

```
natRec
  (λ f. Π (v : &mut List Nat) → Π (Hfuel : Le (len *v) f) →      -- motive: the sealed Π
          Σ (Sorted (*v)) → Π n. Id (count n (*v))               --   with the scrutinee
                                    (count n (old *v)))          --   argument peeled off
  (λ v Hfuel. ⟨base: Le (len *v) Z ⟹ empty; le_zero_eq⟩)
  (λ f'. λ ih. λ v Hfuel.
     ⟨partition; split_off;
      ih ⟨left borrow⟩ H₁;  ih ⟨right borrow⟩ H₂;                -- IH applied at f'
      append_back; glue⟩)
  fuel
```

The **motive is derived from the signature** — the sealed Π with the recursor argument peeled off — so the macro needs no inference, and `[k]` survives only as the macro's hint for *which* argument becomes the scrutinee. Varying arguments are no obstacle: they are Π-bound inside the motive (the same generalized-motive move `add_comm` makes with `b`), so the recursor computes a function at each level.

**The convergence that says this is right.** A recursive occurrence never sees the body, and both stories now derive it independently: in the seal story, while `.seal t u` is being checked, `t` is not yet a checked thing — the only available view of the function is the σ-side, so the recursive call is abstract application at `u` (**self-ensures, forced rather than stipulated**); in the recursor story, `ih` is a bound Π-typed *variable* — literally the sealed view at the predecessor. Two consequences fall out rather than being legislated: the `[k]` guard **evaporates** for recursor-expressed functions (termination by construction — no snapshot-subterm check, no mutual-recursion rejection rule to maintain), and an *unsealed* recursive λ is simply incoherent at checking (unfolding self never terminates), so the language's two recursion forms — transparent eliminator terms in the pure fragment, sealed recursor bindings for everything else — are theorems of the design, not rules.

**What it costs, itemized:**

1. **Runtime-moded recursor motives are the one real kernel addition**: arms contain writes, calls, and borrows — *bodies* — so the checker must symbolically execute an arm as a body with an abstract `ih : Π` in scope. The content of that judgment is exactly today's guard-checking (a body with only the sealed self-view available); the plumbing is new.
2. **`ih` is a first-class runtime function value** — but the *boring* kind: closed (arms reference only their own binders and globals), never partially applied, taking its borrows as arguments. Runtime slots holding closed function values plus call-through-a-variable is all that is needed — roughly 20% of closures, and the checking side needs none of it (checking-side `ih` is a σ : Π; abstract application at a moded Π is the existing call rule keyed by a variable). Environment capture and borrow-carrying closures stay deferred.
3. **Application must be saturated.** Unary curried application at runtime creates the closure problem by construction — `(natRec … fuel) ⟨borrow⟩` is a partial application *holding a borrow* while awaiting the next argument. Two equivalent disciplines avoid it: n-ary spine application (the incumbent — today's telescopes are consumed whole by `processArgs`), or **unary λ taking a Σ-package, matched immediately** — which has no partials by construction and makes λ *unary everywhere* (comptime λ already is), maximal former-uniformity. A *stored* Σ-of-borrows degrades gracefully in principle (it holds suspended loans the demand-end rule reaches later), but only the passed-as-parameter direction has been exercised (the slice probe); the stored and returned directions carry this project's standing warning about unexercised directions.
4. **One guard mode has no easy recursor form**: decreasing through a borrow's *payload* (the `zero_all` shape — no counter at all). Fuel-threading is the always-available fallback; the principled successor is §9. **This is an accepted naturalness regression** (decided 2026-08-04): programs that today recurse `[v]`-style (`split_off`, `zero_all`) become fuel-threaded until §9 exists — accepted because the kernel simplification (guard deleted, recursion a theorem of the design) is worth more than the interim surface cost. The regression is owned here so nobody rediscovers it as a defect.
5. **The executing machine changes too, and goes first.** Concretely: ι-reduction of recursors whose arms are *bodies* (writes, calls, borrows) as control flow, λ-application under ⇒ (bind and run — the existing call semantics with the callee resolved from a value rather than a table), and `ih` as a closed closure in a runtime slot. Nothing conceptually new, but it is new surface in precisely the machine where the array era's surprises lived — so per the polarity doctrine the executing side is built **first or in lockstep** with the checking side, never after, with the differential exercised at concrete and symbolic scrutinees from the first commit.

---

## 8. Programs are terms

There is no declaration former and no module story, because there is nothing left for one to do: **a program is an arbitrary term, and running it is ⇒-evaluating it.** A "module" is a let-chain ending in an expression — `let add = λ…; let Quicksort = …; let quicksort = seal ⟨natRec …⟩ ⟨Π…⟩; ⟨main⟩` — and every piece of structure a declaration form ever carried already lives on the binding: mode by case (§6), opacity by `.seal` on the right-hand side (§5), recursion inside the term as a recursor (§7). `Decl` is deleted alongside `fn`.

The consequences compose from decisions already made. ⇒-evaluation of each `let` is exactly the event the seal's minting needs — one σ per sealed binding, in program order — and checking a program is the symbolic machine making the same walk: each sealed let fires its audit once (per-declaration `checkFn`, relocated), each transparent let binds, the tail is checked in the accumulated Ω. **Call tables become scope**: a caller sees exactly the bindings lexically above it, so the checker's callee-resolution table and its assembly disappear; negative tests that today pass deliberately-wrong tables become programs with different let-prefixes. And a let-chain cannot reference downward, so *no forward references* falls out — consistent by construction with mutual recursion being rejected: what the guard policed by call-graph reachability becomes unwritable. Files, caching, and incremental re-checking are the meta-layer splitting one term, with no semantic content — a planner concern, out of this document's scope by charter.

---

## 9. The borrow-mode eliminator (filed, not built)

The shape: a structural recursor over a mutable structure — `listRecMut` applied to `&mut List T`, arms receiving field borrows. The insight that makes it more than a control gadget: **a borrow-mode eliminator is the induction principle of the ensures discipline** — its motive relates entry and exit states, and each arm proves its constructor's postcondition given the tail's postcondition. The `ih` *is* the ensures at the predecessor, which is exactly the proof pattern M23's relational programs execute by hand.

A literature survey (2026-08-04; reproduced in full in `survey-effectful-folds.md`, alongside this file) both validates and corrects the design:

- **Validated, four times independently**: Swierstra's Hoare state monad (the IH arrives as precisely the recursive call's postcondition, delivered as hypotheses); Hoare Type Theory (whose binary `init`/`mem` heap relations are `old *v`/`*v` verbatim — including the phrase "mediating the switch from unary to binary relations" for what our audit does); Low\*'s `C.Loops.for` (the eliminator as an ordinary `let rec` whose type is Nat-recursion with a heap-indexed motive — and which the compiler extracts to a literal C loop); and Lean 4.30's `Std.Do.Spec.forIn'_list` (a *proven* `@[spec]` theorem: invariant as motive, loop body as arm, conclusion "motive at empty cursor → motive at full cursor" — the closest existing artifact to this design).
- **Nobody ships it as a primitive.** Every instance is derived: a combinator, a theorem, a desugaring, or a spec-typed fixpoint. The recommendation transfers: once §7's arms-as-bodies machinery exists, *derive* the borrow-eliminator; do not add it to the kernel.
- **The load-bearing correction: the motive must be cursor-indexed, not whole-structure.** Four systems converge on the same shape (Lean's `Cursor {prefix, suffix // prefix ++ suffix = l}`; Low\*'s invariant split at index `i` — below it the new values, at-or-above it *still the entry values*; Creusot's ghost `produced`; HTT's reverse over a pair). A motive relating only the whole entry snapshot to the whole exit snapshot **cannot state the state of a half-done traversal**, so the arms cannot prove it. Each arm proves: prefix already satisfies the exit spec, suffix still equals the entry snapshot, one step moves the boundary. The DLLBC mapping is pleasing: the borrow-match's suspended field loans *are already* the syntactic marker for the untouched suffix.
- **The effect-order wall dissolves.** Bottom-up ordering is a property of *catamorphisms*, not of spec-typed recursion: every surveyed system recurses with the spec as the type and runs effects in written order (HTT's in-place list map writes the head *then* recurses, no contortion). The eliminator should be derived from spec-typed recursion, not imposed as a fold.
- **The UX warning (Swierstra's `NoDup` failure)**: the declared ensures is frequently *not* a usable motive — some postconditions are unprovable as stated and need a strictly stronger invariant, weakened afterwards through a computationally inert consequence rule (three systems needed it independently). Whatever the surface, the eliminator must accept a motive stronger than the signature, plus a weakening step at the audit — otherwise "the checker rejects my correct postcondition" dominates the experience.
- **An alternative worth holding**: compute the motive by *folding the element specs* over the same structure (Dijkstra-monad style: `mapD : D (list β) (mapW l w)` — the spec of the fold is the fold of the specs, order fixed once and matching by construction). Plays directly to the array era's ι-rules.

Status: filed. Fuel-threading covers payload-decrease until it exists.

---

## 10. Constraints any solution must respect

Collected from this project's own findings; the tripwires for whoever writes the precise semantics.

1. **Comptime abstract application is the structured neutral, never fresh-σ** (§2). Congruence, statability, resumability all die otherwise — and "fresh" is not even well-defined where there are no events.
2. **The seal is per-definition and cannot be undone by callers.** Transparent-by-default for the pure fragment, sealed-by-default for runtime-moded definitions, is the natural polarity.
3. **Recursion stays tied to eliminators or sealed bindings.** An anonymous transparent recursive λ has no checking story (§7 derives this); the `bad()` self-proof stays unwritable by construction.
4. **The audit is the checking of the seal, at the binding.** Use sites consult the Π. This is today's architecture restated, and it is what makes checking scale.
5. **Closures arrive in two stages, and only the trivial stage is needed now**: closed function values with saturated application (§7); environment capture and borrow-carrying closures stay deferred (main note §10) and nothing above requires them.
6. **Both machines, both extent-kinds, and every direction of every new value form.** The differential must exercise unification choices in the executing machine at concrete and symbolic arguments — and stored/returned directions of Σ-packages, not just passed — per the array era's standing doctrine and its polarity finding. Seals sharpen this: `.seal` is legal anywhere ⇒ evaluates, so checking-vs-executing divergence points (a fresh σ against a concrete value) now occur **mid-expression**, not only at call boundaries and group releases — a new simulation-relation case, named here so it starts life as a stated obligation rather than an assumed one (R9's lesson).
7. **No macro is in the TCB.** The `fn` macro's translatability of self-calls into `ih` applications replaces what the `[k]` guard policed — and that is sound only because the elaborated recursor term is re-checked by the kernel at the seal. Macro output is always kernel-checked; a macro bug is an inconvenience, never an unsoundness.

---

## 11. Prior art

- **Idris 2 / QTT**: one function type with per-binder quantities; quantity 0 ≈ capital binders (§6), including erased data. The closest existing shape to the whole design.
- **Rust `const fn`**: dual-availability by restriction analysis; §4's intersection case is this by theorem (the M11 lift).
- **Lean/Coq reducibility, `Qed`/`Defined`, ML opaque ascription `:>`, module-type ascription**: the transparency spectrum and the seal's ancestors. None has a dial position that is load-bearing for expressiveness (R12) — that part is new.
- **This repo's own M22→M23 transition**: both call semantics (remembered spines vs fresh-σ+ensures) mechanized over the same programs, the choice made on explicit grounds — the evidence that §2.2's rule is a choice, not a necessity.
- **For §9**: Swierstra, *The Hoare State Monad* (TPHOLs'09); Nanevski et al., Hoare Type Theory (JFP) and the Coq HTT library (whose `llist.v`/`quicksort.v` are the closest existing artifacts to DLLBC's target signatures — its quicksort states Perm-plus-locality as one conjunct, `exit = pffun p entry` with `perm_on` bounded support, worth comparing against the counting encoding); *Dijkstra Monads for All* (ICFP'19); F\*/KaRaMeL `C.Loops.fst`; Lean 4.30 `Std.Do` (`Spec.forIn'_list`, `Cursor`); RustHornBelt (PLDI'22); Creusot's iterator specs (TACAS'23).

---

## 12. Decisions

**Resolved in the design round** (2026-08-04) **and IMPLEMENTED** (2026-08-05, M26 A–E). Each carries the commit that discharged it, so a reader can go from the sentence to the machine:

1. The opacity mechanism is the **`.seal` node** — legal under ⇒ anywhere, absent from the pure grammar; checking it is the audit. (Not: a reducibility attribute; not: a const table — δ remains a separate optional representation design for *transparent* names only.) **Implemented `603a25ee`.** The exclusion is structural rather than a check: `.seal` is its own constructor, so ⇝'s application rule cannot see it, and `Val` has no seal former, so no comptime rule for it can be *written*. §2.1's question is not answered conservatively — it is unaskable.
2. **`fn` is a macro** over recursor + sealed binding; motive derived from the signature; `[k]` demoted to scrutinee-selection hint; the guard deleted for recursor-expressed functions. **Implemented `e4f171a8`**, and held to an oracle it could not be tuned against: its `split_off` output is α-equal to the recursor hand-written from this document before the macro existed. `listRec` joined `natRec` in `c4f09dad` — the same elaboration, differing only in what the step arm binds and what the constructors are called. The guard did not have to be deleted: it **evaporated**, because `ih` is a binder and a binder cannot be a self-call.
3. **Modes are per-binder, marked by case** (capital = comptime, extending to `let X`), kind-constrained (borrows lowercase); the fence checks capital binders into ⇝-positions only. Constructor names are reserved keywords, so capitalisation is unambiguous. Congruence is decided by judgment + type, never by the flag. **Implemented `3e3e4c16`/`42cb0f2b`**, at a cost of one rename in the whole corpus. Two things §6 does NOT do were pinned there: modes fix consumption (R16), not staleness (R12), and a capital binder is not *returnable*.
4. **Application is saturated** (Σ-package or spine — no runtime partial applications). **Implemented `603a25ee`/`ec7381b0`**, and it cost nothing, for a reason worth keeping: ι hands its arm the predecessor, the recursor at the predecessor, and everything the caller still owed in ONE application, so no partial application holding a borrow ever exists. Saturation is the shape of the ι rule, not an extra premise. **Half of this is SUPERSEDED by the function-model round (2026-08-05)**, and the halves separate cleanly: *saturation stands* — the call event is atomic, and c1's bounded-curry design was measured GO and not adopted — while the *Σ-package* alternative is refused on design grounds, because under packages no M23 signature is writable (`*v`/`old *v` resolve parameters, and a packaged borrow is not one), the repair reconstitutes the telescope under another name, and the match-immediately discipline turns out to be unenforceable anyway. The surface becomes juxtaposition (`f a b`), which is what a nested Π was always saying.
5. **Runtime calls do not opt into remembered-spine semantics** — door kept closed, noted as a door (the M22 history is the evidence both sides are coherent). **Unchanged, and now load-bearing in code**: `callDeclC` makes a sealed function, an `ih`, and a table entry callable by literally the same rule (`aca66665`).
6. **A program is a term** (§8): declarations are `let`s, scope is the call table, and checking a program is one symbolic ⇒-walk. **Implemented `52520fed`.** Two consequences arrived as absences rather than as rules — no forward references (a name used above its binding resolves to nothing, so the diagnosis is at the *definition*), and the deliberately-wrong declaration table becoming one caller suffix under two let-prefixes. `Decl` is NOT deleted; see the first open below.
7. **The executing machine is built first or in lockstep, never after** (§7 cost 5). **Held, `ec7381b0` onward**, and it paid twice: a kernel gap found because a test asked (a seal in return position), and — in phase E — `globalKind` admitting the σ-form of a binding while refusing its SPINE-form, green for an hour on the checking side and caught by *running* the flagship, because a seal evaluates to its own term when executing and mints a σ when checking.
8. **The `[v]` payload-decrease regression is accepted** (§7 cost 4): fuel-threading is the blessed interim. **Paid three times, and the ledger is below** — it turned out to cost less than "an accepted naturalness regression" suggests, and to be needed by fewer functions than the phrase implies.

**The decision-8 price ledger**, since a cost decided in the abstract should be recorded once it is paid:

| function | what it cost |
|---|---|
| `partition` (`476a61b4`) | one parameter, one dead `botElim` branch, **no lemma** — at the recursive call `Le (len (Cons x rest)) (S f2)` IS `Le (len rest) f2` definitionally, so the bound passes down unchanged. The bound parameter must be CAPITAL, which is §6 paying for §7: a lowercase proof parameter would have been moved by the call. |
| `append_back` (`c1ce77c6`) | the same on the callee side, and **the first real price rise on the caller's**: `quicksort` calls it after sorting both halves, and a sort returns a count equation, not a length bound — every length σ it held has been re-minted. The fuel that works is `len *v` itself with `le_refl` as its bound, STAGED in a `let` before the call, because the borrow is taken in between and a comptime argument mentioning `*v` would demand-collapse the loan it was just lent. One line inserted, one changed. |
| `zero_all` (`fca89ab3`) | one parameter, one dead branch, checking both ways on the first run. The only genuine instance left in the list world — a cursor with no decreasing argument but the payload, which is §7 cost 4's own example. |
| the ARRAY shape | **already paid, in M24, before this decision existed.** `walk` IS `walkArr` with `[fuel]` in place of `[a]` and the same body modulo its own self-call's name; it checks and it migrates. |
| **the correction** | *Most of the class was never a decision-8 cost.* §7 demotes `[k]` to a scrutinee-selection HINT, and the declaration-era guard was sound and happy with `[v]` whenever the payload decreases — a list cursor passes no counter, so nothing ever pressed an author to name a decreasing *index* that was also sitting in the telescope. But `nth`/`nth2` have one, it is a `Nat`, and the macro serves it directly. Correcting the hint is **one field of the `Decl`**: same body, same telescope, same return type, no fuel, no bound, no dead branch, no caller change. The S14 family goes from five declines to **zero**. So decision 8's honest scope is one genuine list shape (`zero_all`), an array shape already paid before the decision existed, and nothing else. |

**Still open** (the list as the design round left it, with the M27 campaign's resolutions marked in place rather than deleted — a closed question is more useful beside what it was than absent):

1. ~~**`back` under a seal — and it is what `Decl`'s deletion waits on.**~~ **RESOLVED by deletion, M27-P2** (`668f3987`, `c9c2bb4d`). The question assumed a replacement was needed for eight declarations; two things corrected that. The number was stale — once M26-F fixed the `[k]` hints underneath it, `back` stood under 49 rather than 8 — and the framing was wrong, because porting a cursor to ensures-style is not a signature change but a PROGRAM rewrite, measured: a cursor given the ensures with its body unchanged is rejected, its exit a fresh existential minted by the sub-call's group. M23 had already done the rewrite. So `back` was superseded rather than replaced, and the corpus now declares none — a fact about the type, since `Decl.back` no longer exists.

2. **The borrow-eliminator's design** (§9): cursor-indexed motive shape, the consequence/weakening rule at the audit, derive-vs-compute motives. Filed with its survey. **Shelved by the user during the M27 campaign** and explicitly NOT a dependency of `Decl`'s deletion. It gained one input in the meantime, from the other end of the language: see open 3.

3. ~~**`recDeep` — §7's genuine expressiveness limit.**~~ **TOO STRONG; corrected M27-P1** (`30298000`). `recDeep` IS expressible as a sealed recursor and it checks. An arm gets `ih` at the predecessor *of the motive it was given*, and the motive is a choice — `recDeep`'s own is constant, so `ih : P a` already IS `P b` for every `b`, with the inner `match` left intact so the two-constructors-down shape is still there. Pinned with a negative control and with the macro's continuing refusal, which is the whole content: **the limit is a MACRO limit, not a calculus one**, because §7 has the elaboration derive the motive mechanically from the signature and this is not that motive. The general two-down shape has a described route — a course-of-values motive `Q m := P m × P (S m)`, step arm `Pair(snd ih, fst ih)` — left explicitly unmechanized. **This is §9's own survey warning** ("the eliminator must accept a motive stronger than the signature") **arriving independently from the other end of the language, before §9 is built** — which makes it open 2's first datum rather than only a correction here.

4. ~~**Adopting `[i]` over `[v]` in `S14Bounds`/`S17Spec`**~~ — **ADOPTED (M26-F, `0db50c71`)**, and it turned out to be free twice over: the old path needed no re-proving, since M14's descent accepts index decrease exactly as it accepted payload decrease. One correction it produced is worth keeping past its own subject: a harness that simulates a fix by NAME-MATCHING reaches the names you thought of, while adopting at the source reaches the whole `with`-closure. `nth2Lie` renames itself, so no simulation could have reached it — and the same lesson recurred in M27-P2, where a `back` carried as a record update survived a sweep of the `back = …` syntax.

5. ~~**Stored and returned Σ-of-borrows**: exercised in one direction only.~~ **MEASURED CLEAN, NOT ADOPTED** (the Σ-package probe, branch `sigprobe`). Both directions came back clean — stored packages keep their suspended loans reachable and the returned direction is already fully general, since `buildResult` and `collectResultBorrows` recurse the Σ-tree. So the direction-coverage worry is discharged. The form is not adopted anyway, and the reason is the ensures convention rather than the machinery: see decision 4 above.

6. **δ-constants granularity**, if and when adopted: per-use unfold (Lean's `unfold`) for proofs about pure functions.

7. **Closures and capture** — deferred wholesale to the main note's §10, and **settled by the ratified model rather than by this document**: functions are ⇝-resolved NAMES and there are no runtime function values at all, so the question of what a function value may capture does not arise. §8's globals never breached the deferral and now cannot: a body names the functions bound above it, and naming is not capture.

**Opened by the M27 campaign**, since a design note that only closes questions is not keeping an honest ledger:

8. **Teaching the read rule about `fsig`.** A σ whose Π is borrow-moded has no `Val` (§2's two representations, at the one type where the second is unavailable), so it lives in the signature table alone and the copy-or-move classifier — which consults the value context — cannot see it. The checking machine then empties a slot the executing machine copies. Contained in M27 by making the position unwritable; the real fix changes the read rule for **every** σ and belongs to the function-model round. It is a PREREQUISITE of any design that accumulates arguments for a sealed callee, not an optional cleanup, because such a design's residual is exactly the object that must be bound and read back.

9. **What a cursor may promise.** M27 closed two soundness holes that were both the same shape — a claim stated in a position nothing audits — and both were refused rather than repaired: a value component of a borrow-carrying return type, and a non-trivial owed type on a parameter consumed into the result. Refusal is the right containment and the wrong end state. The open question is what a borrow-returning function *should* be able to say about its result, given that §5 point 4 makes the ascription the whole contract and the audit currently reads only owed types.

**Closed since the design round**:

* **The intersection smell test** (was open 4): the audit of a no-borrow sealed λ degenerates to exactly `hasType`, discharged in `603a25ee` as an identity over a 16-pair battery with both polarities, not as a spot check — and in milliseconds too, the seal's intercept being the pure fragment's own 6 ms. Sealing is not a tax; what it changes is the slope (0.087 ms per citation against 4.01 ms transparent, a factor of 46 that grows with the proof, because the sealed cost is a function of the statement and the transparent one of the proof).

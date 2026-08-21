# 20 — Module states: threading the checker state across `prog` blocks

Status: agreed in discussion 2026-08-21. Stages 0–3 are built (see the staged-work entries below for what each actually is); stage 4's lemma layer is done (see its entry); consumer migration to chain consumption remains.

## The problem

Reuse today is Lean-level splicing: a library definition is a Lean `def X : Term := prog defer_check { … }`, and a program that wants it either splices it (`%X`) or cites it through the identifier fallback after an `open`. Three costs:

1. Nothing checks a library definition at its definition site. `defer_check` opts it out of the program judgment (which would be the wrong judgment anyway), so an ill-typed lemma compiles green and is citable by its stated type. The reachability sweep of 2026-08-21 found ten StdLemmas entries that had *never* been checked and do not inhabit their stated types; the `chkLib` battery now embedded in `StdLemmas.lean` is a stopgap, not a design.
2. Every use site re-carries the plumbing: `open` lists naming each lemma and its type, splice markers, and the `X`/`XTy` two-defs-per-lemma convention.
3. Tooling stops at the splice boundary. A spliced term has no source positions, so hover and error spans have nothing to attach to inside it.

## The design

`prog` blocks input and output a checker state `St` (Ω's comptime bindings, `sctx`, the fn/call table, the seal-site table, and the housekeeping counters — `nextSym`, seal-site numbering). A module is a `prog` block interpreted once, at its own elaboration; its ending state is persisted, and a later block seeds from it.

Three decisions fixed in discussion:

- **Semantics = prefix splice.** "Importing `Std`" *means* "this program checks exactly as if `Std`'s chain were textually prefixed to it". The persisted state is a cache of the value that prefix produces. Because `St`/`Val` are strict first-order data in a pure language, the cache is definitionally the same value however it is reached — there is no serializer to distort it, and no fidelity test worth writing unless a *derived* (pruned/pre-normalized) cache is introduced later. The one structural requirement: seeding must mean literally "begin the walk with this `St`", the same code path as mid-program state, not a special entry mode.
- **One input state per block.** `prog` takes exactly one predecessor state, so module composition is a chain by construction. Diamond imports are structurally unrepresentable — no union operation exists, so no collision handling and no refusal logic. Counters thread through the state, so the next block mints σs and seal sites where the last one stopped. Merges are consciously deferred.
- **`fn` is the lemma form.** The signature is the stated type, the body is the proof, and the seal's audit checks the body against the signature at elaboration. Never `let X = (λ … : Π …)` — that is exactly what `fn` already is. This deletes the `X`/`XTy` convention: the type is the signature, written once. Parameters are lowercase where the body matches on them (see the snippet and its boundary note below); the λ/`elim` spelling remains for terms cited inside types.

## Modules are ordinary Lean values

No new namespace, no registry: `prog { … }` elaborates to a plain Lean value carrying the term and the ending state, and a consuming block takes a state value as its one argument. Lean's own `def`s, namespaces, and imports do all the bookkeeping. (Lean has no top-level destructuring `def (a, b) := …`, so the pair is a structure with projections:)

```
structure Checked where
  term : Term
  env  : St
```

No separate provenance field. The knowledge half of provenance — what the checker knew at each binding, the point deltas hover replays — already lives inside `St` (`St.ledgers : Ledgers`), position-free, keyed by binder `Var`s and statement `Term`s. The position half — the `SpanAcc` join table (statement-term key → span) the defining elaboration currently discards — becomes a **fourth channel of `Ledgers`**, which is the record's stated purpose: three diagnostic carries were each taught to cross the seal by hand before the carry was made a unit, and a fourth channel joins by construction. Spans are stored as plain data (`module : String`, offsets as `Nat`s), never `Lean.Syntax`, so the kernel gains no elaborator imports; the machine never reads the channel, which is already licensed by `PointDelta.sctx`'s rendering-only precedent. One consequence to note where it bites: two states can be judgment-equivalent while differing in ledgers, so state-equality assertions should compare the judgment-relevant projection.

## What `StdLemmas.lean` becomes

One block (or a short chain of them), written in the surface, checked as it elaborates:

```
def std : Checked := prog {
  fn LeRefl [n] (n : Nat) -> Le n n {
    match n { Z => unit, S(k) => LeRefl(k) } };

  fn LeTrans [a] (a : Nat, b : Nat, c : Nat, Hab : Le a b, Hbc : Le b c) -> Le a c {
    match a { Z => unit,
      S(a2) => match b { Z => botElim (Le (S a2) c) Hab,
        S(b2) => match c { Z => botElim (Le (S a2) Z) Hbc,
          S(c2) => LeTrans(a2, b2, c2, Hab, Hbc) } } } };

  ()
}
```

Both of these CHECK TODAY (probed 2026-08-21, worktree at the tier-cut branch): the `fn` sugar derives the dependent motive from the signature, the self-call becomes `Ih`, and — the notable part — matching `b` ⇜-refines `Hab`/`Hbc`'s types per arm, so the machine's state does the job CIC needs the convoy pattern for. No motive is written anywhere; compare the current triple-`elim` `LeTrans` with three hand-written motives.

The boundary: match-style lemmas take LOWERCASE (runtime) parameters — the fence refuses `match` on a comptime binder, and a comptime split is `elim` by design. Consumption changes shape but not power for PROOF-producing lemmas: today a lemma is usually an inline spine in a ⇝ position (a carve's evidence slot, a proof argument) reduced by the pure engine; under the `fn` form the consumer calls the lemma and binds the result — an opaque σ at the return type — and cites the binding. That serves identically, because proofs are consumed by TYPE (the slot converts `Le k3 …`, never the proof's body). What genuinely cannot move to `fn`+`match` is anything whose RESULT participates in conversion — the spec functions (`Set`, `Count`, `Len`) and type-level terms (`OptP`) that appear inside types and must ⇝-reduce there. Those are not lemmas and keep the λ/`elim` spelling. Making `match` one construct across both arrows is the standing north star, and this is fresh evidence of its payoff — not part of this plan.

Elaborating this block **is** the check: a body that does not inhabit its signature is a squiggle at the offending syntax, at definition time, like any `prog{}` today. Chaining is function application:

```
def sortLemmas : Checked := prog (std.env) {
  fn CountConsHit (…) -> … { … };
  ()
}
```

## What a consumer looks like

```
def quicksortChain : Checked := prog (sortLemmas.env) {
  fn UseTrans (a : Nat, b : Nat, c : Nat, p : Le a b, q : Le b c) -> Le a c {
    LeTrans(a, b, c, p, q) };
  () }
```

No `open` list, no `%` splice: `LeTrans` resolves against the seed state's comptime environment (checked before the existing Lean-constant fallback, which can then retire). The call is checked against `LeTrans`'s signature exactly as any `fn` call is — the signature the definition site already verified the body against. A no-argument `prog{}` seeds the empty state, so existing programs are the degenerate case.

The one piece of real machinery: `prog (sortLemmas.env) { … }` checks at elaboration time, so the elaborator must obtain the **value** of the seed expression during elaboration — `evalExpr`-style evaluation of a compiled constant, the same machinery `native_decide` and the in-elaborator `checkProgram` already use. Cross-file this is a native call (memoizable per session); same-file it falls back to the interpreter. By purity, evaluate-on-demand is indistinguishable from any cached store.

## Why the mechanism is cheap in Lean

- A Lean elab runs with the full `Environment` of every import — constants all natively evaluable. `def std : Checked := …` is an ordinary constant; the `.olean` persists it structurally (strict first-order data, round-trip is identity), and the consuming elab evaluates it on demand. No environment extension needed — that design is kept in reserve only as a cache if on-demand evaluation ever measures too slow.
- **Info trees** (hover data) are per-file and not persisted. Cross-file hover therefore answers from the ledgers (knowledge + spans) carried inside `env` — the same way Lean shows types and docstrings for imported constants. Hover at a use site of `LeTrans` shows its signature (and can show the defining source, since the defining module elaborated real syntax at real positions in its own file).
- `StdLemmas` already imports `ElabCheck`, so none of this needs a layering change; the library sits above the checker today.

## What this deletes

- The `chkLib` battery in `StdLemmas.lean` and every scattered `chkL` check of library entries — definition-site checking subsumes them.
- The `X`/`XTy` two-defs-per-lemma convention (the signature is the type).
- `defer_check` on the library, the per-use-site `open` lists, and the `%` splices for library terms.
- The identifier-fallback resolution channel for library lemmas (kept only for genuinely Lean-side terms, if any remain).

## Staged work

1. **Stage 0 probe — DONE, viable (2026-08-21).** Every runner already threads the initial `St` as an explicit parameter (`programPaths initSt t`, `explore … initSt`), so seeding is a parameter substitution and the identical-code-path property holds by construction. Measured: a `fn` lemma block run to its final `St` (without the closing `endScope` — bindings must persist), then a hand-built consumer (`let y = LeRefl(2)`) explored from that state, against the one-block splice of the same two pieces. Seeded and spliced agree exactly — `nextSym` continues (4 → 5), `y ↦ σ4` in both. Three findings for stage 1:
   * `Term.numberSeals` restarts at site 0 per program; a seeded block needs a start offset (the seed's site count) or its sites collide with the seed's `sealSites` table keys.
   * Mode must be consistent along a chain: a checking-mode seed with `executing := true` flipped on silently takes the checking path. Decide: a module is interpreted per mode, or seeding pins the mode.
   * The macro-layer call-resolution table (`FnMacro.retarget`'s name → Var × `[k]`-hint binds) does not travel in `St`; stage 2's MVP resolves imported calls by name with no `[k]` hint (restriction: imported `[k]`-hoisted fns not yet callable), and the hint table joins the ledgers alongside spans in stage 3.
   * Producing `Checked.env` needs no `ToExpr St`: the elaborated value is `⟨quoted term, finalStOf seed term⟩` — the state expression re-derives the walk on demand, and purity makes it the value the elab-time check computed. The elab-time check itself runs seeded, for diagnostics.
   * Surface compatibility: `prog { … }` keeps elaborating to `Term` (hundreds of sites); the `Checked` forms are `prog () { … }` (empty seed) and `prog (e) { … }` (seeded).
2. **Stage 1 — DONE (2026-08-21).** The forms are `prog () { … }` (empty seed) and `prog (e) { … }` (seeded), one syntax rule with an optional seed term — `()` is itself a Lean term, so two separate rules would hand the parser an ambiguity. Both elaborate to a `Checked`; the bare `prog{ }` still elaborates to a `Term`, and the full suite building green is the compatibility proof. The machinery lives in `Program.lean` (`Checked`, `moduleBoundary`, `modulePathsD`, `moduleFinalSt`, `Checked.seeded`) and `ElabCheck.elabModule`. Decisions made here:
   * **Seal-site offset: a `nextSite : Nat := 0` counter on `St`**, written only by the boundary pass (`moduleBoundary` numbers a seeded block's seals from `seed.nextSite` and the final state records where it stopped). Chosen over "count the seed's `sealSites` entries" because that table only holds seals that were ⇝-read — a never-cited seal would be uncounted and its site re-issued. The counter also matches the plan's own framing: seal-site numbering is one of the housekeeping counters `St` carries.
   * **Mode is pinned to checking** (`modulePathsD` sets `executing := false`) — a module is interpreted as knowledge; per-mode interpretation is not built.
   * **Persisted states carry empty hover ledgers** (`moduleFinalSt` pins `hover`/`pointHover` off), so the plan's judgment-equivalence caveat is answered by construction until stage 3 deliberately puts spans in: state equality on a persisted `env` means what it says. (Stage-3 correction: flag-pinning alone was not quite that — the seal audit retires one empty path per audited body path unconditionally, so a flag-pinned state still accumulated `[] :: …` residue in `ledgers.paths`. `moduleFinalSt` now rebuilds the persisted ledgers explicitly.)
   * **The emitted value is `Checked.seeded <seed> <term>`** — the state is re-derived by the same pure walk on demand, so no `ToExpr St` exists. Its failure branch is a documented `panic!`: elaboration already rejected any block whose walk fails, so it is reachable only by calling the function directly on a term the surface never accepted.
   * A block that assembles to an OPEN value (a splice of a local) is an elaboration error, not a silent deferral — a `Checked` cannot exist without its ending state. Multi-path blocks are refused for the same reason. Blocks end in `()` like programs (the open cosmetic question, settled by doing nothing).
   * Diagnostics run seeded with the ordinary span table; the negative acceptance test pins a wrong-argument error landing on the offending argument's own syntax.
3. **Stage 2 — DONE (2026-08-21), MVP restriction documented.** The elaborator has the seed's evaluated `St` in hand, so every seed Ω entry goes into the surface's scope by name, newest first — matching Ω's own newest-wins resolution (`findSlot?`), with the block's own binders shadowing imports. A bare mention of an imported declaration resolves to the very `Var` the seed's env entry holds (`⟨declSlot, name⟩`); a call falls through to `.call` and `moduleRetarget` (= `FnMacro.retarget` at `moduleBinds seed`) rewrites it into the same app spine a local `fn`'s call becomes — one shape, one function. The restriction: **the `[k]` hint table does not travel in `St`, so every imported bind carries hint `none` — an imported `[k]`-hoisted fn whose scrutinee is not already parameter 0 is not yet callable.** The case is NOT detectable from the state: the seed holds only the sealed σ and its Π, and a hoisted signature is indistinguishable from one declared in that order, so a mis-ordered call is caught by the argument-type check (when the types differ) rather than by a dedicated error. The hint table joins the ledgers at stage 3. Acceptance battery: `Tests/ModuleStates.lean` — definition-site check, seeded consumer (`y ↦ σ4`, `nextSym` continues), splice agreement, cross-boundary seal-site distinctness, the negative, and a two-module chain whose second lemma cites the first from inside its own `fn` body.
4. **Stage 3 — DONE (2026-08-21).** Two module-boundary channels join `Ledgers` as plain data, written by the ELABORATOR — never a rule; the machine reads neither — and read back only at the next boundary. Both ride the emitted `Checked.seeded <seed> <term> <hints> <spans>` call, because they are exactly the two facts about a block the value-level walk cannot re-derive: the `[k]` hint dies at the macro layer (`fnElab` hoists the scrutinee away, and a hoisted signature is indistinguishable from one declared in that order), the spans at the syntax layer.
   * **`hints : List (String × Nat)`** — declaration name ↦ its `[k]` scrutinee's declaration-order index; only hinted `fn`s have entries. The `fn` row files `(name, index)` into a new UNGATED `SpanAcc.fnHints` (not diagnostic, so behind neither collection flag); `elabModule` keeps the entries whose names survive to the module's ending Ω (dropping body-local declarations); `moduleBinds` reads the seed's channel. An imported call to a hinted fn now gets the same argument permutation a local call gets — the stage-2 restriction is lifted. Acceptance: a `TwoRec`/`Nth`-shaped `fn Walk [n] (v : &mut List Nat, n : Nat)` module and a seeded consumer calling `Walk(&m xs, 2)` in declaration order, green — the types make an unpermuted call impossible there, so acceptance itself witnesses the permutation.
   * **`spans : List SpanNote`** — statement-term key (stored in `stmtKeyOf` normal form, directly joinable against a breadcrumb) with `module : String` and byte offsets, `Lean.Syntax` nowhere. `elabModule` collects its span table with `collect := true` — the one deliberate reversal of "a passing block pays nothing for its spans": for a module the table is carried data, not rejection diagnostics, and module blocks are few — and quotes the entries into the emitted value instead of discarding them.
   * **The carry did its job**: `Ledgers.closePath` reads the seed's entries back out of every `fn` audit, so the channels survive `checkRFnBody` by construction (asserted across a two-module chain). `moduleFinalSt` now persists ledgers as ONLY these two channels, hover-replay channels rebuilt empty (see the stage-1 correction above). Judgment equivalence is therefore "equal up to `hints`/`spans`", and it bites exactly where the plan said it would: state-equality assertions compare judgment-relevant projections — the splice-agreement test already did, and no existing assertion moved.
   * Point-hover and `show` replay for IMPORTED names is deliberately not built here — that is UX on top of the carried data, and the S1 source-truth path is untouched. What falls out for free is the data side: a hinted import is callable, and the span channel gives any future cross-file hover its positions.
5. **Stage 4 — the library port, DONE for the lemma layer (2026-08-21).** All 110 StdLemmas lemma pairs live in `StdChain.lean` as one `prog () { … }` block (`Dllbc.std : Checked`), elaborating in ~34 s with `maxHeartbeats 0 — the measured one-block cost; the block can be cut at any statement boundary and chained if that ever hurts the edit loop. 41 lemmas are native match+recursion rewrites; 69 wrap the original proof term applied to the parameters. The original raw terms are renamed `XRaw` in `StdLemmas.lean` (the shadow guard requires the old constant's name to differ; the corpus's `L`-suffix convention collides for `LeAdd`/`LeAddMono`, hence `Raw`), the `chkLib` battery is deleted (the chain's elaboration subsumes it), and the 16 consumer files' citations were renamed mechanically. `Tests/ModuleStates.lean` consumes the real chain: seeded from `Dllbc.std.env`, citing a native lemma, feeding its result to another, and calling a wrapper lemma.

   The port measured the `fn`-lemma boundary precisely, across ten independent transcription agents:
   * **Consumption discipline decides P1.** `Le`-style lemmas (proofs consumed by type: refinement, botElim) rewrite natively. `Id`-lemmas whose recursive step composes through `j`/`IdCongr`/`IdTrans` cannot: `j` consumes its witness by value, a `fn`'s `Ih` is an opaque existential, and matching `Refl` on it is stuck rigid-rigid. Recursive `Id`-arithmetic stays wrapped under the current kernel.
   * `fnElab` lowers `[k]` recursion to `natRec`/`listRec` only — array-shaped lemmas cannot go native regardless of spelling. Non-recursive matches (Σ-projections) have no scrutinee-type restriction.
   * A named capital Σ binder makes its component comptime, and a comptime arm binder cannot be returned as a runtime result — `Ub`/`Lb` projections stay wrapped while `Sorted`/`Bound`'s anonymous-product cousins go native.
   * A proof premise used more than once per branch must be CAPITAL (a lowercase proof is a linear runtime resource, one read per path), Π-typed or not.
   * An all-comptime `fn` body cannot call a sibling `fn` (a call is ⇒-only; the body is ⇝ throughout); pure application of a raw constant is fine. In mixed bodies, a sibling call cannot nest inside a juxtaposed pure application — bind it with a lowercase `let` first. Self-calls are exempt (they become `Ih`).
   * Known diagnostics gap: this last failure class reports with no span, pointing at the block's first `fn`.
6. **Deferred:** state merges (diamonds stay structurally impossible until a use case forces the question).

## Open questions

- Elaboration cost of the std module is paid once per build of that module — acceptable by the standing wall-clock ruling, but worth measuring once, since it moves library checking from `native_decide` batteries (compiled) to the elaborator's walk.
- ~~Whether library blocks end in `()` like programs or admit a module-shaped tail~~ — settled at stage 1 by doing nothing: blocks end in `()`; a module-shaped tail bought no expressiveness and would be a second block grammar.
- How much of `Std` (the Term-level function library: `Len`, `Count`, …) moves into the chain vs stays kernel-adjacent; the carve rule's kernel copies (`Pure.kAddFn`, `Pure.kLeFn`) stay in the kernel regardless, with the existing twin test pinning them to the surface spellings.

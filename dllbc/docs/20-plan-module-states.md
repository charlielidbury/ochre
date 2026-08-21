# 20 — Module states: threading the checker state across `prog` blocks

Status: plan, agreed in discussion 2026-08-21. Nothing here is built.

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

1. **Stage 0 probe (viability, before anything else):** seed a `prog` walk from a nonempty `St` and confirm it takes the identical code path as mid-program state — the splice-semantics requirement. Verify counters (nextSym, seal sites) continue rather than restart.
2. **Stage 1:** `prog { … }` elaborates to a `Checked` value (term + ending state); `prog (e) { … }` accepts one seed expression, evaluated at elaboration time (`evalExpr` over the compiled constant). No-argument form seeds empty — existing call sites unchanged.
3. **Stage 2:** name resolution in a seeded block consults the seed's comptime environment before the Lean-constant fallback.
4. **Stage 3:** spans join the ledgers: the `SpanAcc` join table (statement-term key → module + offsets, plain data) becomes a fourth `Ledgers` channel written by the elaborator instead of being discarded; point-hover and `show` answer for imported names by the same replay they do locally.
5. **Stage 4:** port `Std`/`StdLemmas` to module blocks written with `fn`; delete the battery, the `Ty` defs, and the splice plumbing. The E2E-rule exemption list drops the battery it briefly named.
6. **Deferred:** state merges (diamonds stay structurally impossible until a use case forces the question).

## Open questions

- Elaboration cost of the std module is paid once per build of that module — acceptable by the standing wall-clock ruling, but worth measuring once, since it moves library checking from `native_decide` batteries (compiled) to the elaborator's walk.
- Whether library blocks end in `()` like programs or admit a module-shaped tail; cosmetic, decide at stage 1.
- How much of `Std` (the Term-level function library: `Len`, `Count`, …) moves into the chain vs stays kernel-adjacent; the carve rule's kernel copies (`Pure.kAddFn`, `Pure.kLeFn`) stay in the kernel regardless, with the existing twin test pinning them to the surface spellings.

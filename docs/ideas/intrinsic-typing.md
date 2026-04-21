# Intrinsic typing: carrying well-typedness with the AST

## Problem

Och has one untyped AST ([`Expr`](../../lean/Och/Syntax.lean#L38)) and
a checker `tyCheck : Expr → Val → Except String Bool` whose output is
just a boolean. Well-typedness of the term the checker consumes is
nowhere represented in Lean's type system — it is a meta-level claim
proven separately in [`Soundness.lean`](../../lean/Och/Soundness.lean).

Closures inside `Val` therefore hold arbitrary unchecked `Expr`s, and
`tyCheck` itself calls `NbE.eval` speculatively on sub-expressions
during `subCheckVal` and `.app` typing, so `eval` has to be total over
potentially-ill-typed inputs. Consequences:

- `eval` returns `Option Val` because "stuck on garbage" and "out of
  fuel" share the same `none`.
- `progress_mod_fuel` (§7.1 of `paper.md`) isn't even stated yet.
- Downstream proofs have to re-derive, from the boolean `tyCheck`
  result, the structural facts they need ("this closure's body is
  well-typed under its env"). That is much of what the ten open
  sorries in [`SoundnessProof.lean`](../../lean/Och/SoundnessProof.lean)
  are reassembling.

What if the well-typedness witness were *data*, threaded through the
pipeline alongside (or instead of) the raw AST?

## 1. The spectrum of options

### (a) Refinement-typed wrapper

Keep `Expr` as-is and add a sidecar:

```lean
structure WellTyped where
  expr : Expr
  τ    : Expr
  h    : typeCheck n expr τ = .ok true
```

Anyone who wants the guarantee consumes `WellTyped`; the rest of Och
keeps using `Expr`. Zero invasion. This is morally the same pattern
implicit in `concEval_preservation` — the theorem takes an `Expr`
plus a hypothesis that it type-checks.

### (b) Indexed inductive AST

A new AST where typing is structural:

```lean
inductive WTExpr : (Γ : Ctx) → (τ : Val) → Type
  | bvar : (k : Fin Γ.length) → WTExpr Γ Γ[k]
  | lam  : WTExpr (Γ.push A) B → WTExpr Γ (.lam A ⟨B,…⟩)
  | app  : WTExpr Γ (.lam A B) → WTExpr Γ A → WTExpr Γ (B.open arg)
  …
```

Each constructor enforces its typing rule in its indices. The checker
outputs a term of this type — there is no boolean. Classic
Agda/Idris-style intrinsic typing.

### (c) Post-hoc extraction

Keep `Expr` and `tyCheck`; after the checker succeeds, produce a
`WTExpr Γ τ` that witnesses the derivation. `forget : WTExpr Γ τ → Expr`
erases indices; `check : Expr → Option (Σ τ, WTExpr [] τ)` promotes.
The two ASTs coexist. In practice this is the realistic migration path
to (b): elaborate `Expr → Bool` into `Expr → Option (WTExpr _ _)` one
constructor at a time.

### Intermediate points

- **Typed closures only.** Keep `Expr`, but index `Closure` by a proof
  that its body type-checks under its env. Catches the specific leak
  of unchecked syntax into `Val` without touching the AST.
- **Well-formed-context wrapper.** Keep `Expr`, but index `Env` by a
  typing context: `eval : (ρ : Env Γ) → Expr → …`. Half-way to (b).
- **Erased indices.** `WTExpr` where indices live in `Prop`, so
  compilation is identical to `Expr` but the checker sees richer types.

## 2. Interaction with Och's machinery

| Question               | (a) Refinement  | (b) Intrinsic                                 | (c) Post-hoc          |
| ---------------------- | --------------- | --------------------------------------------- | --------------------- |
| `Val`/`Closure` change | no              | `Closure` indexed by `(Γ, τ)`; strict-positivity pain | no                    |
| `eval` total           | no (`Option`)   | yes modulo fuel on `WTExpr` input             | yes on `WTExpr` arg   |
| Needs fuel             | yes             | yes (Och has `fix` + `Type : Type`; intrinsic typing ≠ normalization) | yes |
| `quote` target         | `Expr`          | `WTExpr` — but quoting mid-check requires well-typedness invariants to hold of values, not just syntax | `Expr` at boundary |
| `Subtype'`             | unchanged       | relation on `WTExpr Γ τ₁ × WTExpr Γ τ₂`; `[S-Trans]` still a constructor (the size-measure problem is orthogonal) | unchanged |
| Seen-set `S`           | `List (Expr × Expr)` | heterogeneous `Σ Γ τ₁ τ₂, …` pairs — painful | unchanged             |
| Soundness theorems     | mostly unchanged | several become definitionally trivial         | unchanged until extraction added |
| Type-in-type           | no interaction  | `WTExpr Γ τ : Type` needs the index universe consistent; object-level `Type : Type` still lives in one meta universe | no interaction |
| Code change            | ~50 LOC additive | rewrite of `Expr`, `Val`, `Closure`, `eval`, `quote`, `subCheckVal`, `tyCheck`, `Subtype'` | ~200 LOC plus extraction |

The strict-positivity issue for (b) deserves spelling out. Och's
`Val.lam : Val → Closure → Val` with `Closure.env : List Val` currently
works. Indexing `Closure` by a `Ctx` of Lean-level `Val` types puts
`Val` in its own index, forcing a universe split. Och's `Type : Type`
at the object level pushes back. Every textbook intrinsic presentation
(Chapman, McBride) solves this, but none solves it cheaply — you end up
with either induction-recursion (not in Lean 4) or an external
well-formedness predicate that is morally option (a).

`[S-Trans]` deserves a note. §3.1 of `paper.md` keeps it as an
explicit constructor because the four `unfold_*` rules make the
term-size measure *increase*, defeating admissibility by induction on
derivations ([`fb53b4c`](https://github.com/charlielidbury/ochre/commit/fb53b4c)).
Indexing derivations by endpoint types doesn't change that — the
measure problem is orthogonal. `[S-Trans]` survives intact.

## 3. Practical tradeoffs

**Metatheory ergonomics.** The ten remaining sorries in
`SoundnessProof.lean` are mostly *threading* proofs: they move an
`OpenCtx`/`R`/`hRa`/`hRb` hypothesis across lemma boundaries. Under (b)
those threading hypotheses would *be* the AST's indices and propagate
definitionally; several of the `_to_Subtype'` sorries would collapse.
Under (a), the ten sorries are essentially unchanged — a refinement
wrapper doesn't discharge the structural facts `SoundnessProof.lean`
is rebuilding.

**User-facing ergonomics.** Ochre users write surface syntax, which
the `och{…}` macro elaborates to `Expr`. Under (b) the macro would
have to produce `WTExpr Γ τ` directly, which means the elaborator
must know the expected type before parsing, or thread it through.
Top-level untyped `let`s currently desugar without any expected type;
that convenience would break.

**Performance.** `Val.beq` has been carefully tuned (ptrEq fast path;
DNat 300s → 3s in `b055339`). Indexed ASTs are harder to `beq`: two
`WTExpr Γ τ`s at different `τ` aren't even the same Lean type, so
comparison requires `HEq`-style gymnastics and worse code generation.
(c) and (a) preserve today's `Val.beq` verbatim.

**Extensibility.** Ochre will grow surface features not in Och (match,
atoms, unions, eventually mutation). Under (b), each needs a new
`WTExpr` constructor with its own typing-rule indices, constraining
how elaboration can be staged. Under (a), elaboration produces `Expr`
and the refinement wrapper is only applied at trust boundaries.

**Soundness benefit.** Does intrinsic typing give `progress_mod_fuel`
for free? *Partly.* Under (b), `eval` on a `WTExpr Γ τ` is total modulo
fuel because constructor indices guarantee every sub-term is
well-formed; the gaps §7.1 calls out (`eval` on `Type`, on a free
variable at the wrong kind) are ruled out by construction. *However*,
the kinding check `τ : Type` at ascription / `whnfPi` / top-level
`typeCheck` entry still has to be proven — that's a property of `Val`,
not `Expr`, and intrinsic typing at the AST level doesn't automatically
deliver it.

## 4. Recommendation

**Not now, and probably not full (b) ever.** Three reasons.

First, the ten open sorries are a poor match for the sales pitch.
Per [`PROGRESS.md`](../../PROGRESS.md) (`67a202b`, `d97b117`), nine are
engineering plumbing with documented routes; the tenth (`openNf_holds`)
is a statement-precision issue. None vanish under (a); only some vanish
under (b), at the cost of a rewrite that would reset the Phase 2 clock.

Second, Ochre's long-term surface features are a moving target.
Committing to `WTExpr` now fixes the shape of typing rules before we
have evidence they're the right shape. Match, atoms, ownership each
want constructor surgery; on an untyped `Expr` that's cheap, on
`WTExpr` it's a rewrite per feature.

Third, the cheap near-term move gets most of the benefit. A `safeEval`
bundled API at the trust boundary — e.g.

```lean
def safeEval (e τ : Expr) (h : typeCheck n e τ = .ok true)
  : { v : Val // R v e τ }
```

gives callers a proof-carrying entry point *without* restructuring
`Val`/`Closure`/`eval`. That's option (a) scoped to the
`Soundness.lean` boundary: a few hours, no risk. `c8e8b71` and
`d97b117` already hint at this style; the safety statements are there,
just not bundled into a callable API.

**Concrete suggestion.** After the ten sorries land, revisit this with
`progress_mod_fuel` in hand. If that proof turns out to require a lot
of "well-kinded closure" bookkeeping, option (c) becomes attractive —
not as a full rewrite, but as a bridge where extracted `WTExpr`s are
used only in the statements of `progress_mod_fuel` and its lemmas,
leaving the executable pipeline unchanged. (b) should wait until
Ochre's surface language is stable, which is a Phase 3+ question, not
a now question.

## Open questions

- Would (c)'s extraction function need its own soundness proof
  ("extracted `WTExpr` faithfully represents the original `Expr`")?
  If yes, it looks suspiciously like the proofs we already have.
- Does the very-dependent DNat/DBool encoding interact badly with
  indexed ASTs? It already abuses `Type : Type`; intrinsic typing may
  or may not tolerate that.
- Could the closures-only variant (§1 intermediate) be done cheaply
  as a stepping stone, catching the "unchecked body in a `Val`" leak
  without committing to full intrinsic typing? Worth a focused
  prototype if `progress_mod_fuel` turns out to need it.

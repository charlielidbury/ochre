# Subtype-engine collapse refactor

**Status**: planned 2026-04-27. Not started.

Branch: `och-refactor`. Direction confirmed: commit to substitution
eval as the only runtime substrate, collapse the subtype-checking
layers to a single public entry point, sorry the existing soundness
proof (preserving statements for future re-proving on the new
substrate).

## Why

The Lean Och codebase has accumulated layered subtype-checking from
incremental development:

- `subCheckVal` (env-NbE structural engine, the original)
- `typeCheck` (bidirectional fast-path, bolted on for perf)
- `subCheckT` (wrapper: try typeCheck, fall back to subCheck)
- `subCheckSubst` (substitution-based mirror of subCheckVal)
- `EvalSubst.subCheckT` (substitution-based wrapper)
- + Subtype' (declarative spec, proof-only)

That's ~7 algorithmic functions. Two whole stacks (NbE + EvalSubst)
each with three layers (structural / wrapper / typed). The
fast/slow distinction isn't a designed architecture — it's an
optimization that grew sideways.

The substrate decision is now settled: substitution-based eval won
~280× on the Och workload (`docs/ideas/eval-subst-vs-env-benchmark.md`),
and the typed-NbE soundness substrate hit structural walls in passes
14-17 (`docs/ideas/typed-nbe.md` post-mortem). Continuing to maintain
two substrates and a multi-layered API is pure tax.

## Target architecture

One subtype/typing pipeline, structured like Variant B
(`agda/paper-B-pure-eval.md`):

```
<~  →  ~>   →  ⇒        (one-way)
  ↘     ↓
   ⊑   ⊑
   ↓
   ⇒                    (sub-term whnf)
```

Concretely, in Lean Och:

- One **public entry point**: `subCheckT (e : Expr) (τ : Expr) → Outcome Bool`
- One **structural engine** on values (the `⊑` analog), private
- One **type inference** path (the `~>` analog) that calls structural
- One **eval** substrate (substitution-based)

No fast-path / slow-path distinction. Bidirectional dispatch where it
helps becomes a structural feature of `~>`, not a separate layer
above the engine.

## Current state (as of 2026-04-27)

| File | Status | Action |
|---|---|---|
| `EvalSubst.lean` | live, primary | keep, becomes the engine |
| `Eval.lean` (concEval) | live, used in soundness chain | keep |
| `NbE.lean` (env-eval, `Val`/`Closure`/`quote`) | partial-dead | shelve |
| `SubCheckVal.lean` (env-NbE structural) | live but redundant | shelve after migration |
| `TyCheck.lean` (typeCheck) | live, fast-path | refactor into `~>` |
| `TypedNbE.lean` | partial — runtime fast-path live, RC/FL substrate dead | split + shelve dead half |
| `Subtyping.lean` (Subtype' declarative) | proof-only | keep |
| `SoundnessProof.lean` (~6K LOC, 4 sorries) | proof depends on env-NbE | sorry bodies, preserve theorem statements |
| `Soundness.lean` (top-level statements) | thin | adapt statements |
| `SoundnessAudit.lean` | algorithmic pins | migrate to public API |
| `MemoRefs.lean` | dead (0% benefit) | delete |
| `Simple/` | separate project | leave alone |

Branch state: 3 commits on `och-refactor` (lam-lam domB flip, test
pathway cleanup, Bool permissive constructors). Build passes.

## Phased plan

### Phase A — sorry the soundness proof (sequential)

`SoundnessProof.lean` is the largest single file (~6K LOC) and its
proofs reference `NbE.Val` / closures throughout. Rebuilding on the
substitution substrate is a separate research effort.

Steps:
1. For each top-level theorem in `SoundnessProof.lean`, replace the
   body with `sorry` while preserving the statement.
2. Remove or sorry the helper lemmas that won't compile against the
   new state (their statements are also worth preserving as scaffolds
   — anywhere a future re-prover will pick up, the *what to prove*
   should be visible).
3. Same treatment for `TypedNbE.lean`'s soundness substrate (RC,
   subtype_closed_aux, typed_nbe_fundamental_open, etc. — the dead
   half identified earlier). Preserve theorem statements.
4. Update `Soundness.lean`'s top-level statements to phrase them
   against `EvalSubst.subCheckT` rather than `NbE.subCheck` where
   needed.
5. `AxiomCheck.lean`: pare back to whatever survives. The current
   axiom report references RC.* and SubV_*; those will need updating
   or deleting.

**Sequential** because all changes are within the same proof
substrate.

**Gate**: full `lake build` passes with sorries (and only sorries —
no compile errors).

### Phase B — caller migration (parallelizable)

Migrate every caller of `NbE.subCheckT` / `NbE.subCheck` /
`NbE.subCheckVal` to `EvalSubst.subCheckT`.

Files (~15) split into independent slices:

**Slice 1**: `Std/*.lean` — Bool, DBool, DNat, Pair, Sigma, Vec, etc.
Mostly `native_decide` tests with `NbE.subCheckT` calls.

**Slice 2**: Test files — `Tests.lean`, `NbETests.lean`,
`TypedNbETests.lean`, `PropertyTests.lean`. Some pins may need
re-baselining (substitution and env-NbE results aren't always literally
equal — quote shapes differ).

**Slice 3**: Audit & bench — `SoundnessAudit.lean`, `BeqBench.lean`,
`EvalBench.lean`, `PerfProbe.lean`.

Each slice is a separate agent's work. Per slice: substitute calls,
run `lake build` on the slice, fix any pin mismatches.

**Gate**: build passes with all slices migrated.

### Phase C — hide internals (sequential)

In `EvalSubst.lean`:
- Make `subCheckSubst`, `subCheckSubstMatch`, `neutralAscent`,
  `synthNeutral` private (or move to a `Private` namespace).
- Public surface = `subCheckT` only.
- `subCheck` (the Expr-level wrapper) can stay public or become
  internal — decide by usage.

Update `Och.lean` (top-level) exports to expose only the public API.

### Phase D — delete dead modules

After B and C complete:
- Delete `NbE.lean` (~520 LOC).
- Delete the dead half of `TypedNbE.lean` (RC predicate, FL,
  substLvl machinery, ~1500 LOC). Keep the live runtime fast-path
  if any survives in the unified pipeline; otherwise delete the file
  entirely.
- Delete `SubCheckVal.lean` (~650 LOC) — entirely subsumed by
  `EvalSubst.subCheckSubst`.
- Delete `MemoRefs.lean` (already dead per its own docstring; just
  remove from `Och.lean`).
- Drop `Och.NbE` namespace wholesale.

**Gate**: full build is clean; no orphan imports.

### Phase E — audit pin migration (parallel with B)

For each pin in `SoundnessAudit.lean`:
- If the pin checks the *engine* (`subCheckVal`-direct), retarget to
  `subCheckT` (the public API). Replace the result if needed.
- If the pin checks `typeCheck` directly, retarget to `subCheckT`
  (semantic intent over pathway).
- Pins on declarative `Subtype'` stay as proof-side checks.

Some pins may flip values (e.g. anything that depended on `domA`
incompleteness has already been fixed in `978da61`). Re-baseline as
needed and document each.

### Phase F — clean Och.lean exports

Final pass: make sure the top-level surface area matches the design.
Public API should be:

- `Och.Syntax` (Expr inductive)
- `Och.Macro` (the `och{...}` DSL)
- `Och.EvalSubst` exporting `subCheckT`, `concEval`, `whnf` (or
  whatever the chosen names are)
- `Och.Subtyping` (declarative `Subtype'` for proofs)
- `Och.Soundness` (sorry'd theorem statements as future scaffolds)

Everything else internal.

## What to preserve for future re-proving

The user has been clear: this refactor must leave the door open to
re-prove soundness later. Concretely:

1. **Subtype' (declarative spec)** — the proof target. Untouched by
   this refactor. Keep as the source of truth for what soundness
   means.
2. **Top-level theorem statements** in `Soundness.lean` and
   `SoundnessProof.lean` — phrased in terms of the public API and
   the declarative spec. Bodies are `sorry`. The statements
   themselves tell a future prover what to prove.
3. **Eval rules** in `EvalSubst.lean` — clearly defined; their
   structure encodes the operational semantics that any soundness
   theorem will quantify over.
4. **The `docs/ideas/` archive** — `typed-nbe.md`,
   `quote-witness-feasibility.md`, `paper-A-vs-B-review.md`,
   `kernel-conversion-survey.md` — record what didn't work and why.
   Future provers can read this before re-attempting.

What's *gone* that future provers don't have:
- The env-NbE substrate. Future proofs build on substitution.
- The RC predicate substrate (passes 14-17 found it structurally
  infeasible at `.neutral` anyway).
- The FL open-environment proof attempt.

Re-proving on substitution may be tractable in ways the env-NbE path
wasn't — closures and quote-witness arguments don't apply, and the
proof shape is different (substitution lemmas vs reducibility
candidates). That's a research direction for a later cycle.

## Parallelization strategy

| Phase | Sequential / Parallel | Estimated cost |
|---|---|---|
| A: sorry soundness | sequential, single file | ~30-60 min |
| B: caller migration | 3 parallel slices | ~30 min wall (parallel), 90 min serial |
| C: hide internals | sequential | ~20 min |
| D: delete dead modules | sequential, after B+C | ~20 min |
| E: audit pin migration | parallel with B | ~20 min |
| F: Och.lean cleanup | sequential | ~10 min |

Wall-clock: ~2 hours with parallelization, ~3-4 hours fully serial.

For B, an agent per slice can work independently because slices
don't share files. They each run `lake build <slice>` and fix
local pin issues. Coordinate via separate commits per slice so the
main branch is always-buildable.

## Risks

- **Test result drift**: substitution and env-NbE produce literally-
  different `Val` / `Expr` results in some cases (quote shapes
  differ). `concEval` results may not match across pipelines for the
  same expression. Tests pinned with `=` rather than via
  `subCheckT` may need re-baselining.
- **Performance regression**: some workloads might be slower under
  substitution. Most are faster (the 280× benchmark), but
  edge cases exist. Run perf benchmarks (`EvalBench.lean`) after the
  migration.
- **Lost compile-time information**: AxiomCheck.lean currently audits
  ~30 RC.* and SubTV.* declarations. After Phase D, this list shrinks.
  If we want similar audits on the new substrate, those are new
  proofs to write.
- **Deletion mistakes**: 5K+ LOC being deleted in Phase D. Ensure
  tests pass after each removal, not just at the end.

## Open questions

- **Should `concEval` survive?** It's the soundness chain's reference
  evaluator. If the new soundness story uses `evalSubst` directly,
  `concEval` may be redundant. Decide as part of Phase A.
- **What's the fate of `Subtyping.lean`?** The declarative spec
  currently has β/let/asc-conversion rules and the lam-lam push
  domB convention. The fix-unfold rules are coinductive. Aligns with
  paper-B's design — keep as-is.
- **Does typeCheck become its own module?** Once collapsed into the
  pipeline, `~>` (the Och paper-B name for type inference) might be
  worth its own file. Or it stays in `EvalSubst.lean` as part of the
  unified engine. Depends on size after collapse.

## Pointers

- `docs/ideas/eval-subst-vs-env-benchmark.md` — perf data motivating
  substitution as the substrate.
- `docs/ideas/typed-nbe.md` — typed-NbE post-mortem; what shipped vs
  what was promised.
- `docs/ideas/a6-closure-env-filtering.md` — why env-filtering wasn't
  the bottleneck (closes that line of investigation).
- `agda/paper-B-pure-eval.md` — the architectural target we're
  collapsing toward.
- `agda/paper-A-typed-eval.md` — alternative we considered and
  rejected (mutual recursion subCheck ↔ eval).
- `rewrite.md` — broader design-decisions log (not committed; scratch
  artifact in working tree).

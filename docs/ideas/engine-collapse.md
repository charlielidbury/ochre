# Subtype-engine collapse refactor

**Status**: shipped 2026-04-27 (Phases A–F + final API redesign).
See "Final architecture" section at the bottom for the
post-refactor surface and findings.

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

Action vocabulary used below:

- **keep** — file stays as-is or with minor adjustments.
- **sorry-preserve** — file stays; theorem bodies become `sorry`,
  but theorem *statements* are kept verbatim as scaffolds for
  future re-proving.
- **delete** — file removed from the working tree on this branch.
  Git history preserves the contents — a future re-prover can
  `git show` the deleted file or revert specific declarations.
  No "live but unused" middle state; if it's not earning its keep
  in the new pipeline, it goes.

| File | Status | Action |
|---|---|---|
| `EvalSubst.lean` | live, primary | **keep** — becomes the engine |
| `Eval.lean` (concEval) | live, used in soundness chain | **keep** (pending decision in Open Questions) |
| `NbE.lean` (env-eval, `Val`/`Closure`/`quote`) | redundant after substrate decision | **delete** in Phase D |
| `SubCheckVal.lean` (env-NbE structural) | redundant after caller migration | **delete** in Phase D |
| `TyCheck.lean` (typeCheck) | live, fast-path | **keep** — refactor into `~>` |
| `TypedNbE.lean` | partial — runtime fast-path live, RC/FL substrate dead | **split**: keep the runtime fast-path (if it survives the unified pipeline), **delete** the RC/FL proof substrate half |
| `Subtyping.lean` (Subtype' declarative) | proof-only | **keep** |
| `SoundnessProof.lean` (~6K LOC, 4 sorries) | proof depends on env-NbE | **sorry-preserve** (Phase A) |
| `Soundness.lean` (top-level statements) | thin | **sorry-preserve** with statements adapted to public API |
| `SoundnessAudit.lean` | algorithmic pins | **keep**; migrate pins to public API (Phase E) |
| `MemoRefs.lean` | dead (0% benefit, already disabled) | **delete** in Phase D |
| `Simple/` | separate project | **keep**, untouched |

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
   half identified earlier). Note: this half is **deleted** in
   Phase D, not sorry-preserved. The proof attempt was found
   structurally infeasible (passes 14-17); preserving its
   statements is misleading because they refer to RC, which itself
   is being deleted. The honest scaffolds for future re-proving
   live in `Soundness.lean` / `SoundnessProof.lean` (sorry-preserved)
   and the `docs/ideas/typed-nbe.md` retrospective.
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

---

## Final architecture

**Public typing/subtyping API** (`lean/Och/API.lean`):

```lean
namespace Och

structure WTValue where
  private mk ::
  whnf : Expr      -- well-typed value (in WHNF)

def synth (e : Expr) (fuel : Nat := 5000) : Outcome WTValue
def subCheck (a b : WTValue) (fuel : Nat := 5000) : Outcome Bool
def subCheckE (fuel : Nat) (e τ : Expr) : Outcome Bool
  -- = synth e; synth τ; subCheck

end Och
```

The `private mk` is the load-bearing API discipline: callers
*must* go through `synth` to obtain a `WTValue`, so the
structural `subCheck` only ever runs on validated values.

### Validation discipline

The original spec's `synth = tyInfer + evalSubst` plan was found
**structurally compromised**: `TyCheck.tyInfer`, the
bidirectional walk, is incomplete on a significant class of
well-formed Och programs. Empirically: `tyInfer succ_ = .error`,
`tyInfer one_ = .error`, `tyInfer appendVec = .error`. The
incompleteness is the A6-family — when `tyInfer` recurses into a
lambda body and hits a `.app f a` whose head is a level-var with
a function type from `Γ`, the bidirectional `tyCheck a dom` arm
can't structurally close conversion at the fresh-bvar boundary,
even on reflexive identity.

The shipped compromise: `synth` runs `tyInfer` for diagnostics
but **tolerates `.error` outcomes**, falling back to plain
`evalSubst` to produce a WHNF. This rescues valid Std programs
at the cost of accepting two classes of ill-typed inputs the
spec wanted rejected at the boundary:

  - SoundnessAudit A3 `(λn:Nat_. n) Bool` (β-substitutes, WHNF
    happens to be `Bool`).
  - `appendVec_wrong` (deep `appendArrays T n1 n1 arr1 arr2`
    domain mismatch).

Both cases remain caught at the `tyInfer` *internal* level —
the corresponding audit pins now assert `tyInfer.isError =
true` rather than `synth.isOk = false`. Closing the
public-surface boundary is a research task: either complete the
bidirectional rules in `tyInfer` (handle the A6-family
correctly), or change the API to require an expected type
(`synth e τ`, which is the original `typeCheck` rebadged).

### Pin audit

~80 pins reclassified across `Std/*`, `Tests.lean`,
`PropertyTests.lean`, `SoundnessAudit.lean`, `EvalBench.lean`:

| Category | Count | Migration |
|---|---|---|
| Subtype check (positive) | ~50 | `subCheckT N a τ = .ok true` → `Och.subCheckE N a τ = .ok true` |
| Subtype check (negative — both sides well-formed) | ~25 | `subCheckT N a τ = .ok false` → `Och.subCheckE N a τ = .ok false` |
| Ill-typed rejection | 5 | `(typeCheck N e τ).isOk = false` → `(TyCheck.tyInfer N #[] e).isError = true` (asserts internal-level rejection; public-surface hole acknowledged) |
| Numeral-tower fuel bumps | 3 | `succ_`-tower `one_/two_ ⊑ Nat_` needed fuel 200 → 2000–5000 (no fast-path) |
| Numeral-tower bench-only | ~4 | `three_/four_/five_ ⊑ Nat_` removed from compile-time pins; runtime in `EvalBench`'s impossibleCases |
| `appendVec ⊑ ...` | 1 | Was via fast-path; structural-only path doesn't close at fuel 5000; commented out (bench-only) |

### What's preserved for future re-proving

1. **`Subtype'`** (declarative spec, untouched).
2. **Top-level theorem statements** in `Soundness.lean`,
   retargeted to the new API:
   - `synth_sound` (existence of declarative type)
   - `subCheck_sound` (structural sound vs `Subtype'`)
   - `concEval_preservation` (preservation)
   - `soundness` (end-to-end)
   All four are sorry'd scaffolds.
3. **Eval rules** in `EvalSubst.lean` — primary engine.
4. **`docs/ideas/`** archive — `typed-nbe.md`,
   `quote-witness-feasibility.md`, `paper-A-vs-B-review.md`,
   etc. + this document.

### What changed in this final pass (vs Phases A–F)

- **Step 1**: introduced `Och.WTValue` / `Och.synth` /
  `Och.subCheck` / `Och.subCheckE` in `Och/API.lean`. Initial
  attempt (`synth = tyInfer + evalSubst`) failed to validate
  most Std; settled on `tyInfer best-effort + evalSubst`.
- **Step 2**: deleted `SubstEval.subCheckT`,
  `Och.FastPathBench`. Made `TyCheck.{whnfPi, typeCheck}`
  private.
- **Step 3**: migrated ~80 pins. Several "ill-typed rejection"
  pins now assert `tyInfer.isError` at the internal level
  rather than `synth.isOk = false`; surfaces the
  public-surface gap.
- **Step 4**: `Och.lean` exports updated to point at the new
  API.

### LOC delta

Approximate (post-refactor vs Phase F head `3120592`):

  - `Och/API.lean` +200 (new file)
  - `Och/FastPathBench.lean` -200 (deleted)
  - `Och/TyCheck.lean` -25 (subCheckT removed)
  - Pin migration across ~20 files: net ~0
  - `lakefile.lean` -3 (fastpath_bench exe removed)

Net: ~0 LOC. The refactor is structural — same code,
re-routed.

### Compromised assumptions surfaced

1. **`tyInfer` is not complete** on Std (succ_, mkVec,
   appendVec, ...). The user's expected-type-free synthesis
   API needs either bidirectional-completeness work or an
   expected-type parameter.
2. **The structural `subCheck`-only path is slower** than the
   former `subCheckT` (which used `typeCheck`'s fast-path).
   Higher numerals are now bench-only; concrete `appendVec`
   doesn't close at fuel 5000.
3. **The A3 hole is not closed at the public surface**. The
   `private mk` discipline is a *structural* defense (callers
   must go through `synth`), not a *semantic* one.

A future cycle should either (a) push `tyInfer` to completeness
on Std, or (b) make the public API take an expected type so
the bidirectional walk can use type-guidance. Either restores
the soundness boundary the spec aimed for.

-- Public API
import Och.Syntax
import Och.Macro
import Och.Outcome
import Och.Eval
import Och.EvalSubst
import Och.TyCheck
import Och.API
import Och.Subtyping
import Och.Soundness
import Och.Soundness.EvalSubstLemmas
import Och.Soundness.SubCheckSubstNeutral
import Och.Soundness.SubCheckSubstStructural
import Och.Soundness.SubCheckSubstFallback
import Och.Soundness.SubtypeSteps
import Och.Soundness.SynthProgress
import Och.Soundness.EvalSubstEquiv

-- Tests, audit, std-library, probes
import Och.SoundnessAudit
import Och.Tests
import Och.PropertyTests
import Och.PropertyTestsExtra
import Och.PerfProbe
import Och.Std
import Och.AppendVecPath

/-!
# Och — top-level library root

## Public API (post-engine-collapse refactor)

The user-facing typing/subtyping surface is `Och.API`:

- `Och.WTValue`    — well-typed value (`private mk`, only `synth`
                     can construct)
- `Och.synth`      — produce a `WTValue` from an `Expr` (validates
                     via `tyInfer` best-effort + `evalSubst` to WHNF)
- `Och.subCheck`   — structural `⊑` on already-typed values
- `Och.subCheckE`  — convenience: `synth e; synth τ; subCheck`

Supporting modules:

- `Och.Syntax`     — `Expr` inductive (the core calculus AST)
- `Och.Macro`      — the `och{...}` DSL surface syntax
- `Och.Outcome`    — `Outcome α` (`.ok` / `.outOfFuel` / `.error`)
- `Och.Eval`       — `concEval` (the reference evaluator)
- `Och.Subtyping`  — `Subtype'` (declarative spec, proof target)
- `Och.Soundness`  — top-level theorem statements (sorry-preserved
                     scaffolds for future re-proving)

Internal modules (still imported because nothing has been moved
behind `private`/`namespace Internal`, but not part of the
intended user surface):

- `Och.EvalSubst`  — substitution-based engine: `evalSubst`,
                     structural `subCheck`, level-var primitives.
                     Most everything here is already `private`;
                     `subCheck` and `evalSubst` are the only
                     externally-consumed pieces.
- `Och.TyCheck`    — bidirectional walk (`tyInfer`/`tyCheck`).
                     Only `tyInfer` is referenced externally
                     (from `Och.API.synth` and a handful of
                     `tyInfer.isError` pins in `SoundnessAudit`
                     / `Std/Vec` / `Std/Array` that test the
                     bidirectional rejection at the internal
                     level).

Tests / audit / std-library / probes (built so their
`native_decide` pins and witnesses are verified):

- `Och.SoundnessAudit` — executable witnesses for soundness gaps
- `Och.Tests`          — smoke tests
- `Och.PropertyTests`  — open-Γ / negative / round-trip properties
- `Och.PropertyTestsExtra` — fuel-mono, ctx-mono, idempotence, Bot,
                              synth/subCheck consistency, β agreement
- `Och.PerfProbe`      — perf benchmarks (compile-time pins)
- `Och.Std`            — Std/* aggregator

## Engine-collapse refactor (2026-04-27)

This refactor (`docs/ideas/engine-collapse.md`) collapsed the
multi-layered subtype-checking surface (`subCheckVal` /
`typeCheck` / `subCheckT` / `subCheckSubst`) to a single public
entry: `synth + subCheck`. The structural `SubstEval.subCheck`
remains as the engine; everything above it goes through
`Och.API`. The unsound `subCheckT` OR-wrapper is gone.
-/

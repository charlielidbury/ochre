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

-- Tests, audit, std-library, probes
import Och.SoundnessAudit
import Och.Tests
import Och.PropertyTests
import Och.PerfProbe
import Och.Std

/-!
# Och — top-level library root

Public API:
- `Och.Syntax`     — `Expr` inductive (the core calculus AST)
- `Och.Macro`      — the `och{...}` DSL surface syntax
- `Och.Outcome`    — `Outcome α` (`.ok` / `.outOfFuel` / `.error`)
- `Och.Eval`       — `concEval` (the reference evaluator)
- `Och.EvalSubst`  — substitution-based engine: `evalSubst`,
                     structural `subCheck`, level-var primitives
                     (`freshLevelVar` / `openFreshTop` / `substTop`
                     / `subCheckOpen`) consumed by `TyCheck`
- `Och.TyCheck`    — bidirectional checker (`TyCheck.typeCheck`)
                     plus the typed top-level entry point
                     `SubstEval.subCheckT`
- `Och.Subtyping`  — `Subtype'` (declarative spec, proof target)
- `Och.Soundness`  — top-level theorem statements (sorry-preserved
                     scaffolds for future re-proving)

Tests / audit / std-library / probes (built so their
`native_decide` pins and witnesses are verified):
- `Och.SoundnessAudit` — executable witnesses for soundness gaps
- `Och.Tests`          — smoke tests
- `Och.PropertyTests`  — open-Γ / negative / round-trip properties
- `Och.PerfProbe`      — perf benchmarks (compile-time pins)
- `Och.Std`            — Std/* aggregator
-/

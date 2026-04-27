-- Public API
import Och.Syntax
import Och.Macro
import Och.Outcome
import Och.Eval
import Och.EvalSubst
import Och.TyCheck
import Och.Subtyping
import Och.Soundness

-- Internal substrate (typeCheck fast-path)
import Och.NbE
import Och.SubCheckVal

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
- `Och.EvalSubst`  — `SubstEval.subCheckT` / `subCheck` / `evalSubst`
                     (the production subtype-checking entry point;
                     internals private post-engine-collapse)
- `Och.TyCheck`    — `NbE.typeCheck` (bidirectional fast-path used
                     by `SubstEval.subCheckT`)
- `Och.Subtyping`  — `Subtype'` (declarative spec, proof target)
- `Och.Soundness`  — top-level theorem statements (sorry-preserved
                     scaffolds for future re-proving)

Internal modules (the typeCheck fast-path substrate; not part of
the user-facing API):
- `Och.NbE`        — env-NbE substrate (`Val` / `Closure` / `eval` /
                     `quote`; underlies `NbE.typeCheck`)
- `Och.SubCheckVal` — `subCheckVal` engine (called by `tyCheck`)

Tests / audit / std-library / probes (built so their
`native_decide` pins and witnesses are verified):
- `Och.SoundnessAudit` — executable witnesses for soundness gaps
- `Och.Tests`          — smoke tests
- `Och.PropertyTests`  — open-Γ / negative / quote-RT properties
- `Och.PerfProbe`      — perf benchmarks (compile-time pins)
- `Och.Std`            — Std/* aggregator
-/

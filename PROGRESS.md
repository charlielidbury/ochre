# Och — current state

## What Och is

Och is a minimal pure calculus isolating the core semantic idea of Ochre
(a systems theorem prover, roughly Rust + Dependent Types). Terms and types
share a single syntax. Types are "approximate programs." The ONLY difference
between compile-time and runtime is the ascription case: `(e : τ)` takes `e`
concretely and `τ` abstractly.

See `docs/what-is-och.md` for details and `docs/ideas/merge-fix-iota.md` for
the mu design.

## Build status

`lake build` passes. **3 sorrys** — all in Soundness.lean:

- `soundness` — the main theorem (VCompat-based, to be proved)
- `VCompat.adequacy` — VCompat respects subCheckNF
- `VCompat.mono` — downward closure

**All milestone tests pass** (M1-M4 including abstract appendVec).
**11 WellTyped witness tests pass.**

## File structure

- `Syntax.lean` — Expr type (de Bruijn indices), substitution, shifting
- `Eval.lean` — absEval, concEval, concEvalE, fuel monotonicity lemmas
- `Subtyping.lean` — subCheckNF (algorithmic), SubtypeCore/Subtype' (declarative)
- `Soundness.lean` — WellTyped, VCompat definition, soundness theorem
- `Tests.lean` — sacred acceptance tests (DO NOT WEAKEN)

## What's been tried (and failed)

Previous agents spent significant effort on a **structural** soundness proof
using SoundRel (a relation requiring matching top-level constructors). This
approach is **fundamentally broken**: ascription `(e : τ)` produces results
with different constructors (e.g., a lam value vs a mu type), so no
structural relation can bridge them.

The git history on `main` documents this extensively. Key lessons:
- SoundRel.subst_congr works but SoundRel can't cross constructor boundaries
- ValSub.subst_congr is FALSE (verified by native_decide counterexample)
- OutputRel (SoundRel + subCheckNF) was a patch that didn't fix the root cause
- The app case needs to handle cross-constructor function results (lam×mu etc.)

**Do not attempt structural relations for soundness.** Use VCompat (logical
relations / semantic compatibility) as described in SUGGESTIONS.md.

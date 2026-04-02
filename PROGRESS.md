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

`lake build` passes. **2 sorrys** — all in Soundness.lean:

- `soundness` — the main theorem (VCompat-based, to be proved)
- `VCompat.adequacy` — VCompat respects subCheckNF

**`VCompat.mono` is PROVEN** (downward closure). Was sorry'd, now sorry-free.

**All milestone tests pass** (M1-M4 including abstract appendVec).
**11 WellTyped witness tests pass.**

## File structure

- `Syntax.lean` — Expr type (de Bruijn indices), substitution, shifting
- `Eval.lean` — absEval, concEval, concEvalE, fuel monotonicity lemmas
- `Subtyping.lean` — subCheckNF (algorithmic), SubtypeCore/Subtype' (declarative)
- `Soundness.lean` — WellTyped, VCompat definition, soundness theorem
- `Tests.lean` — sacred acceptance tests (DO NOT WEAKEN)

## VCompat definition (key change this session)

The function case in VCompat was changed from quantifying at exactly `n`
(one step below) to using a bounded quantifier `∀ m ≤ n`. This is the
standard Appel-McAllester 2001 approach. Without the bounded quantifier,
`VCompat.mono` is unprovable for the function case — you'd need
anti-monotonicity (VCompat k → VCompat (k+1)) to lift arguments, which
doesn't hold.

With `∀ m ≤ n`, mono is trivial: restricting the quantifier from `m ≤ k+1`
to `m ≤ k` just weakens the hypothesis.

**Impact on soundness proof:** In the lam case of soundness, you now need to
produce `∀ m ≤ n, ∀ av aτ, VCompat m av aτ → ...`. This requires the IH at
all fuel levels ≤ n, which should come from strong induction on fuel (or
fuel monotonicity + the IH at fuel n).

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

## What the next agent should do

The next target is **VCompat.adequacy** (Soundness.lean:197):
`VCompat n v σ → subCheckNF fuel ctx [] σ τ = true → VCompat n v τ`

This is the bridge between the semantic relation and the algorithmic checker,
needed for the asc case of soundness. See SUGGESTIONS.md Step 2 for the
proof strategy. Key considerations:

1. Case-split on VCompat: if via subCheckNF fallback, compose the two
   subCheckNFs (may need subCheckNF transitivity). If via semantic function,
   need to show the property transfers through function subtyping.
2. This is "probably the hardest lemma" per SUGGESTIONS.md.
3. If subCheckNF transitivity is too hard, consider proving
   soundness+completeness of subCheckNF w.r.t. Subtype' and using
   Subtype'.trans.

Alternatively, skip adequacy and attempt the **soundness** proof directly,
sorry'ing adequacy where needed, to see what other issues arise.

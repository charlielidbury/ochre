# Extend Och gradually until it's ready

## Prove soundness of concEvalC (closure-based evaluator)

`concEvalC` (closure-based concrete evaluator, Closure.lean) correctly handles
concrete recursive fix with thunked branches AND captures definition-site envs
for correct higher-order behavior. Its soundness theorem is stated but sorry'd.

**Why it's promising:** The lam case of soundness reduces to MONOTONICITY (same
body, related envs) rather than the impossible `absEval_normalize_stable` that
blocked the concEvalS approach. Readback normalizes the closure's body using
absEval in the captured env, producing the same structure as absEval's output.

**The remaining gap:** `absEval_mono` uses `Subtype'` (single step) in `EnvSub`,
but the IH from the asc case gives `SubtypeTrans` (transitive closure). Options:

1. **Prove `absEval_mono_env_trans`** — monotonicity with `SubtypeTrans` envs.
   Follows the same induction as `absEval_mono`. The var case directly uses
   SubtypeTrans from the env. Other cases lift Subtype' to SubtypeTrans.step.
   **Challenge:** the app-beta case needs the SAME expression on both sides, but
   SubtypeTrans.lam_target_shape gives different bodies. May need to decompose
   into a chain of Subtype' steps and show absEval succeeds at each intermediate.

2. **Use a CVal-Expr logical relation** — avoid readback entirely. Define CValLR
   that's step-indexed and existentially quantifies the definition-site env.
   **Challenge:** need to show that the existential Γ_clo matches the Γ_current
   from the app case. This requires either env extension monotonicity or a
   free-variable analysis of normalized bodies.

3. **Prove fuel completeness** — if Subtype' e₂ e₁ and absEval k Γ e₂ succeeds,
   then absEval k Γ e₁ also succeeds. This would allow decomposing SubtypeTrans
   envs into chains of Subtype' steps. The proof follows absEval's structure.

**Estimated effort:** 100-200 lines for the generalized monotonicity, then ~100
lines to fill in soundnessC using the same structure as Soundness.lean.

**Note:** The concEvalS approach (SoundnessS.lean, 7 sorry's) is STALLED — the
bridge theorem `absEval_normalize_stable` is provably FALSE. The closure-based
approach supersedes it.

## North Star: abstract appendVec

The medium-term research goal is getting `appendVec` from docs/add-fix.md working
end-to-end, including with **abstract** arguments (`n : Nat, m : Nat`). Och is
useless without this — a type system that can only verify concrete computations
adds nothing over an evaluator.

Concrete appendVec (fixed n and m) should work once concEval stops normalizing
under binders (see above). Test this first as a sanity check.

For abstract appendVec, the abstract evaluator needs to handle branches where
the result type depends on which branch is taken. Currently `isZero n` for
abstract `n : Nat` correctly evaluates to `Bool` (by applying the type `Nat`
through the elimination chain). But the result of the *outer* branching
(e.g., `(isZero n) ResultType base_case recursive_case`) just gets `ResultType`
— it doesn't know that `base_case` returns `Array 0 T` and `recursive_case`
returns `Array (succ k) T`. Getting branch-precise abstract results may require
partitioning or a similar mechanism, but this is a research question, not a
known-needed feature.

## Extension roadmap

1. **Prove concEvalS soundness** — the urgent next step above.

2. **More concrete recursive fix tests** — now that concEvalS works, add tests
   for `pred`, `mapArray`, `appendArrays` with thunked branches. These exercise
   the evaluator more deeply and may reveal edge cases.

3. **Investigate abstract branching precision** — determine whether the current
   abstract evaluator (which gives `isZero n : Bool` for abstract `n`) is
   sufficient for typing recursive functions, or whether partitioning/narrowing
   is needed. This is research.

4. docs/add-cps.md — should be done eventually, but high risk and might make
   everything very messy.

5. docs/add-implicits.md — should be done eventually, but not if it adds
   unnecessary noise to the underlying theory.

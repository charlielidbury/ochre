# Extend Och gradually until it's ready

## Prove soundness of concEvalS

`concEvalS` (substitution-based concrete evaluator, Eval.lean) correctly handles
concrete recursive fix with thunked branches. But it has no soundness proof.

**Why it's hard:** `concEvalS` uses substitution; `absEval` uses environments.
The current soundness proof relies on both evaluators processing the SAME body
expression in different envs. With substitution, the concrete side evaluates
`body.subst x v` while the abstract side evaluates `body` in `(x,τ)::Γ`.
These are structurally incompatible for a simple inductive proof.

**Recommended approach: Logical relations.**
Define `Sound : Nat → Expr → Expr → Prop`:
- For non-lambdas: `SubtypeTrans v τ`
- For lambdas: when applied to Sound arguments, the results are Sound

This decouples the lam case (no body comparison) and handles the structural
mismatch at application sites. The proof would be by strong induction on fuel.

**Estimated effort:** 200-300 lines. The relation definition + app case is the
core work. Var, type, asc cases are straightforward. Fix case reuses the existing
typing axiom approach.

**Alternative: Unify the evaluators.** Instead of proving concEvalS sound
separately, restructure the main soundness proof to work with a single
substitution-based evaluator. This would make concEvalS the primary evaluator
and eliminate concEval. But it requires changing absEval to substitution too
(losing the "same body" property that makes monotonicity easy).

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

# Extend Och gradually until it's ready

## Prove soundness of concEvalC (closure-based evaluator)

`concEvalC` (closure-based concrete evaluator, Closure.lean) correctly handles
concrete recursive fix with thunked branches AND captures definition-site envs
for correct higher-order behavior. Its soundness theorem is stated but sorry'd.

**What's been done:** `absEval_mono_trans` is PROVED (0 sorry, Monotonicity.lean).
This handles SubtypeTrans on both expressions and environments, producing
SubtypeTrans results. It was the key identified blocker.

**What remains:** The readback-based approach to soundnessC has two deeper
problems that absEval_mono_trans alone doesn't solve:

1. **Readback may fail.** readback normalizes closures via absEval in the readback
   env. Proving absEval succeeds there needs `absEval_succeeds_envsub`, which is
   blocked: in the app-beta case, different envs produce different normalized
   bodies, and the completeness IH (same expression) doesn't handle different bodies.

2. **App-beta: different bodies in different envs.** After evaluating `f`,
   concEvalC has `clo x dom body γ_c` (original body in captured env) while
   absEval has `lam x dom body_a` (normalized body in current env). The
   function IH gives readback(closure) ⊑ abstract lambda, but does NOT give
   CEnvConsistent between the captured env and the abstract env.

**Recommended approach: Kripke-style logical relation (VR)**

Replace readback-based soundnessC with a step-indexed logical relation:

```
VR : Nat → CVal → Expr → Prop
VR n .type .type = True
VR n (.clo x dom body γ_c) (.lam x dom body_a) =
  ∀ k < n, ∀ v_a τ_a, VR k v_a τ_a →
    ∀ v_res τ_res, concEvalC k ((x, v_a) :: γ_c) body = some v_res →
    absEval k ((x, τ_a) :: Γ_a) body_a = some τ_res → VR k v_res τ_res
ER n γ Γ = ∀ x, γ(x) and Γ(x) satisfy VR n
```

**Why this works:**
- **Lam case:** Construct VR directly — the closure satisfies VR because applying
  it to any VR-consistent argument gives VR-consistent results (by the IH at lower
  fuel).
- **App-beta case:** Extract VR from the function result, apply it to the argument.
  No readback needed. The captured env is handled implicitly by VR's closure case.
- **Asc case:** Chain IH with well-typedness (needs absEval_mono_trans, PROVED).

**Challenge:** VR for closures needs to quantify over an abstract env Γ_a for
the body_a evaluation. This Γ_a should come from the function's construction
context. The VR definition must capture Γ_a existentially or carry it as a
parameter. Step-indexing by fuel avoids circularity.

Then readback + SubtypeTrans follows as a corollary of VR.

**Estimated effort:** ~200 lines for VR definition + fundamental theorem,
~50 lines for the readback corollary.

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

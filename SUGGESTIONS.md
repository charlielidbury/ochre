# Proving Och sound via logical relations

## The goal

Prove: for well-typed closed programs, the concrete value is compatible
with the abstract type.

```lean
theorem soundness
    (fuel : Nat) (e : Expr) (v τ : Expr)
    (h_wt : WellTyped fuel [] e = true)
    (h_conc : concEvalE fuel [] e = some v)
    (h_abs : absEval fuel [] e = some τ)
    : VCompat fuel v τ
```

## Why logical relations?

Och's ascription `(e : τ)` evaluates `term` concretely and `ty` abstractly.
The results can have **completely different constructors** — a lambda value
vs a mu type, for instance. This is the whole point of ascription.

Previous agents tried structural relations (SoundRel, SubtypeCore) that
require matching top-level constructors. These are **fundamentally broken**
for any program with ascription. See PROGRESS.md for the history.

The standard PL solution: **logical relations**. Define compatibility
semantically, by behavior. For functions: "compatible iff applying to
compatible args gives compatible results." This avoids the need for
substitution congruence (which is FALSE for contravariant subtyping) and
handles cross-constructor cases (lam compat mu) via unfolding.

## VCompat — the compatibility relation

Defined in `Soundness.lean`. Step-indexed (Appel & McAllester 2001 style):

```
VCompat 0 v τ := True                    -- no budget: trivially compatible
VCompat (n+1) v τ :=
    τ = .type                             -- top
  ∨ v = τ                                -- refl
  ∨ (both lam, semantic function compat)  -- THE KEY CASE
  ∨ (τ = mu, unfold right, VCompat n)    -- equi-recursive right
  ∨ (v = mu, unfold left, VCompat n)     -- equi-recursive left
  ∨ (subCheckNF v τ)                     -- algorithmic fallback
```

The semantic function case: `v = lam domV bodyV`, `τ = lam domT bodyT`, and
for all `VCompat n av aτ`, evaluating `bodyV[av]` and `bodyT[aτ]` gives
`VCompat n rv rτ`.

**The definition may need refinement** as proofs develop. The current version
is a well-informed sketch. Specific open questions:

1. **Env threading:** The current definition uses `concEvalE [] ...` (empty env).
   For the lam case of soundness (normalizing under binders), we may need
   `VCompat` to be parameterized by envs. Or maybe the empty-env version is
   fine because the IH provides what we need.

2. **The subCheckNF fallback:** This is a catch-all that lets VCompat handle
   neutral terms, stuck applications, etc. without structural decomposition.
   It might be too strong (making VCompat trivially true for anything
   subCheckNF can handle) or it might be exactly right. The proof will tell.

3. **Mu unfolding direction:** Currently both left and right unfold. This
   matches equi-recursive subtyping. The step-index decrease prevents
   infinite unfolding.

## Proof strategy

### Step 1: Prove `VCompat.mono` (downward closure)

`VCompat (n+1) v τ → VCompat n v τ`

Standard for step-indexed relations. Prove by induction on `n`, case-splitting
on the VCompat disjuncts. The semantic function case needs fuel monotonicity
(already proved in Eval.lean) to bridge `concEvalE n` vs `concEvalE (n+1)`.

This is mechanical and should go through. If it doesn't, the VCompat
definition needs adjustment (e.g., the subCheckNF fallback might interfere).

### Step 2: Prove `VCompat.adequacy`

`VCompat n v σ → subCheckNF σ τ = true → VCompat n v τ`

This is the bridge between the semantic relation and the algorithmic checker.
Needed for the asc case of soundness.

**This is probably the hardest lemma.** It says: if `v` is compatible with
`σ`, and `σ ⊑ τ` algorithmically, then `v` is compatible with `τ`.

Approach: case-split on VCompat, then on the subCheckNF derivation.
- If VCompat via subCheckNF fallback: compose the two subCheckNFs
  (needs subCheckNF transitivity, which is standard but non-trivial)
- If VCompat via semantic function: need to show the semantic property
  transfers through subCheckNF's function subtyping (contra domain,
  cov body)
- If VCompat via mu unfold: the subCheckNF may also unfold the mu

This lemma may require proving subCheckNF transitivity as a sub-lemma.
If that's too hard, consider proving soundness+completeness of subCheckNF
w.r.t. Subtype' and using Subtype'.trans.

### Step 3: Prove `soundness`

By induction on fuel, case-split on the expression:

- **bvar:** Both evaluators look up the env. With empty env, this is
  vacuous (no free vars in closed programs).

- **type:** Both return .type. VCompat by refl.

- **lam:** Both evaluators normalize the body under a binder (extend env
  with bvar 0). Need to produce semantic function compatibility: for all
  compatible args, evaluating both bodies gives compatible results. This
  is the IH applied to the body with the arg added to the env.

  **Subtlety:** The evaluators extend the env with `bvar 0` for body
  normalization. When the lambda is later applied, they substitute the
  arg into the NORMALIZED body. The IH relates the normalized bodies.
  The semantic quantifier then relates the post-substitution evaluations.

- **mu:** Both evaluators normalize the body with the mu value in the env.
  Return mu with normalized body. VCompat by mu unfolding + IH on body.

- **app:** Both evaluators evaluate f and a, then case-split on f's shape.
  IH gives VCompat for f and a. **This is where logical relations shine:**
  if f_v and f_τ are both lam, use the semantic function compatibility
  (instantiate with the arg). If one is lam and the other is mu, use mu
  unfolding first, then the function case. The VCompat definition handles
  all combinations.

- **asc:** concEvalE evaluates term, absEval evaluates ty. IH on term gives
  VCompat v σ (where σ = absEval(term)). WellTyped gives subCheckNF σ τ.
  Apply VCompat.adequacy to compose them. **This is the crux — adequacy
  bridges the semantic and algorithmic worlds.**

- **top:** absEval returns .type. VCompat by top case. Trivial.

### Step 4 (optional): Bridge to concEval

The soundness theorem uses `concEvalE` (env-based). For the real runtime
(`concEval`, substitution-based), prove:
`concEval fuel e = v → concEvalE fuel [] e = v'` with some relationship
between v and v'. This is a separate concern from the main soundness proof.

## Critical constraints (unchanged)

- **Tests are sacred.** DO NOT WEAKEN. `lake build` must pass.
- **Sorry freely, compile always.**
- **Never weaken preconditions without a witness test.** If you change
  WellTyped, verify satisfiability with `native_decide`.
- **The VCompat definition is a sketch.** If a proof doesn't go through,
  consider whether VCompat needs refinement before forcing the proof.
  Getting the definition right is more valuable than proving things about
  a wrong definition.

## What NOT to do

- **Do not use SoundRel or any structural same-constructor relation.**
  This approach is fundamentally broken for ascription. See PROGRESS.md.
- **Do not attempt ValSub.subst_congr.** It is FALSE (verified by
  native_decide counterexample, preserved in git history on main).
- **Do not re-add ValSub.lean or Monotonicity.lean.** These were part of
  the old approach and were deliberately removed.
- **Do not try to prove soundness by relating evaluator outputs
  structurally.** Use VCompat (behavioral/semantic compatibility).

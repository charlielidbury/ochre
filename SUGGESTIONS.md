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

1. **concEval vs concEvalE:** The definition currently uses `concEval`
   (the real substitution-based runtime). **Try this first.** If it doesn't
   work (e.g., the lam case is too hard because concEval doesn't normalize
   under binders), fall back to `concEvalE` (env-based, normalizes under
   binders like absEval). Using concEval directly avoids needing a bridge
   theorem between the two evaluators.

2. **Env threading:** The current definition uses empty envs.
   For the lam case of soundness (normalizing under binders), we may need
   `VCompat` to be parameterized by envs. Or maybe the empty-env version is
   fine because the IH provides what we need.

3. **The subCheckNF fallback:** This is a catch-all that lets VCompat handle
   neutral terms, stuck applications, etc. without structural decomposition.
   It might be too strong (making VCompat trivially true for anything
   subCheckNF can handle) or it might be exactly right. The proof will tell.

4. **Mu unfolding direction:** Currently both left and right unfold. This
   matches equi-recursive subtyping. The step-index decrease prevents
   infinite unfolding.

## Proof strategy

### Step 1: ✅ DONE — `VCompat.mono` (downward closure)

`VCompat (n+1) v τ → VCompat n v τ`

**Proven.** Required changing the VCompat function case from `∀ av aτ,
VCompat n av aτ → ...` to the standard Appel-McAllester bounded quantifier
`∀ m, m ≤ n → ∀ av aτ, VCompat m av aτ → ...`. With this change, the
function case of mono is trivial (restrict quantifier from m ≤ k+1 to m ≤ k).

### Step 2: Prove `soundness_gen` app case (application congruence)

**This is the hardest remaining step.** The IH gives VCompat for the
evaluated function (structural lam: VCompat for bodies) and VCompat for
the arg. The evaluators then substitute the arg into the body and
re-evaluate. But the two bodies are DIFFERENT (normalized by different
evaluators) and the two args are DIFFERENT (concrete vs abstract).

The soundness_gen IH needs the SAME source expression on both sides.
But after beta-reduction, we have bodyV.subst 0 a_v ≠ bodyT.subst 0 a_τ.

**Approaches to consider:**
1. **Env-substitution equivalence:** Show that evaluating (normalized body
   with arg substituted) equals evaluating (source body with arg in env).
   Then apply soundness_gen's IH to the source body.
2. **Separate congruence lemma by induction on VCompat or expressions.**
3. **Reformulate with related envs** (env_v, env_τ with EnvCompat). The
   standard LR approach, but requires more infrastructure.
4. **Use subCheckNF fallback** if evaluation outputs happen to be related.

See PROGRESS.md for detailed analysis.

### Step 3: Prove `VCompat.adequacy`

`VCompat n v σ → subCheckNF fuel ctx [] σ τ = true → VCompat n v τ`

**This is the critical next step.** The asc case of soundness_gen already
uses it (via sorry). Once proven, the asc case becomes sorry-free.

**Proof strategy:** By induction on n.
- n = 0: VCompat 0 = True, trivially true.
- n + 1: Case split on VCompat (n+1) v σ:
  - σ = .type: subCheckNF .type τ implies τ = .type, VCompat via top.
  - v = σ: use subCheckNF fallback directly.
  - structural lam: IH on bodies (subCheckNF decomposes structurally).
    The relaxed domain matching in VCompat makes this work even when
    subCheckNF changes the domain via contravariance.
  - structural mu: similar to lam.
  - mu unfold: harder — interacts with subCheckNF's `seen` list for
    coinductive termination. May need a generalized version with
    arbitrary `seen` and a coinductive hypothesis.
  - subCheckNF fallback: compose two subCheckNFs (needs transitivity).

**Sub-lemma needed:** subCheckNF transitivity. This is a well-defined
property of the algorithmic checker and should be provable.

### ✅ DONE — `soundness_gen` asc case

Proven using VCompat.adequacy (which is sorry'd). The key insight was
decoupling the VCompat step index `n` from the evaluation fuel. With
the decoupled approach, the IH gives VCompat at ANY step level, so
adequacy (same-level n) applies without step-index mismatch.

### Step 4: Bridge concEval → concEvalE

For the top-level `soundness` theorem. Prove that concEval and concEvalE
agree on closed terms (possibly up to VCompat).

### ✅ DONE — `soundness_gen` bvar, type, lam, mu cases

All proved via structural VCompat + IH. The lam and mu cases are direct
because both evaluators process the same source body in the same env.

### ✅ DONE — `VCompat.mono` (downward closure)

Proved. The structural lam/mu cases make mono trivial (apply IH on bodies).

### ✅ DONE — Decoupled step index from fuel

The VCompat step index `n` is now a separate parameter from evaluation
`fuel` in soundness_gen. This was essential: with coupled indices, the
asc case IH gives VCompat at fuel k but needs VCompat at fuel k+1,
and adequacy preserves the step level. With decoupled indices, the IH
gives VCompat at ANY step level, eliminating the mismatch.

### ✅ DONE — VCompat: relaxed domain/annotation matching

Structural lam/mu cases no longer require matching domains/annotations.
This is needed for adequacy: subCheckNF can change domains via
contravariance, so VCompat must accommodate different domains.

## Before you prove ANYTHING: try to disprove it first

This is the most important rule. Previous agents wasted enormous effort
proving theorems that turned out to be FALSE (SoundRel across ascription,
ValSub.subst_congr). A sorry on a false statement is worse than useless —
it gives false confidence and wastes every future agent's time.

**Before attempting any proof, you MUST:**

1. **Think about whether it could be false.** What would a counterexample
   look like? Is there a program where the preconditions hold but the
   conclusion doesn't? Write down your reasoning.

2. **Test concrete cases with `native_decide`.** Pick 2-3 real programs
   from Tests.lean and verify the theorem holds for them. For example,
   if proving `VCompat.adequacy`, test:
   ```lean
   -- Does VCompat hold for (zero : Nat)?
   example : VCompat 20 (absEval 20 [] zero') (absEval 20 [] SelfNat) ... 
   ```
   If you can't even construct a witness for a concrete case, the theorem
   is probably wrong.

3. **Try to construct a native_decide counterexample.** Especially for
   lemmas involving subCheckNF, substitution, or cross-constructor cases.
   A 5-minute counterexample search saves days of stuck proofs.

4. **Only then attempt the proof.** And if you get stuck, go back to
   step 1 — maybe you're stuck because it's false.

**The sign of a productive session is discovering a false theorem statement
and documenting it, NOT adding more sorrys to a stuck proof.**

## Critical constraints

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

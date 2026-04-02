import Och.Syntax
import Och.Eval
import Och.Subtyping

/-!
# Soundness via Logical Relations (VCompat)

## Goal

Prove: for well-typed `e`, `concEvalE(e)` is compatible with `absEval(e)`.

## Why logical relations?

Och's ascription `(term : ty)` evaluates `term` concretely and `ty`
abstractly. The results can have completely different top-level constructors
(e.g., a lambda value vs a mu type). No structural relation (like the old
SoundRel) can bridge this — it's the entire point of ascription.

The standard PL solution: define compatibility **semantically**, by behavior.
For functions: "compatible iff applying to compatible args gives compatible
results." This avoids substitution congruence entirely — the definition of
function compatibility already quantifies over all possible applications.

## Architecture

`VCompat n v τ` — step-indexed value-type compatibility.

- **n = 0:** everything is compatible (no observation budget)
- **τ = .type:** everything is compatible (top type)
- **Both lam:** for all compatible args at any level m ≤ n, evaluating both
  bodies gives compatible results (semantic function compatibility)
- **τ = mu:** unfold the mu, check compatibility with the unfolded body
  (equi-recursive; costs one step)
- **v = mu:** unfold the mu on the value side (costs one step)
- **Fallback:** use subCheckNF (algorithmic subtyping handles remaining cases)

The key theorem:

```
soundness : WellTyped fuel [] e = true →
            concEvalE fuel [] e = some v →
            absEval fuel [] e = some τ →
            VCompat fuel v τ
```

## Key lemmas needed

1. **VCompat respects subCheckNF ("adequacy"):**
   `VCompat n v σ → subCheckNF σ τ = true → VCompat n v τ`
   Needed for the asc case (WellTyped gives subCheckNF, IH gives VCompat).

2. **VCompat downward closure:**
   `VCompat (n+1) v τ → VCompat n v τ`
   Standard for step-indexed relations.

3. **Fuel monotonicity** (already proved in Eval.lean):
   `concEvalE n e = some v → concEvalE (n+1) e = some v`
   Needed to bridge fuel levels in the semantic function case.
-/

open Expr

/-! ## Well-typedness -/

/-- Well-typedness: all ascriptions encountered during evaluation are sound.
    Bool-valued with subCheckNF in the ascription case.

    The env parameter serves double duty: it's the absEval environment AND
    the subCheckNF typing context. -/
def WellTyped (fuel : Nat) (env : Env) (e : Expr) : Bool :=
  match fuel with
  | 0 => true
  | fuel + 1 =>
    match e with
    | .bvar _ => true
    | .lam _dom body => WellTyped fuel (env.extend (.bvar 0)) body
    | .type => true
    | .asc term ty =>
        WellTyped fuel env term && WellTyped fuel env ty &&
        match absEval fuel env term, absEval fuel env ty with
        | some σ, some τ' => subCheckNF fuel env [] σ τ'
        | _, _ => false
    | .mu ann body =>
        WellTyped fuel (env.extend (.mu ann body)) body
    | .app f a =>
        WellTyped fuel env f && WellTyped fuel env a &&
        match absEval fuel env f, absEval fuel env a with
        | some (.lam _dom body), some aVal =>
            WellTyped fuel env (body.subst 0 aVal)
        | some (.mu ann body_mu), some aVal =>
          match ann, body_mu with
          | .lam _dom_ann retBody, .lam _ _ =>
              WellTyped fuel env (retBody.subst 0 aVal)
          | .lam _dom_ann retBody, _ =>
              WellTyped fuel env (retBody.subst 0 aVal)
          | _, .lam _dom_body bodyRes =>
              WellTyped fuel env (bodyRes.subst 0 aVal)
          | _, _ => true
        | _, _ => true

/-! ## VCompat: step-indexed value-type compatibility

This is the logical relation. It defines when a concrete value `v` is
compatible with an abstract type `τ`, given an observation budget `n`.

**Design notes:**

The function case currently uses `concEvalE` (env-based concrete evaluator).
**Try `concEval` (substitution-based) first** — it's the real runtime, and
if the proof works with it directly, no bridge is needed. `concEval` treats
lambdas as values (bodies untouched until applied), while `concEvalE`
normalizes under binders like absEval. The lam case of soundness may be
simpler with `concEval` (just return the lambda as-is) or harder (the
semantic quantifier needs to relate un-normalized bodies). Try it and see.
Fall back to `concEvalE` only if `concEval` doesn't work.

The mu cases unfold one level and decrease the step index. This is the
standard approach for equi-recursive types (Appel & McAllester 2001).

The `subCheckNF` fallback handles cases where structural decomposition
doesn't apply (e.g., neutral terms, stuck applications). This is safe
because subCheckNF is the intended algorithmic subtype checker.

**Open question:** The exact definition below is a SKETCH. It may need
refinement as proofs develop. In particular:
- Should mu unfolding be on left, right, or both?
- Is the subCheckNF fallback the right escape hatch, or should it be
  more restrictive?
- Does the env need to be threaded through (for non-closed terms)?

These questions should be resolved by attempting the proof and seeing
what the induction demands. -/

/-- Step-indexed value-type compatibility.

    `VCompat n v τ` means: value `v` is compatible with type `τ`,
    given `n` steps of observation budget.

    This is defined as a recursive function on `n` (not an inductive),
    following the Appel-McAllester style. -/
def VCompat : Nat → Expr → Expr → Prop
  | 0, _, _ => True
  | n + 1, v, τ =>
    -- Top: everything inhabits Type
    τ = .type
    -- Refl: syntactic equality (optimization)
    ∨ v = τ
    -- Semantic function compatibility (THE KEY CASE):
    -- Both are lambdas, and for all compatible args at ANY level m ≤ n,
    -- application gives compatible results. The bounded quantifier (∀ m ≤ n)
    -- is the standard Appel-McAllester approach — it makes downward closure
    -- (VCompat.mono) trivially provable for the function case.
    -- NOTE: uses concEval (real runtime). If this doesn't work, try concEvalE.
    ∨ (∃ domV bodyV domT bodyT,
        v = .lam domV bodyV ∧ τ = .lam domT bodyT ∧
        (∀ m, m ≤ n → ∀ av aτ, VCompat m av aτ →
           ∀ rv, concEval (m + 1) (bodyV.subst 0 av) = some rv →
           ∀ rτ, absEval (m + 1) [] (bodyT.subst 0 aτ) = some rτ →
           VCompat m rv rτ))
    -- Mu unfolding on the right (self-intro): costs one step
    ∨ (∃ ann body,
        τ = .mu ann body ∧
        VCompat n v (body.subst 0 (.mu ann body)))
    -- Mu unfolding on the left (self-elim): costs one step
    ∨ (∃ ann body,
        v = .mu ann body ∧
        VCompat n (body.subst 0 (.mu ann body)) τ)
    -- Algorithmic fallback: subCheckNF witnesses compatibility
    ∨ (∃ fuel ctx, subCheckNF fuel ctx [] v τ = true)

/-! ## Soundness theorem

The main theorem. Sorry'd — this is what we're working toward. -/

/-- Soundness for the real runtime (concEval).
    Try this first. Fall back to concEvalE version only if needed. -/
theorem soundness
    (fuel : Nat) (e : Expr) (v τ : Expr)
    (h_wt : WellTyped fuel [] e = true)
    (h_conc : concEval fuel e = some v)
    (h_abs : absEval fuel [] e = some τ)
    : VCompat fuel v τ := by
  sorry

/-! ## Key lemmas (all sorry'd — to be proved)

These are the lemmas needed for the soundness proof. They should be
proved in roughly this order. -/

/-- VCompat respects subCheckNF: if v is compatible with σ, and σ ⊑ τ
    by the algorithmic checker, then v is compatible with τ.

    This is the "adequacy" lemma — the bridge between the semantic relation
    (VCompat) and the algorithmic checker (subCheckNF). It's needed for the
    asc case: the IH gives VCompat v σ (from evaluating the term), and
    WellTyped gives subCheckNF σ τ (from the ascription check). -/
theorem VCompat.adequacy {n : Nat} {v σ τ : Expr} {fuel : Nat} {ctx : List Expr}
    (hv : VCompat n v σ) (hcheck : subCheckNF fuel ctx [] σ τ = true)
    : VCompat n v τ := by
  sorry

/-- Downward closure: more observation budget implies less.
    Standard for step-indexed relations. -/
theorem VCompat.mono {n : Nat} {v τ : Expr}
    (h : VCompat (n + 1) v τ) : VCompat n v τ := by
  cases n with
  | zero =>
    -- VCompat 0 v τ = True
    unfold VCompat; trivial
  | succ k =>
    -- h : VCompat (k+2) v τ, goal : VCompat (k+1) v τ
    -- Unfold one level of VCompat in both h and the goal
    unfold VCompat at h ⊢
    rcases h with h_top | h_refl | ⟨domV, bodyV, domT, bodyT, hv, hτ, h_fn⟩ |
                  ⟨ann, body, hτ, h_mu⟩ | ⟨ann, body, hv, h_mu⟩ |
                  ⟨fuel, ctx, h_sub⟩
    -- τ = .type → trivial at any level
    · exact Or.inl h_top
    -- v = τ → trivial at any level
    · exact Or.inr (Or.inl h_refl)
    -- Semantic function: ∀ m ≤ k+1 → ... becomes ∀ m ≤ k → ...
    -- Since m ≤ k implies m ≤ k+1, just restrict the quantifier.
    · exact Or.inr (Or.inr (Or.inl ⟨domV, bodyV, domT, bodyT, hv, hτ,
        fun m hm => h_fn m (Nat.le_succ_of_le hm)⟩))
    -- Mu right: VCompat (k+1) v (body.subst ...) → VCompat k v (body.subst ...) by IH
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨ann, body, hτ, VCompat.mono h_mu⟩)))
    -- Mu left: VCompat (k+1) (body.subst ...) τ → VCompat k (body.subst ...) τ by IH
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨ann, body, hv, VCompat.mono h_mu⟩))))
    -- subCheckNF fallback: no step index, passes through
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨fuel, ctx, h_sub⟩))))

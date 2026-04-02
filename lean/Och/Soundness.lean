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
- **Both lam:** same domain, bodies are compatible (structural)
- **Both mu:** same annotation, bodies are compatible (structural)
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

VCompat uses structural cases (bodies are compatible) rather than semantic
function cases (quantifying over args and evaluating). This is because the
soundness proof's IH gives VCompat for the two evaluators' outputs on the
SAME source body. With a semantic function case, the lam/mu cases are hard
because the bodies diverge (concEval returns source body, absEval normalizes).
With structural cases, the IH directly applies.

The mu-unfolding cases (equi-recursive, costs one step) are kept for
adequacy and the app case. The subCheckNF fallback handles remaining
cases (neutral terms, stuck applications, cross-constructor compatibility). -/

/-- Step-indexed value-type compatibility.

    `VCompat n v τ` means: value `v` is compatible with type `τ`,
    given `n` steps of observation budget.

    This is defined as a recursive function on `n` (not an inductive),
    following the Appel-McAllester style.

    **Design choice: structural function/mu cases.**

    Previous versions used a SEMANTIC function case: "for all compatible
    args, evaluating both bodies gives compatible results." This doesn't
    work well with the soundness IH because the two evaluators (concEvalE
    and absEval) produce different normalized bodies from the same source.
    The IH needs the SAME expression on both sides.

    Instead, we use STRUCTURAL cases: "both are lambdas with compatible
    bodies" (and similarly for mu). The soundness proof's lam/mu cases
    become trivial — the IH on the body (same source expression, same env)
    gives VCompat for the two normalized bodies directly.

    The app case of soundness then needs a separate "application congruence"
    lemma: VCompat bodyV bodyT → VCompat a_v a_τ → compatible results after
    substitution+evaluation. This is harder but more modular.

    The mu-unfolding cases (equi-recursive) are kept for adequacy and the
    app case. The subCheckNF fallback handles everything else. -/
def VCompat : Nat → Expr → Expr → Prop
  | 0, _, _ => True
  | n + 1, v, τ =>
    -- Top: everything inhabits Type
    τ = .type
    -- Refl: syntactic equality (optimization)
    ∨ v = τ
    -- Structural lambda: both are lambdas with the same domain,
    -- and the bodies are compatible at the lower step.
    ∨ (∃ dom bodyV bodyT,
        v = .lam dom bodyV ∧ τ = .lam dom bodyT ∧
        VCompat n bodyV bodyT)
    -- Structural mu: both are mus with the same annotation,
    -- and the bodies are compatible at the lower step.
    ∨ (∃ ann bodyV bodyT,
        v = .mu ann bodyV ∧ τ = .mu ann bodyT ∧
        VCompat n bodyV bodyT)
    -- Mu unfolding on the right (equi-recursive self-intro): costs one step
    ∨ (∃ ann body,
        τ = .mu ann body ∧
        VCompat n v (body.subst 0 (.mu ann body)))
    -- Mu unfolding on the left (equi-recursive self-elim): costs one step
    ∨ (∃ ann body,
        v = .mu ann body ∧
        VCompat n (body.subst 0 (.mu ann body)) τ)
    -- Algorithmic fallback: subCheckNF witnesses compatibility
    ∨ (∃ fuel ctx, subCheckNF fuel ctx [] v τ = true)

/-! ## Soundness theorem

Two forms:
1. `soundness_gen` — uses concEvalE (env-based, normalizes under binders).
   Both evaluators process the SAME source expression in the SAME env,
   so the IH applies directly for bvar/type/lam/mu cases.
2. `soundness` — the top-level theorem using concEval (real runtime).
   Follows from soundness_gen via a concEval→concEvalE bridge (TBD).

The env-based form is the workhorse. The bridge is a separate concern. -/

/-- Generalized soundness with concEvalE.
    Uses the same env for both evaluators. By induction on fuel.
    The lam and mu cases are direct (structural VCompat from IH on body).
    The app case needs "application congruence" (VCompat through eval+subst).
    The asc case needs VCompat.adequacy (VCompat through subCheckNF). -/
theorem soundness_gen
    (fuel : Nat) (env : Env) (e : Expr) (v τ : Expr)
    (h_wt : WellTyped fuel env e = true)
    (h_conc : concEvalE fuel env e = some v)
    (h_abs : absEval fuel env e = some τ)
    : VCompat fuel v τ := by
  cases fuel with
  | zero => simp [concEvalE] at h_conc
  | succ n =>
    cases e with
    | bvar k =>
      -- Both evaluators look up env[k]. Same result → VCompat by refl.
      simp [concEvalE] at h_conc
      simp [absEval] at h_abs
      have : v = τ := by
        have := h_conc.symm.trans h_abs
        exact Option.some.inj this
      subst this
      unfold VCompat; exact Or.inr (Or.inl rfl)
    | type =>
      simp [concEvalE] at h_conc
      simp [absEval] at h_abs
      subst h_conc; subst h_abs
      unfold VCompat; exact Or.inr (Or.inl rfl)
    | lam dom body =>
      -- concEvalE normalizes body: v = lam dom bodyV'
      -- absEval normalizes body: τ = lam dom bodyT'
      -- Both use env.extend (bvar 0). IH on body gives VCompat n bodyV' bodyT'.
      simp only [concEvalE] at h_conc
      simp only [absEval] at h_abs
      -- Extract bodyV' and bodyT' from the match on concEvalE/absEval of body
      match h_cv : concEvalE n (Env.extend env (.bvar 0)) body with
      | none => simp [h_cv] at h_conc
      | some bodyV' =>
        simp [h_cv] at h_conc
        match h_av : absEval n (Env.extend env (.bvar 0)) body with
        | none => simp [h_av] at h_abs
        | some bodyT' =>
          simp [h_av] at h_abs
          -- h_conc : v = .lam dom bodyV', h_abs : τ = .lam dom bodyT'
          subst h_conc; subst h_abs
          -- WellTyped for body under binder
          have h_wt_body : WellTyped n (Env.extend env (.bvar 0)) body = true := by
            simp [WellTyped] at h_wt; exact h_wt
          -- IH on body
          have ih := soundness_gen n (Env.extend env (.bvar 0)) body bodyV' bodyT'
                     h_wt_body h_cv h_av
          -- VCompat (n+1) (lam dom bodyV') (lam dom bodyT') via structural lam
          unfold VCompat
          exact Or.inr (Or.inr (Or.inl ⟨dom, bodyV', bodyT', rfl, rfl, ih⟩))
    | mu ann body =>
      -- concEvalE: v = mu ann bodyV' where bodyV' = concEvalE n env' body
      -- absEval: τ = mu ann bodyT' where bodyT' = absEval n env' body
      -- Both use env.extend (mu ann body). IH on body gives VCompat n bodyV' bodyT'.
      simp only [concEvalE] at h_conc
      simp only [absEval] at h_abs
      match h_cv : concEvalE n (Env.extend env (.mu ann body)) body with
      | none => simp [h_cv] at h_conc
      | some bodyV' =>
        simp [h_cv] at h_conc
        match h_av : absEval n (Env.extend env (.mu ann body)) body with
        | none => simp [h_av] at h_abs
        | some bodyT' =>
          simp [h_av] at h_abs
          subst h_conc; subst h_abs
          have h_wt_body : WellTyped n (Env.extend env (.mu ann body)) body = true := by
            simp [WellTyped] at h_wt; exact h_wt
          have ih := soundness_gen n (Env.extend env (.mu ann body)) body bodyV' bodyT'
                     h_wt_body h_cv h_av
          -- VCompat (n+1) (mu ann bodyV') (mu ann bodyT') via structural mu
          unfold VCompat
          exact Or.inr (Or.inr (Or.inr (Or.inl ⟨ann, bodyV', bodyT', rfl, rfl, ih⟩)))
    | app f a =>
      -- IH on f and a give VCompat for evaluated function and arg.
      -- Need "application congruence": VCompat bodies + VCompat args →
      -- VCompat results after substitution+evaluation.
      sorry
    | asc term ty =>
      -- concEvalE: v = concEvalE n env term
      -- absEval: τ = absEval n env ty
      -- IH on term: VCompat n v (absEval n env term) =: VCompat n v σ
      -- WellTyped: subCheckNF σ τ
      -- Needs VCompat.adequacy to bridge.
      sorry

/-- Soundness for the real runtime (concEval).
    Follows from soundness_gen via a concEval→concEvalE bridge. -/
theorem soundness
    (fuel : Nat) (e : Expr) (v τ : Expr)
    (h_wt : WellTyped fuel [] e = true)
    (h_conc : concEval fuel e = some v)
    (h_abs : absEval fuel [] e = some τ)
    : VCompat fuel v τ := by
  sorry  -- needs concEval → concEvalE bridge

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
    unfold VCompat; trivial
  | succ k =>
    -- h : VCompat (k+2) v τ, goal : VCompat (k+1) v τ
    unfold VCompat at h ⊢
    rcases h with h_top | h_refl |
                  ⟨dom, bodyV, bodyT, hv, hτ, h_body⟩ |
                  ⟨ann, bodyV, bodyT, hv, hτ, h_body⟩ |
                  ⟨ann, body, hτ, h_mu⟩ | ⟨ann, body, hv, h_mu⟩ |
                  ⟨fuel, ctx, h_sub⟩
    -- Top
    · exact Or.inl h_top
    -- Refl
    · exact Or.inr (Or.inl h_refl)
    -- Structural lam: VCompat (k+1) bodyV bodyT → VCompat k bodyV bodyT by IH
    · exact Or.inr (Or.inr (Or.inl ⟨dom, bodyV, bodyT, hv, hτ, VCompat.mono h_body⟩))
    -- Structural mu: VCompat (k+1) bodyV bodyT → VCompat k bodyV bodyT by IH
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨ann, bodyV, bodyT, hv, hτ, VCompat.mono h_body⟩)))
    -- Mu right: VCompat (k+1) v (body.subst ...) → VCompat k by IH
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨ann, body, hτ, VCompat.mono h_mu⟩))))
    -- Mu left: VCompat (k+1) (body.subst ...) τ → VCompat k by IH
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨ann, body, hv, VCompat.mono h_mu⟩)))))
    -- subCheckNF fallback: passes through
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨fuel, ctx, h_sub⟩)))))

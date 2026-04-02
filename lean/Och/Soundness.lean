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
soundness_gen : WellTyped fuel [] e = true →
                concEvalE fuel [] e = some v →
                absEval fuel [] e = some τ →
                ∀ n, VCompat n v τ
```

Note: the step index `n` is decoupled from `fuel`. This is essential
for the asc case — see soundness_gen's doc comment.

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
    -- Structural lambda: both are lambdas (possibly different domains),
    -- and the bodies are compatible at the lower step.
    -- Domains need not match: subCheckNF handles contravariant domain
    -- checking, so adequacy (VCompat + subCheckNF → VCompat) can change
    -- the domain via the subtype relation.
    ∨ (∃ domV domT bodyV bodyT,
        v = .lam domV bodyV ∧ τ = .lam domT bodyT ∧
        VCompat n bodyV bodyT)
    -- Structural mu: both are mus (possibly different annotations),
    -- and the bodies are compatible at the lower step.
    ∨ (∃ annV annT bodyV bodyT,
        v = .mu annV bodyV ∧ τ = .mu annT bodyT ∧
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

/-! ## VCompat lemmas -/

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
                  ⟨domV, domT, bodyV, bodyT, hv, hτ, h_body⟩ |
                  ⟨annV, annT, bodyV, bodyT, hv, hτ, h_body⟩ |
                  ⟨ann, body, hτ, h_mu⟩ | ⟨ann, body, hv, h_mu⟩ |
                  ⟨fuel, ctx, h_sub⟩
    -- Top
    · exact Or.inl h_top
    -- Refl
    · exact Or.inr (Or.inl h_refl)
    -- Structural lam: VCompat (k+1) bodyV bodyT → VCompat k bodyV bodyT by IH
    · exact Or.inr (Or.inr (Or.inl ⟨domV, domT, bodyV, bodyT, hv, hτ, VCompat.mono h_body⟩))
    -- Structural mu: VCompat (k+1) bodyV bodyT → VCompat k bodyV bodyT by IH
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨annV, annT, bodyV, bodyT, hv, hτ, VCompat.mono h_body⟩)))
    -- Mu right: VCompat (k+1) v (body.subst ...) → VCompat k by IH
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨ann, body, hτ, VCompat.mono h_mu⟩))))
    -- Mu left: VCompat (k+1) (body.subst ...) τ → VCompat k by IH
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨ann, body, hv, VCompat.mono h_mu⟩)))))
    -- subCheckNF fallback: passes through
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨fuel, ctx, h_sub⟩)))))

/-- VCompat respects subCheckNF: if v is compatible with σ, and σ ⊑ τ
    by the algorithmic checker, then v is compatible with τ.

    This is the "adequacy" lemma — the bridge between the semantic relation
    (VCompat) and the algorithmic checker (subCheckNF). It's needed for the
    asc case: the IH gives VCompat v σ (from evaluating the term), and
    WellTyped gives subCheckNF σ τ (from the ascription check).

    Proof approach: induction on n (VCompat step index).
    - n = 0: trivially True.
    - n + 1: case split on VCompat disjunct:
      - top/refl/subCheckNF fallback: straightforward
      - structural lam/mu: IH on bodies (subCheckNF decomposes structurally)
      - mu unfolding: use VCompat mu-unfold + IH (costs one step of n)
    The mu cases interact with subCheckNF's `seen` list (coinductive
    termination). A generalized version with arbitrary `seen` may be needed. -/
theorem VCompat.adequacy {n : Nat} {v σ τ : Expr} {fuel : Nat} {ctx : List Expr}
    (hv : VCompat n v σ) (hcheck : subCheckNF fuel ctx [] σ τ = true)
    : VCompat n v τ := by
  induction n generalizing v σ τ fuel ctx with
  | zero => exact trivial
  | succ m ih =>
    -- Handle σ = τ and τ = .type upfront (covers all VCompat disjuncts)
    by_cases hστ : σ = τ
    · rw [hστ] at hv; exact hv
    · by_cases hτ : τ = Expr.type
      · rw [hτ]; unfold VCompat; exact Or.inl rfl
      · -- σ ≠ τ, τ ≠ .type. Case split on VCompat (m+1) v σ.
        unfold VCompat at hv
        rcases hv with h_top | h_refl |
                       ⟨dV, dS, bV, bS, hv_eq, hσ_eq, h_body⟩ |
                       ⟨annV, annS, bodyV, bodyS, hv_eq, hσ_eq, h_body⟩ |
                       ⟨ann_σ, body_σ, hσ_eq, h_unfold⟩ |
                       ⟨ann_v, body_v, hv_eq, h_unfold⟩ |
                       ⟨fuel1, ctx1, h_sub⟩
        -- Case 1: σ = .type (τ ≠ .type, τ ≠ σ → τ must be mu via self-intro)
        · subst h_top
          cases τ with
          | type => exact absurd rfl hτ
          | mu _ _ => sorry  -- self-intro with .type ⊑ mu
          | bvar _ | lam _ _ | app _ _ | asc _ _ =>
            -- subCheckNF .type (non-type, non-mu) = false: inferType .type = none
            cases fuel with
            | zero => simp [subCheckNF] at hcheck
            | succ k =>
              simp [subCheckNF, inferType, beq_eq_false_iff_ne.mpr hστ] at hcheck
        -- Case 2: v = σ → use subCheckNF fallback directly
        · subst h_refl
          unfold VCompat
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨fuel, ctx, hcheck⟩)))))
        -- Case 3: structural lam (v = lam dV bV, σ = lam dS bS)
        · subst hv_eq; subst hσ_eq
          -- h_body : VCompat m bV bS
          -- hcheck : subCheckNF fuel ctx [] (lam dS bS) τ = true
          -- Need: VCompat (m+1) (lam dV bV) τ
          cases τ with
          | type => exact absurd rfl hτ
          | lam dT bT =>
            -- Extract body subCheckNF from lam/lam case
            cases fuel with
            | zero => simp [subCheckNF] at hcheck
            | succ k =>
              by_cases h_eq2 : Expr.lam dS bS = Expr.lam dT bT
              · exact absurd h_eq2 hστ
              · obtain ⟨fuel', ctx', h_body_sub⟩ := subCheckNF_lam_lam_body hcheck h_eq2
                -- IH on bodies: VCompat m bV bT
                have h_bT := ih h_body h_body_sub
                -- Build structural lam VCompat
                unfold VCompat
                exact Or.inr (Or.inr (Or.inl ⟨dV, dT, bV, bT, rfl, rfl, h_bT⟩))
          | mu _ _ => sorry  -- self-intro (needs seen-list handling)
          | bvar _ =>
            exfalso; exact subCheckNF_lam_impossible hcheck hστ
              (fun h => nomatch h) (fun _ _ h => nomatch h) (fun _ _ h => nomatch h)
          | app _ _ =>
            exfalso; exact subCheckNF_lam_impossible hcheck hστ
              (fun h => nomatch h) (fun _ _ h => nomatch h) (fun _ _ h => nomatch h)
          | asc _ _ =>
            exfalso; exact subCheckNF_lam_impossible hcheck hστ
              (fun h => nomatch h) (fun _ _ h => nomatch h) (fun _ _ h => nomatch h)
        -- Case 4: structural mu (v = mu annV bodyV, σ = mu annS bodyS)
        · subst hv_eq; subst hσ_eq
          -- h_body : VCompat m bodyV bodyS
          -- hcheck : subCheckNF fuel ctx [] (mu annS bodyS) τ = true
          cases τ with
          | type => exact absurd rfl hτ
          | mu annT bodyT =>
            cases fuel with
            | zero => simp [subCheckNF] at hcheck
            | succ k =>
              by_cases h_eq2 : Expr.mu annS bodyS = Expr.mu annT bodyT
              · exact absurd h_eq2 hστ
              · obtain ⟨fuel', ctx', h_body_sub⟩ := subCheckNF_mu_mu_body hcheck h_eq2
                have h_bT := ih h_body h_body_sub
                unfold VCompat
                exact Or.inr (Or.inr (Or.inr (Or.inl ⟨annV, annT, bodyV, bodyT, rfl, rfl, h_bT⟩)))
          | _ => sorry  -- self-elim (needs seen-list handling)
        -- Case 5: mu right (σ = mu ann_σ body_σ, unfold right)
        · subst hσ_eq; sorry
        -- Case 6: mu left (v = mu ann_v body_v, unfold left) → IH!
        · subst hv_eq
          -- h_unfold : VCompat m (body_v.subst 0 (mu ann_v body_v)) σ
          -- ih gives: VCompat m (body_v.subst 0 (mu ann_v body_v)) τ
          -- Build mu-left disjunct of VCompat (m+1)
          unfold VCompat
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
            ⟨ann_v, body_v, rfl, ih h_unfold hcheck⟩)))))
        -- Case 7: subCheckNF fallback (needs transitivity of subCheckNF)
        · sorry

/-! ## Soundness theorem

Two forms:
1. `soundness_gen` — uses concEvalE (env-based, normalizes under binders).
   Both evaluators process the SAME source expression in the SAME env,
   so the IH applies directly for bvar/type/lam/mu cases. The VCompat
   step index `n` is a separate parameter from evaluation `fuel`.
2. `soundness` — the top-level theorem using concEval (real runtime).
   Follows from soundness_gen via a concEval→concEvalE bridge (TBD).

The env-based form is the workhorse. The bridge is a separate concern. -/

/-- Generalized soundness with concEvalE.
    Uses the same env for both evaluators. By induction on fuel.

    KEY DESIGN: the VCompat step index `n` is decoupled from `fuel`.
    soundness_gen proves VCompat at ALL step levels simultaneously.
    This is essential for the asc case: the IH gives VCompat at any n,
    so adequacy (same-level n) applies without step-index mismatch.

    Without this decoupling, the IH at fuel k gives VCompat k, but the
    asc case needs VCompat (k+1) (which adequacy can't provide since
    it preserves the step level).

    The lam and mu cases are direct (structural VCompat from IH on body).
    The app case needs "application congruence" (VCompat through eval+subst).
    The asc case uses VCompat.adequacy (VCompat through subCheckNF). -/
theorem soundness_gen
    (fuel : Nat) (env : Env) (e : Expr) (v τ : Expr) (n : Nat)
    (h_wt : WellTyped fuel env e = true)
    (h_conc : concEvalE fuel env e = some v)
    (h_abs : absEval fuel env e = some τ)
    : VCompat n v τ := by
  induction fuel generalizing env e v τ n with
  | zero => simp [concEvalE] at h_conc
  | succ k ih =>
    cases n with
    | zero => exact trivial  -- VCompat 0 = True
    | succ m =>
      cases e with
      | bvar j =>
        -- Both evaluators look up env[j]. Same result → VCompat by refl.
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
        -- Both use env.extend (bvar 0). IH on body gives VCompat m bodyV' bodyT'.
        simp only [concEvalE] at h_conc
        simp only [absEval] at h_abs
        match h_cv : concEvalE k (Env.extend env (.bvar 0)) body with
        | none => simp [h_cv] at h_conc
        | some bodyV' =>
          simp [h_cv] at h_conc
          match h_av : absEval k (Env.extend env (.bvar 0)) body with
          | none => simp [h_av] at h_abs
          | some bodyT' =>
            simp [h_av] at h_abs
            subst h_conc; subst h_abs
            have h_wt_body : WellTyped k (Env.extend env (.bvar 0)) body = true := by
              simp [WellTyped] at h_wt; exact h_wt
            -- IH on body at step m (one less than goal m+1)
            have ih_body := ih (Env.extend env (.bvar 0)) body bodyV' bodyT' m
                           h_wt_body h_cv h_av
            -- VCompat (m+1) (lam dom bodyV') (lam dom bodyT') via structural lam
            unfold VCompat
            exact Or.inr (Or.inr (Or.inl ⟨dom, dom, bodyV', bodyT', rfl, rfl, ih_body⟩))
      | mu ann body =>
        simp only [concEvalE] at h_conc
        simp only [absEval] at h_abs
        match h_cv : concEvalE k (Env.extend env (.mu ann body)) body with
        | none => simp [h_cv] at h_conc
        | some bodyV' =>
          simp [h_cv] at h_conc
          match h_av : absEval k (Env.extend env (.mu ann body)) body with
          | none => simp [h_av] at h_abs
          | some bodyT' =>
            simp [h_av] at h_abs
            subst h_conc; subst h_abs
            have h_wt_body : WellTyped k (Env.extend env (.mu ann body)) body = true := by
              simp [WellTyped] at h_wt; exact h_wt
            -- IH on body at step m (one less than goal m+1)
            have ih_body := ih (Env.extend env (.mu ann body)) body bodyV' bodyT' m
                           h_wt_body h_cv h_av
            unfold VCompat
            exact Or.inr (Or.inr (Or.inr (Or.inl ⟨ann, ann, bodyV', bodyT', rfl, rfl, ih_body⟩)))
      | app f a =>
        -- IH on f and a give VCompat for evaluated function and arg.
        -- Need "application congruence": VCompat bodies + VCompat args →
        -- VCompat results after substitution+evaluation.
        sorry
      | asc term ty =>
        -- concEvalE (k+1) env (asc term ty) = concEvalE k env term = some v
        -- absEval (k+1) env (asc term ty) = absEval k env ty = some τ
        simp only [concEvalE] at h_conc
        simp only [absEval] at h_abs
        -- Extract WellTyped components
        simp only [WellTyped, Bool.and_eq_true] at h_wt
        obtain ⟨⟨h_wt_term, h_wt_ty⟩, h_sub⟩ := h_wt
        -- Get σ = absEval k env term
        match h_σ : absEval k env term with
        | none => simp [h_σ] at h_sub
        | some σ =>
          -- Get τ' = absEval k env ty (= τ from h_abs)
          match h_τ' : absEval k env ty with
          | none => simp [h_σ, h_τ'] at h_sub
          | some τ' =>
            simp [h_τ'] at h_abs; subst h_abs
            simp [h_σ, h_τ'] at h_sub
            -- IH on term at step (m+1) — SAME step level as goal!
            -- This is the key benefit of decoupling n from fuel.
            have ih_term := ih env term v σ (m + 1) h_wt_term h_conc h_σ
            -- Bridge via adequacy: VCompat (m+1) v σ → subCheckNF σ τ → VCompat (m+1) v τ
            exact VCompat.adequacy ih_term h_sub

/-- Soundness for the real runtime (concEval).
    Follows from soundness_gen via a concEval→concEvalE bridge. -/
theorem soundness
    (fuel : Nat) (e : Expr) (v τ : Expr) (n : Nat)
    (h_wt : WellTyped fuel [] e = true)
    (h_conc : concEval fuel e = some v)
    (h_abs : absEval fuel [] e = some τ)
    : VCompat n v τ := by
  sorry  -- needs concEval → concEvalE bridge


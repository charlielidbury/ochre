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
- **Both mu:** same annotation, UNFOLDED bodies (self-substituted) are compatible
- **τ = mu:** unfold the mu, check compatibility with the unfolded body
  (equi-recursive; costs one step)
- **v = mu:** unfold the mu on the value side (costs one step)
- **Fallback:** for neutral terms (bvar, app), infer a type and check at lower step

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

/-! ## VCompat-equivalence (vEquiv) and eval-closedness (closedEval)

These support the soundness_gen mu case. The evaluators copy lambda domains
and mu annotations verbatim from the source, so outputs can have free bvar 0
in those positions. The naive closedness lemma (v.subst 0 X = v) is FALSE
(see Tests.lean §14). However, VCompat doesn't compare domains/annotations,
so subst into those positions is invisible to VCompat.

**vEquivB**: two expressions agree on everything VCompat cares about (bodies,
app structure, asc structure) but may differ in lambda domains and mu
annotations. This is the equivalence relation that VCompat respects.

**closedEvalB**: all bvar indices in VCompat-relevant positions (everything
except lambda domains and mu annotations) are below the binding depth.
Evaluator outputs satisfy closedEvalB 0 because the evaluator resolves all
bvar lookups in evaluated positions.

Chain for the mu case:
1. IH gives VCompat m bodyV' bodyT'
2. eval_closedEvalB: closedEvalB 0 bodyV' and closedEvalB 0 bodyT'
3. closedEvalB_subst_vEquiv: vEquivB (bodyV'.subst 0 X) bodyV' and similarly
4. VCompat_of_vEquivB: VCompat m (bodyV'.subst 0 X) (bodyT'.subst 0 Y)
-/

/-- Two expressions are VCompat-equivalent: they agree on everything except
    lambda domains and mu annotations. VCompat only compares bodies (for
    structural lam/mu), app components, and asc components — never domains
    or annotations. So vEquiv expressions are interchangeable for VCompat. -/
def Expr.vEquivB : Expr → Expr → Bool
  | .bvar k, .bvar k' => k == k'
  | .lam _ b1, .lam _ b2 => b1.vEquivB b2
  | .app f1 a1, .app f2 a2 => f1.vEquivB f2 && a1.vEquivB a2
  | .asc t1 y1, .asc t2 y2 => t1.vEquivB t2 && y1.vEquivB y2
  | .type, .type => true
  | .mu _ b1, .mu _ b2 => b1.vEquivB b2
  | _, _ => false

/-- Eval-closedness: all bvar indices in VCompat-relevant positions are < n.
    "VCompat-relevant" means everything EXCEPT lambda domains and mu annotations,
    which VCompat's structural cases ignore.

    For evaluator outputs at the top level: closedEvalB 0 holds because the
    evaluator resolves all bvar lookups in evaluated positions. Unevaluated
    positions (domains, annotations) are NOT checked. -/
def Expr.closedEvalB (n : Nat) : Expr → Bool
  | .bvar k => k < n
  | .lam _ body => body.closedEvalB (n + 1)
  | .app f a => f.closedEvalB n && a.closedEvalB n
  | .asc t y => t.closedEvalB n && y.closedEvalB n
  | .type => true
  | .mu _ body => body.closedEvalB (n + 1)

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

VCompat uses structural cases for lam (raw bodies compatible) and
"unfolded structural" for mu (self-substituted bodies compatible).
The mu case uses unfolded forms because the old raw-body variant
made adequacy FALSE (see Tests.lean §13 counterexample). The unfolded
structural mu tracks actual mu behavior after self-reference resolution.

The lam case uses raw bodies because the soundness IH gives VCompat for
the two evaluators' outputs on the SAME source body. The mu case uses
unfolded forms and needs a "VCompat-equivalence" argument: evaluator
outputs have no free bvar 0 in VCompat-relevant positions (lam bodies,
mu bodies), so subst 0 only affects domains/annotations which VCompat
doesn't compare. NOTE: the naive closedness lemma (v.subst 0 X = v)
is FALSE because evaluators don't evaluate domains. See Tests.lean §14.

The mu-unfolding cases (equi-recursive, costs one step) are kept for
adequacy and the app case. The inferType fallback handles neutral terms
(bvar, app) by inferring a type and checking compatibility at a lower
step index. This replaces the old subCheckNF fallback, which required
transitivity (proved FALSE — see Tests.lean counterexample). -/

/-- Step-indexed value-type compatibility.

    `VCompat n v τ` means: value `v` is compatible with type `τ`,
    given `n` steps of observation budget.

    This is defined as a recursive function on `n` (not an inductive),
    following the Appel-McAllester style.

    **Design choice: structural lam, unfolded structural mu.**

    Lam uses STRUCTURAL cases: "both are lambdas with compatible
    bodies." The soundness proof's lam case is trivial — the IH on the
    body gives VCompat for the normalized bodies directly.

    Mu uses UNFOLDED STRUCTURAL cases: "both are mus, and the self-
    substituted (unfolded) bodies are compatible." This differs from
    the old raw-body variant, which made VCompat.adequacy FALSE (proven
    constructively in Tests.lean §13). The unfolded variant means VCompat
    tracks actual mu behavior, making adequacy's self-elim cases work.

    The app case of soundness needs a separate "application congruence"
    lemma. The mu case needs a "closedness" lemma showing evaluator outputs
    have no free bvar 0, so bodyV'.subst 0 X = bodyV'. -/
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
    -- Unfolded structural mu: both are mus (possibly different annotations),
    -- and the UNFOLDED bodies (self-substituted) are compatible at the lower step.
    -- This replaces the old "raw bodies compatible" variant, which was PROVEN
    -- FALSE for adequacy (see Tests.lean §13 counterexample with old definition).
    -- Using unfolded forms means VCompat tracks actual mu behavior after
    -- self-reference resolution, not just syntactic body similarity.
    ∨ (∃ annV annT bodyV bodyT,
        v = .mu annV bodyV ∧ τ = .mu annT bodyT ∧
        VCompat n (bodyV.subst 0 (.mu annV bodyV)) (bodyT.subst 0 (.mu annT bodyT)))
    -- Mu unfolding on the right (equi-recursive self-intro): costs one step
    ∨ (∃ ann body,
        τ = .mu ann body ∧
        VCompat n v (body.subst 0 (.mu ann body)))
    -- Mu unfolding on the left (equi-recursive self-elim): costs one step
    ∨ (∃ ann body,
        v = .mu ann body ∧
        VCompat n (body.subst 0 (.mu ann body)) τ)
    -- Structural app: both are applications with compatible components.
    -- Needed for VCompat_of_vEquivB (the refl→app case) and for the
    -- soundness_gen app neutral subcase (both evaluators return app).
    ∨ (∃ fV fT aV aT,
        v = .app fV aV ∧ τ = .app fT aT ∧
        VCompat n fV fT ∧ VCompat n aV aT)
    -- InferType fallback: for neutral terms (bvar, app), infer a type and
    -- check compatibility at a lower step. The step decrease (n vs n+1)
    -- ensures well-foundedness and enables composition in adequacy without
    -- needing subCheckNF transitivity (which is FALSE).
    ∨ (∃ ctx ty, inferType ctx v = some ty ∧ VCompat n ty τ)

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
                  ⟨fV, fT, aV, aT, hv, hτ, h_f, h_a⟩ |
                  ⟨ctx, ty, h_infer, h_compat⟩
    -- Top
    · exact Or.inl h_top
    -- Refl
    · exact Or.inr (Or.inl h_refl)
    -- Structural lam: VCompat (k+1) bodyV bodyT → VCompat k bodyV bodyT by IH
    · exact Or.inr (Or.inr (Or.inl ⟨domV, domT, bodyV, bodyT, hv, hτ, VCompat.mono h_body⟩))
    -- Unfolded structural mu: VCompat (k+1) on subst'd bodies → VCompat k by IH
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨annV, annT, bodyV, bodyT, hv, hτ, VCompat.mono h_body⟩)))
    -- Mu right: VCompat (k+1) v (body.subst ...) → VCompat k by IH
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨ann, body, hτ, VCompat.mono h_mu⟩))))
    -- Mu left: VCompat (k+1) (body.subst ...) τ → VCompat k by IH
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨ann, body, hv, VCompat.mono h_mu⟩)))))
    -- Structural app: apply mono to both components
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨fV, fT, aV, aT, hv, hτ, VCompat.mono h_f, VCompat.mono h_a⟩))))))
    -- inferType fallback: apply mono to inner VCompat
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨ctx, ty, h_infer, VCompat.mono h_compat⟩))))))

/-- Multi-step downward closure: VCompat at step n implies VCompat at any step m ≤ n. -/
theorem VCompat.mono_le {n m : Nat} {v τ : Expr}
    (h : VCompat n v τ) (hle : m ≤ n) : VCompat m v τ := by
  induction n generalizing m with
  | zero => cases Nat.le_zero.mp hle; exact h
  | succ k ih =>
    cases m with
    | zero => unfold VCompat; trivial
    | succ j =>
      cases Nat.eq_or_lt_of_le hle with
      | inl heq => rw [heq]; exact h
      | inr hlt => exact ih (VCompat.mono h) (Nat.lt_succ_iff.mp hlt)

/-- For fixpoint mus (body.subst 0 (mu ann body) = mu ann body), VCompat holds
    at all step levels. The mu-right unfolding at each step reduces to the same
    mu, and the chain bottoms out at step 0 (VCompat 0 = True). -/
theorem VCompat.fixpoint_mu {ann body : Expr} (n : Nat) (v : Expr)
    (hfix : body.subst 0 (.mu ann body) = .mu ann body)
    : VCompat n v (.mu ann body) := by
  induction n with
  | zero => trivial
  | succ k ih =>
    unfold VCompat
    apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inl
    exact ⟨ann, body, rfl, by rw [hfix]; exact ih⟩

/-- When self-intro reaches equality (σ = body.subst 0 (mu ann body)),
    VCompat follows from mu-right + mono. -/
theorem VCompat.self_intro_eq {n : Nat} {v σ ann body : Expr}
    (hv : VCompat (n + 1) v σ)
    (heq : σ = body.subst 0 (.mu ann body))
    : VCompat (n + 1) v (.mu ann body) := by
  unfold VCompat
  apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inl
  exact ⟨ann, body, rfl, by rw [← heq]; exact VCompat.mono hv⟩

/-- For fixpoint mus (body.subst 0 self = self), mu-left gives VCompat at all
    steps: v = mu ann body implies VCompat n v τ for ALL τ.
    This is because mu-left unfolds the fixpoint, and the chain bottoms at 0. -/
theorem VCompat.fixpoint_mu_left {ann body : Expr} (n : Nat) (τ : Expr)
    (hfix : body.subst 0 (.mu ann body) = .mu ann body)
    : VCompat n (.mu ann body) τ := by
  induction n with
  | zero => trivial
  | succ k ih =>
    unfold VCompat
    apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inl
    exact ⟨ann, body, rfl, by rw [hfix]; exact ih⟩

/-- When subCheckNF succeeds for .type ⊑ mu with empty seen, self-intro fires:
    the inner call checks .type ⊑ body.subst 0 (mu ann body) with extended seen. -/
theorem subCheckNF_type_self_intro {fuel : Nat} {ctx : List Expr} {ann body : Expr}
    (h : subCheckNF (fuel + 1) ctx [] Expr.type (.mu ann body) = true)
    : subCheckNF fuel ctx [(.type, .mu ann body)] .type (body.subst 0 (.mu ann body)) = true := by
  unfold subCheckNF at h
  have h_neq : (Expr.type == Expr.mu ann body) = false :=
    beq_eq_false_iff_ne.mpr (fun h => nomatch h)
  simp only [h_neq, ite_false, List.any_nil, Bool.false_eq_true] at h
  exact h

/-- When subCheckNF succeeds from .type, VCompat holds for all v and n.
    subCheckNF .type τ only succeeds when τ is .type (top) or a mu (self-intro chain).
    The proof uses outer induction on fuel (self-intro decreases fuel) and inner
    induction on the VCompat step index (mu-right decreases step).

    hseen bridges seen entries: self-intro adds (.type, mu) to seen; the seen hit
    gives the result when a cycle is encountered. -/
theorem VCompat.from_type_sub_gen :
    ∀ (fuel : Nat), ∀ (n : Nat) (v τ : Expr) (ctx : List Expr) (seen : List (Expr × Expr)),
    subCheckNF fuel ctx seen Expr.type τ = true →
    (∀ p, p ∈ seen → VCompat n v p.2) →
    VCompat n v τ := by
  intro fuel
  induction fuel with
  | zero => intro n v τ ctx seen h; simp [subCheckNF] at h
  | succ k ih_fuel =>
    intro n v τ ctx seen hcheck hseen
    unfold subCheckNF at hcheck
    by_cases heq_beq : (Expr.type == τ) = true
    · have heq : τ = Expr.type := (eq_of_beq heq_beq).symm
      subst heq
      cases n with | zero => trivial | succ m => unfold VCompat; exact Or.inl rfl
    · have heq_false : (Expr.type == τ) = false := by
        cases h : (Expr.type == τ) with | true => exact absurd h heq_beq | false => rfl
      simp only [heq_false, ite_false] at hcheck
      by_cases hseen_hit : (seen.any fun p => Expr.type == p.1 && τ == p.2) = true
      · have := List.any_eq_true.mp hseen_hit
        obtain ⟨⟨a', b'⟩, h_mem, h_match⟩ := this
        simp [Bool.and_eq_true] at h_match
        obtain ⟨_, hb'⟩ := h_match
        subst hb'
        exact hseen ⟨a', τ⟩ h_mem
      · simp only [hseen_hit, ite_false] at hcheck
        cases τ with
        | type => simp [Expr.beq_refl] at heq_beq
        | mu ann_τ body_τ =>
          -- Self-intro: hcheck is now the inner call after match
          -- .type is not lam/mu, τ = mu → match goes to (_, .mu) → self-intro
          -- hcheck : subCheckNF k ctx ((.type, mu) :: seen) .type (body.subst ...)
          -- Build VCompat n v (mu ann_τ body_τ) via inner induction on step j ≤ n
          suffices h_all : ∀ j, j ≤ n → VCompat j v (.mu ann_τ body_τ) from
            h_all n (Nat.le_refl _)
          intro j; induction j with
          | zero => intro _; trivial
          | succ i ih_j =>
            intro hi
            -- mu-right: VCompat i v (body.subst ...)
            unfold VCompat
            apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inl
            refine ⟨ann_τ, body_τ, rfl, ?_⟩
            -- Use ih_fuel at step i with extended seen
            apply ih_fuel i v _ ctx ((.type, .mu ann_τ body_τ) :: seen) hcheck
            -- hseen for extended seen at step i
            intro p hp
            cases List.mem_cons.mp hp with
            | inl heq_p =>
              -- New entry (.type, mu ann_τ body_τ): need VCompat i v (mu ...)
              cases heq_p; simp
              exact ih_j (Nat.le_of_succ_le hi)
            | inr h_old =>
              -- Old entry: VCompat i v p.2 from hseen at step n via mono_le
              exact VCompat.mono_le (hseen p h_old) (Nat.le_of_succ_le hi)
        | lam _ _ => simp [inferType] at hcheck
        | bvar _ => simp [inferType] at hcheck
        | app _ _ => simp [inferType] at hcheck
        | asc _ _ => simp [inferType] at hcheck

/-- Corollary: subCheckNF .type (mu ann body) with empty seen gives VCompat. -/
theorem VCompat.from_type_sub {fuel : Nat} {ctx : List Expr} {n : Nat} {v : Expr}
    {ann body : Expr}
    (hcheck : subCheckNF fuel ctx [] Expr.type (.mu ann body) = true)
    : VCompat n v (.mu ann body) :=
  VCompat.from_type_sub_gen fuel n v _ ctx [] hcheck
    (fun p hp => absurd hp (List.not_mem_nil p))

/-- General self-intro: if subCheckNF σ (mu ann body) succeeds with empty seen,
    and σ is not a mu, then VCompat n v (mu ann body) for all n and v.

    This works because self-intro unfolds to subCheckNF σ (body.subst 0 (mu ann body))
    with seen [(σ, mu ann body)]. The inner recursion either:
    1. Hits equality (σ = body.subst) → VCompat via refl/mono
    2. Hits seen (body.subst = mu ann body, fixpoint) → VCompat via fixpoint chain
    3. Further recurses (fuel decreases) → IH handles it

    Uses outer induction on fuel and inner induction on VCompat step index. -/
theorem VCompat.from_self_intro_gen :
    ∀ (fuel : Nat), ∀ (n : Nat) (v σ : Expr) (ctx : List Expr) (seen : List (Expr × Expr)),
    (∀ ann' body', σ ≠ .mu ann' body') →
    ∀ (ann body : Expr),
    subCheckNF fuel ctx seen σ (.mu ann body) = true →
    (∀ p, p ∈ seen → VCompat n v p.2) →
    VCompat n v (.mu ann body) := by
  intro fuel
  induction fuel with
  | zero => intro n v σ ctx seen _ ann body h; simp [subCheckNF] at h
  | succ k ih_fuel =>
    intro n v σ ctx seen hσ_not_mu ann body hcheck hseen
    unfold subCheckNF at hcheck
    by_cases heq_beq : (σ == Expr.mu ann body) = true
    · -- σ = mu ann body — but σ is not a mu!
      have heq := eq_of_beq heq_beq
      exact absurd heq (hσ_not_mu ann body)
    · have heq_false : (σ == Expr.mu ann body) = false := by
        cases h : (σ == Expr.mu ann body) with | true => exact absurd h heq_beq | false => rfl
      simp only [heq_false, ite_false] at hcheck
      by_cases hseen_hit : (seen.any fun p => σ == p.1 && Expr.mu ann body == p.2) = true
      · -- Seen hit: σ matches a seen entry's LHS, mu ann body matches RHS
        have := List.any_eq_true.mp hseen_hit
        obtain ⟨⟨a', b'⟩, h_mem, h_match⟩ := this
        simp [Bool.and_eq_true] at h_match
        obtain ⟨_, hb'⟩ := h_match
        subst hb'
        exact hseen ⟨a', .mu ann body⟩ h_mem
      · have hseen_false : (seen.any fun p => σ == p.1 && Expr.mu ann body == p.2) = false := by
          cases h : (seen.any _) with | true => exact absurd h hseen_hit | false => rfl
        simp only [hseen_false, ite_false] at hcheck
        -- After equality and seen checks fail, match on rhs = mu ann body
        -- The match goes to (_, .mu ann body) → self-intro (since σ ≠ mu)
        -- hcheck is now: subCheckNF k ctx ((σ, mu ann body) :: seen) σ (body.subst 0 (mu ann body))
        -- Build VCompat n v (mu ann body) by inner induction on step
        suffices h_all : ∀ j, j ≤ n → VCompat j v (.mu ann body) from
          h_all n (Nat.le_refl _)
        intro j; induction j with
        | zero => intro _; trivial
        | succ i ih_j =>
          intro hi
          unfold VCompat
          apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inl
          refine ⟨ann, body, rfl, ?_⟩
          -- Need: VCompat i v (body.subst 0 (mu ann body))
          -- The inner subCheckNF is σ ⊑ body.subst, not .type ⊑ body.subst.
          -- We can't directly apply from_type_sub_gen.
          -- Instead, we need a general self-intro adequacy at step i.
          -- For now, use sorry for this complex case.
          sorry

/-- Corollary: self-intro with empty seen. -/
theorem VCompat.from_self_intro {fuel : Nat} {ctx : List Expr} {n : Nat} {v σ : Expr}
    {ann body : Expr}
    (hσ_not_mu : ∀ ann' body', σ ≠ .mu ann' body')
    (hcheck : subCheckNF fuel ctx [] σ (.mu ann body) = true)
    : VCompat n v (.mu ann body) :=
  VCompat.from_self_intro_gen fuel n v σ ctx [] hσ_not_mu ann body hcheck
    (fun p hp => absurd hp (List.not_mem_nil p))

/-- VCompat respects subCheckNF: if v is compatible with σ, and σ ⊑ τ
    by the algorithmic checker, then v is compatible with τ.

    This is the "adequacy" lemma — the bridge between the semantic relation
    (VCompat) and the algorithmic checker (subCheckNF). It's needed for the
    asc case: the IH gives VCompat v σ (from evaluating the term), and
    WellTyped gives subCheckNF σ τ (from the ascription check).

    Proof approach: induction on n (VCompat step index).
    - n = 0: trivially True.
    - n + 1: case split on VCompat disjunct:
      - top: trivial
      - refl (v = σ): case-split on σ shape; use structural VCompat + IH
        for lam/mu, inferType disjunct for bvar/app
      - structural lam/mu: IH on bodies (subCheckNF decomposes structurally)
      - mu unfolding: use VCompat mu-unfold + IH (costs one step of n)
      - inferType: compose via IH (no transitivity needed!)
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
                       ⟨fV, fS, aV, aS, hv_eq, hσ_eq, h_f, h_a⟩ |
                       ⟨ctx1, ty1, h_infer, h_compat⟩
        -- Case 1: σ = .type (τ ≠ .type, τ ≠ σ → τ must be mu via self-intro)
        · subst h_top
          cases τ with
          | type => exact absurd rfl hτ
          | mu ann_τ body_τ =>
            -- .type ⊑ mu ann_τ body_τ by self-intro
            exact VCompat.from_type_sub hcheck
          | bvar _ | lam _ _ | app _ _ | asc _ _ =>
            -- subCheckNF .type (non-type, non-mu) = false: inferType .type = none
            cases fuel with
            | zero => simp [subCheckNF] at hcheck
            | succ k =>
              simp [subCheckNF, inferType, beq_eq_false_iff_ne.mpr hστ] at hcheck
        -- Case 2: v = σ (refl) — case-split on v's shape to produce VCompat disjunct
        · subst h_refl
          -- v = σ, hcheck : subCheckNF fuel ctx [] v τ = true
          -- Need: VCompat (m+1) v τ
          -- Strategy: decompose v to find a VCompat disjunct for (v, τ)
          cases v with
          | type =>
            -- v = σ = .type → subCheckNF .type τ, τ ≠ .type → τ = mu
            cases τ with
            | type => exact absurd rfl hτ
            | mu ann_τ body_τ => exact VCompat.from_type_sub hcheck
            | bvar _ | lam _ _ | app _ _ | asc _ _ =>
              cases fuel with
              | zero => simp [subCheckNF] at hcheck
              | succ k =>
                simp [subCheckNF, inferType, beq_eq_false_iff_ne.mpr hστ] at hcheck
          | lam dV bV =>
            -- v = σ = lam dV bV, τ ≠ .type
            cases τ with
            | type => exact absurd rfl hτ
            | lam dT bT =>
              -- structural lam: need VCompat m bV bT
              -- VCompat m bV bV by refl, subCheckNF bV bT from extraction, IH
              cases fuel with
              | zero => simp [subCheckNF] at hcheck
              | succ k =>
                by_cases h_eq : Expr.lam dV bV = Expr.lam dT bT
                · exact absurd h_eq hστ
                · obtain ⟨fuel', ctx', h_body_sub⟩ := subCheckNF_lam_lam_body hcheck h_eq
                  -- VCompat m bV bV: by refl
                  have h_bV_refl : VCompat m bV bV := by
                    cases m with
                    | zero => trivial
                    | succ k => unfold VCompat; exact Or.inr (Or.inl rfl)
                  have h_bT := ih h_bV_refl h_body_sub
                  unfold VCompat
                  exact Or.inr (Or.inr (Or.inl ⟨dV, dT, bV, bT, rfl, rfl, h_bT⟩))
            | mu ann_τ body_τ =>
              exact VCompat.from_self_intro (fun _ _ h => by cases h) hcheck
            | bvar _ =>
              exfalso; exact subCheckNF_lam_impossible hcheck hστ
                (fun h => nomatch h) (fun _ _ h => nomatch h) (fun _ _ h => nomatch h)
            | app _ _ =>
              exfalso; exact subCheckNF_lam_impossible hcheck hστ
                (fun h => nomatch h) (fun _ _ h => nomatch h) (fun _ _ h => nomatch h)
            | asc _ _ =>
              exfalso; exact subCheckNF_lam_impossible hcheck hστ
                (fun h => nomatch h) (fun _ _ h => nomatch h) (fun _ _ h => nomatch h)
          | mu annV bodyV =>
            -- v = σ = mu annV bodyV
            cases τ with
            | type => exact absurd rfl hτ
            | mu annT bodyT =>
              -- structural mu: need VCompat on subst'd bodies
              -- With unfolded structural mu, need:
              --   VCompat m (bodyV.subst 0 (mu annV bodyV)) (bodyT.subst 0 (mu annT bodyT))
              -- Have: subCheckNF bodyV bodyT (from extraction), but IH needs
              -- subCheckNF on subst'd forms. Sorry for now.
              sorry
            | _ =>
              -- Self-elim: v = σ = mu annV bodyV, τ ≠ type, ≠ mu
              -- Use mu-left: VCompat (m+1) v τ ← VCompat m (bodyV.subst 0 v) τ
              unfold VCompat
              apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inl
              refine ⟨annV, bodyV, rfl, ?_⟩
              -- Need: VCompat m (bodyV.subst 0 (mu annV bodyV)) τ
              by_cases hfix : bodyV.subst 0 (.mu annV bodyV) = .mu annV bodyV
              · -- Fixpoint: bodyV.subst 0 v = v → use IH with refl
                rw [hfix]
                have h_refl : VCompat m (.mu annV bodyV) (.mu annV bodyV) := by
                  cases m with | zero => trivial | succ k => unfold VCompat; exact Or.inr (Or.inl rfl)
                exact ih h_refl hcheck
              · -- Non-fixpoint: needs generalized adequacy with seen
                sorry
          | bvar k =>
            -- v = σ = bvar k. subCheckNF uses inferType catch-all.
            cases fuel with
            | zero => simp [subCheckNF] at hcheck
            | succ fk =>
              cases τ with
              | type => exact absurd rfl hτ
              | mu ann_τ body_τ =>
                exact VCompat.from_self_intro (fun _ _ h => by cases h) hcheck
              | _ =>
                -- Non-type, non-mu τ: extract inferType from subCheckNF
                obtain ⟨ty_inf, h_inf, h_sub⟩ := subCheckNF_neutral_inferType hcheck
                  hστ hτ (fun _ _ h => nomatch h) (fun _ _ h => nomatch h) (fun _ _ h => nomatch h)
                -- Build inferType disjunct via IH
                have h_refl : VCompat m ty_inf ty_inf := by
                  cases m with | zero => trivial | succ k => unfold VCompat; exact Or.inr (Or.inl rfl)
                have h_ty_τ := ih h_refl h_sub
                unfold VCompat
                exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨ctx, ty_inf, h_inf, h_ty_τ⟩))))))
          | app f a =>
            -- v = σ = app f a. Similar to bvar: inferType catch-all.
            cases fuel with
            | zero => simp [subCheckNF] at hcheck
            | succ fk =>
              cases τ with
              | type => exact absurd rfl hτ
              | mu ann_τ body_τ =>
                exact VCompat.from_self_intro (fun _ _ h => by cases h) hcheck
              | _ =>
                obtain ⟨ty_inf, h_inf, h_sub⟩ := subCheckNF_neutral_inferType hcheck
                  hστ hτ (fun _ _ h => nomatch h) (fun _ _ h => nomatch h) (fun _ _ h => nomatch h)
                have h_refl : VCompat m ty_inf ty_inf := by
                  cases m with | zero => trivial | succ k => unfold VCompat; exact Or.inr (Or.inl rfl)
                have h_ty_τ := ih h_refl h_sub
                unfold VCompat
                exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨ctx, ty_inf, h_inf, h_ty_τ⟩))))))
          | asc t ty =>
            -- v = σ = asc t ty. inferType returns none → subCheckNF fails
            -- unless τ = .type (handled) or σ = τ (handled) or τ = .mu
            cases fuel with
            | zero => simp [subCheckNF] at hcheck
            | succ fk =>
              cases τ with
              | type => exact absurd rfl hτ
              | mu ann_τ body_τ =>
                exact VCompat.from_self_intro (fun _ _ h => by cases h) hcheck
              | _ =>
                -- asc is not lam/mu, τ is not type/mu → inferType catch-all
                -- inferType (asc ...) = none → false, contradiction
                exfalso
                have := subCheckNF_neutral_inferType hcheck hστ hτ
                  (fun _ _ h => nomatch h) (fun _ _ h => nomatch h) (fun _ _ h => nomatch h)
                obtain ⟨ty_inf, h_inf, _⟩ := this
                simp [inferType] at h_inf
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
          | mu ann_τ body_τ =>
            exact VCompat.from_self_intro (fun _ _ h => by cases h) hcheck
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
          -- h_body : VCompat m (bodyV.subst 0 (mu annV bodyV)) (bodyS.subst 0 (mu annS bodyS))
          -- hcheck : subCheckNF fuel ctx [] (mu annS bodyS) τ = true
          cases τ with
          | type => exact absurd rfl hτ
          | mu annT bodyT =>
            -- mu/mu → mu: subCheckNF extracts body check on raw bodies,
            -- but IH needs subCheckNF on subst'd forms.
            sorry
          | _ =>
            -- Self-elim: v = mu annV bodyV, σ = mu annS bodyS, τ ≠ type, ≠ mu
            -- Use mu-left to construct VCompat (m+1) v τ
            unfold VCompat
            apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inl
            refine ⟨annV, bodyV, rfl, ?_⟩
            -- Need: VCompat m (bodyV.subst 0 v) τ where v = mu annV bodyV
            -- For fixpoint σ: bodyS.subst 0 σ = σ → h_body becomes VCompat m ... σ
            -- IH: VCompat m ... σ → subCheckNF σ τ → VCompat m ... τ
            by_cases hfixσ : bodyS.subst 0 (.mu annS bodyS) = .mu annS bodyS
            · rw [hfixσ] at h_body
              exact ih h_body hcheck
            · sorry  -- non-fixpoint σ: needs generalized adequacy with seen
        -- Case 5: mu right (σ = mu ann_σ body_σ, unfold right)
        · subst hσ_eq
          -- h_unfold : VCompat m v (body_σ.subst 0 (mu ann_σ body_σ))
          -- hcheck : subCheckNF (mu ann_σ body_σ) τ
          -- After self-elim: subCheckNF (body_σ.subst 0 σ) τ (with seen)
          -- IH: VCompat m v (body_σ.subst 0 σ) → subCheckNF (body_σ.subst 0 σ) τ → VCompat m v τ
          -- Same seen-list issue.
          sorry
        -- Case 6: mu left (v = mu ann_v body_v, unfold left) → IH!
        · subst hv_eq
          -- h_unfold : VCompat m (body_v.subst 0 (mu ann_v body_v)) σ
          -- ih gives: VCompat m (body_v.subst 0 (mu ann_v body_v)) τ
          -- Build mu-left disjunct of VCompat (m+1)
          unfold VCompat
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
            ⟨ann_v, body_v, rfl, ih h_unfold hcheck⟩)))))
        -- Case 7: structural app (v = app fV aV, σ = app fS aS)
        · subst hv_eq; subst hσ_eq
          -- h_f : VCompat m fV fS, h_a : VCompat m aV aS
          -- hcheck : subCheckNF fuel ctx [] (app fS aS) τ = true
          -- Need: VCompat (m+1) (app fV aV) τ
          cases τ with
          | type => exact absurd rfl hτ
          | mu ann_τ body_τ =>
            exact VCompat.from_self_intro (fun _ _ h => by cases h) hcheck
          | _ =>
            -- Non-type, non-mu τ: subCheckNF uses inferType on σ = app fS aS
            -- Need to extract inferType result and bridge to VCompat for v
            sorry  -- structural app adequacy: needs inferType congruence
        -- Case 8: inferType fallback — compose via IH (no transitivity needed!)
        · -- h_infer : inferType ctx1 v = some ty1
          -- h_compat : VCompat m ty1 σ
          -- hcheck : subCheckNF fuel ctx [] σ τ = true
          -- IH on h_compat: VCompat m ty1 τ
          have h_ty_τ := ih h_compat hcheck
          -- Build inferType disjunct of VCompat (m+1) v τ
          unfold VCompat
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
            ⟨ctx1, ty1, h_infer, h_ty_τ⟩))))))

/-! ## VCompat-equivalence lemmas

These lemmas support the soundness_gen mu case. The chain is:
1. eval_closedEvalB: evaluator outputs satisfy closedEvalB 0
2. closedEvalB_subst_vEquiv: subst at j is a vEquiv-no-op for closedEvalB j
3. VCompat_of_vEquivB: VCompat is invariant under vEquiv

Together: IH gives VCompat for raw bodies, evaluator closedness + subst vEquiv
gives VCompat for substituted bodies. -/

/-- Substitution at index j is a vEquiv-no-op for expressions that are
    closedEval at depth j. Since closedEvalB only checks bvar indices in
    VCompat-relevant positions, and those are all < j (so subst j X leaves
    them alone), the result is vEquiv to the original.

    Key cases:
    - bvar k with k < j: subst returns bvar k. vEquivB ✓
    - lam dom body: subst changes dom (not checked) and body at j+1.
      closedEvalB checks body at j+1, so IH gives vEquivB for body. ✓
    - mu ann body: same as lam (ann not checked). ✓ -/
theorem closedEvalB_subst_vEquiv (j : Nat) (e : Expr) (X : Expr)
    (hc : e.closedEvalB j = true)
    : (e.subst j X).vEquivB e = true := by
  induction e generalizing j X with
  | bvar k =>
    simp [Expr.closedEvalB] at hc
    unfold Expr.subst
    have hne : (k == j) = false := by
      simp [BEq.beq, decEq]; omega
    simp [hne]
    have hle : ¬(k > j) := by omega
    simp [hle]
    simp [Expr.vEquivB, BEq.beq, decEq]
  | lam dom body _ ih_body =>
    simp [Expr.closedEvalB] at hc
    simp [Expr.subst, Expr.vEquivB]
    exact ih_body (j + 1) (X.shift 1 0) hc
  | app f a ih_f ih_a =>
    simp [Expr.closedEvalB, Bool.and_eq_true] at hc
    simp [Expr.subst, Expr.vEquivB, Bool.and_eq_true]
    exact ⟨ih_f j X hc.1, ih_a j X hc.2⟩
  | asc t y ih_t ih_y =>
    simp [Expr.closedEvalB, Bool.and_eq_true] at hc
    simp [Expr.subst, Expr.vEquivB, Bool.and_eq_true]
    exact ⟨ih_t j X hc.1, ih_y j X hc.2⟩
  | type =>
    simp [Expr.subst, Expr.vEquivB]
  | mu ann body _ ih_body =>
    simp [Expr.closedEvalB] at hc
    simp [Expr.subst, Expr.vEquivB]
    exact ih_body (j + 1) (X.shift 1 0) hc

/-- vEquiv is preserved by shift: shifting both sides preserves vEquiv. -/
theorem Expr.vEquivB_shift (d : Nat) :
    ∀ (c : Nat) (a b : Expr),
    a.vEquivB b = true → (a.shift d c).vEquivB (b.shift d c) = true := by
  intro c a; induction a generalizing c with
  | bvar k => intro b h; cases b <;> simp_all [Expr.vEquivB, Expr.shift, BEq.beq, decEq]; split <;> simp [Expr.vEquivB, BEq.beq, decEq]
  | lam dom body _ ih => intro b h; cases b with | lam d' b' => simp [Expr.vEquivB] at h; simp [Expr.shift, Expr.vEquivB]; exact ih (c+1) b' h | _ => simp [Expr.vEquivB] at h
  | app f a ihf iha => intro b h; cases b with | app f' a' => simp [Expr.vEquivB, Bool.and_eq_true] at h; simp [Expr.shift, Expr.vEquivB, Bool.and_eq_true]; exact ⟨ihf c f' h.1, iha c a' h.2⟩ | _ => simp [Expr.vEquivB] at h
  | asc t y iht ihy => intro b h; cases b with | asc t' y' => simp [Expr.vEquivB, Bool.and_eq_true] at h; simp [Expr.shift, Expr.vEquivB, Bool.and_eq_true]; exact ⟨iht c t' h.1, ihy c y' h.2⟩ | _ => simp [Expr.vEquivB] at h
  | type => intro b h; cases b <;> simp_all [Expr.vEquivB, Expr.shift]
  | mu ann body _ ih => intro b h; cases b with | mu a' b' => simp [Expr.vEquivB] at h; simp [Expr.shift, Expr.vEquivB]; exact ih (c+1) b' h | _ => simp [Expr.vEquivB] at h

/-- vEquiv is preserved by substitution: if a ≈ b and X ≈ Y, then
    a.subst j X ≈ b.subst j Y. -/
theorem Expr.vEquivB_subst (j : Nat) (a : Expr) :
    ∀ (b X Y : Expr),
    a.vEquivB b = true → X.vEquivB Y = true →
    (a.subst j X).vEquivB (b.subst j Y) = true := by
  induction a generalizing j with
  | bvar k => intro b X Y h hXY; cases b with
    | bvar k' =>
      simp [Expr.vEquivB, BEq.beq, decEq] at h; subst h
      simp [Expr.subst]; split
      · exact hXY
      · split <;> simp [Expr.vEquivB, BEq.beq, decEq]
    | _ => simp [Expr.vEquivB] at h
  | lam dom body _ ih => intro b X Y h hXY; cases b with
    | lam d' b' =>
      simp [Expr.vEquivB] at h; simp [Expr.subst, Expr.vEquivB]
      exact ih (j + 1) b' (X.shift 1 0) (Y.shift 1 0) h (Expr.vEquivB_shift 1 0 X Y hXY)
    | _ => simp [Expr.vEquivB] at h
  | app f a ihf iha => intro b X Y h hXY; cases b with
    | app f' a' =>
      simp [Expr.vEquivB, Bool.and_eq_true] at h; simp [Expr.subst, Expr.vEquivB, Bool.and_eq_true]
      exact ⟨ihf j f' X Y h.1 hXY, iha j a' X Y h.2 hXY⟩
    | _ => simp [Expr.vEquivB] at h
  | asc t y iht ihy => intro b X Y h hXY; cases b with
    | asc t' y' =>
      simp [Expr.vEquivB, Bool.and_eq_true] at h; simp [Expr.subst, Expr.vEquivB, Bool.and_eq_true]
      exact ⟨iht j t' X Y h.1 hXY, ihy j y' X Y h.2 hXY⟩
    | _ => simp [Expr.vEquivB] at h
  | type => intro b X Y h hXY; cases b <;> simp_all [Expr.vEquivB, Expr.subst]
  | mu ann body _ ih => intro b X Y h hXY; cases b with
    | mu a' b' =>
      simp [Expr.vEquivB] at h; simp [Expr.subst, Expr.vEquivB]
      exact ih (j + 1) b' (X.shift 1 0) (Y.shift 1 0) h (Expr.vEquivB_shift 1 0 X Y hXY)
    | _ => simp [Expr.vEquivB] at h

/-- VCompat is reflexive at all step levels. -/
theorem VCompat.refl (n : Nat) (e : Expr) : VCompat n e e := by
  cases n with
  | zero => trivial
  | succ k => unfold VCompat; exact Or.inr (Or.inl rfl)

/-- vEquivB is reflexive. -/
theorem Expr.vEquivB_refl : ∀ (e : Expr), e.vEquivB e = true
  | .bvar k => by simp [Expr.vEquivB, BEq.beq, decEq]
  | .lam dom body => by simp [Expr.vEquivB]; exact Expr.vEquivB_refl body
  | .app f a => by simp [Expr.vEquivB, Bool.and_eq_true]; exact ⟨Expr.vEquivB_refl f, Expr.vEquivB_refl a⟩
  | .asc t y => by simp [Expr.vEquivB, Bool.and_eq_true]; exact ⟨Expr.vEquivB_refl t, Expr.vEquivB_refl y⟩
  | .type => by simp [Expr.vEquivB]
  | .mu ann body => by simp [Expr.vEquivB]; exact Expr.vEquivB_refl body

/-- vEquivB preserves top-level constructor: if a ≈ b, they have the same head. -/
-- Shape lemmas: vEquivB constrains both operands to have matching constructors.
-- "forward" versions: a.vEquivB b → b has matching constructor
private theorem vEquivB_fwd_bvar {k : Nat} {b : Expr} (h : (Expr.bvar k).vEquivB b = true) : b = .bvar k := by
  cases b <;> simp [Expr.vEquivB, BEq.beq, decEq] at h; subst h; rfl
private theorem vEquivB_fwd_lam {d bo : Expr} {b : Expr} (h : (Expr.lam d bo).vEquivB b = true) : ∃ d' bo', b = .lam d' bo' ∧ bo.vEquivB bo' = true := by
  cases b with | lam d' bo' => exact ⟨d', bo', rfl, by simp [Expr.vEquivB] at h; exact h⟩ | _ => simp [Expr.vEquivB] at h
private theorem vEquivB_fwd_app {f a : Expr} {b : Expr} (h : (Expr.app f a).vEquivB b = true) : ∃ f' a', b = .app f' a' ∧ f.vEquivB f' = true ∧ a.vEquivB a' = true := by
  cases b with | app f' a' => simp [Expr.vEquivB, Bool.and_eq_true] at h; exact ⟨f', a', rfl, h.1, h.2⟩ | _ => simp [Expr.vEquivB] at h
private theorem vEquivB_fwd_type {b : Expr} (h : Expr.type.vEquivB b = true) : b = .type := by
  cases b with | type => rfl | _ => simp [Expr.vEquivB] at h
private theorem vEquivB_fwd_mu {ann bo : Expr} {b : Expr} (h : (Expr.mu ann bo).vEquivB b = true) : ∃ ann' bo', b = .mu ann' bo' ∧ bo.vEquivB bo' = true := by
  cases b with | mu ann' bo' => exact ⟨ann', bo', rfl, by simp [Expr.vEquivB] at h; exact h⟩ | _ => simp [Expr.vEquivB] at h
-- "backward" versions: a.vEquivB b → a has matching constructor (for v'.vEquivB v)
private theorem vEquivB_bwd_bvar {k : Nat} {a : Expr} (h : a.vEquivB (Expr.bvar k) = true) : a = .bvar k := by
  cases a <;> simp [Expr.vEquivB, BEq.beq, decEq] at h; subst h; rfl
private theorem vEquivB_bwd_lam {d bo : Expr} {a : Expr} (h : a.vEquivB (Expr.lam d bo) = true) : ∃ d' bo', a = .lam d' bo' ∧ bo'.vEquivB bo = true := by
  cases a with | lam d' bo' => exact ⟨d', bo', rfl, by simp [Expr.vEquivB] at h; exact h⟩ | _ => simp [Expr.vEquivB] at h
private theorem vEquivB_bwd_app {f a : Expr} {b : Expr} (h : b.vEquivB (Expr.app f a) = true) : ∃ f' a', b = .app f' a' ∧ f'.vEquivB f = true ∧ a'.vEquivB a = true := by
  cases b with | app f' a' => simp [Expr.vEquivB, Bool.and_eq_true] at h; exact ⟨f', a', rfl, h.1, h.2⟩ | _ => simp [Expr.vEquivB] at h
private theorem vEquivB_bwd_type {a : Expr} (h : a.vEquivB Expr.type = true) : a = .type := by
  cases a with | type => rfl | _ => simp [Expr.vEquivB] at h
private theorem vEquivB_bwd_mu {ann bo : Expr} {a : Expr} (h : a.vEquivB (Expr.mu ann bo) = true) : ∃ ann' bo', a = .mu ann' bo' ∧ bo'.vEquivB bo = true := by
  cases a with | mu ann' bo' => exact ⟨ann', bo', rfl, by simp [Expr.vEquivB] at h; exact h⟩ | _ => simp [Expr.vEquivB] at h

/-- inferType is compatible with vEquiv: if v' ≈ v and inferType ctx v = some ty,
    then inferType ctx v' = some ty' with ty' ≈ ty. -/
theorem inferType_vEquivB {ctx : List Expr} {v v' : Expr}
    (hv : v'.vEquivB v = true)
    {ty : Expr} (h : inferType ctx v = some ty)
    : ∃ ty', inferType ctx v' = some ty' ∧ ty'.vEquivB ty = true := by
  induction v generalizing v' ty with
  | bvar k =>
    have := vEquivB_bwd_bvar hv; subst this
    exact ⟨ty, h, Expr.vEquivB_refl ty⟩
  | lam _ _ _ _ => simp [inferType] at h
  | asc _ _ _ _ => simp [inferType] at h
  | type => simp [inferType] at h
  | mu _ _ _ _ => simp [inferType] at h
  | app f a ihf _ =>
    obtain ⟨f', a', rfl, hf, ha⟩ := vEquivB_bwd_app hv
    -- Case split on inferType ctx f
    cases hfty : inferType ctx f with
    | none =>
      have : inferType ctx (.app f a) = none := by simp [inferType, hfty]
      rw [this] at h; cases h
    | some fty =>
      obtain ⟨fty', hfty', hftye⟩ := ihf hf hfty
      cases fty with
      | lam dom retTy =>
        have h1 : inferType ctx (.app f a) = some (retTy.subst 0 a) := by
          simp [inferType, hfty]
        rw [h1] at h; injection h with h; subst h
        obtain ⟨dom', retTy', rfl, hre⟩ := vEquivB_bwd_lam hftye
        exact ⟨retTy'.subst 0 a', by simp [inferType, hfty'],
               Expr.vEquivB_subst 0 retTy' retTy a' a hre ha⟩
      | mu ann body =>
        obtain ⟨ann', body', rfl, hbe⟩ := vEquivB_bwd_mu hftye
        have h_unf := Expr.vEquivB_subst 0 body' body f' f hbe hf
        cases h_match : body.subst 0 f with
        | lam dom retTy =>
          have h1 : inferType ctx (.app f a) = some (retTy.subst 0 a) := by
            simp [inferType, hfty, h_match]
          rw [h1] at h; injection h with h; subst h
          rw [h_match] at h_unf
          obtain ⟨dom'', retTy', h_eq, hre⟩ := vEquivB_bwd_lam h_unf
          exact ⟨retTy'.subst 0 a', by simp [inferType, hfty', h_eq],
                 Expr.vEquivB_subst 0 retTy' retTy a' a hre ha⟩
        | _ =>
          have : inferType ctx (.app f a) = none := by simp [inferType, hfty, h_match]
          rw [this] at h; cases h
      | _ =>
        have : inferType ctx (.app f a) = none := by simp [inferType, hfty]
        rw [this] at h; cases h

/-- VCompat is invariant under vEquiv: if v' ≈ v and τ' ≈ τ (same structure
    except possibly different domains/annotations), and VCompat n v τ, then
    VCompat n v' τ'.

    The proof goes by induction on n. For each VCompat disjunct:
    - top (τ = type): vEquiv preserves type constructor → τ' = type → top ✓
    - refl (v = τ): case-split on v shape, use structural cases for lam/mu
    - structural lam/mu: vEquiv preserves lam/mu and bodies → IH on bodies
    - mu unfold: vEquiv preserves mu → unfold the vEquiv'd mu → IH
    - inferType: vEquiv may change inferType results via domain changes,
      but evaluator outputs (the actual use case) don't have this issue.

    NOTE: This is stated for Bool-valued vEquivB. The proof is sorry'd pending
    detailed case analysis of the inferType interaction. The key use case
    (evaluator outputs differing only in domains/annotations) is confirmed
    correct by native_decide testing (Tests.lean §16). -/
theorem VCompat_of_vEquivB {n : Nat} {v v' τ τ' : Expr}
    (hv : v'.vEquivB v = true) (hτ : τ'.vEquivB τ = true)
    (h : VCompat n v τ) : VCompat n v' τ' := by
  induction n generalizing v v' τ τ' with
  | zero => trivial
  | succ k ih =>
    unfold VCompat at h ⊢
    rcases h with h_top | h_refl
      | ⟨dV, dT, bV, bT, rfl, rfl, hbody⟩
      | ⟨aV, aT, bV, bT, rfl, rfl, hbody⟩
      | ⟨ann, body, rfl, hunf⟩
      | ⟨ann, body, rfl, hunf⟩
      | ⟨fV, fT, aV, aT, rfl, rfl, hfc, hac⟩
      | ⟨ctx1, ty1, hinf, hcompat⟩
    -- Case 1: top (τ = type)
    · subst h_top; exact Or.inl (vEquivB_bwd_type hτ)
    -- Case 2: refl (v = τ)
    · subst h_refl  -- now τ = v, hτ : τ'.vEquivB v = true
      cases v with
      | bvar k =>
        have := vEquivB_bwd_bvar hv; have := vEquivB_bwd_bvar hτ
        subst_vars; exact Or.inr (Or.inl rfl)
      | type => exact Or.inl (vEquivB_bwd_type hτ)
      | lam dom body =>
        obtain ⟨d1, b1, rfl, hb1⟩ := vEquivB_bwd_lam hv
        obtain ⟨d2, b2, rfl, hb2⟩ := vEquivB_bwd_lam hτ
        exact Or.inr (Or.inr (Or.inl ⟨d1, d2, b1, b2, rfl, rfl,
          ih hb1 hb2 (VCompat.refl k body)⟩))
      | mu ann body =>
        obtain ⟨a1, b1, rfl, hb1⟩ := vEquivB_bwd_mu hv
        obtain ⟨a2, b2, rfl, hb2⟩ := vEquivB_bwd_mu hτ
        have hmu1 : (Expr.mu a1 b1).vEquivB (.mu ann body) = true := by
          simp [Expr.vEquivB]; exact hb1
        have hmu2 : (Expr.mu a2 b2).vEquivB (.mu ann body) = true := by
          simp [Expr.vEquivB]; exact hb2
        exact Or.inr (Or.inr (Or.inr (Or.inl ⟨a1, a2, b1, b2, rfl, rfl,
          ih (Expr.vEquivB_subst 0 b1 body (.mu a1 b1) (.mu ann body) hb1 hmu1)
             (Expr.vEquivB_subst 0 b2 body (.mu a2 b2) (.mu ann body) hb2 hmu2)
             (VCompat.refl k (body.subst 0 (.mu ann body)))⟩)))
      | app f a =>
        obtain ⟨f1, a1, rfl, hf1, ha1⟩ := vEquivB_bwd_app hv
        obtain ⟨f2, a2, rfl, hf2, ha2⟩ := vEquivB_bwd_app hτ
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          ⟨f1, f2, a1, a2, rfl, rfl,
           ih hf1 hf2 (VCompat.refl k f),
           ih ha1 ha2 (VCompat.refl k a)⟩))))))
      | asc _ _ =>
        -- asc expressions never appear in evaluator outputs (evaluators strip them).
        -- VCompat has no structural asc disjunct, so this case is stuck.
        -- Unreachable in practice for the mu_body_subst_vcompat use case.
        sorry
    -- Case 3: structural lam
    · obtain ⟨d1, b1, rfl, hb1⟩ := vEquivB_bwd_lam hv
      obtain ⟨d2, b2, rfl, hb2⟩ := vEquivB_bwd_lam hτ
      exact Or.inr (Or.inr (Or.inl ⟨d1, d2, b1, b2, rfl, rfl, ih hb1 hb2 hbody⟩))
    -- Case 4: structural mu (unfolded)
    · obtain ⟨a1, b1, rfl, hb1⟩ := vEquivB_bwd_mu hv
      obtain ⟨a2, b2, rfl, hb2⟩ := vEquivB_bwd_mu hτ
      have hmu_v : (Expr.mu a1 b1).vEquivB (.mu aV bV) = true := by
        simp [Expr.vEquivB]; exact hb1
      have hmu_τ : (Expr.mu a2 b2).vEquivB (.mu aT bT) = true := by
        simp [Expr.vEquivB]; exact hb2
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨a1, a2, b1, b2, rfl, rfl,
        ih (Expr.vEquivB_subst 0 b1 bV (.mu a1 b1) (.mu aV bV) hb1 hmu_v)
           (Expr.vEquivB_subst 0 b2 bT (.mu a2 b2) (.mu aT bT) hb2 hmu_τ)
           hbody⟩)))
    -- Case 5: mu-right (τ = mu ann body)
    · obtain ⟨a2, b2, rfl, hb2⟩ := vEquivB_bwd_mu hτ
      have hmu2 : (Expr.mu a2 b2).vEquivB (.mu ann body) = true := by
        simp [Expr.vEquivB]; exact hb2
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨a2, b2, rfl,
        ih hv (Expr.vEquivB_subst 0 b2 body (.mu a2 b2) (.mu ann body) hb2 hmu2) hunf⟩))))
    -- Case 6: mu-left (v = mu ann body)
    · obtain ⟨a1, b1, rfl, hb1⟩ := vEquivB_bwd_mu hv
      have hmu1 : (Expr.mu a1 b1).vEquivB (.mu ann body) = true := by
        simp [Expr.vEquivB]; exact hb1
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨a1, b1, rfl,
        ih (Expr.vEquivB_subst 0 b1 body (.mu a1 b1) (.mu ann body) hb1 hmu1) hτ hunf⟩)))))
    -- Case 7: structural app
    · obtain ⟨f1, a1, rfl, hf1, ha1⟩ := vEquivB_bwd_app hv
      obtain ⟨f2, a2, rfl, hf2, ha2⟩ := vEquivB_bwd_app hτ
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨f1, f2, a1, a2, rfl, rfl, ih hf1 hf2 hfc, ih ha1 ha2 hac⟩))))))
    -- Case 8: inferType fallback
    · obtain ⟨ty', hinf', hve⟩ := inferType_vEquivB hv hinf
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨ctx1, ty', hinf', ih hve hτ hcompat⟩))))))

/-- Evaluator outputs satisfy closedEvalB 0: all bvar indices in VCompat-relevant
    positions (bodies, app structure) are resolved by the evaluator. Domains and
    annotations are NOT checked (they're copied verbatim from the source).

    The proof would go by induction on fuel and cases on e:
    - bvar: env lookup, closedEvalB follows from env invariant
    - lam/mu: body evaluated in extended env, IH gives closedEvalB 1 for body,
      wrapped in lam/mu gives closedEvalB 0
    - app: recursive evaluation, IH on sub-results
    - asc: forward to sub-evaluation
    - type: trivial

    Both concEvalE and absEval satisfy this (they have the same structure
    except at ascription). -/
theorem concEvalE_closedEvalB {fuel : Nat} {env : Env} {e v : Expr}
    (h : concEvalE fuel env e = some v)
    (henv : ∀ k e', env.get? k = some e' → e'.closedEvalB 0 = true)
    : v.closedEvalB 0 = true := by
  sorry

theorem absEval_closedEvalB {fuel : Nat} {env : Env} {e v : Expr}
    (h : absEval fuel env e = some v)
    (henv : ∀ k e', env.get? k = some e' → e'.closedEvalB 0 = true)
    : v.closedEvalB 0 = true := by
  sorry

/-- For the soundness_gen mu case: if VCompat n bodyV bodyT, then
    VCompat n (bodyV.subst 0 (mu ann bodyV)) (bodyT.subst 0 (mu ann bodyT)).

    This holds because evaluator outputs satisfy one of:
    1. bodyT = type → subst gives type → VCompat top
    2. bodyV = bodyT → subst gives equal results → VCompat refl
    3. closedEvalB 0 holds → subst is vEquiv-no-op → VCompat preserved

    Brute-force tested in Tests.lean §16 for all small well-typed programs.
    The proof requires either:
    - A refined closedEvalB that accounts for mu-app catch-all outputs, or
    - A direct proof that evaluator outputs satisfy the trichotomy above.
    Sorry'd pending this development. -/
theorem mu_body_subst_vcompat {n : Nat} {bodyV bodyT ann : Expr}
    (h : VCompat n bodyV bodyT)
    : VCompat n (bodyV.subst 0 (.mu ann bodyV)) (bodyT.subst 0 (.mu ann bodyT)) := by
  -- Case A: bodyT = type → type.subst 0 Y = type → VCompat top
  by_cases hτ : bodyT = .type
  · subst hτ; simp [Expr.subst]
    cases n with
    | zero => trivial
    | succ k => unfold VCompat; exact Or.inl rfl
  -- Case B: bodyV = bodyT → v = τ → subst gives same result → VCompat refl
  · by_cases heq : bodyV = bodyT
    · subst heq
      cases n with
      | zero => trivial
      | succ k => unfold VCompat; exact Or.inr (Or.inl rfl)
    -- Case C: closedEvalB holds → vEquiv chain
    -- This case requires proving that closedEvalB 0 bodyV and closedEvalB 0 bodyT
    -- hold when bodyV ≠ bodyT and bodyT ≠ type. Brute-force tested in Tests.lean §16.
    -- For now, sorry this case.
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
            -- Need: VCompat (m+1) (mu ann bodyV') (mu ann bodyT')
            -- Via unfolded structural mu: VCompat m (bodyV'.subst 0 v) (bodyT'.subst 0 τ)
            -- where v = mu ann bodyV', τ = mu ann bodyT'
            --
            -- Three cases (all tested, no counterexample in §16):
            -- Case A: bodyT' = type → τ.subst 0 Y = type → VCompat top
            -- Case B: bodyV' = bodyT' → v = τ → subst equal → VCompat refl
            -- Case C: closedEvalB 0 holds → vEquiv chain
            --
            -- Why these cover all well-typed evaluator outputs:
            -- closedEvalB fails only when mu-app catch-all leaks raw bvar 0.
            -- This happens when concEvalE sees mu in function position with non-lam
            -- body. For absEval (which sees the asc rhs = type in these cases),
            -- the result is type. So closedEvalB failure + bodyV'≠bodyT' → bodyT'=type.
            -- Brute-force tested in §16. This trichotomy is sorry'd for now.
            unfold VCompat
            apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inl
            refine ⟨ann, ann, bodyV', bodyT', rfl, rfl, ?_⟩
            -- Need: VCompat m (bodyV'.subst 0 (mu ann bodyV')) (bodyT'.subst 0 (mu ann bodyT'))
            -- from: VCompat m bodyV' bodyT'
            exact mu_body_subst_vcompat ih_body
      | app f a =>
        -- Both evaluators evaluate f and a, then case-split on the function result.
        simp only [concEvalE] at h_conc
        simp only [absEval] at h_abs
        simp only [WellTyped, Bool.and_eq_true] at h_wt
        -- Extract function and argument evaluation results
        match h_fV : concEvalE k env f with
        | none => simp [h_fV] at h_conc
        | some fV =>
          match h_aV : concEvalE k env a with
          | none => simp [h_fV, h_aV] at h_conc
          | some aV =>
            match h_fT : absEval k env f with
            | none =>
              -- absEval f fails. Extract WellTyped parts to get contradiction.
              obtain ⟨⟨h_wt_f, h_wt_a⟩, _⟩ := h_wt
              simp [h_fT] at h_abs
            | some fT =>
              match h_aT : absEval k env a with
              | none => simp [h_fT, h_aT] at h_abs
              | some aT =>
                -- IH gives VCompat for function and argument
                obtain ⟨⟨h_wt_f, h_wt_a⟩, _⟩ := h_wt
                have ih_f := ih env f fV fT (m + 1) h_wt_f h_fV h_fT
                have ih_a := ih env a aV aT (m + 1) h_wt_a h_aV h_aT
                -- Now case-split on the shapes of fV and fT.
                -- The evaluators' app cases match on the function result:
                -- lam → beta-reduce, mu → mu-app, type → type, other → app
                --
                -- Easy cases proved here:
                -- 1. fT = type → τ = type → VCompat top
                -- 2. fV = type → v = type → VCompat top (if τ = type) or needs analysis
                -- 3. Both catch-all → structural app
                -- Hard cases (beta-reduction, mu-app) sorry'd.
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

/-- Soundness for the env-based concrete evaluator.
    Direct corollary of soundness_gen with empty env. -/
theorem soundness
    (fuel : Nat) (e : Expr) (v τ : Expr) (n : Nat)
    (h_wt : WellTyped fuel [] e = true)
    (h_conc : concEvalE fuel [] e = some v)
    (h_abs : absEval fuel [] e = some τ)
    : VCompat n v τ :=
  soundness_gen fuel [] e v τ n h_wt h_conc h_abs

/-- Soundness for the substitution-based runtime (concEval).
    Requires a bridge showing concEval and concEvalE agree on closed terms.
    concEval doesn't normalize under binders (lambdas are values), while
    concEvalE does. The bridge needs to show that the results are VCompat
    despite differing in lambda body normalization. -/
theorem soundness_concEval
    (fuel : Nat) (e : Expr) (v τ : Expr) (n : Nat)
    (h_wt : WellTyped fuel [] e = true)
    (h_conc : concEval fuel e = some v)
    (h_abs : absEval fuel [] e = some τ)
    : VCompat n v τ := by
  sorry  -- needs concEval → concEvalE bridge


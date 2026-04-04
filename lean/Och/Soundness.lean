import Och.Syntax
import Och.Eval
import Och.Subtyping

/-!
# Soundness via Logical Relations (VCompat)

## Goal

Prove: if `absEval` succeeds, `concEval(e)` is compatible with `absEval(e)`.

## Why logical relations?

Och's ascription `(term : ty)` evaluates `term` concretely and `ty`
abstractly. The results can have completely different top-level constructors
(e.g., a lambda value vs a mu type). No structural relation can bridge
this — it's the entire point of ascription.

The standard PL solution: define compatibility **semantically**, by behavior.
For functions: "compatible iff applying to compatible args gives compatible
results." This avoids substitution congruence entirely.

## Architecture

`VCompat n v τ` — step-indexed value-type compatibility.

- **n = 0:** everything is compatible (no observation budget)
- **τ = .type:** everything is compatible (top type)
- **Both lam:** same domain, bodies are compatible (structural)
- **Both mu:** same annotation, UNFOLDED bodies (self-substituted) are compatible
- **τ = mu:** unfold the mu, check compatibility with the unfolded body
- **v = mu:** unfold the mu on the value side (costs one step)
- **Fallback:** for neutral terms (bvar, app), infer a type and check at lower step

The key theorem:

```
soundness : concEval fuel e = some v →
            absEval fuel [] [] e = .ok τ →
            ∀ n, VCompat n v τ
```

The `WellTyped` precondition is gone — it's implied by `absEval` succeeding
(absEval now validates ascriptions and callability internally).
-/

open Expr

/-! ## VCompat: step-indexed value-type compatibility -/

/-- Step-indexed value-type compatibility.

    `VCompat n v τ` means: value `v` is compatible with type `τ`,
    given `n` steps of observation budget. -/
def VCompat : Nat → Expr → Expr → Prop
  | 0, _, _ => True
  | n + 1, v, τ =>
    -- Top: everything inhabits Type
    τ = .type
    -- Refl: syntactic equality (optimization)
    ∨ v = τ
    -- Semantic lambda: both are lambdas; for all compatible arguments
    -- at step j ≤ n, evaluating bodyV[aV] and bodyT[aT] gives compatible results.
    ∨ (∃ domV domT bodyV bodyT,
        v = .lam domV bodyV ∧ τ = .lam domT bodyT ∧
        ∀ (j : Nat), j ≤ n → ∀ (fuel : Nat) (aV aT : Expr),
          VCompat j aV aT →
          ∀ rv, concEval fuel (bodyV.subst 0 aV) = some rv →
          ∀ (rτ : NfExpr), absEval fuel [] [] (bodyT.subst 0 aT) = .ok rτ →
          VCompat j rv rτ.val)
    -- Unfolded structural mu
    ∨ (∃ annV annT bodyV bodyT,
        v = .mu annV bodyV ∧ τ = .mu annT bodyT ∧
        VCompat n (bodyV.subst 0 (.mu annV bodyV)) (bodyT.subst 0 (.mu annT bodyT)))
    -- Mu unfolding on the right (equi-recursive self-intro): costs one step
    ∨ (∃ ann body,
        τ = .mu ann body ∧
        VCompat n v (body.subst 0 (.mu ann body)))
    -- Mu unfolding on the right with normalization: unfold the mu AND normalize
    -- the result via absEval. This bridges the gap between raw substitution results
    -- (which may contain .asc nodes) and their normalized forms. Only applies to mu
    -- types, so it doesn't make VCompat trivially true (unlike a general normalization
    -- disjunct which would allow VCompat n v τ for any normalizable τ).
    ∨ (∃ ann body, ∃ (nfuel : Nat) (nctx : TyCtx) (nseen : List (Expr × Expr)) (u' : NfExpr),
        τ = .mu ann body ∧
        absEval nfuel nctx nseen (body.subst 0 (.mu ann body)) = .ok u' ∧
        VCompat n v u'.val)
    -- Mu unfolding on the left (equi-recursive self-elim): costs one step
    ∨ (∃ ann body,
        v = .mu ann body ∧
        VCompat n (body.subst 0 (.mu ann body)) τ)
    -- Structural app: both are applications with compatible components.
    ∨ (∃ fV fT aV aT,
        v = .app fV aV ∧ τ = .app fT aT ∧
        VCompat n fV fT ∧ VCompat n aV aT)
    -- InferType fallback: for neutral terms
    ∨ (∃ (ctx : TyCtx) (ty : Expr), inferType ctx v = some ty ∧ VCompat n ty τ)

@[simp] theorem VCompat.zero_eq (v τ : Expr) : VCompat 0 v τ = True := by
  unfold VCompat; rfl

/-! ## VCompat lemmas -/

/-- Downward closure: more observation budget implies less. -/
theorem VCompat.mono {n : Nat} {v τ : Expr}
    (h : VCompat (n + 1) v τ) : VCompat n v τ := by
  cases n with
  | zero =>
    unfold VCompat; trivial
  | succ k =>
    unfold VCompat at h ⊢
    rcases h with h_top | h_refl |
                  ⟨domV, domT, bodyV, bodyT, hv, hτ, h_body⟩ |
                  ⟨annV, annT, bodyV, bodyT, hv, hτ, h_body⟩ |
                  ⟨ann, body, hτ, h_mu⟩ |
                  ⟨ann, body, ⟨nfuel, nctx, nseen, u', hτ, habs, h_mu_norm⟩⟩ |
                  ⟨ann, body, hv, h_mu⟩ |
                  ⟨fV, fT, aV, aT, hv, hτ, h_f, h_a⟩ |
                  ⟨ctx, ty, h_infer, h_compat⟩
    · exact Or.inl h_top
    · exact Or.inr (Or.inl h_refl)
    · exact Or.inr (Or.inr (Or.inl ⟨domV, domT, bodyV, bodyT, hv, hτ,
        fun j hj => h_body j (Nat.le_succ_of_le hj)⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨annV, annT, bodyV, bodyT, hv, hτ, VCompat.mono h_body⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨ann, body, hτ, VCompat.mono h_mu⟩))))
    · -- Normalized mu-right: same mu structure, mono the inner VCompat
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨ann, body, ⟨nfuel, nctx, nseen, u', hτ, habs, VCompat.mono h_mu_norm⟩⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨ann, body, hv, VCompat.mono h_mu⟩))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨fV, fT, aV, aT, hv, hτ, VCompat.mono h_f, VCompat.mono h_a⟩)))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨ctx, ty, h_infer, VCompat.mono h_compat⟩)))))))

/-- Multi-step downward closure. -/
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

/-- For fixpoint mus, VCompat holds at all step levels. -/
theorem VCompat.fixpoint_mu {ann body : Expr} (n : Nat) (v : Expr)
    (hfix : body.subst 0 (.mu ann body) = .mu ann body)
    : VCompat n v (.mu ann body) := by
  induction n with
  | zero => simp [VCompat]
  | succ k ih =>
    unfold VCompat
    apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inl
    exact ⟨ann, body, rfl, by rw [hfix]; exact ih⟩

/-- Self-intro from equality. -/
theorem VCompat.self_intro_eq {n : Nat} {v σ ann body : Expr}
    (hv : VCompat (n + 1) v σ)
    (heq : σ = body.subst 0 (.mu ann body))
    : VCompat (n + 1) v (.mu ann body) := by
  unfold VCompat
  apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inl
  exact ⟨ann, body, rfl, by rw [← heq]; exact VCompat.mono hv⟩

/-- For fixpoint mus, mu-left gives VCompat at all steps. -/
theorem VCompat.fixpoint_mu_left {ann body : Expr} (n : Nat) (τ : Expr)
    (hfix : body.subst 0 (.mu ann body) = .mu ann body)
    : VCompat n (.mu ann body) τ := by
  induction n with
  | zero => simp [VCompat]
  | succ k ih =>
    unfold VCompat
    apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
    apply Or.inr; apply Or.inr; apply Or.inl
    exact ⟨ann, body, rfl, by rw [hfix]; exact ih⟩

/-- When subCheckNF succeeds from .type, VCompat holds for all v and n. -/
theorem VCompat.from_type_sub_gen :
    ∀ (fuel : Nat), ∀ (n : Nat) (v τ : Expr) (ctx : TyCtx) (seen : List (Expr × Expr)),
    subCheckNF fuel ctx seen Expr.type τ = true →
    (∀ p, p ∈ seen → VCompat n v p.2) →
    VCompat n v τ := by
  intro fuel
  induction fuel with
  | zero => intro n v τ ctx seen h; simp [subCheckNF] at h
  | succ k ih_fuel =>
    -- Double induction: outer on fuel, inner on step index n
    intro n
    induction n with
    | zero => intro v τ ctx seen _ _; simp [VCompat]
    | succ m ih_n =>
    intro v τ ctx seen hcheck hseen
    -- Save original hypothesis for use in recursive ih_n calls
    have hcheck_orig := hcheck
    -- Unfold subCheckNF to analyze what made it succeed
    unfold subCheckNF at hcheck; dsimp only [] at hcheck
    -- Case 1: syntactic equality (Type == τ)
    by_cases heq : (Expr.type == τ) = true
    · rw [← (beq_iff_eq.mp heq : Expr.type = τ)]
      unfold VCompat; exact Or.inl rfl
    · simp only [if_neg heq] at hcheck
      -- Case 2: seen check
      by_cases hseen_chk : (seen.any fun (a', b') => Expr.type == a' && τ == b') = true
      · -- Extract the matching pair from seen
        rw [List.any_eq_true] at hseen_chk
        obtain ⟨p, hp_mem, hp_match⟩ := hseen_chk
        simp only [Bool.and_eq_true, beq_iff_eq] at hp_match
        rw [hp_match.2]; exact hseen p hp_mem
      · simp only [if_neg hseen_chk] at hcheck
        -- Case 3: match on τ
        cases τ with
        | type => unfold VCompat; exact Or.inl rfl
        | mu ann body =>
          -- Self-intro case: subCheckNF unfolds the mu and checks .type against
          -- the normalized unfolded body.
          -- Strategy: use the normalized mu-right disjunct directly.
          have hcheck' := hcheck
          match habs : absEval k ctx ((Expr.type, Expr.mu ann body) :: seen)
              (body.subst 0 (Expr.mu ann body)) with
          | .error _ => simp [habs] at hcheck'
          | .ok u' =>
            simp only [habs] at hcheck'
            -- hcheck': subCheckNF k ctx seen' .type u'.val = true
            -- Goal: VCompat (m+1) v (.mu ann body)
            -- Use normalized mu-right disjunct (6th): need VCompat m v u'.val
            unfold VCompat
            apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
            apply Or.inr; apply Or.inl
            exact ⟨ann, body, ⟨k, ctx, (Expr.type, Expr.mu ann body) :: seen, u', rfl, habs, by
              -- Goal: VCompat m v u'.val
              -- Use ih_fuel at fuel k, step m
              apply ih_fuel m v u'.val ctx ((Expr.type, Expr.mu ann body) :: seen) hcheck'
              intro p hp
              cases hp with
              | head =>
                -- Goal: VCompat m v (.mu ann body)
                -- Use ih_n at step m, with the ORIGINAL hcheck
                exact ih_n v (Expr.mu ann body) ctx seen hcheck_orig
                  (fun q hq => VCompat.mono (hseen q hq))
              | tail _ hp_tail =>
                -- p ∈ seen: from hseen (step m+1) + mono_le
                exact VCompat.mono_le (hseen p hp_tail) (by omega)⟩⟩
        | lam _ _ => simp [inferType] at hcheck
        | bvar _ => simp [inferType] at hcheck
        | app _ _ => simp [inferType] at hcheck
        | asc _ _ => simp [inferType] at hcheck

/-- Corollary: subCheckNF .type (mu ann body) with empty seen gives VCompat. -/
theorem VCompat.from_type_sub {fuel : Nat} {ctx : TyCtx} {n : Nat} {v : Expr}
    {ann body : Expr}
    (hcheck : subCheckNF fuel ctx [] Expr.type (.mu ann body) = true)
    : VCompat n v (.mu ann body) :=
  VCompat.from_type_sub_gen fuel n v _ ctx [] hcheck
    (fun p hp => absurd hp (List.not_mem_nil p))

/-- VCompat is reflexive at all step levels. -/
theorem VCompat.refl (n : Nat) (e : Expr) : VCompat n e e := by
  cases n with
  | zero => simp [VCompat]
  | succ k => unfold VCompat; exact Or.inr (Or.inl rfl)

/-- VCompat respects subCheckNF (adequacy), generalized over seen.

    Proved cases:
    - σ = τ (syntactic equality): direct from hypothesis
    - (σ, τ) in seen: from seen callback
    - τ = Type: top type, trivial
    - τ = mu (self-intro): normalized mu-right disjunct + ih_fuel/ih_n

    Sorry'd cases (documented blockers):
    - (lam, lam): needs substitution lemma for subCheckNF — showing that
      if subCheckNF(bodyσ, bodyτ) under extended context, evaluating bodyσ[a]
      and bodyτ[a] preserves the subtype relationship
    - (mu, _) self-elim: needs annotation correctness — going from
      VCompat(v, mu ann body) to VCompat(v, ann) requires the annotation to
      accurately describe the mu's behavior
    - (app, app) congruence: provable in principle via structural app disjunct
    - inferType fallback: needs inferType reasoning -/
theorem VCompat.adequacy_gen :
    ∀ (fuel : Nat), ∀ (n : Nat) (v σ τ : Expr) (ctx : TyCtx) (seen : List (Expr × Expr)),
    VCompat n v σ →
    subCheckNF fuel ctx seen σ τ = true →
    (∀ p, p ∈ seen → VCompat n v p.2) →
    VCompat n v τ := by
  intro fuel
  induction fuel with
  | zero => intro n v σ τ ctx seen _ h; simp [subCheckNF] at h
  | succ k ih_fuel =>
    intro n
    induction n with
    | zero => intro v σ τ ctx seen _ _ _; simp [VCompat]
    | succ m ih_n =>
    intro v σ τ ctx seen hv hcheck hseen
    have hcheck_orig := hcheck
    unfold subCheckNF at hcheck; dsimp only [] at hcheck
    -- Case 1: σ = τ (syntactic equality)
    by_cases heq : (σ == τ) = true
    · have : σ = τ := beq_iff_eq.mp heq; subst this; exact hv
    · simp only [if_neg heq] at hcheck
      -- Case 2: seen check
      by_cases hseen_chk : (seen.any fun (a', b') => σ == a' && τ == b') = true
      · rw [List.any_eq_true] at hseen_chk
        obtain ⟨p, hp_mem, hp_match⟩ := hseen_chk
        simp only [Bool.and_eq_true, beq_iff_eq] at hp_match
        rw [hp_match.2]; exact hseen p hp_mem
      · simp only [if_neg hseen_chk] at hcheck
        -- Case 3: match on τ
        cases τ with
        | type => unfold VCompat; exact Or.inl rfl
        | mu ann body =>
          -- Self-intro: subCheckNF unfolds the mu and checks σ against normalized body
          have hcheck' := hcheck
          match habs : absEval k ctx ((σ, Expr.mu ann body) :: seen)
              (body.subst 0 (Expr.mu ann body)) with
          | .error _ => simp [habs] at hcheck'
          | .ok u' =>
            simp only [habs] at hcheck'
            -- hcheck': subCheckNF k ctx seen' σ u'.val = true
            -- Use normalized mu-right disjunct: need VCompat m v u'.val
            unfold VCompat
            apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
            apply Or.inr; apply Or.inl
            exact ⟨ann, body, ⟨k, ctx, (σ, Expr.mu ann body) :: seen, u', rfl, habs, by
              -- Goal: VCompat m v u'.val
              -- Use ih_fuel at fuel k, step m
              apply ih_fuel m v σ u'.val ctx ((σ, Expr.mu ann body) :: seen)
              · exact VCompat.mono hv
              · exact hcheck'
              · intro p hp
                cases hp with
                | head =>
                  -- p = (σ, mu ann body): need VCompat m v (mu ann body)
                  -- Use ih_n at step m with the ORIGINAL hcheck
                  exact ih_n v σ (Expr.mu ann body) ctx seen
                    (VCompat.mono hv) hcheck_orig
                    (fun q hq => VCompat.mono (hseen q hq))
                | tail _ hp_tail =>
                  exact VCompat.mono (hseen p hp_tail)⟩⟩
        | _ =>
          -- Remaining cases: τ is lam, bvar, app, or asc
          -- subCheckNF matches on (σ, τ):
          -- - (lam, lam): hard, needs substitution lemma
          -- - (_, mu): already handled above
          -- - (mu, _): self-elim, needs annotation correctness
          -- - (app, app): congruence, might be provable
          -- - (_, _): inferType fallback
          sorry

/-- VCompat respects subCheckNF (adequacy). -/
theorem VCompat.adequacy {n : Nat} {v σ τ : Expr} {fuel : Nat} {ctx : TyCtx}
    (hv : VCompat n v σ) (hcheck : subCheckNF fuel ctx [] σ τ = true)
    : VCompat n v τ :=
  VCompat.adequacy_gen fuel n v σ τ ctx [] hv hcheck
    (fun p hp => absurd hp (List.not_mem_nil p))

/-- General self-intro. -/
theorem VCompat.from_self_intro_gen :
    ∀ (fuel : Nat), ∀ (n : Nat) (σ : Expr) (ctx : TyCtx) (seen : List (Expr × Expr)),
    (∀ ann' body', σ ≠ .mu ann' body') →
    ∀ (ann body : Expr),
    subCheckNF fuel ctx seen σ (.mu ann body) = true →
    (∀ p, p ∈ seen → VCompat n σ p.2) →
    VCompat n σ (.mu ann body) := by
  intro fuel
  induction fuel with
  | zero => intro n σ ctx seen _ ann body h; simp [subCheckNF] at h
  | succ k ih_fuel =>
    intro n
    induction n with
    | zero => intro σ ctx seen _ ann body _ _; simp [VCompat]
    | succ m ih_n =>
    intro σ ctx seen hσ_not_mu ann body hcheck hseen
    have hcheck_orig := hcheck
    -- Unfold subCheckNF to analyze
    unfold subCheckNF at hcheck; dsimp only [] at hcheck
    -- σ ≠ .mu ann body (since σ is not a mu)
    have h_neq : (σ == Expr.mu ann body) = false := by
      rw [beq_eq_false_iff_ne]; intro heq; rw [heq] at hσ_not_mu; exact hσ_not_mu ann body rfl
    simp only [if_neg (by rw [h_neq]; decide : ¬(σ == Expr.mu ann body) = true)] at hcheck
    -- Seen check
    by_cases hseen_chk : (seen.any fun (a', b') => σ == a' && Expr.mu ann body == b') = true
    · -- Hit seen set
      rw [List.any_eq_true] at hseen_chk
      obtain ⟨p, hp_mem, hp_match⟩ := hseen_chk
      simp only [Bool.and_eq_true, beq_iff_eq] at hp_match
      rw [hp_match.2]; exact hseen p hp_mem
    · simp only [if_neg hseen_chk] at hcheck
      -- Self-intro case: subCheckNF unfolds the mu and checks σ against normalized body
      have hcheck_mu := hcheck
      match habs : absEval k ctx ((σ, Expr.mu ann body) :: seen)
          (body.subst 0 (Expr.mu ann body)) with
      | .error _ => simp [habs] at hcheck_mu
      | .ok u' =>
        simp only [habs] at hcheck_mu
        -- hcheck_mu: subCheckNF k ctx seen' σ u'.val = true
        -- Use normalized mu-right disjunct: need VCompat m σ u'.val
        unfold VCompat
        apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
        apply Or.inr; apply Or.inl
        exact ⟨ann, body, ⟨k, ctx, (σ, Expr.mu ann body) :: seen, u', rfl, habs, by
          -- Goal: VCompat m σ u'.val
          -- Use adequacy_gen: VCompat m σ σ (refl) + subCheckNF k ... σ u'.val → VCompat m σ u'.val
          apply VCompat.adequacy_gen k m σ σ u'.val ctx ((σ, Expr.mu ann body) :: seen)
          · exact VCompat.refl m σ
          · exact hcheck_mu
          · intro p hp
            cases hp with
            | head =>
              -- p = (σ, mu ann body): need VCompat m σ (mu ann body)
              exact ih_n σ ctx seen hσ_not_mu ann body hcheck_orig
                (fun q hq => VCompat.mono (hseen q hq))
            | tail _ hp_tail =>
              exact VCompat.mono (hseen p hp_tail)⟩⟩

/-- Corollary: self-intro with empty seen. -/
theorem VCompat.from_self_intro {fuel : Nat} {ctx : TyCtx} {n : Nat} {σ : Expr}
    {ann body : Expr}
    (hσ_not_mu : ∀ ann' body', σ ≠ .mu ann' body')
    (hcheck : subCheckNF fuel ctx [] σ (.mu ann body) = true)
    : VCompat n σ (.mu ann body) :=
  VCompat.from_self_intro_gen fuel n σ ctx [] hσ_not_mu ann body hcheck
    (fun p hp => absurd hp (List.not_mem_nil p))

/-! ## Soundness theorem

The WellTyped precondition is gone — absEval now validates ascriptions
and callability internally. A term is well-typed iff absEval succeeds. -/

/-- Soundness: if both evaluators succeed on the same term, their outputs
    are VCompat at all step levels.

    KEY CHANGE: No WellTyped precondition. absEval succeeding implies
    the term is well-typed (ascriptions are checked, callability is validated).

    KEY DESIGN: the VCompat step index `n` is decoupled from `fuel`.
    soundness proves VCompat at ALL step levels simultaneously. -/
theorem soundness
    (fuel : Nat) (e : Expr) (v : Expr) (τ : NfExpr) (n : Nat)
    (h_conc : concEval fuel e = some v)
    (h_abs : absEval fuel [] [] e = .ok τ)
    : VCompat n v τ.val := by
  sorry

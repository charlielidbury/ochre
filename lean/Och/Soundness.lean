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
    -- at step j ≤ n, concEval of bodyV[aV] is compatible with bodyT[aT].
    -- NOTE: no absEval on the type side. The raw substitution bodyT.subst 0 aT
    -- is used directly. This breaks a circular dependency: soundness_open's lam
    -- case can use the IH on body + composition lemma to get VCompat directly,
    -- without needing absEval_preserves. The cost: the app case of soundness
    -- needs absEval_preserves to bridge from bodyT.subst 0 aT to the absEval
    -- result. But the app case is already sorry'd.
    ∨ (∃ domV domT bodyV bodyT,
        v = .lam domV bodyV ∧ τ = .lam domT bodyT ∧
        ∀ (j : Nat), j ≤ n → ∀ (aV aT : Expr),
          (match aV with | .lam _ _ | .type | .mu _ _ => True | _ => False) →
          VCompat j aV aT →
          ∀ (fuel : Nat) rv, concEval fuel (bodyV.subst 0 aV) = some rv →
          VCompat j rv (bodyT.subst 0 aT))
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
    -- Asc-left erasure: (e : τ) as a value behaves like `e` at runtime.
    -- concEval erases ascriptions, so the runtime value of `asc term ty` is
    -- the runtime value of `term`. This disjunct reflects that in VCompat.
    -- Needed because mu-left unfolding can introduce asc nodes in the value
    -- position (body may contain asc from let-bindings etc.).
    ∨ (∃ term tyAsc, v = .asc term tyAsc ∧ VCompat n term τ)

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
                  ⟨ctx, ty, h_infer, h_compat⟩ |
                  ⟨term, tyAsc, hv, h_asc⟩
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
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨ctx, ty, h_infer, VCompat.mono h_compat⟩))))))))
    · -- Asc-left: mono the inner VCompat
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨term, tyAsc, hv, VCompat.mono h_asc⟩))))))))

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

/-- VCompat(n, v, bvar k) implies VCompat(n, v, ty) when inferType looks up
    bvar k to ty. Bridges the inferType fallback in subCheckNF for bvar terms. -/
theorem VCompat.bvar_inferType {n : Nat} {v : Expr} {k : Nat} {ctx : TyCtx} {ty : Expr}
    (hv : VCompat n v (.bvar k))
    (hinf : inferType ctx (.bvar k) = some ty)
    : VCompat n v ty := by
  induction n generalizing v with
  | zero => simp [VCompat]
  | succ m ih =>
    unfold VCompat at hv
    rcases hv with
      h_type | h_refl |
      ⟨_, _, _, _, _, hτ_lam, _⟩ |
      ⟨_, _, _, _, _, hτ_mu, _⟩ |
      ⟨_, _, hτ_mu5, _⟩ |
      ⟨_, _, ⟨_, _, _, _, hτ_mu6, _, _⟩⟩ |
      ⟨ann, body, hv_mu, hv_body⟩ |
      ⟨_, _, _, _, _, hτ_app, _, _⟩ |
      ⟨ctx', ty', hinf_v, hcompat⟩ |
      ⟨term, tyAsc, hv_asc, h_asc⟩
    · cases h_type
    · subst h_refl
      unfold VCompat
      apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
      apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
      exact Or.inl ⟨ctx, ty, hinf, VCompat.refl m ty⟩
    · cases hτ_lam
    · cases hτ_mu
    · cases hτ_mu5
    · cases hτ_mu6
    · unfold VCompat
      apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
      apply Or.inr; apply Or.inr; apply Or.inl
      exact ⟨ann, body, hv_mu, ih hv_body⟩
    · cases hτ_app
    · unfold VCompat
      apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
      apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
      exact Or.inl ⟨ctx', ty', hinf_v, ih hcompat⟩
    · -- Asc-left: v = asc term tyAsc, VCompat m term (bvar k)
      -- Recurse: bvar_inferType on the inner term
      unfold VCompat
      apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
      apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
      exact Or.inr ⟨term, tyAsc, hv_asc, ih h_asc⟩

/-- VCompat(n, v, app f a) implies VCompat(n, v, ty) when inferType infers
    app f a to ty. Bridges the inferType fallback in subCheckNF for app terms.
    Analogous to bvar_inferType but for application expressions.
    SORRY: structural app case (v = app fV aV with VCompat components). -/
theorem VCompat.app_inferType {n : Nat} {v f a : Expr} {ctx : TyCtx} {ty : Expr}
    (hv : VCompat n v (.app f a))
    (hinf : inferType ctx (.app f a) = some ty)
    : VCompat n v ty := by
  induction n generalizing v with
  | zero => simp [VCompat]
  | succ m ih =>
    unfold VCompat at hv
    rcases hv with
      h_type | h_refl |
      ⟨_, _, _, _, _, hτ_lam, _⟩ |
      ⟨_, _, _, _, _, hτ_mu, _⟩ |
      ⟨_, _, hτ_mu5, _⟩ |
      ⟨_, _, ⟨_, _, _, _, hτ_mu6, _, _⟩⟩ |
      ⟨ann, body, hv_mu, hv_body⟩ |
      ⟨fV, fT, aV, aT, hv_eq, hτ_eq, h_f, h_a⟩ |
      ⟨ctx', ty', hinf_v, hcompat⟩ |
      ⟨term, tyAsc, hv_asc, h_asc⟩
    · cases h_type   -- app ≠ type
    · -- Refl: v = app f a. Use inferType disjunct.
      subst h_refl
      unfold VCompat
      apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
      apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
      exact Or.inl ⟨ctx, ty, hinf, VCompat.refl m ty⟩
    · cases hτ_lam   -- app ≠ lam
    · cases hτ_mu    -- app ≠ mu
    · cases hτ_mu5   -- app ≠ mu
    · cases hτ_mu6   -- app ≠ mu
    · -- Mu-left: v = mu ann body, VCompat m (body.subst) (app f a)
      unfold VCompat
      apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
      apply Or.inr; apply Or.inr; apply Or.inl
      exact ⟨ann, body, hv_mu, ih hv_body⟩
    · -- Structural app: v = app fV aV, VCompat m fV f, VCompat m aV a
      -- HARD: need to relate inferType(app fV aV) to inferType(app f a)
      -- through VCompat on components. This requires showing that VCompat
      -- preserves type inference structure, which is non-trivial.
      sorry
    · -- InferType: inferType ctx' v = some ty', VCompat m ty' (app f a)
      unfold VCompat
      apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
      apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
      exact Or.inl ⟨ctx', ty', hinf_v, ih hcompat⟩
    · -- Asc-left: v = asc term tyAsc, VCompat m term (app f a)
      unfold VCompat
      apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
      apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
      exact Or.inr ⟨term, tyAsc, hv_asc, ih h_asc⟩

/-- Normalization preserves VCompat: if VCompat(n, v, e) and absEval normalizes
    e to e', then VCompat(n, v, e'.val). KEY REMAINING LEMMA for inferType
    fallback sorrys and soundness mu case. -/
theorem VCompat.absEval_preserves {n : Nat} {v e : Expr}
    {fuel : Nat} {ctx : TyCtx} {seen : List (Expr × Expr)} {e' : NfExpr}
    (hv : VCompat n v e)
    (habs : absEval fuel ctx seen e = .ok e')
    : VCompat n v e'.val := by
  induction n generalizing v e fuel ctx seen e' with
  | zero => simp [VCompat]
  | succ m ih =>
    unfold VCompat at hv
    rcases hv with
      h_type | h_refl |
      ⟨domV, domT, bodyV, bodyT, hv_eq, hτ_eq, h_body⟩ |
      ⟨annV, annT, bodyV, bodyT, hv_eq, hτ_eq, h_body⟩ |
      ⟨ann, body, hτ_mu, h_mu⟩ |
      ⟨ann, body, ⟨nfuel, nctx, nseen, u', hτ_mu, habs_inner, h_mu_norm⟩⟩ |
      ⟨ann_l, body_l, hv_mu, h_mu_body⟩ |
      ⟨fV, fT, aV, aT, hv_eq, hτ_eq, h_f, h_a⟩ |
      ⟨ctxi, tyi, hinf_v, h_compat⟩ |
      ⟨term, tyAsc, hv_asc, h_asc⟩
    · -- Top: e = type. absEval(type) = ok ⟨type⟩. e'.val = type.
      subst h_type; unfold absEval at habs
      cases fuel with
      | zero => simp [absEval] at habs
      | succ k => simp [absEval] at habs; subst habs; unfold VCompat; exact Or.inl rfl
    · -- Refl: v = e. Need VCompat(m+1, e, e'.val).
      subst h_refl
      -- After subst, e is gone; case-split on v (= former e)
      cases fuel with
      | zero => simp [absEval] at habs
      | succ k =>
        cases v with
        | bvar j =>
          -- absEval(bvar j) = ok ⟨bvar j⟩, so e'.val = bvar j = e
          unfold absEval at habs; injection habs with heq; subst heq
          unfold VCompat; exact Or.inr (Or.inl rfl)
        | type =>
          -- absEval(type) = ok ⟨type⟩, e'.val = type
          unfold absEval at habs; injection habs with heq; subst heq
          unfold VCompat; exact Or.inl rfl
        | asc term ty =>
          -- absEval(asc term ty) = sigma ← absEval(term), tau ← absEval(ty),
          -- check sigma ⊑ tau, return tau.
          -- Use asc-left: VCompat(m, term, e'.val) via IH
          unfold absEval at habs; dsimp only [] at habs
          match h_sigma : absEval k ctx seen term with
          | .error _ => simp [h_sigma, bind, Except.bind] at habs
          | .ok sigma =>
            simp only [h_sigma, bind, Except.bind] at habs
            match h_tau : absEval k ctx seen ty with
            | .error _ => simp [h_tau, bind, Except.bind] at habs
            | .ok tau =>
              simp only [h_tau, bind, Except.bind] at habs
              by_cases hsub : subCheckNF k ctx seen sigma.val tau.val = true
              · simp only [hsub, ite_true] at habs
                injection habs with heq; subst heq
                -- Goal: VCompat(m+1, asc term ty, tau.val)
                -- Use asc-left: need VCompat(m, term, tau.val)
                -- Proof sketch: IH gives VCompat(m, term, sigma.val), then
                -- adequacy bridges to tau.val. But VCompat.adequacy is defined
                -- AFTER this lemma, so we can't use it here.
                -- NOTE: This case does NOT arise at current use sites — at the
                -- bvar use sites in adequacy_gen, VCompat(n+1, v, bvar k) forces
                -- v ∉ {asc}, so the asc-refl path is never taken.
                sorry
              · simp only [Bool.not_eq_true] at hsub; simp only [hsub] at habs; simp at habs
        | lam dom body =>
          -- absEval(lam) normalizes domain and body. v = lam dom body.
          -- Need VCompat(m+1, lam dom body, lam dom'.val body'.val).
          -- HARD: needs substitution lemma / normalization coherence.
          sorry
        | mu ann body =>
          -- absEval(mu) validates annotation but keeps raw. v = mu ann body, e'.val = mu ann body.
          -- VCompat by refl since v = e'.val.
          unfold absEval at habs; dsimp only [] at habs
          match h_ann : absEval k ctx seen ann with
          | .error _ => simp [h_ann, bind, Except.bind] at habs
          | .ok ann' =>
            simp only [h_ann, bind, Except.bind] at habs
            injection habs with heq; subst heq
            unfold VCompat; exact Or.inr (Or.inl rfl)
        | app f a =>
          -- absEval(app f a) normalizes f→f', a→a', dispatches on f'.val.
          -- Neutral case: e' = ⟨app f'.val a'.val⟩, proved via structural app + IH.
          -- Beta/mu cases: shape changes completely, sorry'd.
          unfold absEval at habs; dsimp only [] at habs
          match hf' : absEval k ctx seen f with
          | .error _ => simp [hf', bind, Except.bind] at habs
          | .ok fNF =>
            simp only [hf', bind, Except.bind] at habs
            match ha' : absEval k ctx seen a with
            | .error _ => simp [ha', bind, Except.bind] at habs
            | .ok aNF =>
              simp only [ha', bind, Except.bind] at habs
              -- IH: VCompat(m, f, fNF.val) and VCompat(m, a, aNF.val)
              have hf_compat := ih (VCompat.refl m f) hf'
              have ha_compat := ih (VCompat.refl m a) ha'
              match hfv : fNF.val with
              | .lam _ _ =>
                -- Beta-reduction: result shape differs. HARD.
                simp only [hfv] at habs; sorry
              | .mu _ _ =>
                -- Mu-app dispatch: complex. HARD.
                simp only [hfv] at habs; sorry
              | .type =>
                simp only [hfv] at habs; simp at habs
              | .bvar _ | .app _ _ | .asc _ _ =>
                -- Neutral: e' = ⟨app fNF.val aNF.val⟩
                simp only [hfv] at habs
                by_cases hcall : isCallableNF ctx fNF = true
                · simp only [hcall, ite_true] at habs
                  have heq : e'.val = Expr.app fNF.val aNF.val := by
                    injection habs with h; rw [← h]; simp [hfv]
                  unfold VCompat
                  apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
                  apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inl
                  exact ⟨f, fNF.val, a, aNF.val, rfl, heq, hf_compat, ha_compat⟩
                · simp only [hcall] at habs; simp at habs
    · -- Semantic lam: v = lam domV bodyV, e = lam domT bodyT
      -- Need VCompat(m+1, lam domV bodyV, e'.val)
      -- HARD: needs normalization coherence for bodies
      sorry
    · -- Structural mu: v = mu annV bodyV, e = mu annT bodyT
      -- absEval(mu annT bodyT) validates ann, returns ⟨mu annT bodyT⟩.
      -- So e'.val = mu annT bodyT = e. Reconstruct structural mu.
      subst hv_eq; subst hτ_eq
      cases fuel with
      | zero => simp [absEval] at habs
      | succ fk =>
        unfold absEval at habs; dsimp only [] at habs
        match h_ann : absEval fk ctx seen annT with
        | .error _ => simp [h_ann, bind, Except.bind] at habs
        | .ok ann' =>
          simp only [h_ann, bind, Except.bind] at habs
          injection habs with heq; subst heq
          unfold VCompat
          apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inl
          exact ⟨annV, annT, bodyV, bodyT, rfl, rfl, h_body⟩
    · -- Mu-right: e = mu ann body, VCompat(m, v, body[0:=mu])
      -- absEval(mu ann body) = ok ⟨mu ann body⟩. So e'.val = mu ann body.
      -- Use mu-right: VCompat(m, v, body.subst 0 (mu ann body)) is exactly h_mu.
      subst hτ_mu
      cases fuel with
      | zero => simp [absEval] at habs
      | succ fk =>
        unfold absEval at habs; dsimp only [] at habs
        match h_ann : absEval fk ctx seen ann with
        | .error _ => simp [h_ann, bind, Except.bind] at habs
        | .ok ann' =>
          simp only [h_ann, bind, Except.bind] at habs
          injection habs with heq; subst heq
          unfold VCompat
          apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inl
          exact ⟨ann, body, rfl, h_mu⟩
    · -- Normalized mu-right: e = mu ann body, absEval(body.subst) = ok u', VCompat(m, v, u'.val)
      -- absEval(mu ann body) = ok ⟨mu ann body⟩. Use normalized mu-right.
      subst hτ_mu
      cases fuel with
      | zero => simp [absEval] at habs
      | succ fk =>
        unfold absEval at habs; dsimp only [] at habs
        match h_ann : absEval fk ctx seen ann with
        | .error _ => simp [h_ann, bind, Except.bind] at habs
        | .ok ann'' =>
          simp only [h_ann, bind, Except.bind] at habs
          injection habs with heq; subst heq
          unfold VCompat
          apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
          apply Or.inr; apply Or.inl
          exact ⟨ann, body, ⟨nfuel, nctx, nseen, u', rfl, habs_inner, h_mu_norm⟩⟩
    · -- Mu-left: v = mu ann_l body_l, VCompat(m, body_l[0:=mu], e)
      -- By IH: VCompat(m, body_l[0:=mu], e'.val)
      -- Then mu-left: VCompat(m+1, mu ann_l body_l, e'.val)
      unfold VCompat
      apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
      apply Or.inr; apply Or.inr; apply Or.inl
      exact ⟨ann_l, body_l, hv_mu, ih h_mu_body habs⟩
    · -- Structural app: v = app fV aV, e = app fT aT
      -- absEval(app fT aT) normalizes fT and aT, then dispatches on fT'.val.
      subst hv_eq; subst hτ_eq
      -- Extract the sub-evaluations from absEval(app fT aT)
      cases fuel with
      | zero => simp [absEval] at habs
      | succ k =>
        unfold absEval at habs; dsimp only [] at habs
        match hfT : absEval k ctx seen fT with
        | .error _ => simp [hfT, bind, Except.bind] at habs
        | .ok fT' =>
          simp only [hfT, bind, Except.bind] at habs
          match haT : absEval k ctx seen aT with
          | .error _ => simp [haT, bind, Except.bind] at habs
          | .ok aT' =>
            simp only [haT, bind, Except.bind] at habs
            -- IH on sub-expressions: VCompat(m, fV, fT'.val) and VCompat(m, aV, aT'.val)
            have hfV := ih h_f hfT
            have haV := ih h_a haT
            -- Dispatch on fT'.val
            match hfval : fT'.val with
            | .lam _dom _body =>
              -- Beta-reduction: absEval beta-reduces. Result has different shape.
              -- HARD: need substitution/evaluation coherence
              simp only [hfval] at habs
              sorry
            | .mu _ann _body' =>
              -- Mu-app: various sub-cases depending on annotation and body shapes.
              -- HARD: complex dispatch
              simp only [hfval] at habs
              sorry
            | .type =>
              -- Type is not callable → error
              simp only [hfval] at habs; simp at habs
            | .bvar _ | .app _ _ | .asc _ _ =>
              -- Neutral app: e' = ⟨app fT'.val aT'.val⟩ (after callability check)
              simp only [hfval] at habs
              by_cases hcall : isCallableNF ctx fT' = true
              · simp only [hcall, ite_true] at habs
                have heq : e'.val = Expr.app fT'.val aT'.val := by
                  injection habs with h; rw [← h]; simp [hfval]
                -- VCompat(m+1, app fV aV, app fT'.val aT'.val) via structural app
                unfold VCompat
                apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
                apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inl
                exact ⟨fV, fT'.val, aV, aT'.val, rfl, heq, hfV, haV⟩
              · simp only [hcall] at habs; simp at habs
    · -- InferType: inferType ctx' v = some ty', VCompat(m, ty', e)
      -- By IH: VCompat(m, ty', e'.val)
      -- Then inferType: VCompat(m+1, v, e'.val)
      unfold VCompat
      apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
      apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
      exact Or.inl ⟨ctxi, tyi, hinf_v, ih h_compat habs⟩
    · -- Asc-left: v = asc term tyAsc, VCompat(m, term, e)
      -- By IH: VCompat(m, term, e'.val)
      -- Then asc-left: VCompat(m+1, asc term tyAsc, e'.val)
      unfold VCompat
      apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
      apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
      exact Or.inr ⟨term, tyAsc, hv_asc, ih h_asc habs⟩

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
        | lam _dT _bT =>
          -- τ = lam: case-split on σ to identify subCheckNF dispatch path
          cases σ with
          | type =>
            -- σ = type, τ = lam: catch-all, inferType(type) = none → contradiction
            dsimp only [] at hcheck; simp [inferType] at hcheck
          | asc _tS _tyS =>
            -- σ = asc, τ = lam: catch-all, inferType(asc) = none → contradiction
            dsimp only [] at hcheck; simp [inferType] at hcheck
          | lam _dS _bS =>
            -- σ = lam _dS _bS, τ = lam _dT _bT: structural lam-lam check
            -- The structural check uses empty seen [], so we can reconstruct
            -- subCheckNF with [] for ih_n usage (vacuous callback).
            -- Construct subCheckNF with empty seen (structural check is seen-independent)
            have hcheck_empty : subCheckNF (k + 1) ctx [] (Expr.lam _dS _bS) (Expr.lam _dT _bT) = true := by
              have h := hcheck_orig
              unfold subCheckNF at h ⊢; dsimp only [] at h ⊢
              simp only [if_neg heq] at h ⊢
              simp only [if_neg hseen_chk] at h
              simp only [List.any_nil, ite_false]
              exact h
            -- VCompat case analysis on VCompat (m+1) v (lam _dS _bS)
            unfold VCompat at hv
            rcases hv with
              h_type | h_refl |
              ⟨domV, _, bodyV, _, hv_eq, hσ_eq, h_body⟩ |
              ⟨_, _, _, _, _, hσ_mu4, _⟩ |
              ⟨_, _, hσ_mu5, _⟩ |
              ⟨_, _, ⟨_, _, _, _, hσ_mu6, _, _⟩⟩ |
              ⟨ann_l, body_l, hvm7, hvb7⟩ |
              ⟨_, _, _, _, _, hσ_app8, _, _⟩ |
              ⟨ctxi, tyi, hinf, hty⟩ |
              ⟨term_asc, tyAsc, hv_asc, h_asc⟩
            · cases h_type  -- lam ≠ type
            · -- Refl: v = lam _dS _bS. Needs substitution lemma to construct semantic lam.
              sorry
            · -- Semantic lam: v = lam domV bodyV. Needs substitution lemma to
              -- transport body compatibility from _bS to _bT.
              sorry
            · cases hσ_mu4  -- lam ≠ mu
            · cases hσ_mu5  -- lam ≠ mu
            · cases hσ_mu6  -- lam ≠ mu
            · -- Mu-left: v = mu ann_l body_l, VCompat m (body_l.subst ...) (lam _dS _bS)
              unfold VCompat
              apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
              apply Or.inr; apply Or.inr; apply Or.inl
              exact ⟨ann_l, body_l, hvm7,
                ih_n _ (Expr.lam _dS _bS) (Expr.lam _dT _bT) ctx []
                  hvb7 hcheck_empty
                  (fun p hp => absurd hp (List.not_mem_nil p))⟩
            · cases hσ_app8  -- lam ≠ app
            · -- InferType: inferType ctx' v = some ty, VCompat m ty (lam _dS _bS)
              unfold VCompat
              apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
              apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
              exact Or.inl ⟨ctxi, tyi, hinf,
                ih_n _ (Expr.lam _dS _bS) (Expr.lam _dT _bT) ctx []
                  hty hcheck_empty
                  (fun p hp => absurd hp (List.not_mem_nil p))⟩
            · -- Asc-left: v = asc term_asc tyAsc, VCompat m term_asc (lam _dS _bS)
              -- Transport via ih_n on inner term
              unfold VCompat
              apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
              apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
              exact Or.inr ⟨term_asc, tyAsc, hv_asc,
                ih_n _ (Expr.lam _dS _bS) (Expr.lam _dT _bT) ctx []
                  h_asc hcheck_empty
                  (fun p hp => absurd hp (List.not_mem_nil p))⟩
          | mu _annS _bodyS =>
            -- σ = mu, τ = lam: self-elim (mu ⊑ lam)
            -- Two paths: annotation check or body normalization.
            --
            -- Annotation path: still blocked by annotation-trust gap (Phase 0).
            --
            -- Body path: the self-elim fix (seen not seen') removes the circular
            -- callback dependency. However, expanding the proof reveals that:
            -- - mu-left, inferType, asc-left cases work via ih_n (using hcheck_orig
            --   + hseen callback for original v — NOT the transformed v)
            -- - refl, structural mu cases need absEval_preserves (sorry'd)
            -- - mu-right cases have a step-count issue (VCompat at m, need m+1)
            --
            -- KEY INSIGHT: The ih_n callback uses hseen for the ORIGINAL v. This works
            -- because ih_n is called with hcheck_orig (which has the original seen),
            -- and the callback maps VCompat(m+1, v, p.2) → VCompat(m, v', p.2) via mono.
            -- But v' ≠ v in general (v' = body.subst for mu-left, ty for inferType, etc.).
            -- The callback needs VCompat for v', not v. This fails when seen is non-empty.
            -- When seen = [] (the common case from VCompat.adequacy), it's vacuous.
            sorry
          | bvar _kS =>
            -- σ = bvar, τ = lam: via bvar_inferType + absEval_preserves + ih_fuel
            dsimp only [] at hcheck
            match hinf : inferType ctx (Expr.bvar _kS) with
            | some ty =>
              simp only [hinf] at hcheck
              match habs : absEval k ctx seen ty with
              | .ok ty' =>
                simp only [habs] at hcheck
                exact ih_fuel (m + 1) v ty'.val (Expr.lam _dT _bT) ctx seen
                  (VCompat.absEval_preserves (VCompat.bvar_inferType hv hinf) habs)
                  hcheck hseen
              | .error _ => simp [habs] at hcheck
            | none => simp [hinf] at hcheck
          | app _fS _aS =>
            -- σ = app, τ = lam: via app_inferType + absEval_preserves + ih_fuel
            dsimp only [] at hcheck
            match hinf : inferType ctx (Expr.app _fS _aS) with
            | some ty =>
              simp only [hinf] at hcheck
              match habs : absEval k ctx seen ty with
              | .ok ty' =>
                simp only [habs] at hcheck
                exact ih_fuel (m + 1) v ty'.val (Expr.lam _dT _bT) ctx seen
                  (VCompat.absEval_preserves (VCompat.app_inferType hv hinf) habs)
                  hcheck hseen
              | .error _ => simp [habs] at hcheck
            | none => simp [hinf] at hcheck
        | bvar _j =>
          -- τ = bvar: case-split on σ
          cases σ with
          | type =>
            dsimp only [] at hcheck; simp [inferType] at hcheck
          | lam _dS _bS =>
            dsimp only [] at hcheck; simp [inferType] at hcheck
          | asc _tS _tyS =>
            dsimp only [] at hcheck; simp [inferType] at hcheck
          | mu _annS _bodyS =>
            -- σ = mu, τ = bvar: self-elim
            -- Same structure as mu-lam case above. Annotation path blocked by
            -- annotation-trust. Body path: mu-left/inferType/asc-left work via
            -- ih_n when seen=[]; refl/structural need absEval_preserves;
            -- mu-right has step-count issue. See mu-lam comment for details.
            sorry
          | bvar _kS =>
            -- σ = bvar, τ = bvar: via bvar_inferType + absEval_preserves + ih_fuel
            dsimp only [] at hcheck
            match hinf : inferType ctx (Expr.bvar _kS) with
            | some ty =>
              simp only [hinf] at hcheck
              match habs : absEval k ctx seen ty with
              | .ok ty' =>
                simp only [habs] at hcheck
                exact ih_fuel (m + 1) v ty'.val (Expr.bvar _j) ctx seen
                  (VCompat.absEval_preserves (VCompat.bvar_inferType hv hinf) habs)
                  hcheck hseen
              | .error _ => simp [habs] at hcheck
            | none => simp [hinf] at hcheck
          | app _fS _aS =>
            -- σ = app, τ = bvar: via app_inferType + absEval_preserves + ih_fuel
            dsimp only [] at hcheck
            match hinf : inferType ctx (Expr.app _fS _aS) with
            | some ty =>
              simp only [hinf] at hcheck
              match habs : absEval k ctx seen ty with
              | .ok ty' =>
                simp only [habs] at hcheck
                exact ih_fuel (m + 1) v ty'.val (Expr.bvar _j) ctx seen
                  (VCompat.absEval_preserves (VCompat.app_inferType hv hinf) habs)
                  hcheck hseen
              | .error _ => simp [habs] at hcheck
            | none => simp [hinf] at hcheck
        | asc _tA _tyA =>
          -- τ = asc: case-split on σ
          cases σ with
          | type =>
            dsimp only [] at hcheck; simp [inferType] at hcheck
          | lam _dS _bS =>
            dsimp only [] at hcheck; simp [inferType] at hcheck
          | asc _tS _tyS =>
            dsimp only [] at hcheck; simp [inferType] at hcheck
          | mu _annS _bodyS =>
            -- σ = mu, τ = asc: self-elim (same structure as mu-lam case)
            sorry
          | bvar _kS =>
            -- σ = bvar, τ = asc: via bvar_inferType + absEval_preserves + ih_fuel
            dsimp only [] at hcheck
            match hinf : inferType ctx (Expr.bvar _kS) with
            | some ty =>
              simp only [hinf] at hcheck
              match habs : absEval k ctx seen ty with
              | .ok ty' =>
                simp only [habs] at hcheck
                exact ih_fuel (m + 1) v ty'.val (Expr.asc _tA _tyA) ctx seen
                  (VCompat.absEval_preserves (VCompat.bvar_inferType hv hinf) habs)
                  hcheck hseen
              | .error _ => simp [habs] at hcheck
            | none => simp [hinf] at hcheck
          | app _fS _aS =>
            -- σ = app, τ = asc: via app_inferType + absEval_preserves + ih_fuel
            dsimp only [] at hcheck
            match hinf : inferType ctx (Expr.app _fS _aS) with
            | some ty =>
              simp only [hinf] at hcheck
              match habs : absEval k ctx seen ty with
              | .ok ty' =>
                simp only [habs] at hcheck
                exact ih_fuel (m + 1) v ty'.val (Expr.asc _tA _tyA) ctx seen
                  (VCompat.absEval_preserves (VCompat.app_inferType hv hinf) habs)
                  hcheck hseen
              | .error _ => simp [habs] at hcheck
            | none => simp [hinf] at hcheck
        | app f2 a2 =>
          -- τ = app f2 a2. Case-split on σ to match subCheckNF dispatch.
          cases σ with
          | app f1 a1 =>
            -- App-app congruence case.
            -- Reduce hcheck now that both constructors are known.
            dsimp only [] at hcheck
            -- hcheck: (if subCheckNF k ctx [] f1 f2 && subCheckNF k ctx [] a1 a2
            --          then true else inferType fallback) = true
            by_cases hcong : (subCheckNF k ctx [] f1 f2 && subCheckNF k ctx [] a1 a2) = true
            · -- Structural congruence succeeded
              simp only [Bool.and_eq_true] at hcong
              obtain ⟨hf_sub, ha_sub⟩ := hcong
              -- Key insight: the structural check uses empty seen ([]), so we can
              -- reconstruct subCheckNF (k+1) ctx [] (app f1 a1) (app f2 a2) = true.
              -- This lets us use ih_n with empty seen (vacuous callback).
              have hcheck_empty : subCheckNF (k + 1) ctx [] (Expr.app f1 a1) (Expr.app f2 a2) = true := by
                -- The structural check uses [] and succeeds (hf_sub, ha_sub).
                -- Reconstructing: subCheckNF (k+1) with empty seen must succeed.
                unfold subCheckNF
                by_cases heq2 : (Expr.app f1 a1 == Expr.app f2 a2) = true
                · simp [heq2]
                · simp only [if_neg heq2, List.any_nil, ite_false]
                  -- After the if-checks, we're at match b with | .type | _ => match (a,b) with ...
                  -- For (app f1 a1, app f2 a2), this hits the app-app branch
                  simp only [hf_sub, ha_sub, Bool.and_self, ite_true]; decide
              -- Case analysis on VCompat (m+1) v (app f1 a1)
              unfold VCompat at hv
              rcases hv with
                h_type | h_refl |
                ⟨_, _, _, _, _, hτl, _⟩ |
                ⟨_, _, _, _, _, hτm, _⟩ |
                ⟨_, _, hτm5, _⟩ |
                ⟨_, _, ⟨_, _, _, _, hτm6, _, _⟩⟩ |
                ⟨ann_l, body_l, hvm7, hvb7⟩ |
                ⟨fV, fT, aV, aT, hva, hτa, hvf, hva_a⟩ |
                ⟨ctxi, tyi, hinf, hty⟩ |
                ⟨term_asc, tyAsc, hv_asc, h_asc⟩
              -- Impossible: app ≠ type/lam/mu
              · cases h_type
              · -- Refl: v = app f1 a1
                subst h_refl
                unfold VCompat
                apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
                apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inl
                exact ⟨f1, f2, a1, a2, rfl, rfl,
                  ih_fuel m f1 f1 f2 ctx []
                    (VCompat.refl m f1) hf_sub
                    (fun p hp => absurd hp (List.not_mem_nil p)),
                  ih_fuel m a1 a1 a2 ctx []
                    (VCompat.refl m a1) ha_sub
                    (fun p hp => absurd hp (List.not_mem_nil p))⟩
              · cases hτl
              · cases hτm
              · cases hτm5
              · cases hτm6
              · -- Mu-left: v = mu ann_l body_l, VCompat m (body_l.subst ...) (app f1 a1)
                -- Use ih_n with empty seen (vacuous callback)
                unfold VCompat
                apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
                apply Or.inr; apply Or.inr; apply Or.inl
                exact ⟨ann_l, body_l, hvm7,
                  ih_n _ (Expr.app f1 a1) (Expr.app f2 a2) ctx []
                    hvb7 hcheck_empty
                    (fun p hp => absurd hp (List.not_mem_nil p))⟩
              · -- Structural app: v = app fV aV, VCompat m fV fT, VCompat m aV aT
                -- where app f1 a1 = app fT aT, so fT = f1, aT = a1
                cases hτa
                -- Now fT = f1, aT = a1, hvf: VCompat m fV f1, hva_a: VCompat m aV a1
                unfold VCompat
                apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
                apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inl
                exact ⟨fV, f2, aV, a2, hva, rfl,
                  ih_fuel m fV f1 f2 ctx []
                    hvf hf_sub
                    (fun p hp => absurd hp (List.not_mem_nil p)),
                  ih_fuel m aV a1 a2 ctx []
                    hva_a ha_sub
                    (fun p hp => absurd hp (List.not_mem_nil p))⟩
              · -- InferType: VCompat m tyi (app f1 a1)
                -- Use ih_n with empty seen (vacuous callback)
                unfold VCompat
                apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
                apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
                exact Or.inl ⟨ctxi, tyi, hinf,
                  ih_n _ (Expr.app f1 a1) (Expr.app f2 a2) ctx []
                    hty hcheck_empty
                    (fun p hp => absurd hp (List.not_mem_nil p))⟩
              · -- Asc-left: v = asc term_asc tyAsc, VCompat m term_asc (app f1 a1)
                -- Transport via ih_n on inner term
                unfold VCompat
                apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
                apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
                exact Or.inr ⟨term_asc, tyAsc, hv_asc,
                  ih_n _ (Expr.app f1 a1) (Expr.app f2 a2) ctx []
                    h_asc hcheck_empty
                    (fun p hp => absurd hp (List.not_mem_nil p))⟩
            · -- Structural check failed, inferType fallback
              -- Simplify hcheck: structural check is false, so the else branch applies
              have hcong_false : (subCheckNF k ctx [] f1 f2 && subCheckNF k ctx [] a1 a2) = false := by
                simp only [Bool.not_eq_true] at hcong; exact hcong
              simp only [hcong_false, ite_false] at hcheck
              match hinf : inferType ctx (Expr.app f1 a1) with
              | some ty =>
                simp only [hinf] at hcheck
                match habs : absEval k ctx seen ty with
                | .ok ty' =>
                  simp only [habs] at hcheck
                  exact ih_fuel (m + 1) v ty'.val (Expr.app f2 a2) ctx seen
                    (VCompat.absEval_preserves (VCompat.app_inferType hv hinf) habs)
                    hcheck hseen
                | .error _ => simp [habs] at hcheck
              | none => simp [hinf] at hcheck
          | mu _annS _bodyS =>
            -- σ = mu, τ = app: self-elim (same structure as mu-lam case)
            sorry
          | lam _dS _bS =>
            -- σ = lam, τ = app: inferType(lam) = none → contradiction
            dsimp only [] at hcheck; simp [inferType] at hcheck
          | bvar _kS =>
            -- σ = bvar, τ = app: via bvar_inferType + absEval_preserves + ih_fuel
            dsimp only [] at hcheck
            match hinf : inferType ctx (Expr.bvar _kS) with
            | some ty =>
              simp only [hinf] at hcheck
              match habs : absEval k ctx seen ty with
              | .ok ty' =>
                simp only [habs] at hcheck
                exact ih_fuel (m + 1) v ty'.val (Expr.app f2 a2) ctx seen
                  (VCompat.absEval_preserves (VCompat.bvar_inferType hv hinf) habs)
                  hcheck hseen
              | .error _ => simp [habs] at hcheck
            | none => simp [hinf] at hcheck
          | type =>
            -- σ = type, τ = app: inferType(type) = none → contradiction
            dsimp only [] at hcheck; simp [inferType] at hcheck
          | asc _t _ty =>
            -- σ = asc, τ = app: inferType(asc) = none → contradiction
            dsimp only [] at hcheck; simp [inferType] at hcheck

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

/-! ## Environment compatibility (for the fundamental theorem) -/

/-- Two environments are VCompat-related: corresponding entries are VCompat.
    This is the semantic typing condition for the fundamental theorem. -/
def EnvCompat (n : Nat) (γV γT : List Expr) : Prop :=
  γV.length = γT.length ∧
  ∀ i (hV : i < γV.length) (hT : i < γT.length), VCompat n (γV[i]) (γT[i])

/-! ## Fundamental theorem of the logical relation (open-term soundness)

This is the generalization of soundness to open terms with VCompat-related
environments. It resolves the dual-substitution problem: the lam body is a
sub-expression, so the IH applies directly. Both evaluators work on the SAME
body; the environment difference is captured by substEnv.

STATUS: Not yet proved. This is the recommended path forward for resolving
the ~8 dual-substitution sorrys. See DECISION-LOG and SUGGESTIONS.md.

Key insight: induction is on EXPRESSION STRUCTURE (not fuel). The IH for
the lam body gives soundness for the body with an extended environment.
The semantic lam is proved by extending the environment with VCompat args.

REQUIRES: substEnv composition lemmas (showing substEnv commutes with
single subst), and substEnv_idEnv (identity property). These are in Syntax.lean. -/

/-- Multi-step fuel monotonicity for absEval: if it succeeds at fuel n,
    it succeeds at any fuel ≥ n with the same result. -/
theorem absEval_fuel_mono_le {n m : Nat} {ctx : TyCtx} {seen : List (Expr × Expr)}
    {e : Expr} {v : NfExpr}
    (h : absEval n ctx seen e = .ok v) (hle : n ≤ m) : absEval m ctx seen e = .ok v := by
  induction m generalizing n with
  | zero => have := Nat.le_zero.mp hle; subst this; exact h
  | succ k ih =>
    by_cases heq : n = k + 1
    · subst heq; exact h
    · exact absEval_fuel_mono (ih h (by omega))

/-- Multi-step fuel monotonicity for concEval. -/
theorem concEval_fuel_mono_le {n m : Nat} {e v : Expr}
    (h : concEval n e = some v) (hle : n ≤ m) : concEval m e = some v := by
  induction m generalizing n with
  | zero => have := Nat.le_zero.mp hle; subst this; exact h
  | succ k ih =>
    by_cases heq : n = k + 1
    · subst heq; exact h
    · exact concEval_fuel_mono (ih h (by omega))

/-- Concrete values (lam/type/mu) are stable under concEval: evaluating them
    returns themselves. -/
theorem concEval_val {fuel : Nat} {v : Expr} (hfuel : fuel > 0)
    (hval : match v with | .lam _ _ | .type | .mu _ _ => True | _ => False)
    : concEval fuel v = some v := by
  cases fuel with
  | zero => omega
  | succ k =>
    cases v with
    | lam _ _ => simp [concEval]
    | type => simp [concEval]
    | mu _ _ => simp [concEval]
    | bvar _ => exact absurd hval (by simp)
    | app _ _ => exact absurd hval (by simp)
    | asc _ _ => exact absurd hval (by simp)

/-- A concrete-value environment: all entries are lam, type, or mu.
    This ensures entries are stable under concEval. -/
def ConcreteValEnv (γ : List Expr) : Prop :=
  ∀ i (h : i < γ.length), match γ[i] with | .lam _ _ | .type | .mu _ _ => True | _ => False

/-- Empty environment is a concrete value environment. -/
theorem ConcreteValEnv.nil : ConcreteValEnv [] :=
  fun i h => absurd h (Nat.not_lt_zero i)

/-- Extending a concrete value environment with a concrete value. -/
theorem ConcreteValEnv.cons {v : Expr} {γ : List Expr}
    (hv : match v with | .lam _ _ | .type | .mu _ _ => True | _ => False)
    (hγ : ConcreteValEnv γ)
    : ConcreteValEnv (v :: γ) := by
  intro i hi
  cases i with
  | zero => simp [List.getElem_cons_zero]; exact hv
  | succ j =>
    simp only [List.getElem_cons_succ]
    exact hγ j (by simp [List.length_cons] at hi; omega)

/-- EnvCompat for the fundamental theorem: environments are VCompat-related
    AND the concrete side contains only concrete values (lam/type/mu). -/
def FunEnvCompat (n : Nat) (γV γT : List Expr) : Prop :=
  γV.length = γT.length ∧
  ConcreteValEnv γV ∧
  ∀ i (hV : i < γV.length) (hT : i < γT.length), VCompat n (γV[i]) (γT[i])

/-- Empty FunEnvCompat. -/
theorem FunEnvCompat.nil (n : Nat) : FunEnvCompat n [] [] :=
  ⟨rfl, ConcreteValEnv.nil, fun i h => absurd h (Nat.not_lt_zero i)⟩

/-- Extend FunEnvCompat with a concrete-value pair. -/
theorem FunEnvCompat.cons {n : Nat} {v τ : Expr} {γV γT : List Expr}
    (hval : match v with | .lam _ _ | .type | .mu _ _ => True | _ => False)
    (hcompat : VCompat n v τ)
    (henv : FunEnvCompat n γV γT)
    : FunEnvCompat n (v :: γV) (τ :: γT) := by
  obtain ⟨hlen, hval_env, hvc⟩ := henv
  exact ⟨by simp [hlen], ConcreteValEnv.cons hval hval_env,
    fun i hiV hiT => by
      cases i with
      | zero => simp [List.getElem_cons_zero]; exact hcompat
      | succ j =>
        simp only [List.getElem_cons_succ]
        have hjV : j < γV.length := by simp [List.length_cons] at hiV; omega
        have hjT : j < γT.length := by simp [List.length_cons] at hiT; omega
        exact hvc j hjV hjT⟩

/-- Downward closure for FunEnvCompat. -/
theorem FunEnvCompat.mono {n : Nat} {γV γT : List Expr}
    (h : FunEnvCompat (n + 1) γV γT) : FunEnvCompat n γV γT := by
  obtain ⟨hlen, hval, hvc⟩ := h
  exact ⟨hlen, hval, fun i hiV hiT => VCompat.mono (hvc i hiV hiT)⟩

/-- Multi-step downward closure for FunEnvCompat. -/
theorem FunEnvCompat.mono_le {n m : Nat} {γV γT : List Expr}
    (h : FunEnvCompat n γV γT) (hle : m ≤ n) : FunEnvCompat m γV γT := by
  obtain ⟨hlen, hval, hvc⟩ := h
  exact ⟨hlen, hval, fun i hiV hiT => VCompat.mono_le (hvc i hiV hiT) hle⟩

/-! ## Fundamental theorem of the logical relation (open-term soundness)

This is the generalization of soundness to open terms with VCompat-related
environments. It resolves the dual-substitution problem: the lam body is a
sub-expression, so the IH applies directly. Both evaluators work on the SAME
body; the environment difference is captured by substEnv.

Key insight: induction is on EXPRESSION STRUCTURE (not fuel). The IH for
the lam body gives soundness for the body with an extended environment.
The semantic lam is proved by extending the environment with VCompat args.

REQUIRES: substEnv composition lemmas (Syntax.lean) — ALL PROVED.

PRECONDITIONS:
- FunEnvCompat: environments are VCompat-related AND concrete-side entries
  are concrete values (lam/type/mu). This ensures the bvar case works:
  substEnv maps bvar k to γV[k], and concEval of a concrete value returns
  itself, so v = γV[k] and VCompat follows from FunEnvCompat.
- closedAt: the expression has at most ctx.length free variables. Needed
  for the composition lemma (substEnv_subst_comp) in the lam case. -/

theorem soundness_open (e : Expr)
    (fuel : Nat) (ctx : TyCtx) (τ : NfExpr)
    (h_abs : absEval fuel ctx [] e = .ok τ)
    (n : Nat) (γV γT : List Expr)
    (h_env : FunEnvCompat n γV γT)
    (h_ctx : γT.length = ctx.length)
    (h_closed : e.closedAt ctx.length = true)
    (v : Expr)
    (h_conc : concEval fuel (e.substEnv γV) = some v)
    : VCompat n v (τ.val.substEnv γT) := by
  induction e generalizing fuel ctx τ n γV γT v with
  | bvar k =>
    -- absEval: returns ⟨bvar k⟩ regardless of context
    cases fuel with
    | zero => simp [absEval] at h_abs
    | succ fk =>
      unfold absEval at h_abs; injection h_abs with hτ; subst hτ
      -- τ.val = bvar k, so τ.val.substEnv γT = γT[k] (since k < ctx.length = γT.length)
      simp only [Expr.substEnv]
      have hk_lt : k < ctx.length := by simp [Expr.closedAt] at h_closed; exact h_closed
      have hk_lt_T : k < γT.length := by omega
      have hk_lt_V : k < γV.length := by
        obtain ⟨hlen, _, _⟩ := h_env; omega
      -- substEnv maps bvar k to γV[k]! / γT[k]!
      -- Simplify goal and hypothesis using the bounds
      simp only [Expr.substEnv, hk_lt_V, ite_true] at h_conc
      simp only [hk_lt_T, ite_true]
      obtain ⟨_, hval_env, hvc⟩ := h_env
      -- γV[k]! is a concrete value, so concEval returns it unchanged
      have hval_k : match γV[k]! with | .lam _ _ | .type | .mu _ _ => True | _ => False := by
        have h := hval_env k hk_lt_V
        rw [getElem!_pos γV k hk_lt_V]; exact h
      have hstable := concEval_val (by omega : fk + 1 > 0) hval_k
      rw [hstable] at h_conc; injection h_conc with hv; subst hv
      -- v = γV[k]!, need VCompat n γV[k]! γT[k]!
      have hvc_k := hvc k hk_lt_V hk_lt_T
      rw [show γV[k]! = γV[k] from getElem!_pos γV k hk_lt_V,
          show γT[k]! = γT[k] from getElem!_pos γT k hk_lt_T]
      exact hvc_k
  | type =>
    -- absEval: type → ⟨type⟩, concEval: type → type, VCompat by refl
    cases fuel with
    | zero => simp [absEval] at h_abs
    | succ fk =>
      unfold absEval at h_abs; injection h_abs with hτ; subst hτ
      simp only [Expr.substEnv] at h_conc ⊢
      unfold concEval at h_conc; injection h_conc with hv; subst hv
      exact VCompat.refl n .type
  | mu ann body ih_ann ih_body =>
    -- absEval: validates ann, returns ⟨mu ann body⟩ (raw)
    -- concEval: mu is a value, returns itself
    cases fuel with
    | zero => simp [absEval] at h_abs
    | succ fk =>
      unfold absEval at h_abs; dsimp only [] at h_abs
      match h_ann_abs : absEval fk ctx [] ann with
      | .error _ => simp [h_ann_abs, bind, Except.bind] at h_abs
      | .ok ann' =>
        simp only [h_ann_abs, bind, Except.bind] at h_abs
        injection h_abs with hτ; subst hτ
        -- τ.val = mu ann body, τ.val.substEnv γT = mu (ann.substEnv γT) (body.substEnv (lift γT))
        -- concEval of (mu ...).substEnv γV returns it as a value
        simp only [Expr.substEnv] at h_conc ⊢
        -- mu is a value: concEval (fk+1) (mu ...) = some (mu ...)
        unfold concEval at h_conc
        injection h_conc with hv; subst hv
        -- v = mu (ann.substEnv γV) (body.substEnv (lift γV))
        -- Goal: VCompat n (mu (ann.substEnv γV) (body.substEnv (lift γV)))
        --                 (mu (ann.substEnv γT) (body.substEnv (lift γT)))
        -- SORRY: Need structural mu disjunct, which requires VCompat on
        -- unfolded bodies (self-substitution + substEnv). This is complex.
        sorry
  | lam dom body ih_dom ih_body =>
    -- KEY CASE: the whole point of the fundamental theorem.
    -- absEval: normalizes domain and body under binder
    -- concEval: lam is a value (body not evaluated)
    cases fuel with
    | zero => simp [absEval] at h_abs
    | succ fk =>
      unfold absEval at h_abs; dsimp only [] at h_abs
      match h_dom_abs : absEval fk ctx [] dom with
      | .error _ => simp [h_dom_abs, bind, Except.bind] at h_abs
      | .ok dom' =>
        simp only [h_dom_abs, bind, Except.bind] at h_abs
        match h_body_abs : absEval fk (TyCtx.extend ctx dom') [] body with
        | .error _ => simp [h_body_abs, bind, Except.bind] at h_abs
        | .ok body' =>
          simp only [h_body_abs, bind, Except.bind] at h_abs
          injection h_abs with hτ; subst hτ
          -- τ.val = lam dom'.val body'.val
          -- τ.val.substEnv γT = lam (dom'.val.substEnv γT) (body'.val.substEnv (lift γT))
          simp only [Expr.substEnv] at h_conc ⊢
          -- concEval: lam is a value
          unfold concEval at h_conc
          injection h_conc with hv; subst hv
          -- v = lam (dom.substEnv γV) (body.substEnv (lift γV))
          -- Goal: VCompat n (lam ...) (lam ...)
          -- Use the semantic lam disjunct
          cases n with
          | zero => simp [VCompat]
          | succ m =>
            unfold VCompat
            apply Or.inr; apply Or.inr; apply Or.inl
            exact ⟨_, _, _, _, rfl, rfl, fun j hj aV aT hval_aV hcompat_arg fuel' rv h_conc_body => by
              -- Prove the semantic lam (no absEval on type side):
              -- bodyV.subst 0 aV = body.substEnv (aV :: γV) (composition)
              -- bodyT.subst 0 aT = body'.val.substEnv (aT :: γT) (composition)
              -- IH on body gives VCompat j rv (body'.val.substEnv (aT :: γT))
              have h_closed_body : body.closedAt (ctx.length + 1) = true := by
                simp [Expr.closedAt] at h_closed; exact h_closed.2
              have h_closed_body_env : body.closedAt (γV.length + 1) = true := by
                obtain ⟨hlen, _, _⟩ := h_env; rw [← h_ctx, ← hlen] at h_closed_body
                exact h_closed_body
              -- Composition on concrete side: rewrite subst as substEnv
              rw [Expr.substEnv_subst_comp body γV aV h_closed_body_env] at h_conc_body
              -- Composition on type side: sorry closedAt for body'.val
              have h_closed_body'_env : body'.val.closedAt (γT.length + 1) = true := by
                have h_ext_len : (TyCtx.extend ctx dom').length = ctx.length + 1 := by
                  simp [TyCtx.extend, List.length_cons, List.length_map]
                rw [show γT.length + 1 = (TyCtx.extend ctx dom').length from by omega]
                exact absEval_preserves_closedAt h_body_abs (by rw [h_ext_len]; exact h_closed_body)
              rw [Expr.substEnv_subst_comp body'.val γT aT h_closed_body'_env]
              -- Goal: VCompat j rv (body'.val.substEnv (aT :: γT))
              -- Align fuels and apply IH on body
              have h_abs_max := absEval_fuel_mono_le h_body_abs (Nat.le_max_right fuel' fk)
              have h_conc_max := concEval_fuel_mono_le h_conc_body (Nat.le_max_left fuel' fk)
              -- Build extended environment
              have h_env_ext : FunEnvCompat j (aV :: γV) (aT :: γT) := by
                exact FunEnvCompat.cons hval_aV hcompat_arg (FunEnvCompat.mono_le h_env (by omega))
              exact ih_body (max fuel' fk) (TyCtx.extend ctx dom') body' h_abs_max
                j (aV :: γV) (aT :: γT) h_env_ext
                (by simp [TyCtx.extend, List.length_cons, List.length_map]; omega)
                (by show body.closedAt ((TyCtx.extend ctx dom').length) = true
                    simp [TyCtx.extend, List.length_cons, List.length_map]
                    exact h_closed_body)
                rv h_conc_max⟩
  | asc term ty ih_term ih_ty =>
    -- absEval: check term ⊑ ty, return ty's normalization
    -- concEval: erase ascription, evaluate term
    cases fuel with
    | zero => simp [absEval] at h_abs
    | succ fk =>
      unfold absEval at h_abs; dsimp only [] at h_abs
      match h_sigma : absEval fk ctx [] term with
      | .error _ => simp [h_sigma, bind, Except.bind] at h_abs
      | .ok sigma =>
        simp only [h_sigma, bind, Except.bind] at h_abs
        match h_tau : absEval fk ctx [] ty with
        | .error _ => simp [h_tau, bind, Except.bind] at h_abs
        | .ok tau =>
          simp only [h_tau, bind, Except.bind] at h_abs
          by_cases hsub : subCheckNF fk ctx [] sigma.val tau.val = true
          · simp only [hsub, ite_true] at h_abs
            injection h_abs with heq; subst heq
            -- τ = tau. τ.val.substEnv γT = tau.val.substEnv γT.
            -- concEval: concEval (fk+1) (substEnv γV (asc term ty))
            --         = concEval (fk+1) (asc (substEnv γV term) (substEnv γV ty))
            --         = concEval fk (substEnv γV term)
            simp only [Expr.substEnv] at h_conc
            unfold concEval at h_conc
            -- h_conc: concEval fk (term.substEnv γV) = some v
            -- IH on term: VCompat n v (sigma.val.substEnv γT)
            have h_closed_term : term.closedAt ctx.length = true := by
              simp [Expr.closedAt] at h_closed; exact h_closed.1
            have h_closed_ty : ty.closedAt ctx.length = true := by
              simp [Expr.closedAt] at h_closed; exact h_closed.2
            have ih_v_sigma := ih_term fk ctx sigma h_sigma n γV γT h_env h_ctx h_closed_term v h_conc
            -- Now bridge from sigma.val.substEnv γT to tau.val.substEnv γT via adequacy
            -- Need: subCheckNF bridges through substEnv.
            -- This requires: subCheckNF fk ctx [] sigma.val tau.val = true
            --   implies VCompat n v (sigma.substEnv γT) → VCompat n v (tau.substEnv γT)
            -- BLOCKER: subCheckNF operates on open terms (in ctx), but we need the
            -- result on closed terms (after substEnv). This is a key gap.
            sorry
          · simp only [Bool.not_eq_true] at hsub; simp only [hsub] at h_abs; simp at h_abs
  | app f a ih_f ih_a =>
    -- The hardest case. concEval evaluates f and a, dispatches on f's value.
    -- absEval evaluates f and a, dispatches on f's type.
    -- The fundamental theorem resolves the lam-lam sub-case (different bodies
    -- and arguments) but other sub-cases remain complex.
    sorry

/-! ## Soundness theorem (closed-term version)

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
  induction fuel generalizing e v τ n with
  | zero => simp [concEval] at h_conc
  | succ k ih =>
    cases e with
    | bvar _ => simp [concEval] at h_conc
    | type =>
      -- concEval: type is a value, v = type
      -- absEval: type normalizes to type, τ = ⟨type⟩
      unfold concEval at h_conc; injection h_conc with hv; subst hv
      unfold absEval at h_abs; injection h_abs with hτ; subst hτ
      exact VCompat.refl n Expr.type
    | asc term ty =>
      -- concEval erases ascription: concEval (k+1) (asc term ty) = concEval k term
      unfold concEval at h_conc
      -- absEval checks ascription: normalize both sides, check subtyping, return type
      unfold absEval at h_abs; dsimp only [] at h_abs
      match h_sigma : absEval k [] [] term with
      | .error _ => simp [h_sigma, bind, Except.bind] at h_abs
      | .ok sigma =>
        simp only [h_sigma, bind, Except.bind] at h_abs
        match h_tau : absEval k [] [] ty with
        | .error _ => simp [h_tau, bind, Except.bind] at h_abs
        | .ok tau =>
          simp only [h_tau, bind, Except.bind] at h_abs
          -- h_abs encodes: if subCheckNF succeeded, τ = tau; else error
          by_cases hsub : subCheckNF k [] [] sigma.val tau.val = true
          · simp only [hsub, ite_true] at h_abs
            injection h_abs with h_eq; subst h_eq
            -- IH gives VCompat n v sigma.val, adequacy bridges to tau.val
            exact VCompat.adequacy (ih term v sigma n h_conc h_sigma) hsub
          · simp only [Bool.not_eq_true] at hsub
            simp only [hsub] at h_abs
            simp at h_abs
    | lam dom body =>
      -- concEval: lam is a value, v = lam dom body
      -- absEval: normalizes domain and body under binder
      -- BLOCKER: semantic lam quantifies over ALL fuel levels for inner evaluation;
      -- the fuel-induction IH only gives soundness at fuel k. Bridging requires
      -- either strong induction + fuel mono, or a combined fuel/step induction.
      -- See PROGRESS.md for analysis.
      sorry
    | mu ann body =>
      -- concEval: mu is a value, v = mu ann body
      -- absEval: validates annotation, returns ⟨mu ann body⟩ (raw annotation kept)
      -- Since both return mu ann body, VCompat by refl.
      unfold concEval at h_conc; injection h_conc with hv; subst hv
      unfold absEval at h_abs; dsimp only [] at h_abs
      match h_ann : absEval k [] [] ann with
      | .error _ => simp [h_ann, bind, Except.bind] at h_abs
      | .ok ann' =>
        simp only [h_ann, bind, Except.bind] at h_abs
        injection h_abs with hτ; subst hτ
        exact VCompat.refl n (Expr.mu ann body)
    | app f a =>
      -- concEval: evaluate f → fV, a → aV, dispatch on fV
      unfold concEval at h_conc
      match hcf : concEval k f with
      | none => simp [hcf] at h_conc
      | some fV =>
        match hca : concEval k a with
        | none => simp [hcf, hca] at h_conc
        | some aV =>
          simp only [hcf, hca] at h_conc
          -- absEval: evaluate f → fT, a → aT, dispatch on fT.val
          unfold absEval at h_abs; dsimp only [] at h_abs
          match haf : absEval k [] [] f with
          | .error _ => simp [haf, bind, Except.bind] at h_abs
          | .ok fT =>
            simp only [haf, bind, Except.bind] at h_abs
            match haa : absEval k [] [] a with
            | .error _ => simp [haa, bind, Except.bind] at h_abs
            | .ok aT =>
              simp only [haa, bind, Except.bind] at h_abs
              -- IH: VCompat n fV fT.val, VCompat n aV aT.val
              have ih_f := ih f fV fT n hcf haf
              have ih_a := ih a aV aT n hca haa
              -- Dispatch on fT.val (abstract function type)
              match hftv : fT.val with
              | .lam _domT _bodyT =>
                -- absEval: lam case. Domain check + beta-reduce.
                simp only [hftv] at h_abs
                by_cases hdom : subCheckNF k [] [] aT.val _domT = true
                · simp only [hdom, ite_true] at h_abs
                  -- h_abs: absEval k [] [] (_bodyT.subst 0 aT.val) = .ok τ
                  -- Dispatch on fV for concEval
                  match hfvv : fV with
                  | .bvar _k =>
                    -- Impossible: concEval never produces bvar
                    exact absurd hcf (by intro h; exact concEval_not_bvar h)
                  | .asc _t _ty =>
                    -- Impossible: concEval never produces asc
                    exact absurd hcf (by intro h; exact concEval_not_asc h)
                  | .type =>
                    -- Contradiction: VCompat 1 type (lam ...) is False.
                    -- type is not lam/mu/app/asc, inferType returns none for type.
                    exfalso
                    have h_vc := ih f Expr.type fT 1 hcf haf
                    rw [hftv] at h_vc
                    unfold VCompat at h_vc
                    rcases h_vc with h | h |
                      ⟨_, _, _, _, h, _, _⟩ | ⟨_, _, _, _, h, _, _⟩ |
                      ⟨_, _, h, _⟩ | ⟨_, _, _, _, _, _, h, _, _⟩ |
                      ⟨_, _, h, _⟩ | ⟨_, _, _, _, h, _, _, _⟩ |
                      ⟨_, _, h, _⟩ | ⟨_, _, h, _⟩
                    all_goals (first | cases h | simp [inferType] at h)
                  | .lam _domV _bodyV =>
                    -- BLOCKER: dual-substitution. concEval beta-reduces bodyV.subst 0 aV,
                    -- absEval beta-reduces bodyT.subst 0 aT.val. Different bodies AND
                    -- different arguments. The semantic lam from IH on f can't be extracted
                    -- because VCompat might hold via the refl disjunct.
                    simp only [hfvv] at h_conc
                    sorry
                  | .mu _annV _bodyV =>
                    -- concEval unrolls mu then re-applies, absEval beta-reduces bodyT.
                    simp only [hfvv] at h_conc
                    sorry
                  | .app _fV' _aV' =>
                    -- Neutral app: v = app (app _fV' _aV') aV.
                    -- absEval beta-reduces bodyT.subst 0 aT.val → τ.
                    -- ih_f: VCompat n (app _fV' _aV') (lam domT bodyT) — may hold
                    -- via inferType (which provides type info) but extracting the
                    -- semantic lam from this is non-trivial.
                    simp only [hfvv] at h_conc
                    sorry
                · simp only [Bool.not_eq_true] at hdom
                  simp only [hdom] at h_abs; simp at h_abs
              | .mu _annT _bodyT =>
                -- absEval: mu-app dispatch. Complex annotation-trust + mu unrolling.
                simp only [hftv] at h_abs
                sorry
              | .type =>
                simp only [hftv] at h_abs; simp at h_abs
              | .bvar _ | .app _ _ | .asc _ _ =>
                -- absEval: neutral application. fT.val is not lam/mu/type.
                simp only [hftv] at h_abs
                by_cases hcall : isCallableNF [] fT = true
                · simp only [hcall, ite_true] at h_abs
                  injection h_abs with h_eq_abs
                  -- τ = ⟨app fT.val aT.val⟩, so τ.val = app fT.val aT.val
                  -- Dispatch on fV for concEval
                  match hfvv : fV with
                  | .lam _domV _bodyV =>
                    -- fV = lam, fT.val = neutral: CONTRADICTION.
                    -- VCompat 1 (lam) (bvar/app/asc) is False: no disjunct applies.
                    -- (lam ≠ mu/app/asc, inferType returns none for lam,
                    --  and fT.val ≠ type/lam/mu since those match arms were handled.)
                    exfalso
                    have h_vc := ih f (Expr.lam _domV _bodyV) fT 1 hcf haf
                    rw [hftv] at h_vc
                    unfold VCompat at h_vc
                    rcases h_vc with h | h |
                      ⟨_, _, _, _, _, h, _⟩ | ⟨_, _, _, _, h, _, _⟩ |
                      ⟨_, _, h, _⟩ | ⟨_, _, _, _, _, _, h, _, _⟩ |
                      ⟨_, _, h, _⟩ | ⟨_, _, _, _, h, _, _, _⟩ |
                      ⟨_, _, h, _⟩ | ⟨_, _, h, _⟩
                    all_goals (first | cases h | simp [inferType] at h)
                  | .mu _annV _bodyV =>
                    -- fV = mu, fT.val = neutral: concEval unrolls mu, absEval
                    -- returns neutral app. Shape mismatch.
                    simp only [hfvv] at h_conc
                    sorry
                  | .bvar _ | .type | .app _ _ | .asc _ _ =>
                    -- NEUTRAL-NEUTRAL: both sides produce neutral apps.
                    -- concEval: v = app fV aV (catch-all for non-lam/non-mu fV)
                    -- absEval: τ.val = app fT.val aT.val
                    -- VCompat via structural app + IH on f and a.
                    simp only [hfvv] at h_conc
                    injection h_conc with h_v; subst h_v
                    -- Get τ.val equation from h_eq_abs
                    have hτv : τ.val = Expr.app fT.val aT.val := by
                      have := h_eq_abs.symm; subst this; simp [hftv]
                    cases n with
                    | zero => simp [VCompat]
                    | succ m =>
                      rw [hτv]
                      unfold VCompat
                      apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
                      apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inl
                      exact ⟨_, fT.val, _, aT.val, rfl, rfl,
                        VCompat.mono ih_f, VCompat.mono ih_a⟩
                · simp only [hcall] at h_abs; simp at h_abs

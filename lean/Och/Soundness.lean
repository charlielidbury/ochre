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
          -- absEval(mu) normalizes annotation. v = mu ann body, e'.val = mu ann'.val body.
          -- HARD: needs annotation normalization congruence.
          sorry
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
      -- HARD: annotation normalization congruence
      sorry
    · -- Mu-right: e = mu ann body, VCompat(m, v, body[0:=mu])
      -- HARD: annotation normalization congruence
      sorry
    · -- Normalized mu-right: e = mu, already normalized VCompat(m, v, u'.val)
      -- HARD: composing two normalizations
      sorry
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
            -- BLOCKER: annotation-trust gap — going from VCompat(v, mu) to
            -- VCompat(v, ann) requires annotation correctness
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
            -- σ = app, τ = lam: inferType fallback
            -- BLOCKER: needs app_inferType lemma
            sorry
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
            -- BLOCKER: annotation-trust gap
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
            -- σ = app, τ = bvar: inferType fallback
            -- BLOCKER: needs app_inferType lemma
            sorry
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
            -- σ = mu, τ = asc: self-elim
            -- BLOCKER: annotation-trust gap
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
            -- σ = app, τ = asc: inferType fallback
            -- BLOCKER: needs app_inferType lemma
            sorry
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
              sorry
          | mu _annS _bodyS =>
            -- Self-elim (mu ⊑ app): blocked by annotation-trust gap
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
      -- absEval: normalizes annotation ann → ann', returns ⟨mu ann'.val body⟩
      -- BLOCKER: need to relate (mu ann body) to (mu ann'.val body) in VCompat.
      -- If ann = ann'.val (annotation already normal), it's refl. Otherwise need
      -- a lemma about annotation normalization preserving VCompat.
      sorry
    | app f a =>
      -- Beta-reduction case — most complex
      -- concEval: evaluate f and a, dispatch on fV (lam → beta, mu → unroll, etc.)
      -- absEval: evaluate f and a, dispatch on f'.val with domain checking
      -- BLOCKER: same all-fuel issue as lam, plus needs VCompat dispatch on
      -- fV/f'.val shapes (lam-lam, mu-app, neutral app).
      sorry

import Och.Syntax
import Och.Eval
import Och.Subtyping

/-!
# Soundness via Logical Relations (VCompat)

## Goal

Prove: if `absEval` succeeds, `concEvalE(e)` is compatible with `absEval(e)`.

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
soundness_gen : concEvalE fuel [] e = some v →
                absEval fuel [] e = .ok τ →
                ∀ n, VCompat n v τ
```

The `WellTyped` precondition is gone — it's implied by `absEval` succeeding
(absEval now validates ascriptions and callability internally).
-/

open Expr

/-! ## VCompat-equivalence (vEquiv) and eval-closedness (closedEval)

These support the soundness_gen mu case. The evaluators copy lambda domains
and mu annotations verbatim from the source, so outputs can have free bvar 0
in those positions. VCompat doesn't compare domains/annotations, so subst
into those positions is invisible to VCompat.

**vEquivB**: two expressions agree on everything VCompat cares about (bodies,
app structure, asc structure) but may differ in lambda domains and mu
annotations.

**closedEvalB**: all bvar indices in VCompat-relevant positions are below
the binding depth. -/

/-- Two expressions are VCompat-equivalent: they agree on everything except
    lambda domains and mu annotations. -/
def Expr.vEquivB : Expr → Expr → Bool
  | .bvar k, .bvar k' => k == k'
  | .lam _ b1, .lam _ b2 => b1.vEquivB b2
  | .app f1 a1, .app f2 a2 => f1.vEquivB f2 && a1.vEquivB a2
  | .asc t1 y1, .asc t2 y2 => t1.vEquivB t2 && y1.vEquivB y2
  | .type, .type => true
  | .mu _ b1, .mu _ b2 => b1.vEquivB b2
  | _, _ => false

/-- Eval-closedness: all bvar indices in VCompat-relevant positions are < n. -/
def Expr.closedEvalB (n : Nat) : Expr → Bool
  | .bvar k => k < n
  | .lam _ body => body.closedEvalB (n + 1)
  | .app f a => f.closedEvalB n && a.closedEvalB n
  | .asc t y => t.closedEvalB n && y.closedEvalB n
  | .type => true
  | .mu _ body => body.closedEvalB (n + 1)

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
        ∀ (j : Nat), j ≤ n → ∀ (fuel : Nat) (env : Env) (aV aT : Expr),
          VCompat j aV aT →
          ∀ rv, concEvalE fuel env (bodyV.subst 0 aV) = some rv →
          ∀ rτ, absEval fuel [] (bodyT.subst 0 aT) = .ok rτ →
          VCompat j rv rτ)
    -- Unfolded structural mu
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
    ∨ (∃ fV fT aV aT,
        v = .app fV aV ∧ τ = .app fT aT ∧
        VCompat n fV fT ∧ VCompat n aV aT)
    -- InferType fallback: for neutral terms
    ∨ (∃ ctx ty, inferType ctx v = some ty ∧ VCompat n ty τ)

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
                  ⟨ann, body, hτ, h_mu⟩ | ⟨ann, body, hv, h_mu⟩ |
                  ⟨fV, fT, aV, aT, hv, hτ, h_f, h_a⟩ |
                  ⟨ctx, ty, h_infer, h_compat⟩
    · exact Or.inl h_top
    · exact Or.inr (Or.inl h_refl)
    · exact Or.inr (Or.inr (Or.inl ⟨domV, domT, bodyV, bodyT, hv, hτ,
        fun j hj => h_body j (Nat.le_succ_of_le hj)⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨annV, annT, bodyV, bodyT, hv, hτ, VCompat.mono h_body⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨ann, body, hτ, VCompat.mono h_mu⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨ann, body, hv, VCompat.mono h_mu⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨fV, fT, aV, aT, hv, hτ, VCompat.mono h_f, VCompat.mono h_a⟩))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨ctx, ty, h_infer, VCompat.mono h_compat⟩))))))

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
    apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inl
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
    intro n v τ ctx seen hcheck hseen
    -- Needs update for new mutual absEval/subCheckNF definition
    sorry

/-- Corollary: subCheckNF .type (mu ann body) with empty seen gives VCompat. -/
theorem VCompat.from_type_sub {fuel : Nat} {ctx : TyCtx} {n : Nat} {v : Expr}
    {ann body : Expr}
    (hcheck : subCheckNF fuel ctx [] Expr.type (.mu ann body) = true)
    : VCompat n v (.mu ann body) :=
  VCompat.from_type_sub_gen fuel n v _ ctx [] hcheck
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
    intro n σ ctx seen hσ_not_mu ann body hcheck hseen
    -- Needs update for new mutual absEval/subCheckNF definition
    sorry

/-- Corollary: self-intro with empty seen. -/
theorem VCompat.from_self_intro {fuel : Nat} {ctx : TyCtx} {n : Nat} {σ : Expr}
    {ann body : Expr}
    (hσ_not_mu : ∀ ann' body', σ ≠ .mu ann' body')
    (hcheck : subCheckNF fuel ctx [] σ (.mu ann body) = true)
    : VCompat n σ (.mu ann body) :=
  VCompat.from_self_intro_gen fuel n σ ctx [] hσ_not_mu ann body hcheck
    (fun p hp => absurd hp (List.not_mem_nil p))

/-- VCompat respects subCheckNF (adequacy). -/
theorem VCompat.adequacy {n : Nat} {v σ τ : Expr} {fuel : Nat} {ctx : TyCtx}
    (hv : VCompat n v σ) (hcheck : subCheckNF fuel ctx [] σ τ = true)
    : VCompat n v τ := by
  -- Needs update for new mutual absEval/subCheckNF definition
  sorry

/-! ## VCompat-equivalence lemmas -/

/-- Substitution at index j is a vEquiv-no-op for closedEvalB j expressions. -/
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

/-- vEquiv is preserved by shift. -/
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

/-- vEquiv is preserved by substitution. -/
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
  | zero => simp [VCompat]
  | succ k => unfold VCompat; exact Or.inr (Or.inl rfl)

/-- vEquivB is reflexive. -/
theorem Expr.vEquivB_refl : ∀ (e : Expr), e.vEquivB e = true
  | .bvar k => by simp [Expr.vEquivB, BEq.beq, decEq]
  | .lam dom body => by simp [Expr.vEquivB]; exact Expr.vEquivB_refl body
  | .app f a => by simp [Expr.vEquivB, Bool.and_eq_true]; exact ⟨Expr.vEquivB_refl f, Expr.vEquivB_refl a⟩
  | .asc t y => by simp [Expr.vEquivB, Bool.and_eq_true]; exact ⟨Expr.vEquivB_refl t, Expr.vEquivB_refl y⟩
  | .type => by simp [Expr.vEquivB]
  | .mu ann body => by simp [Expr.vEquivB]; exact Expr.vEquivB_refl body

-- Shape lemmas for vEquivB
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

/-- inferType is compatible with vEquiv. -/
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

/-- VCompat is invariant under vEquiv. -/
theorem VCompat_of_vEquivB {n : Nat} {v v' τ τ' : Expr}
    (hv : v'.vEquivB v = true) (hτ : τ'.vEquivB τ = true)
    (h : VCompat n v τ) : VCompat n v' τ' := by
  -- Needs update for new VCompat definition (absEval in semantic lam uses [] not env)
  sorry

/-- Evaluator outputs satisfy closedEvalB 0. -/
theorem concEvalE_closedEvalB {fuel : Nat} {env : Env} {e v : Expr}
    (h : concEvalE fuel env e = some v)
    (henv : ∀ k e', env.get? k = some e' → e'.closedEvalB 0 = true)
    : v.closedEvalB 0 = true := by
  sorry

theorem absEval_closedEvalB {fuel : Nat} {ctx : TyCtx} {e v : Expr}
    (h : absEval fuel ctx e = .ok v)
    : v.closedEvalB 0 = true := by
  sorry

/-! ## Soundness theorem

The WellTyped precondition is gone — absEval now validates ascriptions
and callability internally. A term is well-typed iff absEval succeeds. -/

/-- Generalized soundness with concEvalE.

    KEY CHANGE: No WellTyped precondition. absEval succeeding implies
    the term is well-typed (ascriptions are checked, callability is validated).

    KEY DESIGN: the VCompat step index `n` is decoupled from `fuel`.
    soundness_gen proves VCompat at ALL step levels simultaneously. -/
theorem soundness_gen
    (fuel : Nat) (env : Env) (e : Expr) (v τ : Expr) (n : Nat)
    (h_conc : concEvalE fuel env e = some v)
    (h_abs : absEval fuel [] e = .ok τ)
    : VCompat n v τ := by
  -- The proof structure changes significantly with the new absEval.
  -- absEval no longer takes an env, and concEvalE still does.
  -- The parallel recursion structure is broken — these need different approaches.
  -- Sorry for now; the key contribution is the simplified theorem statement.
  sorry

/-- Soundness for the env-based concrete evaluator. -/
theorem soundness
    (fuel : Nat) (e : Expr) (v τ : Expr) (n : Nat)
    (h_conc : concEvalE fuel [] e = some v)
    (h_abs : absEval fuel [] e = .ok τ)
    : VCompat n v τ :=
  soundness_gen fuel [] e v τ n h_conc h_abs

/-- Soundness for the substitution-based runtime (concEval). -/
theorem soundness_concEval
    (fuel : Nat) (e : Expr) (v τ : Expr) (n : Nat)
    (h_conc : concEval fuel e = some v)
    (h_abs : absEval fuel [] e = .ok τ)
    : VCompat n v τ := by
  sorry  -- needs concEval → concEvalE bridge

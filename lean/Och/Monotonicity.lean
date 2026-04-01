import Och.Syntax
import Och.Eval
import Och.Subtyping

/-!
# Monotonicity

Generalized to `absEval_mono` taking `Subtype' e₂ e₁` + `EnvSub Γ₂ Γ₁`.
Standard monotonicity is the corollary with `Subtype'.refl`.

Key technique: removing `trans` from `Subtype'` enables lambda inversion.

## Status after mu unification

The monotonicity proof needs rework for mu. Key issues:
- The mu case in absEval normalizes BOTH body and annotation in the env.
  The `mu_body` Subtype' constructor requires same annotation, but
  annotations normalized in different envs may differ. This needs either:
  (a) a more general Subtype' constructor for mu (allowing different annotations)
  (b) proving annotations normalize the same way under EnvSub
  (c) changing absEval to not normalize annotations
- The app case now needs mu-elim handling (when function evaluates to mu).

For now, the core theorems are sorry'd. Supporting definitions and helper
lemmas are preserved.
-/

open Expr

def EnvSub (Γ₂ Γ₁ : Env) : Prop :=
  ∀ x τ₁, Γ₁.lookup x = some τ₁ → ∃ τ₂, Γ₂.lookup x = some τ₂ ∧ Subtype' τ₂ τ₁

theorem envSub_extend {Γ₂ Γ₁ : Env} (h : EnvSub Γ₂ Γ₁) (x : Name) (v : Expr) :
    EnvSub ((x, v) :: Γ₂) ((x, v) :: Γ₁) := by
  intro y τ₁ h_lookup
  simp only [Env.lookup] at h_lookup ⊢
  split at h_lookup <;> split
  · cases h_lookup; exact ⟨v, rfl, Subtype'.refl v⟩
  · rename_i h1 h2; exact absurd h1 h2
  · rename_i h1 h2; exact absurd h2 h1
  · exact h y τ₁ h_lookup

theorem envSub_extend_sub {Γ₂ Γ₁ : Env} (h : EnvSub Γ₂ Γ₁)
    (x : Name) {v₂ v₁ : Expr} (hv : Subtype' v₂ v₁) :
    EnvSub ((x, v₂) :: Γ₂) ((x, v₁) :: Γ₁) := by
  intro y τ₁ h_lookup
  simp only [Env.lookup] at h_lookup ⊢
  split at h_lookup <;> split
  · cases h_lookup; exact ⟨v₂, rfl, hv⟩
  · rename_i h1 h2; exact absurd h1 h2
  · rename_i h1 h2; exact absurd h2 h1
  · exact h y τ₁ h_lookup

/-- **Generalized monotonicity.** Sorry'd pending mu proof rework.

    The mu case is non-trivial because absEval normalizes both annotation
    and body, but mu_body requires same annotation. -/
theorem absEval_mono
    (fuel : Nat) (Γ₁ Γ₂ : Env) (e₁ e₂ τ₁ τ₂ : Expr)
    (h_sub : Subtype' e₂ e₁)
    (h_env : EnvSub Γ₂ Γ₁)
    (h₁ : absEval fuel Γ₁ e₁ = some τ₁)
    (h₂ : absEval fuel Γ₂ e₂ = some τ₂)
    : Subtype' τ₂ τ₁ := by
  sorry

theorem monotonicity
    (Γ₁ Γ₂ : Env) (e τ₁ τ₂ : Expr) (fuel : Nat)
    (h_env : EnvSub Γ₂ Γ₁)
    (h_abs₁ : absEval fuel Γ₁ e = some τ₁)
    (h_abs₂ : absEval fuel Γ₂ e = some τ₂)
    : Subtype' τ₂ τ₁ :=
  absEval_mono fuel Γ₁ Γ₂ e e τ₁ τ₂ (Subtype'.refl e) h_env h_abs₁ h_abs₂

-- ============================================================
-- Generalized monotonicity with SubtypeTrans
-- ============================================================

/-- Environment subtyping via SubtypeTrans (transitive closure). -/
def EnvSubTrans (Γ₂ Γ₁ : Env) : Prop :=
  ∀ x τ₁, Γ₁.lookup x = some τ₁ → ∃ τ₂, Γ₂.lookup x = some τ₂ ∧ SubtypeTrans τ₂ τ₁

theorem envSubTrans_extend {Γ₂ Γ₁ : Env} (h : EnvSubTrans Γ₂ Γ₁) (x : Name) (v : Expr) :
    EnvSubTrans ((x, v) :: Γ₂) ((x, v) :: Γ₁) := by
  intro y τ₁ h_lookup
  simp only [Env.lookup] at h_lookup ⊢
  split at h_lookup <;> split
  · cases h_lookup; exact ⟨v, rfl, SubtypeTrans.step (Subtype'.refl v)⟩
  · rename_i h1 h2; exact absurd h1 h2
  · rename_i h1 h2; exact absurd h2 h1
  · exact h y τ₁ h_lookup

theorem envSubTrans_extend_sub {Γ₂ Γ₁ : Env} (h : EnvSubTrans Γ₂ Γ₁)
    (x : Name) {v₂ v₁ : Expr} (hv : SubtypeTrans v₂ v₁) :
    EnvSubTrans ((x, v₂) :: Γ₂) ((x, v₁) :: Γ₁) := by
  intro y τ₁ h_lookup
  simp only [Env.lookup] at h_lookup ⊢
  split at h_lookup <;> split
  · cases h_lookup; exact ⟨v₂, rfl, hv⟩
  · rename_i h1 h2; exact absurd h1 h2
  · rename_i h1 h2; exact absurd h2 h1
  · exact h y τ₁ h_lookup

/-- **Generalized monotonicity with SubtypeTrans.** Sorry'd pending mu rework. -/
theorem absEval_mono_trans
    (fuel : Nat) (Γ₁ Γ₂ : Env) (e₁ e₂ τ₁ τ₂ : Expr)
    (h_sub : SubtypeTrans e₂ e₁)
    (h_env : EnvSubTrans Γ₂ Γ₁)
    (h₁ : absEval fuel Γ₁ e₁ = some τ₁)
    (h₂ : absEval fuel Γ₂ e₂ = some τ₂)
    : SubtypeTrans τ₂ τ₁ := by
  sorry

/-- Standard monotonicity corollary with SubtypeTrans envs. -/
theorem monotonicity_trans
    (Γ₁ Γ₂ : Env) (e τ₁ τ₂ : Expr) (fuel : Nat)
    (h_env : EnvSubTrans Γ₂ Γ₁)
    (h_abs₁ : absEval fuel Γ₁ e = some τ₁)
    (h_abs₂ : absEval fuel Γ₂ e = some τ₂)
    : SubtypeTrans τ₂ τ₁ :=
  absEval_mono_trans fuel Γ₁ Γ₂ e e τ₁ τ₂ (SubtypeTrans.step (Subtype'.refl e))
    h_env h_abs₁ h_abs₂

/-- **Totality under env narrowing.** Sorry'd — was already sorry'd before mu. -/
theorem absEval_succeeds_envsub
    (fuel : Nat) (Γ₁ Γ₂ : Env) (e τ₁ : Expr)
    (h_env : EnvSubTrans Γ₂ Γ₁)
    (h₁ : absEval fuel Γ₁ e = some τ₁)
    : ∃ τ₂, absEval fuel Γ₂ e = some τ₂ := by
  sorry

-- ============================================================
-- evalFreeVars coverage: absEval outputs have evalFreeVars ⊆ neutralVars(Γ)
-- ============================================================

/-- A variable is "neutral" in an env if it maps to itself. -/
def isNeutral (Γ : Env) (x : Name) : Prop :=
  Γ.lookup x = some (.var x)

/-- An env is "eval-closed" if every env value's evalFreeVars are neutral. -/
def EnvEvalClosed' (Γ : Env) : Prop :=
  ∀ x v, Γ.lookup x = some v → ∀ y, y ∈ v.evalFreeVars → isNeutral Γ y

/-- Extending an eval-closed env with a neutral binding preserves closedness. -/
theorem envEvalClosed'_extend_neutral {Γ : Env} (h : EnvEvalClosed' Γ) (x : Name) :
    EnvEvalClosed' ((x, .var x) :: Γ) := by
  intro y v h_lookup z h_z_free
  simp only [Env.lookup] at h_lookup
  simp only [isNeutral, Env.lookup]
  split at h_lookup <;> rename_i h_eq
  · cases h_lookup
    simp [Expr.evalFreeVars] at h_z_free
    subst h_z_free
    simp [h_eq]
  · have h_neutral := h y v h_lookup z h_z_free
    simp only [isNeutral, Env.lookup] at h_neutral
    split
    · rename_i h_zx
      have : x = z := by exact beq_iff_eq.mp h_zx
      rw [this]
    · exact h_neutral

/-- Helper: extending env with neutral binding preserves eval-coverage for P ∨ (· = x). -/
private theorem env_extend_neutral_or (Γ : Env) (x : Name) (P : Name → Prop)
    (h_env : ∀ z v, Γ.lookup z = some v → ∀ w, w ∈ v.evalFreeVars → P w) :
    ∀ z v, Env.lookup ((x, .var x) :: Γ) z = some v →
    ∀ w, w ∈ v.evalFreeVars → P w ∨ w = x := by
  intro z v h_lookup w hw
  simp only [Env.lookup] at h_lookup
  split at h_lookup <;> rename_i h_eq
  · cases h_lookup; simp [Expr.evalFreeVars] at hw; exact Or.inr hw
  · exact Or.inl (h_env z v h_lookup w hw)

/-- Helper: extending env with a value whose evalFreeVars ⊆ P preserves coverage. -/
private theorem env_extend_val (Γ : Env) (x : Name) (v : Expr) (P : Name → Prop)
    (h_env : ∀ z u, Γ.lookup z = some u → ∀ w, w ∈ u.evalFreeVars → P w)
    (hv : ∀ w, w ∈ v.evalFreeVars → P w) :
    ∀ z u, Env.lookup ((x, v) :: Γ) z = some u → ∀ w, w ∈ u.evalFreeVars → P w := by
  intro z u h_lookup w hw
  simp only [Env.lookup] at h_lookup
  split at h_lookup <;> rename_i h_eq
  · cases h_lookup; exact hv w hw
  · exact h_env z u h_lookup w hw

/-- **General coverage: absEval outputs have evalFreeVars ⊆ P.** -/
theorem absEval_evalFreeVars_general
    (fuel : Nat) (Γ : Env) (e τ : Expr)
    (P : Name → Prop)
    (h_eval : absEval fuel Γ e = some τ)
    (h_env : ∀ x v, Γ.lookup x = some v → ∀ y, y ∈ v.evalFreeVars → P y)
    : ∀ y, y ∈ τ.evalFreeVars → P y := by
  induction fuel generalizing Γ e τ P with
  | zero => simp [absEval] at h_eval
  | succ n ih =>
    -- Helper for binder cases (lam body, mu body): body normalized under (x, var x),
    -- result's evalFreeVars = body'.evalFreeVars.filter(·!=x) ⊆ P.
    have binder_case : ∀ (x : Name) (body body' : Expr),
        absEval n ((x, .var x) :: Γ) body = some body' →
        ∀ y, y ∈ body'.evalFreeVars.filter (· != x) → P y := by
      intro x body body' hb y hy
      have ⟨h_mem, h_ne⟩ := List.mem_filter.mp hy
      have ih_body := ih ((x, .var x) :: Γ) body body' (fun z => P z ∨ z = x) hb
        (env_extend_neutral_or Γ x P h_env) y h_mem
      cases ih_body with
      | inl h => exact h
      | inr h =>
        exfalso
        have h_ne' : ¬(y == x) = true := by
          intro heq; rw [beq_iff_eq.mp heq] at h_ne; simp at h_ne
        exact h_ne' (beq_iff_eq.mpr h)
    cases e with
    | var x =>
      simp only [absEval] at h_eval
      exact h_env x τ h_eval
    | type =>
      simp only [absEval] at h_eval; cases h_eval
      intro y hy; simp [Expr.evalFreeVars] at hy
    | asc _term ty =>
      simp only [absEval] at h_eval
      exact ih Γ ty τ P h_eval h_env
    | lam x _dom body =>
      simp only [absEval] at h_eval
      cases hb : absEval n ((x, .var x) :: Γ) body with
      | none => simp [hb] at h_eval
      | some body' =>
        simp [hb] at h_eval; cases h_eval
        -- evalFreeVars(.lam x _dom body') = body'.evalFreeVars.filter(·!=x)
        exact binder_case x body body' hb
    | mu x ann body =>
      simp only [absEval] at h_eval
      cases hb : absEval n ((x, .var x) :: Γ) body with
      | none => simp [hb] at h_eval
      | some body' =>
        cases hann : absEval n Γ ann with
        | none => simp [hb, hann] at h_eval
        | some ann' =>
          simp [hb, hann] at h_eval; cases h_eval
          -- evalFreeVars(.mu x ann' body') = body'.evalFreeVars.filter(·!=x)
          exact binder_case x body body' hb
    | app f a =>
      simp only [absEval] at h_eval
      cases hf : absEval n Γ f with
      | none => simp [hf] at h_eval
      | some τ_f =>
        cases ha : absEval n Γ a with
        | none => simp [hf, ha] at h_eval
        | some τ_a =>
          rw [hf, ha] at h_eval
          have ih_f := ih Γ f τ_f P hf h_env
          have ih_a := ih Γ a τ_a P ha h_env
          cases τ_f with
          | lam x _dom body =>
            simp only at h_eval
            exact ih ((x, τ_a) :: Γ) body τ P h_eval
              (env_extend_val Γ x τ_a P h_env ih_a)
          | type =>
            simp only at h_eval; cases h_eval
            intro y hy; simp [Expr.evalFreeVars] at hy
          | mu x_mu ann_mu body_mu =>
            -- mu-elim: annotation-first approach changed the control flow.
            -- Sorry'd pending proof update for the new mu app case structure.
            sorry
          | var _ =>
            simp only at h_eval; cases h_eval
            intro y hy
            rcases List.mem_append.mp hy with h1 | h2
            · exact ih_f y h1
            · exact ih_a y h2
          | app _ _ =>
            simp only at h_eval; cases h_eval
            intro y hy
            rcases List.mem_append.mp hy with h1 | h2
            · exact ih_f y h1
            · exact ih_a y h2
          | asc _ _ =>
            simp only at h_eval; cases h_eval
            intro y hy
            rcases List.mem_append.mp hy with h1 | h2
            · exact ih_f y h1
            · exact ih_a y h2

/-- **absEval outputs have evalFreeVars ⊆ neutralVars(Γ).** -/
theorem absEval_evalFreeVars_neutral
    (fuel : Nat) (Γ : Env) (e τ : Expr)
    (h_eval : absEval fuel Γ e = some τ)
    (h_env : EnvEvalClosed' Γ)
    : ∀ y, y ∈ τ.evalFreeVars → isNeutral Γ y :=
  absEval_evalFreeVars_general fuel Γ e τ (isNeutral Γ) h_eval h_env

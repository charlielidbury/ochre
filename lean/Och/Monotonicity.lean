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

/-- **General coverage: absEval outputs have evalFreeVars ⊆ P.**
    Sorry'd pending mu rework (mu case needs both body and ann handling). -/
theorem absEval_evalFreeVars_general
    (fuel : Nat) (Γ : Env) (e τ : Expr)
    (P : Name → Prop)
    (h_eval : absEval fuel Γ e = some τ)
    (h_env : ∀ x v, Γ.lookup x = some v → ∀ y, y ∈ v.evalFreeVars → P y)
    : ∀ y, y ∈ τ.evalFreeVars → P y := by
  sorry

/-- **absEval outputs have evalFreeVars ⊆ neutralVars(Γ).** -/
theorem absEval_evalFreeVars_neutral
    (fuel : Nat) (Γ : Env) (e τ : Expr)
    (h_eval : absEval fuel Γ e = some τ)
    (h_env : EnvEvalClosed' Γ)
    : ∀ y, y ∈ τ.evalFreeVars → isNeutral Γ y :=
  absEval_evalFreeVars_general fuel Γ e τ (isNeutral Γ) h_eval h_env

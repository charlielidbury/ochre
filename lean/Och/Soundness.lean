import Och.Syntax
import Och.Eval
import Och.Subtyping
import Och.Monotonicity

/-!
# Soundness

If abstract evaluation says `e` has type `τ`, and concrete evaluation
produces value `v`, then `v ⊑ τ` (in SubtypeTrans).

The proof produces `SubtypeTrans` because the ascription case chains
the IH result with the well-typedness hypothesis via transitivity.
-/

open Expr

def EnvConsistent (γ : Env) (Γ : Env) : Prop :=
  ∀ x τ, Γ.lookup x = some τ → ∃ v, γ.lookup x = some v ∧ SubtypeTrans v τ

/-- Well-typedness: all ascriptions encountered during evaluation are sound.
    Uses closure-based eval in the app case (matching the evaluator). -/
def WellTyped (fuel : Nat) (Γ : Env) (e : Expr) : Prop :=
  match fuel with
  | 0 => True
  | fuel + 1 =>
    match e with
    | .var _ => True
    | .lam x _ body => WellTyped fuel ((x, .var x) :: Γ) body
    | .type => True
    | .asc term ty =>
        WellTyped fuel Γ term ∧ WellTyped fuel Γ ty ∧
        ∃ σ τ', absEval fuel Γ term = some σ ∧
                absEval fuel Γ ty = some τ' ∧
                Subtype' σ τ'
    | .app f a =>
        WellTyped fuel Γ f ∧ WellTyped fuel Γ a ∧
        match absEval fuel Γ f, absEval fuel Γ a with
        | some (.lam x _ body), some aVal => WellTyped fuel ((x, aVal) :: Γ) body
        | _, _ => True

theorem envConsistent_extend {γ Γ : Env} (h : EnvConsistent γ Γ) (x : Name) (v : Expr) :
    EnvConsistent ((x, v) :: γ) ((x, v) :: Γ) := by
  intro y τ h_lookup
  simp only [Env.lookup] at h_lookup ⊢
  split at h_lookup <;> split
  · cases h_lookup; exact ⟨v, rfl, SubtypeTrans.step (Subtype'.refl v)⟩
  · rename_i h1 h2; exact absurd h1 h2
  · rename_i h1 h2; exact absurd h2 h1
  · exact h y τ h_lookup

/-- **Soundness theorem.**

    Standard soundness (same expression in both evaluators).
    For now, the app case is left as sorry since it requires a
    generalized statement (like monotonicity's absEval_mono). -/
theorem soundness
    (Γ : Env) (γ : Env) (e τ v : Expr) (fuel : Nat)
    (h_abs : absEval fuel Γ e = some τ)
    (h_conc : concEval fuel γ e = some v)
    (h_env : EnvConsistent γ Γ)
    (h_wt : WellTyped fuel Γ e)
    : SubtypeTrans v τ := by
  induction fuel generalizing Γ γ e τ v with
  | zero => simp [absEval] at h_abs
  | succ n ih =>
    cases e with
    | var x =>
      simp [absEval, concEval] at h_abs h_conc
      have ⟨val, h_lv, h_sub⟩ := h_env x τ h_abs
      rw [h_lv] at h_conc; cases h_conc; exact h_sub
    | type =>
      simp [absEval, concEval] at h_abs h_conc
      rw [← h_abs, ← h_conc]; exact SubtypeTrans.step (Subtype'.refl .type)
    | lam x dom body =>
      simp only [absEval, concEval] at h_abs h_conc
      cases hb_abs : absEval n ((x, .var x) :: Γ) body with
      | none => simp [hb_abs] at h_abs
      | some body_a =>
        simp [hb_abs] at h_abs
        cases hb_conc : concEval n ((x, .var x) :: γ) body with
        | none => simp [hb_conc] at h_conc
        | some body_c =>
          simp [hb_conc] at h_conc; rw [← h_abs, ← h_conc]
          have h_env' := envConsistent_extend h_env x (.var x)
          have h_wt' : WellTyped n ((x, .var x) :: Γ) body := h_wt
          have ih_body := ih _ _ body _ _ hb_abs hb_conc h_env' h_wt'
          exact SubtypeTrans.lam_body ih_body
    | asc term ty =>
      simp only [absEval, concEval] at h_abs h_conc
      have ⟨h_wt_term, _, σ, τ', h_abs_term, h_abs_ty, h_sub_wt⟩ := h_wt
      rw [h_abs] at h_abs_ty; cases h_abs_ty
      have h_vs := ih Γ γ term σ v h_abs_term h_conc h_env h_wt_term
      exact SubtypeTrans.trans h_vs (SubtypeTrans.step h_sub_wt)
    | app f a =>
      -- Both evaluators: eval f, eval a, then beta-reduce or stuck
      -- This case requires a generalized soundness (like absEval_mono)
      -- since beta-reduction uses different normalized bodies.
      sorry

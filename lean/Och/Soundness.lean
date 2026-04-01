import Och.Syntax
import Och.Eval
import Och.Subtyping
import Och.Monotonicity

/-!
# Soundness

If abstract evaluation says `e` has type `τ`, and concrete evaluation
produces value `v`, then `v ⊑ τ` (in SubtypeTrans).

The proof uses a generalized `soundness_gen` that takes `SubtypeTrans e_c e_a`
(related expressions) since the app-beta case produces different normalized
bodies from the function IH.

## Status after mu unification

The soundness proof needs to be redone for the mu constructor. The fix and
iota cases have been merged into a single mu case. Key changes:
- WellTyped needs a mu case (replacing fix and iota cases)
- EnvNoFix is replaced by EnvNoMu (same idea: absEval doesn't return mu... wait, it DOES now)
- Actually, absEval now RETURNS mu terms (unlike fix which was eliminated to dom).
  This means the soundness proof structure changes significantly.
  The app case now has a mu-elim branch to handle.

For now, the proof is sorry'd. The definitions are updated to compile.
-/

open Expr

def EnvConsistent (γ : Env) (Γ : Env) : Prop :=
  ∀ x τ, Γ.lookup x = some τ → ∃ v, γ.lookup x = some v ∧ SubtypeTrans v τ

/-- Well-typedness: all ascriptions encountered during evaluation are sound. -/
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
    | .mu x _ann body =>
        -- mu well-typedness: body is well-typed under (x, var x)
        WellTyped fuel ((x, .var x) :: Γ) body
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

theorem envConsistent_extend_sub {γ Γ : Env} (h : EnvConsistent γ Γ)
    (x : Name) {v τ : Expr} (hv : SubtypeTrans v τ) :
    EnvConsistent ((x, v) :: γ) ((x, τ) :: Γ) := by
  intro y σ h_lookup
  simp only [Env.lookup] at h_lookup ⊢
  split at h_lookup <;> split
  · cases h_lookup; exact ⟨v, rfl, hv⟩
  · rename_i h1 h2; exact absurd h1 h2
  · rename_i h1 h2; exact absurd h2 h1
  · exact h y σ h_lookup

/-- **Generalized soundness.** Sorry'd pending mu proof rework.

    The proof structure changes with mu because absEval now returns mu terms
    (not annotations), and the app case needs mu-elim handling. -/
theorem soundness_gen
    (fuel : Nat) (Γ : Env) (γ : Env) (e_a e_c τ v : Expr)
    (h_sub : SubtypeTrans e_c e_a)
    (h_abs : absEval fuel Γ e_a = some τ)
    (h_conc : concEval fuel γ e_c = some v)
    (h_env : EnvConsistent γ Γ)
    (h_wt : WellTyped fuel Γ e_a)
    : SubtypeTrans v τ := by
  sorry

/-- **Soundness theorem.**

    If abstract evaluation gives type `τ` and concrete evaluation gives value `v`,
    then `SubtypeTrans v τ`. -/
theorem soundness
    (Γ : Env) (γ : Env) (e τ v : Expr) (fuel : Nat)
    (h_abs : absEval fuel Γ e = some τ)
    (h_conc : concEval fuel γ e = some v)
    (h_env : EnvConsistent γ Γ)
    (h_wt : WellTyped fuel Γ e)
    : SubtypeTrans v τ :=
  soundness_gen fuel Γ γ e e τ v (SubtypeTrans.step (Subtype'.refl e))
    h_abs h_conc h_env h_wt

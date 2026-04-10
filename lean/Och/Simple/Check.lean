import Och.Simple.Syntax
import Och.Simple.Subtype
import Och.Simple.Eval

/-!
# Bidirectional Subtype Checker for Simple Och (no μ)

A fuel-indexed, decidable checker for the subtype relation `Sub`. Because the
Simple Och calculus has no μ, there are no cycles. Fuel guarantees termination
and is decremented on every recursive call.

## Structure

- `synthLam fuel Γ e` : `Option (Expr × Expr)`
  Synthesizes a function type for `e`: if it returns `some (D, R)` then
  `Sub Γ e (.lam D R)` holds.
- `subCheck fuel Γ a b` : `Bool`
  Decides `Sub Γ a b`.

Soundness is proven in `synthLam_sound` and `subCheck_sound`.
-/

set_option autoImplicit false

namespace Och.Simple

open Expr

mutual

/-- Synthesize a "function type" for `e`: returns `some (D, R)` such that
    `Sub Γ e (.lam D R)` is derivable (see `synthLam_sound`). -/
def synthLam (fuel : Nat) (Γ : Ctx) (e : Expr) : Option (Expr × Expr) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match e with
    | .lam D R => some (D, R)
    | .var x =>
      match Γ.get? x with
      | none => none
      | some T => synthLam fuel Γ T
    | .asc e' τ =>
      if subCheck fuel Γ e' τ then synthLam fuel Γ τ else none
    | .app f' a' =>
      match synthLam fuel Γ f' with
      | none => none
      | some (D'', R'') =>
        if subCheck fuel Γ a' D'' then synthLam fuel Γ (R''.subst 0 a')
        else none
    | .top => none

/-- Decide `Sub Γ a b` up to the supplied `fuel`.

    The dispatch is structured to make soundness easy to prove: the rules are
    tried in a deterministic order (Refl → Top → Asc-R → Asc-L → Var → Lam → App)
    with non-overlapping conditions. -/
def subCheck (fuel : Nat) (Γ : Ctx) (a b : Expr) : Bool :=
  match fuel with
  | 0 => false
  | fuel + 1 =>
    if a == b then true  -- [Refl]
    else if b == .top then true  -- [Top]
    else
      subCheckStep fuel Γ a b

/-- Post-Refl/Top dispatcher. Factored out so that the soundness proof can
    pattern-match uniformly on the shape of `a` / `b`. -/
def subCheckStep (fuel : Nat) (Γ : Ctx) (a b : Expr) : Bool :=
  match b with
  -- [Asc-R]: a ⊑ (e : τ)
  | .asc e τ => subCheck fuel Γ e τ && subCheck fuel Γ a e
  | _ =>
    match a with
    -- [Asc-L]: (e : τ) ⊑ b
    | .asc e τ => subCheck fuel Γ e τ && subCheck fuel Γ τ b
    -- [Var]
    | .var x =>
      match Γ.get? x with
      | none => false
      | some T => subCheck fuel Γ T b
    -- [Lam] — only fires when b is also a lam
    | .lam A₁ b₁ =>
      match b with
      | .lam A₂ b₂ =>
        subCheck fuel Γ A₂ A₁ && subCheck fuel (A₂ :: Γ) b₁ b₂
      | _ => false
    -- [App]
    | .app f arg =>
      match synthLam fuel Γ f with
      | none => false
      | some (D, R) =>
        subCheck fuel Γ arg D && subCheck fuel Γ (R.subst 0 arg) b
    | .top => false

end  -- mutual

/-- Top-level `check` (alias for `subCheck`). -/
def check (fuel : Nat) (Γ : Ctx) (e τ : Expr) : Bool :=
  subCheck fuel Γ e τ

-- ============================================================
-- Soundness: subCheck and synthLam are sound w.r.t. the inductive Sub
-- ============================================================

-- Helper: destructing conjunction from Bool.and_eq_true
private theorem bool_and_split {x y : Bool} (h : (x && y) = true) : x = true ∧ y = true := by
  cases x <;> cases y <;> simp_all

mutual

/-- `synthLam` soundness: if `synthLam fuel Γ e = some (D, R)` then
    `Sub Γ e (.lam D R)`. -/
noncomputable def synthLam_sound :
    (fuel : Nat) → (Γ : Ctx) → (e : Expr) → (D R : Expr) →
    synthLam fuel Γ e = some (D, R) → Sub Γ e (.lam D R)
  | 0, _, _, _, _, h => by simp [synthLam] at h
  | fuel + 1, Γ, e, D, R, h => by
    cases e with
    | lam D' R' =>
      simp only [synthLam] at h
      obtain ⟨hD, hR⟩ : D' = D ∧ R' = R := by
        have := h
        simp at this
        exact this
      subst hD; subst hR
      exact Sub.refl Γ (.lam D' R')
    | var x =>
      simp only [synthLam] at h
      cases hget : Γ.get? x with
      | none => rw [hget] at h; simp at h
      | some T =>
        rw [hget] at h
        have ih := synthLam_sound fuel Γ T D R h
        exact Sub.var Γ x (.lam D R) T hget ih
    | asc e' τ =>
      simp only [synthLam] at h
      by_cases hcheck : subCheck fuel Γ e' τ = true
      · rw [if_pos hcheck] at h
        have hsub_eτ : Sub Γ e' τ := subCheck_sound fuel Γ e' τ hcheck
        have ih : Sub Γ τ (.lam D R) := synthLam_sound fuel Γ τ D R h
        exact Sub.ascL Γ e' τ (.lam D R) hsub_eτ ih
      · rw [if_neg hcheck] at h; simp at h
    | app f a =>
      simp only [synthLam] at h
      cases hf : synthLam fuel Γ f with
      | none => rw [hf] at h; simp at h
      | some p =>
        obtain ⟨D'', R''⟩ := p
        rw [hf] at h
        first | (exact Bool.noConfusion h) | (simp only at h)
        by_cases hcheck : subCheck fuel Γ a D'' = true
        · rw [if_pos hcheck] at h
          have hf_sub : Sub Γ f (.lam D'' R'') := synthLam_sound fuel Γ f D'' R'' hf
          have ha_sub : Sub Γ a D'' := subCheck_sound fuel Γ a D'' hcheck
          have hR_sub : Sub Γ (R''.subst 0 a) (.lam D R) :=
            synthLam_sound fuel Γ (R''.subst 0 a) D R h
          exact Sub.app Γ f a (.lam D R) D'' R'' hf_sub ha_sub hR_sub
        · rw [if_neg hcheck] at h; simp at h
    | top => simp [synthLam] at h

/-- `subCheck` soundness: if `subCheck fuel Γ a b = true` then `Sub Γ a b`. -/
noncomputable def subCheck_sound :
    (fuel : Nat) → (Γ : Ctx) → (a b : Expr) →
    subCheck fuel Γ a b = true → Sub Γ a b
  | 0, _, _, _, h => by simp [subCheck] at h
  | fuel + 1, Γ, a, b, h => by
    simp only [subCheck] at h
    by_cases heq : (a == b) = true
    · have : a = b := beq_iff_eq.mp heq
      subst this
      exact Sub.refl Γ a
    · rw [if_neg heq] at h
      by_cases htop : (b == .top) = true
      · have : b = .top := beq_iff_eq.mp htop
        subst this
        exact Sub.top Γ a
      · rw [if_neg htop] at h
        -- Now h : subCheckStep (fuel+1) Γ a b = true
        -- Note: we still have fuel+1 as the fuel parameter because subCheck
        -- unfolded once and called subCheckStep with its same fuel.
        exact subCheckStep_sound fuel Γ a b htop h

/-- `subCheckStep` soundness. `htop : ¬(b == .top)` is needed because
    `subCheckStep` doesn't handle Top — that's dispatched in `subCheck`. -/
noncomputable def subCheckStep_sound :
    (fuel : Nat) → (Γ : Ctx) → (a b : Expr) →
    ¬ (b == .top) = true →
    subCheckStep fuel Γ a b = true → Sub Γ a b := by
  intro fuel Γ a b htop h
  unfold subCheckStep at h
  -- Case analysis: is b an asc?
  cases hb : b with
  | asc e τ =>
    subst hb
    first | (exact Bool.noConfusion h) | (simp only at h)
    obtain ⟨h1, h2⟩ := bool_and_split h
    have hs1 : Sub Γ e τ := subCheck_sound fuel Γ e τ h1
    have hs2 : Sub Γ a e := subCheck_sound fuel Γ a e h2
    exact Sub.ascR Γ a e τ hs1 hs2
  | var x_b =>
    subst hb
    first | (exact Bool.noConfusion h) | (simp only at h)
    cases ha : a with
    | asc e τ =>
      subst ha
      first | (exact Bool.noConfusion h) | (simp only at h)
      obtain ⟨h1, h2⟩ := bool_and_split h
      have hs1 : Sub Γ e τ := subCheck_sound fuel Γ e τ h1
      have hs2 : Sub Γ τ (.var x_b) := subCheck_sound fuel Γ τ (.var x_b) h2
      exact Sub.ascL Γ e τ (.var x_b) hs1 hs2
    | var x_a =>
      subst ha
      first | (exact Bool.noConfusion h) | (simp only at h)
      cases hget : Γ.get? x_a with
      | none => rw [hget] at h; simp at h
      | some T =>
        rw [hget] at h
        have hs : Sub Γ T (.var x_b) := subCheck_sound fuel Γ T (.var x_b) h
        exact Sub.var Γ x_a (.var x_b) T hget hs
    | lam A₁ b₁ =>
      subst ha
      first | (exact Bool.noConfusion h) | (simp only at h)
    | app f arg =>
      subst ha
      first | (exact Bool.noConfusion h) | (simp only at h)
      cases hsy : synthLam fuel Γ f with
      | none => rw [hsy] at h; simp at h
      | some p =>
        obtain ⟨D, R⟩ := p
        rw [hsy] at h
        first | (exact Bool.noConfusion h) | (simp only at h)
        obtain ⟨h1, h2⟩ := bool_and_split h
        have hf_sub : Sub Γ f (.lam D R) := synthLam_sound fuel Γ f D R hsy
        have ha_sub : Sub Γ arg D := subCheck_sound fuel Γ arg D h1
        have hR_sub : Sub Γ (R.subst 0 arg) (.var x_b) :=
          subCheck_sound fuel Γ (R.subst 0 arg) (.var x_b) h2
        exact Sub.app Γ f arg (.var x_b) D R hf_sub ha_sub hR_sub
    | top =>
      subst ha
      first | (exact Bool.noConfusion h) | (simp only at h)
  | top =>
    subst hb
    exfalso; apply htop; simp
  | lam A₂ b₂ =>
    subst hb
    first | (exact Bool.noConfusion h) | (simp only at h)
    cases ha : a with
    | asc e τ =>
      subst ha
      first | (exact Bool.noConfusion h) | (simp only at h)
      obtain ⟨h1, h2⟩ := bool_and_split h
      have hs1 : Sub Γ e τ := subCheck_sound fuel Γ e τ h1
      have hs2 : Sub Γ τ (.lam A₂ b₂) := subCheck_sound fuel Γ τ (.lam A₂ b₂) h2
      exact Sub.ascL Γ e τ (.lam A₂ b₂) hs1 hs2
    | var x_a =>
      subst ha
      first | (exact Bool.noConfusion h) | (simp only at h)
      cases hget : Γ.get? x_a with
      | none => rw [hget] at h; simp at h
      | some T =>
        rw [hget] at h
        have hs : Sub Γ T (.lam A₂ b₂) := subCheck_sound fuel Γ T (.lam A₂ b₂) h
        exact Sub.var Γ x_a (.lam A₂ b₂) T hget hs
    | lam A₁ b₁ =>
      subst ha
      first | (exact Bool.noConfusion h) | (simp only at h)
      obtain ⟨h1, h2⟩ := bool_and_split h
      have hs1 : Sub Γ A₂ A₁ := subCheck_sound fuel Γ A₂ A₁ h1
      have hs2 : Sub (A₂ :: Γ) b₁ b₂ := subCheck_sound fuel (A₂ :: Γ) b₁ b₂ h2
      exact Sub.lam Γ A₁ A₂ b₁ b₂ hs1 hs2
    | app f arg =>
      subst ha
      first | (exact Bool.noConfusion h) | (simp only at h)
      cases hsy : synthLam fuel Γ f with
      | none => rw [hsy] at h; simp at h
      | some p =>
        obtain ⟨D, R⟩ := p
        rw [hsy] at h
        first | (exact Bool.noConfusion h) | (simp only at h)
        obtain ⟨h1, h2⟩ := bool_and_split h
        have hf_sub : Sub Γ f (.lam D R) := synthLam_sound fuel Γ f D R hsy
        have ha_sub : Sub Γ arg D := subCheck_sound fuel Γ arg D h1
        have hR_sub : Sub Γ (R.subst 0 arg) (.lam A₂ b₂) :=
          subCheck_sound fuel Γ (R.subst 0 arg) (.lam A₂ b₂) h2
        exact Sub.app Γ f arg (.lam A₂ b₂) D R hf_sub ha_sub hR_sub
    | top =>
      subst ha
      first | (exact Bool.noConfusion h) | (simp only at h)
  | app f_b a_b =>
    subst hb
    first | (exact Bool.noConfusion h) | (simp only at h)
    cases ha : a with
    | asc e τ =>
      subst ha
      first | (exact Bool.noConfusion h) | (simp only at h)
      obtain ⟨h1, h2⟩ := bool_and_split h
      have hs1 : Sub Γ e τ := subCheck_sound fuel Γ e τ h1
      have hs2 : Sub Γ τ (.app f_b a_b) := subCheck_sound fuel Γ τ (.app f_b a_b) h2
      exact Sub.ascL Γ e τ (.app f_b a_b) hs1 hs2
    | var x_a =>
      subst ha
      first | (exact Bool.noConfusion h) | (simp only at h)
      cases hget : Γ.get? x_a with
      | none => rw [hget] at h; simp at h
      | some T =>
        rw [hget] at h
        have hs : Sub Γ T (.app f_b a_b) := subCheck_sound fuel Γ T (.app f_b a_b) h
        exact Sub.var Γ x_a (.app f_b a_b) T hget hs
    | lam A₁ b₁ =>
      subst ha
      first | (exact Bool.noConfusion h) | (simp only at h)
    | app f arg =>
      subst ha
      first | (exact Bool.noConfusion h) | (simp only at h)
      cases hsy : synthLam fuel Γ f with
      | none => rw [hsy] at h; simp at h
      | some p =>
        obtain ⟨D, R⟩ := p
        rw [hsy] at h
        first | (exact Bool.noConfusion h) | (simp only at h)
        obtain ⟨h1, h2⟩ := bool_and_split h
        have hf_sub : Sub Γ f (.lam D R) := synthLam_sound fuel Γ f D R hsy
        have ha_sub : Sub Γ arg D := subCheck_sound fuel Γ arg D h1
        have hR_sub : Sub Γ (R.subst 0 arg) (.app f_b a_b) :=
          subCheck_sound fuel Γ (R.subst 0 arg) (.app f_b a_b) h2
        exact Sub.app Γ f arg (.app f_b a_b) D R hf_sub ha_sub hR_sub
    | top =>
      subst ha
      first | (exact Bool.noConfusion h) | (simp only at h)

end  -- mutual soundness

-- ============================================================
-- Sanity tests
-- ============================================================

section Tests

private def BOOL : Expr := .lam .top (.lam (.var 0) (.lam (.var 1) (.var 2)))
private def TRUE : Expr := .lam .top (.lam (.var 0) (.lam (.var 1) (.var 1)))
private def FALSE : Expr := .lam .top (.lam (.var 0) (.lam (.var 1) (.var 0)))

-- Reflexivity
example : check 10 [] .top .top = true := by native_decide
example : check 10 [] BOOL BOOL = true := by native_decide

-- Top
example : check 10 [] BOOL .top = true := by native_decide
example : check 10 [] (.var 0) .top = true := by native_decide

-- TRUE ⊑ BOOL
example : check 10 [] TRUE BOOL = true := by native_decide
-- FALSE ⊑ BOOL
example : check 10 [] FALSE BOOL = true := by native_decide

-- Var
example : check 10 [.top] (.var 0) .top = true := by native_decide

-- Lambda contravariance
example : check 10 [] (.lam .top (.var 0)) (.lam (.lam .top .top) (.var 0)) = true := by
  native_decide

end Tests

end Och.Simple

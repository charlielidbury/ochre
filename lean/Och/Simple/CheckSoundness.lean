import Och.Simple.Check
import Och.Simple.Properties

/-!
# Soundness of the algorithmic checker

Proves:
1. `synth_sound`: if `synth fuel Γ e = some τ`, then `Sub Γ e τ`
2. `check_sound`: if `check fuel Γ a b = some true`, then `Sub Γ a b`

## Sorrys

Synth soundness has gaps because synth is "optimistic" — it returns types
without verifying all sub-obligations (e.g., arg ⊑ D for app, e ⊑ τ for asc).

Check soundness has two sorry'd branches:
- [App]: complex multi-strategy branch involving synth
- [Mu annotation]: the algorithm trusts `A ⊑ b` implies `μA.body ⊑ b`
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Och.Simple

open Expr

-- ============================================================
-- Synth soundness
-- ============================================================

/-- If `synth fuel Γ e = some τ`, then `Sub Γ e τ`. -/
noncomputable def synth_sound :
    (fuel : Nat) → (Γ : Ctx) → (e τ : Expr) →
    synth fuel Γ e = some τ → Sub Γ e τ
  | 0, _, _, _, h => by simp [synth] at h
  | fuel + 1, Γ, .var x, τ, h => by
    simp [synth] at h
    exact Sub.var Γ x τ τ h (Sub.refl Γ τ)
  | fuel + 1, _, .lam D body, _, h => by
    simp [synth] at h; subst h
    exact Sub.refl _ (.lam D body)
  | fuel + 1, _, .app _ _, _, _ => by sorry
  | fuel + 1, _, .asc _ _, _, _ => by sorry
  | fuel + 1, Γ, .mu (.lam _ _) _, _, _ => by sorry
  | fuel + 1, Γ, .mu (.var k) body, τ, h => by
    simp [synth] at h
    exact Sub.muUnfoldL Γ _ body τ (synth_sound fuel Γ _ τ h)
  | fuel + 1, Γ, .mu (.app f a) body, τ, h => by
    simp [synth] at h
    exact Sub.muUnfoldL Γ _ body τ (synth_sound fuel Γ _ τ h)
  | fuel + 1, Γ, .mu (.asc e ty) body, τ, h => by
    simp [synth] at h
    exact Sub.muUnfoldL Γ _ body τ (synth_sound fuel Γ _ τ h)
  | fuel + 1, Γ, .mu .top body, τ, h => by
    simp [synth] at h
    exact Sub.muUnfoldL Γ _ body τ (synth_sound fuel Γ _ τ h)
  | fuel + 1, Γ, .mu (.mu ann body') body, τ, h => by
    simp [synth] at h
    exact Sub.muUnfoldL Γ _ body τ (synth_sound fuel Γ _ τ h)
  | fuel + 1, _, .top, _, h => by
    simp [synth] at h; subst h; exact Sub.refl _ .top

-- ============================================================
-- Check soundness helper
-- ============================================================

-- The check function is deeply nested with conditionals and matches.
-- Rather than fighting Lean's unifier on the full function, we use a
-- helper lemma that extracts the "check returned some true" hypothesis
-- from each branch and produces the Sub derivation.

/-- check at fuel+1 with a == b gives some true → Sub. -/
private noncomputable def check_sound_refl (Γ : Ctx) (a : Expr)
    : Sub Γ a a := Sub.refl Γ a

/-- If `check fuel Γ a b = some true`, then `Sub Γ a b`. -/
noncomputable def check_sound : (fuel : Nat) → (Γ : Ctx) → (a b : Expr) →
    check fuel Γ a b = some true → Sub Γ a b := by
  intro fuel
  induction fuel with
  | zero => intro Γ a b h; simp [check] at h
  | succ fuel ih =>
    intro Γ a b h
    -- Unfold check at fuel+1
    simp only [check] at h
    -- First: if a == b then some true → refl
    by_cases hab : (a == b) = true
    · simp [hab] at h
      have := beq_iff_eq.mp hab
      subst this; exact Sub.refl Γ a
    · simp only [show ¬ (a == b) = true from hab, ite_false] at h
      -- Next: match b
      cases b with
      | top =>
        -- b = .top → some true
        simp at h; exact Sub.top Γ a
      | var bx =>
        -- b is not top, so we fall through to the a,b match
        cases a with
        | var x =>
          simp [check] at h
          match hget : Γ.get? x with
          | some T =>
            rw [hget] at h; simp at h
            exact Sub.var Γ x (.var bx) T hget (ih Γ T (.var bx) h)
          | none => rw [hget] at h; simp at h
        | lam A body₁ => simp at h
        | app f arg => sorry
        | asc e τ =>
          simp at h
          match heτ : check fuel Γ e τ with
          | some true =>
            rw [heτ] at h; simp at h
            exact Sub.ascL Γ e τ _ (ih Γ e τ heτ) (ih Γ τ _ h)
          | some false => rw [heτ] at h; simp at h
          | none => rw [heτ] at h; simp at h
        | mu A bodyA =>
          simp at h
          match hAb : check fuel Γ A (.var bx) with
          | some true =>
            rw [hAb] at h; simp at h
            sorry -- annotation trust
          | some false =>
            rw [hAb] at h; simp at h
            exact Sub.muUnfoldL Γ A bodyA _ (ih Γ _ _ h)
          | none =>
            rw [hAb] at h; simp at h
            exact Sub.muUnfoldL Γ A bodyA _ (ih Γ _ _ h)
        | top => simp at h
      | lam B body₂ =>
        cases a with
        | var x =>
          simp at h
          match hget : Γ.get? x with
          | some T =>
            rw [hget] at h; simp at h
            exact Sub.var Γ x _ T hget (ih Γ T _ h)
          | none => rw [hget] at h; simp at h
        | lam A body₁ =>
          simp at h
          match hdom : check fuel Γ B A with
          | some true =>
            rw [hdom] at h; simp at h
            exact Sub.lam Γ A B body₁ body₂ (ih Γ B A hdom) (ih (B :: Γ) body₁ body₂ h)
          | some false => rw [hdom] at h; simp at h
          | none => rw [hdom] at h; simp at h
        | app f arg => sorry
        | asc e τ =>
          simp at h
          match heτ : check fuel Γ e τ with
          | some true =>
            rw [heτ] at h; simp at h
            exact Sub.ascL Γ e τ _ (ih Γ e τ heτ) (ih Γ τ _ h)
          | some false => rw [heτ] at h; simp at h
          | none => rw [heτ] at h; simp at h
        | mu A bodyA =>
          simp at h
          match hAb : check fuel Γ A (.lam B body₂) with
          | some true =>
            rw [hAb] at h; simp at h
            sorry -- annotation trust
          | some false =>
            rw [hAb] at h; simp at h
            exact Sub.muUnfoldL Γ A bodyA _ (ih Γ _ _ h)
          | none =>
            rw [hAb] at h; simp at h
            exact Sub.muUnfoldL Γ A bodyA _ (ih Γ _ _ h)
        | top => simp at h
      | app bf ba =>
        cases a with
        | var x =>
          simp at h
          match hget : Γ.get? x with
          | some T =>
            rw [hget] at h; simp at h
            exact Sub.var Γ x _ T hget (ih Γ T _ h)
          | none => rw [hget] at h; simp at h
        | lam _ _ => simp at h
        | app f arg => sorry
        | asc e τ =>
          simp at h
          match heτ : check fuel Γ e τ with
          | some true =>
            rw [heτ] at h; simp at h
            exact Sub.ascL Γ e τ _ (ih Γ e τ heτ) (ih Γ τ _ h)
          | some false => rw [heτ] at h; simp at h
          | none => rw [heτ] at h; simp at h
        | mu A bodyA =>
          simp at h
          match hAb : check fuel Γ A (.app bf ba) with
          | some true =>
            rw [hAb] at h; simp at h
            sorry -- annotation trust
          | some false =>
            rw [hAb] at h; simp at h
            exact Sub.muUnfoldL Γ A bodyA _ (ih Γ _ _ h)
          | none =>
            rw [hAb] at h; simp at h
            exact Sub.muUnfoldL Γ A bodyA _ (ih Γ _ _ h)
        | top => simp at h
      | asc be bτ =>
        cases a with
        | var x =>
          simp at h
          match hget : Γ.get? x with
          | some T =>
            rw [hget] at h; simp at h
            exact Sub.var Γ x _ T hget (ih Γ T _ h)
          | none => rw [hget] at h; simp at h
        | lam domain₁ body₁ =>
          -- a=lam, b=asc: check falls through to (_, .asc e τ) = Asc-R
          -- check (fuel+1) Γ (lam domain₁ body₁) (asc be bτ) reduces to:
          -- match check fuel Γ be bτ with | some true => check fuel Γ (lam ...) be | other => other
          change (match check fuel Γ be bτ with
                  | some true => check fuel Γ (.lam domain₁ body₁) be
                  | other => other) = some true at h
          match heτ : check fuel Γ be bτ with
          | some true =>
            rw [heτ] at h; simp at h
            exact Sub.ascR Γ (.lam domain₁ body₁) be bτ (ih Γ be bτ heτ) (ih Γ _ be h)
          | some false => rw [heτ] at h; simp at h
          | none => rw [heτ] at h; simp at h
        | app f arg => sorry -- app case
        | asc e τ =>
          simp at h
          match heτ : check fuel Γ e τ with
          | some true =>
            rw [heτ] at h; simp at h
            exact Sub.ascL Γ e τ _ (ih Γ e τ heτ) (ih Γ τ _ h)
          | some false => rw [heτ] at h; simp at h
          | none => rw [heτ] at h; simp at h
        | mu A bodyA =>
          simp at h
          match hAb : check fuel Γ A (.asc be bτ) with
          | some true =>
            rw [hAb] at h; simp at h
            sorry -- annotation trust
          | some false =>
            rw [hAb] at h; simp at h
            -- falls through to muUnfoldL
            exact Sub.muUnfoldL Γ A bodyA _
              (ih Γ (bodyA.subst 0 (.mu A bodyA)) _ h)
          | none =>
            rw [hAb] at h; simp at h
            exact Sub.muUnfoldL Γ A bodyA _
              (ih Γ (bodyA.subst 0 (.mu A bodyA)) _ h)
        | top =>
          -- top on LHS, asc on RHS → [Asc-R]
          simp at h
          match heτ : check fuel Γ be bτ with
          | some true =>
            rw [heτ] at h; simp at h
            exact Sub.ascR Γ .top be bτ (ih Γ be bτ heτ) (ih Γ .top be h)
          | some false => rw [heτ] at h; simp at h
          | none => rw [heτ] at h; simp at h
      | mu Ab bodyB =>
        cases a with
        | var x =>
          simp at h
          match hget : Γ.get? x with
          | some T =>
            rw [hget] at h; simp at h
            exact Sub.var Γ x _ T hget (ih Γ T _ h)
          | none => rw [hget] at h; simp at h
        | lam domain₁ body₁ =>
          -- a=lam, b=mu: check falls through to (_, .mu Ab bodyB) = Mu-R
          change (match check fuel Γ (.lam domain₁ body₁) Ab with
                  | some true => check fuel Γ (.lam domain₁ body₁) (bodyB.subst 0 (.lam domain₁ body₁))
                  | other => other) = some true at h
          match hAb : check fuel Γ (.lam domain₁ body₁) Ab with
          | some true =>
            rw [hAb] at h; simp at h
            exact Sub.muR Γ (.lam domain₁ body₁) Ab bodyB
              (ih Γ _ Ab hAb) (ih Γ _ _ h)
          | some false => rw [hAb] at h; simp at h
          | none => rw [hAb] at h; simp at h
        | app f arg => sorry
        | asc e τ =>
          simp at h
          match heτ : check fuel Γ e τ with
          | some true =>
            rw [heτ] at h; simp at h
            exact Sub.ascL Γ e τ _ (ih Γ e τ heτ) (ih Γ τ _ h)
          | some false => rw [heτ] at h; simp at h
          | none => rw [heτ] at h; simp at h
        | mu A bodyA =>
          simp at h
          -- Strategy 1: annotation A ⊑ (mu Ab bodyB)
          match hAb : check fuel Γ A (.mu Ab bodyB) with
          | some true =>
            rw [hAb] at h; simp at h
            sorry -- annotation trust: A ⊑ b implies mu A bodyA ⊑ b
          | some false =>
            rw [hAb] at h; simp at h
            -- Strategy 2: muR check or muUnfoldL
            match hmuR1 : check fuel Γ (.mu A bodyA) Ab with
            | some true =>
              rw [hmuR1] at h; simp at h
              match hmuR2 : check fuel Γ (.mu A bodyA) (bodyB.subst 0 (.mu A bodyA)) with
              | some true =>
                rw [hmuR2] at h; simp at h
                exact Sub.muR Γ (.mu A bodyA) Ab bodyB
                  (ih Γ (.mu A bodyA) Ab hmuR1)
                  (ih Γ (.mu A bodyA) (bodyB.subst 0 (.mu A bodyA)) hmuR2)
              | some false =>
                rw [hmuR2] at h; simp at h
                exact Sub.muUnfoldL Γ A bodyA _
                  (ih Γ (bodyA.subst 0 (.mu A bodyA)) _ h)
              | none =>
                rw [hmuR2] at h; simp at h
                exact Sub.muUnfoldL Γ A bodyA _
                  (ih Γ (bodyA.subst 0 (.mu A bodyA)) _ h)
            | some false =>
              rw [hmuR1] at h; simp at h
              exact Sub.muUnfoldL Γ A bodyA _
                (ih Γ (bodyA.subst 0 (.mu A bodyA)) _ h)
            | none =>
              rw [hmuR1] at h; simp at h
              exact Sub.muUnfoldL Γ A bodyA _
                (ih Γ (bodyA.subst 0 (.mu A bodyA)) _ h)
          | none =>
            rw [hAb] at h; simp at h
            -- Same as some false
            match hmuR1 : check fuel Γ (.mu A bodyA) Ab with
            | some true =>
              rw [hmuR1] at h; simp at h
              match hmuR2 : check fuel Γ (.mu A bodyA) (bodyB.subst 0 (.mu A bodyA)) with
              | some true =>
                rw [hmuR2] at h; simp at h
                exact Sub.muR Γ (.mu A bodyA) Ab bodyB
                  (ih Γ (.mu A bodyA) Ab hmuR1)
                  (ih Γ (.mu A bodyA) (bodyB.subst 0 (.mu A bodyA)) hmuR2)
              | some false =>
                rw [hmuR2] at h; simp at h
                exact Sub.muUnfoldL Γ A bodyA _
                  (ih Γ (bodyA.subst 0 (.mu A bodyA)) _ h)
              | none =>
                rw [hmuR2] at h; simp at h
                exact Sub.muUnfoldL Γ A bodyA _
                  (ih Γ (bodyA.subst 0 (.mu A bodyA)) _ h)
            | some false =>
              rw [hmuR1] at h; simp at h
              exact Sub.muUnfoldL Γ A bodyA _
                (ih Γ (bodyA.subst 0 (.mu A bodyA)) _ h)
            | none =>
              rw [hmuR1] at h; simp at h
              exact Sub.muUnfoldL Γ A bodyA _
                (ih Γ (bodyA.subst 0 (.mu A bodyA)) _ h)
        | top =>
          -- top on LHS, mu on RHS → [Mu-R]
          simp at h
          match hmuR1 : check fuel Γ .top Ab with
          | some true =>
            rw [hmuR1] at h; simp at h
            exact Sub.muR Γ .top Ab bodyB
              (ih Γ .top Ab hmuR1)
              (ih Γ .top (bodyB.subst 0 .top) h)
          | some false => rw [hmuR1] at h; simp at h
          | none => rw [hmuR1] at h; simp at h

-- ============================================================
-- Main theorem
-- ============================================================

/-- **Algorithmic soundness**: if the decision procedure accepts, the subtyping holds. -/
noncomputable def check_implies_Sub
    {fuel : Nat} {Γ : Ctx} {a b : Expr}
    (h : check fuel Γ a b = some true) : Sub Γ a b :=
  check_sound fuel Γ a b h

end Och.Simple

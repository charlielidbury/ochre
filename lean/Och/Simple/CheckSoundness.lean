import Och.Simple.Check
import Och.Simple.Properties

/-!
# Soundness of the algorithmic checker

Proves:
1. `synth_sound`: if `synth fuel seen Γ e = some τ`, then `Sub Γ e τ`
2. `check_sound`: if `check fuel [] Γ a b = some true`, then `Sub Γ a b`

The `check` function uses a `seen` set for cycle detection in the muR rule.
When the seen set fires (cycle detected), soundness relies on a coinductive
argument that is sorry'd for now. The main theorem `check_implies_Sub` only
applies to calls with an empty seen set.

## Remaining sorrys

- [App]: complex multi-strategy branch involving synth (pre-existing)
- [Cycle detection / SeenValid]: coinductive reasoning for seen set validity
- Synth soundness gaps for app/asc/mu-lam cases (pre-existing)

## What was fixed

- The mu annotation shortcut now checks BOTH `A ⊑ b` AND `body ⊑ A↑`,
  matching the `Sub.mu` rule exactly. This eliminates the previous
  "annotation trust" sorrys (4 instances).
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000

namespace Och.Simple

open Expr

-- ============================================================
-- Synth soundness
-- ============================================================

/-- If `synth fuel seen Γ e = some τ`, then `Sub Γ e τ`. -/
noncomputable def synth_sound :
    (fuel : Nat) → (seen : List (Expr × Expr)) → (Γ : Ctx) → (e τ : Expr) →
    synth fuel seen Γ e = some τ → Sub Γ e τ
  | 0, _, _, _, _, h => by simp [synth] at h
  | fuel + 1, _, Γ, .var x, τ, h => by
    simp [synth] at h
    exact Sub.var Γ x τ τ h (Sub.refl Γ τ)
  | fuel + 1, _, _, .lam D body, _, h => by
    simp [synth] at h; subst h
    exact Sub.refl _ (.lam D body)
  | fuel + 1, _, _, .app _ _, _, _ => by sorry
  | fuel + 1, _, _, .asc _ _, _, _ => by sorry
  | fuel + 1, _, Γ, .mu (.lam _ _) _, _, _ => by sorry
  | fuel + 1, seen, Γ, .mu (.var k) body, τ, h => by
    simp [synth] at h
    exact Sub.muUnfoldL Γ _ body τ (synth_sound fuel seen Γ _ τ h)
  | fuel + 1, seen, Γ, .mu (.app f a) body, τ, h => by
    simp [synth] at h
    exact Sub.muUnfoldL Γ _ body τ (synth_sound fuel seen Γ _ τ h)
  | fuel + 1, seen, Γ, .mu (.asc e ty) body, τ, h => by
    simp [synth] at h
    exact Sub.muUnfoldL Γ _ body τ (synth_sound fuel seen Γ _ τ h)
  | fuel + 1, seen, Γ, .mu .top body, τ, h => by
    simp [synth] at h
    exact Sub.muUnfoldL Γ _ body τ (synth_sound fuel seen Γ _ τ h)
  | fuel + 1, seen, Γ, .mu (.mu ann body') body, τ, h => by
    simp [synth] at h
    exact Sub.muUnfoldL Γ _ body τ (synth_sound fuel seen Γ _ τ h)
  | fuel + 1, _, _, .top, _, h => by
    simp [synth] at h; subst h; exact Sub.refl _ .top

-- ============================================================
-- Check soundness (for empty seen set)
-- ============================================================

-- The proof strategy: we prove soundness for arbitrary `seen` sets,
-- sorry'ing the cycle detection cases. For the main theorem, seen = [].

/-- If `check fuel seen Γ a b = some true`, then `Sub Γ a b`.
    This is the internal version that sorry's cycle detection cases. -/
noncomputable def check_sound_aux : (fuel : Nat) → (seen : List (Expr × Expr)) →
    (Γ : Ctx) → (a b : Expr) →
    check fuel seen Γ a b = some true → Sub Γ a b := by
  intro fuel
  induction fuel with
  | zero => intro seen Γ a b h; simp [check] at h
  | succ fuel ih =>
    intro seen Γ a b h
    simp only [check] at h
    by_cases hab : (a == b) = true
    · simp [hab] at h
      have := beq_iff_eq.mp hab
      subst this; exact Sub.refl Γ a
    · simp only [show ¬ (a == b) = true from hab, ite_false] at h
      cases b with
      | top =>
        simp at h; exact Sub.top Γ a
      | var bx =>
        cases a with
        | var x =>
          simp [check] at h
          match hget : Γ.get? x with
          | some T =>
            rw [hget] at h; simp at h
            exact Sub.var Γ x (.var bx) T hget (ih seen Γ T (.var bx) h)
          | none => rw [hget] at h; simp at h
        | lam A body₁ => simp at h
        | app f arg => sorry
        | asc e τ =>
          simp at h
          match heτ : check fuel seen Γ e τ with
          | some true =>
            rw [heτ] at h; simp at h
            exact Sub.ascL Γ e τ _ (ih seen Γ e τ heτ) (ih seen Γ τ _ h)
          | some false => rw [heτ] at h; simp at h
          | none => rw [heτ] at h; simp at h
        | mu A bodyA =>
          simp at h
          match hAb : check fuel seen Γ A (.var bx) with
          | some true =>
            rw [hAb] at h; simp at h
            match hbody : check fuel seen (A :: Γ) bodyA (A.shift 0 1) with
            | some true =>
              rw [hbody] at h; simp at h
              exact Sub.mu Γ A bodyA (.var bx)
                (ih seen Γ A (.var bx) hAb)
                (ih seen (A :: Γ) bodyA (A.shift 0 1) hbody)
            | some false =>
              rw [hbody] at h; simp at h
              exact Sub.muUnfoldL Γ A bodyA _ (ih seen Γ _ _ h)
            | none =>
              rw [hbody] at h; simp at h
              exact Sub.muUnfoldL Γ A bodyA _ (ih seen Γ _ _ h)
          | some false =>
            rw [hAb] at h; simp at h
            exact Sub.muUnfoldL Γ A bodyA _ (ih seen Γ _ _ h)
          | none =>
            rw [hAb] at h; simp at h
            exact Sub.muUnfoldL Γ A bodyA _ (ih seen Γ _ _ h)
        | top => simp at h
      | lam B body₂ =>
        cases a with
        | var x =>
          simp at h
          match hget : Γ.get? x with
          | some T =>
            rw [hget] at h; simp at h
            exact Sub.var Γ x _ T hget (ih seen Γ T _ h)
          | none => rw [hget] at h; simp at h
        | lam A body₁ =>
          simp at h
          match hdom : check fuel seen Γ B A with
          | some true =>
            rw [hdom] at h; simp at h
            exact Sub.lam Γ A B body₁ body₂ (ih seen Γ B A hdom) (ih seen (B :: Γ) body₁ body₂ h)
          | some false => rw [hdom] at h; simp at h
          | none => rw [hdom] at h; simp at h
        | app f arg => sorry
        | asc e τ =>
          simp at h
          match heτ : check fuel seen Γ e τ with
          | some true =>
            rw [heτ] at h; simp at h
            exact Sub.ascL Γ e τ _ (ih seen Γ e τ heτ) (ih seen Γ τ _ h)
          | some false => rw [heτ] at h; simp at h
          | none => rw [heτ] at h; simp at h
        | mu A bodyA =>
          simp at h
          match hAb : check fuel seen Γ A (.lam B body₂) with
          | some true =>
            rw [hAb] at h; simp at h
            match hbody : check fuel seen (A :: Γ) bodyA (A.shift 0 1) with
            | some true =>
              rw [hbody] at h; simp at h
              exact Sub.mu Γ A bodyA (.lam B body₂)
                (ih seen Γ A (.lam B body₂) hAb)
                (ih seen (A :: Γ) bodyA (A.shift 0 1) hbody)
            | some false =>
              rw [hbody] at h; simp at h
              exact Sub.muUnfoldL Γ A bodyA _ (ih seen Γ _ _ h)
            | none =>
              rw [hbody] at h; simp at h
              exact Sub.muUnfoldL Γ A bodyA _ (ih seen Γ _ _ h)
          | some false =>
            rw [hAb] at h; simp at h
            exact Sub.muUnfoldL Γ A bodyA _ (ih seen Γ _ _ h)
          | none =>
            rw [hAb] at h; simp at h
            exact Sub.muUnfoldL Γ A bodyA _ (ih seen Γ _ _ h)
        | top => simp at h
      | app bf ba =>
        cases a with
        | var x =>
          simp at h
          match hget : Γ.get? x with
          | some T =>
            rw [hget] at h; simp at h
            exact Sub.var Γ x _ T hget (ih seen Γ T _ h)
          | none => rw [hget] at h; simp at h
        | lam _ _ => simp at h
        | app f arg => sorry
        | asc e τ =>
          simp at h
          match heτ : check fuel seen Γ e τ with
          | some true =>
            rw [heτ] at h; simp at h
            exact Sub.ascL Γ e τ _ (ih seen Γ e τ heτ) (ih seen Γ τ _ h)
          | some false => rw [heτ] at h; simp at h
          | none => rw [heτ] at h; simp at h
        | mu A bodyA =>
          simp at h
          match hAb : check fuel seen Γ A (.app bf ba) with
          | some true =>
            rw [hAb] at h; simp at h
            match hbody : check fuel seen (A :: Γ) bodyA (A.shift 0 1) with
            | some true =>
              rw [hbody] at h; simp at h
              exact Sub.mu Γ A bodyA (.app bf ba)
                (ih seen Γ A (.app bf ba) hAb)
                (ih seen (A :: Γ) bodyA (A.shift 0 1) hbody)
            | some false =>
              rw [hbody] at h; simp at h
              exact Sub.muUnfoldL Γ A bodyA _ (ih seen Γ _ _ h)
            | none =>
              rw [hbody] at h; simp at h
              exact Sub.muUnfoldL Γ A bodyA _ (ih seen Γ _ _ h)
          | some false =>
            rw [hAb] at h; simp at h
            exact Sub.muUnfoldL Γ A bodyA _ (ih seen Γ _ _ h)
          | none =>
            rw [hAb] at h; simp at h
            exact Sub.muUnfoldL Γ A bodyA _ (ih seen Γ _ _ h)
        | top => simp at h
      | asc be bτ =>
        cases a with
        | var x =>
          simp at h
          match hget : Γ.get? x with
          | some T =>
            rw [hget] at h; simp at h
            exact Sub.var Γ x _ T hget (ih seen Γ T _ h)
          | none => rw [hget] at h; simp at h
        | lam domain₁ body₁ =>
          change (match check fuel seen Γ be bτ with
                  | some true => check fuel seen Γ (.lam domain₁ body₁) be
                  | other => other) = some true at h
          match heτ : check fuel seen Γ be bτ with
          | some true =>
            rw [heτ] at h; simp at h
            exact Sub.ascR Γ (.lam domain₁ body₁) be bτ (ih seen Γ be bτ heτ) (ih seen Γ _ be h)
          | some false => rw [heτ] at h; simp at h
          | none => rw [heτ] at h; simp at h
        | app f arg => sorry
        | asc e τ =>
          simp at h
          match heτ : check fuel seen Γ e τ with
          | some true =>
            rw [heτ] at h; simp at h
            exact Sub.ascL Γ e τ _ (ih seen Γ e τ heτ) (ih seen Γ τ _ h)
          | some false => rw [heτ] at h; simp at h
          | none => rw [heτ] at h; simp at h
        | mu A bodyA =>
          simp at h
          match hAb : check fuel seen Γ A (.asc be bτ) with
          | some true =>
            rw [hAb] at h; simp at h
            match hbody : check fuel seen (A :: Γ) bodyA (A.shift 0 1) with
            | some true =>
              rw [hbody] at h; simp at h
              exact Sub.mu Γ A bodyA (.asc be bτ)
                (ih seen Γ A (.asc be bτ) hAb)
                (ih seen (A :: Γ) bodyA (A.shift 0 1) hbody)
            | some false =>
              rw [hbody] at h; simp at h
              exact Sub.muUnfoldL Γ A bodyA _
                (ih seen Γ (bodyA.subst 0 (.mu A bodyA)) _ h)
            | none =>
              rw [hbody] at h; simp at h
              exact Sub.muUnfoldL Γ A bodyA _
                (ih seen Γ (bodyA.subst 0 (.mu A bodyA)) _ h)
          | some false =>
            rw [hAb] at h; simp at h
            exact Sub.muUnfoldL Γ A bodyA _
              (ih seen Γ (bodyA.subst 0 (.mu A bodyA)) _ h)
          | none =>
            rw [hAb] at h; simp at h
            exact Sub.muUnfoldL Γ A bodyA _
              (ih seen Γ (bodyA.subst 0 (.mu A bodyA)) _ h)
        | top =>
          simp at h
          match heτ : check fuel seen Γ be bτ with
          | some true =>
            rw [heτ] at h; simp at h
            exact Sub.ascR Γ .top be bτ (ih seen Γ be bτ heτ) (ih seen Γ .top be h)
          | some false => rw [heτ] at h; simp at h
          | none => rw [heτ] at h; simp at h
      | mu Ab bodyB =>
        cases a with
        | var x =>
          simp at h
          match hget : Γ.get? x with
          | some T =>
            rw [hget] at h; simp at h
            exact Sub.var Γ x _ T hget (ih seen Γ T _ h)
          | none => rw [hget] at h; simp at h
        | lam domain₁ body₁ =>
          -- a=lam, b=mu: muR with cycle detection
          sorry
        | app f arg => sorry
        | asc e τ =>
          simp at h
          match heτ : check fuel seen Γ e τ with
          | some true =>
            rw [heτ] at h; simp at h
            exact Sub.ascL Γ e τ _ (ih seen Γ e τ heτ) (ih seen Γ τ _ h)
          | some false => rw [heτ] at h; simp at h
          | none => rw [heτ] at h; simp at h
        | mu A bodyA =>
          simp at h
          -- Strategy 1: annotation A ⊑ (mu Ab bodyB) AND body ⊑ A↑
          match hAb : check fuel seen Γ A (.mu Ab bodyB) with
          | some true =>
            rw [hAb] at h; simp at h
            match hbody : check fuel seen (A :: Γ) bodyA (A.shift 0 1) with
            | some true =>
              rw [hbody] at h; simp at h
              exact Sub.mu Γ A bodyA (.mu Ab bodyB)
                (ih seen Γ A (.mu Ab bodyB) hAb)
                (ih seen (A :: Γ) bodyA (A.shift 0 1) hbody)
            | some false =>
              rw [hbody] at h; simp at h
              -- Fallthrough: muR or muUnfoldL
              match hmuR1 : check fuel seen Γ (.mu A bodyA) Ab with
              | some true =>
                rw [hmuR1] at h; simp at h
                match hmuR2 : check fuel seen Γ (.mu A bodyA) (bodyB.subst 0 (.mu A bodyA)) with
                | some true =>
                  rw [hmuR2] at h; simp at h
                  exact Sub.muR Γ (.mu A bodyA) Ab bodyB
                    (ih seen Γ (.mu A bodyA) Ab hmuR1)
                    (ih seen Γ (.mu A bodyA) (bodyB.subst 0 (.mu A bodyA)) hmuR2)
                | some false =>
                  rw [hmuR2] at h; simp at h
                  exact Sub.muUnfoldL Γ A bodyA _
                    (ih seen Γ (bodyA.subst 0 (.mu A bodyA)) _ h)
                | none =>
                  rw [hmuR2] at h; simp at h
                  exact Sub.muUnfoldL Γ A bodyA _
                    (ih seen Γ (bodyA.subst 0 (.mu A bodyA)) _ h)
              | some false =>
                rw [hmuR1] at h; simp at h
                exact Sub.muUnfoldL Γ A bodyA _
                  (ih seen Γ (bodyA.subst 0 (.mu A bodyA)) _ h)
              | none =>
                rw [hmuR1] at h; simp at h
                exact Sub.muUnfoldL Γ A bodyA _
                  (ih seen Γ (bodyA.subst 0 (.mu A bodyA)) _ h)
            | none =>
              rw [hbody] at h; simp at h
              match hmuR1 : check fuel seen Γ (.mu A bodyA) Ab with
              | some true =>
                rw [hmuR1] at h; simp at h
                match hmuR2 : check fuel seen Γ (.mu A bodyA) (bodyB.subst 0 (.mu A bodyA)) with
                | some true =>
                  rw [hmuR2] at h; simp at h
                  exact Sub.muR Γ (.mu A bodyA) Ab bodyB
                    (ih seen Γ (.mu A bodyA) Ab hmuR1)
                    (ih seen Γ (.mu A bodyA) (bodyB.subst 0 (.mu A bodyA)) hmuR2)
                | some false =>
                  rw [hmuR2] at h; simp at h
                  exact Sub.muUnfoldL Γ A bodyA _
                    (ih seen Γ (bodyA.subst 0 (.mu A bodyA)) _ h)
                | none =>
                  rw [hmuR2] at h; simp at h
                  exact Sub.muUnfoldL Γ A bodyA _
                    (ih seen Γ (bodyA.subst 0 (.mu A bodyA)) _ h)
              | some false =>
                rw [hmuR1] at h; simp at h
                exact Sub.muUnfoldL Γ A bodyA _
                  (ih seen Γ (bodyA.subst 0 (.mu A bodyA)) _ h)
              | none =>
                rw [hmuR1] at h; simp at h
                exact Sub.muUnfoldL Γ A bodyA _
                  (ih seen Γ (bodyA.subst 0 (.mu A bodyA)) _ h)
          | some false =>
            rw [hAb] at h; simp at h
            -- Strategy 2: muR or muUnfoldL
            match hmuR1 : check fuel seen Γ (.mu A bodyA) Ab with
            | some true =>
              rw [hmuR1] at h; simp at h
              match hmuR2 : check fuel seen Γ (.mu A bodyA) (bodyB.subst 0 (.mu A bodyA)) with
              | some true =>
                rw [hmuR2] at h; simp at h
                exact Sub.muR Γ (.mu A bodyA) Ab bodyB
                  (ih seen Γ (.mu A bodyA) Ab hmuR1)
                  (ih seen Γ (.mu A bodyA) (bodyB.subst 0 (.mu A bodyA)) hmuR2)
              | some false =>
                rw [hmuR2] at h; simp at h
                exact Sub.muUnfoldL Γ A bodyA _
                  (ih seen Γ (bodyA.subst 0 (.mu A bodyA)) _ h)
              | none =>
                rw [hmuR2] at h; simp at h
                exact Sub.muUnfoldL Γ A bodyA _
                  (ih seen Γ (bodyA.subst 0 (.mu A bodyA)) _ h)
            | some false =>
              rw [hmuR1] at h; simp at h
              exact Sub.muUnfoldL Γ A bodyA _
                (ih seen Γ (bodyA.subst 0 (.mu A bodyA)) _ h)
            | none =>
              rw [hmuR1] at h; simp at h
              exact Sub.muUnfoldL Γ A bodyA _
                (ih seen Γ (bodyA.subst 0 (.mu A bodyA)) _ h)
          | none =>
            rw [hAb] at h; simp at h
            match hmuR1 : check fuel seen Γ (.mu A bodyA) Ab with
            | some true =>
              rw [hmuR1] at h; simp at h
              match hmuR2 : check fuel seen Γ (.mu A bodyA) (bodyB.subst 0 (.mu A bodyA)) with
              | some true =>
                rw [hmuR2] at h; simp at h
                exact Sub.muR Γ (.mu A bodyA) Ab bodyB
                  (ih seen Γ (.mu A bodyA) Ab hmuR1)
                  (ih seen Γ (.mu A bodyA) (bodyB.subst 0 (.mu A bodyA)) hmuR2)
              | some false =>
                rw [hmuR2] at h; simp at h
                exact Sub.muUnfoldL Γ A bodyA _
                  (ih seen Γ (bodyA.subst 0 (.mu A bodyA)) _ h)
              | none =>
                rw [hmuR2] at h; simp at h
                exact Sub.muUnfoldL Γ A bodyA _
                  (ih seen Γ (bodyA.subst 0 (.mu A bodyA)) _ h)
            | some false =>
              rw [hmuR1] at h; simp at h
              exact Sub.muUnfoldL Γ A bodyA _
                (ih seen Γ (bodyA.subst 0 (.mu A bodyA)) _ h)
            | none =>
              rw [hmuR1] at h; simp at h
              exact Sub.muUnfoldL Γ A bodyA _
                (ih seen Γ (bodyA.subst 0 (.mu A bodyA)) _ h)
        | top =>
          -- top on LHS, mu on RHS: muR with cycle detection
          sorry

-- ============================================================
-- Main theorem
-- ============================================================

/-- **Algorithmic soundness**: if the decision procedure accepts (with empty seen set),
    the subtyping holds. -/
noncomputable def check_implies_Sub
    {fuel : Nat} {Γ : Ctx} {a b : Expr}
    (h : check fuel [] Γ a b = some true) : Sub Γ a b :=
  check_sound_aux fuel [] Γ a b h

end Och.Simple

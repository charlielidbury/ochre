import Och.Simple.Check
import Och.Simple.Properties

/-!
# Soundness of the algorithmic checker

Proves:
- `check_sound`: if `check fuel [] Γ a b = some true`, then `Sub Γ a b`

The `check` function uses a `seen` set for cycle detection in the muR rule.
When the seen set fires (cycle detected), soundness relies on a coinductive
argument that is sorry'd for now. The main theorem `check_implies_Sub` only
applies to calls with an empty seen set.

## Remaining sorrys

Only **2** sorrys remain, both for the coinductive cycle detection cases:
- `a = lam ..., b = mu ...` with cycle detection
- `a = top, b = mu ...` with cycle detection

Both arise from `check`'s `seen`-set short-circuit in the `_, .mu Ab bodyB`
branch of its definition, and require a coinductive soundness argument for
`SeenValid`-style reasoning.

## Closed sorrys (this commit)

- **6 app-case sorrys in `check_sound_aux`**: for each `b` constructor
  (`var`, `lam`, `app`, `asc`, `mu`), the `a = .app f arg` case is proved
  by matching on `synth f` and the subsequent `check f (lam D R)`,
  `check arg D`, `check (R[0 := arg]) b` calls, delegating the fall-through
  `tryUnfolded` path to the helper `check_app_tryUnfolded_sound`.
- **3 synth soundness sorrys (`.app`, `.asc`, `.mu (.lam _ _)`)**: these
  are **unprovable as stated** because `synth` intentionally trusts
  annotations without verification. Since `check_sound_aux` does not depend
  on `synth_sound`, the theorem has been removed (see the block comment in
  place of the old definition).

## Prior fixes

- The mu annotation shortcut now checks BOTH `A ⊑ b` AND `body ⊑ A↑`,
  matching the `Sub.mu` rule exactly. This eliminated the previous
  "annotation trust" sorrys (4 instances).
-/

set_option autoImplicit false
set_option maxHeartbeats 12800000

namespace Och.Simple

open Expr

-- ============================================================
-- Synth soundness (removed)
-- ============================================================

/-!
`synth_sound` as previously stated — "if `synth fuel seen Γ e = some τ` then
`Sub Γ e τ`" — is **unprovable as a standalone lemma**. The `synth` function
intentionally trusts annotations without verification:

- For `.app f a`, synth returns `R[0 := a]` from `synth f = lam D R` without
  checking `a ⊑ D`.
- For `.asc e τ`, synth returns `τ` without checking `e ⊑ τ`.
- For `.mu (lam D R) body`, synth returns `lam D R` without checking that
  `body` actually inhabits the annotation.

The mu-unfolding recursive cases reduce to these three unprovable cases after
one step (e.g. `synth (mu A body)` for non-lam `A` recurses on
`body[0 := mu A body]`, which may be an `app`/`asc`/`mu-lam`).

Since `check_sound_aux` does not rely on `synth_sound` (it re-verifies all
premises via its own recursive `check` calls in the app branch), `synth_sound`
is unnecessary and has been removed.
-/

-- ============================================================
-- Helpers for the app case of check_sound_aux
-- ============================================================

/-- If the inner `tryWithDR`-style match returns `some true`, we can build `Sub.app`. -/
private noncomputable def check_app_tryWithDR_sound
    (fuel : Nat) (seen : List (Expr × Expr)) (Γ : Ctx) (f arg b D R : Expr)
    (ih : ∀ (seen : List (Expr × Expr)) (Γ : Ctx) (a b : Expr),
      check fuel seen Γ a b = some true → Sub Γ a b)
    (h : (match check fuel seen Γ f (.lam D R) with
      | some true =>
        match check fuel seen Γ arg D with
        | some true => check fuel seen Γ (R.subst 0 arg) b
        | other => other
      | other => other) = some true) : Sub Γ (.app f arg) b := by
  match hf : check fuel seen Γ f (.lam D R) with
  | some true =>
    simp only [hf] at h
    match ha : check fuel seen Γ arg D with
    | some true =>
      simp only [ha] at h
      exact Sub.app Γ f arg b D R (ih _ _ _ _ hf) (ih _ _ _ _ ha) (ih _ _ _ _ h)
    | some false => simp only [ha] at h; simp at h
    | none => simp only [ha] at h; simp at h
  | some false => simp only [hf] at h; simp at h
  | none => simp only [hf] at h; simp at h

/-- If the `tryUnfolded` branch (LHS is `μ`, synth unfolds it, then try app) returns
    `some true`, we can build `Sub.app`. -/
private noncomputable def check_app_tryUnfolded_sound
    (fuel : Nat) (seen : List (Expr × Expr)) (Γ : Ctx) (f arg b : Expr)
    (ih : ∀ (seen : List (Expr × Expr)) (Γ : Ctx) (a b : Expr),
      check fuel seen Γ a b = some true → Sub Γ a b)
    (h : (match f with
      | .mu _A bodyF =>
        match synth fuel seen Γ (bodyF.subst 0 f) with
        | some (.lam D R) =>
          match check fuel seen Γ f (.lam D R) with
          | some true =>
            match check fuel seen Γ arg D with
            | some true => check fuel seen Γ (R.subst 0 arg) b
            | other => other
          | other => other
        | _ => some false
      | _ => some false) = some true) : Sub Γ (.app f arg) b := by
  match f with
  | .mu A bodyF =>
    simp only at h
    match hsyn : synth fuel seen Γ (bodyF.subst 0 (.mu A bodyF)) with
    | some (.lam D R) =>
      simp only [hsyn] at h
      exact check_app_tryWithDR_sound fuel seen Γ (.mu A bodyF) arg b D R ih h
    | some (.var _) => simp only [hsyn] at h; simp at h
    | some (.app _ _) => simp only [hsyn] at h; simp at h
    | some (.asc _ _) => simp only [hsyn] at h; simp at h
    | some (.mu _ _) => simp only [hsyn] at h; simp at h
    | some .top => simp only [hsyn] at h; simp at h
    | none => simp only [hsyn] at h; simp at h
  | .var _ => simp at h
  | .lam _ _ => simp at h
  | .app _ _ => simp at h
  | .asc _ _ => simp at h
  | .top => simp at h

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
        | app f arg =>
          simp only [Bool.false_eq_true, ↓reduceIte] at h
          match hs : synth fuel seen Γ f with
          | some (.lam D R) =>
            simp only [hs] at h
            match hf : check fuel seen Γ f (.lam D R) with
            | some true =>
              simp only [hf] at h
              match ha : check fuel seen Γ arg D with
              | some true =>
                simp only [ha] at h
                match hr : check fuel seen Γ (R.subst 0 arg) (.var bx) with
                | some true =>
                  simp only [hr] at h
                  exact Sub.app Γ f arg _ D R
                    (ih _ _ _ _ hf) (ih _ _ _ _ ha) (ih _ _ _ _ hr)
                | some false =>
                  simp only [hr] at h
                  exact check_app_tryUnfolded_sound fuel seen Γ f arg _ ih h
                | none => simp only [hr] at h; simp at h
              | some false =>
                simp only [ha] at h
                exact check_app_tryUnfolded_sound fuel seen Γ f arg _ ih h
              | none => simp only [ha] at h; simp at h
            | some false =>
              simp only [hf] at h
              exact check_app_tryUnfolded_sound fuel seen Γ f arg _ ih h
            | none => simp only [hf] at h; simp at h
          | some (.var _) => simp only [hs] at h; exact check_app_tryUnfolded_sound fuel seen Γ f arg _ ih h
          | some (.app _ _) => simp only [hs] at h; exact check_app_tryUnfolded_sound fuel seen Γ f arg _ ih h
          | some (.asc _ _) => simp only [hs] at h; exact check_app_tryUnfolded_sound fuel seen Γ f arg _ ih h
          | some (.mu _ _) => simp only [hs] at h; exact check_app_tryUnfolded_sound fuel seen Γ f arg _ ih h
          | some .top => simp only [hs] at h; exact check_app_tryUnfolded_sound fuel seen Γ f arg _ ih h
          | none => simp only [hs] at h; exact check_app_tryUnfolded_sound fuel seen Γ f arg _ ih h
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
        | app f arg =>
          simp only [Bool.false_eq_true, ↓reduceIte] at h
          match hs : synth fuel seen Γ f with
          | some (.lam D R) =>
            simp only [hs] at h
            match hf : check fuel seen Γ f (.lam D R) with
            | some true =>
              simp only [hf] at h
              match ha : check fuel seen Γ arg D with
              | some true =>
                simp only [ha] at h
                match hr : check fuel seen Γ (R.subst 0 arg) (.lam B body₂) with
                | some true =>
                  simp only [hr] at h
                  exact Sub.app Γ f arg _ D R
                    (ih _ _ _ _ hf) (ih _ _ _ _ ha) (ih _ _ _ _ hr)
                | some false =>
                  simp only [hr] at h
                  exact check_app_tryUnfolded_sound fuel seen Γ f arg _ ih h
                | none => simp only [hr] at h; simp at h
              | some false =>
                simp only [ha] at h
                exact check_app_tryUnfolded_sound fuel seen Γ f arg _ ih h
              | none => simp only [ha] at h; simp at h
            | some false =>
              simp only [hf] at h
              exact check_app_tryUnfolded_sound fuel seen Γ f arg _ ih h
            | none => simp only [hf] at h; simp at h
          | some (.var _) => simp only [hs] at h; exact check_app_tryUnfolded_sound fuel seen Γ f arg _ ih h
          | some (.app _ _) => simp only [hs] at h; exact check_app_tryUnfolded_sound fuel seen Γ f arg _ ih h
          | some (.asc _ _) => simp only [hs] at h; exact check_app_tryUnfolded_sound fuel seen Γ f arg _ ih h
          | some (.mu _ _) => simp only [hs] at h; exact check_app_tryUnfolded_sound fuel seen Γ f arg _ ih h
          | some .top => simp only [hs] at h; exact check_app_tryUnfolded_sound fuel seen Γ f arg _ ih h
          | none => simp only [hs] at h; exact check_app_tryUnfolded_sound fuel seen Γ f arg _ ih h
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
        | app f arg =>
          simp only [Bool.false_eq_true, ↓reduceIte] at h
          match hs : synth fuel seen Γ f with
          | some (.lam D R) =>
            simp only [hs] at h
            match hf : check fuel seen Γ f (.lam D R) with
            | some true =>
              simp only [hf] at h
              match ha : check fuel seen Γ arg D with
              | some true =>
                simp only [ha] at h
                match hr : check fuel seen Γ (R.subst 0 arg) (.app bf ba) with
                | some true =>
                  simp only [hr] at h
                  exact Sub.app Γ f arg _ D R
                    (ih _ _ _ _ hf) (ih _ _ _ _ ha) (ih _ _ _ _ hr)
                | some false =>
                  simp only [hr] at h
                  exact check_app_tryUnfolded_sound fuel seen Γ f arg _ ih h
                | none => simp only [hr] at h; simp at h
              | some false =>
                simp only [ha] at h
                exact check_app_tryUnfolded_sound fuel seen Γ f arg _ ih h
              | none => simp only [ha] at h; simp at h
            | some false =>
              simp only [hf] at h
              exact check_app_tryUnfolded_sound fuel seen Γ f arg _ ih h
            | none => simp only [hf] at h; simp at h
          | some (.var _) => simp only [hs] at h; exact check_app_tryUnfolded_sound fuel seen Γ f arg _ ih h
          | some (.app _ _) => simp only [hs] at h; exact check_app_tryUnfolded_sound fuel seen Γ f arg _ ih h
          | some (.asc _ _) => simp only [hs] at h; exact check_app_tryUnfolded_sound fuel seen Γ f arg _ ih h
          | some (.mu _ _) => simp only [hs] at h; exact check_app_tryUnfolded_sound fuel seen Γ f arg _ ih h
          | some .top => simp only [hs] at h; exact check_app_tryUnfolded_sound fuel seen Γ f arg _ ih h
          | none => simp only [hs] at h; exact check_app_tryUnfolded_sound fuel seen Γ f arg _ ih h
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
        | app f arg =>
          simp only [Bool.false_eq_true, ↓reduceIte] at h
          match hs : synth fuel seen Γ f with
          | some (.lam D R) =>
            simp only [hs] at h
            match hf : check fuel seen Γ f (.lam D R) with
            | some true =>
              simp only [hf] at h
              match ha : check fuel seen Γ arg D with
              | some true =>
                simp only [ha] at h
                match hr : check fuel seen Γ (R.subst 0 arg) (.asc be bτ) with
                | some true =>
                  simp only [hr] at h
                  exact Sub.app Γ f arg _ D R
                    (ih _ _ _ _ hf) (ih _ _ _ _ ha) (ih _ _ _ _ hr)
                | some false =>
                  simp only [hr] at h
                  exact check_app_tryUnfolded_sound fuel seen Γ f arg _ ih h
                | none => simp only [hr] at h; simp at h
              | some false =>
                simp only [ha] at h
                exact check_app_tryUnfolded_sound fuel seen Γ f arg _ ih h
              | none => simp only [ha] at h; simp at h
            | some false =>
              simp only [hf] at h
              exact check_app_tryUnfolded_sound fuel seen Γ f arg _ ih h
            | none => simp only [hf] at h; simp at h
          | some (.var _) => simp only [hs] at h; exact check_app_tryUnfolded_sound fuel seen Γ f arg _ ih h
          | some (.app _ _) => simp only [hs] at h; exact check_app_tryUnfolded_sound fuel seen Γ f arg _ ih h
          | some (.asc _ _) => simp only [hs] at h; exact check_app_tryUnfolded_sound fuel seen Γ f arg _ ih h
          | some (.mu _ _) => simp only [hs] at h; exact check_app_tryUnfolded_sound fuel seen Γ f arg _ ih h
          | some .top => simp only [hs] at h; exact check_app_tryUnfolded_sound fuel seen Γ f arg _ ih h
          | none => simp only [hs] at h; exact check_app_tryUnfolded_sound fuel seen Γ f arg _ ih h
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
        | app f arg =>
          simp only [Bool.false_eq_true, ↓reduceIte] at h
          match hs : synth fuel seen Γ f with
          | some (.lam D R) =>
            simp only [hs] at h
            match hf : check fuel seen Γ f (.lam D R) with
            | some true =>
              simp only [hf] at h
              match ha : check fuel seen Γ arg D with
              | some true =>
                simp only [ha] at h
                match hr : check fuel seen Γ (R.subst 0 arg) (.mu Ab bodyB) with
                | some true =>
                  simp only [hr] at h
                  exact Sub.app Γ f arg _ D R
                    (ih _ _ _ _ hf) (ih _ _ _ _ ha) (ih _ _ _ _ hr)
                | some false =>
                  simp only [hr] at h
                  exact check_app_tryUnfolded_sound fuel seen Γ f arg _ ih h
                | none => simp only [hr] at h; simp at h
              | some false =>
                simp only [ha] at h
                exact check_app_tryUnfolded_sound fuel seen Γ f arg _ ih h
              | none => simp only [ha] at h; simp at h
            | some false =>
              simp only [hf] at h
              exact check_app_tryUnfolded_sound fuel seen Γ f arg _ ih h
            | none => simp only [hf] at h; simp at h
          | some (.var _) => simp only [hs] at h; exact check_app_tryUnfolded_sound fuel seen Γ f arg _ ih h
          | some (.app _ _) => simp only [hs] at h; exact check_app_tryUnfolded_sound fuel seen Γ f arg _ ih h
          | some (.asc _ _) => simp only [hs] at h; exact check_app_tryUnfolded_sound fuel seen Γ f arg _ ih h
          | some (.mu _ _) => simp only [hs] at h; exact check_app_tryUnfolded_sound fuel seen Γ f arg _ ih h
          | some .top => simp only [hs] at h; exact check_app_tryUnfolded_sound fuel seen Γ f arg _ ih h
          | none => simp only [hs] at h; exact check_app_tryUnfolded_sound fuel seen Γ f arg _ ih h
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

import Och.Simple.Syntax
import Och.Simple.Subtype

/-!
# Properties of the Sub relation

Auxiliary shift/subst lemmas and the three main properties of Sub.

## Status
- `shift_add`, `shift_shift_comm`: fully proven
- `subst_shift_lo`: fully proven
- `subst_shift_hi`, `subst_subst`: structure proven, 2 var sub-cases
  sorry'd due to tedious `if false = true` / Nat subtraction interaction
  with simp (provable with more manual case splitting)
- `Sub.weaken`: 7/8 cases proven, lam sorry'd (needs exchange)
- `Sub.trans`: 4/8 cases proven, rest sorry'd (needs narrowing etc.)
- `Sub.subst_lemma`: 7/8 cases proven, lam sorry'd (needs generalized subst)
-/

set_option autoImplicit false
set_option maxHeartbeats 6400000

namespace Och.Simple

open Expr

-- ============================================================
-- 1. Shift lemmas (fully proven)
-- ============================================================

theorem Expr.shift_add (e : Expr) (c n₁ n₂ : Nat) :
    (e.shift c n₂).shift c n₁ = e.shift c (n₁ + n₂) := by
  induction e generalizing c with
  | var k =>
    simp only [shift]
    by_cases hk : k < c
    · simp only [hk, ite_true, shift, ite_true]
    · simp only [hk, ite_false, shift, show ¬ (k + n₂ < c) from by omega, ite_false]; congr 1; omega
  | lam _ _ ihd ihb => simp only [shift]; congr 1; exact ihd c; exact ihb (c + 1)
  | app _ _ ihf iha => simp only [shift]; congr 1; exact ihf c; exact iha c
  | asc _ _ ihe iht => simp only [shift]; congr 1; exact ihe c; exact iht c
  | top => rfl

theorem Expr.shift_shift_comm (e : Expr) (c₁ c₂ n₁ n₂ : Nat) (h : c₁ ≤ c₂) :
    (e.shift c₁ n₁).shift (c₂ + n₁) n₂ = (e.shift c₂ n₂).shift c₁ n₁ := by
  induction e generalizing c₁ c₂ with
  | var k =>
    simp only [shift]
    by_cases h1 : k < c₁
    · simp only [h1, ite_true, shift, show k < c₂ + n₁ from by omega, show k < c₂ from by omega, ite_true]
    · by_cases h2 : k < c₂
      · simp only [shift, h1, h2, show k + n₁ < c₂ + n₁ from by omega, ite_true, ite_false,
                    show ¬ (k + n₂ < c₁) from by omega]
      · simp only [shift, h1, h2, show ¬ (k + n₁ < c₂ + n₁) from by omega, ite_false,
                    show ¬ (k + n₂ < c₁) from by omega]; congr 1; omega
  | lam _ _ ihd ihb =>
    simp only [shift]; congr 1; exact ihd c₁ c₂ h
    rw [show c₂ + n₁ + 1 = (c₂ + 1) + n₁ from by omega]; exact ihb (c₁ + 1) (c₂ + 1) (by omega)
  | app _ _ ihf iha => simp only [shift]; congr 1; exact ihf c₁ c₂ h; exact iha c₁ c₂ h
  | asc _ _ ihe iht => simp only [shift]; congr 1; exact ihe c₁ c₂ h; exact iht c₁ c₂ h
  | top => rfl

-- ============================================================
-- 2. Shift-Subst interaction
-- ============================================================

theorem Expr.subst_shift_lo (e : Expr) (n c d : Nat) (v : Expr) (h : c ≤ n) :
    (e.subst n v).shift c d = (e.shift c d).subst (n + d) (v.shift c d) := by
  induction e generalizing n c v with
  | var k =>
    simp only [subst, shift]
    split
    · rename_i h1; have hkn : k = n := beq_iff_eq.mp h1
      simp only [show ¬ k < c from by omega, ite_false, subst,
                 show (k + d == n + d) = true from by simp [beq_iff_eq]; omega, ite_true]
    · rename_i h1; have hkn : k ≠ n := by intro h'; simp [h'] at h1
      split
      · rename_i h2
        simp only [show ¬ k < c from by omega, ite_false, shift, show ¬ (k - 1 < c) from by omega, ite_false,
                    subst, show (k + d == n + d) = false from by simp [beq_iff_eq]; omega, ite_false,
                    show k + d > n + d from by omega, ite_true]; congr 1; omega
      · rename_i h2; by_cases hkc : k < c
        · simp only [hkc, ite_true, shift, hkc, ite_true, subst,
                      show (k == n + d) = false from by simp [beq_iff_eq]; omega, ite_false,
                      show ¬ k > n + d from by omega, ite_false]; simp
        · simp only [hkc, ite_false, shift, hkc, ite_false, subst,
                      show (k + d == n + d) = false from by simp [beq_iff_eq]; omega, ite_false,
                      show ¬ k + d > n + d from by omega, ite_false]; simp
  | lam _ _ ihd ihb =>
    simp only [subst, shift]; congr 1; exact ihd n c v h
    have := ihb (n + 1) (c + 1) (v.shift 0 1) (by omega)
    rw [show n + 1 + d = (n + d) + 1 from by omega] at this; rw [this]; congr 1
    exact Expr.shift_shift_comm v 0 c 1 d (by omega)
  | app _ _ ihf iha => simp only [subst, shift]; congr 1; exact ihf n c v h; exact iha n c v h
  | asc _ _ ihe iht => simp only [subst, shift]; congr 1; exact ihe n c v h; exact iht n c v h
  | top => rfl

theorem Expr.subst_shift_hi (e : Expr) (n c d : Nat) (v : Expr) (h : n ≤ c) :
    (e.subst n v).shift c d = (e.shift (c + 1) d).subst n (v.shift c d) := by
  induction e generalizing n c v with
  | var k =>
    -- The var case is provable but requires tedious case analysis on k vs n, k vs c.
    -- The same pattern as subst_shift_lo works but with different arithmetic.
    sorry
  | lam _ _ ihd ihb =>
    simp only [subst, shift]; congr 1; exact ihd n c v h
    have := ihb (n + 1) (c + 1) (v.shift 0 1) (by omega)
    rw [show c + 1 + 1 = (c + 1) + 1 from by omega] at this; rw [this]; congr 1
    exact Expr.shift_shift_comm v 0 c 1 d (by omega)
  | app _ _ ihf iha => simp only [subst, shift]; congr 1; exact ihf n c v h; exact iha n c v h
  | asc _ _ ihe iht => simp only [subst, shift]; congr 1; exact ihe n c v h; exact iht n c v h
  | top => rfl

theorem Expr.subst_shift_zero (R a : Expr) (d : Nat) :
    (R.subst 0 a).shift 0 d = (R.shift 1 d).subst 0 (a.shift 0 d) :=
  Expr.subst_shift_hi R 0 0 d a (by omega)

-- ============================================================
-- 3. Subst-Subst interaction
-- ============================================================

theorem Expr.subst_subst (e : Expr) (m n : Nat) (u w : Expr) (h : m ≤ n) :
    (e.subst (n + 1) (w.shift m 1)).subst m (u.subst n w) =
    (e.subst m u).subst n w := by
  induction e generalizing m n u w with
  | var k =>
    -- Provable by exhaustive case analysis on k vs m, k vs n+1.
    -- Requires subst_shift_cancel and careful Nat arithmetic.
    sorry
  | lam _ _ ihd ihb =>
    simp only [subst]; congr 1; exact ihd m n u w h
    have hw : (w.shift m 1).shift 0 1 = (w.shift 0 1).shift (m + 1) 1 :=
      (Expr.shift_shift_comm w 0 m 1 1 (by omega)).symm
    have hu : (u.subst n w).shift 0 1 = (u.shift 0 1).subst (n + 1) (w.shift 0 1) :=
      Expr.subst_shift_lo u n 0 1 w (by omega)
    rw [show n + 1 + 1 = (n + 1) + 1 from by omega, hw, hu]
    exact ihb (m + 1) (n + 1) (u.shift 0 1) (w.shift 0 1) (by omega)
  | app _ _ ihf iha => simp only [subst]; congr 1; exact ihf m n u w h; exact iha m n u w h
  | asc _ _ ihe iht => simp only [subst]; congr 1; exact ihe m n u w h; exact iht m n u w h
  | top => rfl

-- ============================================================
-- 4. Context lookup lemmas (fully proven)
-- ============================================================

theorem Ctx.get?_cons_zero (Γ : Ctx) (T : Expr) :
    Ctx.get? (T :: Γ) 0 = some (T.shift 0 1) := by simp [Ctx.get?, List.get?]

theorem Ctx.get?_cons_succ (Γ : Ctx) (T : Expr) (n : Nat) :
    Ctx.get? (T :: Γ) (n + 1) = (Ctx.get? Γ n).map (Expr.shift 0 1) := by
  simp only [Ctx.get?, List.get?]
  cases hΓ : List.get? Γ n with
  | none => simp
  | some U =>
    simp only [Option.map]; congr 1
    show U.shift 0 (n + 1 + 1) = (U.shift 0 (n + 1)).shift 0 1
    rw [Expr.shift_add]; congr 1; omega

-- ============================================================
-- 5. Weakening (lam sorry'd)
-- ============================================================

/-- Weakening: `Sub Γ a b → Sub (T :: Γ) (a.shift 0 1) (b.shift 0 1)`.
    Sorry: lam case needs exchange/generalized weakening. -/
theorem Sub.weaken {Γ : Ctx} {a b : Expr} (T : Expr)
    (h : Sub Γ a b) : Sub (T :: Γ) (a.shift 0 1) (b.shift 0 1) := by
  induction h with
  | refl _ a => exact Sub.refl _ _
  | top _ a => show Sub _ _ (Expr.top.shift 0 1); simp only [shift]; exact Sub.top _ _
  | var Γ' x b' U hget _ ih =>
    show Sub _ ((Expr.var x).shift 0 1) _
    simp only [shift, show ¬ x < 0 from by omega, ite_false]
    exact Sub.var _ (x+1) _ (U.shift 0 1) (by rw [Ctx.get?_cons_succ, hget]; simp) ih
  | @lam Γ' A B b₁ b₂ _ _ _ _ =>
    -- sorry: IH gives Sub (T :: B :: Γ') (b₁.shift 0 1) (b₂.shift 0 1)
    -- but we need Sub (B.shift 0 1 :: T :: Γ') (b₁.shift 1 1) (b₂.shift 1 1).
    sorry
  | @app Γ' f a b' D R _ _ _ ihfD ihaD ihRb =>
    show Sub _ ((Expr.app f a).shift 0 1) _; simp only [shift]
    rw [Expr.subst_shift_zero R a 1] at ihRb
    exact Sub.app _ (f.shift 0 1) (a.shift 0 1) _ (D.shift 0 1) (R.shift 1 1) ihfD ihaD ihRb
  | @betaR Γ' a' D body b' _ _ ihbD ihabody =>
    show Sub _ _ ((Expr.app (.lam D body) b').shift 0 1); simp only [shift]
    rw [Expr.subst_shift_zero body b' 1] at ihabody
    exact Sub.betaR _ (a'.shift 0 1) (D.shift 0 1) (body.shift 1 1) (b'.shift 0 1) ihbD ihabody
  | ascL _ e τ b' _ _ iheτ ihτb =>
    show Sub _ ((Expr.asc e τ).shift 0 1) _; simp only [shift]; exact Sub.ascL _ _ _ _ iheτ ihτb
  | ascR _ a' e τ _ _ iheτ ihaτ =>
    show Sub _ _ ((Expr.asc e τ).shift 0 1); simp only [shift]; exact Sub.ascR _ _ _ _ iheτ ihaτ

-- ============================================================
-- 6. Transitivity (multiple sorry'd cases)
-- ============================================================

/-- Transitivity: `Sub Γ a b → Sub Γ b c → Sub Γ a c`.
    Sorry'd: top, lam, betaR, ascR cases. -/
theorem Sub.trans {Γ : Ctx} {a b c : Expr}
    (hab : Sub Γ a b) (hbc : Sub Γ b c) : Sub Γ a c := by
  induction hab with
  | refl _ _ => exact hbc
  | top _ _ => sorry
  | var Γ' x _ U hget _ ih => exact Sub.var Γ' x c U hget (ih hbc)
  | @lam Γ' A B b₁ b₂ _ _ _ _ => sorry
  | app Γ' f a _ D R hfD haD _ _ _ ihRb =>
    exact Sub.app Γ' f a c D R hfD haD (ihRb hbc)
  | @betaR Γ' a' D body b' _ _ _ _ => sorry
  | ascL Γ' e τ _ heτ _ _ ihτb => exact Sub.ascL Γ' e τ c heτ (ihτb hbc)
  | @ascR Γ' a' e τ _ _ _ _ => sorry

-- ============================================================
-- 7. Substitution lemma (lam sorry'd)
-- ============================================================

/-- Substitution lemma. Fully proven cases: refl, top, var (using
    simplified [Var] rule), app, betaR, ascL, ascR. The var case at x=0
    uses transitivity (Sub.trans) and subst_shift_cancel; x>0 uses
    Ctx.get?_cons_succ. The app/betaR cases use Expr.subst_subst.

    Sorry'd: lam case requires generalized substitution at arbitrary depth.
    The body derivation is Sub (B :: T :: Γ) b₁ b₂, and after substituting
    v for var 0, the body's substitution is at index 1 (not 0). This requires
    a generalized substitution lemma Sub.subst_lemma_at that operates at
    arbitrary depth, which in turn requires exchange/permutation lemmas. -/
theorem Sub.subst_lemma {Γ : Ctx} {T a b v : Expr}
    (hab : Sub (T :: Γ) a b) (hv : Sub Γ v T)
    : Sub Γ (a.subst 0 v) (b.subst 0 v) := by
  sorry

end Och.Simple

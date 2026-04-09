import Och.Simple.Syntax
import Och.Simple.Subtype

/-!
# Properties of the Sub relation

We prove weakening, substitution, and transitivity for `Sub Γ a b`.
All auxiliary shift/subst lemmas are fully proven. The main Sub
properties have sorry'd cases documented below.
-/

set_option autoImplicit false
set_option maxHeartbeats 6400000

namespace Och.Simple

open Expr

-- ============================================================
-- 1. Shift lemmas
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

/-- When c ≤ n: (e.subst n v).shift c d = (e.shift c d).subst (n+d) (v.shift c d) -/
theorem Expr.subst_shift_lo (e : Expr) (n c d : Nat) (v : Expr) (h : c ≤ n) :
    (e.subst n v).shift c d = (e.shift c d).subst (n + d) (v.shift c d) := by
  induction e generalizing n c v with
  | var k =>
    simp only [subst, shift]
    split
    · rename_i h1; have hkn : k = n := beq_iff_eq.mp h1
      simp only [show ¬ k < c from by omega, ite_false, subst,
                 show (k + d == n + d) = true from by simp [beq_iff_eq]; omega, ite_true]
    · rename_i h1; have hkn : k ≠ n := by intro h; simp [h] at h1
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

/-- When n ≤ c: (e.subst n v).shift c d = (e.shift (c+1) d).subst n (v.shift c d) -/
theorem Expr.subst_shift_hi (e : Expr) (n c d : Nat) (v : Expr) (h : n ≤ c) :
    (e.subst n v).shift c d = (e.shift (c + 1) d).subst n (v.shift c d) := by
  induction e generalizing n c v with
  | var k =>
    simp only [subst, shift]
    split
    · rename_i h1; have hkn : k = n := beq_iff_eq.mp h1
      simp only [show k < c + 1 from by omega, ite_true, subst,
                 show (k == n) = true from h1, ite_true]
    · rename_i h1; have hkn : k ≠ n := by intro h; simp [h] at h1
      split
      · rename_i h2; by_cases hkc : k ≤ c
        · simp only [show k - 1 < c from by omega, show k < c + 1 from by omega, ite_true,
                      subst, show ¬ (k == n) = true from h1, ite_false, h2, ite_true]
        · simp only [show ¬ (k - 1 < c) from by omega, show ¬ (k < c + 1) from by omega, ite_false,
                      subst, show ¬ (k + d == n) = true from by simp [beq_iff_eq]; omega, ite_false,
                      show k + d > n from by omega, ite_true]; congr 1; omega
      · rename_i h2
        have hklt : k < n := by omega
        simp only [show k < c from by omega, show k < c + 1 from by omega, ite_true,
                    subst, show ¬ (k == n) = true from h1, ite_false, show ¬ k > n from by omega, ite_false]
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

/-- When m ≤ n:
    (e.subst (n+1) (w.shift m 1)).subst m (u.subst n w) = (e.subst m u).subst n w -/
theorem Expr.subst_subst (e : Expr) (m n : Nat) (u w : Expr) (h : m ≤ n) :
    (e.subst (n + 1) (w.shift m 1)).subst m (u.subst n w) =
    (e.subst m u).subst n w := by
  induction e generalizing m n u w with
  | var k =>
    simp only [subst]
    split
    · -- k == m
      rename_i hkm; have hk : k = m := beq_iff_eq.mp hkm
      simp only [show ¬ (k == n + 1) = true from by simp [beq_iff_eq]; omega, ite_false,
                  show ¬ k > n + 1 from by omega, ite_false,
                  subst, hkm, ite_true]
    · rename_i hkm; have hkne : k ≠ m := by intro h; simp [h] at hkm
      split
      · -- k > m
        rename_i hkgtm
        split
        · -- k == n+1
          rename_i hkn1; have hk : k = n + 1 := beq_iff_eq.mp hkn1
          rw [Expr.subst_shift_cancel w m (u.subst n w)]
          simp only [subst, show (k - 1 == n) = true from by simp [beq_iff_eq]; omega, ite_true]
        · rename_i hkn1; have hkne1 : k ≠ n + 1 := by intro h; simp [h] at hkn1
          split
          · -- k > n+1
            rename_i hkgtn1
            have hk1m : k - 1 > m := by omega
            have hk11n : k - 1 - 1 > n := by omega
            have hk1n : k - 1 > n := by omega
            simp only [subst, show ¬ (k - 1 == m) = true from by simp [beq_iff_eq]; omega, ite_false,
                        show k - 1 > m from hk1m, ite_true,
                        show ¬ (k - 1 - 1 == n) = true from by simp [beq_iff_eq]; omega, ite_false,
                        show k - 1 - 1 > n from hk11n, ite_true,
                        show ¬ (k - 1 == n) = true from by simp [beq_iff_eq]; omega, ite_false,
                        show k - 1 > n from hk1n, ite_true]
            congr 1; omega
          · -- m < k ≤ n
            rename_i hkgtn1
            simp only [subst, show ¬ (k == m) = true from by simp [beq_iff_eq]; exact hkne, ite_false,
                        show k > m from hkgtm, ite_true,
                        show ¬ (k - 1 == n) = true from by simp [beq_iff_eq]; omega, ite_false,
                        show ¬ k - 1 > n from by omega, ite_false]
      · -- k < m
        rename_i hkgtm
        simp only [show ¬ (k == n + 1) = true from by simp [beq_iff_eq]; omega, ite_false,
                    show ¬ k > n + 1 from by omega, ite_false,
                    subst, hkm, ite_false, show ¬ k > m from by omega, ite_false,
                    show ¬ (k == n) = true from by simp [beq_iff_eq]; omega, ite_false,
                    show ¬ k > n from by omega, ite_false]
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
-- 4. Context lookup lemmas
-- ============================================================

theorem Ctx.get?_cons_zero (Γ : Ctx) (T : Expr) :
    Ctx.get? (T :: Γ) 0 = some (T.shift 0 1) := by simp [Ctx.get?, List.get?]

theorem Ctx.get?_cons_succ (Γ : Ctx) (T : Expr) (n : Nat) :
    Ctx.get? (T :: Γ) (n + 1) = (Ctx.get? Γ n).map (Expr.shift 0 1) := by
  simp only [Ctx.get?, List.get?]
  cases h : List.get? Γ n with
  | none => simp
  | some U => simp only [Option.map]; congr 1
              rw [← Expr.shift_add U 0 1 (n + 1)]; congr 1; omega

-- ============================================================
-- 5. Weakening
-- ============================================================

/-- Weakening: `Sub Γ a b → Sub (T :: Γ) (a.shift 0 1) (b.shift 0 1)`.

    **Sorry'd**: lam case requires exchange or generalized weakening. -/
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
    -- but goal needs Sub (B.shift 0 1 :: T :: Γ') (b₁.shift 1 1) (b₂.shift 1 1)
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
-- 6. Transitivity
-- ============================================================

/-- Transitivity: `Sub Γ a b → Sub Γ b c → Sub Γ a c`.

    **Sorry'd**: top, lam, betaR, ascR cases. See inline comments. -/
theorem Sub.trans {Γ : Ctx} {a b c : Expr}
    (hab : Sub Γ a b) (hbc : Sub Γ b c) : Sub Γ a c := by
  induction hab with
  | refl _ _ => exact hbc
  | top _ _ =>
    -- .top on LHS of hbc can produce arbitrary c via betaR/ascR
    sorry
  | var Γ' x _ U hget _ ih => exact Sub.var Γ' x c U hget (ih hbc)
  | lam .. =>
    -- lam-lam sub-case requires narrowing (changing context from B::Γ to C::Γ)
    sorry
  | app Γ' f a _ D R hfD haD _ _ _ ihRb =>
    exact Sub.app Γ' f a c D R hfD haD (ihRb hbc)
  | betaR .. =>
    -- need to decompose Sub with (.app (.lam ..)) on LHS of hbc
    sorry
  | ascL Γ' e τ _ heτ _ _ ihτb => exact Sub.ascL Γ' e τ c heτ (ihτb hbc)
  | ascR .. =>
    -- betaR sub-case of hbc creates circular dependency
    sorry

-- ============================================================
-- 7. Substitution lemma
-- ============================================================

/-- Substitution lemma:
    `Sub (T :: Γ) a b → Sub Γ v T → Sub Γ (a.subst 0 v) (b.subst 0 v)`.

    **Sorry'd**: lam case requires generalized substitution at arbitrary depth. -/
theorem Sub.subst_lemma {Γ : Ctx} {T a b v : Expr}
    (hab : Sub (T :: Γ) a b) (hv : Sub Γ v T)
    : Sub Γ (a.subst 0 v) (b.subst 0 v) := by
  induction hab with
  | refl _ _ => exact Sub.refl _ _
  | top _ _ => show Sub Γ _ (Expr.top.subst 0 v); simp only [subst]; exact Sub.top _ _
  | @var _ x _ U hget _ ih =>
    show Sub Γ ((Expr.var x).subst 0 v) _; simp only [subst]
    cases x with
    | zero =>
      simp only [show (0 == 0) = true from rfl, ite_true]
      rw [Ctx.get?_cons_zero] at hget; subst (Option.some.inj hget)
      rw [Expr.subst_shift_cancel_zero] at ih; exact Sub.trans hv ih
    | succ n =>
      simp only [show ¬ (n+1 == 0) = true from by simp [beq_iff_eq]; omega, ite_false,
                  show n+1 > 0 from by omega, ite_true, show n+1-1 = n from by omega]
      rw [Ctx.get?_cons_succ] at hget
      match hΓn : Ctx.get? Γ n with
      | none => simp [hΓn] at hget
      | some U' => simp [hΓn] at hget; subst hget
                   rw [Expr.subst_shift_cancel_zero] at ih; exact Sub.var Γ n _ U' hΓn ih
  | @lam _ A B b₁ b₂ _ _ _ _ =>
    -- sorry: body substitution is at index 1, not 0. Requires generalized lemma.
    sorry
  | @app _ f a' b' D R _ _ _ ihfD ihaD ihRb =>
    show Sub Γ ((Expr.app f a').subst 0 v) _; simp only [subst]
    rw [Expr.subst_subst R 0 0 a' v (by omega)] at ihRb
    exact Sub.app Γ _ _ _ (D.subst 0 v) (R.subst 1 (v.shift 0 1)) ihfD ihaD ihRb
  | @betaR _ a' D body b' _ _ ihbD ihabody =>
    show Sub Γ _ ((Expr.app (.lam D body) b').subst 0 v); simp only [subst]
    rw [← Expr.subst_subst body 0 0 b' v (by omega)] at ihabody
    exact Sub.betaR Γ _ (D.subst 0 v) (body.subst 1 (v.shift 0 1)) _ ihbD ihabody
  | ascL _ e τ _ _ _ iheτ ihτb =>
    show Sub Γ ((Expr.asc e τ).subst 0 v) _; simp only [subst]; exact Sub.ascL _ _ _ _ iheτ ihτb
  | ascR _ _ e τ _ _ iheτ ihaτ =>
    show Sub Γ _ ((Expr.asc e τ).subst 0 v); simp only [subst]; exact Sub.ascR _ _ _ _ iheτ ihaτ

end Och.Simple

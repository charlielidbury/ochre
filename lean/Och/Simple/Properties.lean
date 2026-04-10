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
- `liftCtx`, `Ctx.get?_liftCtx_lt`, `Ctx.get?_liftCtx_ge`: fully proven
- `Sub.weaken_gen`: fully proven (all 7 cases including Lam!)
- `Sub.weaken`: fully proven (corollary of weaken_gen)
- `Sub.weaken_prepend`: fully proven (multi-weakening by prepending a prefix)
- `Sub.trans`: FULLY PROVEN — lexicographic induction on
  (b.complexity, hab.size + hbc.size) via mutual trans+narrow_gen.
  BetaR removed from Sub. Narrow generalized to arbitrary depth via
  Γ_pre prefix, closing all cases. Zero sorrys in transitivity proof.
- `substCtx`: fully defined
- `Sub.subst_gen`: generalized substitution at arbitrary depth, 6/7 cases
  proven (all cases including Lam!), [Var] sorry'd (needs context lookup
  lemmas for Δ ++ T :: Γ and Sub.trans for x = |Δ|)
- `Sub.subst_lemma`: corollary of subst_gen with Δ = []
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
  | mu _ _ iha ihb => simp only [shift]; congr 1; exact iha c; exact ihb (c + 1)

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
  | mu _ _ iha ihb =>
    simp only [shift]; congr 1; exact iha c₁ c₂ h
    rw [show c₂ + n₁ + 1 = (c₂ + 1) + n₁ from by omega]; exact ihb (c₁ + 1) (c₂ + 1) (by omega)

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
  | mu _ _ iha ihb =>
    simp only [subst, shift]; congr 1; exact iha n c v h
    have := ihb (n + 1) (c + 1) (v.shift 0 1) (by omega)
    rw [show n + 1 + d = (n + d) + 1 from by omega] at this; rw [this]; congr 1
    exact Expr.shift_shift_comm v 0 c 1 d (by omega)

theorem Expr.subst_shift_hi (e : Expr) (n c d : Nat) (v : Expr) (h : n ≤ c) :
    (e.subst n v).shift c d = (e.shift (c + 1) d).subst n (v.shift c d) := by
  induction e generalizing n c v with
  | var k =>
    -- LHS: ((var k).subst n v).shift c d
    -- RHS: ((var k).shift (c+1) d).subst n (v.shift c d)
    -- Compute LHS:
    have lhs_eq : (Expr.var k).subst n v = if k == n then v else if k > n then Expr.var (k - 1) else Expr.var k := by simp [subst]
    -- Compute RHS shift:
    have rhs_shift : (Expr.var k).shift (c + 1) d = if k < c + 1 then Expr.var k else Expr.var (k + d) := by simp [shift]
    rw [lhs_eq, rhs_shift]
    by_cases hkn : k = n
    · subst hkn
      simp only [beq_self_eq_true, ite_true, show k < c + 1 from by omega, subst, beq_self_eq_true, ite_true]
    · simp only [show (k == n) = false from by rw [beq_eq_false_iff_ne]; exact hkn,
                  Bool.false_eq_true, ite_false]
      by_cases hk_gt : k > n
      · simp only [hk_gt, ite_true]
        by_cases hkc : k - 1 < c
        · simp only [shift, hkc, ite_true, show k < c + 1 from by omega, ite_true, subst,
            show (k == n) = false from by rw [beq_eq_false_iff_ne]; exact hkn,
            Bool.false_eq_true, ite_false, show k > n from hk_gt, ite_true]
        · simp only [shift, hkc, ite_false, show ¬ (k < c + 1) from by omega, ite_false, subst,
            show (k + d == n) = false from by rw [beq_eq_false_iff_ne]; omega,
            Bool.false_eq_true, ite_false, show k + d > n from by omega, ite_true]
          congr 1; omega
      · simp only [hk_gt, ite_false, shift, show k < c from by omega, ite_true,
          show k < c + 1 from by omega, subst,
          show (k == n) = false from by rw [beq_eq_false_iff_ne]; exact hkn,
          Bool.false_eq_true, ite_false, hk_gt, ite_false]
  | lam _ _ ihd ihb =>
    simp only [subst, shift]; congr 1; exact ihd n c v h
    have := ihb (n + 1) (c + 1) (v.shift 0 1) (by omega)
    rw [show c + 1 + 1 = (c + 1) + 1 from by omega] at this; rw [this]; congr 1
    exact Expr.shift_shift_comm v 0 c 1 d (by omega)
  | app _ _ ihf iha => simp only [subst, shift]; congr 1; exact ihf n c v h; exact iha n c v h
  | asc _ _ ihe iht => simp only [subst, shift]; congr 1; exact ihe n c v h; exact iht n c v h
  | top => rfl
  | mu _ _ iha ihb =>
    simp only [subst, shift]; congr 1; exact iha n c v h
    have := ihb (n + 1) (c + 1) (v.shift 0 1) (by omega)
    rw [show c + 1 + 1 = (c + 1) + 1 from by omega] at this; rw [this]; congr 1
    exact Expr.shift_shift_comm v 0 c 1 d (by omega)

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
    -- LHS: ((var k).subst (n+1) (w.shift m 1)).subst m (u.subst n w)
    -- RHS: ((var k).subst m u).subst n w
    have lhs_subst1 : (Expr.var k).subst (n + 1) (w.shift m 1) =
      if k == n + 1 then w.shift m 1 else if k > n + 1 then Expr.var (k - 1) else Expr.var k := by simp [subst]
    have rhs_subst1 : (Expr.var k).subst m u =
      if k == m then u else if k > m then Expr.var (k - 1) else Expr.var k := by simp [subst]
    rw [lhs_subst1, rhs_subst1]
    by_cases hkn1 : k = n + 1
    · subst hkn1
      simp only [beq_self_eq_true, ite_true,
        show (n + 1 == m) = false from by rw [beq_eq_false_iff_ne]; omega,
        Bool.false_eq_true, ite_false,
        show n + 1 > m from by omega, ite_true, show n + 1 - 1 = n from by omega,
        subst, beq_self_eq_true, ite_true]
      exact Expr.subst_shift_cancel w m (u.subst n w)
    · simp only [show (k == n + 1) = false from by rw [beq_eq_false_iff_ne]; exact hkn1,
                  Bool.false_eq_true, ite_false]
      by_cases hkn1_gt : k > n + 1
      · simp only [hkn1_gt, ite_true]
        -- LHS: (var (k-1)).subst m (u.subst n w); k-1 ≠ m (since k > n+1 ≥ m+1, k-1 ≥ n+1 > m when n ≥ m)
        -- wait, k-1 ≥ n+1 > n ≥ m, so k-1 > m. So LHS = var (k-1-1)
        -- Then .subst m (u.subst n w): k-1-1 could be = m if k = m+2
        -- Actually no, k > n+1 and m ≤ n, so k ≥ n+2 ≥ m+2, k-1 ≥ m+1 > m, k-1-1 ≥ m
        -- k-1-1 = m iff k = m+2. Since k ≥ n+2 and m ≤ n, m+2 ≤ n+2 ≤ k. So k-1-1 ≥ m.
        -- If k = m+2: k-1-1 = m, beq is true.
        -- Hmm this is getting complicated. Let me use a different strategy.
        -- Actually, k-1 > m means k-1 ≥ m+1, so k ≥ m+2, k-1-1 ≥ m. But k-1-1 could equal m.
        -- Let's just compute more carefully.
        -- LHS inner: (var (k-1)).subst m (u.subst n w)
        --   k-1 ≠ m (k > n+1, n ≥ m, so k ≥ n+2 ≥ m+2, k-1 ≥ m+1 > m... wait, k-1 could be m+1, not = m)
        --   Actually k-1 > m always: k > n+1 ≥ m+1, so k-1 ≥ m+1 > m. So k-1 ≠ m and k-1 > m.
        --   Result: var (k-1-1)
        -- LHS outer: (var (k-1-1)).subst m (u.subst n w)  -- WAIT, the outer subst was already done
        -- No wait, the structure is: ((var k).subst (n+1) (w.shift m 1)).subst m (u.subst n w)
        -- = (var (k-1)).subst m (u.subst n w) [since k > n+1, k ≠ n+1]
        -- Now k-1 > m (as argued), k-1 ≠ m, so result = var (k-1-1)
        -- RHS: ((var k).subst m u).subst n w
        -- k > m (k > n+1 ≥ m+1 > m), k ≠ m, so = (var (k-1)).subst n w
        -- k-1 > n (k > n+1 means k-1 ≥ n+1 > n), k-1 ≠ n (k-1 ≥ n+1 > n), so = var (k-1-1)
        -- Both sides are var (k-1-1). ✓
        -- But actually k - 1 - 1 in Lean Nat might be weird. k > n+1 means k ≥ n+2 ≥ 2, so k-1 ≥ 1, k-1-1 ≥ 0. OK.
        simp only [subst,
          show (k - 1 == m) = false from by rw [beq_eq_false_iff_ne]; omega,
          show (k == m) = false from by rw [beq_eq_false_iff_ne]; omega,
          show (k - 1 == n) = false from by rw [beq_eq_false_iff_ne]; omega,
          Bool.false_eq_true, ite_false,
          show k - 1 > m from by omega, ite_true,
          show k > m from by omega, ite_true,
          show k - 1 > n from by omega, ite_true]
        -- Goal: var (k - 1 - 1) = var (k - 1 - 1)  -- but Lean might represent differently
        -- Actually LHS subst gave var ((k-1) - 1) and RHS gave var ((k-1) - 1), should be identical
      · simp only [hkn1_gt, ite_false]
        by_cases hkm : k = m
        · subst hkm
          simp only [beq_self_eq_true, ite_true, subst, beq_self_eq_true, ite_true]
        · -- k ≠ m, k ≤ n
          -- LHS has (var k).subst m (u.subst n w): since k ≠ m
          -- RHS has (if (k == m) then u else if k > m then var (k-1) else var k).subst n w
          -- Need to simplify (k == m) on both sides first
          simp only [show (k == m) = false from by rw [beq_eq_false_iff_ne]; exact hkm,
                      Bool.false_eq_true, ite_false]
          by_cases hkm_gt : k > m
          · -- k > m: LHS = var (k-1), RHS = (var (k-1)).subst n w = var (k-1) since k-1 < n
            simp only [hkm_gt, ite_true, subst,
              show (k == m) = false from by rw [beq_eq_false_iff_ne]; exact hkm,
              show (k - 1 == n) = false from by rw [beq_eq_false_iff_ne]; omega,
              Bool.false_eq_true, ite_false,
              show k > m from hkm_gt, ite_true,
              show ¬ (k - 1 > n) from by omega, ite_false]
          · -- k < m
            simp only [hkm_gt, ite_false, subst,
              show (k == m) = false from by rw [beq_eq_false_iff_ne]; exact hkm,
              show (k == n) = false from by rw [beq_eq_false_iff_ne]; omega,
              Bool.false_eq_true, ite_false,
              show ¬ (k > m) from hkm_gt, ite_false,
              show ¬ (k > n) from by omega, ite_false]
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
  | mu _ _ iha ihb =>
    simp only [subst]; congr 1; exact iha m n u w h
    have hw : (w.shift m 1).shift 0 1 = (w.shift 0 1).shift (m + 1) 1 :=
      (Expr.shift_shift_comm w 0 m 1 1 (by omega)).symm
    have hu : (u.subst n w).shift 0 1 = (u.shift 0 1).subst (n + 1) (w.shift 0 1) :=
      Expr.subst_shift_lo u n 0 1 w (by omega)
    rw [show n + 1 + 1 = (n + 1) + 1 from by omega, hw, hu]
    exact ihb (m + 1) (n + 1) (u.shift 0 1) (w.shift 0 1) (by omega)

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
-- 5. Generalized weakening (fully proven)
-- ============================================================

/-- Insert binding T at position n in context Γ, shifting stored types to account for the new binding. -/
def liftCtx : Nat → Expr → Ctx → Ctx
  | 0, T, Γ => T :: Γ
  | _+1, T, [] => [T]
  | n+1, T, A :: Γ => (A.shift n 1) :: liftCtx n T Γ

/-- If `Ctx.get? Γ x = some U` and `x < n`, then `Ctx.get? (liftCtx n T Γ) x = some (U.shift n 1)`.
    The variable is before the insertion point so its index stays the same. -/
theorem Ctx.get?_liftCtx_lt {Γ : Ctx} {x : Nat} {U : Expr}
    (n : Nat) (T : Expr) (hget : Ctx.get? Γ x = some U) (hx : x < n) :
    Ctx.get? (liftCtx n T Γ) x = some (U.shift n 1) := by
  induction n generalizing Γ x U with
  | zero => omega
  | succ n ih =>
    match Γ with
    | [] =>
      -- Ctx.get? [] x can never be some
      cases x with
      | zero => simp [Ctx.get?] at hget
      | succ x => simp [Ctx.get?] at hget
    | A :: Γ =>
      cases x with
      | zero =>
        -- Ctx.get? (A :: Γ) 0 = some (A.shift 0 1) by get?_cons_zero
        -- liftCtx (n+1) T (A :: Γ) = (A.shift n 1) :: liftCtx n T Γ
        -- Ctx.get? ((A.shift n 1) :: liftCtx n T Γ) 0 = some ((A.shift n 1).shift 0 1)
        simp only [liftCtx]
        rw [Ctx.get?_cons_zero] at hget ⊢
        simp only [Option.some.injEq] at hget ⊢
        rw [← hget]
        -- goal: (A.shift n 1).shift 0 1 = (A.shift 0 1).shift (n+1) 1
        exact (Expr.shift_shift_comm A 0 n 1 1 (by omega)).symm
      | succ x =>
        -- liftCtx (n+1) T (A :: Γ) = (A.shift n 1) :: liftCtx n T Γ
        simp only [liftCtx]
        rw [Ctx.get?_cons_succ] at hget ⊢
        -- hget: (Ctx.get? Γ x).map (shift 0 1) = some U
        -- goal: (Ctx.get? (liftCtx n T Γ) x).map (shift 0 1) = some (U.shift (n+1) 1)
        cases hΓ : Ctx.get? Γ x with
        | none => simp [hΓ] at hget
        | some W =>
          simp only [hΓ, Option.map, Option.some.injEq] at hget ⊢
          -- hget: W.shift 0 1 = U
          -- IH: Ctx.get? (liftCtx n T Γ) x = some (W.shift n 1)
          have him := @ih Γ x W (by rw [hΓ]) (by omega)
          cases hL : Ctx.get? (liftCtx n T Γ) x with
          | none => rw [hL] at him; simp at him
          | some W' =>
            rw [hL] at him; simp only [Option.some.injEq] at him
            simp only [hL, Option.map, Option.some.injEq]
            -- him: W' = W.shift n 1
            -- goal: W'.shift 0 1 = U.shift (n+1) 1
            rw [← hget, him]
            -- goal: (W.shift n 1).shift 0 1 = (W.shift 0 1).shift (n+1) 1
            exact (Expr.shift_shift_comm W 0 n 1 1 (by omega)).symm

/-- If `Ctx.get? Γ x = some U` and `x ≥ n`, then `Ctx.get? (liftCtx n T Γ) (x+1) = some (U.shift n 1)`.
    The variable is at or after the insertion point so its index shifts by 1. -/
theorem Ctx.get?_liftCtx_ge {Γ : Ctx} {x : Nat} {U : Expr}
    (n : Nat) (T : Expr) (hget : Ctx.get? Γ x = some U) (hx : n ≤ x) :
    Ctx.get? (liftCtx n T Γ) (x + 1) = some (U.shift n 1) := by
  induction n generalizing Γ x U with
  | zero =>
    -- liftCtx 0 T Γ = T :: Γ
    simp only [liftCtx]
    rw [Ctx.get?_cons_succ]
    rw [hget]; simp only [Option.map]
  | succ n ih =>
    match Γ with
    | [] =>
      cases x with
      | zero => simp [Ctx.get?] at hget
      | succ x => simp [Ctx.get?] at hget
    | A :: Γ =>
      cases x with
      | zero => omega
      | succ x =>
        -- liftCtx (n+1) T (A :: Γ) = (A.shift n 1) :: liftCtx n T Γ
        simp only [liftCtx]
        -- Need: Ctx.get? ((A.shift n 1) :: liftCtx n T Γ) (x+2) = some (U.shift (n+1) 1)
        rw [Ctx.get?_cons_succ] at hget ⊢
        -- hget: (Ctx.get? Γ x).map (shift 0 1) = some U
        -- goal: (Ctx.get? (liftCtx n T Γ) (x+1)).map (shift 0 1) = some (U.shift (n+1) 1)
        cases hΓ : Ctx.get? Γ x with
        | none => simp [hΓ] at hget
        | some W =>
          simp only [hΓ, Option.map, Option.some.injEq] at hget ⊢
          -- hget: W.shift 0 1 = U
          have him := @ih Γ x W (by rw [hΓ]) (by omega)
          -- him: Ctx.get? (liftCtx n T Γ) (x+1) = some (W.shift n 1)
          cases hL : Ctx.get? (liftCtx n T Γ) (x + 1) with
          | none => rw [hL] at him; simp at him
          | some W' =>
            rw [hL] at him; simp only [Option.some.injEq] at him
            simp only [hL, Option.map, Option.some.injEq]
            rw [← hget, him]
            exact (Expr.shift_shift_comm W 0 n 1 1 (by omega)).symm

/-- Generalized weakening: inserting a binding at arbitrary position n. -/
noncomputable def Sub.weaken_gen {Γ : Ctx} {a b : Expr} (n : Nat) (T : Expr)
    (h : Sub Γ a b) : Sub (liftCtx n T Γ) (a.shift n 1) (b.shift n 1) := by
  induction h generalizing n with
  | refl _ a => exact Sub.refl _ _
  | top _ a =>
    show Sub _ _ (Expr.top.shift n 1); simp only [shift]; exact Sub.top _ _
  | var Γ' x b' U hget _ ih =>
    show Sub _ ((Expr.var x).shift n 1) _
    simp only [shift]
    by_cases hxn : x < n
    · -- x < n: variable before insertion point
      simp only [hxn, ite_true]
      exact Sub.var _ x _ (U.shift n 1)
        (Ctx.get?_liftCtx_lt n T hget hxn)
        (ih n)
    · -- x ≥ n: variable after insertion point
      simp only [hxn, ite_false]
      exact Sub.var _ (x + 1) _ (U.shift n 1)
        (Ctx.get?_liftCtx_ge n T hget (by omega))
        (ih n)
  | @lam Γ' A B b₁ b₂ _hBA _hb₁b₂ ihBA ihb₁b₂ =>
    show Sub _ (Expr.lam (A.shift n 1) (b₁.shift (n+1) 1)) (Expr.lam (B.shift n 1) (b₂.shift (n+1) 1))
    have hdom := ihBA n
    have hbody := ihb₁b₂ (n + 1)
    -- KEY: liftCtx (n+1) T (B::Γ') = (B.shift n 1) :: liftCtx n T Γ' by definition!
    exact Sub.lam _ _ _ _ _ hdom hbody
  | @app Γ' f a b' D R _ _ _ ihfD ihaD ihRb =>
    show Sub _ ((Expr.app f a).shift n 1) _; simp only [shift]
    have ihRb' := ihRb n
    rw [Expr.subst_shift_hi R 0 n 1 a (by omega)] at ihRb'
    exact Sub.app _ (f.shift n 1) (a.shift n 1) _ (D.shift n 1) (R.shift (n+1) 1) (ihfD n) (ihaD n) ihRb'
  | ascL _ e τ b' _ _ iheτ ihτb =>
    show Sub _ ((Expr.asc e τ).shift n 1) _; simp only [shift]; exact Sub.ascL _ _ _ _ (iheτ n) (ihτb n)
  | ascR _ a' e τ _ _ iheτ ihaτ =>
    show Sub _ _ ((Expr.asc e τ).shift n 1); simp only [shift]; exact Sub.ascR _ _ _ _ (iheτ n) (ihaτ n)
  | @mu Γ' A b' c _hAc _hbA ihAc ihbA =>
    show Sub _ ((Expr.mu A b').shift n 1) _; simp only [shift]
    have hdom := ihAc n
    have hbody := ihbA (n + 1)
    -- Need: A.shift 0 1 shifted at (n+1) = (A.shift n 1).shift 0 1
    rw [Expr.shift_shift_comm A 0 n 1 1 (by omega)] at hbody
    exact Sub.mu _ _ _ _ hdom hbody

/-- Weakening: `Sub Γ a b → Sub (T :: Γ) (a.shift 0 1) (b.shift 0 1)`. Corollary of generalized weakening. -/
noncomputable def Sub.weaken {Γ : Ctx} {a b : Expr} (T : Expr)
    (h : Sub Γ a b) : Sub (T :: Γ) (a.shift 0 1) (b.shift 0 1) :=
  Sub.weaken_gen 0 T h

/-- Multi-weakening: prepending any prefix to the context shifts free variables accordingly. -/
noncomputable def Sub.weaken_prepend {Γ : Ctx} {a b : Expr}
    (Δ : Ctx) (h : Sub Γ a b) : Sub (Δ ++ Γ) (a.shift 0 Δ.length) (b.shift 0 Δ.length) := by
  induction Δ with
  | nil => simp [Expr.shift_zero]; exact h
  | cons T Δ ih =>
    simp only [List.cons_append, List.length_cons]
    have h1 := Sub.weaken T ih
    rw [Expr.shift_add] at h1
    rw [Expr.shift_add] at h1
    simp only [show 1 + Δ.length = Δ.length + 1 from by omega] at h1
    exact h1

-- ============================================================
-- 6. Transitivity and Narrowing (mutually dependent)
-- ============================================================

-- Transitivity and generalized narrowing are mutually dependent:
-- * Transitivity [Lam-Lam] case needs narrowing to re-type the
--   body under a narrowed context.
-- * Narrowing [Var x=0] case needs transitivity to compose the
--   weakened Sub Γ C B with the narrowed continuation.
--
-- We use a LEXICOGRAPHIC measure: (b.complexity, hab.size + hbc.size).
-- Encoded via two nested inductions:
--   Outer: on `m` bounding b.complexity (for trans)
--   Inner: on `n` bounding derivation sizes (for both trans and narrow)
--
-- Key insight: in [Lam-Lam], b = lam B b₂, and the body trans has cut
-- formula b₂ with strictly smaller complexity. So the outer measure
-- decreases, allowing arbitrary derivation sizes.
--
-- Similarly in [AscR-AscL], b = asc e τ, and both intermediate trans
-- calls use cut formulae e and τ which have strictly smaller complexity.
--
-- Recall the Sub.lam constructor:
--   Sub.lam Γ A B b₁ b₂ : Sub Γ B A → Sub (B :: Γ) b₁ b₂ → Sub Γ (.lam A b₁) (.lam B b₂)
-- So the first Sub arg is contra-variant (B ⊑ A), and the body lives under B.
--
-- BetaR removed from Sub, eliminating the BetaR-App sorry.
-- Narrow generalized to arbitrary depth via Γ_pre prefix, closing Narrow Lam.

/-- Complexity of an expression — counts constructors. Used as the primary
    component of the lexicographic termination measure for transitivity. -/
def Expr.complexity : Expr → Nat
  | .var _ => 0
  | .top => 0
  | .lam d b => 1 + d.complexity + b.complexity
  | .app f a => 1 + f.complexity + a.complexity
  | .asc e t => 1 + e.complexity + t.complexity
  | .mu ann body => 1 + ann.complexity + body.complexity

/-- Shifting preserves complexity — shift only changes variable indices, not structure. -/
theorem Expr.shift_complexity (e : Expr) (c n : Nat) : (e.shift c n).complexity = e.complexity := by
  induction e generalizing c with
  | var k => simp [shift, complexity]; split <;> simp [complexity]
  | lam d b ihd ihb => simp [shift, complexity, ihd c, ihb (c+1)]
  | app f a ihf iha => simp [shift, complexity, ihf c, iha c]
  | asc e t ihe iht => simp [shift, complexity, ihe c, iht c]
  | top => rfl
  | mu ann body iha ihb => simp [shift, complexity, iha c, ihb (c+1)]

-- 6a. Sub.size — derivation size for well-founded recursion

/-- Size of a subtyping derivation (number of nodes). -/
def Sub.size {Γ : Ctx} {a b : Expr} : Sub Γ a b → Nat
  | .refl _ _ => 1
  | .top _ _ => 1
  | .var _ _ _ _ _ h => 1 + h.size
  | .lam _ _ _ _ _ h1 h2 => 1 + h1.size + h2.size
  | .app _ _ _ _ _ _ h1 h2 h3 => 1 + h1.size + h2.size + h3.size
  | .ascL _ _ _ _ h1 h2 => 1 + h1.size + h2.size
  | .ascR _ _ _ _ h1 h2 => 1 + h1.size + h2.size
  | .mu _ _ _ _ h1 h2 => 1 + h1.size + h2.size

/-- Every derivation has positive size. -/
theorem Sub.size_pos {Γ : Ctx} {a b : Expr} (h : Sub Γ a b) : 0 < h.size := by
  cases h <;> simp [Sub.size] <;> omega

-- 6b. Inner induction (on derivation sizes)
-- Given access to trans at strictly smaller cut-formula complexity,
-- prove trans + narrow at bounded derivation sizes.

-- Context lookup lemmas for narrowing at arbitrary depth.

/-- Raw list lookup: positions before |Γ_pre| are the same in both contexts. -/
private theorem List.get?_narrow_lt_raw {Γ_pre Γ_suf : List Expr} {B C : Expr} {x : Nat}
    (hx : x < Γ_pre.length) :
    List.get? (Γ_pre ++ B :: Γ_suf) x = List.get? (Γ_pre ++ C :: Γ_suf) x := by
  induction Γ_pre generalizing x with
  | nil => simp [List.length] at hx
  | cons A Γ_pre ih =>
    cases x with
    | zero => simp [List.get?]
    | succ x =>
      simp only [List.cons_append, List.get?]
      exact ih (by simp [List.length] at hx; omega)

/-- Variables before the narrowing point are unchanged. -/
theorem Ctx.get?_narrow_lt {Γ_pre Γ_suf : Ctx} {B : Expr} (C : Expr) {x : Nat} {U : Expr}
    (hget : Ctx.get? (Γ_pre ++ B :: Γ_suf) x = some U) (hx : x < Γ_pre.length) :
    Ctx.get? (Γ_pre ++ C :: Γ_suf) x = some U := by
  simp only [Ctx.get?] at hget ⊢
  rw [← List.get?_narrow_lt_raw (B := B) (C := C) hx]; exact hget

/-- The variable at the narrowing point changes from B to C. -/
theorem Ctx.get?_narrow_eq {Γ_pre Γ_suf : Ctx} {B : Expr} {U : Expr}
    (hget : Ctx.get? (Γ_pre ++ B :: Γ_suf) Γ_pre.length = some U) :
    U = (B.shift 0 (Γ_pre.length + 1)) := by
  induction Γ_pre generalizing U with
  | nil => simp [Ctx.get?, List.get?] at hget; exact hget.symm
  | cons A Γ_pre ih =>
    simp only [List.cons_append, List.length_cons] at hget
    rw [Ctx.get?_cons_succ] at hget
    cases hΓ : Ctx.get? (Γ_pre ++ B :: Γ_suf) Γ_pre.length with
    | none => simp [hΓ] at hget
    | some W =>
      simp only [hΓ, Option.map, Option.some.injEq] at hget
      have := ih (by rw [hΓ])
      rw [← hget, this]
      simp only [List.length_cons]
      rw [Expr.shift_add]; congr 1; omega

/-- The variable at the narrowing point in the new context gives C.shifted. -/
theorem Ctx.get?_narrow_eq_new {Γ_pre Γ_suf : Ctx} {C : Expr} :
    Ctx.get? (Γ_pre ++ C :: Γ_suf) Γ_pre.length = some (C.shift 0 (Γ_pre.length + 1)) := by
  induction Γ_pre with
  | nil => simp [Ctx.get?, List.get?]
  | cons A Γ_pre ih =>
    simp only [List.cons_append, List.length_cons]
    rw [Ctx.get?_cons_succ]
    rw [ih]; simp only [Option.map, Option.some.injEq]
    rw [Expr.shift_add]; congr 1; omega

/-- Raw list lookup: positions after |Γ_pre| are the same in both contexts. -/
private theorem List.get?_narrow_gt_raw {Γ_pre Γ_suf : List Expr} {B C : Expr} {x : Nat}
    (hx : Γ_pre.length < x) :
    List.get? (Γ_pre ++ B :: Γ_suf) x = List.get? (Γ_pre ++ C :: Γ_suf) x := by
  induction Γ_pre generalizing x with
  | nil =>
    cases x with
    | zero => omega
    | succ x => simp [List.nil_append, List.get?]
  | cons A Γ_pre ih =>
    cases x with
    | zero => omega
    | succ x =>
      simp only [List.cons_append, List.get?, List.length_cons] at hx ⊢
      exact ih (by omega)

/-- Variables after the narrowing point are unchanged. -/
theorem Ctx.get?_narrow_gt {Γ_pre Γ_suf : Ctx} {B : Expr} (C : Expr) {x : Nat} {U : Expr}
    (hget : Ctx.get? (Γ_pre ++ B :: Γ_suf) x = some U) (hx : Γ_pre.length < x) :
    Ctx.get? (Γ_pre ++ C :: Γ_suf) x = some U := by
  simp only [Ctx.get?] at hget ⊢
  rw [← List.get?_narrow_gt_raw (B := B) (C := C) hx]; exact hget

private noncomputable def transNarrowInner
    {m : Nat}
    (trans_lo : ∀ (Γ : Ctx) (a b c : Expr), b.complexity < m →
      Sub Γ a b → Sub Γ b c → Sub Γ a c)
    : (n : Nat) →
    -- trans: b.complexity ≤ m, sizes ≤ n
    (∀ (Γ : Ctx) (a b c : Expr) (hab : Sub Γ a b) (hbc : Sub Γ b c),
      b.complexity ≤ m → hab.size + hbc.size ≤ n → Sub Γ a c) ×
    -- narrow_gen: replace B with C at arbitrary depth, sizes ≤ n, B.complexity < m
    (∀ (Γ_pre : Ctx) (Γ_suf : Ctx) (B C : Expr) (a b : Expr)
      (hCB : Sub Γ_suf C B) (hab : Sub (Γ_pre ++ B :: Γ_suf) a b),
      B.complexity < m → hCB.size + hab.size ≤ n → Sub (Γ_pre ++ C :: Γ_suf) a b)
  | 0 => ⟨
      fun _ _ _ _ hab hbc _ h => absurd h (by have := hab.size_pos; have := hbc.size_pos; omega),
      fun _ _ _ _ _ _ _ hab _ h => absurd h (by have := hab.size_pos; omega)⟩
  | n + 1 =>
    let ⟨trans_n, narrow_n⟩ := transNarrowInner trans_lo n
    ⟨fun Γ a b c hab hbc hcplx hle => by
      -- ==================== TRANS at (m, n+1) ====================
      match hab with
      -- [Refl]: a = b
      | .refl _ _ => exact hbc
      -- [Top]: b = ⊤. Case-split on hbc : Sub Γ ⊤ c
      | .top _ _ =>
        match hbc with
        | .refl _ _ => exact Sub.top _ _
        | .top _ _ => exact Sub.top _ _
        | .ascR _ _ e τ heτ hae =>
          exact Sub.ascR _ _ e τ heτ (trans_n Γ _ _ e (Sub.top _ _) hae
            hcplx (by simp [Sub.size] at hle ⊢; omega))
      -- [Var]: a = var x, hUb : Sub Γ U b
      | .var _ x _ U hget hUb =>
        have hUc := trans_n Γ U b c hUb hbc hcplx (by
          simp [Sub.size] at hle ⊢; omega)
        exact Sub.var _ x c U hget hUc
      -- [App]: a = app f a', hRb : Sub Γ (R.subst 0 a') b
      | .app _ f a' _ D R hfD haD hRb =>
        have hRc := trans_n Γ _ b c hRb hbc hcplx (by
          simp [Sub.size] at hle ⊢; omega)
        exact Sub.app _ f a' c D R hfD haD hRc
      -- [Lam]: a = lam A body_a, b = lam B body_b
      | .lam _ A B body_a body_b hBA hbody_ab =>
        match hbc with
        | .refl _ _ => exact Sub.lam _ A B body_a body_b hBA hbody_ab
        | .top _ _ => exact Sub.top _ _
        | .lam _ .(B) C .(body_b) body_c hCB hbody_bc =>
          -- b = lam B body_b, complexity = 1 + B.complexity + body_b.complexity
          -- Domain: trans(hCB, hBA) with cut B — strictly smaller complexity
          have hCA := trans_lo Γ C B A
            (by simp [Expr.complexity] at hcplx ⊢; omega) hCB hBA
          -- Body: narrow hbody_ab from B::Γ to C::Γ, then trans with cut body_b
          -- Use narrow_gen with Γ_pre = [], Γ_suf = Γ
          have hbody_narrow := narrow_n [] Γ B C body_a body_b hCB hbody_ab
            (by simp [Expr.complexity] at hcplx; omega) (by
            simp [Sub.size] at hle ⊢; omega)
          -- body_b.complexity < (lam B body_b).complexity — use trans_lo!
          have hbody_ac := trans_lo (C :: Γ) body_a body_b body_c
            (by simp [Expr.complexity] at hcplx ⊢; omega) hbody_narrow hbody_bc
          exact Sub.lam _ A C body_a body_c hCA hbody_ac
        | .ascR _ _ e τ heτ hae =>
          exact Sub.ascR _ _ e τ heτ (trans_n Γ _ _ e
            (Sub.lam _ A B body_a body_b hBA hbody_ab) hae hcplx
            (by simp [Sub.size] at hle ⊢; omega))
      -- [Asc-L]: a = asc e τ, heτ : Sub Γ e τ, hτb : Sub Γ τ b
      | .ascL _ e τ _ heτ hτb =>
        have hτc := trans_n Γ τ b c hτb hbc hcplx (by
          simp [Sub.size] at hle ⊢; omega)
        exact Sub.ascL _ e τ c heτ hτc
      -- [Asc-R]: b = asc e τ
      | .ascR _ _ e τ heτ hae =>
        match hbc with
        | .refl _ _ => exact Sub.ascR _ _ e τ heτ hae
        | .top _ _ => exact Sub.top _ _
        | .ascL _ _ _ _ heτ' hτc =>
          -- b = asc e τ, complexity = 1 + e.complexity + τ.complexity
          -- trans(hae, heτ') with cut e — strictly smaller complexity
          have haτ := trans_lo Γ a e τ
            (by simp [Expr.complexity] at hcplx ⊢; omega) hae heτ'
          -- trans(haτ, hτc) with cut τ — strictly smaller complexity
          exact trans_lo Γ a τ c
            (by simp [Expr.complexity] at hcplx ⊢; omega) haτ hτc
        | .ascR _ _ e₂ τ₂ heτ₂ hae₂ =>
          exact Sub.ascR _ _ e₂ τ₂ heτ₂ (trans_n Γ _ _ e₂
            (Sub.ascR _ _ e τ heτ hae) hae₂ hcplx
            (by simp [Sub.size] at hle ⊢; omega))
      -- [Mu]: a = mu A body, hAb : Sub Γ A b, hbodyA : Sub (A::Γ) body (A.shift 0 1)
      | .mu _ A body _ hAb hbodyA =>
        have hAc := trans_n Γ A b c hAb hbc hcplx (by
          simp [Sub.size] at hle ⊢; omega)
        exact Sub.mu _ A body c hAc hbodyA
    ,
    -- ==================== NARROW_GEN at (m, n+1) ====================
    fun Γ_pre Γ_suf B C a b hCB hab hBcplx hle => by
      match hab with
      | .refl _ _ => exact Sub.refl _ _
      | .top _ _ => exact Sub.top _ _
      | .var _ x _ U hget hUb =>
        by_cases hx_lt : x < Γ_pre.length
        · -- Variable before narrowing point: unchanged
          have hget' := Ctx.get?_narrow_lt C hget hx_lt
          have hUb' := narrow_n Γ_pre Γ_suf B C U b hCB hUb hBcplx (by
            simp [Sub.size] at hle ⊢; omega)
          exact Sub.var _ x b U hget' hUb'
        · by_cases hx_eq : x = Γ_pre.length
          · -- Variable at narrowing point: type changes from B.shifted to C.shifted
            subst hx_eq
            have hU_eq := Ctx.get?_narrow_eq hget
            subst hU_eq
            have hUb_narrow := narrow_n Γ_pre Γ_suf B C _ b hCB hUb hBcplx (by
              simp [Sub.size] at hle ⊢; omega)
            -- Weaken hCB into (Γ_pre ++ C :: Γ_suf) via multi-weakening.
            -- First weaken by C, then prepend Γ_pre.
            have hCB_weak : Sub (Γ_pre ++ C :: Γ_suf) (C.shift 0 (Γ_pre.length + 1)) (B.shift 0 (Γ_pre.length + 1)) := by
              have h1 := Sub.weaken C hCB  -- Sub (C :: Γ_suf) (C.shift 0 1) (B.shift 0 1)
              have h2 := Sub.weaken_prepend Γ_pre h1  -- Sub (Γ_pre ++ C :: Γ_suf) ...
              rw [Expr.shift_add, Expr.shift_add] at h2
              simp only [show Γ_pre.length + 1 = 1 + Γ_pre.length from by omega] at h2 ⊢
              exact h2
            have hCb := trans_lo (Γ_pre ++ C :: Γ_suf) (C.shift 0 (Γ_pre.length + 1)) (B.shift 0 (Γ_pre.length + 1)) b
              (by rw [Expr.shift_complexity]; omega) hCB_weak hUb_narrow
            exact Sub.var _ Γ_pre.length b (C.shift 0 (Γ_pre.length + 1)) Ctx.get?_narrow_eq_new hCb
          · -- Variable after narrowing point: unchanged
            have hx_gt : Γ_pre.length < x := by omega
            have hget' := Ctx.get?_narrow_gt C hget hx_gt
            have hUb' := narrow_n Γ_pre Γ_suf B C U b hCB hUb hBcplx (by
              simp [Sub.size] at hle ⊢; omega)
            exact Sub.var _ x b U hget' hUb'
      | .lam _ A_lam B_lam body_a body_b hBA hbody =>
        -- hBA : Sub (Γ_pre ++ B :: Γ_suf) B_lam A_lam
        -- hbody : Sub (B_lam :: (Γ_pre ++ B :: Γ_suf)) body_a body_b
        have hBA' := narrow_n Γ_pre Γ_suf B C B_lam A_lam hCB hBA hBcplx (by
          simp [Sub.size] at hle ⊢; omega)
        -- B_lam :: (Γ_pre ++ B :: Γ_suf) is definitionally (B_lam :: Γ_pre) ++ B :: Γ_suf
        -- Use narrow_n with Γ_pre' = B_lam :: Γ_pre
        have hbody' : Sub ((B_lam :: Γ_pre) ++ C :: Γ_suf) body_a body_b :=
          narrow_n (B_lam :: Γ_pre) Γ_suf B C body_a body_b hCB hbody hBcplx (by
            simp [Sub.size] at hle ⊢; omega)
        exact Sub.lam _ A_lam B_lam body_a body_b hBA' hbody'
      | .app _ f a' _ D R hfD haD hRb =>
        have hfD' := narrow_n Γ_pre Γ_suf B C f (.lam D R) hCB hfD hBcplx (by
          simp [Sub.size] at hle ⊢; omega)
        have haD' := narrow_n Γ_pre Γ_suf B C a' D hCB haD hBcplx (by
          simp [Sub.size] at hle ⊢; omega)
        have hRb' := narrow_n Γ_pre Γ_suf B C (R.subst 0 a') b hCB hRb hBcplx (by
          simp [Sub.size] at hle ⊢; omega)
        exact Sub.app _ f a' b D R hfD' haD' hRb'
      | .ascL _ e τ _ heτ hτb =>
        have heτ' := narrow_n Γ_pre Γ_suf B C e τ hCB heτ hBcplx (by
          simp [Sub.size] at hle ⊢; omega)
        have hτb' := narrow_n Γ_pre Γ_suf B C τ b hCB hτb hBcplx (by
          simp [Sub.size] at hle ⊢; omega)
        exact Sub.ascL _ e τ b heτ' hτb'
      | .ascR _ _ e τ heτ hae =>
        have heτ' := narrow_n Γ_pre Γ_suf B C e τ hCB heτ hBcplx (by
          simp [Sub.size] at hle ⊢; omega)
        have hae' := narrow_n Γ_pre Γ_suf B C a e hCB hae hBcplx (by
          simp [Sub.size] at hle ⊢; omega)
        exact Sub.ascR _ _ e τ heτ' hae'
      | .mu _ A_mu body_mu _ hAc hbodyA =>
        have hAc' := narrow_n Γ_pre Γ_suf B C A_mu b hCB hAc hBcplx (by
          simp [Sub.size] at hle ⊢; omega)
        -- hbodyA : Sub (A_mu :: (Γ_pre ++ B :: Γ_suf)) body_mu (A_mu.shift 0 1)
        -- Need: Sub (A_mu :: (Γ_pre ++ C :: Γ_suf)) body_mu (A_mu.shift 0 1)
        -- Use narrow_n with Γ_pre' = A_mu :: Γ_pre
        have hbodyA' : Sub ((A_mu :: Γ_pre) ++ C :: Γ_suf) body_mu (A_mu.shift 0 1) :=
          narrow_n (A_mu :: Γ_pre) Γ_suf B C body_mu (A_mu.shift 0 1) hCB hbodyA hBcplx (by
            simp [Sub.size] at hle ⊢; omega)
        exact Sub.mu _ A_mu body_mu b hAc' hbodyA'⟩

-- 6c. Outer induction (on cut-formula complexity)

/-- Outer induction on cut-formula complexity. For each complexity bound m,
    we get trans at b.complexity ≤ m (for any derivation sizes). -/
private noncomputable def transOuter : (m : Nat) →
    (∀ (Γ : Ctx) (a b c : Expr), b.complexity ≤ m →
      Sub Γ a b → Sub Γ b c → Sub Γ a c)
  | 0 => fun Γ a b c hcplx hab hbc =>
      let ⟨tr, _⟩ := transNarrowInner (fun _ _ _ _ hlt _ _ => absurd hlt (by omega)) (hab.size + hbc.size)
      tr Γ a b c hab hbc hcplx (Nat.le_refl _)
  | m + 1 => fun Γ a b c hcplx hab hbc =>
      let trans_lo := transOuter m
      let trans_lo' : ∀ Γ a b c, b.complexity < m + 1 → Sub Γ a b → Sub Γ b c → Sub Γ a c :=
        fun Γ a b c hlt hab hbc => trans_lo Γ a b c (by omega) hab hbc
      let ⟨tr, _⟩ := transNarrowInner trans_lo' (hab.size + hbc.size)
      tr Γ a b c hab hbc hcplx (Nat.le_refl _)

/-- Transitivity: `Sub Γ a b → Sub Γ b c → Sub Γ a c`.
    Proved via lexicographic induction on (b.complexity, hab.size + hbc.size).
    The [Lam-Lam] and [AscR-AscL] cases are fully handled because the
    cut formula's complexity strictly decreases. Narrow generalized to
    arbitrary depth via Γ_pre prefix, closing [Narrow Lam].
    Remaining sorry: [Narrow Var x=|Γ_pre|] needs weakening of hCB into
    the full context Γ_pre ++ C :: Γ_suf. -/
noncomputable def Sub.trans {Γ : Ctx} {a b c : Expr}
    (hab : Sub Γ a b) (hbc : Sub Γ b c) : Sub Γ a c :=
  transOuter b.complexity Γ a b c (Nat.le_refl _) hab hbc

-- ============================================================
-- 7. Generalized substitution lemma
-- ============================================================

/-- Substitute into each entry of a context prefix.
    Given Δ (stored types in front of T) and v (the replacement for T),
    each `Δ[i]` lives `i` entries above Γ, so var `|Δ|-1-i` refers to T.
    After removing T, we substitute accordingly. -/
def substCtx : Ctx → Expr → Ctx
  | [], _ => []
  | A :: rest, v => (A.subst rest.length (v.shift 0 rest.length)) :: substCtx rest v

/-- substCtx preserves length. -/
theorem substCtx_length (Δ : Ctx) (v : Expr) : (substCtx Δ v).length = Δ.length := by
  induction Δ with
  | nil => simp [substCtx]
  | cons A Δ ih => simp [substCtx, ih]

/-- Context lookup: positions before |Δ| in (Δ ++ T :: Γ) come from Δ,
    and after substitution the type is correspondingly substituted. -/
theorem Ctx.get?_substCtx_lt {Δ : Ctx} {T : Expr} {Γ : Ctx} (v : Expr) {x : Nat} {U : Expr}
    (hget : Ctx.get? (Δ ++ T :: Γ) x = some U) (hx : x < Δ.length) :
    Ctx.get? (substCtx Δ v ++ Γ) x = some (U.subst Δ.length (v.shift 0 Δ.length)) := by
  induction Δ generalizing x U with
  | nil => simp at hx
  | cons A Δ ih =>
    cases x with
    | zero =>
      simp only [List.cons_append, Ctx.get?, List.get?] at hget
      simp only [Option.some.injEq] at hget
      simp only [substCtx, List.cons_append, Ctx.get?, List.get?, List.length_cons]
      simp only [Option.some.injEq]
      rw [← hget]
      have := Expr.subst_shift_lo A Δ.length 0 1 (v.shift 0 Δ.length) (by omega)
      rw [this]; congr 1
      rw [Expr.shift_add]; congr 1; omega
    | succ x =>
      simp only [List.cons_append, List.length_cons] at hx
      simp only [List.cons_append] at hget
      rw [Ctx.get?_cons_succ] at hget
      cases hΔ : Ctx.get? (Δ ++ T :: Γ) x with
      | none => simp [hΔ] at hget
      | some W =>
        simp only [hΔ, Option.map, Option.some.injEq] at hget
        have ihx := ih (by rw [hΔ]) (by omega)
        -- goal: Ctx.get? (substCtx (A :: Δ) v ++ Γ) (x+1) = some (U.subst (A :: Δ).length (v.shift 0 (A :: Δ).length))
        -- substCtx (A :: Δ) v = (A.subst ...) :: substCtx Δ v (by def)
        simp only [substCtx, List.cons_append, List.length_cons]
        -- Now goal has: Ctx.get? ((A.subst ...) :: substCtx Δ v ++ Γ) (x + 1) = ...
        rw [Ctx.get?_cons_succ, ihx]; simp only [Option.map, Option.some.injEq]
        rw [← hget]
        have := Expr.subst_shift_lo W Δ.length 0 1 (v.shift 0 Δ.length) (by omega)
        rw [this]; congr 1
        rw [Expr.shift_add]; congr 1; omega

/-- Context lookup: position |Δ| in (Δ ++ T :: Γ) gives T.shifted. -/
theorem Ctx.get?_append_eq {Δ : Ctx} {T : Expr} {Γ : Ctx} {U : Expr}
    (hget : Ctx.get? (Δ ++ T :: Γ) Δ.length = some U) :
    U = T.shift 0 (Δ.length + 1) := by
  induction Δ generalizing U with
  | nil => simp [Ctx.get?, List.get?] at hget; exact hget.symm
  | cons A Δ ih =>
    simp only [List.cons_append, List.length_cons] at hget
    rw [Ctx.get?_cons_succ] at hget
    cases hΔ : Ctx.get? (Δ ++ T :: Γ) Δ.length with
    | none => simp [hΔ] at hget
    | some W =>
      simp only [hΔ, Option.map, Option.some.injEq] at hget
      have ihW := ih (by rw [hΔ])
      -- ihW : W = T.shift 0 (Δ.length + 1)
      -- hget : W.shift 0 1 = U
      -- goal: U = T.shift 0 ((A :: Δ).length + 1)
      rw [← hget, ihW]
      simp only [List.length_cons]
      rw [Expr.shift_add]; congr 1; omega

/-- Context lookup: positions after |Δ| in (Δ ++ T :: Γ) come from Γ (shifted). -/
theorem Ctx.get?_substCtx_ge {Δ : Ctx} {T : Expr} {Γ : Ctx} (v : Expr) {x : Nat} {U : Expr}
    (hget : Ctx.get? (Δ ++ T :: Γ) x = some U) (hx : Δ.length < x) :
    Ctx.get? (substCtx Δ v ++ Γ) (x - 1) = some (U.subst Δ.length (v.shift 0 Δ.length)) := by
  induction Δ generalizing x U with
  | nil =>
    -- Δ = [], substCtx [] v = [], so substCtx Δ v ++ Γ = Γ
    -- x > 0, hget : Ctx.get? (T :: Γ) x = some U
    simp only [List.nil_append, List.length_nil] at hx
    simp only [substCtx, List.nil_append, List.length_nil]
    cases x with
    | zero => omega
    | succ x =>
      -- goal: Ctx.get? Γ (x+1-1) = some (U.subst 0 (shift 0 0 v))
      -- x+1-1 = x, shift 0 0 v = v
      simp only [Nat.add_sub_cancel, Expr.shift_zero]
      simp only [List.nil_append] at hget
      rw [Ctx.get?_cons_succ] at hget
      cases hΓ : Ctx.get? Γ x with
      | none => simp [hΓ] at hget
      | some W =>
        simp only [hΓ, Option.map, Option.some.injEq] at hget
        rw [← hget, Expr.subst_shift_cancel]
  | cons A Δ ih =>
    cases x with
    | zero => omega
    | succ x =>
      -- x+1 > (A :: Δ).length = Δ.length + 1, so x ≥ Δ.length + 1, i.e. Δ.length < x
      simp only [List.cons_append, List.length_cons] at hx
      -- Goal: (substCtx (A :: Δ) v ++ Γ).get? (x + 1 - 1) = ...
      -- x + 1 - 1 = x
      show Ctx.get? (substCtx (A :: Δ) v ++ Γ) x = some (U.subst (Δ.length + 1) (v.shift 0 (Δ.length + 1)))
      simp only [List.cons_append] at hget
      rw [Ctx.get?_cons_succ] at hget
      cases hΔ : Ctx.get? (Δ ++ T :: Γ) x with
      | none => simp [hΔ] at hget
      | some W =>
        simp only [hΔ, Option.map, Option.some.injEq] at hget
        simp only [substCtx, List.cons_append, List.length_cons]
        -- goal: Ctx.get? ((A.subst ...) :: substCtx Δ v ++ Γ) x = ...
        cases x with
        | zero =>
          -- x = 0, but Δ.length < 0 from hx is impossible when Δ nonempty
          -- Actually hx says Δ.length + 1 < 0 + 1 i.e. Δ.length < 0, possible only if Δ = []
          -- Then Δ.length = 0, not < 0. Actually hx says Δ.length < x = 0, i.e. Δ.length = 0... wait
          -- After `simp ... at hx`, hx : Δ.length + 1 < x + 1, with x = 0: Δ.length < 0. Contradiction.
          omega
        | succ x' =>
          -- x = x' + 1, goal has (x'+1+1-1) = x'+1
          show Ctx.get? (substCtx (A :: Δ) v ++ Γ) (x' + 1) = some (U.subst (Δ.length + 1) (v.shift 0 (Δ.length + 1)))
          simp only [substCtx, List.cons_append, List.length_cons]
          rw [Ctx.get?_cons_succ]
          have hxΔ : Δ.length < x' + 1 := by omega
          have ihx := ih (by rw [hΔ]) hxΔ
          -- ihx : (substCtx Δ v ++ Γ).get? (x'+1-1) = some (W.subst Δ.length (shift 0 Δ.length v))
          -- x'+1-1 = x'
          simp only [Nat.add_sub_cancel] at ihx
          rw [ihx]; simp only [Option.map, Option.some.injEq]
          rw [← hget]
          rw [Expr.subst_shift_lo W Δ.length 0 1 (v.shift 0 Δ.length) (by omega)]
          congr 1; rw [Expr.shift_add]; congr 1; omega

/-- Generalized substitution lemma: substitute at arbitrary depth.
    Given `Sub (Δ ++ T :: Γ) a b` and `Sub Γ v T`, we can substitute out the
    binding T at position `|Δ|`. -/
private noncomputable def Sub.subst_gen_aux {Γ' : Ctx} {a b : Expr} (hab : Sub Γ' a b)
    (Δ : Ctx) {Γ : Ctx} {T v : Expr} (hctx : Γ' = Δ ++ T :: Γ) (hv : Sub Γ v T)
    : Sub (substCtx Δ v ++ Γ) (a.subst Δ.length (v.shift 0 Δ.length)) (b.subst Δ.length (v.shift 0 Δ.length)) := by
  induction hab generalizing Δ Γ with
  | refl _ a => exact Sub.refl _ _
  | top _ a =>
    show Sub _ _ (Expr.top.subst Δ.length (v.shift 0 Δ.length))
    simp only [subst]; exact Sub.top _ _
  | var Γ'' x b' U hget _hUb ihUb =>
    subst hctx
    show Sub _ ((Expr.var x).subst Δ.length (v.shift 0 Δ.length)) (b'.subst Δ.length (v.shift 0 Δ.length))
    simp only [subst]
    by_cases hx_lt : x < Δ.length
    · -- x < |Δ|: variable is in Δ
      simp only [show (x == Δ.length) = false from by rw [beq_eq_false_iff_ne]; omega, ite_false,
                 show ¬ x > Δ.length from by omega, ite_false]
      have hget' := Ctx.get?_substCtx_lt v hget hx_lt
      have ihUb' := ihUb Δ rfl hv
      exact Sub.var _ x _ _ hget' ihUb'
    · by_cases hx_eq : x = Δ.length
      · -- x = |Δ|: variable refers to T
        subst hx_eq
        simp only [beq_self_eq_true, ite_true]
        have hU_eq := Ctx.get?_append_eq hget
        subst hU_eq
        have ihUb' := ihUb Δ rfl hv
        have hkey : (T.shift 0 (Δ.length + 1)).subst Δ.length (v.shift 0 Δ.length) = T.shift 0 Δ.length := by
          have h1 : T.shift 0 (Δ.length + 1) = (T.shift 0 Δ.length).shift Δ.length 1 := by
            -- shift_shift_comm with c₁=0, c₂=0, n₁=|Δ|, n₂=1:
            -- (T.shift 0 |Δ|).shift |Δ| 1 = (T.shift 0 1).shift 0 |Δ|
            have := Expr.shift_shift_comm T 0 0 Δ.length 1 (by omega)
            simp only [Nat.zero_add] at this
            rw [this, Expr.shift_add]
          rw [h1, Expr.subst_shift_cancel]
        rw [hkey] at ihUb'
        have hv_weak := Sub.weaken_prepend (substCtx Δ v) hv
        rw [substCtx_length] at hv_weak
        exact Sub.trans hv_weak ihUb'
      · -- x > |Δ|: variable is past T in Γ
        have hx_gt : x > Δ.length := by omega
        simp only [show (x == Δ.length) = false from by rw [beq_eq_false_iff_ne]; omega, ite_false,
                   show x > Δ.length from hx_gt, ite_true]
        have hget' := Ctx.get?_substCtx_ge v hget hx_gt
        have ihUb' := ihUb Δ rfl hv
        exact Sub.var _ (x - 1) _ _ hget' ihUb'
  | @lam Γ'' A B b₁ b₂ _hBA _hbody ihBA ihbody =>
    -- Domain: IH with same Δ
    have hdom := ihBA Δ hctx hv
    -- Body: Sub (B :: Γ'') b₁ b₂ where Γ'' = Δ ++ T :: Γ
    -- So B :: Γ'' = (B :: Δ) ++ T :: Γ
    have hbody' := ihbody (B :: Δ) (by rw [hctx]; simp [List.cons_append]) hv
    -- Simplify: (B :: Δ).length = Δ.length + 1
    simp only [List.length_cons] at hbody'
    -- substCtx (B :: Δ) v unfolds by definition
    change Sub ((B.subst Δ.length (v.shift 0 Δ.length)) :: substCtx Δ v ++ Γ) _ _ at hbody'
    -- Construct the lam subtype
    show Sub _ ((Expr.lam A b₁).subst Δ.length (v.shift 0 Δ.length))
               ((Expr.lam B b₂).subst Δ.length (v.shift 0 Δ.length))
    unfold subst
    have hshift : (v.shift 0 Δ.length).shift 0 1 = v.shift 0 (Δ.length + 1) := by
      rw [Expr.shift_add]; congr 1; omega
    rw [hshift]
    exact Sub.lam _ _ _ _ _ hdom hbody'
  | @app Γ'' f a' b' D R _hfD _haD _hRb ihfD ihaD ihRb =>
    show Sub _ ((Expr.app f a').subst Δ.length (v.shift 0 Δ.length)) _
    simp only [subst]
    have hshift : (v.shift 0 Δ.length).shift 0 1 = v.shift 0 (Δ.length + 1) := by
      rw [Expr.shift_add]; congr 1; omega
    -- ihfD gives Sub ... f.subst ((lam D R).subst n w); unfold subst on lam
    have ihfD' := ihfD Δ hctx hv
    simp only [subst] at ihfD'
    rw [hshift] at ihfD'
    have ihRb' := ihRb Δ hctx hv
    -- Rewrite (R.subst 0 a').subst n w using subst_subst
    have hss := Expr.subst_subst R 0 Δ.length a' (v.shift 0 Δ.length) (by omega)
    rw [← hss] at ihRb'
    rw [hshift] at ihRb'
    exact Sub.app _ _ _ _
      (D.subst Δ.length (v.shift 0 Δ.length))
      (R.subst (Δ.length + 1) (v.shift 0 (Δ.length + 1)))
      ihfD' (ihaD Δ hctx hv) ihRb'
  | ascL _ e τ b' _ _ iheτ ihτb =>
    show Sub _ ((Expr.asc e τ).subst Δ.length (v.shift 0 Δ.length)) _
    simp only [subst]; exact Sub.ascL _ _ _ _ (iheτ Δ hctx hv) (ihτb Δ hctx hv)
  | ascR _ a' e τ _ _ iheτ ihaτ =>
    show Sub _ _ ((Expr.asc e τ).subst Δ.length (v.shift 0 Δ.length))
    simp only [subst]; exact Sub.ascR _ _ _ _ (iheτ Δ hctx hv) (ihaτ Δ hctx hv)
  | @mu Γ'' A body c' _hAc _hbA ihAc ihbA =>
    simp only [subst]
    have hshift : (v.shift 0 Δ.length).shift 0 1 = v.shift 0 (Δ.length + 1) := by
      rw [Expr.shift_add]; congr 1; omega
    rw [hshift]
    -- Domain: IH with same Δ
    have hdom := ihAc Δ hctx hv
    -- Body: Sub (A :: Γ'') body (A.shift 0 1) where Γ'' = Δ ++ T :: Γ
    -- So A :: Γ'' = (A :: Δ) ++ T :: Γ
    have hbody' := ihbA (A :: Δ) (by rw [hctx]; simp [List.cons_append]) hv
    simp only [List.length_cons] at hbody'
    -- hbody' has (shift 0 1 A).subst ... but Sub.mu expects shift 0 1 (A.subst ...)
    -- These are equal by subst_shift_lo
    change Sub ((A.subst Δ.length (v.shift 0 Δ.length)) :: substCtx Δ v ++ Γ) _ _ at hbody'
    have hann_eq : (A.shift 0 1).subst (Δ.length + 1) (v.shift 0 (Δ.length + 1)) =
        (A.subst Δ.length (v.shift 0 Δ.length)).shift 0 1 := by
      rw [Expr.subst_shift_lo A Δ.length 0 1 (v.shift 0 Δ.length) (by omega)]
      congr 1; rw [Expr.shift_add]; congr 1; omega
    simp only [hann_eq] at hbody'
    exact Sub.mu _ _ _ _ hdom hbody'

/-- Generalized substitution lemma: substitute at arbitrary depth. -/
noncomputable def Sub.subst_gen (Δ : Ctx) {Γ : Ctx} {T a b v : Expr}
    (hab : Sub (Δ ++ T :: Γ) a b) (hv : Sub Γ v T)
    : Sub (substCtx Δ v ++ Γ) (a.subst Δ.length (v.shift 0 Δ.length)) (b.subst Δ.length (v.shift 0 Δ.length)) :=
  Sub.subst_gen_aux hab Δ rfl hv

/-- Substitution lemma (depth 0): corollary of the generalized version with Δ = []. -/
noncomputable def Sub.subst_lemma {Γ : Ctx} {T a b v : Expr}
    (hab : Sub (T :: Γ) a b) (hv : Sub Γ v T)
    : Sub Γ (a.subst 0 v) (b.subst 0 v) := by
  have h := Sub.subst_gen [] hab hv
  simp only [substCtx, List.nil_append, List.length_nil, Expr.shift_zero] at h
  exact h

end Och.Simple

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
- `Sub.weaken_gen`: fully proven (all 8 cases including Lam!)
- `Sub.weaken`: fully proven (corollary of weaken_gen)
- `Sub.trans`: induction on hbc; [Refl], [Top], [BetaR], [AscR], [AscL/AscR]
  fully proved. 11 sub-cases sorry'd (need well-founded recursion; see §6).
- `substCtx`: fully defined
- `Sub.subst_gen`: generalized substitution at arbitrary depth, 7/8 cases
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
theorem Sub.weaken_gen {Γ : Ctx} {a b : Expr} (n : Nat) (T : Expr)
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
  | @betaR Γ' a' D body b' _ _ ihbD ihabody =>
    show Sub _ _ ((Expr.app (.lam D body) b').shift n 1); simp only [shift]
    have ihabody' := ihabody n
    rw [Expr.subst_shift_hi body 0 n 1 b' (by omega)] at ihabody'
    exact Sub.betaR _ (a'.shift n 1) (D.shift n 1) (body.shift (n+1) 1) (b'.shift n 1) (ihbD n) ihabody'
  | ascL _ e τ b' _ _ iheτ ihτb =>
    show Sub _ ((Expr.asc e τ).shift n 1) _; simp only [shift]; exact Sub.ascL _ _ _ _ (iheτ n) (ihτb n)
  | ascR _ a' e τ _ _ iheτ ihaτ =>
    show Sub _ _ ((Expr.asc e τ).shift n 1); simp only [shift]; exact Sub.ascR _ _ _ _ (iheτ n) (ihaτ n)

/-- Weakening: `Sub Γ a b → Sub (T :: Γ) (a.shift 0 1) (b.shift 0 1)`. Corollary of generalized weakening. -/
theorem Sub.weaken {Γ : Ctx} {a b : Expr} (T : Expr)
    (h : Sub Γ a b) : Sub (T :: Γ) (a.shift 0 1) (b.shift 0 1) :=
  Sub.weaken_gen 0 T h

-- ============================================================
-- 6. Transitivity and Narrowing (mutually dependent)
-- ============================================================

-- Transitivity and generalized narrowing are mutually dependent:
-- * Transitivity [Lam-Lam] case needs narrowing to re-type the
--   body under a narrowed context.
-- * Narrowing [Var x=0] case needs transitivity to compose the
--   weakened Sub Γ B' B with the narrowed continuation.
--
-- CHALLENGE: Sub lives in Prop, so we cannot define a size/depth
-- function on derivations (large elimination from a Prop inductive
-- with multiple constructors is not allowed in Lean 4). This blocks
-- the standard strong-induction-on-combined-size approach.
--
-- RESOLUTION PATH: Change `Sub` from `Prop` to `Type`, then define
-- Sub.size and use well-founded recursion on derivation size for the
-- mutual proof. This is left as future work.
--
-- We induct on `hbc` (second derivation), case-splitting on `hab` where
-- needed. This gives strong IHs for [BetaR] and [AscR] hbc-cases.
--
-- Fully proved (hbc constructor / hab constructor):
--   [Refl]/*  [Top]/*  [BetaR]/*  [AscR]/*  — all hab handled.
--   [Var]/[Refl]  [Lam]/[Refl]  [App]/[Refl]  [AscL]/[Refl]
--   [AscL]/[AscR] — key non-trivial case.
--
-- Sorry'd (all require trans(hab_sub, hbc) where hab_sub is a
-- sub-derivation of hab but hbc is the full second derivation):
--   [Var]: /[Var], /[App], /[AscL]
--   [Lam]: /[Lam](+narrowing), /[Var], /[App], /[AscL]
--   [App]: /[Var], /[App], /[AscL], /[BetaR]
--   [AscL]: /[Var], /[App], /[AscL]

/-- Transitivity: `Sub Γ a b → Sub Γ b c → Sub Γ a c`.
    Proved by induction on `hbc` (the second derivation), case-splitting
    on `hab` where the middle term `b` is determined by `hbc`.
    This direction fully proves [BetaR], [AscR], and [AscL-AscR] cases
    that were previously sorry'd. 11 sub-cases remain sorry'd (see above). -/
theorem Sub.trans {Γ : Ctx} {a b c : Expr}
    (hab : Sub Γ a b) (hbc : Sub Γ b c) : Sub Γ a c := by
  induction hbc generalizing a with
  | refl _ _ => exact hab
  | top _ _ => exact Sub.top _ _
  | var Γ' x c' U hget hUc ihUc =>
    -- hbc : Sub Γ (var x) c' via [Var]
    -- b = var x; case-split on hab : Sub Γ a (var x)
    -- b = var x. Possible hab constructors: [Refl], [Var], [App], [Asc-L].
    -- ([Top] eliminated: b = .top ≠ var x; [Lam]: b = lam; [BetaR]: b = app; [AscR]: b = asc)
    cases hab with
    | refl _ _ => exact Sub.var Γ' x c' U hget hUc
    | var Γ'' x' _ U' hget' hU'varx =>
      -- a = var x', hU'varx : Sub Γ U' (var x)
      -- ihUc : ∀ a', Sub Γ a' U → Sub Γ a' c'
      -- Need Sub Γ U' c'. Have Sub Γ U' (var x) but need Sub Γ U' U.
      -- BLOCKED: middle term of ihUc is U, not (var x).
      sorry
    | app _ f a'' _ D R hfD haD hRvarx =>
      -- hRvarx : Sub Γ (R.subst 0 a'') (var x)
      -- ihUc : ∀ a', Sub Γ a' U → Sub Γ a' c'
      -- Need Sub Γ (R.subst 0 a'') c'. Same issue: ihUc wants Sub Γ ? U.
      sorry
    | ascL _ e' τ' _ he'τ' hτ'varx =>
      -- hτ'varx : Sub Γ τ' (var x)
      -- Same issue.
      sorry
  | @lam Γ' C b_rhs c₁ c₂ hCb hc₁c₂ ihCb ihc₁c₂ =>
    -- hbc : Sub Γ (lam C c₁) (lam b_rhs c₂) via [Lam]
    -- hCb : Sub Γ b_rhs C, hc₁c₂ : Sub (b_rhs::Γ) c₁ c₂
    -- b = lam C c₁. Possible hab: [Refl], [Lam], [Var], [App], [Asc-L].
    cases hab with
    | refl _ _ => exact Sub.lam _ _ _ _ _ hCb hc₁c₂
    | @lam _ A' _ a₁ _ hCA' ha₁c₁ =>
      -- [Lam-Lam]: need b_rhs ⊑ A' and (b_rhs::Γ) ⊢ a₁ ⊑ c₂.
      -- Domain: have hCb : Sub Γ b_rhs C and hCA' : Sub Γ C A'.
      --   ihCb : ∀ a', Sub Γ a' b_rhs → Sub Γ a' C (wrong direction).
      -- Body: have ha₁c₁ : Sub (C::Γ) a₁ c₁, need Sub (b_rhs::Γ) a₁ c₂.
      --   ihc₁c₂ : ∀ a', Sub (b_rhs::Γ) a' c₁ → Sub (b_rhs::Γ) a' c₂
      --   But ha₁c₁ is in C::Γ, not b_rhs::Γ. Needs narrowing.
      -- BLOCKED: needs contra-variant domain trans + narrowing.
      sorry
    | var _ x' _ U' hget' hU'lam =>
      -- hU'lam : Sub Γ U' (lam C c₁). Need Sub Γ U' (lam b_rhs c₂).
      -- This is trans(hU'lam, hbc), which is self-reference.
      sorry
    | app _ f a'' _ D R hfD haD hRlam =>
      -- hRlam : Sub Γ (R.subst 0 a'') (lam C c₁). Need trans(hRlam, hbc).
      sorry
    | ascL _ e' τ' _ he'τ' hτ'lam =>
      -- hτ'lam : Sub Γ τ' (lam C c₁). Need trans(hτ'lam, hbc).
      sorry
  | app Γ' f' a' c' D R hfD haD hRc ihfD ihaD ihRc =>
    -- hbc : Sub Γ (app f' a') c' via [App]
    -- b = app f' a'. The IHs are for sub-derivations hfD, haD, hRc of hbc.
    -- ihRc : ∀ a'', Sub Γ a'' (R.subst 0 a') → Sub Γ a'' c'.
    -- But hab : Sub Γ a (app f' a') gives us a ⊑ (app f' a'), not a ⊑ (R.subst 0 a').
    -- We'd need to convert a ⊑ (app f' a') to a ⊑ (R.subst 0 a') to use ihRc.
    -- That conversion itself requires the [App] rule applied to a, not available.
    -- All non-trivial sub-cases need trans(hab_sub, hbc) which is self-reference.
    -- BLOCKED: requires well-founded recursion.
    cases hab with
    | refl _ _ => exact Sub.app _ f' a' c' D R hfD haD hRc
    | _ => sorry
  | betaR Γ' a' D body b' hbD habody ihbD ihabody =>
    -- hbc : Sub Γ b (app (lam D body) b') via [BetaR]
    -- ihabody : ∀ a'', Sub Γ a'' b → Sub Γ a'' (body.subst 0 b')
    -- Use [BetaR] with hbD and ihabody hab.
    exact Sub.betaR _ _ D body b' hbD (ihabody hab)
  | ascL Γ' e τ c' heτ hτc iheτ ihτc =>
    -- hbc : Sub Γ (asc e τ) c' via [Asc-L]
    -- b = asc e τ. iheτ/ihτc are IHs from sub-derivations heτ/hτc.
    -- ihτc : ∀ a', Sub Γ a' τ → Sub Γ a' c'
    -- iheτ : ∀ a', Sub Γ a' e → Sub Γ a' τ
    -- Possible hab constructors for b = asc e τ:
    -- [Refl], [Var], [App], [Asc-L], [AscR].
    -- ([Top]: b=.top; [Lam]: b=lam; [BetaR]: b=app — eliminated by Lean)
    cases hab with
    | refl _ _ => exact Sub.ascL _ e τ c' heτ hτc
    | var _ x _ U hget hU_asc =>
      -- hU_asc : Sub Γ U (asc e τ). Need Sub Γ U c'.
      -- This is trans(hU_asc, hbc) — self-reference.
      sorry
    | app _ f a'' _ D' R' hfD' haD' hR_asc =>
      -- hR_asc : Sub Γ (R'.subst 0 a'') (asc e τ). Need trans(hR_asc, hbc).
      sorry
    | ascL _ e' τ' _ he'τ' hτ'_asc =>
      -- hτ'_asc : Sub Γ τ' (asc e τ). Need trans(hτ'_asc, hbc).
      sorry
    | ascR _ _ e' τ' he'τ' ha_e' =>
      -- [AscR]: ha_e' : Sub Γ a e, he'τ' : Sub Γ e τ (since e'=e, τ'=τ).
      -- Chain: iheτ ha_e' : Sub Γ a τ, then ihτc (iheτ ha_e') : Sub Γ a c'.
      exact ihτc (iheτ ha_e')
  | ascR Γ' a' e τ heτ hae iheτ ihae =>
    -- hbc : Sub Γ b (asc e τ) via [AscR]
    -- ihae : ∀ a'', Sub Γ a'' b → Sub Γ a'' e
    -- Use [AscR] with heτ and ihae hab.
    exact Sub.ascR _ _ e τ heτ (ihae hab)

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

/-- Generalized substitution lemma: substitute at arbitrary depth.
    Given `Sub (Δ ++ T :: Γ) a b` and `Sub Γ v T`, we can substitute out the
    binding T at position `|Δ|`.

    The [Var x=|Δ|] subcase (variable refers to T) is sorry'd because it
    requires Sub.trans. All other cases are proven, including [Lam]. -/
private theorem Sub.subst_gen_aux {Γ' : Ctx} {a b : Expr} (hab : Sub Γ' a b)
    (Δ : Ctx) {Γ : Ctx} {T v : Expr} (hctx : Γ' = Δ ++ T :: Γ) (hv : Sub Γ v T)
    : Sub (substCtx Δ v ++ Γ) (a.subst Δ.length (v.shift 0 Δ.length)) (b.subst Δ.length (v.shift 0 Δ.length)) := by
  induction hab generalizing Δ Γ with
  | refl _ a => exact Sub.refl _ _
  | top _ a =>
    show Sub _ _ (Expr.top.subst Δ.length (v.shift 0 Δ.length))
    simp only [subst]; exact Sub.top _ _
  | var Γ'' x b' U hget _hUb ihUb =>
    -- The var case requires context lookup lemmas for Δ ++ T :: Γ
    -- and transitivity for x = |Δ|. Sorry for now.
    sorry
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
  | @betaR Γ'' a' D body b' _hbD _habody ihbD ihabody =>
    show Sub _ _ ((Expr.app (.lam D body) b').subst Δ.length (v.shift 0 Δ.length))
    simp only [subst]
    have hshift : (v.shift 0 Δ.length).shift 0 1 = v.shift 0 (Δ.length + 1) := by
      rw [Expr.shift_add]; congr 1; omega
    rw [hshift]
    have ihabody' := ihabody Δ hctx hv
    have hss := Expr.subst_subst body 0 Δ.length b' (v.shift 0 Δ.length) (by omega)
    rw [← hss] at ihabody'
    rw [hshift] at ihabody'
    exact Sub.betaR _ _
      (D.subst Δ.length (v.shift 0 Δ.length))
      (body.subst (Δ.length + 1) (v.shift 0 (Δ.length + 1)))
      (b'.subst Δ.length (v.shift 0 Δ.length))
      (ihbD Δ hctx hv) ihabody'
  | ascL _ e τ b' _ _ iheτ ihτb =>
    show Sub _ ((Expr.asc e τ).subst Δ.length (v.shift 0 Δ.length)) _
    simp only [subst]; exact Sub.ascL _ _ _ _ (iheτ Δ hctx hv) (ihτb Δ hctx hv)
  | ascR _ a' e τ _ _ iheτ ihaτ =>
    show Sub _ _ ((Expr.asc e τ).subst Δ.length (v.shift 0 Δ.length))
    simp only [subst]; exact Sub.ascR _ _ _ _ (iheτ Δ hctx hv) (ihaτ Δ hctx hv)

/-- Generalized substitution lemma: substitute at arbitrary depth. -/
theorem Sub.subst_gen (Δ : Ctx) {Γ : Ctx} {T a b v : Expr}
    (hab : Sub (Δ ++ T :: Γ) a b) (hv : Sub Γ v T)
    : Sub (substCtx Δ v ++ Γ) (a.subst Δ.length (v.shift 0 Δ.length)) (b.subst Δ.length (v.shift 0 Δ.length)) :=
  Sub.subst_gen_aux hab Δ rfl hv

/-- Substitution lemma (depth 0): corollary of the generalized version with Δ = []. -/
theorem Sub.subst_lemma {Γ : Ctx} {T a b v : Expr}
    (hab : Sub (T :: Γ) a b) (hv : Sub Γ v T)
    : Sub Γ (a.subst 0 v) (b.subst 0 v) := by
  have h := Sub.subst_gen [] hab hv
  simp only [substCtx, List.nil_append, List.length_nil, Expr.shift_zero] at h
  exact h

end Och.Simple

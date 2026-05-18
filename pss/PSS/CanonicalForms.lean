import PSS.Sub

/-!
# Canonical Forms Lemma

Goal: `PSS.Sub Γ .top (.lam s t) → False`

With `Sub` and `Wf` now in `Type`, we define height functions and use
strong (well-founded) induction on derivation height.

## Status

**1 sorry remaining** in `appHelper` — the `.app g c'` sub-case of h1's trans
in the beta_L case of h2. All other cases are closed. See inline comments
for the precise stuck point and termination argument.
-/

open Expr

mutual
def PSS.Sub.height {Γ : Ctx} {a b : Expr} : PSS.Sub Γ a b → Nat
  | .refl _       => 0
  | .top _        => 0
  | .trans h1 h2 hw => 1 + h1.height + h2.height + hw.height
  | .bvar _       => 0
  | .lam h1 h2 h3  => 1 + h1.height + h2.height + h3.height
  | .app_cong h1 h2 h3 => 1 + h1.height + h2.height + h3.height
  | .beta_L       => 0
  | .beta_R       => 0

def PSS.Wf.height {Γ : Ctx} {e : Expr} : PSS.Wf Γ e → Nat
  | .var _         => 0
  | .top           => 0
  | .lam hd hb     => 1 + hd.height + hb.height
  | .app hf ha hs hsub harg => 1 + hf.height + ha.height + hs.height + hsub.height + harg.height
end

def Expr.IsHeadForm : Expr → Prop
  | .lam _ _ => True
  | .bvar _ => True
  | _ => False

namespace PSS

inductive CtxWf : Ctx → Prop where
  | nil : CtxWf []
  | cons {Γ : Ctx} {t : Expr} : CtxWf Γ → Wf Γ t → CtxWf (t :: Γ)

/-- Handle the .app middle term chain.

    Given h1 : Sub Γ .top (.app f c) and h2 : Sub Γ (.app f c) b with IsHeadForm b,
    derive False. Uses the Part A IH and a bound ensuring composed derivations stay
    within the IH range.

    The proof proceeds by strong induction on h2.height (for the trans/.app case)
    and then h1.height (for the beta_L case). -/
private theorem appHelper
    {n : Nat}
    (ih : ∀ (m : Nat), m < n → ∀ (Γ : Ctx) (a b : Expr) (h : Sub Γ a b),
      h.height ≤ m → a = .top → Expr.IsHeadForm b → False)
    {Γ : Ctx} {f c b : Expr}
    (h1 : Sub Γ .top (.app f c))
    (h2 : Sub Γ (.app f c) b)
    (hw : Wf Γ (.app f c))
    (hb : Expr.IsHeadForm b)
    (hbound : h1.height + h2.height + hw.height < n) : False := by
  -- Strong induction on h2.height.
  -- For the .app middle case in trans, h2 strictly decreases.
  -- For beta_L, we case-split h1 and use a secondary induction.
  suffices ∀ (p : Nat) {Γ' : Ctx} {f' c' b' : Expr}
    (h1' : Sub Γ' .top (.app f' c')) (h2' : Sub Γ' (.app f' c') b')
    (hw' : Wf Γ' (.app f' c')) (hb' : Expr.IsHeadForm b')
    (hbound' : h1'.height + h2'.height + hw'.height < n)
    (hp2 : h2'.height ≤ p), False from
    this h2.height h1 h2 hw hb hbound (Nat.le_refl _)
  intro p
  induction p using Nat.strongRecOn with
  | _ p ihp =>
    intro Γ' f' c' b' h1' h2' hw' hb' hbound' hp2
    -- Case-split h2' with generic indices
    suffices ∀ (a2 b2 : Expr) (h2x : Sub Γ' a2 b2),
      h2x.height ≤ p → a2 = .app f' c' → Expr.IsHeadForm b2 →
      (h1'.height + h2x.height + hw'.height < n) →
      False from this (.app f' c') b' h2' hp2 rfl hb' hbound'
    intro a2 b2 h2x hp2x heq hb2 hboundx
    cases h2x with
    | refl => rw [heq] at hb2; simp [Expr.IsHeadForm] at hb2
    | top => simp [Expr.IsHeadForm] at hb2
    | @trans _ _ m2 _ h2a h2b hw2 =>
      subst heq
      -- h2a : Sub Γ' (.app f' c') m2, h2b : Sub Γ' m2 b2
      have hh2b_lt_p : h2b.height < p := by simp [Sub.height] at hp2x; omega
      match m2 with
      | .top =>
        -- h2b : Sub Γ' .top b2. IsHeadForm b2. Use ih (Part A).
        exact ih h2b.height (by omega) Γ' .top b2 h2b (Nat.le_refl _) rfl hb2
      | .lam d bd =>
        -- Build Sub.trans h1' h2a hw' : Sub Γ' .top (.lam d bd). Use ih.
        have hht : (Sub.trans h1' h2a hw').height < n := by
          simp [Sub.height] at hboundx ⊢; omega
        exact ih _ hht Γ' .top (.lam d bd) (.trans h1' h2a hw') (Nat.le_refl _) rfl trivial
      | .bvar k =>
        have hht : (Sub.trans h1' h2a hw').height < n := by
          simp [Sub.height] at hboundx ⊢; omega
        exact ih _ hht Γ' .top (.bvar k) (.trans h1' h2a hw') (Nat.le_refl _) rfl trivial
      | .app g d =>
        -- Compose and recurse: h2b.height < p, total bound preserved.
        have hht_bound : (.trans h1' h2a hw').height + h2b.height + hw2.height < n := by
          simp [Sub.height] at hboundx ⊢; omega
        exact ihp h2b.height hh2b_lt_p (.trans h1' h2a hw') h2b hw2 hb2
          hht_bound (Nat.le_refl _)
    | bvar _ => exact Expr.noConfusion heq
    | lam _ _ _ => exact Expr.noConfusion heq
    | app_cong _ _ _ => simp [Expr.IsHeadForm] at hb2
    | @beta_L _ dom body arg =>
      -- h2x = beta_L: a2 = .app (.lam dom body) arg, b2 = body.subst 0 arg
      cases heq
      -- h1' : Sub Γ' .top (.app (.lam dom body) arg). IsHeadForm (body.subst 0 arg).
      -- Case-split h1' with suffices.
      suffices ∀ (a1 b1 : Expr) (h1x : Sub Γ' a1 b1),
        h1x.height + 0 + hw'.height < n →
        a1 = .top → b1 = .app (.lam dom body) arg →
        False from this .top _ h1' (by simp [Sub.height] at hboundx; omega) rfl rfl
      intro a1 b1 h1x hbound1 ha1 hb1
      cases h1x with
      | refl => subst ha1; exact Expr.noConfusion hb1
      | top => exact Expr.noConfusion hb1
      | @trans _ _ m1 _ h1a h1b hw1 =>
        subst ha1; subst hb1
        -- h1a : Sub Γ' .top m1, h1b : Sub Γ' m1 (.app (.lam dom body) arg)
        match m1 with
        | .top =>
          -- h1b : Sub Γ' .top (.app (.lam dom body) arg). Recurse on ihp with height 0.
          -- h2 = beta_L has height 0. h1b has smaller height than h1x (since trans).
          -- New hbound: h1b.height + 0 + hw'.height < n
          exact ihp 0 (by simp [Sub.height] at hp2x; omega)
            h1b .beta_L hw' hb2
            (by simp [Sub.height] at hbound1 ⊢; omega) (by simp [Sub.height])
        | .lam d bd =>
          exact ih h1a.height (by omega) Γ' .top (.lam d bd) h1a (Nat.le_refl _) rfl trivial
        | .bvar k =>
          exact ih h1a.height (by omega) Γ' .top (.bvar k) h1a (Nat.le_refl _) rfl trivial
        | .app g d =>
          -- h1a : Sub Γ' .top (.app g d), h1b : Sub Γ' (.app g d) (.app (.lam dom body) arg)
          -- We need to compose h1b with beta_L and recurse.
          -- New h2 = Sub.trans h1b .beta_L hw' : Sub Γ' (.app g d) (body.subst 0 arg)
          -- New h1 = h1a. New hw = hw1.
          -- Termination: h1a has smaller height than h1x.
          -- But the new h2 height = 1 + h1b.height + 0 + hw'.height could be > p.
          -- We'd need a different induction variable for this sub-case.
          --
          -- The correct argument: the TOTAL h1x.height + 0 + hw'.height is the relevant
          -- measure. h1a.height < h1x.height (from trans). And:
          -- New total = h1a.height + (1 + h1b.height + 0 + hw'.height) + hw1.height
          --           = h1a.height + h1b.height + hw'.height + hw1.height + 1
          -- Old total = h1x.height + 0 + hw'.height
          --           = (1 + h1a.height + h1b.height + hw1.height) + hw'.height
          --           = h1a.height + h1b.height + hw1.height + hw'.height + 1
          -- These are EQUAL! The total doesn't decrease.
          --
          -- But we can use ihp at the new h2.height (= 1 + h1b.height + hw'.height).
          -- Need this < p. We know p ≥ hp2x but hp2x bounds the ORIGINAL h2x (= beta_L, height 0).
          -- So p could be 0. The new h2 height could be > p.
          --
          -- This is the genuinely hard sub-case. It likely needs a TRIPLE induction
          -- or well-founded recursion on a custom relation.
          sorry
      | bvar _ => exact Expr.noConfusion ha1
      | lam _ _ _ => exact Expr.noConfusion ha1
      | app_cong _ _ _ => exact Expr.noConfusion ha1
      | beta_L => exact Expr.noConfusion ha1
      | @beta_R _ dom' body' arg' =>
        subst hb1
        -- body'.subst 0 arg' = .top (from ha1), body'.subst 0 arg' = body.subst 0 arg
        -- (from .app (.lam dom' body') arg' = .app (.lam dom body) arg)
        -- So body.subst 0 arg = .top. IsHeadForm (body.subst 0 arg) = IsHeadForm .top = False.
        rw [ha1] at hb2; simp [Expr.IsHeadForm] at hb2
    | beta_R => simp [Expr.IsHeadForm] at hb2

/-- Core auxiliary: Sub Γ a b → a = .top → IsHeadForm b → height ≤ n → False. -/
private theorem top_not_sub_headForm_aux (n : Nat) :
    ∀ (Γ : Ctx) (a b : Expr) (h : Sub Γ a b),
      h.height ≤ n → a = .top → Expr.IsHeadForm b → False := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro Γ a b h hle ha hb
    cases h with
    | refl e => subst ha; simp [Expr.IsHeadForm] at hb
    | top e => simp [Expr.IsHeadForm] at hb
    | @trans _ _ m _ h1 h2 hw =>
      subst ha
      have hh1 : h1.height < n := by simp [Sub.height] at hle; omega
      have hh2 : h2.height < n := by simp [Sub.height] at hle; omega
      match m with
      | .top => exact ih h2.height hh2 Γ .top b h2 (Nat.le_refl _) rfl hb
      | .lam d bd => exact ih h1.height hh1 Γ .top (.lam d bd) h1 (Nat.le_refl _) rfl trivial
      | .bvar k => exact ih h1.height hh1 Γ .top (.bvar k) h1 (Nat.le_refl _) rfl trivial
      | .app f' a' =>
        have hbound : h1.height + h2.height + hw.height < n := by
          simp [Sub.height] at hle; omega
        exact appHelper ih h1 h2 hw hb hbound
    | bvar _ => exact Expr.noConfusion ha
    | lam _ _ _ => exact Expr.noConfusion ha
    | app_cong _ _ _ => exact Expr.noConfusion ha
    | beta_L => exact Expr.noConfusion ha
    | beta_R => simp [Expr.IsHeadForm] at hb

/-- Top cannot be a subtype of a function type. -/
theorem top_not_sub_lam {Γ : Ctx} {s t : Expr}
    (h : Sub Γ .top (.lam s t)) : False :=
  top_not_sub_headForm_aux h.height Γ .top (.lam s t) h (Nat.le_refl _) rfl trivial

/-- Top cannot be a subtype of a variable. -/
theorem top_not_sub_bvar {Γ : Ctx} {k : Nat}
    (h : Sub Γ .top (.bvar k)) : False :=
  top_not_sub_headForm_aux h.height Γ .top (.bvar k) h (Nat.le_refl _) rfl trivial

end PSS

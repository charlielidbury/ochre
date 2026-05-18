import PSS.Sub

/-!
# Canonical Forms Lemma

Goal: `PSS.Sub Γ .top (.lam s t) → False`

With `Sub` and `Wf` in `Type`, we define height functions and use
strong (well-founded) induction on derivation height.

The key difficulty is the interaction between the `trans` rule (with its
`+1` height overhead) and the `beta_L` rule in the "app helper".  Using
a **strict** `<` bound throughout gives exactly the slack needed to
compose `h1` with `beta_L` via `trans` and feed the result back to the
outer inductive hypothesis.
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

/-- Handle the .app middle term in a transitivity chain.

Given `h1 : Sub Γ .top (.app f c)` and `h2 : Sub Γ (.app f c) b` with
`IsHeadForm b`, derive `False`.

Uses strong induction on `h2.height`.  The key `beta_L` case composes
`h1` with `beta_L` via `trans` and appeals to the outer Part-1 IH;
the strict-`<` bound ensures the composed derivation's height stays
below `n`. -/
private theorem appHelper
    {n : Nat}
    (ih : ∀ (m : Nat), m < n → ∀ (Γ : Ctx) (a b : Expr) (h : Sub Γ a b),
      h.height ≤ m → a = .top → Expr.IsHeadForm b → False)
    {Γ : Ctx} {f c b : Expr}
    (h1 : Sub Γ .top (.app f c))
    (h2 : Sub Γ (.app f c) b)
    (hw : Wf Γ (.app f c))
    (hb : Expr.IsHeadForm b)
    (hbound : 1 + h1.height + h2.height + hw.height < n) : False := by
  -- Strong induction on h2.height.
  suffices ∀ (p : Nat) {Γ' : Ctx} {f' c' b' : Expr}
    (h1' : Sub Γ' .top (.app f' c')) (h2' : Sub Γ' (.app f' c') b')
    (hw' : Wf Γ' (.app f' c')) (hb' : Expr.IsHeadForm b')
    (hbound' : 1 + h1'.height + h2'.height + hw'.height < n)
    (hp2 : h2'.height ≤ p), False from
    this h2.height h1 h2 hw hb hbound (Nat.le_refl _)
  intro p
  induction p using Nat.strongRecOn with
  | _ p ihp =>
    intro Γ' f' c' b' h1' h2' hw' hb' hbound' hp2
    -- Case-split h2' with generic indices
    suffices ∀ (a2 b2 : Expr) (h2x : Sub Γ' a2 b2),
      h2x.height ≤ p → a2 = .app f' c' → Expr.IsHeadForm b2 →
      (1 + h1'.height + h2x.height + hw'.height < n) →
      False from this (.app f' c') b' h2' hp2 rfl hb' hbound'
    intro a2 b2 h2x hp2x heq hb2 hboundx
    cases h2x with
    | refl => rw [heq] at hb2; simp [Expr.IsHeadForm] at hb2
    | top => simp [Expr.IsHeadForm] at hb2
    | @trans _ _ m2 _ h2a h2b hw2 =>
      subst heq
      have hh2b_lt_p : h2b.height < p := by simp [Sub.height] at hp2x; omega
      match m2 with
      | .top =>
        exact ih h2b.height (by omega) Γ' .top b2 h2b (Nat.le_refl _) rfl hb2
      | .lam d bd =>
        exact ih _ (by simp [Sub.height] at hboundx; omega) Γ' .top (.lam d bd)
          (.trans h1' h2a hw') (by simp [Sub.height]; omega) rfl trivial
      | .bvar k =>
        exact ih _ (by simp [Sub.height] at hboundx; omega) Γ' .top (.bvar k)
          (.trans h1' h2a hw') (by simp [Sub.height]; omega) rfl trivial
      | .app g d =>
        have hbound_new : 1 + (Sub.trans h1' h2a hw').height + h2b.height + hw2.height < n := by
          simp [Sub.height] at hboundx ⊢; omega
        exact ihp h2b.height hh2b_lt_p (.trans h1' h2a hw') h2b hw2 hb2
          hbound_new (Nat.le_refl _)
    | bvar _ => exact Expr.noConfusion heq
    | lam _ _ _ => exact Expr.noConfusion heq
    | app_cong _ _ _ => simp [Expr.IsHeadForm] at hb2
    | @beta_L _ dom body arg =>
      -- h2x = beta_L: a2 = .app (.lam dom body) arg, b2 = body.subst 0 arg
      cases heq
      -- Compose: Sub.trans h1' .beta_L hw' : Sub Γ' .top (body.subst 0 arg)
      -- Height = 1 + h1'.height + 0 + hw'.height
      -- Bound: 1 + h1'.height + 0 + hw'.height < n  (from hboundx with beta_L height 0)
      have h_composed : Sub Γ' .top (body.subst 0 arg) := .trans h1' .beta_L hw'
      have h_composed_height : h_composed.height = 1 + h1'.height + 0 + hw'.height := by
        simp [Sub.height]
      have h_lt : h_composed.height < n := by
        simp [Sub.height] at hboundx; simp [Sub.height]; omega
      exact ih h_composed.height h_lt Γ' .top (body.subst 0 arg)
        h_composed (Nat.le_refl _) rfl hb2
    | beta_R => simp [Expr.IsHeadForm] at hb2

/-- Core auxiliary: Sub Γ a b → a = .top → IsHeadForm b → h.height < n → False. -/
private theorem top_not_sub_headForm_aux (n : Nat) :
    ∀ (Γ : Ctx) (a b : Expr) (h : Sub Γ a b),
      h.height < n → a = .top → Expr.IsHeadForm b → False := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro Γ a b h hlt ha hb
    -- ih : ∀ m < n, ∀ Γ a b h, h.height < m → a = .top → IsHeadForm b → False
    -- Reformulate ih to use ≤ for convenience
    have ih' : ∀ (m : Nat), m < n → ∀ (Γ : Ctx) (a b : Expr) (h : Sub Γ a b),
        h.height ≤ m → a = .top → Expr.IsHeadForm b → False := by
      intro m hm Γ' a' b' h' hle' ha' hb'
      exact ih (m + 1) (by omega) Γ' a' b' h' (by omega) ha' hb'
    cases h with
    | refl e => subst ha; simp [Expr.IsHeadForm] at hb
    | top e => simp [Expr.IsHeadForm] at hb
    | @trans _ _ m _ h1 h2 hw =>
      subst ha
      match m with
      | .top =>
        exact ih h2.height (by simp [Sub.height] at hlt; omega) Γ .top b h2
          (by simp [Sub.height] at hlt; omega) rfl hb
      | .lam d bd =>
        exact ih h1.height (by simp [Sub.height] at hlt; omega) Γ .top (.lam d bd) h1
          (by simp [Sub.height] at hlt; omega) rfl trivial
      | .bvar k =>
        exact ih h1.height (by simp [Sub.height] at hlt; omega) Γ .top (.bvar k) h1
          (by simp [Sub.height] at hlt; omega) rfl trivial
      | .app f' a' =>
        -- h1 : Sub Γ .top (.app f' a'), h2 : Sub Γ (.app f' a') b
        -- h.height = 1 + h1.height + h2.height + hw.height < n
        -- appHelper needs: 1 + h1.height + h2.height + hw.height < n
        -- This is exactly h.height < n!
        exact appHelper ih' h1 h2 hw hb (by simp [Sub.height] at hlt; omega)
    | bvar _ => exact Expr.noConfusion ha
    | lam _ _ _ => exact Expr.noConfusion ha
    | app_cong _ _ _ => exact Expr.noConfusion ha
    | beta_L => exact Expr.noConfusion ha
    | beta_R => simp [Expr.IsHeadForm] at hb

/-- Top cannot be a subtype of a function type. -/
theorem top_not_sub_lam {Γ : Ctx} {s t : Expr}
    (h : Sub Γ .top (.lam s t)) : False :=
  top_not_sub_headForm_aux (h.height + 1) Γ .top (.lam s t) h (Nat.lt.base _) rfl trivial

/-- Top cannot be a subtype of a variable. -/
theorem top_not_sub_bvar {Γ : Ctx} {k : Nat}
    (h : Sub Γ .top (.bvar k)) : False :=
  top_not_sub_headForm_aux (h.height + 1) Γ .top (.bvar k) h (Nat.lt.base _) rfl trivial

/-- A lambda cannot be a subtype of a bound variable. -/
theorem lam_not_sub_bvar {Γ : Ctx} {dom body : Expr} {k : Nat}
    (h : Sub Γ (.lam dom body) (.bvar k)) : False :=
  sorry

/-- **Inversion lemma (Lemma 5.2)**: if `(λa.b) ≤ (λs.t)` then `a ≡ s`.

    The `.lam` and `.top` middle-term cases are closed; the `.app` case
    is the open problem (trans through a β-expansion, same obstacle as
    the paper's Conjecture 5.1 on transitivity elimination). -/
theorem lam_sub_lam_inversion {Γ : Ctx} {a b s t : Expr}
    (h : Sub Γ (.lam a b) (.lam s t)) : Sub Γ a s × Sub Γ s a :=
  sorry

end PSS

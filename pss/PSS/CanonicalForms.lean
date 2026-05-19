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

/-- Handle the .app middle term for lam_not_sub_bvar.

Given `h1 : Sub Γ (.lam a b) (.app f c)` and `h2 : Sub Γ (.app f c) (.bvar k)`,
derive `False` using strong induction on h2's height. -/
private theorem lamBvarAppHelper
    {n : Nat}
    (ih : ∀ (m : Nat), m < n → ∀ (Γ : Ctx) (dom body : Expr) (k : Nat)
      (h : Sub Γ (.lam dom body) (.bvar k)),
      h.height ≤ m → False)
    {Γ : Ctx} {dom body : Expr} {f c : Expr} {k : Nat}
    (h1 : Sub Γ (.lam dom body) (.app f c))
    (h2 : Sub Γ (.app f c) (.bvar k))
    (hw : Wf Γ (.app f c))
    (hbound : 1 + h1.height + h2.height + hw.height < n) : False := by
  -- Strong induction on h2.height
  suffices ∀ (p : Nat) {Γ' : Ctx} {dom' body' : Expr} {f' c' : Expr} {k' : Nat}
    (h1' : Sub Γ' (.lam dom' body') (.app f' c'))
    (h2' : Sub Γ' (.app f' c') (.bvar k'))
    (hw' : Wf Γ' (.app f' c'))
    (hbound' : 1 + h1'.height + h2'.height + hw'.height < n)
    (hp2 : h2'.height ≤ p), False from
    this h2.height h1 h2 hw hbound (Nat.le_refl _)
  intro p
  induction p using Nat.strongRecOn with
  | _ p ihp =>
    intro Γ' dom' body' f' c' k' h1' h2' hw' hbound' hp2
    -- Case-split h2' with generic indices
    suffices ∀ (a2 b2 : Expr) (h2x : Sub Γ' a2 b2),
      h2x.height ≤ p → a2 = .app f' c' → b2 = .bvar k' →
      (1 + h1'.height + h2x.height + hw'.height < n) →
      False from this (.app f' c') (.bvar k') h2' hp2 rfl rfl hbound'
    intro a2 b2 h2x hp2x heq_a heq_b hboundx
    cases h2x with
    | refl => rw [heq_a] at heq_b; exact Expr.noConfusion heq_b
    | top => exact Expr.noConfusion heq_b
    | @trans _ _ m2 _ h2a h2b hw2 =>
      subst heq_a; subst heq_b
      have hh2b_lt_p : h2b.height < p := by simp [Sub.height] at hp2x; omega
      match m2 with
      | .top =>
        exact top_not_sub_bvar h2b
      | .lam d bd =>
        -- h2a : Sub Γ' (.app f' c') (.lam d bd)
        -- compose with h1' via trans to get Sub Γ' (.lam dom' body') (.lam d bd)
        -- then h2b : Sub Γ' (.lam d bd) (.bvar k')
        -- Use outer ih on h2b
        exact ih _ (by simp [Sub.height] at hboundx; omega) Γ' d bd k'
          h2b (by omega)
      | .bvar j =>
        -- h2b : Sub Γ' (.bvar j) (.bvar k'), smaller height
        -- h2a : Sub Γ' (.app f' c') (.bvar j)
        -- compose h1' with h2a to get Sub Γ' (.lam dom' body') (.bvar j)
        -- use outer ih
        exact ih _ (by simp [Sub.height] at hboundx; omega) Γ' dom' body' j
          (.trans h1' h2a hw') (by simp [Sub.height]; omega)
      | .app g d =>
        -- h2a : Sub Γ' (.app f' c') (.app g d)
        -- h2b : Sub Γ' (.app g d) (.bvar k')
        -- compose h1' with h2a: Sub Γ' (.lam dom' body') (.app g d) via trans
        exact ihp h2b.height hh2b_lt_p
          (.trans h1' h2a hw') h2b hw2
          (by simp [Sub.height] at hboundx ⊢; omega) (Nat.le_refl _)
    | bvar _ => exact Expr.noConfusion heq_a
    | lam _ _ _ => exact Expr.noConfusion heq_a
    | app_cong _ _ _ => exact Expr.noConfusion heq_b
    | @beta_L _ bdom bbody barg =>
      -- h2x = beta_L: a2 = .app (.lam bdom bbody) barg, b2 = bbody.subst 0 barg
      -- b2 = .bvar k' means bbody.subst 0 barg = .bvar k'
      cases heq_a
      -- compose: Sub.trans h1' .beta_L hw' : Sub Γ' (.lam dom' body') (bbody.subst 0 barg)
      -- But bbody.subst 0 barg = .bvar k', so this is Sub Γ' (.lam dom' body') (.bvar k')
      have h_composed : Sub Γ' (.lam dom' body') (bbody.subst 0 barg) := .trans h1' .beta_L hw'
      rw [heq_b] at h_composed
      exact ih h_composed.height (by simp [Sub.height] at hboundx; simp [Sub.height]; omega)
        Γ' dom' body' k' h_composed (Nat.le_refl _)
    | beta_R => exact Expr.noConfusion heq_b

/-- Core auxiliary: Sub Γ (.lam dom body) (.bvar k) → h.height < n → False. -/
private theorem lam_not_sub_bvar_aux (n : Nat) :
    ∀ (Γ : Ctx) (dom body : Expr) (k : Nat) (h : Sub Γ (.lam dom body) (.bvar k)),
      h.height < n → False := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro Γ dom body k h hlt
    have ih' : ∀ (m : Nat), m < n → ∀ (Γ : Ctx) (dom body : Expr) (k : Nat)
        (h : Sub Γ (.lam dom body) (.bvar k)),
        h.height ≤ m → False := by
      intro m hm Γ' dom' body' k' h' hle'
      exact ih (m + 1) (by omega) Γ' dom' body' k' h' (by omega)
    -- Case-split on h
    -- Only trans is possible for (.lam dom body) on LHS and (.bvar k) on RHS
    cases h with
    | refl => exact Expr.noConfusion rfl
    | top => exact Expr.noConfusion rfl
    | @trans _ _ m _ h1 h2 hw =>
      match m with
      | .top =>
        exact top_not_sub_bvar h2
      | .lam d bd =>
        -- h2 : Sub Γ (.lam d bd) (.bvar k), smaller height
        exact ih h2.height (by simp [Sub.height] at hlt; omega) Γ d bd k h2
          (by simp [Sub.height] at hlt; omega)
      | .bvar j =>
        -- h1 : Sub Γ (.lam dom body) (.bvar j), smaller height
        exact ih h1.height (by simp [Sub.height] at hlt; omega) Γ dom body j h1
          (by simp [Sub.height] at hlt; omega)
      | .app f a =>
        exact lamBvarAppHelper ih' h1 h2 hw (by simp [Sub.height] at hlt; omega)
    | bvar _ => exact Expr.noConfusion rfl
    | lam _ _ _ => exact Expr.noConfusion rfl
    | app_cong _ _ _ => exact Expr.noConfusion rfl
    | beta_L => exact Expr.noConfusion rfl
    | beta_R => exact Expr.noConfusion rfl

/-- A lambda cannot be a subtype of a bound variable. -/
theorem lam_not_sub_bvar {Γ : Ctx} {dom body : Expr} {k : Nat}
    (h : Sub Γ (.lam dom body) (.bvar k)) : False :=
  lam_not_sub_bvar_aux (h.height + 1) Γ dom body k h (Nat.lt.base _)

/-- Handle the .app middle term for lam_sub_lam_inversion.

Given `h1 : Sub Γ (.lam a b) (.app f c)` and `h2 : Sub Γ (.app f c) (.lam s t)`,
extract `Sub Γ a s × Sub Γ s a` by doing strong induction on h2's height.

In the beta_L base case, composing h1 with beta_L yields a lam-to-lam derivation
whose height is bounded by the original trans. In the trans/app recursive case,
the inner h2b has strictly smaller height. -/
private theorem lamInvAppHelper
    {n : Nat}
    (outer_ih : ∀ (m : Nat), m < n → ∀ (Γ : Ctx) (a b s t : Expr)
      (h : Sub Γ (.lam a b) (.lam s t)),
      h.height ≤ m → Sub Γ a s × Sub Γ s a)
    {Γ : Ctx} {a b : Expr} {f c : Expr} {s t : Expr}
    (h1 : Sub Γ (.lam a b) (.app f c))
    (h2 : Sub Γ (.app f c) (.lam s t))
    (hw : Wf Γ (.app f c))
    (hbound : 1 + h1.height + h2.height + hw.height < n)
    : Sub Γ a s × Sub Γ s a := by
  -- Strong induction on h2.height
  suffices ∀ (p : Nat) {Γ' : Ctx} {a' b' : Expr} {f' c' : Expr} {s' t' : Expr}
    (h1' : Sub Γ' (.lam a' b') (.app f' c'))
    (h2' : Sub Γ' (.app f' c') (.lam s' t'))
    (hw' : Wf Γ' (.app f' c'))
    (hbound' : 1 + h1'.height + h2'.height + hw'.height < n)
    (hp2 : h2'.height ≤ p), Sub Γ' a' s' × Sub Γ' s' a' from
    this h2.height h1 h2 hw hbound (Nat.le_refl _)
  intro p
  induction p using Nat.strongRecOn with
  | _ p ihp =>
    intro Γ' a' b' f' c' s' t' h1' h2' hw' hbound' hp2
    -- Case-split h2' with generic indices
    suffices ∀ (lhs rhs : Expr) (h2x : Sub Γ' lhs rhs),
      h2x.height ≤ p → lhs = .app f' c' → rhs = .lam s' t' →
      (1 + h1'.height + h2x.height + hw'.height < n) →
      Sub Γ' a' s' × Sub Γ' s' a' from
      this (.app f' c') (.lam s' t') h2' hp2 rfl rfl hbound'
    intro lhs rhs h2x hp2x heq_lhs heq_rhs hboundx
    cases h2x with
    | refl => rw [heq_lhs] at heq_rhs; exact absurd heq_rhs (Expr.noConfusion)
    | top => exact absurd heq_rhs (Expr.noConfusion)
    | @trans _ _ m2 _ h2a h2b hw2 =>
      subst heq_lhs; subst heq_rhs
      have hh2b_lt_p : h2b.height < p := by simp [Sub.height] at hp2x; omega
      match m2 with
      | .top =>
        exact absurd (top_not_sub_lam h2b) False.elim
      | .bvar j =>
        -- h2a : Sub Γ' (.app f' c') (.bvar j)
        -- compose h1' with h2a: Sub Γ' (.lam a' b') (.bvar j)
        exact absurd (lam_not_sub_bvar (.trans h1' h2a hw')) False.elim
      | .lam d e =>
        -- h2a : Sub Γ' (.app f' c') (.lam d e)
        -- h2b : Sub Γ' (.lam d e) (.lam s' t')
        -- hw2 : Wf Γ' (.lam d e)
        -- compose h1' with h2a via trans: Sub Γ' (.lam a' b') (.lam d e)
        have h_ae : Sub Γ' (.lam a' b') (.lam d e) := .trans h1' h2a hw'
        -- Extract Wf Γ' d from hw2
        have hwd : Wf Γ' d := match hw2 with | .lam hd _ => hd
        -- Use outer IH on h_ae
        have inv1 := outer_ih h_ae.height
          (by simp [Sub.height] at hboundx ⊢; omega)
          Γ' a' b' d e h_ae (Nat.le_refl _)
        -- Use outer IH on h2b
        have inv2 := outer_ih h2b.height
          (by simp [Sub.height] at hboundx; omega)
          Γ' d e s' t' h2b (Nat.le_refl _)
        -- Compose: a' ≡ d ≡ s'
        exact ⟨.trans inv1.1 inv2.1 hwd, .trans inv2.2 inv1.2 hwd⟩
      | .app g d =>
        -- h2a : Sub Γ' (.app f' c') (.app g d)
        -- h2b : Sub Γ' (.app g d) (.lam s' t')
        -- hw2 : Wf Γ' (.app g d)
        -- compose h1' with h2a: Sub Γ' (.lam a' b') (.app g d) via trans
        exact ihp h2b.height hh2b_lt_p
          (.trans h1' h2a hw') h2b hw2
          (by simp [Sub.height] at hboundx ⊢; omega) (Nat.le_refl _)
    | bvar _ => exact absurd heq_lhs (Expr.noConfusion)
    | lam _ _ _ => exact absurd heq_lhs (Expr.noConfusion)
    | app_cong _ _ _ => exact absurd heq_rhs (Expr.noConfusion)
    | @beta_L _ bdom bbody barg =>
      -- h2x = beta_L: lhs = .app (.lam bdom bbody) barg, rhs = bbody.subst 0 barg
      -- rhs = .lam s' t' means bbody.subst 0 barg = .lam s' t'
      cases heq_lhs
      -- Compose h1' with beta_L via trans: Sub Γ' (.lam a' b') (bbody.subst 0 barg)
      -- And bbody.subst 0 barg = .lam s' t'
      have h_composed : Sub Γ' (.lam a' b') (bbody.subst 0 barg) := .trans h1' .beta_L hw'
      rw [heq_rhs] at h_composed
      exact outer_ih h_composed.height
        (by simp [Sub.height] at hboundx; simp [Sub.height]; omega)
        Γ' a' b' s' t' h_composed (Nat.le_refl _)
    | beta_R => exact absurd heq_rhs (Expr.noConfusion)

/-- Core auxiliary for lam-to-lam inversion: height-bounded strong induction. -/
private theorem lam_sub_lam_inversion_aux (n : Nat) :
    ∀ (Γ : Ctx) (a b s t : Expr) (h : Sub Γ (.lam a b) (.lam s t)),
      h.height < n → Sub Γ a s × Sub Γ s a := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro Γ a b s t h hlt
    have ih' : ∀ (m : Nat), m < n → ∀ (Γ : Ctx) (a b s t : Expr)
        (h : Sub Γ (.lam a b) (.lam s t)),
        h.height ≤ m → Sub Γ a s × Sub Γ s a := by
      intro m hm Γ' a' b' s' t' h' hle'
      exact ih (m + 1) (by omega) Γ' a' b' s' t' h' (by omega)
    -- Case-split on h
    -- For (.lam a b) on LHS and (.lam s t) on RHS:
    -- refl, lam, or trans
    cases h with
    | refl =>
      -- .lam a b = .lam s t, so a = s and b = t
      exact ⟨.refl a, .refl a⟩
    | top => exact absurd rfl (Expr.noConfusion)
    | @trans _ _ m _ h1 h2 hw =>
      match m with
      | .top =>
        exact absurd (top_not_sub_lam h2) False.elim
      | .bvar j =>
        exact absurd (lam_not_sub_bvar h1) False.elim
      | .lam d e =>
        -- h1 : Sub Γ (.lam a b) (.lam d e), h2 : Sub Γ (.lam d e) (.lam s t)
        -- hw : Wf Γ (.lam d e)
        have hwd : Wf Γ d := match hw with | .lam hd _ => hd
        have inv1 := ih' h1.height (by simp [Sub.height] at hlt; omega)
          Γ a b d e h1 (Nat.le_refl _)
        have inv2 := ih' h2.height (by simp [Sub.height] at hlt; omega)
          Γ d e s t h2 (Nat.le_refl _)
        exact ⟨.trans inv1.1 inv2.1 hwd, .trans inv2.2 inv1.2 hwd⟩
      | .app f c =>
        -- h1 : Sub Γ (.lam a b) (.app f c), h2 : Sub Γ (.app f c) (.lam s t)
        -- hw : Wf Γ (.app f c)
        exact lamInvAppHelper ih' h1 h2 hw (by simp [Sub.height] at hlt; omega)
    | bvar _ => exact absurd rfl (Expr.noConfusion)
    | @lam _ dom dom' bd bd' h_dd' h_d'd h_bb' =>
      -- .lam dom bd = .lam a b and .lam dom' bd' = .lam s t
      -- so dom = a, bd = b, dom' = s, bd' = t
      exact ⟨h_dd', h_d'd⟩
    | app_cong _ _ _ => exact absurd rfl (Expr.noConfusion)
    | beta_L => exact absurd rfl (Expr.noConfusion)
    | beta_R => exact absurd rfl (Expr.noConfusion)

/-- **Inversion lemma (Lemma 5.2)**: if `(λa.b) ≤ (λs.t)` then `a ≡ s`.

    The domains of related lambda types are equivalent (both `a ≤ s` and `s ≤ a`).
    Proved via strong induction on derivation height, with a helper for
    the `.app` middle-term case in transitivity (β-expansion chains). -/
theorem lam_sub_lam_inversion {Γ : Ctx} {a b s t : Expr}
    (h : Sub Γ (.lam a b) (.lam s t)) : Sub Γ a s × Sub Γ s a :=
  lam_sub_lam_inversion_aux (h.height + 1) Γ a b s t h (Nat.lt.base _)

end PSS

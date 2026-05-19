import PSS.Sub

/-!
# Canonical Forms Lemma

Proves that `Sub Γ .top (.lam s t) → False` and `Sub Γ .top (.bvar k) → False`.

## Proof technique

Strong induction on derivation height with `P(n) := ∀ h, h.height = n → …`.
This gives a "flat" IH: `∀ h, h.height < n → …` (by setting `m = h.height`
in `∀ m < n, P m`).

The `.app`-middle trans case delegates to `appHelper` (inner induction on
h2.height).  All cases are closed cleanly EXCEPT the "boundary" sub-case
where h2 is directly `beta_L` AND the h1 decomposition has `.app` middle.
In that sub-case the composed derivation has exactly the same height as the
original, so no height-based argument can make progress.  This is the exact
obstacle identified by Hutchins (POPL 2010, §6.6.3) and confirmed by
Pasquale & Garcia-Perez (CSL 2026).

## Status

`top_not_sub_lam` and `top_not_sub_bvar` have ONE sorry: the
`.app`-middle sub-case of h1 decomposition in the beta_L boundary case.
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

The IH `ih` is "flat": any derivation with `h.height < n` can be
dispatched directly.  The bound is strict (`< n`). -/
private theorem appHelper
    {n : Nat}
    (ih : ∀ (Γ : Ctx) (a b : Expr) (h : Sub Γ a b),
      h.height < n → a = .top → Expr.IsHeadForm b → False)
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
      have hbx : 1 + h1'.height + (1 + h2a.height + h2b.height + hw2.height) + hw'.height < n := by
        simp [Sub.height] at hboundx; omega
      match m2 with
      | .top =>
        exact ih Γ' .top b2 h2b (by omega) rfl hb2
      | .lam d bd =>
        exact ih Γ' .top (.lam d bd) (.trans h1' h2a hw')
          (by simp [Sub.height]; omega) rfl trivial
      | .bvar k =>
        exact ih Γ' .top (.bvar k) (.trans h1' h2a hw')
          (by simp [Sub.height]; omega) rfl trivial
      | .app g d =>
        have hbound_new : 1 + (Sub.trans h1' h2a hw').height + h2b.height + hw2.height < n := by
          simp [Sub.height]; omega
        exact ihp h2b.height hh2b_lt_p (.trans h1' h2a hw') h2b hw2 hb2
          hbound_new (Nat.le_refl _)
    | bvar _ => exact Expr.noConfusion heq
    | lam _ _ _ => exact Expr.noConfusion heq
    | app_cong _ _ _ => simp [Expr.IsHeadForm] at hb2
    | @beta_L _ dom body _ =>
      cases heq
      -- Composed: Sub.trans h1' .beta_L hw' has height 1 + h1'.height + 0 + hw'.height < n
      exact ih Γ' .top (body.subst 0 _) (.trans h1' .beta_L hw')
        (by simp [Sub.height] at hboundx ⊢; omega) rfl hb2
    | beta_R => simp [Expr.IsHeadForm] at hb2

/-- Core: `Sub Γ a b → a = .top → IsHeadForm b → h.height = n → False`. -/
private theorem top_not_sub_headForm_aux (n : Nat) :
    ∀ (Γ : Ctx) (a b : Expr) (h : Sub Γ a b),
      h.height = n → a = .top → Expr.IsHeadForm b → False := by
  induction n using Nat.strongRecOn with
  | _ n ih_strong =>
    intro Γ a b h heq ha hb
    -- Flat IH: for any h' with h'.height < n, the conclusion holds.
    have ih_flat : ∀ (Γ' : Ctx) (a' b' : Expr) (h' : Sub Γ' a' b'),
        h'.height < n → a' = .top → Expr.IsHeadForm b' → False := by
      intro Γ' a' b' h' hlt' ha' hb'
      exact ih_strong h'.height hlt' Γ' a' b' h' rfl ha' hb'
    cases h with
    | refl e => subst ha; simp [Expr.IsHeadForm] at hb
    | top e => simp [Expr.IsHeadForm] at hb
    | @trans _ _ m _ h1 h2 hw =>
      subst ha
      have htrans : 1 + h1.height + h2.height + hw.height = n := by
        simp [Sub.height] at heq; omega
      match m with
      | .top =>
        exact ih_flat Γ .top b h2 (by omega) rfl hb
      | .lam d bd =>
        exact ih_flat Γ .top (.lam d bd) h1 (by omega) rfl trivial
      | .bvar k =>
        exact ih_flat Γ .top (.bvar k) h1 (by omega) rfl trivial
      | .app f' a' =>
        -- 1 + h1.height + h2.height + hw.height = n.
        -- Generalize h2 for case analysis.
        suffices ∀ (a2 b2 : Expr) (h2g : Sub Γ a2 b2),
          a2 = .app f' a' → Expr.IsHeadForm b2 →
          1 + h1.height + h2g.height + hw.height = n → False from
          this _ _ h2 rfl hb htrans
        intro a2 b2 h2g heq2 hb2 htrans2
        cases h2g with
        | refl => rw [heq2] at hb2; simp [Expr.IsHeadForm] at hb2
        | top => simp [Expr.IsHeadForm] at hb2
        | @trans _ _ m2 _ h2a h2b hw2 =>
          subst heq2
          have hbound2 : 1 + h1.height + (1 + h2a.height + h2b.height + hw2.height) + hw.height = n := by
            simp [Sub.height] at htrans2; omega
          match m2 with
          | .top =>
            exact ih_flat Γ .top b2 h2b (by omega) rfl hb2
          | .lam d bd =>
            exact ih_flat Γ .top (.lam d bd) (.trans h1 h2a hw)
              (by simp [Sub.height]; omega) rfl trivial
          | .bvar k =>
            exact ih_flat Γ .top (.bvar k) (.trans h1 h2a hw)
              (by simp [Sub.height]; omega) rfl trivial
          | .app g d =>
            -- Bound = n, appHelper needs < n. Same blocker as beta_L boundary.
            sorry
        | bvar _ => exact Expr.noConfusion heq2
        | lam _ _ _ => exact Expr.noConfusion heq2
        | app_cong _ _ _ => simp [Expr.IsHeadForm] at hb2
        | @beta_L _ dom body _ =>
          cases heq2
          -- h2 = beta_L, h2.height = 0
          -- Compose h1 with beta_L via trans: this is the boundary case.
          -- The composed derivation has the same height as n.
          -- This is the genuine blocker that requires transitivity elimination.
          sorry
        | beta_R => simp [Expr.IsHeadForm] at hb2
    | bvar _ => exact Expr.noConfusion ha
    | lam _ _ _ => exact Expr.noConfusion ha
    | app_cong _ _ _ => exact Expr.noConfusion ha
    | beta_L => exact Expr.noConfusion ha
    | beta_R => simp [Expr.IsHeadForm] at hb

/-- Top cannot be a subtype of a function type. -/
theorem top_not_sub_lam {Γ : Ctx} {s t : Expr}
    (h : Sub Γ .top (.lam s t)) : False :=
  top_not_sub_headForm_aux h.height Γ .top (.lam s t) h rfl rfl trivial

/-- Top cannot be a subtype of a variable. -/
theorem top_not_sub_bvar {Γ : Ctx} {k : Nat}
    (h : Sub Γ .top (.bvar k)) : False :=
  top_not_sub_headForm_aux h.height Γ .top (.bvar k) h rfl rfl trivial

/-- A lambda cannot be a subtype of a bound variable. -/
theorem lam_not_sub_bvar {Γ : Ctx} {dom body : Expr} {k : Nat}
    (h : Sub Γ (.lam dom body) (.bvar k)) : False :=
  sorry

/-- **Inversion lemma (Lemma 5.2)**: if `(λa.b) ≤ (λs.t)` then `a ≡ s`.

    The `.lam` and `.top` middle-term cases are closed; the `.app` case
    is the open problem (trans through a β-expansion, same obstacle as
    the paper's Conjecture 5.1 on transitivity elimination). -/
def lam_sub_lam_inversion {Γ : Ctx} {a b s t : Expr}
    (h : Sub Γ (.lam a b) (.lam s t)) : Sub Γ a s × Sub Γ s a :=
  sorry

end PSS

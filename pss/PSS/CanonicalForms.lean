import PSS.Sub

/-!
# Canonical Forms Lemma

Goal: `PSS.Sub Γ .top (.lam s t) → False`

With `Sub` and `Wf` now in `Type`, we define height functions and use
strong (well-founded) induction on derivation height.

## Status

The proof handles all cases except the `.app` middle term in `trans`.
The `.app` case requires lexicographic induction on (h2.height, h1.height)
with composition of derivations, which creates a circularity with the main
lemma. See the detailed analysis in the `appHelper_note` below.

## What's proved

- Height functions on Sub and Wf derivations
- All base-case constructors are impossible for Sub Γ .top (headform)
- The trans case with .top, .lam, .bvar middle terms

## What's sorry'd

- The trans case with .app middle term (1 sorry)
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

/-!
## Analysis of the .app middle term case

In the trans case `h = Sub.trans h1 h2 hw` where `h1 : Sub Γ .top (.app f a)` and
`h2 : Sub Γ (.app f a) b` with `IsHeadForm b`:

**Why it's hard**: Neither h1 nor h2 alone has the goal shape
(`Sub Γ .top (headform)`). h1 has .app on the RHS (not a head form),
and h2 has .app on the LHS (not .top).

**Correct termination argument**: Lexicographic induction on `(h2.height, h1.height)`.
- When we case-split h2 and the middle term is .app: we compose h1 with h2a
  (building a bigger h1'), but h2b.height < h2.height. First component decreases.
- When h2 = beta_L: we case-split h1. If h1 = trans, we peel h1 to get h1b
  with h1b.height < h1.height. h2 stays the same. Second component decreases.
- When h1 = beta_R and h2 = beta_L: body.subst 0 arg = .top = b.
  IsHeadForm .top = False. Direct contradiction.

**Why it doesn't close yet**: The helper needs Part A (the main lemma) at
arbitrary heights (for newly composed derivations), but Part A calls the
helper, creating a circularity that Lean's termination checker can't resolve
with simple strong induction. This likely needs well-founded recursion on a
custom relation combining both derivations.
-/

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
        -- h1 : Sub Γ .top (.app f' a'), h2 : Sub Γ (.app f' a') b
        -- Both heights < n. IsHeadForm b.
        -- See module docstring for analysis of why this case is hard.
        sorry
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

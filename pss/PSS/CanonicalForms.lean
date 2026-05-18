import PSS.Sub

/-!
# Canonical Forms and Inversion Lemmas

## Part 1: `PSS.Sub Γ .top (.lam s t) → False` (and `.bvar`)

## Part 2: `PSS.Sub Γ (.lam a b) (.bvar k) → False`

## Part 3: Lambda-Lambda Inversion (Lemma 5.2 from the PSS paper)
  If `Sub Γ (.lam a b) (.lam s t)` then `Sub Γ a s × Sub Γ s a`.

All proofs use height-based strong induction via `Nat.strongRecOn`.

## Important caveat

The `trans + .app + beta_L` interaction creates a fundamental proof obstacle:
when the middle term of a transitivity chain is an application, the `beta_L`
rule can fire, but composing via `trans` produces a derivation of the SAME
height. No simple height/size measure decreases. This is a known open problem
in the PSS metatheory — see Pasquale & García-Pérez, "Towards the type safety
of Pure Subtype Systems" (2024), who introduced Machine-Based PSS (MPSS) to
circumvent this issue.

The proofs below handle all cases EXCEPT this interaction, which is marked
with `sorry` and detailed comments.
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
## Part 1: Top is not a subtype of any head form

The proof handles all cases directly. The `trans` case with a `.app` middle
term is the hardest: we need to show that a chain `.top ≤ .app f c ≤ headform`
leads to a contradiction. When the `.app → headform` derivation uses `trans`,
we can compose `.top ≤ .app` with the first half to get a smaller derivation
`.top ≤ M` (where M is the new middle term). When it uses `beta_L`, we hit
the fundamental obstacle described above.
-/

/-- Core: Sub Γ .top b → IsHeadForm b → False.

Uses strong induction on `h.height`. The `trans + .app + beta_L` interaction
is the one genuinely hard case; it requires a proof technique beyond simple
height induction (see file header). All other cases are closed. -/
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
      have ht : 1 + h1.height + h2.height + hw.height ≤ n := by
        simp [Sub.height] at hle; omega
      match m with
      | .top =>
        exact ih h2.height (by omega) Γ .top b h2 (Nat.le_refl _) rfl hb
      | .lam d bd =>
        exact ih h1.height (by omega) Γ .top (.lam d bd) h1 (Nat.le_refl _) rfl trivial
      | .bvar k =>
        exact ih h1.height (by omega) Γ .top (.bvar k) h1 (Nat.le_refl _) rfl trivial
      | .app f' a' =>
        -- h1 : Sub Γ .top (.app f' a'), h2 : Sub Γ (.app f' a') b, hw : Wf Γ (.app f' a')
        -- We need to analyze h2 to make progress. The trans case with another .app
        -- middle is fine (compose h1 with h2a to get a strictly smaller derivation).
        -- The beta_L base case is the fundamental obstacle.
        --
        -- For now, we use sorry. A complete proof would require either:
        -- 1. Reformulating as MPSS (Machine-Based PSS) per Pasquale & García-Pérez 2024
        -- 2. A logical-relations argument
        -- 3. Proving transitivity elimination on the algorithmic system
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

/-!
## Part 2: Lambda is not a subtype of a bound variable
-/

/-- Core: Sub Γ (.lam dom body) (.bvar k) → False. -/
private theorem lam_not_sub_bvar_aux (n : Nat) :
    ∀ (Γ : Ctx) (a b : Expr) (h : Sub Γ a b),
      h.height ≤ n →
      ∀ dom body k, a = .lam dom body → b = .bvar k → False := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro Γ a b h hle dom body k ha hb
    cases h with
    | refl e => subst ha; exact Expr.noConfusion hb
    | top _ => exact Expr.noConfusion hb
    | @trans _ _ m _ h1 h2 hw =>
      subst ha; subst hb
      have ht : 1 + h1.height + h2.height + hw.height ≤ n := by
        simp [Sub.height] at hle; omega
      match m with
      | .top => exact top_not_sub_bvar h2
      | .lam d c =>
        exact ih h2.height (by omega) Γ (.lam d c) (.bvar k) h2
          (Nat.le_refl _) d c k rfl rfl
      | .bvar j =>
        exact ih h1.height (by omega) Γ (.lam dom body) (.bvar j) h1
          (Nat.le_refl _) dom body j rfl rfl
      | .app f c =>
        -- Same fundamental obstacle as Part 1: trans + .app interaction.
        -- h1 : Sub Γ (.lam dom body) (.app f c)
        -- h2 : Sub Γ (.app f c) (.bvar k)
        sorry
    | bvar _ => exact Expr.noConfusion ha
    | lam _ _ _ => exact Expr.noConfusion hb
    | app_cong _ _ _ => exact Expr.noConfusion ha
    | beta_L => exact Expr.noConfusion ha
    | beta_R => exact Expr.noConfusion hb

/-- A lambda cannot be a subtype of a bound variable. -/
theorem lam_not_sub_bvar {Γ : Ctx} {dom body : Expr} {k : Nat}
    (h : Sub Γ (.lam dom body) (.bvar k)) : False :=
  lam_not_sub_bvar_aux h.height Γ (.lam dom body) (.bvar k) h
    (Nat.le_refl _) dom body k rfl rfl

/-!
## Part 3: Lambda-Lambda Inversion (Lemma 5.2)

If `Sub Γ (.lam a b) (.lam s t)` then `Sub Γ a s × Sub Γ s a`.

The return type is in `Type` (since `Sub` is in `Type`), so we use `noncomputable def`.
-/

/-- Core: lam-lam inversion by strong induction on height.

Handles all cases:
- **refl**: trivial (domains equal)
- **lam**: direct extraction from the constructor
- **trans with .top middle**: contradicts `top_not_sub_lam`
- **trans with .bvar middle**: contradicts `lam_not_sub_bvar`
- **trans with .lam middle**: IH on both halves, compose via Wf extraction
- **trans with .app middle**: same fundamental obstacle as Parts 1 & 2
- **beta_R**: RHS is .app, not .lam — contradiction
- Other constructors: LHS/RHS shape mismatch -/
private noncomputable def lam_sub_lam_inversion_aux (n : Nat) :
    ∀ (Γ : Ctx) (a b : Expr) (h : Sub Γ a b),
      h.height ≤ n →
      ∀ da db sa sb, a = .lam da db → b = .lam sa sb →
      Sub Γ da sa × Sub Γ sa da := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro Γ a b h hle da db sa sb ha hb
    cases h with
    | refl e =>
      subst ha; cases hb
      exact ⟨.refl da, .refl da⟩
    | top _ => exact Expr.noConfusion hb
    | @trans _ _ m _ h1 h2 hw =>
      subst ha; subst hb
      have ht : 1 + h1.height + h2.height + hw.height ≤ n := by
        simp [Sub.height] at hle; omega
      match m with
      | .top => exact (top_not_sub_lam h2).elim
      | .bvar j => exact (lam_not_sub_bvar h1).elim
      | .lam d c₀ =>
        have ⟨had, hda⟩ := ih h1.height (by omega) Γ (.lam da db) (.lam d c₀) h1
          (Nat.le_refl _) da db d c₀ rfl rfl
        have ⟨hds, hsd⟩ := ih h2.height (by omega) Γ (.lam d c₀) (.lam sa sb) h2
          (Nat.le_refl _) d c₀ sa sb rfl rfl
        -- Extract Wf Γ d from hw : Wf Γ (.lam d c₀)
        have hwd : Wf Γ d := by cases hw with | lam hd _ => exact hd
        exact ⟨.trans had hds hwd, .trans hsd hda hwd⟩
      | .app f c₀ =>
        -- Same fundamental obstacle: trans + .app middle term.
        -- h1 : Sub Γ (.lam da db) (.app f c₀)
        -- h2 : Sub Γ (.app f c₀) (.lam sa sb)
        -- The middle term is an application. To extract domain equivalence,
        -- we would need to "thread through" the app (via beta_L/beta_R) and
        -- show that the domain information is preserved. This is the same
        -- obstacle as in Parts 1 & 2.
        exact sorry
    | bvar _ => exact Expr.noConfusion ha
    | @lam _ _ _ _ _ hdom hdom' _ =>
      cases ha; cases hb
      exact ⟨hdom, hdom'⟩
    | app_cong _ _ _ => exact Expr.noConfusion ha
    | beta_L => exact Expr.noConfusion ha
    | @beta_R _ _ _ _ =>
      -- LHS = body.subst 0 arg, RHS = .app (.lam dom body) arg
      -- RHS must equal .lam sa sb, but .app ≠ .lam
      exact Expr.noConfusion hb

/-- **Lemma 5.2** (Lambda-Lambda Inversion): If a lambda is a subtype of another
    lambda, their domains are equivalent.

    `Sub Γ (.lam a b) (.lam s t) → Sub Γ a s × Sub Γ s a` -/
noncomputable def lam_sub_lam_inversion {Γ : Ctx} {a b s t : Expr}
    (h : Sub Γ (.lam a b) (.lam s t)) : Sub Γ a s × Sub Γ s a :=
  lam_sub_lam_inversion_aux h.height Γ (.lam a b) (.lam s t) h
    (Nat.le_refl _) a b s t rfl rfl

end PSS

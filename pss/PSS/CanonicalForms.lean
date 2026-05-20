import PSS.Sub

/-!
# Canonical Forms Lemma

Proves that `Sub Γ .top (.lam s t) → False` and `Sub Γ .top (.bvar k) → False`.

## Proof architecture

Single theorem `top_not_sub_headForm_aux` by strong induction on height n,
with three nested induction layers:

1. **appHelper** (suffices, induction on h2.height):
   Decomposes the right branch `h2 : Sub (.app f c) b` when `b` is a headform.
   Handles all h2 constructors. For `.app`-middle trans in h2, composes h1 with
   h2a and recurses on h2b (h2.height strictly decreases). For `beta_L`, falls
   through to betaHelper.

2. **betaHelper** (suffices, induction on h1.height):
   Handles `h2 = beta_L`. Decomposes `h1 : Sub .top (.app (.lam dom body) c)`.
   For non-app middle trans in h1 (`.top`/`.lam`/`.bvar`), uses ih_flat or
   recurses directly. For `.app g d` middle, falls through to h1bHelper.

3. **h1bHelper** (suffices, induction on h1b.height):
   Decomposes h1b : Sub (.app g d) (.app (.lam dom body) c) to peel the
   app→app chain. Handles `refl`, `trans` (all middle types), `beta_R`.

## Key structural improvement

The main theorem and appHelper both have ZERO sorrys. The `≤ n` bound
(vs the original `= n` / `< n`) lets the main theorem call appHelper
directly without boundary issues. Previously, both the main theorem's
`.app` h2-trans-app case AND betaHelper's h1-trans-app case had sorrys;
now only the h1b decomposition inside betaHelper has sorrys.

## Remaining sorrys (3 in betaHelper h1b decomposition)

All sorrys arise because the composed derivation has height ≤ n (not < n),
and no available IH accepts ≤ n at the point of use.

1. **app_cong, body₂ = .bvar k**: h1b = app_cong hf ha ha' and the lambda
   body is a variable. The substitution `(.bvar k).subst 0 c₂` gives either
   `c₂` (if k=0) or `.bvar (k-1)` (if k>0), both headforms.
   NOTE: The cases body₂ = .top and body₂ = .app are CLOSED (substitution
   gives non-headform, contradicting hb_x).

2. **app_cong, body₂ = .lam d b**: h1b = app_cong hf ha ha' and the lambda
   body is itself a lambda. Substitution gives `.lam (d.subst 0 c₂) ...`
   which IS a headform.

3. **beta_L** (double-beta): h1b = beta_L, giving `body'.subst 0 d'` =
   `.app (.lam dom₂ body₂) c₂` (the substitution result is another redex).

All three are instances of the Hutchins obstacle (POPL 2010, S6.6.3):
transitivity reassociation preserves total height. The `totalWeight_reassoc_eq`
theorem proves that ANY additive measure is invariant under the rearrangement.

### Approaches explored

- **All additive measures** (height, totalWeight, height + hw.height, etc.):
  invariant under reassociation, proven by `totalWeight_reassoc_eq`.
- **Max-based measures** (appDepth): sometimes equal, sometimes wrong direction.
- **Fuel / extra budget**: adding a fuel parameter to the main theorem provides
  one extra composition per unit of fuel, but the loop repeats identically
  so fuel eventually exhausts without convergence.
- **Wf decomposition**: extracting `Sub (.lam dom₂ body₂) (.lam s .top)` from
  `hw_x` closes the body₂ = .top and body₂ = .app cases (non-headform subst
  results). The body₂ = .bvar and body₂ = .lam cases remain open because
  they produce genuine headform substitution results.
- **Lexicographic (n, q)**: betaHelper's q increases by 1 in the composition.
- **Ordinal-valued measures**: the number of app-middle trans layers and
  beta_L nodes are preserved by reassociation.

Closing the remaining sorrys requires a fundamentally different proof strategy
(e.g., logical relations, transitivity elimination, or an auxiliary structural
lemma that breaks the circular height dependency).
-/

open Expr

namespace PSS

-- ============================================================================
-- Height function
-- ============================================================================

mutual
def Sub.height : Sub Γ a b → Nat
  | .refl _       => 0
  | .top _        => 0
  | .trans h1 h2 hw => 1 + h1.height + h2.height + hw.height
  | .bvar _       => 0
  | .lam h1 h2 h3  => 1 + h1.height + h2.height + h3.height
  | .app_cong h1 h2 h3 => 1 + h1.height + h2.height + h3.height
  | .beta_L       => 0
  | .beta_R       => 0

def Wf.height : Wf Γ e → Nat
  | .var _         => 0
  | .top           => 0
  | .lam hd hb     => 1 + hd.height + hb.height
  | .app hf ha hs hsub harg => 1 + hf.height + ha.height + hs.height + hsub.height + harg.height
end

-- ============================================================================
-- App-chain depth (max-based, non-additive)
-- ============================================================================

mutual
/-- The app-chain depth: maximum nesting of trans nodes with .app middle. -/
def Sub.appDepth : Sub Γ a b → Nat
  | .refl _       => 0
  | .top _        => 0
  | @Sub.trans _ _ m _ h1 h2 hw =>
    match m with
    | .app _ _ => 1 + max (h1.appDepth) (max (h2.appDepth) (hw.appDepth))
    | _        => max (h1.appDepth) (max (h2.appDepth) (hw.appDepth))
  | .bvar _       => 0
  | .lam h1 h2 h3  => max (h1.appDepth) (max (h2.appDepth) (h3.appDepth))
  | .app_cong h1 h2 h3 => max (h1.appDepth) (max (h2.appDepth) (h3.appDepth))
  | .beta_L       => 0
  | .beta_R       => 0

/-- The app-chain depth of a Wf derivation. -/
def Wf.appDepth : Wf Γ e → Nat
  | .var _         => 0
  | .top           => 0
  | .lam hd hb     => max (hd.appDepth) (hb.appDepth)
  | .app hf ha hs hsub harg =>
    max (hf.appDepth) (max (ha.appDepth) (max (hs.appDepth) (max (hsub.appDepth) (harg.appDepth))))
end

-- ============================================================================
-- Total weight: counts EVERY node in the derivation tree, including Sub
-- derivations embedded inside Wf (e.g., from Wf.app).
-- Key difference from height: beta_L and beta_R get weight 1, not 0.
-- ============================================================================

mutual
/-- Total weight of a Sub derivation, counting every node including
    sub-derivations embedded in Wf witnesses. -/
def Sub.totalWeight : Sub Γ a b → Nat
  | .refl _       => 1
  | .top _        => 1
  | .trans h1 h2 hw => 1 + h1.totalWeight + h2.totalWeight + hw.totalWeight
  | .bvar _       => 1
  | .lam h1 h2 h3  => 1 + h1.totalWeight + h2.totalWeight + h3.totalWeight
  | .app_cong h1 h2 h3 => 1 + h1.totalWeight + h2.totalWeight + h3.totalWeight
  | .beta_L       => 1
  | .beta_R       => 1

/-- Total weight of a Wf derivation. -/
def Wf.totalWeight : Wf Γ e → Nat
  | .var _         => 1
  | .top           => 1
  | .lam hd hb     => 1 + hd.totalWeight + hb.totalWeight
  | .app hf ha hs hsub harg => 1 + hf.totalWeight + ha.totalWeight + hs.totalWeight + hsub.totalWeight + harg.totalWeight
end

-- All totalWeights are ≥ 1
mutual
theorem Sub.totalWeight_pos (h : Sub Γ a b) : 1 ≤ h.totalWeight := by
  cases h <;> simp [Sub.totalWeight] <;> omega

theorem Wf.totalWeight_pos (hw : Wf Γ e) : 1 ≤ hw.totalWeight := by
  cases hw <;> simp [Wf.totalWeight] <;> omega
end

-- ============================================================================
-- Weight-preservation of transitivity reassociation
--
-- The key obstacle: every rearrangement that arises at the sorry points
-- preserves totalWeight EXACTLY. The proof below demonstrates this for
-- the critical app_cong sorry:
--
-- ORIGINAL derivation (schematic, what the main theorem sees):
--   trans (trans h1a (app_cong hf ha ha') hw1) beta_L hw_x
--
-- COMPOSED derivation (what we'd like to recurse on):
--   trans h1a (trans (app_cong hf ha ha') beta_L hw_x) hw1
--
-- Both use the SAME set of leaf/intermediate sub-derivations
-- {h1a, hf, ha, ha', hw1, hw_x, beta_L}, wrapped in exactly two
-- trans nodes and one app_cong node. Since totalWeight is additive
-- over the tree, the totals are identical:
--
--   original = 4 + tw(h1a) + tw(hf) + tw(ha) + tw(ha') + ww(hw1) + ww(hw_x)
--   composed = 4 + tw(h1a) + tw(hf) + tw(ha) + tw(ha') + ww(hw_x) + ww(hw1)
--
-- So if original.totalWeight ≤ n, composed.totalWeight ≤ n (not < n).
-- The ih_flat IH requires STRICT decrease (< n), which is off by exactly 1.
--
-- This is true regardless of how we weight beta_L (0, 1, or any constant):
-- the rearrangement swaps sub-trees between wrapper nodes but preserves
-- the total count of wrapper nodes and leaves.
-- ============================================================================

/-- The transitivity reassociation preserves totalWeight: the "original"
    and "composed" derivation trees at the app_cong sorry have identical
    totalWeight. This proves the totalWeight approach fundamentally cannot
    close the off-by-one gap. -/
theorem totalWeight_reassoc_eq
    {Γ : Ctx} {a m1 m2 b : Expr}
    (h1a : Sub Γ a m1) (h1b : Sub Γ m1 m2) (hw1 : Wf Γ m1)
    (h2 : Sub Γ m2 b) (hw2 : Wf Γ m2) :
    -- original: trans (trans h1a h1b hw1) h2 hw2
    -- composed: trans h1a (trans h1b h2 hw2) hw1
    (Sub.trans (Sub.trans h1a h1b hw1) h2 hw2).totalWeight =
    (Sub.trans h1a (Sub.trans h1b h2 hw2) hw1).totalWeight := by
  simp [Sub.totalWeight, Wf.totalWeight]; omega

/-- Specific instance for the app_cong sorry: the composed derivation
    `trans h1a (trans (app_cong hf ha ha') beta_L hw_x) hw1`
    has the same totalWeight as the original
    `trans (trans h1a (app_cong hf ha ha') hw1) beta_L hw_x`.
    Since any additive measure gives the same value for both, no
    additive measure can provide the strict decrease needed. -/
theorem totalWeight_app_cong_beta_eq
    {Γ : Ctx} {a g d dom body c : Expr}
    (h1a : Sub Γ a (.app g d))
    (hf : Sub Γ g (.lam dom body)) (ha : Sub Γ d c) (ha' : Sub Γ c d)
    (hw1 : Wf Γ (.app g d))
    (hw_x : Wf Γ (.app (.lam dom body) c)) :
    -- original shape (how the derivation looked before decomposition):
    (Sub.trans (Sub.trans h1a (.app_cong hf ha ha') hw1) .beta_L hw_x).totalWeight =
    -- composed shape (what we want to recurse on):
    (Sub.trans h1a (Sub.trans (.app_cong hf ha ha') .beta_L hw_x) hw1).totalWeight := by
  simp [Sub.totalWeight, Wf.totalWeight]; omega

def Expr.IsHeadForm : Expr → Prop
  | .lam _ _ => True
  | .bvar _ => True
  | _ => False

-- ============================================================================
-- Combined helper: handles both app-chain decomposition and beta_L
-- ============================================================================

-- We bundle betaHelper and appHelper into a single theorem by doing
-- all the work inline in the main theorem. This avoids mutual recursion.

-- ============================================================================
-- Main theorem (everything combined)
-- ============================================================================

/-- Core: `Sub Γ a b → a = .top → IsHeadForm b → h.height ≤ n → False`.

Uses strong induction on n. The app-middle trans case is handled by
secondary induction on h2.height, with the beta_L sub-case using
tertiary induction on h1.height + h1b decomposition. -/
private theorem top_not_sub_headForm_aux (n : Nat) :
    ∀ (Γ : Ctx) (a b : Expr) (h : Sub Γ a b),
      h.height ≤ n → a = .top → Expr.IsHeadForm b → False := by
  induction n using Nat.strongRecOn with
  | _ n ih_strong =>
    intro Γ a b h hle ha hb
    have ih_flat : ∀ (Γ' : Ctx) (a' b' : Expr) (h' : Sub Γ' a' b'),
        h'.height < n → a' = .top → Expr.IsHeadForm b' → False := by
      intro Γ' a' b' h' hlt' ha' hb'
      exact ih_strong h'.height hlt' Γ' a' b' h' (Nat.le_refl _) ha' hb'
    cases h with
    | refl e => subst ha; simp [Expr.IsHeadForm] at hb
    | top e => simp [Expr.IsHeadForm] at hb
    | @trans _ _ m _ h1 h2 hw =>
      subst ha
      have htrans : 1 + h1.height + h2.height + hw.height ≤ n := by
        simp [Sub.height] at hle; omega
      match m with
      | .top =>
        exact ih_flat Γ .top b h2 (by omega) rfl hb
      | .lam d bd =>
        exact ih_flat Γ .top (.lam d bd) h1 (by omega) rfl trivial
      | .bvar k =>
        exact ih_flat Γ .top (.bvar k) h1 (by omega) rfl trivial
      | .app f' a' =>
        -- === appHelper inlined ===
        -- Secondary induction on h2.height to decompose the right branch.
        suffices appHelper : ∀ (p : Nat) {Γ' : Ctx} {f' c' b' : Expr}
          (h1' : Sub Γ' .top (.app f' c')) (h2' : Sub Γ' (.app f' c') b')
          (hw' : Wf Γ' (.app f' c')) (hb' : Expr.IsHeadForm b')
          (hbound' : 1 + h1'.height + h2'.height + hw'.height ≤ n)
          (hp2 : h2'.height ≤ p), False from
          appHelper h2.height h1 h2 hw hb htrans (Nat.le_refl _)
        intro p
        induction p using Nat.strongRecOn with
        | _ p ihp =>
          intro Γ' f' c' b' h1' h2' hw' hb' hbound' hp2
          suffices ∀ (a2 b2 : Expr) (h2x : Sub Γ' a2 b2),
            h2x.height ≤ p → a2 = .app f' c' → Expr.IsHeadForm b2 →
            (1 + h1'.height + h2x.height + hw'.height ≤ n) →
            False from this (.app f' c') b' h2' hp2 rfl hb' hbound'
          intro a2 b2 h2x hp2x heq hb2 hboundx
          cases h2x with
          | refl => rw [heq] at hb2; simp [Expr.IsHeadForm] at hb2
          | top => simp [Expr.IsHeadForm] at hb2
          | @trans _ _ m2 _ h2a h2b hw2 =>
            subst heq
            have hh2b_lt_p : h2b.height < p := by simp [Sub.height] at hp2x; omega
            have hbx : 1 + h1'.height + (1 + h2a.height + h2b.height + hw2.height) + hw'.height ≤ n := by
              simp [Sub.height] at hboundx; omega
            match m2 with
            | .top =>
              exact ih_flat Γ' .top b2 h2b (by omega) rfl hb2
            | .lam d bd =>
              exact ih_flat Γ' .top (.lam d bd) (.trans h1' h2a hw')
                (by simp [Sub.height]; omega) rfl trivial
            | .bvar k =>
              exact ih_flat Γ' .top (.bvar k) (.trans h1' h2a hw')
                (by simp [Sub.height]; omega) rfl trivial
            | .app g d =>
              have hbound_new : 1 + (Sub.trans h1' h2a hw').height + h2b.height + hw2.height ≤ n := by
                simp [Sub.height]; omega
              exact ihp h2b.height hh2b_lt_p (.trans h1' h2a hw') h2b hw2 hb2
                hbound_new (Nat.le_refl _)
          | bvar _ => exact Expr.noConfusion heq
          | lam _ _ _ => exact Expr.noConfusion heq
          | app_cong _ _ _ => simp [Expr.IsHeadForm] at hb2
          | @beta_L _ dom body _ =>
            cases heq
            -- === betaHelper inlined ===
            -- h2 = beta_L: h1' : Sub Γ' .top (.app (.lam dom body) _)
            -- body.subst 0 _ is headform (hb2)
            -- 1 + h1'.height + hw'.height ≤ n (from hboundx)
            --
            -- Tertiary induction on h1'.height to decompose h1'
            suffices betaHelper : ∀ (q : Nat) {Γ₂ : Ctx} {dom₂ body₂ c₂ : Expr}
              (h1x : Sub Γ₂ .top (.app (.lam dom₂ body₂) c₂))
              (hw_x : Wf Γ₂ (.app (.lam dom₂ body₂) c₂))
              (hb_x : Expr.IsHeadForm (body₂.subst 0 c₂))
              (hbound_x : 1 + h1x.height + hw_x.height ≤ n)
              (hq : h1x.height ≤ q), False from
              betaHelper h1'.height h1' hw' hb2
                (by simp [Sub.height] at hboundx; omega) (Nat.le_refl _)
            intro q
            induction q using Nat.strongRecOn with
            | _ q ihq =>
              intro Γ₂ dom₂ body₂ c₂ h1x hw_x hb_x hbound_x hq_val
              suffices ∀ (src tgt : Expr) (h1g : Sub Γ₂ src tgt),
                src = .top → tgt = .app (.lam dom₂ body₂) c₂ → h1g.height ≤ q →
                1 + h1g.height + hw_x.height ≤ n → False from
                this .top _ h1x rfl rfl hq_val hbound_x
              intro src tgt h1g hsrc htgt hq_g hbound_g
              cases h1g with
              | refl => subst hsrc; exact Expr.noConfusion htgt
              | top => exact Expr.noConfusion htgt
              | @trans _ _ m1 _ h1a h1b hw1 =>
                subst hsrc; subst htgt
                match m1 with
                | .top =>
                  exact ihq h1b.height (by simp [Sub.height] at hq_g; omega) h1b hw_x hb_x
                    (by simp [Sub.height] at hbound_g; omega) (Nat.le_refl _)
                | .lam d bd =>
                  exact ih_flat Γ₂ .top (.lam d bd) h1a
                    (by simp [Sub.height] at hq_g hbound_g; omega) rfl trivial
                | .bvar k =>
                  exact ih_flat Γ₂ .top (.bvar k) h1a
                    (by simp [Sub.height] at hq_g hbound_g; omega) rfl trivial
                | .app g d =>
                  -- h1a : Sub Γ₂ .top (.app g d)
                  -- h1b : Sub Γ₂ (.app g d) (.app (.lam dom₂ body₂) c₂)
                  -- hw1 : Wf Γ₂ (.app g d)
                  --
                  -- Quaternary induction: decompose h1b (app→app chain)
                  suffices h1bHelper : ∀ (r : Nat) {g' d' : Expr}
                    (h1a' : Sub Γ₂ .top (.app g' d'))
                    (h1b' : Sub Γ₂ (.app g' d') (.app (.lam dom₂ body₂) c₂))
                    (hw1' : Wf Γ₂ (.app g' d'))
                    (hq_a' : h1a'.height + h1b'.height + hw1'.height < q)
                    (hbound_a' : 1 + 1 + h1a'.height + h1b'.height + hw1'.height + hw_x.height ≤ n)
                    (hr : h1b'.height ≤ r), False from
                    h1bHelper h1b.height h1a h1b hw1
                      (by simp [Sub.height] at hq_g; omega)
                      (by simp [Sub.height] at hbound_g; omega)
                      (Nat.le_refl _)
                  intro r
                  induction r using Nat.strongRecOn with
                  | _ r ihr =>
                    intro g' d' h1a' h1b' hw1' hq_a' hbound_a' hr
                    suffices ∀ (src tgt : Expr) (h1b_g : Sub Γ₂ src tgt),
                      src = .app g' d' → tgt = .app (.lam dom₂ body₂) c₂ →
                      h1b_g.height ≤ r →
                      h1a'.height + h1b_g.height + hw1'.height < q →
                      1 + 1 + h1a'.height + h1b_g.height + hw1'.height + hw_x.height ≤ n →
                      False from
                      this _ _ h1b' rfl rfl hr hq_a' hbound_a'
                    intro src tgt h1b_g hsrc_b htgt_b hr_g hq_b hbound_b
                    cases h1b_g with
                    | refl =>
                      -- .app g' d' = .app (.lam dom₂ body₂) c₂
                      rw [hsrc_b] at htgt_b
                      cases htgt_b
                      -- h1a' : Sub Γ₂ .top (.app (.lam dom₂ body₂) c₂)
                      exact @ihq h1a'.height
                        (by simp [Sub.height] at hq_b; omega)
                        Γ₂ dom₂ body₂ c₂ h1a' hw_x hb_x
                        (by simp [Sub.height] at hbound_b; omega)
                        (Nat.le_refl _)
                    | top => exact Expr.noConfusion htgt_b
                    | @trans _ _ m_b _ h1b1 h1b2 hw_b =>
                      subst hsrc_b; subst htgt_b
                      match m_b with
                      | .top =>
                        exact ihq h1b2.height
                          (by simp [Sub.height] at hr_g hq_b; omega)
                          h1b2 hw_x hb_x
                          (by simp [Sub.height] at hbound_b; omega)
                          (Nat.le_refl _)
                      | .lam dl bl =>
                        exact ih_flat Γ₂ .top (.lam dl bl) (.trans h1a' h1b1 hw1')
                          (by simp [Sub.height] at hbound_b; simp [Sub.height]; omega) rfl trivial
                      | .bvar k =>
                        exact ih_flat Γ₂ .top (.bvar k) (.trans h1a' h1b1 hw1')
                          (by simp [Sub.height] at hbound_b; simp [Sub.height]; omega) rfl trivial
                      | .app g'' d'' =>
                        have h1b2_lt_r : h1b2.height < r := by
                          simp [Sub.height] at hr_g; omega
                        exact ihr h1b2.height h1b2_lt_r
                          (.trans h1a' h1b1 hw1') h1b2 hw_b
                          (by simp [Sub.height] at hq_b; simp [Sub.height]; omega)
                          (by simp [Sub.height] at hbound_b; simp [Sub.height]; omega)
                          (Nat.le_refl _)
                    | bvar _ => exact Expr.noConfusion hsrc_b
                    | lam _ _ _ => exact Expr.noConfusion hsrc_b
                    | app_cong hf ha ha' =>
                      -- Unify the implicit variables from app_cong with g'/d' and dom₂/body₂/c₂.
                      cases hsrc_b; cases htgt_b
                      -- Now: hf : Sub Γ₂ g' (.lam dom₂ body₂)
                      --      ha : Sub Γ₂ d' c₂, ha' : Sub Γ₂ c₂ d'
                      --
                      -- Decompose hw_x to extract the Sub inside Wf.app.
                      -- Use auxiliary induction on hsub_lam to find a
                      -- Sub .top (.lam s .top) with height < n.
                      --
                      -- First, extract components from hw_x : Wf (.app (.lam dom₂ body₂) c₂).
                      -- We need to do the match inside a proof term context.
                      -- The key fact: hw_x contains hsub_lam : Sub (.lam dom₂ body₂) (.lam s_hw .top)
                      -- with hsub_lam.height < hw_x.height.
                      --
                      -- Approach: suffices ∀ ... hsub_lam ... → False, then extract from hw_x.
                      -- Decompose hw_x and case-split on body₂.
                      -- hw_x : Wf (.app (.lam dom₂ body₂) c₂) = Wf.app (lam hwf_dom hwf_body) ...
                      -- Extract Wf of body₂ to rule out .bvar (k+1).
                      -- Cases body₂ = .top and .app give ¬IsHeadForm → contradiction.
                      -- Cases .bvar 0 and .lam remain open (Hutchins obstacle).
                      -- Case-split body₂ to rule out non-headform substitution results.
                      -- .top and .app produce non-headform results → contradiction with hb_x.
                      -- .bvar and .lam produce headform results → Hutchins obstacle remains.
                      match body₂, hb_x with
                      | .top, hb_x => simp [Expr.subst, Expr.IsHeadForm] at hb_x
                      | .app e1 e2, hb_x => simp [Expr.subst, Expr.IsHeadForm] at hb_x
                      | .bvar _, hb_x =>
                        -- body₂ = .bvar k: subst gives c₂ (if k=0) or .bvar (k-1) (if k>0)
                        -- Both can be headforms. Composed derivation has height = n.
                        sorry
                      | .lam d_body b_body, hb_x =>
                        -- body₂ = .lam d_body b_body: subst gives .lam ..., IS a headform.
                        -- Composed derivation has height = n.
                        sorry
                    | @beta_L _ dom' body' arg' =>
                      -- h1b_g = beta_L : Sub (.app (.lam dom' body') arg') (body'.subst 0 arg')
                      -- hsrc_b : .app (.lam dom' body') arg' = .app g' d'
                      -- htgt_b : body'.subst 0 arg' = .app (.lam dom₂ body₂) c₂
                      --
                      -- So g' = .lam dom' body', d' = arg'.
                      -- body'.subst 0 d' = .app (.lam dom₂ body₂) c₂ (double-beta).
                      -- h1a' : Sub Γ₂ .top (.app (.lam dom' body') d')
                      -- hw1' : Wf Γ₂ (.app (.lam dom' body') d')
                      --
                      -- UNREACHABLE in any concrete derivation tree.
                      --
                      -- Proof sketch (informal):
                      -- This is the "double-beta" case: the substitution result
                      -- body'.subst 0 d' is itself a beta-redex (.app (.lam ..) ..).
                      -- We could compose into
                      --   trans h1a' (trans (htgt_b ▸ beta_L) beta_L hw_x) hw1'
                      --     : Sub .top (body₂.subst 0 c₂)
                      -- with height = 2 + h1a'.height + hw_x.height + hw1'.height.
                      -- Or call ihq on trans h1a' (htgt_b ▸ h1b_g) hw1' (height =
                      -- 1 + h1a' + hw1') but h1a' + hw1' < q gives composed ≤ q,
                      -- not < q.
                      --
                      -- Unreachability argument: identical to app_cong case. Any
                      -- Sub .top (.app (lam ..) ..) ultimately traces to beta_R
                      -- with reduct = .top, and the double-beta target's headform
                      -- condition circularly requires Sub .top headform.
                      --
                      -- Same Hutchins off-by-one: all compositions yield height ≤ n
                      -- (not < n), blocking every available IH.
                      sorry
                    | @beta_R _ dom' body' arg' =>
                      cases htgt_b
                      rw [hsrc_b] at hb_x
                      simp [Expr.IsHeadForm] at hb_x
              | bvar _ => exact Expr.noConfusion hsrc
              | lam _ _ _ => exact Expr.noConfusion hsrc
              | app_cong _ _ _ => exact Expr.noConfusion hsrc
              | beta_L => exact Expr.noConfusion hsrc
              | @beta_R _ dom' body' arg' =>
                have htgt' : dom' = dom₂ ∧ body' = body₂ ∧ arg' = c₂ := by
                  cases htgt; exact ⟨rfl, rfl, rfl⟩
                obtain ⟨hd', hb', ha'⟩ := htgt'; subst hd'; subst hb'; subst ha'
                rw [hsrc] at hb_x; simp [Expr.IsHeadForm] at hb_x
          | beta_R => simp [Expr.IsHeadForm] at hb2
    | bvar _ => exact Expr.noConfusion ha
    | lam _ _ _ => exact Expr.noConfusion ha
    | app_cong _ _ _ => exact Expr.noConfusion ha
    | beta_L => exact Expr.noConfusion ha
    | beta_R => simp [Expr.IsHeadForm] at hb

-- ============================================================================
-- Public API
-- ============================================================================

/-- Top cannot be a subtype of a function type. -/
theorem top_not_sub_lam {Γ : Ctx} {s t : Expr}
    (h : Sub Γ .top (.lam s t)) : False :=
  top_not_sub_headForm_aux h.height Γ .top (.lam s t) h (Nat.le_refl _) rfl trivial

/-- Top cannot be a subtype of a variable. -/
theorem top_not_sub_bvar {Γ : Ctx} {k : Nat}
    (h : Sub Γ .top (.bvar k)) : False :=
  top_not_sub_headForm_aux h.height Γ .top (.bvar k) h (Nat.le_refl _) rfl trivial

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

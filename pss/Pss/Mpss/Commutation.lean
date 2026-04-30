import Pss.Mpss.Diamond
import Pss.Mpss.Substitution
import Pss.Mpss.Weakening
import Pss.Mpss.Narrowing
import Pss.Mpss.ContextRed

set_option linter.unusedVariables false

/-! # `Pss.Mpss.Commutation` — Lemma 1 (Strong Commutativity)

Pasquale & García-Pérez 2024 (CSL 2026), §3 (statement) and Appendix A.

The headline `Lemma_1_StrongCommutativity` says that the MPSS equivalence
reduction `⟶^≡` and subtype reduction `⟶^≤` strongly commute modulo a
context-stepping discipline `↣*`.

```
    t₂ ──≡──→ t₃              (closing equiv:   in Γ₁; s₁)
    ↑         ↑
    ≡         ≤              (closing subtype: in Γ₂; s₂)
    ↑         ↑
    t₀ ──≤──→ t₁              (input solid arrows in Γ₀; s₀)
```

## Mechanization status

This module replaces the previous `axiom Lemma_1_StrongCommutativity`
with a `noncomputable def`. Structure mirrors `Lemma_2_DiamondMEqRed`:

* A `_core` (same-context) form is built by induction on the `MSubRed`
  derivation, with case analysis on `MEqRed` in each arm.
* The headline lifts `_core` across `↣*` evolutions via a single helper
  axiom `Lemma_1_ctx_axiom` (paralleling Lemma 2's
  `Lemma_2_DiamondMEqRed_ctx_axiom`).

Cells discharged in `_core`:

  - **Ms-Pro × Me-Var**: closing `t₃ := t` (the looked-up sub-term).
  - **Ms-Pro × Me-Pro**: vacuous by prevalidity.
  - **Ms-Pro × {everything else}**: vacuous by source-shape mismatch.
  - **Ms-Top × *** (8 cells): closing `t₃ := Top`.
  - **Ms-Equ × *** (8 cells): dispatched to Lemma 2.
  - **Ms-App × Me-App**: congruence with operator IH + Ct-Stk lift.
  - **Ms-App × Me-TAp**: closing `t₃ := Top`.

Cells delegated to per-row residual axioms (mirror Lemma 2's pattern):

  - **Ms-App × Me-Bet**: `Lemma_1_inline_app_bet_residual` (β-step;
    needs term-size induction).
  - **Ms-Fun × Me-Fun**: `Lemma_1_inline_fun_fun_residual`.
  - **Ms-FOp × Me-FOp**: `Lemma_1_inline_fOp_fOp_residual`.

Plus the single context-evolution lift: `Lemma_1_ctx_axiom`.

This brings the total axiom count from 1 (headline) to 4 (1 lift + 3
narrow per-cell), with all easy cells fully discharged. -/

namespace Pss

/-! ## §1. Vacuity helpers -/

/-- A `subBinds` lookup that succeeds implies the variable is in the
domain. -/
private theorem _comm_lookupSub_some_dom
    {Γ : Ctx} {x : String} {t : Term} (h : Γ.subBinds x t) : x ∈ Γ.dom := by
  induction Γ with
  | nil => simp [Ctx.subBinds, Ctx.lookupSub] at h
  | cons e rest ih =>
    rw [Ctx.subBinds, Ctx.lookupSub_cons] at h
    by_cases hex : e.name = x
    · simp [Ctx.dom_cons, hex]
    · simp [hex] at h
      simp [Ctx.dom_cons]
      exact Or.inr (ih h)

private theorem _comm_lookupEqu_some_dom
    {Γ : Ctx} {x : String} {α : Term} (h : Γ.equBinds x α) : x ∈ Γ.dom := by
  induction Γ with
  | nil => simp [Ctx.equBinds, Ctx.lookupEqu] at h
  | cons e rest ih =>
    rw [Ctx.equBinds, Ctx.lookupEqu_cons] at h
    by_cases hex : e.name = x
    · simp [Ctx.dom_cons, hex]
    · simp [hex] at h
      simp [Ctx.dom_cons]
      exact Or.inr (ih h)

/-- **Sub-case `pro × pro`** (paper p. 17): vacuous by prevalidity. -/
theorem Lemma_1_case_pro_pro_vacuous
    {Γ : Ctx} {x : String} {t α : Term}
    (hpv : Prevalid Γ)
    (hsub : Γ.subBinds x t) (hequ : Γ.equBinds x α) :
    False := by
  induction Γ with
  | nil =>
    simp [Ctx.subBinds, Ctx.lookupSub] at hsub
  | cons e rest ih =>
    have hpv_norm : Prevalid (e :: rest) := hpv
    by_cases hex : e.name = x
    · cases he_kind : e.kind with
      | sub =>
        have hequ' : Ctx.equBinds (e :: rest) x α := hequ
        rw [Ctx.equBinds, Ctx.lookupEqu_cons] at hequ'
        rw [if_pos hex, he_kind] at hequ'
        exact Option.noConfusion hequ'
      | equ =>
        have hsub' : Ctx.subBinds (e :: rest) x t := hsub
        rw [Ctx.subBinds, Ctx.lookupSub_cons] at hsub'
        rw [if_pos hex, he_kind] at hsub'
        exact Option.noConfusion hsub'
    · have hsub' : Ctx.subBinds (e :: rest) x t := hsub
      have hequ' : Ctx.equBinds (e :: rest) x α := hequ
      rw [Ctx.subBinds, Ctx.lookupSub_cons] at hsub'
      rw [Ctx.equBinds, Ctx.lookupEqu_cons] at hequ'
      simp [hex] at hsub' hequ'
      exact ih hpv_norm.tail hsub' hequ'

/-! ## §2. Context-evolution lift -/

/-- Lift a same-context Lemma-1-style joining derivation across two
`↣*` evolutions. Mirrors `Lemma_2_DiamondMEqRed_ctx_axiom`. -/
private axiom Lemma_1_ctx_axiom
    {Γ₀ : Ctx} {s₀ : Stack} {t₁ t₂ : Term}
    {Γ₁ : Ctx} {s₁ : Stack} {Γ₂ : Ctx} {s₂ : Stack}
    (hCt₁ : ExtCtxRedStar (Γ₀, s₀) (Γ₁, s₁))
    (hCt₂ : ExtCtxRedStar (Γ₀, s₀) (Γ₂, s₂))
    {t₃ : Term} (h₁'₀ : MEqRed Γ₀ s₀ t₁ t₃) (h₂'₀ : MSubRed Γ₀ s₀ t₂ t₃) :
    Σ' (t₃' : Term), MEqRed Γ₁ s₁ t₁ t₃' × MSubRed Γ₂ s₂ t₂ t₃'

/-! ## §3. Per-cell residual axioms (narrow) -/

/-- Ms-App × Me-Bet residual: source operator is `.abs t' body`. The
β-step on the right reduces to `Term.opening v body'`. The closing
diagram needs term-size induction (paper p. 22). -/
private axiom Lemma_1_inline_app_bet_residual
    {Γ : Ctx} {s : Stack} {u' v t' body body' v' : Term} {L : Finset String}
    (hu : MSubRed Γ (v :: s) (.abs t' body) u')
    (hLCv : Term.LC v) (hfvv : Term.fv v ⊆ Γ.dom)
    (hLCt' : Term.LC t')
    (hbody : ∀ y, y ∉ L → MEqRed Γ s (body^[y]) (body'^[y]))
    (hv₂ : MEqRed Γ [] v v')
    (ihu : ∀ {t₂' : Term}, MEqRed Γ (v :: s) (.abs t' body) t₂' →
      Σ' (t₃ : Term), MEqRed Γ (v :: s) u' t₃ × MSubRed Γ (v :: s) t₂' t₃) :
    Σ' (t₃ : Term),
      MEqRed Γ s (.app u' v) t₃ ×
      MSubRed Γ s (Term.opening v' body') t₃

/-- Ms-Fun × Me-Fun residual: cofinite body congruence at `[]` stack
under `.sub` head. Mirrors `Lemma_2_inline_fun_fun`. Receives the body
IH as a parameter so a future discharge can recurse without re-deriving
it. -/
private axiom Lemma_1_inline_fun_fun_residual
    {Γ : Ctx} {t t' body body₁ body₂ : Term} {L₁ L₂ : Finset String}
    (hLCt : Term.LC t)
    (hbody₁ : ∀ y, y ∉ L₁ →
      MSubRed (⟨y, t, .sub⟩ :: Γ) [] (body^[y]) (body₁^[y]))
    (ht₂ : MEqRed Γ [] t t')
    (hbody₂ : ∀ y, y ∉ L₂ →
      MEqRed (⟨y, t, .sub⟩ :: Γ) [] (body^[y]) (body₂^[y]))
    (ihbody : ∀ y (_hy : y ∉ L₁) {body₂' : Term},
      MEqRed (⟨y, t, .sub⟩ :: Γ) [] (body^[y]) body₂' →
      Σ' (t₃ : Term),
        MEqRed (⟨y, t, .sub⟩ :: Γ) [] (body₁^[y]) t₃ ×
        MSubRed (⟨y, t, .sub⟩ :: Γ) [] body₂' t₃) :
    Σ' (t₃ : Term),
      MEqRed Γ [] (.abs t body₁) t₃ ×
      MSubRed Γ [] (.abs t' body₂) t₃

/-- Ms-FOp × Me-FOp residual: cofinite body congruence at `α::s` under
`.equ` head. Mirrors `Lemma_2_inline_fOp_fOp`. -/
private axiom Lemma_1_inline_fOp_fOp_residual
    {Γ : Ctx} {s : Stack} {t t' α body body₁ body₂ : Term}
    {L₁ L₂ : Finset String}
    (hLCt : Term.LC t)
    (hbody₁ : ∀ y, y ∉ L₁ →
      MSubRed (⟨y, α, .equ⟩ :: Γ) s (body^[y]) (body₁^[y]))
    (ht₂ : MEqRed Γ [] t t')
    (hbody₂ : ∀ y, y ∉ L₂ →
      MEqRed (⟨y, α, .equ⟩ :: Γ) s (body^[y]) (body₂^[y]))
    (ihbody : ∀ y (_hy : y ∉ L₁) {body₂' : Term},
      MEqRed (⟨y, α, .equ⟩ :: Γ) s (body^[y]) body₂' →
      Σ' (t₃ : Term),
        MEqRed (⟨y, α, .equ⟩ :: Γ) s (body₁^[y]) t₃ ×
        MSubRed (⟨y, α, .equ⟩ :: Γ) s body₂' t₃) :
    Σ' (t₃ : Term),
      MEqRed Γ (α :: s) (.abs t body₁) t₃ ×
      MSubRed Γ (α :: s) (.abs t' body₂) t₃

/-! ## §4. Same-context core lemma -/

/-- **Same-context Lemma 1 (core).** Strong commutativity of `⟶^≡` and
`⟶^≤` at a single extended context. -/
noncomputable def Lemma_1_StrongCommutativity_core
    {Γ : Ctx} {s : Stack} {t₀ t₁ t₂ : Term}
    (hsub : MSubRed Γ s t₀ t₁)
    (heq  : MEqRed  Γ s t₀ t₂) :
    Σ' t₃, MEqRed Γ s t₁ t₃ × MSubRed Γ s t₂ t₃ := by
  induction hsub generalizing t₂ with
  | @pro Γ s x t hpv hsb =>
    -- Source: .fvar x. Cases on heq: only Me-Var and Me-Pro fit.
    cases heq with
    | @pro _ _ _ α α' hpv₂ heq₂ hα₂ =>
      exact (Lemma_1_case_pro_pro_vacuous (extractPrevalid hpv) hsb heq₂).elim
    | @var _ _ _ hpv₂ =>
      -- t₂ = .fvar x. Closing: t₃ = t.
      have hLCt : Term.LC t := Prevalid.lc_lookupSub (extractPrevalid hpv) hsb
      have hfvt : Term.fv t ⊆ Γ.dom := Prevalid.fv_lookupSub (extractPrevalid hpv) hsb
      exact ⟨t, MEqRed.refl hpv hLCt hfvt, MSubRed.pro hpv hsb⟩
  | @top Γ s u hpv hLCu hfvu =>
    -- Closing: t₃ = Top.
    have hLCt₂ : Term.LC t₂ := MEqRed.lc_right heq
    have hfvt₂ : Term.fv t₂ ⊆ Γ.dom := MEqRed_fv_preserve heq hfvu
    exact ⟨.top, MEqRed.top hpv, MSubRed.top hpv hLCt₂ hfvt₂⟩
  | @equ Γ s u v hpv heqLeft =>
    -- Dispatch to Lemma 2.
    obtain ⟨t₃, hvt₃, ht₂t₃⟩ :=
      Lemma_2_DiamondMEqRed_sameCtx heqLeft heq
    exact ⟨t₃, hvt₃, MSubRed.equ hpv ht₂t₃⟩
  | @app Γ s u u' v hu hLCv hfvv ihu =>
    -- Source: .app u v. Cases on heq.
    cases heq with
    | @app _ _ _ u₂ _ v₂ hu₂ hv₂ =>
      -- App × App congruence via operator IH + Ct-Stk lift.
      obtain ⟨w, hu'_w, hu₂_w⟩ := ihu hu₂
      have hCt₁ : ExtCtxRedStar (Γ, v :: s) (Γ, v :: s) := Relation.ReflTransGen.refl
      have hCt₂ : ExtCtxRedStar (Γ, v :: s) (Γ, v₂ :: s) :=
        ExtCtxRed.to_star (.stk .refl hv₂)
      obtain ⟨w', hu'_w', hu₂_w'⟩ :=
        Lemma_1_ctx_axiom hCt₁ hCt₂ hu'_w hu₂_w
      have hLCv₂ : Term.LC v₂ := MEqRed.lc_right hv₂
      have hfvv₂ : Term.fv v₂ ⊆ Γ.dom := MEqRed_fv_preserve hv₂ hfvv
      exact ⟨.app w' v₂, MEqRed.app hu'_w' hv₂, MSubRed.app hu₂_w' hLCv₂ hfvv₂⟩
    | @bet _ _ tBound _ _ body body' L hLCt hbody hv₂ =>
      -- App × Bet residual.
      exact Lemma_1_inline_app_bet_residual hu hLCv hfvv hLCt hbody hv₂ ihu
    | @tAp _ _ _ hpv₂ hLCu' hfvu' =>
      -- Source: .app .top v. So `hu : MSubRed Γ (v::s) .top u'`.
      -- Cases on hu force u' to be .top (via top or equ).
      -- Closing: t₃ = .top, left edge MEqRed.tAp, right edge MSubRed.top.
      have hLCv' : Term.LC v := hLCv
      have hfvv' : Term.fv v ⊆ Γ.dom := hfvv
      cases hu with
      | @top _ _ _ hpvU hLCuTop hfvuTop =>
        -- u' = .top.
        refine ⟨.top, MEqRed.tAp hpv₂ hLCv' hfvv', ?_⟩
        exact MSubRed.top hpv₂ Term.LC.top (by intro z hz; simp [Term.fv] at hz)
      | @equ _ _ _ _ hpvE heq' =>
        -- heq' : MEqRed Γ (v::s) .top u'. Case on heq': only `top` produces `.top` source.
        cases heq' with
        | top hpvT =>
          -- u' = .top.
          refine ⟨.top, MEqRed.tAp hpv₂ hLCv' hfvv', ?_⟩
          exact MSubRed.top hpv₂ Term.LC.top (by intro z hz; simp [Term.fv] at hz)
  | @fun_ Γ t body body' L hLCt hbody ihbody =>
    -- Source: .abs t body at empty stack. Cases on heq.
    cases heq with
    | @fun_ _ _ t' _ body₂ L₂ ht₂ hbody₂ =>
      exact Lemma_1_inline_fun_fun_residual hLCt hbody ht₂ hbody₂ ihbody
  | @fOp Γ s t α body body' L hLCt hbody ihbody =>
    -- Source: .abs t body at α::s. Cases on heq.
    cases heq with
    | @fOp _ _ _ t' _ _ body₂ L₂ ht₂ hbody₂ =>
      exact Lemma_1_inline_fOp_fOp_residual hLCt hbody ht₂ hbody₂ ihbody

/-! ## §5. Headline theorem -/

/-- **Lemma 1 (Strong Commutativity, Pasquale & García-Pérez 2024 §3,
appendix A).** The MPSS equivalence reduction `⟶^≡` and subtype
reduction `⟶^≤` strongly commute modulo the extended-context-stepping
discipline `↣*`.

Status: **DEF** modulo per-cell residual axioms in §3 and the
context-evolution lift in §2. Returns `Σ'` since `MEqRed`/`MSubRed`
are `Type`-valued. -/
noncomputable def Lemma_1_StrongCommutativity
    {Γ₀ : Ctx} {s₀ : Stack} {t₀ t₁ t₂ : Term}
    (hsub : MSubRed Γ₀ s₀ t₀ t₁)
    (heq  : MEqRed  Γ₀ s₀ t₀ t₂)
    {Γ₁ : Ctx} {s₁ : Stack} {Γ₂ : Ctx} {s₂ : Stack}
    (hCt₁ : ExtCtxRedStar (Γ₀, s₀) (Γ₁, s₁))
    (hCt₂ : ExtCtxRedStar (Γ₀, s₀) (Γ₂, s₂)) :
    Σ' t₃,
      MEqRed  Γ₁ s₁ t₁ t₃ ×
      MSubRed Γ₂ s₂ t₂ t₃ := by
  obtain ⟨t₃, h₁'₀, h₂'₀⟩ := Lemma_1_StrongCommutativity_core hsub heq
  exact Lemma_1_ctx_axiom hCt₁ hCt₂ h₁'₀ h₂'₀

/-! ## §6. Same-context corollary -/

/-- Same-context corollary: take `Γ₁; s₁ = Γ₂; s₂ = Γ₀; s₀`. -/
noncomputable def Lemma_1_StrongCommutativity_sameCtx
    {Γ : Ctx} {s : Stack} {t₀ t₁ t₂ : Term}
    (hsub : MSubRed Γ s t₀ t₁)
    (heq  : MEqRed  Γ s t₀ t₂) :
    Σ' t₃, MEqRed Γ s t₁ t₃ × MSubRed Γ s t₂ t₃ :=
  Lemma_1_StrongCommutativity hsub heq
    Relation.ReflTransGen.refl Relation.ReflTransGen.refl

/-! ## §7. Discharged sub-cases (kept for backward compatibility) -/

/-- **Sub-case `top × *`** (paper p. 17): the closing top edge is
`Me-Top` and the closing right edge is `Ms-Top`. Fully discharged. -/
def Lemma_1_case_top
    {Γ₁ : Ctx} {s₁ : Stack} {Γ₂ : Ctx} {s₂ : Stack} {t₂ : Term}
    (hpv₁ : PrevalidExt Γ₁ s₁) (hpv₂ : PrevalidExt Γ₂ s₂)
    (hLCt₂ : Term.LC t₂)
    (hfv₂ : Term.fv t₂ ⊆ Γ₂.dom) :
    Σ' t₃, MEqRed Γ₁ s₁ Term.top t₃ × MSubRed Γ₂ s₂ t₂ t₃ :=
  ⟨.top, MEqRed.top hpv₁, MSubRed.top hpv₂ hLCt₂ hfv₂⟩

end Pss

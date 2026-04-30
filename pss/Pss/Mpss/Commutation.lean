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

/-! ### Local helpers for cofinite body discharges

Mirrors the local helpers in `Pss.Mpss.Diamond` for `Lemma_2_inline_*`.
We re-prove `Term.fv_close_notMem` and a `Prevalid` extractor for
`MSubRed` here as `private` to keep this file self-contained.
For the `.equ`-head fOp residual we additionally build a local
`MSubRed.rename_equ_loc_C` helper that mirrors Diamond's
`MEqRed.rename_equ_loc` but for `MSubRed` (no `fv body ⊆ Γ.dom`
precondition). -/

/-- Closing a term over `x` removes `x` from its free-variable set. -/
private theorem _Term_fv_close_notMem_C (x : String) :
    ∀ (k : Nat) (e : Term), x ∉ Term.fv (Term.close_ k x e) := by
  intro k e
  induction e generalizing k with
  | bvar i => simp [Term.close_, Term.fv]
  | fvar y =>
    by_cases h : y = x
    · simp [Term.close_, h, Term.fv]
    · simp [Term.close_, h, Term.fv]; exact Ne.symm h
  | top => simp [Term.close_, Term.fv]
  | abs t b iht ihb =>
    simp [Term.close_, Term.fv, Finset.mem_union]
    exact ⟨iht k, ihb (k+1)⟩
  | app t u iht ihu =>
    simp [Term.close_, Term.fv, Finset.mem_union]
    exact ⟨iht k, ihu k⟩

/-- Local re-proof of the `Prevalid` extractor for `MEqRed`. -/
private theorem _extractPrevalidOfMEqRed_C {Γ : Ctx} {s : Stack} {u v : Term}
    (h : MEqRed Γ s u v) : Prevalid Γ := by
  induction h with
  | @pro Γ st x α α' hpv _ _ _ => exact extractPrevalid hpv
  | @bet Γ s t v v' body body' L _ _ _ _ ihv => exact ihv
  | @top Γ s hpv => exact extractPrevalid hpv
  | @app Γ s u u' v v' _ _ _ ihv => exact ihv
  | @var Γ s x hpv => exact extractPrevalid hpv
  | @fun_ Γ t t' body body' L _ _ iht _ => exact iht
  | @tAp Γ s u hpv _ _ => exact extractPrevalid hpv
  | @fOp Γ s t t' α body body' L _ _ iht _ => exact iht

/-- Local re-proof of the `Prevalid` extractor for `MSubRed`. -/
private theorem _extractPrevalidOfMSubRed_C {Γ : Ctx} {s : Stack} {u v : Term}
    (h : MSubRed Γ s u v) : Prevalid Γ := by
  induction h with
  | @pro Γ st x t hpv _ => exact extractPrevalid hpv
  | @top Γ st u hpv _ _ => exact extractPrevalid hpv
  | @equ Γ st u v hpv heq => exact extractPrevalid hpv
  | @app Γ st u u' v _ _ _ ihu => exact ihu
  | @fun_ Γ t body body' L _ _ ihbody =>
    classical
    obtain ⟨x, hx⟩ := Term.exists_fresh L
    exact (ihbody x hx).tail
  | @fOp Γ st t α body body' L _ _ ihbody =>
    classical
    obtain ⟨x, hx⟩ := Term.exists_fresh L
    exact (ihbody x hx).tail

/-- **Ms-Fun × Me-Fun residual** — DISCHARGED.
Strategy mirrors `Lemma_2_inline_fun_fun` (commit `009a666`). Pick a
fresh `y`, apply IHs at `y` to get a joining body `b`, close to
`body₃ := close_ 0 y b`. For arbitrary fresh `z`, lift the body
derivations from `y` to `z` via `MEqRed.rename_sub` and
`MSubRed.rename_sub` (both unconditional w.r.t. fv body), then on the
right side use `Lemma_24_NarrowingMSubRed` to swap the head annotation
`t → t'`. -/
private noncomputable def Lemma_1_inline_fun_fun_residual
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
      MSubRed Γ [] (.abs t' body₂) t₃ := by
  classical
  let Lall : Finset String :=
    L₁ ∪ L₂ ∪ Γ.dom ∪ Term.fv body ∪ Term.fv body₁ ∪ Term.fv body₂
  let y : String := Classical.choose (Term.exists_fresh Lall)
  have hyfresh : y ∉ Lall := Classical.choose_spec (Term.exists_fresh Lall)
  have hy_notin_L₁ : y ∉ L₁ := fun h => hyfresh
    (Finset.mem_union.mpr <| Or.inl <| Finset.mem_union.mpr <| Or.inl <|
     Finset.mem_union.mpr <| Or.inl <| Finset.mem_union.mpr <| Or.inl <|
     Finset.mem_union.mpr <| Or.inl h)
  have hy_notin_L₂ : y ∉ L₂ := fun h => hyfresh
    (Finset.mem_union.mpr <| Or.inl <| Finset.mem_union.mpr <| Or.inl <|
     Finset.mem_union.mpr <| Or.inl <| Finset.mem_union.mpr <| Or.inl <|
     Finset.mem_union.mpr <| Or.inr h)
  have hy_notin_Γ : y ∉ Γ.dom := fun h => hyfresh
    (Finset.mem_union.mpr <| Or.inl <| Finset.mem_union.mpr <| Or.inl <|
     Finset.mem_union.mpr <| Or.inl <| Finset.mem_union.mpr <| Or.inr h)
  have hy_notin_body₁ : y ∉ Term.fv body₁ := fun h => hyfresh
    (Finset.mem_union.mpr <| Or.inl <| Finset.mem_union.mpr <| Or.inr h)
  have hy_notin_body₂ : y ∉ Term.fv body₂ := fun h => hyfresh
    (Finset.mem_union.mpr <| Or.inr h)
  have hb₁_y : MSubRed (⟨y, t, .sub⟩ :: Γ) [] (body^[y]) (body₁^[y]) :=
    hbody₁ y hy_notin_L₁
  have hb₂_y : MEqRed (⟨y, t, .sub⟩ :: Γ) [] (body^[y]) (body₂^[y]) :=
    hbody₂ y hy_notin_L₂
  -- Apply ihbody on hb₂_y (an MEqRed input) — ihbody returns
  --   ⟨b, MEqRed body₁ → b, MSubRed body₂ → b⟩.
  obtain ⟨b, hb₁_to_b, hb₂_to_b⟩ := ihbody y hy_notin_L₁ hb₂_y
  let body₃ := Term.close_ 0 y b
  have hLCb : Term.LC b := MEqRed.lc_right hb₁_to_b
  have hb_eq : body₃^[y] = b := by
    show Term.open_ 0 (.fvar y) (Term.close_ 0 y b) = b
    exact Term.open_close hLCb 0 y
  have hy_notin_body₃ : y ∉ Term.fv body₃ :=
    _Term_fv_close_notMem_C y 0 b
  -- Extract Prevalid Γ and head annotation invariants.
  have hpv_y : Prevalid (⟨y, t, .sub⟩ :: Γ) :=
    _extractPrevalidOfMSubRed_C hb₁_y
  have hpvΓ : Prevalid Γ := hpv_y.tail
  have hLCt' : Term.LC t' := MEqRed.lc_right ht₂
  have hfvt : Term.fv t ⊆ Γ.dom := by
    cases hpv_y with
    | sub _ _ hfvt _ => exact hfvt
  have hfvt' : Term.fv t' ⊆ Γ.dom := MEqRed_fv_preserve ht₂ hfvt
  refine ⟨.abs t' body₃, ?_, ?_⟩
  · -- Left edge: MEqRed Γ [] (.abs t body₁) (.abs t' body₃) via Me-Fun.
    refine MEqRed.fun_ (Γ.dom ∪ Term.fv body₁ ∪ Term.fv body₃ ∪ {y}) ht₂ ?_
    intro z hzfresh
    have hz_notin_Γ : z ∉ Γ.dom := fun h => hzfresh
      (Finset.mem_union.mpr <| Or.inl <| Finset.mem_union.mpr <| Or.inl <|
       Finset.mem_union.mpr <| Or.inl h)
    have hz_notin_body₁ : z ∉ Term.fv body₁ := fun h => hzfresh
      (Finset.mem_union.mpr <| Or.inl <| Finset.mem_union.mpr <| Or.inl <|
       Finset.mem_union.mpr <| Or.inr h)
    have hz_notin_body₃ : z ∉ Term.fv body₃ := fun h => hzfresh
      (Finset.mem_union.mpr <| Or.inl <| Finset.mem_union.mpr <| Or.inr h)
    have h_at_y : MEqRed (⟨y, t, .sub⟩ :: Γ) [] (body₁^[y]) (body₃^[y]) := by
      rw [hb_eq]; exact hb₁_to_b
    -- Rename y → z via MEqRed.rename_sub. No fv body precondition needed.
    exact MEqRed.rename_sub hpvΓ hLCt hfvt hy_notin_Γ hz_notin_Γ
      hy_notin_body₁ hy_notin_body₃ (by intro α hα; cases hα) h_at_y
  · -- Right edge: MSubRed Γ [] (.abs t' body₂) (.abs t' body₃) via Ms-Fun.
    refine MSubRed.fun_ (Γ.dom ∪ Term.fv body₂ ∪ Term.fv body₃ ∪ {y}) hLCt' ?_
    intro z hzfresh
    have hz_notin_Γ : z ∉ Γ.dom := fun h => hzfresh
      (Finset.mem_union.mpr <| Or.inl <| Finset.mem_union.mpr <| Or.inl <|
       Finset.mem_union.mpr <| Or.inl h)
    have hz_notin_body₂ : z ∉ Term.fv body₂ := fun h => hzfresh
      (Finset.mem_union.mpr <| Or.inl <| Finset.mem_union.mpr <| Or.inl <|
       Finset.mem_union.mpr <| Or.inr h)
    have hz_notin_body₃ : z ∉ Term.fv body₃ := fun h => hzfresh
      (Finset.mem_union.mpr <| Or.inl <| Finset.mem_union.mpr <| Or.inr h)
    have h_at_y : MSubRed (⟨y, t, .sub⟩ :: Γ) [] (body₂^[y]) (body₃^[y]) := by
      rw [hb_eq]; exact hb₂_to_b
    -- Rename y → z via MSubRed.rename_sub (no fv body precondition).
    have h_at_z : MSubRed (⟨z, t, .sub⟩ :: Γ) [] (body₂^[z]) (body₃^[z]) :=
      MSubRed.rename_sub hpvΓ hLCt hfvt hy_notin_Γ hz_notin_Γ
        hy_notin_body₂ hy_notin_body₃ (by intro α hα; cases hα) h_at_y
    -- Narrow head annotation t → t' via Lemma_24_NarrowingMSubRed.
    exact Lemma_24_NarrowingMSubRed (Γ₂ := []) (Γ₁ := Γ) (x := z)
      (t := t') (t' := t) h_at_z hLCt' hfvt'

/-! #### Local renaming infrastructure for `.equ`-head no-fv-precondition

Mirrors Diamond's `MEqRed.rename_equ_loc` / `rename_equ_no_fv` plus an
analogous `MSubRed` version. These are needed for the fOp×fOp residual
because the source `body` of `MSubRed.fOp` does not satisfy
`fv body ⊆ Γ.dom`, blocking use of Renaming.lean's `MSubRed.rename_equ`. -/

/-- Local copy: `Prevalid` doubled-equ insertion (mirrors Diamond). -/
private theorem _Prevalid_insert_fresh_equ_mid_C
    {Γ₁ Γ₂ : Ctx} {y z : String} {α : Term}
    (hyz : y ≠ z)
    (hz_notin_Γ₁ : z ∉ Γ₁.dom)
    (hz_notin_Γ₂ : z ∉ Γ₂.dom)
    (hpv : Prevalid (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁)) :
    Prevalid (Γ₂ ++ ⟨y, α, .equ⟩ :: ⟨z, α, .equ⟩ :: Γ₁) := by
  classical
  have hpv_inner : Prevalid (⟨y, α, .equ⟩ :: Γ₁) := Prevalid.outer hpv
  cases hpv_inner with
  | equ hpvΓ₁ hy_notin_Γ₁ hfvα hLCα =>
    have hpv_z : Prevalid (⟨z, α, .equ⟩ :: Γ₁) :=
      Prevalid.equ hpvΓ₁ hz_notin_Γ₁ hfvα hLCα
    have hyz_zα : y ∉ Ctx.dom (⟨z, α, .equ⟩ :: Γ₁) := by
      rw [Ctx.dom_cons]
      intro hmem
      rcases Finset.mem_insert.mp hmem with hyz' | hyΓ
      · exact hyz hyz'
      · exact hy_notin_Γ₁ hyΓ
    have hfvα_z : Term.fv α ⊆ Ctx.dom (⟨z, α, .equ⟩ :: Γ₁) := by
      intro w hw; rw [Ctx.dom_cons]
      exact Finset.mem_insert_of_mem (hfvα hw)
    have hpv_yz : Prevalid (⟨y, α, .equ⟩ :: ⟨z, α, .equ⟩ :: Γ₁) :=
      Prevalid.equ hpv_z hyz_zα hfvα_z hLCα
    induction Γ₂ with
    | nil => simpa using hpv_yz
    | cons e rest ih =>
      have hpv'' : Prevalid (e :: (rest ++ ⟨y, α, .equ⟩ :: Γ₁)) := by
        simpa using hpv
      have hpv_rest : Prevalid (rest ++ ⟨y, α, .equ⟩ :: Γ₁) := hpv''.tail
      have hz_notin_rest : z ∉ Ctx.dom rest := by
        intro hmem; apply hz_notin_Γ₂
        rw [Ctx.dom_cons]; exact Finset.mem_insert_of_mem hmem
      have ih' := ih hz_notin_rest hpv_rest
      have he_notin : e.name ∉ Ctx.dom (rest ++ ⟨y, α, .equ⟩ :: Γ₁) := by
        cases hpv'' with
        | sub _ hen _ _ => exact hen
        | equ _ hen _ _ => exact hen
      have he_notin' : e.name ∉
          Ctx.dom (rest ++ ⟨y, α, .equ⟩ :: ⟨z, α, .equ⟩ :: Γ₁) := by
        intro hmem
        rw [Ctx.dom_append, Ctx.dom_cons, Ctx.dom_cons] at hmem
        rw [Ctx.dom_append, Ctx.dom_cons] at he_notin
        rcases Finset.mem_union.mp hmem with hr | htail
        · apply he_notin; exact Finset.mem_union.mpr (Or.inl hr)
        · rcases Finset.mem_insert.mp htail with hey | hrest_x
          · apply he_notin
            exact Finset.mem_union.mpr
              (Or.inr (Finset.mem_insert.mpr (Or.inl hey)))
          · rcases Finset.mem_insert.mp hrest_x with hez | hΓ
            · apply hz_notin_Γ₂
              rw [show z = e.name from hez.symm]
              exact Finset.mem_insert_self _ _
            · apply he_notin
              exact Finset.mem_union.mpr
                (Or.inr (Finset.mem_insert.mpr (Or.inr hΓ)))
      cases hpv'' with
      | @sub _ name u' _ _ hfve hlce =>
        have hfve' : Term.fv u' ⊆
            Ctx.dom (rest ++ ⟨y, α, .equ⟩ :: ⟨z, α, .equ⟩ :: Γ₁) := by
          intro w hw
          have hw' := hfve hw
          rw [Ctx.dom_append, Ctx.dom_cons] at hw'
          rw [Ctx.dom_append, Ctx.dom_cons, Ctx.dom_cons]
          rcases Finset.mem_union.mp hw' with hr | htail
          · exact Finset.mem_union.mpr (Or.inl hr)
          · rcases Finset.mem_insert.mp htail with hey | hΓ
            · exact Finset.mem_union.mpr
                (Or.inr (Finset.mem_insert.mpr (Or.inl hey)))
            · exact Finset.mem_union.mpr
                (Or.inr (Finset.mem_insert.mpr
                  (Or.inr (Finset.mem_insert.mpr (Or.inr hΓ)))))
        exact Prevalid.sub ih' he_notin' hfve' hlce
      | @equ _ name αe _ _ hfve hlce =>
        have hfve' : Term.fv αe ⊆
            Ctx.dom (rest ++ ⟨y, α, .equ⟩ :: ⟨z, α, .equ⟩ :: Γ₁) := by
          intro w hw
          have hw' := hfve hw
          rw [Ctx.dom_append, Ctx.dom_cons] at hw'
          rw [Ctx.dom_append, Ctx.dom_cons, Ctx.dom_cons]
          rcases Finset.mem_union.mp hw' with hr | htail
          · exact Finset.mem_union.mpr (Or.inl hr)
          · rcases Finset.mem_insert.mp htail with hey | hΓ
            · exact Finset.mem_union.mpr
                (Or.inr (Finset.mem_insert.mpr (Or.inl hey)))
            · exact Finset.mem_union.mpr
                (Or.inr (Finset.mem_insert.mpr
                  (Or.inr (Finset.mem_insert.mpr (Or.inr hΓ)))))
        exact Prevalid.equ ih' he_notin' hfve' hlce

/-- Local `PrevalidExt` analog. -/
private theorem _PrevalidExt_insert_fresh_equ_mid_C
    {Γ₁ Γ₂ : Ctx} {st : Stack} {y z : String} {α : Term}
    (hyz : y ≠ z)
    (hz_notin_Γ₁ : z ∉ Γ₁.dom)
    (hz_notin_Γ₂ : z ∉ Γ₂.dom)
    (hpv : PrevalidExt (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁) st) :
    PrevalidExt (Γ₂ ++ ⟨y, α, .equ⟩ :: ⟨z, α, .equ⟩ :: Γ₁) st := by
  induction st with
  | nil =>
    cases hpv with
    | nil hpvL =>
      exact PrevalidExt.nil
        (_Prevalid_insert_fresh_equ_mid_C hyz hz_notin_Γ₁ hz_notin_Γ₂ hpvL)
  | cons αs srest ihst =>
    cases hpv with
    | cons hpvr hLCαs hfvαs =>
      have ihst' := ihst hpvr
      have hfvαs' : Term.fv αs ⊆
          Ctx.dom (Γ₂ ++ ⟨y, α, .equ⟩ :: ⟨z, α, .equ⟩ :: Γ₁) := by
        intro w hw
        have hwΓ : w ∈ Ctx.dom (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁) := hfvαs hw
        rw [Ctx.dom_append, Ctx.dom_cons] at hwΓ
        rw [Ctx.dom_append, Ctx.dom_cons, Ctx.dom_cons]
        rcases Finset.mem_union.mp hwΓ with hΓ₂' | htail
        · exact Finset.mem_union.mpr (Or.inl hΓ₂')
        · rcases Finset.mem_insert.mp htail with hwy | hwΓ₁
          · exact Finset.mem_union.mpr
              (Or.inr (Finset.mem_insert.mpr (Or.inl hwy)))
          · exact Finset.mem_union.mpr
              (Or.inr (Finset.mem_insert.mpr
                (Or.inr (Finset.mem_insert.mpr (Or.inr hwΓ₁)))))
      exact PrevalidExt.cons ihst' hLCαs hfvαs'

/-- Local `lookupEqu_some_mem_dom` helper. -/
private lemma _lookupEqu_some_mem_dom_C {Γ : Ctx} {x : String} {α : Term}
    (h : Γ.lookupEqu x = some α) : x ∈ Γ.dom := by
  induction Γ with
  | nil => simp [Ctx.lookupEqu] at h
  | cons e rest ih =>
    rw [Ctx.lookupEqu_cons] at h
    by_cases hex : e.name = x
    · simp [Ctx.dom_cons, hex]
    · simp [hex] at h
      simp [Ctx.dom_cons]
      exact Or.inr (ih h)

/-- Local `lookupEqu_lift_middle` helper. -/
private theorem _lookupEqu_lift_middle_C
    {Γ₁ Γ₂ : Ctx} {yi z : String} {α β' : Term}
    (hyiz : yi ≠ z)
    (h : (Γ₂ ++ Γ₁).lookupEqu yi = some β') :
    (Γ₂ ++ ⟨z, α, .equ⟩ :: Γ₁).lookupEqu yi = some β' := by
  induction Γ₂ with
  | nil =>
    simpa [Ctx.lookupEqu_cons, Ne.symm hyiz] using h
  | cons e rest ih =>
    rw [List.cons_append, Ctx.lookupEqu_cons] at h ⊢
    by_cases hex : e.name = yi
    · simp [hex] at h ⊢
      cases hkind : e.kind with
      | sub => simp [hkind] at h
      | equ => simp [hkind] at h ⊢; exact h
    · simp [hex] at h ⊢
      exact ih h

/-- Local copy: `MEqRed` renaming under `.equ` head, non-doubled context,
no fv body precondition. Verbatim copy of Diamond's
`MEqRed.rename_equ_loc` (which is `private` to that file). -/
private noncomputable def _MEqRed_rename_equ_loc_C
    {Γ₁ Γ₂ : Ctx} {st : Stack} {y z : String} {α u u' : Term}
    (hyz : y ≠ z)
    (hz_notin_Γ₁ : z ∉ Γ₁.dom)
    (hz_notin_Γ₂ : z ∉ Γ₂.dom)
    (hy_notin_α : y ∉ Term.fv α)
    (h : MEqRed (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁) st u u') :
    MEqRed (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, α, .equ⟩ :: Γ₁)
      (Stack.subst y (.fvar z) st)
      (Term.subst y (.fvar z) u) (Term.subst y (.fvar z) u') := by
  classical
  have hok : SubstOk (⟨z, α, .equ⟩ :: Γ₁) (.fvar z) := by
    refine ⟨Term.LC.fvar z, ?_⟩
    intro w hw
    have hwz : w = z := by simpa [Term.fv] using hw
    subst hwz
    rw [Ctx.dom_cons]; exact Finset.mem_insert_self _ _
  generalize hΓ : (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁) = Γ at h
  induction h generalizing Γ₂ with
  | @pro Γ st' yi β β' hpv heq hβ ihβ =>
    subst hΓ
    have hpvL : Prevalid (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁) := extractPrevalid hpv
    have hpv_doubled :=
      _PrevalidExt_insert_fresh_equ_mid_C hyz hz_notin_Γ₁ hz_notin_Γ₂ hpv
    have hpv' : PrevalidExt (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, α, .equ⟩ :: Γ₁)
        (Stack.subst y (.fvar z) st') :=
      Lemma_28_SubstPreservesPrevalid (Γ₂ := Γ₂) (Γ₁ := ⟨z, α, .equ⟩ :: Γ₁)
        (x := y) (t := α) (s := .fvar z) (k := .equ) hpv_doubled hok
    by_cases hyiy : yi = y
    · have heq_y : (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁).equBinds y β := hyiy ▸ heq
      have hβα : β = α := equBinds_at_equ_head_unique hpvL heq_y
      have ihβ_app := ihβ (Γ₂ := Γ₂) hz_notin_Γ₂ rfl
      rw [hβα] at ihβ_app
      have hα_subst : Term.subst y (.fvar z) α = α := Term.subst_fresh hy_notin_α
      rw [hα_subst] at ihβ_app
      have hz_eqbinds :
          (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, α, .equ⟩ :: Γ₁).equBinds z α := by
        have hz_notin_subst_Γ₂ : z ∉ (Ctx.subst y (.fvar z) Γ₂).dom := by
          rw [Ctx.dom_subst]; exact hz_notin_Γ₂
        have hlk_tail : Ctx.lookupEqu (⟨z, α, .equ⟩ :: Γ₁) z = some α := by
          simp [Ctx.lookupEqu, Ctx.lookupEqu_cons]
        show Ctx.lookupEqu (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, α, .equ⟩ :: Γ₁) z = some α
        exact Ctx.lookupEqu_append_right (Ctx.subst y (.fvar z) Γ₂) _ z α
          hz_notin_subst_Γ₂ hlk_tail
      have hfvar_eq : Term.subst y (.fvar z) (.fvar yi) = .fvar z := by
        rw [hyiy]; simp [Term.subst]
      rw [hfvar_eq]
      exact MEqRed.pro hpv' hz_eqbinds ihβ_app
    · rw [Term.subst_fvar_ne hyiy]
      have heq_un : (Ctx.subst y (.fvar z) Γ₂ ++ Γ₁).equBinds yi
          (Term.subst y (.fvar z) β) :=
        equBinds_split_equ (s := .fvar z) hyiy hpvL heq
      have hyi_in_orig : yi ∈ (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁).dom :=
        _lookupEqu_some_mem_dom_C heq
      have hz_notin_orig : z ∉ (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁).dom := by
        rw [Ctx.dom_append, Ctx.dom_cons]
        intro hmem
        rcases Finset.mem_union.mp hmem with hΓ₂' | htail
        · exact hz_notin_Γ₂ hΓ₂'
        · rcases Finset.mem_insert.mp htail with hzy | hzΓ₁
          · exact hyz hzy.symm
          · exact hz_notin_Γ₁ hzΓ₁
      have hyiz : yi ≠ z := by
        intro hh; subst hh; exact hz_notin_orig hyi_in_orig
      have heq' : (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, α, .equ⟩ :: Γ₁).equBinds yi
          (Term.subst y (.fvar z) β) :=
        _lookupEqu_lift_middle_C hyiz heq_un
      exact MEqRed.pro hpv' heq' (ihβ (Γ₂ := Γ₂) hz_notin_Γ₂ rfl)
  | @bet Γ st' tBound v0 v0' bd bd' L hLCt hbody hv ihbody ihv =>
    subst hΓ
    have hLCfz : Term.LC (.fvar z) := Term.LC.fvar z
    have hsubst_open : Term.subst y (.fvar z) (Term.opening v0' bd') =
        Term.opening (Term.subst y (.fvar z) v0') (Term.subst y (.fvar z) bd') := by
      simp [Term.opening, Term.subst_open hLCfz]
    show MEqRed (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, α, .equ⟩ :: Γ₁)
      (Stack.subst y (.fvar z) st')
      (Term.subst y (.fvar z) (.app (.abs tBound bd) v0))
      (Term.subst y (.fvar z) (Term.opening v0' bd'))
    rw [hsubst_open]
    show MEqRed (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, α, .equ⟩ :: Γ₁)
      (Stack.subst y (.fvar z) st')
      (.app (.abs (Term.subst y (.fvar z) tBound) (Term.subst y (.fvar z) bd))
            (Term.subst y (.fvar z) v0))
      (Term.opening (Term.subst y (.fvar z) v0') (Term.subst y (.fvar z) bd'))
    refine MEqRed.bet (L ∪ {y}) (Term.subst_lc hLCfz hLCt) ?_ ?_
    · intro yfresh hyfresh
      simp [Finset.mem_union, Finset.mem_singleton] at hyfresh
      have hyfL : yfresh ∉ L := hyfresh.1
      have hyfy : yfresh ≠ y := hyfresh.2
      have ih_body := ihbody yfresh hyfL (Γ₂ := Γ₂) hz_notin_Γ₂ rfl
      rw [Term.subst_open_var (Ne.symm hyfy) hLCfz bd,
          Term.subst_open_var (Ne.symm hyfy) hLCfz bd'] at ih_body
      exact ih_body
    · have ihv' := ihv (Γ₂ := Γ₂) hz_notin_Γ₂ rfl
      simpa using ihv'
  | @top Γ st' hpv =>
    subst hΓ
    have hpv_doubled :=
      _PrevalidExt_insert_fresh_equ_mid_C hyz hz_notin_Γ₁ hz_notin_Γ₂ hpv
    have hpv' : PrevalidExt (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, α, .equ⟩ :: Γ₁)
        (Stack.subst y (.fvar z) st') :=
      Lemma_28_SubstPreservesPrevalid (Γ₂ := Γ₂) (Γ₁ := ⟨z, α, .equ⟩ :: Γ₁)
        (x := y) (t := α) (s := .fvar z) (k := .equ) hpv_doubled hok
    exact MEqRed.top hpv'
  | @app Γ st' u_ u_' v_ v_' hu hv ihu ihv =>
    subst hΓ
    have ihu' := ihu (Γ₂ := Γ₂) hz_notin_Γ₂ rfl
    have ihv' := ihv (Γ₂ := Γ₂) hz_notin_Γ₂ rfl
    simp at ihu'
    refine MEqRed.app ?_ ?_
    · exact ihu'
    · simpa using ihv'
  | @var Γ st' yi hpv =>
    subst hΓ
    have hpv_doubled :=
      _PrevalidExt_insert_fresh_equ_mid_C hyz hz_notin_Γ₁ hz_notin_Γ₂ hpv
    have hpv' : PrevalidExt (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, α, .equ⟩ :: Γ₁)
        (Stack.subst y (.fvar z) st') :=
      Lemma_28_SubstPreservesPrevalid (Γ₂ := Γ₂) (Γ₁ := ⟨z, α, .equ⟩ :: Γ₁)
        (x := y) (t := α) (s := .fvar z) (k := .equ) hpv_doubled hok
    by_cases hyiy : yi = y
    · have hsubst_eq : Term.subst y (.fvar z) (.fvar yi) = .fvar z := by
        rw [hyiy]; simp [Term.subst]
      rw [hsubst_eq]
      have hLCz : Term.LC (.fvar z) := Term.LC.fvar z
      have hfvz : Term.fv (.fvar z) ⊆
          Ctx.dom (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, α, .equ⟩ :: Γ₁) := by
        intro w hw
        have hwz : w = z := by simpa [Term.fv] using hw
        subst hwz
        rw [Ctx.dom_append, Ctx.dom_subst, Ctx.dom_cons]
        exact Finset.mem_union.mpr (Or.inr (Finset.mem_insert_self _ _))
      exact MEqRed.refl hpv' hLCz hfvz
    · rw [Term.subst_fvar_ne hyiy]
      exact MEqRed.var hpv'
  | @fun_ Γ tt tt' bd bd' L ht hbody iht ihbody =>
    subst hΓ
    show MEqRed (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, α, .equ⟩ :: Γ₁)
      (Stack.subst y (.fvar z) [])
      (.abs (Term.subst y (.fvar z) tt) (Term.subst y (.fvar z) bd))
      (.abs (Term.subst y (.fvar z) tt') (Term.subst y (.fvar z) bd'))
    refine MEqRed.fun_ (L ∪ {y} ∪ {z}) ?_ ?_
    · have iht' := iht (Γ₂ := Γ₂) hz_notin_Γ₂ rfl
      simpa using iht'
    · intro yfresh hyfresh
      simp only [Finset.mem_union, Finset.mem_singleton, not_or] at hyfresh
      obtain ⟨⟨hyfL, hyfy⟩, hyfz⟩ := hyfresh
      have hz_notin_Γ₂' : z ∉ Ctx.dom (⟨yfresh, tt, .sub⟩ :: Γ₂) := by
        rw [Ctx.dom_cons]
        intro hmem
        rcases Finset.mem_insert.mp hmem with hzy | hzΓ₂
        · exact hyfz hzy.symm
        · exact hz_notin_Γ₂ hzΓ₂
      have ih_body := ihbody yfresh hyfL (Γ₂ := ⟨yfresh, tt, .sub⟩ :: Γ₂)
        hz_notin_Γ₂' (by simp)
      have hLCfz : Term.LC (.fvar z) := Term.LC.fvar z
      rw [Term.subst_open_var (Ne.symm hyfy) hLCfz bd,
          Term.subst_open_var (Ne.symm hyfy) hLCfz bd'] at ih_body
      simpa [Ctx.subst, List.cons_append] using ih_body
  | @tAp Γ st' u_ hpv hLCu hfv =>
    subst hΓ
    have hpv_doubled :=
      _PrevalidExt_insert_fresh_equ_mid_C hyz hz_notin_Γ₁ hz_notin_Γ₂ hpv
    have hpv' : PrevalidExt (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, α, .equ⟩ :: Γ₁)
        (Stack.subst y (.fvar z) st') :=
      Lemma_28_SubstPreservesPrevalid (Γ₂ := Γ₂) (Γ₁ := ⟨z, α, .equ⟩ :: Γ₁)
        (x := y) (t := α) (s := .fvar z) (k := .equ) hpv_doubled hok
    have hLCu' : Term.LC (Term.subst y (.fvar z) u_) :=
      Term.subst_lc (Term.LC.fvar z) hLCu
    have hfv' :
        Term.fv (Term.subst y (.fvar z) u_) ⊆
          Ctx.dom (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, α, .equ⟩ :: Γ₁) := by
      intro w hw
      have hsub := Term.fv_subst_subset y (.fvar z) u_ hw
      rcases Finset.mem_union.mp hsub with hsd | hsd
      · rcases Finset.mem_sdiff.mp hsd with ⟨hwfv, hwne⟩
        have hwΓ : w ∈ Ctx.dom (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁) := hfv hwfv
        rw [Ctx.dom_append, Ctx.dom_cons] at hwΓ
        rw [Ctx.dom_append, Ctx.dom_subst, Ctx.dom_cons]
        rcases Finset.mem_union.mp hwΓ with hΓ₂' | htail
        · exact Finset.mem_union.mpr (Or.inl hΓ₂')
        · rcases Finset.mem_insert.mp htail with hwy | hwΓ₁
          · exact absurd hwy (fun hh => hwne (by simp [hh]))
          · apply Finset.mem_union.mpr
            right; exact Finset.mem_insert_of_mem hwΓ₁
      · have hwz : w = z := by simpa [Term.fv] using hsd
        subst hwz
        rw [Ctx.dom_append, Ctx.dom_subst, Ctx.dom_cons]
        apply Finset.mem_union.mpr
        right; exact Finset.mem_insert_self _ _
    show MEqRed (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, α, .equ⟩ :: Γ₁)
      (Stack.subst y (.fvar z) st')
      (Term.subst y (.fvar z) (.app .top u_)) (Term.subst y (.fvar z) .top)
    simp [Term.subst]
    exact MEqRed.tAp hpv' hLCu' hfv'
  | @fOp Γ st' tt tt' αi bd bd' L ht hbody iht ihbody =>
    subst hΓ
    show MEqRed (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, α, .equ⟩ :: Γ₁)
      (Stack.subst y (.fvar z) (αi :: st'))
      (.abs (Term.subst y (.fvar z) tt) (Term.subst y (.fvar z) bd))
      (.abs (Term.subst y (.fvar z) tt') (Term.subst y (.fvar z) bd'))
    rw [Stack.subst_cons]
    refine MEqRed.fOp (L ∪ {y} ∪ {z}) ?_ ?_
    · have iht' := iht (Γ₂ := Γ₂) hz_notin_Γ₂ rfl
      simpa using iht'
    · intro yfresh hyfresh
      simp only [Finset.mem_union, Finset.mem_singleton, not_or] at hyfresh
      obtain ⟨⟨hyfL, hyfy⟩, hyfz⟩ := hyfresh
      have hz_notin_Γ₂' : z ∉ Ctx.dom (⟨yfresh, αi, .equ⟩ :: Γ₂) := by
        rw [Ctx.dom_cons]
        intro hmem
        rcases Finset.mem_insert.mp hmem with hzy | hzΓ₂
        · exact hyfz hzy.symm
        · exact hz_notin_Γ₂ hzΓ₂
      have ih_body := ihbody yfresh hyfL (Γ₂ := ⟨yfresh, αi, .equ⟩ :: Γ₂)
        hz_notin_Γ₂' (by simp)
      have hLCfz : Term.LC (.fvar z) := Term.LC.fvar z
      rw [Term.subst_open_var (Ne.symm hyfy) hLCfz bd,
          Term.subst_open_var (Ne.symm hyfy) hLCfz bd'] at ih_body
      simpa [Ctx.subst, List.cons_append] using ih_body

/-- Local helper for the `Ms-Pro` arm of `_MSubRed_rename_equ_loc_C`:
lift `subBinds` past a freshly inserted `⟨z, α, .equ⟩` middle entry. -/
private theorem _lookupSub_lift_middle_equ_C
    {Γ₁ Γ₂ : Ctx} {yi z : String} {α t' : Term}
    (hyiz : yi ≠ z)
    (h : (Γ₂ ++ Γ₁).subBinds yi t') :
    (Γ₂ ++ ⟨z, α, .equ⟩ :: Γ₁).subBinds yi t' := by
  induction Γ₂ with
  | nil =>
    show Ctx.lookupSub (⟨z, α, .equ⟩ :: Γ₁) yi = some t'
    rw [Ctx.lookupSub_cons]
    simp [Ne.symm hyiz]
    exact h
  | cons e rest ih =>
    show Ctx.lookupSub (e :: (rest ++ ⟨z, α, .equ⟩ :: Γ₁)) yi = some t'
    have h' : Ctx.lookupSub (e :: (rest ++ Γ₁)) yi = some t' := h
    rw [Ctx.lookupSub_cons] at h' ⊢
    by_cases hex : e.name = yi
    · simp [hex] at h' ⊢
      cases hkind : e.kind with
      | sub => simp [hkind] at h' ⊢; exact h'
      | equ => simp [hkind] at h'
    · simp [hex] at h' ⊢
      exact ih h'

/-- Local copy: `MSubRed` renaming under `.equ` head, non-doubled context,
no fv body precondition. Mirrors `_MEqRed_rename_equ_loc_C` for MSubRed. -/
private noncomputable def _MSubRed_rename_equ_loc_C
    {Γ₁ Γ₂ : Ctx} {st : Stack} {y z : String} {α u u' : Term}
    (hyz : y ≠ z)
    (hz_notin_Γ₁ : z ∉ Γ₁.dom)
    (hz_notin_Γ₂ : z ∉ Γ₂.dom)
    (hy_notin_α : y ∉ Term.fv α)
    (h : MSubRed (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁) st u u') :
    MSubRed (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, α, .equ⟩ :: Γ₁)
      (Stack.subst y (.fvar z) st)
      (Term.subst y (.fvar z) u) (Term.subst y (.fvar z) u') := by
  classical
  have hok : SubstOk (⟨z, α, .equ⟩ :: Γ₁) (.fvar z) := by
    refine ⟨Term.LC.fvar z, ?_⟩
    intro w hw
    have hwz : w = z := by simpa [Term.fv] using hw
    subst hwz
    rw [Ctx.dom_cons]; exact Finset.mem_insert_self _ _
  generalize hΓ : (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁) = Γ at h
  induction h generalizing Γ₂ with
  | @pro Γ st' yi t' hpv hsb =>
    subst hΓ
    have hpvL : Prevalid (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁) := extractPrevalid hpv
    have hpv_doubled :=
      _PrevalidExt_insert_fresh_equ_mid_C hyz hz_notin_Γ₁ hz_notin_Γ₂ hpv
    have hpv' : PrevalidExt (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, α, .equ⟩ :: Γ₁)
        (Stack.subst y (.fvar z) st') :=
      Lemma_28_SubstPreservesPrevalid (Γ₂ := Γ₂) (Γ₁ := ⟨z, α, .equ⟩ :: Γ₁)
        (x := y) (t := α) (s := .fvar z) (k := .equ) hpv_doubled hok
    by_cases hyiy : yi = y
    · -- yi = y. Only y-entry is .equ, not .sub: contradiction.
      subst hyiy
      exact (subBinds_at_equ_head_impossible hpvL hsb).elim
    · rw [Term.subst_fvar_ne hyiy]
      have hsb_split : (Ctx.subst y (.fvar z) Γ₂ ++ Γ₁).subBinds yi
          (Term.subst y (.fvar z) t') :=
        subBinds_split_equ (s := .fvar z) hyiy hpvL hsb
      -- Now lift past the inserted ⟨z, α, .equ⟩.
      have hyi_in_orig : yi ∈ (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁).dom := by
        -- subBinds lookup implies in dom
        have hlk : (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁).lookupSub yi = some t' := hsb
        exact _comm_lookupSub_some_dom hsb
      have hz_notin_orig : z ∉ (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁).dom := by
        rw [Ctx.dom_append, Ctx.dom_cons]
        intro hmem
        rcases Finset.mem_union.mp hmem with hΓ₂' | htail
        · exact hz_notin_Γ₂ hΓ₂'
        · rcases Finset.mem_insert.mp htail with hzy | hzΓ₁
          · exact hyz hzy.symm
          · exact hz_notin_Γ₁ hzΓ₁
      have hyiz : yi ≠ z := by
        intro hh; subst hh; exact hz_notin_orig hyi_in_orig
      -- Lift the subBinds past the ⟨z, α, .equ⟩ head.
      have hsb' : (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, α, .equ⟩ :: Γ₁).subBinds yi
          (Term.subst y (.fvar z) t') :=
        _lookupSub_lift_middle_equ_C hyiz hsb_split
      exact MSubRed.pro hpv' hsb'
  | @top Γ st' u_ hpv hLCu hfv =>
    subst hΓ
    have hpv_doubled :=
      _PrevalidExt_insert_fresh_equ_mid_C hyz hz_notin_Γ₁ hz_notin_Γ₂ hpv
    have hpv' : PrevalidExt (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, α, .equ⟩ :: Γ₁)
        (Stack.subst y (.fvar z) st') :=
      Lemma_28_SubstPreservesPrevalid (Γ₂ := Γ₂) (Γ₁ := ⟨z, α, .equ⟩ :: Γ₁)
        (x := y) (t := α) (s := .fvar z) (k := .equ) hpv_doubled hok
    have hLCu' : Term.LC (Term.subst y (.fvar z) u_) :=
      Term.subst_lc (Term.LC.fvar z) hLCu
    have hfv' :
        Term.fv (Term.subst y (.fvar z) u_) ⊆
          Ctx.dom (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, α, .equ⟩ :: Γ₁) := by
      intro w hw
      have hsub := Term.fv_subst_subset y (.fvar z) u_ hw
      rcases Finset.mem_union.mp hsub with hsd | hsd
      · rcases Finset.mem_sdiff.mp hsd with ⟨hwfv, hwne⟩
        have hwΓ : w ∈ Ctx.dom (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁) := hfv hwfv
        rw [Ctx.dom_append, Ctx.dom_cons] at hwΓ
        rw [Ctx.dom_append, Ctx.dom_subst, Ctx.dom_cons]
        rcases Finset.mem_union.mp hwΓ with hΓ₂' | htail
        · exact Finset.mem_union.mpr (Or.inl hΓ₂')
        · rcases Finset.mem_insert.mp htail with hwy | hwΓ₁
          · exact absurd hwy (fun hh => hwne (by simp [hh]))
          · apply Finset.mem_union.mpr
            right; exact Finset.mem_insert_of_mem hwΓ₁
      · have hwz : w = z := by simpa [Term.fv] using hsd
        subst hwz
        rw [Ctx.dom_append, Ctx.dom_subst, Ctx.dom_cons]
        apply Finset.mem_union.mpr
        right; exact Finset.mem_insert_self _ _
    show MSubRed (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, α, .equ⟩ :: Γ₁)
      (Stack.subst y (.fvar z) st')
      (Term.subst y (.fvar z) u_) (Term.subst y (.fvar z) .top)
    simp [Term.subst]
    exact MSubRed.top hpv' hLCu' hfv'
  | @equ Γ st' u_ v_ hpv heq =>
    subst hΓ
    have hpv_doubled :=
      _PrevalidExt_insert_fresh_equ_mid_C hyz hz_notin_Γ₁ hz_notin_Γ₂ hpv
    have hpv' : PrevalidExt (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, α, .equ⟩ :: Γ₁)
        (Stack.subst y (.fvar z) st') :=
      Lemma_28_SubstPreservesPrevalid (Γ₂ := Γ₂) (Γ₁ := ⟨z, α, .equ⟩ :: Γ₁)
        (x := y) (t := α) (s := .fvar z) (k := .equ) hpv_doubled hok
    have heq' :=
      _MEqRed_rename_equ_loc_C (Γ₂ := Γ₂) hyz hz_notin_Γ₁ hz_notin_Γ₂ hy_notin_α heq
    exact MSubRed.equ hpv' heq'
  | @app Γ st' u_ u_' v_ hu hLCv hfvv ihu =>
    subst hΓ
    have ihu' := ihu (Γ₂ := Γ₂) hz_notin_Γ₂ rfl
    have hLCv' : Term.LC (Term.subst y (.fvar z) v_) :=
      Term.subst_lc (Term.LC.fvar z) hLCv
    have hfvv' :
        Term.fv (Term.subst y (.fvar z) v_) ⊆
          Ctx.dom (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, α, .equ⟩ :: Γ₁) := by
      intro w hw
      have hsub := Term.fv_subst_subset y (.fvar z) v_ hw
      rcases Finset.mem_union.mp hsub with hsd | hsd
      · rcases Finset.mem_sdiff.mp hsd with ⟨hwfv, hwne⟩
        have hwΓ : w ∈ Ctx.dom (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁) := hfvv hwfv
        rw [Ctx.dom_append, Ctx.dom_cons] at hwΓ
        rw [Ctx.dom_append, Ctx.dom_subst, Ctx.dom_cons]
        rcases Finset.mem_union.mp hwΓ with hΓ₂' | htail
        · exact Finset.mem_union.mpr (Or.inl hΓ₂')
        · rcases Finset.mem_insert.mp htail with hwy | hwΓ₁
          · exact absurd hwy (fun hh => hwne (by simp [hh]))
          · apply Finset.mem_union.mpr
            right; exact Finset.mem_insert_of_mem hwΓ₁
      · have hwz : w = z := by simpa [Term.fv] using hsd
        subst hwz
        rw [Ctx.dom_append, Ctx.dom_subst, Ctx.dom_cons]
        apply Finset.mem_union.mpr
        right; exact Finset.mem_insert_self _ _
    show MSubRed (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, α, .equ⟩ :: Γ₁)
      (Stack.subst y (.fvar z) st')
      (Term.subst y (.fvar z) (.app u_ v_)) (Term.subst y (.fvar z) (.app u_' v_))
    simp [Term.subst]
    refine MSubRed.app ?_ hLCv' hfvv'
    simpa using ihu'
  | @fun_ Γ tt bd bd' L hLCt hbody ihbody =>
    subst hΓ
    show MSubRed (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, α, .equ⟩ :: Γ₁)
      (Stack.subst y (.fvar z) [])
      (Term.subst y (.fvar z) (.abs tt bd)) (Term.subst y (.fvar z) (.abs tt bd'))
    simp [Term.subst]
    refine MSubRed.fun_ (L ∪ {y} ∪ {z}) (Term.subst_lc (Term.LC.fvar z) hLCt) ?_
    intro yfresh hyfresh
    simp only [Finset.mem_union, Finset.mem_singleton, not_or] at hyfresh
    obtain ⟨⟨hyfL, hyfy⟩, hyfz⟩ := hyfresh
    have hz_notin_Γ₂' : z ∉ Ctx.dom (⟨yfresh, tt, .sub⟩ :: Γ₂) := by
      rw [Ctx.dom_cons]
      intro hmem
      rcases Finset.mem_insert.mp hmem with hzy | hzΓ₂
      · exact hyfz hzy.symm
      · exact hz_notin_Γ₂ hzΓ₂
    have ih_body := ihbody yfresh hyfL (Γ₂ := ⟨yfresh, tt, .sub⟩ :: Γ₂)
      hz_notin_Γ₂' (by simp)
    rw [Term.subst_open_var (Ne.symm hyfy) (Term.LC.fvar z) bd,
        Term.subst_open_var (Ne.symm hyfy) (Term.LC.fvar z) bd'] at ih_body
    simpa [Ctx.subst, List.cons_append] using ih_body
  | @fOp Γ st' tt αi bd bd' L hLCt hbody ihbody =>
    subst hΓ
    show MSubRed (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, α, .equ⟩ :: Γ₁)
      (Stack.subst y (.fvar z) (αi :: st'))
      (Term.subst y (.fvar z) (.abs tt bd)) (Term.subst y (.fvar z) (.abs tt bd'))
    rw [Stack.subst_cons]
    simp [Term.subst]
    refine MSubRed.fOp (L ∪ {y} ∪ {z}) (Term.subst_lc (Term.LC.fvar z) hLCt) ?_
    intro yfresh hyfresh
    simp only [Finset.mem_union, Finset.mem_singleton, not_or] at hyfresh
    obtain ⟨⟨hyfL, hyfy⟩, hyfz⟩ := hyfresh
    have hz_notin_Γ₂' : z ∉ Ctx.dom (⟨yfresh, αi, .equ⟩ :: Γ₂) := by
      rw [Ctx.dom_cons]
      intro hmem
      rcases Finset.mem_insert.mp hmem with hzy | hzΓ₂
      · exact hyfz hzy.symm
      · exact hz_notin_Γ₂ hzΓ₂
    have ih_body := ihbody yfresh hyfL (Γ₂ := ⟨yfresh, αi, .equ⟩ :: Γ₂)
      hz_notin_Γ₂' (by simp)
    rw [Term.subst_open_var (Ne.symm hyfy) (Term.LC.fvar z) bd,
        Term.subst_open_var (Ne.symm hyfy) (Term.LC.fvar z) bd'] at ih_body
    simpa [Ctx.subst, List.cons_append] using ih_body

/-- Wrapper: rename `MSubRed` head `.equ`-binding's name `y → z` in
`⟨y, α, .equ⟩ :: Γ`, no fv body precondition. -/
private noncomputable def _MSubRed_rename_equ_no_fv_C
    {Γ : Ctx} {s : Stack} {body body' α : Term} {y z : String}
    (hyz : y ≠ z)
    (hy_notin_Γ : y ∉ Γ.dom) (hz_notin_Γ : z ∉ Γ.dom)
    (hy_notin_α : y ∉ Term.fv α)
    (hy_notin_body : y ∉ Term.fv body) (hy_notin_body' : y ∉ Term.fv body')
    (hy_notin_stack : ∀ β ∈ s, y ∉ Term.fv β)
    (h : MSubRed (⟨y, α, .equ⟩ :: Γ) s (body^[y]) (body'^[y])) :
    MSubRed (⟨z, α, .equ⟩ :: Γ) s (body^[z]) (body'^[z]) := by
  classical
  have hz_notin_empty : z ∉ Ctx.dom ([] : Ctx) := by simp [Ctx.dom]
  have h_in : MSubRed (([] : Ctx) ++ ⟨y, α, .equ⟩ :: Γ) s
      (body^[y]) (body'^[y]) := by simpa using h
  have h_subst :=
    _MSubRed_rename_equ_loc_C (Γ₂ := []) (Γ₁ := Γ) hyz hz_notin_Γ hz_notin_empty
      hy_notin_α h_in
  have hctx_eq :
      Ctx.subst y (.fvar z) ([] : Ctx) ++ (⟨z, α, .equ⟩ :: Γ) =
        ⟨z, α, .equ⟩ :: Γ := by simp
  have hstk_eq : Stack.subst y (.fvar z) s = s :=
    Stack.subst_fresh hy_notin_stack
  have hbody_eq : Term.subst y (.fvar z) (body^[y]) = body^[z] :=
    Term.subst_open_fresh hy_notin_body
  have hbody'_eq : Term.subst y (.fvar z) (body'^[y]) = body'^[z] :=
    Term.subst_open_fresh hy_notin_body'
  rw [hctx_eq, hstk_eq, hbody_eq, hbody'_eq] at h_subst
  exact h_subst

/-- Same wrapper for `MEqRed`. -/
private noncomputable def _MEqRed_rename_equ_no_fv_C
    {Γ : Ctx} {s : Stack} {body body' α : Term} {y z : String}
    (hyz : y ≠ z)
    (hy_notin_Γ : y ∉ Γ.dom) (hz_notin_Γ : z ∉ Γ.dom)
    (hy_notin_α : y ∉ Term.fv α)
    (hy_notin_body : y ∉ Term.fv body) (hy_notin_body' : y ∉ Term.fv body')
    (hy_notin_stack : ∀ β ∈ s, y ∉ Term.fv β)
    (h : MEqRed (⟨y, α, .equ⟩ :: Γ) s (body^[y]) (body'^[y])) :
    MEqRed (⟨z, α, .equ⟩ :: Γ) s (body^[z]) (body'^[z]) := by
  classical
  have hz_notin_empty : z ∉ Ctx.dom ([] : Ctx) := by simp [Ctx.dom]
  have h_in : MEqRed (([] : Ctx) ++ ⟨y, α, .equ⟩ :: Γ) s
      (body^[y]) (body'^[y]) := by simpa using h
  have h_subst :=
    _MEqRed_rename_equ_loc_C (Γ₂ := []) (Γ₁ := Γ) hyz hz_notin_Γ hz_notin_empty
      hy_notin_α h_in
  have hctx_eq :
      Ctx.subst y (.fvar z) ([] : Ctx) ++ (⟨z, α, .equ⟩ :: Γ) =
        ⟨z, α, .equ⟩ :: Γ := by simp
  have hstk_eq : Stack.subst y (.fvar z) s = s :=
    Stack.subst_fresh hy_notin_stack
  have hbody_eq : Term.subst y (.fvar z) (body^[y]) = body^[z] :=
    Term.subst_open_fresh hy_notin_body
  have hbody'_eq : Term.subst y (.fvar z) (body'^[y]) = body'^[z] :=
    Term.subst_open_fresh hy_notin_body'
  rw [hctx_eq, hstk_eq, hbody_eq, hbody'_eq] at h_subst
  exact h_subst

/-- **Ms-FOp × Me-FOp residual** — DISCHARGED.
Mirrors `Lemma_2_inline_fOp_fOp` (commit `009a666`). The body context
uses `⟨y, α, .equ⟩` (annotation `α` from stack head, unchanged). The
outer annotation `t → t'` reduces but no narrowing of the body context
is needed. Renaming uses local `_MEqRed_rename_equ_no_fv_C` /
`_MSubRed_rename_equ_no_fv_C` since `MEqRed.rename_equ` /
`MSubRed.rename_equ` from `Pss.Mpss.Renaming` require fv body
preconditions that `MSubRed.fOp`'s source body doesn't satisfy. -/
private noncomputable def Lemma_1_inline_fOp_fOp_residual
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
      MSubRed Γ (α :: s) (.abs t' body₂) t₃ := by
  classical
  -- Stack-fv union for stack-freshness.
  let stkFv : Finset String := s.foldr (fun α acc => Term.fv α ∪ acc) ∅
  let Lall : Finset String :=
    L₁ ∪ L₂ ∪ Γ.dom ∪ Term.fv α ∪ Term.fv body₁ ∪ Term.fv body₂ ∪ stkFv
  let y : String := Classical.choose (Term.exists_fresh Lall)
  have hyfresh : y ∉ Lall := Classical.choose_spec (Term.exists_fresh Lall)
  have hy_notin_L₁ : y ∉ L₁ := fun h => hyfresh
    (Finset.mem_union.mpr <| Or.inl <| Finset.mem_union.mpr <| Or.inl <|
     Finset.mem_union.mpr <| Or.inl <| Finset.mem_union.mpr <| Or.inl <|
     Finset.mem_union.mpr <| Or.inl <| Finset.mem_union.mpr <| Or.inl h)
  have hy_notin_L₂ : y ∉ L₂ := fun h => hyfresh
    (Finset.mem_union.mpr <| Or.inl <| Finset.mem_union.mpr <| Or.inl <|
     Finset.mem_union.mpr <| Or.inl <| Finset.mem_union.mpr <| Or.inl <|
     Finset.mem_union.mpr <| Or.inl <| Finset.mem_union.mpr <| Or.inr h)
  have hy_notin_Γ : y ∉ Γ.dom := fun h => hyfresh
    (Finset.mem_union.mpr <| Or.inl <| Finset.mem_union.mpr <| Or.inl <|
     Finset.mem_union.mpr <| Or.inl <| Finset.mem_union.mpr <| Or.inl <|
     Finset.mem_union.mpr <| Or.inr h)
  have hy_notin_α : y ∉ Term.fv α := fun h => hyfresh
    (Finset.mem_union.mpr <| Or.inl <| Finset.mem_union.mpr <| Or.inl <|
     Finset.mem_union.mpr <| Or.inl <| Finset.mem_union.mpr <| Or.inr h)
  have hy_notin_body₁ : y ∉ Term.fv body₁ := fun h => hyfresh
    (Finset.mem_union.mpr <| Or.inl <| Finset.mem_union.mpr <| Or.inl <|
     Finset.mem_union.mpr <| Or.inr h)
  have hy_notin_body₂ : y ∉ Term.fv body₂ := fun h => hyfresh
    (Finset.mem_union.mpr <| Or.inl <| Finset.mem_union.mpr <| Or.inr h)
  have hy_notin_stkFv : y ∉ stkFv := fun h => hyfresh
    (Finset.mem_union.mpr <| Or.inr h)
  have hfv_in_stkFv : ∀ {ss : Stack} (β : Term), β ∈ ss → Term.fv β ⊆
      ss.foldr (fun α acc => Term.fv α ∪ acc) ∅ := by
    intro ss β hβ w hw
    induction ss with
    | nil => exact (List.not_mem_nil _ hβ).elim
    | cons γ rest ih =>
      simp only [List.foldr_cons, Finset.mem_union]
      cases hβ with
      | head => exact Or.inl hw
      | tail _ hβ' => exact Or.inr (ih hβ')
  have hy_notin_stack : ∀ β ∈ s, y ∉ Term.fv β := by
    intro β hβ hyβ
    exact hy_notin_stkFv (hfv_in_stkFv β hβ hyβ)
  have hb₁_y : MSubRed (⟨y, α, .equ⟩ :: Γ) s (body^[y]) (body₁^[y]) :=
    hbody₁ y hy_notin_L₁
  have hb₂_y : MEqRed (⟨y, α, .equ⟩ :: Γ) s (body^[y]) (body₂^[y]) :=
    hbody₂ y hy_notin_L₂
  obtain ⟨b, hb₁_to_b, hb₂_to_b⟩ := ihbody y hy_notin_L₁ hb₂_y
  let body₃ := Term.close_ 0 y b
  have hLCb : Term.LC b := MEqRed.lc_right hb₁_to_b
  have hb_eq : body₃^[y] = b := by
    show Term.open_ 0 (.fvar y) (Term.close_ 0 y b) = b
    exact Term.open_close hLCb 0 y
  have hy_notin_body₃ : y ∉ Term.fv body₃ :=
    _Term_fv_close_notMem_C y 0 b
  -- Annotation IH joining is trivial here: t → t' on left, t' → t' on right (refl)
  -- but right side just reuses t' (Ms-FOp annotation invariant).
  have hLCt' : Term.LC t' := MEqRed.lc_right ht₂
  refine ⟨.abs t' body₃, ?_, ?_⟩
  · -- Left: MEqRed Γ (α :: s) (.abs t body₁) (.abs t' body₃) via Me-FOp.
    refine MEqRed.fOp (Γ.dom ∪ Term.fv body₁ ∪ Term.fv body₃ ∪ Term.fv α ∪ {y})
      ht₂ ?_
    intro z hzfresh
    have hz_notin_Γ : z ∉ Γ.dom := fun h => hzfresh
      (Finset.mem_union.mpr <| Or.inl <| Finset.mem_union.mpr <| Or.inl <|
       Finset.mem_union.mpr <| Or.inl <| Finset.mem_union.mpr <| Or.inl h)
    have hz_notin_body₁ : z ∉ Term.fv body₁ := fun h => hzfresh
      (Finset.mem_union.mpr <| Or.inl <| Finset.mem_union.mpr <| Or.inl <|
       Finset.mem_union.mpr <| Or.inl <| Finset.mem_union.mpr <| Or.inr h)
    have hz_notin_body₃ : z ∉ Term.fv body₃ := fun h => hzfresh
      (Finset.mem_union.mpr <| Or.inl <| Finset.mem_union.mpr <| Or.inl <|
       Finset.mem_union.mpr <| Or.inr h)
    have hyz : y ≠ z := by
      intro hyz; apply hzfresh
      apply Finset.mem_union.mpr; right
      simp [Finset.mem_singleton]; exact hyz.symm
    have h_at_y : MEqRed (⟨y, α, .equ⟩ :: Γ) s (body₁^[y]) (body₃^[y]) := by
      rw [hb_eq]; exact hb₁_to_b
    exact _MEqRed_rename_equ_no_fv_C hyz hy_notin_Γ hz_notin_Γ hy_notin_α
      hy_notin_body₁ hy_notin_body₃ hy_notin_stack h_at_y
  · -- Right: MSubRed Γ (α :: s) (.abs t' body₂) (.abs t' body₃) via Ms-FOp.
    refine MSubRed.fOp (Γ.dom ∪ Term.fv body₂ ∪ Term.fv body₃ ∪ Term.fv α ∪ {y})
      hLCt' ?_
    intro z hzfresh
    have hz_notin_Γ : z ∉ Γ.dom := fun h => hzfresh
      (Finset.mem_union.mpr <| Or.inl <| Finset.mem_union.mpr <| Or.inl <|
       Finset.mem_union.mpr <| Or.inl <| Finset.mem_union.mpr <| Or.inl h)
    have hz_notin_body₂ : z ∉ Term.fv body₂ := fun h => hzfresh
      (Finset.mem_union.mpr <| Or.inl <| Finset.mem_union.mpr <| Or.inl <|
       Finset.mem_union.mpr <| Or.inl <| Finset.mem_union.mpr <| Or.inr h)
    have hz_notin_body₃ : z ∉ Term.fv body₃ := fun h => hzfresh
      (Finset.mem_union.mpr <| Or.inl <| Finset.mem_union.mpr <| Or.inl <|
       Finset.mem_union.mpr <| Or.inr h)
    have hyz : y ≠ z := by
      intro hyz; apply hzfresh
      apply Finset.mem_union.mpr; right
      simp [Finset.mem_singleton]; exact hyz.symm
    have h_at_y : MSubRed (⟨y, α, .equ⟩ :: Γ) s (body₂^[y]) (body₃^[y]) := by
      rw [hb_eq]; exact hb₂_to_b
    exact _MSubRed_rename_equ_no_fv_C hyz hy_notin_Γ hz_notin_Γ hy_notin_α
      hy_notin_body₂ hy_notin_body₃ hy_notin_stack h_at_y

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

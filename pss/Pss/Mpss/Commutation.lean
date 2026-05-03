import Pss.Mpss.Diamond
import Pss.Mpss.Substitution
import Pss.Mpss.Weakening
import Pss.Mpss.Narrowing
import Pss.Mpss.Renaming
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
    needs term-size induction — see `AXIOMS.md` axiom #7).

Cells previously delegated, now discharged (commit `eba1284`):

  - **Ms-Fun × Me-Fun**: discharged via `MSubRed.rename_sub`
    + `Lemma_25_NarrowingMEqRed` (theorem, not axiom).
  - **Ms-FOp × Me-FOp**: discharged via the local
    `MSubRed.rename_equ` helper (theorem, not axiom).

Plus the single context-evolution lift: `Lemma_1_ctx_axiom`
(see `AXIOMS.md` axiom #6).

**Current axiom count: 2** (1 ctx-lift + 1 narrow per-cell), with all
non-β-residual cells fully discharged. The headline
`Lemma_1_StrongCommutativity` is a theorem, conditional on these two
private axioms plus the Lemma 2 / Narrowing infrastructure axioms it
inherits. -/

namespace Pss

/-! ## §1. Vacuity helpers -/

-- `_comm_lookupSub_some_dom` was extracted to `Pss.Mpss.Renaming` as the
-- public helper `_lookupSub_some_dom` (Phase A of `Lemma_24` discharge).

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

/-! ## §2. Context-evolution lift

### Discharge-attempt blocker (this session, 2026-04-29)

Same fundamental obstruction as `Lemma_2_DiamondMEqRed_ctx_axiom`.
Path-(b) "direct construction via existing infrastructure" was attempted
and bottoms out at the inductive (non-refl) arms of `↣*`:

* **refl/refl** is trivial (return `⟨t₃, h₁'₀, h₂'₀⟩`).
* **Ct-Stk single step** (the only non-trivial usage at the internal
  call site, App × App in `_core`): replacing stack head `v` with `v₂`
  where `MEqRed Γ [] v v₂`. The `Ms-FOp`/`Me-FOp` constructors pop the
  stack head INTO an `.equ`-binding `⟨x, v, .equ⟩`. Replacing `v` with
  `v₂` requires `.equ`-narrowing of `MSubRed`/`MEqRed` along an
  `MEqRed`-step on the bound term, which is itself confluence-shaped
  (the body's `Me-Pro` rule looks up `equBinds y α` and chains
  `α → ...`; replacing `α` with reduct `α'` requires the strong
  commutativity to re-thread the chain).
* **Ct-Ann single step** for a `.sub` annotation requires Lemma 24,
  still axiomatised. Honest discharge would need WSubM-transitivity
  from `Pss.Mpss.TransitivityElim`, which is downstream of this
  module (cycle-creating import).
* **Ct-Ann single step** for an `.equ` annotation: same shape as
  Ct-Stk (`.equ`-narrowing along an `MEqRed`-step).

### Both consumers actually pass reflexive chains

1. The headline is only consumed via
   `Lemma_1_StrongCommutativity_sameCtx` (passes `refl, refl`); see
   `Pss.Mpss.TransitivityElim` line 186.
2. The internal `_core` App × App arm passes `hCt₁ = refl` and
   `hCt₂ = .stk .refl hv₂` (a single Ct-Stk step on the stack head).

If the App × App arm could be re-engineered to avoid the stk-shift
(e.g. by reducing `v, v₂` to a common reduct via Lemma 2 first, then
joining at the common stack), `_ctx_axiom` could be eliminated
entirely. That refactor was not attempted in this session. -/

/-- Lift a same-context Lemma-1-style joining derivation across two
`↣*` evolutions. Mirrors `Lemma_2_DiamondMEqRed_ctx_axiom`.

**Why an axiom (precise blocker):** the inductive arms of `↣*`
(`Ct-Stk` for stack-head replacement, `Ct-Ann` for context-annotation
replacement) re-cast `MSubRed`/`MEqRed` derivations under an outer
`MEqRed`-step on the popped stack head or annotation. That re-casting
is itself confluence-shaped (e.g., the `.equ`-narrowing chain in
Me-Pro lookups), creating a recursive call into the strong-commutativity
machinery. The Ct-Ann arm for `.sub`-annotations would need
`Lemma_24_NarrowingMSubRed` (still axiomatized) plus WSubM-transitivity
from `TransitivityElim` — downstream of this module (cycle-creating
import).

**Discharge plan:** see `AXIOMS.md` axiom #6 (`Lemma_1_ctx_axiom`).
Both consumers of this axiom currently pass refl-or-near-refl chains;
the App × App `_core` arm specifically uses a single Ct-Stk step. A
refactor of App × App to reduce `v, v₂` to a common reduct via Lemma 2
*before* joining at the common stack would eliminate the internal use,
leaving only the (refl, refl) external use which is provable directly. -/
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
diagram needs term-size induction (paper p. 22).

**Why an axiom (precise blocker):** the β-reduction
`(.abs t body) v ⟶ body[v/x]` can grow the term, so structural
induction on the derivation tree does not terminate. The paper threads
a "no Me-Pro on `x`" side condition (`avoidsPro` Bool, see
`Pss/Mpss/AvoidsPro.lean`) that bounds the body's structure during the
opening, allowing a lex measure on `(Term.size t₀, avoidsPro-count)`.
Threading that side condition through `_core`'s induction scheme
requires either:

1. The standalone `avoidsPro_refl` axiom (already in `AvoidsPro.lean`)
   plumbed through;
2. A Type-LC refactor (lift `Term.LC` from `Prop` to `Type`) that
   eliminates `MEqRed.refl`'s `Classical.choice` opacity — see
   `PLAN.md`'s discharge-campaign "Option B".

**Discharge plan:** see `AXIOMS.md` axiom #7
(`Lemma_1_inline_app_bet_residual`). -/
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
private noncomputable def _extractPrevalidOfMEqRed_C {Γ : Ctx} {s : Stack} {u v : Term}
    (h : MEqRed Γ s u v) : Prevalid Γ := by
  induction h with
  | @pro Γ st x α α' hpv _ _ _ => exact extractPrevalid hpv
  | @bet Γ s t v v' body body' L _ _ _ _ _ ihv => exact ihv
  | @top Γ s hpv => exact extractPrevalid hpv
  | @app Γ s u u' v v' _ _ _ ihv => exact ihv
  | @var Γ s x hpv => exact extractPrevalid hpv
  | @fun_ Γ t t' body body' L _ _ _ iht _ => exact iht
  | @tAp Γ s u hpv _ _ => exact extractPrevalid hpv
  | @fOp Γ s t t' α body body' L _ _ _ iht _ => exact iht

/-- Local re-proof of the `Prevalid` extractor for `MSubRed`. -/
private noncomputable def _extractPrevalidOfMSubRed_C {Γ : Ctx} {s : Stack} {u v : Term}
    (h : MSubRed Γ s u v) : Prevalid Γ := by
  induction h with
  | @pro Γ st x t hpv _ => exact extractPrevalid hpv
  | @top Γ st u hpv _ _ => exact extractPrevalid hpv
  | @equ Γ st u v hpv heq => exact extractPrevalid hpv
  | @app Γ st u u' v _ _ _ ihu => exact ihu
  | @fun_ Γ t body body' L _ _ _ ihbody =>
    classical
    let x : String := Classical.choose (Term.exists_fresh L)
    have hx : x ∉ L := Classical.choose_spec (Term.exists_fresh L)
    exact (ihbody x hx).tail
  | @fOp Γ st t α body body' L _ _ _ ihbody =>
    classical
    let x : String := Classical.choose (Term.exists_fresh L)
    have hx : x ∉ L := Classical.choose_spec (Term.exists_fresh L)
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
    refine MEqRed.fun_ (Γ.dom ∪ Term.fv body₁ ∪ Term.fv body₃ ∪ {y}) ht₂ ?_ trivial
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
    refine MSubRed.fun_ (Γ.dom ∪ Term.fv body₂ ∪ Term.fv body₃ ∪ {y}) hLCt' ?_ trivial
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

/-! #### Renaming infrastructure now in `Pss.Mpss.Renaming`

The `_*_C` private copies (Prevalid/PrevalidExt insert-mid, lookup
lifters, and the `MEqRed`/`MSubRed` `rename_equ_loc` / `rename_equ_no_fv`
primitives) were extracted to `Pss.Mpss.Renaming` as public helpers
(prefixed `_` to avoid clashes with Diamond's `private` copies). See
Phase A of `Lemma_24_NarrowingMSubRed` discharge. -/

/-- **Ms-FOp × Me-FOp residual** — DISCHARGED.
Mirrors `Lemma_2_inline_fOp_fOp` (commit `009a666`). The body context
uses `⟨y, α, .equ⟩` (annotation `α` from stack head, unchanged). The
outer annotation `t → t'` reduces but no narrowing of the body context
is needed. Renaming uses `_MEqRed_rename_equ_no_fv` /
`_MSubRed_rename_equ_no_fv` from `Pss.Mpss.Renaming` since
`MEqRed.rename_equ` / `MSubRed.rename_equ` require fv body
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
      ht₂ ?_ trivial
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
    exact _MEqRed_rename_equ_no_fv hyz hy_notin_Γ hz_notin_Γ hy_notin_α
      hy_notin_body₁ hy_notin_body₃ hy_notin_stack h_at_y
  · -- Right: MSubRed Γ (α :: s) (.abs t' body₂) (.abs t' body₃) via Ms-FOp.
    refine MSubRed.fOp (Γ.dom ∪ Term.fv body₂ ∪ Term.fv body₃ ∪ Term.fv α ∪ {y})
      hLCt' ?_ trivial
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
    exact _MSubRed_rename_equ_no_fv hyz hy_notin_Γ hz_notin_Γ hy_notin_α
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
    | @bet _ _ tBound _ _ body body' L hLCt hbody _hUni₂ hv₂ =>
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
  | @fun_ Γ t body body' L hLCt hbody _hUni ihbody =>
    -- Source: .abs t body at empty stack. Cases on heq.
    cases heq with
    | @fun_ _ _ t' _ body₂ L₂ ht₂ hbody₂ _hUni₂ =>
      exact Lemma_1_inline_fun_fun_residual hLCt hbody ht₂ hbody₂ ihbody
  | @fOp Γ s t α body body' L hLCt hbody _hUni ihbody =>
    -- Source: .abs t body at α::s. Cases on heq.
    cases heq with
    | @fOp _ _ _ t' _ _ body₂ L₂ ht₂ hbody₂ _hUni₂ =>
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

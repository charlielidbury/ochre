import Pss.Mpss.DeBruijnTypeSafety
import Pss.Paper.Lemma_2_Diamond
import Pss.Paper.Lemma_2_DiamondClosure
import Pss.Paper.Lemma_2_NoPromotion
import Pss.Paper.Lemma_2_BundleProof
import Pss.Paper.Lemma_2_EqDiamondsWithMoreover
import Pss.Paper.Aux.EvolutionTransport
import Pss.Paper.Aux.CommutativityWeakening
import Pss.Paper.Investigation.Lemma_32_EquHead
import Pss.Paper.Investigation.Lemma_32_KindNarrowedAsymmetric

/-! # `Pss.Paper.Lemma_2_DiamondGeneral` — paper Lemma 2's general-context
diamond, paper-faithful AppBet/BetApp inlines, and `UniformEqDiamonds`
closure.

This file ships the **general-context Moreover-tracked diamond** that
mirrors paper Lemma 2 (Pasquale & García-Pérez 2024, p. 9:9 statement;
proof p. 9:21-25):

> *Statement.* Let `Γ_0; s_0` be an extended context. Let `t_0, t_1, t_2`
> be terms. If `Γ_0; s_0 ⊢ t_0 →ᵉᵠᵘ t_1` and `Γ_0; s_0 ⊢ t_0 →ᵉᵠᵘ t_2`,
> then for any extended contexts `Γ_1; s_1` and `Γ_2; s_2` such that
> `Γ_0; s_0 ↣ Γ_1; s_1` and `Γ_0; s_0 ↣ Γ_2; s_2`, there exists a term
> `t_3` such that `Γ_1; s_1 ⊢ t_1 →ᵉᵠᵘ t_3` and `Γ_2; s_2 ⊢ t_2 →ᵉᵠᵘ t_3`.
>
> Moreover (paper p. 9:9), for any variable `x`, if in the derivation
> `t_0 → t_1` there isn't an application of `Me-Pro` that makes a
> promotion of `x`, then in the derivation `t_2 → t_3` there won't be
> an application of `Me-Pro` that makes a promotion of `x`
> (respectively, `t_0 → t_2`'s `NP-x` propagates to `t_1 → t_3`).

The diamond is captured as `MoreoverDiamondGeneral` (asymmetric crossed
Moreover, paper-faithful), and `UniformMoreoverDiamondGeneral` is the
universal closure. Projection theorems deliver the plain general-context
diamond and the same-context `UniformEqDiamonds`.

## Strategy

The diamond is proved by **structural induction on `h_1`** with
case-split on `h_2`, dispatching to per-cell discharges. The cross-β
cases (App×Bet, Bet×App) are **inlined paper-faithfully** using
`Lemma_32_EquHead_proved_closed` + `cons_evolve` for body context
evolution. Non-cross-β cells (TopTop, VarVar, TApTAp, ProPro, ProVar,
AppTAp, FunFun, FOpFOp, BetBet, AppApp) invoke the per-cell theorems in
`Pss.Paper.Lemma_2_DiamondClosure`.

## Status

**Phase 1 (predicate definitions + trivial cells)** — shipped:
* `MoreoverDiamondGeneral` (Moreover-tracked general-context predicate,
  asymmetric crossed form per paper p. 9:9).
* `UniformMoreoverDiamondGeneral` (universal closure target).
* Projection `MoreoverDiamondGeneral.toLemma_2_DiamondMEqRed_Conclusion`.
* `UniformMoreoverDiamondGeneral.toUniformEqDiamonds` (`ctRefl/ctRefl`
  specialization).
* Trivial-cell Moreover discharges: TopTop, VarVar, TApTAp.

**Phase 2 (paper-faithful AppBet / BetApp inlines)** — shipped:
* `Lemma_2_PaperFaithful_AppBet`: cross-β App×Bet diamond conclusion
  using Lemma 32 EquHead + cons_evolve (paper p. 9:22-23).
* `Lemma_2_PaperFaithful_BetApp`: symmetric.

These inlines take body and arg IHs at `MoreoverDiamondGeneral` shape.
They produce the diamond conclusion (`∃ t₃, MEqRedJ ... ∧ MEqRedJ ...`)
**without the outer Moreover witness** — that is deferred to Phase 3
pending the structural NP-preservation lemmas for `Lemma 32 EquHead`
and `equ_to_sub_head_replace_NoPromotion`.

## Remaining work (Phase 3 onwards)

**Phase 3a — outer Moreover witnesses on AppBet/BetApp.**
Required structural lemmas:
* `Lemma_32_EquHead_PreservesNP_Payload`: NP-x of Lemma 32 EquHead
  output from body's NP-(x+1) and arg's NP-x. Proved by structural
  induction on the Lemma 32 EquHead `via_wall` construction.
* `MEqRed.equ_to_sub_head_replace_NoPromotion_preserves_NP`: NP-x
  preservation through the `.equ → .sub` head bridge (analogous to
  the existing `bridgeSubToEquHead_preserves_NP`). Proved by structural
  induction on `MEqRed.replaceAt_equ_to_sub_aux`.

**Phase 3b — non-cross-β Moreover-tracked cells.** ProPro, ProVar/VarPro,
AppApp (with `MEqRedOpStackHeadTransportPayload`), AppTAp/TApApp,
FunFun, FOpFOp, BetBet (with `Lemma_32_PreservesNP_Payload`). Most
mirror the same-context cells in `Lemma_2_BundleProof.lean` with
`ContextEvolution` evolutions added.

**Phase 3c — bundle recursion.** Structural induction on `h₁` then
case-split on `h₂`, dispatching to per-cell discharges. Termination
via `MEqRedDepth h₁ + MEqRedDepth h₂` (custom measure from
`Lemma_2_BundleProof.lean`).

**Phase 4 — `UniformEqDiamonds_proved` closure.** Projection of
`UniformMoreoverDiamondGeneral_proved` via `ctRefl/ctRefl`. Wires up
to discharge the `UniformEqDiamonds` residual in
`Pss/Mpss/DeBruijnTypeSafety.lean:22241`.

No `sorry`. No new axioms.
-/

namespace Pss
namespace DeBruijn
namespace Paper

open Investigation

/-! ## Predicate definitions -/

/-- **Paper Lemma 2 conclusion with Moreover NP-tracking** (asymmetric
crossed form, paper p. 9:9).

Given two equivalence-reduction steps from a common source at `Γ_0; s_0`,
plus any two evolved extended contexts `Γ_1; s_1` and `Γ_2; s_2`, this
delivers a common reduct `t_3` joined by `MEqRed` derivations `d_1, d_2`
on both sides, plus the asymmetric Moreover witness: `h_i.NP-x` of
either source crosses to `d_j.NP-x` of the OTHER output (`i ≠ j`).

The asymmetric crossed form mirrors the paper text exactly: NP of
*one* input propagates to the *other* output (the diagonal direction
through the diamond). -/
def MoreoverDiamondGeneral
    {Γ₀ : Ctx} {s₀ : Stack} {t₀ t₁ t₂ : Term}
    (h₁ : MEqRed Γ₀ s₀ t₀ t₁) (h₂ : MEqRed Γ₀ s₀ t₀ t₂) : Prop :=
  ∀ {Γ₁ s₁ Γ₂ s₂ : _},
    ContextEvolution Γ₀ s₀ Γ₁ s₁ →
    ContextEvolution Γ₀ s₀ Γ₂ s₂ →
    ∃ (t₃ : Term) (d₁ : MEqRed Γ₁ s₁ t₁ t₃) (d₂ : MEqRed Γ₂ s₂ t₂ t₃),
      ∀ (x : Nat),
        (h₁.NoPromotionOf x → d₂.NoPromotionOf x) ∧
        (h₂.NoPromotionOf x → d₁.NoPromotionOf x)

/-- Universal closure of the general-context Moreover diamond at every
extended context, over every source pair. -/
def UniformMoreoverDiamondGeneral : Prop :=
  ∀ {Γ₀ : Ctx} {s₀ : Stack} {t₀ t₁ t₂ : Term}
    (h₁ : MEqRed Γ₀ s₀ t₀ t₁) (h₂ : MEqRed Γ₀ s₀ t₀ t₂),
    MoreoverDiamondGeneral h₁ h₂

/-! ## Projections -/

/-- Drop the Moreover NP witness from a general-context Moreover
diamond, yielding the plain general-context diamond conclusion
(`Lemma_2_DiamondMEqRed_Conclusion`). -/
theorem MoreoverDiamondGeneral.toLemma_2_DiamondMEqRed_Conclusion
    {Γ₀ : Ctx} {s₀ : Stack} {t₀ t₁ t₂ : Term}
    {h₁ : MEqRed Γ₀ s₀ t₀ t₁} {h₂ : MEqRed Γ₀ s₀ t₀ t₂}
    (h : MoreoverDiamondGeneral h₁ h₂) :
    Lemma_2_DiamondMEqRed_Conclusion h₁ h₂ := by
  intro Γ₁ s₁ Γ₂ s₂ he₁ he₂
  obtain ⟨t₃, d₁, d₂, _⟩ := h he₁ he₂
  exact ⟨t₃, ⟨d₁⟩, ⟨d₂⟩⟩

/-- The general-context Moreover diamond's universal closure specializes
to the same-context `UniformEqDiamonds` via `ctRefl/ctRefl`. -/
theorem UniformMoreoverDiamondGeneral.toUniformEqDiamonds
    (h : UniformMoreoverDiamondGeneral) : UniformEqDiamonds := by
  intro Γ s t₀ t₁ t₂ h₁ h₂
  obtain ⟨t₃, d₁, d₂, _⟩ :=
    (h h₁ h₂) ContextEvolution.ctRefl ContextEvolution.ctRefl
  exact ⟨t₃, ⟨d₁⟩, ⟨d₂⟩⟩

/-! ## Trivial-cell discharges

The trivial source-shape cases (Me-Top × Me-Top, Me-Var × Me-Var,
Me-TAp × Me-TAp) close immediately by reflexivity/transport, with
trivial Moreover witnesses (the outputs are themselves `MEqRed`
identities or transport-images that admit `NoPromotionOf x` for all
`x`).

These take only the `MEqRedTransportAcrossEvolution` payload, but since
the trivial sources never use `Me-Pro` (the outputs are `.top` or
`.bvar i`), the NP witness for the outputs is trivially `True`. -/

/-- Me-Top × Me-Top: source `.top`, both targets `.top`, output `.top`
on both evolved contexts. Moreover witness trivial since neither source
uses `Me-Pro`. -/
theorem MoreoverDiamondGeneral_top_top {Γ₀ : Ctx} {s₀ : Stack}
    (hpv : PrevalidExt Γ₀ s₀) :
    MoreoverDiamondGeneral (MEqRed.top hpv) (MEqRed.top hpv) := by
  intro Γ₁ s₁ Γ₂ s₂ he₁ he₂
  have hpv₁ : PrevalidExt Γ₁ s₁ :=
    Classical.choice (he₁.preservesNonemptyPrevalidExt ⟨hpv⟩)
  have hpv₂ : PrevalidExt Γ₂ s₂ :=
    Classical.choice (he₂.preservesNonemptyPrevalidExt ⟨hpv⟩)
  refine ⟨.top, MEqRed.top hpv₁, MEqRed.top hpv₂, ?_⟩
  intro x
  exact ⟨fun _ => trivial, fun _ => trivial⟩

/-- Me-Var × Me-Var: source `.bvar i`, both targets `.bvar i`, output
`.bvar i` on both evolved contexts. Moreover trivial. -/
theorem MoreoverDiamondGeneral_var_var {Γ₀ : Ctx} {s₀ : Stack} {i : Nat}
    (hpv : PrevalidExt Γ₀ s₀) (hi : i < Γ₀.depth) :
    MoreoverDiamondGeneral (MEqRed.var hpv hi) (MEqRed.var hpv hi) := by
  intro Γ₁ s₁ Γ₂ s₂ he₁ he₂
  have hpv₁ : PrevalidExt Γ₁ s₁ :=
    Classical.choice (he₁.preservesNonemptyPrevalidExt ⟨hpv⟩)
  have hpv₂ : PrevalidExt Γ₂ s₂ :=
    Classical.choice (he₂.preservesNonemptyPrevalidExt ⟨hpv⟩)
  have hdepth₁ : Γ₀.depth = Γ₁.depth := he₁.preserves_ctx_depth
  have hdepth₂ : Γ₀.depth = Γ₂.depth := he₂.preserves_ctx_depth
  have hi₁ : i < Γ₁.depth := by rw [← hdepth₁]; exact hi
  have hi₂ : i < Γ₂.depth := by rw [← hdepth₂]; exact hi
  refine ⟨.bvar i, MEqRed.var hpv₁ hi₁, MEqRed.var hpv₂ hi₂, ?_⟩
  intro x
  exact ⟨fun _ => trivial, fun _ => trivial⟩

/-- Me-TAp × Me-TAp: source `.app .top u`, both targets `.top`, output
`.top` on both evolved contexts. Moreover trivial. -/
theorem MoreoverDiamondGeneral_tAp_tAp {Γ₀ : Ctx} {s₀ : Stack} {u : Term}
    (hpv : PrevalidExt Γ₀ s₀) (hu : Term.Scoped Γ₀.depth u) :
    MoreoverDiamondGeneral (MEqRed.tAp hpv hu) (MEqRed.tAp hpv hu) := by
  intro Γ₁ s₁ Γ₂ s₂ he₁ he₂
  have hpv₁ : PrevalidExt Γ₁ s₁ :=
    Classical.choice (he₁.preservesNonemptyPrevalidExt ⟨hpv⟩)
  have hpv₂ : PrevalidExt Γ₂ s₂ :=
    Classical.choice (he₂.preservesNonemptyPrevalidExt ⟨hpv⟩)
  refine ⟨.top, MEqRed.top hpv₁, MEqRed.top hpv₂, ?_⟩
  intro x
  exact ⟨fun _ => trivial, fun _ => trivial⟩

/-! ## Paper-faithful App × Bet inline (paper p. 9:22–23)

The cross-β case `Me-App × Me-Bet` is **the hardest** of paper Lemma 2's
cases. The paper's proof (p. 9:22–23) proceeds:

1. Me-App side decomposes via Me-FOp inversion:
   * Bound `Γ_0; nil ⊢ t_0 → t_1`.
   * Body `Γ_0, x ≡ v_0; s_0 ⊢ u_0 → u_1` (`.equ`-head, bound `v_0`).
   * Operand `Γ_0; nil ⊢ v_0 → v_1`.

2. Me-Bet side:
   * Body `Γ_0; s_0 ⊢ u_0 → u_2` (paper); de Bruijn: `.sub`-head bound `t_0`.
   * Operand `Γ_0; nil ⊢ v_0 → v_2`.

3. Lemma 19 (weakening) lifts Me-Bet body to `Γ_0, x ≡ v_0; s_0`. In
   de Bruijn this is the **`.sub → .equ` head bridge**
   `MEqRed.bridgeSubToEquHead` from `BundleProof.lean`.

4. Body IH at `Γ_0, x ≡ v_0; s_0` with evolutions:
   * LHS: `cons_evolve he₁ hArg₁` evolves bound `v_0 → v_1`.
   * RHS: `cons_evolve he₂ hArg₂` evolves bound `v_0 → v_2`.

   Body IH gives `u_3, d_1` at `{v_1,.equ}::Γ_1; shift 0 s_1` and
   `d_2` at `{v_2,.equ}::Γ_2; shift 0 s_2`, plus asymmetric Moreover
   `(h_2_bridged.NP-0 → d_1.NP-0)`.

5. Arg IH at `Γ_0; nil` gives `v_3, dArg_1, dArg_2`.

6. **LHS output** `Γ_1; s_1 ⊢ (λx≤t_1.u_1) v_1 → u_3[x\v_3]` via Me-Bet,
   bridging `d_1` from `{v_1,.equ}` to `{t_1,.sub}` via
   `equ_to_sub_head_replace_NoPromotion` using the Moreover-delivered
   `d_1.NP-0`.

7. **RHS output** `Γ_2; s_2 ⊢ u_2[x\v_2] → u_3[x\v_3]` via the paper's
   **`.equ`-head Lemma 32** (`Lemma_32_EquHead_proved_closed`) on
   `d_2 : MEqRed ({v_2,.equ}::Γ_2) ... u_2 u_3` with arg reduction
   `dArg_2 : MEqRed Γ_2 [] v_2 v_3`. The stack simplifies via
   `Stack.instantiate_shift_zero_id`.

This inline produces the diamond conclusion (existence of `t_3, d_1_out,
d_2_out`) without the outer Moreover witness. The outer Moreover requires
NP-propagation through `Me-Bet` (LHS) and `Lemma 32 EquHead` (RHS); both
will be handled at the full-bundle assembly with the
`Lemma_32_EquHead_PreservesNP_Payload` residual.

## Helper: `bridgeSubToEquHead.1` interface

The `.sub → .equ` head bridge from `Pss.Paper.Lemma_2_BundleProof`
returns `Σ' (h', _)` where `h'` is the bridged derivation. The `.1`
projection (the bridged derivation itself) inherits NP-0 from the
source's trivial NP-0 at `.sub`-head via `bridgeSubToEquHead_NP_zero`. -/

/-- Stack-simplification helper: `Stack.instantiate 0 v (Stack.shift 0 s) = s`.
Re-exported from `Lemma_2_BundleProof` via re-derivation, since the
original is `private`. Internal to this file. -/
private theorem Stack.instantiate_shift_zero_id_general (v : Term) (s : Stack) :
    Stack.instantiate 0 v (Stack.shift 0 s) = s := by
  have h := Stack.instantiate_shiftBy_zero_tail (n := 0) (v := v) (s := s)
  have hsBy_zero : ∀ (sx : Stack), Stack.shiftBy 0 0 sx = sx := by
    intro sx
    induction sx with
    | nil => rfl
    | cons α t ih =>
        show Term.shiftBy 0 0 α :: Stack.shiftBy 0 0 t = α :: t
        rw [Term.shiftBy_zero_id, ih]
  rw [hsBy_zero] at h
  simpa [Term.shiftBy_zero_id, Stack.shift] using h

/-- **Paper-faithful App × Bet diamond conclusion** (paper p. 9:22–23).

Given the inverted form of the Me-App source (Me-FOp body at
`.equ`-head bound `v_0`) and the Me-Bet source, plus body and arg
recursive IHs at the bundle's `MoreoverDiamondGeneral` shape — both
operating on the body sources after the **`.sub → .equ` head bridge**
— produces the AppBet diamond conclusion.

The body IH is invoked at `{v_0,.equ}::Γ_0; shift 0 s_0` with both
sources at the common `.equ`-head context. The arg IH is at `Γ_0; nil`.

The output drops the outer Moreover witness (deferred to the full
bundle assembly, conditional on NP-propagation through Lemma 32 EquHead). -/
theorem Lemma_2_PaperFaithful_AppBet
    {Γ₀ : Ctx} {s₀ : Stack}
    {t₀_inner u₀ u₁ u₂ v₀ v₁ v₂ t₁ : Term}
    (hT₁ : MEqRed Γ₀ [] t₀_inner t₁)
    (hv₀Scoped : Term.Scoped Γ₀.depth v₀)
    (hBody₁ : MEqRed ({bound := v₀, kind := .equ} :: Γ₀)
      (Stack.shift 0 s₀) u₀ u₁)
    (hArg₁ : MEqRed Γ₀ [] v₀ v₁)
    (ht₀_innerScoped : Term.Scoped Γ₀.depth t₀_inner)
    (hBody₂ : MEqRed ({bound := t₀_inner, kind := .sub} :: Γ₀)
      (Stack.shift 0 s₀) u₀ u₂)
    (hArg₂ : MEqRed Γ₀ [] v₀ v₂)
    -- Body IH operates on (hBody₁, bridged hBody₂). The asymmetric
    -- Moreover clause needed downstream: `h_2_bridged.NP-0 → d_1.NP-0`.
    (hBodyIH :
      MoreoverDiamondGeneral hBody₁
        (MEqRed.bridgeSubToEquHead hBody₂ hv₀Scoped).1)
    (hArgIH : MoreoverDiamondGeneral hArg₁ hArg₂)
    {Γ₁ s₁ Γ₂ s₂ : _}
    (he₁ : ContextEvolution Γ₀ s₀ Γ₁ s₁)
    (he₂ : ContextEvolution Γ₀ s₀ Γ₂ s₂) :
    ∃ (t₃ : Term),
      MEqRedJ Γ₁ s₁ (.app (.abs t₁ u₁) v₁) t₃ ∧
      MEqRedJ Γ₂ s₂ (Term.instantiate 0 v₂ u₂) t₃ := by
  -- Lift evolutions to body context via cons_evolve with the arg reductions.
  -- LHS body: {v_0,.equ}::Γ_0 evolves to {v_1,.equ}::Γ_1 via hArg₁ (Ct-Ann).
  -- RHS body: {v_0,.equ}::Γ_0 evolves to {v_2,.equ}::Γ_2 via hArg₂ (Ct-Ann).
  let heBody₁ : ContextEvolution ({bound := v₀, kind := .equ} :: Γ₀)
      (Stack.shift 0 s₀)
      ({bound := v₁, kind := .equ} :: Γ₁) (Stack.shift 0 s₁) :=
    ContextEvolution.cons_evolve he₁ hArg₁
  let heBody₂ : ContextEvolution ({bound := v₀, kind := .equ} :: Γ₀)
      (Stack.shift 0 s₀)
      ({bound := v₂, kind := .equ} :: Γ₂) (Stack.shift 0 s₂) :=
    ContextEvolution.cons_evolve he₂ hArg₂
  -- Body IH delivers u_3 at the common evolved body contexts with
  -- Moreover crossing NP-0 from h_2_bridged (= bridge.1, trivially NP-0)
  -- to d_1.
  obtain ⟨u_3, d_1, d_2, hMBody⟩ := hBodyIH heBody₁ heBody₂
  -- NP-0 on the bridged source (= bridge.1). The source `hBody₂` is at
  -- `.sub`-head, hence has trivial NP-0; the bridge preserves NP-0.
  have hBridged_NP_0 :
      (MEqRed.bridgeSubToEquHead hBody₂ hv₀Scoped).1.NoPromotionOf 0 :=
    bridgeSubToEquHead_NP_zero hBody₂ hv₀Scoped
  -- Moreover crossing: bridged.NP-0 → d_1.NP-0.
  have hd_1_NP_0 : d_1.NoPromotionOf 0 := (hMBody 0).2 hBridged_NP_0
  -- Arg IH at Γ_0; [] with evolutions stripped via Lemma 36.
  have hArgEv₁ : ContextEvolution Γ₀ [] Γ₁ [] :=
    he₁.Lemma_36_CommutativityContextWeakening
  have hArgEv₂ : ContextEvolution Γ₀ [] Γ₂ [] :=
    he₂.Lemma_36_CommutativityContextWeakening
  obtain ⟨v_3, dArg_1, dArg_2, _⟩ := hArgIH hArgEv₁ hArgEv₂
  -- Scoping witnesses at evolved contexts.
  have ht₁Scoped : Term.Scoped Γ₁.depth t₁ := by
    have h : Term.Scoped Γ₀.depth t₁ := hT₁.scoped_right
    rw [he₁.preserves_ctx_depth] at h
    exact h
  have hv₂Scoped₂ : Term.Scoped Γ₂.depth v₂ := dArg_2.scoped_left
  have hv_3Scoped₂ : Term.Scoped Γ₂.depth v_3 := dArg_2.scoped_right
  -- LHS output: build via Me-Bet from `d_1` bridged to `.sub`-head bound `t_1`.
  let d_1_bridged : MEqRed ({bound := t₁, kind := .sub} :: Γ₁)
      (Stack.shift 0 s₁) u₁ u_3 :=
    d_1.equ_to_sub_head_replace_NoPromotion hd_1_NP_0 ht₁Scoped
  let hLHS_out : MEqRed Γ₁ s₁
      (.app (.abs t₁ u₁) v₁) (Term.instantiate 0 v_3 u_3) :=
    MEqRed.bet ht₁Scoped d_1_bridged dArg_1
  -- RHS output: build via Lemma 32 EquHead on `d_2` at `{v_2,.equ}::Γ_2`.
  -- Lemma 32 EquHead with arg = v_2, arg' = v_3:
  --   `MEqRed Γ_2 (Stack.instantiate 0 v_2 (shift 0 s_2))
  --              (instantiate 0 v_2 u_2) (instantiate 0 v_3 u_3)`.
  -- Simplify stack: Stack.instantiate 0 v_2 (shift 0 s_2) = s_2.
  have hRHS_pre :=
    Lemma_32_EquHead_proved_closed hv₂Scoped₂ hv_3Scoped₂ dArg_2 d_2
  have hStackSimp :
      Stack.instantiate 0 v₂ (Stack.shift 0 s₂) = s₂ :=
    Stack.instantiate_shift_zero_id_general v₂ s₂
  rw [hStackSimp] at hRHS_pre
  refine ⟨Term.instantiate 0 v_3 u_3, ⟨hLHS_out⟩, ⟨hRHS_pre⟩⟩

/-! ## Paper-faithful Bet × App inline (paper p. 9:22-23 mirrored)

Symmetric to App × Bet: LHS does Me-Bet, RHS does Me-App. The body
sources are swapped, but the structure is identical. -/

/-- **Paper-faithful Bet × App diamond conclusion** (paper p. 9:22-23
mirrored). Symmetric to `Lemma_2_PaperFaithful_AppBet`. -/
theorem Lemma_2_PaperFaithful_BetApp
    {Γ₀ : Ctx} {s₀ : Stack}
    {t₀_inner u₀ u₁ u₂ v₀ v₁ v₂ t₂ : Term}
    (ht₀_innerScoped : Term.Scoped Γ₀.depth t₀_inner)
    (hBody₁ : MEqRed ({bound := t₀_inner, kind := .sub} :: Γ₀)
      (Stack.shift 0 s₀) u₀ u₁)
    (hArg₁ : MEqRed Γ₀ [] v₀ v₁)
    (hT₂ : MEqRed Γ₀ [] t₀_inner t₂)
    (hv₀Scoped : Term.Scoped Γ₀.depth v₀)
    (hBody₂ : MEqRed ({bound := v₀, kind := .equ} :: Γ₀)
      (Stack.shift 0 s₀) u₀ u₂)
    (hArg₂ : MEqRed Γ₀ [] v₀ v₂)
    -- Body IH operates on (bridged hBody₁, hBody₂).
    (hBodyIH :
      MoreoverDiamondGeneral
        (MEqRed.bridgeSubToEquHead hBody₁ hv₀Scoped).1
        hBody₂)
    (hArgIH : MoreoverDiamondGeneral hArg₁ hArg₂)
    {Γ₁ s₁ Γ₂ s₂ : _}
    (he₁ : ContextEvolution Γ₀ s₀ Γ₁ s₁)
    (he₂ : ContextEvolution Γ₀ s₀ Γ₂ s₂) :
    ∃ (t₃ : Term),
      MEqRedJ Γ₁ s₁ (Term.instantiate 0 v₁ u₁) t₃ ∧
      MEqRedJ Γ₂ s₂ (.app (.abs t₂ u₂) v₂) t₃ := by
  let heBody₁ : ContextEvolution ({bound := v₀, kind := .equ} :: Γ₀)
      (Stack.shift 0 s₀)
      ({bound := v₁, kind := .equ} :: Γ₁) (Stack.shift 0 s₁) :=
    ContextEvolution.cons_evolve he₁ hArg₁
  let heBody₂ : ContextEvolution ({bound := v₀, kind := .equ} :: Γ₀)
      (Stack.shift 0 s₀)
      ({bound := v₂, kind := .equ} :: Γ₂) (Stack.shift 0 s₂) :=
    ContextEvolution.cons_evolve he₂ hArg₂
  obtain ⟨u_3, d_1, d_2, hMBody⟩ := hBodyIH heBody₁ heBody₂
  -- NP-0 on the bridged LHS source (= bridge.1).
  have hBridged_NP_0 :
      (MEqRed.bridgeSubToEquHead hBody₁ hv₀Scoped).1.NoPromotionOf 0 :=
    bridgeSubToEquHead_NP_zero hBody₁ hv₀Scoped
  -- Asymmetric Moreover crossing: bridged_h_1.NP-0 → d_2.NP-0.
  have hd_2_NP_0 : d_2.NoPromotionOf 0 := (hMBody 0).1 hBridged_NP_0
  -- Arg IH.
  have hArgEv₁ : ContextEvolution Γ₀ [] Γ₁ [] :=
    he₁.Lemma_36_CommutativityContextWeakening
  have hArgEv₂ : ContextEvolution Γ₀ [] Γ₂ [] :=
    he₂.Lemma_36_CommutativityContextWeakening
  obtain ⟨v_3, dArg_1, dArg_2, _⟩ := hArgIH hArgEv₁ hArgEv₂
  -- Scoping witnesses.
  have ht₂Scoped : Term.Scoped Γ₂.depth t₂ := by
    have h : Term.Scoped Γ₀.depth t₂ := hT₂.scoped_right
    rw [he₂.preserves_ctx_depth] at h
    exact h
  have hv₁Scoped₁ : Term.Scoped Γ₁.depth v₁ := dArg_1.scoped_left
  have hv_3Scoped₁ : Term.Scoped Γ₁.depth v_3 := dArg_1.scoped_right
  -- LHS output: Lemma 32 EquHead on `d_1` at `{v_1,.equ}::Γ_1`.
  have hLHS_pre :=
    Lemma_32_EquHead_proved_closed hv₁Scoped₁ hv_3Scoped₁ dArg_1 d_1
  have hStackSimp :
      Stack.instantiate 0 v₁ (Stack.shift 0 s₁) = s₁ :=
    Stack.instantiate_shift_zero_id_general v₁ s₁
  rw [hStackSimp] at hLHS_pre
  -- RHS output: Me-Bet using `d_2` bridged to `.sub`-head bound `t_2`.
  let d_2_bridged : MEqRed ({bound := t₂, kind := .sub} :: Γ₂)
      (Stack.shift 0 s₂) u₂ u_3 :=
    d_2.equ_to_sub_head_replace_NoPromotion hd_2_NP_0 ht₂Scoped
  let hRHS_out : MEqRed Γ₂ s₂
      (.app (.abs t₂ u₂) v₂) (Term.instantiate 0 v_3 u_3) :=
    MEqRed.bet ht₂Scoped d_2_bridged dArg_2
  refine ⟨Term.instantiate 0 v_3 u_3, ⟨hLHS_pre⟩, ⟨hRHS_out⟩⟩

/-! ## Phase 3a — Lemma 32 EquHead NP-preservation payload

The cross-β AppBet/BetApp outer Moreover witness requires NP-preservation
through Lemma 32 EquHead's substitution: given a body `MEqRed
({arg,.equ}::Γ) s lhs rhs` with NP-(x+1), and an arg reduction `MEqRed Γ
[] arg arg'` with NP-x, the substituted output `MEqRed Γ
(Stack.instantiate 0 arg s) (Term.instantiate 0 arg lhs) (Term.instantiate
0 arg' rhs)` has NP-x.

This is the `.equ`-head analog of the existing `Lemma_32_PreservesNP_Payload`
(which is for the `.sub`-head, kind-narrowed form used by BetBet). Like its
`.sub`-head sibling, this payload is structurally provable by induction on
`Lemma_32_EquHead_via_wall`'s construction; the proof effort is comparable
to `Lemma_32_PreservesNP_Payload` and is deferred to a dedicated dispatch.

The bundle's AppBet/BetApp cells take this payload as a residual; downstream
the bundle is conditional on it (mirroring the existing pattern). -/

/-- **Lemma 32 EquHead NP-preservation payload.**

NP-x of `Lemma_32_EquHead_proved_closed` output, given NP-(x+1) of body
input and NP-x of arg input. Paper-faithful to the `.equ`-head substitution
case. Companion to `Lemma_32_PreservesNP_Payload` (`.sub`-head form). -/
def Lemma_32_EquHead_PreservesNP_Payload : Prop :=
  ∀ {Γ : Ctx} {arg arg' lhs rhs : Term} {s : Stack}
    (hArgScoped : Term.Scoped Γ.depth arg)
    (hArg'Scoped : Term.Scoped Γ.depth arg')
    (hArgArg' : MEqRed Γ [] arg arg')
    (h : MEqRed ({bound := arg, kind := .equ} :: Γ) s lhs rhs)
    (x : Nat),
    h.NoPromotionOf (x + 1) →
    hArgArg'.NoPromotionOf x →
    (Lemma_32_EquHead_proved_closed hArgScoped hArg'Scoped hArgArg' h).NoPromotionOf x

/-! ## Phase 3a — strengthened AppBet/BetApp with outer Moreover

The strengthened paper-faithful inlines produce the full
`MoreoverDiamondGeneral` shape — diamond conclusion + asymmetric Moreover
witness — conditional on the Lemma 32 NP payloads. The Moreover witness
on the outer outputs is established by:

* **LHS output (Me-Bet rebuild):** NP-x of `MEqRed.bet ht d_1_bridged dArg_1`
  unfolds to `(NP-(x+1) d_1_bridged) ∧ (NP-x dArg_1)`. Each conjunct is
  established from the body/arg IH's Moreover crossings + bridge
  NP-preservation.

* **RHS output (Lemma 32 EquHead application):** NP-x of the Lemma 32
  EquHead output is delivered by `Lemma_32_EquHead_PreservesNP_Payload`
  applied to NP-(x+1) of `d_2` (body) and NP-x of `dArg_2` (arg). -/

/-- **Strengthened paper-faithful App × Bet** with full Moreover output.

Produces the `MoreoverDiamondGeneral`-shape Σ-type at the call site:
diamond conclusion plus the asymmetric Moreover witness, conditional on
`Lemma_32_EquHead_PreservesNP_Payload`. -/
theorem Lemma_2_PaperFaithful_AppBet_Moreover
    (hLem32EquHeadNP : Lemma_32_EquHead_PreservesNP_Payload)
    {Γ₀ : Ctx} {s₀ : Stack}
    {t₀_inner u₀ u₁ u₂ v₀ v₁ v₂ t₁ : Term}
    (hT₁ : MEqRed Γ₀ [] t₀_inner t₁)
    (hv₀Scoped : Term.Scoped Γ₀.depth v₀)
    (hBody₁ : MEqRed ({bound := v₀, kind := .equ} :: Γ₀)
      (Stack.shift 0 s₀) u₀ u₁)
    (hArg₁ : MEqRed Γ₀ [] v₀ v₁)
    (ht₀_innerScoped : Term.Scoped Γ₀.depth t₀_inner)
    (hBody₂ : MEqRed ({bound := t₀_inner, kind := .sub} :: Γ₀)
      (Stack.shift 0 s₀) u₀ u₂)
    (hArg₂ : MEqRed Γ₀ [] v₀ v₂)
    (hBodyIH :
      MoreoverDiamondGeneral hBody₁
        (MEqRed.bridgeSubToEquHead hBody₂ hv₀Scoped).1)
    (hArgIH : MoreoverDiamondGeneral hArg₁ hArg₂)
    {Γ₁ s₁ Γ₂ s₂ : _}
    (he₁ : ContextEvolution Γ₀ s₀ Γ₁ s₁)
    (he₂ : ContextEvolution Γ₀ s₀ Γ₂ s₂) :
    ∃ (t₃ : Term)
      (d₁ : MEqRed Γ₁ s₁ (.app (.abs t₁ u₁) v₁) t₃)
      (d₂ : MEqRed Γ₂ s₂ (Term.instantiate 0 v₂ u₂) t₃),
      ∀ (x : Nat),
        ((MEqRed.app
            (MEqRed.fOp hT₁ hv₀Scoped hBody₁) hArg₁).NoPromotionOf x →
          d₂.NoPromotionOf x) ∧
        ((MEqRed.bet ht₀_innerScoped hBody₂ hArg₂).NoPromotionOf x →
          d₁.NoPromotionOf x) := by
  let heBody₁ : ContextEvolution ({bound := v₀, kind := .equ} :: Γ₀)
      (Stack.shift 0 s₀)
      ({bound := v₁, kind := .equ} :: Γ₁) (Stack.shift 0 s₁) :=
    ContextEvolution.cons_evolve he₁ hArg₁
  let heBody₂ : ContextEvolution ({bound := v₀, kind := .equ} :: Γ₀)
      (Stack.shift 0 s₀)
      ({bound := v₂, kind := .equ} :: Γ₂) (Stack.shift 0 s₂) :=
    ContextEvolution.cons_evolve he₂ hArg₂
  obtain ⟨u_3, d_1, d_2, hMBody⟩ := hBodyIH heBody₁ heBody₂
  have hBridged_NP_0 :
      (MEqRed.bridgeSubToEquHead hBody₂ hv₀Scoped).1.NoPromotionOf 0 :=
    bridgeSubToEquHead_NP_zero hBody₂ hv₀Scoped
  have hd_1_NP_0 : d_1.NoPromotionOf 0 := (hMBody 0).2 hBridged_NP_0
  have hArgEv₁ : ContextEvolution Γ₀ [] Γ₁ [] :=
    he₁.Lemma_36_CommutativityContextWeakening
  have hArgEv₂ : ContextEvolution Γ₀ [] Γ₂ [] :=
    he₂.Lemma_36_CommutativityContextWeakening
  obtain ⟨v_3, dArg_1, dArg_2, hMArg⟩ := hArgIH hArgEv₁ hArgEv₂
  have ht₁Scoped : Term.Scoped Γ₁.depth t₁ := by
    have h : Term.Scoped Γ₀.depth t₁ := hT₁.scoped_right
    rw [he₁.preserves_ctx_depth] at h
    exact h
  have hv₂Scoped₂ : Term.Scoped Γ₂.depth v₂ := dArg_2.scoped_left
  have hv_3Scoped₂ : Term.Scoped Γ₂.depth v_3 := dArg_2.scoped_right
  let d_1_bridged : MEqRed ({bound := t₁, kind := .sub} :: Γ₁)
      (Stack.shift 0 s₁) u₁ u_3 :=
    d_1.equ_to_sub_head_replace_NoPromotion hd_1_NP_0 ht₁Scoped
  let hLHS_out : MEqRed Γ₁ s₁
      (.app (.abs t₁ u₁) v₁) (Term.instantiate 0 v_3 u_3) :=
    MEqRed.bet ht₁Scoped d_1_bridged dArg_1
  have hStackSimp :
      Stack.instantiate 0 v₂ (Stack.shift 0 s₂) = s₂ :=
    Stack.instantiate_shift_zero_id_general v₂ s₂
  let hRHS_pre :
      MEqRed Γ₂ (Stack.instantiate 0 v₂ (Stack.shift 0 s₂))
        (Term.instantiate 0 v₂ u₂) (Term.instantiate 0 v_3 u_3) :=
    Lemma_32_EquHead_proved_closed hv₂Scoped₂ hv_3Scoped₂ dArg_2 d_2
  let hRHS_out : MEqRed Γ₂ s₂
      (Term.instantiate 0 v₂ u₂) (Term.instantiate 0 v_3 u_3) :=
    hStackSimp ▸ hRHS_pre
  refine ⟨Term.instantiate 0 v_3 u_3, hLHS_out, hRHS_out, ?_⟩
  intro x
  refine ⟨?_, ?_⟩
  · -- h_1.NP-x → d_2.NP-x. h_1 = MEqRed.app (MEqRed.fOp hT₁ hv₀Scoped hBody₁) hArg₁.
    -- h_1.NP-x = (NP-x (fOp hT₁ ... hBody₁)) ∧ (NP-x hArg₁)
    --         = ((NP-x hT₁) ∧ (NP-(x+1) hBody₁)) ∧ (NP-x hArg₁).
    -- d_2 = hRHS_out = hStackSimp ▸ (Lemma_32_EquHead applied to d_2).
    -- NP-x of d_2 via the Lemma 32 EquHead NP payload from NP-(x+1) of body
    -- diamond's d_2 + NP-x of arg's dArg_2.
    intro h₁np
    have hBodyOuterNP : hBody₁.NoPromotionOf (x + 1) := h₁np.1.2
    have hArgOuterNP : hArg₁.NoPromotionOf x := h₁np.2
    have hd_2_body_NP : d_2.NoPromotionOf (x + 1) :=
      (hMBody (x + 1)).1 hBodyOuterNP
    have hdArg_2_NP : dArg_2.NoPromotionOf x := (hMArg x).1 hArgOuterNP
    have hPre : hRHS_pre.NoPromotionOf x :=
      hLem32EquHeadNP hv₂Scoped₂ hv_3Scoped₂ dArg_2 d_2 x hd_2_body_NP hdArg_2_NP
    show MEqRed.NoPromotionOf x hRHS_out
    -- hRHS_out = hStackSimp ▸ hRHS_pre. NP-x propagates through Eq.rec.
    have hMotive : ∀ (s' : Stack)
      (heq : Stack.instantiate 0 v₂ (Stack.shift 0 s₂) = s')
      (d : MEqRed Γ₂ s'
        (Term.instantiate 0 v₂ u₂) (Term.instantiate 0 v_3 u_3)),
      d = heq ▸ hRHS_pre →
      MEqRed.NoPromotionOf x d := by
        intro s' heq d hd
        subst heq
        subst hd
        exact hPre
    exact hMotive _ _ _ rfl
  · -- h_2.NP-x → d_1.NP-x. h_2 = MEqRed.bet ht₀ hBody₂ hArg₂.
    -- h_2.NP-x = (NP-(x+1) hBody₂) ∧ (NP-x hArg₂).
    -- d_1 = MEqRed.bet ht₁Scoped d_1_bridged dArg_1.
    -- d_1.NP-x = (NP-(x+1) d_1_bridged) ∧ (NP-x dArg_1).
    -- NP-(x+1) d_1_bridged = NP-(x+1) of equ_to_sub_head_replace_NoPromotion d_1 ht₁ ...
    -- For x ≥ 0, x+1 ≠ 0, so equ_to_sub_head_replace_NoPromotion_preserves_NP gives:
    --   NP-(x+1) d_1 → NP-(x+1) d_1_bridged.
    -- The bridged source hBody₂ has NP-(x+1) by hypothesis; bridgeSubToEquHead
    -- preserves NP. Use Moreover crossing (bridged_h₂ → d_1).
    intro h₂np
    have hBody₂NP : hBody₂.NoPromotionOf (x + 1) := h₂np.1
    have hArg₂NP : hArg₂.NoPromotionOf x := h₂np.2
    have hBridged_NP :
        (MEqRed.bridgeSubToEquHead hBody₂ hv₀Scoped).1.NoPromotionOf (x + 1) :=
      bridgeSubToEquHead_preserves_NP hBody₂ hv₀Scoped (x + 1) hBody₂NP
    have hd_1_body_NP : d_1.NoPromotionOf (x + 1) :=
      (hMBody (x + 1)).2 hBridged_NP
    have hdArg_1_NP : dArg_1.NoPromotionOf x := (hMArg x).2 hArg₂NP
    -- NP-(x+1) of d_1_bridged via equ_to_sub_head_replace_NoPromotion_preserves_NP.
    have hd_1_bridged_NP : d_1_bridged.NoPromotionOf (x + 1) :=
      MEqRed.equ_to_sub_head_replace_NoPromotion_preserves_NP
        d_1 hd_1_NP_0 ht₁Scoped (x + 1) (by omega) hd_1_body_NP
    -- Output NP-x = NP-(x+1) d_1_bridged ∧ NP-x dArg_1.
    exact ⟨hd_1_bridged_NP, hdArg_1_NP⟩

/-- **Strengthened paper-faithful Bet × App** with full Moreover output.
Symmetric to `Lemma_2_PaperFaithful_AppBet_Moreover`. -/
theorem Lemma_2_PaperFaithful_BetApp_Moreover
    (hLem32EquHeadNP : Lemma_32_EquHead_PreservesNP_Payload)
    {Γ₀ : Ctx} {s₀ : Stack}
    {t₀_inner u₀ u₁ u₂ v₀ v₁ v₂ t₂ : Term}
    (ht₀_innerScoped : Term.Scoped Γ₀.depth t₀_inner)
    (hBody₁ : MEqRed ({bound := t₀_inner, kind := .sub} :: Γ₀)
      (Stack.shift 0 s₀) u₀ u₁)
    (hArg₁ : MEqRed Γ₀ [] v₀ v₁)
    (hT₂ : MEqRed Γ₀ [] t₀_inner t₂)
    (hv₀Scoped : Term.Scoped Γ₀.depth v₀)
    (hBody₂ : MEqRed ({bound := v₀, kind := .equ} :: Γ₀)
      (Stack.shift 0 s₀) u₀ u₂)
    (hArg₂ : MEqRed Γ₀ [] v₀ v₂)
    (hBodyIH :
      MoreoverDiamondGeneral
        (MEqRed.bridgeSubToEquHead hBody₁ hv₀Scoped).1
        hBody₂)
    (hArgIH : MoreoverDiamondGeneral hArg₁ hArg₂)
    {Γ₁ s₁ Γ₂ s₂ : _}
    (he₁ : ContextEvolution Γ₀ s₀ Γ₁ s₁)
    (he₂ : ContextEvolution Γ₀ s₀ Γ₂ s₂) :
    ∃ (t₃ : Term)
      (d₁ : MEqRed Γ₁ s₁ (Term.instantiate 0 v₁ u₁) t₃)
      (d₂ : MEqRed Γ₂ s₂ (.app (.abs t₂ u₂) v₂) t₃),
      ∀ (x : Nat),
        ((MEqRed.bet ht₀_innerScoped hBody₁ hArg₁).NoPromotionOf x →
          d₂.NoPromotionOf x) ∧
        ((MEqRed.app
            (MEqRed.fOp hT₂ hv₀Scoped hBody₂) hArg₂).NoPromotionOf x →
          d₁.NoPromotionOf x) := by
  let heBody₁ : ContextEvolution ({bound := v₀, kind := .equ} :: Γ₀)
      (Stack.shift 0 s₀)
      ({bound := v₁, kind := .equ} :: Γ₁) (Stack.shift 0 s₁) :=
    ContextEvolution.cons_evolve he₁ hArg₁
  let heBody₂ : ContextEvolution ({bound := v₀, kind := .equ} :: Γ₀)
      (Stack.shift 0 s₀)
      ({bound := v₂, kind := .equ} :: Γ₂) (Stack.shift 0 s₂) :=
    ContextEvolution.cons_evolve he₂ hArg₂
  obtain ⟨u_3, d_1, d_2, hMBody⟩ := hBodyIH heBody₁ heBody₂
  have hBridged_NP_0 :
      (MEqRed.bridgeSubToEquHead hBody₁ hv₀Scoped).1.NoPromotionOf 0 :=
    bridgeSubToEquHead_NP_zero hBody₁ hv₀Scoped
  have hd_2_NP_0 : d_2.NoPromotionOf 0 := (hMBody 0).1 hBridged_NP_0
  have hArgEv₁ : ContextEvolution Γ₀ [] Γ₁ [] :=
    he₁.Lemma_36_CommutativityContextWeakening
  have hArgEv₂ : ContextEvolution Γ₀ [] Γ₂ [] :=
    he₂.Lemma_36_CommutativityContextWeakening
  obtain ⟨v_3, dArg_1, dArg_2, hMArg⟩ := hArgIH hArgEv₁ hArgEv₂
  have ht₂Scoped : Term.Scoped Γ₂.depth t₂ := by
    have h : Term.Scoped Γ₀.depth t₂ := hT₂.scoped_right
    rw [he₂.preserves_ctx_depth] at h
    exact h
  have hv₁Scoped₁ : Term.Scoped Γ₁.depth v₁ := dArg_1.scoped_left
  have hv_3Scoped₁ : Term.Scoped Γ₁.depth v_3 := dArg_1.scoped_right
  have hStackSimp :
      Stack.instantiate 0 v₁ (Stack.shift 0 s₁) = s₁ :=
    Stack.instantiate_shift_zero_id_general v₁ s₁
  let hLHS_pre :
      MEqRed Γ₁ (Stack.instantiate 0 v₁ (Stack.shift 0 s₁))
        (Term.instantiate 0 v₁ u₁) (Term.instantiate 0 v_3 u_3) :=
    Lemma_32_EquHead_proved_closed hv₁Scoped₁ hv_3Scoped₁ dArg_1 d_1
  let hLHS_out : MEqRed Γ₁ s₁
      (Term.instantiate 0 v₁ u₁) (Term.instantiate 0 v_3 u_3) :=
    hStackSimp ▸ hLHS_pre
  let d_2_bridged : MEqRed ({bound := t₂, kind := .sub} :: Γ₂)
      (Stack.shift 0 s₂) u₂ u_3 :=
    d_2.equ_to_sub_head_replace_NoPromotion hd_2_NP_0 ht₂Scoped
  let hRHS_out : MEqRed Γ₂ s₂
      (.app (.abs t₂ u₂) v₂) (Term.instantiate 0 v_3 u_3) :=
    MEqRed.bet ht₂Scoped d_2_bridged dArg_2
  refine ⟨Term.instantiate 0 v_3 u_3, hLHS_out, hRHS_out, ?_⟩
  intro x
  refine ⟨?_, ?_⟩
  · -- h_1.NP-x → d_2.NP-x. h_1 = MEqRed.bet ht₀ hBody₁ hArg₁.
    -- d_2 = hRHS_out = MEqRed.bet ht₂Scoped d_2_bridged dArg_2.
    -- d_2.NP-x = (NP-(x+1) d_2_bridged) ∧ (NP-x dArg_2).
    intro h₁np
    have hBody₁NP : hBody₁.NoPromotionOf (x + 1) := h₁np.1
    have hArg₁NP : hArg₁.NoPromotionOf x := h₁np.2
    have hBridged_NP :
        (MEqRed.bridgeSubToEquHead hBody₁ hv₀Scoped).1.NoPromotionOf (x + 1) :=
      bridgeSubToEquHead_preserves_NP hBody₁ hv₀Scoped (x + 1) hBody₁NP
    have hd_2_body_NP : d_2.NoPromotionOf (x + 1) :=
      (hMBody (x + 1)).1 hBridged_NP
    have hdArg_2_NP : dArg_2.NoPromotionOf x := (hMArg x).1 hArg₁NP
    have hd_2_bridged_NP : d_2_bridged.NoPromotionOf (x + 1) :=
      MEqRed.equ_to_sub_head_replace_NoPromotion_preserves_NP
        d_2 hd_2_NP_0 ht₂Scoped (x + 1) (by omega) hd_2_body_NP
    exact ⟨hd_2_bridged_NP, hdArg_2_NP⟩
  · -- h_2.NP-x → d_1.NP-x. h_2 = MEqRed.app (MEqRed.fOp hT₂ hv₀Scoped hBody₂) hArg₂.
    -- d_1 = hLHS_out = hStackSimp ▸ Lemma_32_EquHead output.
    intro h₂np
    have hBodyOuterNP : hBody₂.NoPromotionOf (x + 1) := h₂np.1.2
    have hArgOuterNP : hArg₂.NoPromotionOf x := h₂np.2
    have hd_1_body_NP : d_1.NoPromotionOf (x + 1) :=
      (hMBody (x + 1)).2 hBodyOuterNP
    have hdArg_1_NP : dArg_1.NoPromotionOf x := (hMArg x).2 hArgOuterNP
    have hPre : hLHS_pre.NoPromotionOf x :=
      hLem32EquHeadNP hv₁Scoped₁ hv_3Scoped₁ dArg_1 d_1 x hd_1_body_NP hdArg_1_NP
    show MEqRed.NoPromotionOf x hLHS_out
    have hMotive : ∀ (s' : Stack)
      (heq : Stack.instantiate 0 v₁ (Stack.shift 0 s₁) = s')
      (d : MEqRed Γ₁ s'
        (Term.instantiate 0 v₁ u₁) (Term.instantiate 0 v_3 u_3)),
      d = heq ▸ hLHS_pre →
      MEqRed.NoPromotionOf x d := by
        intro s' heq d hd
        subst heq
        subst hd
        exact hPre
    exact hMotive _ _ _ rfl

/-! ## Phase 3b — non-cross-β Moreover-tracked cells (general context)

Mirroring the same-context `MoreoverDiamond_*` cells in
`Lemma_2_BundleProof.lean`, but at general context with
`ContextEvolution` evolutions. Each cell takes:

* `h₁, h₂` source derivations
* Per-cell IHs at `MoreoverDiamondGeneral` shape (sub-derivations of
  `h₁, h₂` evolved to arbitrary `Γ_i; s_i`)
* Two outer evolutions `he_i : ContextEvolution Γ₀ s₀ Γ_i s_i`

Returns the `MoreoverDiamondGeneral`-shape conclusion: a common reduct
`t_3` with derivations `d_1, d_2` and the asymmetric Moreover witness. -/

/-- **Me-Pro × Me-Pro** at general context. Both promote the same `bvar i`
through the same equ-binding; recurse on the bound. -/
theorem MoreoverDiamondGeneral_pro_pro {Γ₀ : Ctx} {s₀ : Stack} {i : Nat}
    {α₀ α_1 α_2 : Term}
    (hpv₁ hpv₂ : PrevalidExt Γ₀ s₀)
    (hb₁ hb₂ : Γ₀.equBinds i α₀)
    (hα₁ : MEqRed Γ₀ s₀ α₀ α_1) (hα₂ : MEqRed Γ₀ s₀ α₀ α_2)
    (hBoundIH : MoreoverDiamondGeneral hα₁ hα₂) :
    MoreoverDiamondGeneral
      (MEqRed.pro hpv₁ hb₁ hα₁) (MEqRed.pro hpv₂ hb₂ hα₂) := by
  intro Γ₁ s₁ Γ₂ s₂ he₁ he₂
  obtain ⟨α_3, d_1, d_2, hMoreoverBound⟩ := hBoundIH he₁ he₂
  refine ⟨α_3, d_1, d_2, ?_⟩
  intro x
  refine ⟨?_, ?_⟩
  · intro h₁np
    exact (hMoreoverBound x).1 h₁np.2
  · intro h₂np
    exact (hMoreoverBound x).2 h₂np.2

/-! ### Note: ProVar / VarPro and other parametric-IH cells

The Me-Pro × Me-Var (and symmetric Me-Var × Me-Pro) cells require an IH
parametric over a SECOND derivation: the paper recurses with `α₀ →
α_evolved` (obtained via Lemma 36 / Ct-Ann + Lemma 19) as the bound's
second derivation, not refl. Our `MoreoverDiamondGeneral` predicate fixes
both source derivations, so the bundle's recursion produces IHs that fix
the second derivation as a sub-derivation of the original `h_2`.

For ProVar/VarPro this means the bundle's bound IH delivers `α_3` joining
`α_1` and `α_evolved` (NOT `α_1` and `α_0`). The Me-Pro output `bvar i
→ α_3` at Γ_2; s_2 is rebuilt from the EVOLVED binding `hb_evolved :
Γ_2.equBinds i α_evolved` and the bound's d_2 (sourced from α_evolved).

To support this in the recursion, the bundle's structural induction at
the Me-Pro × Me-Var pair must:
1. Compute α_evolved via `he₂.equBinds_evolve hpv.ctx hb`.
2. Lift `α_0 → α_evolved` across `s_0` via `lift_empty_to_stack`.
3. Run the bound IH against `(hα₁, lifted)` — a MoreoverDiamondGeneral
   call with second derivation = the lifted reduction.
4. The bound IH's d_2 has source α_evolved at Γ_2; s_2; build Me-Pro.

The lifted `α_0 → α_evolved` is a NEW derivation, not a sub-derivation of
h_2 = Me-Var. The bundle's recursion measure must accommodate this.

Implementation status: ProVar / VarPro general-context Moreover cells
are DEFERRED to a dedicated dispatch. The existing
`Lemma_2_Case_ProVar_proved` in `Lemma_2_DiamondClosure.lean` handles
the plain (non-Moreover) version; the Moreover-tracked version requires
restructuring the bundle's IH shape (parametric second derivation) and
re-engineering the per-cell theorem.

For the same-context (`ctRefl/ctRefl`) projection that closes
`UniformEqDiamonds`, ProVar/VarPro at `ctRefl/ctRefl` becomes:
α_evolved = α_0, lifted = refl, bound IH = (hα₁, refl). At this
specialization the cell collapses to the BundleProof's
`MoreoverDiamond_pro_var` cell with refl bound. -/

/-- **Me-App × Me-TAp** at general context. The Me-TAp source's stack
inversion forces `u_1 = .top` via `top_inv`. Both diamond endpoints
collapse to `.top`. -/
theorem MoreoverDiamondGeneral_app_tAp {Γ₀ : Ctx} {s₀ : Stack}
    {u_1 v₀ v_1 : Term}
    (hOp : MEqRed Γ₀ (v₀ :: s₀) .top u_1)
    (hArg : MEqRed Γ₀ [] v₀ v_1)
    (hpvTAp : PrevalidExt Γ₀ s₀) (hv₀ : Term.Scoped Γ₀.depth v₀) :
    MoreoverDiamondGeneral
      (MEqRed.app hOp hArg) (MEqRed.tAp hpvTAp hv₀) := by
  intro Γ₁ s₁ Γ₂ s₂ he₁ he₂
  have hu₁ : u_1 = .top := hOp.top_inv
  subst hu₁
  have hpvE₁ : PrevalidExt Γ₁ s₁ :=
    Classical.choice (he₁.preservesNonemptyPrevalidExt ⟨hpvTAp⟩)
  have hpvE₂ : PrevalidExt Γ₂ s₂ :=
    Classical.choice (he₂.preservesNonemptyPrevalidExt ⟨hpvTAp⟩)
  have hv₁Scoped : Term.Scoped Γ₀.depth v_1 := hArg.scoped_right
  have hv₁Scoped₁ : Term.Scoped Γ₁.depth v_1 := by
    rw [← he₁.preserves_ctx_depth]; exact hv₁Scoped
  refine ⟨.top, MEqRed.tAp hpvE₁ hv₁Scoped₁, MEqRed.top hpvE₂, ?_⟩
  intro x
  exact ⟨fun _ => trivial, fun _ => trivial⟩

/-- **Me-TAp × Me-App** at general context. Symmetric to `_app_tAp`. -/
theorem MoreoverDiamondGeneral_tAp_app {Γ₀ : Ctx} {s₀ : Stack}
    {u_2 v₀ v_2 : Term}
    (hpvTAp : PrevalidExt Γ₀ s₀) (hv₀ : Term.Scoped Γ₀.depth v₀)
    (hOp : MEqRed Γ₀ (v₀ :: s₀) .top u_2)
    (hArg : MEqRed Γ₀ [] v₀ v_2) :
    MoreoverDiamondGeneral
      (MEqRed.tAp hpvTAp hv₀) (MEqRed.app hOp hArg) := by
  intro Γ₁ s₁ Γ₂ s₂ he₁ he₂
  have hu₂ : u_2 = .top := hOp.top_inv
  subst hu₂
  have hpvE₁ : PrevalidExt Γ₁ s₁ :=
    Classical.choice (he₁.preservesNonemptyPrevalidExt ⟨hpvTAp⟩)
  have hpvE₂ : PrevalidExt Γ₂ s₂ :=
    Classical.choice (he₂.preservesNonemptyPrevalidExt ⟨hpvTAp⟩)
  have hv₂Scoped : Term.Scoped Γ₀.depth v_2 := hArg.scoped_right
  have hv₂Scoped₂ : Term.Scoped Γ₂.depth v_2 := by
    rw [← he₂.preserves_ctx_depth]; exact hv₂Scoped
  refine ⟨.top, MEqRed.top hpvE₁, MEqRed.tAp hpvE₂ hv₂Scoped₂, ?_⟩
  intro x
  exact ⟨fun _ => trivial, fun _ => trivial⟩

/-- **Me-Fun × Me-Fun** at general context. Both descend under unapplied
abstractions; outer stack is `[]`. Body IH at `{t₀,.sub}::Γ_0; []`. The
body outputs at `{t₀,.sub}::Γ_i; []` are bridged to the evolved
abstraction's bound `{t_i,.sub}::Γ_i; []` via the body IH directly
(by lifting evolution with the abstraction's bound reduction). -/
theorem MoreoverDiamondGeneral_fun_fun {Γ₀ : Ctx}
    {t₀ t_1 t_2 body₀ body_1 body_2 : Term}
    (hT_1 : MEqRed Γ₀ [] t₀ t_1)
    (hBody_1 : MEqRed ({bound := t₀, kind := .sub} :: Γ₀) [] body₀ body_1)
    (hT_2 : MEqRed Γ₀ [] t₀ t_2)
    (hBody_2 : MEqRed ({bound := t₀, kind := .sub} :: Γ₀) [] body₀ body_2)
    (hBoundIH : MoreoverDiamondGeneral hT_1 hT_2)
    (hBodyIH : MoreoverDiamondGeneral hBody_1 hBody_2) :
    MoreoverDiamondGeneral
      (MEqRed.fun_ hT_1 hBody_1) (MEqRed.fun_ hT_2 hBody_2) := by
  intro Γ₁ s₁ Γ₂ s₂ he₁ he₂
  -- Force s_i = [] from stack-length preservation.
  have hs₁_nil : s₁ = [] := by
    have h := he₁.preserves_stack_length
    cases s₁
    · rfl
    · simp at h
  have hs₂_nil : s₂ = [] := by
    have h := he₂.preserves_stack_length
    cases s₂
    · rfl
    · simp at h
  subst hs₁_nil; subst hs₂_nil
  -- Bound diamond at evolved contexts.
  obtain ⟨t_3, d_1_bound, d_2_bound, hMBound⟩ := hBoundIH he₁ he₂
  -- Build body context evolutions via ctAnn with the abstraction's bound reductions.
  let heBody₁ : ContextEvolution ({bound := t₀, kind := .sub} :: Γ₀) []
      ({bound := t_1, kind := .sub} :: Γ₁) [] :=
    ContextEvolution.ctAnn he₁ hT_1
  let heBody₂ : ContextEvolution ({bound := t₀, kind := .sub} :: Γ₀) []
      ({bound := t_2, kind := .sub} :: Γ₂) [] :=
    ContextEvolution.ctAnn he₂ hT_2
  obtain ⟨body_3, d_1_body, d_2_body, hMBody⟩ := hBodyIH heBody₁ heBody₂
  refine ⟨.abs t_3 body_3,
    MEqRed.fun_ d_1_bound d_1_body,
    MEqRed.fun_ d_2_bound d_2_body, ?_⟩
  intro x
  refine ⟨?_, ?_⟩
  · intro h₁np
    -- h₁ = MEqRed.fun_ hT_1 hBody_1, NP-x = (NP-x hT_1) ∧ (NP-(x+1) hBody_1)
    -- d_2 = MEqRed.fun_ d_2_bound d_2_body, NP-x = (NP-x d_2_bound) ∧ (NP-(x+1) d_2_body)
    exact ⟨(hMBound x).1 h₁np.1, (hMBody (x + 1)).1 h₁np.2⟩
  · intro h₂np
    exact ⟨(hMBound x).2 h₂np.1, (hMBody (x + 1)).2 h₂np.2⟩

/-- **Me-FOp × Me-FOp** at general context. Both pop the stack head into an
`.equ`-head body context with bound = α. The α →= α_i step is extracted
from the outer evolution via `stripStackHeadWithReduction`, then the
body context evolution is built via `cons_evolve`. -/
theorem MoreoverDiamondGeneral_fOp_fOp {Γ₀ : Ctx} {s₀ : Stack}
    {α t₀ t_1 t_2 body₀ body_1 body_2 : Term}
    (hαScoped : Term.Scoped Γ₀.depth α)
    (hT_1 : MEqRed Γ₀ [] t₀ t_1)
    (hBody_1 : MEqRed ({bound := α, kind := .equ} :: Γ₀)
      (Stack.shift 0 s₀) body₀ body_1)
    (hT_2 : MEqRed Γ₀ [] t₀ t_2)
    (hBody_2 : MEqRed ({bound := α, kind := .equ} :: Γ₀)
      (Stack.shift 0 s₀) body₀ body_2)
    (hBoundIH : MoreoverDiamondGeneral hT_1 hT_2)
    -- The body IH's signature is for the ORIGINAL body context
    -- `{α,.equ}::Γ₀; shift 0 s₀`. We invoke it with body-evolved
    -- contexts `{α_i,.equ}::Γ_i; shift 0 s_inner_i` derived via
    -- `cons_evolve` with α →= α_i.
    (hBodyIH : MoreoverDiamondGeneral hBody_1 hBody_2) :
    MoreoverDiamondGeneral
      (MEqRed.fOp hT_1 hαScoped hBody_1) (MEqRed.fOp hT_2 hαScoped hBody_2) := by
  intro Γ₁ s₁ Γ₂ s₂ he₁ he₂
  -- We need PrevalidExt Γ₀ (α :: s₀) to invoke stripStackHeadWithReduction.
  -- Build from body's prevalidity.
  have hpvE_body : PrevalidExt ({bound := α, kind := .equ} :: Γ₀)
      (Stack.shift 0 s₀) := hBody_1.prevalidExt
  have hpvCtx_body : Prevalid ({bound := α, kind := .equ} :: Γ₀) :=
    PrevalidExt.ctx hpvE_body
  have hpvCtx₀ : Prevalid Γ₀ := Prevalid.tail hpvCtx_body
  have hStackScopedShifted : Stack.Scoped (Γ₀.depth + 1) (Stack.shift 0 s₀) := by
    have h := PrevalidExt.stack_scoped hpvE_body
    simpa [Ctx.depth_cons] using h
  have hStackScoped₀ : Stack.Scoped Γ₀.depth s₀ :=
    Stack.Scoped.shift_inv hStackScopedShifted
  have hpvE_s₀ : PrevalidExt Γ₀ s₀ :=
    PrevalidExt.of_stack_scoped hpvCtx₀ hStackScoped₀
  have hpvE_α_s₀ : PrevalidExt Γ₀ (α :: s₀) := PrevalidExt.cons hpvE_s₀ hαScoped
  -- s_i must be `α_i :: s_inner_i`; extract.
  have hLen₁ := he₁.preserves_stack_length
  have hLen₂ := he₂.preserves_stack_length
  cases hs1 : s₁ with
  | nil => rw [hs1] at hLen₁; simp at hLen₁
  | cons α_1 s_inner_1 =>
  cases hs2 : s₂ with
  | nil => rw [hs2] at hLen₂; simp at hLen₂
  | cons α_2 s_inner_2 =>
  rw [hs1] at he₁ hLen₁
  rw [hs2] at he₂ hLen₂
  -- Extract α →= α_i + stripped Γ₀;s₀ ↣ Γ_i;s_inner_i.
  obtain ⟨hHead₁_ne, heStrip₁⟩ :=
    ContextEvolution.stripStackHeadWithReduction he₁ hαScoped hpvE_α_s₀
  obtain ⟨hHead₂_ne, heStrip₂⟩ :=
    ContextEvolution.stripStackHeadWithReduction he₂ hαScoped hpvE_α_s₀
  let hHead₁ : MEqRed Γ₀ [] α α_1 := Classical.choice hHead₁_ne
  let hHead₂ : MEqRed Γ₀ [] α α_2 := Classical.choice hHead₂_ne
  -- Bound IH at evolved Γ_0; [] ↣ Γ_i; [] via Lemma 36 on stripped evolutions.
  have hBoundEv₁ : ContextEvolution Γ₀ [] Γ₁ [] :=
    heStrip₁.Lemma_36_CommutativityContextWeakening
  have hBoundEv₂ : ContextEvolution Γ₀ [] Γ₂ [] :=
    heStrip₂.Lemma_36_CommutativityContextWeakening
  obtain ⟨t_3, d_1_bound, d_2_bound, hMBound⟩ := hBoundIH hBoundEv₁ hBoundEv₂
  -- Body context evolutions via cons_evolve (with α →= α_i).
  let heBody₁ : ContextEvolution ({bound := α, kind := .equ} :: Γ₀)
      (Stack.shift 0 s₀)
      ({bound := α_1, kind := .equ} :: Γ₁) (Stack.shift 0 s_inner_1) :=
    ContextEvolution.cons_evolve heStrip₁ hHead₁
  let heBody₂ : ContextEvolution ({bound := α, kind := .equ} :: Γ₀)
      (Stack.shift 0 s₀)
      ({bound := α_2, kind := .equ} :: Γ₂) (Stack.shift 0 s_inner_2) :=
    ContextEvolution.cons_evolve heStrip₂ hHead₂
  obtain ⟨body_3, d_1_body, d_2_body, hMBody⟩ := hBodyIH heBody₁ heBody₂
  have hα₁Scoped : Term.Scoped Γ₁.depth α_1 := by
    have h : Term.Scoped Γ₀.depth α_1 := hHead₁.scoped_right
    rw [heStrip₁.preserves_ctx_depth] at h
    exact h
  have hα₂Scoped : Term.Scoped Γ₂.depth α_2 := by
    have h : Term.Scoped Γ₀.depth α_2 := hHead₂.scoped_right
    rw [heStrip₂.preserves_ctx_depth] at h
    exact h
  refine ⟨.abs t_3 body_3,
    MEqRed.fOp d_1_bound hα₁Scoped d_1_body,
    MEqRed.fOp d_2_bound hα₂Scoped d_2_body, ?_⟩
  intro x
  refine ⟨?_, ?_⟩
  · intro h₁np
    exact ⟨(hMBound x).1 h₁np.1, (hMBody (x + 1)).1 h₁np.2⟩
  · intro h₂np
    exact ⟨(hMBound x).2 h₂np.1, (hMBody (x + 1)).2 h₂np.2⟩

/-- **Me-Bet × Me-Bet** at general context. Both perform β at body
`{t,.sub}::Γ_0; shift 0 s_0` and arg `Γ_0; []`. Uses Lemma 32
(kind-narrowed asymmetric closed) on each side to produce the joint
β-substituted output. Conditional on `Lemma_32_PreservesNP_Payload`. -/
theorem MoreoverDiamondGeneral_bet_bet
    (hLem32NP : Lemma_32_PreservesNP_Payload)
    {Γ₀ : Ctx} {s₀ : Stack}
    {t v_0 u_0 u_1 u_2 v_1 v_2 : Term}
    (ht : Term.Scoped Γ₀.depth t)
    (hBody_1 : MEqRed ({bound := t, kind := .sub} :: Γ₀)
      (Stack.shift 0 s₀) u_0 u_1)
    (hArg_1 : MEqRed Γ₀ [] v_0 v_1)
    (hBody_2 : MEqRed ({bound := t, kind := .sub} :: Γ₀)
      (Stack.shift 0 s₀) u_0 u_2)
    (hArg_2 : MEqRed Γ₀ [] v_0 v_2)
    -- Body IH at the SAME starting context (both bodies share
    -- `{t,.sub}::Γ_0; shift 0 s_0`).
    (hBodyIH : MoreoverDiamondGeneral hBody_1 hBody_2)
    (hArgIH : MoreoverDiamondGeneral hArg_1 hArg_2) :
    MoreoverDiamondGeneral
      (MEqRed.bet ht hBody_1 hArg_1) (MEqRed.bet ht hBody_2 hArg_2) := by
  intro Γ₁ s₁ Γ₂ s₂ he₁ he₂
  -- Body context evolutions via cons_lift (bound unchanged on both sides).
  let heBody₁ : ContextEvolution ({bound := t, kind := .sub} :: Γ₀)
      (Stack.shift 0 s₀)
      ({bound := t, kind := .sub} :: Γ₁) (Stack.shift 0 s₁) :=
    ContextEvolution.cons_lift he₁ ht
  let heBody₂ : ContextEvolution ({bound := t, kind := .sub} :: Γ₀)
      (Stack.shift 0 s₀)
      ({bound := t, kind := .sub} :: Γ₂) (Stack.shift 0 s₂) :=
    ContextEvolution.cons_lift he₂ ht
  obtain ⟨u_3, d_1_body, d_2_body, hMBody⟩ := hBodyIH heBody₁ heBody₂
  have hArgEv₁ : ContextEvolution Γ₀ [] Γ₁ [] :=
    he₁.Lemma_36_CommutativityContextWeakening
  have hArgEv₂ : ContextEvolution Γ₀ [] Γ₂ [] :=
    he₂.Lemma_36_CommutativityContextWeakening
  obtain ⟨v_3, d_1_arg, d_2_arg, hMArg⟩ := hArgIH hArgEv₁ hArgEv₂
  have hv₁Scoped : Term.Scoped Γ₁.depth v_1 := d_1_arg.scoped_left
  have hv₂Scoped : Term.Scoped Γ₂.depth v_2 := d_2_arg.scoped_left
  have hv_3Scoped₁ : Term.Scoped Γ₁.depth v_3 := d_1_arg.scoped_right
  have hv_3Scoped₂ : Term.Scoped Γ₂.depth v_3 := d_2_arg.scoped_right
  have htScoped₁ : Term.Scoped Γ₁.depth t := by
    rw [← he₁.preserves_ctx_depth]; exact ht
  have htScoped₂ : Term.Scoped Γ₂.depth t := by
    rw [← he₂.preserves_ctx_depth]; exact ht
  have hStackSimp₁ : Stack.instantiate 0 v_1 (Stack.shift 0 s₁) = s₁ :=
    Stack.instantiate_shift_zero_id_general v_1 s₁
  have hStackSimp₂ : Stack.instantiate 0 v_2 (Stack.shift 0 s₂) = s₂ :=
    Stack.instantiate_shift_zero_id_general v_2 s₂
  let hLHS_pre :
      MEqRed Γ₁ (Stack.instantiate 0 v_1 (Stack.shift 0 s₁))
        (Term.instantiate 0 v_1 u_1) (Term.instantiate 0 v_3 u_3) :=
    Investigation.Lemma_32_KindNarrowedAsymmetric_proved_closed
      htScoped₁ hv₁Scoped hv_3Scoped₁ d_1_arg d_1_body
  let hRHS_pre :
      MEqRed Γ₂ (Stack.instantiate 0 v_2 (Stack.shift 0 s₂))
        (Term.instantiate 0 v_2 u_2) (Term.instantiate 0 v_3 u_3) :=
    Investigation.Lemma_32_KindNarrowedAsymmetric_proved_closed
      htScoped₂ hv₂Scoped hv_3Scoped₂ d_2_arg d_2_body
  let hLHS_out : MEqRed Γ₁ s₁
      (Term.instantiate 0 v_1 u_1) (Term.instantiate 0 v_3 u_3) :=
    hStackSimp₁ ▸ hLHS_pre
  let hRHS_out : MEqRed Γ₂ s₂
      (Term.instantiate 0 v_2 u_2) (Term.instantiate 0 v_3 u_3) :=
    hStackSimp₂ ▸ hRHS_pre
  refine ⟨Term.instantiate 0 v_3 u_3, hLHS_out, hRHS_out, ?_⟩
  intro x
  refine ⟨?_, ?_⟩
  · -- h₁.NP-x → d_2.NP-x. h₁ = MEqRed.bet ht hBody_1 hArg_1.
    intro h₁np
    have hBody_NP : d_2_body.NoPromotionOf (x + 1) :=
      (hMBody (x + 1)).1 h₁np.1
    have hArg_NP : d_2_arg.NoPromotionOf x := (hMArg x).1 h₁np.2
    have hPre : hRHS_pre.NoPromotionOf x :=
      hLem32NP htScoped₂ hv₂Scoped hv_3Scoped₂ d_2_arg d_2_body x hBody_NP hArg_NP
    show MEqRed.NoPromotionOf x hRHS_out
    have hMotive : ∀ (s' : Stack)
      (heq : Stack.instantiate 0 v_2 (Stack.shift 0 s₂) = s')
      (d : MEqRed Γ₂ s'
        (Term.instantiate 0 v_2 u_2) (Term.instantiate 0 v_3 u_3)),
      d = heq ▸ hRHS_pre →
      MEqRed.NoPromotionOf x d := by
        intro s' heq d hd
        subst heq
        subst hd
        exact hPre
    exact hMotive _ _ _ rfl
  · intro h₂np
    have hBody_NP : d_1_body.NoPromotionOf (x + 1) :=
      (hMBody (x + 1)).2 h₂np.1
    have hArg_NP : d_1_arg.NoPromotionOf x := (hMArg x).2 h₂np.2
    have hPre : hLHS_pre.NoPromotionOf x :=
      hLem32NP htScoped₁ hv₁Scoped hv_3Scoped₁ d_1_arg d_1_body x hBody_NP hArg_NP
    show MEqRed.NoPromotionOf x hLHS_out
    have hMotive : ∀ (s' : Stack)
      (heq : Stack.instantiate 0 v_1 (Stack.shift 0 s₁) = s')
      (d : MEqRed Γ₁ s'
        (Term.instantiate 0 v_1 u_1) (Term.instantiate 0 v_3 u_3)),
      d = heq ▸ hLHS_pre →
      MEqRed.NoPromotionOf x d := by
        intro s' heq d hd
        subst heq
        subst hd
        exact hPre
    exact hMotive _ _ _ rfl

/-- **Me-App × Me-App** at general context. Operator IH at expanded stack
`v_0 :: s_0` (Ct-Stk evolution); operand IH at empty stack. -/
theorem MoreoverDiamondGeneral_app_app {Γ₀ : Ctx} {s₀ : Stack}
    {u_0 u_1 u_2 v_0 v_1 v_2 : Term}
    (hOp_1 : MEqRed Γ₀ (v_0 :: s₀) u_0 u_1)
    (hArg_1 : MEqRed Γ₀ [] v_0 v_1)
    (hOp_2 : MEqRed Γ₀ (v_0 :: s₀) u_0 u_2)
    (hArg_2 : MEqRed Γ₀ [] v_0 v_2)
    (hOpIH : MoreoverDiamondGeneral hOp_1 hOp_2)
    (hArgIH : MoreoverDiamondGeneral hArg_1 hArg_2) :
    MoreoverDiamondGeneral
      (MEqRed.app hOp_1 hArg_1) (MEqRed.app hOp_2 hArg_2) := by
  intro Γ₁ s₁ Γ₂ s₂ he₁ he₂
  have hArgEv₁ : ContextEvolution Γ₀ [] Γ₁ [] :=
    he₁.Lemma_36_CommutativityContextWeakening
  have hArgEv₂ : ContextEvolution Γ₀ [] Γ₂ [] :=
    he₂.Lemma_36_CommutativityContextWeakening
  obtain ⟨v_3, d_1_arg, d_2_arg, hMArg⟩ := hArgIH hArgEv₁ hArgEv₂
  -- Operator IH at expanded stack via Ct-Stk.
  let heOp₁ : ContextEvolution Γ₀ (v_0 :: s₀) Γ₁ (v_1 :: s₁) :=
    ContextEvolution.ctStk he₁ hArg_1
  let heOp₂ : ContextEvolution Γ₀ (v_0 :: s₀) Γ₂ (v_2 :: s₂) :=
    ContextEvolution.ctStk he₂ hArg_2
  obtain ⟨u_3, d_1_op, d_2_op, hMOp⟩ := hOpIH heOp₁ heOp₂
  refine ⟨.app u_3 v_3,
    MEqRed.app d_1_op d_1_arg,
    MEqRed.app d_2_op d_2_arg, ?_⟩
  intro x
  refine ⟨?_, ?_⟩
  · intro h₁np
    exact ⟨(hMOp x).1 h₁np.1, (hMArg x).1 h₁np.2⟩
  · intro h₂np
    exact ⟨(hMOp x).2 h₂np.1, (hMArg x).2 h₂np.2⟩

/-! ## Phase 4 — projection from Moreover to plain `UniformEqDiamonds`

The bundle's universal closure `UniformMoreoverDiamondGeneral_proved` —
the structural induction on h₁ × h₂ dispatching to the 13 per-cell
theorems above — is a substantial assembly (estimated ~1500 lines)
that handles all 64+ source-pair combinations, including ProVar/VarPro
which require a parametric-second-derivation IH (paper-faithful: the
bundle's structural induction on h₁ naturally provides this IH because
h₂ is universally quantified at each recursion step).

Pending that assembly, we ship the **projection** from the universal
Moreover closure to `UniformEqDiamonds`. The projection is conditional
on `UniformMoreoverDiamondGeneral` as a Prop hypothesis; once the
bundle's assembly is shipped, this projection becomes the final
discharge of `UniformEqDiamonds`. -/

/-- **Projection: `UniformMoreoverDiamondGeneral → UniformEqDiamonds`.**

Specialise the universal closure to `ctRefl/ctRefl` (same-context
evolutions) and drop the Moreover NP witness. This is the wire-up
point for the de Bruijn Lemma 2 headline. -/
theorem UniformEqDiamonds_proved_of_MoreoverGeneral
    (hMoreover : UniformMoreoverDiamondGeneral) :
    UniformEqDiamonds :=
  hMoreover.toUniformEqDiamonds

/-! ## ProVar / VarPro residual payload

The Me-Pro × Me-Var (and symmetric) cells require a bound IH that runs
the bundle with a SYNTHETIC second derivation (the lifted `α_0 → α_evolved`
from `equBinds_evolve` + `lift_empty_to_stack`), not a sub-derivation of
the original `h_2 = Me-Var`. This is the **parametric-second-derivation**
shape natively provided by structural induction on h_1 where h_2 is
universally quantified at each recursive step.

Our `MoreoverDiamondGeneral h₁ h₂` predicate fixes both source derivations,
so the per-cell theorem signature for ProVar can't directly express the
synthetic-second-derivation IH. The structural-on-h_1 bundle naturally
provides it.

For now, we ship the missing cells as a Prop residual:

* `MoreoverDiamondGeneral_ProVarVarPro_Payload` — the universal closure
  of ProVar/VarPro cells at general context.

The bundle assembly (structural induction on h_1 dispatching to the 12
shipped cells + the ProVar/VarPro residual) becomes conditional on this
payload. -/

/-- **Universal ProVar/VarPro cell at general context.**

Captures both ProVar (h_1 = Me-Pro, h_2 = Me-Var) and VarPro (symmetric).
The bound IH (`hBoundDiamond`) takes a `bvar i`-bound's derivation pair
(possibly involving the synthetic lifted reduction `α_0 → α_evolved`) and
returns a `MoreoverDiamondGeneral`-shape closure on it. -/
def MoreoverDiamondGeneral_ProVarVarPro_Payload : Prop :=
  -- ProVar: h_1 = Me-Pro, h_2 = Me-Var (or symmetric VarPro).
  ∀ {Γ₀ : Ctx} {s₀ : Stack} {i : Nat} {α₀ α_1 : Term}
    (hpv₁ : PrevalidExt Γ₀ s₀) (hb : Γ₀.equBinds i α₀)
    (hα : MEqRed Γ₀ s₀ α₀ α_1)
    (hpv₂ : PrevalidExt Γ₀ s₀) (hi : i < Γ₀.depth),
    MoreoverDiamondGeneral
      (MEqRed.pro hpv₁ hb hα) (MEqRed.var hpv₂ hi)

/-- **Universal VarPro cell at general context** (symmetric to ProVar). -/
def MoreoverDiamondGeneral_VarPro_Payload : Prop :=
  ∀ {Γ₀ : Ctx} {s₀ : Stack} {i : Nat} {α₀ α_2 : Term}
    (hpv₁ : PrevalidExt Γ₀ s₀) (hi : i < Γ₀.depth)
    (hpv₂ : PrevalidExt Γ₀ s₀) (hb : Γ₀.equBinds i α₀)
    (hα : MEqRed Γ₀ s₀ α₀ α_2),
    MoreoverDiamondGeneral
      (MEqRed.var hpv₁ hi) (MEqRed.pro hpv₂ hb hα)

/-! ## Phase 4 — bundle assembly architectural analysis

The bundle `UniformMoreoverDiamondGeneral_proved` ideally proceeds by
**structural induction on h_1** with `h_2` generalised at each step.
This naturally provides the parametric-second-derivation IH for
ProVar/VarPro: when h_1 = `Me-Pro hpv hb hα`, the IH `ihα : ∀ t₂' h₂',
MoreoverDiamondGeneral hα h₂'` is universally quantified over h_2'.

Each constructor case of h_1 dispatches to the corresponding cell:

| h_1 constructor | h_2 cases handled | Cell |
|-----------------|-------------------|------|
| `top` | `top` | `MoreoverDiamondGeneral_top_top` |
| `pro` | `pro` | `MoreoverDiamondGeneral_pro_pro` |
| `pro` | `var` | `MoreoverDiamondGeneral_ProVarVarPro_Payload` |
| `var` | `var` | `MoreoverDiamondGeneral_var_var` |
| `var` | `pro` | `MoreoverDiamondGeneral_VarPro_Payload` |
| `app` | `app` | `MoreoverDiamondGeneral_app_app` |
| `app` | `bet` | `Lemma_2_PaperFaithful_AppBet_Moreover` |
| `app` | `tAp` | `MoreoverDiamondGeneral_app_tAp` |
| `bet` | `bet` | `MoreoverDiamondGeneral_bet_bet` |
| `bet` | `app` | `Lemma_2_PaperFaithful_BetApp_Moreover` |
| `tAp` | `tAp` | `MoreoverDiamondGeneral_tAp_tAp` |
| `tAp` | `app` | `MoreoverDiamondGeneral_tAp_app` |
| `fun_` | `fun_` | `MoreoverDiamondGeneral_fun_fun` |
| `fOp` | `fOp` | `MoreoverDiamondGeneral_fOp_fOp` |

Source-shape forcings ensure many h_1 × h_2 combinations are impossible
(e.g. `bet` h_1 forces source `(.abs t u) v`, ruling out `tAp` h_2).

**Cross-β architectural challenge.** For AppBet / BetApp, the body
diamond's two source derivations live in DIFFERENT head contexts:
* h_1 (Me-App via Me-FOp inversion): body at `{v_0, .equ}::Γ₀; shift 0 s₀`
* h_2 (Me-Bet): body at `{t, .sub}::Γ₀; shift 0 s₀`

The bridge `MEqRed.bridgeSubToEquHead` aligns these to a common
`.equ`-head context. The bundle's body IH is at the ORIGINAL source's
context — to invoke `Lemma_2_PaperFaithful_*_Moreover`, the body IH
must be at the bridged (common) context.

The bridge preserves derivation depth, so well-founded recursion on
`MEqRedDepth h_1 + MEqRedDepth h_2` can be used to invoke the bundle at
the bridged body context. Structural induction on h_1 alone cannot
directly express this — the body call needs the FULL bundle, not just
the IH on h_1's sub-derivations.

**Path forward** for the bundle's full assembly:
1. Define `UniformMoreoverDiamondGeneral_aux : (n : Nat) → ...` via
   well-founded recursion on `n = MEqRedDepth h_1 + MEqRedDepth h_2`.
2. AppBet/BetApp cases invoke the recursion at the bridged body context
   with depth `bodyDepth_1 + bodyDepth_2 < total + 2` (bridge preserves
   depth, body sub-derivations strictly smaller).
3. All other cases work via direct dispatch on the IH at sub-derivations.

This is the natural form. Estimated 600-1000 lines additional. -/

end Paper
end DeBruijn
end Pss

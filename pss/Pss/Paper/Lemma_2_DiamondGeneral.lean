import Pss.Mpss.DeBruijnTypeSafety
import Pss.Paper.Lemma_2_Diamond
import Pss.Paper.Lemma_2_DiamondClosure
import Pss.Paper.Lemma_2_NoPromotion
import Pss.Paper.Lemma_2_BundleProof
import Pss.Paper.Lemma_2_EqDiamondsWithMoreover
import Pss.Paper.Aux.EvolutionTransport
import Pss.Paper.Aux.CommutativityWeakening
import Pss.Paper.Investigation.Lemma_32_EquHead

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

end Paper
end DeBruijn
end Pss

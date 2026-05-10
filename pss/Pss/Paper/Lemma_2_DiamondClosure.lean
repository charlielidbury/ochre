import Pss.Paper.Lemma_2_Diamond
import Pss.Paper.Aux.CommutativityWeakening
import Pss.Paper.Aux.EvolutionTransport
import Pss.Paper.Aux.Substitution
import Pss.Paper.Investigation.Lemma_32_KindNarrowedAsymmetric
import Pss.Mpss.DeBruijnTypeSafety

/-! # `Pss.Paper.Lemma_2_DiamondClosure` — discharging the 9 case obligations

Discharges the per-case obligations declared in
`Pss.Paper.Lemma_2_Diamond` (`Lemma_2_Case_*`) by using the existing
paper-mirroring infrastructure (Lemma 19, Lemma 32 asymmetric
kind-narrowed, Lemma 36, plus `equBinds_evolve` and
`preservesNonemptyPrevalidExt` from `EvolutionTransport.lean`).

Each obligation takes recursive IHs (the diamond at smaller
sub-derivations / sub-terms) plus the outer `ContextEvolution` premises.
The discharge of each case is mechanized faithfully against the paper
proof at p. 9:21–25.

The trivial cases (`TopTop`, `VarVar`, `TApTAp`) are **already proved
unconditionally** in `EvolutionTransport.lean`; the matching paper-named
obligations here are connector functions that adapt the unconditional
proofs to the case-obligation shape.

## Status

This file is **active discharge**. Cases close incrementally; final
unconditional closure of `UniformEqDiamonds` is gated by all 9 cases.

Build green; no new axioms; no `sorry`.
-/

namespace Pss
namespace DeBruijn
namespace Paper

open ContextEvolution

/-! ## Trivial-cell discharges (paper p. 9:21 base, p. 9:25 trivials)

These are connectors to the already-proved unconditional cells in
`EvolutionTransport.lean`. They have a slightly different signature
shape than the `Prop`-defined cases in `Lemma_2_Diamond.lean`, so we
ship explicit case-obligation discharges that match the paper's grid. -/

/-- Discharge of `Lemma_2_Case_AppTAp`: the Me-TAp source forces operator
`= .top`, so all LHS reducts end at `.top` via `Me-TAp` rebuilt at the
evolved context. -/
theorem Lemma_2_Case_AppTAp_proved : Lemma_2_Case_AppTAp := by
  intro Γ₀ s₀ u₁ v₀ v₁ hOp hArg hVScoped hpv₀
    Γ₁ s₁ Γ₂ s₂ he₁ he₂
  -- hOp : MEqRed Γ₀ (v₀ :: s₀) .top u₁ → u₁ = .top by Me-Top inversion.
  have hu₁_top : u₁ = .top := hOp.top_inv
  subst hu₁_top
  -- Now LHS = .app .top v₁ → .top via Me-TAp at evolved Γ₁;s₁.
  have hpvE₁ : PrevalidExt Γ₁ s₁ :=
    Classical.choice (he₁.preservesNonemptyPrevalidExt ⟨hpv₀⟩)
  have hpvE₂ : PrevalidExt Γ₂ s₂ :=
    Classical.choice (he₂.preservesNonemptyPrevalidExt ⟨hpv₀⟩)
  have hv₁Scoped : Term.Scoped Γ₀.depth v₁ := hArg.scoped_right
  have hdepth₁ : Γ₀.depth = Γ₁.depth := he₁.preserves_ctx_depth
  have hv₁Scoped₁ : Term.Scoped Γ₁.depth v₁ := by
    rw [← hdepth₁]; exact hv₁Scoped
  refine ⟨.top, ?_, ?_⟩
  · exact ⟨MEqRed.tAp hpvE₁ hv₁Scoped₁⟩
  · exact ⟨MEqRed.top hpvE₂⟩

/-- Discharge of `Lemma_2_Case_TApTAp` via the unconditional cell. -/
theorem Lemma_2_Case_TApTAp_proved : Lemma_2_Case_TApTAp := by
  intro Γ₀ s₀ u hpv₀ hu Γ₁ s₁ Γ₂ s₂ he₁ he₂
  exact Lemma_2_TApTAp_proved_unconditional hpv₀ hu he₁ he₂

/-! ## Body transport closures (used in deeper cases)

These were left as residual payloads in the existing infrastructure but
are fully provable from `MEqRed.sub_to_equ_head_replace` (which is total:
the kind narrowing `.sub → .equ` widens the relation, and the head bound
change is fine since body's `.sub`-source forbids `Me-Pro` lookups at
index 0). -/

/-- The body transport `MEqRedSubHeadToEquHeadPayload` is provably
dischargeable: at empty stack, source `.sub`-head body transport to
`.equ`-head body with a different bound is exactly
`MEqRed.sub_to_equ_head_replace`. -/
noncomputable def MEqRedSubHeadToEquHeadPayload_proved :
    MEqRedSubHeadToEquHeadPayload := by
  intro Γ bound operand body body' hbody hOperand
  exact hbody.sub_to_equ_head_replace hOperand

/-- The Me-Fun stack-append payload follows from the body transport. -/
noncomputable def MEqRedFunStackAppendPayload_proved :
    MEqRedFunStackAppendPayload :=
  MEqRedFunStackAppendPayload.of_body_transport
    MEqRedSubHeadToEquHeadPayload_proved

/-- The general stack-append payload follows from the Me-Fun-specific
case via the structural induction in `MEqRedStackAppendPayload.of_fun`. -/
noncomputable def MEqRedStackAppendPayload_proved :
    MEqRedStackAppendPayload :=
  MEqRedStackAppendPayload.of_fun MEqRedFunStackAppendPayload_proved

/-- Stack-extend an empty-stack equivalence reduction by one operand. -/
noncomputable def MEqRed.append_operand
    {Γ : Ctx} {source target operand : Term}
    (hStep : MEqRed Γ [] source target)
    (hOperand : Term.Scoped Γ.depth operand) :
    MEqRed Γ [operand] source target := by
  simpa using MEqRedStackAppendPayload_proved (s := []) hStep hOperand

/-- Split a `PrevalidExt Γ (front ++ [op])` into the front prevalidity and
the operand scoping. -/
noncomputable def PrevalidExt.append_inv
    {Γ : Ctx} {front : Stack} {op : Term} :
    PrevalidExt Γ (front ++ [op]) →
    PrevalidExt Γ front × Term.Scoped Γ.depth op := by
  intro hpv
  induction front with
  | nil =>
    -- hpv : PrevalidExt Γ ([] ++ [op]) = PrevalidExt Γ [op].
    -- This is PrevalidExt.cons (PrevalidExt.nil hΓ) hOp.
    cases hpv with
    | cons hpvNil hOp =>
      cases hpvNil with
      | nil hΓ =>
        exact ⟨PrevalidExt.nil hΓ, hOp⟩
  | cons head rest ih =>
    -- hpv : PrevalidExt Γ (head :: rest ++ [op]) = PrevalidExt Γ (head :: (rest ++ [op])).
    cases hpv with
    | cons hpvRest hHead =>
      let ⟨hpvRest', hOp⟩ := ih hpvRest
      exact ⟨PrevalidExt.cons hpvRest' hHead, hOp⟩

/-- Lift an empty-stack equivalence reduction across an arbitrary
prevalid operand stack. Iterates the append form `s ++ [operand]` from
nil. -/
noncomputable def MEqRed.lift_empty_to_stack
    {Γ : Ctx} {s : Stack} {source target : Term}
    (hStep : MEqRed Γ [] source target)
    (hpv : PrevalidExt Γ s) :
    MEqRed Γ s source target := by
  -- Use reverse-induction so the `cons` case becomes an append.
  induction s using List.reverseRecOn with
  | nil => exact hStep
  | append_singleton front op ih =>
    -- We have MEqRed Γ front source target by ih, plus front prevalidity
    -- and op scoping; append op to get MEqRed Γ (front ++ [op]) source target.
    let ⟨hpvFront, hOp⟩ := PrevalidExt.append_inv hpv
    exact MEqRedStackAppendPayload_proved
      (s := front) (operand := op) (ih hpvFront) hOp

/-! ## ContextEvolution.cons_lift — body-context evolution lifts

For the body cases of Lemma 2 (Bet × Bet, Fun × Fun, FOp × FOp, App ×
Bet, Bet × App), the body sub-derivation lives in an extended context
`(head :: Γ₀); shift 0 s₀`. The body IH is parameterized over evolutions
of THIS extended context. To invoke the body IH after deriving the
outer evolution `Γ₀; s₀ ↣ Γ_i; s_i`, we lift the outer evolution to
the body context, producing `(head :: Γ₀); shift 0 s₀ ↣ (head :: Γ_i);
shift 0 s_i`.

The lift walks the outer derivation, rebuilding each step at the
extended context: each `ctAnn`'s bound reduction is weakened across
the new head; each `ctStk`'s stack head reduction is also weakened.
The new head is unchanged through the walk. -/

-- Note: a richer `stripStackHead'` that also returns the head reduction
-- `α → α'` is desirable for lifting the FOp body context, but requires
-- additional infrastructure for the ctRefl and ctAnn cases (the
-- ctRefl case needs `Term.Scoped` on α to construct the refl reduction;
-- the ctAnn case needs to weaken the head reduction across the new
-- head). Postponed.

/-! ## Variable-source cases (paper p. 9:21) -/

/-- Discharge of `Lemma_2_Case_ProPro`: when both sides promote the same
variable, the paper invokes prevalidity to identify the bound, then
invokes the bound IH. -/
theorem Lemma_2_Case_ProPro_proved : Lemma_2_Case_ProPro := by
  intro Γ₀ s₀ i α₀ α₁ α₂ hpv₀ hb hα₁ hα₂ hBoundIH Γ₁ s₁ Γ₂ s₂ he₁ he₂
  -- Both reductions of the same `bvar i` use the same bound `α₀` (forced
  -- by Ctx prevalidity → unique lookup). Apply the bound IH.
  exact hBoundIH he₁ he₂

/-- Discharge of `Lemma_2_Case_ProVar`: when LHS is Me-Pro (bound
reduction `α₀ → α₁`) and RHS is Me-Var (identity), the paper:
1. By Lemma 36 + multiple Ct-Ann (= `equBinds_evolve` here) finds α₂
   such that `Γ₂.equBinds i α₂` and `Γ₀; nil ⊢ α₀ → α₂`.
2. By Lemma 19 (= stack-append, our `lift_empty_to_stack`) lifts
   `α₀ → α₂` to `Γ₀; s₀`.
3. By bound IH on `Γ₀; s₀ ⊢ α₀ → α₁` against the lifted `α₀ → α₂`,
   obtains α₃ with `Γ₁; s₁ ⊢ α₁ → α₃` and `Γ₂; s₂ ⊢ α₂ → α₃`.
4. Builds RHS via Me-Pro from `Γ₂.equBinds i α₂` and the bound's α₃
   reduction. -/
theorem Lemma_2_Case_ProVar_proved : Lemma_2_Case_ProVar := by
  intro Γ₀ s₀ i α₀ α_1 hpv₀ hb hα₁ hBoundIH Γ₁ s₁ Γ₂ s₂ he₁ he₂
  -- Step 1: equBinds_evolve at he₂ gives α₂ with Γ₂.equBinds i α₂ and
  -- Γ₀; nil ⊢ α₀ → α₂.
  obtain ⟨α₂, hb₂, hRedNil⟩ :=
    he₂.equBinds_evolve hpv₀.ctx hb
  let hRedNil₀ : MEqRed Γ₀ [] α₀ α₂ := Classical.choice hRedNil
  -- Step 2: lift α₀ → α₂ from Γ₀; nil to Γ₀; s₀ via stack-append.
  let hRedAtS : MEqRed Γ₀ s₀ α₀ α₂ :=
    hRedNil₀.lift_empty_to_stack hpv₀
  -- Step 3: bound IH on hα₁ against hRedAtS at evolved contexts (he₁, he₂).
  obtain ⟨α₃, hL, hR⟩ := hBoundIH hRedAtS he₁ he₂
  -- hL : MEqRedJ Γ₁ s₁ α_1 α₃
  -- hR : MEqRedJ Γ₂ s₂ α₂ α₃
  -- Step 4: Build the LHS at Γ₁; s₁: α_1 → α₃, just hL.
  -- Build the RHS at Γ₂; s₂: bvar i → α₃ via Me-Pro from hb₂ and hR.
  let hR₀ : MEqRed Γ₂ s₂ α₂ α₃ := Classical.choice hR
  have hpv₂ : PrevalidExt Γ₂ s₂ :=
    Classical.choice (he₂.preservesNonemptyPrevalidExt ⟨hpv₀⟩)
  refine ⟨α₃, hL, ?_⟩
  exact ⟨MEqRed.pro hpv₂ hb₂ hR₀⟩

/-! ## Body-source cases (paper p. 9:23–24) — Me-Fun and Me-FOp -/

/-- Discharge of `Lemma_2_Case_FunFun`: paper p. 9:23. Both sides
descend under an unapplied abstraction with `s₀ = []`. The body
context's evolution at `({t_i, .sub} :: Γ_i); []` (note: bound = `t_i`
on each side, NOT `t₀`) is built directly via `ctAnn` from the outer
evolution + the abstraction's bound reduction. -/
theorem Lemma_2_Case_FunFun_proved : Lemma_2_Case_FunFun := by
  intro Γ₀ t₀ t₁ t₂ body₀ body₁ body₂ hT₁ hBody₁ hT₂ hBody₂
    hBoundIH hBodyIH Γ₁ s₁ Γ₂ s₂ he₁ he₂
  -- Outer stacks forced to [].
  have hs₁_nil : s₁ = [] := by
    have := he₁.preserves_stack_length
    cases s₁
    · rfl
    · simp at this
  have hs₂_nil : s₂ = [] := by
    have := he₂.preserves_stack_length
    cases s₂
    · rfl
    · simp at this
  subst hs₁_nil; subst hs₂_nil
  -- Bound diamond.
  obtain ⟨t_3, hLBound, hRBound⟩ := hBoundIH he₁ he₂
  -- Body IH: lift outer evolutions to body context via ctAnn with the
  -- ABSTRACTION'S bound reduction t₀ → t₁ (resp. t₀ → t₂). The body
  -- context's bound EVOLVES along with the abstraction's bound.
  let heBody₁ : ContextEvolution ({bound := t₀, kind := .sub} :: Γ₀) []
      ({bound := t₁, kind := .sub} :: Γ₁) [] :=
    ContextEvolution.ctAnn he₁ hT₁
  let heBody₂ : ContextEvolution ({bound := t₀, kind := .sub} :: Γ₀) []
      ({bound := t₂, kind := .sub} :: Γ₂) [] :=
    ContextEvolution.ctAnn he₂ hT₂
  obtain ⟨b_3, hLBody, hRBody⟩ := hBodyIH heBody₁ heBody₂
  -- Now we have:
  --   hLBody : MEqRedJ ({t₁, .sub} :: Γ₁) [] body₁ b_3
  --   hRBody : MEqRedJ ({t₂, .sub} :: Γ₂) [] body₂ b_3
  -- Plus bound diamond:
  --   hLBound : MEqRedJ Γ₁ [] t₁ t_3
  --   hRBound : MEqRedJ Γ₂ [] t₂ t_3
  -- Rebuild via Me-Fun:
  --   LHS: (.abs t₁ body₁) → (.abs t_3 b_3) at Γ₁; [].
  --        Me-Fun needs bound reduction `t₁ → t_3` and body reduction
  --        in `{t₁, .sub} :: Γ₁; []`. ✓ both available.
  let hLBound₀ : MEqRed Γ₁ [] t₁ t_3 := Classical.choice hLBound
  let hRBound₀ : MEqRed Γ₂ [] t₂ t_3 := Classical.choice hRBound
  let hLBody₀ : MEqRed ({bound := t₁, kind := .sub} :: Γ₁) [] body₁ b_3 :=
    Classical.choice hLBody
  let hRBody₀ : MEqRed ({bound := t₂, kind := .sub} :: Γ₂) [] body₂ b_3 :=
    Classical.choice hRBody
  refine ⟨.abs t_3 b_3, ?_, ?_⟩
  · exact ⟨MEqRed.fun_ hLBound₀ hLBody₀⟩
  · exact ⟨MEqRed.fun_ hRBound₀ hRBody₀⟩

/-! ## Body-context lifts and Bet × Bet — DEFERRED

The body cases of paper Lemma 2 (Bet × Bet, FOp × FOp, App × Bet,
Bet × App) need to lift an outer evolution `Γ₀; s₀ ↣ Γ₁; s₁` to the
body context's evolution `({bound, .sub} :: Γ₀); shift 0 s₀ ↣
({bound, .sub} :: Γ₁); shift 0 s₁`.

The `ctRefl` and `ctStk` cases of this lift are mechanical (refl on
both sides; ctStk with weakened head reduction). The `ctAnn` case
walls structurally: it would require modifying a NON-OUTERMOST entry
of the body-context, which `ContextEvolution.ctAnn` (which modifies
the outermost) doesn't directly support.

A clean discharge requires extending `ContextEvolution` with a
`weaken_outer` constructor (insert a new outermost head into an
existing evolution at the inner level). Postponed to a follow-up
dispatch.

Given this, the body cases (Bet × Bet, FOp × FOp, App × Bet, Bet × App)
remain undischarged in this commit. -/

end Paper
end DeBruijn
end Pss

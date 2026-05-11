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

/-! ## Body-context lifts via `cons_lift`

The body cases of paper Lemma 2 (Bet × Bet, FOp × FOp, App × Bet,
Bet × App) lift an outer evolution `Γ₀; s₀ ↣ Γ_i; s_i` to the body
context's evolution `(entry :: Γ₀); shift 0 s₀ ↣ (entry :: Γ_i); shift 0 s_i`
via `ContextEvolution.cons_lift`. This requires a scoping witness for
the head's `bound` at `Γ₀.depth`. -/

/-! ## Body-source cases — Me-Bet × Me-Bet (paper p. 9:25) -/

/-- Discharge of `Lemma_2_Case_BetBet`: paper p. 9:25.

Both LHS and RHS perform β. After body diamond at evolved bodies'
contexts (lifted via `cons_lift`) and operand diamond at evolved empty
stacks (after Lemma 36 to strip the stack), the joint reduct is
constructed by Lemma 32 (kind-narrowed asymmetric, closed-stack) on
each side. -/
theorem Lemma_2_Case_BetBet_proved : Lemma_2_Case_BetBet := by
  intro Γ₀ s₀ t u₀ u₁ u₂ v₀ v₁ v₂ ht hBody₁ hArg₁ hBody₂ hArg₂
    hBodyIH hArgIH Γ₁ s₁ Γ₂ s₂ he₁ he₂
  -- Lift the outer evolutions to the body context via cons_lift, using
  -- the abstraction's bound `t` as the head's bound.
  let heBody₁ : ContextEvolution
      ({bound := t, kind := .sub} :: Γ₀) (Stack.shift 0 s₀)
      ({bound := t, kind := .sub} :: Γ₁) (Stack.shift 0 s₁) :=
    ContextEvolution.cons_lift he₁ ht
  let heBody₂ : ContextEvolution
      ({bound := t, kind := .sub} :: Γ₀) (Stack.shift 0 s₀)
      ({bound := t, kind := .sub} :: Γ₂) (Stack.shift 0 s₂) :=
    ContextEvolution.cons_lift he₂ ht
  obtain ⟨u_3, hLBody, hRBody⟩ := hBodyIH heBody₁ heBody₂
  -- Strip the stacks for the operand IH via Lemma 36 (= preserves_ctx_depth
  -- + reflexivity is more direct: paper says "by Lemma 36 we obtain Γ₀; nil
  -- ↣ Γ_i; nil"). For the operand IH we need ContextEvolution Γ₀ [] Γ_i [].
  have hArgEv₁ : ContextEvolution Γ₀ [] Γ₁ [] :=
    he₁.Lemma_36_CommutativityContextWeakening
  have hArgEv₂ : ContextEvolution Γ₀ [] Γ₂ [] :=
    he₂.Lemma_36_CommutativityContextWeakening
  obtain ⟨v_3, hLArg, hRArg⟩ := hArgIH hArgEv₁ hArgEv₂
  -- Extract the underlying derivations.
  let hLBody₀ : MEqRed ({bound := t, kind := .sub} :: Γ₁)
      (Stack.shift 0 s₁) u₁ u_3 := Classical.choice hLBody
  let hRBody₀ : MEqRed ({bound := t, kind := .sub} :: Γ₂)
      (Stack.shift 0 s₂) u₂ u_3 := Classical.choice hRBody
  let hLArg₀ : MEqRed Γ₁ [] v₁ v_3 := Classical.choice hLArg
  let hRArg₀ : MEqRed Γ₂ [] v₂ v_3 := Classical.choice hRArg
  -- Scoping witnesses for v_1, v_2, v_3 at their respective contexts.
  have hv₁Scoped₁ : Term.Scoped Γ₁.depth v₁ := hLArg₀.scoped_left
  have hv₃Scoped₁ : Term.Scoped Γ₁.depth v_3 := hLArg₀.scoped_right
  have hv₂Scoped₂ : Term.Scoped Γ₂.depth v₂ := hRArg₀.scoped_left
  have hv₃Scoped₂ : Term.Scoped Γ₂.depth v_3 := hRArg₀.scoped_right
  have htScoped₁ : Term.Scoped Γ₁.depth t := by
    have : Γ₀.depth = Γ₁.depth := he₁.preserves_ctx_depth
    rw [← this]; exact ht
  have htScoped₂ : Term.Scoped Γ₂.depth t := by
    have : Γ₀.depth = Γ₂.depth := he₂.preserves_ctx_depth
    rw [← this]; exact ht
  -- Apply Lemma 32 (kind-narrowed asymmetric closed) on each side.
  -- LHS: at Γ₁, source bound is t, LHS arg v₁, RHS arg v₃; body diamond
  -- hLBody₀ : MEqRed ({t,.sub}::Γ₁) (shift 0 s₁) u₁ u_3.
  -- Result: MEqRed Γ₁ (Stack.instantiate 0 v₁ (shift 0 s₁))
  --                 (Term.instantiate 0 v₁ u₁) (Term.instantiate 0 v₃ u_3).
  -- We need: MEqRed Γ₁ s₁ (instantiate 0 v₁ u₁) (instantiate 0 v_3 u_3).
  -- Use Stack.instantiate_shiftBy_zero_tail to simplify the stack.
  have hL := Investigation.Lemma_32_KindNarrowedAsymmetric_proved_closed
    (Γ := Γ₁) (t := t) (arg := v₁) (arg' := v_3)
    (lhs := u₁) (rhs := u_3) (s := Stack.shift 0 s₁)
    htScoped₁ hv₁Scoped₁ hv₃Scoped₁ hLArg₀ hLBody₀
  -- Stack.instantiate 0 v₁ (Stack.shift 0 s₁) = s₁.
  have hStackSimp₁ :
      Stack.instantiate 0 v₁ (Stack.shift 0 s₁) = s₁ := by
    have h := Stack.instantiate_shiftBy_zero_tail (n := 0) (v := v₁) (s := s₁)
    -- Stack.shiftBy 0 0 s = s by induction on s.
    have hsBy_zero : ∀ (sx : Stack), Stack.shiftBy 0 0 sx = sx := by
      intro sx
      induction sx with
      | nil => rfl
      | cons α t ih =>
          show Term.shiftBy 0 0 α :: Stack.shiftBy 0 0 t = α :: t
          rw [Term.shiftBy_zero_id, ih]
    rw [hsBy_zero] at h
    simpa [Term.shiftBy_zero_id, Stack.shift] using h
  rw [hStackSimp₁] at hL
  -- RHS: at Γ₂.
  have hR := Investigation.Lemma_32_KindNarrowedAsymmetric_proved_closed
    (Γ := Γ₂) (t := t) (arg := v₂) (arg' := v_3)
    (lhs := u₂) (rhs := u_3) (s := Stack.shift 0 s₂)
    htScoped₂ hv₂Scoped₂ hv₃Scoped₂ hRArg₀ hRBody₀
  have hStackSimp₂ :
      Stack.instantiate 0 v₂ (Stack.shift 0 s₂) = s₂ := by
    have h := Stack.instantiate_shiftBy_zero_tail (n := 0) (v := v₂) (s := s₂)
    have hsBy_zero : ∀ (sx : Stack), Stack.shiftBy 0 0 sx = sx := by
      intro sx
      induction sx with
      | nil => rfl
      | cons α t ih =>
          show Term.shiftBy 0 0 α :: Stack.shiftBy 0 0 t = α :: t
          rw [Term.shiftBy_zero_id, ih]
    rw [hsBy_zero] at h
    simpa [Term.shiftBy_zero_id, Stack.shift] using h
  rw [hStackSimp₂] at hR
  exact ⟨Term.instantiate 0 v_3 u_3, ⟨hL⟩, ⟨hR⟩⟩

/-! ## Me-App × Me-App (paper p. 9:21–22) -/

/-- Discharge of `Lemma_2_Case_AppApp`: paper p. 9:21-22.

Both sides do Me-App. Operator IH at expanded stack `v_i :: s_i`; operand
IH at empty stack. Paper uses Ct-Stk to build the operator evolutions.

The key insight (paper p. 9:22): "By rule Ct-Stk, we know
Γ_0; v_0 :: s_0 ↣ Γ_1; v_1 :: s_1 from Γ_0; nil ⊢ v_0 → v_1." -/
theorem Lemma_2_Case_AppApp_proved : Lemma_2_Case_AppApp := by
  intro Γ₀ s₀ u₀ u₁ u₂ v₀ v₁ v₂ hOp₁ hArg₁ hOp₂ hArg₂ hOpIH hArgIH
    Γ₁ s₁ Γ₂ s₂ he₁ he₂
  -- Operand diamond at evolved []: use Lemma 36 to strip stacks.
  have hArgEv₁ : ContextEvolution Γ₀ [] Γ₁ [] :=
    he₁.Lemma_36_CommutativityContextWeakening
  have hArgEv₂ : ContextEvolution Γ₀ [] Γ₂ [] :=
    he₂.Lemma_36_CommutativityContextWeakening
  obtain ⟨v_3, hLArg, hRArg⟩ := hArgIH hArgEv₁ hArgEv₂
  let hLArg₀ : MEqRed Γ₁ [] v₁ v_3 := Classical.choice hLArg
  let hRArg₀ : MEqRed Γ₂ [] v₂ v_3 := Classical.choice hRArg
  -- Operator IH at evolved (v_i :: s_i): use Ct-Stk to build operator
  -- evolutions from the existing he_i + the operand head reductions
  -- (lifted from Γ₀ to Γ_i context via paper's Ct-Stk pattern).
  -- Actually paper applies Ct-Stk on the SOURCE side: from
  -- Γ₀; s₀ ↣ Γ_i; s_i_inner (the strip) and Γ₀; nil ⊢ v_0 → v_i, build
  -- Γ₀; v_0 :: s_0 ↣ Γ_i; v_i :: s_i_inner. But our he_i is already at
  -- (v_0 :: s_0). Strip the head and rebuild with the new operand.
  -- WAIT: our he_i is at outer stack s₀, NOT (v_0 :: s_0). Looking at
  -- the obligation: he_1 : ContextEvolution Γ₀ s₀ Γ₁ s_1. We need to
  -- INVOKE the operator IH at evolution Γ₀ (v_0 :: s_0) ↣ Γ_? (v_? :: s_?).
  -- Build this via Ct-Stk from he_i + the operand-head reduction.
  -- Operand head reduction: MEqRed Γ₀ [] v_0 v_i. From hArg_i.
  let heOp₁ : ContextEvolution Γ₀ (v₀ :: s₀) Γ₁ (v₁ :: s₁) :=
    ContextEvolution.ctStk he₁ hArg₁
  let heOp₂ : ContextEvolution Γ₀ (v₀ :: s₀) Γ₂ (v₂ :: s₂) :=
    ContextEvolution.ctStk he₂ hArg₂
  -- Operator IH gives u_3 at (v_i :: s_i).
  obtain ⟨u_3, hLOp, hROp⟩ := hOpIH heOp₁ heOp₂
  let hLOp₀ : MEqRed Γ₁ (v₁ :: s₁) u₁ u_3 := Classical.choice hLOp
  let hROp₀ : MEqRed Γ₂ (v₂ :: s₂) u₂ u_3 := Classical.choice hROp
  -- Now we need the joint reduct. Paper's reasoning: the operator
  -- IH gives u_1 → u_3 at v_1 :: s_1 and u_2 → u_3 at v_2 :: s_2.
  -- Then we build Me-App on each side.
  -- LHS: Me-App from hLOp₀ (u_1 → u_3 at v_1 :: s_1) + arg reduction
  -- v_1 → v_3 at [] = hLArg₀. Result: (.app u_1 v_1) → (.app u_3 v_3) at Γ_1; s_1.
  refine ⟨.app u_3 v_3, ?_, ?_⟩
  · exact ⟨MEqRed.app hLOp₀ hLArg₀⟩
  · exact ⟨MEqRed.app hROp₀ hRArg₀⟩

/-! ## Me-App × Me-Bet (paper p. 9:22-23) — cross-β case

The cross-β case where LHS is Me-App and RHS is Me-Bet. The paper's
proof (p. 9:22-23) uses the Ct-Ann body-context evolution mid-proof
(translated to de Bruijn as `cons_evolve` with the operand head
reduction), plus the Moreover NP-0 propagation for the equ→sub bridge
in the LHS output rebuild, plus Lemma 32 (asymmetric, kind-narrowed)
for the RHS output rebuild. -/

/-- Discharge of `Lemma_2_Case_AppBet`: paper p. 9:22-23. -/
theorem Lemma_2_Case_AppBet_proved : Lemma_2_Case_AppBet := by
  intro Γ₀ s₀ t₀ u₀ u₁ u₂ v₀ v₁ v₂ t₁
    ht₀Scoped hv₀Scoped hT₁ hBody₁ hArg₁ hBody₂ hArg₂
    hBodyIH hArgIH Γ₁ s₁ Γ₂ s₂ he₁ he₂
  -- Operand IH at evolved Γ₀; [].
  have hArgEv₁ : ContextEvolution Γ₀ [] Γ₁ [] :=
    he₁.Lemma_36_CommutativityContextWeakening
  have hArgEv₂ : ContextEvolution Γ₀ [] Γ₂ [] :=
    he₂.Lemma_36_CommutativityContextWeakening
  obtain ⟨v_3, hLArg, hRArg⟩ := hArgIH hArgEv₁ hArgEv₂
  let hLArg₀ : MEqRed Γ₁ [] v₁ v_3 := Classical.choice hLArg
  let hRArg₀ : MEqRed Γ₂ [] v₂ v_3 := Classical.choice hRArg
  -- Body context evolutions:
  --   LHS body: ({v_0, .equ}::Γ_0; shift 0 s_0) ↣ ({v_1, .equ}::Γ_1; shift 0 s_1)
  --     via cons_evolve he₁ hArg₁.
  --   RHS body: ({t_0, .sub}::Γ_0; shift 0 s_0) ↣ ({t_0, .sub}::Γ_2; shift 0 s_2)
  --     via cons_lift he₂ ht₀Scoped (bound unchanged on RHS).
  let heBody₁ : ContextEvolution ({bound := v₀, kind := .equ} :: Γ₀)
      (Stack.shift 0 s₀)
      ({bound := v₁, kind := .equ} :: Γ₁) (Stack.shift 0 s₁) :=
    ContextEvolution.cons_evolve he₁ hArg₁
  let heBody₂ : ContextEvolution ({bound := t₀, kind := .sub} :: Γ₀)
      (Stack.shift 0 s₀)
      ({bound := t₀, kind := .sub} :: Γ₂) (Stack.shift 0 s₂) :=
    ContextEvolution.cons_lift he₂ ht₀Scoped
  -- Body IH with Moreover: d_1 has NP-0.
  obtain ⟨u_3, d_1, d_2, hd_1_NP⟩ := hBodyIH heBody₁ heBody₂
  -- d_1 : MEqRed ({v_1, .equ} :: Γ_1) (shift 0 s_1) u_1 u_3
  -- d_2 : MEqRed ({t_0, .sub} :: Γ_2) (shift 0 s_2) u_2 u_3
  -- For LHS output: target is `instantiate 0 v_3 u_3`. Build via Me-Bet.
  -- Me-Bet requires:
  --   Term.Scoped Γ_1.depth t_1
  --   MEqRed ({t_1, .sub} :: Γ_1) (shift 0 s_1) u_1 u_3 — bridge d_1
  --     via equ_to_sub_head_replace_NoPromotion using hd_1_NP.
  --   MEqRed Γ_1 [] v_1 v_3
  have ht₁Scoped : Term.Scoped Γ₁.depth t₁ := by
    have h : Term.Scoped Γ₀.depth t₁ := hT₁.scoped_right
    rw [he₁.preserves_ctx_depth] at h
    exact h
  let d_1_bridged : MEqRed ({bound := t₁, kind := .sub} :: Γ₁)
      (Stack.shift 0 s₁) u₁ u_3 :=
    d_1.equ_to_sub_head_replace_NoPromotion hd_1_NP ht₁Scoped
  -- For RHS output: target is `instantiate 0 v_3 u_3`. Use Lemma 32
  -- (asymmetric, kind-narrowed, closed-stack).
  -- Lemma 32 needs:
  --   Term.Scoped Γ_2.depth t_0
  --   Term.Scoped Γ_2.depth v_2
  --   Term.Scoped Γ_2.depth v_3
  --   MEqRed Γ_2 [] v_2 v_3 (= hRArg₀)
  --   MEqRed ({t_0, .sub} :: Γ_2) (shift 0 s_2) u_2 u_3 (= d_2)
  -- Result: MEqRed Γ_2 (Stack.instantiate 0 v_2 (shift 0 s_2))
  --                    (instantiate 0 v_2 u_2) (instantiate 0 v_3 u_3).
  -- Stack.instantiate 0 v_2 (shift 0 s_2) = s_2.
  have ht₀_at_Γ₂ : Term.Scoped Γ₂.depth t₀ := by
    have h : Term.Scoped Γ₀.depth t₀ := ht₀Scoped
    rw [he₂.preserves_ctx_depth] at h
    exact h
  have hv₂Scoped : Term.Scoped Γ₂.depth v₂ := hRArg₀.scoped_left
  have hv_3_at_Γ₂ : Term.Scoped Γ₂.depth v_3 := hRArg₀.scoped_right
  have hRHS_pre := Investigation.Lemma_32_KindNarrowedAsymmetric_proved_closed
    (Γ := Γ₂) (t := t₀) (arg := v₂) (arg' := v_3)
    (lhs := u₂) (rhs := u_3) (s := Stack.shift 0 s₂)
    ht₀_at_Γ₂ hv₂Scoped hv_3_at_Γ₂ hRArg₀ d_2
  -- Stack.instantiate 0 v₂ (Stack.shift 0 s₂) = s₂.
  have hStackSimp :
      Stack.instantiate 0 v₂ (Stack.shift 0 s₂) = s₂ := by
    have h := Stack.instantiate_shiftBy_zero_tail (n := 0) (v := v₂) (s := s₂)
    have hsBy_zero : ∀ (sx : Stack), Stack.shiftBy 0 0 sx = sx := by
      intro sx
      induction sx with
      | nil => rfl
      | cons α t ih =>
          show Term.shiftBy 0 0 α :: Stack.shiftBy 0 0 t = α :: t
          rw [Term.shiftBy_zero_id, ih]
    rw [hsBy_zero] at h
    simpa [Term.shiftBy_zero_id, Stack.shift] using h
  rw [hStackSimp] at hRHS_pre
  -- LHS output via Me-Bet.
  let hLHS_out : MEqRed Γ₁ s₁
      (.app (.abs t₁ u₁) v₁) (Term.instantiate 0 v_3 u_3) :=
    MEqRed.bet ht₁Scoped d_1_bridged hLArg₀
  refine ⟨Term.instantiate 0 v_3 u_3, ?_, ?_⟩
  · exact ⟨hLHS_out⟩
  · exact ⟨hRHS_pre⟩

/-! ## Me-Bet × Me-App (paper p. 9:22-23 mirrored) — cross-β case (symmetric)

Symmetric to AppBet: LHS does Me-Bet (β with .sub-head body), RHS does
Me-App (Me-FOp inversion gives .equ-head body). Structure is identical
to AppBet with sides swapped. -/

/-- Discharge of `Lemma_2_Case_BetApp`: paper p. 9:22-23 mirrored. -/
theorem Lemma_2_Case_BetApp_proved : Lemma_2_Case_BetApp := by
  intro Γ₀ s₀ t₀ u₀ u₁ u₂ v₀ v₁ v₂ t₂
    ht₀Scoped hv₀Scoped hBody₁ hArg₁ hT₂ hBody₂ hArg₂
    hBodyIH hArgIH Γ₁ s₁ Γ₂ s₂ he₁ he₂
  have hArgEv₁ : ContextEvolution Γ₀ [] Γ₁ [] :=
    he₁.Lemma_36_CommutativityContextWeakening
  have hArgEv₂ : ContextEvolution Γ₀ [] Γ₂ [] :=
    he₂.Lemma_36_CommutativityContextWeakening
  obtain ⟨v_3, hLArg, hRArg⟩ := hArgIH hArgEv₁ hArgEv₂
  let hLArg₀ : MEqRed Γ₁ [] v₁ v_3 := Classical.choice hLArg
  let hRArg₀ : MEqRed Γ₂ [] v₂ v_3 := Classical.choice hRArg
  -- Body context evolutions:
  --   LHS body: ({t_0, .sub}::Γ_0) ↣ ({t_0, .sub}::Γ_1) via cons_lift.
  --   RHS body: ({v_0, .equ}::Γ_0) ↣ ({v_2, .equ}::Γ_2) via cons_evolve.
  let heBody₁ : ContextEvolution ({bound := t₀, kind := .sub} :: Γ₀)
      (Stack.shift 0 s₀)
      ({bound := t₀, kind := .sub} :: Γ₁) (Stack.shift 0 s₁) :=
    ContextEvolution.cons_lift he₁ ht₀Scoped
  let heBody₂ : ContextEvolution ({bound := v₀, kind := .equ} :: Γ₀)
      (Stack.shift 0 s₀)
      ({bound := v₂, kind := .equ} :: Γ₂) (Stack.shift 0 s₂) :=
    ContextEvolution.cons_evolve he₂ hArg₂
  obtain ⟨u_3, d_1, d_2, hd_2_NP⟩ := hBodyIH heBody₁ heBody₂
  -- d_1 : MEqRed ({t_0, .sub} :: Γ_1) (shift 0 s_1) u_1 u_3
  -- d_2 : MEqRed ({v_2, .equ} :: Γ_2) (shift 0 s_2) u_2 u_3
  -- LHS output: target = `instantiate 0 v_3 u_3`. Use Lemma 32 (asymm, kind-narrowed).
  have ht₀_at_Γ₁ : Term.Scoped Γ₁.depth t₀ := by
    have h : Term.Scoped Γ₀.depth t₀ := ht₀Scoped
    rw [he₁.preserves_ctx_depth] at h
    exact h
  have hv₁Scoped : Term.Scoped Γ₁.depth v₁ := hLArg₀.scoped_left
  have hv_3_at_Γ₁ : Term.Scoped Γ₁.depth v_3 := hLArg₀.scoped_right
  have hLHS_pre := Investigation.Lemma_32_KindNarrowedAsymmetric_proved_closed
    (Γ := Γ₁) (t := t₀) (arg := v₁) (arg' := v_3)
    (lhs := u₁) (rhs := u_3) (s := Stack.shift 0 s₁)
    ht₀_at_Γ₁ hv₁Scoped hv_3_at_Γ₁ hLArg₀ d_1
  have hStackSimp₁ :
      Stack.instantiate 0 v₁ (Stack.shift 0 s₁) = s₁ := by
    have h := Stack.instantiate_shiftBy_zero_tail (n := 0) (v := v₁) (s := s₁)
    have hsBy_zero : ∀ (sx : Stack), Stack.shiftBy 0 0 sx = sx := by
      intro sx
      induction sx with
      | nil => rfl
      | cons α t ih =>
          show Term.shiftBy 0 0 α :: Stack.shiftBy 0 0 t = α :: t
          rw [Term.shiftBy_zero_id, ih]
    rw [hsBy_zero] at h
    simpa [Term.shiftBy_zero_id, Stack.shift] using h
  rw [hStackSimp₁] at hLHS_pre
  -- RHS output: target = `instantiate 0 v_3 u_3`. Use Me-Bet on RHS source.
  -- Me-Bet requires:
  --   Term.Scoped Γ_2.depth t_2
  --   MEqRed ({t_2, .sub} :: Γ_2) (shift 0 s_2) u_2 u_3 — bridge d_2.
  --   MEqRed Γ_2 [] v_2 v_3
  have ht₂Scoped : Term.Scoped Γ₂.depth t₂ := by
    have h : Term.Scoped Γ₀.depth t₂ := hT₂.scoped_right
    rw [he₂.preserves_ctx_depth] at h
    exact h
  let d_2_bridged : MEqRed ({bound := t₂, kind := .sub} :: Γ₂)
      (Stack.shift 0 s₂) u₂ u_3 :=
    d_2.equ_to_sub_head_replace_NoPromotion hd_2_NP ht₂Scoped
  let hRHS_out : MEqRed Γ₂ s₂
      (.app (.abs t₂ u₂) v₂) (Term.instantiate 0 v_3 u_3) :=
    MEqRed.bet ht₂Scoped d_2_bridged hRArg₀
  refine ⟨Term.instantiate 0 v_3 u_3, ?_, ?_⟩
  · exact ⟨hLHS_pre⟩
  · exact ⟨hRHS_out⟩

/-! ## Me-FOp × Me-FOp (paper p. 9:24)

Both sides do Me-FOp: the outer stack starts with `α`, which is popped
into a `.equ`-head body context with bound = α. The body diamond happens
in the (evolved) body context. The bound `t_0 →= t_i` reduces at empty
stack.

For the body context's evolution, we extract α →= α_i from the outer
evolution via `stripStackHeadWithReduction`, then build the body
context's evolution via `cons_evolve` (= `ctAnn` with shifted stack). -/

/-- Discharge of `Lemma_2_Case_FOpFOp`: paper p. 9:24. -/
theorem Lemma_2_Case_FOpFOp_proved : Lemma_2_Case_FOpFOp := by
  intro Γ₀ s₀ α t₀ t₁ t₂ body₀ body₁ body₂ hαScoped hT₁ hBody₁ hT₂ hBody₂
    hBoundIH hBodyIH Γ₁ s₁ Γ₂ s₂ he₁ he₂
  -- Outer stack length forces s_i to start with some α_i.
  have hLen₁ := he₁.preserves_stack_length
  have hLen₂ := he₂.preserves_stack_length
  -- s_1 has form α_1 :: s_inner_1.
  cases s₁ with
  | nil => simp at hLen₁
  | cons α_1 s_inner_1 =>
  cases s₂ with
  | nil => simp at hLen₂
  | cons α_2 s_inner_2 =>
  -- Get PrevalidExt for the outer source context Γ₀; α::s₀.
  -- Strategy: hBody₁ : MEqRed ({α,.equ}::Γ₀) (shift 0 s₀) body₀ body₁ gives
  -- PrevalidExt ({α,.equ}::Γ₀) (shift 0 s₀). Extract: Prevalid Γ₀ (via tail
  -- of context) and Stack.Scoped Γ₀.depth s₀ (via shift_inv). Recombine:
  -- PrevalidExt Γ₀ s₀ via of_stack_scoped, then PrevalidExt.cons with hαScoped.
  have hpvE_body : PrevalidExt ({bound := α, kind := .equ} :: Γ₀)
      (Stack.shift 0 s₀) := hBody₁.prevalidExt
  have hpvCtx_body : Prevalid ({bound := α, kind := .equ} :: Γ₀) :=
    PrevalidExt.ctx hpvE_body
  have hpvCtx₀ : Prevalid Γ₀ := Prevalid.tail hpvCtx_body
  have hStackScopedShifted' : Stack.Scoped (Γ₀.depth + 1) (Stack.shift 0 s₀) := by
    have h := PrevalidExt.stack_scoped hpvE_body
    simpa [Ctx.depth_cons] using h
  have hStackScoped₀ : Stack.Scoped Γ₀.depth s₀ :=
    Stack.Scoped.shift_inv hStackScopedShifted'
  have hpvE_s₀ : PrevalidExt Γ₀ s₀ :=
    PrevalidExt.of_stack_scoped hpvCtx₀ hStackScoped₀
  have hpvE₀ : PrevalidExt Γ₀ (α :: s₀) := PrevalidExt.cons hpvE_s₀ hαScoped
  -- Extract head reductions and stripped evolutions via stripStackHeadWithReduction.
  obtain ⟨hHead₁_ne, heStrip₁⟩ :=
    ContextEvolution.stripStackHeadWithReduction he₁ hαScoped hpvE₀
  obtain ⟨hHead₂_ne, heStrip₂⟩ :=
    ContextEvolution.stripStackHeadWithReduction he₂ hαScoped hpvE₀
  let hHead₁ : MEqRed Γ₀ [] α α_1 := Classical.choice hHead₁_ne
  let hHead₂ : MEqRed Γ₀ [] α α_2 := Classical.choice hHead₂_ne
  -- Bound IH at evolved Γ₀;[] ↣ Γ_i;[]: strip stacks from stripped evolutions
  -- via Lemma 36.
  have hBoundEv₁ : ContextEvolution Γ₀ [] Γ₁ [] :=
    heStrip₁.Lemma_36_CommutativityContextWeakening
  have hBoundEv₂ : ContextEvolution Γ₀ [] Γ₂ [] :=
    heStrip₂.Lemma_36_CommutativityContextWeakening
  obtain ⟨t_3, hLBound, hRBound⟩ := hBoundIH hBoundEv₁ hBoundEv₂
  let hLBound₀ : MEqRed Γ₁ [] t₁ t_3 := Classical.choice hLBound
  let hRBound₀ : MEqRed Γ₂ [] t₂ t_3 := Classical.choice hRBound
  -- Body context evolutions via cons_evolve.
  let heBody₁ : ContextEvolution ({bound := α, kind := .equ} :: Γ₀)
      (Stack.shift 0 s₀)
      ({bound := α_1, kind := .equ} :: Γ₁) (Stack.shift 0 s_inner_1) :=
    ContextEvolution.cons_evolve heStrip₁ hHead₁
  let heBody₂ : ContextEvolution ({bound := α, kind := .equ} :: Γ₀)
      (Stack.shift 0 s₀)
      ({bound := α_2, kind := .equ} :: Γ₂) (Stack.shift 0 s_inner_2) :=
    ContextEvolution.cons_evolve heStrip₂ hHead₂
  obtain ⟨b_3, hLBody, hRBody⟩ := hBodyIH heBody₁ heBody₂
  let hLBody₀ : MEqRed ({bound := α_1, kind := .equ} :: Γ₁)
      (Stack.shift 0 s_inner_1) body₁ b_3 := Classical.choice hLBody
  let hRBody₀ : MEqRed ({bound := α_2, kind := .equ} :: Γ₂)
      (Stack.shift 0 s_inner_2) body₂ b_3 := Classical.choice hRBody
  -- Build outputs via Me-FOp.
  -- LHS: MEqRed Γ_1 (α_1 :: s_inner_1) (abs t_1 body_1) (abs t_3 b_3)
  -- Me-FOp requires:
  --   MEqRed Γ_1 [] t_1 t_3 ✓ hLBound₀
  --   Term.Scoped Γ_1.depth α_1
  --   MEqRed ({α_1, .equ} :: Γ_1) (shift 0 s_inner_1) body_1 b_3 ✓ hLBody₀
  have hα₁Scoped : Term.Scoped Γ₁.depth α_1 := by
    have h : Term.Scoped Γ₀.depth α_1 := hHead₁.scoped_right
    rw [heStrip₁.preserves_ctx_depth] at h
    exact h
  have hα₂Scoped : Term.Scoped Γ₂.depth α_2 := by
    have h : Term.Scoped Γ₀.depth α_2 := hHead₂.scoped_right
    rw [heStrip₂.preserves_ctx_depth] at h
    exact h
  refine ⟨.abs t_3 b_3, ?_, ?_⟩
  · exact ⟨MEqRed.fOp hLBound₀ hα₁Scoped hLBody₀⟩
  · exact ⟨MEqRed.fOp hRBound₀ hα₂Scoped hRBody₀⟩

end Paper
end DeBruijn
end Pss

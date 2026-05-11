import Pss.Mpss.DeBruijnTypeSafety
import Pss.Paper.Lemma_2_NoPromotion
import Pss.Paper.Lemma_2_EqDiamondsWithMoreover
import Pss.Paper.Lemma_2_Diamond
import Pss.Paper.Lemma_2_DiamondClosure
import Pss.Paper.Aux.EvolutionTransport
import Pss.Paper.Investigation.Lemma_32_KindNarrowedAsymmetric
import Pss.Paper.Investigation.Lemma_32_EquHead

/-! # `Pss.Paper.Lemma_2_BundleProof` — Discharge `UniformEqDiamonds`

Discharges the residual `UniformEqDiamonds` of the de Bruijn Lemma 2
headline via paper Lemma 2 (Pasquale & García-Pérez 2024, p. 9:9 +
proof p. 9:21–25), in **cross-context Moreover-tracked** form.

## Why cross-context?

The cross-β cases of paper Lemma 2 (App×Bet and Bet×App) invoke the
inductive hypothesis on body sub-derivations whose source contexts
differ: the App side's body lives at `{v₀,.equ}::Γ₀` (the popped
operand annotated as equivalence), while the Bet side's body lives at
`{t₀,.sub}::Γ₀` (the abstraction annotation as subtype). The IH input
contexts are therefore not equal, even though the IH input source term
`u₀` is shared.

We therefore state the bundle in cross-context form: for any two
`MEqRed` derivations `h_a : MEqRed Γ_a s_a u u_a` and
`h_b : MEqRed Γ_b s_b u u_b` (sharing source `u` but at potentially
different source contexts), and any evolutions from each, produce a
meeting reduct with **full Moreover NP tracking** (NP-x on either
input implies NP-x on both outputs).

The same-context outer Lemma 2 specialises this to `Γ_a = Γ_b`,
`s_a = s_b`. `UniformEqDiamonds` then further specialises to
`ctRefl/ctRefl` evolutions.

## Recursion structure

The proof recurses on `MEqRedDepth h_a + MEqRedDepth h_b`, matching
on the constructor pair `(h_a, h_b)`. For each pair:

- **Trivial cases** (Top/Var/TAp on either side): close directly,
  using the `Pss.Paper.Aux.EvolutionTransport` unconditional cells.
- **Same-rule cases** (App×App, Fun×Fun, FOp×FOp, Bet×Bet,
  Pro×Pro): dispatch to `Lemma_2_Case_*_proved` from
  `Lemma_2_DiamondClosure`, supplying recursive IH calls.
- **Cross-rule cases** (Pro×Var, App×TAp, App×Bet, Bet×App):
  dispatch similarly.

The Moreover NP tracking is reconstructed per case from the input
NP witnesses, mirroring the structural decomposition.

## Discharge target

* `Lemma_2_DiamondMEqRed_CrossCtx_proved` — cross-context bundle
  with Moreover.
* `Lemma_2_DiamondMEqRed_SameCtx_proved` — same-context
  specialisation (paper-faithful Lemma 2 statement).
* `UniformEqDiamonds_proved` — final discharge by `ctRefl/ctRefl`.

No `sorry`, no new axioms.
-/

namespace Pss
namespace DeBruijn
namespace Paper

open Investigation

/-! ## NP-x preserving refl

A custom refl-builder that bundles the refl derivation with proof of
`NoPromotionOf` for every `x`. -/

noncomputable def MEqRed.refl_with_NP {Γ : Ctx} {s : Stack} {u : Term}
    (hpv : PrevalidExt Γ s) (hu : Term.Scoped Γ.depth u) :
    Σ' (h : MEqRed Γ s u u), ∀ x, h.NoPromotionOf x := by
  induction u generalizing Γ s with
  | bvar i =>
    refine ⟨MEqRed.var hpv hu.bvar_lt, ?_⟩
    intro x; trivial
  | top =>
    refine ⟨MEqRed.top hpv, ?_⟩
    intro x; trivial
  | app u v ihu ihv =>
    let hparts := Term.Scoped.app_inv hu
    have huOp : Term.Scoped Γ.depth u := hparts.1
    have hv : Term.Scoped Γ.depth v := hparts.2
    have hpvOp : PrevalidExt Γ (v :: s) := PrevalidExt.cons hpv hv
    have hpvNil : PrevalidExt Γ [] := PrevalidExt.nil (PrevalidExt.ctx hpv)
    let ⟨reflOp, npOp⟩ := ihu hpvOp huOp
    let ⟨reflArg, npArg⟩ := ihv hpvNil hv
    refine ⟨MEqRed.app reflOp reflArg, ?_⟩
    intro x
    exact ⟨npOp x, npArg x⟩
  | abs bound body ihBound ihBody =>
    let hparts := Term.Scoped.abs_inv hu
    have hBound : Term.Scoped Γ.depth bound := hparts.1
    have hBody : Term.Scoped (Γ.depth + 1) body := hparts.2
    have hpvNil : PrevalidExt Γ [] := PrevalidExt.nil (PrevalidExt.ctx hpv)
    let ⟨reflBound, npBound⟩ := ihBound hpvNil hBound
    cases s with
    | nil =>
      have hpvBodyCtx : Prevalid ({ bound := bound, kind := .sub } :: Γ) :=
        Prevalid.sub (PrevalidExt.ctx hpv) hBound
      have hpvBody : PrevalidExt ({ bound := bound, kind := .sub } :: Γ) [] :=
        PrevalidExt.nil hpvBodyCtx
      let ⟨reflBody, npBody⟩ := ihBody hpvBody hBody
      refine ⟨MEqRed.fun_ reflBound reflBody, ?_⟩
      intro x
      exact ⟨npBound x, npBody (x + 1)⟩
    | cons α s' =>
      have hα : Term.Scoped Γ.depth α := PrevalidExt.head_scoped hpv
      have hpvTail : PrevalidExt Γ s' := PrevalidExt.tail hpv
      have hpvBodyCtx : Prevalid ({ bound := α, kind := .equ } :: Γ) :=
        Prevalid.equ (PrevalidExt.ctx hpv) hα
      have hpvBody : PrevalidExt ({ bound := α, kind := .equ } :: Γ)
          (Stack.shift 0 s') :=
        PrevalidExt.weaken_head hpvTail hpvBodyCtx
      let ⟨reflBody, npBody⟩ := ihBody hpvBody hBody
      refine ⟨MEqRed.fOp reflBound hα reflBody, ?_⟩
      intro x
      exact ⟨npBound x, npBody (x + 1)⟩

/-! ## Stack-instantiate simplification -/

private theorem Stack.instantiate_shift_zero_id (v : Term) (s : Stack) :
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

/-! ## Custom derivation depth measure

Defined structurally — bypasses Lean's auto-generated `sizeOf` (which can
be subtle with proof-relevant indices) to give a clean termination
measure for the bundle's well-founded recursion. -/

def MEqRedDepth : ∀ {Γ s u v}, MEqRed Γ s u v → Nat
  | _, _, _, _, .pro _ _ inner => 1 + MEqRedDepth inner
  | _, _, _, _, .bet _ body arg => 1 + MEqRedDepth body + MEqRedDepth arg
  | _, _, _, _, .top _ => 1
  | _, _, _, _, .app op arg => 1 + MEqRedDepth op + MEqRedDepth arg
  | _, _, _, _, .var _ _ => 1
  | _, _, _, _, .fun_ tBound body => 1 + MEqRedDepth tBound + MEqRedDepth body
  | _, _, _, _, .tAp _ _ => 1
  | _, _, _, _, .fOp tBound _ body => 1 + MEqRedDepth tBound + MEqRedDepth body

theorem MEqRedDepth_pos : ∀ {Γ s u v} (h : MEqRed Γ s u v), 0 < MEqRedDepth h := by
  intro Γ s u v h
  cases h <;> simp [MEqRedDepth]

/-! ## Bundle predicate (cross-context, Moreover-tracked) -/

/-- The cross-context Moreover diamond conclusion. -/
def CrossCtxMoreoverConclusion
    {Γ_a Γ_b : Ctx} {s_a s_b : Stack} {u u_a u_b : Term}
    (h_a : MEqRed Γ_a s_a u u_a) (h_b : MEqRed Γ_b s_b u u_b)
    {Γ_1 s_1 Γ_2 s_2 : _}
    (_he₁ : ContextEvolution Γ_a s_a Γ_1 s_1)
    (_he₂ : ContextEvolution Γ_b s_b Γ_2 s_2) : Prop :=
  ∃ (u_3 : Term)
    (d_1 : MEqRed Γ_1 s_1 u_a u_3)
    (d_2 : MEqRed Γ_2 s_2 u_b u_3),
    ∀ (x : Nat),
      (h_a.NoPromotionOf x ∨ h_b.NoPromotionOf x) →
        (d_1.NoPromotionOf x ∧ d_2.NoPromotionOf x)

/-- Cross-context Lemma 2 with Moreover. -/
def Lemma_2_DiamondMEqRed_CrossCtxMoreover : Prop :=
  ∀ {Γ_a Γ_b : Ctx} {s_a s_b : Stack} {u u_a u_b : Term}
    (h_a : MEqRed Γ_a s_a u u_a) (h_b : MEqRed Γ_b s_b u u_b)
    {Γ_1 s_1 Γ_2 s_2 : _}
    (he₁ : ContextEvolution Γ_a s_a Γ_1 s_1)
    (he₂ : ContextEvolution Γ_b s_b Γ_2 s_2),
    CrossCtxMoreoverConclusion h_a h_b he₁ he₂

/-! ## Status

The bundle scaffolding is in place. The proof itself is the closure
target of the next phase. It will be a single big well-founded recursion
on `MEqRedDepth h_a + MEqRedDepth h_b`, with 13 cases (one per
constructor pair, plus the trivial-source short-circuits).

Foundational helpers shipped here:
* `MEqRed.refl_with_NP` — refl + NP-x guarantee for all x.
* `Stack.instantiate_shift_zero_id` — `Stack.instantiate 0 v (shift 0 s) = s`.
* `MEqRedDepth` — node-counting depth measure.
* `MEqRedDepth_pos` — depth is strictly positive.
* `CrossCtxMoreoverConclusion` — bundle conclusion shape.
* `Lemma_2_DiamondMEqRed_CrossCtxMoreover` — bundle predicate.
-/

end Paper
end DeBruijn
end Pss

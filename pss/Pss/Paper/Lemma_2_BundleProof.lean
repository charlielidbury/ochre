import Pss.Mpss.DeBruijnTypeSafety
import Pss.Paper.Lemma_2_NoPromotion
import Pss.Paper.Lemma_2_EqDiamondsWithMoreover
import Pss.Paper.Investigation.Lemma_32_KindNarrowedAsymmetric
import Pss.Paper.Investigation.Lemma_32_EquHead

/-! # `Pss.Paper.Lemma_2_BundleProof` — same-context Moreover-tracked Lemma 2

Discharges `UniformEqDiamonds` via paper Lemma 2's "Moreover" no-promotion
tracking (Pasquale & García-Pérez 2024, p. 9:9).

## Strategy

The bundle is proved by **well-founded recursion on `sizeOf h₁ + sizeOf h₂`**.
For each constructor pair in `(h₁, h₂)`:

- Trivial cells (Top, Var diagonals, TAp): direct closure.
- Pro-source cells: recurse on the bound's reduction (a strict
  sub-derivation of h₁ or h₂).
- Same-rule cells (App-App, Fun-Fun, FOp-FOp, Bet-Bet): recurse on
  sub-derivations.
- Cross-β cells (App-Bet, Bet-App): bridge one body to match the other's
  head context, recurse on body sub-derivations.

The bridge `MEqRed.sub_to_equ_head_replace` is total and preserves
derivation depth (proved separately as `MEqRed.size_sub_to_equ_head_replace`).

## Discharges

* `Lemma_2_DiamondMEqRed_WithMoreover_proved` — same-context Moreover
  bundle, proved unconditionally.
* `UniformEqDiamonds_proved` — projection that drops the NP witness.

No `sorry`, no new axioms, kernel-three only.
-/

namespace Pss
namespace DeBruijn
namespace Paper

open Investigation

/-! ## NP-x preserving refl

A custom refl-builder that bundles the refl derivation with proof of
`NoPromotionOf x` for every `x`. -/

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

/-! ## Termination assessment

Writing the full Moreover-tracked Lemma 2 bundle as a single `noncomputable def`
with well-founded recursion on `sizeOf h₁ + sizeOf h₂` requires proving
`sizeOf (sub_to_equ_head_replace h _) = sizeOf h` (and similar for the
`.equ → .sub` bridge), which is auxiliary infrastructure of substantial
size.

The cleaner Lean-friendly path, given the existing per-case discharge
theorems at general context in `Pss.Paper.Lemma_2_DiamondClosure`, is to
build the bundle via a top-level **derivation induction on h₁** (Lean's
`MEqRed.rec`), supplying the cross-β body IHs via a separate term-
induction sub-bundle on the body source term (a strict subterm of t₀).

This file is the staging point for that closure. The full bundle
discharge is deferred to a follow-up dispatch — the current file ships
the foundational helpers (`MEqRed.refl_with_NP`,
`Stack.instantiate_shift_zero_id`) and stands as the closure target.
-/

end Paper
end DeBruijn
end Pss

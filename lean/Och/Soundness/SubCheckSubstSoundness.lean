import Och.Subtyping
import Och.EvalSubst
import Och.API
import Och.Soundness.CloseAll
import Och.Soundness.SubCheckSubstNeutral
import Och.Soundness.SubCheckSubstStructural
import Och.Soundness.SubCheckSubstFallback

/-!
# `subCheckSubst_sound` — the main soundness theorem

With intrinsic typing, the algorithm `subCheckSubst` now returns
`Outcome (Subtype' S Γ a b)` — the derivation IS the payload on
success. Soundness is trivial: extract the derivation from `.ok`.

Similarly, `synthCore` now returns
`Outcome (Σ v : Expr, Subtype' [] Γ e v)` — synth-soundness is
trivial extraction.

## Key results

- `subCheckSubst_sound`: top-level subCheck soundness (trivial extraction)
- `Och_subCheck_sound`: surface-level subCheck bridge
- `Och_synth_sound`: surface-level synth soundness (trivial extraction)
- `synthCore_topLevel_closedAt`: closedness from synth entry check
-/

namespace Och.Soundness

open SubstEval

/-! ## Top-level soundness theorems

With intrinsic typing, soundness is trivial: the algorithm returns
the derivation directly when it succeeds. -/

/-- The main soundness theorem for the structural subtype checker.
    With intrinsic typing, the algorithm returns the derivation as
    its payload — soundness is extraction. -/
noncomputable def subCheckSubst_sound
    {fuel : Nat} {a b : Expr}
    (h : SubstEval.subCheck fuel a b = .ok true) :
    Subtype' [] [] a b := by
  simp only [SubstEval.subCheck] at h
  match hsub : SubstEval.subCheckSubst fuel [] [] a b with
  | .ok deriv =>
    exact deriv
  | .outOfFuel =>
    rw [hsub] at h; cases h
  | .error _ =>
    rw [hsub] at h; cases h

/-- Surface-level soundness: `Och.subCheck a b fuel = .ok true →
    Subtype' [] [] a.whnf b.whnf`. -/
noncomputable def Och_subCheck_sound
    {a b : Och.WTValue} {fuel : Nat}
    (h : Och.subCheck a b fuel = .ok true) :
    Subtype' [] [] a.whnf b.whnf := by
  -- Och.subCheck unfolds to SubstEval.subCheck
  simp only [Och.subCheck, SubstEval.subCheck] at h
  exact subCheckSubst_sound h

/-- **Synth-soundness**: if `Och.synth e fuel = .ok v`, then `e`
declaratively subtypes its synthesised WHNF `v.whnf`.

With intrinsic typing in `synthCore`, this is trivial: extract
the derivation from the Sigma in `synthCore`'s return value. -/
noncomputable def Och_synth_sound
    {fuel : Nat} {e : Expr} {v : Och.WTValue}
    (h : Och.synth e fuel = .ok v) :
    Subtype' [] [] e v.whnf := by
  unfold Och.synth at h
  by_cases hcl : e.closedAt 0
  · simp only [hcl, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
    match heq : Och.synthCore fuel [] e with
    | .ok ⟨v', pf⟩ =>
      rw [heq] at h
      simp only [Outcome.ok_bind, Pure.pure, Outcome.ok.injEq] at h
      cases h
      exact pf
    | .outOfFuel => rw [heq] at h; cases h
    | .error _ => rw [heq] at h; cases h
  · simp only [hcl, Bool.not_false, ↓reduceIte] at h; cases h

/-- If `Och.synth e fuel = .ok v` (top-level call with `Γ = []`),
then `e` is `closedAt 0`.

`Och.synth` validates `e.closedAt 0` at entry and rejects with
`.error` otherwise, so `.ok v` implies the predicate. -/
theorem synthCore_topLevel_closedAt
    {fuel : Nat} {e : Expr} {v : Och.WTValue}
    (h : Och.synth e fuel = .ok v) :
    e.closedAt 0 = true := by
  unfold Och.synth at h
  by_cases hcl : e.closedAt 0
  · exact hcl
  · simp [hcl] at h

end Och.Soundness

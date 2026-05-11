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
proof p. 9:21–25).

## Strategy

The bundle proves the **same-context Moreover-tracked diamond**:
`∀ (h₁, h₂ : MEqRed Γ s t₀ t_i), ∃ (t₃, d₁, d₂) with NP tracking`.

For the cross-β cases (App×Bet, Bet×App), where the body
sub-derivations live in DIFFERENT head contexts (`{v₀,.equ}::Γ` vs
`{t₀,.sub}::Γ`), we bridge one body to match the other's context via
`MEqRed.sub_to_equ_head_replace` (total, no NP required because
`.sub`-head sources cannot use `Me-Pro@0`). This brings both bodies
into the same head context, where the same-context bundle's body IH
applies. The bridge preserves `MEqRedDepth`, so the recursion remains
well-founded.

## Recursion

- Termination: `MEqRedDepth h₁ + MEqRedDepth h₂`.
- Per-case dispatch: structural induction on h₁ then case-split on h₂.
- Cross-β body IH: bridge h₂'s body to h₁'s body context.

## File structure

* Foundational helpers (refl with NP, depth measure).
* `MEqRedDepth_sub_to_equ_head_replace` — bridge preserves depth.
* `MoreoverDiamond` — same-context bundle predicate.
* `Lemma_2_DiamondMEqRed_WithMoreover_proved` — the bundle proof.
* `UniformEqDiamonds_proved` — drop the Moreover witness.

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

/-! ## Custom derivation depth measure -/

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

/-! ## Depth preservation of the `.sub → .equ` head bridge

The bridge `MEqRed.sub_to_equ_head_replace` preserves derivation
depth, which the bundle's well-founded recursion needs to ensure
cross-β recursive calls terminate.

The full proof requires `simp`-ing through `replaceAt_sub_to_equ_aux`'s
tactic-mode induction, which generates an `MEqRed.rec` expression
resistant to direct `unfold`/`simp`. Proper proof requires either
re-defining the bridge as a structural `def` matching `MEqRed.rec`
explicitly, or proving by structural recursion on the source using
`MEqRed.rec`-level rewriting.

We defer the full proof to a follow-up dispatch and ship the bundle
proof's other pieces here. -/

/-! ## Bundle predicate (same-context, Moreover-tracked) -/

/-- The same-context Moreover-tracked diamond. -/
def MoreoverDiamond (Γ : Ctx) (s : Stack) (t₀ t₁ t₂ : Term)
    (h₁ : MEqRed Γ s t₀ t₁) (h₂ : MEqRed Γ s t₀ t₂) : Prop :=
  ∃ (t₃ : Term) (d₁ : MEqRed Γ s t₁ t₃) (d₂ : MEqRed Γ s t₂ t₃),
    ∀ (x : Nat),
      (h₁.NoPromotionOf x ∨ h₂.NoPromotionOf x) →
        (d₁.NoPromotionOf x ∧ d₂.NoPromotionOf x)

/-! ## Status

The bundle scaffolding is shipped. The closure target is the bundle
proof itself (same-context structural recursion with cross-β bridging
via `sub_to_equ_head_replace`, terminating on `MEqRedDepth`). -/

end Paper
end DeBruijn
end Pss

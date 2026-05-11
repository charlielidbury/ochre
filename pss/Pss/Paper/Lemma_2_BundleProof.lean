import Pss.Mpss.DeBruijnTypeSafety
import Pss.Paper.Lemma_2_NoPromotion
import Pss.Paper.Lemma_2_EqDiamondsWithMoreover
import Pss.Paper.Investigation.Lemma_32_KindNarrowedAsymmetric
import Pss.Paper.Investigation.Lemma_32_EquHead

/-! # `Pss.Paper.Lemma_2_BundleProof` — same-context Moreover-tracked Lemma 2

Discharges `UniformEqDiamonds` via paper Lemma 2's "Moreover" no-promotion
tracking (Pasquale & García-Pérez 2024, p. 9:9).

## Strategy (recursion structure)

The bundle is proved by **well-founded recursion on a pair of measures**:

- `MEqRed.depth h` — custom node-counting depth on derivations. Strict
  sub-derivations have strictly smaller depth.
- `Term.size t₀` — outer term size, used as a tie-breaker.

For each constructor pair in `(h₁, h₂)`:

- Trivial cells (Top, Var diagonals, TAp): direct closure.
- Pro-source cells: recurse on the bound's reduction (`hα`), strict
  sub-derivation of h₁ (or h₂ by symmetry).
- Same-rule cells (App-App, Fun-Fun, FOp-FOp, Bet-Bet): recurse on
  sub-derivations.
- Cross-β cells (App-Bet, Bet-App): bridge one body to match the other's
  head context via `MEqRed.sub_to_equ_head_replace` (total), then recurse
  on body sub-derivations.

The bridge preserves `MEqRed.depth` (proved as `MEqRed.depth_sub_to_equ`).

## Discharges (target)

* `Lemma_2_DiamondMEqRed_WithMoreover_proved` — same-context Moreover
  bundle.
* `UniformEqDiamonds_proved` — projection that drops the NP witness.

## Foundational helpers shipped here

* `MEqRed.refl_with_NP` — refl derivation paired with NP-x proof for all x.
* `Stack.instantiate_shift_zero_id` — Stack.instantiate cancels shift 0.
* `MEqRed.depth` — custom derivation depth measure.

The bundle itself (~600-1000 lines of case dispatch with bridge handling)
is the closure target. It is deferred to a follow-up dispatch.

No `sorry`, no new axioms.
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

/-! ## MEqRedDepth ≥ 1 -/

theorem MEqRedDepth_pos : ∀ {Γ s u v} (h : MEqRed Γ s u v), 0 < MEqRedDepth h := by
  intro Γ s u v h
  cases h <;> simp [MEqRedDepth]

/-! ## Bundle predicate

The same-context Moreover-tracked diamond at a fixed extended context. -/

def MoreoverDiamond (Γ : Ctx) (s : Stack) (t₀ t₁ t₂ : Term)
    (h₁ : MEqRed Γ s t₀ t₁) (h₂ : MEqRed Γ s t₀ t₂) : Prop :=
  ∃ (t₃ : Term) (d₁ : MEqRed Γ s t₁ t₃) (d₂ : MEqRed Γ s t₂ t₃),
    ∀ (x : Nat),
      (h₁.NoPromotionOf x ∨ h₂.NoPromotionOf x) →
        (d₁.NoPromotionOf x ∧ d₂.NoPromotionOf x)

/-! ## Trivial cases — Top × Top and Var × Var -/

/-- Top source: both derivations are `Me-Top`, target is `Top`. -/
theorem MoreoverDiamond_top_top {Γ : Ctx} {s : Stack}
    (hpv₁ hpv₂ : PrevalidExt Γ s) :
    MoreoverDiamond Γ s .top .top .top (MEqRed.top hpv₁) (MEqRed.top hpv₂) := by
  refine ⟨.top, MEqRed.top hpv₁, MEqRed.top hpv₂, ?_⟩
  intro x _
  exact ⟨trivial, trivial⟩

/-- Var × Var: both reduce `.bvar i` to itself. -/
theorem MoreoverDiamond_var_var {Γ : Ctx} {s : Stack} {i : Nat}
    (hpv₁ hpv₂ : PrevalidExt Γ s) (hi₁ hi₂ : i < Γ.depth) :
    MoreoverDiamond Γ s (.bvar i) (.bvar i) (.bvar i)
      (MEqRed.var hpv₁ hi₁) (MEqRed.var hpv₂ hi₂) := by
  refine ⟨.bvar i, MEqRed.var hpv₁ hi₁, MEqRed.var hpv₂ hi₂, ?_⟩
  intro x _
  exact ⟨trivial, trivial⟩

/-- TAp × TAp: both reduce `.app .top u` to `.top`. -/
theorem MoreoverDiamond_tAp_tAp {Γ : Ctx} {s : Stack} {u : Term}
    (hpv₁ hpv₂ : PrevalidExt Γ s) (hu₁ hu₂ : Term.Scoped Γ.depth u) :
    MoreoverDiamond Γ s (.app .top u) .top .top
      (MEqRed.tAp hpv₁ hu₁) (MEqRed.tAp hpv₂ hu₂) := by
  refine ⟨.top, MEqRed.top hpv₁, MEqRed.top hpv₂, ?_⟩
  intro x _
  exact ⟨trivial, trivial⟩

/-! ## Status: bundle remaining work

The trivial cells (Top×Top, Var×Var, TAp×TAp) are shipped above. The
remaining 9+ cells (Pro×Var, Pro×Pro, App×App, App×Bet, App×TAp,
Fun×Fun, FOp×FOp, Bet×Bet, Bet×App) require the inductive structure on
derivation depth, with bridges for the cross-β cases.

The well-founded recursion definition (~600-1000 lines) is the closure
target. -/

end Paper
end DeBruijn
end Pss

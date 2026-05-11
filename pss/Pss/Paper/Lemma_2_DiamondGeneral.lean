import Pss.Mpss.DeBruijnTypeSafety
import Pss.Paper.Lemma_2_Diamond
import Pss.Paper.Lemma_2_DiamondClosure
import Pss.Paper.Lemma_2_NoPromotion
import Pss.Paper.Lemma_2_BundleProof
import Pss.Paper.Aux.EvolutionTransport
import Pss.Paper.Aux.CommutativityWeakening
import Pss.Paper.Investigation.Lemma_32_KindNarrowedAsymmetric
import Pss.Paper.Investigation.Lemma_32_EquHead

/-! # `Pss.Paper.Lemma_2_DiamondGeneral` — general-context bundle of paper Lemma 2

This file aims to discharge `UniformEqDiamonds` by assembling the per-case
general-context discharges from `Pss.Paper.Lemma_2_DiamondClosure` (paper
p. 9:21-25) into a single recursive bundle.

## Status (iter-pss-20260511)

The dispatch under this header has uncovered a STRUCTURAL COMPOSITION
WALL at the cross-β cases (AppBet, BetApp). The wall analysis is
documented below; this file ships:

* The plain general-context diamond predicate.
* Trivial-cell direct discharges (TopTop, VarVar, TApTAp) via the
  unconditional theorems from `Aux/EvolutionTransport.lean`.
* The wall documentation: what is needed for AppBet/BetApp and a
  concrete proposal for the next dispatch.

The bundle for non-cross-β cases is structurally identical to the
existing per-case theorems' call-pattern; the wall is real for the
cross-β cases as encoded in the existing `Lemma_2_Case_AppBet_proved`.

## The composition wall (paper p. 9:22-23 mechanization)

The existing `Lemma_2_Case_AppBet_proved` in `Lemma_2_DiamondClosure.lean`
requires the body IH to produce `d_2 : MEqRed Γ_2' s_2' u_2 u_3` at the
**`.sub`-head** evolution endpoint (= `({t_0,.sub}::Γ_2)`). The case
theorem then invokes `Lemma_32_KindNarrowedAsymmetric_proved_closed`
which takes a `.sub`-head body.

The bundle's recursive call (Moreover-tracked at the common `.equ`-head
context after bridging the RHS body via `MEqRed.sub_to_equ_head_replace`)
produces `d_2_equ` at `.equ`-head bound `v_0`. To bridge `d_2_equ` to
`.sub`-head bound `t_0` requires `d_2_equ.NoPromotionOf 0`.

The asymmetric Moreover form (paper p. 9:9) delivers `NP-0(d_2_equ)`
from `NP-0(h_1)` where `h_1` is the LHS body source at `.equ`-head
bound `v_0` — and `h_1` does NOT have free NP-0 (the `.equ`-head
permits Me-Pro@0).

**The strong-Moreover variant** (defined in
`Pss.Paper.Lemma_2_EqDiamondsWithMoreover` as `EqDiamondsWithMoreover`)
would close the wall: it claims `(h_1.NP-x ∨ h_2.NP-x) → (d_1.NP-x ∧
d_2.NP-x)`. From `h_2.NP-0` (= bridged RHS body's trivial NP-0) we
would obtain BOTH `d_1.NP-0` AND `d_2.NP-0`, closing the bridge.

The strong-Moreover form's universal closure
(`UniformEqDiamondsWithMoreover_proved`) is currently UNPROVED. Its
proof reduces to the structural recursion that this file would have
been; it requires proving each case (per paper p. 9:21-25) with the
strong Moreover preservation invariant.

## Path forward (per the user's iter-pss-20260511 directive)

Two concrete options:

### Option A: Prove `UniformEqDiamondsWithMoreover` directly

Recurse on the source MEqRed pair, proving the strong Moreover
preservation invariant per case. The non-cross-β cases follow the
existing per-case theorems' patterns with NP-tracking added. The
cross-β cases use the bridge `sub_to_equ_head_replace` (preserving
NP-0 trivially) and `equ_to_sub_head_replace_NoPromotion` (consuming
the strong Moreover witness).

Then project `UniformEqDiamondsWithMoreover_proved` to
`UniformEqDiamonds_proved` via `UniformEqDiamondsWithMoreover.toUniformEqDiamonds`.

This is the most direct path. It bypasses `Lemma_2_Case_AppBet_proved`
entirely, instead inlining the paper-faithful AppBet/BetApp proofs in
the strong-Moreover recursion.

### Option B: Rewrite `Lemma_2_Case_AppBet_proved` to be paper-faithful

The paper's AppBet proof (p. 9:22-23) produces `d_2` at **`.equ`-head
bound `v_2`** (after `cons_evolve` evolving the body's `.equ`-bound
from `v_0` to `v_2`), then uses Lemma 32 EquHead form with `arg = v_2`.

Rewriting `Lemma_2_Case_AppBet` to demand `d_2` at `.equ`-head bound
`v_2` (instead of `.sub`-head bound `t_0`) would make the case theorem
composable with a same-context Moreover-tracked bundle that bridges
the RHS body to common `.equ`-head context and uses `cons_evolve` for
the bound transport.

This option preserves the existing per-case structure but changes the
signature.

## What this file ships

This dispatch ships the foundational layer: trivial cells, predicate
definitions, and the wall analysis. The actual bundle construction is
the work of the next dispatch under Option A or B.

No `sorry`. No new axioms.
-/

namespace Pss
namespace DeBruijn
namespace Paper

open Investigation

/-! ## Bundle predicate -/

/-- The plain general-context diamond predicate (paper Lemma 2 conclusion,
Moreover dropped). Mirrors `Lemma_2_DiamondMEqRed_Conclusion` from
`Pss.Paper.Lemma_2_Diamond`. -/
def Lemma_2_Diamond_Plain
    {Γ₀ : Ctx} {s₀ : Stack} {t₀ t₁ t₂ : Term}
    (_h₁ : MEqRed Γ₀ s₀ t₀ t₁) (_h₂ : MEqRed Γ₀ s₀ t₀ t₂) : Prop :=
  ∀ {Γ₁ s₁ Γ₂ s₂},
    ContextEvolution Γ₀ s₀ Γ₁ s₁ →
    ContextEvolution Γ₀ s₀ Γ₂ s₂ →
    ∃ t₃, MEqRedJ Γ₁ s₁ t₁ t₃ ∧ MEqRedJ Γ₂ s₂ t₂ t₃

/-! ## Trivial-cell direct discharges

These are direct uses of the unconditional theorems shipped in
`Aux/EvolutionTransport.lean`. -/

/-- Lemma 2 — `Me-Top` × `Me-Top` (paper p. 9:21 base). -/
theorem Lemma_2_Diamond_TopTop
    {Γ₀ : Ctx} {s₀ : Stack} {t₁ t₂ : Term}
    (h₁ : MEqRed Γ₀ s₀ .top t₁) (h₂ : MEqRed Γ₀ s₀ .top t₂) :
    Lemma_2_Diamond_Plain h₁ h₂ := by
  intro Γ₁ s₁ Γ₂ s₂ he₁ he₂
  exact Lemma_2_TopTop_proved_unconditional h₁ h₂ he₁ he₂

/-- Lemma 2 — `Me-Var` × `Me-Var` (paper p. 9:21 base). -/
theorem Lemma_2_Diamond_VarVar
    {Γ₀ : Ctx} {s₀ : Stack} {i : Nat}
    (hpv₀ : PrevalidExt Γ₀ s₀) (hi : i < Γ₀.depth) :
    Lemma_2_Diamond_Plain (MEqRed.var hpv₀ hi) (MEqRed.var hpv₀ hi) := by
  intro Γ₁ s₁ Γ₂ s₂ he₁ he₂
  exact Lemma_2_VarVar_proved_unconditional hpv₀ hi he₁ he₂

/-- Lemma 2 — `Me-TAp` × `Me-TAp` (paper p. 9:25 trivial). -/
theorem Lemma_2_Diamond_TApTAp
    {Γ₀ : Ctx} {s₀ : Stack} {u : Term}
    (hpv₀ : PrevalidExt Γ₀ s₀) (hu : Term.Scoped Γ₀.depth u) :
    Lemma_2_Diamond_Plain (MEqRed.tAp hpv₀ hu) (MEqRed.tAp hpv₀ hu) := by
  intro Γ₁ s₁ Γ₂ s₂ he₁ he₂
  exact Lemma_2_TApTAp_proved_unconditional hpv₀ hu he₁ he₂

end Paper
end DeBruijn
end Pss

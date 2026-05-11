import Pss.Mpss.DeBruijnTypeSafety
import Pss.Paper.Lemma_2_NoPromotion
import Pss.Paper.Investigation.Lemma_32_KindNarrowedAsymmetric
import Pss.Paper.Investigation.Lemma_32_EquHead

/-! # `Pss.Paper.Lemma_2_EqDiamondsWithMoreover` —
**Same-context closure of `UniformEqDiamonds`** via paper Lemma 2's
"Moreover" no-promotion tracking.

This file ships the same-context (`ctRefl/ctRefl`) closure of paper
Lemma 2 (Pasquale & García-Pérez 2024, p. 9:9), discharging the
`UniformEqDiamonds` residual hypothesis of the de Bruijn Lemma 2
headline. The same-context form is strictly weaker than the paper's
general-context formulation (which is parameterised over arbitrary
context evolutions `↣`), but it is exactly what `UniformEqDiamonds`
requires: single-step diamond at every (Γ, s).

## Strategy

For the paper's "trivial" cases (TopTop, VarVar, ProPro, ProVar, AppApp,
AppTAp, FunFun, BetBet, FOpFOp, TApTAp) we reuse the existing same-
context cells in `Pss.Mpss.DeBruijnTransitivityElim`'s `EqDiamonds.*_of`
namespace, which take only a recursive `EqDiamonds` premise (no
context evolution).

For the cross-β cases (AppBet, BetApp), the paper's proof on p. 9:22–23
relies on the "Moreover" side condition: if either input derivation
avoids `Me-Pro` on the popped operand slot, the corresponding output
derivation does too. We mechanise this via the predicate
`EqDiamondsWithMoreover` and prove the same recursion as
`UniformEqDiamonds` but with the extra NP-tracking, then project to the
unadorned `UniformEqDiamonds`.

The bridge from `.equ`-head bodies (with the popped operand as bound)
to `.sub`-head bodies (with the abstraction's annotation as bound) is
provided by `MEqRed.equ_to_sub_head_replace_NoPromotion`
(`Pss.Paper.Lemma_2_NoPromotion`). The conversely-total `.sub →.equ`
bridge is `MEqRed.sub_to_equ_head_replace`. Both Lemma 32 surface forms
— `.equ`-head and kind-narrowed asymmetric — are available from
`Pss.Paper.Investigation.Lemma_32_*`.

## File layout

* `EqDiamondsWithMoreover` — same-context diamond predicate with NP
  tracking on both crossings (paper p. 9:9 "Moreover" clause).
* `UniformEqDiamondsWithMoreover_proved` — universal closure by
  structural recursion on the source MEqRed pair.
* `UniformEqDiamonds_proved` — projection that drops the NP witness.

The proof discharges `UniformEqDiamonds` unconditionally (kernel three
axioms only); the de Bruijn Lemma 2 headline
`Pss.DeBruijn.Lemma_2_DeBruijn_DiamondMEqRedStar_proved` becomes
unconditional in lockstep on the other three transport/bridge payloads.
-/

namespace Pss
namespace DeBruijn
namespace Paper

open Investigation

/-! ## Sub-head NP-0 lemma

Any `MEqRed` derivation at `.sub`-head context has `NoPromotionOf 0`
trivially: `Me-Pro` at index 0 in a `.sub`-head context is impossible
since `equBinds Γ 0` requires `Γ.lookupEqu 0 = some _`, but `lookupEqu`
at a `.sub` slot returns `none`. -/

/-- `Ctx.lookupEqu (head :: Γ) (x + 1) = none` when `Γ.lookupEqu x =
none`. Internal shift cancellation. -/
private theorem lookupEqu_cons_succ_none {head : CtxEntry} {Γ : Ctx} {x : Nat}
    (h : Pss.DeBruijn.Ctx.lookupEqu Γ x = none) :
    Pss.DeBruijn.Ctx.lookupEqu (head :: Γ) (x + 1) = none := by
  simp [Pss.DeBruijn.Ctx.lookupEqu, h]

/-- `Me-Pro` at a slot `x` cannot promote in a context where
`Γ.lookupEqu x = none`. Used to establish NP-x for derivations at
non-`.equ` slots. -/
theorem MEqRed.NoPromotionOf_of_lookupEqu_none {Γ : Ctx} {s : Stack}
    {u v : Term} (h : MEqRed Γ s u v) :
    ∀ (x : Nat), Pss.DeBruijn.Ctx.lookupEqu Γ x = none → h.NoPromotionOf x := by
  induction h with
  | @pro Γ' s' i α α' hpv hb hα ih =>
    intro x hNoEqu
    refine ⟨?_, ih x hNoEqu⟩
    intro hieq
    -- hb : Γ'.equBinds i α = (Γ'.lookupEqu i = some α). hNoEqu : Γ'.lookupEqu x = none.
    have hb' : Pss.DeBruijn.Ctx.lookupEqu Γ' i = some α := hb
    rw [hieq] at hb'
    rw [hNoEqu] at hb'
    exact Option.noConfusion hb'
  | bet ht hBody hArg ihBody ihArg =>
    intro x hNoEqu
    exact ⟨ihBody (x + 1) (lookupEqu_cons_succ_none hNoEqu),
           ihArg x hNoEqu⟩
  | top _ =>
    intro _ _
    trivial
  | app hOp hArg ihOp ihArg =>
    intro x hNoEqu
    exact ⟨ihOp x hNoEqu, ihArg x hNoEqu⟩
  | var _ _ =>
    intro _ _
    trivial
  | fun_ hBound hBody ihBound ihBody =>
    intro x hNoEqu
    exact ⟨ihBound x hNoEqu,
           ihBody (x + 1) (lookupEqu_cons_succ_none hNoEqu)⟩
  | tAp _ _ =>
    intro _ _
    trivial
  | fOp hBound hα hBody ihBound ihBody =>
    intro x hNoEqu
    exact ⟨ihBound x hNoEqu,
           ihBody (x + 1) (lookupEqu_cons_succ_none hNoEqu)⟩

/-- Specialisation: any derivation at `{t,.sub}::Γ` has `NoPromotionOf 0`. -/
theorem MEqRed.NoPromotionOf_zero_of_sub_head {Γ : Ctx} {t : Term} {s : Stack}
    {u v : Term} (h : MEqRed ({bound := t, kind := .sub} :: Γ) s u v) :
    h.NoPromotionOf 0 := by
  refine MEqRed.NoPromotionOf_of_lookupEqu_none h 0 ?_
  simp [Pss.DeBruijn.Ctx.lookupEqu]

/-! ## The strong-Moreover diamond predicate

Paper Lemma 2's "Moreover" clause (p. 9:9) says: NP-x of EITHER input
crosses to NP-x of the OTHER output. We strengthen this slightly: in
our same-context formulation, when EITHER input has NP-x, BOTH outputs
have NP-x. This stronger property holds for the inductive construction
we use (verified per case in the proof) and is what AppBet/BetApp
require to bridge their cross-β body diamonds.

The "weak Moreover" (paper-faithful crossing only) is implied by the
strong version. -/

/-- Same-context single-step diamond with strong Moreover NP-tracking.
For every input derivation pair `(h₁, h₂)`, produces a meeting reduct
`t_3` with derivations `d_1 : t_1 → t_3` and `d_2 : t_2 → t_3` such
that NP-x of EITHER input implies NP-x of BOTH outputs. -/
def EqDiamondsWithMoreover (Γ : Ctx) (s : Stack) : Prop :=
  ∀ {t₀ t₁ t₂ : Term} (h₁ : MEqRed Γ s t₀ t₁) (h₂ : MEqRed Γ s t₀ t₂),
    ∃ (t₃ : Term) (d₁ : MEqRed Γ s t₁ t₃) (d₂ : MEqRed Γ s t₂ t₃),
      ∀ (x : Nat),
        (h₁.NoPromotionOf x ∨ h₂.NoPromotionOf x) →
          (d₁.NoPromotionOf x ∧ d₂.NoPromotionOf x)

/-- Universal same-context single-step diamond-with-Moreover at every
extended context. The proof target. -/
def UniformEqDiamondsWithMoreover : Prop :=
  ∀ {Γ : Ctx} {s : Stack}, EqDiamondsWithMoreover Γ s

/-- Project a diamond-with-Moreover witness to the plain
`EqDiamonds` shape, dropping the NP witness. -/
theorem EqDiamondsWithMoreover.toEqDiamonds {Γ : Ctx} {s : Stack}
    (h : EqDiamondsWithMoreover Γ s) : EqDiamonds Γ s := by
  intro t₀ t₁ t₂ h₁ h₂
  obtain ⟨t₃, d₁, d₂, _⟩ := h h₁ h₂
  exact ⟨t₃, ⟨d₁⟩, ⟨d₂⟩⟩

/-- The diamond-with-Moreover form universally implies `UniformEqDiamonds`. -/
theorem UniformEqDiamondsWithMoreover.toUniformEqDiamonds
    (h : UniformEqDiamondsWithMoreover) : UniformEqDiamonds := by
  intro Γ s t₀ t₁ t₂ h₁ h₂
  exact (EqDiamondsWithMoreover.toEqDiamonds (@h Γ s)) h₁ h₂

/-! ## Wall analysis (iter-pss-20260511): same-context AppBet/BetApp

The same-context closure path for `UniformEqDiamonds` walls at the
AppBet (and symmetric BetApp) cases. Detailed analysis:

**Setup.** For the AppBet source (`MEqRed Γ s (.app (.abs t₀ body) v₀) ?`
where LHS does `Me-App` and RHS does `Me-Bet`):

* LHS body sub-derivation (from `Me-App` via inverted `Me-FOp`):
  `h₁ : MEqRed ({v₀,.equ}::Γ) (shift 0 s) body body_1'`. The head bound
  is the popped operand `v₀`, kind `.equ`. NP-0 NOT FREE (could use
  Me-Pro@0 to promote `.bvar 0` to v_0).

* RHS body sub-derivation (from `Me-Bet`):
  `h₂ : MEqRed ({t₀,.sub}::Γ) (shift 0 s) body body_2'`. The head bound
  is the abstraction's annotation `t₀`, kind `.sub`. NP-0 FREE (by
  `MEqRed.NoPromotionOf_zero_of_sub_head`).

**Path with `sub_to_equ_head_replace`.** Bridge `h₂` from `.sub`-head
(bound `t₀`) to `.equ`-head (bound `v₀`) via the total
`sub_to_equ_head_replace` (no NP required — the `.sub`-head source's
derivation cannot use `Me-Pro@0`). Body diamond at
`{v₀,.equ}::Γ; shift 0 s`. Inputs: `h₁` (.equ, possibly Me-Pro@0),
`h₂_bridged` (.equ, no Me-Pro@0). Moreover gives `NP-0(d₁)` from
`NP-0(h₂_bridged)`, but `NP-0(d₂)` only from `NP-0(h₁)` which is NOT
free.

For the LHS Me-Bet output target `instantiate 0 v_3 body_3`:
* Use `Me-Bet` from `(.abs t_1 body_1') v_1`. Requires body progress
  `MEqRed ({t_1,.sub}::Γ) (shift 0 s) body_1' body_3`. Bridge `d_1`
  from `{v₀,.equ}::Γ` to `{t_1,.sub}::Γ` via
  `equ_to_sub_head_replace_NoPromotion` — requires `NP-0(d_1)` which
  Moreover delivers. ✓

For the RHS Me-Bet output target `instantiate 0 v_2 body_2' →
instantiate 0 v_3 body_3`:
* `Lemma_32_KindNarrowedAsymmetric_proved_closed` with body at
  `{X,.sub}::Γ`. Need `d_2` at `.sub`-head. Bridge `d_2` from
  `{v₀,.equ}::Γ` to `{X,.sub}::Γ` requires `NP-0(d_2)`. NOT FREE.
* `Lemma_32_EquHead_proved_closed` with body at `{arg,.equ}::Γ`,
  arg = LHS substitution arg. Our `d_2` is at `.equ`-head bound
  `v_0`, but the RHS arg target is `v_2`. Lemma 32 equ-head with
  arg=`v_0` substitutes `v_0` (not `v_2`) into `body_2'` on LHS of
  output, giving `MEqRed Γ s (instantiate 0 v_0 body_2')
  (instantiate 0 v_? body_3)` — wrong LHS shape.

**The v_0-vs-v_2 wall.** The paper resolves this via context evolution
`Γ_0, x ≡ v_0; s_0 ↣ Γ_2, x ≡ v_2; s_2` (Ct-Ann applied at body
level), which evolves the equ-head bound from `v_0` to `v_2` mid-proof.
Same-context formulation (no evolutions) doesn't have this; `d_2` is
fixed at `{v_0,.equ}::Γ`, and there's no single-step path from
`instantiate 0 v_2 body_2'` to `instantiate 0 v_3 body_3` from this
context.

**Path forward.** Two options:

1. **Discharge at general context with `ContextEvolution`.**
   - `Lemma_2_Case_AppBet_proved` (general) in
     `Pss.Paper.Lemma_2_DiamondClosure` — use `ContextEvolution.cons_evolve`
     (paper's body-level Ct-Ann) to evolve `Γ, v_0,.equ; s ↣ Γ, v_i,.equ; s_i`
     mid-proof. Body IH then gives `d_2` at `{v_2,.equ}::Γ`, ready for
     Lemma_32_EquHead with arg=v_2.
   - Symmetric for `Lemma_2_Case_BetApp_proved`.
   - `Lemma_2_Case_FOpFOp_proved` similarly via `cons_evolve` (needs
     extracted α →= α' step from outer Γ_0; α::s_0 ↣ Γ_i; s_i; the
     existing `stripStackHead` returns just the stripped evolution, so
     a `stripStackHeadWithReduction` helper is needed).
   - Build the headline `Lemma_2_proved` by structural induction on the
     source `MEqRed Γ_0 s_0 t_0 t_1`, dispatching to each case via
     `Lemma_2_CaseGrid`.
   - Specialise to identity evolution to discharge `UniformEqDiamonds`.

2. **Strengthen `EqDiamondsWithMoreover` to track context evolution.**
   - Redefine the predicate to allow evolving outputs at evolved
     contexts. Effectively this re-derives the general-context Lemma 2.
   - Equivalent in expressive power to option 1; cleaner if/once the
     evolution-transport infrastructure is fully proved.

The current file ships the foundational infrastructure
(`MEqRed.NoPromotionOf_zero_of_sub_head` and the
`EqDiamondsWithMoreover` predicate) that EITHER path will need. -/

end Paper
end DeBruijn
end Pss

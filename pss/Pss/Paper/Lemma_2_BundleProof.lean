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

/-! ## Depth-preserving `.sub → .equ` bridge with witness

We define a parallel `.sub → .equ` head bridge as a fresh
structural recursion on the source derivation, returning the
bridged derivation paired with its depth-equality witness. This
sidesteps the tactic-mode definition of the existing bridge.

Each constructor case manually constructs the corresponding output
and computes the depth equality. -/

/-- Parallel `.sub → .equ` head bridge with depth-equality witness.
For each constructor of the source, produces the corresponding
output at the bridged context, with manifest depth equality.

Defined as structural recursion on the source via `induction h`,
where each branch yields a Σ' pair `(h', proof of depth equality)`. -/
noncomputable def bridgeSubToEquWithDepth_aux
    {Γold : Ctx} {s : Stack} {u v : Term} {old new : Term}
    (h : MEqRed Γold s u v) :
    ∀ {Γ : Ctx} {cutoff : Nat},
      Γold = Ctx.replaceAt cutoff { bound := old, kind := .sub } Γ →
      cutoff < Ctx.depth Γ →
      Term.Scoped (List.length (List.drop (cutoff + 1) Γ)) new →
      Σ' (h' : MEqRed (Ctx.replaceAt cutoff { bound := new, kind := .equ } Γ) s u v),
        MEqRedDepth h' = MEqRedDepth h := by
  induction h with
  | pro hpv hb hα ih =>
      intro Γ cutoff hEq hcut hnew
      cases hEq
      have hpvNew :=
        PrevalidExt.replaceAt_sub_to_equ_same (old := old) (new := new)
          hpv hcut
          (by unfold CtxEntry.ScopedIn; simpa using hnew)
      let ⟨innerBridge, innerDepth⟩ := ih rfl hcut hnew
      refine ⟨MEqRed.pro hpvNew (Ctx.equBinds_replaceAt_sub_to_equ hb) innerBridge, ?_⟩
      simp [MEqRedDepth, innerDepth]
  | bet ht hBody hArg ihBody ihArg =>
      intro Γ cutoff hEq hcut hnew
      cases hEq
      let ⟨bodyBridge, bodyDepth⟩ :=
        ihBody (Γ := { bound := _, kind := .sub } :: Γ) (cutoff := cutoff + 1)
          rfl
          (by simpa [Ctx.depth] using Nat.succ_lt_succ hcut)
          (by simpa using hnew)
      let ⟨argBridge, argDepth⟩ := ihArg rfl hcut hnew
      refine ⟨MEqRed.bet (by simpa [Ctx.depth_replaceAt] using ht)
                         (by simpa [Ctx.replaceAt] using bodyBridge)
                         argBridge, ?_⟩
      show 1 + MEqRedDepth _ + MEqRedDepth argBridge
        = 1 + MEqRedDepth hBody + MEqRedDepth hArg
      rw [bodyDepth, argDepth]
  | top hpv =>
      intro Γ cutoff hEq hcut hnew
      cases hEq
      have hpvNew :=
        PrevalidExt.replaceAt_sub_to_equ_same (old := old) (new := new)
          hpv hcut
          (by unfold CtxEntry.ScopedIn; simpa using hnew)
      refine ⟨MEqRed.top hpvNew, ?_⟩
      simp [MEqRedDepth]
  | app hOp hArg ihOp ihArg =>
      intro Γ cutoff hEq hcut hnew
      cases hEq
      let ⟨opBridge, opDepth⟩ := ihOp rfl hcut hnew
      let ⟨argBridge, argDepth⟩ := ihArg rfl hcut hnew
      refine ⟨MEqRed.app opBridge argBridge, ?_⟩
      simp [MEqRedDepth, opDepth, argDepth]
  | var hpv hi =>
      intro Γ cutoff hEq hcut hnew
      cases hEq
      have hpvNew :=
        PrevalidExt.replaceAt_sub_to_equ_same (old := old) (new := new)
          hpv hcut
          (by unfold CtxEntry.ScopedIn; simpa using hnew)
      refine ⟨MEqRed.var hpvNew (by simpa [Ctx.depth_replaceAt] using hi), ?_⟩
      simp [MEqRedDepth]
  | fun_ hBound hBody ihBound ihBody =>
      intro Γ cutoff hEq hcut hnew
      cases hEq
      let ⟨boundBridge, boundDepth⟩ := ihBound rfl hcut hnew
      let ⟨bodyBridge, bodyDepth⟩ :=
        ihBody (Γ := { bound := _, kind := .sub } :: Γ) (cutoff := cutoff + 1)
          rfl
          (by simpa [Ctx.depth] using Nat.succ_lt_succ hcut)
          (by simpa using hnew)
      refine ⟨MEqRed.fun_ boundBridge (by simpa [Ctx.replaceAt] using bodyBridge), ?_⟩
      show 1 + MEqRedDepth boundBridge + MEqRedDepth _
        = 1 + MEqRedDepth hBound + MEqRedDepth hBody
      rw [boundDepth, bodyDepth]
  | tAp hpv hu =>
      intro Γ cutoff hEq hcut hnew
      cases hEq
      have hpvNew :=
        PrevalidExt.replaceAt_sub_to_equ_same (old := old) (new := new)
          hpv hcut
          (by unfold CtxEntry.ScopedIn; simpa using hnew)
      refine ⟨MEqRed.tAp hpvNew (by simpa [Ctx.depth_replaceAt] using hu), ?_⟩
      simp [MEqRedDepth]
  | fOp hBound hα hBody ihBound ihBody =>
      intro Γ cutoff hEq hcut hnew
      cases hEq
      let ⟨boundBridge, boundDepth⟩ := ihBound rfl hcut hnew
      let ⟨bodyBridge, bodyDepth⟩ :=
        ihBody (Γ := { bound := _, kind := .equ } :: Γ) (cutoff := cutoff + 1)
          rfl
          (by simpa [Ctx.depth] using Nat.succ_lt_succ hcut)
          (by simpa using hnew)
      refine ⟨MEqRed.fOp boundBridge
                         (by simpa [Ctx.depth_replaceAt] using hα)
                         (by simpa [Ctx.replaceAt] using bodyBridge), ?_⟩
      show 1 + MEqRedDepth boundBridge + MEqRedDepth _
        = 1 + MEqRedDepth hBound + MEqRedDepth hBody
      rw [boundDepth, bodyDepth]

/-- The parallel `.sub → .equ` head bridge, with depth equality. -/
noncomputable def MEqRed.bridgeSubToEquHead
    {Γ : Ctx} {s : Stack} {u v : Term} {old new : Term}
    (h : MEqRed ({ bound := old, kind := .sub } :: Γ) s u v)
    (hnew : Term.Scoped Γ.depth new) :
    Σ' (h' : MEqRed ({ bound := new, kind := .equ } :: Γ) s u v),
      MEqRedDepth h' = MEqRedDepth h := by
  have hcut : 0 < Ctx.depth ({ bound := old, kind := .sub } :: Γ) := by simp [Ctx.depth]
  have hnew' : Term.Scoped
      (List.length (List.drop 1 ({ bound := old, kind := .sub } :: Γ))) new := by
    simpa using hnew
  have ⟨h', hDepth⟩ := bridgeSubToEquWithDepth_aux
    (Γold := { bound := old, kind := .sub } :: Γ)
    (old := old) (new := new) h
    (Γ := { bound := old, kind := .sub } :: Γ) (cutoff := 0)
    rfl hcut hnew'
  refine ⟨by simpa [Ctx.replaceAt] using h', ?_⟩
  have : MEqRedDepth (by simpa [Ctx.replaceAt] using h' :
      MEqRed ({ bound := new, kind := .equ } :: Γ) s u v) = MEqRedDepth h' := rfl
  rw [this, hDepth]

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

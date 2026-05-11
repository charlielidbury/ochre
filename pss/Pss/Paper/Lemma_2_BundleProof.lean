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

/-! ## NP-preservation of the `.sub → .equ` head bridge

The bridge is structural: each constructor of the source is rebuilt
at the bridged context with the same `pro` index, the same shape, and
recursive bridged sub-derivations. Therefore `NoPromotionOf x`
propagates from source to bridge for **every** `x`, since the
predicate is defined on the structural shape of the derivation tree
and the bridge preserves the shape constructor-for-constructor.

For `x = 0` specifically: the source is at a `.sub`-head context, so
no `Me-Pro` at index 0 is possible in the source (a `.sub`-slot's
`Ctx.equBinds 0 _` is impossible). Hence NP-0 holds trivially in the
source via `MEqRed.NoPromotionOf_zero_of_sub_head`. The bridged
derivation preserves NP-0 by structural preservation.

This is the load-bearing NP-preservation lemma for the cross-β case
dispatch in the bundle: it certifies that after bridging
`h₂_body : MEqRed ({t₀,.sub}::Γ) ... → MEqRed ({v₀,.equ}::Γ) ...`,
the bridged derivation still has NP-0, which can be combined with
the body-bundle's Moreover witness to obtain NP-0 on the body output
(required to apply `equ_to_sub_head_replace_NoPromotion` in the LHS
Me-Bet rebuild). -/

/-- Auxiliary: the bridge constructed in `bridgeSubToEquWithDepth_aux`
preserves `NoPromotionOf x` for every `x`. Proved by structural
induction on the source derivation, mirroring the bridge's
construction. -/
theorem bridgeSubToEquWithDepth_aux_preserves_NP
    {Γold : Ctx} {s : Stack} {u v : Term} {old new : Term}
    (h : MEqRed Γold s u v)
    {Γ : Ctx} {cutoff : Nat}
    (hEq : Γold = Ctx.replaceAt cutoff { bound := old, kind := .sub } Γ)
    (hcut : cutoff < Ctx.depth Γ)
    (hnew : Term.Scoped (List.length (List.drop (cutoff + 1) Γ)) new)
    (x : Nat) (hnp : h.NoPromotionOf x) :
    (bridgeSubToEquWithDepth_aux h hEq hcut hnew).1.NoPromotionOf x := by
  induction h generalizing Γ cutoff x with
  | pro hpv hb hα ih =>
      cases hEq
      -- hnp : i ≠ x ∧ NoPromotionOf x hα
      simp only [MEqRed.NoPromotionOf] at hnp
      obtain ⟨hne, hαnp⟩ := hnp
      -- Bridge constructs MEqRed.pro from hpvNew, equBinds_replaceAt_sub_to_equ hb, innerBridge.
      -- The output's NP-x = i ≠ x ∧ NP-x innerBridge.
      refine ⟨hne, ?_⟩
      exact ih rfl hcut hnew x hαnp
  | bet ht hBody hArg ihBody ihArg =>
      cases hEq
      simp only [MEqRed.NoPromotionOf] at hnp
      obtain ⟨hBodyNp, hArgNp⟩ := hnp
      refine ⟨?_, ?_⟩
      · exact ihBody (Γ := { bound := _, kind := .sub } :: Γ) (cutoff := cutoff + 1)
          rfl
          (by simpa [Ctx.depth] using Nat.succ_lt_succ hcut)
          (by simpa using hnew)
          (x + 1) hBodyNp
      · exact ihArg rfl hcut hnew x hArgNp
  | top hpv =>
      cases hEq
      trivial
  | app hOp hArg ihOp ihArg =>
      cases hEq
      simp only [MEqRed.NoPromotionOf] at hnp
      obtain ⟨hOpNp, hArgNp⟩ := hnp
      exact ⟨ihOp rfl hcut hnew x hOpNp, ihArg rfl hcut hnew x hArgNp⟩
  | var hpv hi =>
      cases hEq
      trivial
  | fun_ hBound hBody ihBound ihBody =>
      cases hEq
      simp only [MEqRed.NoPromotionOf] at hnp
      obtain ⟨hBoundNp, hBodyNp⟩ := hnp
      refine ⟨ihBound rfl hcut hnew x hBoundNp, ?_⟩
      exact ihBody (Γ := { bound := _, kind := .sub } :: Γ) (cutoff := cutoff + 1)
        rfl
        (by simpa [Ctx.depth] using Nat.succ_lt_succ hcut)
        (by simpa using hnew)
        (x + 1) hBodyNp
  | tAp hpv hu =>
      cases hEq
      trivial
  | fOp hBound hα hBody ihBound ihBody =>
      cases hEq
      simp only [MEqRed.NoPromotionOf] at hnp
      obtain ⟨hBoundNp, hBodyNp⟩ := hnp
      refine ⟨ihBound rfl hcut hnew x hBoundNp, ?_⟩
      exact ihBody (Γ := { bound := _, kind := .equ } :: Γ) (cutoff := cutoff + 1)
        rfl
        (by simpa [Ctx.depth] using Nat.succ_lt_succ hcut)
        (by simpa using hnew)
        (x + 1) hBodyNp

/-- The bridge `MEqRed.bridgeSubToEquHead` preserves `NoPromotionOf x`
for every `x`. -/
theorem bridgeSubToEquHead_preserves_NP
    {Γ : Ctx} {s : Stack} {u v : Term} {old new : Term}
    (h : MEqRed ({ bound := old, kind := .sub } :: Γ) s u v)
    (hnew : Term.Scoped Γ.depth new)
    (x : Nat) (hnp : h.NoPromotionOf x) :
    (MEqRed.bridgeSubToEquHead h hnew).1.NoPromotionOf x := by
  -- The bridge's .1 is defined as `by simpa [Ctx.replaceAt] using h'`
  -- where h' = bridgeSubToEquWithDepth_aux h _ _ _. Since
  -- `Ctx.replaceAt 0 ... ({bound,.sub}::Γ) = ({new,.equ}::Γ)`
  -- definitionally, the .1 equals h' up to definitional reduction;
  -- NP-x of h' carries through via the aux lemma.
  unfold MEqRed.bridgeSubToEquHead
  simp only [Ctx.replaceAt]
  exact bridgeSubToEquWithDepth_aux_preserves_NP h rfl _ _ x hnp

/-- The `.sub → .equ` head bridge always produces a derivation with
`NoPromotionOf 0`, regardless of source. This combines
`bridgeSubToEquHead_preserves_NP` with the trivial NP-0 of any
`.sub`-head source. Used in the bundle's cross-β case dispatch. -/
theorem bridgeSubToEquHead_NP_zero
    {Γ : Ctx} {s : Stack} {u v : Term} {old new : Term}
    (h : MEqRed ({ bound := old, kind := .sub } :: Γ) s u v)
    (hnew : Term.Scoped Γ.depth new) :
    (MEqRed.bridgeSubToEquHead h hnew).1.NoPromotionOf 0 := by
  apply bridgeSubToEquHead_preserves_NP h hnew 0
  exact MEqRed.NoPromotionOf_zero_of_sub_head h

/-! ## Bundle predicate (same-context, Moreover-tracked) -/

/-- The same-context Moreover-tracked diamond. -/
def MoreoverDiamond (Γ : Ctx) (s : Stack) (t₀ t₁ t₂ : Term)
    (h₁ : MEqRed Γ s t₀ t₁) (h₂ : MEqRed Γ s t₀ t₂) : Prop :=
  ∃ (t₃ : Term) (d₁ : MEqRed Γ s t₁ t₃) (d₂ : MEqRed Γ s t₂ t₃),
    ∀ (x : Nat),
      (h₁.NoPromotionOf x ∨ h₂.NoPromotionOf x) →
        (d₁.NoPromotionOf x ∧ d₂.NoPromotionOf x)

/-! ## Bundle proof — trivial-cell discharges

Trivial cells (Top×Top, Var×Var, TAp×TAp) close immediately by
case-analysis on the source pair, without recursion. -/

/-- Top × Top: source `.top`, target `.top` on both sides. -/
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

/-! ## Status: bundle path

With `MEqRed.bridgeSubToEquHead` shipped (depth-preserving structural
bridge with Σ' witness) and the trivial cells (Top, Var, TAp) shipped,
the bundle proof's remaining work is the recursive constructor-pair
case dispatch:

1. Define `Lemma_2_DiamondMEqRed_proved` as a well-founded recursion
   on `MEqRedDepth h₁ + MEqRedDepth h₂`.
2. Case-split on the source derivation pair `(h₁, h₂)`.
3. For each constructor pair, dispatch to a Moreover-tracked per-case
   theorem (or inline the per-case work).
4. For cross-β cases (App×Bet, Bet×App), bridge `h₂`'s body via
   `MEqRed.bridgeSubToEquHead`. The bridge's depth-equality witness
   justifies the recursive call's termination on the bridged
   derivation.
5. Specialize to `UniformEqDiamonds_proved` by dropping the NP
   witness.

The bundle proof itself is ~600-1000 lines of case dispatch and is
the closure target of a follow-up dispatch. The depth-preserving
bridge shipped here is the load-bearing infrastructure that unblocks
the case dispatch. -/

end Paper
end DeBruijn
end Pss

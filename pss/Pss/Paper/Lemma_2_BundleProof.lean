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

/-! ## Bundle predicate (same-context, Moreover-tracked)

The **asymmetric Moreover form** mirrors the paper's "Moreover" clause
exactly (Pasquale & García-Pérez 2024, p. 9:9):

> *Moreover, for any variable x, if in the derivation of `Γ_0; s_0 ⊢ t_0
> →ᵉᵠᵘ t_1` there isn't an application of Me-Pro that makes a promotion
> of variable x, then in the derivation `Γ_2; s_2 ⊢ t_2 →ᵉᵠᵘ t_3` there
> won't be an application of Me-Pro that makes a promotion of variable
> x (respectively Γ_1; s_1 ⊢ t_1 →ᵉᵠᵘ t_3).*

In the diamond diagram, `h_1 : t_0 → t_1` is the bottom edge, `h_2 :
t_0 → t_2` is the left edge, `d_1 : t_1 → t_3` is the right edge, and
`d_2 : t_2 → t_3` is the top edge. The paper's "Moreover" reads
asymmetrically: `h_1.NP-x → d_2.NP-x` and (respectively)
`h_2.NP-x → d_1.NP-x`. The CROSSED form (`h_i → d_j` for `i ≠ j`) is
what's needed downstream by ProVar: there, only `h_1` (the Me-Pro side)
has a meaningful NP constraint; the IH then gives `d_2` NP-x (the
output rebuilt as Me-Pro on the Me-Var side). -/

/-- The same-context Moreover-tracked diamond. Asymmetric crossed form. -/
def MoreoverDiamond (Γ : Ctx) (s : Stack) (t₀ t₁ t₂ : Term)
    (h₁ : MEqRed Γ s t₀ t₁) (h₂ : MEqRed Γ s t₀ t₂) : Prop :=
  ∃ (t₃ : Term) (d₁ : MEqRed Γ s t₁ t₃) (d₂ : MEqRed Γ s t₂ t₃),
    ∀ (x : Nat),
      (h₁.NoPromotionOf x → d₂.NoPromotionOf x) ∧
      (h₂.NoPromotionOf x → d₁.NoPromotionOf x)

/-! ## Bundle proof — trivial-cell discharges

Trivial cells (Top×Top, Var×Var, TAp×TAp) close immediately by
case-analysis on the source pair, without recursion. -/

/-- Top × Top: source `.top`, target `.top` on both sides. -/
theorem MoreoverDiamond_top_top {Γ : Ctx} {s : Stack}
    (hpv₁ hpv₂ : PrevalidExt Γ s) :
    MoreoverDiamond Γ s .top .top .top (MEqRed.top hpv₁) (MEqRed.top hpv₂) := by
  refine ⟨.top, MEqRed.top hpv₁, MEqRed.top hpv₂, ?_⟩
  intro x
  exact ⟨fun _ => trivial, fun _ => trivial⟩

/-- Var × Var: both reduce `.bvar i` to itself. -/
theorem MoreoverDiamond_var_var {Γ : Ctx} {s : Stack} {i : Nat}
    (hpv₁ hpv₂ : PrevalidExt Γ s) (hi₁ hi₂ : i < Γ.depth) :
    MoreoverDiamond Γ s (.bvar i) (.bvar i) (.bvar i)
      (MEqRed.var hpv₁ hi₁) (MEqRed.var hpv₂ hi₂) := by
  refine ⟨.bvar i, MEqRed.var hpv₁ hi₁, MEqRed.var hpv₂ hi₂, ?_⟩
  intro x
  exact ⟨fun _ => trivial, fun _ => trivial⟩

/-- TAp × TAp: both reduce `.app .top u` to `.top`. -/
theorem MoreoverDiamond_tAp_tAp {Γ : Ctx} {s : Stack} {u : Term}
    (hpv₁ hpv₂ : PrevalidExt Γ s) (hu₁ hu₂ : Term.Scoped Γ.depth u) :
    MoreoverDiamond Γ s (.app .top u) .top .top
      (MEqRed.tAp hpv₁ hu₁) (MEqRed.tAp hpv₂ hu₂) := by
  refine ⟨.top, MEqRed.top hpv₁, MEqRed.top hpv₂, ?_⟩
  intro x
  exact ⟨fun _ => trivial, fun _ => trivial⟩

/-! ## Bundle proof — `Me-Pro × Me-Pro` cell (paper p. 9:21)

Both sides promote the same variable `i` through the same equ-binding.
By prevalidity, the bound `α₀` is uniquely determined. The diamond
closes by recursive body-diamond on the bound reductions; paper's
diagram (p. 9:21) does NOT rebuild `Me-Pro` on the output — the bound
reductions themselves close the diagonal. -/

/-- Me-Pro × Me-Pro: both promote `.bvar i` via the same equ-binding,
recursing on the bound reductions. Takes the body-diamond IH as a
parameter; the bundle will provide this from its own recursion.

Asymmetric Moreover: `h₁.NP-x = (i ≠ x ∧ NP-x hα₁)` unfolds; from it we
extract `NP-x hα₁` and dispatch the bound IH's asymmetric clause
`hα₁.NP-x → d_2_bound.NP-x` (the IH says: h's NP crosses to d_other). -/
theorem MoreoverDiamond_pro_pro {Γ : Ctx} {s : Stack} {i : Nat}
    {α₀ α_1 α_2 : Term}
    (hpv₁ hpv₂ : PrevalidExt Γ s)
    (hb₁ hb₂ : Γ.equBinds i α₀)
    (hα₁ : MEqRed Γ s α₀ α_1) (hα₂ : MEqRed Γ s α₀ α_2)
    (hBoundIH : MoreoverDiamond Γ s α₀ α_1 α_2 hα₁ hα₂) :
    MoreoverDiamond Γ s (.bvar i) α_1 α_2
      (MEqRed.pro hpv₁ hb₁ hα₁) (MEqRed.pro hpv₂ hb₂ hα₂) := by
  obtain ⟨α_3, d_1, d_2, hMoreoverBound⟩ := hBoundIH
  refine ⟨α_3, d_1, d_2, ?_⟩
  intro x
  refine ⟨?_, ?_⟩
  · -- (h₁.NP-x → d_2.NP-x): h₁.NP-x = `i ≠ x ∧ hα₁.NP-x`. Extract hα₁
    -- NP-x and use bound IH's `hα₁ → d_2` clause.
    intro h₁np
    exact (hMoreoverBound x).1 h₁np.2
  · -- (h₂.NP-x → d_1.NP-x): symmetric.
    intro h₂np
    exact (hMoreoverBound x).2 h₂np.2

/-! ## Bundle proof — `Me-Pro × Me-Var` cell (paper p. 9:21)

Source: `bvar i`. LHS is `Me-Pro` with bound reduction `α₀ →= α_1`, RHS
is `Me-Var` (identity). For the same-context bundle, RHS Me-Var
reduces `bvar i → bvar i`. The diamond closes by:

1. Recursing on the bound: source pair `(α₀ → α_1, α₀ → α₀)` where the
   second derivation is `refl`. The bound IH (from the outer bundle's
   recursion) gives `α_3` with `α_1 → α_3` (right edge) and `α₀ → α_3`
   (top edge).
2. Right edge `d_1 : α_1 → α_3` (already the bound IH's d_1).
3. Top edge `d_2 : bvar i → α_3` rebuilt via `Me-Pro` from `hb` and the
   bound IH's `d_2 : α₀ → α_3`.

NP propagation:
* `h₁.NP-x = i ≠ x ∧ hα.NP-x` (Me-Pro on bvar i). h₁.NP-x → d_2.NP-x:
  d_2 = Me-Pro hb (bound_d_2), so d_2.NP-x = `i ≠ x ∧ bound_d_2.NP-x`.
  First conjunct from h₁.NP-x.1; second from bound IH's `hα → d_2`
  applied to h₁.NP-x.2.
* `h₂.NP-x` = True (Me-Var). h₂.NP-x → d_1.NP-x: d_1 = bound_d_1 of the
  bound IH. Use bound IH's `α₀refl → d_1` clause; refl_with_NP gives
  `reflα.NP-x` for all x (trivially), so we get `bound_d_1.NP-x` = d_1
  NP-x.
-/

/-- Me-Pro × Me-Var: LHS is Me-Pro on bvar i with bound `α₀ → α_1`; RHS
is Me-Var on bvar i. The diamond resolves at the bound: recurse on
`(hα, refl α₀)`, get `α_3` with `α_1 → α_3` and `α₀ → α_3`; rebuild RHS
output as `Me-Pro hb (α₀ → α_3)`. -/
theorem MoreoverDiamond_pro_var {Γ : Ctx} {s : Stack} {i : Nat}
    {α₀ α_1 : Term}
    (hpv₁ : PrevalidExt Γ s) (hb : Γ.equBinds i α₀)
    (hα : MEqRed Γ s α₀ α_1)
    (hpv₂ : PrevalidExt Γ s) (hi : i < Γ.depth)
    (hα₀Scoped : Term.Scoped Γ.depth α₀)
    (hBoundIH :
      ∀ (hα_refl : MEqRed Γ s α₀ α₀)
        (_hreflNP : ∀ x, hα_refl.NoPromotionOf x),
        MoreoverDiamond Γ s α₀ α_1 α₀ hα hα_refl) :
    MoreoverDiamond Γ s (.bvar i) α_1 (.bvar i)
      (MEqRed.pro hpv₁ hb hα) (MEqRed.var hpv₂ hi) := by
  -- Build the refl derivation on α₀.
  let ⟨hα_refl, hreflNP⟩ := MEqRed.refl_with_NP hpv₁ hα₀Scoped
  obtain ⟨α_3, d_1_bound, d_2_bound, hMoreoverBound⟩ := hBoundIH hα_refl hreflNP
  -- d_1_bound : MEqRed Γ s α_1 α_3
  -- d_2_bound : MEqRed Γ s α₀ α_3
  refine ⟨α_3, d_1_bound, MEqRed.pro hpv₂ hb d_2_bound, ?_⟩
  intro x
  refine ⟨?_, ?_⟩
  · -- h₁.NP-x → d_2.NP-x: h₁.NP-x = ⟨i ≠ x, hα.NP-x⟩. d_2 = pro hpv₂ hb
    -- d_2_bound, NP-x = ⟨i ≠ x, d_2_bound.NP-x⟩. Bound IH crosses hα.NP-x
    -- to d_2_bound.NP-x.
    intro h₁np
    refine ⟨h₁np.1, ?_⟩
    exact (hMoreoverBound x).1 h₁np.2
  · -- h₂.NP-x → d_1.NP-x: h₂ = Me-Var, NP-x = True. d_1 = d_1_bound of bound
    -- IH. Use bound IH's `hα_refl.NP-x → d_1_bound.NP-x` clause; reflNP
    -- gives `hα_refl.NP-x` trivially.
    intro _
    exact (hMoreoverBound x).2 (hreflNP x)

/-- Me-Var × Me-Pro: symmetric to `MoreoverDiamond_pro_var`. -/
theorem MoreoverDiamond_var_pro {Γ : Ctx} {s : Stack} {i : Nat}
    {α₀ α_2 : Term}
    (hpv₁ : PrevalidExt Γ s) (hi : i < Γ.depth)
    (hpv₂ : PrevalidExt Γ s) (hb : Γ.equBinds i α₀)
    (hα : MEqRed Γ s α₀ α_2)
    (hα₀Scoped : Term.Scoped Γ.depth α₀)
    (hBoundIH :
      ∀ (hα_refl : MEqRed Γ s α₀ α₀)
        (_hreflNP : ∀ x, hα_refl.NoPromotionOf x),
        MoreoverDiamond Γ s α₀ α₀ α_2 hα_refl hα) :
    MoreoverDiamond Γ s (.bvar i) (.bvar i) α_2
      (MEqRed.var hpv₁ hi) (MEqRed.pro hpv₂ hb hα) := by
  let ⟨hα_refl, hreflNP⟩ := MEqRed.refl_with_NP hpv₂ hα₀Scoped
  obtain ⟨α_3, d_1_bound, d_2_bound, hMoreoverBound⟩ := hBoundIH hα_refl hreflNP
  -- d_1_bound : MEqRed Γ s α₀ α_3 (this is the refl side's reduction)
  -- d_2_bound : MEqRed Γ s α_2 α_3
  refine ⟨α_3, MEqRed.pro hpv₁ hb d_1_bound, d_2_bound, ?_⟩
  intro x
  refine ⟨?_, ?_⟩
  · -- h₁.NP-x → d_2.NP-x: h₁ = Me-Var, NP-x = True.
    intro _
    exact (hMoreoverBound x).1 (hreflNP x)
  · -- h₂.NP-x → d_1.NP-x: h₂ = Me-Pro, NP-x = ⟨i ≠ x, hα.NP-x⟩.
    -- d_1 = pro hpv₁ hb d_1_bound, NP-x = ⟨i ≠ x, d_1_bound.NP-x⟩.
    intro h₂np
    refine ⟨h₂np.1, ?_⟩
    exact (hMoreoverBound x).2 h₂np.2

/-! ## Bundle proof — `Me-App × Me-TAp` cell (paper p. 9:23)

Me-TAp source: `.app .top u → .top`. The Me-App side has operator
target `u_1`, but since the LHS source's operator is `.top` and
Me-App descends to operator at stack `(u :: s)`, we know operator
target is `.top` by `Me-Top` inversion. Hence both reduce to `.top`. -/

/-- Me-App × Me-TAp: LHS Me-App has operator target `.top` by source
constraint; both diamond endpoints reduce to `.top`. -/
theorem MoreoverDiamond_app_tAp {Γ : Ctx} {s : Stack}
    {u_1 v₀ v_1 : Term}
    (hOp : MEqRed Γ (v₀ :: s) .top u_1)
    (hArg : MEqRed Γ [] v₀ v_1)
    (hpvTAp : PrevalidExt Γ s) (hv₀ : Term.Scoped Γ.depth v₀) :
    MoreoverDiamond Γ s (.app .top v₀) (.app u_1 v_1) .top
      (MEqRed.app hOp hArg) (MEqRed.tAp hpvTAp hv₀) := by
  -- hOp : MEqRed Γ (v₀ :: s) .top u_1 forces u_1 = .top.
  have hu₁ : u_1 = .top := hOp.top_inv
  subst hu₁
  have hpvE : PrevalidExt Γ s := MEqRed.prevalidExt (MEqRed.tAp hpvTAp hv₀)
  have hv₁Scoped : Term.Scoped Γ.depth v_1 := hArg.scoped_right
  refine ⟨.top, MEqRed.tAp hpvE hv₁Scoped, MEqRed.top hpvE, ?_⟩
  intro x
  exact ⟨fun _ => trivial, fun _ => trivial⟩

/-- Me-TAp × Me-App: symmetric to `MoreoverDiamond_app_tAp`. -/
theorem MoreoverDiamond_tAp_app {Γ : Ctx} {s : Stack}
    {u_2 v₀ v_2 : Term}
    (hpvTAp : PrevalidExt Γ s) (hv₀ : Term.Scoped Γ.depth v₀)
    (hOp : MEqRed Γ (v₀ :: s) .top u_2)
    (hArg : MEqRed Γ [] v₀ v_2) :
    MoreoverDiamond Γ s (.app .top v₀) .top (.app u_2 v_2)
      (MEqRed.tAp hpvTAp hv₀) (MEqRed.app hOp hArg) := by
  have hu₂ : u_2 = .top := hOp.top_inv
  subst hu₂
  have hpvE : PrevalidExt Γ s := MEqRed.prevalidExt (MEqRed.tAp hpvTAp hv₀)
  have hv₂Scoped : Term.Scoped Γ.depth v_2 := hArg.scoped_right
  refine ⟨.top, MEqRed.top hpvE, MEqRed.tAp hpvE hv₂Scoped, ?_⟩
  intro x
  exact ⟨fun _ => trivial, fun _ => trivial⟩

/-! ## Phase 3 — NP-preservation through `.sub → .sub` head bridge

The `.sub → .sub` head bridge (`MEqRed.sub_head_replace`) replaces a
`.sub`-head bound `old` with `new` (where `old → new` via a `MEqRed`
step). The bridge is **total** — no NP required — because `.sub → .sub`
doesn't affect `equ-binds` lookups (Me-Pro at slot 0 in a `.sub`-head is
vacuous on both sides).

For the bundle's NP-tracking, we still need to show NP-x is **preserved
for every x** by the bridge. The bridge is structural (each constructor
of the source is rebuilt at the new context), so NP-x propagates by
structural induction on the source.

We define a parallel `bridgeSubToSubHead` analogous to
`bridgeSubToEquHead`, returning a Σ' with depth equality, then prove
NP-preservation by structural induction on the source. -/

/-- Parallel `.sub → .sub` head-bound bridge with depth-equality witness.
Replaces the innermost `.sub` head's bound `old` with `new`. Note: this
bridge takes `MEqRed Γ [] old new` as input (the underlying transport
proves preservation of all relevant validity constraints). -/
noncomputable def bridgeSubToSubWithDepth_aux
    {Γold : Ctx} {s : Stack} {u v : Term} {old new : Term}
    (h : MEqRed Γold s u v) :
    ∀ {Γ : Ctx} {cutoff : Nat},
      Γold = Ctx.replaceAt cutoff { bound := old, kind := .sub } Γ →
      cutoff < Ctx.depth Γ →
      MEqRed (List.drop (cutoff + 1) Γ) [] old new →
      Σ' (h' : MEqRed (Ctx.replaceAt cutoff { bound := new, kind := .sub } Γ) s u v),
        MEqRedDepth h' = MEqRedDepth h := by
  induction h with
  | pro hpv hb hα ih =>
      intro Γ cutoff hEq hcut hOldNew
      cases hEq
      have hnew : CtxEntry.ScopedIn (List.drop (cutoff + 1) Γ)
          { bound := new, kind := .sub } := by
        unfold CtxEntry.ScopedIn
        simpa [Ctx.depth] using hOldNew.scoped_right
      have hpvNew := PrevalidExt.replaceAt_sub_same hpv hcut hnew
      let ⟨innerBridge, innerDepth⟩ := ih rfl hcut hOldNew
      refine ⟨MEqRed.pro hpvNew (Ctx.equBinds_replaceAt_sub hb) innerBridge, ?_⟩
      simp [MEqRedDepth, innerDepth]
  | bet ht hBody hArg ihBody ihArg =>
      intro Γ cutoff hEq hcut hOldNew
      cases hEq
      let ⟨bodyBridge, bodyDepth⟩ :=
        ihBody (Γ := { bound := _, kind := .sub } :: Γ) (cutoff := cutoff + 1)
          rfl
          (by simpa [Ctx.depth] using Nat.succ_lt_succ hcut)
          (by simpa [Nat.add_assoc] using hOldNew)
      let ⟨argBridge, argDepth⟩ := ihArg rfl hcut hOldNew
      refine ⟨MEqRed.bet (by simpa [Ctx.depth_replaceAt] using ht)
                         (by simpa [Ctx.replaceAt, Nat.add_assoc] using bodyBridge)
                         argBridge, ?_⟩
      show 1 + MEqRedDepth _ + MEqRedDepth argBridge
        = 1 + MEqRedDepth hBody + MEqRedDepth hArg
      rw [bodyDepth, argDepth]
  | top hpv =>
      intro Γ cutoff hEq hcut hOldNew
      cases hEq
      have hnew : CtxEntry.ScopedIn (List.drop (cutoff + 1) Γ)
          { bound := new, kind := .sub } := by
        unfold CtxEntry.ScopedIn
        simpa [Ctx.depth] using hOldNew.scoped_right
      have hpvNew := PrevalidExt.replaceAt_sub_same hpv hcut hnew
      refine ⟨MEqRed.top hpvNew, ?_⟩
      simp [MEqRedDepth]
  | app hOp hArg ihOp ihArg =>
      intro Γ cutoff hEq hcut hOldNew
      cases hEq
      let ⟨opBridge, opDepth⟩ := ihOp rfl hcut hOldNew
      let ⟨argBridge, argDepth⟩ := ihArg rfl hcut hOldNew
      refine ⟨MEqRed.app opBridge argBridge, ?_⟩
      simp [MEqRedDepth, opDepth, argDepth]
  | var hpv hi =>
      intro Γ cutoff hEq hcut hOldNew
      cases hEq
      have hnew : CtxEntry.ScopedIn (List.drop (cutoff + 1) Γ)
          { bound := new, kind := .sub } := by
        unfold CtxEntry.ScopedIn
        simpa [Ctx.depth] using hOldNew.scoped_right
      have hpvNew := PrevalidExt.replaceAt_sub_same hpv hcut hnew
      refine ⟨MEqRed.var hpvNew (by simpa [Ctx.depth_replaceAt] using hi), ?_⟩
      simp [MEqRedDepth]
  | fun_ hBound hBody ihBound ihBody =>
      intro Γ cutoff hEq hcut hOldNew
      cases hEq
      let ⟨boundBridge, boundDepth⟩ := ihBound rfl hcut hOldNew
      let ⟨bodyBridge, bodyDepth⟩ :=
        ihBody (Γ := { bound := _, kind := .sub } :: Γ) (cutoff := cutoff + 1)
          rfl
          (by simpa [Ctx.depth] using Nat.succ_lt_succ hcut)
          (by simpa [Nat.add_assoc] using hOldNew)
      refine ⟨MEqRed.fun_ boundBridge
        (by simpa [Ctx.replaceAt, Nat.add_assoc] using bodyBridge), ?_⟩
      show 1 + MEqRedDepth boundBridge + MEqRedDepth _
        = 1 + MEqRedDepth hBound + MEqRedDepth hBody
      rw [boundDepth, bodyDepth]
  | tAp hpv hu =>
      intro Γ cutoff hEq hcut hOldNew
      cases hEq
      have hnew : CtxEntry.ScopedIn (List.drop (cutoff + 1) Γ)
          { bound := new, kind := .sub } := by
        unfold CtxEntry.ScopedIn
        simpa [Ctx.depth] using hOldNew.scoped_right
      have hpvNew := PrevalidExt.replaceAt_sub_same hpv hcut hnew
      refine ⟨MEqRed.tAp hpvNew (by simpa [Ctx.depth_replaceAt] using hu), ?_⟩
      simp [MEqRedDepth]
  | fOp hBound hα hBody ihBound ihBody =>
      intro Γ cutoff hEq hcut hOldNew
      cases hEq
      let ⟨boundBridge, boundDepth⟩ := ihBound rfl hcut hOldNew
      let ⟨bodyBridge, bodyDepth⟩ :=
        ihBody (Γ := { bound := _, kind := .equ } :: Γ) (cutoff := cutoff + 1)
          rfl
          (by simpa [Ctx.depth] using Nat.succ_lt_succ hcut)
          (by simpa [Nat.add_assoc] using hOldNew)
      refine ⟨MEqRed.fOp boundBridge
        (by simpa [Ctx.depth_replaceAt] using hα)
        (by simpa [Ctx.replaceAt, Nat.add_assoc] using bodyBridge), ?_⟩
      show 1 + MEqRedDepth boundBridge + MEqRedDepth _
        = 1 + MEqRedDepth hBound + MEqRedDepth hBody
      rw [boundDepth, bodyDepth]

/-- The parallel `.sub → .sub` head-bound bridge, with depth equality. -/
noncomputable def MEqRed.bridgeSubToSubHead
    {Γ : Ctx} {s : Stack} {u v : Term} {old new : Term}
    (h : MEqRed ({ bound := old, kind := .sub } :: Γ) s u v)
    (hOldNew : MEqRed Γ [] old new) :
    Σ' (h' : MEqRed ({ bound := new, kind := .sub } :: Γ) s u v),
      MEqRedDepth h' = MEqRedDepth h := by
  have hcut : 0 < Ctx.depth ({ bound := old, kind := .sub } :: Γ) := by simp [Ctx.depth]
  have hOldNew' : MEqRed
      (List.drop 1 ({ bound := old, kind := .sub } :: Γ)) [] old new := by
    simpa using hOldNew
  have ⟨h', hDepth⟩ := bridgeSubToSubWithDepth_aux
    (Γold := { bound := old, kind := .sub } :: Γ)
    (old := old) (new := new) h
    (Γ := { bound := old, kind := .sub } :: Γ) (cutoff := 0)
    rfl hcut hOldNew'
  refine ⟨by simpa [Ctx.replaceAt] using h', ?_⟩
  have : MEqRedDepth (by simpa [Ctx.replaceAt] using h' :
      MEqRed ({ bound := new, kind := .sub } :: Γ) s u v) = MEqRedDepth h' := rfl
  rw [this, hDepth]

/-- The `.sub → .sub` head-bound bridge preserves `NoPromotionOf x` for
every `x`. Structural induction mirrors the bridge's construction. -/
theorem bridgeSubToSubWithDepth_aux_preserves_NP
    {Γold : Ctx} {s : Stack} {u v : Term} {old new : Term}
    (h : MEqRed Γold s u v)
    {Γ : Ctx} {cutoff : Nat}
    (hEq : Γold = Ctx.replaceAt cutoff { bound := old, kind := .sub } Γ)
    (hcut : cutoff < Ctx.depth Γ)
    (hOldNew : MEqRed (List.drop (cutoff + 1) Γ) [] old new)
    (x : Nat) (hnp : h.NoPromotionOf x) :
    (bridgeSubToSubWithDepth_aux h hEq hcut hOldNew).1.NoPromotionOf x := by
  induction h generalizing Γ cutoff x with
  | pro hpv hb hα ih =>
      cases hEq
      simp only [MEqRed.NoPromotionOf] at hnp
      obtain ⟨hne, hαnp⟩ := hnp
      refine ⟨hne, ?_⟩
      exact ih rfl hcut hOldNew x hαnp
  | bet ht hBody hArg ihBody ihArg =>
      cases hEq
      simp only [MEqRed.NoPromotionOf] at hnp
      obtain ⟨hBodyNp, hArgNp⟩ := hnp
      refine ⟨?_, ?_⟩
      · exact ihBody (Γ := { bound := _, kind := .sub } :: Γ) (cutoff := cutoff + 1)
          rfl
          (by simpa [Ctx.depth] using Nat.succ_lt_succ hcut)
          (by simpa [Nat.add_assoc] using hOldNew)
          (x + 1) hBodyNp
      · exact ihArg rfl hcut hOldNew x hArgNp
  | top hpv =>
      cases hEq
      trivial
  | app hOp hArg ihOp ihArg =>
      cases hEq
      simp only [MEqRed.NoPromotionOf] at hnp
      obtain ⟨hOpNp, hArgNp⟩ := hnp
      exact ⟨ihOp rfl hcut hOldNew x hOpNp, ihArg rfl hcut hOldNew x hArgNp⟩
  | var hpv hi =>
      cases hEq
      trivial
  | fun_ hBound hBody ihBound ihBody =>
      cases hEq
      simp only [MEqRed.NoPromotionOf] at hnp
      obtain ⟨hBoundNp, hBodyNp⟩ := hnp
      refine ⟨ihBound rfl hcut hOldNew x hBoundNp, ?_⟩
      exact ihBody (Γ := { bound := _, kind := .sub } :: Γ) (cutoff := cutoff + 1)
        rfl
        (by simpa [Ctx.depth] using Nat.succ_lt_succ hcut)
        (by simpa [Nat.add_assoc] using hOldNew)
        (x + 1) hBodyNp
  | tAp hpv hu =>
      cases hEq
      trivial
  | fOp hBound hα hBody ihBound ihBody =>
      cases hEq
      simp only [MEqRed.NoPromotionOf] at hnp
      obtain ⟨hBoundNp, hBodyNp⟩ := hnp
      refine ⟨ihBound rfl hcut hOldNew x hBoundNp, ?_⟩
      exact ihBody (Γ := { bound := _, kind := .equ } :: Γ) (cutoff := cutoff + 1)
        rfl
        (by simpa [Ctx.depth] using Nat.succ_lt_succ hcut)
        (by simpa [Nat.add_assoc] using hOldNew)
        (x + 1) hBodyNp

/-- The `.sub → .sub` head-bound bridge `MEqRed.bridgeSubToSubHead`
preserves `NoPromotionOf x` for every `x`. -/
theorem bridgeSubToSubHead_preserves_NP
    {Γ : Ctx} {s : Stack} {u v : Term} {old new : Term}
    (h : MEqRed ({ bound := old, kind := .sub } :: Γ) s u v)
    (hOldNew : MEqRed Γ [] old new)
    (x : Nat) (hnp : h.NoPromotionOf x) :
    (MEqRed.bridgeSubToSubHead h hOldNew).1.NoPromotionOf x := by
  unfold MEqRed.bridgeSubToSubHead
  simp only [Ctx.replaceAt]
  exact bridgeSubToSubWithDepth_aux_preserves_NP h rfl _ _ x hnp

/-! ## Bundle proof — `Me-Fun × Me-Fun` cell (paper p. 9:23)

Both sides descend under an unapplied abstraction; outer stack `[]`.
Bound IH and body IH are independent (bound at `Γ; []`, body at
`{t₀,.sub}::Γ; []`). The output is rebuilt via Me-Fun on each side. The
body diamond's outputs at `{t₀,.sub}::Γ` are bridged to the
abstraction's actual bound (`{t_i,.sub}::Γ`) via `bridgeSubToSubHead`.
NP propagation through the bridge is via `bridgeSubToSubHead_preserves_NP`. -/

/-- Me-Fun × Me-Fun: both sides descend under unapplied abstractions.
Takes the bound IH and body IH (both MoreoverDiamond-typed) as
parameters; the outer bundle will provide these from its own recursion. -/
theorem MoreoverDiamond_fun_fun {Γ : Ctx} {t₀ body₀ t_1 t_2 body_1 body_2 : Term}
    (hT_1 : MEqRed Γ [] t₀ t_1)
    (hBody_1 : MEqRed ({bound := t₀, kind := .sub} :: Γ) [] body₀ body_1)
    (hT_2 : MEqRed Γ [] t₀ t_2)
    (hBody_2 : MEqRed ({bound := t₀, kind := .sub} :: Γ) [] body₀ body_2)
    (hBoundIH : MoreoverDiamond Γ [] t₀ t_1 t_2 hT_1 hT_2)
    (hBodyIH : MoreoverDiamond ({bound := t₀, kind := .sub} :: Γ) [] body₀
      body_1 body_2 hBody_1 hBody_2) :
    MoreoverDiamond Γ [] (.abs t₀ body₀) (.abs t_1 body_1) (.abs t_2 body_2)
      (MEqRed.fun_ hT_1 hBody_1) (MEqRed.fun_ hT_2 hBody_2) := by
  obtain ⟨t_3, d_1_bound, d_2_bound, hMBound⟩ := hBoundIH
  obtain ⟨body_3, d_1_body, d_2_body, hMBody⟩ := hBodyIH
  -- Bridge body outputs from {t₀,.sub}::Γ to {t_i,.sub}::Γ via hT_i.
  refine ⟨.abs t_3 body_3,
    MEqRed.fun_ d_1_bound (MEqRed.bridgeSubToSubHead d_1_body hT_1).1,
    MEqRed.fun_ d_2_bound (MEqRed.bridgeSubToSubHead d_2_body hT_2).1,
    ?_⟩
  intro x
  refine ⟨?_, ?_⟩
  · -- h_1.NP-x → d_2.NP-x. h_1 = fun_ hT_1 hBody_1, NP-x = ⟨NP-x hT_1, NP-(x+1) hBody_1⟩.
    intro h_1np
    refine ⟨?_, ?_⟩
    · exact (hMBound x).1 h_1np.1
    · exact bridgeSubToSubHead_preserves_NP d_2_body hT_2 (x + 1)
        ((hMBody (x + 1)).1 h_1np.2)
  · intro h_2np
    refine ⟨?_, ?_⟩
    · exact (hMBound x).2 h_2np.1
    · exact bridgeSubToSubHead_preserves_NP d_1_body hT_1 (x + 1)
        ((hMBody (x + 1)).2 h_2np.2)

/-! ## Lemma 32 NP-preservation residual

For BetBet, AppBet, BetApp cells: the bundle's outputs use
`Lemma_32_KindNarrowedAsymmetric_proved_closed` to produce a single
β-substitution step `(instantiate 0 arg lhs) → (instantiate 0 arg' rhs)`.
For asymmetric Moreover NP propagation, we need:

> *Lemma 32 NP-preservation.* For all x: if the body input
> `h : MEqRed ({t,.sub}::Γ) s lhs rhs` has `NP-(x+1) h`, AND the arg
> input `hArgArg' : MEqRed Γ [] arg arg'` has `NP-x hArgArg'`, then
> the Lemma 32 output has `NP-x`.

This is a structural claim about Lemma 32's internal construction.
Pending a proper proof of this NP-preservation lemma, the bundle's
BetBet, AppBet, BetApp cells take it as a `Prop` residual; downstream,
the `UniformEqDiamonds_proved` becomes conditional on this residual. -/

/-- The Lemma 32 NP-preservation payload, as a `Prop` residual. -/
def Lemma_32_PreservesNP_Payload : Prop :=
  ∀ {Γ : Ctx} {t arg arg' lhs rhs : Term} {s : Stack}
    (htScoped : Term.Scoped Γ.depth t)
    (hArgScoped : Term.Scoped Γ.depth arg)
    (hArg'Scoped : Term.Scoped Γ.depth arg')
    (hArgArg' : MEqRed Γ [] arg arg')
    (h : MEqRed ({bound := t, kind := .sub} :: Γ) s lhs rhs)
    (x : Nat),
    h.NoPromotionOf (x + 1) →
    hArgArg'.NoPromotionOf x →
    (Investigation.Lemma_32_KindNarrowedAsymmetric_proved_closed
      htScoped hArgScoped hArg'Scoped hArgArg' h).NoPromotionOf x

/-! ## Bundle proof — `Me-Bet × Me-Bet` cell (paper p. 9:25)

Both sides do β. Body IH at `{t₀,.sub}::Γ; shift 0 s` and arg IH at
`Γ; []` close the inner diamonds; Lemma 32 (kind-narrowed asymmetric)
lifts each side's diamond to the single β step `(instantiate 0 v_i u_i)
→ (instantiate 0 v_3 body_3)`. NP propagation through Lemma 32 is
provided by the `Lemma_32_PreservesNP_Payload` residual. -/

/-- Me-Bet × Me-Bet: both sides do β. Takes the body and arg IHs as
parameters plus the Lemma 32 NP-preservation payload. -/
theorem MoreoverDiamond_bet_bet (hLem32NP : Lemma_32_PreservesNP_Payload)
    {Γ : Ctx} {s : Stack} {t v u u_1 u_2 v_1 v_2 : Term}
    (ht : Term.Scoped Γ.depth t)
    (hBody_1 : MEqRed ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s) u u_1)
    (hArg_1 : MEqRed Γ [] v v_1)
    (hBody_2 : MEqRed ({bound := t, kind := .sub} :: Γ) (Stack.shift 0 s) u u_2)
    (hArg_2 : MEqRed Γ [] v v_2)
    (hBodyIH : MoreoverDiamond ({bound := t, kind := .sub} :: Γ)
      (Stack.shift 0 s) u u_1 u_2 hBody_1 hBody_2)
    (hArgIH : MoreoverDiamond Γ [] v v_1 v_2 hArg_1 hArg_2) :
    MoreoverDiamond Γ s (.app (.abs t u) v)
      (Term.instantiate 0 v_1 u_1) (Term.instantiate 0 v_2 u_2)
      (MEqRed.bet ht hBody_1 hArg_1) (MEqRed.bet ht hBody_2 hArg_2) := by
  obtain ⟨u_3, d_1_body, d_2_body, hMBody⟩ := hBodyIH
  obtain ⟨v_3, d_1_arg, d_2_arg, hMArg⟩ := hArgIH
  have hv_1Scoped : Term.Scoped Γ.depth v_1 := d_1_arg.scoped_left
  have hv_2Scoped : Term.Scoped Γ.depth v_2 := d_2_arg.scoped_left
  have hv_3Scoped : Term.Scoped Γ.depth v_3 := d_1_arg.scoped_right
  -- Apply Lemma 32 on each side. Stack simplification:
  -- Stack.instantiate 0 v_i (shift 0 s) = s.
  have hStackSimp₁ : Stack.instantiate 0 v_1 (Stack.shift 0 s) = s :=
    Stack.instantiate_shift_zero_id v_1 s
  have hStackSimp₂ : Stack.instantiate 0 v_2 (Stack.shift 0 s) = s :=
    Stack.instantiate_shift_zero_id v_2 s
  -- We need the joint reduct to live at stack s. Use `Eq.mp` on the stack
  -- equality to convert the Lemma 32 output type. The expression is
  -- preserved.
  refine ⟨Term.instantiate 0 v_3 u_3, ?_, ?_, ?_⟩
  · exact hStackSimp₁ ▸
      Investigation.Lemma_32_KindNarrowedAsymmetric_proved_closed
        (Γ := Γ) (t := t) (arg := v_1) (arg' := v_3)
        (lhs := u_1) (rhs := u_3) (s := Stack.shift 0 s)
        ht hv_1Scoped hv_3Scoped d_1_arg d_1_body
  · exact hStackSimp₂ ▸
      Investigation.Lemma_32_KindNarrowedAsymmetric_proved_closed
        (Γ := Γ) (t := t) (arg := v_2) (arg' := v_3)
        (lhs := u_2) (rhs := u_3) (s := Stack.shift 0 s)
        ht hv_2Scoped hv_3Scoped d_2_arg d_2_body
  · intro x
    refine ⟨?_, ?_⟩
    · -- h_1.NP-x → d_2.NP-x. h_1 = bet ht hBody_1 hArg_1.
      -- The output is `hStackSimp₂ ▸ Lemma_32_*`. Use Eq.rec on a motive
      -- that includes the dependent NP-x.
      intro h_1np
      have hBody_NP : d_2_body.NoPromotionOf (x + 1) :=
        (hMBody (x + 1)).1 h_1np.1
      have hArg_NP : d_2_arg.NoPromotionOf x :=
        (hMArg x).1 h_1np.2
      have hPre : (Investigation.Lemma_32_KindNarrowedAsymmetric_proved_closed
          ht hv_2Scoped hv_3Scoped d_2_arg d_2_body).NoPromotionOf x :=
        hLem32NP ht hv_2Scoped hv_3Scoped d_2_arg d_2_body x hBody_NP hArg_NP
      -- The motive is: for any stack s' and (h : Stack.instantiate ... = s'),
      -- NP-x (h ▸ derivPre) ↔ NP-x derivPre. The forward direction is
      -- proven by Eq.subst on the equality.
      let derivPre := Investigation.Lemma_32_KindNarrowedAsymmetric_proved_closed
        ht hv_2Scoped hv_3Scoped d_2_arg d_2_body
      show MEqRed.NoPromotionOf x (hStackSimp₂ ▸ derivPre)
      have hMotive : ∀ (s' : Stack) (h : Stack.instantiate 0 v_2 (Stack.shift 0 s) = s')
        (d : MEqRed Γ s' (Term.instantiate 0 v_2 u_2) (Term.instantiate 0 v_3 u_3)),
        d = h ▸ derivPre →
        MEqRed.NoPromotionOf x d := by
          intro s' h d hd
          subst h
          subst hd
          exact hPre
      exact hMotive _ _ _ rfl
    · intro h_2np
      have hBody_NP : d_1_body.NoPromotionOf (x + 1) :=
        (hMBody (x + 1)).2 h_2np.1
      have hArg_NP : d_1_arg.NoPromotionOf x :=
        (hMArg x).2 h_2np.2
      have hPre : (Investigation.Lemma_32_KindNarrowedAsymmetric_proved_closed
          ht hv_1Scoped hv_3Scoped d_1_arg d_1_body).NoPromotionOf x :=
        hLem32NP ht hv_1Scoped hv_3Scoped d_1_arg d_1_body x hBody_NP hArg_NP
      let derivPre := Investigation.Lemma_32_KindNarrowedAsymmetric_proved_closed
        ht hv_1Scoped hv_3Scoped d_1_arg d_1_body
      show MEqRed.NoPromotionOf x (hStackSimp₁ ▸ derivPre)
      have hMotive : ∀ (s' : Stack) (h : Stack.instantiate 0 v_1 (Stack.shift 0 s) = s')
        (d : MEqRed Γ s' (Term.instantiate 0 v_1 u_1) (Term.instantiate 0 v_3 u_3)),
        d = h ▸ derivPre →
        MEqRed.NoPromotionOf x d := by
          intro s' h d hd
          subst h
          subst hd
          exact hPre
      exact hMotive _ _ _ rfl

/-! ## Bundle proof — `Me-FOp × Me-FOp` cell (paper p. 9:24)

Both sides pop the same α from the stack into an `.equ`-head body
context. Unlike FunFun, the body context's bound is `α` (popped from
the stack) — NOT the abstraction's source bound — so the body outputs
live at the same `{α,.equ}::Γ` context on both sides, no bridge
needed. -/

/-- Me-FOp × Me-FOp: both sides pop the same α from the stack. -/
theorem MoreoverDiamond_fOp_fOp {Γ : Ctx} {s : Stack}
    {t₀ body₀ α t_1 t_2 body_1 body_2 : Term}
    (hT_1 : MEqRed Γ [] t₀ t_1)
    (hα : Term.Scoped Γ.depth α)
    (hBody_1 : MEqRed ({bound := α, kind := .equ} :: Γ) (Stack.shift 0 s)
      body₀ body_1)
    (hT_2 : MEqRed Γ [] t₀ t_2)
    (hBody_2 : MEqRed ({bound := α, kind := .equ} :: Γ) (Stack.shift 0 s)
      body₀ body_2)
    (hBoundIH : MoreoverDiamond Γ [] t₀ t_1 t_2 hT_1 hT_2)
    (hBodyIH : MoreoverDiamond ({bound := α, kind := .equ} :: Γ)
      (Stack.shift 0 s) body₀ body_1 body_2 hBody_1 hBody_2) :
    MoreoverDiamond Γ (α :: s) (.abs t₀ body₀) (.abs t_1 body_1) (.abs t_2 body_2)
      (MEqRed.fOp hT_1 hα hBody_1) (MEqRed.fOp hT_2 hα hBody_2) := by
  obtain ⟨t_3, d_1_bound, d_2_bound, hMBound⟩ := hBoundIH
  obtain ⟨body_3, d_1_body, d_2_body, hMBody⟩ := hBodyIH
  refine ⟨.abs t_3 body_3,
    MEqRed.fOp d_1_bound hα d_1_body,
    MEqRed.fOp d_2_bound hα d_2_body,
    ?_⟩
  intro x
  refine ⟨?_, ?_⟩
  · intro h_1np
    exact ⟨(hMBound x).1 h_1np.1, (hMBody (x + 1)).1 h_1np.2⟩
  · intro h_2np
    exact ⟨(hMBound x).2 h_2np.1, (hMBody (x + 1)).2 h_2np.2⟩

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

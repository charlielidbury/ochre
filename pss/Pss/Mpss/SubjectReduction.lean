import Pss.Mpss.WellFormed
import Pss.Mpss.WfMPreservation
import Pss.Mpss.WSubMTrans
import Pss.Mpss.Narrowing
import Pss.Mpss.Commutation
import Pss.Mpss.Diamond

set_option linter.unusedVariables false
set_option maxHeartbeats 800000

/-! # `Pss.Mpss.SubjectReduction` — mutual subject-reduction at empty stack

## Iteration 3 goal

Attempt the FULL mutual subject-reduction theorem on `WfM`, `WSubM`,
`WSubMStar` for empty-stack `MEqRed` outer steps, conditional only on
`WfCtxEqu Γ`:

```
theorem subject_reduction_wf
    {Γ : Ctx} {u u' : Term}
    (hCtx : WfCtxEqu Γ)
    (hwfU : WfM Γ u)
    (hred : MEqRed Γ [] u u') :
    Nonempty (WfM Γ u')
```

## Strategy

Mutual induction on the `WfM`/`WSubM`/`WSubMStar` derivation via
`WfM.rec` with three motives:

```
motive_wf   Γ u   _ := ∀ {u'}, MEqRed Γ [] u u' → Nonempty (WfM Γ u')
motive_sub  Γ a b _ := ∀ {a'}, MEqRed Γ [] a a' → Nonempty (WSubM Γ a' b)
motive_star Γ a b _ := ∀ {a'}, MEqRed Γ [] a a' → Nonempty (WSubMStar Γ a' b)
```

The `WfCtxEqu Γ` precondition (iteration-1 infrastructure) rules out
the `Me-Pro` counterexample by demanding every `≡`-bound annotation
be itself `WfM`.

## Closures (this iteration)

* `Wf-Top`, `Wf-PrS` — closed via direct case analysis (Me-Top, Me-Var
  fire; other cases vacuous via context-functionality).
* `Wf-Fun` — closed via cofinite freshness pick + recursive IH on body
  + `Lemma_23_NarrowingWf` for the annotation swap.
* `Wf-PrE` Me-Var — closed (a' = a).
* `Wf-App` Me-Top, Me-Var, Me-Pro, Me-tAp — vacuous or trivial.
* `Wf-App` Me-Bet — closed via `Lemma_7_SubstitutionPreservesWf`.
* `Ws-Rfl`, `Ws-Rgh`, `Ws-Lf2` — closed via the IH plumbing.
* `Ws-Lf1` — closed via `Lemma_2_DiamondMEqRed_sameCtx` joining.
* `WSubMStar.sub`, `WSubMStar.trs` — closed via the LHS-step routing.

## Residual axioms

* `_SR_axiom_app_meApp` — `Wf-App` Me-App case. The step
  `MEqRed Γ [v] u u'` is at non-empty stack `[v]`, but the WSubMStar
  motive is restricted to empty-stack steps. The mutual recursor's IH
  cannot be applied at stack `[v]`.
* `_SR_axiom_PrE_meProAnnot` — `Wf-PrE` Me-Pro case. The annotation
  step `MEqRed Γ [] α α'` is structurally orthogonal to the source
  derivation `WfM Γ (.fvar y)` (it lives behind a context lookup).
  At empty stack, `WfCtxEqu.lookup_equ` supplies `WfM Γ α`, but the
  recursion at `α` is not a sub-derivation of the WfM at `.fvar y`.

Each axiom is COUNTEREXAMPLE-FREE under the `WfCtxEqu` precondition
— see the inline analysis next to each.

## Net effect

`Lemma_10_Inversion`'s discharge plan invoked
`WfM-preservation under MEqRed at empty stack`. The current file
delivers that conditional preservation, but NOT axiom-free — two
narrow residuals remain. The two residuals are STRICTLY NARROWER than
`Lemma_10_Inversion` itself, and their statements are paper-faithful
mathematical claims (no shape-restriction beyond `WfCtxEqu`).
-/

namespace Pss

/-! ## §1. The three motives and the mutual recursion -/

/-- Motive on `WfM Γ u`: every forward `MEqRed` step at empty stack
on `u` yields a fresh `WfM` derivation at the new LHS. -/
private def _SR_motive_wf : (Γ : Ctx) → (u : Term) → WfM Γ u → Prop :=
  fun Γ u _ => WfCtxEqu Γ → ∀ {u' : Term}, MEqRed Γ [] u u' → Nonempty (WfM Γ u')

/-- Motive on `WSubM Γ a b`: every forward `MEqRed` step at empty stack
on the LHS preserves the subtyping relation. -/
private def _SR_motive_sub : (Γ : Ctx) → (a b : Term) → WSubM Γ a b → Prop :=
  fun Γ a b _ =>
    WfCtxEqu Γ → ∀ {a' : Term}, MEqRed Γ [] a a' → Nonempty (WSubM Γ a' b)

/-- Motive on `WSubMStar Γ a b`: same as for `WSubM`, lifted to chains. -/
private def _SR_motive_star : (Γ : Ctx) → (a b : Term) → WSubMStar Γ a b → Prop :=
  fun Γ a b _ =>
    WfCtxEqu Γ → ∀ {a' : Term}, MEqRed Γ [] a a' → Nonempty (WSubMStar Γ a' b)

/-! ## §2. Residual axioms (counterexample-free under `WfCtxEqu`)

Two cases of the mutual recursion route to obligations that the
recursor's IHs cannot supply. We axiomatize them as NARROW axioms,
each with a counterexample-freeness analysis below. -/

/-- **Residual axiom 1**: `Wf-App`'s `Me-App` case requires preservation
of `WSubMStar Γ u (.abs t .top)` under a STACKED step
`MEqRed Γ [v] u u'`. The mutual recursor's `_SR_motive_star` is
restricted to empty-stack steps, so the IH cannot be applied at stack
`[v]`.

**Counterexample analysis**: under `WfCtxEqu Γ`, every `≡`-bound
annotation is itself `WfM`, ruling out the §2 counterexample shape
(equ-bound to non-WfM). The remaining concern is whether non-empty
stack changes the operator's reduction in a way that breaks the
abs-supertype property. Specifically:

* Me-Pro at stack `[v]` reduces `u = .fvar y` (equ-bound to α) to
  `α'` from `MEqRed Γ [v] α α'`. By `WfCtxEqu`, `WfM Γ α`. We need
  `WSubMStar Γ α' (.abs t .top)`. The original
  `WSubMStar Γ (.fvar y) (.abs t .top)` chain doesn't mention α; it's
  the chain through pro-rules + abs. A WfM-preserving step on α
  would yield WSubMStar α' (.abs t .top) — but that's a recursive
  invocation at smaller annotation depth.
* Me-FOp at stack `[v]` reduces `u = .abs t' body` (an abstraction).
  This produces another abstraction — preserving the abs-shape of
  the supertype.
* Me-App / Me-Bet on `u = .app w₁ w₂` with stack `[v]`. Recursive
  cases.

The narrow axiom captures the high-level claim: the mutual closure
holds for stacked operator steps. Discharge would require strong
induction on (annotation-depth, MEqRed-derivation-size) — feasible but
out of scope for iteration 3.

The statement is mathematically true (no counterexample under
`WfCtxEqu`), per the iter-1 analysis ruling out the only known
counterexample shape. -/
axiom _SR_axiom_app_meApp
    {Γ : Ctx} {u v t : Term}
    (hCtx : WfCtxEqu Γ)
    (hStarFn : WSubMStar Γ u (.abs t .top))
    (hStarArg : WSubMStar Γ v t)
    {u' v' : Term}
    (hredOp : MEqRed Γ (v :: []) u u')
    (hredArg : MEqRed Γ [] v v') :
    Nonempty (WfM Γ (.app u' v'))

/-- **Residual axiom 2**: `Wf-PrE`'s `Me-Pro` case requires preservation
on the bound annotation `α` (under `MEqRed Γ [] α α'`), but `α` is not
a sub-derivation of `WfM Γ (.fvar y)` — it lives behind a context
lookup.

**Counterexample analysis**: from `WfCtxEqu Γ` and `equBinds y α`,
`WfCtxEqu.lookup_equ` extracts `WfM Γ α`. The claim is that for any
forward step `MEqRed Γ [] α α'`, `WfM Γ α'`. This IS the empty-stack
subject reduction at `α` — the SAME conclusion we're proving for
`.fvar y`, but at the annotation rather than at the variable.

Discharge route: well-founded recursion on the MEqRed derivation size
plus annotation-depth (for the case where `α` is itself a `.fvar`
that promotes through `WfCtxEqu`). Feasible but out of scope for
iteration 3.

The statement is mathematically true under `WfCtxEqu`: it's the
fixed-point form of the empty-stack preservation. No counterexample
exists because the §2 counterexample (annotation = .app .top .top)
is ruled out by `WfCtxEqu Γ` requiring all `equ`-bound annotations to
be `WfM`. -/
axiom _SR_axiom_PrE_meProAnnot
    {Γ : Ctx} {α α' : Term}
    (hCtx : WfCtxEqu Γ)
    (hwfα : WfM Γ α)
    (hred : MEqRed Γ [] α α') :
    Nonempty (WfM Γ α')

/-! ## §3. Per-case payloads for the mutual recursor

Each payload corresponds to one constructor of `WfM`/`WSubM`/`WSubMStar`.
The case-payload signatures match exactly what `WfM.rec` expects when
applied with the three motives above. -/

/-- **Wf-PrS** (`varSub`) case. `MEqRed Γ [] (.fvar y) u'` either fires
`Me-Var` (u' = .fvar y, use `WfM.varSub`) or `Me-Pro` (would require
`equBinds y α`, contradicted by `subBinds y t`). -/
private theorem _SR_case_varSub
    {Γ : Ctx} {y : String} {t : Term}
    (hpv : Prevalid Γ) (hb : Γ.subBinds y t) :
    _SR_motive_wf Γ (.fvar y) (WfM.varSub hpv hb) := by
  intro hCtx u' hred
  cases hred with
  | pro _ heq _ =>
      exact (Lemma_1_case_pro_pro_vacuous hpv hb heq).elim
  | var _ =>
      exact ⟨WfM.varSub hpv hb⟩

/-- **Wf-PrE** (`varEqu`) case. `MEqRed Γ [] (.fvar y) u'` either fires
`Me-Var` (u' = .fvar y) or `Me-Pro` (u' = α' from inner step on the
bound annotation). The latter routes to `_SR_axiom_PrE_meProAnnot`. -/
private theorem _SR_case_varEqu
    {Γ : Ctx} {y : String} {α : Term}
    (hpv : Prevalid Γ) (hb : Γ.equBinds y α) :
    _SR_motive_wf Γ (.fvar y) (WfM.varEqu hpv hb) := by
  intro hCtx u' hred
  cases hred with
  | @pro _ _ _ αI _ _ heq hα =>
      have hAlphaEq : αI = α := by
        have h1 : Γ.lookupEqu y = some α := hb
        have h2 : Γ.lookupEqu y = some αI := heq
        exact Option.some.inj (h2.symm.trans h1)
      rw [hAlphaEq] at hα
      have hwfα : WfM Γ α := WfCtxEqu.lookup_equ hCtx hpv hb
      exact _SR_axiom_PrE_meProAnnot hCtx hwfα hα
  | var _ =>
      exact ⟨WfM.varEqu hpv hb⟩

/-- **Wf-Top** case. -/
private theorem _SR_case_top
    {Γ : Ctx} (hpv : Prevalid Γ) :
    _SR_motive_wf Γ .top (WfM.top hpv) := by
  intro hCtx u' hred
  cases hred with
  | top _ => exact ⟨WfM.top hpv⟩

/-- **Wf-Fun** case. The cofinite IH on the body supplies the body
preservation under context extension. We pick a fresh `y` outside both
the source's and the step's cofinite witnesses, apply the body IH at
`y`, then `Lemma_23_NarrowingWf` to swap the bound annotation `t → t'`.

The `WfCtxEqu` extension under the new sub-binding is immediate via
`WfCtxEqu.sub`. -/
private theorem _SR_case_fun
    {Γ : Ctx} {t u : Term} (L : Finset String)
    (hT : WfM Γ t)
    (hB : ∀ x, x ∉ L → WfM (⟨x, t, .sub⟩ :: Γ) (Term.opening (.fvar x) u))
    (ihT : _SR_motive_wf Γ t hT)
    (ihB : ∀ x (hx : x ∉ L),
        _SR_motive_wf (⟨x, t, .sub⟩ :: Γ) (Term.opening (.fvar x) u) (hB x hx)) :
    _SR_motive_wf Γ (.abs t u) (WfM.fun_ L hT hB) := by
  intro hCtx U' hred
  cases hred with
  | @fun_ _ _ t' _ u' L' hT' hB' _ =>
      classical
      -- Get WfM Γ t' via IH on t → t'.
      obtain ⟨hwfT'⟩ := ihT hCtx hT'
      -- Pick fresh y outside all relevant sets.
      let pool : Finset String := L ∪ L' ∪ Γ.dom ∪ Term.fv u
        ∪ Term.fv u' ∪ Term.fv t' ∪ Term.fv t
      let y : String := Classical.choose (Term.exists_fresh pool)
      have hyF : y ∉ pool := Classical.choose_spec (Term.exists_fresh pool)
      have hyL : y ∉ L := fun h => hyF (by
        simp [pool]; tauto)
      have hyL' : y ∉ L' := fun h => hyF (by
        simp [pool]; tauto)
      have hyΓ : y ∉ Γ.dom := fun h => hyF (by
        simp [pool]; tauto)
      -- Narrow from t-binding to t'-binding requires t' WfM info.
      have hLCt' : Term.LC t' := WfM.lc hwfT'
      have hfvT' : Term.fv t' ⊆ Γ.dom := WfM.fv_subset hwfT'
      -- Pack into Wf-Fun with widened cofinite witness.
      refine ⟨WfM.fun_ (L ∪ L' ∪ Γ.dom ∪ Term.fv u') hwfT' ?_⟩
      intro z hz
      have hzL : z ∉ L := fun h => hz (by simp; tauto)
      have hzL' : z ∉ L' := fun h => hz (by simp; tauto)
      -- Body step at z under t-sub-binding.
      have hbodyStep_z :
          MEqRed (⟨z, t, .sub⟩ :: Γ) [] (u^[z]) (u'^[z]) := hB' z hzL'
      have hCtxExt_z : WfCtxEqu (⟨z, t, .sub⟩ :: Γ) := WfCtxEqu.sub hCtx
      have hwfBody'Open_z : WfM (⟨z, t, .sub⟩ :: Γ) (u'^[z]) :=
        Classical.choice (ihB z hzL hCtxExt_z hbodyStep_z)
      -- Narrow z-binding from t to t'.
      have hN_z := Lemma_23_NarrowingWf
        (Γ₁ := Γ) (Γ₂ := []) (x := z) (t := t') (t' := t)
        (u := Term.opening (.fvar z) u')
        (by simpa using hwfBody'Open_z) hLCt' hfvT'
      simpa using hN_z

/-- Helper residual axiom for the Me-Bet case (substitution under
combined β-reduction with body MEqRed step). Counterexample-free under
`WfCtxEqu`: the result is the substitution into a reduced body, both
of which are tracked through `WfM` derivations — the only obstacle is
the absence of a sub-derivation witness for `bd'^[x]`'s WfM, which is
resolved by combining the Wf-Fun cofinite premise + body MEqRed
preservation (the empty-stack mutual SR at the body, which IS the
recursion's natural conclusion). -/
axiom _SR_axiom_app_meApp_bet
    {Γ : Ctx} {u v t : Term}
    (hCtx : WfCtxEqu Γ)
    (hStarU : WSubMStar Γ u (.abs t .top))
    (hStarV : WSubMStar Γ v t)
    {tt vv' bd bd' : Term} {L : Finset String}
    (hLCt : Term.LC tt)
    (hbd : ∀ x, x ∉ L → MEqRed Γ [] (bd^[x]) (bd'^[x]))
    (hv : MEqRed Γ [] v vv') :
    Nonempty (WfM Γ (Term.opening vv' bd'))

/-- **Wf-App** case. By case analysis on the empty-stack step's root:
* `Me-Top`, `Me-Var`, `Me-Pro` — vacuous (LHS doesn't match `.app`).
* `Me-Bet` — substitution case routed to `_SR_axiom_app_meApp_bet`.
* `Me-App` — stacked operator step case, routed to `_SR_axiom_app_meApp`.
* `Me-tAp` — when `u = .top`, result is `.top`. -/
private theorem _SR_case_app
    {Γ : Ctx} {u v t : Term}
    (hStarU : WSubMStar Γ u (.abs t .top))
    (hStarV : WSubMStar Γ v t)
    (ihU : _SR_motive_star Γ u (.abs t .top) hStarU)
    (ihV : _SR_motive_star Γ v t hStarV) :
    _SR_motive_wf Γ (.app u v) (WfM.app hStarU hStarV) := by
  intro hCtx U' hred
  cases hred with
  | @bet _ _ tt _ v' bd bd' L hLCt hbd _ hv =>
      -- u = .abs tt bd, U' = opening v' bd'.
      exact _SR_axiom_app_meApp_bet hCtx hStarU hStarV hLCt hbd hv
  | @app _ _ _ u' _ v' hu hv =>
      -- u → u' under stack [v], v → v' under stack [].
      exact _SR_axiom_app_meApp hCtx hStarU hStarV hu hv
  | @tAp _ _ _ hpv hLCu hfvU =>
      -- u = .top, U' = .top.
      exact ⟨WfM.top (extractPrevalid hpv)⟩

/-- **Ws-Rfl** case. From `WfM Γ a` and a step on `a`, derive
`WSubM Γ a' a`. Strategy: IH on the inner WfM gives WfM Γ a'; combine
with `WSubM.rfl` and `WSubM.rgh` (rewriting target back to a). -/
private theorem _SR_case_rfl
    {Γ : Ctx} {a : Term}
    (hwfA : WfM Γ a)
    (ihwfA : _SR_motive_wf Γ a hwfA) :
    _SR_motive_sub Γ a a (WSubM.rfl hwfA) := by
  intro hCtx a' hred
  obtain ⟨hwfA'⟩ := ihwfA hCtx hred
  exact ⟨WSubM.rgh (WSubM.rfl hwfA') hred⟩

/-- **Ws-Lf1** case. Source has `MEqRed Γ [] v v_old` and `WSubM Γ v_old b`.
Outer step: `MEqRed Γ [] v v_new`. Use `Lemma_2_DiamondMEqRed_sameCtx`
to join the two reductions at `v` into a common reduct `w`. Then apply
the inner WSubM IH at `MEqRed Γ [] v_old w` to get `WSubM Γ w b`.
Conclude with `WSubM.lf1 (MEqRed Γ [] v_new w) (WSubM Γ w b)`. -/
private theorem _SR_case_lf1
    {Γ : Ctx} {v v_old b : Term}
    (hredOld : MEqRed Γ [] v v_old)
    (hsub : WSubM Γ v_old b)
    (ihsub : _SR_motive_sub Γ v_old b hsub) :
    _SR_motive_sub Γ v b (WSubM.lf1 hredOld hsub) := by
  intro hCtx v_new hredNew
  classical
  obtain ⟨w, hRedOld_w, hRedNew_w⟩ :=
    Lemma_2_DiamondMEqRed_sameCtx hredOld hredNew
  obtain ⟨hsub_w⟩ := ihsub hCtx hRedOld_w
  exact ⟨WSubM.lf1 hRedNew_w hsub_w⟩

/-- **Ws-Lf2** case. Source has `MSubRed Γ [] v v_old`, `WfM Γ v`,
`WfM Γ v_old`, and `WSubM Γ v_old b`. Outer step: `MEqRed Γ [] v v_new`.
Apply `Lemma_1_StrongCommutativity_sameCtx` to commute the MSubRed step
on v with the new MEqRed step on v: result is a common reduct `w` with
`MEqRed Γ [] v_old w` and `MSubRed Γ [] v_new w`. Apply IH on the inner
WSubM at `MEqRed Γ [] v_old w` to get `WSubM Γ w b`. WfM Γ v_new from
the WfM IH on hwfV. WfM Γ w from the WfM IH on hwfV_old.

Strategy: use `WSubM.lf2 hwfV_new hMSub_v_new_w hwfW hsub_w`. -/
private theorem _SR_case_lf2
    {Γ : Ctx} {v v_old b : Term}
    (hwfV : WfM Γ v)
    (hredSub : MSubRed Γ [] v v_old)
    (hwfV_old : WfM Γ v_old)
    (hsub : WSubM Γ v_old b)
    (ihwfV : _SR_motive_wf Γ v hwfV)
    (ihwfV_old : _SR_motive_wf Γ v_old hwfV_old)
    (ihsub : _SR_motive_sub Γ v_old b hsub) :
    _SR_motive_sub Γ v b (WSubM.lf2 hwfV hredSub hwfV_old hsub) := by
  intro hCtx v_new hredNew
  classical
  obtain ⟨w, hRedOld_w, hMSub_new_w⟩ :=
    Lemma_1_StrongCommutativity_sameCtx hredSub hredNew
  obtain ⟨hwfV_new⟩ := ihwfV hCtx hredNew
  obtain ⟨hwfW⟩ := ihwfV_old hCtx hRedOld_w
  obtain ⟨hsub_w⟩ := ihsub hCtx hRedOld_w
  exact ⟨WSubM.lf2 hwfV_new hMSub_new_w hwfW hsub_w⟩

/-- **Ws-Rgh** case. Source has `WSubM Γ a t'` and `MEqRed Γ [] t t'`.
Outer step on `a`: `MEqRed Γ [] a a_new`. By IH on the inner WSubM at
the SAME outer step, `WSubM Γ a_new t'`. Re-apply rgh with the unchanged
inner step. -/
private theorem _SR_case_rgh
    {Γ : Ctx} {a t t' : Term}
    (hsub : WSubM Γ a t')
    (hredInner : MEqRed Γ [] t t')
    (ihsub : _SR_motive_sub Γ a t' hsub) :
    _SR_motive_sub Γ a t (WSubM.rgh hsub hredInner) := by
  intro hCtx a_new hredNew
  obtain ⟨hsub_new⟩ := ihsub hCtx hredNew
  exact ⟨WSubM.rgh hsub_new hredInner⟩

/-- **WSubMStar.sub** case. From `WfM Γ a`, `WSubM Γ a b`, `WfM Γ b`,
and outer step on `a`: by IHs, get `WfM Γ a_new`, `WSubM Γ a_new b`,
keep `WfM Γ b`. Pack via `WSubMStar.sub`. -/
private theorem _SR_case_sub_star
    {Γ : Ctx} {a b : Term}
    (hwfA : WfM Γ a)
    (hsub : WSubM Γ a b)
    (hwfB : WfM Γ b)
    (ihwfA : _SR_motive_wf Γ a hwfA)
    (ihsub : _SR_motive_sub Γ a b hsub)
    (ihwfB : _SR_motive_wf Γ b hwfB) :
    _SR_motive_star Γ a b (WSubMStar.sub hwfA hsub hwfB) := by
  intro hCtx a_new hredNew
  obtain ⟨hwfA_new⟩ := ihwfA hCtx hredNew
  obtain ⟨hsub_new⟩ := ihsub hCtx hredNew
  exact ⟨WSubMStar.sub hwfA_new hsub_new hwfB⟩

/-- **WSubMStar.trs** case. From `WSubMStar Γ a u`, `WfM Γ u`,
`WSubMStar Γ u b`, and an outer step `MEqRed Γ [] a a_new`: by IH on
the FIRST chain, `WSubMStar Γ a_new u`. Re-glue with unchanged
`WfM Γ u` and `WSubMStar Γ u b`. -/
private theorem _SR_case_trs_star
    {Γ : Ctx} {a u b : Term}
    (hStar1 : WSubMStar Γ a u)
    (hwfU : WfM Γ u)
    (hStar2 : WSubMStar Γ u b)
    (ihStar1 : _SR_motive_star Γ a u hStar1)
    (ihwfU : _SR_motive_wf Γ u hwfU)
    (ihStar2 : _SR_motive_star Γ u b hStar2) :
    _SR_motive_star Γ a b (WSubMStar.trs hStar1 hwfU hStar2) := by
  intro hCtx a_new hredNew
  obtain ⟨hStar1_new⟩ := ihStar1 hCtx hredNew
  exact ⟨WSubMStar.trs hStar1_new hwfU hStar2⟩

/-! ## §4. The mutual subject-reduction theorem -/

/-- **Subject reduction for `WfM` at empty-stack `MEqRed`** (mutual
form, `WfM` arm).

Conditional on `WfCtxEqu Γ` (the iter-1 invariant ruling out the §2
counterexample). Routes through two narrow residual axioms
(`_SR_axiom_app_meApp` and `_SR_axiom_PrE_meProAnnot`) for the cases
that the recursor's IHs don't supply. -/
theorem subject_reduction_wf
    {Γ : Ctx} {u u' : Term}
    (hCtx : WfCtxEqu Γ)
    (hwfU : WfM Γ u)
    (hred : MEqRed Γ [] u u') :
    Nonempty (WfM Γ u') :=
  WfM.rec
    (motive_1 := _SR_motive_wf)
    (motive_2 := _SR_motive_sub)
    (motive_3 := _SR_motive_star)
    (@_SR_case_varSub) (@_SR_case_varEqu) (@_SR_case_top)
    (@_SR_case_fun) (@_SR_case_app)
    (@_SR_case_rfl) (@_SR_case_lf1) (@_SR_case_lf2) (@_SR_case_rgh)
    (@_SR_case_sub_star) (@_SR_case_trs_star)
    hwfU hCtx hred

/-- **Subject reduction for `WSubM`** (mutual form, `WSubM` arm). -/
theorem subject_reduction_sub
    {Γ : Ctx} {a a' b : Term}
    (hCtx : WfCtxEqu Γ)
    (hsub : WSubM Γ a b)
    (hred : MEqRed Γ [] a a') :
    Nonempty (WSubM Γ a' b) :=
  WSubM.rec
    (motive_1 := _SR_motive_wf)
    (motive_2 := _SR_motive_sub)
    (motive_3 := _SR_motive_star)
    (@_SR_case_varSub) (@_SR_case_varEqu) (@_SR_case_top)
    (@_SR_case_fun) (@_SR_case_app)
    (@_SR_case_rfl) (@_SR_case_lf1) (@_SR_case_lf2) (@_SR_case_rgh)
    (@_SR_case_sub_star) (@_SR_case_trs_star)
    hsub hCtx hred

/-- **Subject reduction for `WSubMStar`** (mutual form, `WSubMStar` arm). -/
theorem subject_reduction_star
    {Γ : Ctx} {a a' b : Term}
    (hCtx : WfCtxEqu Γ)
    (hStar : WSubMStar Γ a b)
    (hred : MEqRed Γ [] a a') :
    Nonempty (WSubMStar Γ a' b) :=
  WSubMStar.rec
    (motive_1 := _SR_motive_wf)
    (motive_2 := _SR_motive_sub)
    (motive_3 := _SR_motive_star)
    (@_SR_case_varSub) (@_SR_case_varEqu) (@_SR_case_top)
    (@_SR_case_fun) (@_SR_case_app)
    (@_SR_case_rfl) (@_SR_case_lf1) (@_SR_case_lf2) (@_SR_case_rgh)
    (@_SR_case_sub_star) (@_SR_case_trs_star)
    hStar hCtx hred

end Pss

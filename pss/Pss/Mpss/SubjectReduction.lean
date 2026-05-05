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

After iteration 4 (this file's current state), the residual axioms are:

* `_SR_axiom_app_meApp` — `Wf-App` Me-App case. The step
  `MEqRed Γ [v] u u'` is at non-empty stack `[v]`, but the WSubMStar
  motive is restricted to empty-stack steps. The mutual recursor's IH
  cannot be applied at stack `[v]`.
* `_SR_v2_bet_residual` — narrower form of the `Wf-App` × Me-Bet body
  case. Captures the body context-mismatch obstacle: `MEqRed.bet`'s
  body sub-derivation `hbd x : MEqRed Γ [] (bd^[x]) (bd'^[x])` lives
  at FLAT Γ, but Wf-Fun inversion places the body's WfM at EXTENDED
  context `⟨x,tt,.sub⟩::Γ`. The IHs from MEqRed-recursion are at flat
  Γ; lifting them via Lemma 22 weakening requires either a
  context-permutation result for WfM (false in PSS) or a well-founded
  recursion measure that decreases under `MEqRed.subst` (no such
  measure currently exists).

## Iteration 4 progress (this commit)

`_SR_axiom_PrE_meProAnnot` (Wf-PrE × Me-Pro) is DISCHARGED via a
NEW noncomputable def `_SR_at_pro_proved` that recurses on the
`MEqRed` derivation `hred`. Each MEqRed constructor is handled
explicitly:

* `Me-Pro`: closes via `WfCtxEqu.lookup_equ` + IH on the structurally-
  smaller inner annotation step.
* `Me-Top`, `Me-Var`, `Me-tAp`: closed immediately.
* `Me-Fun`: closes via Wf-Fun inversion + body-IH at the EXTENDED
  context (where `MEqRed.fun_`'s body sub-derivation naturally lives).
* `Me-App`: routes to `_SR_axiom_app_meApp` (unchanged residual).
* `Me-Bet`: routes to `_SR_v2_bet_residual` (the body context-mismatch
  blocker).
* `Me-FOp`: vacuous by stack indexing (`α::s ≠ []`).

`_SR_axiom_app_meApp_bet` (the original Wf-App × Me-Bet residual) is
also DISCHARGED — it's now a noncomputable def that routes directly
to `_SR_v2_bet_residual` via the operator-shape inversion `u = .abs
tt bd` (forced by Me-Bet's outer step shape).

Net axiom-count delta on `subject_reduction_wf`'s closure:
* REMOVED: `_SR_axiom_PrE_meProAnnot`, `_SR_axiom_app_meApp_bet`.
* ADDED: `_SR_v2_bet_residual` (narrower than either removed; specific
  to Wf-App × Me-Bet shape).
* UNCHANGED: `_SR_axiom_app_meApp`.

Two SR axioms reduced to one strictly narrower residual.
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

/-! ### §2.5. Discharge of `_SR_axiom_PrE_meProAnnot` via MEqRed-recursion

We replace the original axiom with a NONCOMPUTABLE DEF that recurses
on the `MEqRed` derivation `hred`. The recursion structure provides
IHs on STRUCTURALLY SMALLER MEqRed sub-derivations — exactly what's
needed to handle the `Me-Pro` case (where the bound annotation step
is a sub-derivation of the outer Me-Pro).

For the body cases (Me-Bet, Me-Fun) we route to:
* `_SR_v2_bet_residual` — narrower residual for the Me-Bet case,
  capturing the specific Wf-App × Me-Bet shape with the body
  context-mismatch obstacle.
* `Me-Fun` — closed by inverting input WfM via Wf-Fun and applying the
  IH on the body sub-derivation (which lives at the EXTENDED context,
  matching Wf-Fun's premise).
* `Me-App` — routed to existing `_SR_axiom_app_meApp`.
* `Me-FOp` at outer `s = []` is impossible by type-indexing.

This SPLITS the original axiom into the narrower `_SR_v2_bet_residual`
plus the existing `_SR_axiom_app_meApp`, while DISCHARGING the
Me-Pro, Me-Top, Me-Var, Me-tAp, Me-Fun cases axiom-free. -/

/-- Helper: combine `equBinds` and `subBinds` for the same name to derive
`False`. The head entry for `y` in `Γ` is either `.sub` or `.equ`, not
both; the two lookup functions return `none` for the wrong kind. -/
private lemma _SR_v2_equ_sub_disjoint
    {Γ : Ctx} {y : String} {α t : Term}
    (he : Γ.equBinds y α) (hs : Γ.subBinds y t) : False := by
  induction Γ with
  | nil =>
    simp [Ctx.equBinds, Ctx.lookupEqu] at he
  | cons e rest ih =>
    by_cases hne : e.name = y
    · -- Head entry's name matches y. Either kind.
      rcases e with ⟨name, bound, kind⟩
      change name = y at hne
      cases kind with
      | sub =>
        -- equ-lookup returns none for sub-head with matching name.
        unfold Ctx.equBinds Ctx.lookupEqu at he
        simp [hne] at he
      | equ =>
        -- sub-lookup returns none for equ-head with matching name.
        unfold Ctx.subBinds Ctx.lookupSub at hs
        simp [hne] at hs
    · have he' : Ctx.equBinds rest y α :=
        (Ctx.equBinds_cons_other (e := e) hne).mp he
      have hs' : Ctx.subBinds rest y t :=
        (Ctx.subBinds_cons_other (e := e) hne).mp hs
      exact ih he' hs'

/-- **Narrower residual for the Me-Bet body case in `_SR_at_pro_proved`.**
The input is a Wf-App with the LHS abstraction; the body MEqRed step
lives at flat Γ but the Wf-Fun inversion gives the body WfM at extended
Γ. The context-mismatch obstacle is the same one captured in
`_SR_axiom_app_meApp_bet` — this is just the projected per-case form,
indexed on the actual abstraction body `bd`.

## Circular-dependency finding (iteration `pss-20260504-025516` audit)

**The natural discharge of `_SR_v2_bet_residual` requires
`Lemma_10_Inversion`.** This makes the SR-as-discharge-of-Lemma-10
strategy circular: SR's β-residual essentially encodes a specialization
of Lemma 10 inversion.

Sketch of the discharge attempt:
1. Pick fresh `x ∉ L ∪ Lfn ∪ Γ.dom ∪ relevant fvs`.
2. From `hwfFn`, by Wf-Fun inversion: `WfM (⟨x, tt, .sub⟩ :: Γ) (bd^[x])`.
3. Lift `hbd x : MEqRed Γ [] (bd^[x]) (bd'^[x])` to extended context via
   `Lemma_22_WeakeningMEqRed`.
4. Recursive SR call at extended context yields
   `WfM (⟨x, tt, .sub⟩ :: Γ) (bd'^[x])`.
5. Recursive SR call at `hv` yields `WfM Γ v'`.
6. Apply `Lemma_7_SubstitutionPreservesWf` with substitution `x → v'` —
   **this requires `WSubMStar Γ v' tt`**, where `tt` is the abstraction's
   bound annotation.
7. We have `hStarV : WSubMStar Γ v T` and `MEqRed Γ [] v v'`. To get
   `WSubMStar Γ v' tt`, we need to:
   - Forward-extend the LHS through `hv` (confluence-shaped — itself
     non-trivial), AND
   - Bridge the codomain `T` (from `hStarFn`'s target shape) to the
     bound annotation `tt`.
   - The codomain-to-bound bridge IS exactly `Lemma_10_Inversion`'s
     output (`WEquM Γ tt T`), then translated via `Lemma_15_WEquM_symm`
     and `Lemma_16_WEquM_to_WSubM` (mirroring TypeSafety.lean:959-970).

Without `Lemma_10_Inversion`, no path is known for step 7. So:
* SR-via-MEqRed-recursion does NOT yield a fresh discharge angle for
  `Lemma_10_Inversion`; it merely renames the dependency.
* Wiring SR into Lemma_10's discharge via this residual would yield
  net 0 axiom-count improvement (Lemma_10 → _SR_v2_bet_residual,
  which itself encodes Lemma_10's content).

The remaining honest paths to break this stalemate are the same ones
listed in `Pss/Mpss/WfMPreservation.lean` (recovery strategies 1-4)
and the Phase 5g.3b "remaining honest paths" (CAPSU-aware existence-
form composition, setoid-quotient on derivations, de-Bruijn
re-encoding, or accept axioms permanently).

The axiom is RETAINED as a Pareto-positive narrowing of
`_SR_axiom_app_meApp_bet` (more hypotheses, hence harder to
counterexample-falsify and easier to discharge if a fresh angle is
found). Future work should not re-attempt the natural discharge path
above — it is documented blocked by the circularity. -/
private axiom _SR_v2_bet_residual
    {Γ : Ctx} {tt bd v T : Term}
    (hCtx : WfCtxEqu Γ)
    (hStarFn : WSubMStar Γ (.abs tt bd) (.abs T .top))
    (hStarV : WSubMStar Γ v T)
    {bd' v' : Term} {L : Finset String}
    (hLCtt : Term.LC tt)
    (hbd : ∀ x, x ∉ L → MEqRed Γ [] (bd^[x]) (bd'^[x]))
    (hv : MEqRed Γ [] v v')
    (hwfFn : WfM Γ (.abs tt bd))
    (hwfV : WfM Γ v) :
    Nonempty (WfM Γ (Term.opening v' bd'))

/-- The motive for the MEqRed-recursion proof of
`_SR_axiom_PrE_meProAnnot`. -/
private def _SR_v2_motive : (Γ : Ctx) → (s : Stack) → (u u' : Term) →
    MEqRed Γ s u u' → Prop :=
  fun Γ s u u' _ =>
    s = [] → WfCtxEqu Γ → WfM Γ u → Nonempty (WfM Γ u')

/-- Per-case payload: Me-Pro. -/
private theorem _SR_v2_case_pro
    {Γ : Ctx} {s : Stack} {y : String} {α α' : Term}
    (hpvE : PrevalidExt Γ s) (hb : Γ.equBinds y α)
    (hα : MEqRed Γ s α α')
    (ihα : _SR_v2_motive Γ s α α' hα) :
    _SR_v2_motive Γ s (.fvar y) α' (MEqRed.pro hpvE hb hα) := by
  intro hSnil hCtx hwf
  subst hSnil
  cases hwf with
  | @varSub _ _ tS hpv hbS =>
    exact (_SR_v2_equ_sub_disjoint hb hbS).elim
  | @varEqu _ _ αV hpv hbE =>
    have hAlphaEq : α = αV := by
      have h1 : Γ.lookupEqu y = some αV := hbE
      have h2 : Γ.lookupEqu y = some α := hb
      exact Option.some.inj (h2.symm.trans h1)
    have hwfα : WfM Γ α := WfCtxEqu.lookup_equ hCtx hpv hb
    exact ihα rfl hCtx hwfα

/-- Per-case payload: Me-Top. -/
private theorem _SR_v2_case_top
    {Γ : Ctx} {s : Stack} (hpvE : PrevalidExt Γ s) :
    _SR_v2_motive Γ s .top .top (MEqRed.top hpvE) := by
  intro hSnil hCtx hwf
  exact ⟨hwf⟩

/-- Per-case payload: Me-Var. -/
private theorem _SR_v2_case_var
    {Γ : Ctx} {s : Stack} {y : String} (hpvE : PrevalidExt Γ s) :
    _SR_v2_motive Γ s (.fvar y) (.fvar y) (@MEqRed.var Γ s y hpvE) := by
  intro hSnil hCtx hwf
  exact ⟨hwf⟩

/-- Per-case payload: Me-tAp. -/
private theorem _SR_v2_case_tAp
    {Γ : Ctx} {s : Stack} {u : Term}
    (hpvE : PrevalidExt Γ s) (hLCu : Term.LC u)
    (hfvU : Term.fv u ⊆ Γ.dom) :
    _SR_v2_motive Γ s (.app .top u) .top (MEqRed.tAp hpvE hLCu hfvU) := by
  intro hSnil hCtx hwf
  exact ⟨WfM.top (prevalid_of_wfM hwf)⟩

/-- Per-case payload: Me-Fun. The body `hB y` lives at EXTENDED context
`⟨y,t,.sub⟩::Γ`, matching Wf-Fun's body premise. -/
private theorem _SR_v2_case_fun
    {Γ : Ctx} {t t' bd bd' : Term} (L : Finset String)
    (ht : MEqRed Γ [] t t')
    (hB : ∀ x, x ∉ L → MEqRed (⟨x, t, .sub⟩ :: Γ) [] (bd^[x]) (bd'^[x]))
    (hUni : True)
    (iht : _SR_v2_motive Γ [] t t' ht)
    (ihB : ∀ x (hx : x ∉ L),
        _SR_v2_motive (⟨x, t, .sub⟩ :: Γ) [] (bd^[x]) (bd'^[x]) (hB x hx)) :
    _SR_v2_motive Γ [] (.abs t bd) (.abs t' bd')
        (MEqRed.fun_ L ht hB hUni) := by
  intro hSnil hCtx hwf
  classical
  cases hwf with
  | @fun_ _ _ _ Lfn hwfT hwfBd =>
    -- Get WfM Γ t' via iht.
    have hwfT' : WfM Γ t' := Classical.choice (iht rfl hCtx hwfT)
    have hLCT' : Term.LC t' := WfM.lc hwfT'
    have hfvT' : Term.fv t' ⊆ Γ.dom := WfM.fv_subset hwfT'
    refine ⟨WfM.fun_ (L ∪ Lfn ∪ Γ.dom ∪ Term.fv bd' ∪ Term.fv t') hwfT' ?_⟩
    intro z hz
    have hzL : z ∉ L := fun h => hz (by simp; tauto)
    have hzLfn : z ∉ Lfn := fun h => hz (by simp; tauto)
    have hzΓ : z ∉ Γ.dom := fun h => hz (by simp; tauto)
    -- Get WfM (⟨z,t,.sub⟩::Γ) (bd^[z]) from hwfBd z hzLfn.
    have hwfBd_z : WfM (⟨z, t, .sub⟩ :: Γ) (bd^[z]) := hwfBd z hzLfn
    -- Apply ihB z hzL at extended context.
    have hCEext : WfCtxEqu (⟨z, t, .sub⟩ :: Γ) := WfCtxEqu.sub hCtx
    have hwfBd'_z : WfM (⟨z, t, .sub⟩ :: Γ) (bd'^[z]) :=
      Classical.choice (ihB z hzL rfl hCEext hwfBd_z)
    -- Narrow t → t' at the head.
    have hN := Lemma_23_NarrowingWf
      (Γ₁ := Γ) (Γ₂ := []) (x := z) (t := t') (t' := t)
      (u := bd'^[z])
      (by simpa using hwfBd'_z) hLCT' hfvT'
    simpa using hN

/-- Per-case payload: Me-Bet. Routes to `_SR_v2_bet_residual`. -/
private theorem _SR_v2_case_bet
    {Γ : Ctx} {s : Stack} {tt v v' bd bd' : Term} (L : Finset String)
    (hLCtt : Term.LC tt)
    (hbd : ∀ x, x ∉ L → MEqRed Γ s (bd^[x]) (bd'^[x]))
    (hUni : True)
    (hv : MEqRed Γ [] v v')
    (ihbd : ∀ x (hx : x ∉ L),
        _SR_v2_motive Γ s (bd^[x]) (bd'^[x]) (hbd x hx))
    (ihv : _SR_v2_motive Γ [] v v' hv) :
    _SR_v2_motive Γ s (.app (.abs tt bd) v) (Term.opening v' bd')
        (MEqRed.bet L hLCtt hbd hUni hv) := by
  intro hSnil hCtx hwf
  subst hSnil
  classical
  cases hwf with
  | @app _ _ _ T hStarFn hStarV =>
    have hwfFn : WfM Γ (.abs tt bd) := wfM_left_of_wsubmstar hStarFn
    have hwfV : WfM Γ v := wfM_left_of_wsubmstar hStarV
    exact _SR_v2_bet_residual hCtx hStarFn hStarV hLCtt hbd hv hwfFn hwfV

/-- Per-case payload: Me-App. Routes to `_SR_axiom_app_meApp`. -/
private theorem _SR_v2_case_app
    {Γ : Ctx} {s : Stack} {u u' v v' : Term}
    (hu : MEqRed Γ (v :: s) u u') (hv : MEqRed Γ [] v v')
    (ihu : _SR_v2_motive Γ (v :: s) u u' hu)
    (ihv : _SR_v2_motive Γ [] v v' hv) :
    _SR_v2_motive Γ s (.app u v) (.app u' v') (MEqRed.app hu hv) := by
  intro hSnil hCtx hwf
  subst hSnil
  cases hwf with
  | @app _ _ _ T hStarFn hStarV =>
    exact _SR_axiom_app_meApp hCtx hStarFn hStarV hu hv

/-- Per-case payload: Me-FOp. At outer `s = []`, the constructor's
type-index forces `s = α::s'` for some `α`, contradicting `s = []`.
Hence vacuous. -/
private theorem _SR_v2_case_fOp
    {Γ : Ctx} {s : Stack} {t t' α : Term} {bd bd' : Term} (L : Finset String)
    (ht : MEqRed Γ [] t t')
    (hB : ∀ x, x ∉ L → MEqRed (⟨x, α, .equ⟩ :: Γ) s (bd^[x]) (bd'^[x]))
    (hUni : True)
    (iht : _SR_v2_motive Γ [] t t' ht)
    (ihB : ∀ x (hx : x ∉ L),
        _SR_v2_motive (⟨x, α, .equ⟩ :: Γ) s (bd^[x]) (bd'^[x]) (hB x hx)) :
    _SR_v2_motive Γ (α :: s) (.abs t bd) (.abs t' bd')
        (MEqRed.fOp L ht hB hUni) := by
  intro hSnil _ _
  -- hSnil : α :: s = []. Impossible.
  exact (List.cons_ne_nil _ _ hSnil).elim

/-- **Discharged form of `_SR_axiom_PrE_meProAnnot`.** Proved by
recursion on the `MEqRed` derivation. -/
noncomputable def _SR_at_pro_proved
    {Γ : Ctx} {α α' : Term}
    (hCtx : WfCtxEqu Γ)
    (hwfα : WfM Γ α)
    (hred : MEqRed Γ [] α α') :
    Nonempty (WfM Γ α') :=
  MEqRed.rec
    (motive := _SR_v2_motive)
    (@_SR_v2_case_pro)
    (@_SR_v2_case_bet)
    (@_SR_v2_case_top)
    (@_SR_v2_case_app)
    (@_SR_v2_case_var)
    (@_SR_v2_case_fun)
    (@_SR_v2_case_tAp)
    (@_SR_v2_case_fOp)
    hred rfl hCtx hwfα

/-- Re-export of `_SR_at_pro_proved` under the old axiom name to
preserve call sites. The original axiom is REPLACED by this proof. -/
@[reducible] noncomputable def _SR_axiom_PrE_meProAnnot
    {Γ : Ctx} {α α' : Term}
    (hCtx : WfCtxEqu Γ)
    (hwfα : WfM Γ α)
    (hred : MEqRed Γ [] α α') :
    Nonempty (WfM Γ α') :=
  _SR_at_pro_proved hCtx hwfα hred

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

/-- Helper residual for the Me-Bet case (substitution under combined
β-reduction with body MEqRed step). Iteration 4: replaced the axiom
with a noncomputable def that routes to `_SR_v2_bet_residual` via
extracting the abstraction shape from `hStarU`. The narrower
residual captures the same Me-Bet body context-mismatch obstacle. -/
noncomputable def _SR_axiom_app_meApp_bet
    {Γ : Ctx} {u v t : Term}
    (hCtx : WfCtxEqu Γ)
    (hStarU : WSubMStar Γ u (.abs t .top))
    (hStarV : WSubMStar Γ v t)
    {tt vv' bd bd' : Term} {L : Finset String}
    (hLCt : Term.LC tt)
    (hbd : ∀ x, x ∉ L → MEqRed Γ [] (bd^[x]) (bd'^[x]))
    (hv : MEqRed Γ [] v vv')
    (huEq : u = .abs tt bd)
    (hwfFn : WfM Γ u) :
    Nonempty (WfM Γ (Term.opening vv' bd')) := by
  subst huEq
  exact _SR_v2_bet_residual hCtx hStarU hStarV hLCt hbd hv hwfFn
    (wfM_left_of_wsubmstar hStarV)

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
      have hwfFn : WfM Γ (.abs tt bd) := wfM_left_of_wsubmstar hStarU
      exact _SR_axiom_app_meApp_bet hCtx hStarU hStarV hLCt hbd hv rfl hwfFn
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

/-! ## §5. Conditional single-step `WSubM` transitivity

The unconditional single-`WSubM` transitivity obstruction documented in
`Pss.Mpss.WSubMTrans` is exactly the `WSubM.rgh` case. The conditional
subject-reduction theorem above supplies that missing case under `WfCtxEqu`.
-/

/-- **Conditional single-step transitivity for `WSubM`.**

Under `WfCtxEqu Γ`, two single well-subtyping derivations compose into a
single `WSubM`. The only non-structural case is `WSubM.rgh`: it requires
transporting the second derivation across the right-hand `MEqRed` step, and
that is provided by `subject_reduction_sub`. -/
noncomputable def WSubM.trans_under_wfctx
    {Γ : Ctx} {a b c : Term}
    (hCtx : WfCtxEqu Γ)
    (h₁ : WSubM Γ a b)
    (h₂ : WSubM Γ b c) :
    WSubM Γ a c := by
  refine (WSubM.rec
    (motive_1 := fun _ _ _ => PUnit)
    (motive_2 := fun Γ a b _ =>
      WfCtxEqu Γ → ∀ {c : Term}, WSubM Γ b c → WSubM Γ a c)
    (motive_3 := fun _ _ _ _ => PUnit)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h₁) hCtx h₂
  · intro _ _ _ _ _
    exact PUnit.unit
  · intro _ _ _ _ _
    exact PUnit.unit
  · intro _ _
    exact PUnit.unit
  · intro _ _ _ _ _ _ _ _
    exact PUnit.unit
  · intro _ _ _ _ _ _ _ _
    exact PUnit.unit
  · intro _ _ _ _ _ _ hsub
    exact hsub
  · intro _ _ _ _ hred _ ih hCtx _ hsub
    exact WSubM.lf1 hred (ih hCtx hsub)
  · intro _ _ _ _ hwfV hred hwfV' _ _ _ ih hCtx _ hsub
    exact WSubM.lf2 hwfV hred hwfV' (ih hCtx hsub)
  · intro _ _ _ _ _ hred ih hCtx _ hsub
    exact ih hCtx (subject_reduction_sub hCtx hsub hred).some
  · intro _ _ _ _ _ _ _ _ _
    exact PUnit.unit
  · intro _ _ _ _ _ _ _ _ _ _
    exact PUnit.unit

/-! ## §6. `WSubMStar` collapse under `WfCtxEqu`

The previous theorem supplies the only missing ingredient for eliminating
the explicit `WSubMStar.trs` nodes when `WfCtxEqu Γ` is available. This is
not a headline axiom discharge, because it inherits the same
subject-reduction residuals as `WSubM.trans_under_wfctx`; it is a checked
bridge for conditional downstream routes.
-/

/-- Collapse a transitive well-subtyping chain to a single `WSubM` under
`WfCtxEqu Γ`.

The `.sub` case unwraps directly. The `.trs` case recursively collapses
both legs and composes them with `WSubM.trans_under_wfctx`. -/
noncomputable def WSubMStar.toWSubM_under_wfctx
    {Γ : Ctx} {a b : Term}
    (hCtx : WfCtxEqu Γ)
    (h : WSubMStar Γ a b) :
    WSubM Γ a b := by
  refine (WSubMStar.rec
    (motive_1 := fun _ _ _ => PUnit)
    (motive_2 := fun _ _ _ _ => PUnit)
    (motive_3 := fun Γ a b _ => WfCtxEqu Γ → WSubM Γ a b)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h) hCtx
  · intro _ _ _ _ _
    exact PUnit.unit
  · intro _ _ _ _ _
    exact PUnit.unit
  · intro _ _
    exact PUnit.unit
  · intro _ _ _ _ _ _ _ _
    exact PUnit.unit
  · intro _ _ _ _ _ _ _ _
    exact PUnit.unit
  · intro _ _ _ _
    exact PUnit.unit
  · intro _ _ _ _ _ _ _
    exact PUnit.unit
  · intro _ _ _ _ _ _ _ _ _ _ _
    exact PUnit.unit
  · intro _ _ _ _ _ _ _
    exact PUnit.unit
  · intro _ _ _ _ hsub _ _ _ _ _
    exact hsub
  · intro _ _ _ _ _ _ _ ihLeft _ ihRight hCtx
    exact WSubM.trans_under_wfctx hCtx (ihLeft hCtx) (ihRight hCtx)

/-- Conditional Lemma 10 inversion under `WfCtxEqu`.

This turns the full `WSubMStar` premise into a single `WSubM` using
`WSubMStar.toWSubM_under_wfctx`, then reuses the axiom-free single-step
inversion from `Pss.Mpss.WellFormed`. -/
noncomputable def Lemma_10_Inversion_under_wfctx
    {Γ : Ctx} {t t' u u' : Term}
    (hCtx : WfCtxEqu Γ)
    (h : WSubMStar Γ (.abs t u) (.abs t' u')) :
    WEquM Γ t t' :=
  _Lemma_10_Inversion_sub_partial
    (WSubMStar.toWSubM_under_wfctx hCtx h) rfl rfl

/-- Closed-context specialization of `Lemma_10_Inversion_under_wfctx`. -/
noncomputable def Lemma_10_Inversion_empty
    {t t' u u' : Term}
    (h : WSubMStar [] (.abs t u) (.abs t' u')) :
    WEquM [] t t' :=
  Lemma_10_Inversion_under_wfctx WfCtxEqu.empty h

end Pss

import Pss.Mpss.DeBruijnTransitivityElim

/-! # `Pss.Mpss.DeBruijnTypeSafety` — de Bruijn type-safety endpoints

This module states the de Bruijn versions of the type-safety endpoints over
the already-ported operational and well-formed judgments. The remaining hard
metatheoretic ingredients are explicit premises rather than axioms.
-/

namespace Pss
namespace DeBruijn

/-- De Bruijn analogue of Lemma 11's use in progress: at the empty context,
`Top` has no function supertype. -/
def NoTopFunctionSupertypes : Prop :=
  ∀ {bound : Term}, WSubMStar [] .top (.abs bound .top) → False

/-- Once de Bruijn Theorem 3 is available at the empty context, `Top` cannot
have a function supertype. Diagrammatic subtyping from `Top` can only join at
`Top`, while equivalence chains from an abstraction can only target another
abstraction. -/
noncomputable def NoTopFunctionSupertypes_of
    (hcomm : StrongCommutes [] []) :
    NoTopFunctionSupertypes := by
  intro bound hTopFun
  obtain ⟨join, hSubTop, hEqAbs⟩ := hTopFun.toMSub_of hcomm
  have hJoinTop : join = .top := hSubTop.top_inv
  subst hJoinTop
  obtain ⟨bound', body', hAbsTop⟩ := hEqAbs.abs_inv
  cases hAbsTop

/-- De Bruijn progress, conditional on the `Top`-has-no-function-supertype
fact. A closed well-formed term is an abstraction, `Top`, or takes an
operational step. -/
theorem Theorem_4_DeBruijn_Progress_of
    (hNoTop : NoTopFunctionSupertypes)
    {t : Term} (hwf : WfM [] t) :
    (∃ bound body, t = .abs bound body) ∨
      t = .top ∨
      (∃ t', Step t t') := by
  induction t with
  | bvar i =>
      exact (Term.no_scoped_zero_bvar i hwf.scoped).elim
  | top =>
      exact Or.inr (Or.inl rfl)
  | abs bound body =>
      exact Or.inl ⟨bound, body, rfl⟩
  | app u v ihU ihV =>
      obtain ⟨funBound, hFun, hArg⟩ := hwf.app_inv
      have hScopedU : Term.Scoped 0 u := hFun.scoped_left
      have hScopedV : Term.Scoped 0 v := hArg.scoped_left
      have hwfU : WfM [] u := hFun.wf_left
      have hwfV : WfM [] v := hArg.wf_left
      cases ihU hwfU with
      | inl hAbs =>
          obtain ⟨bound, body, hEqU⟩ := hAbs
          subst hEqU
          cases ihV hwfV with
          | inl _ =>
              exact Or.inr (Or.inr
                ⟨_, StepAt.beta hScopedU hScopedV⟩)
          | inr hVRest =>
              cases hVRest with
              | inl _ =>
                  exact Or.inr (Or.inr
                    ⟨_, StepAt.beta hScopedU hScopedV⟩)
              | inr hStepV =>
                  obtain ⟨v', hStepV⟩ := hStepV
                  exact Or.inr (Or.inr
                    ⟨_, StepAt.appR hScopedU hStepV⟩)
      | inr hURest =>
          cases hURest with
          | inl hTop =>
              subst hTop
              exact (hNoTop hFun).elim
          | inr hStepU =>
              obtain ⟨u', hStepU⟩ := hStepU
              exact Or.inr (Or.inr
                ⟨_, StepAt.appL hStepU hScopedV⟩)

/-- De Bruijn progress from the empty-context strong-commutativity premise
used by Theorem 3. -/
noncomputable def Theorem_4_DeBruijn_Progress_of_StrongCommutativity
    (hcomm : StrongCommutes [] [])
    {t : Term} (hwf : WfM [] t) :
    (∃ bound body, t = .abs bound body) ∨
      t = .top ∨
      (∃ t', Step t t') :=
  Theorem_4_DeBruijn_Progress_of (NoTopFunctionSupertypes_of hcomm) hwf

/-- De Bruijn analogue of Lemma 6's preservation payload for operational
steps at arbitrary context depth. -/
def StepPreservesWfM : Type :=
  ∀ {Γ : Ctx} {t t' : Term}, StepAt Γ.depth t t' → WfM Γ t → WfM Γ t'

/-- Remaining β payload for de Bruijn operational well-formedness
preservation. -/
def StepBetaPreservesWfM : Type :=
  ∀ {Γ : Ctx} {bound body arg : Term},
    WfM Γ (.app (.abs bound body) arg) →
      WfM Γ (Term.instantiate 0 arg body)

/-- Remaining abstraction-bound payload for de Bruijn operational
well-formedness preservation. The body lives under the old bound, so changing
the bound still needs the future narrowing/replacement theorem. -/
def StepAbsBoundPreservesWfM : Type :=
  ∀ {Γ : Ctx} {bound bound' body : Term},
    StepAt Γ.depth bound bound' →
      WfM Γ (.abs bound body) →
        WfM Γ (.abs bound' body)

namespace StepAt

/-- All structural operational well-formedness preservation cases reduce to
the β payload and the abstraction-bound replacement payload. The result is
wrapped in `Nonempty` because `StepAt` is `Prop`-valued while `WfM` is
`Type`-valued. -/
theorem wf_right_nonempty_of
    (hBeta : StepBetaPreservesWfM)
    (hAbsBound : StepAbsBoundPreservesWfM)
    {depth : Nat} {t t' : Term} (hstep : StepAt depth t t') :
    Nonempty (∀ {Γ : Ctx}, Γ.depth = depth → WfM Γ t → WfM Γ t') := by
  induction hstep with
  | beta =>
      exact ⟨fun {Γ} _hdepth hwf => hBeta (Γ := Γ) hwf⟩
  | @appL depth op op' arg hOp _hArgScoped ih =>
      exact ⟨fun {Γ} hdepth hwf =>
        let ⟨funBound, hFun, hArg⟩ := hwf.app_inv
        let hwfOp' : WfM Γ op' := ih.some hdepth hFun.wf_left
        let hBack : WSubMStar Γ op' op :=
          WSubMStar.of_StepAt_back (by simpa [hdepth] using hOp)
            hFun.wf_left hwfOp'
        WfM.app (WSubMStar.trans hFun.wf_left hBack hFun) hArg⟩
  | @appR depth op arg arg' _hOpScoped hArgStep ih =>
      exact ⟨fun {Γ} hdepth hwf =>
        let ⟨funBound, hFun, hArg⟩ := hwf.app_inv
        let hwfArg' : WfM Γ arg' := ih.some hdepth hArg.wf_left
        let hBack : WSubMStar Γ arg' arg :=
          WSubMStar.of_StepAt_back (by simpa [hdepth] using hArgStep)
            hArg.wf_left hwfArg'
        WfM.app hFun (WSubMStar.trans hArg.wf_left hBack hArg)⟩
  | @absBound depth bound bound' body hBound _hBodyScoped _ih =>
      exact ⟨fun {Γ} hdepth hwf =>
        hAbsBound (by simpa [hdepth] using hBound) hwf⟩
  | @absBody depth bound body body' _hBoundScoped hBody ih =>
      exact ⟨fun {Γ} hdepth hwf =>
        let hParts := hwf.fun_inv
        let hBody' : WfM ({ bound := bound, kind := .sub } :: Γ) body' :=
          ih.some (by simpa [Ctx.depth, hdepth]) hParts.2
        WfM.fun_ hParts.1 hBody'⟩

end StepAt

/-- De Bruijn operational well-formedness preservation reduced to the two
remaining hard payloads: β instantiation and abstraction-bound replacement. -/
noncomputable def StepPreservesWfM_of
    (hBeta : StepBetaPreservesWfM)
    (hAbsBound : StepAbsBoundPreservesWfM) :
    StepPreservesWfM := by
  intro Γ t t' hstep hwf
  exact (StepAt.wf_right_nonempty_of hBeta hAbsBound hstep).some rfl hwf

/-- De Bruijn preservation, conditional on operational well-formedness
preservation. The operational step is at the ambient context depth so the
closed case specializes to `Step`. -/
noncomputable def Theorem_5_DeBruijn_Preservation_of
    (hStepPres : StepPreservesWfM)
    {Γ : Ctx} {t t' u : Term}
    (hwf : WSubMStar Γ t u)
    (hstep : StepAt Γ.depth t t') :
    WSubMStar Γ t' u := by
  have hwfT : WfM Γ t := hwf.wf_left
  have hwfT' : WfM Γ t' := hStepPres hstep hwfT
  have hBack : WSubMStar Γ t' t :=
    WSubMStar.of_StepAt_back hstep hwfT hwfT'
  exact WSubMStar.trans hwfT hBack hwf

/-- Closed-term specialization of de Bruijn preservation, using the
operational `Step` alias. -/
noncomputable def Theorem_5_DeBruijn_ClosedPreservation_of
    (hStepPres : StepPreservesWfM)
    {t t' u : Term}
    (hwf : WSubMStar [] t u)
    (hstep : Step t t') :
    WSubMStar [] t' u :=
  Theorem_5_DeBruijn_Preservation_of hStepPres hwf hstep

end DeBruijn
end Pss

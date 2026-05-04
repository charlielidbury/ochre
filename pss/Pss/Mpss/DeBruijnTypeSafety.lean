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

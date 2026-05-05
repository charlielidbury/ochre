import Pss.Mpss.TypeSafety
import Pss.Mpss.SubjectReduction

set_option linter.unusedVariables false

/-! # `Pss.Mpss.TypeSafetyWfCtx`

Conditional type-safety endpoints under the `WfCtxEqu` context invariant.
These live downstream of both `TypeSafety` and `SubjectReduction`, so they
can use the subject-reduction-backed `Lemma_10_Inversion_under_wfctx`
without introducing an import cycle in the original generic theorem.
-/

namespace Pss

/-- `WfCtxEqu`-parametric Lemma 6.

This is the same operational preservation proof as
`Lemma_6_EvaluationPreservesWf`, except the beta case uses
`Lemma_10_Inversion_under_wfctx` instead of the raw `Lemma_10_Inversion`
axiom. The abstraction-body case threads the invariant through the fresh
`.sub` binder with `WfCtxEqu.sub`. -/
private theorem Lemma_6_EvaluationPreservesWf_under_wfctx_J
    {Γ : Ctx} {t t' : Term}
    (hCtx : WfCtxEqu Γ)
    (hwf : WfM Γ t)
    (hstep : Step t t') :
    Nonempty (WfM Γ t') := by
  classical
  induction hstep generalizing Γ with
  | @beta bound body arg hAbsLC hArgLC =>
    cases hwf with
    | @app _ _ _ z hStarFn hStarArg =>
      have hEquBz : WEquM Γ bound z :=
        Lemma_10_Inversion_under_wfctx hCtx hStarFn
      have hSubZBd : WSubM Γ z bound :=
        Lemma_16_WEquM_to_WSubM (Lemma_15_WEquM_symm hEquBz)
      have hwfZ : WfM Γ z := wfM_right_of_wsubmstar hStarArg
      have hwfFn : WfM Γ (.abs bound body) := wfM_left_of_wsubmstar hStarFn
      have hwfBd : WfM Γ bound := by
        cases hwfFn with
        | @fun_ _ _ _ _ hT _ => exact hT
      have hStarZBd : WSubMStar Γ z bound :=
        WSubMStar.sub hwfZ hSubZBd hwfBd
      have hStarArgBd : WSubMStar Γ arg bound :=
        WSubMStar.trs hStarArg hwfZ hStarZBd
      cases hwfFn with
      | @fun_ _ _ _ Lfn _ hB =>
        let x : String :=
          Classical.choose (Term.exists_fresh (Lfn ∪ Term.fv body))
        have hxF : x ∉ Lfn ∪ Term.fv body :=
          Classical.choose_spec (Term.exists_fresh (Lfn ∪ Term.fv body))
        have hxL : x ∉ Lfn := fun h => hxF (Finset.mem_union.mpr (Or.inl h))
        have hxFv : x ∉ Term.fv body :=
          fun h => hxF (Finset.mem_union.mpr (Or.inr h))
        have hwfBodyOpen : WfM (⟨x, bound, .sub⟩ :: Γ)
            (Term.opening (.fvar x) body) :=
          hB x hxL
        have hSubstEq : Term.subst x arg (Term.opening (.fvar x) body) =
            Term.opening arg body :=
          (Term.subst_intro hxFv hArgLC).symm
        have hwfSubst : WfM Γ
            (Term.subst x arg (Term.opening (.fvar x) body)) :=
          Lemma_7_SubstitutionPreservesWf hwfBodyOpen hStarArgBd
        rw [hSubstEq] at hwfSubst
        exact ⟨hwfSubst⟩
  | @appL u u' v hstep hLCv ihU =>
    cases hwf with
    | @app _ _ _ z hStarFn hStarArg =>
      have hwfU : WfM Γ u := wfM_left_of_wsubmstar hStarFn
      have hwfFnRHS : WfM Γ (.abs z .top) := wfM_right_of_wsubmstar hStarFn
      have hwfU' : WfM Γ u' := (ihU hCtx hwfU).some
      have hpvΓ : Prevalid Γ := prevalid_of_wfM hwfU
      have hpvNil : PrevalidExt Γ [] := PrevalidExt.nil hpvΓ
      have hLCu : Term.LC u := WfM.lc hwfU
      have hfvU : Term.fv u ⊆ Γ.dom := WfM.fv_subset hwfU
      obtain ⟨hMEq⟩ : Nonempty (MEqRed Γ [] u u') :=
        Proposition_17_FromOperationalToEqRed hpvNil hLCu hfvU hstep
      have hSubU' : WSubM Γ u' u' := WSubM.rfl hwfU'
      have hSubU'_u : WSubM Γ u' u := WSubM.rgh hSubU' hMEq
      have hStarU'_u : WSubMStar Γ u' u := WSubMStar.sub hwfU' hSubU'_u hwfU
      have hStarU'_FnRHS : WSubMStar Γ u' (.abs z .top) :=
        WSubMStar.trs hStarU'_u hwfU hStarFn
      exact ⟨WfM.app hStarU'_FnRHS hStarArg⟩
  | @appR u v v' hLCu hstep ihV =>
    cases hwf with
    | @app _ _ _ z hStarFn hStarArg =>
      have hwfV : WfM Γ v := wfM_left_of_wsubmstar hStarArg
      have hwfZ : WfM Γ z := wfM_right_of_wsubmstar hStarArg
      have hwfV' : WfM Γ v' := (ihV hCtx hwfV).some
      have hpvΓ : Prevalid Γ := prevalid_of_wfM hwfV
      have hpvNil : PrevalidExt Γ [] := PrevalidExt.nil hpvΓ
      have hLCv : Term.LC v := WfM.lc hwfV
      have hfvV : Term.fv v ⊆ Γ.dom := WfM.fv_subset hwfV
      obtain ⟨hMEq⟩ : Nonempty (MEqRed Γ [] v v') :=
        Proposition_17_FromOperationalToEqRed hpvNil hLCv hfvV hstep
      have hSubV' : WSubM Γ v' v' := WSubM.rfl hwfV'
      have hSubV'_v : WSubM Γ v' v := WSubM.rgh hSubV' hMEq
      have hStarV'_v : WSubMStar Γ v' v := WSubMStar.sub hwfV' hSubV'_v hwfV
      have hStarV'_z : WSubMStar Γ v' z :=
        WSubMStar.trs hStarV'_v hwfV hStarArg
      exact ⟨WfM.app hStarFn hStarV'_z⟩
  | @absBound bound bound' body L hstep hbodyLC ihBound =>
    cases hwf with
    | @fun_ _ _ _ L₀ hT hB =>
      have hwfBd' : WfM Γ bound' := (ihBound hCtx hT).some
      have hLCBd' : Term.LC bound' := Step.lc_right hstep
      have hLCBd : Term.LC bound := WfM.lc hT
      have hfvBd : Term.fv bound ⊆ Γ.dom := WfM.fv_subset hT
      have hpvΓ : Prevalid Γ := prevalid_of_wfM hT
      have hpvNil : PrevalidExt Γ [] := PrevalidExt.nil hpvΓ
      obtain ⟨hMEqBd⟩ : Nonempty (MEqRed Γ [] bound bound') :=
        Proposition_17_FromOperationalToEqRed hpvNil hLCBd hfvBd hstep
      have hfvBd' : Term.fv bound' ⊆ Γ.dom := by
        intro y hy
        have hy' : y ∈ Term.fv bound ∪ Γ.dom := MEqRed_fv_subset hMEqBd hy
        rcases Finset.mem_union.mp hy' with h | h
        · exact hfvBd h
        · exact h
      refine ⟨WfM.fun_ (L₀ ∪ Γ.dom) hwfBd' ?_⟩
      intro y hy
      have hyL₀ : y ∉ L₀ := fun h =>
        hy (Finset.mem_union.mpr (Or.inl h))
      have hwfBody_old : WfM (⟨y, bound, .sub⟩ :: Γ)
          (Term.opening (.fvar y) body) :=
        hB y hyL₀
      have :=
        Lemma_23_NarrowingWf (Γ₁ := Γ) (Γ₂ := []) (x := y)
          (t := bound') (t' := bound) (u := Term.opening (.fvar y) body)
          (by simpa using hwfBody_old) hLCBd' hfvBd'
      simpa using this
  | @absBody bound body body' L hLCbound hbody ihBody =>
    cases hwf with
    | @fun_ _ _ _ L₀ hT hB =>
      refine ⟨WfM.fun_ (L ∪ L₀ ∪ Γ.dom) hT ?_⟩
      intro y hy
      have hyL : y ∉ L := fun h => hy (by
        apply Finset.mem_union.mpr; left
        apply Finset.mem_union.mpr; left; exact h)
      have hyL₀ : y ∉ L₀ := fun h => hy (by
        apply Finset.mem_union.mpr; left
        apply Finset.mem_union.mpr; right; exact h)
      have hwfBody_old : WfM (⟨y, bound, .sub⟩ :: Γ)
          (Term.opening (.fvar y) body) :=
        hB y hyL₀
      exact (ihBody y hyL (WfCtxEqu.sub hCtx) hwfBody_old).some

/-- `WfCtxEqu`-parametric evaluation preservation. -/
noncomputable def Lemma_6_EvaluationPreservesWf_under_wfctx
    {Γ : Ctx} {t t' : Term}
    (hCtx : WfCtxEqu Γ)
    (hwf : WfM Γ t)
    (hstep : Step t t') :
    WfM Γ t' :=
  (Lemma_6_EvaluationPreservesWf_under_wfctx_J hCtx hwf hstep).some

/-- Preservation under `WfCtxEqu`, using the conditional Lemma 6 route. -/
noncomputable def Theorem_5_Preservation_under_wfctx
    {Γ : Ctx} {t t' u : Term}
    (hCtx : WfCtxEqu Γ)
    (hwf : WSubMStar Γ t u)
    (hstep : Step t t') :
    WSubMStar Γ t' u := by
  have hwfT : WfM Γ t := wfM_left_of_wsubmstar hwf
  have hwfT' : WfM Γ t' :=
    Lemma_6_EvaluationPreservesWf_under_wfctx hCtx hwfT hstep
  have hpvΓ : Prevalid Γ := prevalid_of_wfM hwfT
  have hpvNil : PrevalidExt Γ [] := PrevalidExt.nil hpvΓ
  have hLCt : Term.LC t := WfM.lc hwfT
  have hfvT : Term.fv t ⊆ Γ.dom := WfM.fv_subset hwfT
  have hMEq : MEqRed Γ [] t t' :=
    (Proposition_17_FromOperationalToEqRed hpvNil hLCt hfvT hstep).some
  have hSubT' : WSubM Γ t' t' := WSubM.rfl hwfT'
  have hSubT'_t : WSubM Γ t' t := WSubM.rgh hSubT' hMEq
  have hStarT'_t : WSubMStar Γ t' t := WSubMStar.sub hwfT' hSubT'_t hwfT
  exact WSubMStar.trs hStarT'_t hwfT hwf

/-- Closed-context specialization of `Theorem_5_Preservation_under_wfctx`. -/
noncomputable def Theorem_5_Preservation_empty_wfctx
    {t t' u : Term}
    (hwf : WSubMStar [] t u)
    (hstep : Step t t') :
    WSubMStar [] t' u :=
  Theorem_5_Preservation_under_wfctx WfCtxEqu.empty hwf hstep

end Pss

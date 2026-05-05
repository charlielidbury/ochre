import Pss.Mpss.Substitution

set_option linter.unusedVariables false

/-! # `Pss.Mpss.SubstitutionNoPro`

A downstream, axiom-free variant of Lemma 30 under an explicit derivation
predicate excluding `Ms-Pro` on the substituted variable. Unlike the
Bool-valued `msAvoidsPro` sampler, `MSubRed.noProOn` quantifies over all
cofinite body branches, so the substitution proof can recurse through
`Ms-Fun` and `Ms-FOp` without an alpha-equivariance lemma.
-/

namespace Pss

private theorem fv_subst_dom_shift_noPro {Γ₁ Γ₂ : Ctx} {x : String}
    {s u : Term} {t : Term} {k : CtxEntryKind}
    (hok : SubstOk Γ₁ s)
    (hfv : Term.fv u ⊆ (Γ₂ ++ ⟨x, t, k⟩ :: Γ₁).dom) :
    Term.fv (Term.subst x s u) ⊆ (Ctx.subst x s Γ₂ ++ Γ₁).dom := by
  intro z hz
  have hsub := Term.fv_subst_subset x s u hz
  rw [Ctx.dom_append, Ctx.dom_subst]
  rcases Finset.mem_union.mp hsub with hsd | hsd
  · rcases Finset.mem_sdiff.mp hsd with ⟨hz_fv, hz_neq⟩
    have hz_in : z ∈ (Γ₂ ++ ⟨x, t, k⟩ :: Γ₁).dom := hfv hz_fv
    rw [Ctx.dom_append] at hz_in
    rw [Ctx.dom_cons] at hz_in
    rcases Finset.mem_union.mp hz_in with h | h
    · exact Finset.mem_union.mpr (Or.inl h)
    · rcases Finset.mem_insert.mp h with hzx | hzΓ
      · exact absurd hzx (fun hh => hz_neq (by simp [hh]))
      · exact Finset.mem_union.mpr (Or.inr hzΓ)
  · have hzΓ : z ∈ Γ₁.dom := hok.fv_sub hsd
    exact Finset.mem_union.mpr (Or.inr hzΓ)

/-- `h.noProOn x` means the `MSubRed` derivation `h` contains no `Ms-Pro`
constructor promoting variable `x`.

The cofinite constructors require this for every body branch, not just one
canonical sample. This is stronger than `msAvoidsPro`, but it exactly
matches what the structural Lemma 30 recursion needs. -/
def MSubRed.noProOn : {Γ : Ctx} → {st : Stack} → {u v : Term} →
    MSubRed Γ st u v → String → Prop
  | _, _, _, _, @MSubRed.pro _ _ y _ _ _, x => y ≠ x
  | _, _, _, _, @MSubRed.top _ _ _ _ _ _, _ => True
  | _, _, _, _, @MSubRed.equ _ _ _ _ _ _, _ => True
  | _, _, _, _, @MSubRed.app _ _ _ _ _ hu _ _, x => hu.noProOn x
  | _, _, _, _, @MSubRed.fun_ _ _ body body' L _ hbody _, x =>
      ∀ y (hy : y ∉ L), (hbody y hy).noProOn x
  | _, _, _, _, @MSubRed.fOp _ _ _ _ body body' L _ hbody _, x =>
      ∀ y (hy : y ∉ L), (hbody y hy).noProOn x

/-- **Lemma 30 under an explicit no-`Ms-Pro` predicate.**

This is the same conclusion as `Lemma_30_ReductionUnderSubst_Sub`, but it
does not use `Lemma_30_msPro_x_axiom`: the `Ms-Pro y = x` case is ruled out
by `h.noProOn x`, and the cofinite cases recurse using the all-branches
definition of `noProOn`. -/
noncomputable def Lemma_30_ReductionUnderSubst_Sub_noProOn
    {Γ₁ Γ₂ : Ctx} {st : Stack} {x : String} {s t u v : Term}
    (h : MSubRed (Γ₂ ++ ⟨x, t, .sub⟩ :: Γ₁) st u v)
    (hok : SubstOk Γ₁ s)
    (hNo : h.noProOn x) :
    MSubRed (Ctx.subst x s Γ₂ ++ Γ₁) (Stack.subst x s st)
      (Term.subst x s u) (Term.subst x s v) := by
  generalize hΓ : (Γ₂ ++ ⟨x, t, .sub⟩ :: Γ₁) = Γ at h
  induction h generalizing Γ₂ with
  | @pro Γ st' y t' hpv hsb =>
    subst hΓ
    have hpvL : Prevalid (Γ₂ ++ ⟨x, t, .sub⟩ :: Γ₁) := extractPrevalid hpv
    have hpv' : PrevalidExt (Ctx.subst x s Γ₂ ++ Γ₁) (Stack.subst x s st') :=
      Lemma_28_SubstPreservesPrevalid hpv hok
    by_cases hyx : y = x
    · exact (hNo hyx).elim
    · rw [Term.subst_fvar_ne hyx]
      have hsb' := subBinds_split_neq (s := s) hyx hpvL hsb
      exact MSubRed.pro hpv' hsb'
  | @top Γ st' u_ hpv hLCu hfv =>
    subst hΓ
    have hpv' : PrevalidExt (Ctx.subst x s Γ₂ ++ Γ₁) (Stack.subst x s st') :=
      Lemma_28_SubstPreservesPrevalid hpv hok
    have hLCu' : Term.LC (Term.subst x s u_) := Term.subst_lc hok.lc hLCu
    have hfv' := fv_subst_dom_shift_noPro hok hfv
    show MSubRed (Ctx.subst x s Γ₂ ++ Γ₁) (Stack.subst x s st')
      (Term.subst x s u_) (Term.subst x s .top)
    simp [Term.subst]
    exact MSubRed.top hpv' hLCu' hfv'
  | @equ Γ st' u_ v_ hpv heq =>
    subst hΓ
    have hpv' : PrevalidExt (Ctx.subst x s Γ₂ ++ Γ₁) (Stack.subst x s st') :=
      Lemma_28_SubstPreservesPrevalid hpv hok
    have heq' := Lemma_31_ReductionUnderSubst_Eq heq hok
    exact MSubRed.equ hpv' heq'
  | @app Γ st' u_ u_' v_ hu hLCv hfvv ihu =>
    subst hΓ
    have ihu' := ihu (Γ₂ := Γ₂) rfl hNo
    have hLCv' : Term.LC (Term.subst x s v_) := Term.subst_lc hok.lc hLCv
    have hfvv' := fv_subst_dom_shift_noPro hok hfvv
    show MSubRed (Ctx.subst x s Γ₂ ++ Γ₁) (Stack.subst x s st')
      (Term.subst x s (.app u_ v_)) (Term.subst x s (.app u_' v_))
    simp [Term.subst]
    refine MSubRed.app ?_ hLCv' hfvv'
    simpa using ihu'
  | @fun_ Γ t' body body' L hLCt hbody _hUni ihbody =>
    subst hΓ
    show MSubRed (Ctx.subst x s Γ₂ ++ Γ₁) (Stack.subst x s [])
      (Term.subst x s (.abs t' body)) (Term.subst x s (.abs t' body'))
    simp [Term.subst]
    refine MSubRed.fun_ (L ∪ {x}) (Term.subst_lc hok.lc hLCt) ?_ trivial
    intro y hy
    simp [Finset.mem_union, Finset.mem_singleton] at hy
    have hyL : y ∉ L := hy.1
    have hyx : y ≠ x := hy.2
    have ih_body := ihbody y hyL (Γ₂ := ⟨y, t', .sub⟩ :: Γ₂) (by simp)
      (hNo y hyL)
    rw [Term.subst_open_var (Ne.symm hyx) hok.lc body,
        Term.subst_open_var (Ne.symm hyx) hok.lc body'] at ih_body
    simpa [Ctx.subst, List.cons_append] using ih_body
  | @fOp Γ st' t' α body body' L hLCt hbody _hUni ihbody =>
    subst hΓ
    show MSubRed (Ctx.subst x s Γ₂ ++ Γ₁) (Stack.subst x s (α :: st'))
      (Term.subst x s (.abs t' body)) (Term.subst x s (.abs t' body'))
    rw [Stack.subst_cons]
    simp [Term.subst]
    refine MSubRed.fOp (L ∪ {x}) (Term.subst_lc hok.lc hLCt) ?_ trivial
    intro y hy
    simp [Finset.mem_union, Finset.mem_singleton] at hy
    have hyL : y ∉ L := hy.1
    have hyx : y ≠ x := hy.2
    have ih_body := ihbody y hyL (Γ₂ := ⟨y, α, .equ⟩ :: Γ₂) (by simp)
      (hNo y hyL)
    rw [Term.subst_open_var (Ne.symm hyx) hok.lc body,
        Term.subst_open_var (Ne.symm hyx) hok.lc body'] at ih_body
    simpa [Ctx.subst, List.cons_append] using ih_body

end Pss

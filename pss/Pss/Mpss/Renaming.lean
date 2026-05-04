import Pss.Mpss.Substitution
import Pss.Mpss.Weakening
import Pss.Mpss.AvoidsPro

/-! # `Pss.Mpss.Renaming` — fresh-variable renaming for MPSS reductions

When two cofinite-quantified body premises need to be combined (as in the
`fun_ × fun_` and `fOp × fOp` cases of Lemma 2 / the diamond property),
the result is naturally proved at one specific fresh `y`. We then need to
**rename** that body-level derivation to an arbitrary other fresh `z` so
the conclusion can be packaged back into a cofinite premise.

This module provides:

* `MEqRed.rename_sub` — rename `y → z` in
  `MEqRed (⟨y, t, .sub⟩::Γ) s (body^[y]) (body'^[y])`
  to obtain the same statement at `z`.
* `MEqRed.rename_equ` — same shape but for an `.equ` head binding.
* `MSubRed.rename_sub` / `MSubRed.rename_equ` — analogues for `MSubRed`.

## Strategy

Each renaming theorem is proved by direct induction on the derivation,
mirroring the structure of `Lemma_31_ReductionUnderSubst_Eq` /
`Lemma_32_ReductionUnderSubst_Eq_OfEqu` from `Pss.Mpss.Substitution`,
specialized to the case where the substituted term is `(.fvar z)` for
a fresh `z`.

For the `.sub`-head version we leverage Lemma 31 directly (after a
weakening step that brings `z` into scope, so `SubstOk` is satisfied).
For the `.equ`-head version we use Lemma 32's restricted form
(`s = v`) on a special instance (`y → y` for the kind change), but the
real renaming uses a custom proof inlined here.
-/

namespace Pss

/-! ## §1. Substitution-fresh helpers -/

/-- `Stack.subst` is the identity on a stack whose terms don't mention `x`. -/
theorem Stack.subst_fresh {x : String} {u : Term} {s : Stack}
    (h : ∀ α ∈ s, x ∉ Term.fv α) :
    Stack.subst x u s = s := by
  induction s with
  | nil => rfl
  | cons α tail ih =>
    have hα : x ∉ Term.fv α := h α (List.mem_cons_self α tail)
    have htail : ∀ β ∈ tail, x ∉ Term.fv β := fun β hβ =>
      h β (List.mem_cons_of_mem α hβ)
    rw [Stack.subst_cons, Term.subst_fresh hα, ih htail]

/-- `Ctx.subst` is the identity on a context whose entries don't mention `x`
in their bound terms. -/
theorem Ctx.subst_fresh {x : String} {u : Term} {Γ : Ctx}
    (h : ∀ e ∈ Γ, x ∉ Term.fv e.bound) :
    Ctx.subst x u Γ = Γ := by
  induction Γ with
  | nil => rfl
  | cons e rest ih =>
    have he : x ∉ Term.fv e.bound := h e (List.mem_cons_self e rest)
    have hrest : ∀ f ∈ rest, x ∉ Term.fv f.bound := fun f hf =>
      h f (List.mem_cons_of_mem e hf)
    rw [Ctx.subst_cons, Term.subst_fresh he, ih hrest]

/-- Helper: `fv u ⊆ Γ.dom` and `x ∉ Γ.dom` imply `x ∉ fv u`. -/
private lemma fv_notin_of_dom_notin {Γ : Ctx} {u : Term} {x : String}
    (hfv : Term.fv u ⊆ Γ.dom) (hx : x ∉ Γ.dom) : x ∉ Term.fv u :=
  fun h => hx (hfv h)

/-- Renaming via subst-then-open: when `y ∉ fv e`, opening with `z` is
the same as opening with `y` then substituting `y → z`. The mirror of
`Term.subst_intro`. -/
theorem Term.subst_open_fresh {y z : String} {e : Term}
    (hy : y ∉ Term.fv e) :
    Term.subst y (.fvar z) (e^[y]) = e^[z] :=
  (Term.subst_intro (x := y) (u := .fvar z) (e := e) hy
    (Term.LC.fvar z)).symm

/-! ## §2. Renaming for MEqRed under a `.sub` head binding

The previous implementation went through Lemma 22 (weakening) then
Lemma 31, which required the caller to supply `Term.fv body ⊆ Γ.dom`.
We replace it with a **direct renaming primitive** `subst_yz_sub_head`
that operates on the non-doubled context `Γ₂ ++ ⟨y, t, .sub⟩ :: Γ₁`,
substituting `y → fvar z` and producing the result in
`Γ₂.subst y (.fvar z) ++ ⟨z, t, .sub⟩ :: Γ₁`. No weakening step is
performed, so no `fv body` precondition is needed at the call site.

The proof mirrors `subst_yz_equ_head` (§3) but for `.sub` head:
- `Me-Pro yi` never fires on `y` (which has a `.sub` binding, not `.equ`),
  so the `.equ`-uniqueness arm doesn't appear; all `Me-Pro` cases are
  handled uniformly via `equBinds_split` (followed by a middle-insert
  to restore the renamed head binding).
- `Me-Var y` becomes `MEqRed.refl` for `z` (which is now in scope at
  the renamed head).
-/

/-- Helper: build prevalidity of the renamed context
`Γ₂.subst y (.fvar z) ++ ⟨z, t, .sub⟩ :: Γ₁`.

Constructs prevalidity of the doubled context first, then substitutes
`y → fvar z` (which is `SubstOk` because `z` is now in scope as the
new head). -/
private noncomputable def prevalid_rename_sub_head
    {Γ₂ Γ₁ : Ctx} {y z : String} {t : Term}
    (hyz : y ≠ z)
    (hz_notin_Γ₁ : z ∉ Γ₁.dom)
    (hz_notin_Γ₂ : z ∉ Γ₂.dom)
    (hpv : Prevalid (Γ₂ ++ ⟨y, t, .sub⟩ :: Γ₁)) :
    Prevalid (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, t, .sub⟩ :: Γ₁) := by
  classical
  -- Extract head data from hpv via Prevalid.outer.
  have hpv_inner : Prevalid (⟨y, t, .sub⟩ :: Γ₁) := Prevalid.outer hpv
  cases hpv_inner with
  | sub hpvΓ₁ hy_notin_Γ₁ hfvt hLCt =>
    -- Build Prevalid (⟨y,t,.sub⟩ :: ⟨z,t,.sub⟩ :: Γ₁).
    have hpv_zsub : Prevalid (⟨z, t, .sub⟩ :: Γ₁) :=
      Prevalid.sub hpvΓ₁ hz_notin_Γ₁ hfvt hLCt
    have hyz_zsub : y ∉ Ctx.dom (⟨z, t, .sub⟩ :: Γ₁) := by
      rw [Ctx.dom_cons]
      intro hmem
      rcases Finset.mem_insert.mp hmem with hyz' | hyΓ
      · exact hyz hyz'
      · exact hy_notin_Γ₁ hyΓ
    have hfvt_z : Term.fv t ⊆ Ctx.dom (⟨z, t, .sub⟩ :: Γ₁) := by
      intro w hw
      rw [Ctx.dom_cons]; exact Finset.mem_insert_of_mem (hfvt hw)
    have hpv_y_z : Prevalid (⟨y, t, .sub⟩ :: ⟨z, t, .sub⟩ :: Γ₁) :=
      Prevalid.sub hpv_zsub hyz_zsub hfvt_z hLCt
    -- Extend to Prevalid (Γ₂ ++ ⟨y,t,.sub⟩ :: ⟨z,t,.sub⟩ :: Γ₁) by induction on Γ₂.
    have hpv_doubled :
        Prevalid (Γ₂ ++ ⟨y, t, .sub⟩ :: ⟨z, t, .sub⟩ :: Γ₁) := by
      induction Γ₂ with
      | nil => simpa using hpv_y_z
      | cons e rest ih =>
        have hpv' : Prevalid (e :: (rest ++ ⟨y, t, .sub⟩ :: Γ₁)) := by simpa using hpv
        have hpv_rest : Prevalid (rest ++ ⟨y, t, .sub⟩ :: Γ₁) := hpv'.tail
        have hz_notin_rest : z ∉ Ctx.dom rest := by
          intro hmem
          apply hz_notin_Γ₂
          rw [Ctx.dom_cons]; exact Finset.mem_insert_of_mem hmem
        have ih' := ih hz_notin_rest hpv_rest
        have he_notin : e.name ∉ Ctx.dom (rest ++ ⟨y, t, .sub⟩ :: Γ₁) := by
          cases hpv' with
          | sub _ hen _ _ => exact hen
          | equ _ hen _ _ => exact hen
        have he_notin' : e.name ∉ Ctx.dom (rest ++ ⟨y, t, .sub⟩ :: ⟨z, t, .sub⟩ :: Γ₁) := by
          intro hmem
          rw [Ctx.dom_append, Ctx.dom_cons, Ctx.dom_cons] at hmem
          rw [Ctx.dom_append, Ctx.dom_cons] at he_notin
          rcases Finset.mem_union.mp hmem with hr | htail
          · apply he_notin; exact Finset.mem_union.mpr (Or.inl hr)
          · rcases Finset.mem_insert.mp htail with hey | hrest
            · apply he_notin
              exact Finset.mem_union.mpr (Or.inr (Finset.mem_insert.mpr (Or.inl hey)))
            · rcases Finset.mem_insert.mp hrest with hez | hΓ
              · -- e.name = z. But e ∈ Γ₂ has name in Γ₂.dom; z ∉ Γ₂.dom.
                apply hz_notin_Γ₂
                -- Goal: z ∈ Ctx.dom (e :: rest); after simp: z ∈ insert e.name (Ctx.dom rest).
                rw [show z = e.name from hez.symm]
                exact Finset.mem_insert_self _ _
              · apply he_notin
                exact Finset.mem_union.mpr (Or.inr (Finset.mem_insert.mpr (Or.inr hΓ)))
        cases hpv' with
        | @sub _ name u' _ _ hfve hlce =>
          have hfve' : Term.fv u' ⊆
              Ctx.dom (rest ++ ⟨y, t, .sub⟩ :: ⟨z, t, .sub⟩ :: Γ₁) := by
            intro w hw
            have hw' := hfve hw
            rw [Ctx.dom_append, Ctx.dom_cons] at hw'
            rw [Ctx.dom_append, Ctx.dom_cons, Ctx.dom_cons]
            rcases Finset.mem_union.mp hw' with hr | htail
            · exact Finset.mem_union.mpr (Or.inl hr)
            · rcases Finset.mem_insert.mp htail with hey | hΓ
              · exact Finset.mem_union.mpr (Or.inr (Finset.mem_insert.mpr (Or.inl hey)))
              · exact Finset.mem_union.mpr
                  (Or.inr (Finset.mem_insert.mpr
                    (Or.inr (Finset.mem_insert.mpr (Or.inr hΓ)))))
          have res := Prevalid.sub ih' he_notin' hfve' hlce
          simpa using res
        | @equ _ name α _ _ hfve hlce =>
          have hfve' : Term.fv α ⊆
              Ctx.dom (rest ++ ⟨y, t, .sub⟩ :: ⟨z, t, .sub⟩ :: Γ₁) := by
            intro w hw
            have hw' := hfve hw
            rw [Ctx.dom_append, Ctx.dom_cons] at hw'
            rw [Ctx.dom_append, Ctx.dom_cons, Ctx.dom_cons]
            rcases Finset.mem_union.mp hw' with hr | htail
            · exact Finset.mem_union.mpr (Or.inl hr)
            · rcases Finset.mem_insert.mp htail with hey | hΓ
              · exact Finset.mem_union.mpr (Or.inr (Finset.mem_insert.mpr (Or.inl hey)))
              · exact Finset.mem_union.mpr
                  (Or.inr (Finset.mem_insert.mpr
                    (Or.inr (Finset.mem_insert.mpr (Or.inr hΓ)))))
          have res := Prevalid.equ ih' he_notin' hfve' hlce
          simpa using res
    -- Apply Lemma 28a with x := y, s := .fvar z, target tail := ⟨z,t,.sub⟩ :: Γ₁.
    have hok : SubstOk (⟨z, t, .sub⟩ :: Γ₁) (.fvar z) := by
      refine ⟨Term.LC.fvar z, ?_⟩
      intro w hw
      have hwz : w = z := by simpa [Term.fv] using hw
      subst hwz
      rw [Ctx.dom_cons]; exact Finset.mem_insert_self _ _
    exact Lemma_28a_SubstPreservesPrevalid_kind hpv_doubled hok

/-- Helper: build `PrevalidExt` of the renamed context with stack also renamed. -/
private noncomputable def prevalidExt_rename_sub_head
    {Γ₂ Γ₁ : Ctx} {st : Stack} {y z : String} {t : Term}
    (hyz : y ≠ z)
    (hz_notin_Γ₁ : z ∉ Γ₁.dom)
    (hz_notin_Γ₂ : z ∉ Γ₂.dom)
    (hpv : PrevalidExt (Γ₂ ++ ⟨y, t, .sub⟩ :: Γ₁) st) :
    PrevalidExt (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, t, .sub⟩ :: Γ₁)
      (Stack.subst y (.fvar z) st) := by
  classical
  have hpv_base := extractPrevalid hpv
  have hpv_renamed := prevalid_rename_sub_head hyz hz_notin_Γ₁ hz_notin_Γ₂ hpv_base
  -- Now we have prevalidity of the output context. Need to rebuild stack.
  have hLCfz : Term.LC (.fvar z) := Term.LC.fvar z
  -- Build by induction on st.
  induction st with
  | nil =>
    cases hpv with
    | nil _ => exact PrevalidExt.nil hpv_renamed
  | cons α st' ih =>
    match hpv with
    | PrevalidExt.cons hpvr hLCα hfvα =>
      have ih' := ih hpvr
      have hLCα' : Term.LC (Term.subst y (.fvar z) α) := Term.subst_lc hLCfz hLCα
      have hfvα' : Term.fv (Term.subst y (.fvar z) α) ⊆
          Ctx.dom (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, t, .sub⟩ :: Γ₁) := by
        intro w hw
        have hsub := Term.fv_subst_subset y (.fvar z) α hw
        rcases Finset.mem_union.mp hsub with hsd | hsd
        · rcases Finset.mem_sdiff.mp hsd with ⟨hwfv, hwne⟩
          have hw_in : w ∈ Ctx.dom (Γ₂ ++ ⟨y, t, .sub⟩ :: Γ₁) := hfvα hwfv
          rw [Ctx.dom_append, Ctx.dom_cons] at hw_in
          show w ∈ Ctx.dom (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, t, .sub⟩ :: Γ₁)
          rw [Ctx.dom_append, Ctx.dom_subst, Ctx.dom_cons]
          rcases Finset.mem_union.mp hw_in with hΓ₂ | htail
          · exact Finset.mem_union.mpr (Or.inl hΓ₂)
          · rcases Finset.mem_insert.mp htail with hwy | hwΓ₁
            · exact absurd hwy (fun hh => hwne (by simp [hh]))
            · exact Finset.mem_union.mpr
                (Or.inr (Finset.mem_insert_of_mem hwΓ₁))
        · have hwz : w = z := by simpa [Term.fv] using hsd
          rw [hwz]
          show z ∈ Ctx.dom (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, t, .sub⟩ :: Γ₁)
          rw [Ctx.dom_append, Ctx.dom_subst, Ctx.dom_cons]
          exact Finset.mem_union.mpr
            (Or.inr (Finset.mem_insert_self _ _))
      exact PrevalidExt.cons ih' hLCα' hfvα'

/-- Specialized renaming substitution lemma for a `.sub` head binding.
Substitutes `(.fvar z)` for `y` in a derivation whose head-`.sub`
binding is `⟨y, t, .sub⟩`, producing a derivation in the renamed context
where the head is `⟨z, t, .sub⟩`. **No weakening required** at the call
site, hence no `fv body ⊆ Γ.dom` hypothesis needed. -/
private noncomputable def MEqRed.subst_yz_sub_head
    {Γ₁ Γ₂ : Ctx} {st : Stack} {y z : String} {t u u' : Term}
    (hyz : y ≠ z)
    (hz_notin_Γ₁ : z ∉ Γ₁.dom)
    (hz_notin_Γ₂ : z ∉ Γ₂.dom)
    (h : MEqRed (Γ₂ ++ ⟨y, t, .sub⟩ :: Γ₁) st u u') :
    MEqRed (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, t, .sub⟩ :: Γ₁)
      (Stack.subst y (.fvar z) st)
      (Term.subst y (.fvar z) u) (Term.subst y (.fvar z) u') := by
  classical
  generalize hΓ : (Γ₂ ++ ⟨y, t, .sub⟩ :: Γ₁) = Γ at h
  revert hz_notin_Γ₂
  induction h generalizing Γ₂ with
  | @pro Γ st' yi α α' hpv heq hα ihα =>
    subst hΓ
    intro hz_notin_Γ₂
    have hpvL : Prevalid (Γ₂ ++ ⟨y, t, .sub⟩ :: Γ₁) := extractPrevalid hpv
    have hpv' : PrevalidExt (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, t, .sub⟩ :: Γ₁)
        (Stack.subst y (.fvar z) st') :=
      prevalidExt_rename_sub_head hyz hz_notin_Γ₁ hz_notin_Γ₂ hpv
    have hyiy : yi ≠ y := equBinds_ne_x_at_sub_head hpvL heq
    rw [Term.subst_fvar_ne hyiy]
    have heq_lifted : (Ctx.subst y (.fvar z) Γ₂ ++ Γ₁).equBinds yi
        (Term.subst y (.fvar z) α) :=
      equBinds_split (s := .fvar z) hyiy hpvL heq
    have hpv_big : Prevalid (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, t, .sub⟩ :: Γ₁) :=
      prevalid_rename_sub_head hyz hz_notin_Γ₁ hz_notin_Γ₂ hpvL
    have hpv_big_assoc :
        Prevalid (Ctx.subst y (.fvar z) Γ₂ ++ [⟨z, t, .sub⟩] ++ Γ₁) := by
      have heq : (Ctx.subst y (.fvar z) Γ₂ ++ [⟨z, t, .sub⟩] ++ Γ₁) =
          (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, t, .sub⟩ :: Γ₁) := by simp
      exact heq ▸ hpv_big
    have heq' : (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, t, .sub⟩ :: Γ₁).equBinds yi
        (Term.subst y (.fvar z) α) := by
      have := Ctx.equBinds_insert_middle
        (Γ₁ := Ctx.subst y (.fvar z) Γ₂) (Δ := [⟨z, t, .sub⟩]) (Γ₂ := Γ₁)
        hpv_big_assoc heq_lifted
      have heq_simp : (Ctx.subst y (.fvar z) Γ₂ ++ [⟨z, t, .sub⟩] ++ Γ₁) =
          (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, t, .sub⟩ :: Γ₁) := by simp
      exact heq_simp ▸ this
    exact MEqRed.pro hpv' heq' (ihα (Γ₂ := Γ₂) rfl hz_notin_Γ₂)
  | @bet Γ st' tBound v0 v0' bd bd' L hLCt hbody _hUni hv ihbody ihv =>
    subst hΓ
    intro hz_notin_Γ₂
    have hLCfz : Term.LC (.fvar z) := Term.LC.fvar z
    have hsubst_open : Term.subst y (.fvar z) (Term.opening v0' bd') =
        Term.opening (Term.subst y (.fvar z) v0') (Term.subst y (.fvar z) bd') := by
      simp [Term.opening, Term.subst_open hLCfz]
    show MEqRed (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, t, .sub⟩ :: Γ₁)
      (Stack.subst y (.fvar z) st')
      (Term.subst y (.fvar z) (.app (.abs tBound bd) v0))
      (Term.subst y (.fvar z) (Term.opening v0' bd'))
    rw [hsubst_open]
    show MEqRed (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, t, .sub⟩ :: Γ₁)
      (Stack.subst y (.fvar z) st')
      (.app (.abs (Term.subst y (.fvar z) tBound) (Term.subst y (.fvar z) bd))
            (Term.subst y (.fvar z) v0))
      (Term.opening (Term.subst y (.fvar z) v0') (Term.subst y (.fvar z) bd'))
    refine MEqRed.bet (L ∪ {y}) (Term.subst_lc hLCfz hLCt) ?_ trivial ?_
    · intro yfresh hyfresh
      simp [Finset.mem_union, Finset.mem_singleton] at hyfresh
      have hyfL : yfresh ∉ L := hyfresh.1
      have hyfy : yfresh ≠ y := hyfresh.2
      -- Bet body recurses with same Γ₂ (no extension), so reuse hz_notin_Γ₂.
      have ih_body := ihbody yfresh hyfL (Γ₂ := Γ₂) rfl hz_notin_Γ₂
      rw [Term.subst_open_var (Ne.symm hyfy) hLCfz bd,
          Term.subst_open_var (Ne.symm hyfy) hLCfz bd'] at ih_body
      exact ih_body
    · have ihv' := ihv (Γ₂ := Γ₂) rfl hz_notin_Γ₂
      simpa using ihv'
  | @top Γ st' hpv =>
    subst hΓ
    intro hz_notin_Γ₂
    exact MEqRed.top
      (prevalidExt_rename_sub_head hyz hz_notin_Γ₁ hz_notin_Γ₂ hpv)
  | @app Γ st' u_ u_' v_ v_' hu hv ihu ihv =>
    subst hΓ
    intro hz_notin_Γ₂
    have ihu' := ihu (Γ₂ := Γ₂) rfl hz_notin_Γ₂
    have ihv' := ihv (Γ₂ := Γ₂) rfl hz_notin_Γ₂
    simp at ihu'
    refine MEqRed.app ?_ ?_
    · exact ihu'
    · simpa using ihv'
  | @var Γ st' yi hpv =>
    subst hΓ
    intro hz_notin_Γ₂
    have hpv' : PrevalidExt (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, t, .sub⟩ :: Γ₁)
        (Stack.subst y (.fvar z) st') :=
      prevalidExt_rename_sub_head hyz hz_notin_Γ₁ hz_notin_Γ₂ hpv
    by_cases hyiy : yi = y
    · -- subst y (.fvar z) (.fvar yi) = .fvar z when yi = y. Use MEqRed.refl.
      have hsubst_eq : Term.subst y (.fvar z) (.fvar yi) = .fvar z := by
        rw [hyiy]; simp [Term.subst]
      rw [hsubst_eq]
      have hLCz : Term.LC (.fvar z) := Term.LC.fvar z
      have hfvz : Term.fv (.fvar z) ⊆
          Ctx.dom (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, t, .sub⟩ :: Γ₁) := by
        intro w hw
        have hwz : w = z := by simpa [Term.fv] using hw
        subst hwz
        rw [Ctx.dom_append, Ctx.dom_subst, Ctx.dom_cons]
        exact Finset.mem_union.mpr (Or.inr (Finset.mem_insert_self _ _))
      exact MEqRed.refl hpv' hLCz hfvz
    · rw [Term.subst_fvar_ne hyiy]
      exact MEqRed.var hpv'
  | @fun_ Γ tt tt' bd bd' L ht hbody _hUni iht ihbody =>
    subst hΓ
    intro hz_notin_Γ₂
    show MEqRed (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, t, .sub⟩ :: Γ₁)
      (Stack.subst y (.fvar z) [])
      (.abs (Term.subst y (.fvar z) tt) (Term.subst y (.fvar z) bd))
      (.abs (Term.subst y (.fvar z) tt') (Term.subst y (.fvar z) bd'))
    refine MEqRed.fun_ (L ∪ {y} ∪ {z}) ?_ ?_ trivial
    · have iht' := iht (Γ₂ := Γ₂) rfl hz_notin_Γ₂
      simpa using iht'
    · intro yfresh hyfresh
      simp only [Finset.mem_union, Finset.mem_singleton, not_or] at hyfresh
      have hyfL : yfresh ∉ L := hyfresh.1.1
      have hyfy : yfresh ≠ y := hyfresh.1.2
      have hyfz : yfresh ≠ z := hyfresh.2
      -- yfresh ≠ z, so z ∉ (⟨yfresh, tt, .sub⟩ :: Γ₂).dom.
      have hz_notin_Γ₂' : z ∉ Ctx.dom (⟨yfresh, tt, .sub⟩ :: Γ₂) := by
        rw [Ctx.dom_cons]
        intro hmem
        rcases Finset.mem_insert.mp hmem with hzy | hzΓ
        · exact hyfz hzy.symm
        · exact hz_notin_Γ₂ hzΓ
      have ih_body :=
        ihbody yfresh hyfL (Γ₂ := ⟨yfresh, tt, .sub⟩ :: Γ₂) (by simp) hz_notin_Γ₂'
      have hLCfz : Term.LC (.fvar z) := Term.LC.fvar z
      rw [Term.subst_open_var (Ne.symm hyfy) hLCfz bd,
          Term.subst_open_var (Ne.symm hyfy) hLCfz bd'] at ih_body
      simpa [Ctx.subst, List.cons_append] using ih_body
  | @tAp Γ st' u_ hpv hLCu hfv =>
    subst hΓ
    intro hz_notin_Γ₂
    have hpv' : PrevalidExt (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, t, .sub⟩ :: Γ₁)
        (Stack.subst y (.fvar z) st') :=
      prevalidExt_rename_sub_head hyz hz_notin_Γ₁ hz_notin_Γ₂ hpv
    have hLCu' : Term.LC (Term.subst y (.fvar z) u_) :=
      Term.subst_lc (Term.LC.fvar z) hLCu
    have hfv' :
        Term.fv (Term.subst y (.fvar z) u_) ⊆
          Ctx.dom (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, t, .sub⟩ :: Γ₁) := by
      intro w hw
      have hsub := Term.fv_subst_subset y (.fvar z) u_ hw
      rcases Finset.mem_union.mp hsub with hsd | hsd
      · rcases Finset.mem_sdiff.mp hsd with ⟨hwfv, hwne⟩
        have hw_in : w ∈ Ctx.dom (Γ₂ ++ ⟨y, t, .sub⟩ :: Γ₁) := hfv hwfv
        rw [Ctx.dom_append, Ctx.dom_cons] at hw_in
        show w ∈ Ctx.dom (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, t, .sub⟩ :: Γ₁)
        rw [Ctx.dom_append, Ctx.dom_subst, Ctx.dom_cons]
        rcases Finset.mem_union.mp hw_in with hΓ₂ | htail
        · exact Finset.mem_union.mpr (Or.inl hΓ₂)
        · rcases Finset.mem_insert.mp htail with hwy | hwΓ₁
          · exact absurd hwy (fun hh => hwne (by simp [hh]))
          · exact Finset.mem_union.mpr
              (Or.inr (Finset.mem_insert_of_mem hwΓ₁))
      · have hwz : w = z := by simpa [Term.fv] using hsd
        rw [hwz]
        show z ∈ Ctx.dom (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, t, .sub⟩ :: Γ₁)
        rw [Ctx.dom_append, Ctx.dom_subst, Ctx.dom_cons]
        exact Finset.mem_union.mpr
          (Or.inr (Finset.mem_insert_self _ _))
    show MEqRed (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, t, .sub⟩ :: Γ₁)
      (Stack.subst y (.fvar z) st')
      (Term.subst y (.fvar z) (.app .top u_)) (Term.subst y (.fvar z) .top)
    simp [Term.subst]
    exact MEqRed.tAp hpv' hLCu' hfv'
  | @fOp Γ st' tt tt' αi bd bd' L ht hbody _hUni iht ihbody =>
    subst hΓ
    intro hz_notin_Γ₂
    show MEqRed (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, t, .sub⟩ :: Γ₁)
      (Stack.subst y (.fvar z) (αi :: st'))
      (.abs (Term.subst y (.fvar z) tt) (Term.subst y (.fvar z) bd))
      (.abs (Term.subst y (.fvar z) tt') (Term.subst y (.fvar z) bd'))
    rw [Stack.subst_cons]
    refine MEqRed.fOp (L ∪ {y} ∪ {z}) ?_ ?_ trivial
    · have iht' := iht (Γ₂ := Γ₂) rfl hz_notin_Γ₂
      simpa using iht'
    · intro yfresh hyfresh
      simp only [Finset.mem_union, Finset.mem_singleton, not_or] at hyfresh
      have hyfL : yfresh ∉ L := hyfresh.1.1
      have hyfy : yfresh ≠ y := hyfresh.1.2
      have hyfz : yfresh ≠ z := hyfresh.2
      have hz_notin_Γ₂' : z ∉ Ctx.dom (⟨yfresh, αi, .equ⟩ :: Γ₂) := by
        rw [Ctx.dom_cons]
        intro hmem
        rcases Finset.mem_insert.mp hmem with hzy | hzΓ
        · exact hyfz hzy.symm
        · exact hz_notin_Γ₂ hzΓ
      have ih_body :=
        ihbody yfresh hyfL (Γ₂ := ⟨yfresh, αi, .equ⟩ :: Γ₂) (by simp) hz_notin_Γ₂'
      have hLCfz : Term.LC (.fvar z) := Term.LC.fvar z
      rw [Term.subst_open_var (Ne.symm hyfy) hLCfz bd,
          Term.subst_open_var (Ne.symm hyfy) hLCfz bd'] at ih_body
      simpa [Ctx.subst, List.cons_append] using ih_body

/-- **Renaming for `MEqRed` under a `.sub`-head binding.** Given a
derivation at a fresh `y`, produce one at any other fresh `z`.

This version does **NOT** require `Term.fv body ⊆ Γ.dom` (the previous
implementation needed it for the internal weakening step). It uses the
`subst_yz_sub_head` primitive directly, with `Γ₂ := []`. -/
noncomputable def MEqRed.rename_sub
    {Γ : Ctx} {s : Stack} {body body' t : Term} {y z : String}
    (hpvΓ : Prevalid Γ)
    (hLCt : Term.LC t) (hfvt : Term.fv t ⊆ Γ.dom)
    (hy_notin_Γ : y ∉ Γ.dom) (hz_notin_Γ : z ∉ Γ.dom)
    (hy_notin_body : y ∉ Term.fv body) (hy_notin_body' : y ∉ Term.fv body')
    (hy_notin_stack : ∀ α ∈ s, y ∉ Term.fv α)
    (h : MEqRed (⟨y, t, .sub⟩ :: Γ) s (body^[y]) (body'^[y])) :
    MEqRed (⟨z, t, .sub⟩ :: Γ) s (body^[z]) (body'^[z]) := by
  classical
  by_cases hyz : y = z
  · subst hyz; exact h
  -- Apply subst_yz_sub_head with Γ₂ := [], y := y, z := z.
  have h_in_form : MEqRed (([] : Ctx) ++ ⟨y, t, .sub⟩ :: Γ) s (body^[y]) (body'^[y]) := by
    show MEqRed (⟨y, t, .sub⟩ :: Γ) s (body^[y]) (body'^[y]); exact h
  have hz_notin_empty : z ∉ Ctx.dom ([] : Ctx) := by
    simp [Ctx.dom]
  have h_subst :=
    MEqRed.subst_yz_sub_head (Γ₂ := ([] : Ctx)) hyz hz_notin_Γ hz_notin_empty h_in_form
  -- h_subst : MEqRed ([].subst y (.fvar z) ++ ⟨z, t, .sub⟩ :: Γ) ...
  have hctx_eq :
      Ctx.subst y (.fvar z) ([] : Ctx) ++ (⟨z, t, .sub⟩ :: Γ) =
        ⟨z, t, .sub⟩ :: Γ := by simp
  have hstk_eq : Stack.subst y (.fvar z) s = s :=
    Stack.subst_fresh hy_notin_stack
  have hbody_eq : Term.subst y (.fvar z) (body^[y]) = body^[z] :=
    Term.subst_open_fresh hy_notin_body
  have hbody'_eq : Term.subst y (.fvar z) (body'^[y]) = body'^[z] :=
    Term.subst_open_fresh hy_notin_body'
  rw [hctx_eq, hstk_eq, hbody_eq, hbody'_eq] at h_subst
  exact h_subst

/-! ## §3. Renaming for MEqRed under an `.equ` head binding

For an `.equ`-head context `⟨y, α, .equ⟩ :: Γ`, Lemma 32 (restricted to
`s = v`) doesn't directly apply to renaming (we'd need `.fvar z = α`,
which is generally false).

We use a different tactic: we first apply Lemma 32 with a TRIVIAL
self-substitution `subst y (.fvar y)` to enable the IH machinery, then
notice that this is the identity. That alone doesn't help. The clean
fix is to inline the proof.

Below we provide a from-scratch renaming proof for `.equ` head, by
direct induction on the derivation (mirroring Lemma 32's structure).
The crucial `Me-Pro y_inner = y` arm uses uniqueness of the head
binding to rewrite the target, then applies `Me-Pro` for `z` against
the renamed head binding.
-/

/-- Specialized renaming substitution lemma for an `.equ` head binding.
Substitutes `(.fvar z)` for `y` in a derivation whose head-`.equ`
binding is `⟨y, α, .equ⟩`, where `y ∉ fv α` (always true by
prevalidity of the input context).

The proof is a direct induction on the derivation, mirroring
`Lemma_32_ReductionUnderSubst_Eq_OfEqu`. The renaming provides exactly
the structural simplification needed to dispatch the `Me-Pro y_inner = y`
arm uniformly: the looked-up `α` (= the head binding) is unaffected by
substitution, and the renamed lookup target `.fvar z` is found in the
new head `⟨z, α, .equ⟩`. -/
private noncomputable def MEqRed.subst_yz_equ_head
    {Γ₁ Γ₂ : Ctx} {st : Stack} {y z : String} {α u u' : Term}
    (hyz : y ≠ z)
    (hy_notin_α : y ∉ Term.fv α)
    (h : MEqRed (Γ₂ ++ ⟨y, α, .equ⟩ :: ⟨z, α, .equ⟩ :: Γ₁) st u u') :
    MEqRed (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, α, .equ⟩ :: Γ₁)
      (Stack.subst y (.fvar z) st)
      (Term.subst y (.fvar z) u) (Term.subst y (.fvar z) u') := by
  classical
  -- The substituted term s = .fvar z, the bound α at head is independent of y.
  -- We pose Lemma 32 with v := α, s := .fvar z, but Lemma 32 requires s = v.
  -- So we need to handle this via direct induction. Inline the proof.
  have hok : SubstOk (⟨z, α, .equ⟩ :: Γ₁) (.fvar z) := by
    refine ⟨Term.LC.fvar z, ?_⟩
    intro w hw
    have hwz : w = z := by simpa [Term.fv] using hw
    subst hwz
    rw [Ctx.dom_cons]; exact Finset.mem_insert_self _ _
  generalize hΓ : (Γ₂ ++ ⟨y, α, .equ⟩ :: ⟨z, α, .equ⟩ :: Γ₁) = Γ at h
  induction h generalizing Γ₂ with
  | @pro Γ st' yi β β' hpv heq hβ ihβ =>
    subst hΓ
    have hpvL : Prevalid (Γ₂ ++ ⟨y, α, .equ⟩ :: ⟨z, α, .equ⟩ :: Γ₁) := extractPrevalid hpv
    have hpv' : PrevalidExt (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, α, .equ⟩ :: Γ₁)
        (Stack.subst y (.fvar z) st') :=
      Lemma_28_SubstPreservesPrevalid hpv hok
    by_cases hyiy : yi = y
    · -- yi = y. The .equ head for y has bound α — uniqueness gives β = α.
      have heq_y : (Γ₂ ++ ⟨y, α, .equ⟩ :: ⟨z, α, .equ⟩ :: Γ₁).equBinds y β :=
        hyiy ▸ heq
      have hβα : β = α := equBinds_at_equ_head_unique hpvL heq_y
      -- We rewrite β to α in ihβ rather than substituting (which would erase α).
      have ihβ_app := ihβ (Γ₂ := Γ₂) rfl
      rw [hβα] at ihβ_app
      have hα_subst : Term.subst y (.fvar z) α = α := Term.subst_fresh hy_notin_α
      rw [hα_subst] at ihβ_app
      -- We need equBinds for z in the renamed context.
      have hz_eqbinds :
          (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, α, .equ⟩ :: Γ₁).equBinds z α := by
        -- z ∉ Γ₂.dom (and so z ∉ (Ctx.subst y (.fvar z) Γ₂).dom = Γ₂.dom).
        -- Then lookup misses in Γ₂ and finds z at the head of the tail.
        have hpvL_norm : Prevalid (Γ₂ ++ (⟨y, α, .equ⟩ :: ⟨z, α, .equ⟩ :: Γ₁)) :=
          hpvL
        have hpv_inner : Prevalid (⟨y, α, .equ⟩ :: ⟨z, α, .equ⟩ :: Γ₁) :=
          Prevalid.outer hpvL_norm
        -- z fresh w.r.t. ⟨y,α,.equ⟩ :: ... — actually z ∈ ⟨z,α,.equ⟩ :: Γ₁'s dom (it's the head).
        -- But is z ∈ Γ₂.dom? We need Γ₂.dom ∩ {z} = ∅. By prevalidity, all entries in Γ₂ have
        -- names ∉ subsequent context dom, so e.name ≠ z for all e in Γ₂.
        have hz_notin_Γ₂ : z ∉ Γ₂.dom := by
          intro hzΓ₂
          have hpv_inner' : Prevalid (⟨z, α, .equ⟩ :: Γ₁) :=
            Prevalid.outer (Γ₂ := [⟨y, α, .equ⟩]) (Γ₁ := ⟨z, α, .equ⟩ :: Γ₁) (by
              show Prevalid ([⟨y, α, .equ⟩] ++ ⟨z, α, .equ⟩ :: Γ₁); exact hpv_inner)
          -- z is the head's name; from Prevalid we get z ∉ Γ₁.dom but not Γ₂.dom directly.
          -- Need: from Prevalid (Γ₂ ++ ⟨y,α,.equ⟩ :: ⟨z,α,.equ⟩ :: Γ₁), prove z ∉ Γ₂.dom.
          -- This follows from the NoDup property: NoDup of names in the full list.
          -- Use Ctx.notin_delta_of_in_tail (from Weakening): z ∈ tail.dom → z ∉ Δ.dom.
          -- Treat Γ₂ as Δ, ⟨y,α,.equ⟩ :: ⟨z,α,.equ⟩ :: Γ₁ as the inner Γ₂.
          have hz_in_tail : z ∈ Ctx.dom (⟨y, α, .equ⟩ :: ⟨z, α, .equ⟩ :: Γ₁) := by
            rw [Ctx.dom_cons, Ctx.dom_cons]
            exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
          exact (Ctx.notin_delta_of_in_tail hpvL hz_in_tail) hzΓ₂
        -- Now, lookupEqu in Γ₂ for z is none (z ∉ dom).
        -- Then lookupEqu in ⟨z,α,.equ⟩ :: Γ₁ for z is some α.
        -- Use a helper: Ctx.lookupEqu_append_right.
        have hlk_tail : Ctx.lookupEqu (⟨z, α, .equ⟩ :: Γ₁) z = some α := by
          simp [Ctx.lookupEqu, Ctx.lookupEqu_cons]
        have hz_notin_subst_Γ₂ : z ∉ (Ctx.subst y (.fvar z) Γ₂).dom := by
          rw [Ctx.dom_subst]; exact hz_notin_Γ₂
        show Ctx.lookupEqu (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, α, .equ⟩ :: Γ₁) z = some α
        exact Ctx.lookupEqu_append_right (Ctx.subst y (.fvar z) Γ₂) _ z α
          hz_notin_subst_Γ₂ hlk_tail
      have hfvar_eq : Term.subst y (.fvar z) (.fvar yi) = .fvar z := by
        rw [hyiy]; simp [Term.subst]
      rw [hfvar_eq]
      exact MEqRed.pro hpv' hz_eqbinds ihβ_app
    · -- yi ≠ y: standard case. Look up yi's .equ binding in renamed context.
      rw [Term.subst_fvar_ne hyiy]
      have heq' : (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, α, .equ⟩ :: Γ₁).equBinds yi
          (Term.subst y (.fvar z) β) := by
        -- equBinds_split_equ: handles ⟨y, v, .equ⟩-head case via Lemma 32 lemma.
        -- Our context is Γ₂ ++ ⟨y, α, .equ⟩ :: ⟨z, α, .equ⟩ :: Γ₁; substitute y → fvar z.
        -- equBinds_split_equ handles substituting at an .equ head, where the head is
        -- ⟨y, α, .equ⟩, the tail is ⟨z, α, .equ⟩ :: Γ₁.
        exact equBinds_split_equ (s := .fvar z) hyiy hpvL heq
      exact MEqRed.pro hpv' heq' (ihβ (Γ₂ := Γ₂) rfl)
  | @bet Γ st' tBound v0 v0' bd bd' L hLCt hbody _hUni hv ihbody ihv =>
    subst hΓ
    have hLCfz : Term.LC (.fvar z) := Term.LC.fvar z
    have hsubst_open : Term.subst y (.fvar z) (Term.opening v0' bd') =
        Term.opening (Term.subst y (.fvar z) v0') (Term.subst y (.fvar z) bd') := by
      simp [Term.opening, Term.subst_open hLCfz]
    show MEqRed (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, α, .equ⟩ :: Γ₁)
      (Stack.subst y (.fvar z) st')
      (Term.subst y (.fvar z) (.app (.abs tBound bd) v0))
      (Term.subst y (.fvar z) (Term.opening v0' bd'))
    rw [hsubst_open]
    show MEqRed (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, α, .equ⟩ :: Γ₁)
      (Stack.subst y (.fvar z) st')
      (.app (.abs (Term.subst y (.fvar z) tBound) (Term.subst y (.fvar z) bd))
            (Term.subst y (.fvar z) v0))
      (Term.opening (Term.subst y (.fvar z) v0') (Term.subst y (.fvar z) bd'))
    refine MEqRed.bet (L ∪ {y}) (Term.subst_lc hLCfz hLCt) ?_ trivial ?_
    · intro yfresh hyfresh
      simp [Finset.mem_union, Finset.mem_singleton] at hyfresh
      have hyfL : yfresh ∉ L := hyfresh.1
      have hyfy : yfresh ≠ y := hyfresh.2
      have ih_body := ihbody yfresh hyfL (Γ₂ := Γ₂) rfl
      rw [Term.subst_open_var (Ne.symm hyfy) hLCfz bd,
          Term.subst_open_var (Ne.symm hyfy) hLCfz bd'] at ih_body
      exact ih_body
    · have ihv' := ihv (Γ₂ := Γ₂) rfl
      simpa using ihv'
  | @top Γ st' hpv =>
    subst hΓ
    exact MEqRed.top (Lemma_28_SubstPreservesPrevalid hpv hok)
  | @app Γ st' u_ u_' v_ v_' hu hv ihu ihv =>
    subst hΓ
    have ihu' := ihu (Γ₂ := Γ₂) rfl
    have ihv' := ihv (Γ₂ := Γ₂) rfl
    simp at ihu'
    refine MEqRed.app ?_ ?_
    · exact ihu'
    · simpa using ihv'
  | @var Γ st' yi hpv =>
    subst hΓ
    have hpv' : PrevalidExt (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, α, .equ⟩ :: Γ₁)
        (Stack.subst y (.fvar z) st') :=
      Lemma_28_SubstPreservesPrevalid hpv hok
    by_cases hyiy : yi = y
    · -- subst y (.fvar z) (.fvar yi) = .fvar z when yi = y.
      have hsubst_eq : Term.subst y (.fvar z) (.fvar yi) = .fvar z := by
        rw [hyiy]; simp [Term.subst]
      rw [hsubst_eq]
      have hLCz : Term.LC (.fvar z) := Term.LC.fvar z
      have hfvz : Term.fv (.fvar z) ⊆
          Ctx.dom (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, α, .equ⟩ :: Γ₁) := by
        intro w hw
        have hwz : w = z := by simpa [Term.fv] using hw
        subst hwz
        rw [Ctx.dom_append, Ctx.dom_subst, Ctx.dom_cons]
        exact Finset.mem_union.mpr (Or.inr (Finset.mem_insert_self _ _))
      exact MEqRed.refl hpv' hLCz hfvz
    · rw [Term.subst_fvar_ne hyiy]
      exact MEqRed.var hpv'
  | @fun_ Γ tt tt' bd bd' L ht hbody _hUni iht ihbody =>
    subst hΓ
    show MEqRed (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, α, .equ⟩ :: Γ₁)
      (Stack.subst y (.fvar z) [])
      (.abs (Term.subst y (.fvar z) tt) (Term.subst y (.fvar z) bd))
      (.abs (Term.subst y (.fvar z) tt') (Term.subst y (.fvar z) bd'))
    refine MEqRed.fun_ (L ∪ {y}) ?_ ?_ trivial
    · have iht' := iht (Γ₂ := Γ₂) rfl
      simpa using iht'
    · intro yfresh hyfresh
      simp [Finset.mem_union, Finset.mem_singleton] at hyfresh
      have hyfL : yfresh ∉ L := hyfresh.1
      have hyfy : yfresh ≠ y := hyfresh.2
      have ih_body := ihbody yfresh hyfL (Γ₂ := ⟨yfresh, tt, .sub⟩ :: Γ₂) (by simp)
      have hLCfz : Term.LC (.fvar z) := Term.LC.fvar z
      rw [Term.subst_open_var (Ne.symm hyfy) hLCfz bd,
          Term.subst_open_var (Ne.symm hyfy) hLCfz bd'] at ih_body
      simpa [Ctx.subst, List.cons_append] using ih_body
  | @tAp Γ st' u_ hpv hLCu hfv =>
    subst hΓ
    have hpv' : PrevalidExt (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, α, .equ⟩ :: Γ₁)
        (Stack.subst y (.fvar z) st') :=
      Lemma_28_SubstPreservesPrevalid hpv hok
    have hLCu' : Term.LC (Term.subst y (.fvar z) u_) :=
      Term.subst_lc (Term.LC.fvar z) hLCu
    have hfv' :
        Term.fv (Term.subst y (.fvar z) u_) ⊆
          Ctx.dom (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, α, .equ⟩ :: Γ₁) := by
      intro w hw
      have hsub := Term.fv_subst_subset y (.fvar z) u_ hw
      rcases Finset.mem_union.mp hsub with hsd | hsd
      · rcases Finset.mem_sdiff.mp hsd with ⟨hwfv, hwne⟩
        have hwΓ : w ∈ Ctx.dom (Γ₂ ++ ⟨y, α, .equ⟩ :: ⟨z, α, .equ⟩ :: Γ₁) :=
          hfv hwfv
        rw [Ctx.dom_append] at hwΓ
        rw [Ctx.dom_append, Ctx.dom_subst]
        rcases Finset.mem_union.mp hwΓ with hΓ₂ | htail
        · exact Finset.mem_union.mpr (Or.inl hΓ₂)
        · simp [Ctx.dom_cons] at htail
          rcases htail with hwy | hwz | hwΓ₁
          · exact absurd hwy (fun hh => hwne (by simp [hh]))
          · subst hwz
            apply Finset.mem_union.mpr; right
            simp [Ctx.dom_cons]
          · apply Finset.mem_union.mpr; right
            simp [Ctx.dom_cons]; exact Or.inr hwΓ₁
      · have hwz : w = z := by simpa [Term.fv] using hsd
        subst hwz
        rw [Ctx.dom_append, Ctx.dom_subst]
        apply Finset.mem_union.mpr; right
        simp [Ctx.dom_cons]
    show MEqRed (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, α, .equ⟩ :: Γ₁)
      (Stack.subst y (.fvar z) st')
      (Term.subst y (.fvar z) (.app .top u_)) (Term.subst y (.fvar z) .top)
    simp [Term.subst]
    exact MEqRed.tAp hpv' hLCu' hfv'
  | @fOp Γ st' tt tt' αi bd bd' L ht hbody _hUni iht ihbody =>
    subst hΓ
    show MEqRed (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, α, .equ⟩ :: Γ₁)
      (Stack.subst y (.fvar z) (αi :: st'))
      (.abs (Term.subst y (.fvar z) tt) (Term.subst y (.fvar z) bd))
      (.abs (Term.subst y (.fvar z) tt') (Term.subst y (.fvar z) bd'))
    rw [Stack.subst_cons]
    refine MEqRed.fOp (L ∪ {y}) ?_ ?_ trivial
    · have iht' := iht (Γ₂ := Γ₂) rfl
      simpa using iht'
    · intro yfresh hyfresh
      simp [Finset.mem_union, Finset.mem_singleton] at hyfresh
      have hyfL : yfresh ∉ L := hyfresh.1
      have hyfy : yfresh ≠ y := hyfresh.2
      have ih_body := ihbody yfresh hyfL (Γ₂ := ⟨yfresh, αi, .equ⟩ :: Γ₂) (by simp)
      have hLCfz : Term.LC (.fvar z) := Term.LC.fvar z
      rw [Term.subst_open_var (Ne.symm hyfy) hLCfz bd,
          Term.subst_open_var (Ne.symm hyfy) hLCfz bd'] at ih_body
      simpa [Ctx.subst, List.cons_append] using ih_body

/-- **Renaming for `MEqRed` under an `.equ`-head binding.** Given a
derivation at a fresh `y`, produce one at any other fresh `z`. -/
noncomputable def MEqRed.rename_equ
    {Γ : Ctx} {s : Stack} {body body' α : Term} {y z : String}
    (hpvΓ : Prevalid Γ)
    (hLCα : Term.LC α) (hfvα : Term.fv α ⊆ Γ.dom)
    (hy_notin_Γ : y ∉ Γ.dom) (hz_notin_Γ : z ∉ Γ.dom)
    (hy_notin_body : y ∉ Term.fv body) (hy_notin_body' : y ∉ Term.fv body')
    (hfv_body : Term.fv body ⊆ Γ.dom) (hfv_body' : Term.fv body' ⊆ Γ.dom)
    (hy_notin_stack : ∀ β ∈ s, y ∉ Term.fv β)
    (h : MEqRed (⟨y, α, .equ⟩ :: Γ) s (body^[y]) (body'^[y])) :
    MEqRed (⟨z, α, .equ⟩ :: Γ) s (body^[z]) (body'^[z]) := by
  classical
  by_cases hyz : y = z
  · subst hyz; exact h
  -- Build prevalidity for ⟨y,α,.equ⟩ :: ⟨z,α,.equ⟩ :: Γ.
  have hy_notin_α : y ∉ Term.fv α := fv_notin_of_dom_notin hfvα hy_notin_Γ
  have hpvz : Prevalid (⟨z, α, .equ⟩ :: Γ) :=
    Prevalid.equ hpvΓ hz_notin_Γ hfvα hLCα
  have hyzdom : y ∉ Ctx.dom (⟨z, α, .equ⟩ :: Γ) := by
    rw [Ctx.dom_cons]
    intro hmem
    rcases Finset.mem_insert.mp hmem with hyz' | hyΓ
    · exact hyz hyz'
    · exact hy_notin_Γ hyΓ
  have hfvα_z : Term.fv α ⊆ Ctx.dom (⟨z, α, .equ⟩ :: Γ) := by
    intro w hw
    rw [Ctx.dom_cons]
    exact Finset.mem_insert_of_mem (hfvα hw)
  have hpv_yz : Prevalid (⟨y, α, .equ⟩ :: ⟨z, α, .equ⟩ :: Γ) :=
    Prevalid.equ hpvz hyzdom hfvα_z hLCα
  -- Build fv bound on body^[y].
  have hfv_open_y : Term.fv (body^[y]) ⊆ Ctx.dom (⟨y, α, .equ⟩ :: Γ) := by
    intro w hw
    have hsub := Term.fv_open_subset 0 (.fvar y) body
    rw [Ctx.dom_cons]
    rcases Finset.mem_union.mp (hsub hw) with hwBody | hwY
    · exact Finset.mem_insert_of_mem (hfv_body hwBody)
    · have hwy : w = y := by simpa [Term.fv] using hwY
      subst hwy
      exact Finset.mem_insert_self _ _
  -- Apply Lemma 22.
  have hpv_pre : Prevalid (([⟨y, α, .equ⟩] : Ctx) ++ Γ) := by
    show Prevalid (⟨y, α, .equ⟩ :: Γ)
    exact Prevalid.equ hpvΓ hy_notin_Γ hfvα hLCα
  have hpv_post : Prevalid (([⟨y, α, .equ⟩] : Ctx) ++ [⟨z, α, .equ⟩] ++ Γ) := by
    show Prevalid (⟨y, α, .equ⟩ :: ⟨z, α, .equ⟩ :: Γ)
    exact hpv_yz
  have h_weakened : MEqRed (⟨y, α, .equ⟩ :: ⟨z, α, .equ⟩ :: Γ)
      s (body^[y]) (body'^[y]) := by
    have hh : MEqRed (([⟨y, α, .equ⟩] : Ctx) ++ Γ) s (body^[y]) (body'^[y]) := by
      show MEqRed (⟨y, α, .equ⟩ :: Γ) s (body^[y]) (body'^[y]); exact h
    have hfvU : Term.fv (body^[y]) ⊆ Ctx.dom (([⟨y, α, .equ⟩] : Ctx) ++ Γ) := by
      show Term.fv (body^[y]) ⊆ Ctx.dom (⟨y, α, .equ⟩ :: Γ); exact hfv_open_y
    have hres :=
      Lemma_22_WeakeningMEqRed (Γ₁ := [⟨y, α, .equ⟩]) (Δ := [⟨z, α, .equ⟩]) (Γ₂ := Γ)
        hpv_pre hfvU hpv_post hh
    have heq : (([⟨y, α, .equ⟩] : Ctx) ++ [⟨z, α, .equ⟩] ++ Γ) =
        (⟨y, α, .equ⟩ :: ⟨z, α, .equ⟩ :: Γ) := by simp
    exact heq ▸ hres
  -- Apply our specialized renaming substitution.
  have h_norm : MEqRed (([] : Ctx) ++ ⟨y, α, .equ⟩ :: ⟨z, α, .equ⟩ :: Γ)
      s (body^[y]) (body'^[y]) := by
    show MEqRed (⟨y, α, .equ⟩ :: ⟨z, α, .equ⟩ :: Γ) s (body^[y]) (body'^[y])
    exact h_weakened
  have h_subst :=
    MEqRed.subst_yz_equ_head (Γ₂ := []) hyz hy_notin_α h_norm
  have hctx_eq :
      Ctx.subst y (.fvar z) ([] : Ctx) ++ (⟨z, α, .equ⟩ :: Γ) =
        ⟨z, α, .equ⟩ :: Γ := by simp
  have hstk_eq : Stack.subst y (.fvar z) s = s :=
    Stack.subst_fresh hy_notin_stack
  have hbody_eq : Term.subst y (.fvar z) (body^[y]) = body^[z] :=
    Term.subst_open_fresh hy_notin_body
  have hbody'_eq : Term.subst y (.fvar z) (body'^[y]) = body'^[z] :=
    Term.subst_open_fresh hy_notin_body'
  rw [hctx_eq, hstk_eq, hbody_eq, hbody'_eq] at h_subst
  exact h_subst

/-! ## §4. Renaming for MSubRed under a `.sub`-head binding

We provide the analogue `MSubRed.subst_yz_sub_head` of
`MEqRed.subst_yz_sub_head` that operates on the non-doubled context.
The proof is by direct induction; for the `Ms-Equ` arm we delegate to
`MEqRed.subst_yz_sub_head`. Critically, **no escape-hatch axiom** (such
as `Lemma_30_msPro_x_axiom`) is needed: the `Ms-Pro y = x` case is
discharged directly because `subBinds_at_sub_head_unique` gives
`t' = t`, then `y ∉ fv t` (by prevalidity) makes `subst y (.fvar z) t = t`,
yielding `Ms-Pro z` against the renamed head binding.
-/

/-- Specialized renaming substitution lemma for `MSubRed` under a
`.sub`-head binding. Mirrors `MEqRed.subst_yz_sub_head`. **No
weakening required**, no `fv body ⊆ Γ.dom` hypothesis, **no axiom**
(unlike `Lemma_30_ReductionUnderSubst_Sub` which uses
`Lemma_30_msPro_x_axiom`). -/
private noncomputable def MSubRed.subst_yz_sub_head
    {Γ₁ Γ₂ : Ctx} {st : Stack} {y z : String} {t u u' : Term}
    (hyz : y ≠ z)
    (hz_notin_Γ₁ : z ∉ Γ₁.dom)
    (hz_notin_Γ₂ : z ∉ Γ₂.dom)
    (h : MSubRed (Γ₂ ++ ⟨y, t, .sub⟩ :: Γ₁) st u u') :
    MSubRed (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, t, .sub⟩ :: Γ₁)
      (Stack.subst y (.fvar z) st)
      (Term.subst y (.fvar z) u) (Term.subst y (.fvar z) u') := by
  classical
  generalize hΓ : (Γ₂ ++ ⟨y, t, .sub⟩ :: Γ₁) = Γ at h
  revert hz_notin_Γ₂
  induction h generalizing Γ₂ with
  | @pro Γ st' yi t' hpv hsb =>
    subst hΓ
    intro hz_notin_Γ₂
    have hpvL : Prevalid (Γ₂ ++ ⟨y, t, .sub⟩ :: Γ₁) := extractPrevalid hpv
    have hpv' : PrevalidExt (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, t, .sub⟩ :: Γ₁)
        (Stack.subst y (.fvar z) st') :=
      prevalidExt_rename_sub_head hyz hz_notin_Γ₁ hz_notin_Γ₂ hpv
    by_cases hyiy : yi = y
    · -- yi = y. Lookup .sub binding for y at head: t' = t.
      have hsb_y : (Γ₂ ++ ⟨y, t, .sub⟩ :: Γ₁).subBinds y t' := hyiy ▸ hsb
      have ht'_eq : t' = t := subBinds_at_sub_head_unique hpvL hsb_y
      rw [hyiy, ht'_eq]
      -- subst y (.fvar y) (.fvar y) = .fvar z. We need y ∉ fv t to make
      -- subst y (.fvar z) t = t. Get from Prevalid: ⟨y, t, .sub⟩ :: Γ₁'s t has fv ⊆ Γ₁.dom; y ∉ Γ₁.dom.
      have hpv_inner : Prevalid (⟨y, t, .sub⟩ :: Γ₁) := Prevalid.outer hpvL
      have hy_notin_t : y ∉ Term.fv t := by
        cases hpv_inner with
        | sub _ hy_notin_Γ₁_inner hfvt _ =>
          intro h; exact hy_notin_Γ₁_inner (hfvt h)
      have hsubst_y_fvar_y : Term.subst y (.fvar z) (.fvar y) = .fvar z := by
        simp [Term.subst]
      rw [hsubst_y_fvar_y, Term.subst_fresh hy_notin_t]
      -- Goal: MSubRed (renamed) (.fvar z) t. Use Ms-Pro for z; subBinds z t holds because
      -- z ∉ Γ₂.dom so lookup goes to head ⟨z, t, .sub⟩.
      have hsb_z : (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, t, .sub⟩ :: Γ₁).subBinds z t := by
        have hz_notin_subst_Γ₂ : z ∉ (Ctx.subst y (.fvar z) Γ₂).dom := by
          rw [Ctx.dom_subst]; exact hz_notin_Γ₂
        have hlk_tail : Ctx.lookupSub (⟨z, t, .sub⟩ :: Γ₁) z = some t := by
          simp [Ctx.lookupSub, Ctx.lookupSub_cons]
        show Ctx.lookupSub (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, t, .sub⟩ :: Γ₁) z = some t
        exact Ctx.lookupSub_append_right (Ctx.subst y (.fvar z) Γ₂) _ z t
          hz_notin_subst_Γ₂ hlk_tail
      exact MSubRed.pro hpv' hsb_z
    · -- yi ≠ y. Standard case: use subBinds_split_neq + insert_middle.
      rw [Term.subst_fvar_ne hyiy]
      have hsb_lifted : (Ctx.subst y (.fvar z) Γ₂ ++ Γ₁).subBinds yi
          (Term.subst y (.fvar z) t') :=
        subBinds_split_neq (s := .fvar z) hyiy hpvL hsb
      have hpv_big : Prevalid (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, t, .sub⟩ :: Γ₁) :=
        prevalid_rename_sub_head hyz hz_notin_Γ₁ hz_notin_Γ₂ hpvL
      have hpv_big_assoc :
          Prevalid (Ctx.subst y (.fvar z) Γ₂ ++ [⟨z, t, .sub⟩] ++ Γ₁) := by
        have heq : (Ctx.subst y (.fvar z) Γ₂ ++ [⟨z, t, .sub⟩] ++ Γ₁) =
            (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, t, .sub⟩ :: Γ₁) := by simp
        exact heq ▸ hpv_big
      have hsb' : (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, t, .sub⟩ :: Γ₁).subBinds yi
          (Term.subst y (.fvar z) t') := by
        have := Ctx.subBinds_insert_middle
          (Γ₁ := Ctx.subst y (.fvar z) Γ₂) (Δ := [⟨z, t, .sub⟩]) (Γ₂ := Γ₁)
          hpv_big_assoc hsb_lifted
        have heq_simp : (Ctx.subst y (.fvar z) Γ₂ ++ [⟨z, t, .sub⟩] ++ Γ₁) =
            (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, t, .sub⟩ :: Γ₁) := by simp
        exact heq_simp ▸ this
      exact MSubRed.pro hpv' hsb'
  | @top Γ st' u_ hpv hLCu hfv =>
    subst hΓ
    intro hz_notin_Γ₂
    have hpv' : PrevalidExt (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, t, .sub⟩ :: Γ₁)
        (Stack.subst y (.fvar z) st') :=
      prevalidExt_rename_sub_head hyz hz_notin_Γ₁ hz_notin_Γ₂ hpv
    have hLCu' : Term.LC (Term.subst y (.fvar z) u_) :=
      Term.subst_lc (Term.LC.fvar z) hLCu
    have hfv' :
        Term.fv (Term.subst y (.fvar z) u_) ⊆
          Ctx.dom (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, t, .sub⟩ :: Γ₁) := by
      intro w hw
      have hsub := Term.fv_subst_subset y (.fvar z) u_ hw
      rcases Finset.mem_union.mp hsub with hsd | hsd
      · rcases Finset.mem_sdiff.mp hsd with ⟨hwfv, hwne⟩
        have hw_in : w ∈ Ctx.dom (Γ₂ ++ ⟨y, t, .sub⟩ :: Γ₁) := hfv hwfv
        rw [Ctx.dom_append, Ctx.dom_cons] at hw_in
        show w ∈ Ctx.dom (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, t, .sub⟩ :: Γ₁)
        rw [Ctx.dom_append, Ctx.dom_subst, Ctx.dom_cons]
        rcases Finset.mem_union.mp hw_in with hΓ₂ | htail
        · exact Finset.mem_union.mpr (Or.inl hΓ₂)
        · rcases Finset.mem_insert.mp htail with hwy | hwΓ₁
          · exact absurd hwy (fun hh => hwne (by simp [hh]))
          · exact Finset.mem_union.mpr
              (Or.inr (Finset.mem_insert_of_mem hwΓ₁))
      · have hwz : w = z := by simpa [Term.fv] using hsd
        rw [hwz]
        show z ∈ Ctx.dom (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, t, .sub⟩ :: Γ₁)
        rw [Ctx.dom_append, Ctx.dom_subst, Ctx.dom_cons]
        exact Finset.mem_union.mpr
          (Or.inr (Finset.mem_insert_self _ _))
    show MSubRed (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, t, .sub⟩ :: Γ₁)
      (Stack.subst y (.fvar z) st')
      (Term.subst y (.fvar z) u_) (Term.subst y (.fvar z) .top)
    simp [Term.subst]
    exact MSubRed.top hpv' hLCu' hfv'
  | @equ Γ st' u_ v_ hpv heq =>
    subst hΓ
    intro hz_notin_Γ₂
    have hpv' : PrevalidExt (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, t, .sub⟩ :: Γ₁)
        (Stack.subst y (.fvar z) st') :=
      prevalidExt_rename_sub_head hyz hz_notin_Γ₁ hz_notin_Γ₂ hpv
    have heq' :=
      MEqRed.subst_yz_sub_head (Γ₂ := Γ₂) hyz hz_notin_Γ₁ hz_notin_Γ₂ heq
    exact MSubRed.equ hpv' heq'
  | @app Γ st' u_ u_' v_ hu hLCv hfvv ihu =>
    subst hΓ
    intro hz_notin_Γ₂
    have ihu' := ihu (Γ₂ := Γ₂) rfl hz_notin_Γ₂
    have hLCv' : Term.LC (Term.subst y (.fvar z) v_) :=
      Term.subst_lc (Term.LC.fvar z) hLCv
    have hfvv' :
        Term.fv (Term.subst y (.fvar z) v_) ⊆
          Ctx.dom (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, t, .sub⟩ :: Γ₁) := by
      intro w hw
      have hsub := Term.fv_subst_subset y (.fvar z) v_ hw
      rcases Finset.mem_union.mp hsub with hsd | hsd
      · rcases Finset.mem_sdiff.mp hsd with ⟨hwfv, hwne⟩
        have hw_in : w ∈ Ctx.dom (Γ₂ ++ ⟨y, t, .sub⟩ :: Γ₁) := hfvv hwfv
        rw [Ctx.dom_append, Ctx.dom_cons] at hw_in
        show w ∈ Ctx.dom (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, t, .sub⟩ :: Γ₁)
        rw [Ctx.dom_append, Ctx.dom_subst, Ctx.dom_cons]
        rcases Finset.mem_union.mp hw_in with hΓ₂ | htail
        · exact Finset.mem_union.mpr (Or.inl hΓ₂)
        · rcases Finset.mem_insert.mp htail with hwy | hwΓ₁
          · exact absurd hwy (fun hh => hwne (by simp [hh]))
          · exact Finset.mem_union.mpr
              (Or.inr (Finset.mem_insert_of_mem hwΓ₁))
      · have hwz : w = z := by simpa [Term.fv] using hsd
        rw [hwz]
        show z ∈ Ctx.dom (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, t, .sub⟩ :: Γ₁)
        rw [Ctx.dom_append, Ctx.dom_subst, Ctx.dom_cons]
        exact Finset.mem_union.mpr
          (Or.inr (Finset.mem_insert_self _ _))
    show MSubRed (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, t, .sub⟩ :: Γ₁)
      (Stack.subst y (.fvar z) st')
      (Term.subst y (.fvar z) (.app u_ v_)) (Term.subst y (.fvar z) (.app u_' v_))
    simp [Term.subst]
    refine MSubRed.app ?_ hLCv' hfvv'
    simpa using ihu'
  | @fun_ Γ tt bd bd' L hLCt hbody _hUni ihbody =>
    subst hΓ
    intro hz_notin_Γ₂
    show MSubRed (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, t, .sub⟩ :: Γ₁)
      (Stack.subst y (.fvar z) [])
      (Term.subst y (.fvar z) (.abs tt bd)) (Term.subst y (.fvar z) (.abs tt bd'))
    simp [Term.subst]
    refine MSubRed.fun_ (L ∪ {y} ∪ {z}) (Term.subst_lc (Term.LC.fvar z) hLCt) ?_ trivial
    intro yfresh hyfresh
    simp only [Finset.mem_union, Finset.mem_singleton, not_or] at hyfresh
    have hyfL : yfresh ∉ L := hyfresh.1.1
    have hyfy : yfresh ≠ y := hyfresh.1.2
    have hyfz : yfresh ≠ z := hyfresh.2
    have hz_notin_Γ₂' : z ∉ Ctx.dom (⟨yfresh, tt, .sub⟩ :: Γ₂) := by
      rw [Ctx.dom_cons]
      intro hmem
      rcases Finset.mem_insert.mp hmem with hzy | hzΓ
      · exact hyfz hzy.symm
      · exact hz_notin_Γ₂ hzΓ
    have ih_body :=
      ihbody yfresh hyfL (Γ₂ := ⟨yfresh, tt, .sub⟩ :: Γ₂) (by simp) hz_notin_Γ₂'
    rw [Term.subst_open_var (Ne.symm hyfy) (Term.LC.fvar z) bd,
        Term.subst_open_var (Ne.symm hyfy) (Term.LC.fvar z) bd'] at ih_body
    simpa [Ctx.subst, List.cons_append] using ih_body
  | @fOp Γ st' tt αi bd bd' L hLCt hbody _hUni ihbody =>
    subst hΓ
    intro hz_notin_Γ₂
    show MSubRed (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, t, .sub⟩ :: Γ₁)
      (Stack.subst y (.fvar z) (αi :: st'))
      (Term.subst y (.fvar z) (.abs tt bd)) (Term.subst y (.fvar z) (.abs tt bd'))
    rw [Stack.subst_cons]
    simp [Term.subst]
    refine MSubRed.fOp (L ∪ {y} ∪ {z}) (Term.subst_lc (Term.LC.fvar z) hLCt) ?_ trivial
    intro yfresh hyfresh
    simp only [Finset.mem_union, Finset.mem_singleton, not_or] at hyfresh
    have hyfL : yfresh ∉ L := hyfresh.1.1
    have hyfy : yfresh ≠ y := hyfresh.1.2
    have hyfz : yfresh ≠ z := hyfresh.2
    have hz_notin_Γ₂' : z ∉ Ctx.dom (⟨yfresh, αi, .equ⟩ :: Γ₂) := by
      rw [Ctx.dom_cons]
      intro hmem
      rcases Finset.mem_insert.mp hmem with hzy | hzΓ
      · exact hyfz hzy.symm
      · exact hz_notin_Γ₂ hzΓ
    have ih_body :=
      ihbody yfresh hyfL (Γ₂ := ⟨yfresh, αi, .equ⟩ :: Γ₂) (by simp) hz_notin_Γ₂'
    rw [Term.subst_open_var (Ne.symm hyfy) (Term.LC.fvar z) bd,
        Term.subst_open_var (Ne.symm hyfy) (Term.LC.fvar z) bd'] at ih_body
    simpa [Ctx.subst, List.cons_append] using ih_body

/-- **Renaming for `MSubRed` under a `.sub`-head binding.** Analogous to
`MEqRed.rename_sub`. **No** `fv body ⊆ Γ.dom` precondition required (uses
the new `subst_yz_sub_head` primitive instead of going through Lemmas
21/30). -/
noncomputable def MSubRed.rename_sub
    {Γ : Ctx} {s : Stack} {body body' t : Term} {y z : String}
    (hpvΓ : Prevalid Γ)
    (hLCt : Term.LC t) (hfvt : Term.fv t ⊆ Γ.dom)
    (hy_notin_Γ : y ∉ Γ.dom) (hz_notin_Γ : z ∉ Γ.dom)
    (hy_notin_body : y ∉ Term.fv body) (hy_notin_body' : y ∉ Term.fv body')
    (hy_notin_stack : ∀ α ∈ s, y ∉ Term.fv α)
    (h : MSubRed (⟨y, t, .sub⟩ :: Γ) s (body^[y]) (body'^[y])) :
    MSubRed (⟨z, t, .sub⟩ :: Γ) s (body^[z]) (body'^[z]) := by
  classical
  by_cases hyz : y = z
  · subst hyz; exact h
  have h_in_form : MSubRed (([] : Ctx) ++ ⟨y, t, .sub⟩ :: Γ) s (body^[y]) (body'^[y]) := by
    show MSubRed (⟨y, t, .sub⟩ :: Γ) s (body^[y]) (body'^[y]); exact h
  have hz_notin_empty : z ∉ Ctx.dom ([] : Ctx) := by simp [Ctx.dom]
  have h_subst :=
    MSubRed.subst_yz_sub_head (Γ₂ := ([] : Ctx)) hyz hz_notin_Γ hz_notin_empty h_in_form
  have hctx_eq :
      Ctx.subst y (.fvar z) ([] : Ctx) ++ (⟨z, t, .sub⟩ :: Γ) =
        ⟨z, t, .sub⟩ :: Γ := by simp
  have hstk_eq : Stack.subst y (.fvar z) s = s :=
    Stack.subst_fresh hy_notin_stack
  have hbody_eq : Term.subst y (.fvar z) (body^[y]) = body^[z] :=
    Term.subst_open_fresh hy_notin_body
  have hbody'_eq : Term.subst y (.fvar z) (body'^[y]) = body'^[z] :=
    Term.subst_open_fresh hy_notin_body'
  rw [hctx_eq, hstk_eq, hbody_eq, hbody'_eq] at h_subst
  exact h_subst

/-! ## §5. Renaming for MSubRed under an `.equ` head binding

Build via the `Ms-Equ` arm: an `MSubRed` derivation that's not merely
`Ms-Equ` of an `MEqRed` requires special handling. We mirror the
structure of `MEqRed.subst_yz_equ_head` for `MSubRed`'s constructors.
-/

/-- Specialized renaming substitution lemma for `MSubRed` under an
`.equ` head binding. Mirrors `MEqRed.subst_yz_equ_head`. -/
private noncomputable def MSubRed.subst_yz_equ_head
    {Γ₁ Γ₂ : Ctx} {st : Stack} {y z : String} {α u u' : Term}
    (hyz : y ≠ z)
    (hy_notin_α : y ∉ Term.fv α)
    (h : MSubRed (Γ₂ ++ ⟨y, α, .equ⟩ :: ⟨z, α, .equ⟩ :: Γ₁) st u u') :
    MSubRed (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, α, .equ⟩ :: Γ₁)
      (Stack.subst y (.fvar z) st)
      (Term.subst y (.fvar z) u) (Term.subst y (.fvar z) u') := by
  classical
  have hok : SubstOk (⟨z, α, .equ⟩ :: Γ₁) (.fvar z) := by
    refine ⟨Term.LC.fvar z, ?_⟩
    intro w hw
    have hwz : w = z := by simpa [Term.fv] using hw
    subst hwz
    rw [Ctx.dom_cons]; exact Finset.mem_insert_self _ _
  generalize hΓ : (Γ₂ ++ ⟨y, α, .equ⟩ :: ⟨z, α, .equ⟩ :: Γ₁) = Γ at h
  induction h generalizing Γ₂ with
  | @pro Γ st' yi t' hpv hsb =>
    subst hΓ
    have hpvL : Prevalid (Γ₂ ++ ⟨y, α, .equ⟩ :: ⟨z, α, .equ⟩ :: Γ₁) := extractPrevalid hpv
    have hpv' : PrevalidExt (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, α, .equ⟩ :: Γ₁)
        (Stack.subst y (.fvar z) st') :=
      Lemma_28_SubstPreservesPrevalid hpv hok
    by_cases hyiy : yi = y
    · -- yi = y. Only y-entry is .equ, not .sub: contradiction.
      subst hyiy
      exact (subBinds_at_equ_head_impossible hpvL hsb).elim
    · rw [Term.subst_fvar_ne hyiy]
      have hsb' : (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, α, .equ⟩ :: Γ₁).subBinds yi
          (Term.subst y (.fvar z) t') :=
        subBinds_split_equ (s := .fvar z) hyiy hpvL hsb
      exact MSubRed.pro hpv' hsb'
  | @top Γ st' u_ hpv hLCu hfv =>
    subst hΓ
    have hpv' : PrevalidExt (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, α, .equ⟩ :: Γ₁)
        (Stack.subst y (.fvar z) st') :=
      Lemma_28_SubstPreservesPrevalid hpv hok
    have hLCu' : Term.LC (Term.subst y (.fvar z) u_) :=
      Term.subst_lc (Term.LC.fvar z) hLCu
    have hfv' :
        Term.fv (Term.subst y (.fvar z) u_) ⊆
          Ctx.dom (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, α, .equ⟩ :: Γ₁) := by
      intro w hw
      have hsub := Term.fv_subst_subset y (.fvar z) u_ hw
      rcases Finset.mem_union.mp hsub with hsd | hsd
      · rcases Finset.mem_sdiff.mp hsd with ⟨hwfv, hwne⟩
        have hwΓ : w ∈ Ctx.dom (Γ₂ ++ ⟨y, α, .equ⟩ :: ⟨z, α, .equ⟩ :: Γ₁) :=
          hfv hwfv
        rw [Ctx.dom_append] at hwΓ
        rw [Ctx.dom_append, Ctx.dom_subst]
        rcases Finset.mem_union.mp hwΓ with hΓ₂ | htail
        · exact Finset.mem_union.mpr (Or.inl hΓ₂)
        · simp [Ctx.dom_cons] at htail
          rcases htail with hwy | hwz | hwΓ₁
          · exact absurd hwy (fun hh => hwne (by simp [hh]))
          · subst hwz
            apply Finset.mem_union.mpr; right
            simp [Ctx.dom_cons]
          · apply Finset.mem_union.mpr; right
            simp [Ctx.dom_cons]; exact Or.inr hwΓ₁
      · have hwz : w = z := by simpa [Term.fv] using hsd
        subst hwz
        rw [Ctx.dom_append, Ctx.dom_subst]
        apply Finset.mem_union.mpr; right
        simp [Ctx.dom_cons]
    show MSubRed (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, α, .equ⟩ :: Γ₁)
      (Stack.subst y (.fvar z) st')
      (Term.subst y (.fvar z) u_) (Term.subst y (.fvar z) .top)
    simp [Term.subst]
    exact MSubRed.top hpv' hLCu' hfv'
  | @equ Γ st' u_ v_ hpv heq =>
    subst hΓ
    have hpv' : PrevalidExt (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, α, .equ⟩ :: Γ₁)
        (Stack.subst y (.fvar z) st') :=
      Lemma_28_SubstPreservesPrevalid hpv hok
    have heq' :=
      MEqRed.subst_yz_equ_head (Γ₂ := Γ₂) hyz hy_notin_α heq
    exact MSubRed.equ hpv' heq'
  | @app Γ st' u_ u_' v_ hu hLCv hfvv ihu =>
    subst hΓ
    have ihu' := ihu (Γ₂ := Γ₂) rfl
    have hLCv' : Term.LC (Term.subst y (.fvar z) v_) :=
      Term.subst_lc (Term.LC.fvar z) hLCv
    have hfvv' :
        Term.fv (Term.subst y (.fvar z) v_) ⊆
          Ctx.dom (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, α, .equ⟩ :: Γ₁) := by
      intro w hw
      have hsub := Term.fv_subst_subset y (.fvar z) v_ hw
      rcases Finset.mem_union.mp hsub with hsd | hsd
      · rcases Finset.mem_sdiff.mp hsd with ⟨hwfv, hwne⟩
        have hwΓ : w ∈ Ctx.dom (Γ₂ ++ ⟨y, α, .equ⟩ :: ⟨z, α, .equ⟩ :: Γ₁) :=
          hfvv hwfv
        rw [Ctx.dom_append] at hwΓ
        rw [Ctx.dom_append, Ctx.dom_subst]
        rcases Finset.mem_union.mp hwΓ with hΓ₂ | htail
        · exact Finset.mem_union.mpr (Or.inl hΓ₂)
        · simp [Ctx.dom_cons] at htail
          rcases htail with hwy | hwz | hwΓ₁
          · exact absurd hwy (fun hh => hwne (by simp [hh]))
          · subst hwz
            apply Finset.mem_union.mpr; right
            simp [Ctx.dom_cons]
          · apply Finset.mem_union.mpr; right
            simp [Ctx.dom_cons]; exact Or.inr hwΓ₁
      · have hwz : w = z := by simpa [Term.fv] using hsd
        subst hwz
        rw [Ctx.dom_append, Ctx.dom_subst]
        apply Finset.mem_union.mpr; right
        simp [Ctx.dom_cons]
    show MSubRed (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, α, .equ⟩ :: Γ₁)
      (Stack.subst y (.fvar z) st')
      (Term.subst y (.fvar z) (.app u_ v_)) (Term.subst y (.fvar z) (.app u_' v_))
    simp [Term.subst]
    refine MSubRed.app ?_ hLCv' hfvv'
    simpa using ihu'
  | @fun_ Γ tt bd bd' L hLCt hbody _hUni ihbody =>
    subst hΓ
    show MSubRed (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, α, .equ⟩ :: Γ₁)
      (Stack.subst y (.fvar z) [])
      (Term.subst y (.fvar z) (.abs tt bd)) (Term.subst y (.fvar z) (.abs tt bd'))
    simp [Term.subst]
    refine MSubRed.fun_ (L ∪ {y}) (Term.subst_lc (Term.LC.fvar z) hLCt) ?_ trivial
    intro yfresh hyfresh
    simp [Finset.mem_union, Finset.mem_singleton] at hyfresh
    have hyfL : yfresh ∉ L := hyfresh.1
    have hyfy : yfresh ≠ y := hyfresh.2
    have ih_body := ihbody yfresh hyfL (Γ₂ := ⟨yfresh, tt, .sub⟩ :: Γ₂) (by simp)
    rw [Term.subst_open_var (Ne.symm hyfy) (Term.LC.fvar z) bd,
        Term.subst_open_var (Ne.symm hyfy) (Term.LC.fvar z) bd'] at ih_body
    simpa [Ctx.subst, List.cons_append] using ih_body
  | @fOp Γ st' tt αi bd bd' L hLCt hbody _hUni ihbody =>
    subst hΓ
    show MSubRed (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, α, .equ⟩ :: Γ₁)
      (Stack.subst y (.fvar z) (αi :: st'))
      (Term.subst y (.fvar z) (.abs tt bd)) (Term.subst y (.fvar z) (.abs tt bd'))
    rw [Stack.subst_cons]
    simp [Term.subst]
    refine MSubRed.fOp (L ∪ {y}) (Term.subst_lc (Term.LC.fvar z) hLCt) ?_ trivial
    intro yfresh hyfresh
    simp [Finset.mem_union, Finset.mem_singleton] at hyfresh
    have hyfL : yfresh ∉ L := hyfresh.1
    have hyfy : yfresh ≠ y := hyfresh.2
    have ih_body := ihbody yfresh hyfL (Γ₂ := ⟨yfresh, αi, .equ⟩ :: Γ₂) (by simp)
    rw [Term.subst_open_var (Ne.symm hyfy) (Term.LC.fvar z) bd,
        Term.subst_open_var (Ne.symm hyfy) (Term.LC.fvar z) bd'] at ih_body
    simpa [Ctx.subst, List.cons_append] using ih_body

/-- **Renaming for `MSubRed` under an `.equ`-head binding.** -/
noncomputable def MSubRed.rename_equ
    {Γ : Ctx} {s : Stack} {body body' α : Term} {y z : String}
    (hpvΓ : Prevalid Γ)
    (hLCα : Term.LC α) (hfvα : Term.fv α ⊆ Γ.dom)
    (hy_notin_Γ : y ∉ Γ.dom) (hz_notin_Γ : z ∉ Γ.dom)
    (hy_notin_body : y ∉ Term.fv body) (hy_notin_body' : y ∉ Term.fv body')
    (hfv_body : Term.fv body ⊆ Γ.dom) (hfv_body' : Term.fv body' ⊆ Γ.dom)
    (hy_notin_stack : ∀ β ∈ s, y ∉ Term.fv β)
    (h : MSubRed (⟨y, α, .equ⟩ :: Γ) s (body^[y]) (body'^[y])) :
    MSubRed (⟨z, α, .equ⟩ :: Γ) s (body^[z]) (body'^[z]) := by
  classical
  by_cases hyz : y = z
  · subst hyz; exact h
  have hy_notin_α : y ∉ Term.fv α := fv_notin_of_dom_notin hfvα hy_notin_Γ
  have hpvz : Prevalid (⟨z, α, .equ⟩ :: Γ) :=
    Prevalid.equ hpvΓ hz_notin_Γ hfvα hLCα
  have hyzdom : y ∉ Ctx.dom (⟨z, α, .equ⟩ :: Γ) := by
    rw [Ctx.dom_cons]
    intro hmem
    rcases Finset.mem_insert.mp hmem with hyz' | hyΓ
    · exact hyz hyz'
    · exact hy_notin_Γ hyΓ
  have hfvα_z : Term.fv α ⊆ Ctx.dom (⟨z, α, .equ⟩ :: Γ) := by
    intro w hw
    rw [Ctx.dom_cons]; exact Finset.mem_insert_of_mem (hfvα hw)
  have hpv_yz : Prevalid (⟨y, α, .equ⟩ :: ⟨z, α, .equ⟩ :: Γ) :=
    Prevalid.equ hpvz hyzdom hfvα_z hLCα
  have hfv_open_y : Term.fv (body^[y]) ⊆ Ctx.dom (⟨y, α, .equ⟩ :: Γ) := by
    intro w hw
    have hsub := Term.fv_open_subset 0 (.fvar y) body
    rw [Ctx.dom_cons]
    rcases Finset.mem_union.mp (hsub hw) with hwBody | hwY
    · exact Finset.mem_insert_of_mem (hfv_body hwBody)
    · have hwy : w = y := by simpa [Term.fv] using hwY
      subst hwy; exact Finset.mem_insert_self _ _
  have hpv_pre : Prevalid (([⟨y, α, .equ⟩] : Ctx) ++ Γ) := by
    show Prevalid (⟨y, α, .equ⟩ :: Γ)
    exact Prevalid.equ hpvΓ hy_notin_Γ hfvα hLCα
  have hpv_post : Prevalid (([⟨y, α, .equ⟩] : Ctx) ++ [⟨z, α, .equ⟩] ++ Γ) := by
    show Prevalid (⟨y, α, .equ⟩ :: ⟨z, α, .equ⟩ :: Γ); exact hpv_yz
  have h_weakened : MSubRed (([⟨y, α, .equ⟩] : Ctx) ++ [⟨z, α, .equ⟩] ++ Γ)
      s (body^[y]) (body'^[y]) := by
    have hh : MSubRed (([⟨y, α, .equ⟩] : Ctx) ++ Γ) s (body^[y]) (body'^[y]) := by
      show MSubRed (⟨y, α, .equ⟩ :: Γ) s (body^[y]) (body'^[y]); exact h
    have hfvU : Term.fv (body^[y]) ⊆ Ctx.dom (([⟨y, α, .equ⟩] : Ctx) ++ Γ) := by
      show Term.fv (body^[y]) ⊆ Ctx.dom (⟨y, α, .equ⟩ :: Γ); exact hfv_open_y
    exact Lemma_21_WeakeningMSubRed hpv_pre hfvU hpv_post hh
  have h_norm : MSubRed (([] : Ctx) ++ ⟨y, α, .equ⟩ :: ⟨z, α, .equ⟩ :: Γ)
      s (body^[y]) (body'^[y]) := by
    have heq : (([⟨y, α, .equ⟩] : Ctx) ++ [⟨z, α, .equ⟩] ++ Γ) =
        (([] : Ctx) ++ ⟨y, α, .equ⟩ :: ⟨z, α, .equ⟩ :: Γ) := by simp
    exact heq ▸ h_weakened
  have h_subst :=
    MSubRed.subst_yz_equ_head (Γ₂ := []) hyz hy_notin_α h_norm
  have hctx_eq :
      Ctx.subst y (.fvar z) ([] : Ctx) ++ (⟨z, α, .equ⟩ :: Γ) =
        ⟨z, α, .equ⟩ :: Γ := by simp
  have hstk_eq : Stack.subst y (.fvar z) s = s :=
    Stack.subst_fresh hy_notin_stack
  have hbody_eq : Term.subst y (.fvar z) (body^[y]) = body^[z] :=
    Term.subst_open_fresh hy_notin_body
  have hbody'_eq : Term.subst y (.fvar z) (body'^[y]) = body'^[z] :=
    Term.subst_open_fresh hy_notin_body'
  rw [hctx_eq, hstk_eq, hbody_eq, hbody'_eq] at h_subst
  exact h_subst

/-! ## §6. Renaming under `.equ`-head with **no** `fv body` precondition

The `MEqRed.rename_equ` / `MSubRed.rename_equ` provided in §3 / §5 require
`Term.fv body ⊆ Γ.dom` (because they go through `Lemma_22_Weakening` →
`Lemma_32_ReductionUnderSubst_Eq_OfEqu`). For consumers that do not have
that fv-bound (notably the `Lemma_2_inline_fOp_fOp` arm in
`Pss.Mpss.Diamond` and the `Ms-FOp` arm of `Lemma_24_NarrowingMSubRed`),
we provide a parallel set of renaming primitives that operate on the
non-doubled context `Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁` directly.

These were previously inlined as `private` copies in `Pss.Mpss.Diamond`
and `Pss.Mpss.Commutation`. They are extracted here (public, with an
underscore-prefixed flat name to avoid name clashes with Diamond's
existing `private` copies) so that consumers downstream of `Renaming`
in the import graph (`Narrowing`, `Diamond`, `Commutation`) can share
a single implementation.

Naming convention: leading `_` prefix marks these as internal-but-public
infrastructure; the consumers wrapping them are the load-bearing API. -/

/-- A `subBinds` lookup that succeeds implies the variable is in the
domain. (Sub-helper of `_MSubRed_rename_equ_loc` for the `Ms-Pro` arm.) -/
theorem _lookupSub_some_dom
    {Γ : Ctx} {x : String} {t : Term} (h : Γ.subBinds x t) : x ∈ Γ.dom := by
  induction Γ with
  | nil => simp [Ctx.subBinds, Ctx.lookupSub] at h
  | cons e rest ih =>
    rw [Ctx.subBinds, Ctx.lookupSub_cons] at h
    by_cases hex : e.name = x
    · simp [Ctx.dom_cons, hex]
    · simp [hex] at h
      simp [Ctx.dom_cons]
      exact Or.inr (ih h)

/-- `Prevalid` doubled-equ insertion: insert a fresh `⟨z, α, .equ⟩` entry
just below an existing `⟨y, α, .equ⟩` entry in a prevalid context.
(Sub-helper of `_PrevalidExt_insert_fresh_equ_mid`.) -/
noncomputable def _Prevalid_insert_fresh_equ_mid
    {Γ₁ Γ₂ : Ctx} {y z : String} {α : Term}
    (hyz : y ≠ z)
    (hz_notin_Γ₁ : z ∉ Γ₁.dom)
    (hz_notin_Γ₂ : z ∉ Γ₂.dom)
    (hpv : Prevalid (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁)) :
    Prevalid (Γ₂ ++ ⟨y, α, .equ⟩ :: ⟨z, α, .equ⟩ :: Γ₁) := by
  classical
  have hpv_inner : Prevalid (⟨y, α, .equ⟩ :: Γ₁) := Prevalid.outer hpv
  cases hpv_inner with
  | equ hpvΓ₁ hy_notin_Γ₁ hfvα hLCα =>
    have hpv_z : Prevalid (⟨z, α, .equ⟩ :: Γ₁) :=
      Prevalid.equ hpvΓ₁ hz_notin_Γ₁ hfvα hLCα
    have hyz_zα : y ∉ Ctx.dom (⟨z, α, .equ⟩ :: Γ₁) := by
      rw [Ctx.dom_cons]
      intro hmem
      rcases Finset.mem_insert.mp hmem with hyz' | hyΓ
      · exact hyz hyz'
      · exact hy_notin_Γ₁ hyΓ
    have hfvα_z : Term.fv α ⊆ Ctx.dom (⟨z, α, .equ⟩ :: Γ₁) := by
      intro w hw; rw [Ctx.dom_cons]
      exact Finset.mem_insert_of_mem (hfvα hw)
    have hpv_yz : Prevalid (⟨y, α, .equ⟩ :: ⟨z, α, .equ⟩ :: Γ₁) :=
      Prevalid.equ hpv_z hyz_zα hfvα_z hLCα
    induction Γ₂ with
    | nil => simpa using hpv_yz
    | cons e rest ih =>
      have hpv'' : Prevalid (e :: (rest ++ ⟨y, α, .equ⟩ :: Γ₁)) := by
        simpa using hpv
      have hpv_rest : Prevalid (rest ++ ⟨y, α, .equ⟩ :: Γ₁) := hpv''.tail
      have hz_notin_rest : z ∉ Ctx.dom rest := by
        intro hmem; apply hz_notin_Γ₂
        rw [Ctx.dom_cons]; exact Finset.mem_insert_of_mem hmem
      have ih' := ih hz_notin_rest hpv_rest
      have he_notin : e.name ∉ Ctx.dom (rest ++ ⟨y, α, .equ⟩ :: Γ₁) := by
        cases hpv'' with
        | sub _ hen _ _ => exact hen
        | equ _ hen _ _ => exact hen
      have he_notin' : e.name ∉
          Ctx.dom (rest ++ ⟨y, α, .equ⟩ :: ⟨z, α, .equ⟩ :: Γ₁) := by
        intro hmem
        rw [Ctx.dom_append, Ctx.dom_cons, Ctx.dom_cons] at hmem
        rw [Ctx.dom_append, Ctx.dom_cons] at he_notin
        rcases Finset.mem_union.mp hmem with hr | htail
        · apply he_notin; exact Finset.mem_union.mpr (Or.inl hr)
        · rcases Finset.mem_insert.mp htail with hey | hrest_x
          · apply he_notin
            exact Finset.mem_union.mpr
              (Or.inr (Finset.mem_insert.mpr (Or.inl hey)))
          · rcases Finset.mem_insert.mp hrest_x with hez | hΓ
            · apply hz_notin_Γ₂
              rw [show z = e.name from hez.symm]
              exact Finset.mem_insert_self _ _
            · apply he_notin
              exact Finset.mem_union.mpr
                (Or.inr (Finset.mem_insert.mpr (Or.inr hΓ)))
      cases hpv'' with
      | @sub _ name u' _ _ hfve hlce =>
        have hfve' : Term.fv u' ⊆
            Ctx.dom (rest ++ ⟨y, α, .equ⟩ :: ⟨z, α, .equ⟩ :: Γ₁) := by
          intro w hw
          have hw' := hfve hw
          rw [Ctx.dom_append, Ctx.dom_cons] at hw'
          rw [Ctx.dom_append, Ctx.dom_cons, Ctx.dom_cons]
          rcases Finset.mem_union.mp hw' with hr | htail
          · exact Finset.mem_union.mpr (Or.inl hr)
          · rcases Finset.mem_insert.mp htail with hey | hΓ
            · exact Finset.mem_union.mpr
                (Or.inr (Finset.mem_insert.mpr (Or.inl hey)))
            · exact Finset.mem_union.mpr
                (Or.inr (Finset.mem_insert.mpr
                  (Or.inr (Finset.mem_insert.mpr (Or.inr hΓ)))))
        exact Prevalid.sub ih' he_notin' hfve' hlce
      | @equ _ name αe _ _ hfve hlce =>
        have hfve' : Term.fv αe ⊆
            Ctx.dom (rest ++ ⟨y, α, .equ⟩ :: ⟨z, α, .equ⟩ :: Γ₁) := by
          intro w hw
          have hw' := hfve hw
          rw [Ctx.dom_append, Ctx.dom_cons] at hw'
          rw [Ctx.dom_append, Ctx.dom_cons, Ctx.dom_cons]
          rcases Finset.mem_union.mp hw' with hr | htail
          · exact Finset.mem_union.mpr (Or.inl hr)
          · rcases Finset.mem_insert.mp htail with hey | hΓ
            · exact Finset.mem_union.mpr
                (Or.inr (Finset.mem_insert.mpr (Or.inl hey)))
            · exact Finset.mem_union.mpr
                (Or.inr (Finset.mem_insert.mpr
                  (Or.inr (Finset.mem_insert.mpr (Or.inr hΓ)))))
        exact Prevalid.equ ih' he_notin' hfve' hlce

/-- `PrevalidExt` analog of `_Prevalid_insert_fresh_equ_mid`: insert a
fresh `⟨z, α, .equ⟩` entry just below `⟨y, α, .equ⟩` in a `PrevalidExt`. -/
noncomputable def _PrevalidExt_insert_fresh_equ_mid
    {Γ₁ Γ₂ : Ctx} {st : Stack} {y z : String} {α : Term}
    (hyz : y ≠ z)
    (hz_notin_Γ₁ : z ∉ Γ₁.dom)
    (hz_notin_Γ₂ : z ∉ Γ₂.dom)
    (hpv : PrevalidExt (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁) st) :
    PrevalidExt (Γ₂ ++ ⟨y, α, .equ⟩ :: ⟨z, α, .equ⟩ :: Γ₁) st := by
  induction st with
  | nil =>
    cases hpv with
    | nil hpvL =>
      exact PrevalidExt.nil
        (_Prevalid_insert_fresh_equ_mid hyz hz_notin_Γ₁ hz_notin_Γ₂ hpvL)
  | cons αs srest ihst =>
    cases hpv with
    | cons hpvr hLCαs hfvαs =>
      have ihst' := ihst hpvr
      have hfvαs' : Term.fv αs ⊆
          Ctx.dom (Γ₂ ++ ⟨y, α, .equ⟩ :: ⟨z, α, .equ⟩ :: Γ₁) := by
        intro w hw
        have hwΓ : w ∈ Ctx.dom (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁) := hfvαs hw
        rw [Ctx.dom_append, Ctx.dom_cons] at hwΓ
        rw [Ctx.dom_append, Ctx.dom_cons, Ctx.dom_cons]
        rcases Finset.mem_union.mp hwΓ with hΓ₂' | htail
        · exact Finset.mem_union.mpr (Or.inl hΓ₂')
        · rcases Finset.mem_insert.mp htail with hwy | hwΓ₁
          · exact Finset.mem_union.mpr
              (Or.inr (Finset.mem_insert.mpr (Or.inl hwy)))
          · exact Finset.mem_union.mpr
              (Or.inr (Finset.mem_insert.mpr
                (Or.inr (Finset.mem_insert.mpr (Or.inr hwΓ₁)))))
      exact PrevalidExt.cons ihst' hLCαs hfvαs'

/-- `Ctx.lookupEqu` success implies the key is in the domain.
(Sub-helper of `_MEqRed_rename_equ_loc` for the `Me-Pro` arm.) -/
lemma _lookupEqu_some_mem_dom {Γ : Ctx} {x : String} {α : Term}
    (h : Γ.lookupEqu x = some α) : x ∈ Γ.dom := by
  induction Γ with
  | nil => simp [Ctx.lookupEqu] at h
  | cons e rest ih =>
    rw [Ctx.lookupEqu_cons] at h
    by_cases hex : e.name = x
    · simp [Ctx.dom_cons, hex]
    · simp [hex] at h
      simp [Ctx.dom_cons]
      exact Or.inr (ih h)

/-- Lift an `equBinds yi β'` lookup past an inserted middle `⟨z, α, .equ⟩`
entry, for `yi ≠ z`. -/
theorem _lookupEqu_lift_middle
    {Γ₁ Γ₂ : Ctx} {yi z : String} {α β' : Term}
    (hyiz : yi ≠ z)
    (h : (Γ₂ ++ Γ₁).lookupEqu yi = some β') :
    (Γ₂ ++ ⟨z, α, .equ⟩ :: Γ₁).lookupEqu yi = some β' := by
  induction Γ₂ with
  | nil =>
    simpa [Ctx.lookupEqu_cons, Ne.symm hyiz] using h
  | cons e rest ih =>
    rw [List.cons_append, Ctx.lookupEqu_cons] at h ⊢
    by_cases hex : e.name = yi
    · simp [hex] at h ⊢
      cases hkind : e.kind with
      | sub => simp [hkind] at h
      | equ => simp [hkind] at h ⊢; exact h
    · simp [hex] at h ⊢
      exact ih h

/-- `MEqRed` renaming under an `.equ` head, non-doubled context, no fv body
precondition. Mirrors the structure of `subst_yz_equ_head` (§3) but
operates on the non-doubled context `Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁` directly,
producing a derivation in the renamed context
`Γ₂.subst y (.fvar z) ++ ⟨z, α, .equ⟩ :: Γ₁`. -/
noncomputable def _MEqRed_rename_equ_loc
    {Γ₁ Γ₂ : Ctx} {st : Stack} {y z : String} {α u u' : Term}
    (hyz : y ≠ z)
    (hz_notin_Γ₁ : z ∉ Γ₁.dom)
    (hz_notin_Γ₂ : z ∉ Γ₂.dom)
    (hy_notin_α : y ∉ Term.fv α)
    (h : MEqRed (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁) st u u') :
    MEqRed (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, α, .equ⟩ :: Γ₁)
      (Stack.subst y (.fvar z) st)
      (Term.subst y (.fvar z) u) (Term.subst y (.fvar z) u') := by
  classical
  have hok : SubstOk (⟨z, α, .equ⟩ :: Γ₁) (.fvar z) := by
    refine ⟨Term.LC.fvar z, ?_⟩
    intro w hw
    have hwz : w = z := by simpa [Term.fv] using hw
    subst hwz
    rw [Ctx.dom_cons]; exact Finset.mem_insert_self _ _
  generalize hΓ : (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁) = Γ at h
  induction h generalizing Γ₂ with
  | @pro Γ st' yi β β' hpv heq hβ ihβ =>
    subst hΓ
    have hpvL : Prevalid (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁) := extractPrevalid hpv
    have hpv_doubled :=
      _PrevalidExt_insert_fresh_equ_mid hyz hz_notin_Γ₁ hz_notin_Γ₂ hpv
    have hpv' : PrevalidExt (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, α, .equ⟩ :: Γ₁)
        (Stack.subst y (.fvar z) st') :=
      Lemma_28_SubstPreservesPrevalid (Γ₂ := Γ₂) (Γ₁ := ⟨z, α, .equ⟩ :: Γ₁)
        (x := y) (t := α) (s := .fvar z) (k := .equ) hpv_doubled hok
    by_cases hyiy : yi = y
    · have heq_y : (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁).equBinds y β := hyiy ▸ heq
      have hβα : β = α := equBinds_at_equ_head_unique hpvL heq_y
      have ihβ_app := ihβ (Γ₂ := Γ₂) hz_notin_Γ₂ rfl
      rw [hβα] at ihβ_app
      have hα_subst : Term.subst y (.fvar z) α = α := Term.subst_fresh hy_notin_α
      rw [hα_subst] at ihβ_app
      have hz_eqbinds :
          (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, α, .equ⟩ :: Γ₁).equBinds z α := by
        have hz_notin_subst_Γ₂ : z ∉ (Ctx.subst y (.fvar z) Γ₂).dom := by
          rw [Ctx.dom_subst]; exact hz_notin_Γ₂
        have hlk_tail : Ctx.lookupEqu (⟨z, α, .equ⟩ :: Γ₁) z = some α := by
          simp [Ctx.lookupEqu, Ctx.lookupEqu_cons]
        show Ctx.lookupEqu (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, α, .equ⟩ :: Γ₁) z = some α
        exact Ctx.lookupEqu_append_right (Ctx.subst y (.fvar z) Γ₂) _ z α
          hz_notin_subst_Γ₂ hlk_tail
      have hfvar_eq : Term.subst y (.fvar z) (.fvar yi) = .fvar z := by
        rw [hyiy]; simp [Term.subst]
      rw [hfvar_eq]
      exact MEqRed.pro hpv' hz_eqbinds ihβ_app
    · rw [Term.subst_fvar_ne hyiy]
      have heq_un : (Ctx.subst y (.fvar z) Γ₂ ++ Γ₁).equBinds yi
          (Term.subst y (.fvar z) β) :=
        equBinds_split_equ (s := .fvar z) hyiy hpvL heq
      have hyi_in_orig : yi ∈ (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁).dom :=
        _lookupEqu_some_mem_dom heq
      have hz_notin_orig : z ∉ (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁).dom := by
        rw [Ctx.dom_append, Ctx.dom_cons]
        intro hmem
        rcases Finset.mem_union.mp hmem with hΓ₂' | htail
        · exact hz_notin_Γ₂ hΓ₂'
        · rcases Finset.mem_insert.mp htail with hzy | hzΓ₁
          · exact hyz hzy.symm
          · exact hz_notin_Γ₁ hzΓ₁
      have hyiz : yi ≠ z := by
        intro hh; subst hh; exact hz_notin_orig hyi_in_orig
      have heq' : (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, α, .equ⟩ :: Γ₁).equBinds yi
          (Term.subst y (.fvar z) β) :=
        _lookupEqu_lift_middle hyiz heq_un
      exact MEqRed.pro hpv' heq' (ihβ (Γ₂ := Γ₂) hz_notin_Γ₂ rfl)
  | @bet Γ st' tBound v0 v0' bd bd' L hLCt hbody _hUni hv ihbody ihv =>
    subst hΓ
    have hLCfz : Term.LC (.fvar z) := Term.LC.fvar z
    have hsubst_open : Term.subst y (.fvar z) (Term.opening v0' bd') =
        Term.opening (Term.subst y (.fvar z) v0') (Term.subst y (.fvar z) bd') := by
      simp [Term.opening, Term.subst_open hLCfz]
    show MEqRed (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, α, .equ⟩ :: Γ₁)
      (Stack.subst y (.fvar z) st')
      (Term.subst y (.fvar z) (.app (.abs tBound bd) v0))
      (Term.subst y (.fvar z) (Term.opening v0' bd'))
    rw [hsubst_open]
    show MEqRed (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, α, .equ⟩ :: Γ₁)
      (Stack.subst y (.fvar z) st')
      (.app (.abs (Term.subst y (.fvar z) tBound) (Term.subst y (.fvar z) bd))
            (Term.subst y (.fvar z) v0))
      (Term.opening (Term.subst y (.fvar z) v0') (Term.subst y (.fvar z) bd'))
    refine MEqRed.bet (L ∪ {y}) (Term.subst_lc hLCfz hLCt) ?_ trivial ?_
    · intro yfresh hyfresh
      simp [Finset.mem_union, Finset.mem_singleton] at hyfresh
      have hyfL : yfresh ∉ L := hyfresh.1
      have hyfy : yfresh ≠ y := hyfresh.2
      have ih_body := ihbody yfresh hyfL (Γ₂ := Γ₂) hz_notin_Γ₂ rfl
      rw [Term.subst_open_var (Ne.symm hyfy) hLCfz bd,
          Term.subst_open_var (Ne.symm hyfy) hLCfz bd'] at ih_body
      exact ih_body
    · have ihv' := ihv (Γ₂ := Γ₂) hz_notin_Γ₂ rfl
      simpa using ihv'
  | @top Γ st' hpv =>
    subst hΓ
    have hpv_doubled :=
      _PrevalidExt_insert_fresh_equ_mid hyz hz_notin_Γ₁ hz_notin_Γ₂ hpv
    have hpv' : PrevalidExt (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, α, .equ⟩ :: Γ₁)
        (Stack.subst y (.fvar z) st') :=
      Lemma_28_SubstPreservesPrevalid (Γ₂ := Γ₂) (Γ₁ := ⟨z, α, .equ⟩ :: Γ₁)
        (x := y) (t := α) (s := .fvar z) (k := .equ) hpv_doubled hok
    exact MEqRed.top hpv'
  | @app Γ st' u_ u_' v_ v_' hu hv ihu ihv =>
    subst hΓ
    have ihu' := ihu (Γ₂ := Γ₂) hz_notin_Γ₂ rfl
    have ihv' := ihv (Γ₂ := Γ₂) hz_notin_Γ₂ rfl
    simp at ihu'
    refine MEqRed.app ?_ ?_
    · exact ihu'
    · simpa using ihv'
  | @var Γ st' yi hpv =>
    subst hΓ
    have hpv_doubled :=
      _PrevalidExt_insert_fresh_equ_mid hyz hz_notin_Γ₁ hz_notin_Γ₂ hpv
    have hpv' : PrevalidExt (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, α, .equ⟩ :: Γ₁)
        (Stack.subst y (.fvar z) st') :=
      Lemma_28_SubstPreservesPrevalid (Γ₂ := Γ₂) (Γ₁ := ⟨z, α, .equ⟩ :: Γ₁)
        (x := y) (t := α) (s := .fvar z) (k := .equ) hpv_doubled hok
    by_cases hyiy : yi = y
    · have hsubst_eq : Term.subst y (.fvar z) (.fvar yi) = .fvar z := by
        rw [hyiy]; simp [Term.subst]
      rw [hsubst_eq]
      have hLCz : Term.LC (.fvar z) := Term.LC.fvar z
      have hfvz : Term.fv (.fvar z) ⊆
          Ctx.dom (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, α, .equ⟩ :: Γ₁) := by
        intro w hw
        have hwz : w = z := by simpa [Term.fv] using hw
        subst hwz
        rw [Ctx.dom_append, Ctx.dom_subst, Ctx.dom_cons]
        exact Finset.mem_union.mpr (Or.inr (Finset.mem_insert_self _ _))
      exact MEqRed.refl hpv' hLCz hfvz
    · rw [Term.subst_fvar_ne hyiy]
      exact MEqRed.var hpv'
  | @fun_ Γ tt tt' bd bd' L ht hbody _hUni iht ihbody =>
    subst hΓ
    show MEqRed (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, α, .equ⟩ :: Γ₁)
      (Stack.subst y (.fvar z) [])
      (.abs (Term.subst y (.fvar z) tt) (Term.subst y (.fvar z) bd))
      (.abs (Term.subst y (.fvar z) tt') (Term.subst y (.fvar z) bd'))
    refine MEqRed.fun_ (L ∪ {y} ∪ {z}) ?_ ?_ trivial
    · have iht' := iht (Γ₂ := Γ₂) hz_notin_Γ₂ rfl
      simpa using iht'
    · intro yfresh hyfresh
      simp only [Finset.mem_union, Finset.mem_singleton, not_or] at hyfresh
      obtain ⟨⟨hyfL, hyfy⟩, hyfz⟩ := hyfresh
      have hz_notin_Γ₂' : z ∉ Ctx.dom (⟨yfresh, tt, .sub⟩ :: Γ₂) := by
        rw [Ctx.dom_cons]
        intro hmem
        rcases Finset.mem_insert.mp hmem with hzy | hzΓ₂
        · exact hyfz hzy.symm
        · exact hz_notin_Γ₂ hzΓ₂
      have ih_body := ihbody yfresh hyfL (Γ₂ := ⟨yfresh, tt, .sub⟩ :: Γ₂)
        hz_notin_Γ₂' (by simp)
      have hLCfz : Term.LC (.fvar z) := Term.LC.fvar z
      rw [Term.subst_open_var (Ne.symm hyfy) hLCfz bd,
          Term.subst_open_var (Ne.symm hyfy) hLCfz bd'] at ih_body
      simpa [Ctx.subst, List.cons_append] using ih_body
  | @tAp Γ st' u_ hpv hLCu hfv =>
    subst hΓ
    have hpv_doubled :=
      _PrevalidExt_insert_fresh_equ_mid hyz hz_notin_Γ₁ hz_notin_Γ₂ hpv
    have hpv' : PrevalidExt (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, α, .equ⟩ :: Γ₁)
        (Stack.subst y (.fvar z) st') :=
      Lemma_28_SubstPreservesPrevalid (Γ₂ := Γ₂) (Γ₁ := ⟨z, α, .equ⟩ :: Γ₁)
        (x := y) (t := α) (s := .fvar z) (k := .equ) hpv_doubled hok
    have hLCu' : Term.LC (Term.subst y (.fvar z) u_) :=
      Term.subst_lc (Term.LC.fvar z) hLCu
    have hfv' :
        Term.fv (Term.subst y (.fvar z) u_) ⊆
          Ctx.dom (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, α, .equ⟩ :: Γ₁) := by
      intro w hw
      have hsub := Term.fv_subst_subset y (.fvar z) u_ hw
      rcases Finset.mem_union.mp hsub with hsd | hsd
      · rcases Finset.mem_sdiff.mp hsd with ⟨hwfv, hwne⟩
        have hwΓ : w ∈ Ctx.dom (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁) := hfv hwfv
        rw [Ctx.dom_append, Ctx.dom_cons] at hwΓ
        rw [Ctx.dom_append, Ctx.dom_subst, Ctx.dom_cons]
        rcases Finset.mem_union.mp hwΓ with hΓ₂' | htail
        · exact Finset.mem_union.mpr (Or.inl hΓ₂')
        · rcases Finset.mem_insert.mp htail with hwy | hwΓ₁
          · exact absurd hwy (fun hh => hwne (by simp [hh]))
          · apply Finset.mem_union.mpr
            right; exact Finset.mem_insert_of_mem hwΓ₁
      · have hwz : w = z := by simpa [Term.fv] using hsd
        subst hwz
        rw [Ctx.dom_append, Ctx.dom_subst, Ctx.dom_cons]
        apply Finset.mem_union.mpr
        right; exact Finset.mem_insert_self _ _
    show MEqRed (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, α, .equ⟩ :: Γ₁)
      (Stack.subst y (.fvar z) st')
      (Term.subst y (.fvar z) (.app .top u_)) (Term.subst y (.fvar z) .top)
    simp [Term.subst]
    exact MEqRed.tAp hpv' hLCu' hfv'
  | @fOp Γ st' tt tt' αi bd bd' L ht hbody _hUni iht ihbody =>
    subst hΓ
    show MEqRed (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, α, .equ⟩ :: Γ₁)
      (Stack.subst y (.fvar z) (αi :: st'))
      (.abs (Term.subst y (.fvar z) tt) (Term.subst y (.fvar z) bd))
      (.abs (Term.subst y (.fvar z) tt') (Term.subst y (.fvar z) bd'))
    rw [Stack.subst_cons]
    refine MEqRed.fOp (L ∪ {y} ∪ {z}) ?_ ?_ trivial
    · have iht' := iht (Γ₂ := Γ₂) hz_notin_Γ₂ rfl
      simpa using iht'
    · intro yfresh hyfresh
      simp only [Finset.mem_union, Finset.mem_singleton, not_or] at hyfresh
      obtain ⟨⟨hyfL, hyfy⟩, hyfz⟩ := hyfresh
      have hz_notin_Γ₂' : z ∉ Ctx.dom (⟨yfresh, αi, .equ⟩ :: Γ₂) := by
        rw [Ctx.dom_cons]
        intro hmem
        rcases Finset.mem_insert.mp hmem with hzy | hzΓ₂
        · exact hyfz hzy.symm
        · exact hz_notin_Γ₂ hzΓ₂
      have ih_body := ihbody yfresh hyfL (Γ₂ := ⟨yfresh, αi, .equ⟩ :: Γ₂)
        hz_notin_Γ₂' (by simp)
      have hLCfz : Term.LC (.fvar z) := Term.LC.fvar z
      rw [Term.subst_open_var (Ne.symm hyfy) hLCfz bd,
          Term.subst_open_var (Ne.symm hyfy) hLCfz bd'] at ih_body
      simpa [Ctx.subst, List.cons_append] using ih_body

/-- Helper for the `Ms-Pro` arm of `_MSubRed_rename_equ_loc`: lift a
`subBinds` lookup past a freshly inserted middle `⟨z, α, .equ⟩` entry. -/
theorem _lookupSub_lift_middle_equ
    {Γ₁ Γ₂ : Ctx} {yi z : String} {α t' : Term}
    (hyiz : yi ≠ z)
    (h : (Γ₂ ++ Γ₁).subBinds yi t') :
    (Γ₂ ++ ⟨z, α, .equ⟩ :: Γ₁).subBinds yi t' := by
  induction Γ₂ with
  | nil =>
    show Ctx.lookupSub (⟨z, α, .equ⟩ :: Γ₁) yi = some t'
    rw [Ctx.lookupSub_cons]
    simp [Ne.symm hyiz]
    exact h
  | cons e rest ih =>
    show Ctx.lookupSub (e :: (rest ++ ⟨z, α, .equ⟩ :: Γ₁)) yi = some t'
    have h' : Ctx.lookupSub (e :: (rest ++ Γ₁)) yi = some t' := h
    rw [Ctx.lookupSub_cons] at h' ⊢
    by_cases hex : e.name = yi
    · simp [hex] at h' ⊢
      cases hkind : e.kind with
      | sub => simp [hkind] at h' ⊢; exact h'
      | equ => simp [hkind] at h'
    · simp [hex] at h' ⊢
      exact ih h'

/-- `MSubRed` renaming under an `.equ` head, non-doubled context, no fv body
precondition. Mirrors `_MEqRed_rename_equ_loc` for `MSubRed`. -/
noncomputable def _MSubRed_rename_equ_loc
    {Γ₁ Γ₂ : Ctx} {st : Stack} {y z : String} {α u u' : Term}
    (hyz : y ≠ z)
    (hz_notin_Γ₁ : z ∉ Γ₁.dom)
    (hz_notin_Γ₂ : z ∉ Γ₂.dom)
    (hy_notin_α : y ∉ Term.fv α)
    (h : MSubRed (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁) st u u') :
    MSubRed (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, α, .equ⟩ :: Γ₁)
      (Stack.subst y (.fvar z) st)
      (Term.subst y (.fvar z) u) (Term.subst y (.fvar z) u') := by
  classical
  have hok : SubstOk (⟨z, α, .equ⟩ :: Γ₁) (.fvar z) := by
    refine ⟨Term.LC.fvar z, ?_⟩
    intro w hw
    have hwz : w = z := by simpa [Term.fv] using hw
    subst hwz
    rw [Ctx.dom_cons]; exact Finset.mem_insert_self _ _
  generalize hΓ : (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁) = Γ at h
  induction h generalizing Γ₂ with
  | @pro Γ st' yi t' hpv hsb =>
    subst hΓ
    have hpvL : Prevalid (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁) := extractPrevalid hpv
    have hpv_doubled :=
      _PrevalidExt_insert_fresh_equ_mid hyz hz_notin_Γ₁ hz_notin_Γ₂ hpv
    have hpv' : PrevalidExt (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, α, .equ⟩ :: Γ₁)
        (Stack.subst y (.fvar z) st') :=
      Lemma_28_SubstPreservesPrevalid (Γ₂ := Γ₂) (Γ₁ := ⟨z, α, .equ⟩ :: Γ₁)
        (x := y) (t := α) (s := .fvar z) (k := .equ) hpv_doubled hok
    by_cases hyiy : yi = y
    · -- yi = y. Only y-entry is .equ, not .sub: contradiction.
      subst hyiy
      exact (subBinds_at_equ_head_impossible hpvL hsb).elim
    · rw [Term.subst_fvar_ne hyiy]
      have hsb_split : (Ctx.subst y (.fvar z) Γ₂ ++ Γ₁).subBinds yi
          (Term.subst y (.fvar z) t') :=
        subBinds_split_equ (s := .fvar z) hyiy hpvL hsb
      -- Now lift past the inserted ⟨z, α, .equ⟩.
      have hyi_in_orig : yi ∈ (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁).dom := by
        -- subBinds lookup implies in dom
        have hlk : (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁).lookupSub yi = some t' := hsb
        exact _lookupSub_some_dom hsb
      have hz_notin_orig : z ∉ (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁).dom := by
        rw [Ctx.dom_append, Ctx.dom_cons]
        intro hmem
        rcases Finset.mem_union.mp hmem with hΓ₂' | htail
        · exact hz_notin_Γ₂ hΓ₂'
        · rcases Finset.mem_insert.mp htail with hzy | hzΓ₁
          · exact hyz hzy.symm
          · exact hz_notin_Γ₁ hzΓ₁
      have hyiz : yi ≠ z := by
        intro hh; subst hh; exact hz_notin_orig hyi_in_orig
      -- Lift the subBinds past the ⟨z, α, .equ⟩ head.
      have hsb' : (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, α, .equ⟩ :: Γ₁).subBinds yi
          (Term.subst y (.fvar z) t') :=
        _lookupSub_lift_middle_equ hyiz hsb_split
      exact MSubRed.pro hpv' hsb'
  | @top Γ st' u_ hpv hLCu hfv =>
    subst hΓ
    have hpv_doubled :=
      _PrevalidExt_insert_fresh_equ_mid hyz hz_notin_Γ₁ hz_notin_Γ₂ hpv
    have hpv' : PrevalidExt (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, α, .equ⟩ :: Γ₁)
        (Stack.subst y (.fvar z) st') :=
      Lemma_28_SubstPreservesPrevalid (Γ₂ := Γ₂) (Γ₁ := ⟨z, α, .equ⟩ :: Γ₁)
        (x := y) (t := α) (s := .fvar z) (k := .equ) hpv_doubled hok
    have hLCu' : Term.LC (Term.subst y (.fvar z) u_) :=
      Term.subst_lc (Term.LC.fvar z) hLCu
    have hfv' :
        Term.fv (Term.subst y (.fvar z) u_) ⊆
          Ctx.dom (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, α, .equ⟩ :: Γ₁) := by
      intro w hw
      have hsub := Term.fv_subst_subset y (.fvar z) u_ hw
      rcases Finset.mem_union.mp hsub with hsd | hsd
      · rcases Finset.mem_sdiff.mp hsd with ⟨hwfv, hwne⟩
        have hwΓ : w ∈ Ctx.dom (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁) := hfv hwfv
        rw [Ctx.dom_append, Ctx.dom_cons] at hwΓ
        rw [Ctx.dom_append, Ctx.dom_subst, Ctx.dom_cons]
        rcases Finset.mem_union.mp hwΓ with hΓ₂' | htail
        · exact Finset.mem_union.mpr (Or.inl hΓ₂')
        · rcases Finset.mem_insert.mp htail with hwy | hwΓ₁
          · exact absurd hwy (fun hh => hwne (by simp [hh]))
          · apply Finset.mem_union.mpr
            right; exact Finset.mem_insert_of_mem hwΓ₁
      · have hwz : w = z := by simpa [Term.fv] using hsd
        subst hwz
        rw [Ctx.dom_append, Ctx.dom_subst, Ctx.dom_cons]
        apply Finset.mem_union.mpr
        right; exact Finset.mem_insert_self _ _
    show MSubRed (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, α, .equ⟩ :: Γ₁)
      (Stack.subst y (.fvar z) st')
      (Term.subst y (.fvar z) u_) (Term.subst y (.fvar z) .top)
    simp [Term.subst]
    exact MSubRed.top hpv' hLCu' hfv'
  | @equ Γ st' u_ v_ hpv heq =>
    subst hΓ
    have hpv_doubled :=
      _PrevalidExt_insert_fresh_equ_mid hyz hz_notin_Γ₁ hz_notin_Γ₂ hpv
    have hpv' : PrevalidExt (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, α, .equ⟩ :: Γ₁)
        (Stack.subst y (.fvar z) st') :=
      Lemma_28_SubstPreservesPrevalid (Γ₂ := Γ₂) (Γ₁ := ⟨z, α, .equ⟩ :: Γ₁)
        (x := y) (t := α) (s := .fvar z) (k := .equ) hpv_doubled hok
    have heq' :=
      _MEqRed_rename_equ_loc (Γ₂ := Γ₂) hyz hz_notin_Γ₁ hz_notin_Γ₂ hy_notin_α heq
    exact MSubRed.equ hpv' heq'
  | @app Γ st' u_ u_' v_ hu hLCv hfvv ihu =>
    subst hΓ
    have ihu' := ihu (Γ₂ := Γ₂) hz_notin_Γ₂ rfl
    have hLCv' : Term.LC (Term.subst y (.fvar z) v_) :=
      Term.subst_lc (Term.LC.fvar z) hLCv
    have hfvv' :
        Term.fv (Term.subst y (.fvar z) v_) ⊆
          Ctx.dom (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, α, .equ⟩ :: Γ₁) := by
      intro w hw
      have hsub := Term.fv_subst_subset y (.fvar z) v_ hw
      rcases Finset.mem_union.mp hsub with hsd | hsd
      · rcases Finset.mem_sdiff.mp hsd with ⟨hwfv, hwne⟩
        have hwΓ : w ∈ Ctx.dom (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁) := hfvv hwfv
        rw [Ctx.dom_append, Ctx.dom_cons] at hwΓ
        rw [Ctx.dom_append, Ctx.dom_subst, Ctx.dom_cons]
        rcases Finset.mem_union.mp hwΓ with hΓ₂' | htail
        · exact Finset.mem_union.mpr (Or.inl hΓ₂')
        · rcases Finset.mem_insert.mp htail with hwy | hwΓ₁
          · exact absurd hwy (fun hh => hwne (by simp [hh]))
          · apply Finset.mem_union.mpr
            right; exact Finset.mem_insert_of_mem hwΓ₁
      · have hwz : w = z := by simpa [Term.fv] using hsd
        subst hwz
        rw [Ctx.dom_append, Ctx.dom_subst, Ctx.dom_cons]
        apply Finset.mem_union.mpr
        right; exact Finset.mem_insert_self _ _
    show MSubRed (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, α, .equ⟩ :: Γ₁)
      (Stack.subst y (.fvar z) st')
      (Term.subst y (.fvar z) (.app u_ v_)) (Term.subst y (.fvar z) (.app u_' v_))
    simp [Term.subst]
    refine MSubRed.app ?_ hLCv' hfvv'
    simpa using ihu'
  | @fun_ Γ tt bd bd' L hLCt hbody _hUni ihbody =>
    subst hΓ
    show MSubRed (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, α, .equ⟩ :: Γ₁)
      (Stack.subst y (.fvar z) [])
      (Term.subst y (.fvar z) (.abs tt bd)) (Term.subst y (.fvar z) (.abs tt bd'))
    simp [Term.subst]
    refine MSubRed.fun_ (L ∪ {y} ∪ {z}) (Term.subst_lc (Term.LC.fvar z) hLCt) ?_ trivial
    intro yfresh hyfresh
    simp only [Finset.mem_union, Finset.mem_singleton, not_or] at hyfresh
    obtain ⟨⟨hyfL, hyfy⟩, hyfz⟩ := hyfresh
    have hz_notin_Γ₂' : z ∉ Ctx.dom (⟨yfresh, tt, .sub⟩ :: Γ₂) := by
      rw [Ctx.dom_cons]
      intro hmem
      rcases Finset.mem_insert.mp hmem with hzy | hzΓ₂
      · exact hyfz hzy.symm
      · exact hz_notin_Γ₂ hzΓ₂
    have ih_body := ihbody yfresh hyfL (Γ₂ := ⟨yfresh, tt, .sub⟩ :: Γ₂)
      hz_notin_Γ₂' (by simp)
    rw [Term.subst_open_var (Ne.symm hyfy) (Term.LC.fvar z) bd,
        Term.subst_open_var (Ne.symm hyfy) (Term.LC.fvar z) bd'] at ih_body
    simpa [Ctx.subst, List.cons_append] using ih_body
  | @fOp Γ st' tt αi bd bd' L hLCt hbody _hUni ihbody =>
    subst hΓ
    show MSubRed (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, α, .equ⟩ :: Γ₁)
      (Stack.subst y (.fvar z) (αi :: st'))
      (Term.subst y (.fvar z) (.abs tt bd)) (Term.subst y (.fvar z) (.abs tt bd'))
    rw [Stack.subst_cons]
    simp [Term.subst]
    refine MSubRed.fOp (L ∪ {y} ∪ {z}) (Term.subst_lc (Term.LC.fvar z) hLCt) ?_ trivial
    intro yfresh hyfresh
    simp only [Finset.mem_union, Finset.mem_singleton, not_or] at hyfresh
    obtain ⟨⟨hyfL, hyfy⟩, hyfz⟩ := hyfresh
    have hz_notin_Γ₂' : z ∉ Ctx.dom (⟨yfresh, αi, .equ⟩ :: Γ₂) := by
      rw [Ctx.dom_cons]
      intro hmem
      rcases Finset.mem_insert.mp hmem with hzy | hzΓ₂
      · exact hyfz hzy.symm
      · exact hz_notin_Γ₂ hzΓ₂
    have ih_body := ihbody yfresh hyfL (Γ₂ := ⟨yfresh, αi, .equ⟩ :: Γ₂)
      hz_notin_Γ₂' (by simp)
    rw [Term.subst_open_var (Ne.symm hyfy) (Term.LC.fvar z) bd,
        Term.subst_open_var (Ne.symm hyfy) (Term.LC.fvar z) bd'] at ih_body
    simpa [Ctx.subst, List.cons_append] using ih_body

/-- Wrapper: rename `MSubRed` head `.equ`-binding's name `y → z` in
`⟨y, α, .equ⟩ :: Γ`, no fv body precondition. -/
noncomputable def _MSubRed_rename_equ_no_fv
    {Γ : Ctx} {s : Stack} {body body' α : Term} {y z : String}
    (hyz : y ≠ z)
    (hy_notin_Γ : y ∉ Γ.dom) (hz_notin_Γ : z ∉ Γ.dom)
    (hy_notin_α : y ∉ Term.fv α)
    (hy_notin_body : y ∉ Term.fv body) (hy_notin_body' : y ∉ Term.fv body')
    (hy_notin_stack : ∀ β ∈ s, y ∉ Term.fv β)
    (h : MSubRed (⟨y, α, .equ⟩ :: Γ) s (body^[y]) (body'^[y])) :
    MSubRed (⟨z, α, .equ⟩ :: Γ) s (body^[z]) (body'^[z]) := by
  classical
  have hz_notin_empty : z ∉ Ctx.dom ([] : Ctx) := by simp [Ctx.dom]
  have h_in : MSubRed (([] : Ctx) ++ ⟨y, α, .equ⟩ :: Γ) s
      (body^[y]) (body'^[y]) := by simpa using h
  have h_subst :=
    _MSubRed_rename_equ_loc (Γ₂ := []) (Γ₁ := Γ) hyz hz_notin_Γ hz_notin_empty
      hy_notin_α h_in
  have hctx_eq :
      Ctx.subst y (.fvar z) ([] : Ctx) ++ (⟨z, α, .equ⟩ :: Γ) =
        ⟨z, α, .equ⟩ :: Γ := by simp
  have hstk_eq : Stack.subst y (.fvar z) s = s :=
    Stack.subst_fresh hy_notin_stack
  have hbody_eq : Term.subst y (.fvar z) (body^[y]) = body^[z] :=
    Term.subst_open_fresh hy_notin_body
  have hbody'_eq : Term.subst y (.fvar z) (body'^[y]) = body'^[z] :=
    Term.subst_open_fresh hy_notin_body'
  rw [hctx_eq, hstk_eq, hbody_eq, hbody'_eq] at h_subst
  exact h_subst

/-- Wrapper: rename `MEqRed` head `.equ`-binding's name `y → z` in
`⟨y, α, .equ⟩ :: Γ`, no fv body precondition. -/
noncomputable def _MEqRed_rename_equ_no_fv
    {Γ : Ctx} {s : Stack} {body body' α : Term} {y z : String}
    (hyz : y ≠ z)
    (hy_notin_Γ : y ∉ Γ.dom) (hz_notin_Γ : z ∉ Γ.dom)
    (hy_notin_α : y ∉ Term.fv α)
    (hy_notin_body : y ∉ Term.fv body) (hy_notin_body' : y ∉ Term.fv body')
    (hy_notin_stack : ∀ β ∈ s, y ∉ Term.fv β)
    (h : MEqRed (⟨y, α, .equ⟩ :: Γ) s (body^[y]) (body'^[y])) :
    MEqRed (⟨z, α, .equ⟩ :: Γ) s (body^[z]) (body'^[z]) := by
  classical
  have hz_notin_empty : z ∉ Ctx.dom ([] : Ctx) := by simp [Ctx.dom]
  have h_in : MEqRed (([] : Ctx) ++ ⟨y, α, .equ⟩ :: Γ) s
      (body^[y]) (body'^[y]) := by simpa using h
  have h_subst :=
    _MEqRed_rename_equ_loc (Γ₂ := []) (Γ₁ := Γ) hyz hz_notin_Γ hz_notin_empty
      hy_notin_α h_in
  have hctx_eq :
      Ctx.subst y (.fvar z) ([] : Ctx) ++ (⟨z, α, .equ⟩ :: Γ) =
        ⟨z, α, .equ⟩ :: Γ := by simp
  have hstk_eq : Stack.subst y (.fvar z) s = s :=
    Stack.subst_fresh hy_notin_stack
  have hbody_eq : Term.subst y (.fvar z) (body^[y]) = body^[z] :=
    Term.subst_open_fresh hy_notin_body
  have hbody'_eq : Term.subst y (.fvar z) (body'^[y]) = body'^[z] :=
    Term.subst_open_fresh hy_notin_body'
  rw [hctx_eq, hstk_eq, hbody_eq, hbody'_eq] at h_subst
  exact h_subst

/-! ## §7. Stray-variable renaming functor on derivations

Phase 1 of the architectural lever to unblock the β-residual axioms
(per `CLAUDE.md` "next big architectural lever" and rule 5a).

The `rename_sub` / `rename_equ` lemmas of §2-§6 rename a binder name `y`
that appears at the top of `Γ`. The **stray-variable** version takes a
derivation in plain `Γ` and renames `y → z` where BOTH `y` and `z` are
*outside* `Γ.dom` (and so are not bound anywhere in the context).

This is exactly the case that the β-residual proofs need: when
discharging the Me-Bet/Ms-App grid in Lemma 1 / Lemma 2, the
"alpha-equivariance" ingredient reduces to: given a body derivation at
some fresh `y`, produce a body derivation at any other fresh `z`. Both
`y` and `z` are stray w.r.t. the surrounding `Γ`.

### Why this is provable (and why naive alpha-equivariance is not)

The reverted commit `4145292` shipped `avoidsPro_alpha_equiv` which
claimed `avoidsPro (hbody y₁ _) x = avoidsPro (hbody y₂ _) x` for an
arbitrary `hbody : ∀ y ∉ L, MEqRed _ _ _ _`. That statement is FALSE:
`hbody` is an arbitrary function and can branch on its input. The
counterexample `hbody y _ := if y = "foo" then h_with_pro_y else h_var`
has different `avoidsPro` values across witnesses.

`rename_stray` sidesteps this by being a CONCRETE construction (not an
arbitrary function): we BUILD the renamed derivation by structural
recursion. The companion `avoidsPro_rename_stray` (below) is provably
true because both sides recurse on the SAME derivation tree shape.

### Strategy

We use the same `Γ₂ ++ ⟨y, ⋯⟩ :: Γ₁` decomposition as the §3-§5
helpers BUT with no actual `⟨y, …⟩` head binding. Instead we observe
that when `y ∉ Γ.dom`, every constructor that mentions `y` (which can
only be `.fvar y` inside terms or via `MEqRed.var` / `MEqRed.pro`) has
a clean substitution rule:

* `MEqRed.var yi`: `yi` itself is unconstrained at `var`-level, so we
  case-split on `yi = y`. If `yi = y`, we need `MEqRed Γ s (.fvar z)
  (.fvar z)`, which is `MEqRed.var hpv'` (using the same `hpv'` since
  the substitution is the identity on Γ).
* `MEqRed.pro yi`: by `equBinds yi α` we have `yi ∈ Γ.dom`, hence
  `yi ≠ y`. Also `α` has `fv α ⊆ Γ.dom`, hence `y ∉ fv α` and
  `subst y (.fvar z) α = α`.
-/

/-- `Term.subst y (.fvar y) e = e` for any term `e`. The substitution
of a variable for itself is the identity. -/
private theorem _Term_subst_self_id (y : String) (e : Term) :
    Term.subst y (.fvar y) e = e := by
  induction e with
  | bvar _ => rfl
  | fvar x =>
    by_cases h : x = y
    · simp [Term.subst, h]
    · simp [Term.subst, h]
  | top => rfl
  | abs t b iht ihb => simp [Term.subst, iht, ihb]
  | app t s iht ihs => simp [Term.subst, iht, ihs]

/-- `Stack.subst y (.fvar y) s = s`. -/
private theorem _Stack_subst_self_id (y : String) (s : Stack) :
    Stack.subst y (.fvar y) s = s := by
  induction s with
  | nil => rfl
  | cons α tail ih => rw [Stack.subst_cons, _Term_subst_self_id, ih]

/-- Free variables of an entry's bound term are contained in the
context's domain (when the context is prevalid). Used to discharge
"y ∉ entry.bound.fv" obligations from "y ∉ Γ.dom". -/
private theorem _Prevalid_fv_entry_subset_dom {Γ : Ctx} (h : Prevalid Γ) :
    ∀ e ∈ Γ, Term.fv e.bound ⊆ Γ.dom := by
  induction h with
  | empty => intro e he; cases he
  | @sub Γ' y t hΓ' _hy hfv _hLC ih =>
    intro e he
    rcases List.mem_cons.mp he with he | he
    · subst he
      intro w hw
      rw [Ctx.dom_cons]
      exact Finset.mem_insert_of_mem (hfv hw)
    · intro w hw
      have := ih e he hw
      rw [Ctx.dom_cons]
      exact Finset.mem_insert_of_mem this
  | @equ Γ' y α hΓ' _hy hfv _hLC ih =>
    intro e he
    rcases List.mem_cons.mp he with he | he
    · subst he
      intro w hw
      rw [Ctx.dom_cons]
      exact Finset.mem_insert_of_mem (hfv hw)
    · intro w hw
      have := ih e he hw
      rw [Ctx.dom_cons]
      exact Finset.mem_insert_of_mem this

/-- If `y ∉ Γ.dom`, substitution of `y` is the identity on `Γ`. -/
private theorem _Ctx_subst_id_of_stray {Γ : Ctx} {y : String} {u : Term}
    (hpv : Prevalid Γ) (hy : y ∉ Γ.dom) :
    Ctx.subst y u Γ = Γ := by
  apply Ctx.subst_fresh
  intro e he
  exact fun h => hy (_Prevalid_fv_entry_subset_dom hpv e he h)

/-- If `y ∉ Γ.dom`, every stack entry's `fv` excludes `y`, and so
substitution is the identity on the stack. -/
private theorem _Stack_subst_id_of_stray {Γ : Ctx} {st : Stack}
    {y : String} {u : Term}
    (hpv : PrevalidExt Γ st) (hy : y ∉ Γ.dom) :
    Stack.subst y u st = st := by
  apply Stack.subst_fresh
  induction hpv with
  | nil _ => intro α hα; cases hα
  | @cons _ β _ hLCβ hfvβ ih =>
    intro α hα
    rcases List.mem_cons.mp hα with hα | hα
    · subst hα; intro h; exact hy (hfvβ h)
    · exact ih α hα

/-- `Ms-Pro yi` cannot have `yi = y` when `y ∉ Γ.dom`: the lookup would
require `y ∈ Γ.dom`. -/
private theorem _subBinds_in_dom {Γ : Ctx} {y : String} {t : Term}
    (h : Γ.subBinds y t) : y ∈ Γ.dom := _lookupSub_some_dom h

/-- `Me-Pro yi` cannot have `yi = y` when `y ∉ Γ.dom`. -/
private theorem _equBinds_in_dom {Γ : Ctx} {y : String} {α : Term}
    (h : Γ.equBinds y α) : y ∈ Γ.dom := _lookupEqu_some_mem_dom h

/-! ### Helper: equBinds, subBinds preserved under whole-context substitution

When we substitute `y → s` over the whole context Γ pointwise (without
removing any binding), an `equBinds yi α` lookup becomes `equBinds yi
(subst y s α)` — the names are unchanged, only the bound terms are
renamed. -/

theorem _equBinds_subst_pointwise {Γ : Ctx} {yi : String} {α : Term}
    (y : String) (s : Term) (h : Γ.equBinds yi α) :
    (Ctx.subst y s Γ).equBinds yi (Term.subst y s α) := by
  induction Γ with
  | nil => simp [Ctx.equBinds, Ctx.lookupEqu] at h
  | cons e rest ih =>
    show Ctx.lookupEqu (⟨e.name, Term.subst y s e.bound, e.kind⟩ :: Ctx.subst y s rest) yi
        = some (Term.subst y s α)
    have h' : Ctx.lookupEqu (e :: rest) yi = some α := h
    rw [Ctx.lookupEqu_cons] at h' ⊢
    by_cases hex : e.name = yi
    · simp [hex] at h' ⊢
      cases hkind : e.kind with
      | sub => simp [hkind] at h'
      | equ =>
        simp [hkind] at h' ⊢
        subst h'; rfl
    · simp [hex] at h' ⊢
      exact ih h'

theorem _subBinds_subst_pointwise {Γ : Ctx} {yi : String} {t : Term}
    (y : String) (s : Term) (h : Γ.subBinds yi t) :
    (Ctx.subst y s Γ).subBinds yi (Term.subst y s t) := by
  induction Γ with
  | nil => simp [Ctx.subBinds, Ctx.lookupSub] at h
  | cons e rest ih =>
    show Ctx.lookupSub (⟨e.name, Term.subst y s e.bound, e.kind⟩ :: Ctx.subst y s rest) yi
        = some (Term.subst y s t)
    have h' : Ctx.lookupSub (e :: rest) yi = some t := h
    rw [Ctx.lookupSub_cons] at h' ⊢
    by_cases hex : e.name = yi
    · simp [hex] at h' ⊢
      cases hkind : e.kind with
      | equ => simp [hkind] at h'
      | sub =>
        simp [hkind] at h' ⊢
        subst h'; rfl
    · simp [hex] at h' ⊢
      exact ih h'

/-! ### Helper: Prevalid preservation under SubstOk-style substitution

When `y` is stray (`y ∉ Γ.dom`), the substitution `subst y (.fvar z) Γ`
is the identity. Prevalidity is preserved trivially (since we're
substituting nothing). -/

private noncomputable def _Prevalid_subst_stray
    {Γ : Ctx} {y z : String} (hpv : Prevalid Γ) (hy_notin : y ∉ Γ.dom) :
    Prevalid (Ctx.subst y (.fvar z) Γ) := by
  rw [_Ctx_subst_id_of_stray hpv hy_notin]; exact hpv

private noncomputable def _PrevalidExt_subst_stray
    {Γ : Ctx} {st : Stack} {y z : String}
    (hpv : PrevalidExt Γ st) (hy_notin : y ∉ Γ.dom) :
    PrevalidExt (Ctx.subst y (.fvar z) Γ) (Stack.subst y (.fvar z) st) := by
  rw [_Ctx_subst_id_of_stray (extractPrevalid hpv) hy_notin,
      _Stack_subst_id_of_stray hpv hy_notin]
  exact hpv

/-! ### Helper: in-the-extended-context Prevalid for binder cases

When the body recursion extends Γ by `⟨yfresh, β, .sub⟩` (or `.equ`),
we need `Prevalid` of the substituted extended context for the body's
`hpv'` argument. The substitution renames `β` to `subst y (.fvar z) β`
in the new entry; Γ itself stays unchanged (since `y ∉ Γ.dom`). -/

/-- Core renaming for `MEqRed` (stray-pair version), substituting the
WHOLE context. The wrapper `MEqRed.rename_stray` then unfolds
`Ctx.subst y (.fvar z) Γ = Γ` and `Stack.subst y (.fvar z) s = s` via
the identity facts above (using `Prevalid Γ` extracted from `h`).

We carry `y ∉ Γ.dom` as a hypothesis (not `z ∉ Γ.dom`, which is only
needed at the wrapper level for stack-identity simplification). The
`y ∉ Γ.dom` hypothesis is propagated through binder cases by
extending. The `pro`/`var` arms case-split on `yi = y`. -/
noncomputable def MEqRed.subst_yz_stray
    {Γ : Ctx} {st : Stack} {y z : String} {u u' : Term}
    (hyz : y ≠ z)
    (hy_notin_Γ : y ∉ Γ.dom)
    (h : MEqRed Γ st u u') :
    MEqRed (Ctx.subst y (.fvar z) Γ) (Stack.subst y (.fvar z) st)
      (Term.subst y (.fvar z) u) (Term.subst y (.fvar z) u') := by
  classical
  revert hy_notin_Γ
  induction h with
  | @pro Γ st' yi α α' hpv heq hα ihα =>
    intro hy_notin_Γ
    have hpvL : Prevalid Γ := extractPrevalid hpv
    have hyi_dom : yi ∈ Γ.dom := _equBinds_in_dom heq
    have hyiy : yi ≠ y := fun hh => hy_notin_Γ (hh ▸ hyi_dom)
    have hpv' : PrevalidExt (Ctx.subst y (.fvar z) Γ) (Stack.subst y (.fvar z) st') :=
      _PrevalidExt_subst_stray hpv hy_notin_Γ
    rw [Term.subst_fvar_ne hyiy]
    have heq' : (Ctx.subst y (.fvar z) Γ).equBinds yi (Term.subst y (.fvar z) α) :=
      _equBinds_subst_pointwise y (.fvar z) heq
    exact MEqRed.pro hpv' heq' (ihα hy_notin_Γ)
  | @bet Γ st' tBound v0 v0' bd bd' L hLCt hbody _hUni hv ihbody ihv =>
    intro hy_notin_Γ
    have hLCfz : Term.LC (.fvar z) := Term.LC.fvar z
    have hsubst_open : Term.subst y (.fvar z) (Term.opening v0' bd') =
        Term.opening (Term.subst y (.fvar z) v0') (Term.subst y (.fvar z) bd') := by
      simp [Term.opening, Term.subst_open hLCfz]
    show MEqRed (Ctx.subst y (.fvar z) Γ) (Stack.subst y (.fvar z) st')
      (Term.subst y (.fvar z) (.app (.abs tBound bd) v0))
      (Term.subst y (.fvar z) (Term.opening v0' bd'))
    rw [hsubst_open]
    show MEqRed (Ctx.subst y (.fvar z) Γ) (Stack.subst y (.fvar z) st')
      (.app (.abs (Term.subst y (.fvar z) tBound) (Term.subst y (.fvar z) bd))
            (Term.subst y (.fvar z) v0))
      (Term.opening (Term.subst y (.fvar z) v0') (Term.subst y (.fvar z) bd'))
    refine MEqRed.bet (L ∪ {y} ∪ {z}) (Term.subst_lc hLCfz hLCt) ?_ trivial ?_
    · intro yfresh hyfresh
      simp only [Finset.mem_union, Finset.mem_singleton, not_or] at hyfresh
      obtain ⟨⟨hyfL, hyfy⟩, hyfz⟩ := hyfresh
      -- Bet's body recurses at the same Γ (no extension), so reuse hy_notin_Γ.
      have ih_body := ihbody yfresh hyfL hy_notin_Γ
      rw [Term.subst_open_var (Ne.symm hyfy) hLCfz bd,
          Term.subst_open_var (Ne.symm hyfy) hLCfz bd'] at ih_body
      exact ih_body
    · exact ihv hy_notin_Γ
  | @top Γ st' hpv =>
    intro hy_notin_Γ
    have hpv' : PrevalidExt (Ctx.subst y (.fvar z) Γ) (Stack.subst y (.fvar z) st') :=
      _PrevalidExt_subst_stray hpv hy_notin_Γ
    show MEqRed (Ctx.subst y (.fvar z) Γ) (Stack.subst y (.fvar z) st')
      (Term.subst y (.fvar z) .top) (Term.subst y (.fvar z) .top)
    simp [Term.subst]
    exact MEqRed.top hpv'
  | @app Γ st' u_ u_' v_ v_' hu hv ihu ihv =>
    intro hy_notin_Γ
    show MEqRed (Ctx.subst y (.fvar z) Γ) (Stack.subst y (.fvar z) st')
      (Term.subst y (.fvar z) (.app u_ v_)) (Term.subst y (.fvar z) (.app u_' v_'))
    simp [Term.subst]
    refine MEqRed.app ?_ ?_
    · have ihu' := ihu hy_notin_Γ
      simpa using ihu'
    · exact ihv hy_notin_Γ
  | @var Γ st' yi hpv =>
    intro hy_notin_Γ
    have hpv' : PrevalidExt (Ctx.subst y (.fvar z) Γ) (Stack.subst y (.fvar z) st') :=
      _PrevalidExt_subst_stray hpv hy_notin_Γ
    by_cases hyiy : yi = y
    · -- yi = y: the substituted target is .fvar z. Use MEqRed.var with .fvar z.
      have hsubst_eq : Term.subst y (.fvar z) (.fvar yi) = .fvar z := by
        rw [hyiy]; simp [Term.subst]
      rw [hsubst_eq]
      exact MEqRed.var hpv'
    · rw [Term.subst_fvar_ne hyiy]
      exact MEqRed.var hpv'
  | @fun_ Γ tt tt' bd bd' L ht hbody _hUni iht ihbody =>
    intro hy_notin_Γ
    show MEqRed (Ctx.subst y (.fvar z) Γ) (Stack.subst y (.fvar z) [])
      (Term.subst y (.fvar z) (.abs tt bd)) (Term.subst y (.fvar z) (.abs tt' bd'))
    simp [Term.subst]
    refine MEqRed.fun_ (L ∪ {y} ∪ {z}) ?_ ?_ trivial
    · have iht' := iht hy_notin_Γ
      simpa using iht'
    · intro yfresh hyfresh
      simp only [Finset.mem_union, Finset.mem_singleton, not_or] at hyfresh
      obtain ⟨⟨hyfL, hyfy⟩, hyfz⟩ := hyfresh
      have hy_notin_Γ' : y ∉ Ctx.dom (⟨yfresh, tt, .sub⟩ :: Γ) := by
        rw [Ctx.dom_cons]
        intro hmem
        rcases Finset.mem_insert.mp hmem with hyy | hyΓ
        · exact hyfy hyy.symm
        · exact hy_notin_Γ hyΓ
      have ih_body := ihbody yfresh hyfL hy_notin_Γ'
      have hLCfz : Term.LC (.fvar z) := Term.LC.fvar z
      rw [Term.subst_open_var (Ne.symm hyfy) hLCfz bd,
          Term.subst_open_var (Ne.symm hyfy) hLCfz bd'] at ih_body
      simpa [Ctx.subst, List.cons_append] using ih_body
  | @tAp Γ st' u_ hpv hLCu hfv =>
    intro hy_notin_Γ
    have hpv' : PrevalidExt (Ctx.subst y (.fvar z) Γ) (Stack.subst y (.fvar z) st') :=
      _PrevalidExt_subst_stray hpv hy_notin_Γ
    have hLCu' : Term.LC (Term.subst y (.fvar z) u_) :=
      Term.subst_lc (Term.LC.fvar z) hLCu
    have hfv' : Term.fv (Term.subst y (.fvar z) u_) ⊆
        Ctx.dom (Ctx.subst y (.fvar z) Γ) := by
      rw [Ctx.dom_subst]
      intro w hw
      have hsub := Term.fv_subst_subset y (.fvar z) u_ hw
      rcases Finset.mem_union.mp hsub with hsd | hsd
      · rcases Finset.mem_sdiff.mp hsd with ⟨hwfv, _⟩
        exact hfv hwfv
      · -- hsd : w ∈ fv (.fvar z), so w = z. Use the fact that y ∉ fv u_ (from hfv +
        -- hy_notin_Γ) to conclude that subst y (.fvar z) u_ = u_, so the .fvar-z branch
        -- of the fv_subst_subset breakdown is actually impossible — except we can also
        -- close out by noting w ∈ fv u_ then.
        have hy_notin_u : y ∉ Term.fv u_ := fun h' => hy_notin_Γ (hfv h')
        have hu_eq : Term.subst y (.fvar z) u_ = u_ := Term.subst_fresh hy_notin_u
        rw [hu_eq] at hw
        exact hfv hw
    show MEqRed (Ctx.subst y (.fvar z) Γ) (Stack.subst y (.fvar z) st')
      (Term.subst y (.fvar z) (.app .top u_)) (Term.subst y (.fvar z) .top)
    simp [Term.subst]
    exact MEqRed.tAp hpv' hLCu' hfv'
  | @fOp Γ st' tt tt' αi bd bd' L ht hbody _hUni iht ihbody =>
    intro hy_notin_Γ
    show MEqRed (Ctx.subst y (.fvar z) Γ) (Stack.subst y (.fvar z) (αi :: st'))
      (Term.subst y (.fvar z) (.abs tt bd)) (Term.subst y (.fvar z) (.abs tt' bd'))
    rw [Stack.subst_cons]
    simp [Term.subst]
    refine MEqRed.fOp (L ∪ {y} ∪ {z}) ?_ ?_ trivial
    · have iht' := iht hy_notin_Γ
      simpa using iht'
    · intro yfresh hyfresh
      simp only [Finset.mem_union, Finset.mem_singleton, not_or] at hyfresh
      obtain ⟨⟨hyfL, hyfy⟩, hyfz⟩ := hyfresh
      have hy_notin_Γ' : y ∉ Ctx.dom (⟨yfresh, αi, .equ⟩ :: Γ) := by
        rw [Ctx.dom_cons]
        intro hmem
        rcases Finset.mem_insert.mp hmem with hyy | hyΓ
        · exact hyfy hyy.symm
        · exact hy_notin_Γ hyΓ
      have ih_body := ihbody yfresh hyfL hy_notin_Γ'
      have hLCfz : Term.LC (.fvar z) := Term.LC.fvar z
      rw [Term.subst_open_var (Ne.symm hyfy) hLCfz bd,
          Term.subst_open_var (Ne.symm hyfy) hLCfz bd'] at ih_body
      simpa [Ctx.subst, List.cons_append] using ih_body

/-- **Renaming for `MEqRed` over a stray-binder pair.** Given a derivation
in `Γ` and `y, z` both outside `Γ.dom`, produce the substituted derivation.

The substitution is the identity on `Γ` and the stack (since `y ∉ Γ.dom`),
but acts non-trivially on the source / target terms.

This is the principled replacement for the FALSE alpha-equivariance lemma
reverted in `12da200`: instead of a postulate that `avoidsPro` is
preserved across arbitrary cofinite-witness substitution, we provide a
CONCRETE renaming functor on derivations that we built by structural
recursion. The companion `avoidsPro_rename_stray` (below) is provably
true because both sides recurse on the same derivation tree shape. -/
noncomputable def MEqRed.rename_stray
    {Γ : Ctx} {s : Stack} {u v : Term}
    (hpvΓ : Prevalid Γ)
    (h : MEqRed Γ s u v)
    (y z : String) (hy : y ∉ Γ.dom) (hz : z ∉ Γ.dom) :
    MEqRed Γ
      (Stack.subst y (.fvar z) s)
      (Term.subst y (.fvar z) u) (Term.subst y (.fvar z) v) := by
  classical
  by_cases hyz : y = z
  · subst hyz
    rw [_Term_subst_self_id, _Term_subst_self_id, _Stack_subst_self_id]
    exact h
  · have h_sub := MEqRed.subst_yz_stray hyz hy h
    have hctx_eq : Ctx.subst y (.fvar z) Γ = Γ := _Ctx_subst_id_of_stray hpvΓ hy
    rw [hctx_eq] at h_sub
    exact h_sub

/-- Core renaming substitution lemma for `MSubRed` (stray version),
substituting the WHOLE context. Mirrors `MEqRed.subst_yz_stray`. -/
noncomputable def MSubRed.subst_yz_stray
    {Γ : Ctx} {st : Stack} {y z : String} {u u' : Term}
    (hyz : y ≠ z)
    (hy_notin_Γ : y ∉ Γ.dom)
    (h : MSubRed Γ st u u') :
    MSubRed (Ctx.subst y (.fvar z) Γ) (Stack.subst y (.fvar z) st)
      (Term.subst y (.fvar z) u) (Term.subst y (.fvar z) u') := by
  classical
  revert hy_notin_Γ
  induction h with
  | @pro Γ st' yi t' hpv hsb =>
    intro hy_notin_Γ
    have hpvL : Prevalid Γ := extractPrevalid hpv
    have hyi_dom : yi ∈ Γ.dom := _subBinds_in_dom hsb
    have hyiy : yi ≠ y := fun hh => hy_notin_Γ (hh ▸ hyi_dom)
    have hpv' : PrevalidExt (Ctx.subst y (.fvar z) Γ) (Stack.subst y (.fvar z) st') :=
      _PrevalidExt_subst_stray hpv hy_notin_Γ
    rw [Term.subst_fvar_ne hyiy]
    have hsb' : (Ctx.subst y (.fvar z) Γ).subBinds yi (Term.subst y (.fvar z) t') :=
      _subBinds_subst_pointwise y (.fvar z) hsb
    exact MSubRed.pro hpv' hsb'
  | @top Γ st' u_ hpv hLCu hfv =>
    intro hy_notin_Γ
    have hpv' : PrevalidExt (Ctx.subst y (.fvar z) Γ) (Stack.subst y (.fvar z) st') :=
      _PrevalidExt_subst_stray hpv hy_notin_Γ
    have hLCu' : Term.LC (Term.subst y (.fvar z) u_) :=
      Term.subst_lc (Term.LC.fvar z) hLCu
    have hfv' : Term.fv (Term.subst y (.fvar z) u_) ⊆
        Ctx.dom (Ctx.subst y (.fvar z) Γ) := by
      rw [Ctx.dom_subst]
      have hy_notin_u : y ∉ Term.fv u_ := fun h => hy_notin_Γ (hfv h)
      have hu_eq : Term.subst y (.fvar z) u_ = u_ := Term.subst_fresh hy_notin_u
      rw [hu_eq]; exact hfv
    show MSubRed (Ctx.subst y (.fvar z) Γ) (Stack.subst y (.fvar z) st')
      (Term.subst y (.fvar z) u_) (Term.subst y (.fvar z) .top)
    simp [Term.subst]
    exact MSubRed.top hpv' hLCu' hfv'
  | @equ Γ st' u_ v_ hpv heq =>
    intro hy_notin_Γ
    have hpv' : PrevalidExt (Ctx.subst y (.fvar z) Γ) (Stack.subst y (.fvar z) st') :=
      _PrevalidExt_subst_stray hpv hy_notin_Γ
    have heq' := MEqRed.subst_yz_stray hyz hy_notin_Γ heq
    exact MSubRed.equ hpv' heq'
  | @app Γ st' u_ u_' v_ hu hLCv hfvv ihu =>
    intro hy_notin_Γ
    have ihu' := ihu hy_notin_Γ
    have hLCv' : Term.LC (Term.subst y (.fvar z) v_) :=
      Term.subst_lc (Term.LC.fvar z) hLCv
    have hfvv' : Term.fv (Term.subst y (.fvar z) v_) ⊆
        Ctx.dom (Ctx.subst y (.fvar z) Γ) := by
      rw [Ctx.dom_subst]
      have hy_notin_v : y ∉ Term.fv v_ := fun h => hy_notin_Γ (hfvv h)
      have hv_eq : Term.subst y (.fvar z) v_ = v_ := Term.subst_fresh hy_notin_v
      rw [hv_eq]; exact hfvv
    show MSubRed (Ctx.subst y (.fvar z) Γ) (Stack.subst y (.fvar z) st')
      (Term.subst y (.fvar z) (.app u_ v_)) (Term.subst y (.fvar z) (.app u_' v_))
    simp [Term.subst]
    refine MSubRed.app ?_ hLCv' hfvv'
    simpa using ihu'
  | @fun_ Γ tt bd bd' L hLCt hbody _hUni ihbody =>
    intro hy_notin_Γ
    show MSubRed (Ctx.subst y (.fvar z) Γ) (Stack.subst y (.fvar z) [])
      (Term.subst y (.fvar z) (.abs tt bd)) (Term.subst y (.fvar z) (.abs tt bd'))
    simp [Term.subst]
    refine MSubRed.fun_ (L ∪ {y} ∪ {z}) (Term.subst_lc (Term.LC.fvar z) hLCt) ?_ trivial
    intro yfresh hyfresh
    simp only [Finset.mem_union, Finset.mem_singleton, not_or] at hyfresh
    obtain ⟨⟨hyfL, hyfy⟩, hyfz⟩ := hyfresh
    have hy_notin_Γ' : y ∉ Ctx.dom (⟨yfresh, tt, .sub⟩ :: Γ) := by
      rw [Ctx.dom_cons]
      intro hmem
      rcases Finset.mem_insert.mp hmem with hyy | hyΓ
      · exact hyfy hyy.symm
      · exact hy_notin_Γ hyΓ
    have ih_body := ihbody yfresh hyfL hy_notin_Γ'
    have hLCfz : Term.LC (.fvar z) := Term.LC.fvar z
    rw [Term.subst_open_var (Ne.symm hyfy) hLCfz bd,
        Term.subst_open_var (Ne.symm hyfy) hLCfz bd'] at ih_body
    simpa [Ctx.subst, List.cons_append] using ih_body
  | @fOp Γ st' tt αi bd bd' L hLCt hbody _hUni ihbody =>
    intro hy_notin_Γ
    show MSubRed (Ctx.subst y (.fvar z) Γ) (Stack.subst y (.fvar z) (αi :: st'))
      (Term.subst y (.fvar z) (.abs tt bd)) (Term.subst y (.fvar z) (.abs tt bd'))
    rw [Stack.subst_cons]
    simp [Term.subst]
    refine MSubRed.fOp (L ∪ {y} ∪ {z}) (Term.subst_lc (Term.LC.fvar z) hLCt) ?_ trivial
    intro yfresh hyfresh
    simp only [Finset.mem_union, Finset.mem_singleton, not_or] at hyfresh
    obtain ⟨⟨hyfL, hyfy⟩, hyfz⟩ := hyfresh
    have hy_notin_Γ' : y ∉ Ctx.dom (⟨yfresh, αi, .equ⟩ :: Γ) := by
      rw [Ctx.dom_cons]
      intro hmem
      rcases Finset.mem_insert.mp hmem with hyy | hyΓ
      · exact hyfy hyy.symm
      · exact hy_notin_Γ hyΓ
    have ih_body := ihbody yfresh hyfL hy_notin_Γ'
    have hLCfz : Term.LC (.fvar z) := Term.LC.fvar z
    rw [Term.subst_open_var (Ne.symm hyfy) hLCfz bd,
        Term.subst_open_var (Ne.symm hyfy) hLCfz bd'] at ih_body
    simpa [Ctx.subst, List.cons_append] using ih_body

/-- **Renaming for `MSubRed` over a stray-binder pair.** Analog of
`MEqRed.rename_stray`. -/
noncomputable def MSubRed.rename_stray
    {Γ : Ctx} {s : Stack} {u v : Term}
    (hpvΓ : Prevalid Γ)
    (h : MSubRed Γ s u v)
    (y z : String) (hy : y ∉ Γ.dom) (hz : z ∉ Γ.dom) :
    MSubRed Γ
      (Stack.subst y (.fvar z) s)
      (Term.subst y (.fvar z) u) (Term.subst y (.fvar z) v) := by
  classical
  by_cases hyz : y = z
  · subst hyz
    rw [_Term_subst_self_id, _Term_subst_self_id, _Stack_subst_self_id]
    exact h
  · have h_sub := MSubRed.subst_yz_stray hyz hy h
    have hctx_eq : Ctx.subst y (.fvar z) Γ = Γ := _Ctx_subst_id_of_stray hpvΓ hy
    rw [hctx_eq] at h_sub
    exact h_sub

/-! ### §7.0a. Phase 5c: existence-form rename + `AvoidsProUniv` preservation

The original `MEqRed.subst_yz_stray` is defined in tactic mode; its
`rw [...]`-induced casts make the result-shape opaque to `simp`, so an
*ex-post* preservation theorem
`AvoidsProUniv (subst_yz_stray h) x`
has to syntactically reduce the functor on each constructor case — which
fails because tactic-mode `induction h with ...` doesn't generate
`.eq_pro/.eq_bet/...` simp lemmas usable in proof contexts.

The principled fix is a *parallel* construction
`AvoidsProUniv_subst_yz_stray_exists`: an **existence statement**
`∃ h' : MEqRed (rename Γ) (rename st) (rename u) (rename u'),
  AvoidsProUniv h' x`,
proven by induction on `h`. At each constructor case, we BUILD a fresh
rename derivation (parallel to but not literally `subst_yz_stray h`) and
pair it with an `AvoidsProUniv` proof — both come from the IHs.

This is what Phase 5d's `equ_head_replace` will consume: it doesn't need
the rename to be literally `subst_yz_stray h`; it needs *some* renamed
derivation it can use, with the avoidance preserved. The existence form
delivers exactly that. -/

/-- Existence-form preservation: for any `MEqRed`-derivation that
universally avoids `x` at all `Me-Pro` lookups, there exists a
`y → z`-renamed derivation that also avoids `x`. -/
theorem AvoidsProUniv_subst_yz_stray_exists
    {Γ : Ctx} {st : Stack} {y z : String} {u u' : Term}
    (hyz : y ≠ z)
    (hy_notin_Γ : y ∉ Γ.dom)
    (h : MEqRed Γ st u u')
    (x : String)
    (hUniv : AvoidsProUniv h x) :
    ∃ h' : MEqRed (Ctx.subst y (.fvar z) Γ) (Stack.subst y (.fvar z) st)
              (Term.subst y (.fvar z) u) (Term.subst y (.fvar z) u'),
      AvoidsProUniv h' x := by
  classical
  revert hy_notin_Γ hUniv
  induction h with
  | @pro Γ st' yi α α' hpv heq hα ihα =>
    intro hy_notin_Γ hUniv
    rw [AvoidsProUniv_pro] at hUniv
    obtain ⟨hyix, huα⟩ := hUniv
    have hyi_dom : yi ∈ Γ.dom := _equBinds_in_dom heq
    have hyiy : yi ≠ y := fun hh => hy_notin_Γ (hh ▸ hyi_dom)
    have hpv' : PrevalidExt (Ctx.subst y (.fvar z) Γ)
        (Stack.subst y (.fvar z) st') :=
      _PrevalidExt_subst_stray hpv hy_notin_Γ
    have heq' : (Ctx.subst y (.fvar z) Γ).equBinds yi
        (Term.subst y (.fvar z) α) :=
      _equBinds_subst_pointwise y (.fvar z) heq
    obtain ⟨hα', huα'⟩ := ihα hy_notin_Γ huα
    have heq_subst : Term.subst y (.fvar z) (.fvar yi) = .fvar yi :=
      Term.subst_fvar_ne hyiy (.fvar z)
    refine ⟨heq_subst.symm ▸ MEqRed.pro hpv' heq' hα', ?_⟩
    simp only [AvoidsProUniv_subst_eq_src, AvoidsProUniv_pro]
    exact ⟨hyix, huα'⟩
  | @bet Γ st' tBound v0 v0' bd bd' L hLCt hbody _hUni hv ihbody ihv =>
    intro hy_notin_Γ hUniv
    rw [AvoidsProUniv_bet] at hUniv
    obtain ⟨hbU, hvU⟩ := hUniv
    have hLCfz : Term.LC (.fvar z) := Term.LC.fvar z
    -- Body data: ihbody recursively gives existence of body rename + AvoidsProUniv
    -- at the OPENED term. We'll later need to align this with the bet-constructor's
    -- expected body shape (∂(subst bd)^[yfresh] vs subst (bd^[yfresh])).
    have body_each : ∀ yfresh, yfresh ∉ L ∪ {y} ∪ {z} →
        ∃ h' : MEqRed (Ctx.subst y (.fvar z) Γ) (Stack.subst y (.fvar z) st')
                  ((Term.subst y (.fvar z) bd)^[yfresh])
                  ((Term.subst y (.fvar z) bd')^[yfresh]),
          AvoidsProUniv h' x := by
      intro yfresh hyfresh
      simp only [Finset.mem_union, Finset.mem_singleton, not_or] at hyfresh
      obtain ⟨⟨hyfL, hyfy⟩, _hyfz⟩ := hyfresh
      have hbd_eq : Term.subst y (.fvar z) (bd^[yfresh]) =
          (Term.subst y (.fvar z) bd)^[yfresh] :=
        Term.subst_open_var (Ne.symm hyfy) hLCfz bd
      have hbd'_eq : Term.subst y (.fvar z) (bd'^[yfresh]) =
          (Term.subst y (.fvar z) bd')^[yfresh] :=
        Term.subst_open_var (Ne.symm hyfy) hLCfz bd'
      obtain ⟨h_inner, hu_inner⟩ := ihbody yfresh hyfL hy_notin_Γ (hbU yfresh hyfL)
      refine ⟨hbd_eq ▸ hbd'_eq ▸ h_inner, ?_⟩
      simp only [AvoidsProUniv_subst_eq_src, AvoidsProUniv_subst_eq_dest]
      exact hu_inner
    obtain ⟨hv', hvU'⟩ := ihv hy_notin_Γ hvU
    -- Construct the bet derivation by choice.
    let body_witness : ∀ yfresh, yfresh ∉ L ∪ {y} ∪ {z} →
        MEqRed (Ctx.subst y (.fvar z) Γ) (Stack.subst y (.fvar z) st')
          ((Term.subst y (.fvar z) bd)^[yfresh])
          ((Term.subst y (.fvar z) bd')^[yfresh]) :=
      fun yfresh hyfresh => (body_each yfresh hyfresh).choose
    have body_witness_avoids : ∀ yfresh (hyfresh : yfresh ∉ L ∪ {y} ∪ {z}),
        AvoidsProUniv (body_witness yfresh hyfresh) x :=
      fun yfresh hyfresh => (body_each yfresh hyfresh).choose_spec
    have hsubst_open : Term.subst y (.fvar z) (Term.opening v0' bd') =
        Term.opening (Term.subst y (.fvar z) v0') (Term.subst y (.fvar z) bd') := by
      simp [Term.opening, Term.subst_open hLCfz]
    -- Build the bet derivation explicitly with a single ▸-cast on the dest term.
    let bet_core : MEqRed (Ctx.subst y (.fvar z) Γ) (Stack.subst y (.fvar z) st')
        (.app (.abs (Term.subst y (.fvar z) tBound) (Term.subst y (.fvar z) bd))
              (Term.subst y (.fvar z) v0))
        (Term.opening (Term.subst y (.fvar z) v0') (Term.subst y (.fvar z) bd')) :=
      MEqRed.bet (L ∪ {y} ∪ {z}) (Term.subst_lc hLCfz hLCt) body_witness trivial hv'
    -- The source term .app (.abs tBound bd) v0 substitutes by definition to
    -- .app (.abs (subst tBound) (subst bd)) (subst v0) — this is rfl.
    -- The dest term (subst (Term.opening v0' bd')) needs hsubst_open.
    refine ⟨hsubst_open ▸ bet_core, ?_⟩
    -- Avoidance: AvoidsProUniv (hsubst_open ▸ bet_core) x ↔ AvoidsProUniv bet_core x
    -- via AvoidsProUniv_subst_eq_dest. Then the bet_core's avoidance is built from
    -- body_witness_avoids and hvU'.
    simp only [AvoidsProUniv_subst_eq_dest]
    show AvoidsProUniv (MEqRed.bet (L ∪ {y} ∪ {z}) (Term.subst_lc hLCfz hLCt)
        body_witness trivial hv') x
    simp only [AvoidsProUniv_bet]
    exact ⟨body_witness_avoids, hvU'⟩
  | @top Γ st' hpv =>
    intro hy_notin_Γ _hUniv
    have hpv' : PrevalidExt (Ctx.subst y (.fvar z) Γ)
        (Stack.subst y (.fvar z) st') :=
      _PrevalidExt_subst_stray hpv hy_notin_Γ
    -- subst y _ .top = .top by definition.
    have htop_eq : Term.subst y (.fvar z) .top = .top := rfl
    refine ⟨htop_eq.symm ▸ MEqRed.top hpv', ?_⟩
    simp only [AvoidsProUniv_subst_eq_src, AvoidsProUniv_subst_eq_dest,
               AvoidsProUniv_top]
  | @app Γ st' u_ u_' v_ v_' hu hv ihu ihv =>
    intro hy_notin_Γ hUniv
    rw [AvoidsProUniv_app] at hUniv
    obtain ⟨huU, hvU⟩ := hUniv
    obtain ⟨hu', huU'⟩ := ihu hy_notin_Γ huU
    obtain ⟨hv', hvU'⟩ := ihv hy_notin_Γ hvU
    -- hu' has stack `Stack.subst y (.fvar z) (v_ :: st')`, need
    -- (Term.subst y _ v_) :: (Stack.subst y _ st'). Aligned via Stack.subst_cons.
    have hstack_eq : Stack.subst y (.fvar z) (v_ :: st') =
        Term.subst y (.fvar z) v_ :: Stack.subst y (.fvar z) st' := by
      simp [Stack.subst]
    let hu'_aligned : MEqRed (Ctx.subst y (.fvar z) Γ)
        (Term.subst y (.fvar z) v_ :: Stack.subst y (.fvar z) st')
        (Term.subst y (.fvar z) u_) (Term.subst y (.fvar z) u_') :=
      hstack_eq ▸ hu'
    -- subst y _ (.app u_ v_) = .app (subst y _ u_) (subst y _ v_) by definition.
    have hsrc_eq : Term.subst y (.fvar z) (.app u_ v_) =
        .app (Term.subst y (.fvar z) u_) (Term.subst y (.fvar z) v_) := rfl
    have hdst_eq : Term.subst y (.fvar z) (.app u_' v_') =
        .app (Term.subst y (.fvar z) u_') (Term.subst y (.fvar z) v_') := rfl
    refine ⟨hsrc_eq.symm ▸ hdst_eq.symm ▸ MEqRed.app hu'_aligned hv', ?_⟩
    simp only [AvoidsProUniv_subst_eq_src, AvoidsProUniv_subst_eq_dest]
    show AvoidsProUniv (MEqRed.app hu'_aligned hv') x
    simp only [AvoidsProUniv_app]
    refine ⟨?_, hvU'⟩
    show AvoidsProUniv (hstack_eq ▸ hu') x
    simp only [AvoidsProUniv_subst_eq_stack]
    exact huU'
  | @var Γ st' yi hpv =>
    intro hy_notin_Γ _hUniv
    have hpv' : PrevalidExt (Ctx.subst y (.fvar z) Γ)
        (Stack.subst y (.fvar z) st') :=
      _PrevalidExt_subst_stray hpv hy_notin_Γ
    -- Var is symmetric (same source and dest). Use a single cast on the
    -- MEqRed type level via congruence equality.
    by_cases hyiy : yi = y
    · have heqe : Term.subst y (.fvar z) (.fvar yi) = .fvar z := by
        rw [hyiy]; simp [Term.subst]
      have htype_eq : MEqRed (Ctx.subst y (.fvar z) Γ) (Stack.subst y (.fvar z) st')
          (.fvar z) (.fvar z) =
          MEqRed (Ctx.subst y (.fvar z) Γ) (Stack.subst y (.fvar z) st')
          (Term.subst y (.fvar z) (.fvar yi)) (Term.subst y (.fvar z) (.fvar yi)) := by
        rw [heqe]
      refine ⟨cast htype_eq (MEqRed.var hpv' : MEqRed _ _ (.fvar z) (.fvar z)), ?_⟩
      rw [AvoidsProUniv_cast _ _ _ _ htype_eq]
      · simp [AvoidsProUniv_var]
      · exact rfl
      · exact rfl
      · exact heqe.symm
      · exact heqe.symm
    · have heqe : Term.subst y (.fvar z) (.fvar yi) = .fvar yi :=
        Term.subst_fvar_ne hyiy (.fvar z)
      have htype_eq : MEqRed (Ctx.subst y (.fvar z) Γ) (Stack.subst y (.fvar z) st')
          (.fvar yi) (.fvar yi) =
          MEqRed (Ctx.subst y (.fvar z) Γ) (Stack.subst y (.fvar z) st')
          (Term.subst y (.fvar z) (.fvar yi)) (Term.subst y (.fvar z) (.fvar yi)) := by
        rw [heqe]
      refine ⟨cast htype_eq (MEqRed.var hpv' : MEqRed _ _ (.fvar yi) (.fvar yi)), ?_⟩
      rw [AvoidsProUniv_cast _ _ _ _ htype_eq]
      · simp [AvoidsProUniv_var]
      · exact rfl
      · exact rfl
      · exact heqe.symm
      · exact heqe.symm
  | @fun_ Γ tt tt' bd bd' L ht hbody _hUni iht ihbody =>
    intro hy_notin_Γ hUniv
    rw [AvoidsProUniv_fun_] at hUniv
    obtain ⟨htU, hbU⟩ := hUniv
    obtain ⟨ht', htU'⟩ := iht hy_notin_Γ htU
    have hLCfz : Term.LC (.fvar z) := Term.LC.fvar z
    -- Body data with the extended-context hypothesis on hy_notin_Γ.
    have body_each : ∀ yfresh, yfresh ∉ L ∪ {y} ∪ {z} →
        ∃ h' : MEqRed (⟨yfresh, Term.subst y (.fvar z) tt, .sub⟩ ::
                        Ctx.subst y (.fvar z) Γ) []
                  ((Term.subst y (.fvar z) bd)^[yfresh])
                  ((Term.subst y (.fvar z) bd')^[yfresh]),
          AvoidsProUniv h' x := by
      intro yfresh hyfresh
      simp only [Finset.mem_union, Finset.mem_singleton, not_or] at hyfresh
      obtain ⟨⟨hyfL, hyfy⟩, _⟩ := hyfresh
      have hy_notin_Γ' : y ∉ Ctx.dom (⟨yfresh, tt, .sub⟩ :: Γ) := by
        rw [Ctx.dom_cons]
        intro hmem
        rcases Finset.mem_insert.mp hmem with hyy | hyΓ
        · exact hyfy hyy.symm
        · exact hy_notin_Γ hyΓ
      obtain ⟨h_inner, hu_inner⟩ :=
        ihbody yfresh hyfL hy_notin_Γ' (hbU yfresh hyfL)
      have hbd_eq : Term.subst y (.fvar z) (bd^[yfresh]) =
          (Term.subst y (.fvar z) bd)^[yfresh] :=
        Term.subst_open_var (Ne.symm hyfy) hLCfz bd
      have hbd'_eq : Term.subst y (.fvar z) (bd'^[yfresh]) =
          (Term.subst y (.fvar z) bd')^[yfresh] :=
        Term.subst_open_var (Ne.symm hyfy) hLCfz bd'
      have hctx_eq : Ctx.subst y (.fvar z) (⟨yfresh, tt, .sub⟩ :: Γ) =
          ⟨yfresh, Term.subst y (.fvar z) tt, .sub⟩ :: Ctx.subst y (.fvar z) Γ := by
        simp [Ctx.subst]
      refine ⟨hctx_eq ▸ hbd_eq ▸ hbd'_eq ▸ h_inner, ?_⟩
      simp only [AvoidsProUniv_subst_eq_ctx, AvoidsProUniv_subst_eq_src,
                 AvoidsProUniv_subst_eq_dest]
      exact hu_inner
    let body_witness : ∀ yfresh, yfresh ∉ L ∪ {y} ∪ {z} →
        MEqRed (⟨yfresh, Term.subst y (.fvar z) tt, .sub⟩ ::
                  Ctx.subst y (.fvar z) Γ) []
          ((Term.subst y (.fvar z) bd)^[yfresh])
          ((Term.subst y (.fvar z) bd')^[yfresh]) :=
      fun yfresh hyfresh => (body_each yfresh hyfresh).choose
    have body_witness_avoids : ∀ yfresh (hyfresh : yfresh ∉ L ∪ {y} ∪ {z}),
        AvoidsProUniv (body_witness yfresh hyfresh) x :=
      fun yfresh hyfresh => (body_each yfresh hyfresh).choose_spec
    have hsrc_eq : Term.subst y (.fvar z) (.abs tt bd) =
        .abs (Term.subst y (.fvar z) tt) (Term.subst y (.fvar z) bd) := rfl
    have hdst_eq : Term.subst y (.fvar z) (.abs tt' bd') =
        .abs (Term.subst y (.fvar z) tt') (Term.subst y (.fvar z) bd') := rfl
    have hstack_eq : Stack.subst y (.fvar z) ([] : Stack) = ([] : Stack) := rfl
    refine ⟨hstack_eq.symm ▸ hsrc_eq.symm ▸ hdst_eq.symm ▸
              MEqRed.fun_ (L ∪ {y} ∪ {z}) ht' body_witness trivial, ?_⟩
    simp only [AvoidsProUniv_subst_eq_stack, AvoidsProUniv_subst_eq_src,
               AvoidsProUniv_subst_eq_dest]
    show AvoidsProUniv (MEqRed.fun_ (L ∪ {y} ∪ {z}) ht' body_witness trivial) x
    simp only [AvoidsProUniv_fun_]
    exact ⟨htU', body_witness_avoids⟩
  | @tAp Γ st' u_ hpv hLCu hfv =>
    intro hy_notin_Γ _hUniv
    have hpv' : PrevalidExt (Ctx.subst y (.fvar z) Γ)
        (Stack.subst y (.fvar z) st') :=
      _PrevalidExt_subst_stray hpv hy_notin_Γ
    have hLCu' : Term.LC (Term.subst y (.fvar z) u_) :=
      Term.subst_lc (Term.LC.fvar z) hLCu
    have hfv' : Term.fv (Term.subst y (.fvar z) u_) ⊆
        Ctx.dom (Ctx.subst y (.fvar z) Γ) := by
      rw [Ctx.dom_subst]
      have hy_notin_u : y ∉ Term.fv u_ := fun h' => hy_notin_Γ (hfv h')
      have hu_eq : Term.subst y (.fvar z) u_ = u_ := Term.subst_fresh hy_notin_u
      rw [hu_eq]; exact hfv
    have hsrc_eq : Term.subst y (.fvar z) (.app .top u_) =
        .app .top (Term.subst y (.fvar z) u_) := rfl
    have hdst_eq : Term.subst y (.fvar z) (.top : Term) = .top := rfl
    refine ⟨hsrc_eq.symm ▸ hdst_eq.symm ▸ MEqRed.tAp hpv' hLCu' hfv', ?_⟩
    simp only [AvoidsProUniv_subst_eq_src, AvoidsProUniv_subst_eq_dest]
    show AvoidsProUniv (MEqRed.tAp hpv' hLCu' hfv') x
    simp only [AvoidsProUniv_tAp]
  | @fOp Γ st' tt tt' αi bd bd' L ht hbody _hUni iht ihbody =>
    intro hy_notin_Γ hUniv
    rw [AvoidsProUniv_fOp] at hUniv
    obtain ⟨htU, hbU⟩ := hUniv
    obtain ⟨ht', htU'⟩ := iht hy_notin_Γ htU
    have hLCfz : Term.LC (.fvar z) := Term.LC.fvar z
    have body_each : ∀ yfresh, yfresh ∉ L ∪ {y} ∪ {z} →
        ∃ h' : MEqRed (⟨yfresh, Term.subst y (.fvar z) αi, .equ⟩ ::
                        Ctx.subst y (.fvar z) Γ)
                  (Stack.subst y (.fvar z) st')
                  ((Term.subst y (.fvar z) bd)^[yfresh])
                  ((Term.subst y (.fvar z) bd')^[yfresh]),
          AvoidsProUniv h' x := by
      intro yfresh hyfresh
      simp only [Finset.mem_union, Finset.mem_singleton, not_or] at hyfresh
      obtain ⟨⟨hyfL, hyfy⟩, _⟩ := hyfresh
      have hy_notin_Γ' : y ∉ Ctx.dom (⟨yfresh, αi, .equ⟩ :: Γ) := by
        rw [Ctx.dom_cons]
        intro hmem
        rcases Finset.mem_insert.mp hmem with hyy | hyΓ
        · exact hyfy hyy.symm
        · exact hy_notin_Γ hyΓ
      obtain ⟨h_inner, hu_inner⟩ :=
        ihbody yfresh hyfL hy_notin_Γ' (hbU yfresh hyfL)
      have hbd_eq : Term.subst y (.fvar z) (bd^[yfresh]) =
          (Term.subst y (.fvar z) bd)^[yfresh] :=
        Term.subst_open_var (Ne.symm hyfy) hLCfz bd
      have hbd'_eq : Term.subst y (.fvar z) (bd'^[yfresh]) =
          (Term.subst y (.fvar z) bd')^[yfresh] :=
        Term.subst_open_var (Ne.symm hyfy) hLCfz bd'
      have hctx_eq : Ctx.subst y (.fvar z) (⟨yfresh, αi, .equ⟩ :: Γ) =
          ⟨yfresh, Term.subst y (.fvar z) αi, .equ⟩ ::
          Ctx.subst y (.fvar z) Γ := by simp [Ctx.subst]
      refine ⟨hctx_eq ▸ hbd_eq ▸ hbd'_eq ▸ h_inner, ?_⟩
      simp only [AvoidsProUniv_subst_eq_ctx, AvoidsProUniv_subst_eq_src,
                 AvoidsProUniv_subst_eq_dest]
      exact hu_inner
    let body_witness : ∀ yfresh, yfresh ∉ L ∪ {y} ∪ {z} →
        MEqRed (⟨yfresh, Term.subst y (.fvar z) αi, .equ⟩ ::
                  Ctx.subst y (.fvar z) Γ)
          (Stack.subst y (.fvar z) st')
          ((Term.subst y (.fvar z) bd)^[yfresh])
          ((Term.subst y (.fvar z) bd')^[yfresh]) :=
      fun yfresh hyfresh => (body_each yfresh hyfresh).choose
    have body_witness_avoids : ∀ yfresh (hyfresh : yfresh ∉ L ∪ {y} ∪ {z}),
        AvoidsProUniv (body_witness yfresh hyfresh) x :=
      fun yfresh hyfresh => (body_each yfresh hyfresh).choose_spec
    have hsrc_eq : Term.subst y (.fvar z) (.abs tt bd) =
        .abs (Term.subst y (.fvar z) tt) (Term.subst y (.fvar z) bd) := rfl
    have hdst_eq : Term.subst y (.fvar z) (.abs tt' bd') =
        .abs (Term.subst y (.fvar z) tt') (Term.subst y (.fvar z) bd') := rfl
    have hstack_eq : Stack.subst y (.fvar z) (αi :: st') =
        Term.subst y (.fvar z) αi :: Stack.subst y (.fvar z) st' := by
      simp [Stack.subst]
    refine ⟨hstack_eq ▸ hsrc_eq.symm ▸ hdst_eq.symm ▸
              MEqRed.fOp (L ∪ {y} ∪ {z}) ht' body_witness trivial, ?_⟩
    simp only [AvoidsProUniv_subst_eq_stack, AvoidsProUniv_subst_eq_src,
               AvoidsProUniv_subst_eq_dest]
    show AvoidsProUniv (MEqRed.fOp (L ∪ {y} ∪ {z}) ht' body_witness trivial) x
    simp only [AvoidsProUniv_fOp]
    exact ⟨htU', body_witness_avoids⟩

/-! ### §7.1. Note on `avoidsPro_rename_stray` — Phase 2 follow-up

The user-spec for Phase 1 also requested a companion
`avoidsPro_rename_stray h y z hy hz x = avoidsPro h x` lemma. After
implementing the renaming functor, careful analysis reveals this
particular preservation statement runs into the SAME alpha-equivariance
trap that the FALSE `avoidsPro_alpha_equiv` axiom (reverted in
`12da200`) tried to discharge.

The crux: `avoidsPro` for the cofinite arms (`bet`, `fun_`, `fOp`)
evaluates the body at the canonical witness `pickFresh L`, where `L` is
the binder's avoidance set. The renamed derivation has a different
binder set `L' = L ∪ {y, z}`, so `avoidsPro` of the renamed derivation
samples at `pickFresh L'`, and `pickFresh L ≠ pickFresh L'` in general.
Equating `avoidsPro (hbody (pickFresh L) _) x` with
`avoidsPro (hbody (pickFresh L') _) x` for arbitrary `hbody` is
exactly the FALSE alpha-equivariance statement (counterexample:
`hbody y _ := if y = pickFresh L then h_with_pro else h_var`).

The principled fix lives at the `avoidsPro` definition level, not at
the rename_stray level: redesign `avoidsPro` so the cofinite witness is
**universally quantified** rather than `pickFresh`-canonical. Concretely:

```
-- Future Phase 2 redesign sketch:
def avoidsPro' (h : MEqRed Γ s u v) (x : String) : Prop := match h with
  | .bet L hLCt hbody hv =>
      (∀ y ∉ L, avoidsPro' (hbody y _) x) ∧ avoidsPro' hv x
  ...
```

Under this Prop-valued ∀-witness formulation, `avoidsPro'_rename_stray`
becomes provable: for any `y ∉ L'`, we have `y ∉ L` (since `L' ⊇ L`),
so the IH at `y` directly applies. No alpha-equivariance is needed.

The downside: `avoidsPro'` is `Prop`-valued, which complicates the
existing `avoidsPro_refl` theorem (currently a Bool-valued reflexivity
fact). The current `avoidsPro` is `Bool`-valued precisely so it can be
introspected by `simp` decision procedures in downstream consumers
(notably `Lemma_30_msPro_x` and the projected `equ_head_replace`
discharge).

A hybrid approach: keep Bool-valued `avoidsPro` for downstream use,
but carry a separate Prop-valued `AvoidsPro_universal` predicate that
DOES survive renaming. The two are equivalent under appropriate
witness alignment, but only the Prop-valued one is rename-stable.

Phase 2 work item: implement the Prop-valued `AvoidsPro_universal` and
prove `AvoidsPro_universal_rename_stray`. Then connect it back to the
Bool `avoidsPro` for the specific witness it cares about. This unblocks
the β-residual axioms via a different mechanical route than the current
`equ_head_replace` scaffolding. -/

/-! ## §8. `equ_head_replace` — bound-term replacement on `.equ`-head

Phase 2 of the architectural lever to unblock the β-residual axioms.

`MEqRed.equ_head_replace`: replace the bound term of a `.equ`-head from
`α` to `α'` (related by `MEqRed Γ₁ [] α α'`) in `Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁`.
Requires an `avoidsPro h y = true` premise (rules out `Me-Pro y` lookups
that would observe the changed binding) and a `cofinDomFresh h = true`
premise (the canonical witness `pickFresh L` is fresh w.r.t. Γ.dom and
the body's fvs at every cofinite arm — needed to apply `rename_stray` /
`rename_sub` / `rename_equ` in the cofinite arms to convert from
canonical-witness derivations to arbitrary cofinite-output witnesses).

The proof structure for each constructor:

* **`pro`**: split on `yi = y`. If `yi = y`, `avoidsPro_pro` reduces the
  premise to `decide (y ≠ y) && _ = true`, contradiction. If `yi ≠ y`,
  use `_equBinds_equ_head_swap_neq` to lift the lookup to the new head,
  recurse on the inner derivation.
* **`top`/`var`/`tAp`**: just use `PrevalidExt.equ_head_replace_mid`.
* **`app`**: recurse on both subterms, `avoidsPro_app` propagates.
* **`bet`/`fun_`/`fOp`** (cofinite): recurse at the canonical witness
  `pickFresh L` (allowed because `avoidsPro` and `cofinDomFresh` track
  the canonical witness). Then use `rename_stray` (bet) /
  `MEqRed.rename_sub` (fun_) / `_MEqRed_rename_equ_no_fv` (fOp) to
  convert the `pickFresh L`-witness derivation to one at any other
  `yfresh ∉ L_new` (where L_new is widened to include `pickFresh L` and
  Γ.dom so every cofinite output witness is fresh w.r.t. the renamed-from
  witness).

### Why this is NOT alpha-equivariance

The `avoidsPro h y = true` and `cofinDomFresh h = true` premises both
sample at the SAME canonical witness (`pickFresh L`). They are
deterministic Bool functions of the derivation tree's shape, not
cross-witness claims. We use them to extract data at `pickFresh L`
only, then construct cross-witness extensions via the structural
`rename_stray` / `rename_sub` / `rename_equ` functors (which DO produce
cross-witness derivations, but as concrete constructions, not as
preservation claims about an arbitrary input). -/

/-! ### §8.1. Helpers for the cofinite-arm renaming compositions -/

/-- `(Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁).dom = (Γ₂ ++ ⟨y, α', .equ⟩ :: Γ₁).dom`.
The `.equ`-head bound-term swap doesn't change the names. -/
private theorem _Ctx_dom_eq_under_equ_head_replace
    {Γ₁ Γ₂ : Ctx} {y : String} {α α' : Term} :
    Ctx.dom (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁) =
      Ctx.dom (Γ₂ ++ ⟨y, α', .equ⟩ :: Γ₁) := by
  rw [Ctx.dom_append, Ctx.dom_append, Ctx.dom_cons, Ctx.dom_cons]

/-- All stack entries' fv ⊆ Γ.dom (extracted from PrevalidExt). -/
private theorem _PrevalidExt_stack_fv_subset_dom
    {Γ : Ctx} {s : Stack} (h : PrevalidExt Γ s) :
    ∀ β ∈ s, Term.fv β ⊆ Γ.dom := by
  induction h with
  | nil _ => intro β hβ; cases hβ
  | cons _ _ hfvβ ih =>
    intro α hα
    rcases List.mem_cons.mp hα with hα | hα
    · subst hα; exact hfvβ
    · exact ih α hα

/-- A name `y₀ ∉ Γ.dom` is also ∉ fv of any stack entry (whose fv is
contained in Γ.dom). -/
private theorem _y₀_notin_stack_fv_of_notin_dom
    {Γ : Ctx} {s : Stack} {y₀ : String}
    (hpv : PrevalidExt Γ s) (hy₀_dom : y₀ ∉ Γ.dom) :
    ∀ β ∈ s, y₀ ∉ Term.fv β := by
  intro β hβ hyβ
  exact hy₀_dom (_PrevalidExt_stack_fv_subset_dom hpv β hβ hyβ)

/-! ### §8.2. `MEqRed.equ_head_replace` -/

/-- **Replace the bound term of a `.equ`-head context.**

Given:
* `h : MEqRed (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁) st u u'` — the input derivation.
* `hα : MEqRed Γ₁ [] α α'` — relates the old and new bound terms.
* `hLCα'`, `hfvα'` — well-formedness data for `α'`.
* `hAvoid : avoidsPro h y = true` — no `Me-Pro y` step in `h`.
* `hFresh : cofinDomFresh h = true` — canonical witnesses fresh.

Produces: `MEqRed (Γ₂ ++ ⟨y, α', .equ⟩ :: Γ₁) st u u'`. -/
noncomputable def MEqRed.equ_head_replace
    {Γ₁ Γ₂ : Ctx} {st : Stack} {y : String} {α α' u u' : Term}
    (h : MEqRed (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁) st u u')
    (hLCα' : Term.LC α') (hfvα' : Term.fv α' ⊆ Γ₁.dom)
    (hAvoid : avoidsPro h y = true)
    (hFresh : cofinDomFresh h = true) :
    MEqRed (Γ₂ ++ ⟨y, α', .equ⟩ :: Γ₁) st u u' := by
  classical
  generalize hΓ : (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁) = Γ at h
  induction h generalizing Γ₂ with
  | @pro Γ st' yi β β' hpv heq hβ ihβ =>
    subst hΓ
    rw [avoidsPro_pro] at hAvoid
    rw [cofinDomFresh_pro] at hFresh
    obtain ⟨hyiy_decide, hAvoid_inner⟩ := Bool.and_eq_true _ _ |>.mp hAvoid
    have hyiy : yi ≠ y := decide_eq_true_eq.mp hyiy_decide
    have hpv' : PrevalidExt (Γ₂ ++ ⟨y, α', .equ⟩ :: Γ₁) st' :=
      PrevalidExt.equ_head_replace_mid hpv hLCα' hfvα'
    have heq' := _equBinds_equ_head_swap_neq (α' := α') hyiy heq
    exact MEqRed.pro hpv' heq' (ihβ (Γ₂ := Γ₂) rfl hAvoid_inner hFresh)
  | @bet Γ st' tBound v0 v0' bd bd' L hLCt hbody _hUni hv ihbody ihv =>
    subst hΓ
    rw [avoidsPro_bet] at hAvoid
    rw [cofinDomFresh_bet] at hFresh
    obtain ⟨hAvoid_body, hAvoid_v⟩ := Bool.and_eq_true _ _ |>.mp hAvoid
    -- Decompose hFresh: (...dom && ...fvbd && ...fvbd') && body && v
    obtain ⟨hFresh_left_v, hFresh_v⟩ := Bool.and_eq_true _ _ |>.mp hFresh
    obtain ⟨hFresh_left_body, hFresh_body⟩ := Bool.and_eq_true _ _ |>.mp hFresh_left_v
    obtain ⟨hFresh_left_fvbd', hFresh_fvbd'_dec⟩ :=
      Bool.and_eq_true _ _ |>.mp hFresh_left_body
    obtain ⟨hFresh_dom_dec, hFresh_fvbd_dec⟩ :=
      Bool.and_eq_true _ _ |>.mp hFresh_left_fvbd'
    have hy₀_dom : pickFresh L ∉ Ctx.dom (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁) :=
      decide_eq_true_eq.mp hFresh_dom_dec
    have hy₀_fvbd : pickFresh L ∉ Term.fv bd :=
      decide_eq_true_eq.mp hFresh_fvbd_dec
    have hy₀_fvbd' : pickFresh L ∉ Term.fv bd' :=
      decide_eq_true_eq.mp hFresh_fvbd'_dec
    let y₀ := pickFresh L
    have hy₀L : y₀ ∉ L := pickFresh_notMem L
    have hy₀_dom' : y₀ ∉ Ctx.dom (Γ₂ ++ ⟨y, α', .equ⟩ :: Γ₁) := by
      rw [← _Ctx_dom_eq_under_equ_head_replace (α := α) (α' := α')]; exact hy₀_dom
    have ihbody_y₀ := ihbody y₀ hy₀L (Γ₂ := Γ₂) rfl hAvoid_body hFresh_body
    have ihv' := ihv (Γ₂ := Γ₂) rfl hAvoid_v hFresh_v
    -- Output L_new ⊇ L ∪ Γ.dom ∪ {y₀} so yfresh ≠ y₀ and yfresh ∉ Γ_replaced.dom.
    refine MEqRed.bet (L ∪ Ctx.dom (Γ₂ ++ ⟨y, α', .equ⟩ :: Γ₁) ∪ {y₀})
      hLCt ?_ trivial ihv'
    intro yfresh hyfresh
    simp only [Finset.mem_union, Finset.mem_singleton] at hyfresh
    push_neg at hyfresh
    obtain ⟨⟨hyfL, hyf_dom⟩, hyf_y₀⟩ := hyfresh
    -- hpv for the new context.
    have hpvE_y₀ : PrevalidExt (Γ₂ ++ ⟨y, α', .equ⟩ :: Γ₁) st' :=
      MEqRed.prevalidExt ihbody_y₀
    have hpv_replaced : Prevalid (Γ₂ ++ ⟨y, α', .equ⟩ :: Γ₁) :=
      extractPrevalid hpvE_y₀
    -- Stack freshness for y₀ via PrevalidExt at the new context.
    have hy₀_stack : ∀ β ∈ st', y₀ ∉ Term.fv β :=
      _y₀_notin_stack_fv_of_notin_dom hpvE_y₀ hy₀_dom'
    -- Rename y₀ → yfresh.
    have ren := MEqRed.rename_stray hpv_replaced ihbody_y₀ y₀ yfresh hy₀_dom' hyf_dom
    have hstk_eq : Stack.subst y₀ (.fvar yfresh) st' = st' :=
      Stack.subst_fresh hy₀_stack
    have hbd_eq : Term.subst y₀ (.fvar yfresh) (bd^[y₀]) = bd^[yfresh] :=
      Term.subst_open_fresh hy₀_fvbd
    have hbd'_eq : Term.subst y₀ (.fvar yfresh) (bd'^[y₀]) = bd'^[yfresh] :=
      Term.subst_open_fresh hy₀_fvbd'
    rw [hstk_eq, hbd_eq, hbd'_eq] at ren
    exact ren
  | @top Γ st' hpv =>
    subst hΓ
    have hpv' : PrevalidExt (Γ₂ ++ ⟨y, α', .equ⟩ :: Γ₁) st' :=
      PrevalidExt.equ_head_replace_mid hpv hLCα' hfvα'
    exact MEqRed.top hpv'
  | @app Γ st' u_ u_' v_ v_' hu hv ihu ihv =>
    subst hΓ
    rw [avoidsPro_app] at hAvoid
    rw [cofinDomFresh_app] at hFresh
    obtain ⟨hAvoid_u, hAvoid_v⟩ := Bool.and_eq_true _ _ |>.mp hAvoid
    obtain ⟨hFresh_u, hFresh_v⟩ := Bool.and_eq_true _ _ |>.mp hFresh
    have ihu' := ihu (Γ₂ := Γ₂) rfl hAvoid_u hFresh_u
    have ihv' := ihv (Γ₂ := Γ₂) rfl hAvoid_v hFresh_v
    exact MEqRed.app ihu' ihv'
  | @var Γ st' yi hpv =>
    subst hΓ
    have hpv' : PrevalidExt (Γ₂ ++ ⟨y, α', .equ⟩ :: Γ₁) st' :=
      PrevalidExt.equ_head_replace_mid hpv hLCα' hfvα'
    exact MEqRed.var hpv'
  | @fun_ Γ tt tt' bd bd' L ht hbody _hUni iht ihbody =>
    subst hΓ
    rw [avoidsPro_fun_] at hAvoid
    rw [cofinDomFresh_fun_] at hFresh
    obtain ⟨hAvoid_t, hAvoid_body⟩ := Bool.and_eq_true _ _ |>.mp hAvoid
    obtain ⟨hFresh_left_body, hFresh_body⟩ := Bool.and_eq_true _ _ |>.mp hFresh
    obtain ⟨hFresh_left_t, hFresh_t⟩ := Bool.and_eq_true _ _ |>.mp hFresh_left_body
    obtain ⟨hFresh_left_fvbd', hFresh_fvbd'_dec⟩ :=
      Bool.and_eq_true _ _ |>.mp hFresh_left_t
    obtain ⟨hFresh_dom_dec, hFresh_fvbd_dec⟩ :=
      Bool.and_eq_true _ _ |>.mp hFresh_left_fvbd'
    have hy₀_dom : pickFresh L ∉ Ctx.dom (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁) :=
      decide_eq_true_eq.mp hFresh_dom_dec
    have hy₀_fvbd : pickFresh L ∉ Term.fv bd :=
      decide_eq_true_eq.mp hFresh_fvbd_dec
    have hy₀_fvbd' : pickFresh L ∉ Term.fv bd' :=
      decide_eq_true_eq.mp hFresh_fvbd'_dec
    let y₀ := pickFresh L
    have hy₀L : y₀ ∉ L := pickFresh_notMem L
    have hy₀_dom' : y₀ ∉ Ctx.dom (Γ₂ ++ ⟨y, α', .equ⟩ :: Γ₁) := by
      rw [← _Ctx_dom_eq_under_equ_head_replace (α := α) (α' := α')]; exact hy₀_dom
    have iht' := iht (Γ₂ := Γ₂) rfl hAvoid_t hFresh_t
    have ihbody_y₀ := ihbody y₀ hy₀L
      (Γ₂ := ⟨y₀, tt, .sub⟩ :: Γ₂) (by simp) hAvoid_body hFresh_body
    refine MEqRed.fun_ (L ∪ Ctx.dom (Γ₂ ++ ⟨y, α', .equ⟩ :: Γ₁) ∪ {y₀}) iht' ?_ trivial
    intro yfresh hyfresh
    simp only [Finset.mem_union, Finset.mem_singleton] at hyfresh
    push_neg at hyfresh
    obtain ⟨⟨hyfL, hyf_dom⟩, hyf_y₀⟩ := hyfresh
    -- Extract data from ihbody_y₀'s prevalidExt.
    have hpvE_full : PrevalidExt (⟨y₀, tt, .sub⟩ :: (Γ₂ ++ ⟨y, α', .equ⟩ :: Γ₁)) [] := by
      have := MEqRed.prevalidExt ihbody_y₀
      simpa using this
    have hpv_full : Prevalid (⟨y₀, tt, .sub⟩ :: (Γ₂ ++ ⟨y, α', .equ⟩ :: Γ₁)) :=
      extractPrevalid hpvE_full
    have hpv_outer : Prevalid (Γ₂ ++ ⟨y, α', .equ⟩ :: Γ₁) := by
      cases hpv_full with
      | sub hpv _ _ _ => exact hpv
    have hLCt_tt : Term.LC tt := by
      cases hpv_full with
      | sub _ _ _ hLCtt => exact hLCtt
    have hfvtt : Term.fv tt ⊆ Ctx.dom (Γ₂ ++ ⟨y, α', .equ⟩ :: Γ₁) := by
      cases hpv_full with
      | sub _ _ hfvtt _ => exact hfvtt
    -- Apply MEqRed.rename_sub. Stack is empty for fun_, so stack-freshness is trivial.
    have ihbody_y₀_norm : MEqRed (⟨y₀, tt, .sub⟩ :: (Γ₂ ++ ⟨y, α', .equ⟩ :: Γ₁)) []
        (bd^[y₀]) (bd'^[y₀]) := by simpa using ihbody_y₀
    have ren := MEqRed.rename_sub hpv_outer hLCt_tt hfvtt
      hy₀_dom' hyf_dom hy₀_fvbd hy₀_fvbd'
      (by intro β hβ; cases hβ) ihbody_y₀_norm
    -- ren : MEqRed (⟨yfresh, tt, .sub⟩ :: (Γ₂ ++ ⟨y, α', .equ⟩ :: Γ₁)) []
    --              (bd^[yfresh]) (bd'^[yfresh])
    simpa using ren
  | @tAp Γ st' u_ hpv hLCu hfv =>
    subst hΓ
    have hpv' : PrevalidExt (Γ₂ ++ ⟨y, α', .equ⟩ :: Γ₁) st' :=
      PrevalidExt.equ_head_replace_mid hpv hLCα' hfvα'
    have hfv' : Term.fv u_ ⊆ Ctx.dom (Γ₂ ++ ⟨y, α', .equ⟩ :: Γ₁) := by
      rw [← _Ctx_dom_eq_under_equ_head_replace (α := α) (α' := α')]; exact hfv
    exact MEqRed.tAp hpv' hLCu hfv'
  | @fOp Γ st' tt tt' αi bd bd' L ht hbody _hUni iht ihbody =>
    subst hΓ
    rw [avoidsPro_fOp] at hAvoid
    rw [cofinDomFresh_fOp] at hFresh
    obtain ⟨hAvoid_t, hAvoid_body⟩ := Bool.and_eq_true _ _ |>.mp hAvoid
    obtain ⟨hFresh_left_body, hFresh_body⟩ := Bool.and_eq_true _ _ |>.mp hFresh
    obtain ⟨hFresh_left_t, hFresh_t⟩ := Bool.and_eq_true _ _ |>.mp hFresh_left_body
    obtain ⟨hFresh_left_fvbd', hFresh_fvbd'_dec⟩ :=
      Bool.and_eq_true _ _ |>.mp hFresh_left_t
    obtain ⟨hFresh_dom_dec, hFresh_fvbd_dec⟩ :=
      Bool.and_eq_true _ _ |>.mp hFresh_left_fvbd'
    have hy₀_dom : pickFresh L ∉ Ctx.dom (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁) :=
      decide_eq_true_eq.mp hFresh_dom_dec
    have hy₀_fvbd : pickFresh L ∉ Term.fv bd :=
      decide_eq_true_eq.mp hFresh_fvbd_dec
    have hy₀_fvbd' : pickFresh L ∉ Term.fv bd' :=
      decide_eq_true_eq.mp hFresh_fvbd'_dec
    let y₀ := pickFresh L
    have hy₀L : y₀ ∉ L := pickFresh_notMem L
    have hy₀_dom' : y₀ ∉ Ctx.dom (Γ₂ ++ ⟨y, α', .equ⟩ :: Γ₁) := by
      rw [← _Ctx_dom_eq_under_equ_head_replace (α := α) (α' := α')]; exact hy₀_dom
    have iht' := iht (Γ₂ := Γ₂) rfl hAvoid_t hFresh_t
    have ihbody_y₀ := ihbody y₀ hy₀L
      (Γ₂ := ⟨y₀, αi, .equ⟩ :: Γ₂) (by simp) hAvoid_body hFresh_body
    refine MEqRed.fOp (L ∪ Ctx.dom (Γ₂ ++ ⟨y, α', .equ⟩ :: Γ₁) ∪ {y₀}) iht' ?_ trivial
    intro yfresh hyfresh
    simp only [Finset.mem_union, Finset.mem_singleton] at hyfresh
    push_neg at hyfresh
    obtain ⟨⟨hyfL, hyf_dom⟩, hyf_y₀⟩ := hyfresh
    have hyz : y₀ ≠ yfresh := fun h' => hyf_y₀ h'.symm
    -- Extract data from ihbody_y₀'s prevalidExt.
    have ihbody_y₀_norm :
        MEqRed (⟨y₀, αi, .equ⟩ :: (Γ₂ ++ ⟨y, α', .equ⟩ :: Γ₁)) st'
          (bd^[y₀]) (bd'^[y₀]) := by simpa using ihbody_y₀
    have hpvE_full : PrevalidExt (⟨y₀, αi, .equ⟩ :: (Γ₂ ++ ⟨y, α', .equ⟩ :: Γ₁)) st' :=
      MEqRed.prevalidExt ihbody_y₀_norm
    have hpv_full : Prevalid (⟨y₀, αi, .equ⟩ :: (Γ₂ ++ ⟨y, α', .equ⟩ :: Γ₁)) :=
      extractPrevalid hpvE_full
    have hpv_outer : Prevalid (Γ₂ ++ ⟨y, α', .equ⟩ :: Γ₁) := by
      cases hpv_full with
      | equ hpv _ _ _ => exact hpv
    have hfv_αi : Term.fv αi ⊆ Ctx.dom (Γ₂ ++ ⟨y, α', .equ⟩ :: Γ₁) := by
      cases hpv_full with
      | equ _ _ hfvαi _ => exact hfvαi
    have hy₀_αi : y₀ ∉ Term.fv αi := fun h' => hy₀_dom' (hfv_αi h')
    -- Stack freshness: each entry's fv ⊆ Γ_full.dom; combined with y₀ ∉ Γ_outer.dom
    -- and y₀ ∉ fv αi (the head's bound), we get y₀ ∉ each entry's fv when the entry's
    -- fv is in the OUTER dom. But entries could mention y₀ (the head's name) too.
    -- However, by Prevalid invariant on Γ_full, each tail entry's fv excludes y₀
    -- (since y₀ ∉ Γ_outer.dom, but the entry's fv ⊆ Γ_outer.dom from Prevalid:
    --  the entry was bound BEFORE y₀ entered scope).
    -- Wait — the stack entries are typed against Γ_full = ⟨y₀, αi, .equ⟩ :: Γ_outer.
    -- Their fv ⊆ Γ_full.dom = insert y₀ Γ_outer.dom. So they CAN mention y₀.
    -- Actually no — by PrevalidExt, β.fv ⊆ Γ.dom where Γ is the context the body lives
    -- in. But when MEqRed.prevalidExt extracted PrevalidExt of stack from MEqRed.fOp,
    -- did the original stack entries refer to y₀ ?
    -- Tracing: The original outer MEqRed.fOp has stack `αi :: st'`, with body's MEqRed
    -- at extended ctx with stack `st'`. Each stack entry of st' is bound BEFORE the
    -- body's recursion, so its fv is bounded by the OUTER context's dom.
    -- So we should be able to derive y₀ ∉ fv stack from the OUTER context's prevalidExt,
    -- which exists in the input MEqRed.fOp. Let me extract it.
    have hpv_outer_st : PrevalidExt (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁) (αi :: st') :=
      MEqRed.prevalidExt (MEqRed.fOp L ht hbody trivial)
    -- Wait, that's circular — I'm reconstructing the input. Better: hbody y₀ hy₀L
    -- is the body MEqRed with stack st' at extended ctx. Its prevalidExt gives
    -- PrevalidExt at the extended ctx. Stack entries' fv bound within that.
    -- Alternative: use the EXISTING outer hpv from somewhere. The MEqRed.fOp
    -- input gives me access to (αi :: st') stack. From PrevalidExt at the INPUT
    -- context (which is what the input fOp lives in), each stack entry has fv ⊆
    -- that context's dom.
    -- The cleanest way: derive PrevalidExt of st' at outer ctx from PrevalidExt of
    -- stack (αi :: st') at outer ctx via tail. But I don't have the latter directly.
    -- Hmm. Let me just use the stack entries' fv bound from hpvE_full and
    -- explicitly check that no entry mentions y₀.
    -- hpvE_full : PrevalidExt (⟨y₀, αi, .equ⟩ :: Γ_outer) st'
    -- Each entry β ∈ st' has fv β ⊆ insert y₀ Γ_outer.dom.
    -- We want y₀ ∉ fv β. This requires showing the fv bound is actually ⊆ Γ_outer.dom,
    -- not just ⊆ insert y₀ Γ_outer.dom.
    -- This requires the stronger invariant: PrevalidExt's cons-form requires each
    -- entry's fv to be bounded by the ENTIRE context's dom. So the entry fv may
    -- include y₀.
    -- However! In an MPSS-derived stack, st' lives in Γ_outer (not in
    -- ⟨y₀, αi, .equ⟩ :: Γ_outer) — the cons is the BODY's local context, not the
    -- stack's. Let me check the Me-FOp constructor again.
    -- From Reductions.lean: `MEqRed.fOp` has `s := α :: s'` and the body recurses
    -- under `(⟨x, α, .equ⟩ :: Γ) s'`. So st' lives at extended ctx.
    -- So st' entries CAN mention y₀ in principle.
    -- Hmm, but in practice they don't because y₀ is a fresh witness picked AFTER
    -- the stack was determined. But that's a property of the construction, not
    -- of MEqRed alone.
    -- Way out: the OUTER input MEqRed.fOp has its own prevalidExt at outer Γ
    -- with stack (αi :: st'), built via MEqRed.prevalidExt. From there, st' entries'
    -- fv ⊆ outer Γ.dom (no y₀).
    have hpv_outer_inputst : PrevalidExt (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁) (αi :: st') := by
      -- Reconstruct via the input MEqRed.fOp.
      exact MEqRed.prevalidExt (MEqRed.fOp L ht hbody trivial)
    have hpv_outer_st_only : PrevalidExt (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁) st' := by
      cases hpv_outer_inputst with
      | cons hpv_tail _ _ => exact hpv_tail
    have hy₀_stack : ∀ β ∈ st', y₀ ∉ Term.fv β :=
      _y₀_notin_stack_fv_of_notin_dom hpv_outer_st_only hy₀_dom
    -- Now apply _MEqRed_rename_equ_no_fv. Need stack at the renamed (α') context
    -- to also be fresh — but the stack itself doesn't depend on α/α', so y₀ ∉ fv st'
    -- is the same statement.
    have ren := _MEqRed_rename_equ_no_fv hyz hy₀_dom' hyf_dom hy₀_αi
      hy₀_fvbd hy₀_fvbd' hy₀_stack ihbody_y₀_norm
    simpa using ren

/-! ### §8.2a. Phase 5d: `MEqRed.equ_head_replace_univ_exists`

A parallel form of `equ_head_replace` that takes an `AvoidsProUniv`
premise instead of the Bool `avoidsPro` + `cofinDomFresh` triple, and
returns an existence statement preserving `AvoidsProUniv` on the output.

**Why this matters.** The original `equ_head_replace` samples cofinite
arms at `pickFresh L` and then renames the result via `rename_stray` /
`rename_sub` / `_rename_equ`. This works but threads two Bool freshness
premises (`avoidsPro` + `cofinDomFresh`) that callers must discharge,
and the Bool `avoidsPro` is fragile under future rename compositions
(its sample point shifts when `L` widens — the alpha-equivariance trap).

`AvoidsProUniv` quantifies universally over the cofinite witness:
`∀ yfresh ∉ L, AvoidsProUniv (hbody yfresh _) x`. So the `bet`/`fun_`/
`fOp` arms here can recurse DIRECTLY at any chosen `yfresh` (we use the
output's own cofinite witness — no `pickFresh L` sample, no rename).
This sidesteps the alpha-equivariance trap structurally: there is never
a moment where we "translate" from sample `pickFresh L` to sample
`pickFresh L'`. The `Me-Pro y` arm becomes immediate from
`AvoidsProUniv_pro` (`y_i ≠ y` is part of the universal predicate).

The output preserves `AvoidsProUniv h' y`, enabling consumers that
compose multiple `equ_head_replace_univ_exists` calls.

**Existence form.** We return `∃ h' : MEqRed ..., AvoidsProUniv h' y`
because the cofinite arms construct each body branch via `Classical.choice`
on the inductive existence hypothesis. -/

/-- Equ-head bound-term replacement preserving a *predicate* on
avoidance names AND `CofinAvoidsProSelfUniv`.

The predicate `Avoid : String → Prop` captures the set of names whose
avoidance must be preserved on the output. Critically, in the fOp
Case A delegation from `stack_replace_univ_exists`, we need to preserve
avoidance of BOTH the swapped binder name `y` AND the cofinite witness
`yfresh` (for output `CofinAvoidsProSelfUniv`).

The predicate-form makes this preservation modular: caller supplies any
predicate they want (e.g. `fun z => z = y ∨ z = yfresh` or
`fun _ => True` for the trivial form). -/
theorem MEqRed.equ_head_replace_univ_exists_pred
    {Γ₁ Γ₂ : Ctx} {st : Stack} {y : String} {α α' u u' : Term}
    (h : MEqRed (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁) st u u')
    (hLCα' : Term.LC α') (hfvα' : Term.fv α' ⊆ Γ₁.dom)
    (Avoid : String → Prop)
    (hyAvoid : Avoid y)
    (hAvoidAll : ∀ z, Avoid z → AvoidsProUniv h z)
    (hCAU : CofinAvoidsProSelfUniv h) :
    ∃ h' : MEqRed (Γ₂ ++ ⟨y, α', .equ⟩ :: Γ₁) st u u',
      (∀ z, Avoid z → AvoidsProUniv h' z) ∧
      CofinAvoidsProSelfUniv h' := by
  classical
  revert hyAvoid hAvoidAll hCAU
  generalize hΓ : (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁) = Γ at h
  induction h generalizing Γ₂ Avoid with
  | @pro Γ st' yi β β' hpv heq hβ ihβ =>
    intro hyAvoid hAvoidAll hCAU
    subst hΓ
    rw [CofinAvoidsProSelfUniv_pro] at hCAU
    -- Extract `yi ≠ z` from hAvoidAll for each z in Avoid; the rewrite
    -- happens on demand.
    have hyiy : yi ≠ y := by
      have := hAvoidAll y hyAvoid
      rw [AvoidsProUniv_pro] at this
      exact this.1
    have hpv' : PrevalidExt (Γ₂ ++ ⟨y, α', .equ⟩ :: Γ₁) st' :=
      PrevalidExt.equ_head_replace_mid hpv hLCα' hfvα'
    have heq' := _equBinds_equ_head_swap_neq (α' := α') hyiy heq
    -- Recurse with the same Avoid predicate; need to derive
    -- `∀ z, Avoid z → AvoidsProUniv hβ z` from the input's avoidance.
    have hAvoidInner : ∀ z, Avoid z → AvoidsProUniv hβ z := by
      intro z hz
      have := hAvoidAll z hz
      rw [AvoidsProUniv_pro] at this
      exact this.2
    obtain ⟨hβ', hβA, hβC⟩ := ihβ (Avoid := Avoid) (Γ₂ := Γ₂) rfl hyAvoid hAvoidInner hCAU
    refine ⟨MEqRed.pro hpv' heq' hβ', ?_, ?_⟩
    · intro z hz
      rw [AvoidsProUniv_pro]
      refine ⟨?_, hβA z hz⟩
      have := hAvoidAll z hz
      rw [AvoidsProUniv_pro] at this
      exact this.1
    · rw [CofinAvoidsProSelfUniv_pro]; exact hβC
  | @bet Γ st' tBound v0 v0' bd bd' L hLCt hbody _hUni hv ihbody ihv =>
    intro hyAvoid hAvoidAll hCAU
    subst hΓ
    rw [CofinAvoidsProSelfUniv_bet] at hCAU
    obtain ⟨hbC, hvC⟩ := hCAU
    have body_each : ∀ yfresh, yfresh ∉ L →
        ∃ h' : MEqRed (Γ₂ ++ ⟨y, α', .equ⟩ :: Γ₁) st'
                  (bd^[yfresh]) (bd'^[yfresh]),
          (∀ z, Avoid z → AvoidsProUniv h' z) ∧
          CofinAvoidsProSelfUniv h' := by
      intro yfresh hyf
      have hAvoidBody : ∀ z, Avoid z → AvoidsProUniv (hbody yfresh hyf) z := by
        intro z hz
        have := hAvoidAll z hz
        rw [AvoidsProUniv_bet] at this
        exact this.1 yfresh hyf
      exact ihbody yfresh hyf (Avoid := Avoid) (Γ₂ := Γ₂) rfl hyAvoid hAvoidBody (hbC yfresh hyf)
    let body_witness : ∀ yfresh, yfresh ∉ L →
        MEqRed (Γ₂ ++ ⟨y, α', .equ⟩ :: Γ₁) st'
          (bd^[yfresh]) (bd'^[yfresh]) :=
      fun yfresh hyf => (body_each yfresh hyf).choose
    have body_witness_specs :
        ∀ yfresh (hyf : yfresh ∉ L),
          (∀ z, Avoid z → AvoidsProUniv (body_witness yfresh hyf) z) ∧
          CofinAvoidsProSelfUniv (body_witness yfresh hyf) :=
      fun yfresh hyf => (body_each yfresh hyf).choose_spec
    have hAvoidV : ∀ z, Avoid z → AvoidsProUniv hv z := by
      intro z hz
      have := hAvoidAll z hz
      rw [AvoidsProUniv_bet] at this
      exact this.2
    obtain ⟨hv', hvA, hvC'⟩ := ihv (Avoid := Avoid) (Γ₂ := Γ₂) rfl hyAvoid hAvoidV hvC
    refine ⟨MEqRed.bet L hLCt body_witness trivial hv', ?_, ?_⟩
    · intro z hz
      rw [AvoidsProUniv_bet]
      exact ⟨fun yfresh hyf => (body_witness_specs yfresh hyf).1 z hz, hvA z hz⟩
    · rw [CofinAvoidsProSelfUniv_bet]
      exact ⟨fun yfresh hyf => (body_witness_specs yfresh hyf).2, hvC'⟩
  | @top Γ st' hpv =>
    intro hyAvoid hAvoidAll hCAU
    subst hΓ
    have hpv' : PrevalidExt (Γ₂ ++ ⟨y, α', .equ⟩ :: Γ₁) st' :=
      PrevalidExt.equ_head_replace_mid hpv hLCα' hfvα'
    refine ⟨MEqRed.top hpv', ?_, ?_⟩
    · intro z _; rw [AvoidsProUniv_top]; trivial
    · rw [CofinAvoidsProSelfUniv_top]; trivial
  | @app Γ st' u_ u_' v_ v_' hu hv ihu ihv =>
    intro hyAvoid hAvoidAll hCAU
    subst hΓ
    rw [CofinAvoidsProSelfUniv_app] at hCAU
    obtain ⟨huC, hvC⟩ := hCAU
    have hAvoidU : ∀ z, Avoid z → AvoidsProUniv hu z := by
      intro z hz
      have := hAvoidAll z hz
      rw [AvoidsProUniv_app] at this
      exact this.1
    have hAvoidV : ∀ z, Avoid z → AvoidsProUniv hv z := by
      intro z hz
      have := hAvoidAll z hz
      rw [AvoidsProUniv_app] at this
      exact this.2
    obtain ⟨hu', huA, huC'⟩ := ihu (Avoid := Avoid) (Γ₂ := Γ₂) rfl hyAvoid hAvoidU huC
    obtain ⟨hv', hvA, hvC'⟩ := ihv (Avoid := Avoid) (Γ₂ := Γ₂) rfl hyAvoid hAvoidV hvC
    refine ⟨MEqRed.app hu' hv', ?_, ?_⟩
    · intro z hz; rw [AvoidsProUniv_app]; exact ⟨huA z hz, hvA z hz⟩
    · rw [CofinAvoidsProSelfUniv_app]; exact ⟨huC', hvC'⟩
  | @var Γ st' yi hpv =>
    intro hyAvoid hAvoidAll hCAU
    subst hΓ
    have hpv' : PrevalidExt (Γ₂ ++ ⟨y, α', .equ⟩ :: Γ₁) st' :=
      PrevalidExt.equ_head_replace_mid hpv hLCα' hfvα'
    refine ⟨MEqRed.var hpv', ?_, ?_⟩
    · intro z _; rw [AvoidsProUniv_var]; trivial
    · rw [CofinAvoidsProSelfUniv_var]; trivial
  | @fun_ Γ tt tt' bd bd' L ht hbody _hUni iht ihbody =>
    intro hyAvoid hAvoidAll hCAU
    subst hΓ
    rw [CofinAvoidsProSelfUniv_fun_] at hCAU
    obtain ⟨htC, hbC⟩ := hCAU
    have hAvoidT : ∀ z, Avoid z → AvoidsProUniv ht z := by
      intro z hz
      have := hAvoidAll z hz
      rw [AvoidsProUniv_fun_] at this
      exact this.1
    obtain ⟨ht', htA, htC'⟩ := iht (Avoid := Avoid) (Γ₂ := Γ₂) rfl hyAvoid hAvoidT htC
    have body_each : ∀ yfresh, yfresh ∉ L →
        ∃ h' : MEqRed (⟨yfresh, tt, .sub⟩ :: (Γ₂ ++ ⟨y, α', .equ⟩ :: Γ₁)) []
                  (bd^[yfresh]) (bd'^[yfresh]),
          (∀ z, Avoid z → AvoidsProUniv h' z) ∧
          CofinAvoidsProSelfUniv h' := by
      intro yfresh hyf
      have hAvoidBody : ∀ z, Avoid z → AvoidsProUniv (hbody yfresh hyf) z := by
        intro z hz
        have := hAvoidAll z hz
        rw [AvoidsProUniv_fun_] at this
        exact this.2 yfresh hyf
      have ihres := ihbody yfresh hyf (Avoid := Avoid)
        (Γ₂ := ⟨yfresh, tt, .sub⟩ :: Γ₂)
        (by simp) hyAvoid hAvoidBody (hbC yfresh hyf)
      obtain ⟨h_inner, hAv_inner, hC_inner⟩ := ihres
      refine ⟨?_, ?_, ?_⟩
      · simpa using h_inner
      · intro z hz
        simpa [AvoidsProUniv_subst_eq_ctx] using hAv_inner z hz
      · change CofinAvoidsProSelfUniv h_inner; exact hC_inner
    let body_witness : ∀ yfresh, yfresh ∉ L →
        MEqRed (⟨yfresh, tt, .sub⟩ :: (Γ₂ ++ ⟨y, α', .equ⟩ :: Γ₁)) []
          (bd^[yfresh]) (bd'^[yfresh]) :=
      fun yfresh hyf => (body_each yfresh hyf).choose
    have body_witness_specs :
        ∀ yfresh (hyf : yfresh ∉ L),
          (∀ z, Avoid z → AvoidsProUniv (body_witness yfresh hyf) z) ∧
          CofinAvoidsProSelfUniv (body_witness yfresh hyf) :=
      fun yfresh hyf => (body_each yfresh hyf).choose_spec
    refine ⟨MEqRed.fun_ L ht' body_witness trivial, ?_, ?_⟩
    · intro z hz
      rw [AvoidsProUniv_fun_]
      exact ⟨htA z hz, fun yfresh hyf => (body_witness_specs yfresh hyf).1 z hz⟩
    · rw [CofinAvoidsProSelfUniv_fun_]
      exact ⟨htC', fun yfresh hyf => (body_witness_specs yfresh hyf).2⟩
  | @tAp Γ st' u_ hpv hLCu hfv =>
    intro hyAvoid hAvoidAll hCAU
    subst hΓ
    have hpv' : PrevalidExt (Γ₂ ++ ⟨y, α', .equ⟩ :: Γ₁) st' :=
      PrevalidExt.equ_head_replace_mid hpv hLCα' hfvα'
    have hfv' : Term.fv u_ ⊆ Ctx.dom (Γ₂ ++ ⟨y, α', .equ⟩ :: Γ₁) := by
      rw [← _Ctx_dom_eq_under_equ_head_replace (α := α) (α' := α')]; exact hfv
    refine ⟨MEqRed.tAp hpv' hLCu hfv', ?_, ?_⟩
    · intro z _; rw [AvoidsProUniv_tAp]; trivial
    · rw [CofinAvoidsProSelfUniv_tAp]; trivial
  | @fOp Γ st' tt tt' αi bd bd' L ht hbody _hUni iht ihbody =>
    intro hyAvoid hAvoidAll hCAU
    subst hΓ
    rw [CofinAvoidsProSelfUniv_fOp] at hCAU
    obtain ⟨htC, hbC⟩ := hCAU
    have hAvoidT : ∀ z, Avoid z → AvoidsProUniv ht z := by
      intro z hz
      have := hAvoidAll z hz
      rw [AvoidsProUniv_fOp] at this
      exact this.1
    obtain ⟨ht', htA, htC'⟩ := iht (Avoid := Avoid) (Γ₂ := Γ₂) rfl hyAvoid hAvoidT htC
    -- For each cofinite witness yfresh, we recurse with EXTENDED Avoid =
    -- Avoid ∪ {yfresh}, which gives us the body's avoidance of both the
    -- input's tracked names AND the cofinite witness itself (for output
    -- CofinAvoidsProSelfUniv).
    have body_each : ∀ yfresh, yfresh ∉ L →
        ∃ h' : MEqRed (⟨yfresh, αi, .equ⟩ :: (Γ₂ ++ ⟨y, α', .equ⟩ :: Γ₁)) st'
                  (bd^[yfresh]) (bd'^[yfresh]),
          (∀ z, Avoid z → AvoidsProUniv h' z) ∧
          AvoidsProUniv h' yfresh ∧
          CofinAvoidsProSelfUniv h' := by
      intro yfresh hyf
      let Avoid' : String → Prop := fun z => Avoid z ∨ z = yfresh
      have hAvoidExtended : ∀ z, Avoid' z → AvoidsProUniv (hbody yfresh hyf) z := by
        intro z hz
        cases hz with
        | inl hz =>
          have := hAvoidAll z hz
          rw [AvoidsProUniv_fOp] at this
          exact this.2 yfresh hyf
        | inr hzeq =>
          rw [hzeq]
          exact (hbC yfresh hyf).1
      have hyAvoidExt : Avoid' y := Or.inl hyAvoid
      have ihres := ihbody yfresh hyf (Avoid := Avoid')
        (Γ₂ := ⟨yfresh, αi, .equ⟩ :: Γ₂)
        (by simp) hyAvoidExt hAvoidExtended (hbC yfresh hyf).2
      obtain ⟨h_inner, hAv_inner, hC_inner⟩ := ihres
      refine ⟨?_, ?_, ?_, ?_⟩
      · simpa using h_inner
      · intro z hz
        simpa [AvoidsProUniv_subst_eq_ctx] using hAv_inner z (Or.inl hz)
      · simpa [AvoidsProUniv_subst_eq_ctx] using hAv_inner yfresh (Or.inr rfl)
      · change CofinAvoidsProSelfUniv h_inner; exact hC_inner
    let body_witness : ∀ yfresh, yfresh ∉ L →
        MEqRed (⟨yfresh, αi, .equ⟩ :: (Γ₂ ++ ⟨y, α', .equ⟩ :: Γ₁)) st'
          (bd^[yfresh]) (bd'^[yfresh]) :=
      fun yfresh hyf => (body_each yfresh hyf).choose
    have body_witness_specs :
        ∀ yfresh (hyf : yfresh ∉ L),
          (∀ z, Avoid z → AvoidsProUniv (body_witness yfresh hyf) z) ∧
          AvoidsProUniv (body_witness yfresh hyf) yfresh ∧
          CofinAvoidsProSelfUniv (body_witness yfresh hyf) :=
      fun yfresh hyf => (body_each yfresh hyf).choose_spec
    refine ⟨MEqRed.fOp L ht' body_witness trivial, ?_, ?_⟩
    · intro z hz
      rw [AvoidsProUniv_fOp]
      exact ⟨htA z hz, fun yfresh hyf => (body_witness_specs yfresh hyf).1 z hz⟩
    · rw [CofinAvoidsProSelfUniv_fOp]
      refine ⟨htC', fun yfresh hyf => ?_⟩
      exact ⟨(body_witness_specs yfresh hyf).2.1, (body_witness_specs yfresh hyf).2.2⟩

theorem MEqRed.equ_head_replace_univ_exists
    {Γ₁ Γ₂ : Ctx} {st : Stack} {y : String} {α α' u u' : Term}
    (h : MEqRed (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁) st u u')
    (hLCα' : Term.LC α') (hfvα' : Term.fv α' ⊆ Γ₁.dom)
    (hUniv : AvoidsProUniv h y)
    (hCAU : CofinAvoidsProSelfUniv h) :
    ∃ h' : MEqRed (Γ₂ ++ ⟨y, α', .equ⟩ :: Γ₁) st u u',
      AvoidsProUniv h' y ∧ CofinAvoidsProSelfUniv h' := by
  obtain ⟨h', hAv, hC⟩ :=
    MEqRed.equ_head_replace_univ_exists_pred h hLCα' hfvα'
      (Avoid := fun z => z = y) rfl
      (by intro z hz; subst hz; exact hUniv) hCAU
  exact ⟨h', hAv y rfl, hC⟩

/-! ### §8.3. `MSubRed.equ_head_replace` -/

/-- **MSubRed analog of `MEqRed.equ_head_replace`**: replace the bound
term of a `.equ`-head context for an `MSubRed` derivation. The `pro`
arm uses `_subBinds_equ_head_swap` directly (no avoidance premise needed
— `.sub`-typed lookups never observe the `.equ`-head's bound term). The
`equ` arm delegates to `MEqRed.equ_head_replace`. The `fun_`/`fOp`
cofinite arms mirror the `MEqRed` proof, using
`MSubRed.rename_sub` / `_MSubRed_rename_equ_no_fv`. -/
noncomputable def MSubRed.equ_head_replace
    {Γ₁ Γ₂ : Ctx} {st : Stack} {y : String} {α α' u u' : Term}
    (h : MSubRed (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁) st u u')
    (hLCα' : Term.LC α') (hfvα' : Term.fv α' ⊆ Γ₁.dom)
    (hAvoid : msAvoidsPro h y = true)
    (hFresh : msCofinDomFresh h y = true) :
    MSubRed (Γ₂ ++ ⟨y, α', .equ⟩ :: Γ₁) st u u' := by
  classical
  generalize hΓ : (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁) = Γ at h
  induction h generalizing Γ₂ with
  | @pro Γ st' yi t' hpv hsb =>
    subst hΓ
    have hpv' : PrevalidExt (Γ₂ ++ ⟨y, α', .equ⟩ :: Γ₁) st' :=
      PrevalidExt.equ_head_replace_mid hpv hLCα' hfvα'
    have hsb' := _subBinds_equ_head_swap (α' := α') hsb
    exact MSubRed.pro hpv' hsb'
  | @top Γ st' u_ hpv hLCu hfv =>
    subst hΓ
    have hpv' : PrevalidExt (Γ₂ ++ ⟨y, α', .equ⟩ :: Γ₁) st' :=
      PrevalidExt.equ_head_replace_mid hpv hLCα' hfvα'
    have hfv' : Term.fv u_ ⊆ Ctx.dom (Γ₂ ++ ⟨y, α', .equ⟩ :: Γ₁) := by
      rw [← _Ctx_dom_eq_under_equ_head_replace (α := α) (α' := α')]; exact hfv
    exact MSubRed.top hpv' hLCu hfv'
  | @equ Γ st' u_ v_ hpv heq =>
    subst hΓ
    rw [msAvoidsPro_equ] at hAvoid
    rw [msCofinDomFresh_equ] at hFresh
    have hpv' : PrevalidExt (Γ₂ ++ ⟨y, α', .equ⟩ :: Γ₁) st' :=
      PrevalidExt.equ_head_replace_mid hpv hLCα' hfvα'
    have heq' := MEqRed.equ_head_replace heq hLCα' hfvα' hAvoid hFresh
    exact MSubRed.equ hpv' heq'
  | @app Γ st' u_ u_' v_ hu hLCv hfvv ihu =>
    subst hΓ
    rw [msAvoidsPro_app] at hAvoid
    rw [msCofinDomFresh_app] at hFresh
    have hLCv' : Term.LC v_ := hLCv
    have hfvv' : Term.fv v_ ⊆ Ctx.dom (Γ₂ ++ ⟨y, α', .equ⟩ :: Γ₁) := by
      rw [← _Ctx_dom_eq_under_equ_head_replace (α := α) (α' := α')]; exact hfvv
    have ihu' := ihu (Γ₂ := Γ₂) rfl hAvoid hFresh
    exact MSubRed.app ihu' hLCv' hfvv'
  | @fun_ Γ tt bd bd' L hLCt hbody _hUni ihbody =>
    subst hΓ
    rw [msAvoidsPro_fun_] at hAvoid
    rw [msCofinDomFresh_fun_] at hFresh
    -- hAvoid and hFresh both sample at pickFresh (L_aug L bd bd' y).
    obtain ⟨hFresh_dom_dec, hFresh_body⟩ := Bool.and_eq_true _ _ |>.mp hFresh
    have hy₀_dom : pickFresh (msAvoidsPro_L_aug L bd bd' y) ∉
        Ctx.dom (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁) :=
      decide_eq_true_eq.mp hFresh_dom_dec
    have hy₀_fvbd : pickFresh (msAvoidsPro_L_aug L bd bd' y) ∉ Term.fv bd :=
      msAvoidsPro_L_aug_notMem_body
    have hy₀_fvbd' : pickFresh (msAvoidsPro_L_aug L bd bd' y) ∉ Term.fv bd' :=
      msAvoidsPro_L_aug_notMem_body'
    let y₀ := pickFresh (msAvoidsPro_L_aug L bd bd' y)
    have hy₀L : y₀ ∉ L := msAvoidsPro_L_aug_notMem_L
    have hy₀_dom' : y₀ ∉ Ctx.dom (Γ₂ ++ ⟨y, α', .equ⟩ :: Γ₁) := by
      rw [← _Ctx_dom_eq_under_equ_head_replace (α := α) (α' := α')]; exact hy₀_dom
    have ihbody_y₀ := ihbody y₀ hy₀L
      (Γ₂ := ⟨y₀, tt, .sub⟩ :: Γ₂) (by simp) hAvoid hFresh_body
    refine MSubRed.fun_ (L ∪ Ctx.dom (Γ₂ ++ ⟨y, α', .equ⟩ :: Γ₁) ∪ {y₀}) hLCt ?_ trivial
    intro yfresh hyfresh
    simp only [Finset.mem_union, Finset.mem_singleton] at hyfresh
    push_neg at hyfresh
    obtain ⟨⟨hyfL, hyf_dom⟩, hyf_y₀⟩ := hyfresh
    -- Extract data: Prevalid of outer, LC of tt, fv tt ⊆ outer.dom from
    -- the body's prevalidExt at extended ctx.
    have ihbody_y₀_norm :
        MSubRed (⟨y₀, tt, .sub⟩ :: (Γ₂ ++ ⟨y, α', .equ⟩ :: Γ₁)) []
          (bd^[y₀]) (bd'^[y₀]) := by simpa using ihbody_y₀
    have hpvE_full : PrevalidExt (⟨y₀, tt, .sub⟩ :: (Γ₂ ++ ⟨y, α', .equ⟩ :: Γ₁)) [] :=
      MSubRed.prevalidExt ihbody_y₀_norm
    have hpv_full : Prevalid (⟨y₀, tt, .sub⟩ :: (Γ₂ ++ ⟨y, α', .equ⟩ :: Γ₁)) :=
      extractPrevalid hpvE_full
    have hpv_outer : Prevalid (Γ₂ ++ ⟨y, α', .equ⟩ :: Γ₁) := by
      cases hpv_full with
      | sub hpv _ _ _ => exact hpv
    have hLCtt : Term.LC tt := by cases hpv_full with | sub _ _ _ hLC => exact hLC
    have hfvtt : Term.fv tt ⊆ Ctx.dom (Γ₂ ++ ⟨y, α', .equ⟩ :: Γ₁) := by
      cases hpv_full with | sub _ _ hfv _ => exact hfv
    have ren := MSubRed.rename_sub hpv_outer hLCtt hfvtt
      hy₀_dom' hyf_dom hy₀_fvbd hy₀_fvbd'
      (by intro β hβ; cases hβ) ihbody_y₀_norm
    simpa using ren
  | @fOp Γ st' tt αi bd bd' L hLCt hbody _hUni ihbody =>
    subst hΓ
    rw [msAvoidsPro_fOp] at hAvoid
    rw [msCofinDomFresh_fOp] at hFresh
    obtain ⟨hFresh_dom_dec, hFresh_body⟩ := Bool.and_eq_true _ _ |>.mp hFresh
    have hy₀_dom : pickFresh (msAvoidsPro_L_aug L bd bd' y) ∉
        Ctx.dom (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁) :=
      decide_eq_true_eq.mp hFresh_dom_dec
    have hy₀_fvbd : pickFresh (msAvoidsPro_L_aug L bd bd' y) ∉ Term.fv bd :=
      msAvoidsPro_L_aug_notMem_body
    have hy₀_fvbd' : pickFresh (msAvoidsPro_L_aug L bd bd' y) ∉ Term.fv bd' :=
      msAvoidsPro_L_aug_notMem_body'
    let y₀ := pickFresh (msAvoidsPro_L_aug L bd bd' y)
    have hy₀L : y₀ ∉ L := msAvoidsPro_L_aug_notMem_L
    have hy₀_dom' : y₀ ∉ Ctx.dom (Γ₂ ++ ⟨y, α', .equ⟩ :: Γ₁) := by
      rw [← _Ctx_dom_eq_under_equ_head_replace (α := α) (α' := α')]; exact hy₀_dom
    have ihbody_y₀ := ihbody y₀ hy₀L
      (Γ₂ := ⟨y₀, αi, .equ⟩ :: Γ₂) (by simp) hAvoid hFresh_body
    refine MSubRed.fOp (L ∪ Ctx.dom (Γ₂ ++ ⟨y, α', .equ⟩ :: Γ₁) ∪ {y₀}) hLCt ?_ trivial
    intro yfresh hyfresh
    simp only [Finset.mem_union, Finset.mem_singleton] at hyfresh
    push_neg at hyfresh
    obtain ⟨⟨hyfL, hyf_dom⟩, hyf_y₀⟩ := hyfresh
    have hyz : y₀ ≠ yfresh := fun h' => hyf_y₀ h'.symm
    have ihbody_y₀_norm :
        MSubRed (⟨y₀, αi, .equ⟩ :: (Γ₂ ++ ⟨y, α', .equ⟩ :: Γ₁)) st'
          (bd^[y₀]) (bd'^[y₀]) := by simpa using ihbody_y₀
    have hpvE_full : PrevalidExt (⟨y₀, αi, .equ⟩ :: (Γ₂ ++ ⟨y, α', .equ⟩ :: Γ₁)) st' :=
      MSubRed.prevalidExt ihbody_y₀_norm
    have hpv_full : Prevalid (⟨y₀, αi, .equ⟩ :: (Γ₂ ++ ⟨y, α', .equ⟩ :: Γ₁)) :=
      extractPrevalid hpvE_full
    have hfv_αi : Term.fv αi ⊆ Ctx.dom (Γ₂ ++ ⟨y, α', .equ⟩ :: Γ₁) := by
      cases hpv_full with | equ _ _ hfv _ => exact hfv
    have hy₀_αi : y₀ ∉ Term.fv αi := fun h' => hy₀_dom' (hfv_αi h')
    -- Stack freshness for y₀ from the input MSubRed.fOp.
    have hpv_outer_inputst : PrevalidExt (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁) (αi :: st') :=
      MSubRed.prevalidExt (MSubRed.fOp L hLCt hbody trivial)
    have hpv_outer_st_only : PrevalidExt (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁) st' := by
      cases hpv_outer_inputst with
      | cons hpv_tail _ _ => exact hpv_tail
    have hy₀_stack : ∀ β ∈ st', y₀ ∉ Term.fv β :=
      _y₀_notin_stack_fv_of_notin_dom hpv_outer_st_only hy₀_dom
    have ren := _MSubRed_rename_equ_no_fv hyz hy₀_dom' hyf_dom hy₀_αi
      hy₀_fvbd hy₀_fvbd' hy₀_stack ihbody_y₀_norm
    simpa using ren

/-! ## §9. `stack_replace` — bound-term replacement on a stack element

Phase 3 of the β-residual unblock (per `AXIOMS.md` "Discharge plan for
the β-residuals" item §2). Given `MEqRed Γ (s_pre ++ α :: s_post) u u'`
and `MEqRed Γ [] α α'`, produce `MEqRed Γ (s_pre ++ α' :: s_post) u u'`.

The natural specialization (`s_pre := []`) gives `stack_head_replace`:
`MEqRed Γ (α :: s) u u' → MEqRed Γ [] α α' → MEqRed Γ (α' :: s) u u'`.
This is the form consumed by `Lemma_2_DiamondMEqRed_ctx_axiom`'s App×App
arm, which lifts the operator's join across `Γ; v::s ↣ Γ; v'::s`.

### Generalization to `s_pre, s_post`

The `Me-App` constructor at `s = s_pre ++ α :: s_post` recurses on the
operator at stack `(v :: s_pre) ++ α :: s_post` — i.e. the α we want to
swap is at INTERIOR position. So we generalize stack_replace to take
`s_pre s_post : Stack` and recurse with `s_pre := v :: s_pre`. The
`stack_head_replace` form is a thin wrapper specializing `s_pre := []`.

### Per-constructor sketches

* **`pro`**: Recurse on the inner derivation; rebuild PrevalidExt with
  the new stack via `PrevalidExt.stack_replace_mid` (a tiny helper that
  swaps a stack entry preserving `LC` and `fv ⊆ Γ.dom`).
* **`top`/`var`/`tAp`**: Just rebuild PrevalidExt with the swapped stack.
* **`app`**: Recurse on the operator at extended `s_pre`; pass the
  operand through (lives at empty stack — α isn't in scope there).
* **`bet`**: Recurse on the body (cofinite). The body lives at the same
  Γ with stack matching ours, so just propagate `s_pre/s_post`.
* **`fun_`**: Vacuous when our stack is non-empty (`fun_` requires `[]`).
* **`fOp`**: Two sub-cases on `s_pre`:
  - **Case A** (`s_pre = []`): The constructor's stack matches `α :: s_post`.
    The body lives at `(⟨z, α, .equ⟩ :: Γ) s_post`. Delegate to
    `MEqRed.equ_head_replace` with `Γ₁ = Γ`, `Γ₂ = []`, `y = z` to
    swap `α → α'` in the equ-binding. Then rebuild fOp with α'.
  - **Case B** (`s_pre = β :: s_pre'`): The constructor's stack head is
    `β` (not α); recurse on the body at extended Γ with `s_pre := s_pre'`.

### Why we need `cofinAvoidsProSelf`

The fOp Case A delegates to `equ_head_replace` with `y = pickFresh L`
(internal to the proof). `equ_head_replace` requires `avoidsPro body
pickFresh = true` — but the caller of `stack_replace` doesn't know about
`pickFresh L`. We capture this requirement in the Bool function
`cofinAvoidsProSelf` (in `Pss.Mpss.AvoidsPro` §3.3): at every fOp arm,
it asserts `avoidsPro (body pickFresh) pickFresh = true`. The premise
threads through the recursion deterministically. Phase 4 callers will
discharge this premise at the consumer site.

NOT alpha-equivariance: like `cofinDomFresh`, `cofinAvoidsProSelf` is a
deterministic Bool function of the derivation's shape, sampled at the
SAME canonical witness as the rest of the freshness machinery. -/

/-! ### §9.1. PrevalidExt stack-element swap helper -/

/-- `(s_pre ++ α :: s_post)` and `(s_pre ++ α' :: s_post)` have the same
`PrevalidExt`-ness when `α'` is well-formed (LC, fv ⊆ Γ.dom). The proof
is by induction on `s_pre`. -/
private noncomputable def PrevalidExt.stack_replace_mid
    {Γ : Ctx} {s_pre s_post : Stack} {α α' : Term}
    (h : PrevalidExt Γ (s_pre ++ α :: s_post))
    (hLCα' : Term.LC α') (hfvα' : Term.fv α' ⊆ Γ.dom) :
    PrevalidExt Γ (s_pre ++ α' :: s_post) := by
  induction s_pre with
  | nil =>
    -- (α :: s_post) → (α' :: s_post)
    cases h with
    | cons hpv _ _ => exact PrevalidExt.cons hpv hLCα' hfvα'
  | cons β rest ih =>
    -- (β :: rest ++ α :: s_post) → (β :: rest ++ α' :: s_post)
    cases h with
    | cons hpv hLCβ hfvβ =>
      exact PrevalidExt.cons (ih hpv) hLCβ hfvβ

/-! ### §9.2. `MEqRed.stack_replace` (interior stack-element swap) -/

/-- **Replace a stack element bound term** at position `s_pre`-deep.

Given:
* `h : MEqRed (Γ₂ ++ Γ₁) (s_pre ++ α :: s_post) u u'` — input derivation.
* `hLCα'`, `hfvα'` — well-formedness data for the new α' (bounded by Γ₁,
  the BASE context that doesn't grow under recursion through fOp Case B).
* `hFresh : cofinDomFresh h = true` — canonical witnesses fresh.
* `hAPS : cofinAvoidsProSelf h = true` — body avoids pro on its
  canonical witness at every fOp.

Produces: `MEqRed (Γ₂ ++ Γ₁) (s_pre ++ α' :: s_post) u u'`.

The proof generalizes Γ₂ (which grows through fOp Case B's binder
extension) while keeping Γ₁ (the base context bounding α'.fv) fixed —
mirroring the structure of `MEqRed.equ_head_replace`.

The `Γ₂ = []`, `s_pre = []` specialization is `MEqRed.stack_head_replace`. -/
noncomputable def MEqRed.stack_replace
    {Γ₁ : Ctx} {α α' : Term}
    (hLCα' : Term.LC α') (hfvα' : Term.fv α' ⊆ Γ₁.dom) :
    {Γ₂ : Ctx} → {s_pre s_post : Stack} → {u u' : Term} →
    (h : MEqRed (Γ₂ ++ Γ₁) (s_pre ++ α :: s_post) u u') →
    cofinDomFresh h = true → cofinAvoidsProSelf h = true →
    MEqRed (Γ₂ ++ Γ₁) (s_pre ++ α' :: s_post) u u' := by
  intro Γ₂ s_pre s_post u u' h hFresh hAPS
  classical
  generalize hΓ : (Γ₂ ++ Γ₁) = Γ at h
  generalize hS : (s_pre ++ α :: s_post) = stk at h
  induction h generalizing Γ₂ s_pre with
  | @pro Γ stk' yi β β' hpv heq hβ ihβ =>
    subst hΓ
    subst hS
    rw [cofinDomFresh_pro] at hFresh
    rw [cofinAvoidsProSelf_pro] at hAPS
    have hpv' : PrevalidExt (Γ₂ ++ Γ₁) (s_pre ++ α' :: s_post) :=
      PrevalidExt.stack_replace_mid hpv hLCα' (by
        intro x hx
        have := hfvα' hx
        rw [Ctx.dom_append]; exact Finset.mem_union.mpr (Or.inr this))
    exact MEqRed.pro hpv' heq (ihβ (Γ₂ := Γ₂) (s_pre := s_pre) rfl rfl hFresh hAPS)
  | @bet Γ stk' tBound v0 v0' bd bd' L hLCt hbody _hUni hv ihbody ihv =>
    subst hΓ
    subst hS
    rw [cofinDomFresh_bet] at hFresh
    rw [cofinAvoidsProSelf_bet] at hAPS
    obtain ⟨hFresh_left_v, hFresh_v⟩ := Bool.and_eq_true _ _ |>.mp hFresh
    obtain ⟨hFresh_left_body, hFresh_body⟩ :=
      Bool.and_eq_true _ _ |>.mp hFresh_left_v
    obtain ⟨hFresh_left_fvbd', hFresh_fvbd'_dec⟩ :=
      Bool.and_eq_true _ _ |>.mp hFresh_left_body
    obtain ⟨hFresh_dom_dec, hFresh_fvbd_dec⟩ :=
      Bool.and_eq_true _ _ |>.mp hFresh_left_fvbd'
    obtain ⟨hAPS_body, hAPS_v⟩ := Bool.and_eq_true _ _ |>.mp hAPS
    have hy₀_dom : pickFresh L ∉ Ctx.dom (Γ₂ ++ Γ₁) :=
      decide_eq_true_eq.mp hFresh_dom_dec
    have hy₀_fvbd : pickFresh L ∉ Term.fv bd :=
      decide_eq_true_eq.mp hFresh_fvbd_dec
    have hy₀_fvbd' : pickFresh L ∉ Term.fv bd' :=
      decide_eq_true_eq.mp hFresh_fvbd'_dec
    let y₀ := pickFresh L
    have hy₀L : y₀ ∉ L := pickFresh_notMem L
    have ihbody_y₀ := ihbody y₀ hy₀L (Γ₂ := Γ₂) (s_pre := s_pre) rfl rfl hFresh_body hAPS_body
    refine MEqRed.bet (L ∪ Ctx.dom (Γ₂ ++ Γ₁) ∪ {y₀}) hLCt ?_ trivial hv
    intro yfresh hyfresh
    simp only [Finset.mem_union, Finset.mem_singleton] at hyfresh
    push_neg at hyfresh
    obtain ⟨⟨hyfL, hyf_dom⟩, hyf_y₀⟩ := hyfresh
    have hpvE_y₀ : PrevalidExt (Γ₂ ++ Γ₁) (s_pre ++ α' :: s_post) :=
      MEqRed.prevalidExt ihbody_y₀
    have hpv_Γ : Prevalid (Γ₂ ++ Γ₁) := extractPrevalid hpvE_y₀
    have hy₀_stack : ∀ β ∈ s_pre ++ α' :: s_post, y₀ ∉ Term.fv β :=
      _y₀_notin_stack_fv_of_notin_dom hpvE_y₀ hy₀_dom
    have ren := MEqRed.rename_stray hpv_Γ ihbody_y₀ y₀ yfresh hy₀_dom hyf_dom
    have hstk_eq : Stack.subst y₀ (.fvar yfresh) (s_pre ++ α' :: s_post) =
        s_pre ++ α' :: s_post :=
      Stack.subst_fresh hy₀_stack
    have hbd_eq : Term.subst y₀ (.fvar yfresh) (bd^[y₀]) = bd^[yfresh] :=
      Term.subst_open_fresh hy₀_fvbd
    have hbd'_eq : Term.subst y₀ (.fvar yfresh) (bd'^[y₀]) = bd'^[yfresh] :=
      Term.subst_open_fresh hy₀_fvbd'
    rw [hstk_eq, hbd_eq, hbd'_eq] at ren
    exact ren
  | @top Γ stk' hpv =>
    subst hΓ
    subst hS
    have hpv' : PrevalidExt (Γ₂ ++ Γ₁) (s_pre ++ α' :: s_post) :=
      PrevalidExt.stack_replace_mid hpv hLCα' (by
        intro x hx
        have := hfvα' hx
        rw [Ctx.dom_append]; exact Finset.mem_union.mpr (Or.inr this))
    exact MEqRed.top hpv'
  | @app Γ stk' u_ u_' v_ v_' hu hv ihu ihv =>
    subst hΓ
    subst hS
    rw [cofinDomFresh_app] at hFresh
    rw [cofinAvoidsProSelf_app] at hAPS
    obtain ⟨hFresh_u, hFresh_v⟩ := Bool.and_eq_true _ _ |>.mp hFresh
    obtain ⟨hAPS_u, hAPS_v⟩ := Bool.and_eq_true _ _ |>.mp hAPS
    have ihu' := ihu (Γ₂ := Γ₂) (s_pre := v_ :: s_pre) rfl (by simp) hFresh_u hAPS_u
    exact MEqRed.app ihu' hv
  | @var Γ stk' yi hpv =>
    subst hΓ
    subst hS
    have hpv' : PrevalidExt (Γ₂ ++ Γ₁) (s_pre ++ α' :: s_post) :=
      PrevalidExt.stack_replace_mid hpv hLCα' (by
        intro x hx
        have := hfvα' hx
        rw [Ctx.dom_append]; exact Finset.mem_union.mpr (Or.inr this))
    exact MEqRed.var hpv'
  | @fun_ Γ tt tt' bd bd' L ht hbody _hUni iht ihbody =>
    -- Vacuous: fun_ requires stack [], but s_pre ++ α :: s_post is non-empty.
    exfalso
    cases s_pre with
    | nil => simp at hS
    | cons _ _ => simp at hS
  | @tAp Γ stk' u_ hpv hLCu hfv =>
    subst hΓ
    subst hS
    have hpv' : PrevalidExt (Γ₂ ++ Γ₁) (s_pre ++ α' :: s_post) :=
      PrevalidExt.stack_replace_mid hpv hLCα' (by
        intro x hx
        have := hfvα' hx
        rw [Ctx.dom_append]; exact Finset.mem_union.mpr (Or.inr this))
    exact MEqRed.tAp hpv' hLCu hfv
  | @fOp Γ stk' tt tt' αi bd bd' L ht hbody _hUni iht ihbody =>
    subst hΓ
    cases s_pre with
    | nil =>
      -- Case A: s_pre = []. αi = α and stk' = s_post.
      simp at hS
      obtain ⟨hαieq, hstkeq⟩ := hS
      subst hαieq
      subst hstkeq
      rw [cofinDomFresh_fOp] at hFresh
      rw [cofinAvoidsProSelf_fOp] at hAPS
      obtain ⟨hFresh_left_body, hFresh_body⟩ := Bool.and_eq_true _ _ |>.mp hFresh
      obtain ⟨hFresh_left_t, hFresh_t⟩ := Bool.and_eq_true _ _ |>.mp hFresh_left_body
      obtain ⟨hFresh_left_fvbd', hFresh_fvbd'_dec⟩ :=
        Bool.and_eq_true _ _ |>.mp hFresh_left_t
      obtain ⟨hFresh_dom_dec, hFresh_fvbd_dec⟩ :=
        Bool.and_eq_true _ _ |>.mp hFresh_left_fvbd'
      obtain ⟨hAPS_left_body, hAPS_body⟩ := Bool.and_eq_true _ _ |>.mp hAPS
      obtain ⟨hAPS_avoid, hAPS_t⟩ := Bool.and_eq_true _ _ |>.mp hAPS_left_body
      have hzL : pickFresh L ∉ L := pickFresh_notMem L
      have hfvα'_full : Term.fv α' ⊆ Ctx.dom (Γ₂ ++ Γ₁) := by
        intro x hx
        have := hfvα' hx
        rw [Ctx.dom_append]; exact Finset.mem_union.mpr (Or.inr this)
      -- equ_head_replace's signature uses `Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁`;
      -- here we take its Γ₂ := [] and its Γ₁ := Γ₂ ++ Γ₁ (our outer ctx).
      -- `[] ++ X = X` by definitional reduction of List.append, so
      -- `hbody (pickFresh L) hzL : MEqRed (⟨pickFresh L, α, .equ⟩ :: (Γ₂ ++ Γ₁)) ...`
      -- directly inhabits `MEqRed (([] : Ctx) ++ ⟨pickFresh L, α, .equ⟩ :: (Γ₂ ++ Γ₁)) ...`.
      have hbody_z_swapped' :
          MEqRed (⟨pickFresh L, α', .equ⟩ :: (Γ₂ ++ Γ₁)) s_post
            (bd^[pickFresh L]) (bd'^[pickFresh L]) :=
        MEqRed.equ_head_replace
          (Γ₁ := Γ₂ ++ Γ₁) (Γ₂ := []) (y := pickFresh L)
          (hbody (pickFresh L) hzL) hLCα' hfvα'_full hAPS_avoid hFresh_body
      have hy₀_dom : pickFresh L ∉ Ctx.dom (Γ₂ ++ Γ₁) :=
        decide_eq_true_eq.mp hFresh_dom_dec
      have hy₀_fvbd : pickFresh L ∉ Term.fv bd :=
        decide_eq_true_eq.mp hFresh_fvbd_dec
      have hy₀_fvbd' : pickFresh L ∉ Term.fv bd' :=
        decide_eq_true_eq.mp hFresh_fvbd_dec |> fun _ => decide_eq_true_eq.mp hFresh_fvbd'_dec
      have hy₀_α' : pickFresh L ∉ Term.fv α' :=
        fv_notin_of_dom_notin hfvα'_full hy₀_dom
      have hpv_outer : PrevalidExt (Γ₂ ++ Γ₁) (α :: s_post) :=
        MEqRed.prevalidExt (MEqRed.fOp L ht hbody trivial)
      have hpv_outer_st : PrevalidExt (Γ₂ ++ Γ₁) s_post := by
        cases hpv_outer with
        | cons hpv_t _ _ => exact hpv_t
      have hz_stack : ∀ β ∈ s_post, pickFresh L ∉ Term.fv β :=
        _y₀_notin_stack_fv_of_notin_dom hpv_outer_st hy₀_dom
      refine MEqRed.fOp (L ∪ Ctx.dom (Γ₂ ++ Γ₁) ∪ {pickFresh L}) ht ?_ trivial
      intro yfresh hyfresh
      simp only [Finset.mem_union, Finset.mem_singleton] at hyfresh
      push_neg at hyfresh
      obtain ⟨⟨hyfL, hyf_dom⟩, hyf_z⟩ := hyfresh
      have hyz : pickFresh L ≠ yfresh := fun h' => hyf_z h'.symm
      have ren := _MEqRed_rename_equ_no_fv hyz hy₀_dom hyf_dom hy₀_α'
        hy₀_fvbd hy₀_fvbd' hz_stack hbody_z_swapped'
      simpa using ren
    | cons β rest =>
      -- Case B: αi = β, stk' = rest ++ α :: s_post. Recurse with Γ₂ extended.
      simp at hS
      obtain ⟨hβeq, hstkeq⟩ := hS
      subst hβeq
      subst hstkeq
      rw [cofinDomFresh_fOp] at hFresh
      rw [cofinAvoidsProSelf_fOp] at hAPS
      obtain ⟨hFresh_left_body, hFresh_body⟩ := Bool.and_eq_true _ _ |>.mp hFresh
      obtain ⟨hFresh_left_t, hFresh_t⟩ := Bool.and_eq_true _ _ |>.mp hFresh_left_body
      obtain ⟨hFresh_left_fvbd', hFresh_fvbd'_dec⟩ :=
        Bool.and_eq_true _ _ |>.mp hFresh_left_t
      obtain ⟨hFresh_dom_dec, hFresh_fvbd_dec⟩ :=
        Bool.and_eq_true _ _ |>.mp hFresh_left_fvbd'
      obtain ⟨hAPS_left_body, hAPS_body⟩ := Bool.and_eq_true _ _ |>.mp hAPS
      obtain ⟨_hAPS_avoid, hAPS_t⟩ := Bool.and_eq_true _ _ |>.mp hAPS_left_body
      have hy₀_dom : pickFresh L ∉ Ctx.dom (Γ₂ ++ Γ₁) :=
        decide_eq_true_eq.mp hFresh_dom_dec
      have hy₀_fvbd : pickFresh L ∉ Term.fv bd :=
        decide_eq_true_eq.mp hFresh_fvbd_dec
      have hy₀_fvbd' : pickFresh L ∉ Term.fv bd' :=
        decide_eq_true_eq.mp hFresh_fvbd'_dec
      have hy₀L : pickFresh L ∉ L := pickFresh_notMem L
      -- Recurse: body lives at (⟨pickFresh L, β, .equ⟩ :: Γ₂ ++ Γ₁) — extend Γ₂.
      have ihbody_y₀ := ihbody (pickFresh L) hy₀L
        (Γ₂ := ⟨pickFresh L, β, .equ⟩ :: Γ₂)
        (s_pre := rest) (by simp) (by simp) hFresh_body hAPS_body
      have ihbody_y₀_norm :
          MEqRed (⟨pickFresh L, β, .equ⟩ :: (Γ₂ ++ Γ₁)) (rest ++ α' :: s_post)
            (bd^[pickFresh L]) (bd'^[pickFresh L]) := by simpa using ihbody_y₀
      refine MEqRed.fOp (L ∪ Ctx.dom (Γ₂ ++ Γ₁) ∪ {pickFresh L}) ht ?_ trivial
      intro yfresh hyfresh
      simp only [Finset.mem_union, Finset.mem_singleton] at hyfresh
      push_neg at hyfresh
      obtain ⟨⟨hyfL, hyf_dom⟩, hyf_y₀⟩ := hyfresh
      have hyz : pickFresh L ≠ yfresh := fun h' => hyf_y₀ h'.symm
      have hpv_outer : PrevalidExt (Γ₂ ++ Γ₁) (β :: rest ++ α :: s_post) :=
        MEqRed.prevalidExt (MEqRed.fOp L ht hbody trivial)
      have hpv_outer_β : Term.fv β ⊆ Ctx.dom (Γ₂ ++ Γ₁) := by
        cases hpv_outer with
        | cons _ _ hfvβ => exact hfvβ
      have hy₀_β : pickFresh L ∉ Term.fv β :=
        fv_notin_of_dom_notin hpv_outer_β hy₀_dom
      have hpv_outer_t : PrevalidExt (Γ₂ ++ Γ₁) (rest ++ α :: s_post) := by
        cases hpv_outer with
        | cons hpv_t _ _ => exact hpv_t
      have hy₀_stack_old : ∀ γ ∈ (rest ++ α :: s_post), pickFresh L ∉ Term.fv γ :=
        _y₀_notin_stack_fv_of_notin_dom hpv_outer_t hy₀_dom
      have hfvα'_full : Term.fv α' ⊆ Ctx.dom (Γ₂ ++ Γ₁) := by
        intro x hx
        have := hfvα' hx
        rw [Ctx.dom_append]; exact Finset.mem_union.mpr (Or.inr this)
      have hy₀_α' : pickFresh L ∉ Term.fv α' :=
        fv_notin_of_dom_notin hfvα'_full hy₀_dom
      have hy₀_stack : ∀ γ ∈ (rest ++ α' :: s_post), pickFresh L ∉ Term.fv γ := by
        intro γ hγ
        rcases List.mem_append.mp hγ with hγr | hγr
        · exact hy₀_stack_old γ (List.mem_append.mpr (Or.inl hγr))
        · rcases List.mem_cons.mp hγr with hγeq | hγt
          · subst hγeq; exact hy₀_α'
          · exact hy₀_stack_old γ
              (List.mem_append.mpr (Or.inr (List.mem_cons_of_mem _ hγt)))
      have ren := _MEqRed_rename_equ_no_fv hyz hy₀_dom hyf_dom hy₀_β
        hy₀_fvbd hy₀_fvbd' hy₀_stack ihbody_y₀_norm
      simpa using ren

/-! ### §9.3. `MEqRed.stack_head_replace` (specialization for `Γ₂ = []`,
`s_pre = []`) -/

/-- **Stack-head bound-term replacement.**

Specialization of `MEqRed.stack_replace` with `Γ₂ := []`, `s_pre := []`.

Given `MEqRed Γ (α :: s) u u'` and the LC + fv data of `α'` (relating
to `MEqRed Γ [] α α'` via `lc_right`/`MEqRed_fv_preserve`), produce
`MEqRed Γ (α' :: s) u u'`.

Premises `cofinDomFresh h = true` and `cofinAvoidsProSelf h = true`
ensure the canonical-witness rename composition + fOp Case A delegate
to `equ_head_replace` succeed. See §9.2 for the proof structure. -/
noncomputable def MEqRed.stack_head_replace
    {Γ : Ctx} {s : Stack} {α α' u u' : Term}
    (h : MEqRed Γ (α :: s) u u')
    (hLCα' : Term.LC α') (hfvα' : Term.fv α' ⊆ Γ.dom)
    (hFresh : cofinDomFresh h = true)
    (hAPS : cofinAvoidsProSelf h = true) :
    MEqRed Γ (α' :: s) u u' :=
  -- `[] ++ Γ` unfolds to `Γ` and `[] ++ (α :: s)` unfolds to `α :: s` by
  -- definitional reduction of `List.append`, so `h` directly inhabits the
  -- generalized signature without any conversion.
  MEqRed.stack_replace (Γ₁ := Γ) (Γ₂ := []) (s_pre := []) (s_post := s)
    hLCα' hfvα' h hFresh hAPS

/-! ### §9.3a. Phase 5d: `MEqRed.stack_replace_univ_exists_pred` /
`stack_head_replace_univ_exists`

Phase 5d analog of `stack_replace` / `stack_head_replace`, taking a
`CofinAvoidsProSelfUniv h` premise (replacing both `cofinDomFresh` and
`cofinAvoidsProSelf`) PLUS a predicate-form `AvoidsProUniv` premise
(`∀ z, Avoid z → AvoidsProUniv h z`), and returning an existence form
preserving BOTH `CofinAvoidsProSelfUniv` AND the predicate-form
avoidance on the output.

**Why predicate form.** In fOp Case B (the body's stack is
`β :: rest ++ α :: s_post`), the recursive output's
`CofinAvoidsProSelfUniv` requires `AvoidsProUniv (body_y_i) y_i` —
which is exactly the `Avoid := {y_i}` predicate-form preservation
that this theorem establishes.

**The structural avoidance of the alpha-equivariance trap.** In the
fOp Case A arm, the body recurses at extended ctx with binding
`⟨y_i, α, .equ⟩` for each cofinite witness `y_i ∉ L`. We delegate
directly to `equ_head_replace_univ_exists_pred` at this `y_i`
(NOT at a canonical `pickFresh L`-sample). The premise
`AvoidsProUniv (hbody y_i _) y_i` comes from `CofinAvoidsProSelfUniv`'s
fOp clause without any sample-point alignment between input and output
L's. No rename, no `pickFresh L → pickFresh L'` translation, no
fragility under constructor-set widening. -/

theorem MEqRed.stack_replace_univ_exists_pred
    {Γ₁ : Ctx} {α α' : Term}
    (hLCα' : Term.LC α') (hfvα' : Term.fv α' ⊆ Γ₁.dom) :
    {Γ₂ : Ctx} → {s_pre s_post : Stack} → {u u' : Term} →
    (h : MEqRed (Γ₂ ++ Γ₁) (s_pre ++ α :: s_post) u u') →
    (Avoid : String → Prop) →
    (∀ z, Avoid z → AvoidsProUniv h z) →
    CofinAvoidsProSelfUniv h →
    ∃ h' : MEqRed (Γ₂ ++ Γ₁) (s_pre ++ α' :: s_post) u u',
      (∀ z, Avoid z → AvoidsProUniv h' z) ∧
      CofinAvoidsProSelfUniv h' := by
  intro Γ₂ s_pre s_post u u' h Avoid hAvoidAll hCAU
  classical
  revert hAvoidAll hCAU
  generalize hΓ : (Γ₂ ++ Γ₁) = Γ at h
  generalize hS : (s_pre ++ α :: s_post) = stk at h
  induction h generalizing Γ₂ s_pre Avoid with
  | @pro Γ stk' yi β β' hpv heq hβ ihβ =>
    intro hAvoidAll hCAU
    subst hΓ; subst hS
    rw [CofinAvoidsProSelfUniv_pro] at hCAU
    have hpv' : PrevalidExt (Γ₂ ++ Γ₁) (s_pre ++ α' :: s_post) :=
      PrevalidExt.stack_replace_mid hpv hLCα' (by
        intro x hx
        have := hfvα' hx
        rw [Ctx.dom_append]; exact Finset.mem_union.mpr (Or.inr this))
    have hAvoidInner : ∀ z, Avoid z → AvoidsProUniv hβ z := by
      intro z hz
      have := hAvoidAll z hz
      rw [AvoidsProUniv_pro] at this
      exact this.2
    obtain ⟨hβ', hβA, hβC⟩ := ihβ (Avoid := Avoid) (Γ₂ := Γ₂) (s_pre := s_pre) rfl rfl
      hAvoidInner hCAU
    refine ⟨MEqRed.pro hpv' heq hβ', ?_, ?_⟩
    · intro z hz
      rw [AvoidsProUniv_pro]
      have := hAvoidAll z hz
      rw [AvoidsProUniv_pro] at this
      exact ⟨this.1, hβA z hz⟩
    · rw [CofinAvoidsProSelfUniv_pro]; exact hβC
  | @bet Γ stk' tBound v0 v0' bd bd' L hLCt hbody _hUni hv ihbody ihv =>
    intro hAvoidAll hCAU
    subst hΓ; subst hS
    rw [CofinAvoidsProSelfUniv_bet] at hCAU
    obtain ⟨hbU, hvU⟩ := hCAU
    -- The body shares the stack `stk' = s_pre ++ α :: s_post`, recurse on it.
    -- The operand `hv` has empty stack — no α :: s_post, pass through.
    have body_each : ∀ yfresh, yfresh ∉ L →
        ∃ h' : MEqRed (Γ₂ ++ Γ₁) (s_pre ++ α' :: s_post)
                  (bd^[yfresh]) (bd'^[yfresh]),
          (∀ z, Avoid z → AvoidsProUniv h' z) ∧
          CofinAvoidsProSelfUniv h' := by
      intro yfresh hyf
      have hAvoidBody : ∀ z, Avoid z → AvoidsProUniv (hbody yfresh hyf) z := by
        intro z hz
        have := hAvoidAll z hz
        rw [AvoidsProUniv_bet] at this
        exact this.1 yfresh hyf
      exact ihbody yfresh hyf (Avoid := Avoid) (Γ₂ := Γ₂) (s_pre := s_pre) rfl rfl
        hAvoidBody (hbU yfresh hyf)
    let body_witness : ∀ yfresh, yfresh ∉ L →
        MEqRed (Γ₂ ++ Γ₁) (s_pre ++ α' :: s_post)
          (bd^[yfresh]) (bd'^[yfresh]) :=
      fun yfresh hyf => (body_each yfresh hyf).choose
    have body_witness_specs :
        ∀ yfresh (hyf : yfresh ∉ L),
          (∀ z, Avoid z → AvoidsProUniv (body_witness yfresh hyf) z) ∧
          CofinAvoidsProSelfUniv (body_witness yfresh hyf) :=
      fun yfresh hyf => (body_each yfresh hyf).choose_spec
    refine ⟨MEqRed.bet L hLCt body_witness trivial hv, ?_, ?_⟩
    · intro z hz
      rw [AvoidsProUniv_bet]
      refine ⟨fun yfresh hyf => (body_witness_specs yfresh hyf).1 z hz, ?_⟩
      have := hAvoidAll z hz
      rw [AvoidsProUniv_bet] at this
      exact this.2
    · rw [CofinAvoidsProSelfUniv_bet]
      exact ⟨fun yfresh hyf => (body_witness_specs yfresh hyf).2, hvU⟩
  | @top Γ stk' hpv =>
    intro _ _
    subst hΓ; subst hS
    have hpv' : PrevalidExt (Γ₂ ++ Γ₁) (s_pre ++ α' :: s_post) :=
      PrevalidExt.stack_replace_mid hpv hLCα' (by
        intro x hx
        have := hfvα' hx
        rw [Ctx.dom_append]; exact Finset.mem_union.mpr (Or.inr this))
    refine ⟨MEqRed.top hpv', ?_, ?_⟩
    · intro z _; rw [AvoidsProUniv_top]; trivial
    · rw [CofinAvoidsProSelfUniv_top]; trivial
  | @app Γ stk' u_ u_' v_ v_' hu hv ihu ihv =>
    intro hAvoidAll hCAU
    subst hΓ; subst hS
    rw [CofinAvoidsProSelfUniv_app] at hCAU
    obtain ⟨huU, hvU⟩ := hCAU
    have hAvoidU : ∀ z, Avoid z → AvoidsProUniv hu z := by
      intro z hz
      have := hAvoidAll z hz
      rw [AvoidsProUniv_app] at this
      exact this.1
    obtain ⟨hu', huA, huC'⟩ := ihu (Avoid := Avoid) (Γ₂ := Γ₂) (s_pre := v_ :: s_pre)
      rfl (by simp) hAvoidU huU
    refine ⟨MEqRed.app hu' hv, ?_, ?_⟩
    · intro z hz
      rw [AvoidsProUniv_app]
      refine ⟨huA z hz, ?_⟩
      have := hAvoidAll z hz
      rw [AvoidsProUniv_app] at this
      exact this.2
    · rw [CofinAvoidsProSelfUniv_app]
      exact ⟨huC', hvU⟩
  | @var Γ stk' yi hpv =>
    intro _ _
    subst hΓ; subst hS
    have hpv' : PrevalidExt (Γ₂ ++ Γ₁) (s_pre ++ α' :: s_post) :=
      PrevalidExt.stack_replace_mid hpv hLCα' (by
        intro x hx
        have := hfvα' hx
        rw [Ctx.dom_append]; exact Finset.mem_union.mpr (Or.inr this))
    refine ⟨MEqRed.var hpv', ?_, ?_⟩
    · intro z _; rw [AvoidsProUniv_var]; trivial
    · rw [CofinAvoidsProSelfUniv_var]; trivial
  | @fun_ Γ tt tt' bd bd' L ht hbody _hUni iht ihbody =>
    intro _ _
    -- Vacuous: fun_ requires stack [], but s_pre ++ α :: s_post is non-empty.
    exfalso
    cases s_pre with
    | nil => simp at hS
    | cons _ _ => simp at hS
  | @tAp Γ stk' u_ hpv hLCu hfv =>
    intro _ _
    subst hΓ; subst hS
    have hpv' : PrevalidExt (Γ₂ ++ Γ₁) (s_pre ++ α' :: s_post) :=
      PrevalidExt.stack_replace_mid hpv hLCα' (by
        intro x hx
        have := hfvα' hx
        rw [Ctx.dom_append]; exact Finset.mem_union.mpr (Or.inr this))
    refine ⟨MEqRed.tAp hpv' hLCu hfv, ?_, ?_⟩
    · intro z _; rw [AvoidsProUniv_tAp]; trivial
    · rw [CofinAvoidsProSelfUniv_tAp]; trivial
  | @fOp Γ stk' tt tt' αi bd bd' L ht hbody _hUni iht ihbody =>
    intro hAvoidAll hCAU
    subst hΓ
    cases s_pre with
    | nil =>
      -- Case A: s_pre = []. αi = α and stk' = s_post.
      simp at hS
      obtain ⟨hαieq, hstkeq⟩ := hS
      subst hαieq; subst hstkeq
      rw [CofinAvoidsProSelfUniv_fOp] at hCAU
      obtain ⟨htU, hbcomb⟩ := hCAU
      have hfvα'_full : Term.fv α' ⊆ Ctx.dom (Γ₂ ++ Γ₁) := by
        intro x hx
        have := hfvα' hx
        rw [Ctx.dom_append]; exact Finset.mem_union.mpr (Or.inr this)
      -- For each cofinite witness y_i, use equ_head_replace_univ_exists_pred to swap
      -- α → α' inside the body's context. Track Avoid ∪ {y_i} so the output
      -- preserves both the input's tracked names AND y_i (for self-avoidance).
      have body_each : ∀ y_i, y_i ∉ L →
          ∃ h' : MEqRed (⟨y_i, α', .equ⟩ :: (Γ₂ ++ Γ₁)) s_post
                    (bd^[y_i]) (bd'^[y_i]),
            (∀ z, Avoid z → AvoidsProUniv h' z) ∧
            AvoidsProUniv h' y_i ∧ CofinAvoidsProSelfUniv h' := by
        intro y_i hyiL
        obtain ⟨hAvUniv_i, hCAU_i⟩ := hbcomb y_i hyiL
        let Avoid' : String → Prop := fun z => Avoid z ∨ z = y_i
        have hAvoidExt : ∀ z, Avoid' z → AvoidsProUniv (hbody y_i hyiL) z := by
          intro z hz
          cases hz with
          | inl hz =>
            have := hAvoidAll z hz
            rw [AvoidsProUniv_fOp] at this
            exact this.2 y_i hyiL
          | inr hzeq => rw [hzeq]; exact hAvUniv_i
        have hyAvoidExt : Avoid' y_i := Or.inr rfl
        obtain ⟨h_swap, h_swap_avs, h_swap_cau⟩ :=
          MEqRed.equ_head_replace_univ_exists_pred
            (Γ₁ := Γ₂ ++ Γ₁) (Γ₂ := []) (y := y_i)
            (hbody y_i hyiL) hLCα' hfvα'_full Avoid' hyAvoidExt hAvoidExt hCAU_i
        refine ⟨h_swap, ?_, ?_, h_swap_cau⟩
        · intro z hz; exact h_swap_avs z (Or.inl hz)
        · exact h_swap_avs y_i (Or.inr rfl)
      let body_witness : ∀ y_i, y_i ∉ L →
          MEqRed (⟨y_i, α', .equ⟩ :: (Γ₂ ++ Γ₁)) s_post
            (bd^[y_i]) (bd'^[y_i]) :=
        fun y_i hyiL => (body_each y_i hyiL).choose
      have body_witness_specs :
          ∀ y_i (hyiL : y_i ∉ L),
            (∀ z, Avoid z → AvoidsProUniv (body_witness y_i hyiL) z) ∧
            AvoidsProUniv (body_witness y_i hyiL) y_i ∧
            CofinAvoidsProSelfUniv (body_witness y_i hyiL) :=
        fun y_i hyiL => (body_each y_i hyiL).choose_spec
      refine ⟨MEqRed.fOp L ht body_witness trivial, ?_, ?_⟩
      · intro z hz
        rw [AvoidsProUniv_fOp]
        refine ⟨?_, fun y_i hyiL => (body_witness_specs y_i hyiL).1 z hz⟩
        have := hAvoidAll z hz
        rw [AvoidsProUniv_fOp] at this
        exact this.1
      · rw [CofinAvoidsProSelfUniv_fOp]
        refine ⟨htU, fun y_i hyiL => ?_⟩
        exact ⟨(body_witness_specs y_i hyiL).2.1, (body_witness_specs y_i hyiL).2.2⟩
    | cons β rest =>
      -- Case B: αi = β, stk' = rest ++ α :: s_post.
      simp at hS
      obtain ⟨hβeq, hstkeq⟩ := hS
      subst hβeq; subst hstkeq
      rw [CofinAvoidsProSelfUniv_fOp] at hCAU
      obtain ⟨htU, hbcomb⟩ := hCAU
      -- For each cofinite witness y_i, recurse via the IH (predicate-form),
      -- tracking Avoid ∪ {y_i}.
      have body_each : ∀ y_i, y_i ∉ L →
          ∃ h' : MEqRed (⟨y_i, β, .equ⟩ :: (Γ₂ ++ Γ₁)) (rest ++ α' :: s_post)
                    (bd^[y_i]) (bd'^[y_i]),
            (∀ z, Avoid z → AvoidsProUniv h' z) ∧
            AvoidsProUniv h' y_i ∧ CofinAvoidsProSelfUniv h' := by
        intro y_i hyiL
        obtain ⟨hAvUniv_i, hCAU_i⟩ := hbcomb y_i hyiL
        let Avoid' : String → Prop := fun z => Avoid z ∨ z = y_i
        have hAvoidExt : ∀ z, Avoid' z → AvoidsProUniv (hbody y_i hyiL) z := by
          intro z hz
          cases hz with
          | inl hz =>
            have := hAvoidAll z hz
            rw [AvoidsProUniv_fOp] at this
            exact this.2 y_i hyiL
          | inr hzeq => rw [hzeq]; exact hAvUniv_i
        have ihres := ihbody y_i hyiL (Avoid := Avoid')
          (Γ₂ := ⟨y_i, β, .equ⟩ :: Γ₂)
          (s_pre := rest) (by simp) (by simp) hAvoidExt hCAU_i
        obtain ⟨h_inner, hAv_inner, hC_inner⟩ := ihres
        refine ⟨?_, ?_, ?_, ?_⟩
        · simpa using h_inner
        · intro z hz
          simpa [AvoidsProUniv_subst_eq_ctx] using hAv_inner z (Or.inl hz)
        · simpa [AvoidsProUniv_subst_eq_ctx] using hAv_inner y_i (Or.inr rfl)
        · change CofinAvoidsProSelfUniv h_inner; exact hC_inner
      let body_witness : ∀ y_i, y_i ∉ L →
          MEqRed (⟨y_i, β, .equ⟩ :: (Γ₂ ++ Γ₁)) (rest ++ α' :: s_post)
            (bd^[y_i]) (bd'^[y_i]) :=
        fun y_i hyiL => (body_each y_i hyiL).choose
      have body_witness_specs :
          ∀ y_i (hyiL : y_i ∉ L),
            (∀ z, Avoid z → AvoidsProUniv (body_witness y_i hyiL) z) ∧
            AvoidsProUniv (body_witness y_i hyiL) y_i ∧
            CofinAvoidsProSelfUniv (body_witness y_i hyiL) :=
        fun y_i hyiL => (body_each y_i hyiL).choose_spec
      refine ⟨MEqRed.fOp L ht body_witness trivial, ?_, ?_⟩
      · intro z hz
        rw [AvoidsProUniv_fOp]
        refine ⟨?_, fun y_i hyiL => (body_witness_specs y_i hyiL).1 z hz⟩
        have := hAvoidAll z hz
        rw [AvoidsProUniv_fOp] at this
        exact this.1
      · rw [CofinAvoidsProSelfUniv_fOp]
        refine ⟨htU, fun y_i hyiL => ?_⟩
        exact ⟨(body_witness_specs y_i hyiL).2.1, (body_witness_specs y_i hyiL).2.2⟩

/-- Specialization with `Avoid` trivial (always False). -/
theorem MEqRed.stack_replace_univ_exists
    {Γ₁ Γ₂ : Ctx} {s_pre s_post : Stack} {α α' u u' : Term}
    (hLCα' : Term.LC α') (hfvα' : Term.fv α' ⊆ Γ₁.dom)
    (h : MEqRed (Γ₂ ++ Γ₁) (s_pre ++ α :: s_post) u u')
    (hCAU : CofinAvoidsProSelfUniv h) :
    ∃ h' : MEqRed (Γ₂ ++ Γ₁) (s_pre ++ α' :: s_post) u u',
      CofinAvoidsProSelfUniv h' := by
  obtain ⟨h', _, hC⟩ :=
    MEqRed.stack_replace_univ_exists_pred (Γ₁ := Γ₁) (Γ₂ := Γ₂)
      (s_pre := s_pre) (s_post := s_post) hLCα' hfvα' h
      (Avoid := fun _ => False) (by intro z hz; cases hz) hCAU
  exact ⟨h', hC⟩

/-- Stack-head replacement using the universal-AvoidsProUniv premise.
Specialization with `Γ₂ = []`, `s_pre = []`. -/
theorem MEqRed.stack_head_replace_univ_exists
    {Γ : Ctx} {s : Stack} {α α' u u' : Term}
    (h : MEqRed Γ (α :: s) u u')
    (hLCα' : Term.LC α') (hfvα' : Term.fv α' ⊆ Γ.dom)
    (hCAU : CofinAvoidsProSelfUniv h) :
    ∃ h' : MEqRed Γ (α' :: s) u u', CofinAvoidsProSelfUniv h' :=
  MEqRed.stack_replace_univ_exists (Γ₁ := Γ) (Γ₂ := []) (s_pre := []) (s_post := s)
    hLCα' hfvα' h hCAU

/-! ## §10. `strip_equ_head` — head-removal functor on `MEqRed`

Iteration 7+ of the β-residual unblock campaign. Where
`equ_head_replace` (§8) replaces the bound term `α → α'` of a `.equ`-head
binding, `strip_equ_head` REMOVES the head entirely:

  `MEqRed (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁) st u u'`
  ────────────────────────────────────────────
  `MEqRed (Γ₂ ++ Γ₁) st u u'`

This is the body-diamond-descent piece needed by Lemma 2's App×Bet
residual: the body-IH lives at the EXTENDED context
`(⟨y₀, v, .equ⟩ :: Γ)`, but `MEqRed.bet`'s body cofinite is at the BARE
`Γ`. The strip functor closes that gap when `avoidsPro h y₀ = true`
(no `Me-Pro y₀` lookups against the head being stripped).

### Architectural notes — why this is harder than `equ_head_replace`

`equ_head_replace` preserves `Ctx.dom`: `(Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁).dom
= (Γ₂ ++ ⟨y, α', .equ⟩ :: Γ₁).dom`. Subset/freshness data on terms,
stack entries, and Γ₂'s prior bindings transfers verbatim.

`strip_equ_head` REMOVES `y` from the dom. To rebuild a derivation in
the smaller context, every term that previously had fv against the
larger dom must be re-checked: its fv must in fact avoid `y`. This
applies to:

* `u`, `u'` (source/target): syntactic `y`-freshness must be passed in.
* Stack entries `β ∈ st`: each must avoid `y`.
* Γ₂'s entries' bound terms: each must avoid `y` (so the new
  `Prevalid (Γ₂ ++ Γ₁)` invariants hold).
* For the `pro yi` arm: the looked-up `α_yi` must avoid `y` (used in
  the recursion's source/target).
* For the `bet`/`fun_`/`fOp` cofinite arms: the bound annotation `tt` /
  `αi` and the operand `v0`/`v0'` must avoid `y`.

The natural way to bundle these is a **stronger Bool predicate**
"`avoidsFv h y = true`" that recursively checks every term in the
derivation tree for `y`-freshness. We don't yet have that infrastructure
(adding it is one full session worth of work). For now we provide:

* The dom-equation helper `_Ctx_dom_eq_under_equ_head_remove`.
* The `equBinds`/`subBinds` lookup helpers `_equBinds_equ_head_remove_neq`
  and `_subBinds_equ_head_remove`.
* `Prevalid.equ_head_remove_mid` and `PrevalidExt.equ_head_remove_mid`,
  parametrized by an explicit `Γ₂` "all entries' bounds avoid y"
  hypothesis.

The full `MEqRed.strip_equ_head` is NOT YET defined — building it
requires the `avoidsFv`-style predicate to compose hypotheses through
the cofinite arms. This iteration ships the structural helpers; the
predicate + functor body is the next deliverable.

### Why we don't take a shortcut

A tempting shortcut: prove `MEqRed.strip_equ_head` for `Γ₂ = []` only
(matching iter-6's use site). But the cofinite-arm body recursion grows
`Γ₂` by `⟨y₀, tt, .sub⟩` (or `⟨y₀, αi, .equ⟩`), so even the
`Γ₂ = []` initial call needs the general-`Γ₂` form internally. No
shortcut exists. -/

/-- `(Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁).dom = insert y (Γ₂ ++ Γ₁).dom`.

The head removal removes `y` from the domain, so the LHS dom is the
RHS dom plus `{y}`. -/
private theorem _Ctx_dom_eq_under_equ_head_remove
    {Γ₁ Γ₂ : Ctx} {y : String} {α : Term} :
    Ctx.dom (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁) =
      insert y (Ctx.dom (Γ₂ ++ Γ₁)) := by
  rw [Ctx.dom_append, Ctx.dom_append, Ctx.dom_cons]
  -- LHS: Γ₂.dom ∪ insert y Γ₁.dom
  -- RHS: insert y (Γ₂.dom ∪ Γ₁.dom)
  ext z
  simp [Finset.mem_insert, Finset.mem_union, or_comm, or_left_comm]

/-- If `(Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁).equBinds yi α_yi` and `yi ≠ y`,
the lookup survives in `Γ₂ ++ Γ₁` (we just skip the head we removed).

Mirror of `_equBinds_equ_head_swap_neq` (§8.1) but for full removal. -/
private theorem _equBinds_equ_head_remove_neq
    {Γ₁ Γ₂ : Ctx} {y yi : String} {α α_yi : Term}
    (hyiy : yi ≠ y)
    (hb : (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁).equBinds yi α_yi) :
    (Γ₂ ++ Γ₁).equBinds yi α_yi := by
  induction Γ₂ with
  | nil =>
    simp [Ctx.equBinds, Ctx.lookupEqu_cons] at hb
    by_cases h : y = yi
    · exact absurd h.symm hyiy
    · simp [h] at hb
      exact hb
  | cons e rest ih =>
    show Ctx.lookupEqu (e :: (rest ++ Γ₁)) yi = some α_yi
    have h1 : Ctx.lookupEqu (e :: (rest ++ ⟨y, α, .equ⟩ :: Γ₁)) yi = some α_yi := hb
    rw [Ctx.lookupEqu_cons] at h1 ⊢
    by_cases he : e.name = yi
    · rw [if_pos he] at h1 ⊢; exact h1
    · rw [if_neg he] at h1 ⊢; exact ih h1

/-- Mirror for `subBinds`: if `(Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁).subBinds yi t`,
the lookup survives in `Γ₂ ++ Γ₁` (the removed head is `.equ`-typed, so
`.sub` lookups always skipped it). -/
private theorem _subBinds_equ_head_remove
    {Γ₁ Γ₂ : Ctx} {y yi : String} {α t : Term}
    (hb : (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁).subBinds yi t) :
    (Γ₂ ++ Γ₁).subBinds yi t := by
  induction Γ₂ with
  | nil =>
    show Ctx.lookupSub Γ₁ yi = some t
    have h1 : Ctx.lookupSub (⟨y, α, .equ⟩ :: Γ₁) yi = some t := hb
    rw [Ctx.lookupSub_cons] at h1
    -- Head is `.equ`, so `lookupSub` always skips: name match → none, no match → recurse.
    by_cases hxy : y = yi
    · simp [hxy] at h1
    · simp [hxy] at h1; exact h1
  | cons e rest ih =>
    show Ctx.lookupSub (e :: (rest ++ Γ₁)) yi = some t
    have h1 : Ctx.lookupSub (e :: (rest ++ ⟨y, α, .equ⟩ :: Γ₁)) yi = some t := hb
    rw [Ctx.lookupSub_cons] at h1 ⊢
    by_cases he : e.name = yi
    · rw [if_pos he] at h1 ⊢
      cases hkind : e.kind with
      | sub => simp [hkind] at h1 ⊢; exact h1
      | equ => simp [hkind] at h1
    · rw [if_neg he] at h1 ⊢; exact ih h1

/-- A predicate on contexts: every entry's bound term avoids the variable `y`.
Used as a structural hypothesis for `Prevalid.equ_head_remove_mid`. -/
def Ctx.AvoidsBoundFv (Γ : Ctx) (y : String) : Prop :=
  ∀ e ∈ Γ, y ∉ Term.fv e.bound

@[simp] theorem Ctx.AvoidsBoundFv_nil (y : String) :
    Ctx.AvoidsBoundFv [] y := by
  intro e he; cases he

@[simp] theorem Ctx.AvoidsBoundFv_cons {e : CtxEntry} {rest : Ctx} {y : String} :
    Ctx.AvoidsBoundFv (e :: rest) y ↔
      y ∉ Term.fv e.bound ∧ Ctx.AvoidsBoundFv rest y := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · exact h e (List.mem_cons_self _ _)
    · intro e' he'; exact h e' (List.mem_cons_of_mem _ he')
  · rintro ⟨hhead, htail⟩ e' he'
    rcases List.mem_cons.mp he' with rfl | he'
    · exact hhead
    · exact htail e' he'

/-- **Remove an `.equ`-head from a Prevalid context.**

Given:
* `hpv : Prevalid (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁)` — the input prevalidity.
* `hΓ₂_avoid : Ctx.AvoidsBoundFv Γ₂ y` — every Γ₂ entry's bound term
  avoids `y` (so its fv-subset invariant survives the `y`-removal).

Produces: `Prevalid (Γ₂ ++ Γ₁)`. -/
noncomputable def Prevalid.equ_head_remove_mid
    {Γ₁ Γ₂ : Ctx} {y : String} {α : Term}
    (hpv : Prevalid (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁))
    (hΓ₂_avoid : Ctx.AvoidsBoundFv Γ₂ y) :
    Prevalid (Γ₂ ++ Γ₁) := by
  induction Γ₂ with
  | nil =>
    -- `Γ₂ = []`, so input is `Prevalid (⟨y, α, .equ⟩ :: Γ₁)`. Drop the head via cases.
    cases hpv with
    | equ hΓ _ _ _ => exact hΓ
  | cons e rest ih =>
    -- `Γ₂ = e :: rest`. Input: `Prevalid (e :: (rest ++ ⟨y, α, .equ⟩ :: Γ₁))`.
    have hpv' : Prevalid (e :: (rest ++ ⟨y, α, .equ⟩ :: Γ₁)) := by simpa using hpv
    have ⟨hhead, htail⟩ := Ctx.AvoidsBoundFv_cons.mp hΓ₂_avoid
    cases hpv' with
    | @sub _ x t hpv_tail hx hfvt hLCt =>
      have ih' := ih hpv_tail htail
      -- Need: x ∉ (rest ++ Γ₁).dom, fv t ⊆ (rest ++ Γ₁).dom.
      have hx' : x ∉ Ctx.dom (rest ++ Γ₁) := by
        rw [Ctx.dom_append] at hx ⊢
        rw [Ctx.dom_cons] at hx
        intro hxnew
        rw [Finset.mem_union] at hxnew
        apply hx
        rw [Finset.mem_union]
        cases hxnew with
        | inl h1 => exact Or.inl h1
        | inr h1 => exact Or.inr (Finset.mem_insert_of_mem h1)
      have hfvt' : Term.fv t ⊆ Ctx.dom (rest ++ Γ₁) := by
        intro z hz
        have := hfvt hz
        rw [Ctx.dom_append, Ctx.dom_cons] at this
        rw [Ctx.dom_append]
        rw [Finset.mem_union] at this
        cases this with
        | inl h1 => exact Finset.mem_union.mpr (Or.inl h1)
        | inr h1 =>
          rw [Finset.mem_insert] at h1
          cases h1 with
          | inl hzy =>
            -- z = y, but z ∈ fv t and we have hhead: y ∉ fv (t = e.bound) for this entry.
            -- e here IS this `sub` entry, with bound = t. So hhead : y ∉ fv t.
            -- Wait, e.bound = t? Let's check: e = ⟨x, t, .sub⟩, e.bound = t. Yes.
            -- So z = y → z ∉ fv t, contradiction.
            subst hzy; exact absurd hz hhead
          | inr h2 => exact Finset.mem_union.mpr (Or.inr h2)
      exact Prevalid.sub ih' hx' hfvt' hLCt
    | @equ _ x β hpv_tail hx hfvβ hLCβ =>
      have ih' := ih hpv_tail htail
      have hx' : x ∉ Ctx.dom (rest ++ Γ₁) := by
        rw [Ctx.dom_append] at hx ⊢
        rw [Ctx.dom_cons] at hx
        intro hxnew
        rw [Finset.mem_union] at hxnew
        apply hx
        rw [Finset.mem_union]
        cases hxnew with
        | inl h1 => exact Or.inl h1
        | inr h1 => exact Or.inr (Finset.mem_insert_of_mem h1)
      have hfvβ' : Term.fv β ⊆ Ctx.dom (rest ++ Γ₁) := by
        intro z hz
        have := hfvβ hz
        rw [Ctx.dom_append, Ctx.dom_cons] at this
        rw [Ctx.dom_append]
        rw [Finset.mem_union] at this
        cases this with
        | inl h1 => exact Finset.mem_union.mpr (Or.inl h1)
        | inr h1 =>
          rw [Finset.mem_insert] at h1
          cases h1 with
          | inl hzy =>
            subst hzy; exact absurd hz hhead
          | inr h2 => exact Finset.mem_union.mpr (Or.inr h2)
      exact Prevalid.equ ih' hx' hfvβ' hLCβ

/-- `PrevalidExt` analog: remove the `.equ`-head from `Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁`.

Requires every Γ₂ entry's bound to avoid `y` (for `Prevalid.equ_head_remove_mid`)
AND every stack entry's fv to avoid `y` (since the new dom is smaller). -/
noncomputable def PrevalidExt.equ_head_remove_mid
    {Γ₁ Γ₂ : Ctx} {st : Stack} {y : String} {α : Term}
    (hpv : PrevalidExt (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁) st)
    (hΓ₂_avoid : Ctx.AvoidsBoundFv Γ₂ y)
    (hst_avoid : ∀ β ∈ st, y ∉ Term.fv β) :
    PrevalidExt (Γ₂ ++ Γ₁) st := by
  induction hpv with
  | nil hΓ =>
    exact PrevalidExt.nil (Prevalid.equ_head_remove_mid hΓ hΓ₂_avoid)
  | @cons _ β _hpvE hLCβ hfvβ ih =>
    -- Stack head = β; tail's freshness comes from hst_avoid restricted to tail.
    have hβ_avoid : y ∉ Term.fv β :=
      hst_avoid β (List.mem_cons_self _ _)
    have htail_avoid : ∀ β' ∈ _, y ∉ Term.fv β' := fun β' hβ' =>
      hst_avoid β' (List.mem_cons_of_mem _ hβ')
    have ih' := ih htail_avoid
    refine PrevalidExt.cons ih' hLCβ ?_
    -- New: fv β ⊆ (Γ₂ ++ Γ₁).dom. From hfvβ : fv β ⊆ (Γ₂ ++ ⟨y,α,.equ⟩::Γ₁).dom
    -- combined with y ∉ fv β.
    intro z hz
    have hzd := hfvβ hz
    rw [_Ctx_dom_eq_under_equ_head_remove] at hzd
    rw [Finset.mem_insert] at hzd
    cases hzd with
    | inl hzy => subst hzy; exact absurd hz hβ_avoid
    | inr hz' => exact hz'

/-! ### §10.1. Lookup-side helper: `y ∉ fv α_yi` under context-avoidance

For the `pro yi` arm of `strip_equ_head`, we need `y ∉ fv α_yi` where
`α_yi` is the looked-up bound term. With Γ₂'s entries' bounds avoiding
`y` (hypothesis (2)) and `y ∉ Γ₁.dom` + Γ₁'s Prevalid invariant, this
follows by case-split on whether `yi` is bound in Γ₂ or Γ₁:

* `yi ∈ Γ₂.dom`: `α_yi` is a Γ₂ entry's bound, which by hypothesis (2)
  has `y ∉ fv α_yi`. ✓
* `yi ∉ Γ₂.dom`: lookup goes past Γ₂, past the head (`yi ≠ y` from
  `avoidsPro_pro`), into Γ₁. By `Prevalid.fv_lookupEqu` on Γ₁'s tail at
  `yi`, `fv α_yi ⊆ Γ₁.dom`. With `y ∉ Γ₁.dom`, ✓. -/

/-- If `(Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁).equBinds yi α_yi`, `yi ≠ y`,
Γ₂'s entries' bounds avoid `y`, and `y ∉ Γ₁.dom`, then `y ∉ fv α_yi`.

Provides the missing premise for the `pro` arm of `strip_equ_head`. -/
private theorem _y_notin_fv_lookupEqu_under_avoid
    {Γ₁ Γ₂ : Ctx} {y yi : String} {α α_yi : Term}
    (hpv : Prevalid (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁))
    (hb : (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁).equBinds yi α_yi)
    (hyiy : yi ≠ y)
    (hΓ₂_avoid : Ctx.AvoidsBoundFv Γ₂ y)
    (hy_Γ₁ : y ∉ Γ₁.dom) :
    y ∉ Term.fv α_yi := by
  induction Γ₂ with
  | nil =>
    -- Lookup is in `⟨y, α, .equ⟩ :: Γ₁`. yi ≠ y, so lookup goes into Γ₁.
    show y ∉ Term.fv α_yi
    have hb' : Ctx.lookupEqu (⟨y, α, .equ⟩ :: Γ₁) yi = some α_yi := hb
    rw [Ctx.lookupEqu_cons] at hb'
    by_cases hyy : y = yi
    · exact absurd hyy.symm hyiy
    · simp [hyy] at hb'
      -- hb' : Ctx.lookupEqu Γ₁ yi = some α_yi
      have hpv₁ : Prevalid Γ₁ := by
        have hpv' : Prevalid (⟨y, α, .equ⟩ :: Γ₁) := by simpa using hpv
        cases hpv' with | equ hΓ _ _ _ => exact hΓ
      have hbΓ₁ : Γ₁.equBinds yi α_yi := hb'
      have hfv : Term.fv α_yi ⊆ Γ₁.dom :=
        Prevalid.fv_lookupEqu hpv₁ hbΓ₁
      exact fun h => hy_Γ₁ (hfv h)
  | cons e rest ih =>
    -- Lookup tries e first; if e.name = yi and e is .equ, found = e.bound.
    have ⟨hhead, htail⟩ := Ctx.AvoidsBoundFv_cons.mp hΓ₂_avoid
    have hpv' : Prevalid (e :: (rest ++ ⟨y, α, .equ⟩ :: Γ₁)) := by simpa using hpv
    have hpv_tail : Prevalid (rest ++ ⟨y, α, .equ⟩ :: Γ₁) := by
      cases hpv' with
      | sub hpv_t _ _ _ => exact hpv_t
      | equ hpv_t _ _ _ => exact hpv_t
    have hb' : Ctx.lookupEqu (e :: (rest ++ ⟨y, α, .equ⟩ :: Γ₁)) yi = some α_yi := hb
    rw [Ctx.lookupEqu_cons] at hb'
    by_cases he : e.name = yi
    · rw [if_pos he] at hb'
      cases hkind : e.kind with
      | sub => simp [hkind] at hb'
      | equ =>
        simp [hkind] at hb'
        -- hb' : e.bound = α_yi (after simp)
        -- hhead : y ∉ fv e.bound
        rw [← hb']
        exact hhead
    · rw [if_neg he] at hb'
      exact ih hpv_tail hb' htail

/-! ### §10.2. `MEqRed.strip_equ_head` architectural notes

The full functor is built in §10.3 below (shipped at iter 10).

The architectural sketch: `equ_head_replace` (§8.2) preserves
`Ctx.dom`, so subset / freshness invariants on terms, stack entries,
and Γ₂'s prior bindings transfer verbatim. `strip_equ_head` REMOVES
`y` from `Ctx.dom`, so every term mentioned anywhere in the
derivation tree must independently avoid `y`. The bundling premise
is

  `avoidsPro h y && cofinDomFresh h && avoidsFv h y`

* `avoidsPro h y = true`: no `Me-Pro y` step in `h` (preserves the
  `pro` arm: a `pro yi` lookup with `yi = y` would fail in
  `Γ₂ ++ Γ₁` since the binding has been removed).
* `cofinDomFresh h = true`: canonical `pickFresh L` witnesses are
  fresh w.r.t. the input dom and body fv (preserved from the
  `equ_head_replace` template).
* `avoidsFv h y = true`: every term referenced in the derivation
  tree (source, target, stack, sub-derivations recursively) is
  syntactically `y`-fresh. This is what supplies `y ∉ fv tt` for
  the `fun_` body extension, `y ∉ fv αi` for the `fOp` body
  extension, `y ∉ fv v` for the `app` operator's stack, and the
  `pro` arm's α_yi avoidance via §10.1.

The §10.1 helper `_y_notin_fv_lookupEqu_under_avoid` discharges the
`pro yi` arm's `y ∉ fv α_yi` premise (no `avoidsFv` data on the
looked-up bound — must derive from Γ₂'s `Ctx.AvoidsBoundFv` plus
Γ₁'s Prevalid).

Cross-reference: `Lemma_2_inline_app_bet_residual_axiom` in
`Pss/Mpss/Diamond.lean` (iter-6 blocker analysis at lines 571-697)
is the headline consumer. -/

/-! ### §10.3. `MEqRed.strip_equ_head` — the head-removal functor

Mirror of `MEqRed.equ_head_replace` (§8.2). Each cofinite arm
samples the canonical fresh `y₀ := pickFresh L` from the IH, then
renames `y₀ → yfresh` via `MEqRed.rename_stray` / `MEqRed.rename_sub`
/ `_MEqRed_rename_equ_no_fv`. The output cofinite L-set widens to
`L ∪ Ctx.dom (Γ₂ ++ Γ₁) ∪ {y₀}` (the new dom — without the stripped
`y` head).

The `avoidsFv` premise (iter-9) supplies `y`-freshness for every
term mentioned in the derivation tree, needed because
`y ∉ fv (Term.opening v0' body')` does NOT imply `y ∉ fv v0'` /
`y ∉ fv body'` separately. -/

/-- **Remove an `.equ`-head from a `MEqRed` derivation.**

Given:
* `h : MEqRed (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁) st u u'` — the input
  derivation.
* `hΓ₂_avoid : Ctx.AvoidsBoundFv Γ₂ y` — Γ₂ entries' bounds avoid
  `y`.
* `hy_Γ₁ : y ∉ Γ₁.dom` — `y` is unbound in Γ₁.
* `hst_avoid : ∀ β ∈ st, y ∉ Term.fv β` — stack entries avoid `y`.
* `hAvoid : avoidsPro h y = true` — no `Me-Pro y` step in `h`.
* `hFresh : cofinDomFresh h = true` — canonical witnesses fresh.
* `hAvoidFv : avoidsFv h y = true` — every term in the derivation
  tree avoids `y`.

Produces: `MEqRed (Γ₂ ++ Γ₁) st u u'`. -/
noncomputable def MEqRed.strip_equ_head
    {Γ₁ Γ₂ : Ctx} {st : Stack} {y : String} {α u u' : Term}
    (h : MEqRed (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁) st u u')
    (hΓ₂_avoid : Ctx.AvoidsBoundFv Γ₂ y)
    (hy_Γ₁ : y ∉ Γ₁.dom)
    (hst_avoid : ∀ β ∈ st, y ∉ Term.fv β)
    (hAvoid : avoidsPro h y = true)
    (hFresh : cofinDomFresh h = true)
    (hAvoidFv : avoidsFv h y = true) :
    MEqRed (Γ₂ ++ Γ₁) st u u' := by
  classical
  generalize hΓ : (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁) = Γ at h
  induction h generalizing Γ₂ with
  | @pro Γ st' yi β β' hpv heq hβ ihβ =>
    subst hΓ
    rw [avoidsPro_pro] at hAvoid
    rw [cofinDomFresh_pro] at hFresh
    rw [avoidsFv_pro] at hAvoidFv
    obtain ⟨hyiy_decide, hAvoid_inner⟩ := Bool.and_eq_true _ _ |>.mp hAvoid
    have hyiy : yi ≠ y := decide_eq_true_eq.mp hyiy_decide
    -- Decompose hAvoidFv: (((y ∉ fv (fvar yi) && y ∉ fv β') && stack) && rec).
    obtain ⟨hAvoidFv_left, hAvoidFv_inner⟩ := Bool.and_eq_true _ _ |>.mp hAvoidFv
    obtain ⟨hAvoidFv_left2, hAvoidFv_stack⟩ := Bool.and_eq_true _ _ |>.mp hAvoidFv_left
    obtain ⟨_hAvoidFv_yi, _hAvoidFv_β'⟩ := Bool.and_eq_true _ _ |>.mp hAvoidFv_left2
    -- Get Prevalid of input ctx for the §10.1 helper.
    have hpvFull : Prevalid (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁) := extractPrevalid hpv
    have hy_β : y ∉ Term.fv β :=
      _y_notin_fv_lookupEqu_under_avoid hpvFull heq hyiy hΓ₂_avoid hy_Γ₁
    -- New stack-avoidance: same st', same predicate.
    have hpv' : PrevalidExt (Γ₂ ++ Γ₁) st' :=
      PrevalidExt.equ_head_remove_mid hpv hΓ₂_avoid hst_avoid
    have heq' := _equBinds_equ_head_remove_neq hyiy heq
    exact MEqRed.pro hpv' heq' (ihβ (Γ₂ := Γ₂) hΓ₂_avoid hst_avoid rfl hAvoid_inner hFresh
      hAvoidFv_inner)
  | @bet Γ st' tBound v0 v0' bd bd' L hLCt hbody _hUni hv ihbody ihv =>
    subst hΓ
    rw [avoidsPro_bet] at hAvoid
    rw [cofinDomFresh_bet] at hFresh
    rw [avoidsFv_bet] at hAvoidFv
    obtain ⟨hAvoid_body, hAvoid_v⟩ := Bool.and_eq_true _ _ |>.mp hAvoid
    -- Decompose hFresh: (((dom && fvbd) && fvbd') && body) && v.
    obtain ⟨hFresh_left_v, hFresh_v⟩ := Bool.and_eq_true _ _ |>.mp hFresh
    obtain ⟨hFresh_left_body, hFresh_body⟩ := Bool.and_eq_true _ _ |>.mp hFresh_left_v
    obtain ⟨hFresh_left_fvbd', hFresh_fvbd'_dec⟩ :=
      Bool.and_eq_true _ _ |>.mp hFresh_left_body
    obtain ⟨hFresh_dom_dec, hFresh_fvbd_dec⟩ :=
      Bool.and_eq_true _ _ |>.mp hFresh_left_fvbd'
    -- Decompose hAvoidFv: ((((src && tgt) && stack) && body) && v).
    obtain ⟨hAvoidFv_left_v, hAvoidFv_v⟩ := Bool.and_eq_true _ _ |>.mp hAvoidFv
    obtain ⟨hAvoidFv_left_body, hAvoidFv_body⟩ :=
      Bool.and_eq_true _ _ |>.mp hAvoidFv_left_v
    obtain ⟨hAvoidFv_left_stack, _hAvoidFv_stack⟩ :=
      Bool.and_eq_true _ _ |>.mp hAvoidFv_left_body
    obtain ⟨_hAvoidFv_src, _hAvoidFv_tgt⟩ :=
      Bool.and_eq_true _ _ |>.mp hAvoidFv_left_stack
    have hy₀_dom : pickFresh L ∉ Ctx.dom (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁) :=
      decide_eq_true_eq.mp hFresh_dom_dec
    have hy₀_fvbd : pickFresh L ∉ Term.fv bd :=
      decide_eq_true_eq.mp hFresh_fvbd_dec
    have hy₀_fvbd' : pickFresh L ∉ Term.fv bd' :=
      decide_eq_true_eq.mp hFresh_fvbd'_dec
    let y₀ := pickFresh L
    have hy₀L : y₀ ∉ L := pickFresh_notMem L
    -- y₀ ∉ removed-context dom (smaller).
    have hy₀_dom' : y₀ ∉ Ctx.dom (Γ₂ ++ Γ₁) := by
      intro h_in
      apply hy₀_dom
      rw [_Ctx_dom_eq_under_equ_head_remove]
      exact Finset.mem_insert_of_mem h_in
    -- IH calls. Body keeps Γ₂; stack stays = st'; ctx-avoid + stack-avoid unchanged.
    have ihbody_y₀ := ihbody y₀ hy₀L (Γ₂ := Γ₂) hΓ₂_avoid hst_avoid rfl
      hAvoid_body hFresh_body hAvoidFv_body
    -- Operand v: at empty stack, vacuous stack-avoid.
    have hv_stack_avoid : ∀ β ∈ ([] : Stack), y ∉ Term.fv β := by
      intro β hβ; cases hβ
    have ihv' := ihv (Γ₂ := Γ₂) hΓ₂_avoid hv_stack_avoid rfl hAvoid_v hFresh_v hAvoidFv_v
    -- Build the output bet at the smaller context.
    refine MEqRed.bet (L ∪ Ctx.dom (Γ₂ ++ Γ₁) ∪ {y₀})
      hLCt ?_ trivial ihv'
    intro yfresh hyfresh
    simp only [Finset.mem_union, Finset.mem_singleton] at hyfresh
    push_neg at hyfresh
    obtain ⟨⟨hyfL, hyf_dom⟩, hyf_y₀⟩ := hyfresh
    -- Prevalid for the output context.
    have hpvE_y₀ : PrevalidExt (Γ₂ ++ Γ₁) st' :=
      MEqRed.prevalidExt ihbody_y₀
    have hpv_removed : Prevalid (Γ₂ ++ Γ₁) := extractPrevalid hpvE_y₀
    -- Stack freshness for y₀ via PrevalidExt at the new context.
    have hy₀_stack : ∀ β ∈ st', y₀ ∉ Term.fv β :=
      _y₀_notin_stack_fv_of_notin_dom hpvE_y₀ hy₀_dom'
    -- Rename y₀ → yfresh.
    have ren := MEqRed.rename_stray hpv_removed ihbody_y₀ y₀ yfresh hy₀_dom' hyf_dom
    have hstk_eq : Stack.subst y₀ (.fvar yfresh) st' = st' :=
      Stack.subst_fresh hy₀_stack
    have hbd_eq : Term.subst y₀ (.fvar yfresh) (bd^[y₀]) = bd^[yfresh] :=
      Term.subst_open_fresh hy₀_fvbd
    have hbd'_eq : Term.subst y₀ (.fvar yfresh) (bd'^[y₀]) = bd'^[yfresh] :=
      Term.subst_open_fresh hy₀_fvbd'
    rw [hstk_eq, hbd_eq, hbd'_eq] at ren
    exact ren
  | @top Γ st' hpv =>
    subst hΓ
    have hpv' : PrevalidExt (Γ₂ ++ Γ₁) st' :=
      PrevalidExt.equ_head_remove_mid hpv hΓ₂_avoid hst_avoid
    exact MEqRed.top hpv'
  | @app Γ st' u_ u_' v_ v_' hu hv ihu ihv =>
    subst hΓ
    rw [avoidsPro_app] at hAvoid
    rw [cofinDomFresh_app] at hFresh
    rw [avoidsFv_app] at hAvoidFv
    obtain ⟨hAvoid_u, hAvoid_v⟩ := Bool.and_eq_true _ _ |>.mp hAvoid
    obtain ⟨hFresh_u, hFresh_v⟩ := Bool.and_eq_true _ _ |>.mp hFresh
    -- Decompose hAvoidFv: ((((src && tgt) && stack) && u) && v).
    obtain ⟨hAvoidFv_left_v, hAvoidFv_v⟩ := Bool.and_eq_true _ _ |>.mp hAvoidFv
    obtain ⟨hAvoidFv_left_u, hAvoidFv_u⟩ := Bool.and_eq_true _ _ |>.mp hAvoidFv_left_v
    obtain ⟨hAvoidFv_left_stack, _hAvoidFv_stack⟩ :=
      Bool.and_eq_true _ _ |>.mp hAvoidFv_left_u
    obtain ⟨hAvoidFv_src, _hAvoidFv_tgt⟩ :=
      Bool.and_eq_true _ _ |>.mp hAvoidFv_left_stack
    -- src = .app u_ v_; y ∉ fv src ⇒ y ∉ fv v_, needed for stack of u arm.
    have hy_src : y ∉ Term.fv (Term.app u_ v_) :=
      decide_eq_true_eq.mp hAvoidFv_src
    have hy_v_ : y ∉ Term.fv v_ := by
      intro h_in; apply hy_src; rw [Term.fv_app]
      exact Finset.mem_union.mpr (Or.inr h_in)
    -- Stack for u arm = v_ :: st'; stack-avoid extends.
    have hu_stack_avoid : ∀ β ∈ (v_ :: st'), y ∉ Term.fv β := by
      intro β hβ
      rcases List.mem_cons.mp hβ with rfl | hβtail
      · exact hy_v_
      · exact hst_avoid β hβtail
    have hv_stack_avoid : ∀ β ∈ ([] : Stack), y ∉ Term.fv β := by
      intro β hβ; cases hβ
    have ihu' := ihu (Γ₂ := Γ₂) hΓ₂_avoid hu_stack_avoid rfl hAvoid_u hFresh_u hAvoidFv_u
    have ihv' := ihv (Γ₂ := Γ₂) hΓ₂_avoid hv_stack_avoid rfl hAvoid_v hFresh_v hAvoidFv_v
    exact MEqRed.app ihu' ihv'
  | @var Γ st' yi hpv =>
    subst hΓ
    have hpv' : PrevalidExt (Γ₂ ++ Γ₁) st' :=
      PrevalidExt.equ_head_remove_mid hpv hΓ₂_avoid hst_avoid
    exact MEqRed.var hpv'
  | @fun_ Γ tt tt' bd bd' L ht hbody _hUni iht ihbody =>
    subst hΓ
    rw [avoidsPro_fun_] at hAvoid
    rw [cofinDomFresh_fun_] at hFresh
    rw [avoidsFv_fun_] at hAvoidFv
    obtain ⟨hAvoid_t, hAvoid_body⟩ := Bool.and_eq_true _ _ |>.mp hAvoid
    obtain ⟨hFresh_left_body, hFresh_body⟩ := Bool.and_eq_true _ _ |>.mp hFresh
    obtain ⟨hFresh_left_t, hFresh_t⟩ := Bool.and_eq_true _ _ |>.mp hFresh_left_body
    obtain ⟨hFresh_left_fvbd', hFresh_fvbd'_dec⟩ :=
      Bool.and_eq_true _ _ |>.mp hFresh_left_t
    obtain ⟨hFresh_dom_dec, hFresh_fvbd_dec⟩ :=
      Bool.and_eq_true _ _ |>.mp hFresh_left_fvbd'
    -- Decompose hAvoidFv: (((src && tgt) && t) && body).
    obtain ⟨hAvoidFv_left_body, hAvoidFv_body⟩ :=
      Bool.and_eq_true _ _ |>.mp hAvoidFv
    obtain ⟨hAvoidFv_left_t, hAvoidFv_t⟩ :=
      Bool.and_eq_true _ _ |>.mp hAvoidFv_left_body
    obtain ⟨hAvoidFv_src, _hAvoidFv_tgt⟩ :=
      Bool.and_eq_true _ _ |>.mp hAvoidFv_left_t
    -- src = .abs tt bd; y ∉ fv src ⇒ y ∉ fv tt, needed for the new Γ₂'.
    have hy_src : y ∉ Term.fv (Term.abs tt bd) :=
      decide_eq_true_eq.mp hAvoidFv_src
    have hy_tt : y ∉ Term.fv tt := by
      intro h_in; apply hy_src; rw [Term.fv_abs]
      exact Finset.mem_union.mpr (Or.inl h_in)
    have hy₀_dom : pickFresh L ∉ Ctx.dom (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁) :=
      decide_eq_true_eq.mp hFresh_dom_dec
    have hy₀_fvbd : pickFresh L ∉ Term.fv bd :=
      decide_eq_true_eq.mp hFresh_fvbd_dec
    have hy₀_fvbd' : pickFresh L ∉ Term.fv bd' :=
      decide_eq_true_eq.mp hFresh_fvbd'_dec
    let y₀ := pickFresh L
    have hy₀L : y₀ ∉ L := pickFresh_notMem L
    have hy₀_dom' : y₀ ∉ Ctx.dom (Γ₂ ++ Γ₁) := by
      intro h_in
      apply hy₀_dom
      rw [_Ctx_dom_eq_under_equ_head_remove]
      exact Finset.mem_insert_of_mem h_in
    -- t IH at empty stack.
    have ht_stack_avoid : ∀ β ∈ ([] : Stack), y ∉ Term.fv β := by
      intro β hβ; cases hβ
    have iht' := iht (Γ₂ := Γ₂) hΓ₂_avoid ht_stack_avoid rfl hAvoid_t hFresh_t hAvoidFv_t
    -- body IH at extended Γ₂' = ⟨y₀, tt, .sub⟩ :: Γ₂; stack = [].
    have hΓ₂'_avoid : Ctx.AvoidsBoundFv (⟨y₀, tt, .sub⟩ :: Γ₂) y :=
      Ctx.AvoidsBoundFv_cons.mpr ⟨hy_tt, hΓ₂_avoid⟩
    have hbody_stack_avoid : ∀ β ∈ ([] : Stack), y ∉ Term.fv β := by
      intro β hβ; cases hβ
    have ihbody_y₀ := ihbody y₀ hy₀L
      (Γ₂ := ⟨y₀, tt, .sub⟩ :: Γ₂) hΓ₂'_avoid hbody_stack_avoid (by simp)
      hAvoid_body hFresh_body hAvoidFv_body
    refine MEqRed.fun_ (L ∪ Ctx.dom (Γ₂ ++ Γ₁) ∪ {y₀}) iht' ?_ trivial
    intro yfresh hyfresh
    simp only [Finset.mem_union, Finset.mem_singleton] at hyfresh
    push_neg at hyfresh
    obtain ⟨⟨hyfL, hyf_dom⟩, hyf_y₀⟩ := hyfresh
    -- Extract data from ihbody_y₀'s prevalidExt.
    have ihbody_y₀_norm : MEqRed (⟨y₀, tt, .sub⟩ :: (Γ₂ ++ Γ₁)) []
        (bd^[y₀]) (bd'^[y₀]) := by simpa using ihbody_y₀
    have hpvE_full : PrevalidExt (⟨y₀, tt, .sub⟩ :: (Γ₂ ++ Γ₁)) [] :=
      MEqRed.prevalidExt ihbody_y₀_norm
    have hpv_full : Prevalid (⟨y₀, tt, .sub⟩ :: (Γ₂ ++ Γ₁)) :=
      extractPrevalid hpvE_full
    have hpv_outer : Prevalid (Γ₂ ++ Γ₁) := by
      cases hpv_full with
      | sub hpv _ _ _ => exact hpv
    have hLCt_tt : Term.LC tt := by
      cases hpv_full with
      | sub _ _ _ hLCtt => exact hLCtt
    have hfvtt : Term.fv tt ⊆ Ctx.dom (Γ₂ ++ Γ₁) := by
      cases hpv_full with
      | sub _ _ hfvtt _ => exact hfvtt
    -- Apply MEqRed.rename_sub. Stack is empty for fun_, so stack-freshness is trivial.
    have ren := MEqRed.rename_sub hpv_outer hLCt_tt hfvtt
      hy₀_dom' hyf_dom hy₀_fvbd hy₀_fvbd'
      (by intro β hβ; cases hβ) ihbody_y₀_norm
    simpa using ren
  | @tAp Γ st' u_ hpv hLCu hfv =>
    subst hΓ
    have hpv' : PrevalidExt (Γ₂ ++ Γ₁) st' :=
      PrevalidExt.equ_head_remove_mid hpv hΓ₂_avoid hst_avoid
    -- Need fv u_ ⊆ (Γ₂ ++ Γ₁).dom. From original hfv : ⊆ insert y (Γ₂ ++ Γ₁).dom and
    -- y ∉ fv u_ (from hAvoidFv at this case).
    rw [avoidsFv_tAp] at hAvoidFv
    obtain ⟨hAvoidFv_src, _hAvoidFv_stack⟩ :=
      Bool.and_eq_true _ _ |>.mp hAvoidFv
    -- src = .app .top u_; y ∉ fv src ⇒ y ∉ fv u_.
    have hy_src : y ∉ Term.fv (Term.app Term.top u_) :=
      decide_eq_true_eq.mp hAvoidFv_src
    have hy_u : y ∉ Term.fv u_ := by
      intro h_in; apply hy_src; rw [Term.fv_app]
      exact Finset.mem_union.mpr (Or.inr h_in)
    have hfv' : Term.fv u_ ⊆ Ctx.dom (Γ₂ ++ Γ₁) := by
      intro z hz
      have hzd := hfv hz
      rw [_Ctx_dom_eq_under_equ_head_remove] at hzd
      rw [Finset.mem_insert] at hzd
      cases hzd with
      | inl hzy => subst hzy; exact absurd hz hy_u
      | inr hz' => exact hz'
    exact MEqRed.tAp hpv' hLCu hfv'
  | @fOp Γ st' tt tt' αi bd bd' L ht hbody _hUni iht ihbody =>
    subst hΓ
    rw [avoidsPro_fOp] at hAvoid
    rw [cofinDomFresh_fOp] at hFresh
    rw [avoidsFv_fOp] at hAvoidFv
    obtain ⟨hAvoid_t, hAvoid_body⟩ := Bool.and_eq_true _ _ |>.mp hAvoid
    obtain ⟨hFresh_left_body, hFresh_body⟩ := Bool.and_eq_true _ _ |>.mp hFresh
    obtain ⟨hFresh_left_t, hFresh_t⟩ := Bool.and_eq_true _ _ |>.mp hFresh_left_body
    obtain ⟨hFresh_left_fvbd', hFresh_fvbd'_dec⟩ :=
      Bool.and_eq_true _ _ |>.mp hFresh_left_t
    obtain ⟨hFresh_dom_dec, hFresh_fvbd_dec⟩ :=
      Bool.and_eq_true _ _ |>.mp hFresh_left_fvbd'
    -- Decompose hAvoidFv: ((((src && tgt) && stack(α::st')) && t) && body).
    obtain ⟨hAvoidFv_left_body, hAvoidFv_body⟩ :=
      Bool.and_eq_true _ _ |>.mp hAvoidFv
    obtain ⟨hAvoidFv_left_t, hAvoidFv_t⟩ :=
      Bool.and_eq_true _ _ |>.mp hAvoidFv_left_body
    obtain ⟨hAvoidFv_left_stack, hAvoidFv_stack⟩ :=
      Bool.and_eq_true _ _ |>.mp hAvoidFv_left_t
    obtain ⟨_hAvoidFv_src, _hAvoidFv_tgt⟩ :=
      Bool.and_eq_true _ _ |>.mp hAvoidFv_left_stack
    -- Stack at this node is αi :: st'; we need y ∉ fv αi.
    have hy_αi : y ∉ Term.fv αi := by
      have h_all : (αi :: st').all (fun β => decide (y ∉ Term.fv β)) = true :=
        hAvoidFv_stack
      rw [List.all_cons, Bool.and_eq_true] at h_all
      exact decide_eq_true_eq.mp h_all.1
    have hy₀_dom : pickFresh L ∉ Ctx.dom (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁) :=
      decide_eq_true_eq.mp hFresh_dom_dec
    have hy₀_fvbd : pickFresh L ∉ Term.fv bd :=
      decide_eq_true_eq.mp hFresh_fvbd_dec
    have hy₀_fvbd' : pickFresh L ∉ Term.fv bd' :=
      decide_eq_true_eq.mp hFresh_fvbd'_dec
    let y₀ := pickFresh L
    have hy₀L : y₀ ∉ L := pickFresh_notMem L
    have hy₀_dom' : y₀ ∉ Ctx.dom (Γ₂ ++ Γ₁) := by
      intro h_in
      apply hy₀_dom
      rw [_Ctx_dom_eq_under_equ_head_remove]
      exact Finset.mem_insert_of_mem h_in
    -- t IH at empty stack.
    have ht_stack_avoid : ∀ β ∈ ([] : Stack), y ∉ Term.fv β := by
      intro β hβ; cases hβ
    have iht' := iht (Γ₂ := Γ₂) hΓ₂_avoid ht_stack_avoid rfl hAvoid_t hFresh_t hAvoidFv_t
    -- body IH at extended Γ₂' = ⟨y₀, αi, .equ⟩ :: Γ₂; stack = st' (after pop).
    -- Stack-avoid for st': from outer hst_avoid which was for the ORIGINAL stack
    -- (αi :: st' at this fOp node). Body recurses at st' alone.
    have hst'_avoid : ∀ β ∈ st', y ∉ Term.fv β := fun β hβ =>
      hst_avoid β (List.mem_cons_of_mem _ hβ)
    have hΓ₂'_avoid : Ctx.AvoidsBoundFv (⟨y₀, αi, .equ⟩ :: Γ₂) y :=
      Ctx.AvoidsBoundFv_cons.mpr ⟨hy_αi, hΓ₂_avoid⟩
    have ihbody_y₀ := ihbody y₀ hy₀L
      (Γ₂ := ⟨y₀, αi, .equ⟩ :: Γ₂) hΓ₂'_avoid hst'_avoid (by simp)
      hAvoid_body hFresh_body hAvoidFv_body
    refine MEqRed.fOp (L ∪ Ctx.dom (Γ₂ ++ Γ₁) ∪ {y₀}) iht' ?_ trivial
    intro yfresh hyfresh
    simp only [Finset.mem_union, Finset.mem_singleton] at hyfresh
    push_neg at hyfresh
    obtain ⟨⟨hyfL, hyf_dom⟩, hyf_y₀⟩ := hyfresh
    have hyz : y₀ ≠ yfresh := fun h' => hyf_y₀ h'.symm
    have ihbody_y₀_norm :
        MEqRed (⟨y₀, αi, .equ⟩ :: (Γ₂ ++ Γ₁)) st'
          (bd^[y₀]) (bd'^[y₀]) := by simpa using ihbody_y₀
    have hpvE_full : PrevalidExt (⟨y₀, αi, .equ⟩ :: (Γ₂ ++ Γ₁)) st' :=
      MEqRed.prevalidExt ihbody_y₀_norm
    have hpv_full : Prevalid (⟨y₀, αi, .equ⟩ :: (Γ₂ ++ Γ₁)) :=
      extractPrevalid hpvE_full
    have hfv_αi : Term.fv αi ⊆ Ctx.dom (Γ₂ ++ Γ₁) := by
      cases hpv_full with
      | equ _ _ hfvαi _ => exact hfvαi
    have hy₀_αi : y₀ ∉ Term.fv αi := fun h' => hy₀_dom' (hfv_αi h')
    -- Stack freshness for y₀ at the body's PrevalidExt. Since st' lives at the
    -- EXTENDED ctx, entries' fv ⊆ insert y₀ (Γ₂ ++ Γ₁).dom — they could mention y₀.
    -- Use the OUTER context's PrevalidExt at outer st (αi :: st') instead.
    have hpv_outer_inputst : PrevalidExt (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁) (αi :: st') :=
      MEqRed.prevalidExt (MEqRed.fOp L ht hbody trivial)
    have hpv_outer_st_only : PrevalidExt (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁) st' := by
      cases hpv_outer_inputst with
      | cons hpv_tail _ _ => exact hpv_tail
    have hy₀_stack : ∀ β ∈ st', y₀ ∉ Term.fv β :=
      _y₀_notin_stack_fv_of_notin_dom hpv_outer_st_only hy₀_dom
    -- Apply _MEqRed_rename_equ_no_fv. Stack itself doesn't depend on the head, so
    -- y₀ ∉ fv st' is the same statement at either context.
    have ren := _MEqRed_rename_equ_no_fv hyz hy₀_dom' hyf_dom hy₀_αi
      hy₀_fvbd hy₀_fvbd' hy₀_stack ihbody_y₀_norm
    simpa using ren

/-! ### §9.4. MSubRed analog — DEFERRED to a follow-up phase

A natural follow-up would build `MSubRed.stack_replace` /
`MSubRed.stack_head_replace` mirroring the MEqRed proof. The roadblock:
the MSubRed avoidance/freshness Bool functions (`msAvoidsPro`,
`msCofinDomFresh`, `msCofinAvoidsProSelf`) are parametrized by an
alignment string `x : String` (because `MSubRed.equ_head_replace`'s
sample point depends on the binding name `y` it's swapping at). The
`fOp` Case A delegation to `MSubRed.equ_head_replace` would call it with
`y := z` (the inner canonical sample), which makes equ_head_replace's
inner alignment string `z`, NOT the stack_replace's outer alignment `x`.
Inside `MSubRed.equ_head_replace`, nested fOps then sample at
`pickFresh (msAvoidsPro_L_aug ... z)`, but the stack_replace caller's
premises are at sample `pickFresh (msAvoidsPro_L_aug ... x)` — different
alignment strings, no straightforward way to convert without alpha-
equivariance.

The headline Phase 4 target (`Lemma_2_DiamondMEqRed_ctx_axiom`'s App×App
arm, eliminating `_ctx_axiom` from Theorems 3, 4, 5 and Lemma 1, 2)
operates on MEqRed only — so the MEqRed-only Phase 3 is sufficient to
unblock the most-leveraged headline residual. The MSubRed analog is
needed for `Lemma_1_ctx_axiom` (also App×App-shaped, but mixed
MEqRed/MSubRed); a future session can address it via either:

* Adopting a sample-alignment-free Bool predicate for MSubRed (e.g.,
  sampling at `pickFresh (L ∪ fv body ∪ fv body')` with NO `x` parameter)
  and refactoring `MSubRed.equ_head_replace` to use it; or
* Threading the alignment string through `stack_replace` consistently
  via an additional `x` premise that the caller chooses to match the
  inner Case A sample (workable when the caller knows the inner sample's
  shape ahead of time).

Phase 3 ships MEqRed.stack_replace / .stack_head_replace only. -/

/-! ## §11. `descend_body_equ` — template-aware descent functor on body
derivations (Phase A: `body = .bvar 0` leaf case)

### Architectural picture

`Lemma_2_inline_app_bet_residual_axiom` (the iter-12 headline blocker)
needs an "honest descent" operation: given a derivation living at the
extended context `(⟨y, α, .equ⟩ :: Γ)` with source `body^[y]` (the
opening of some body template `body : Term` at `y`), produce a
derivation at the bare `Γ` with source `body^[z]` for a fresh `z` of
the caller's choice.

The paper sidesteps the obligation via α-conversion on named binders:
"the body is α-equivalent to one freshened over `z`, so we can just
work at `z`". Our locally-nameless mechanization makes the obligation
explicit. The full descent functor `descend_body_equ` will recurse on
the **body template's** structure (with cases for `.bvar 0`, `.fvar`,
`.app`, `.abs`, `.bvar (n+1)`, `.top`, etc.), each branch handling the
shape of `body^[y]` after the opening that template produces.

The total functor is decomposed into Phases A, B, C:

* **Phase A** (this section): `body = .bvar 0` leaf case. The opening
  `(.bvar 0)^[y]` reduces to `.fvar y`, so the source is literally the
  binder name. Possible MEqRed constructors at source `.fvar y` are
  `pro` and `var`; the paper's "moreover" clause (mechanized as
  `avoidsPro h y = true`) rules out `pro`, leaving `var`.
* **Phase B** (future): per-template recursion on the other body shapes
  (`.fvar`, `.app`, `.abs`, deeper `.bvar`, `.top`).
* **Phase C** (future): assembly into `descend_body_equ` proper, paired
  with the "moreover"-clause hypotheses that route through Lemma 2's
  inline-app-bet-residual closing step.

### Phase A signature

The `body = .bvar 0` instantiation — once `(.bvar 0)^[y] = .fvar y` is
applied — collapses to: descend a `MEqRed (⟨y, α, .equ⟩ :: Γ) s (.fvar y)
target_y` derivation, with avoidance `avoidsPro h y = true`, to a bare-
Γ derivation at source `.fvar z`. The substitution `Term.subst y (.fvar z)`
applied to the target lines up with the renamed source after the descent.

For the `.bvar 0` template specifically, the only outputs target_y can
take are `.fvar y` itself (via `MEqRed.var`) — `pro` would emit some β'
but is excluded by `avoidsPro`. So the post-substituted target is `.fvar z`
and the resulting derivation is `MEqRed.var hpv'` at the bare Γ. -/

/-- **Phase A — `body = .bvar 0` leaf case of the descent functor.**

Given a derivation at the extended context `(⟨y, α, .equ⟩ :: Γ)` whose
source is `.fvar y` (the opening of `.bvar 0` at `y`), produce a
derivation at the bare context `Γ` whose source is `.fvar z` for a
caller-chosen fresh `z`.

The `avoidsPro h y = true` premise (the paper's "moreover" clause)
rules out the `MEqRed.pro` constructor, leaving only `MEqRed.var`.

This is the simplest leaf of the template-aware functor
`descend_body_equ` — see the §11 header for the full architectural
picture. -/
noncomputable def MEqRed.descend_body_equ_bvar0
    {Γ : Ctx} {s : Stack} {y : String} {α target_y : Term}
    (h : MEqRed (⟨y, α, .equ⟩ :: Γ) s (.fvar y) target_y)
    (hAvoid : avoidsPro h y = true)
    (hst_avoid : ∀ β ∈ s, y ∉ Term.fv β)
    (z : String) :
    MEqRed Γ s (.fvar z) (Term.subst y (.fvar z) target_y) := by
  classical
  -- Case-analyze on h. Source `.fvar y` rules out everything except
  -- `pro` (excluded by hAvoid) and `var`.
  cases h with
  | @pro _ _ _ β β' hpv heq hβ =>
    -- Source `.fvar y` here forces the constructor's `x = y`. Then
    -- avoidsPro_pro adds factor `decide (y ≠ y) && _`, contradiction.
    rw [avoidsPro_pro] at hAvoid
    simp at hAvoid
  | @var _ _ _ hpv =>
    -- Source `.fvar y`, target `.fvar y`. After `Term.subst y (.fvar z)`,
    -- target becomes `.fvar z`. Build `MEqRed.var` at the head-removed
    -- context.
    have hΓ₂_avoid : Ctx.AvoidsBoundFv ([] : Ctx) y := Ctx.AvoidsBoundFv_nil y
    have hpv' : PrevalidExt ([] ++ Γ) s :=
      PrevalidExt.equ_head_remove_mid (Γ₂ := []) hpv hΓ₂_avoid hst_avoid
    have hpv'' : PrevalidExt Γ s := by simpa using hpv'
    -- Goal target after substitution.
    show MEqRed Γ s (.fvar z) (Term.subst y (.fvar z) (.fvar y))
    rw [Term.subst_fvar_eq]
    exact MEqRed.var hpv''

/-! ### §11.1. Phase B (case `body = .top`).

The opening `(.top)^[y]` reduces to `.top` (opening leaves `.top`
untouched), so the source is literally `.top`. The only constructor
that produces source `.top` is `MEqRed.top`. Its target is also `.top`.
After `Term.subst y (.fvar z) .top = .top`, the resulting derivation is
`MEqRed.top` at the head-removed bare `Γ`, built by
`PrevalidExt.equ_head_remove_mid` with `Γ₂ = []`. -/

/-- **Phase B (case `body = .top`).**

Given a derivation at `(⟨y, α, .equ⟩ :: Γ)` with source `.top`,
produce the same shape at the bare `Γ`. The post-substituted target is
`.top` (substitution is a no-op on `.top`). -/
noncomputable def MEqRed.descend_body_equ_top
    {Γ : Ctx} {s : Stack} {y : String} {α target_y : Term}
    (h : MEqRed (⟨y, α, .equ⟩ :: Γ) s .top target_y)
    (hAvoid : avoidsPro h y = true)
    (hst_avoid : ∀ β ∈ s, y ∉ Term.fv β)
    (z : String) :
    MEqRed Γ s .top (Term.subst y (.fvar z) target_y) := by
  classical
  -- `hAvoid` is unused here — no `pro` constructor produces source `.top`.
  -- Source `.top` admits only `MEqRed.top` as a constructor.
  cases h with
  | @top _ _ hpv =>
    have hΓ₂_avoid : Ctx.AvoidsBoundFv ([] : Ctx) y := Ctx.AvoidsBoundFv_nil y
    have hpv' : PrevalidExt ([] ++ Γ) s :=
      PrevalidExt.equ_head_remove_mid (Γ₂ := []) hpv hΓ₂_avoid hst_avoid
    have hpv'' : PrevalidExt Γ s := by simpa using hpv'
    show MEqRed Γ s .top (Term.subst y (.fvar z) .top)
    -- subst on .top is a no-op.
    show MEqRed Γ s .top .top
    exact MEqRed.top hpv''

/-! ### §11.2. Phase B (case `body = .fvar w`, `w ≠ y`).

The opening `(.fvar w)^[y]` is `.fvar w` (opening only touches `.bvar 0`),
so the source is `.fvar w` with `w ≠ y`. Possible constructors:

* `MEqRed.var` — target = `.fvar w`. Substituting `y` for `.fvar z` in
  `.fvar w` is a no-op (since `w ≠ y`), so the target stays `.fvar w`,
  matching `MEqRed.var hpv'` at the head-removed bare `Γ`.

* `MEqRed.pro hpv heq hβ` — target = β'. The constructor's `x = w`
  (from source-shape match), and from `heq : Γ.equBinds w β` with `w ≠ y`,
  `_equBinds_equ_head_remove_neq` lifts to `(Γ ++ []).equBinds w β` (i.e.
  bare `Γ`-binding). The inner derivation `hβ : MEqRed (⟨y,α,.equ⟩::Γ) s β β'`
  is descended via `MEqRed.strip_equ_head` (with `Γ₂ = []`), which removes
  the head equ-binding wholesale. The output post-substitution: since
  `y ∉ fv β'` (extracted from `hAvoidFv h y`), `Term.subst y (.fvar z) β' = β'`,
  so the goal lines up with `MEqRed.pro hpv' heq' (strip_equ_head hβ ...)`.

  The `pro` arm needs the bundling premises that `strip_equ_head`
  requires: `cofinDomFresh h = true`, `avoidsFv h y = true`, plus
  `y ∉ Γ.dom` for §10.1's lookup helper. -/

/-- **Phase B (case `body = .fvar w`, `w ≠ y`).**

Given a derivation at `(⟨y, α, .equ⟩ :: Γ)` with source `.fvar w` for
`w ≠ y`, produce a derivation at the bare `Γ` with source `.fvar w` and
target `Term.subst y (.fvar z) target_y`. -/
noncomputable def MEqRed.descend_body_equ_fvar
    {Γ : Ctx} {s : Stack} {y w : String} {α target_y : Term}
    (hwy : w ≠ y)
    (h : MEqRed (⟨y, α, .equ⟩ :: Γ) s (.fvar w) target_y)
    (hAvoid : avoidsPro h y = true)
    (hFresh : cofinDomFresh h = true)
    (hAvoidFv : avoidsFv h y = true)
    (hy_Γ : y ∉ Γ.dom)
    (hst_avoid : ∀ β ∈ s, y ∉ Term.fv β)
    (z : String) :
    MEqRed Γ s (.fvar w) (Term.subst y (.fvar z) target_y) := by
  classical
  cases h with
  | @pro _ _ _ aLkup _ hpv heq hβ =>
    -- The constructor's `α'` is forced by goal unification to be `target_y`,
    -- so it appears as `target_y` in the body. The constructor's `α` (the
    -- looked-up bound term) gets bound to `aLkup`. The `x` index gets
    -- substituted to `w` (rigid match on `.fvar w` source).
    -- avoidsPro_pro: factor `decide (w ≠ y)`, combined with the recursive
    -- avoidsPro on hβ.
    rw [avoidsPro_pro] at hAvoid
    obtain ⟨_hwy_decide, hAvoid_inner⟩ := Bool.and_eq_true _ _ |>.mp hAvoid
    -- Decompose hAvoidFv: ((src && tgt) && stack) && rec.
    rw [avoidsFv_pro] at hAvoidFv
    obtain ⟨hAvoidFv_left, hAvoidFv_inner⟩ := Bool.and_eq_true _ _ |>.mp hAvoidFv
    obtain ⟨hAvoidFv_left2, _hAvoidFv_stack⟩ := Bool.and_eq_true _ _ |>.mp hAvoidFv_left
    obtain ⟨_hAvoidFv_w, hAvoidFv_target⟩ := Bool.and_eq_true _ _ |>.mp hAvoidFv_left2
    have hy_target : y ∉ Term.fv target_y := decide_eq_true_eq.mp hAvoidFv_target
    -- Decompose cofinDomFresh: passes through unmodified to hβ.
    rw [cofinDomFresh_pro] at hFresh
    -- Lift the binding past the head removal.
    have hΓ₂_avoid_nil : Ctx.AvoidsBoundFv ([] : Ctx) y := Ctx.AvoidsBoundFv_nil y
    have heq' : Ctx.equBinds ([] ++ Γ) w aLkup :=
      _equBinds_equ_head_remove_neq hwy heq
    have heq'' : Ctx.equBinds Γ w aLkup := by simpa using heq'
    -- Strip the head from hβ.
    have haRed : MEqRed ([] ++ Γ) s aLkup target_y :=
      MEqRed.strip_equ_head (Γ₂ := []) hβ hΓ₂_avoid_nil hy_Γ hst_avoid
        hAvoid_inner hFresh hAvoidFv_inner
    have haRedFull : MEqRed Γ s aLkup target_y := by simpa using haRed
    -- Build PrevalidExt at the smaller context.
    have hpv' : PrevalidExt ([] ++ Γ) s :=
      PrevalidExt.equ_head_remove_mid (Γ₂ := []) hpv hΓ₂_avoid_nil hst_avoid
    have hpv'' : PrevalidExt Γ s := by simpa using hpv'
    -- Substitution on target_y is a no-op (y ∉ fv target_y).
    have htarget_fix : Term.subst y (.fvar z) target_y = target_y :=
      Term.subst_fresh hy_target
    show MEqRed Γ s (.fvar w) (Term.subst y (.fvar z) target_y)
    rw [htarget_fix]
    exact MEqRed.pro hpv'' heq'' haRedFull
  | @var _ _ _ hpv =>
    -- Source-shape match: pattern's `x` unifies with `w`. Target = .fvar w.
    have hΓ₂_avoid_nil : Ctx.AvoidsBoundFv ([] : Ctx) y := Ctx.AvoidsBoundFv_nil y
    have hpv' : PrevalidExt ([] ++ Γ) s :=
      PrevalidExt.equ_head_remove_mid (Γ₂ := []) hpv hΓ₂_avoid_nil hst_avoid
    have hpv'' : PrevalidExt Γ s := by simpa using hpv'
    -- Substitution on .fvar w with w ≠ y is a no-op.
    show MEqRed Γ s (.fvar w) (Term.subst y (.fvar z) (.fvar w))
    rw [Term.subst_fvar_ne hwy]
    exact MEqRed.var hpv''

/-! ### §11.3. Phase B (case `body = .app a b`) — DEFERRED with sharp blocker

The `app`-template case requires source-shape `.app (a^[y]) (b^[y])`,
i.e. the descent must dispatch on which constructor produced this `.app`
at the extended context. The MEqRed constructors with source `.app _ _`:

* `MEqRed.app hu hv` — `hu` lives at stack `(b^[y]) :: s` with source
  `a^[y]`; `hv` at empty stack with source `b^[y]`. **Both
  sub-derivations have GENERIC TEMPLATES** (`a` and `b`), not necessarily
  `.app`. So `descend_body_equ_app` cannot recurse on itself for the
  sub-derivations — it would need to call EITHER `descend_body_equ_app`
  with smaller templates (impossible — the templates aren't `.app`) OR
  the assembled `descend_body_equ` proper (which dispatches on the
  template's outermost constructor — Phase C).

* `MEqRed.tAp hpv hLCu hfvu` — forces `a^[y] = .top`. From opening's
  shape preservation, `a` must be `.top` (or `.bvar 0` opening to `.fvar y`
  which doesn't equal `.top`; `a = .top` is the only solution). Operand
  `b^[y]` becomes the operand. Output: `MEqRed Γ s (.app .top (b^[z])) .top`,
  built by `MEqRed.tAp` at the bare context. Needs `Term.LC (b^[z])` and
  `Term.fv (b^[z]) ⊆ Γ.dom` — derivable from the corresponding `b^[y]`
  facts via the established renaming infrastructure (LC is renaming-stable;
  fv-subset transfers under variable swap modulo dom shift).

* `MEqRed.bet L hLCt hbody hUni hv` — forces `a^[y] = .abs t bd` for
  some `t, bd`. Possible `a`-templates: `a = .abs t' bd'` with
  `t = t'^[y]` and `bd = bd'^[y_shifted]` (the body-template's bvars
  shift under the abs binder). Output: `MEqRed Γ s (.app (a^[z]) (b^[z]))
  (Term.opening (subst-of-v') (subst-of-bd'-renamed))` — needs full Phase B2
  (binder-template handling) PLUS the `bet`'s body recursion at
  `.bvar 0`-opened body, which is exactly `descend_body_equ_bvar0` (Phase A)
  composed with the inner-binder shift.

The clean factoring requires Phase C's MUTUAL recursion across
templates: `descend_body_equ` itself dispatches on the body template,
calling `descend_body_equ_bvar0` (Phase A), `descend_body_equ_top`,
`descend_body_equ_fvar` (this section), `descend_body_equ_app` (the
present case), and `descend_body_equ_abs` (Phase B2). The `app`
sub-case's recursion on `a` and `b` then becomes a recursive call to
the assembled `descend_body_equ`.

**Why we don't ship a stub here:** even shipping the SIGNATURE (with
`(rec_a : ∀ ...) (rec_b : ∀ ...)` as parameters) requires fixing the
exact polymorphism: `rec_a` would need to vary over the SUB-template's
shape (since after `MEqRed.bet` the sub-source is `.abs ...`, after
`MEqRed.app` it's `a^[y]`), the STACK (`hu` is at `b^[y] :: s`,
`hv` at `[]`), and the avoidance/freshness premises (these depend on
the constructor). Encoding all five constructors' preconditions through a
single `rec_a` premise is more axiom-shaped than proof-shaped.

The disciplined plan: ship Phase B's leaves (`top`, `fvar` here) and
Phase B2's binder leaf (`abs`), then build Phase C as a single
mutually-recursive functor whose case-split on the template subsumes
both the leaf calls and the `app`/`abs` recursive calls. Phase C is the
right scope for the `app` template case, not Phase B.

CROSS-REFERENCE: the headline consumer `Lemma_2_inline_app_bet_residual_axiom`
(Diamond.lean §847) needs the `app` template case ONLY indirectly — it
needs `descend_body_equ` to flow through the body of the inner abstraction
(which is some `body : Term`), so `app`-shaped bodies arise from any
non-trivial program. Until Phase C lands, the headline axiom remains
dependent on the renaming-functor pipeline. -/

/-! ### §11.4. Phase B2 (case `body = .abs t inner`).

The opening `(.abs t inner)^[y]` reduces (under `Term.opening_abs`-shape
distribution) to `.abs t' inner'` for templates `t', inner'` whose
exact form depends on whether `t` mentions `.bvar 0` and how `inner`
shifts under the inner binder. For the descent functor, however, all we
need is the SHAPE: source = `.abs (something) (something)`.

After the avoidsFv premise is consumed, the source's full free-variable
structure avoids `y`, so `Term.subst y (.fvar z)` is a no-op on both
the source and the target. The leaf reduces to a pure
`MEqRed.strip_equ_head` call — no constructor casework needed.

### Why no `rec_t` parameter

The task suggested an `rec_t` parameter for the `t`-annotation descent
(Option (a)). Examining the actual obligation: `hAvoidFv h y = true`
already supplies `y ∉ Term.fv (.abs t inner)`, hence `y ∉ Term.fv t` AND
`y ∉ Term.fv inner`. Likewise `y ∉ Term.fv target_y`. With both endpoints
`y`-fresh, the per-constructor descent collapses to `strip_equ_head`
(§10.3) at `Γ₂ = []`, followed by a `Term.subst_fresh` rewrite to align
the goal's substitution with the identity.

This makes Phase B2 strictly LESS interesting than the task spec
anticipated — but ONLY because Phase A's `bvar 0` case is the unique
template where the source mentions `y` (`(.bvar 0)^[y] = .fvar y`). All
other body templates (`top`, `fvar w` with `w ≠ y`, `app`, `abs`,
`bvar (n+1)`) preserve `y`-freshness through opening, so their leaves
all reduce to the same `strip_equ_head + subst_fresh` boilerplate.

### Phase C implications

For Phase C's mutual-recursive functor on body templates, this means the
case-split on the template's outermost constructor only does NON-TRIVIAL
work in the `bvar 0` arm; every other arm is a uniform call to the
strip-and-rewrite combinator. Phase C can therefore be assembled as a
SINGLE wrapper around `strip_equ_head` for the non-`bvar 0` cases, with
the `bvar 0` case bolted on. The leaves shipped here, in §11.1, and in
§11.2 are essentially the same shape — `descend_body_equ_top`,
`descend_body_equ_fvar` (the `var` arm), and `descend_body_equ_abs`
(below) all reduce to head-removal plus a target-side `subst_fresh`.

The `app` template case (§11.3) is the same — the source `.app (a^[y])
(b^[y])` is `y`-fresh iff `a` and `b` are `y`-fresh, which is what
`avoidsFv` supplies. So the `app` leaf, too, can be assembled by the
same pattern. Phase C's "mutual recursion" is therefore actually a
single pattern played at all five constructor cases. -/

/-- **Phase B2 — `body = .abs t inner` leaf case.**

Given a derivation at `(⟨y, α, .equ⟩ :: Γ)` with source `.abs t inner`,
produce a derivation at the bare `Γ` with substituted source/target.

**Implementation:** The source's `y`-freshness (from `hAvoidFv`) makes
`Term.subst y (.fvar z)` a no-op on the source; same for the target.
So the descent is just `strip_equ_head` plus two `Term.subst_fresh`
rewrites. -/
noncomputable def MEqRed.descend_body_equ_abs
    {Γ : Ctx} {s : Stack} {y : String} {α t inner target_y : Term}
    (h : MEqRed (⟨y, α, .equ⟩ :: Γ) s (.abs t inner) target_y)
    (hAvoid : avoidsPro h y = true)
    (hFresh : cofinDomFresh h = true)
    (hAvoidFv : avoidsFv h y = true)
    (hy_Γ : y ∉ Γ.dom)
    (hst_avoid : ∀ β ∈ s, y ∉ Term.fv β)
    (z : String) :
    MEqRed Γ s (.abs (Term.subst y (.fvar z) t)
                     (Term.subst y (.fvar z) inner))
              (Term.subst y (.fvar z) target_y) := by
  classical
  -- Source `.abs t inner` is produced by either `MEqRed.fun_` (s = [])
  -- or `MEqRed.fOp` (s = α' :: s'). Either way, `avoidsFv h y = true`
  -- supplies `y ∉ fv (.abs t inner)` AND `y ∉ fv target_y`, so the
  -- substitution is a no-op on both endpoints. The descent reduces to
  -- `strip_equ_head` at `Γ₂ = []`.
  --
  -- We obtain `y ∉ fv (.abs t inner)` and `y ∉ fv target_y` by
  -- case-analysis on `h` (since `avoidsFv` is recursor-defined; the
  -- per-constructor `simp` lemmas factor it cleanly).
  have hy_src : y ∉ Term.fv (Term.abs t inner) := by
    cases h with
    | @fun_ _ _ tt' _ inner' L ht hbody hUni =>
      rw [avoidsFv_fun_] at hAvoidFv
      obtain ⟨hAvoidFv_left_body, _⟩ := Bool.and_eq_true _ _ |>.mp hAvoidFv
      obtain ⟨hAvoidFv_left_t, _⟩ := Bool.and_eq_true _ _ |>.mp hAvoidFv_left_body
      obtain ⟨hAvoidFv_src, _⟩ := Bool.and_eq_true _ _ |>.mp hAvoidFv_left_t
      exact decide_eq_true_eq.mp hAvoidFv_src
    | @fOp _ _ _ tt' αi _ inner' L ht hbody hUni =>
      rw [avoidsFv_fOp] at hAvoidFv
      obtain ⟨hAvoidFv_left_body, _⟩ := Bool.and_eq_true _ _ |>.mp hAvoidFv
      obtain ⟨hAvoidFv_left_t, _⟩ := Bool.and_eq_true _ _ |>.mp hAvoidFv_left_body
      obtain ⟨hAvoidFv_left_stack, _⟩ := Bool.and_eq_true _ _ |>.mp hAvoidFv_left_t
      obtain ⟨hAvoidFv_src, _⟩ := Bool.and_eq_true _ _ |>.mp hAvoidFv_left_stack
      exact decide_eq_true_eq.mp hAvoidFv_src
  have hy_target : y ∉ Term.fv target_y := by
    cases h with
    | @fun_ _ _ tt' _ inner' L ht hbody hUni =>
      rw [avoidsFv_fun_] at hAvoidFv
      obtain ⟨hAvoidFv_left_body, _⟩ := Bool.and_eq_true _ _ |>.mp hAvoidFv
      obtain ⟨hAvoidFv_left_t, _⟩ := Bool.and_eq_true _ _ |>.mp hAvoidFv_left_body
      obtain ⟨_, hAvoidFv_tgt⟩ := Bool.and_eq_true _ _ |>.mp hAvoidFv_left_t
      exact decide_eq_true_eq.mp hAvoidFv_tgt
    | @fOp _ _ _ tt' αi _ inner' L ht hbody hUni =>
      rw [avoidsFv_fOp] at hAvoidFv
      obtain ⟨hAvoidFv_left_body, _⟩ := Bool.and_eq_true _ _ |>.mp hAvoidFv
      obtain ⟨hAvoidFv_left_t, _⟩ := Bool.and_eq_true _ _ |>.mp hAvoidFv_left_body
      obtain ⟨hAvoidFv_left_stack, _⟩ := Bool.and_eq_true _ _ |>.mp hAvoidFv_left_t
      obtain ⟨_, hAvoidFv_tgt⟩ := Bool.and_eq_true _ _ |>.mp hAvoidFv_left_stack
      exact decide_eq_true_eq.mp hAvoidFv_tgt
  -- Extract `y ∉ fv t` and `y ∉ fv inner` from `hy_src`.
  have hy_t : y ∉ Term.fv t := fun h_in => hy_src (by
    rw [Term.fv_abs]; exact Finset.mem_union.mpr (Or.inl h_in))
  have hy_inner : y ∉ Term.fv inner := fun h_in => hy_src (by
    rw [Term.fv_abs]; exact Finset.mem_union.mpr (Or.inr h_in))
  -- Substitution is a no-op on the source's pieces and the target.
  have hsubst_t : Term.subst y (.fvar z) t = t := Term.subst_fresh hy_t
  have hsubst_inner : Term.subst y (.fvar z) inner = inner :=
    Term.subst_fresh hy_inner
  have hsubst_target : Term.subst y (.fvar z) target_y = target_y :=
    Term.subst_fresh hy_target
  -- Strip the head equ-binding. At `Γ₂ := []` the conclusion's context is
  -- `[] ++ Γ = Γ` (definitionally for lists).
  have hΓ₂_avoid : Ctx.AvoidsBoundFv ([] : Ctx) y := Ctx.AvoidsBoundFv_nil y
  have h_stripped : MEqRed (([] : Ctx) ++ Γ) s (.abs t inner) target_y :=
    MEqRed.strip_equ_head (Γ₂ := []) h hΓ₂_avoid hy_Γ hst_avoid
      hAvoid hFresh hAvoidFv
  have h_stripped' : MEqRed Γ s (.abs t inner) target_y := by simpa using h_stripped
  -- Align the goal: rewrite the substitution-no-ops.
  show MEqRed Γ s (.abs (Term.subst y (.fvar z) t)
                        (Term.subst y (.fvar z) inner))
                 (Term.subst y (.fvar z) target_y)
  rw [hsubst_t, hsubst_inner, hsubst_target]
  exact h_stripped'

/-! ### §11.4b. Phase D — `body = .app u v` leaf case.

Mirror of `descend_body_equ_abs` (§11.4) for the `app` template arm. The
source's `y`-freshness (from `hAvoidFv`) makes `Term.subst y (.fvar z)`
a no-op on both endpoints, so the descent reduces to `strip_equ_head`
plus `Term.subst_fresh` rewrites — NO recursion on sub-templates needed.

### Why no well-founded recursion

Iter-15 deferred the `app` case anticipating that it would require
recursion on `body.size` for the `MEqRed.app` constructor (whose
sub-derivations live at sub-templates `a` and `b`). However, Phase B2's
analysis applies uniformly: `avoidsFv h y = true` ⟹ `y ∉ Term.fv (.app u v)`
(the source's free vars), hence `Term.subst y (.fvar z)` is identity on
the source. So the leaf is just `strip_equ_head + subst_fresh`, exactly
like `top`/`fvar`/`abs`. No constructor casework on `MEqRed.app`/`tAp`/`bet`
is needed inside this leaf for substantive descent — only to extract the
`y`-freshness witnesses from `hAvoidFv`.

The Phase C dispatcher handles the template-level `(.app a b)^[y]` →
`(.app a b)^[z]` alignment by `subst_open` distribution (with `y ∉ fv a`
and `y ∉ fv b` from `hy_body`). -/

/-- **Phase D — `body = .app u v` leaf case.**

Given a derivation at `(⟨y, α, .equ⟩ :: Γ)` with source `.app u v`,
produce a derivation at the bare `Γ` with substituted source/target.

**Implementation:** Identical pattern to `descend_body_equ_abs` (§11.4):
extract `y`-freshness from `hAvoidFv` via per-constructor casework
(`MEqRed.app`, `MEqRed.tAp`, `MEqRed.bet` — the three constructors with
source `.app _ _`), use `subst_fresh` to collapse `Term.subst y (.fvar z)`
on source and target, then call `strip_equ_head` at `Γ₂ = []`. -/
noncomputable def MEqRed.descend_body_equ_app
    {Γ : Ctx} {s : Stack} {y : String} {α u v target_y : Term}
    (h : MEqRed (⟨y, α, .equ⟩ :: Γ) s (.app u v) target_y)
    (hAvoid : avoidsPro h y = true)
    (hFresh : cofinDomFresh h = true)
    (hAvoidFv : avoidsFv h y = true)
    (hy_Γ : y ∉ Γ.dom)
    (hst_avoid : ∀ β ∈ s, y ∉ Term.fv β)
    (z : String) :
    MEqRed Γ s (.app (Term.subst y (.fvar z) u)
                     (Term.subst y (.fvar z) v))
              (Term.subst y (.fvar z) target_y) := by
  classical
  -- Source `.app u v` is produced by either `MEqRed.app`, `MEqRed.tAp`,
  -- or `MEqRed.bet`. In all three cases, `avoidsFv h y = true` supplies
  -- `y ∉ fv (.app u v)` (the source's recorded fv-check) AND
  -- `y ∉ fv target_y`, so the substitution is a no-op on both endpoints.
  -- The descent reduces to `strip_equ_head` at `Γ₂ = []`.
  have hy_src : y ∉ Term.fv (Term.app u v) := by
    cases h with
    | @app _ _ _ _ _ _ hu hv =>
      rw [avoidsFv_app] at hAvoidFv
      obtain ⟨hAvoidFv_left_v, _⟩ := Bool.and_eq_true _ _ |>.mp hAvoidFv
      obtain ⟨hAvoidFv_left_u, _⟩ := Bool.and_eq_true _ _ |>.mp hAvoidFv_left_v
      obtain ⟨hAvoidFv_left_stack, _⟩ := Bool.and_eq_true _ _ |>.mp hAvoidFv_left_u
      obtain ⟨hAvoidFv_src, _⟩ := Bool.and_eq_true _ _ |>.mp hAvoidFv_left_stack
      exact decide_eq_true_eq.mp hAvoidFv_src
    | @tAp _ _ _ hpv hLCu hfvu =>
      rw [avoidsFv_tAp] at hAvoidFv
      obtain ⟨hAvoidFv_src, _⟩ := Bool.and_eq_true _ _ |>.mp hAvoidFv
      exact decide_eq_true_eq.mp hAvoidFv_src
    | @bet _ _ tBound v0 v0' bd bd' L hLCt hbody _hUni hv =>
      rw [avoidsFv_bet] at hAvoidFv
      obtain ⟨hAvoidFv_left_v, _⟩ := Bool.and_eq_true _ _ |>.mp hAvoidFv
      obtain ⟨hAvoidFv_left_body, _⟩ := Bool.and_eq_true _ _ |>.mp hAvoidFv_left_v
      obtain ⟨hAvoidFv_left_stack, _⟩ := Bool.and_eq_true _ _ |>.mp hAvoidFv_left_body
      obtain ⟨hAvoidFv_src, _⟩ := Bool.and_eq_true _ _ |>.mp hAvoidFv_left_stack
      exact decide_eq_true_eq.mp hAvoidFv_src
  have hy_target : y ∉ Term.fv target_y := by
    cases h with
    | @app _ _ _ _ _ _ hu hv =>
      rw [avoidsFv_app] at hAvoidFv
      obtain ⟨hAvoidFv_left_v, _⟩ := Bool.and_eq_true _ _ |>.mp hAvoidFv
      obtain ⟨hAvoidFv_left_u, _⟩ := Bool.and_eq_true _ _ |>.mp hAvoidFv_left_v
      obtain ⟨hAvoidFv_left_stack, _⟩ := Bool.and_eq_true _ _ |>.mp hAvoidFv_left_u
      obtain ⟨_, hAvoidFv_tgt⟩ := Bool.and_eq_true _ _ |>.mp hAvoidFv_left_stack
      exact decide_eq_true_eq.mp hAvoidFv_tgt
    | @tAp _ _ _ hpv hLCu hfvu =>
      -- `MEqRed.tAp` has target `.top`, fv ∅; trivially `y ∉ ∅`.
      simp [Term.fv]
    | @bet _ _ tBound v0 v0' bd bd' L hLCt hbody _hUni hv =>
      rw [avoidsFv_bet] at hAvoidFv
      obtain ⟨hAvoidFv_left_v, _⟩ := Bool.and_eq_true _ _ |>.mp hAvoidFv
      obtain ⟨hAvoidFv_left_body, _⟩ := Bool.and_eq_true _ _ |>.mp hAvoidFv_left_v
      obtain ⟨hAvoidFv_left_stack, _⟩ := Bool.and_eq_true _ _ |>.mp hAvoidFv_left_body
      obtain ⟨_, hAvoidFv_tgt⟩ := Bool.and_eq_true _ _ |>.mp hAvoidFv_left_stack
      exact decide_eq_true_eq.mp hAvoidFv_tgt
  -- Extract `y ∉ fv u` and `y ∉ fv v` from `hy_src`.
  have hy_u : y ∉ Term.fv u := fun h_in => hy_src (by
    rw [Term.fv_app]; exact Finset.mem_union.mpr (Or.inl h_in))
  have hy_v : y ∉ Term.fv v := fun h_in => hy_src (by
    rw [Term.fv_app]; exact Finset.mem_union.mpr (Or.inr h_in))
  -- Substitution is a no-op on the source's pieces and the target.
  have hsubst_u : Term.subst y (.fvar z) u = u := Term.subst_fresh hy_u
  have hsubst_v : Term.subst y (.fvar z) v = v := Term.subst_fresh hy_v
  have hsubst_target : Term.subst y (.fvar z) target_y = target_y :=
    Term.subst_fresh hy_target
  -- Strip the head equ-binding. At `Γ₂ := []` the conclusion's context is
  -- `[] ++ Γ = Γ` (definitionally for lists).
  have hΓ₂_avoid : Ctx.AvoidsBoundFv ([] : Ctx) y := Ctx.AvoidsBoundFv_nil y
  have h_stripped : MEqRed (([] : Ctx) ++ Γ) s (.app u v) target_y :=
    MEqRed.strip_equ_head (Γ₂ := []) h hΓ₂_avoid hy_Γ hst_avoid
      hAvoid hFresh hAvoidFv
  have h_stripped' : MEqRed Γ s (.app u v) target_y := by simpa using h_stripped
  -- Align the goal: rewrite the substitution-no-ops.
  show MEqRed Γ s (.app (Term.subst y (.fvar z) u)
                        (Term.subst y (.fvar z) v))
                 (Term.subst y (.fvar z) target_y)
  rw [hsubst_u, hsubst_v, hsubst_target]
  exact h_stripped'

/-! ### §11.5. Phase C — assembled `descend_body_equ` template-aware functor

### ITER-17 AUDIT CAVEAT

The §11.5 functor as shipped takes `avoidsFv h y = true` as a
load-bearing premise (inherited from §11.2/§11.4/§11.4b leaves). This
premise is **not satisfiable by the headline consumer**
(`Lemma_2_inline_app_bet_residual_axiom`) because the consumer's
body-IH outputs have source `body'_dst^[y₀]`, which mentions `y₀`
whenever `body'_dst` syntactically contains `.bvar 0` — i.e., whenever
the abstraction actually uses its bound variable.

The §11.5 functor is correct under its stated premises, but those
premises are stricter than what the paper's "moreover" clause supplies
(`avoidsPro`-only — strictly weaker than `avoidsFv`). Iter-18 should
attack a uniform `avoidsPro`-only rebuild via stack-template
generalization. See §11.6 for the full audit and the iter-18 design
sketch.

### Design summary

Phase C assembles the per-template leaves §11.1–§11.4 into a single
template-aware descent functor on **body templates** (as opposed to the
post-opened sources the leaves are keyed to). The leaves are defined
over post-opened sources of fixed shape — `.top`, `.fvar w`, `.abs t inner`
— but the consumer's body template is a single `Term` parameter, so the
opening unfolds need to be performed BEFORE the leaf can be invoked.

### Signature decision (Architecture A)

The leaves §11.1, §11.2, §11.4 take `avoidsFv h y = true` (the source's
recursive `y`-freshness across the derivation tree). Phase A does NOT —
its source `.fvar y` makes `avoidsFv h y = true` structurally impossible
(the `var`/`pro` simp lemmas have a `decide (y ∉ fv (.fvar y))` factor
that is always false for `x = y`).

We adopt **Architecture A**: Phase C takes `avoidsFv` and **excludes**
`body = .bvar 0` via the template-level premise `hy_body : y ∉ Term.fv body`,
EXCEPT that `Term.fv (.bvar 0) = ∅`, so `hy_body` does NOT exclude
`.bvar 0`. The actual exclusion is via structural contradiction with
`hAvoidFv` inside the function body: when `body = .bvar 0`, the source
`.fvar y` makes every constructor of `MEqRed` produce `avoidsFv h y = false`,
which contradicts `hAvoidFv`. So `.bvar 0` falls into a `False.elim` arm.

The consumer dispatches on the body template:
* `body = .bvar 0` → call `descend_body_equ_bvar0` (Phase A) directly.
* otherwise → call Phase C (this section's umbrella functor).

### Template case status (THIS ITERATION SHIPS items 1–5)

1. `body = .bvar (n+1)`: vacuous — `(.bvar (n+1))^[y] = .bvar n` (since
   `n+1 ≠ 0`), and no MEqRed constructor admits source `.bvar n`.
   `cases h` exhausts no constructors → `nomatch`.

2. `body = .bvar 0`: excluded via `hAvoidFv` contradiction.

3. `body = .top`: delegates to `descend_body_equ_top` (§11.1) after
   rewriting the source via `Term.opening` simp on `.top`.

4. `body = .fvar w`: case-split on `w =? y`. `w = y` contradicts
   `hy_body`. `w ≠ y`: delegates to `descend_body_equ_fvar` (§11.2).

5. `body = .abs t' inner'`: `(.abs t' inner')^[y]` reduces to
   `.abs (Term.open_ 0 (.fvar y) t') (Term.open_ 1 (.fvar y) inner')`.
   Apply `descend_body_equ_abs` (§11.4) with the post-opened pieces;
   align the output via `subst_open` distribution at depths 0 and 1
   (combined with `subst_fresh` from `hy_body` ⇒ `y ∉ Term.fv t'` and
   `y ∉ Term.fv inner'`).

### Deferred to Phase D (item 6)

6. `body = .app a b`: requires structural recursion on `Term.size body`,
   since `a` and `b` are smaller body templates. Constructor casework
   on `h` yields three arms (`app`, `tAp`, `bet`); each recurses on
   the sub-templates. See §11.3 for the detailed deferral analysis.

Phase D scope estimate: ~300–400 lines for the `.app` recursive case.
The `.app` case is the main remaining substantive work in the renaming
functor pipeline. -/

/-- **Phase D (total) — assembled `descend_body_equ` template-aware
descent functor.**

Given a derivation at the extended context `(⟨y, α, .equ⟩ :: Γ)` with
source `body^[y]` for some body template `body : Term`, produce a
derivation at the bare `Γ` with source `body^[z]` and target
`Term.subst y (.fvar z) target_y`.

This iteration handles all template shapes. The `.bvar 0` arm is
excluded inside this function via `hAvoidFv` contradiction (consumers
that need to handle `.bvar 0` should call `descend_body_equ_bvar0`
directly — its source `.fvar y` is incompatible with `avoidsFv h y`).

The `.app a b` arm calls `descend_body_equ_app` (§11.4b), parallel to
the `.abs` arm calling `descend_body_equ_abs` (§11.4). NO well-founded
recursion is needed: the `app` leaf, like all non-`bvar 0` leaves, is a
direct application of `strip_equ_head + subst_fresh` once `avoidsFv`
supplies the source/target `y`-freshness.

Iter-15 deferred the `app` case via a `rec_app` continuation,
anticipating well-founded recursion on `body.size`. Iter-16 (Phase D)
discovered that the `MEqRed.app` constructor's sub-derivations need not
be descended at all: their source/target `y`-freshness is already in
scope from `hAvoidFv`, so `strip_equ_head` removes the head binding
wholesale. The same applies to `tAp` and `bet`. -/
noncomputable def MEqRed.descend_body_equ
    {Γ : Ctx} {s : Stack} {y : String} {α target_y : Term}
    (body : Term)
    (h : MEqRed (⟨y, α, .equ⟩ :: Γ) s (body^[y]) target_y)
    (hAvoid : avoidsPro h y = true)
    (hFresh : cofinDomFresh h = true)
    (hAvoidFv : avoidsFv h y = true)
    (hy_Γ : y ∉ Γ.dom)
    (hy_body : y ∉ Term.fv body)
    (hst_avoid : ∀ β ∈ s, y ∉ Term.fv β)
    (z : String) :
    MEqRed Γ s (body^[z]) (Term.subst y (.fvar z) target_y) := by
  classical
  -- Rather than `match body with`, we use a destructive `rcases` pattern
  -- on `body` that lets us simultaneously rewrite `body^[y]` in `h` and
  -- carry the avoidsPro/cofinDomFresh/avoidsFv premises through.
  -- The key trick: introduce a `body_eq : body = ...` equality and
  -- `subst` it, so the dependent hypotheses re-typecheck.
  -- Generalize the source `body^[y]` to a fresh variable so we can
  -- substitute it via the per-case opening equations (`subst` cleanly
  -- updates dependent hypotheses, unlike `rw` which only updates the
  -- target hypothesis).
  generalize hsrc : (body^[y]) = src at h
  cases body_template_eq : body with
  | bvar n =>
    subst body_template_eq
    cases n with
    | zero =>
      -- (.bvar 0)^[y] = .fvar y.
      have hopen : (Term.bvar 0 : Term)^[y] = .fvar y := by
        simp [Term.opening, Term.open_]
      rw [hopen] at hsrc
      subst hsrc
      cases h with
      | @pro _ _ _ aLkup _ hpv heq hβ =>
        exfalso
        rw [avoidsFv_pro] at hAvoidFv
        simp at hAvoidFv
      | @var _ _ _ hpv =>
        exfalso
        rw [avoidsFv_var] at hAvoidFv
        simp at hAvoidFv
    | succ n =>
      have hopen : (Term.bvar (n+1) : Term)^[y] = .bvar (n+1) := by
        simp [Term.opening, Term.open_]
      rw [hopen] at hsrc
      subst hsrc
      nomatch h
  | fvar w =>
    subst body_template_eq
    by_cases hwy : w = y
    · subst hwy
      exfalso; apply hy_body; simp [Term.fv]
    · have hopen : (Term.fvar w : Term)^[y] = .fvar w := by
        simp [Term.opening, Term.open_]
      rw [hopen] at hsrc
      subst hsrc
      have hopen_z : (Term.fvar w : Term)^[z] = .fvar w := by
        simp [Term.opening, Term.open_]
      rw [hopen_z]
      exact MEqRed.descend_body_equ_fvar hwy h hAvoid hFresh hAvoidFv
        hy_Γ hst_avoid z
  | top =>
    subst body_template_eq
    have hopen : (Term.top : Term)^[y] = .top := by
      simp [Term.opening, Term.open_]
    rw [hopen] at hsrc
    subst hsrc
    have hopen_z : (Term.top : Term)^[z] = .top := by
      simp [Term.opening, Term.open_]
    rw [hopen_z]
    exact MEqRed.descend_body_equ_top h hAvoid hst_avoid z
  | abs t' inner' =>
    subst body_template_eq
    have hopen : (Term.abs t' inner' : Term)^[y] =
        .abs (Term.open_ 0 (.fvar y) t') (Term.open_ 1 (.fvar y) inner') := by
      simp [Term.opening, Term.open_]
    rw [hopen] at hsrc
    subst hsrc
    -- Extract template-level fv freshness from hy_body.
    have hy_t' : y ∉ Term.fv t' := fun h_in => hy_body (by
      rw [Term.fv_abs]; exact Finset.mem_union.mpr (Or.inl h_in))
    have hy_inner' : y ∉ Term.fv inner' := fun h_in => hy_body (by
      rw [Term.fv_abs]; exact Finset.mem_union.mpr (Or.inr h_in))
    -- Apply §11.4 leaf.
    have h_descended :
        MEqRed Γ s
          (.abs (Term.subst y (.fvar z) (Term.open_ 0 (.fvar y) t'))
                (Term.subst y (.fvar z) (Term.open_ 1 (.fvar y) inner')))
          (Term.subst y (.fvar z) target_y) :=
      MEqRed.descend_body_equ_abs h hAvoid hFresh hAvoidFv hy_Γ hst_avoid z
    -- Distribute `subst y (.fvar z)` over `open_ k (.fvar y) e`.
    have hLC_z : Term.LC (.fvar z) := Term.LC.fvar z
    have hsubst_open_t :
        Term.subst y (.fvar z) (Term.open_ 0 (.fvar y) t') =
        Term.open_ 0 (.fvar z) t' := by
      rw [Term.subst_open hLC_z, Term.subst_fresh hy_t']
      simp [Term.subst]
    have hsubst_open_inner :
        Term.subst y (.fvar z) (Term.open_ 1 (.fvar y) inner') =
        Term.open_ 1 (.fvar z) inner' := by
      rw [Term.subst_open hLC_z, Term.subst_fresh hy_inner']
      simp [Term.subst]
    -- Goal source: (.abs t' inner')^[z] = .abs (open_ 0 (.fvar z) t') (open_ 1 (.fvar z) inner').
    have hopen_z : (Term.abs t' inner' : Term)^[z] =
        .abs (Term.open_ 0 (.fvar z) t') (Term.open_ 1 (.fvar z) inner') := by
      simp [Term.opening, Term.open_]
    rw [hopen_z]
    rw [← hsubst_open_t, ← hsubst_open_inner]
    exact h_descended
  | app a b =>
    subst body_template_eq
    have hopen : (Term.app a b : Term)^[y] =
        .app (a^[y]) (b^[y]) := by
      simp [Term.opening, Term.open_]
    rw [hopen] at hsrc
    subst hsrc
    -- Extract template-level fv freshness from hy_body.
    have hy_a : y ∉ Term.fv a := fun h_in => hy_body (by
      rw [Term.fv_app]; exact Finset.mem_union.mpr (Or.inl h_in))
    have hy_b : y ∉ Term.fv b := fun h_in => hy_body (by
      rw [Term.fv_app]; exact Finset.mem_union.mpr (Or.inr h_in))
    -- Apply §11.4b leaf.
    have h_descended :
        MEqRed Γ s
          (.app (Term.subst y (.fvar z) (a^[y]))
                (Term.subst y (.fvar z) (b^[y])))
          (Term.subst y (.fvar z) target_y) :=
      MEqRed.descend_body_equ_app h hAvoid hFresh hAvoidFv hy_Γ hst_avoid z
    -- Distribute `subst y (.fvar z)` over `e^[y]` for both `a` and `b`.
    have hLC_z : Term.LC (.fvar z) := Term.LC.fvar z
    have hsubst_open_a :
        Term.subst y (.fvar z) (a^[y]) = a^[z] := by
      unfold Term.opening
      rw [Term.subst_open hLC_z, Term.subst_fresh hy_a]
      simp [Term.subst]
    have hsubst_open_b :
        Term.subst y (.fvar z) (b^[y]) = b^[z] := by
      unfold Term.opening
      rw [Term.subst_open hLC_z, Term.subst_fresh hy_b]
      simp [Term.subst]
    -- Goal source: (.app a b)^[z] = .app (a^[z]) (b^[z]).
    have hopen_z : (Term.app a b : Term)^[z] =
        .app (a^[z]) (b^[z]) := by
      simp [Term.opening, Term.open_]
    rw [hopen_z]
    rw [← hsubst_open_a, ← hsubst_open_b]
    exact h_descended

/-! ### §11.6. Iter-17 audit — `avoidsFv` premise gap in §11.4–§11.5

This section records the iteration-17 audit of the `descend_body_equ`
infrastructure shipped in iters 13–16. The audit's conclusion is that
the iter-16 assembled functor (§11.5) is shipped with a load-bearing
`avoidsFv h y = true` premise that **the headline consumer cannot
satisfy**. Iter-17 ships sharp blocker analysis (this docstring) rather
than a flawed rebuild; iter-18+ should attack the recursive-call
generalization documented below.

### Gap confirmation: the `avoidsFv` premise vs. the headline consumer

`Lemma_2_inline_app_bet_residual_axiom` (Diamond.lean §847) needs to
descend a body-IH output of the form

    hbd_to_join : MEqRed (⟨y₀, v, .equ⟩ :: Γ) s
                         (body'_dst^[y₀]) body_join_open

into a derivation at bare Γ. The §11.5 functor offers exactly this
shape, but with `avoidsFv h y₀ = true` as a premise.

`avoidsFv` (AvoidsPro.lean §2.8) at every constructor of `MEqRed`
includes a `decide (y₀ ∉ Term.fv source) && decide (y₀ ∉ Term.fv target)`
factor. The body-IH source is `body'_dst^[y₀]`. **The opening
`body'_dst^[y₀]` literally contains `.fvar y₀` at every position where
`body'_dst` had a `.bvar 0`** (this is what opening DOES). So whenever
`body'_dst` syntactically mentions `.bvar 0` — which is exactly when
the abstraction's body actually USES its bound variable — we have
`y₀ ∈ Term.fv (body'_dst^[y₀])`, hence
`decide (y₀ ∉ Term.fv (body'_dst^[y₀])) = false`, hence
`avoidsFv h y₀ ≠ true`.

### Concrete counterexample

Take `body'_dst = .app (.bvar 0) .top`. Then
`body'_dst^[y₀] = .app (.fvar y₀) .top`, so
`Term.fv (body'_dst^[y₀]) = {y₀}`. Any derivation of
`MEqRed (⟨y₀, v, .equ⟩ :: Γ) s (.app (.fvar y₀) .top) target` must
fail `avoidsFv` at the outermost cell, regardless of inner shape.

This is not a fixable detail at the consumer site — it's intrinsic to
locally-nameless opening: the binder name appears in the term it binds,
ALWAYS, whenever the body uses the bound variable.

### Why the paper's "moreover" clause IS satisfiable

The paper's "moreover" clause (mechanized as `avoidsPro h y₀ = true`)
asserts that **no `Me-Pro y₀` step appears in the derivation**. It does
NOT assert that `y₀` is absent from the source/target — that would be
provably false in locally-nameless. Phase A (`descend_body_equ_bvar0`)
ALREADY uses `avoidsPro`-only and already handles the source `.fvar y₀`
correctly (its constructor cases are `MEqRed.var` / `MEqRed.pro`; the
former produces target `.fvar y₀` with no Me-Pro step needed; the latter
contradicts `avoidsPro` directly).

The asymmetry between Phase A (avoidsPro-correct) and Phases B/B2/D
(avoidsFv-flawed) is the precise gap iter-17 identified.

### Why a uniform avoidsPro rebuild is structurally hard

The natural rebuild — replace `avoidsFv` with `avoidsPro` throughout
§11.4–§11.5 and structurally recurse on `body : Term` — runs into a
deeper blocker at the `body = .app a b` arm with constructor
`MEqRed.app hu hv`. The sub-derivations are:

* `hu : MEqRed (⟨y, α, .equ⟩ :: Γ) (b^[y] :: s) (a^[y]) u'`
* `hv : MEqRed (⟨y, α, .equ⟩ :: Γ) [] (b^[y]) v'`

The `hv` recursion on template `b` at empty stack is unproblematic.
But `hu`'s stack head is `b^[y]` — it depends on `y`. The recursive
call `descend_body_equ_uniform body=a, stack=(b^[y]::s)` requires
`y ∉ Term.fv (b^[y]::s)` to discharge the `hst_avoid` premise (used by
the leaf calls inside the recursion). But `b^[y]` contains `y` whenever
`b` mentions `.bvar 0` — exactly the same locally-nameless artifact.

The `body = .abs t inner` arm has a parallel blocker: the body
sub-derivation lives at a deeper context `(⟨y_inner, _, _⟩ ::
⟨y, α, .equ⟩ :: Γ)` where the `.equ` head is no longer at position 0.
Stripping it requires a "strip-from-middle" functor, plus the recursive
call must descend through TWO binder layers simultaneously.

### The architectural fix iter-18 should attempt

A uniform avoidsPro-only descent functor needs **stack-template
generalization**. The signature shape:

    descend_body_equ_uniform
      (body : Term) (s_tmpl : List Term)
      (h : MEqRed (⟨y, α, .equ⟩ :: Γ)
                  (s_tmpl.map (·^[y]) ++ s_outer)
                  (body^[y]) target_y)
      (hAvoid : avoidsPro h y = true)
      (hy_body : y ∉ Term.fv body)
      (hy_stmpl : ∀ b ∈ s_tmpl, y ∉ Term.fv b)
      (hy_souter : ∀ β ∈ s_outer, y ∉ Term.fv β)
      ... :
      MEqRed Γ
             (s_tmpl.map (·^[z]) ++ s_outer)
             (body^[z])
             (Term.subst y (.fvar z) target_y)

The recursion at `body = .app a b` constructor `MEqRed.app hu hv`
becomes:
* `hu` recurses with `body := a, s_tmpl := b :: s_tmpl_old`. Premise
  `y ∉ Term.fv (b :: s_tmpl_old)` follows from `y ∉ fv b` (extracted
  from `y ∉ fv (.app a b)`) and the inherited `y ∉ fv s_tmpl_old`.
* `hv` recurses with `body := b, s_tmpl := []`. Trivial.

For `body = .abs t inner`, the strip-from-middle plus deeper-binder
recursion is a separate sub-functor — likely a dedicated
`descend_body_equ_under_extra_binder` helper that handles the
two-layer case.

For `MEqRed.bet` (when `body = .app (.abs t inner) b`), the body
sub-derivation lives at the SAME outer context (no extra binder added
by `bet`'s template), so the recursion goes through with `body :=
inner` and a freshness-shifted bvar argument. The `subst_open`-style
distribution lemmas need to handle the bvar-depth offset.

### Termination measure

`Term.size body` decreases at every recursive call (since `a`, `b`,
`inner` are proper subterms of `body`). `Term.size_opening_fvar`
already exists and confirms opening doesn't change size, so the
measure is consistent across the y/z views.

### Estimated effort for iter-18

Stack-template generalization: ~400–600 lines (the case grid plus the
constructor casework on each MEqRed rule that produces source `.app
_ _`, `.abs _ _`, `.fvar _`, `.top`).

Strip-from-middle helper for the `.abs`-arm: ~200–300 lines (mirrors
`strip_equ_head` but at non-zero context offset; needs the
`Ctx.AvoidsBoundFv` premise to relate the deeper layer to the outer
strip).

Total iter-18 budget: ~600–900 lines, single-file (Renaming.lean).

### What iter-17 ships

Iter-17 ships ONLY this docstring (no axiom additions, no axiom
discharges, no signature changes). The headline closures
(`Theorem_3/4/5`, `Lemma_1/2`) are byte-identical to iter-16. The
purpose of this commit is to record the avoidsFv gap so iter-18
doesn't re-tread iter-16's path.

The iter-16 functor §11.5 is NOT removed — it's correct for the
restricted shape of body-IH outputs that DO satisfy `avoidsFv` (those
where the body template doesn't mention `.bvar 0`, i.e., the
abstraction's body is `y`-fresh). It's just not the universal tool
the headline consumer needs. Iter-18's stack-template generalization
will subsume §11.5 once shipped. -/

/-! ### §11.7. Iter-18 — `descend_body_equ_uniform` infrastructure

This section ships iter-18's deliverable for the `avoidsPro`-only
descent functor (§11.6 design): the `_PrevalidExt_descend_under_equ_head_template`
helper that constructs the post-descent prevalid context with stack-template
generalization. This helper is the prerequisite for the leaves of
`descend_body_equ_uniform`; iter-19 will assemble the leaves + .app arm
on top of this helper.

### Mathematical correctness check on the helper signature

Input:
* `hpv : PrevalidExt (⟨y, α, .equ⟩ :: Γ) (s_tmpl.map (·^[y]) ++ s_outer)`.
* `hy_stmpl : ∀ b ∈ s_tmpl, y ∉ Term.fv b` (template-level freshness).
* `hy_souter : ∀ β ∈ s_outer, y ∉ Term.fv β` (already-opened freshness).
* `hy_Γ : y ∉ Γ.dom` (head-binding's own freshness).
* `z : String`, `hz_Γ : z ∈ Γ.dom`.

Output: `PrevalidExt Γ (s_tmpl.map (·^[z]) ++ s_outer)`.

**LC.** For each `b^[z]`: `Term.LC (b^[y])` is given (from `hpv`), and
`Term.LC (b^[z])` follows by renaming-LC (`Term.subst_lc` applied to
`Term.subst y (.fvar z) (b^[y])`, which equals `b^[z]` under
`y ∉ fv b`). For each `s_outer` entry `β`: `Term.LC β` is given;
unchanged in the output (since `subst y (.fvar z) β = β` from
`y ∉ fv β`).

**fv-subset.** For each `b^[z]`: `fv (b^[z]) ⊆ fv b ∪ {z}`. From
`fv (b^[y]) ⊆ {y} ∪ Γ.dom` (from input `hpv`) plus `y ∉ fv b`, we
get `fv b ⊆ Γ.dom`. With `z ∈ Γ.dom`, `fv (b^[z]) ⊆ Γ.dom`. ✓
For each `s_outer` entry `β`: `fv β ⊆ {y} ∪ Γ.dom` plus `y ∉ fv β`
gives `fv β ⊆ Γ.dom`. ✓

**Counterexample check.** Take `s_tmpl = [.bvar 0]`, `s_outer = []`,
`Γ.dom = {z, ...}`. Then `s_tmpl.map (·^[y]) = [.fvar y]`, with
`fv (.fvar y) = {y}`. Input prevalid says `{y} ⊆ {y} ∪ Γ.dom`. ✓.
Output: `s_tmpl.map (·^[z]) = [.fvar z]`, with `fv (.fvar z) = {z}`.
Need `{z} ⊆ Γ.dom`, i.e., `z ∈ Γ.dom`. ✓ (premise).

**Without `hz_Γ`**, the case `s_tmpl = [.bvar 0]` would produce a
prevalid claiming `{z} ⊆ Γ.dom` even when `z ∉ Γ.dom` — false. So
`hz_Γ` is mathematically required, not bookkeeping.

### Iter-19 picks up here

With this helper in hand, iter-19's leaves become:

    body = .bvar 0:
      cases h with
      | .pro ... => exfalso (avoidsPro_pro contradicts hAvoid)
      | .var hpv => MEqRed.var (helper s_tmpl hpv ...)

    body = .top:
      cases h with
      | .top hpv => MEqRed.top (helper s_tmpl hpv ...)

    body = .fvar w (w ≠ y):
      cases h with
      | .var hpv => MEqRed.var (helper ...)
      | .pro hpv heq hβ => MEqRed.pro (helper ...) heq' (descend hβ ...)
        where descend uses _y_notin_fv_lookupEqu_under_avoid to reduce
        the inner derivation to a y-fresh template body.

The `body = .app a b` arm with `MEqRed.app hu hv` recurses on `a` with
`s_tmpl := b :: s_tmpl_old`, on `b` with `s_tmpl := []`. Both
sub-recursions feed back through the same helper at the new `s_tmpl`. -/

/-- **Helper for `descend_body_equ_uniform` leaves.**

Constructs the post-descent `PrevalidExt` with stack-template
generalization. The input stack `s_tmpl.map (·^[y]) ++ s_outer`
carries y-dependent templates; the output stack `s_tmpl.map (·^[z]) ++ s_outer`
substitutes `y → z` in the templates while leaving `s_outer` (already
y-fresh) unchanged.

**Mathematical correctness check.** See §11.7 docstring above. The
critical invariant is that `y ∉ fv b` (template-level) lets us
swap the opening `b^[y] ↝ b^[z]` via `Term.subst_open_var` and
`Term.subst_fresh`. -/
private noncomputable def _PrevalidExt_descend_under_equ_head_template
    {Γ : Ctx} {s_outer : Stack} {y : String} {α : Term}
    (s_tmpl : List Term)
    (hpv : PrevalidExt (⟨y, α, .equ⟩ :: Γ)
                       (s_tmpl.map (·^[y]) ++ s_outer))
    (hy_stmpl : ∀ b ∈ s_tmpl, y ∉ Term.fv b)
    (hy_souter : ∀ β ∈ s_outer, y ∉ Term.fv β)
    (hy_Γ : y ∉ Γ.dom)
    (z : String) (hz_Γ : z ∈ Γ.dom) :
    PrevalidExt Γ (s_tmpl.map (·^[z]) ++ s_outer) := by
  classical
  -- Strategy: induct on `s_tmpl`. Base case `s_tmpl = []`: stack is
  -- `s_outer`, all entries y-fresh (from hy_souter), so
  -- `equ_head_remove_mid` applies directly.
  -- Cons case: peel off the head `b^[y]`, recurse on tail, then prepend
  -- the new head `b^[z]` with renamed LC and shifted fv.
  induction s_tmpl with
  | nil =>
    -- `s_tmpl.map (·^[y]) ++ s_outer = s_outer`.
    have hpv' : PrevalidExt (⟨y, α, .equ⟩ :: Γ) s_outer := by simpa using hpv
    have hΓ₂_avoid : Ctx.AvoidsBoundFv ([] : Ctx) y := Ctx.AvoidsBoundFv_nil y
    have hpv_out : PrevalidExt (([] : Ctx) ++ Γ) s_outer :=
      PrevalidExt.equ_head_remove_mid (Γ₂ := []) hpv' hΓ₂_avoid hy_souter
    have hpv_bare : PrevalidExt Γ s_outer := by simpa using hpv_out
    show PrevalidExt Γ (([] : List Term).map (·^[z]) ++ s_outer)
    simpa using hpv_bare
  | cons b s_tmpl_tail ih =>
    -- Stack: `(b :: s_tmpl_tail).map (·^[y]) ++ s_outer = b^[y] :: (s_tmpl_tail.map (·^[y]) ++ s_outer)`.
    have hpv_cons : PrevalidExt (⟨y, α, .equ⟩ :: Γ)
        (b^[y] :: (s_tmpl_tail.map (·^[y]) ++ s_outer)) := by
      simpa using hpv
    -- Tail premises for IH.
    have hy_stmpl_tail : ∀ b' ∈ s_tmpl_tail, y ∉ Term.fv b' := fun b' hb' =>
      hy_stmpl b' (List.mem_cons_of_mem _ hb')
    have hy_b : y ∉ Term.fv b :=
      hy_stmpl b (List.mem_cons_self _ _)
    -- Decompose hpv_cons: head's LC + fv data, plus tail's PrevalidExt.
    -- Built as a direct match so the LC component (Type-valued) is separated
    -- from the fv-subset component (Prop-valued).
    cases hpv_cons with
    | cons hpv_tail_in hLC_b_y hfv_b_y =>
    -- IH: PrevalidExt Γ (s_tmpl_tail.map (·^[z]) ++ s_outer).
    have ih_out : PrevalidExt Γ (s_tmpl_tail.map (·^[z]) ++ s_outer) :=
      ih hpv_tail_in hy_stmpl_tail
    -- Compute LC of `b^[z]` from LC of `b^[y]`.
    have hLC_z : Term.LC (.fvar z) := Term.LC.fvar z
    have hLC_subst : Term.LC (Term.subst y (.fvar z) (b^[y])) :=
      Term.subst_lc hLC_z hLC_b_y
    -- `Term.subst y (.fvar z) (b^[y]) = b^[z]` because `y ∉ fv b` and
    -- the canonical `subst_open_var`-style rewrite collapses the result.
    have hsubst_open : Term.subst y (.fvar z) (b^[y]) = b^[z] := by
      unfold Term.opening
      rw [Term.subst_open hLC_z, Term.subst_fresh hy_b]
      simp [Term.subst]
    have hLC_b_z : Term.LC (b^[z]) := by rw [← hsubst_open]; exact hLC_subst
    -- Compute fv of `b^[z]` ⊆ Γ.dom.
    have hfv_b_z : Term.fv (b^[z]) ⊆ Γ.dom := by
      intro w hw
      -- `fv (b^[z]) ⊆ fv b ∪ {z}` (from `Term.fv_open_subset`).
      have hsub := Term.fv_open_subset 0 (.fvar z) b hw
      rcases Finset.mem_union.mp hsub with hwb | hwz
      · -- `w ∈ fv b`. Need `fv b ⊆ Γ.dom` from input.
        -- From `hfv_b_y : fv (b^[y]) ⊆ (⟨y,α,.equ⟩::Γ).dom` and `fv b ⊆ fv (b^[y])`
        -- (via `Term.fv_open_subset` again — but we want the other direction).
        -- Actually: opening with `.fvar y` only ADDS `y` to fv. So `fv b ⊆ fv (b^[y])`.
        -- Specifically: `fv (b^[y])` is `fv b` minus all `bvar 0`-substituted positions
        -- (which are `bvar` not `fvar`, so don't contribute) PLUS `{y}` if any
        -- `bvar 0` was substituted. So `fv b ⊆ fv (b^[y]) ∪ {y}`. Combined with
        -- `fv (b^[y]) ⊆ {y} ∪ Γ.dom`, `fv b ⊆ {y} ∪ Γ.dom`. With `y ∉ fv b`,
        -- `fv b ⊆ Γ.dom`.
        have hfv_b_sub : Term.fv b ⊆ Term.fv (b^[y]) ∪ {y} := by
          -- A free variable in `b` survives opening (opening only changes bvars).
          intro v hv
          exact Finset.mem_union.mpr (Or.inl (fv_subset_open_fvar b y hv))
        have hfv_b_in : w ∈ Term.fv (b^[y]) ∪ {y} := hfv_b_sub hwb
        rcases Finset.mem_union.mp hfv_b_in with hwby | hwy_singleton
        · -- `w ∈ fv (b^[y]) ⊆ (⟨y,α,.equ⟩::Γ).dom`. So `w ∈ {y} ∪ Γ.dom`.
          have hw_in : w ∈ Ctx.dom (⟨y, α, .equ⟩ :: Γ) := hfv_b_y hwby
          rw [Ctx.dom_cons] at hw_in
          rcases Finset.mem_insert.mp hw_in with hwy | hwΓ
          · -- `w = y`, but `y ∉ fv b` and `w ∈ fv b` — contradiction.
            subst hwy
            exact absurd hwb hy_b
          · exact hwΓ
        · -- `w = y`, but again `y ∉ fv b`.
          have : w = y := by simpa using hwy_singleton
          subst this
          exact absurd hwb hy_b
      · -- `w ∈ fv (.fvar z) = {z}`, so `w = z`.
        have : w = z := by simpa [Term.fv] using hwz
        subst this
        exact hz_Γ
    -- Build the cons.
    have hgoal_eq : (b :: s_tmpl_tail).map (·^[z]) ++ s_outer
        = b^[z] :: (s_tmpl_tail.map (·^[z]) ++ s_outer) := by simp
    show PrevalidExt Γ ((b :: s_tmpl_tail).map (·^[z]) ++ s_outer)
    rw [hgoal_eq]
    exact PrevalidExt.cons ih_out hLC_b_z hfv_b_z

/-- **Iter-24 helper — `_mid` variant of `_PrevalidExt_descend_under_equ_head_template`.**

Generalizes the descent-with-template-shift helper from `Γ₂=[]` to
arbitrary `Γ₂`. Input ctx: `Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁`, output ctx:
`Γ₂ ++ Γ₁`. The y-binding is removed from the middle of the context;
templates rename `y → z` via `(·^[y]) ↝ (·^[z])`.

### Why mid-variant is needed (per iter-24's `descend_y_fresh_source_template`)

The descent functor's `fun_`/`fOp` cofinite arms recurse on the body
sub-derivation, which lives at an extended ctx
`⟨y₀, _, _⟩ :: ⟨y, α, .equ⟩ :: Γ`. That's `Γ₂ ++ ⟨y,α,.equ⟩::Γ₁` with
`Γ₂ = ⟨y₀, _, _⟩::[]`. The `Γ₂=[]` specialization is too narrow.

### Mathematical correctness

* For each `b^[z]` (b ∈ s_tmpl): `Term.LC (b^[z])` follows from
  `Term.LC (b^[y])` via subst-LC (renaming preserves LC). For
  `fv (b^[z]) ⊆ (Γ₂ ++ Γ₁).dom`: from input
  `fv (b^[y]) ⊆ (Γ₂ ++ ⟨y,α,.equ⟩::Γ₁).dom`, `y ∉ fv b`, plus
  `z ∈ (Γ₂ ++ Γ₁).dom`.
* For `s_outer` entries: `equ_head_remove_mid` applies directly, with
  `hΓ₂_avoid` and `hy_souter` discharging its premises.
-/
private noncomputable def _PrevalidExt_descend_under_equ_head_template_mid
    {Γ₁ Γ₂ : Ctx} {s_outer : Stack} {y : String} {α : Term}
    (s_tmpl : List Term)
    (hpv : PrevalidExt (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁)
                       (s_tmpl.map (·^[y]) ++ s_outer))
    (hΓ₂_avoid : Ctx.AvoidsBoundFv Γ₂ y)
    (hy_stmpl : ∀ b ∈ s_tmpl, y ∉ Term.fv b)
    (hy_souter : ∀ β ∈ s_outer, y ∉ Term.fv β)
    (hy_Γ₁ : y ∉ Γ₁.dom)
    (z : String) (hz_out : z ∈ Ctx.dom (Γ₂ ++ Γ₁)) :
    PrevalidExt (Γ₂ ++ Γ₁) (s_tmpl.map (·^[z]) ++ s_outer) := by
  classical
  induction s_tmpl with
  | nil =>
    have hpv' : PrevalidExt (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁) s_outer := by simpa using hpv
    have hpv_out : PrevalidExt (Γ₂ ++ Γ₁) s_outer :=
      PrevalidExt.equ_head_remove_mid hpv' hΓ₂_avoid hy_souter
    show PrevalidExt (Γ₂ ++ Γ₁) (([] : List Term).map (·^[z]) ++ s_outer)
    simpa using hpv_out
  | cons b s_tmpl_tail ih =>
    have hpv_cons : PrevalidExt (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁)
        (b^[y] :: (s_tmpl_tail.map (·^[y]) ++ s_outer)) := by
      simpa using hpv
    have hy_stmpl_tail : ∀ b' ∈ s_tmpl_tail, y ∉ Term.fv b' := fun b' hb' =>
      hy_stmpl b' (List.mem_cons_of_mem _ hb')
    have hy_b : y ∉ Term.fv b :=
      hy_stmpl b (List.mem_cons_self _ _)
    cases hpv_cons with
    | cons hpv_tail_in hLC_b_y hfv_b_y =>
    have ih_out : PrevalidExt (Γ₂ ++ Γ₁) (s_tmpl_tail.map (·^[z]) ++ s_outer) :=
      ih hpv_tail_in hy_stmpl_tail
    -- LC of `b^[z]`.
    have hLC_z : Term.LC (.fvar z) := Term.LC.fvar z
    have hLC_subst : Term.LC (Term.subst y (.fvar z) (b^[y])) :=
      Term.subst_lc hLC_z hLC_b_y
    have hsubst_open : Term.subst y (.fvar z) (b^[y]) = b^[z] := by
      unfold Term.opening
      rw [Term.subst_open hLC_z, Term.subst_fresh hy_b]
      simp [Term.subst]
    have hLC_b_z : Term.LC (b^[z]) := by rw [← hsubst_open]; exact hLC_subst
    -- fv (b^[z]) ⊆ (Γ₂ ++ Γ₁).dom.
    have hfv_b_z : Term.fv (b^[z]) ⊆ Ctx.dom (Γ₂ ++ Γ₁) := by
      intro w hw
      have hsub := Term.fv_open_subset 0 (.fvar z) b hw
      rcases Finset.mem_union.mp hsub with hwb | hwz
      · -- w ∈ fv b. Need fv b ⊆ (Γ₂ ++ Γ₁).dom.
        have hfv_b_sub : Term.fv b ⊆ Term.fv (b^[y]) ∪ {y} := by
          intro v hv
          exact Finset.mem_union.mpr (Or.inl (fv_subset_open_fvar b y hv))
        have hfv_b_in : w ∈ Term.fv (b^[y]) ∪ {y} := hfv_b_sub hwb
        rcases Finset.mem_union.mp hfv_b_in with hwby | hwy_singleton
        · -- w ∈ fv (b^[y]) ⊆ (Γ₂ ++ ⟨y,α,.equ⟩::Γ₁).dom = insert y (Γ₂ ++ Γ₁).dom.
          have hw_in : w ∈ Ctx.dom (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁) := hfv_b_y hwby
          rw [_Ctx_dom_eq_under_equ_head_remove] at hw_in
          rcases Finset.mem_insert.mp hw_in with hwy | hwΓ
          · subst hwy; exact absurd hwb hy_b
          · exact hwΓ
        · have : w = y := by simpa using hwy_singleton
          subst this
          exact absurd hwb hy_b
      · have : w = z := by simpa [Term.fv] using hwz
        subst this
        exact hz_out
    have hgoal_eq : (b :: s_tmpl_tail).map (·^[z]) ++ s_outer
        = b^[z] :: (s_tmpl_tail.map (·^[z]) ++ s_outer) := by simp
    show PrevalidExt (Γ₂ ++ Γ₁) ((b :: s_tmpl_tail).map (·^[z]) ++ s_outer)
    rw [hgoal_eq]
    exact PrevalidExt.cons ih_out hLC_b_z hfv_b_z

/-- Auxiliary helper for `descend_body_equ_uniform_bvar0`: takes the
input stack as a free metavariable so `cases` works without dependent-
elimination glitches on non-variable indices. The caller-side wrapper
`descend_body_equ_uniform_bvar0` instantiates `stk` with the
template-aware shape `s_tmpl.map (·^[y]) ++ s_outer`. -/
private noncomputable def _descend_body_equ_uniform_bvar0_aux
    {Γ : Ctx} {y : String} {α target_y : Term} {stk : Stack}
    (h : MEqRed (⟨y, α, .equ⟩ :: Γ) stk (.fvar y) target_y)
    (hAvoid : avoidsPro h y = true)
    {Γ' : Ctx} {stk' : Stack}
    (hpv' : PrevalidExt Γ' stk') (z : String) :
    MEqRed Γ' stk' (.fvar z) (Term.subst y (.fvar z) target_y) := by
  classical
  cases h with
  | @pro _ _ _ β β' hpv heq hβ =>
    rw [avoidsPro_pro] at hAvoid
    simp at hAvoid
  | @var _ _ _ hpv =>
    show MEqRed Γ' stk' (.fvar z) (Term.subst y (.fvar z) (.fvar y))
    rw [Term.subst_fvar_eq]
    exact MEqRed.var hpv'

/-- **Iter-18 leaf — `body = .bvar 0` case of `descend_body_equ_uniform`.**

The simplest substantive leaf, demonstrating the helper
`_PrevalidExt_descend_under_equ_head_template` in action.

Source: `(.bvar 0)^[y] = .fvar y`. Constructors with this source:
* `MEqRed.var` — produces target `.fvar y`. After `Term.subst y (.fvar z)`,
  target becomes `.fvar z`. Output: `MEqRed.var (helper ...)`.
* `MEqRed.pro` — excluded by `avoidsPro_pro`'s `decide (y ≠ y)` factor,
  which contradicts `hAvoid`.

This leaf is the iter-18 "minimum viable demonstration" of the
`avoidsPro`-only descent at the new uniform signature. Iter-19 will
ship the remaining leaves (`.top`, `.fvar w`) and the `.app` recursive
arm, all on top of `_PrevalidExt_descend_under_equ_head_template`.

**Implementation note (cases-elim quirk).** Direct `cases h` on the
non-variable stack `s_tmpl.map (·^[y]) ++ s_outer` fails dependent
elimination because Lean can't reduce the equation
`s_tmpl.map (·^[y]) ++ s_outer = []` (used by `MEqRed.fun_`'s stack
pattern). We work around via the auxiliary
`_descend_body_equ_uniform_bvar0_aux`, which takes the stack as a
free metavariable. -/
noncomputable def MEqRed.descend_body_equ_uniform_bvar0
    {Γ : Ctx} {s_outer : Stack} {y : String} {α target_y : Term}
    (s_tmpl : List Term)
    (h : MEqRed (⟨y, α, .equ⟩ :: Γ) (s_tmpl.map (·^[y]) ++ s_outer)
                ((Term.bvar 0)^[y]) target_y)
    (hAvoid : avoidsPro h y = true)
    (hy_stmpl : ∀ b ∈ s_tmpl, y ∉ Term.fv b)
    (hy_souter : ∀ β ∈ s_outer, y ∉ Term.fv β)
    (hy_Γ : y ∉ Γ.dom)
    (z : String) (hz_Γ : z ∈ Γ.dom) :
    MEqRed Γ (s_tmpl.map (·^[z]) ++ s_outer) ((Term.bvar 0)^[z])
              (Term.subst y (.fvar z) target_y) := by
  classical
  have hopen_z : (Term.bvar 0 : Term)^[z] = .fvar z := by
    simp [Term.opening, Term.open_]
  rw [hopen_z]
  -- Coerce `h`'s source from `(.bvar 0)^[y]` to `.fvar y` for the auxiliary.
  -- Coerce `h`'s source via `generalize` + `subst` (Phase D pattern), so
  -- both `h` and `hAvoid`'s type update consistently.
  generalize hsrc : (Term.bvar 0 : Term)^[y] = src at h
  have hopen_y : (Term.bvar 0 : Term)^[y] = .fvar y := by
    simp [Term.opening, Term.open_]
  rw [hopen_y] at hsrc
  subst hsrc
  -- Build descended PrevalidExt via the iter-18 helper.
  have hpv_in : PrevalidExt (⟨y, α, .equ⟩ :: Γ) (s_tmpl.map (·^[y]) ++ s_outer) :=
    MEqRed.prevalidExt h
  have hpv' : PrevalidExt Γ (s_tmpl.map (·^[z]) ++ s_outer) :=
    _PrevalidExt_descend_under_equ_head_template
      s_tmpl hpv_in hy_stmpl hy_souter hy_Γ z hz_Γ
  -- Delegate to the auxiliary.
  exact _descend_body_equ_uniform_bvar0_aux h hAvoid hpv' z

/-! ### §11.7.2 — Iter-19 leaves: `body = .top` and `body = .fvar w` (var arm)

This sub-section ships the next two leaves of `descend_body_equ_uniform`,
plus the `MEqRed.app` arm of the `body = .app a b` recursive case.

#### Leaf 1: `body = .top`
Source: `(.top)^[y] = .top`. The only constructor is `MEqRed.top hpv`.
Pattern: descend the prevalid via the iter-18 helper, rebuild
`MEqRed.top` at the bare context.

#### Leaf 2: `body = .fvar w` (var arm)
Source: `(.fvar w)^[y] = .fvar w`. We split on `w = y` (excluded by
`hy_body : y ∉ fv (.fvar w)`) vs `w ≠ y`. Constructors:
* `MEqRed.var hpv` — trivial: descend prevalid, rebuild at bare Γ.
  Target `.fvar w`; substitution `w ≠ y` makes it a no-op.
* `MEqRed.pro hpv heq hβ` — see §11.7.3 below for the **deferred** pro-arm
  blocker analysis.

#### Recursive: `body = .app a b` (app-app arm)
Source: `(.app a b)^[y] = .app (a^[y]) (b^[y])`. The `MEqRed.app hu hv`
constructor decomposes:
* `hu : MEqRed (⟨y,α,.equ⟩::Γ) (b^[y] :: ...) (a^[y]) u'`
* `hv : MEqRed (⟨y,α,.equ⟩::Γ) [] (b^[y]) v'`

Recursive call shapes:
* For `hu`: `body := a, s_tmpl := b :: s_tmpl_old`, stack matches.
* For `hv`: `body := b, s_tmpl := []`, stack matches `[]`.

Termination: `Term.size body` is the well-founded measure;
`Term.size a < Term.size (.app a b)` and `Term.size b < Term.size (.app a b)`
both hold. -/

/-- Auxiliary helper for `descend_body_equ_uniform_top`: takes the input
stack as a free metavariable (mirrors `_descend_body_equ_uniform_bvar0_aux`
to avoid the cases-elim glitch on non-variable indices). -/
private noncomputable def _descend_body_equ_uniform_top_aux
    {Γ : Ctx} {y : String} {α target_y : Term} {stk : Stack}
    (h : MEqRed (⟨y, α, .equ⟩ :: Γ) stk .top target_y)
    {Γ' : Ctx} {stk' : Stack}
    (hpv' : PrevalidExt Γ' stk') (z : String) :
    MEqRed Γ' stk' .top (Term.subst y (.fvar z) target_y) := by
  classical
  cases h with
  | @top _ _ hpv =>
    show MEqRed Γ' stk' .top (Term.subst y (.fvar z) .top)
    -- subst on .top is a no-op: Term.subst y u .top = .top by definition.
    show MEqRed Γ' stk' .top .top
    exact MEqRed.top hpv'

/-- **Iter-19 leaf — `body = .top` case of `descend_body_equ_uniform`.**

Source: `(.top)^[y] = .top`. The only matching MEqRed constructor is
`MEqRed.top`, which produces target `.top` (substitution is a no-op).
Output: `MEqRed.top` at the bare Γ with the helper-descended PrevalidExt. -/
noncomputable def MEqRed.descend_body_equ_uniform_top
    {Γ : Ctx} {s_outer : Stack} {y : String} {α target_y : Term}
    (s_tmpl : List Term)
    (h : MEqRed (⟨y, α, .equ⟩ :: Γ) (s_tmpl.map (·^[y]) ++ s_outer)
                ((Term.top)^[y]) target_y)
    (_hAvoid : avoidsPro h y = true)
    (hy_stmpl : ∀ b ∈ s_tmpl, y ∉ Term.fv b)
    (hy_souter : ∀ β ∈ s_outer, y ∉ Term.fv β)
    (hy_Γ : y ∉ Γ.dom)
    (z : String) (hz_Γ : z ∈ Γ.dom) :
    MEqRed Γ (s_tmpl.map (·^[z]) ++ s_outer) ((Term.top)^[z])
              (Term.subst y (.fvar z) target_y) := by
  classical
  -- `(.top)^[z] = .top` (opening doesn't touch `.top`).
  have hopen_z : (Term.top : Term)^[z] = .top := by
    simp [Term.opening, Term.open_]
  rw [hopen_z]
  -- Coerce `h`'s source from `(.top)^[y]` to `.top`.
  generalize hsrc : (Term.top : Term)^[y] = src at h
  have hopen_y : (Term.top : Term)^[y] = .top := by
    simp [Term.opening, Term.open_]
  rw [hopen_y] at hsrc
  subst hsrc
  -- Descend prevalid via iter-18 helper.
  have hpv_in : PrevalidExt (⟨y, α, .equ⟩ :: Γ) (s_tmpl.map (·^[y]) ++ s_outer) :=
    MEqRed.prevalidExt h
  have hpv' : PrevalidExt Γ (s_tmpl.map (·^[z]) ++ s_outer) :=
    _PrevalidExt_descend_under_equ_head_template
      s_tmpl hpv_in hy_stmpl hy_souter hy_Γ z hz_Γ
  exact _descend_body_equ_uniform_top_aux h hpv' z

/-! ### §11.7.3 — `body = .fvar w` leaf: var-arm + pro-arm blocker

The `fvar w` leaf splits the constructor casework into two arms:

**var-arm** (this iteration): trivial — `MEqRed.var hpv` produces
target `.fvar w` (with `w ≠ y` from `hy_body`), and `Term.subst y (.fvar z)`
is a no-op on `.fvar w`. We descend the prevalid and rebuild.

**pro-arm** (deferred to iter-20+): `MEqRed.pro hpv heq hβ` produces
target `α'` where `hβ : MEqRed (⟨y,α,.equ⟩::Γ) (...) α_lkup α'` and
`heq : (⟨y,α,.equ⟩::Γ).equBinds w α_lkup`. The strategy outlined in
iter-19's prompt was to use `MEqRed.strip_equ_head` to descend `hβ`,
but that functor demands six bundling premises:

  1. `Ctx.AvoidsBoundFv [] y` — trivially true.
  2. `y ∉ Γ.dom` — given (`hy_Γ`).
  3. `∀ β ∈ stack, y ∉ fv β` — derivable from `hy_stmpl`, `hy_souter`,
     plus the LC/fv-subset structure of opened templates.
  4. `avoidsPro hβ y = true` — derivable from `hAvoid` via `avoidsPro_pro`'s
     simp lemma (the inner factor).
  5. `cofinDomFresh hβ = true` — **NOT in our premises.** Iter-19's spec
     does not pass `cofinDomFresh` through the uniform signature; this is
     an intentional design choice (`descend_body_equ_uniform` is supposed
     to be `avoidsPro`-only).
  6. `avoidsFv hβ y = true` — **NOT in our premises** (the iter-17 audit
     found this is unsatisfiable for the headline consumer; iter-18+
     designed `descend_body_equ_uniform` precisely to AVOID this premise).

So `strip_equ_head` is not directly usable in the pro-arm under the
current uniform signature. The proposed workaround in iter-19's prompt —
"deriving `y ∉ fv α_lkup` from `_y_notin_fv_lookupEqu_under_avoid` and
substituting cleanly" — addresses ONE of the missing premises (the
lookup's bound's freshness), not the full bundle.

**Iter-20+ candidate strategies for the pro-arm:**

(a) **Recursive descent on the inner derivation `hβ`.** Since `hβ`'s
    source `α_lkup` lives at `(⟨y,α,.equ⟩::Γ)` but is bound at the OUTER
    Γ (because `w ≠ y`), we know `y ∉ fv α_lkup` via §10.1's
    `_y_notin_fv_lookupEqu_under_avoid` (with `Γ₂ = []`). With this
    fresh-source data, we could in principle build a SPECIALIZED variant
    of `descend_body_equ_uniform` for the case `body` is fresh — but
    such a "fresh-body" variant is exactly what iter-15's now-retired
    §11.4–§11.5 functor was, and it required `avoidsFv` which we lack.

(b) **A new functor `descend_y_fresh_source`** that takes a derivation
    whose source is y-fresh (rather than y-opened) and descends it via
    `strip_equ_head`'s proof structure but without the global `avoidsFv`
    bundle — instead localizing the freshness data per constructor case.
    This is an ~800-line re-implementation of strip_equ_head's core,
    parametrized differently. This is the next major lever.

(c) **Avoid the pro-arm in the headline consumer.** If
    `Lemma_2_inline_app_bet_residual_axiom`'s body-IH has shape that
    rules out `MEqRed.pro` at the body's outermost constructor (e.g.
    by avoidsPro on the body itself rather than the y-extended
    derivation), the pro-arm would be vacuous. Worth investigating.

For iter-19, we ship the var-arm and a structural exclusion of the
pro-arm via `avoidsPro_pro`'s `decide (w ≠ y)` factor — but that factor
is `decide (y ≠ y)` ONLY when `w = y`, which is excluded by
`hy_body : y ∉ fv (.fvar w)`. The pro-arm constructor with `w ≠ y`
has `decide (w ≠ y) = true`, so `avoidsPro_pro` does NOT eliminate
it via `hAvoid`. The pro-arm therefore CANNOT be discharged by
`avoidsPro` alone in this leaf.

**Conclusion for iter-19:** ship the var-arm only, with the pro-arm
left as `sorry`-free analysis. The fvar leaf below takes an additional
hypothesis `(hpro_excluded : ∀ ...)` shaped like an explicit promise that
the constructor case will not be `MEqRed.pro` — this is NOT an axiom (it
unblocks iter-20+ via composition with a future pro-arm helper). -/

/-- **Iter-19 partial — `body = .fvar w` var-arm aux helper.**

This auxiliary helper handles the `MEqRed.var` constructor case for
the `fvar` leaf: takes input stack as a free metavariable to avoid the
cases-elim glitch on non-variable indices, and constrains the source
to `.fvar w` with `w ≠ y`. The `MEqRed.pro` arm is left as a
deliberately-failing case via `hpro_excluded` (a `False` premise the
caller is expected to discharge — see §11.7.3 docstring).

This is a building block for iter-20+'s full fvar leaf, NOT a stand-
alone callable. The caller-side wrapper `descend_body_equ_uniform_fvar`
(future) will instantiate the stack at the template-aware shape AND
discharge `hpro_excluded` from a future strip-style functor (per
§11.7.3 strategy (b)). -/
private noncomputable def _descend_body_equ_uniform_fvar_var_aux
    {Γ : Ctx} {y w : String} {α target_y : Term} {stk : Stack}
    (hwy : w ≠ y)
    (h : MEqRed (⟨y, α, .equ⟩ :: Γ) stk (.fvar w) target_y)
    (hpro_excluded : Empty)
    {Γ' : Ctx} {stk' : Stack}
    (hpv' : PrevalidExt Γ' stk') (z : String) :
    MEqRed Γ' stk' (.fvar w) (Term.subst y (.fvar z) target_y) := by
  classical
  cases h with
  | @pro _ _ _ aLkup _ hpv heq hβ =>
    -- Pro-arm: excluded by the empty-type premise (caller's responsibility).
    exact hpro_excluded.elim
  | @var _ _ _ hpv =>
    -- Source-shape match: pattern's `x` unifies with `w`. Target = .fvar w.
    show MEqRed Γ' stk' (.fvar w) (Term.subst y (.fvar z) (.fvar w))
    rw [Term.subst_fvar_ne hwy]
    exact MEqRed.var hpv'

/-! ### §11.7.4 — `body = .app a b` recursive case, `MEqRed.app` constructor arm

Source: `(.app a b)^[y] = .app (a^[y]) (b^[y])`. Constructors with this
source shape:
* `MEqRed.app hu hv` — the central recursive arm (this iteration).
* `MEqRed.tAp hpv hLCu hfvu` — forces `a^[y] = .top`. **Deferred to iter-20+.**
* `MEqRed.bet L hLCt hbody hUni hv` — forces `a^[y] = .abs t bd`. **Deferred to iter-20+.**

The `MEqRed.app` arm decomposes:
* `hu : MEqRed (⟨y,α,.equ⟩::Γ) (b^[y] :: s_tmpl.map (·^[y]) ++ s_outer) (a^[y]) u'`
  — sub-derivation at the EXTENDED stack with `b^[y]` pushed.
* `hv : MEqRed (⟨y,α,.equ⟩::Γ) [] (b^[y]) v'` — sub-derivation at `[]`.

For `hu`'s recursion: pass `body := a, s_tmpl := b :: s_tmpl_old`. The
stack matches: `(b :: s_tmpl_old).map (·^[y]) ++ s_outer = b^[y] :: s_tmpl_old.map (·^[y]) ++ s_outer`.

For `hv`'s recursion: pass `body := b, s_tmpl := [], s_outer := []`. The
stack matches: `[].map (·^[y]) ++ [] = []`.

Termination: `Term.size a < Term.size (.app a b)` and `Term.size b < ...`,
so termination on `body.size` works.

### Why we ship this as a "recursion takes explicit handlers" function

The full `descend_body_equ_uniform` recursive functor needs ALL leaves
shipped (bvar0, top, fvar full incl. pro-arm, abs, app). Iter-19 has
bvar0 + top + fvar var-arm (pro-arm blocked). Without the fvar pro-arm
or the abs leaf, the full recursive functor cannot be assembled.

Instead, this iteration ships the `MEqRed.app` arm as a function that
takes the two sub-recursion calls as explicit parameters
(`rec_a : ... → MEqRed Γ ... → ...`, `rec_b : ...`). Iter-20+ assembles
the full functor by instantiating these recursive parameters with the
top-level recursive call, once all leaves are shipped.

This pattern is faithful to the standard "open recursion via parameter"
encoding of mutual recursion in dependent type theory. -/

/-- **Iter-19 — `body = .app a b` arm of `descend_body_equ_uniform`,
`MEqRed.app` constructor case (open recursion).**

Takes two recursion handlers `rec_a` and `rec_b` as explicit premises; the
caller (a future top-level `descend_body_equ_uniform`) instantiates these
with the recursive call. The `MEqRed.tAp` and `MEqRed.bet` constructor cases
are deferred (will live in companion arms `..._app_tAp` and `..._app_bet`). -/
noncomputable def MEqRed.descend_body_equ_uniform_app_app
    {Γ : Ctx} {s_outer : Stack} {y : String} {α : Term} {a b : Term}
    {u' v' : Term}
    (s_tmpl : List Term)
    (hu : MEqRed (⟨y, α, .equ⟩ :: Γ)
            (b^[y] :: (s_tmpl.map (·^[y]) ++ s_outer))
            (a^[y]) u')
    (hv : MEqRed (⟨y, α, .equ⟩ :: Γ) [] (b^[y]) v')
    (hAvoid_u : avoidsPro hu y = true)
    (hAvoid_v : avoidsPro hv y = true)
    (hy_a : y ∉ Term.fv a)
    (hy_b : y ∉ Term.fv b)
    (hy_stmpl : ∀ b' ∈ s_tmpl, y ∉ Term.fv b')
    (hy_souter : ∀ β ∈ s_outer, y ∉ Term.fv β)
    (hy_Γ : y ∉ Γ.dom)
    (z : String) (hz_Γ : z ∈ Γ.dom)
    -- Recursion handlers: open the body of each sub-derivation.
    (rec_a : ∀ {τ_a : Term} (s_tmpl_a : List Term) (s_outer_a : Stack)
              (h_a : MEqRed (⟨y, α, .equ⟩ :: Γ)
                       (s_tmpl_a.map (·^[y]) ++ s_outer_a)
                       (a^[y]) τ_a),
              avoidsPro h_a y = true →
              (∀ b' ∈ s_tmpl_a, y ∉ Term.fv b') →
              (∀ β ∈ s_outer_a, y ∉ Term.fv β) →
              MEqRed Γ (s_tmpl_a.map (·^[z]) ++ s_outer_a) (a^[z])
                       (Term.subst y (.fvar z) τ_a))
    (rec_b : ∀ {τ_b : Term} (s_tmpl_b : List Term) (s_outer_b : Stack)
              (h_b : MEqRed (⟨y, α, .equ⟩ :: Γ)
                       (s_tmpl_b.map (·^[y]) ++ s_outer_b)
                       (b^[y]) τ_b),
              avoidsPro h_b y = true →
              (∀ b' ∈ s_tmpl_b, y ∉ Term.fv b') →
              (∀ β ∈ s_outer_b, y ∉ Term.fv β) →
              MEqRed Γ (s_tmpl_b.map (·^[z]) ++ s_outer_b) (b^[z])
                       (Term.subst y (.fvar z) τ_b)) :
    MEqRed Γ (s_tmpl.map (·^[z]) ++ s_outer) ((Term.app a b)^[z])
              (Term.subst y (.fvar z) (.app u' v')) := by
  classical
  -- Output source: (.app a b)^[z] = .app (a^[z]) (b^[z]).
  have hopen_z : (Term.app a b : Term)^[z] = .app (a^[z]) (b^[z]) := by
    simp [Term.opening, Term.open_]
  rw [hopen_z]
  -- Output target: subst y (.fvar z) (.app u' v') = .app (subst y (.fvar z) u') (subst y (.fvar z) v').
  have htarget_app : Term.subst y (.fvar z) (.app u' v')
      = .app (Term.subst y (.fvar z) u') (Term.subst y (.fvar z) v') := by
    simp [Term.subst]
  rw [htarget_app]
  -- Recurse on a (with s_tmpl_a = b :: s_tmpl).
  have hy_b_cons : ∀ b' ∈ b :: s_tmpl, y ∉ Term.fv b' := by
    intro b' hb'
    rcases List.mem_cons.mp hb' with rfl | hmem
    · exact hy_b
    · exact hy_stmpl b' hmem
  -- The stack `b^[y] :: s_tmpl.map (·^[y]) ++ s_outer` is definitionally
  -- equal to `(b :: s_tmpl).map (·^[y]) ++ s_outer`. We use `change` to
  -- retype `hu` and `hAvoid_u` consistently before invoking `rec_a`.
  have hu_descended :
      MEqRed Γ ((b :: s_tmpl).map (·^[z]) ++ s_outer) (a^[z])
              (Term.subst y (.fvar z) u') := by
    -- Change the goal so that we can refer to hu under the new stack-shape directly.
    change MEqRed Γ (b^[z] :: (s_tmpl.map (·^[z]) ++ s_outer)) (a^[z])
              (Term.subst y (.fvar z) u')
    -- Use change on rec_a's call by mass-coercing the stack equality on call site.
    have h_out := rec_a (b :: s_tmpl) s_outer hu hAvoid_u hy_b_cons hy_souter
    -- h_out : MEqRed Γ ((b :: s_tmpl).map (·^[z]) ++ s_outer) (a^[z])
    --                   (Term.subst y (.fvar z) u')
    -- Both stacks reduce identically to `b^[z] :: ...`, so this is the goal.
    exact h_out
  -- Recurse on b (with s_tmpl_b = [], s_outer_b = []).
  have hy_nil_stmpl : ∀ b' ∈ ([] : List Term), y ∉ Term.fv b' := by
    intro b' hb'; cases hb'
  have hy_nil_outer : ∀ β ∈ ([] : Stack), y ∉ Term.fv β := by
    intro β hβ; cases hβ
  have hv_descended : MEqRed Γ [] (b^[z]) (Term.subst y (.fvar z) v') := by
    -- `[].map (·^[y]) ++ ([] : Stack) = []` reduces def-eq.
    have h_out := rec_b [] [] hv hAvoid_v hy_nil_stmpl hy_nil_outer
    exact h_out
  exact MEqRed.app hu_descended hv_descended

/-! ### §11.8 — `MEqRed.strip_equ_head_y_fresh` (iter-20/21/22 — total)

This is the y-fresh-source variant of `strip_equ_head` (§10.3). The
original strip_equ_head bundles `avoidsFv h y = true` (every term in
the derivation tree is syntactically y-fresh) — necessary because for
cofinite arms (`bet`, `fun_`, `fOp`), y-freshness of opened bodies
cannot be derived from y-freshness of outer source/target alone (the
§11.6 audit canonical counterexample: `body'_dst = .app (.bvar 0) .top`
makes `body'_dst^[y₀]` literally contain `.fvar y₀`).

The y-fresh variant takes y-freshness DATA at the outer source/target/
stack level (the data the consumer naturally has), and derives local
y-freshness for the constructor cases that ALLOW such derivation:

* `top`, `var`: trivial (no recursive sub-derivations).
* `tAp`: source = `.app .top u`, target = `.top`; y-fresh via
  `Term.fv_app`. No body recursion.
* `app`: source = `.app u_ v_`, target = `.app u_' v_'`; both factor
  cleanly into y-freshness of components via `Term.fv_app`.
* `pro`: source = `.fvar yi` with `yi ≠ y` (from `hy_src`); recurse
  into `hβ` with α_lkup's y-freshness derived from §10.1's
  `_y_notin_fv_lookupEqu_under_avoid`, target's y-freshness from
  `hy_tgt`.
* `fun_`/`fOp` (iter-21): source = `.abs tt bd`, target = `.abs tt' bd'`.
  Both factor cleanly via `Term.fv_abs` to give y-freshness on
  `tt`/`bd`/`tt'`/`bd'`. With `cofinDomFresh` re-added (giving
  `pickFresh L ∉ Γ.dom`, hence `pickFresh L ≠ y`), the body IH at
  `y₀ := pickFresh L` gets `y ∉ fv (bd^[y₀])` via `Term.fv_open_subset`
  and `y ∉ fv (bd'^[y₀])` similarly. The output cofinite L widens to
  `L ∪ Ctx.dom (Γ₂ ++ Γ₁) ∪ {y₀}` and renames y₀ → yfresh via
  `MEqRed.rename_sub` (fun_) / `_MEqRed_rename_equ_no_fv` (fOp).
* `bet` (iter-22): the v0'-freshness gap is closed by
  `MEqRed_fv_y_preserve` (§11.8a above). The operand recursion needs
  `y ∉ fv v0'`; iter-21's analysis showed this is not derivable from
  the outer `hy_tgt` alone (when `bvar 0 ∉ bd'`, opening leaves
  `bd'` unchanged so `hy_tgt` gives no v0' info; when `bvar 0 ∈ bd'`,
  it's derivable but only conditionally). The fix uses
  `MEqRed_fv_y_preserve` to *propagate* y-freshness from `hv`'s
  source `v0` (derivable from outer `hy_src`) to its target `v0'`,
  using the same context-shape constraints. The body sub-recursion
  on `bd'` uses the same y-preserve lemma applied to `hbody y₀`.
  All 8 arms now ship total. -/

/-- Helper: `fv e ⊆ fv (open_ k v e)` for ANY `v`. Generalizes the
private `_fv_subset_open` (which is specific to `.fvar x` substitution)
to arbitrary substituted terms. The proof is a routine induction on `e`
— at the `bvar` leaf, `fv (bvar i) = ∅`, so the subset holds trivially
regardless of whether `i = k` (in which case `open_ k v (bvar k) = v`)
or `i ≠ k` (`open_ k v (bvar i) = bvar i`). -/
private theorem _fv_subset_open_general (v : Term) :
    ∀ (k : Nat) (e : Term), Term.fv e ⊆ Term.fv (Term.open_ k v e) := by
  intro k e
  induction e generalizing k with
  | bvar _ => intro w hw; simp [Term.fv] at hw
  | fvar _ => simp [Term.open_]
  | top => simp [Term.fv]
  | abs tt bb iht ihb =>
    intro w hw
    simp [Term.fv] at hw
    rcases hw with hwT | hwB
    · simp [Term.open_, Term.fv]; exact Or.inl (iht k hwT)
    · simp [Term.open_, Term.fv]; exact Or.inr (ihb (k+1) hwB)
  | app tt ss iht ihs =>
    intro w hw
    simp [Term.fv] at hw
    rcases hw with hwT | hwS
    · simp [Term.open_, Term.fv]; exact Or.inl (iht k hwT)
    · simp [Term.open_, Term.fv]; exact Or.inr (ihs k hwS)

/-! ### §11.8a — `MEqRed_fv_y_preserve` (iter-22 unblocker for the bet arm)

The §11.8 bet arm needs `y ∉ fv v0'` for the operand recursion `ihv`,
and `MEqRed_fv_subset` cannot supply it (the y-binding is in Γ.dom,
which it permits). The structural fix is a **per-derivation** y-fresh-
preservation lemma whose context-shape premise (`Γ₂ ++ ⟨y, α, .equ⟩ ::
Γ₁` with Γ₂'s bounds avoiding y and Γ₁'s dom avoiding y) BLOCKS the
escape route: y can never appear in any `Γ`-derived target via Γ.dom,
because that part of the dom is invisible (Γ₂ bounds avoid y, Γ₁'s
domain doesn't contain y, and y itself is the only entry whose dom-
contribution would matter — but `avoidsPro` ensures it's never
promoted).

Proof structure mirrors `strip_equ_head_y_fresh`'s case grid; for
cofinite arms we sample our own fresh `y₀` (not `pickFresh L`), so we
do NOT need `cofinDomFresh`. The bet arm's body uses
`_fv_subset_open_general` (proved above) to back out `y ∉ fv body'`
from the IH, and then combines with `y ∉ fv v0'` to deliver
`y ∉ fv (Term.opening v0' body')`. -/

/-- **Iter-22 — y-freshness preservation under `MEqRed`.**

If `h : MEqRed (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁) st u u'` and the source
avoids `y`, the context's prior bounds avoid `y`, the stack avoids `y`,
`avoidsPro h y = true` (no Me-Pro y step), and `cofinDomFresh h = true`
(canonical witnesses fresh w.r.t. input dom — supplies
`pickFresh L ≠ y` for cofinite arms via the y-binding's presence in
the input dom), then the target also avoids `y`.

**Why this is the right shape.** `MEqRed_fv_subset` gives only
`fv u' ⊆ fv u ∪ Γ.dom`. The y-binding contributes `y` to `Γ.dom`, so
that bound is too weak: it permits `y ∈ fv u'`. The fix uses the
context shape — Γ₂'s prior bounds avoid `y`, the head IS the y-
binding, Γ₁ doesn't bind `y` — to refine the bound. The looked-up
`equ` bound for any `yi ≠ y` is itself y-fresh (via the §10.1 helper),
so the `Me-Pro` arm preserves freshness; `avoidsPro h y = true` blocks
the `Me-Pro y` arm where y-promotion would inject `y` directly. For
cofinite arms, `cofinDomFresh h = true` lets us reuse `pickFresh L`
as the fresh body witness — automatically ≠ y because y is in
the input ctx's dom — keeping the IH's `avoidsPro` available
(the Bool `avoidsPro` only checks `pickFresh L`, not arbitrary L-
avoiding witnesses, so we must use `pickFresh L`).

**Discharges.** §11.8 bet arm's blocker — supplies `y ∉ fv v0'` for
the operand recursion. -/
theorem MEqRed_fv_y_preserve
    {Γ₁ Γ₂ : Ctx} {st : Stack} {y : String} {α u u' : Term}
    (h : MEqRed (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁) st u u')
    (hΓ₂_avoid : Ctx.AvoidsBoundFv Γ₂ y)
    (hy_Γ₁ : y ∉ Γ₁.dom)
    (hst_avoid : ∀ β ∈ st, y ∉ Term.fv β)
    (hAvoid : avoidsPro h y = true)
    (hFresh : cofinDomFresh h = true)
    (hy_src : y ∉ Term.fv u) :
    y ∉ Term.fv u' := by
  classical
  generalize hΓ : (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁) = Γ at h
  induction h generalizing Γ₂ with
  | @pro Γ st' yi β β' hpv heq hβ ihβ =>
    subst hΓ
    rw [avoidsPro_pro] at hAvoid
    rw [cofinDomFresh_pro] at hFresh
    obtain ⟨hyiy_decide, hAvoid_inner⟩ := Bool.and_eq_true _ _ |>.mp hAvoid
    have hyiy : yi ≠ y := decide_eq_true_eq.mp hyiy_decide
    -- Lookup result β is y-fresh by §10.1 helper.
    have hpvFull : Prevalid (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁) := extractPrevalid hpv
    have hy_β : y ∉ Term.fv β :=
      _y_notin_fv_lookupEqu_under_avoid hpvFull heq hyiy hΓ₂_avoid hy_Γ₁
    -- Recurse on hβ. Same context, same stack.
    exact ihβ (Γ₂ := Γ₂) hΓ₂_avoid hst_avoid hy_β rfl hAvoid_inner hFresh
  | @bet Γ st' tBound v0 v0' bd bd' L hLCt hbody _hUni hv ihbody ihv =>
    subst hΓ
    rw [avoidsPro_bet] at hAvoid
    rw [cofinDomFresh_bet] at hFresh
    obtain ⟨hAvoid_body, hAvoid_v⟩ := Bool.and_eq_true _ _ |>.mp hAvoid
    obtain ⟨hFresh_left_v, hFresh_v⟩ := Bool.and_eq_true _ _ |>.mp hFresh
    obtain ⟨hFresh_left_body, hFresh_body⟩ := Bool.and_eq_true _ _ |>.mp hFresh_left_v
    obtain ⟨hFresh_left_fvbd', _hFresh_fvbd'_dec⟩ :=
      Bool.and_eq_true _ _ |>.mp hFresh_left_body
    obtain ⟨hFresh_dom_dec, _hFresh_fvbd_dec⟩ :=
      Bool.and_eq_true _ _ |>.mp hFresh_left_fvbd'
    have hy₀_dom : pickFresh L ∉ Ctx.dom (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁) :=
      decide_eq_true_eq.mp hFresh_dom_dec
    -- Source = .app (.abs tBound bd) v0; decompose y-freshness.
    have hy_v0 : y ∉ Term.fv v0 := by
      intro h_in; apply hy_src; rw [Term.fv_app]
      exact Finset.mem_union.mpr (Or.inr h_in)
    have hy_app_abs : y ∉ Term.fv (.abs tBound bd) := by
      intro h_in; apply hy_src; rw [Term.fv_app]
      exact Finset.mem_union.mpr (Or.inl h_in)
    have hy_bd : y ∉ Term.fv bd := by
      intro h_in; apply hy_app_abs; rw [Term.fv_abs]
      exact Finset.mem_union.mpr (Or.inr h_in)
    -- Operand recursion: y ∉ fv v0', empty stack.
    have hv_stack_avoid : ∀ β ∈ ([] : Stack), y ∉ Term.fv β := by
      intro β hβ; cases hβ
    have hy_v0' : y ∉ Term.fv v0' :=
      ihv (Γ₂ := Γ₂) hΓ₂_avoid hv_stack_avoid hy_v0 rfl hAvoid_v hFresh_v
    -- Body witness y₀ := pickFresh L. y₀ ≠ y because y ∈ input ctx's dom.
    let y₀ := pickFresh L
    have hy₀L : y₀ ∉ L := pickFresh_notMem L
    have hy_in_input : y ∈ Ctx.dom (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁) := by
      rw [_Ctx_dom_eq_under_equ_head_remove]
      exact Finset.mem_insert_self _ _
    have hy₀_neq_y : y₀ ≠ y := fun heq => hy₀_dom (heq ▸ hy_in_input)
    -- y ∉ fv (bd^[y₀]): use Term.fv_open_subset, drop y₀-singleton via y₀ ≠ y.
    have hy_bd_y₀ : y ∉ Term.fv (bd^[y₀]) := by
      intro h_in
      have hsub : y ∈ Term.fv bd ∪ Term.fv (.fvar y₀) :=
        Term.fv_open_subset 0 (.fvar y₀) bd h_in
      rcases Finset.mem_union.mp hsub with hb | hf
      · exact hy_bd hb
      · simp [Term.fv] at hf
        exact hy₀_neq_y (hf ▸ rfl)
    -- IH: y ∉ fv (bd'^[y₀]).
    have hy_bd'_y₀ : y ∉ Term.fv (bd'^[y₀]) :=
      ihbody y₀ hy₀L (Γ₂ := Γ₂) hΓ₂_avoid hst_avoid hy_bd_y₀ rfl
        hAvoid_body hFresh_body
    -- Back out y ∉ fv bd' from y ∉ fv (bd'^[y₀]) via fv_subset_open_fvar.
    have hy_bd' : y ∉ Term.fv bd' := fun h_in =>
      hy_bd'_y₀ (fv_subset_open_fvar bd' y₀ h_in)
    -- Combine: target = Term.opening v0' bd'; fv bounded by fv bd' ∪ fv v0'.
    intro h_in
    have hsub : y ∈ Term.fv bd' ∪ Term.fv v0' := by
      have := Term.fv_open_subset 0 v0' bd' h_in
      simpa [Term.opening] using this
    rcases Finset.mem_union.mp hsub with hb | hv0
    · exact hy_bd' hb
    · exact hy_v0' hv0
  | @top Γ st' hpv =>
    subst hΓ; intro h_in; simp [Term.fv] at h_in
  | @app Γ st' u_ u_' v_ v_' hu hv ihu ihv =>
    subst hΓ
    rw [avoidsPro_app] at hAvoid
    rw [cofinDomFresh_app] at hFresh
    obtain ⟨hAvoid_u, hAvoid_v⟩ := Bool.and_eq_true _ _ |>.mp hAvoid
    obtain ⟨hFresh_u, hFresh_v⟩ := Bool.and_eq_true _ _ |>.mp hFresh
    have hy_u_ : y ∉ Term.fv u_ := by
      intro h_in; apply hy_src; rw [Term.fv_app]
      exact Finset.mem_union.mpr (Or.inl h_in)
    have hy_v_ : y ∉ Term.fv v_ := by
      intro h_in; apply hy_src; rw [Term.fv_app]
      exact Finset.mem_union.mpr (Or.inr h_in)
    -- Stack for u arm = v_ :: st'.
    have hu_stack_avoid : ∀ β ∈ (v_ :: st'), y ∉ Term.fv β := by
      intro β hβ
      rcases List.mem_cons.mp hβ with rfl | hβtail
      · exact hy_v_
      · exact hst_avoid β hβtail
    have hv_stack_avoid : ∀ β ∈ ([] : Stack), y ∉ Term.fv β := by
      intro β hβ; cases hβ
    have hy_u_' : y ∉ Term.fv u_' :=
      ihu (Γ₂ := Γ₂) hΓ₂_avoid hu_stack_avoid hy_u_ rfl hAvoid_u hFresh_u
    have hy_v_' : y ∉ Term.fv v_' :=
      ihv (Γ₂ := Γ₂) hΓ₂_avoid hv_stack_avoid hy_v_ rfl hAvoid_v hFresh_v
    intro h_in
    rw [Term.fv_app] at h_in
    rcases Finset.mem_union.mp h_in with hu | hv
    · exact hy_u_' hu
    · exact hy_v_' hv
  | @var Γ st' yi hpv => subst hΓ; exact hy_src
  | @fun_ Γ tt tt' bd bd' L ht hbody _hUni iht ihbody =>
    subst hΓ
    rw [avoidsPro_fun_] at hAvoid
    rw [cofinDomFresh_fun_] at hFresh
    obtain ⟨hAvoid_t, hAvoid_body⟩ := Bool.and_eq_true _ _ |>.mp hAvoid
    obtain ⟨hFresh_left_body, hFresh_body⟩ := Bool.and_eq_true _ _ |>.mp hFresh
    obtain ⟨hFresh_left_t, hFresh_t⟩ := Bool.and_eq_true _ _ |>.mp hFresh_left_body
    obtain ⟨hFresh_left_fvbd', _hFresh_fvbd'_dec⟩ :=
      Bool.and_eq_true _ _ |>.mp hFresh_left_t
    obtain ⟨hFresh_dom_dec, _hFresh_fvbd_dec⟩ :=
      Bool.and_eq_true _ _ |>.mp hFresh_left_fvbd'
    have hy₀_dom : pickFresh L ∉ Ctx.dom (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁) :=
      decide_eq_true_eq.mp hFresh_dom_dec
    -- Source = .abs tt bd; decompose.
    have hy_tt : y ∉ Term.fv tt := by
      intro h_in; apply hy_src; rw [Term.fv_abs]
      exact Finset.mem_union.mpr (Or.inl h_in)
    have hy_bd : y ∉ Term.fv bd := by
      intro h_in; apply hy_src; rw [Term.fv_abs]
      exact Finset.mem_union.mpr (Or.inr h_in)
    -- t IH at empty stack.
    have ht_stack_avoid : ∀ β ∈ ([] : Stack), y ∉ Term.fv β := by
      intro β hβ; cases hβ
    have hy_tt' : y ∉ Term.fv tt' :=
      iht (Γ₂ := Γ₂) hΓ₂_avoid ht_stack_avoid hy_tt rfl hAvoid_t hFresh_t
    -- Body IH at canonical y₀ := pickFresh L. y₀ ≠ y since y ∈ input dom.
    let y₀ := pickFresh L
    have hy₀L : y₀ ∉ L := pickFresh_notMem L
    have hy_in_input : y ∈ Ctx.dom (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁) := by
      rw [_Ctx_dom_eq_under_equ_head_remove]
      exact Finset.mem_insert_self _ _
    have hy₀_neq_y : y₀ ≠ y := fun heq => hy₀_dom (heq ▸ hy_in_input)
    have hy_bd_y₀ : y ∉ Term.fv (bd^[y₀]) := by
      intro h_in
      have hsub : y ∈ Term.fv bd ∪ Term.fv (.fvar y₀) :=
        Term.fv_open_subset 0 (.fvar y₀) bd h_in
      rcases Finset.mem_union.mp hsub with hb | hf
      · exact hy_bd hb
      · simp [Term.fv] at hf; exact hy₀_neq_y (hf ▸ rfl)
    have hΓ₂'_avoid : Ctx.AvoidsBoundFv (⟨y₀, tt, .sub⟩ :: Γ₂) y :=
      Ctx.AvoidsBoundFv_cons.mpr ⟨hy_tt, hΓ₂_avoid⟩
    have hbody_stack_avoid : ∀ β ∈ ([] : Stack), y ∉ Term.fv β := by
      intro β hβ; cases hβ
    have hy_bd'_y₀ : y ∉ Term.fv (bd'^[y₀]) :=
      ihbody y₀ hy₀L (Γ₂ := ⟨y₀, tt, .sub⟩ :: Γ₂)
        hΓ₂'_avoid hbody_stack_avoid hy_bd_y₀ (by simp) hAvoid_body hFresh_body
    have hy_bd' : y ∉ Term.fv bd' := fun h_in =>
      hy_bd'_y₀ (fv_subset_open_fvar bd' y₀ h_in)
    intro h_in
    rw [Term.fv_abs] at h_in
    rcases Finset.mem_union.mp h_in with ht | hb
    · exact hy_tt' ht
    · exact hy_bd' hb
  | @tAp Γ st' u_ hpv hLCu hfv =>
    subst hΓ; intro h_in; simp [Term.fv] at h_in
  | @fOp Γ st' tt tt' αi bd bd' L ht hbody _hUni iht ihbody =>
    subst hΓ
    rw [avoidsPro_fOp] at hAvoid
    rw [cofinDomFresh_fOp] at hFresh
    obtain ⟨hAvoid_t, hAvoid_body⟩ := Bool.and_eq_true _ _ |>.mp hAvoid
    obtain ⟨hFresh_left_body, hFresh_body⟩ := Bool.and_eq_true _ _ |>.mp hFresh
    obtain ⟨hFresh_left_t, hFresh_t⟩ := Bool.and_eq_true _ _ |>.mp hFresh_left_body
    obtain ⟨hFresh_left_fvbd', _hFresh_fvbd'_dec⟩ :=
      Bool.and_eq_true _ _ |>.mp hFresh_left_t
    obtain ⟨hFresh_dom_dec, _hFresh_fvbd_dec⟩ :=
      Bool.and_eq_true _ _ |>.mp hFresh_left_fvbd'
    have hy₀_dom : pickFresh L ∉ Ctx.dom (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁) :=
      decide_eq_true_eq.mp hFresh_dom_dec
    -- Source = .abs tt bd; stack = αi :: st'.
    have hy_tt : y ∉ Term.fv tt := by
      intro h_in; apply hy_src; rw [Term.fv_abs]
      exact Finset.mem_union.mpr (Or.inl h_in)
    have hy_bd : y ∉ Term.fv bd := by
      intro h_in; apply hy_src; rw [Term.fv_abs]
      exact Finset.mem_union.mpr (Or.inr h_in)
    have hy_αi : y ∉ Term.fv αi :=
      hst_avoid αi (List.mem_cons_self _ _)
    have hst'_avoid : ∀ β ∈ st', y ∉ Term.fv β := fun β hβ =>
      hst_avoid β (List.mem_cons_of_mem _ hβ)
    have ht_stack_avoid : ∀ β ∈ ([] : Stack), y ∉ Term.fv β := by
      intro β hβ; cases hβ
    have hy_tt' : y ∉ Term.fv tt' :=
      iht (Γ₂ := Γ₂) hΓ₂_avoid ht_stack_avoid hy_tt rfl hAvoid_t hFresh_t
    let y₀ := pickFresh L
    have hy₀L : y₀ ∉ L := pickFresh_notMem L
    have hy_in_input : y ∈ Ctx.dom (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁) := by
      rw [_Ctx_dom_eq_under_equ_head_remove]
      exact Finset.mem_insert_self _ _
    have hy₀_neq_y : y₀ ≠ y := fun heq => hy₀_dom (heq ▸ hy_in_input)
    have hy_bd_y₀ : y ∉ Term.fv (bd^[y₀]) := by
      intro h_in
      have hsub : y ∈ Term.fv bd ∪ Term.fv (.fvar y₀) :=
        Term.fv_open_subset 0 (.fvar y₀) bd h_in
      rcases Finset.mem_union.mp hsub with hb | hf
      · exact hy_bd hb
      · simp [Term.fv] at hf; exact hy₀_neq_y (hf ▸ rfl)
    have hΓ₂'_avoid : Ctx.AvoidsBoundFv (⟨y₀, αi, .equ⟩ :: Γ₂) y :=
      Ctx.AvoidsBoundFv_cons.mpr ⟨hy_αi, hΓ₂_avoid⟩
    have hy_bd'_y₀ : y ∉ Term.fv (bd'^[y₀]) :=
      ihbody y₀ hy₀L (Γ₂ := ⟨y₀, αi, .equ⟩ :: Γ₂)
        hΓ₂'_avoid hst'_avoid hy_bd_y₀ (by simp) hAvoid_body hFresh_body
    have hy_bd' : y ∉ Term.fv bd' := fun h_in =>
      hy_bd'_y₀ (fv_subset_open_fvar bd' y₀ h_in)
    intro h_in
    rw [Term.fv_abs] at h_in
    rcases Finset.mem_union.mp h_in with ht | hb
    · exact hy_tt' ht
    · exact hy_bd' hb

/-- **Iter-21 — y-fresh-source variant of `MEqRed.strip_equ_head`.**

Same effect as `MEqRed.strip_equ_head` (remove an `.equ`-head from a
`MEqRed` derivation) but takes localized y-freshness premises
(`hy_src`, `hy_tgt`, `hst_avoid`) in place of the global `avoidsFv`
bundle. Re-introduces `hFresh : cofinDomFresh h = true` (which the
cofinite arms need to ensure `pickFresh L ∉ Γ.dom`, hence `≠ y`).

**Status (iter-22):** all 8 arms ship working. The bet arm's
v0'-freshness gap is closed via `MEqRed_fv_y_preserve` on `hv`. -/
noncomputable def MEqRed.strip_equ_head_y_fresh
    {Γ₁ Γ₂ : Ctx} {st : Stack} {y : String} {α u u' : Term}
    (h : MEqRed (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁) st u u')
    (hΓ₂_avoid : Ctx.AvoidsBoundFv Γ₂ y)
    (hy_Γ₁ : y ∉ Γ₁.dom)
    (hst_avoid : ∀ β ∈ st, y ∉ Term.fv β)
    (hAvoid : avoidsPro h y = true)
    (hFresh : cofinDomFresh h = true)
    (hy_src : y ∉ Term.fv u)
    (hy_tgt : y ∉ Term.fv u') :
    MEqRed (Γ₂ ++ Γ₁) st u u' := by
  classical
  generalize hΓ : (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁) = Γ at h
  induction h generalizing Γ₂ with
  | @pro Γ st' yi β β' hpv heq hβ ihβ =>
    subst hΓ
    rw [avoidsPro_pro] at hAvoid
    rw [cofinDomFresh_pro] at hFresh
    obtain ⟨hyiy_decide, hAvoid_inner⟩ := Bool.and_eq_true _ _ |>.mp hAvoid
    have hyiy : yi ≠ y := decide_eq_true_eq.mp hyiy_decide
    -- Derive y ∉ fv β via §10.1 helper.
    have hpvFull : Prevalid (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁) := extractPrevalid hpv
    have hy_β : y ∉ Term.fv β :=
      _y_notin_fv_lookupEqu_under_avoid hpvFull heq hyiy hΓ₂_avoid hy_Γ₁
    -- Build new prevalidExt for the smaller stack/ctx.
    have hpv' : PrevalidExt (Γ₂ ++ Γ₁) st' :=
      PrevalidExt.equ_head_remove_mid hpv hΓ₂_avoid hst_avoid
    have heq' := _equBinds_equ_head_remove_neq hyiy heq
    -- Recurse on hβ. Source = β (y-fresh from helper), target = β' (y-fresh from hy_tgt).
    exact MEqRed.pro hpv' heq' (ihβ (Γ₂ := Γ₂) hΓ₂_avoid hst_avoid
      hy_β hy_tgt rfl hAvoid_inner hFresh)
  | @bet Γ st' tBound v0 v0' bd bd' L hLCt hbody _hUni hv ihbody ihv =>
    subst hΓ
    rw [avoidsPro_bet] at hAvoid
    rw [cofinDomFresh_bet] at hFresh
    obtain ⟨hAvoid_body, hAvoid_v⟩ := Bool.and_eq_true _ _ |>.mp hAvoid
    -- Decompose hFresh: (((dom && fvbd) && fvbd') && body) && v.
    obtain ⟨hFresh_left_v, hFresh_v⟩ := Bool.and_eq_true _ _ |>.mp hFresh
    obtain ⟨hFresh_left_body, hFresh_body⟩ := Bool.and_eq_true _ _ |>.mp hFresh_left_v
    obtain ⟨hFresh_left_fvbd', hFresh_fvbd'_dec⟩ :=
      Bool.and_eq_true _ _ |>.mp hFresh_left_body
    obtain ⟨hFresh_dom_dec, hFresh_fvbd_dec⟩ :=
      Bool.and_eq_true _ _ |>.mp hFresh_left_fvbd'
    have hy₀_dom : pickFresh L ∉ Ctx.dom (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁) :=
      decide_eq_true_eq.mp hFresh_dom_dec
    have hy₀_fvbd : pickFresh L ∉ Term.fv bd :=
      decide_eq_true_eq.mp hFresh_fvbd_dec
    have hy₀_fvbd' : pickFresh L ∉ Term.fv bd' :=
      decide_eq_true_eq.mp hFresh_fvbd'_dec
    let y₀ := pickFresh L
    have hy₀L : y₀ ∉ L := pickFresh_notMem L
    -- y₀ ≠ y, since y ∈ input ctx's dom but y₀ is not.
    have hy_in_input : y ∈ Ctx.dom (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁) := by
      rw [_Ctx_dom_eq_under_equ_head_remove]
      exact Finset.mem_insert_self _ _
    have hy₀_neq_y : y₀ ≠ y := fun heq => hy₀_dom (heq ▸ hy_in_input)
    have hy₀_dom' : y₀ ∉ Ctx.dom (Γ₂ ++ Γ₁) := by
      intro h_in
      apply hy₀_dom
      rw [_Ctx_dom_eq_under_equ_head_remove]
      exact Finset.mem_insert_of_mem h_in
    -- Decompose hy_src/hy_tgt.
    have hy_v0 : y ∉ Term.fv v0 := by
      intro h_in; apply hy_src; rw [Term.fv_app]
      exact Finset.mem_union.mpr (Or.inr h_in)
    have hy_app_abs : y ∉ Term.fv (.abs tBound bd) := by
      intro h_in; apply hy_src; rw [Term.fv_app]
      exact Finset.mem_union.mpr (Or.inl h_in)
    have hy_bd : y ∉ Term.fv bd := by
      intro h_in; apply hy_app_abs; rw [Term.fv_abs]
      exact Finset.mem_union.mpr (Or.inr h_in)
    -- Operand: derive y ∉ fv v0' via MEqRed_fv_y_preserve on hv.
    have hv_stack_avoid : ∀ β ∈ ([] : Stack), y ∉ Term.fv β := by
      intro β hβ; cases hβ
    have hy_v0' : y ∉ Term.fv v0' :=
      MEqRed_fv_y_preserve hv hΓ₂_avoid hy_Γ₁ hv_stack_avoid hAvoid_v
        hFresh_v hy_v0
    -- Body: y ∉ fv (bd^[y₀]) via fv_open_subset and y₀ ≠ y.
    have hy_bd_y₀ : y ∉ Term.fv (bd^[y₀]) := by
      intro h_in
      have hsub : y ∈ Term.fv bd ∪ Term.fv (.fvar y₀) :=
        Term.fv_open_subset 0 (.fvar y₀) bd h_in
      rcases Finset.mem_union.mp hsub with hb | hf
      · exact hy_bd hb
      · simp [Term.fv] at hf; exact hy₀_neq_y (hf ▸ rfl)
    -- y ∉ fv (bd'^[y₀]) via MEqRed_fv_y_preserve on hbody y₀.
    have hy_bd'_y₀ : y ∉ Term.fv (bd'^[y₀]) :=
      MEqRed_fv_y_preserve (hbody y₀ hy₀L) hΓ₂_avoid hy_Γ₁ hst_avoid
        hAvoid_body hFresh_body hy_bd_y₀
    -- Recurse on body and operand.
    have ihbody_y₀ := ihbody y₀ hy₀L (Γ₂ := Γ₂) hΓ₂_avoid hst_avoid
      hy_bd_y₀ hy_bd'_y₀ rfl hAvoid_body hFresh_body
    have ihv' := ihv (Γ₂ := Γ₂) hΓ₂_avoid hv_stack_avoid
      hy_v0 hy_v0' rfl hAvoid_v hFresh_v
    -- Build the output bet at the smaller context.
    refine MEqRed.bet (L ∪ Ctx.dom (Γ₂ ++ Γ₁) ∪ {y₀})
      hLCt ?_ trivial ihv'
    intro yfresh hyfresh
    simp only [Finset.mem_union, Finset.mem_singleton] at hyfresh
    push_neg at hyfresh
    obtain ⟨⟨hyfL, hyf_dom⟩, _hyf_y₀⟩ := hyfresh
    -- Prevalid for the output context.
    have hpvE_y₀ : PrevalidExt (Γ₂ ++ Γ₁) st' :=
      MEqRed.prevalidExt ihbody_y₀
    have hpv_removed : Prevalid (Γ₂ ++ Γ₁) := extractPrevalid hpvE_y₀
    -- Stack freshness for y₀ via PrevalidExt at the new context.
    have hy₀_stack : ∀ β ∈ st', y₀ ∉ Term.fv β :=
      _y₀_notin_stack_fv_of_notin_dom hpvE_y₀ hy₀_dom'
    -- Rename y₀ → yfresh.
    have ren := MEqRed.rename_stray hpv_removed ihbody_y₀ y₀ yfresh hy₀_dom' hyf_dom
    have hstk_eq : Stack.subst y₀ (.fvar yfresh) st' = st' :=
      Stack.subst_fresh hy₀_stack
    have hbd_eq : Term.subst y₀ (.fvar yfresh) (bd^[y₀]) = bd^[yfresh] :=
      Term.subst_open_fresh hy₀_fvbd
    have hbd'_eq : Term.subst y₀ (.fvar yfresh) (bd'^[y₀]) = bd'^[yfresh] :=
      Term.subst_open_fresh hy₀_fvbd'
    rw [hstk_eq, hbd_eq, hbd'_eq] at ren
    exact ren
  | @top Γ st' hpv =>
    subst hΓ
    have hpv' : PrevalidExt (Γ₂ ++ Γ₁) st' :=
      PrevalidExt.equ_head_remove_mid hpv hΓ₂_avoid hst_avoid
    exact MEqRed.top hpv'
  | @app Γ st' u_ u_' v_ v_' hu hv ihu ihv =>
    subst hΓ
    rw [avoidsPro_app] at hAvoid
    rw [cofinDomFresh_app] at hFresh
    obtain ⟨hAvoid_u, hAvoid_v⟩ := Bool.and_eq_true _ _ |>.mp hAvoid
    obtain ⟨hFresh_u, hFresh_v⟩ := Bool.and_eq_true _ _ |>.mp hFresh
    -- Decompose hy_src and hy_tgt: source = .app u_ v_, target = .app u_' v_'.
    have hy_u_ : y ∉ Term.fv u_ := by
      intro h_in; apply hy_src; rw [Term.fv_app]
      exact Finset.mem_union.mpr (Or.inl h_in)
    have hy_v_ : y ∉ Term.fv v_ := by
      intro h_in; apply hy_src; rw [Term.fv_app]
      exact Finset.mem_union.mpr (Or.inr h_in)
    have hy_u_' : y ∉ Term.fv u_' := by
      intro h_in; apply hy_tgt; rw [Term.fv_app]
      exact Finset.mem_union.mpr (Or.inl h_in)
    have hy_v_' : y ∉ Term.fv v_' := by
      intro h_in; apply hy_tgt; rw [Term.fv_app]
      exact Finset.mem_union.mpr (Or.inr h_in)
    -- Stack for u arm = v_ :: st'.
    have hu_stack_avoid : ∀ β ∈ (v_ :: st'), y ∉ Term.fv β := by
      intro β hβ
      rcases List.mem_cons.mp hβ with rfl | hβtail
      · exact hy_v_
      · exact hst_avoid β hβtail
    have hv_stack_avoid : ∀ β ∈ ([] : Stack), y ∉ Term.fv β := by
      intro β hβ; cases hβ
    have ihu' := ihu (Γ₂ := Γ₂) hΓ₂_avoid hu_stack_avoid
      hy_u_ hy_u_' rfl hAvoid_u hFresh_u
    have ihv' := ihv (Γ₂ := Γ₂) hΓ₂_avoid hv_stack_avoid
      hy_v_ hy_v_' rfl hAvoid_v hFresh_v
    exact MEqRed.app ihu' ihv'
  | @var Γ st' yi hpv =>
    subst hΓ
    have hpv' : PrevalidExt (Γ₂ ++ Γ₁) st' :=
      PrevalidExt.equ_head_remove_mid hpv hΓ₂_avoid hst_avoid
    exact MEqRed.var hpv'
  | @fun_ Γ tt tt' bd bd' L ht hbody _hUni iht ihbody =>
    subst hΓ
    rw [avoidsPro_fun_] at hAvoid
    rw [cofinDomFresh_fun_] at hFresh
    obtain ⟨hAvoid_t, hAvoid_body⟩ := Bool.and_eq_true _ _ |>.mp hAvoid
    obtain ⟨hFresh_left_body, hFresh_body⟩ := Bool.and_eq_true _ _ |>.mp hFresh
    obtain ⟨hFresh_left_t, hFresh_t⟩ := Bool.and_eq_true _ _ |>.mp hFresh_left_body
    obtain ⟨hFresh_left_fvbd', hFresh_fvbd'_dec⟩ :=
      Bool.and_eq_true _ _ |>.mp hFresh_left_t
    obtain ⟨hFresh_dom_dec, hFresh_fvbd_dec⟩ :=
      Bool.and_eq_true _ _ |>.mp hFresh_left_fvbd'
    -- Decompose hy_src/hy_tgt: source = .abs tt bd, target = .abs tt' bd'.
    have hy_tt : y ∉ Term.fv tt := by
      intro h_in; apply hy_src; rw [Term.fv_abs]
      exact Finset.mem_union.mpr (Or.inl h_in)
    have hy_bd : y ∉ Term.fv bd := by
      intro h_in; apply hy_src; rw [Term.fv_abs]
      exact Finset.mem_union.mpr (Or.inr h_in)
    have hy_tt' : y ∉ Term.fv tt' := by
      intro h_in; apply hy_tgt; rw [Term.fv_abs]
      exact Finset.mem_union.mpr (Or.inl h_in)
    have hy_bd' : y ∉ Term.fv bd' := by
      intro h_in; apply hy_tgt; rw [Term.fv_abs]
      exact Finset.mem_union.mpr (Or.inr h_in)
    have hy₀_dom : pickFresh L ∉ Ctx.dom (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁) :=
      decide_eq_true_eq.mp hFresh_dom_dec
    have hy₀_fvbd : pickFresh L ∉ Term.fv bd :=
      decide_eq_true_eq.mp hFresh_fvbd_dec
    have hy₀_fvbd' : pickFresh L ∉ Term.fv bd' :=
      decide_eq_true_eq.mp hFresh_fvbd'_dec
    let y₀ := pickFresh L
    have hy₀L : y₀ ∉ L := pickFresh_notMem L
    -- y₀ ≠ y, since y ∈ input ctx's dom but y₀ is not.
    have hy_in_input : y ∈ Ctx.dom (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁) := by
      rw [_Ctx_dom_eq_under_equ_head_remove]
      exact Finset.mem_insert_self _ _
    have hy₀_neq_y : y₀ ≠ y := fun heq => hy₀_dom (heq ▸ hy_in_input)
    have hy₀_dom' : y₀ ∉ Ctx.dom (Γ₂ ++ Γ₁) := by
      intro h_in
      apply hy₀_dom
      rw [_Ctx_dom_eq_under_equ_head_remove]
      exact Finset.mem_insert_of_mem h_in
    -- t IH at empty stack.
    have ht_stack_avoid : ∀ β ∈ ([] : Stack), y ∉ Term.fv β := by
      intro β hβ; cases hβ
    have iht' := iht (Γ₂ := Γ₂) hΓ₂_avoid ht_stack_avoid
      hy_tt hy_tt' rfl hAvoid_t hFresh_t
    -- body IH at extended Γ₂' = ⟨y₀, tt, .sub⟩ :: Γ₂.
    -- Need y ∉ fv (bd^[y₀]) and y ∉ fv (bd'^[y₀]).
    -- Use Term.fv_open_subset: fv (e^[y₀]) ⊆ fv e ∪ {y₀}.
    have hy_bd_y₀ : y ∉ Term.fv (bd^[y₀]) := by
      intro h_in
      have hsub : y ∈ Term.fv bd ∪ Term.fv (.fvar y₀) :=
        Term.fv_open_subset 0 (.fvar y₀) bd h_in
      rcases Finset.mem_union.mp hsub with hb | hf
      · exact hy_bd hb
      · simp [Term.fv] at hf
        exact hy₀_neq_y (hf ▸ rfl)
    have hy_bd'_y₀ : y ∉ Term.fv (bd'^[y₀]) := by
      intro h_in
      have hsub : y ∈ Term.fv bd' ∪ Term.fv (.fvar y₀) :=
        Term.fv_open_subset 0 (.fvar y₀) bd' h_in
      rcases Finset.mem_union.mp hsub with hb | hf
      · exact hy_bd' hb
      · simp [Term.fv] at hf
        exact hy₀_neq_y (hf ▸ rfl)
    have hΓ₂'_avoid : Ctx.AvoidsBoundFv (⟨y₀, tt, .sub⟩ :: Γ₂) y :=
      Ctx.AvoidsBoundFv_cons.mpr ⟨hy_tt, hΓ₂_avoid⟩
    have hbody_stack_avoid : ∀ β ∈ ([] : Stack), y ∉ Term.fv β := by
      intro β hβ; cases hβ
    have ihbody_y₀ := ihbody y₀ hy₀L
      (Γ₂ := ⟨y₀, tt, .sub⟩ :: Γ₂) hΓ₂'_avoid hbody_stack_avoid
      hy_bd_y₀ hy_bd'_y₀ (by simp) hAvoid_body hFresh_body
    refine MEqRed.fun_ (L ∪ Ctx.dom (Γ₂ ++ Γ₁) ∪ {y₀}) iht' ?_ trivial
    intro yfresh hyfresh
    simp only [Finset.mem_union, Finset.mem_singleton] at hyfresh
    push_neg at hyfresh
    obtain ⟨⟨hyfL, hyf_dom⟩, _hyf_y₀⟩ := hyfresh
    -- Extract data from ihbody_y₀'s prevalidExt (output ctx).
    have ihbody_y₀_norm : MEqRed (⟨y₀, tt, .sub⟩ :: (Γ₂ ++ Γ₁)) []
        (bd^[y₀]) (bd'^[y₀]) := by simpa using ihbody_y₀
    have hpvE_full : PrevalidExt (⟨y₀, tt, .sub⟩ :: (Γ₂ ++ Γ₁)) [] :=
      MEqRed.prevalidExt ihbody_y₀_norm
    have hpv_full : Prevalid (⟨y₀, tt, .sub⟩ :: (Γ₂ ++ Γ₁)) :=
      extractPrevalid hpvE_full
    have hpv_outer : Prevalid (Γ₂ ++ Γ₁) := by
      cases hpv_full with
      | sub hpv _ _ _ => exact hpv
    have hLCt_tt : Term.LC tt := by
      cases hpv_full with
      | sub _ _ _ hLCtt => exact hLCtt
    have hfvtt : Term.fv tt ⊆ Ctx.dom (Γ₂ ++ Γ₁) := by
      cases hpv_full with
      | sub _ _ hfvtt _ => exact hfvtt
    -- Apply MEqRed.rename_sub. Stack is empty for fun_, so stack-freshness is trivial.
    have ren := MEqRed.rename_sub hpv_outer hLCt_tt hfvtt
      hy₀_dom' hyf_dom hy₀_fvbd hy₀_fvbd'
      (by intro β hβ; cases hβ) ihbody_y₀_norm
    simpa using ren
  | @tAp Γ st' u_ hpv hLCu hfv =>
    subst hΓ
    have hpv' : PrevalidExt (Γ₂ ++ Γ₁) st' :=
      PrevalidExt.equ_head_remove_mid hpv hΓ₂_avoid hst_avoid
    -- Need fv u_ ⊆ (Γ₂ ++ Γ₁).dom. From hfv : ⊆ insert y (Γ₂ ++ Γ₁).dom and y ∉ fv u_.
    have hy_u_ : y ∉ Term.fv u_ := by
      intro h_in; apply hy_src; rw [Term.fv_app]
      exact Finset.mem_union.mpr (Or.inr h_in)
    have hfv' : Term.fv u_ ⊆ Ctx.dom (Γ₂ ++ Γ₁) := by
      intro z hz
      have hzd := hfv hz
      rw [_Ctx_dom_eq_under_equ_head_remove] at hzd
      rw [Finset.mem_insert] at hzd
      cases hzd with
      | inl hzy => subst hzy; exact absurd hz hy_u_
      | inr hz' => exact hz'
    exact MEqRed.tAp hpv' hLCu hfv'
  | @fOp Γ st' tt tt' αi bd bd' L ht hbody _hUni iht ihbody =>
    subst hΓ
    rw [avoidsPro_fOp] at hAvoid
    rw [cofinDomFresh_fOp] at hFresh
    obtain ⟨hAvoid_t, hAvoid_body⟩ := Bool.and_eq_true _ _ |>.mp hAvoid
    obtain ⟨hFresh_left_body, hFresh_body⟩ := Bool.and_eq_true _ _ |>.mp hFresh
    obtain ⟨hFresh_left_t, hFresh_t⟩ := Bool.and_eq_true _ _ |>.mp hFresh_left_body
    obtain ⟨hFresh_left_fvbd', hFresh_fvbd'_dec⟩ :=
      Bool.and_eq_true _ _ |>.mp hFresh_left_t
    obtain ⟨hFresh_dom_dec, hFresh_fvbd_dec⟩ :=
      Bool.and_eq_true _ _ |>.mp hFresh_left_fvbd'
    -- Decompose hy_src/hy_tgt: source = .abs tt bd, target = .abs tt' bd'.
    have hy_tt : y ∉ Term.fv tt := by
      intro h_in; apply hy_src; rw [Term.fv_abs]
      exact Finset.mem_union.mpr (Or.inl h_in)
    have hy_bd : y ∉ Term.fv bd := by
      intro h_in; apply hy_src; rw [Term.fv_abs]
      exact Finset.mem_union.mpr (Or.inr h_in)
    have hy_tt' : y ∉ Term.fv tt' := by
      intro h_in; apply hy_tgt; rw [Term.fv_abs]
      exact Finset.mem_union.mpr (Or.inl h_in)
    have hy_bd' : y ∉ Term.fv bd' := by
      intro h_in; apply hy_tgt; rw [Term.fv_abs]
      exact Finset.mem_union.mpr (Or.inr h_in)
    -- Stack at this fOp node is αi :: st'; from hst_avoid (for outer αi :: st'),
    -- y ∉ fv αi and y ∉ fv β for β ∈ st'.
    have hy_αi : y ∉ Term.fv αi :=
      hst_avoid αi (List.mem_cons_self _ _)
    have hst'_avoid : ∀ β ∈ st', y ∉ Term.fv β := fun β hβ =>
      hst_avoid β (List.mem_cons_of_mem _ hβ)
    have hy₀_dom : pickFresh L ∉ Ctx.dom (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁) :=
      decide_eq_true_eq.mp hFresh_dom_dec
    have hy₀_fvbd : pickFresh L ∉ Term.fv bd :=
      decide_eq_true_eq.mp hFresh_fvbd_dec
    have hy₀_fvbd' : pickFresh L ∉ Term.fv bd' :=
      decide_eq_true_eq.mp hFresh_fvbd'_dec
    let y₀ := pickFresh L
    have hy₀L : y₀ ∉ L := pickFresh_notMem L
    have hy_in_input : y ∈ Ctx.dom (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁) := by
      rw [_Ctx_dom_eq_under_equ_head_remove]
      exact Finset.mem_insert_self _ _
    have hy₀_neq_y : y₀ ≠ y := fun heq => hy₀_dom (heq ▸ hy_in_input)
    have hy₀_dom' : y₀ ∉ Ctx.dom (Γ₂ ++ Γ₁) := by
      intro h_in
      apply hy₀_dom
      rw [_Ctx_dom_eq_under_equ_head_remove]
      exact Finset.mem_insert_of_mem h_in
    have ht_stack_avoid : ∀ β ∈ ([] : Stack), y ∉ Term.fv β := by
      intro β hβ; cases hβ
    have iht' := iht (Γ₂ := Γ₂) hΓ₂_avoid ht_stack_avoid
      hy_tt hy_tt' rfl hAvoid_t hFresh_t
    -- body IH: bd^[y₀]/bd'^[y₀] at the extended ctx ⟨y₀, αi, .equ⟩ :: Γ₂.
    have hy_bd_y₀ : y ∉ Term.fv (bd^[y₀]) := by
      intro h_in
      have hsub : y ∈ Term.fv bd ∪ Term.fv (.fvar y₀) :=
        Term.fv_open_subset 0 (.fvar y₀) bd h_in
      rcases Finset.mem_union.mp hsub with hb | hf
      · exact hy_bd hb
      · simp [Term.fv] at hf
        exact hy₀_neq_y (hf ▸ rfl)
    have hy_bd'_y₀ : y ∉ Term.fv (bd'^[y₀]) := by
      intro h_in
      have hsub : y ∈ Term.fv bd' ∪ Term.fv (.fvar y₀) :=
        Term.fv_open_subset 0 (.fvar y₀) bd' h_in
      rcases Finset.mem_union.mp hsub with hb | hf
      · exact hy_bd' hb
      · simp [Term.fv] at hf
        exact hy₀_neq_y (hf ▸ rfl)
    have hΓ₂'_avoid : Ctx.AvoidsBoundFv (⟨y₀, αi, .equ⟩ :: Γ₂) y :=
      Ctx.AvoidsBoundFv_cons.mpr ⟨hy_αi, hΓ₂_avoid⟩
    have ihbody_y₀ := ihbody y₀ hy₀L
      (Γ₂ := ⟨y₀, αi, .equ⟩ :: Γ₂) hΓ₂'_avoid hst'_avoid
      hy_bd_y₀ hy_bd'_y₀ (by simp) hAvoid_body hFresh_body
    refine MEqRed.fOp (L ∪ Ctx.dom (Γ₂ ++ Γ₁) ∪ {y₀}) iht' ?_ trivial
    intro yfresh hyfresh
    simp only [Finset.mem_union, Finset.mem_singleton] at hyfresh
    push_neg at hyfresh
    obtain ⟨⟨hyfL, hyf_dom⟩, hyf_y₀⟩ := hyfresh
    have hyz : y₀ ≠ yfresh := fun h' => hyf_y₀ h'.symm
    have ihbody_y₀_norm :
        MEqRed (⟨y₀, αi, .equ⟩ :: (Γ₂ ++ Γ₁)) st'
          (bd^[y₀]) (bd'^[y₀]) := by simpa using ihbody_y₀
    have hpvE_full : PrevalidExt (⟨y₀, αi, .equ⟩ :: (Γ₂ ++ Γ₁)) st' :=
      MEqRed.prevalidExt ihbody_y₀_norm
    have hpv_full : Prevalid (⟨y₀, αi, .equ⟩ :: (Γ₂ ++ Γ₁)) :=
      extractPrevalid hpvE_full
    have hfv_αi : Term.fv αi ⊆ Ctx.dom (Γ₂ ++ Γ₁) := by
      cases hpv_full with
      | equ _ _ hfvαi _ => exact hfvαi
    have hy₀_αi : y₀ ∉ Term.fv αi := fun h' => hy₀_dom' (hfv_αi h')
    -- Stack freshness for y₀ at the body's PrevalidExt. Use OUTER context's
    -- PrevalidExt at outer st (αi :: st') instead, since the inner ctx is extended.
    have hpv_outer_inputst : PrevalidExt (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁) (αi :: st') :=
      MEqRed.prevalidExt (MEqRed.fOp L ht hbody trivial)
    have hpv_outer_st_only : PrevalidExt (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁) st' := by
      cases hpv_outer_inputst with
      | cons hpv_tail _ _ => exact hpv_tail
    have hy₀_stack : ∀ β ∈ st', y₀ ∉ Term.fv β :=
      _y₀_notin_stack_fv_of_notin_dom hpv_outer_st_only hy₀_dom
    have ren := _MEqRed_rename_equ_no_fv hyz hy₀_dom' hyf_dom hy₀_αi
      hy₀_fvbd hy₀_fvbd' hy₀_stack ihbody_y₀_norm
    simpa using ren

/-! ### §11.9 — `MEqRed.descend_y_fresh_source_template` (iter-25: total — 8 of 8 arms)

This is the architectural unifier of §11.7's leaves. The §11.7 leaves
(`bvar0`, `top`, `fvar var-arm` aux, `app-app` open-recursion arm) each
encode ONE constructor case of the descent functor. This §11.9 functor
encodes the WHOLE case grid by inducting on the input derivation rather
than recursing on `body : Term`.

### Iter-25 update — total functor; gate removed

Iter-23 ran `Γ₂=[]`-only and gated all three cofinite arms behind
`cofinite_blocked : Empty`. Iter-24 generalised to arbitrary `Γ₂` and
shipped 7 of 8 arms (var/top/tAp/app/pro/bet/fun_), leaving fOp gated.

Iter-25 ships the **fOp** arm via case-split on `s_tmpl` (cons-vs-nil)
to dispatch the αi-position into the s_outer slice (subcase A) or the
s_tmpl slice (subcase B); both subcases recurse on `hbody y₀` at the
extended context `⟨y₀, αi, .equ⟩ :: Γ₂` and post-rename y₀ → yfresh via
`_MEqRed_rename_equ_no_fv`. The `cofinite_blocked` gate is removed —
the functor is now total and callable.

### Premise threading

Γ₂-generalization (input ctx `Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁`, output ctx
`Γ₂ ++ Γ₁`) plus the LC premise `hLC_stmpl : ∀ b ∈ s_tmpl, Term.LC b`.
The LC premise collapses `b^[y] = b` and `b^[z] = b` for templates, so
stack entries effectively behave as y-fresh (under `hy_stmpl`). The
cofinite arms recurse into a body sub-derivation at the EXTENDED ctx
`⟨y₀, _, _⟩ :: Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁` (new `Γ₂' = ⟨y₀,_,_⟩::Γ₂`),
then post-rename `y₀ → yfresh` via `MEqRed.rename_stray` (bet) /
`MEqRed.rename_sub` (fun_) / `_MEqRed_rename_equ_no_fv` (fOp).

### Status: 8 of 8 arms

* **var, top, tAp, app, pro, bet, fun_, fOp**: shipped, no axioms, no
  sorries. The descent functor is total and ready for consumer wiring
  into the β-residual closures.

### Why the `app` arm uses `LC v_` to extend `s_tmpl`

For `MEqRed.app hu hv : MEqRed _ s (.app u_ v_) (.app u_' v_')`, `hu`'s
stack is `v_ :: s`. To express this as `s_tmpl_new.map (·^[y]) ++ s_outer`
for the recursive call, we set `s_tmpl_new := v_ :: s_tmpl` and use
`v_^[y] = v_` (which holds because `v_` is LC, so opening at `bvar 0`
is the identity). The `LC v_` data comes from the input prevalidExt
extracted via `MEqRed.prevalidExt h` plus prevalid's `fv ⊆ dom`. -/

/-- **Iter-25 — unified descent functor (total: 8 of 8 arms).**

Threads the stack-template-shift `(·^[y]) ↝ (·^[z])` through each
constructor of `MEqRed`, removing the equ-head from the middle of the
context (`Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁ ↦ Γ₂ ++ Γ₁`). The LC premise on
`s_tmpl` collapses opening to identity, simplifying invariants.

### Premises

* `hΓ₂_avoid`: every entry in `Γ₂` has `y` outside its bound's fv —
  ensures the y-binding is genuinely "in the middle".
* `hAvoid`: blocks the `Me-Pro y` arm (which would inject `y` directly
  into the target via lookup).
* `hFresh`: ensures the cofinite arms' `pickFresh L ≠ y` and dom-freshness.
* `hLC_stmpl`: each template is locally closed (so `b^[y] = b`).
* `hy_stmpl`, `hy_souter`, `hy_Γ₁`: y-freshness data on the stack
  templates, the y-fresh outer, and the outer context's domain.
* `hy_src`: the source `u` is y-fresh. Excludes `body = .bvar 0` (which
  has source `.fvar y` — handled by the existing `bvar0` leaf instead).
* `hz_out`: `z` is in scope at the smaller context `Γ₂ ++ Γ₁`.

### Output

`MEqRed (Γ₂ ++ Γ₁) (s_tmpl.map (·^[z]) ++ s_outer) u (subst y (.fvar z) u')`.

### fOp arm (iter-25 close)

The `fOp` arm's stack at the constructor is `αi :: st'`. We case-split
`s_tmpl`:

* **Subcase A (`s_tmpl = []`):** `s_outer = αi :: st'`. αi-freshness from
  `hy_souter αi (head)`. Body recurses with `s_tmpl' = []`, `s_outer' = st'`.
* **Subcase B (`s_tmpl = b :: stl`):** `b^[y] = αi`. With `hLC_stmpl b`,
  `b^[y] = b`, so `αi = b`, and y-freshness comes from `hy_stmpl b`. Body
  recurses with `s_tmpl' = stl`, `s_outer' = s_outer`.

In both subcases the body recurses at the EXTENDED Γ₂' = `⟨y₀, αi, .equ⟩ :: Γ₂`,
and the post-recursion y₀ → yfresh rename uses `_MEqRed_rename_equ_no_fv`. -/
noncomputable def MEqRed.descend_y_fresh_source_template
    {Γ₁ Γ₂ : Ctx} {s_outer : Stack} {y : String} {α u u' : Term}
    (s_tmpl : List Term)
    (h : MEqRed (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁) (s_tmpl.map (·^[y]) ++ s_outer) u u')
    (hΓ₂_avoid : Ctx.AvoidsBoundFv Γ₂ y)
    (hAvoid : avoidsPro h y = true)
    (hFresh : cofinDomFresh h = true)
    (hLC_stmpl : ∀ b ∈ s_tmpl, Term.LC b)
    (hy_stmpl : ∀ b ∈ s_tmpl, y ∉ Term.fv b)
    (hy_souter : ∀ β ∈ s_outer, y ∉ Term.fv β)
    (hy_Γ₁ : y ∉ Γ₁.dom)
    (hy_src : y ∉ Term.fv u)
    (z : String) (hz_out : z ∈ Ctx.dom (Γ₂ ++ Γ₁)) :
    MEqRed (Γ₂ ++ Γ₁) (s_tmpl.map (·^[z]) ++ s_outer) u
                       (Term.subst y (.fvar z) u') := by
  classical
  -- Generalize the input ctx and stack to free metavariables so `induction h`
  -- works. The equations let us recover the structure at each constructor case.
  generalize hΓ : (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁ : Ctx) = Γ' at h
  generalize hst : s_tmpl.map (·^[y]) ++ s_outer = st at h
  -- Generalize Γ₂, hΓ₂_avoid (cofinite arms change them) plus the stack-shape
  -- and freshness side-data so the IH can refresh them at the recursive call.
  induction h generalizing Γ₂ s_tmpl hLC_stmpl hy_stmpl s_outer hy_souter with
  | @pro Γ_h st' yi β β' hpv heq hβ ihβ =>
    subst hΓ
    rw [avoidsPro_pro] at hAvoid
    rw [cofinDomFresh_pro] at hFresh
    obtain ⟨hyiy_decide, hAvoid_inner⟩ := Bool.and_eq_true _ _ |>.mp hAvoid
    have hyiy : yi ≠ y := decide_eq_true_eq.mp hyiy_decide
    have hpvFull : Prevalid (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁) := extractPrevalid hpv
    have hy_β : y ∉ Term.fv β :=
      _y_notin_fv_lookupEqu_under_avoid hpvFull heq hyiy hΓ₂_avoid hy_Γ₁
    have ih :=
      ihβ (Γ₂ := Γ₂) (s_tmpl := s_tmpl) (s_outer := s_outer)
          (hΓ₂_avoid := hΓ₂_avoid) (hLC_stmpl := hLC_stmpl) (hy_stmpl := hy_stmpl)
          (hy_souter := hy_souter) (hAvoid := hAvoid_inner) (hFresh := hFresh)
          (hy_src := hy_β) (hz_out := hz_out) rfl hst
    have heq' := _equBinds_equ_head_remove_neq hyiy heq
    rw [← hst] at hpv
    have hpv' : PrevalidExt (Γ₂ ++ Γ₁) (s_tmpl.map (·^[z]) ++ s_outer) :=
      _PrevalidExt_descend_under_equ_head_template_mid
        s_tmpl hpv hΓ₂_avoid hy_stmpl hy_souter hy_Γ₁ z hz_out
    show MEqRed (Γ₂ ++ Γ₁) (s_tmpl.map (·^[z]) ++ s_outer) (.fvar yi)
                 (Term.subst y (.fvar z) β')
    exact MEqRed.pro hpv' heq' ih
  | @top Γ_h st' hpv =>
    subst hΓ
    rw [← hst] at hpv
    have hpv' : PrevalidExt (Γ₂ ++ Γ₁) (s_tmpl.map (·^[z]) ++ s_outer) :=
      _PrevalidExt_descend_under_equ_head_template_mid
        s_tmpl hpv hΓ₂_avoid hy_stmpl hy_souter hy_Γ₁ z hz_out
    show MEqRed (Γ₂ ++ Γ₁) (s_tmpl.map (·^[z]) ++ s_outer) .top
                 (Term.subst y (.fvar z) .top)
    show MEqRed (Γ₂ ++ Γ₁) (s_tmpl.map (·^[z]) ++ s_outer) .top .top
    exact MEqRed.top hpv'
  | @var Γ_h st' yi hpv =>
    subst hΓ
    have hyiy : yi ≠ y := by
      intro heq
      apply hy_src
      simp [Term.fv, heq]
    rw [← hst] at hpv
    have hpv' : PrevalidExt (Γ₂ ++ Γ₁) (s_tmpl.map (·^[z]) ++ s_outer) :=
      _PrevalidExt_descend_under_equ_head_template_mid
        s_tmpl hpv hΓ₂_avoid hy_stmpl hy_souter hy_Γ₁ z hz_out
    show MEqRed (Γ₂ ++ Γ₁) (s_tmpl.map (·^[z]) ++ s_outer) (.fvar yi)
                 (Term.subst y (.fvar z) (.fvar yi))
    rw [Term.subst_fvar_ne hyiy]
    exact MEqRed.var hpv'
  | @tAp Γ_h st' u_ hpv hLCu hfv =>
    subst hΓ
    have hy_u_ : y ∉ Term.fv u_ := by
      intro h_in; apply hy_src; rw [Term.fv_app]
      exact Finset.mem_union.mpr (Or.inr h_in)
    rw [← hst] at hpv
    have hpv' : PrevalidExt (Γ₂ ++ Γ₁) (s_tmpl.map (·^[z]) ++ s_outer) :=
      _PrevalidExt_descend_under_equ_head_template_mid
        s_tmpl hpv hΓ₂_avoid hy_stmpl hy_souter hy_Γ₁ z hz_out
    have hfv' : Term.fv u_ ⊆ Ctx.dom (Γ₂ ++ Γ₁) := by
      intro w hw
      have hwd := hfv hw
      rw [_Ctx_dom_eq_under_equ_head_remove] at hwd
      rcases Finset.mem_insert.mp hwd with hwy | hwΓ
      · subst hwy; exact absurd hw hy_u_
      · exact hwΓ
    show MEqRed (Γ₂ ++ Γ₁) (s_tmpl.map (·^[z]) ++ s_outer) (.app .top u_)
                 (Term.subst y (.fvar z) .top)
    show MEqRed (Γ₂ ++ Γ₁) (s_tmpl.map (·^[z]) ++ s_outer) (.app .top u_) .top
    exact MEqRed.tAp hpv' hLCu hfv'
  | @app Γ_h st' u_ u_' v_ v_' hu hv ihu ihv =>
    subst hΓ
    rw [avoidsPro_app] at hAvoid
    rw [cofinDomFresh_app] at hFresh
    obtain ⟨hAvoid_u, hAvoid_v⟩ := Bool.and_eq_true _ _ |>.mp hAvoid
    obtain ⟨hFresh_u, hFresh_v⟩ := Bool.and_eq_true _ _ |>.mp hFresh
    have hy_u_ : y ∉ Term.fv u_ := by
      intro h_in; apply hy_src; rw [Term.fv_app]
      exact Finset.mem_union.mpr (Or.inl h_in)
    have hy_v_ : y ∉ Term.fv v_ := by
      intro h_in; apply hy_src; rw [Term.fv_app]
      exact Finset.mem_union.mpr (Or.inr h_in)
    have hpvE_u : PrevalidExt (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁) (v_ :: st') :=
      MEqRed.prevalidExt hu
    have hLC_v_ : Term.LC v_ := by
      cases hpvE_u with
      | cons _ hLC _ => exact hLC
    have hv_open_y : v_^[y] = v_ := Term.opening_lc hLC_v_ (.fvar y)
    have hv_open_z : v_^[z] = v_ := Term.opening_lc hLC_v_ (.fvar z)
    have hLC_stmpl_u : ∀ b ∈ v_ :: s_tmpl, Term.LC b := by
      intro b hb
      by_cases heq : b = v_
      · exact heq ▸ hLC_v_
      · have hmem : b ∈ s_tmpl := by
          rcases List.mem_cons.mp hb with hh | hh
          · exact absurd hh heq
          · exact hh
        exact hLC_stmpl b hmem
    have hy_stmpl_u : ∀ b ∈ v_ :: s_tmpl, y ∉ Term.fv b := by
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hmem
      · exact hy_v_
      · exact hy_stmpl b hmem
    have hst_u : (v_ :: s_tmpl).map (·^[y]) ++ s_outer = v_ :: st' := by
      simp [List.map_cons, hv_open_y, hst]
    have ihu' :=
      ihu (Γ₂ := Γ₂) (s_tmpl := v_ :: s_tmpl) (s_outer := s_outer)
          (hΓ₂_avoid := hΓ₂_avoid) (hLC_stmpl := hLC_stmpl_u)
          (hy_stmpl := hy_stmpl_u) (hy_souter := hy_souter)
          (hAvoid := hAvoid_u) (hFresh := hFresh_u)
          (hy_src := hy_u_) (hz_out := hz_out) rfl hst_u
    have hLC_stmpl_v : ∀ b ∈ ([] : List Term), Term.LC b := by
      intro b hb; exact (List.not_mem_nil _ hb).elim
    have hy_stmpl_v : ∀ b ∈ ([] : List Term), y ∉ Term.fv b := by
      intro b hb; cases hb
    have hy_souter_v : ∀ β ∈ ([] : Stack), y ∉ Term.fv β := by
      intro β hβ; cases hβ
    have hst_v : ([] : List Term).map (·^[y]) ++ ([] : Stack) = [] := by simp
    have ihv' :=
      ihv (Γ₂ := Γ₂) (s_tmpl := []) (s_outer := [])
          (hΓ₂_avoid := hΓ₂_avoid) (hLC_stmpl := hLC_stmpl_v)
          (hy_stmpl := hy_stmpl_v) (hy_souter := hy_souter_v)
          (hAvoid := hAvoid_v) (hFresh := hFresh_v)
          (hy_src := hy_v_) (hz_out := hz_out) rfl hst_v
    have htgt : Term.subst y (.fvar z) (.app u_' v_')
        = .app (Term.subst y (.fvar z) u_') (Term.subst y (.fvar z) v_') := by
      simp [Term.subst]
    show MEqRed (Γ₂ ++ Γ₁) (s_tmpl.map (·^[z]) ++ s_outer) (.app u_ v_)
                 (Term.subst y (.fvar z) (.app u_' v_'))
    rw [htgt]
    have hu_descended :
        MEqRed (Γ₂ ++ Γ₁) (v_ :: (s_tmpl.map (·^[z]) ++ s_outer))
                u_ (Term.subst y (.fvar z) u_') := by
      have : MEqRed (Γ₂ ++ Γ₁) ((v_ :: s_tmpl).map (·^[z]) ++ s_outer)
                     u_ (Term.subst y (.fvar z) u_') := ihu'
      simpa [List.map_cons, hv_open_z] using this
    have hv_descended : MEqRed (Γ₂ ++ Γ₁) [] v_
                                (Term.subst y (.fvar z) v_') := by
      simpa using ihv'
    exact MEqRed.app hu_descended hv_descended
  | @bet Γ_h st' tBound v0 v0' bd bd' L hLCt hbody _hUni hv ihbody ihv =>
    -- Body sub-derivation lives at SAME outer ctx (Γ₂ ++ ⟨y,α,.equ⟩::Γ₁) at
    -- stack `st'` (= s_tmpl.map (·^[y]) ++ s_outer via hst), but with body
    -- opened at y₀. Recurse on hbody y₀ at same Γ₂ / s_tmpl / s_outer; then
    -- rename y₀ → yfresh via MEqRed.rename_stray on the descended output.
    subst hΓ
    rw [avoidsPro_bet] at hAvoid
    rw [cofinDomFresh_bet] at hFresh
    obtain ⟨hAvoid_body, hAvoid_v⟩ := Bool.and_eq_true _ _ |>.mp hAvoid
    obtain ⟨hFresh_left_v, hFresh_v⟩ := Bool.and_eq_true _ _ |>.mp hFresh
    obtain ⟨hFresh_left_body, hFresh_body⟩ := Bool.and_eq_true _ _ |>.mp hFresh_left_v
    obtain ⟨hFresh_left_fvbd', hFresh_fvbd'_dec⟩ :=
      Bool.and_eq_true _ _ |>.mp hFresh_left_body
    obtain ⟨hFresh_dom_dec, hFresh_fvbd_dec⟩ :=
      Bool.and_eq_true _ _ |>.mp hFresh_left_fvbd'
    have hy₀_dom_in : pickFresh L ∉ Ctx.dom (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁) :=
      decide_eq_true_eq.mp hFresh_dom_dec
    have hy₀_fvbd : pickFresh L ∉ Term.fv bd :=
      decide_eq_true_eq.mp hFresh_fvbd_dec
    have hy₀_fvbd' : pickFresh L ∉ Term.fv bd' :=
      decide_eq_true_eq.mp hFresh_fvbd'_dec
    let y₀ := pickFresh L
    have hy₀L : y₀ ∉ L := pickFresh_notMem L
    have hy_in_input : y ∈ Ctx.dom (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁) := by
      rw [_Ctx_dom_eq_under_equ_head_remove]
      exact Finset.mem_insert_self _ _
    have hy₀_neq_y : y₀ ≠ y := fun heq' => hy₀_dom_in (heq' ▸ hy_in_input)
    have hy₀_dom_out : y₀ ∉ Ctx.dom (Γ₂ ++ Γ₁) := by
      intro h_in
      apply hy₀_dom_in
      rw [_Ctx_dom_eq_under_equ_head_remove]
      exact Finset.mem_insert_of_mem h_in
    -- Decompose hy_src: source = .app (.abs tBound bd) v0.
    have hy_app_abs : y ∉ Term.fv (.abs tBound bd) := by
      intro h_in; apply hy_src; rw [Term.fv_app]
      exact Finset.mem_union.mpr (Or.inl h_in)
    have hy_bd : y ∉ Term.fv bd := by
      intro h_in; apply hy_app_abs; rw [Term.fv_abs]
      exact Finset.mem_union.mpr (Or.inr h_in)
    have hy_v0 : y ∉ Term.fv v0 := by
      intro h_in; apply hy_src; rw [Term.fv_app]
      exact Finset.mem_union.mpr (Or.inr h_in)
    have hy_bd_y₀ : y ∉ Term.fv (bd^[y₀]) := by
      intro h_in
      have hsub : y ∈ Term.fv bd ∪ Term.fv (.fvar y₀) :=
        Term.fv_open_subset 0 (.fvar y₀) bd h_in
      rcases Finset.mem_union.mp hsub with hb | hf
      · exact hy_bd hb
      · simp [Term.fv] at hf; exact hy₀_neq_y (hf ▸ rfl)
    -- Recurse on hbody y₀ at SAME Γ₂. Stack/templates unchanged (hbody y₀'s
    -- stack matches `st'` after generalize).
    have ihbody_y₀ :=
      ihbody y₀ hy₀L (Γ₂ := Γ₂) (s_tmpl := s_tmpl) (s_outer := s_outer)
        (hΓ₂_avoid := hΓ₂_avoid) (hLC_stmpl := hLC_stmpl) (hy_stmpl := hy_stmpl)
        (hy_souter := hy_souter) (hAvoid := hAvoid_body) (hFresh := hFresh_body)
        (hy_src := hy_bd_y₀) (hz_out := hz_out) rfl hst
    -- Recurse on hv at empty stack/templates.
    have hLC_stmpl_v : ∀ b ∈ ([] : List Term), Term.LC b := by
      intro b hb; exact (List.not_mem_nil _ hb).elim
    have hy_stmpl_v : ∀ b ∈ ([] : List Term), y ∉ Term.fv b := by
      intro b hb; cases hb
    have hy_souter_v : ∀ β ∈ ([] : Stack), y ∉ Term.fv β := by
      intro β hβ; cases hβ
    have hst_v : ([] : List Term).map (·^[y]) ++ ([] : Stack) = [] := by simp
    have ihv' :=
      ihv (Γ₂ := Γ₂) (s_tmpl := []) (s_outer := [])
          (hΓ₂_avoid := hΓ₂_avoid) (hLC_stmpl := hLC_stmpl_v)
          (hy_stmpl := hy_stmpl_v) (hy_souter := hy_souter_v)
          (hAvoid := hAvoid_v) (hFresh := hFresh_v)
          (hy_src := hy_v0) (hz_out := hz_out) rfl hst_v
    have ihv_norm : MEqRed (Γ₂ ++ Γ₁) [] v0 (Term.subst y (.fvar z) v0') := by
      simpa using ihv'
    -- Goal target: subst y (.fvar z) (Term.opening v0' bd')
    --   = Term.opening (subst y (.fvar z) v0') (subst y (.fvar z) bd')
    -- via subst-opening commutation (when .fvar z is LC).
    have hLC_z : Term.LC (.fvar z) := Term.LC.fvar z
    have htgt_eq :
        Term.subst y (.fvar z) (Term.opening v0' bd')
          = Term.opening (Term.subst y (.fvar z) v0') (Term.subst y (.fvar z) bd') := by
      unfold Term.opening
      rw [Term.subst_open hLC_z]
    show MEqRed (Γ₂ ++ Γ₁) (s_tmpl.map (·^[z]) ++ s_outer)
                 (.app (.abs tBound bd) v0)
                 (Term.subst y (.fvar z) (Term.opening v0' bd'))
    rw [htgt_eq]
    -- Apply MEqRed.bet at the smaller ctx.
    refine MEqRed.bet (L ∪ Ctx.dom (Γ₂ ++ Γ₁) ∪ {y₀})
      hLCt ?_ trivial ihv_norm
    intro yfresh hyfresh
    simp only [Finset.mem_union, Finset.mem_singleton] at hyfresh
    push_neg at hyfresh
    obtain ⟨⟨hyfL, hyf_dom⟩, hyf_y₀⟩ := hyfresh
    -- ihbody_y₀ : MEqRed (Γ₂ ++ Γ₁) (s_tmpl.map (·^[z]) ++ s_outer)
    --                    (bd^[y₀]) (subst y (.fvar z) (bd'^[y₀])).
    -- Convert subst y (.fvar z) (bd'^[y₀]) ↦ (subst y (.fvar z) bd')^[y₀] via y ≠ y₀.
    have hsubst_open_bd' :
        Term.subst y (.fvar z) (bd'^[y₀]) = (Term.subst y (.fvar z) bd')^[y₀] :=
      Term.subst_open_var hy₀_neq_y.symm hLC_z bd'
    rw [hsubst_open_bd'] at ihbody_y₀
    -- Stack freshness for y₀ at the descended PrevalidExt (output ctx).
    have hpvE_descended : PrevalidExt (Γ₂ ++ Γ₁) (s_tmpl.map (·^[z]) ++ s_outer) :=
      MEqRed.prevalidExt ihbody_y₀
    have hpv_descended : Prevalid (Γ₂ ++ Γ₁) := extractPrevalid hpvE_descended
    have hy₀_stack : ∀ β ∈ s_tmpl.map (·^[z]) ++ s_outer, y₀ ∉ Term.fv β :=
      _y₀_notin_stack_fv_of_notin_dom hpvE_descended hy₀_dom_out
    -- Rename y₀ → yfresh via rename_stray.
    have ren := MEqRed.rename_stray hpv_descended ihbody_y₀ y₀ yfresh
                                     hy₀_dom_out hyf_dom
    -- Stack subst is a no-op via hy₀_stack.
    have hstk_eq : Stack.subst y₀ (.fvar yfresh) (s_tmpl.map (·^[z]) ++ s_outer)
        = s_tmpl.map (·^[z]) ++ s_outer :=
      Stack.subst_fresh hy₀_stack
    have hbd_eq : Term.subst y₀ (.fvar yfresh) (bd^[y₀]) = bd^[yfresh] :=
      Term.subst_open_fresh hy₀_fvbd
    -- y₀ ∉ fv (subst y (.fvar z) bd'). Derive from hy₀_fvbd' + y₀ ≠ z.
    have hy₀_neq_z : y₀ ≠ z := fun h => hy₀_dom_out (h ▸ hz_out)
    have hy₀_notin_subst_bd' : y₀ ∉ Term.fv (Term.subst y (.fvar z) bd') := by
      intro h_in
      have hsub := Term.fv_subst_subset y (.fvar z) bd' h_in
      rcases Finset.mem_union.mp hsub with h1 | h2
      · exact hy₀_fvbd' (Finset.mem_sdiff.mp h1).1
      · have : y₀ = z := by simpa [Term.fv] using h2
        exact hy₀_neq_z this
    have hbd'_eq : Term.subst y₀ (.fvar yfresh) ((Term.subst y (.fvar z) bd')^[y₀])
        = (Term.subst y (.fvar z) bd')^[yfresh] :=
      Term.subst_open_fresh hy₀_notin_subst_bd'
    rw [hstk_eq, hbd_eq, hbd'_eq] at ren
    exact ren
  | @fun_ Γ_h tt tt' bd bd' L ht hbody _hUni iht ihbody =>
    -- Body lives at EXTENDED ctx ⟨y₀, tt, .sub⟩ :: Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁,
    -- which is (⟨y₀, tt, .sub⟩ :: Γ₂) ++ ⟨y, α, .equ⟩ :: Γ₁ — the new Γ₂'.
    -- Stack at fun_ node is []; recursion is at empty stack/templates.
    subst hΓ
    have hst_empty : s_tmpl.map (·^[y]) ++ s_outer = [] := hst
    have hst_split : s_tmpl = [] ∧ s_outer = [] := by
      cases s_tmpl with
      | nil => exact ⟨rfl, by simpa using hst_empty⟩
      | cons _ _ => simp at hst_empty
    obtain ⟨hsmpl_nil, houter_nil⟩ := hst_split
    subst hsmpl_nil; subst houter_nil
    rw [avoidsPro_fun_] at hAvoid
    rw [cofinDomFresh_fun_] at hFresh
    obtain ⟨hAvoid_t, hAvoid_body⟩ := Bool.and_eq_true _ _ |>.mp hAvoid
    obtain ⟨hFresh_left_body, hFresh_body⟩ := Bool.and_eq_true _ _ |>.mp hFresh
    obtain ⟨hFresh_left_t, hFresh_t⟩ := Bool.and_eq_true _ _ |>.mp hFresh_left_body
    obtain ⟨hFresh_left_fvbd', hFresh_fvbd'_dec⟩ :=
      Bool.and_eq_true _ _ |>.mp hFresh_left_t
    obtain ⟨hFresh_dom_dec, hFresh_fvbd_dec⟩ :=
      Bool.and_eq_true _ _ |>.mp hFresh_left_fvbd'
    have hy₀_dom_in : pickFresh L ∉ Ctx.dom (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁) :=
      decide_eq_true_eq.mp hFresh_dom_dec
    have hy₀_fvbd : pickFresh L ∉ Term.fv bd :=
      decide_eq_true_eq.mp hFresh_fvbd_dec
    have hy₀_fvbd' : pickFresh L ∉ Term.fv bd' :=
      decide_eq_true_eq.mp hFresh_fvbd'_dec
    let y₀ := pickFresh L
    have hy₀L : y₀ ∉ L := pickFresh_notMem L
    have hy_in_input : y ∈ Ctx.dom (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁) := by
      rw [_Ctx_dom_eq_under_equ_head_remove]
      exact Finset.mem_insert_self _ _
    have hy₀_neq_y : y₀ ≠ y := fun heq' => hy₀_dom_in (heq' ▸ hy_in_input)
    have hy₀_dom_out : y₀ ∉ Ctx.dom (Γ₂ ++ Γ₁) := by
      intro h_in
      apply hy₀_dom_in
      rw [_Ctx_dom_eq_under_equ_head_remove]
      exact Finset.mem_insert_of_mem h_in
    -- Decompose hy_src: source = .abs tt bd.
    have hy_tt : y ∉ Term.fv tt := by
      intro h_in; apply hy_src; rw [Term.fv_abs]
      exact Finset.mem_union.mpr (Or.inl h_in)
    have hy_bd : y ∉ Term.fv bd := by
      intro h_in; apply hy_src; rw [Term.fv_abs]
      exact Finset.mem_union.mpr (Or.inr h_in)
    have hy_bd_y₀ : y ∉ Term.fv (bd^[y₀]) := by
      intro h_in
      have hsub : y ∈ Term.fv bd ∪ Term.fv (.fvar y₀) :=
        Term.fv_open_subset 0 (.fvar y₀) bd h_in
      rcases Finset.mem_union.mp hsub with hb | hf
      · exact hy_bd hb
      · simp [Term.fv] at hf; exact hy₀_neq_y (hf ▸ rfl)
    -- Recurse on iht at empty stack, same Γ₂.
    have hLC_stmpl_t : ∀ b ∈ ([] : List Term), Term.LC b := by
      intro b hb; exact (List.not_mem_nil _ hb).elim
    have hy_stmpl_t : ∀ b ∈ ([] : List Term), y ∉ Term.fv b := by
      intro b hb; cases hb
    have hy_souter_t : ∀ β ∈ ([] : Stack), y ∉ Term.fv β := by
      intro β hβ; cases hβ
    have hst_t : ([] : List Term).map (·^[y]) ++ ([] : Stack) = [] := by simp
    have iht' :=
      iht (Γ₂ := Γ₂) (s_tmpl := []) (s_outer := [])
          (hΓ₂_avoid := hΓ₂_avoid) (hLC_stmpl := hLC_stmpl_t)
          (hy_stmpl := hy_stmpl_t) (hy_souter := hy_souter_t)
          (hAvoid := hAvoid_t) (hFresh := hFresh_t)
          (hy_src := hy_tt) (hz_out := hz_out) rfl hst_t
    have iht_norm : MEqRed (Γ₂ ++ Γ₁) [] tt (Term.subst y (.fvar z) tt') := by
      simpa using iht'
    -- Recurse on hbody y₀ at extended Γ₂' = ⟨y₀, tt, .sub⟩ :: Γ₂.
    have hΓ₂'_avoid : Ctx.AvoidsBoundFv (⟨y₀, tt, .sub⟩ :: Γ₂) y :=
      Ctx.AvoidsBoundFv_cons.mpr ⟨hy_tt, hΓ₂_avoid⟩
    have hz_out_ext : z ∈ Ctx.dom ((⟨y₀, tt, .sub⟩ :: Γ₂) ++ Γ₁) := by
      simp [Ctx.dom_append, Ctx.dom_cons] at hz_out ⊢
      tauto
    have hctx_eq_body :
        ((⟨y₀, tt, .sub⟩ :: Γ₂) ++ ⟨y, α, .equ⟩ :: Γ₁ : Ctx) =
          ⟨y₀, tt, .sub⟩ :: (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁) := by simp
    have ihbody_y₀ :=
      ihbody y₀ hy₀L (Γ₂ := ⟨y₀, tt, .sub⟩ :: Γ₂)
        (s_tmpl := []) (s_outer := [])
        (hΓ₂_avoid := hΓ₂'_avoid) (hLC_stmpl := hLC_stmpl_t)
        (hy_stmpl := hy_stmpl_t) (hy_souter := hy_souter_t)
        (hAvoid := hAvoid_body) (hFresh := hFresh_body)
        (hy_src := hy_bd_y₀)
        (hz_out := hz_out_ext) hctx_eq_body.symm hst_t
    have ihbody_y₀_norm : MEqRed (⟨y₀, tt, .sub⟩ :: (Γ₂ ++ Γ₁)) []
        (bd^[y₀]) (Term.subst y (.fvar z) (bd'^[y₀])) := by simpa using ihbody_y₀
    have hLC_z : Term.LC (.fvar z) := Term.LC.fvar z
    have hsubst_open_bd' :
        Term.subst y (.fvar z) (bd'^[y₀]) = (Term.subst y (.fvar z) bd')^[y₀] :=
      Term.subst_open_var hy₀_neq_y.symm hLC_z bd'
    rw [hsubst_open_bd'] at ihbody_y₀_norm
    have hpvE_full : PrevalidExt (⟨y₀, tt, .sub⟩ :: (Γ₂ ++ Γ₁)) [] :=
      MEqRed.prevalidExt ihbody_y₀_norm
    have hpv_full : Prevalid (⟨y₀, tt, .sub⟩ :: (Γ₂ ++ Γ₁)) :=
      extractPrevalid hpvE_full
    have hpv_outer : Prevalid (Γ₂ ++ Γ₁) := by
      cases hpv_full with
      | sub hpv _ _ _ => exact hpv
    have hLCt_tt : Term.LC tt := by
      cases hpv_full with
      | sub _ _ _ hLCtt => exact hLCtt
    have hfvtt : Term.fv tt ⊆ Ctx.dom (Γ₂ ++ Γ₁) := by
      cases hpv_full with
      | sub _ _ hfvtt _ => exact hfvtt
    refine MEqRed.fun_ (L ∪ Ctx.dom (Γ₂ ++ Γ₁) ∪ {y₀}) iht_norm ?_ trivial
    intro yfresh hyfresh
    simp only [Finset.mem_union, Finset.mem_singleton] at hyfresh
    push_neg at hyfresh
    obtain ⟨⟨hyfL, hyf_dom⟩, _hyf_y₀⟩ := hyfresh
    have hy₀_neq_z : y₀ ≠ z := fun h => hy₀_dom_out (h ▸ hz_out)
    have hy₀_notin_subst_bd' : y₀ ∉ Term.fv (Term.subst y (.fvar z) bd') := by
      intro h_in
      have hsub := Term.fv_subst_subset y (.fvar z) bd' h_in
      rcases Finset.mem_union.mp hsub with h1 | h2
      · exact hy₀_fvbd' (Finset.mem_sdiff.mp h1).1
      · have : y₀ = z := by simpa [Term.fv] using h2
        exact hy₀_neq_z this
    have ren := MEqRed.rename_sub hpv_outer hLCt_tt hfvtt
      hy₀_dom_out hyf_dom hy₀_fvbd hy₀_notin_subst_bd'
      (by intro β hβ; cases hβ) ihbody_y₀_norm
    -- ren has source binding `tt` (not subst-d since y ∉ fv tt). Confirms with the
    -- fun_ output's body cofinite premise (which uses input `tt` for the binding).
    exact ren
  | @fOp Γ_h st' tt tt' αi bd bd' L ht hbody _hUni iht ihbody =>
    -- fOp's stack is αi :: st'. From `hst : s_tmpl.map (·^[y]) ++ s_outer = αi :: st'`,
    -- case-split on s_tmpl:
    --   A) `s_tmpl = []`: s_outer = αi :: st'. Body recurses with s_tmpl' = [],
    --      s_outer' = st'. αi-freshness from `hy_souter αi (head)`.
    --   B) `s_tmpl = b :: stl`: b^[y] = αi. With `hLC_stmpl b`, b LC so b^[y] = b.
    --      Hence αi = b. Body recurses with s_tmpl' = stl, s_outer' = s_outer.
    -- Both subcases: body lives at EXTENDED Γ₂' = ⟨y₀, αi, .equ⟩ :: Γ₂. After
    -- recursion at extended Γ₂', use `_MEqRed_rename_equ_no_fv` to rename
    -- y₀ → yfresh in the head equ-binding for the fOp output.
    subst hΓ
    rw [avoidsPro_fOp] at hAvoid
    rw [cofinDomFresh_fOp] at hFresh
    obtain ⟨hAvoid_t, hAvoid_body⟩ := Bool.and_eq_true _ _ |>.mp hAvoid
    obtain ⟨hFresh_left_body, hFresh_body⟩ := Bool.and_eq_true _ _ |>.mp hFresh
    obtain ⟨hFresh_left_t, hFresh_t⟩ := Bool.and_eq_true _ _ |>.mp hFresh_left_body
    obtain ⟨hFresh_left_fvbd', hFresh_fvbd'_dec⟩ :=
      Bool.and_eq_true _ _ |>.mp hFresh_left_t
    obtain ⟨hFresh_dom_dec, hFresh_fvbd_dec⟩ :=
      Bool.and_eq_true _ _ |>.mp hFresh_left_fvbd'
    have hy₀_dom_in : pickFresh L ∉ Ctx.dom (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁) :=
      decide_eq_true_eq.mp hFresh_dom_dec
    have hy₀_fvbd : pickFresh L ∉ Term.fv bd :=
      decide_eq_true_eq.mp hFresh_fvbd_dec
    have hy₀_fvbd' : pickFresh L ∉ Term.fv bd' :=
      decide_eq_true_eq.mp hFresh_fvbd'_dec
    let y₀ := pickFresh L
    have hy₀L : y₀ ∉ L := pickFresh_notMem L
    have hy_in_input : y ∈ Ctx.dom (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁) := by
      rw [_Ctx_dom_eq_under_equ_head_remove]
      exact Finset.mem_insert_self _ _
    have hy₀_neq_y : y₀ ≠ y := fun heq' => hy₀_dom_in (heq' ▸ hy_in_input)
    have hy₀_dom_out : y₀ ∉ Ctx.dom (Γ₂ ++ Γ₁) := by
      intro h_in
      apply hy₀_dom_in
      rw [_Ctx_dom_eq_under_equ_head_remove]
      exact Finset.mem_insert_of_mem h_in
    -- Decompose hy_src: source = .abs tt bd.
    have hy_tt : y ∉ Term.fv tt := by
      intro h_in; apply hy_src; rw [Term.fv_abs]
      exact Finset.mem_union.mpr (Or.inl h_in)
    have hy_bd : y ∉ Term.fv bd := by
      intro h_in; apply hy_src; rw [Term.fv_abs]
      exact Finset.mem_union.mpr (Or.inr h_in)
    have hy_bd_y₀ : y ∉ Term.fv (bd^[y₀]) := by
      intro h_in
      have hsub : y ∈ Term.fv bd ∪ Term.fv (.fvar y₀) :=
        Term.fv_open_subset 0 (.fvar y₀) bd h_in
      rcases Finset.mem_union.mp hsub with hb | hf
      · exact hy_bd hb
      · simp [Term.fv] at hf; exact hy₀_neq_y (hf ▸ rfl)
    -- Recurse on iht at empty stack/templates, same Γ₂.
    have hLC_stmpl_t : ∀ b ∈ ([] : List Term), Term.LC b := by
      intro b hb; exact (List.not_mem_nil _ hb).elim
    have hy_stmpl_t : ∀ b ∈ ([] : List Term), y ∉ Term.fv b := by
      intro b hb; cases hb
    have hy_souter_t : ∀ β ∈ ([] : Stack), y ∉ Term.fv β := by
      intro β hβ; cases hβ
    have hst_t : ([] : List Term).map (·^[y]) ++ ([] : Stack) = [] := by simp
    have iht' :=
      iht (Γ₂ := Γ₂) (s_tmpl := []) (s_outer := [])
          (hΓ₂_avoid := hΓ₂_avoid) (hLC_stmpl := hLC_stmpl_t)
          (hy_stmpl := hy_stmpl_t) (hy_souter := hy_souter_t)
          (hAvoid := hAvoid_t) (hFresh := hFresh_t)
          (hy_src := hy_tt) (hz_out := hz_out) rfl hst_t
    have iht_norm : MEqRed (Γ₂ ++ Γ₁) [] tt (Term.subst y (.fvar z) tt') := by
      simpa using iht'
    -- Case-split on s_tmpl. Both subcases yield the same shape: αi y-fresh,
    -- recurse on hbody y₀ at extended Γ₂' = ⟨y₀, αi, .equ⟩ :: Γ₂ with appropriate
    -- (s_tmpl', s_outer') pair such that
    --   s_tmpl'.map (·^[y]) ++ s_outer' = st'   (matching body's stack).
    -- Both subcases produce y₀-fresh αi (so we can extend Γ₂'_avoid).
    have hLC_z : Term.LC (.fvar z) := Term.LC.fvar z
    -- Define s_tmpl'/s_outer' along with the αi-freshness data and the post-
    -- recursion stack-shape equality, then run the body recursion uniformly.
    have hst_eq : s_tmpl.map (·^[y]) ++ s_outer = αi :: st' := hst
    -- Compute the body recursion's output and the αi-freshness in the two
    -- subcases. We package both as a single `∃ s_tmpl' s_outer', ...` block
    -- to keep the arm linear; but a direct `match s_tmpl with` is cleaner.
    -- Source/target of fOp:
    -- source = .abs tt bd, target = .abs tt' bd'. After subst y (.fvar z):
    --   subst y (.fvar z) (.abs tt' bd') = .abs (subst y (.fvar z) tt')
    --                                            (subst y (.fvar z) bd').
    have htgt : Term.subst y (.fvar z) (.abs tt' bd')
        = .abs (Term.subst y (.fvar z) tt') (Term.subst y (.fvar z) bd') := by
      simp [Term.subst]
    show MEqRed (Γ₂ ++ Γ₁) (s_tmpl.map (·^[z]) ++ s_outer)
                 (.abs tt bd) (Term.subst y (.fvar z) (.abs tt' bd'))
    rw [htgt]
    -- Rebuild the fOp output stack `αi :: rest_descended` as
    -- `s_tmpl.map (·^[z]) ++ s_outer`.
    -- Subcase A: s_tmpl = []. Then s_outer = αi :: st'.
    -- Subcase B: s_tmpl = b :: stl, b LC, b^[y] = αi (= b), st' = stl.map (·^[y]) ++ s_outer.
    -- The two subcases are unified by computing y-fresh αi and the body
    -- recursion's stack at appropriate (s_tmpl', s_outer') pair.
    cases s_tmpl with
    | nil =>
      -- s_outer = αi :: st'.
      have hst_outer : s_outer = αi :: st' := by simpa using hst_eq
      -- αi-freshness: αi ∈ s_outer (head).
      have hy_αi : y ∉ Term.fv αi := by
        rw [hst_outer] at hy_souter
        exact hy_souter αi (List.mem_cons_self _ _)
      have hy_st' : ∀ β ∈ st', y ∉ Term.fv β := by
        intro β hβ
        rw [hst_outer] at hy_souter
        exact hy_souter β (List.mem_cons_of_mem _ hβ)
      -- Extend Γ₂_avoid with αi entry.
      have hΓ₂'_avoid : Ctx.AvoidsBoundFv (⟨y₀, αi, .equ⟩ :: Γ₂) y :=
        Ctx.AvoidsBoundFv_cons.mpr ⟨hy_αi, hΓ₂_avoid⟩
      -- y ∉ fv (bd^[y₀]) — already have hy_bd_y₀.
      -- z ∈ Ctx.dom of the new Γ₂' ++ Γ₁ = ⟨y₀, αi, .equ⟩ :: (Γ₂ ++ Γ₁).
      have hz_out_ext : z ∈ Ctx.dom ((⟨y₀, αi, .equ⟩ :: Γ₂) ++ Γ₁) := by
        simp [Ctx.dom_append, Ctx.dom_cons] at hz_out ⊢
        tauto
      -- Recurse on hbody y₀ at extended Γ₂' = ⟨y₀, αi, .equ⟩ :: Γ₂, with
      -- s_tmpl' = [], s_outer' = st' (so s_tmpl'.map (·^[y]) ++ s_outer' = st').
      have hctx_eq_body :
          ((⟨y₀, αi, .equ⟩ :: Γ₂) ++ ⟨y, α, .equ⟩ :: Γ₁ : Ctx) =
            ⟨y₀, αi, .equ⟩ :: (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁) := by simp
      have hst_body : ([] : List Term).map (·^[y]) ++ st' = st' := by simp
      have hLC_stmpl_b : ∀ b ∈ ([] : List Term), Term.LC b := by
        intro b hb; exact (List.not_mem_nil _ hb).elim
      have hy_stmpl_b : ∀ b ∈ ([] : List Term), y ∉ Term.fv b := by
        intro b hb; cases hb
      have ihbody_y₀ :=
        ihbody y₀ hy₀L (Γ₂ := ⟨y₀, αi, .equ⟩ :: Γ₂)
          (s_tmpl := []) (s_outer := st')
          (hΓ₂_avoid := hΓ₂'_avoid) (hLC_stmpl := hLC_stmpl_b)
          (hy_stmpl := hy_stmpl_b) (hy_souter := hy_st')
          (hAvoid := hAvoid_body) (hFresh := hFresh_body)
          (hy_src := hy_bd_y₀)
          (hz_out := hz_out_ext) hctx_eq_body.symm hst_body
      -- ihbody_y₀ : MEqRed ((⟨y₀, αi, .equ⟩ :: Γ₂) ++ Γ₁)
      --                    ([].map (·^[z]) ++ st')
      --                    (bd^[y₀])
      --                    (subst y (.fvar z) (bd'^[y₀])).
      have ihbody_y₀_norm :
          MEqRed (⟨y₀, αi, .equ⟩ :: (Γ₂ ++ Γ₁)) st'
            (bd^[y₀]) (Term.subst y (.fvar z) (bd'^[y₀])) := by
        simpa using ihbody_y₀
      -- Convert subst y (.fvar z) (bd'^[y₀]) ↦ (subst y (.fvar z) bd')^[y₀]
      -- via y ≠ y₀ and `Term.subst_open_var`.
      have hsubst_open_bd' :
          Term.subst y (.fvar z) (bd'^[y₀]) = (Term.subst y (.fvar z) bd')^[y₀] :=
        Term.subst_open_var hy₀_neq_y.symm hLC_z bd'
      rw [hsubst_open_bd'] at ihbody_y₀_norm
      -- Now apply MEqRed.fOp at the smaller ctx with binding αi at the head.
      -- Output stack: αi :: st' = [].map (·^[z]) ++ s_outer = s_outer.
      -- Goal stack: ([] : List Term).map (·^[z]) ++ s_outer = s_outer = αi :: st'.
      -- So we need MEqRed (Γ₂ ++ Γ₁) (αi :: st') ...
      have hgoal_stack : ([] : List Term).map (·^[z]) ++ s_outer = αi :: st' := by
        simp [hst_outer]
      rw [hgoal_stack]
      refine MEqRed.fOp (L ∪ Ctx.dom (Γ₂ ++ Γ₁) ∪ {y₀}) iht_norm ?_ trivial
      intro yfresh hyfresh
      simp only [Finset.mem_union, Finset.mem_singleton] at hyfresh
      push_neg at hyfresh
      obtain ⟨⟨hyfL, hyf_dom⟩, hyf_y₀⟩ := hyfresh
      have hyz : y₀ ≠ yfresh := fun h' => hyf_y₀ h'.symm
      -- y₀ ∉ fv αi (αi ∈ s_outer ⊆ stack of fOp's PrevalidExt at outer ctx).
      -- Pull from the body's PrevalidExt at outer ctx — fOp's stack = αi :: st'.
      have hpvE_outer_full : PrevalidExt (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁) (αi :: st') :=
        MEqRed.prevalidExt (MEqRed.fOp L ht hbody trivial)
      have hpv_outer_st_only : PrevalidExt (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁) st' := by
        cases hpvE_outer_full with
        | cons hpv_tail _ _ => exact hpv_tail
      have hpvE_full : PrevalidExt (⟨y₀, αi, .equ⟩ :: (Γ₂ ++ Γ₁)) st' :=
        MEqRed.prevalidExt ihbody_y₀_norm
      have hpv_full : Prevalid (⟨y₀, αi, .equ⟩ :: (Γ₂ ++ Γ₁)) :=
        extractPrevalid hpvE_full
      have hfv_αi_out : Term.fv αi ⊆ Ctx.dom (Γ₂ ++ Γ₁) := by
        cases hpv_full with
        | equ _ _ hfvαi _ => exact hfvαi
      have hy₀_αi : y₀ ∉ Term.fv αi := fun h' => hy₀_dom_out (hfv_αi_out h')
      have hy₀_st' : ∀ β ∈ st', y₀ ∉ Term.fv β :=
        _y₀_notin_stack_fv_of_notin_dom hpv_outer_st_only hy₀_dom_in
      -- y₀ ∉ fv (subst y (.fvar z) bd').
      have hy₀_neq_z : y₀ ≠ z := fun h => hy₀_dom_out (h ▸ hz_out)
      have hy₀_notin_subst_bd' : y₀ ∉ Term.fv (Term.subst y (.fvar z) bd') := by
        intro h_in
        have hsub := Term.fv_subst_subset y (.fvar z) bd' h_in
        rcases Finset.mem_union.mp hsub with h1 | h2
        · exact hy₀_fvbd' (Finset.mem_sdiff.mp h1).1
        · have : y₀ = z := by simpa [Term.fv] using h2
          exact hy₀_neq_z this
      have ren := _MEqRed_rename_equ_no_fv hyz hy₀_dom_out hyf_dom hy₀_αi
        hy₀_fvbd hy₀_notin_subst_bd' hy₀_st' ihbody_y₀_norm
      simpa using ren
    | cons b stl =>
      -- s_tmpl.map (·^[y]) ++ s_outer = b^[y] :: (stl.map (·^[y]) ++ s_outer) = αi :: st'.
      -- Hence αi = b^[y] and st' = stl.map (·^[y]) ++ s_outer.
      have hst_cons : b^[y] :: (stl.map (·^[y]) ++ s_outer) = αi :: st' := by
        simpa [List.map_cons] using hst_eq
      have hαi_eq : αi = b^[y] := by
        have := List.head_eq_of_cons_eq hst_cons
        exact this.symm
      have hst'_eq : st' = stl.map (·^[y]) ++ s_outer :=
        (List.tail_eq_of_cons_eq hst_cons).symm
      -- LC b → b^[y] = b (and b^[z] = b).
      have hLC_b : Term.LC b := hLC_stmpl b (List.mem_cons_self _ _)
      have hb_open_y : b^[y] = b := Term.opening_lc hLC_b (.fvar y)
      have hb_open_z : b^[z] = b := Term.opening_lc hLC_b (.fvar z)
      -- αi-freshness: y ∉ fv b (from hy_stmpl).
      have hy_b : y ∉ Term.fv b := hy_stmpl b (List.mem_cons_self _ _)
      have hy_αi : y ∉ Term.fv αi := by rw [hαi_eq, hb_open_y]; exact hy_b
      -- Tail freshness data.
      have hLC_stmpl_tail : ∀ b' ∈ stl, Term.LC b' := fun b' hb' =>
        hLC_stmpl b' (List.mem_cons_of_mem _ hb')
      have hy_stmpl_tail : ∀ b' ∈ stl, y ∉ Term.fv b' := fun b' hb' =>
        hy_stmpl b' (List.mem_cons_of_mem _ hb')
      -- Extend Γ₂_avoid with αi entry.
      have hΓ₂'_avoid : Ctx.AvoidsBoundFv (⟨y₀, αi, .equ⟩ :: Γ₂) y :=
        Ctx.AvoidsBoundFv_cons.mpr ⟨hy_αi, hΓ₂_avoid⟩
      have hz_out_ext : z ∈ Ctx.dom ((⟨y₀, αi, .equ⟩ :: Γ₂) ++ Γ₁) := by
        simp [Ctx.dom_append, Ctx.dom_cons] at hz_out ⊢
        tauto
      -- Recurse on hbody y₀ at extended Γ₂', s_tmpl' = stl, s_outer' = s_outer.
      -- Need st' = stl.map (·^[y]) ++ s_outer (already have hst'_eq).
      have hctx_eq_body :
          ((⟨y₀, αi, .equ⟩ :: Γ₂) ++ ⟨y, α, .equ⟩ :: Γ₁ : Ctx) =
            ⟨y₀, αi, .equ⟩ :: (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁) := by simp
      have hst_body : stl.map (·^[y]) ++ s_outer = st' := hst'_eq.symm
      have ihbody_y₀ :=
        ihbody y₀ hy₀L (Γ₂ := ⟨y₀, αi, .equ⟩ :: Γ₂)
          (s_tmpl := stl) (s_outer := s_outer)
          (hΓ₂_avoid := hΓ₂'_avoid) (hLC_stmpl := hLC_stmpl_tail)
          (hy_stmpl := hy_stmpl_tail) (hy_souter := hy_souter)
          (hAvoid := hAvoid_body) (hFresh := hFresh_body)
          (hy_src := hy_bd_y₀)
          (hz_out := hz_out_ext) hctx_eq_body.symm hst_body
      have ihbody_y₀_norm :
          MEqRed (⟨y₀, αi, .equ⟩ :: (Γ₂ ++ Γ₁)) (stl.map (·^[z]) ++ s_outer)
            (bd^[y₀]) (Term.subst y (.fvar z) (bd'^[y₀])) := by
        simpa using ihbody_y₀
      have hsubst_open_bd' :
          Term.subst y (.fvar z) (bd'^[y₀]) = (Term.subst y (.fvar z) bd')^[y₀] :=
        Term.subst_open_var hy₀_neq_y.symm hLC_z bd'
      rw [hsubst_open_bd'] at ihbody_y₀_norm
      -- Goal stack: (b :: stl).map (·^[z]) ++ s_outer = b^[z] :: (stl.map (·^[z]) ++ s_outer)
      --   = b :: (stl.map (·^[z]) ++ s_outer) = αi :: (stl.map (·^[z]) ++ s_outer)
      -- (last step uses αi = b^[y] = b).
      have hαi_eq_b : αi = b := by rw [hαi_eq, hb_open_y]
      have hgoal_stack :
          (b :: stl).map (·^[z]) ++ s_outer = αi :: (stl.map (·^[z]) ++ s_outer) := by
        simp [List.map_cons, hb_open_z, hαi_eq_b]
      rw [hgoal_stack]
      refine MEqRed.fOp (L ∪ Ctx.dom (Γ₂ ++ Γ₁) ∪ {y₀}) iht_norm ?_ trivial
      intro yfresh hyfresh
      simp only [Finset.mem_union, Finset.mem_singleton] at hyfresh
      push_neg at hyfresh
      obtain ⟨⟨hyfL, hyf_dom⟩, hyf_y₀⟩ := hyfresh
      have hyz : y₀ ≠ yfresh := fun h' => hyf_y₀ h'.symm
      -- y₀ ∉ fv αi: αi = b, b ∈ s_tmpl. Pull fv b from prevalidExt of fOp at outer.
      have hpvE_outer_full : PrevalidExt (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁) (αi :: st') :=
        MEqRed.prevalidExt (MEqRed.fOp L ht hbody trivial)
      have hpv_outer_st_only : PrevalidExt (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁) st' := by
        cases hpvE_outer_full with
        | cons hpv_tail _ _ => exact hpv_tail
      -- αi's fv ⊆ outer dom (after equ-head removal under hy_αi). Pull from
      -- inner body's PrevalidExt's head (at extended ctx).
      have hpvE_full : PrevalidExt (⟨y₀, αi, .equ⟩ :: (Γ₂ ++ Γ₁))
                                    (stl.map (·^[z]) ++ s_outer) :=
        MEqRed.prevalidExt ihbody_y₀_norm
      have hpv_full : Prevalid (⟨y₀, αi, .equ⟩ :: (Γ₂ ++ Γ₁)) :=
        extractPrevalid hpvE_full
      have hfv_αi_out : Term.fv αi ⊆ Ctx.dom (Γ₂ ++ Γ₁) := by
        cases hpv_full with
        | equ _ _ hfvαi _ => exact hfvαi
      have hy₀_αi : y₀ ∉ Term.fv αi := fun h' => hy₀_dom_out (hfv_αi_out h')
      -- Stack freshness for y₀: use OUTER PrevalidExt at outer ctx for tail st'.
      have hy₀_st' : ∀ β ∈ st', y₀ ∉ Term.fv β :=
        _y₀_notin_stack_fv_of_notin_dom hpv_outer_st_only hy₀_dom_in
      -- st' = stl.map (·^[y]) ++ s_outer (from hst'_eq). The shape we need is
      -- on stl.map (·^[z]) ++ s_outer. But all these stack entries are y-fresh
      -- and y₀-fresh in BOTH shapes, since:
      --   * For β ∈ s_outer, y₀ ∉ fv β follows from hy₀_st' on β ∈ st'
      --     (since s_outer ⊆ st').
      --   * For β ∈ stl.map (·^[z]), β = b'^[z] with b' ∈ stl. b'^[y] ∈ st'
      --     is y₀-fresh, and b'^[z] = b' = b'^[y] (b' LC). Hence y₀-fresh.
      have hy₀_stk : ∀ β ∈ stl.map (·^[z]) ++ s_outer, y₀ ∉ Term.fv β := by
        intro β hβ
        rcases List.mem_append.mp hβ with hL | hR
        · -- β = b'^[z] for some b' ∈ stl, b' LC.
          rcases List.mem_map.mp hL with ⟨b', hb'_in, hβ_eq⟩
          have hLC_b' : Term.LC b' := hLC_stmpl_tail b' hb'_in
          have hb'_open : b'^[z] = b' := Term.opening_lc hLC_b' (.fvar z)
          have hb'_open_y : b'^[y] = b' := Term.opening_lc hLC_b' (.fvar y)
          -- b'^[y] ∈ stl.map (·^[y]) ⊆ st'.
          have hb'_y_in_st' : b'^[y] ∈ st' := by
            rw [hst'_eq]
            exact List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨b', hb'_in, rfl⟩))
          have : y₀ ∉ Term.fv (b'^[y]) := hy₀_st' (b'^[y]) hb'_y_in_st'
          rw [hb'_open_y] at this
          rw [← hβ_eq, hb'_open]
          exact this
        · -- β ∈ s_outer ⊆ st'.
          have hβ_in_st' : β ∈ st' := by
            rw [hst'_eq]
            exact List.mem_append.mpr (Or.inr hR)
          exact hy₀_st' β hβ_in_st'
      have hy₀_neq_z : y₀ ≠ z := fun h => hy₀_dom_out (h ▸ hz_out)
      have hy₀_notin_subst_bd' : y₀ ∉ Term.fv (Term.subst y (.fvar z) bd') := by
        intro h_in
        have hsub := Term.fv_subst_subset y (.fvar z) bd' h_in
        rcases Finset.mem_union.mp hsub with h1 | h2
        · exact hy₀_fvbd' (Finset.mem_sdiff.mp h1).1
        · have : y₀ = z := by simpa [Term.fv] using h2
          exact hy₀_neq_z this
      have ren := _MEqRed_rename_equ_no_fv hyz hy₀_dom_out hyf_dom hy₀_αi
        hy₀_fvbd hy₀_notin_subst_bd' hy₀_stk ihbody_y₀_norm
      simpa using ren

/-! ### §11.10 — `MEqRed.descend_body_equ_uniform` assembly (iter-26)

The unified template-aware descent functor for the body of an equ-bound
sub-derivation. Dispatches on body's syntactic shape via `match body`.

* **`body = .bvar 0`**: source = `.fvar y`. Uses iter-18's
  `descend_body_equ_uniform_bvar0` leaf.
* **`body = .bvar (n+1)`**: source = `.bvar (n+1)`. Vacuous: no `MEqRed`
  constructor admits a `.bvar` source.
* **`body = .top`**: source = `.top`, y-fresh. Delegate to
  `descend_y_fresh_source_template` at `Γ₂ = []`.
* **`body = .fvar w`** (w ≠ y from `hy_body`): source = `.fvar w`,
  y-fresh. Delegate to `descend_y_fresh_source_template`. The
  previously-blocked pro-arm is handled internally by the y-fresh-
  source descent.
* **`body = .app a b`**: gated behind `Empty` premise `hgate_app`.
  Reason: extending the template with `b` requires `LC b`, but `b`
  need not be LC (only `b^[y]` is, from the PrevalidExt of the
  underlying `MEqRed.app`). The architectural fix needs either
  (i) a strengthened signature with `LC body` as a premise — natural
  for the headline consumer where bodies arise from `.abs`-bound
  positions and are LC modulo bvar 0 — or (ii) an opened-template
  variant that tracks templates as already-opened terms. Iter-27
  picks one and ships.
* **`body = .abs t inner`**: gated behind `Empty` premise `hgate_abs`.
  Reason: opening at depth 1 inside `.abs`'s body requires depth-shift
  handling not yet developed.

### Why no .app/.tAp or .app/.bet sub-arms

These constructor cases can only fire when `body = .app a b` AND
`a^[y]` matches the constructor's source-shape constraint. Once we
gate the entire `.app` body shape, the constructor sub-cases are
subsumed.

### Termination

The function does NOT recurse — every arm delegates to a previously-
shipped helper (via §11.7's leaves and §11.9's full functor) or to
an `Empty` gate. The iter-19 prompt's mention of well-founded
recursion on `Term.size body` applies only when the `.app`/`.abs`
arms recurse; with both gated, the function is non-recursive. -/

/-- **Iter-26 — assembled `descend_body_equ_uniform` functor.**

Top-level dispatcher matching on `body`'s shape. Each shape is either
delegated to an existing leaf/full-functor helper or gated behind an
`Empty` premise (`hgate_app`, `hgate_abs`).

Closed-form `match body` returning a function — so each match arm sees
`h : MEqRed _ _ ((shape)^[y]) _` typed at the SPECIFIC opened body
shape, allowing the leaves' direct use. -/
noncomputable def MEqRed.descend_body_equ_uniform
    {Γ : Ctx} {s_outer : Stack} {y : String} {α : Term}
    (body : Term)
    (s_tmpl : List Term)
    (hLC_stmpl : ∀ b ∈ s_tmpl, Term.LC b)
    (hy_body : y ∉ Term.fv body)
    (hy_stmpl : ∀ b ∈ s_tmpl, y ∉ Term.fv b)
    (hy_souter : ∀ β ∈ s_outer, y ∉ Term.fv β)
    (hy_Γ : y ∉ Γ.dom)
    (z : String) (hz_Γ : z ∈ Γ.dom)
    -- Gates for cases not yet shipped end-to-end.
    (hgate_app : ∀ a b : Term, body = .app a b → Empty)
    (hgate_abs : ∀ t inner : Term, body = .abs t inner → Empty) :
    {target_y : Term} →
    (h : MEqRed (⟨y, α, .equ⟩ :: Γ) (s_tmpl.map (·^[y]) ++ s_outer)
                (body^[y]) target_y) →
    avoidsPro h y = true →
    cofinDomFresh h = true →
    MEqRed Γ (s_tmpl.map (·^[z]) ++ s_outer) (body^[z])
              (Term.subst y (.fvar z) target_y) := by
  classical
  match body, hy_body with
  | .bvar 0, _hy_body =>
    intro target_y h hAvoid _hFresh
    exact MEqRed.descend_body_equ_uniform_bvar0 s_tmpl h hAvoid
            hy_stmpl hy_souter hy_Γ z hz_Γ
  | .bvar (n+1), _hy_body =>
    intro target_y h _hAvoid _hFresh
    -- Source = .bvar (n+1) (opening at depth 0 doesn't change it). No MEqRed
    -- constructor has a .bvar source — vacuous via cases.
    have hopen : (Term.bvar (n+1) : Term)^[y] = .bvar (n+1) := by
      simp [Term.opening, Term.open_]
    rw [hopen] at h
    -- Generalize the stack to make cases work without dep-elim glitches.
    generalize hst_eq : s_tmpl.map (·^[y]) ++ s_outer = stk at h
    cases h
  | .top, _hy_body =>
    intro target_y h hAvoid hFresh
    -- (Term.top)^[y] = .top and (Term.top)^[z] = .top are definitional.
    show MEqRed Γ (s_tmpl.map (·^[z]) ++ s_outer) (.top : Term)
                 (Term.subst y (.fvar z) target_y)
    have hΓ₂_avoid : Ctx.AvoidsBoundFv ([] : Ctx) y := Ctx.AvoidsBoundFv_nil y
    have hy_top : y ∉ Term.fv (.top : Term) := by simp [Term.fv]
    have hz_out : z ∈ Ctx.dom (([] : Ctx) ++ Γ) := by simpa using hz_Γ
    -- Pass h directly (input ctx Γ is def-eq to [] ++ Γ).
    have hres := MEqRed.descend_y_fresh_source_template (Γ₂ := ([] : Ctx)) (Γ₁ := Γ)
                  s_tmpl h hΓ₂_avoid hAvoid hFresh hLC_stmpl
                  hy_stmpl hy_souter hy_Γ hy_top z hz_out
    simpa using hres
  | .fvar w, hy_body =>
    intro target_y h hAvoid hFresh
    have hwy : w ≠ y := by
      intro heq
      apply hy_body
      simp [Term.fv, heq]
    -- (Term.fvar w)^[y] = .fvar w and (Term.fvar w)^[z] = .fvar w are definitional.
    show MEqRed Γ (s_tmpl.map (·^[z]) ++ s_outer) (.fvar w)
                 (Term.subst y (.fvar z) target_y)
    have hΓ₂_avoid : Ctx.AvoidsBoundFv ([] : Ctx) y := Ctx.AvoidsBoundFv_nil y
    have hy_fvarw : y ∉ Term.fv (.fvar w : Term) := by
      simp [Term.fv]; exact fun heq => hwy heq.symm
    have hz_out : z ∈ Ctx.dom (([] : Ctx) ++ Γ) := by simpa using hz_Γ
    have hres := MEqRed.descend_y_fresh_source_template (Γ₂ := ([] : Ctx)) (Γ₁ := Γ)
                  s_tmpl h hΓ₂_avoid hAvoid hFresh hLC_stmpl
                  hy_stmpl hy_souter hy_Γ hy_fvarw z hz_out
    simpa using hres
  | .app a b, _hy_body =>
    intro target_y h _hAvoid _hFresh
    exact (hgate_app a b rfl).elim
  | .abs t inner, _hy_body =>
    intro target_y h _hAvoid _hFresh
    exact (hgate_abs t inner rfl).elim

end Pss

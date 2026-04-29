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
private theorem prevalid_rename_sub_head
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
private theorem prevalidExt_rename_sub_head
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
  | @bet Γ st' tBound v0 v0' bd bd' L hLCt hbody hv ihbody ihv =>
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
    refine MEqRed.bet (L ∪ {y}) (Term.subst_lc hLCfz hLCt) ?_ ?_
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
  | @fun_ Γ tt tt' bd bd' L ht hbody iht ihbody =>
    subst hΓ
    intro hz_notin_Γ₂
    show MEqRed (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, t, .sub⟩ :: Γ₁)
      (Stack.subst y (.fvar z) [])
      (.abs (Term.subst y (.fvar z) tt) (Term.subst y (.fvar z) bd))
      (.abs (Term.subst y (.fvar z) tt') (Term.subst y (.fvar z) bd'))
    refine MEqRed.fun_ (L ∪ {y} ∪ {z}) ?_ ?_
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
  | @fOp Γ st' tt tt' αi bd bd' L ht hbody iht ihbody =>
    subst hΓ
    intro hz_notin_Γ₂
    show MEqRed (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, t, .sub⟩ :: Γ₁)
      (Stack.subst y (.fvar z) (αi :: st'))
      (.abs (Term.subst y (.fvar z) tt) (Term.subst y (.fvar z) bd))
      (.abs (Term.subst y (.fvar z) tt') (Term.subst y (.fvar z) bd'))
    rw [Stack.subst_cons]
    refine MEqRed.fOp (L ∪ {y} ∪ {z}) ?_ ?_
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
  | @bet Γ st' tBound v0 v0' bd bd' L hLCt hbody hv ihbody ihv =>
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
    refine MEqRed.bet (L ∪ {y}) (Term.subst_lc hLCfz hLCt) ?_ ?_
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
  | @fun_ Γ tt tt' bd bd' L ht hbody iht ihbody =>
    subst hΓ
    show MEqRed (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, α, .equ⟩ :: Γ₁)
      (Stack.subst y (.fvar z) [])
      (.abs (Term.subst y (.fvar z) tt) (Term.subst y (.fvar z) bd))
      (.abs (Term.subst y (.fvar z) tt') (Term.subst y (.fvar z) bd'))
    refine MEqRed.fun_ (L ∪ {y}) ?_ ?_
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
  | @fOp Γ st' tt tt' αi bd bd' L ht hbody iht ihbody =>
    subst hΓ
    show MEqRed (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, α, .equ⟩ :: Γ₁)
      (Stack.subst y (.fvar z) (αi :: st'))
      (.abs (Term.subst y (.fvar z) tt) (Term.subst y (.fvar z) bd))
      (.abs (Term.subst y (.fvar z) tt') (Term.subst y (.fvar z) bd'))
    rw [Stack.subst_cons]
    refine MEqRed.fOp (L ∪ {y}) ?_ ?_
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
  | @fun_ Γ tt bd bd' L hLCt hbody ihbody =>
    subst hΓ
    intro hz_notin_Γ₂
    show MSubRed (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, t, .sub⟩ :: Γ₁)
      (Stack.subst y (.fvar z) [])
      (Term.subst y (.fvar z) (.abs tt bd)) (Term.subst y (.fvar z) (.abs tt bd'))
    simp [Term.subst]
    refine MSubRed.fun_ (L ∪ {y} ∪ {z}) (Term.subst_lc (Term.LC.fvar z) hLCt) ?_
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
  | @fOp Γ st' tt αi bd bd' L hLCt hbody ihbody =>
    subst hΓ
    intro hz_notin_Γ₂
    show MSubRed (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, t, .sub⟩ :: Γ₁)
      (Stack.subst y (.fvar z) (αi :: st'))
      (Term.subst y (.fvar z) (.abs tt bd)) (Term.subst y (.fvar z) (.abs tt bd'))
    rw [Stack.subst_cons]
    simp [Term.subst]
    refine MSubRed.fOp (L ∪ {y} ∪ {z}) (Term.subst_lc (Term.LC.fvar z) hLCt) ?_
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
  | @fun_ Γ tt bd bd' L hLCt hbody ihbody =>
    subst hΓ
    show MSubRed (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, α, .equ⟩ :: Γ₁)
      (Stack.subst y (.fvar z) [])
      (Term.subst y (.fvar z) (.abs tt bd)) (Term.subst y (.fvar z) (.abs tt bd'))
    simp [Term.subst]
    refine MSubRed.fun_ (L ∪ {y}) (Term.subst_lc (Term.LC.fvar z) hLCt) ?_
    intro yfresh hyfresh
    simp [Finset.mem_union, Finset.mem_singleton] at hyfresh
    have hyfL : yfresh ∉ L := hyfresh.1
    have hyfy : yfresh ≠ y := hyfresh.2
    have ih_body := ihbody yfresh hyfL (Γ₂ := ⟨yfresh, tt, .sub⟩ :: Γ₂) (by simp)
    rw [Term.subst_open_var (Ne.symm hyfy) (Term.LC.fvar z) bd,
        Term.subst_open_var (Ne.symm hyfy) (Term.LC.fvar z) bd'] at ih_body
    simpa [Ctx.subst, List.cons_append] using ih_body
  | @fOp Γ st' tt αi bd bd' L hLCt hbody ihbody =>
    subst hΓ
    show MSubRed (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, α, .equ⟩ :: Γ₁)
      (Stack.subst y (.fvar z) (αi :: st'))
      (Term.subst y (.fvar z) (.abs tt bd)) (Term.subst y (.fvar z) (.abs tt bd'))
    rw [Stack.subst_cons]
    simp [Term.subst]
    refine MSubRed.fOp (L ∪ {y}) (Term.subst_lc (Term.LC.fvar z) hLCt) ?_
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

end Pss

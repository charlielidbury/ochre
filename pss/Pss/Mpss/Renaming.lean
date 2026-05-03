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
  | @fun_ Γ tt tt' bd bd' L ht hbody iht ihbody =>
    subst hΓ
    show MEqRed (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, α, .equ⟩ :: Γ₁)
      (Stack.subst y (.fvar z) [])
      (.abs (Term.subst y (.fvar z) tt) (Term.subst y (.fvar z) bd))
      (.abs (Term.subst y (.fvar z) tt') (Term.subst y (.fvar z) bd'))
    refine MEqRed.fun_ (L ∪ {y} ∪ {z}) ?_ ?_
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
  | @fOp Γ st' tt tt' αi bd bd' L ht hbody iht ihbody =>
    subst hΓ
    show MEqRed (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, α, .equ⟩ :: Γ₁)
      (Stack.subst y (.fvar z) (αi :: st'))
      (.abs (Term.subst y (.fvar z) tt) (Term.subst y (.fvar z) bd))
      (.abs (Term.subst y (.fvar z) tt') (Term.subst y (.fvar z) bd'))
    rw [Stack.subst_cons]
    refine MEqRed.fOp (L ∪ {y} ∪ {z}) ?_ ?_
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
  | @fun_ Γ tt bd bd' L hLCt hbody ihbody =>
    subst hΓ
    show MSubRed (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, α, .equ⟩ :: Γ₁)
      (Stack.subst y (.fvar z) [])
      (Term.subst y (.fvar z) (.abs tt bd)) (Term.subst y (.fvar z) (.abs tt bd'))
    simp [Term.subst]
    refine MSubRed.fun_ (L ∪ {y} ∪ {z}) (Term.subst_lc (Term.LC.fvar z) hLCt) ?_
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
  | @fOp Γ st' tt αi bd bd' L hLCt hbody ihbody =>
    subst hΓ
    show MSubRed (Ctx.subst y (.fvar z) Γ₂ ++ ⟨z, α, .equ⟩ :: Γ₁)
      (Stack.subst y (.fvar z) (αi :: st'))
      (Term.subst y (.fvar z) (.abs tt bd)) (Term.subst y (.fvar z) (.abs tt bd'))
    rw [Stack.subst_cons]
    simp [Term.subst]
    refine MSubRed.fOp (L ∪ {y} ∪ {z}) (Term.subst_lc (Term.LC.fvar z) hLCt) ?_
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
  | @bet Γ st' tBound v0 v0' bd bd' L hLCt hbody hv ihbody ihv =>
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
    refine MEqRed.bet (L ∪ {y} ∪ {z}) (Term.subst_lc hLCfz hLCt) ?_ ?_
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
  | @fun_ Γ tt tt' bd bd' L ht hbody iht ihbody =>
    intro hy_notin_Γ
    show MEqRed (Ctx.subst y (.fvar z) Γ) (Stack.subst y (.fvar z) [])
      (Term.subst y (.fvar z) (.abs tt bd)) (Term.subst y (.fvar z) (.abs tt' bd'))
    simp [Term.subst]
    refine MEqRed.fun_ (L ∪ {y} ∪ {z}) ?_ ?_
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
  | @fOp Γ st' tt tt' αi bd bd' L ht hbody iht ihbody =>
    intro hy_notin_Γ
    show MEqRed (Ctx.subst y (.fvar z) Γ) (Stack.subst y (.fvar z) (αi :: st'))
      (Term.subst y (.fvar z) (.abs tt bd)) (Term.subst y (.fvar z) (.abs tt' bd'))
    rw [Stack.subst_cons]
    simp [Term.subst]
    refine MEqRed.fOp (L ∪ {y} ∪ {z}) ?_ ?_
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
  | @fun_ Γ tt bd bd' L hLCt hbody ihbody =>
    intro hy_notin_Γ
    show MSubRed (Ctx.subst y (.fvar z) Γ) (Stack.subst y (.fvar z) [])
      (Term.subst y (.fvar z) (.abs tt bd)) (Term.subst y (.fvar z) (.abs tt bd'))
    simp [Term.subst]
    refine MSubRed.fun_ (L ∪ {y} ∪ {z}) (Term.subst_lc (Term.LC.fvar z) hLCt) ?_
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
  | @fOp Γ st' tt αi bd bd' L hLCt hbody ihbody =>
    intro hy_notin_Γ
    show MSubRed (Ctx.subst y (.fvar z) Γ) (Stack.subst y (.fvar z) (αi :: st'))
      (Term.subst y (.fvar z) (.abs tt bd)) (Term.subst y (.fvar z) (.abs tt bd'))
    rw [Stack.subst_cons]
    simp [Term.subst]
    refine MSubRed.fOp (L ∪ {y} ∪ {z}) (Term.subst_lc (Term.LC.fvar z) hLCt) ?_
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
  | @bet Γ st' tBound v0 v0' bd bd' L hLCt hbody hv ihbody ihv =>
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
      hLCt ?_ ihv'
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
  | @fun_ Γ tt tt' bd bd' L ht hbody iht ihbody =>
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
    refine MEqRed.fun_ (L ∪ Ctx.dom (Γ₂ ++ ⟨y, α', .equ⟩ :: Γ₁) ∪ {y₀}) iht' ?_
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
  | @fOp Γ st' tt tt' αi bd bd' L ht hbody iht ihbody =>
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
    refine MEqRed.fOp (L ∪ Ctx.dom (Γ₂ ++ ⟨y, α', .equ⟩ :: Γ₁) ∪ {y₀}) iht' ?_
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
      MEqRed.prevalidExt (MEqRed.fOp L ht hbody)
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
      exact MEqRed.prevalidExt (MEqRed.fOp L ht hbody)
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
  | @fun_ Γ tt bd bd' L hLCt hbody ihbody =>
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
    refine MSubRed.fun_ (L ∪ Ctx.dom (Γ₂ ++ ⟨y, α', .equ⟩ :: Γ₁) ∪ {y₀}) hLCt ?_
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
  | @fOp Γ st' tt αi bd bd' L hLCt hbody ihbody =>
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
    refine MSubRed.fOp (L ∪ Ctx.dom (Γ₂ ++ ⟨y, α', .equ⟩ :: Γ₁) ∪ {y₀}) hLCt ?_
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
      MSubRed.prevalidExt (MSubRed.fOp L hLCt hbody)
    have hpv_outer_st_only : PrevalidExt (Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁) st' := by
      cases hpv_outer_inputst with
      | cons hpv_tail _ _ => exact hpv_tail
    have hy₀_stack : ∀ β ∈ st', y₀ ∉ Term.fv β :=
      _y₀_notin_stack_fv_of_notin_dom hpv_outer_st_only hy₀_dom
    have ren := _MSubRed_rename_equ_no_fv hyz hy₀_dom' hyf_dom hy₀_αi
      hy₀_fvbd hy₀_fvbd' hy₀_stack ihbody_y₀_norm
    simpa using ren

end Pss

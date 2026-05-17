import Pss.Context.Logical
import Pss.Context.Stack

/-! # `Pss.Context.Prevalid` — pre-validity of contexts

Pre-validity is the structural well-formedness used in MPSS Fig. 1
(`Pv-Emp`, `Pv-Ctx`, `Pv-EqA`). It demands:

* names are fresh,
* free variables of bounds/equations are scoped by the prefix,
* bounds/equations are locally closed.

Hutchins' simpler PSS uses only `.sub` entries; MPSS uses both. The unified
`Prevalid` covers both — when restricted to `.sub`-only contexts it collapses
to Hutchins'.
-/

namespace Pss

/-- Pre-validity (MPSS Fig. 1).

`Type`-valued (post-Type-LC refactor): carries `Term.LC` witnesses
in its `sub`/`equ` constructors. -/
inductive Prevalid : Ctx → Type
  | empty : Prevalid []
  | sub {Γ : Ctx} {x : String} {t : Term} :
      Prevalid Γ →
      x ∉ Γ.dom →
      Term.fv t ⊆ Γ.dom →
      Term.LC t →
      Prevalid (⟨x, t, .sub⟩ :: Γ)
  | equ {Γ : Ctx} {x : String} {α : Term} :
      Prevalid Γ →
      x ∉ Γ.dom →
      Term.fv α ⊆ Γ.dom →
      Term.LC α →
      Prevalid (⟨x, α, .equ⟩ :: Γ)

/-- Pre-validity for an extended context `Γ ; s` (MPSS Fig. 1, Pv-Nil/Pv-Sta).

`Type`-valued (post-Type-LC refactor) since it carries `Term.LC`. -/
inductive PrevalidExt : Ctx → Stack → Type
  | nil {Γ : Ctx} : Prevalid Γ → PrevalidExt Γ []
  | cons {Γ : Ctx} {s : Stack} {α : Term} :
      PrevalidExt Γ s → Term.LC α → Term.fv α ⊆ Γ.dom →
      PrevalidExt Γ (α :: s)

/-! ## Structural lemmas -/

/-- Pre-validity implies distinctness of names. -/
theorem Prevalid.nodup {Γ : Ctx} (h : Prevalid Γ) : Ctx.NoDup Γ := by
  induction h with
  | empty => simp
  | @sub Γ x t hΓ hx _ _ ih =>
    rw [Ctx.NoDup_cons]
    refine ⟨?_, ih⟩
    intro hmem
    exact hx ((Ctx.mem_map_name_iff_mem_dom Γ x).mp hmem)
  | @equ Γ x α hΓ hx _ _ ih =>
    rw [Ctx.NoDup_cons]
    refine ⟨?_, ih⟩
    intro hmem
    exact hx ((Ctx.mem_map_name_iff_mem_dom Γ x).mp hmem)

/-- The tail of a pre-valid context is pre-valid.

`def` (since `Prevalid : Type` post-Type-LC refactor). -/
def Prevalid.tail {e : CtxEntry} {Γ : Ctx} (h : Prevalid (e :: Γ)) :
    Prevalid Γ := by
  cases h with
  | sub hΓ _ _ _ => exact hΓ
  | equ hΓ _ _ _ => exact hΓ

/-! ### `lookupSub` lemmas -/

/-- Free variables of a `.sub`-bound term are scoped by the whole context. -/
theorem Prevalid.fv_lookupSub {Γ : Ctx} {x : String} {t : Term}
    (h : Prevalid Γ) (hb : Γ.subBinds x t) : Term.fv t ⊆ Γ.dom := by
  induction h with
  | empty =>
    simp [Ctx.subBinds] at hb
  | @sub Γ' y u hΓ' hy hfv hlc ih =>
    simp [Ctx.subBinds, Ctx.lookupSub] at hb
    by_cases hyx : y = x
    · -- Innermost matches: t = u, and fv u ⊆ Γ'.dom ⊆ insert y Γ'.dom.
      simp [hyx] at hb
      subst hb
      intro z hz
      simp [Ctx.dom]
      exact Or.inr (hfv hz)
    · -- Recurse.
      simp [hyx] at hb
      have := ih hb
      intro z hz
      simp [Ctx.dom]
      exact Or.inr (this hz)
  | @equ Γ' y α hΓ' hy hfv hlc ih =>
    simp [Ctx.subBinds, Ctx.lookupSub] at hb
    by_cases hyx : y = x
    · -- Innermost is `.equ` with the matching name; lookupSub returns none.
      simp [hyx] at hb
    · simp [hyx] at hb
      have := ih hb
      intro z hz
      simp [Ctx.dom]
      exact Or.inr (this hz)

/-- A `.sub`-bound term is locally closed.

`noncomputable def` (since `Term.LC : Type`); inducts on Type-valued `Prevalid`. -/
noncomputable def Prevalid.lc_lookupSub {Γ : Ctx} {x : String} {t : Term}
    (h : Prevalid Γ) (hb : Γ.subBinds x t) : Term.LC t := by
  induction h with
  | empty =>
    simp [Ctx.subBinds] at hb
  | @sub Γ' y u hΓ' hy hfv hlc ih =>
    simp [Ctx.subBinds, Ctx.lookupSub] at hb
    by_cases hyx : y = x
    · simp [hyx] at hb
      subst hb
      exact hlc
    · simp [hyx] at hb
      exact ih hb
  | @equ Γ' y α hΓ' hy hfv hlc ih =>
    simp [Ctx.subBinds, Ctx.lookupSub] at hb
    by_cases hyx : y = x
    · simp [hyx] at hb
    · simp [hyx] at hb
      exact ih hb

/-! ### `lookupEqu` lemmas -/

/-- Free variables of an `.equ`-bound term are scoped by the whole context. -/
theorem Prevalid.fv_lookupEqu {Γ : Ctx} {x : String} {α : Term}
    (h : Prevalid Γ) (hb : Γ.equBinds x α) : Term.fv α ⊆ Γ.dom := by
  induction h with
  | empty =>
    simp [Ctx.equBinds] at hb
  | @sub Γ' y u hΓ' hy hfv hlc ih =>
    simp [Ctx.equBinds, Ctx.lookupEqu] at hb
    by_cases hyx : y = x
    · simp [hyx] at hb
    · simp [hyx] at hb
      have := ih hb
      intro z hz
      simp [Ctx.dom]
      exact Or.inr (this hz)
  | @equ Γ' y β hΓ' hy hfv hlc ih =>
    simp [Ctx.equBinds, Ctx.lookupEqu] at hb
    by_cases hyx : y = x
    · simp [hyx] at hb
      subst hb
      intro z hz
      simp [Ctx.dom]
      exact Or.inr (hfv hz)
    · simp [hyx] at hb
      have := ih hb
      intro z hz
      simp [Ctx.dom]
      exact Or.inr (this hz)

/-- An `.equ`-bound term is locally closed.

`noncomputable def` (since `Term.LC : Type`); inducts on Type-valued `Prevalid`. -/
noncomputable def Prevalid.lc_lookupEqu {Γ : Ctx} {x : String} {α : Term}
    (h : Prevalid Γ) (hb : Γ.equBinds x α) : Term.LC α := by
  induction h with
  | empty =>
    simp [Ctx.equBinds] at hb
  | @sub Γ' y u hΓ' hy hfv hlc ih =>
    simp [Ctx.equBinds, Ctx.lookupEqu] at hb
    by_cases hyx : y = x
    · simp [hyx] at hb
    · simp [hyx] at hb
      exact ih hb
  | @equ Γ' y β hΓ' hy hfv hlc ih =>
    simp [Ctx.equBinds, Ctx.lookupEqu] at hb
    by_cases hyx : y = x
    · simp [hyx] at hb
      subst hb
      exact hlc
    · simp [hyx] at hb
      exact ih hb

end Pss

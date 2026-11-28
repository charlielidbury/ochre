import Ochr.Meaning.Conv.Sound

/-!
# (H3) the unit laws on plain values, from the library's connectives (conv1, 2026-11-28)

`UnitOk K ρ φ Plain` from `LibOk` and one fact of the data model, that `And`'s two parameters are
propositions (`AndParams`; for the `Prelude`'s model `PreludeModel.paramTy_and`, in general
`ParamsFaithful` at `And`). A plain value's meaning does not depend on the hint it is read at (no
sealed program, no constructor value), which the law needs: `And`'s arguments are typed at `Prop`
inside it and read at the outer hint after the law.
-/

namespace Ochr.Meaning.Conv
open Ochr Ochr.Meaning Ochr.Meaning.Strict

/-- (M) The program's `And` takes two propositions. -/
def AndParams (K : RunCtx) : Prop :=
  ∀ d, K.Γ.find? (·.name == "And") = some d → ∀ i e, i < 2 → K.dm.paramTy d i e = TyM.univ 0

section
variable {K : RunCtx} {ρ : Assignment} {φ : Future}

/-- A plain value means the same at every hint. -/
theorem plain_hint : ∀ {v : Value}, Plain v → ∀ h h', meanV K ρ φ h v = meanV K ρ φ h' v
  | _, .zero, _, _ | _, .unit, _, _ | _, .gfn _, _, _ | _, .loan _, _, _ | _, .bot, _, _
  | _, .abs _, _, _ | _, .proof, _, _ | _, .tNat, _, _ | _, .tUnit, _, _ | _, .sort _, _, _
  | _, .succ _, _, _ | _, .tRef _, _, _ | _, .tEq _ _ _, _, _ | _, .tInd _, _, _ => rfl
  | _, .borrow pa, h, h' => plain_hint pa h h'
  | _, .gloan pa, h, h' => plain_hint pa h h'

theorem mem_univ0' {v : Sem} (h : v ∈ₛ[K.dm.read] TyM.univ 0) : ∃ P : Prop, v = .ty (TyM.prop P) := by
  obtain ⟨⟨P⟩, he⟩ := h
  exact ⟨P, he.symm⟩

theorem prop_inj' {p q : Prop} (h : Sem.ty (TyM.prop p) = Sem.ty (TyM.prop q)) : p = q := by
  simp only [Sem.ty.injEq] at h
  unfold TyM.prop at h
  injection h with hA hc
  exact Code0.congr_heq Code0.propOf _ _ hA hc

/-- **(H3) PROVED on plain values**, from the library's connectives (`LibOk`) and `And`'s parameters
being propositions (`AndParams`). -/
theorem unitOk_plain (hl : LibOk K ρ φ) (ha : AndParams K) : UnitOk K ρ φ Plain := by
  refine ⟨fun h T v pv nv fv => ?_⟩
  induction v using unitTop.induct generalizing h T with
  | case1 p q ihp ihq =>
    cases pv with
    | tInd hs =>
    have pp : Plain p := hs p (by simp)
    have pq : Plain q := hs q (by simp)
    have np : NoProp K p := nv.1
    have nq : NoProp K q := nv.2.1
    rcases meanV_tInd_cases K ρ φ h "And" [p, q] with he | ⟨d, hd, hpk⟩
    · rw [he] at fv; exact absurd fv ty_err_not_fit
    have m0 := hpk 0 _ rfl
    have m1 := hpk 1 _ rfl
    have m0' : meanV K ρ φ (.plain (K.dm.paramTy d 0 [])) p ∈ₛ[K.dm.read] TyM.univ 0 := by
      have e := ha d hd 0 ((meanParams K ρ φ d 0 [] [p, q]).take 0) (by decide)
      rw [e] at m0; exact m0
    have m1' : ∃ hq, meanV K ρ φ hq q ∈ₛ[K.dm.read] TyM.univ 0 := by
      have e := ha d hd 1 ((meanParams K ρ φ d 0 [] [p, q]).take 1) (by decide)
      rw [e] at m1; exact ⟨_, m1⟩
    obtain ⟨p', hp'⟩ := mem_univ0' m0'
    obtain ⟨hq₀, m1''⟩ := m1'
    obtain ⟨q', hq'⟩ := mem_univ0' m1''
    have ep : ∀ h₀, meanV K ρ φ h₀ p = .ty (TyM.prop p') := fun h₀ => (plain_hint pp h₀ _).trans hp'
    have eq : ∀ h₀, meanV K ρ φ h₀ q = .ty (TyM.prop q') := fun h₀ => (plain_hint pq h₀ _).trans hq'
    obtain ⟨np', eup⟩ := ihp (.plain (TyM.univ 0)) (TyM.univ 0) pp np
      (.inr (.inl (by rw [ep]; exact ty_univ0_mem p')))
    obtain ⟨nq', euq⟩ := ihq (.plain (TyM.univ 0)) (TyM.univ 0) pq nq
      (.inr (.inl (by rw [eq]; exact ty_univ0_mem q')))
    have up : ∀ h₀, meanV K ρ φ h₀ (unitTop p) = .ty (TyM.prop p') := fun h₀ =>
      (plain_hint (pp.unitTop) h₀ _).trans (eup.trans (ep _))
    have uq : ∀ h₀, meanV K ρ φ h₀ (unitTop q) = .ty (TyM.prop q') := fun h₀ =>
      (plain_hint (pq.unitTop) h₀ _).trans (euq.trans (eq _))
    have hand := hl.and p q p' q' ep eq h
    rw [Ochr.unitTop, hand]
    unfold Ochr.mkAnd
    split
    · rename_i hT
      have e1 : p' = True := prop_inj' ((up (.plain TyM.err)).symm.trans (by rw [hT]; exact hl.tru _))
      subst e1
      refine ⟨nq', ?_⟩
      rw [uq]
      congr 2
      exact propext ⟨fun hq => ⟨trivial, hq⟩, fun hq => hq.2⟩
    · rename_i hT _
      have e1 : q' = True := prop_inj' ((uq (.plain TyM.err)).symm.trans (by rw [hT]; exact hl.tru _))
      subst e1
      refine ⟨np', ?_⟩
      rw [up]
      congr 2
      exact propext ⟨fun hp => ⟨hp, trivial⟩, fun hp => hp.1⟩
    · exact ⟨⟨np', nq', trivial⟩, hl.and _ _ p' q' up uq h⟩
  | case2 v hv =>
    rw [Ochr.unitTop.eq_2 v hv]
    exact ⟨nv, rfl⟩

end

end Ochr.Meaning.Conv

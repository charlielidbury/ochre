import Ochr.Meaning.Steps.FragLet

/-!
# The fragment's `u; w` (lead11)

The first part's value dropped: a number or `()` ends nothing (`SeqInv`, proved by the machine lane;
`seqI_core` here); a borrow is ended by the drop (`SeqBorInv`; `FragSeqB.seqB_core`).
-/

namespace Ochr.Meaning.Steps.Form

open Ochr Ochr.Meaning Ochr.Meaning.Steps
open Classical

/-- **A fragment state with a number or `()` in flight is a fragment state without it.** -/
theorem FStT.untemp {Γ : List FT} {st : MState} {v : Value} {T? : Option Value}
    (hF : FStT Γ (st.withTempT v T?)) (hv : v.Num ∨ v = .unit) : FSt Γ st := by
  have hne : 0 < st.env.size := by have := hF.frame; rwa [size_withTempT] at this
  obtain ⟨fr, hfr⟩ : ∃ fr, st.env[st.env.size - 1]? = some fr :=
    ⟨_, Array.getElem?_eq_getElem (by omega : st.env.size - 1 < st.env.size)⟩
  have hWpos : allPos (st.withTempT v T?).env = allPos st.env ++ [.temp (st.env.size - 1) fr.temps.size] := by
    rw [allPos_withTempT, allPos_pushTempE _ _ fr hfr hne]
  have hWnew : valAt (st.withTempT v T?).env (.temp (st.env.size - 1) fr.temps.size) = v := by
    rw [valAt_withTempT, valAt_pushTempE_new _ _ fr hfr]
  have hntq : ∀ q, q ∈ allPos st.env → q ≠ .temp (st.env.size - 1) fr.temps.size := fun q hq e => by
    rw [e] at hq; obtain ⟨fr', hf', hi⟩ := mem_allPos_temp st.env _ _ hq
    rw [hfr] at hf'; cases hf'; exact absurd hi (Nat.lt_irrefl _)
  have hWold : ∀ q, q ∈ allPos st.env → valAt (st.withTempT v T?).env q = valAt st.env q := by
    intro q hq; rw [valAt_withTempT]
    cases q with
    | bind f i => exact valAt_pushTempE_bind _ _ f i
    | temp f i => exact valAt_pushTempE_old _ _ fr hfr f i (hntq _ hq)
  have hWmem : ∀ q, q ∈ allPos st.env → q ∈ allPos (st.withTempT v T?).env := fun q hq => by
    rw [hWpos]; exact List.mem_append_left _ hq
  have hWcases : ∀ q, q ∈ allPos (st.withTempT v T?).env → q = .temp (st.env.size - 1) fr.temps.size ∨ q ∈ allPos st.env := by
    intro q hq; rw [hWpos, List.mem_append, List.mem_singleton] at hq; exact hq.symm
  have hfrW : (st.withTempT v T?).env[(st.withTempT v T?).env.size - 1]? =
      some { fr with temps := fr.temps.push v, tempTys := fr.tempTys.push T? } := by
    simp only [MState.withTempT, Array.size_modify, Array.getElem?_modify, if_true, hfr]; rfl
  have hvnb : ∀ l c, v ≠ .borrow l c := fun l c e => by
    rcases hv with h | h
    · rw [e] at h; cases h
    · rw [e] at h; cases h
  have hvnl : ∀ m, v ≠ .loan m := fun m e => by
    rcases hv with h | h
    · rw [e] at h; cases h
    · rw [e] at h; cases h
  -- a borrow at an old position is at a binding
  have hbind : ∀ q l c, q ∈ allPos st.env → valAt st.env q = .borrow l c → ∃ f j, q = .bind f j := by
    intro q l c hq e
    cases q with
    | bind f j => exact ⟨f, j, rfl⟩
    | temp f i =>
      obtain ⟨h1, h2⟩ := hF.tempLast f i l c (hWmem _ hq) (by rw [hWold _ hq]; exact e) _ hfrW
      rw [size_withTempT] at h1
      simp only [Array.size_push] at h2
      exact absurd (by rw [h1, h2]; rfl) (hntq _ hq)
  refine ⟨fun q hq => ?_, fun f i hq => ?_, fun q q' l hq hq' e e' => ?_, fun q q' l w w' hq hq' e e' => ?_,
    fun q l hq e => ?_, fun q l c hq e => ?_, fun i B hi => ?_, fun f j f' j' l c hq hq' e e' => ?_,
    fun f j b l hb e => ?_, hne⟩
  · rw [← hWold q hq]; exact hF.vals q (hWmem q hq)
  · rcases hF.temps f i (hWmem _ hq) with h | h | ⟨l, c, h⟩
    · left; rwa [hWold _ hq] at h
    · right; rwa [hWold _ hq] at h
    · obtain ⟨f', j', e⟩ := hbind _ l c hq (by rw [← hWold _ hq]; exact h); cases e
  · exact hF.loan1 q q' l (hWmem _ hq) (hWmem _ hq') (by rw [hWold _ hq]; exact e) (by rw [hWold _ hq']; exact e')
  · exact hF.bor1 q q' l w w' (hWmem _ hq) (hWmem _ hq') (by rw [hWold _ hq]; exact e) (by rw [hWold _ hq']; exact e')
  · obtain ⟨q', c, hq', hy⟩ := hF.held q l (hWmem _ hq) (by rw [hWold _ hq]; exact e)
    rcases hWcases q' hq' with rfl | hq''
    · rw [hWnew] at hy; exact absurd hy (hvnb l c)
    · rw [hWold _ hq''] at hy
      obtain ⟨f', j', rfl⟩ := hbind _ l c hq'' hy
      exact ⟨f', j', c, hq'', hy⟩
  · obtain ⟨q', hq', hx⟩ := hF.lender q l c (hWmem _ hq) (by rw [hWold _ hq]; exact e)
    rcases hWcases q' hq' with rfl | hq''
    · rw [hWnew] at hx; exact absurd hx (hvnl l)
    · exact ⟨q', hq'', by rw [← hWold _ hq'']; exact hx⟩
  · obtain ⟨f, j, b, hck, hlk, h1, h2, h3⟩ := hF.top i B hi
    exact ⟨f, j, b, by rw [← ckVarPos_congr (size_withTempT st v T?) (binds_withTempT st v T?)]; exact hck,
      by rw [← lookup_congr (binds_withTempT st v T?)]; exact hlk, h1, h2, h3⟩
  · exact hF.order f j f' j' l c (hWmem _ hq) (hWmem _ hq') (by rw [hWold _ hq]; exact e) (by rw [hWold _ hq']; exact e')
  · exact hF.lent f j b l (by rw [lookup_congr (binds_withTempT st v T?)]; exact hb) e

section
variable {K : RunCtx} {ρ : Assignment} {φ : Future}

/-- **The fragment's `u; w` with a first part of type `Nat` or `Unit`, at `evalCore`**: the step for
`u`, the drop of its value (a number or `()`: nothing ends, `SeqInv`), the step for `w` from the state
after it (a fragment state again, `FStT.untemp`). -/
theorem seqI_core (hSq : SeqInv) (hR : FragRun K.D) (hdec : FragDec K.D) (hI : InvSteps) (hc : Strict.FundCtx K)
    {Γ : List FT} {u w : Term} {A B : FT} (hu : FTy Γ u A) (hw : FTy Γ w B) (hA : A ≠ .ref) {m : Nat}
    (ihu : EvalSim K ρ φ m u (FSt Γ) (· = true))
    (ihw : ∀ (Δ' : Nat → TyS) (ρ' : Assignment), EvalSim { K with Δ := Δ' } ρ' φ m w (FSt Γ) (· = true)) :
    CoreSim K ρ φ (m + 1) (.seq u w) (FSt Γ) (· = true) := by
  intro st st' typed hint v T? s π hPst hty hm htn htd hcd hp hr hS hv hab hnh hfl hok hD bh h
  subst hty
  obtain ⟨st₀, st₁, stW, v₀, T₀, bh₁, bh₂, hk₀, hm₀, htn₀, htd₀, htdW, hru, hD₁, hdrop, htnW, hrw⟩ :=
    hSq m u w hint st st' bh v T? K.D hm htn htd hD h
  have hP₀ : FSt Γ st₀ := hPst.kern hk₀
  obtain ⟨rfl, hv₀, hme₁, -, -, hF₁⟩ := hR Γ u A m none st₀ st₁ bh₁ v₀ T₀ hu hP₀ hm₀ (.inl htd₀) hD₁ hru
  have hin : v₀.Num ∨ v₀ = .unit := by
    cases A with
    | nat => exact .inl hv₀
    | unit => exact .inr hv₀
    | ref => exact absurd rfl hA
  have hinert : v₀.Inert := by
    rcases hin with h | h
    · exact h.inert
    · rw [h]; exact Value.inert_unit
  have hloans : v₀.loans = [] := by
    rcases hin with h | h
    · exact h.loans
    · rw [h]; simp [Value.loans]
  obtain ⟨hkW, hmeW⟩ := hdrop hinert.holdsBorrow hloans
  have hmW : Mode stW := (hm₀.of_modeEq hme₁).of_modeEq hmeW
  -- the step for `u`
  have hOu := ihu st₀ st₁ true none v₀ (some A.ty) s π hP₀ rfl hm₀ (.inl htd₀) (hp.of_kern hk₀)
    (hr.of_kern hk₀) hS (hu.valsOk _) (fun σ hσ => hu.absBelow _ σ hσ) hu.noHole
    (by rw [scopeOf_rel hr]; exact (hdec Γ u A st hu hPst).1) (fun e => by cases e) hD₁ bh₁ hru
  rw [htn₀] at hOu
  obtain ⟨ρ₁, Δ₁, π₁, ru, s₁, he₁, hxu, -, -, hlu, hp₁, hr₁⟩ := hOu
  have hxu' : runT K ρ φ false (.plain TyM.err) u s = some (ru, s₁) := hxu
  obtain ⟨-, -, -, hS₁⟩ := Strict.fund_all hc u (hu.valsOk _) false (.plain TyM.err) s s₁ ru hS hxu'
  have hrul : ru.2.label = none := by
    rw [hlu]
    rcases hin with h | h
    · rw [num_heldLabel h]; rfl
    · rw [h]; rfl
  -- the drop of the value: nothing on either side
  have hrW : Rel { K with Δ := Δ₁ } ρ₁ φ π₁ stW s₁ := (rel_of_withTempT_inert hinert hr₁).of_kern hkW
  have hpW : Pre { K with Δ := Δ₁ } ρ₁ stW :=
    ⟨hp₁.ctx.of_eq (by show stW.inds = st₁.inds; rw [← hkW.inds]) (by show stW.globals = st₁.globals; rw [← hkW.globals]),
     by rw [← hkW.norm]; exact hI.popInert K.D K.Γ st₁ v₀ _ hin hp₁.inv,
     by rw [← hkW.norm]; exact asg_of_withTempT hp₁.asg⟩
  have hPW : FSt Γ stW := (hF₁.untemp hin).kern hkW
  -- the step for `w`
  have htdW' : stW.tailDecl = none ∨ stW.tailDecl = some (K.D.declOf (DecideScope.topReadings stW) w) := by
    rcases htdW with e | e
    · exact .inl e
    · exact .inr (by rw [e, hcd, (hdec Γ _ B st (.seq Γ u w A B hu hw) hPst).2, (hdec Γ w B stW hw hPW).2])
  have hOw := ihw Δ₁ ρ₁ stW st' true none v T? s₁ π₁ hPW rfl hmW htdW' hpW hrW hS₁ (hw.valsOk _)
    (fun σ hσ => hw.absBelow _ σ hσ) hw.noHole (by rw [scopeOf_rel hrW]; exact (hdec Γ w B stW hw hPW).1)
    (fun e => by cases e) hD bh₂ hrw
  rw [htnW] at hOw
  obtain ⟨ρ₂, Δ₂, π₂, rw', s₂, he₂, hxw, hmw, haw, hlw, hp₂, hr₂⟩ := hOw
  have hxw' : runT K ρ φ st.curTail (.plain TyM.err) w s₁ = some (rw', s₂) := by
    rw [← wcong (fun m' => hw.absBelow m') Δ₁ ρ₁]; exact hxw
  have hxs : runT K ρ φ st.curTail (hintM K ρ hint) (.seq u w) s = some (rw', s₂) := by
    rw [runT_seq _ _ u w s hfl]
    simp only [bind, Option.bind]
    rw [hxu']
    simp only
    rw [SM.guardMod_of (by unfold DiscardOk; rw [hrul]; trivial)]
    simp only
    have hd : discardEnd ru.2 s₁ = s₁ := by unfold discardEnd; rw [hrul]
    rw [hd]; exact hxw'
  have hext : Ext K ρ π st st' ρ₂ Δ₂ π₂ :=
    (he₁.congr hk₀.absTy hk₀.nextLoan hkW.absTy hkW.nextLoan).trans he₂
  exact ⟨ρ₂, Δ₂, π₂, rw', s₂, hext, hxs, hmw, haw, hlw, hp₂, hr₂⟩

end

end Ochr.Meaning.Steps.Form

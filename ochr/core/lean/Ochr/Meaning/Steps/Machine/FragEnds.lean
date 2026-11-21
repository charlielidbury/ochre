import Ochr.Meaning.Steps.Machine.FragEndRuns
import Ochr.Meaning.Steps.Machine.FormFacts
import Ochr.Meaning.Steps.Machine.StepInv
import Ochr.Meaning.Steps.Machine.VarEndInv

/-!
# The fragment's facts that end one borrow (machine lane, machine6)

Each is the generic end (`runs_endBorrow_fend`, `runs_endTopLoan_fend`: `endE`) placed in the run
of a construct: `DropBorrowInv` (the `let`'s drop of a binding holding a borrow).
-/

namespace Ochr.Meaning.Steps.Machine

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.DecideScope Ochr.Meaning.Steps.Slice
open Ochr.Meaning.Steps.Form

theorem size_endE (E : Env) (px ph : Pos) (c : Value) : (endE E px ph c).size = E.size := by
  rw [endE, size_setAtE_any, size_setAtE_any]

/-- **[Drop] of a binding holding a borrow, with the mode**: the end (`endE`), then the pop; nothing
it runs touches the mode's fields. -/
theorem dropBorrowInvM (n : Nat) (st st' : MState) (bh : Nat) (fr : Frame) (b : Binding) (px : Pos) (l : Nat)
    (c : Value) (hfr : st.env[st.env.size - 1]? = some fr) (hb : fr.binds.back? = some b) (hv : b.val = .borrow l c)
    (hF : FEnd st.env px (.bind (st.env.size - 1) (fr.binds.size - 1)) l c)
    (h : Runs (Ochr.dropTopBind n) st bh () st') :
    Kern { st with env := Env.popBindE (endE st.env px (.bind (st.env.size - 1) (fr.binds.size - 1)) c) } st' ∧
      ModeEq st st' := by
  cases n with
  | zero => unfold Ochr.dropTopBind at h; simp only [runs_exhausted_iff] at h
  | succ k =>
    rw [Ochr.dropTopBind.eq_1] at h
    obtain ⟨f, s₁, b₁, hf, h₁⟩ := Runs.bind_inv h
    clear h
    obtain ⟨hf1, hs⟩ := runs_topIdx_inv hf
    clear hf
    subst hf1
    rw [hs] at h₁
    clear hs
    have hb' : (st.env[st.env.size - 1]!).binds.back? = some b := by
      rw [getElem!_def, hfr]; exact hb
    peel h₁
    rw [hb'] at h₁
    peel h₁
    have hbr : b.val.borrowBelowRoot = false := by
      rw [hv]; exact (Value.Num.anyAtom hF.c rfl (fun _ => rfl) : c.hasBorrow = false)
    rw [hbr] at h₁
    simp only [Bool.false_eq_true, if_false] at h₁
    rw [hv] at h₁
    simp only at h₁
    obtain ⟨u, s₂, b₂, he, h₂⟩ := Runs.bind_inv h₁
    have e2 := runs_endBorrow_fend hF he
    subst e2
    unfold modifyFrame at h₂
    have e3 := runs_modify_inv h₂
    subst e3
    refine ⟨⟨?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl⟩⟩
    simp only [Env.popBindE, size_endE]

theorem dropBorrowInv : DropBorrowInv := fun n st st' bh fr b px l c hfr hb hv hF h =>
  ⟨st, Quiet.refl st, fun _ _ h => h,
    (dropBorrowInvM n st st' bh fr b px l c hfr hb hv hF h).1⟩

/-! ## `VarLentInv`: the read of a lent number variable -/

theorem lookup_setAtE_self {E : Env} {f j : Nat} {b : Binding} {v : Value}
    (hb : E[f]?.bind (fun fr : Frame => fr.binds[j]?) = some b) :
    (Env.setAtE E (.bind f j) v)[f]?.bind (fun fr : Frame => fr.binds[j]?) = some { b with val := v } := by
  rcases e : E[f]? with _ | fr
  · rw [e] at hb; cases hb
  · rw [e] at hb
    simp only [Option.bind_some] at hb
    simp only [Env.setAtE, Array.getElem?_modify, e, if_true, Option.map_some, Option.bind_some, hb]

theorem lookup_setAtE_fwd' {env : Env} {p : Pos} {v : Value} {f i : Nat} {b : Binding}
    (h : env[f]?.bind (fun fr : Frame => fr.binds[i]?) = some b) :
    ∃ b', (Env.setAtE env p v)[f]?.bind (fun fr : Frame => fr.binds[i]?) = some b' ∧ b'.ty = b.ty ∧ b'.decl = b.decl := by
  rcases e : env[f]? with _ | fr
  · rw [e] at h; cases h
  · rw [e] at h; simp only [Option.bind_some] at h
    cases p with
    | bind f' i' =>
      by_cases hf : f' = f
      · subst hf
        by_cases hi : i' = i
        · subst hi; exact ⟨{ b with val := v }, by simp [Env.setAtE, Array.getElem?_modify, e, h], rfl, rfl⟩
        · exact ⟨b, by simp [Env.setAtE, Array.getElem?_modify, e, h, hi], rfl, rfl⟩
      · exact ⟨b, by simp [Env.setAtE, Array.getElem?_modify, e, h, hf], rfl, rfl⟩
    | temp f' i' =>
      by_cases hf : f' = f
      · subst hf; exact ⟨b, by simp [Env.setAtE, Array.getElem?_modify, e, h], rfl, rfl⟩
      · exact ⟨b, by simp [Env.setAtE, Array.getElem?_modify, e, h, hf], rfl, rfl⟩

/-- The binding read after the end: the lender's, holding `c`. -/
theorem lookup_endE_px {E : Env} {f j : Nat} {ph : Pos} {c : Value} {b : Binding}
    (hb : E[f]?.bind (fun fr : Frame => fr.binds[j]?) = some b) :
    ∃ b', (endE E (.bind f j) ph c)[f]?.bind (fun fr : Frame => fr.binds[j]?) = some b' ∧ b'.val = c ∧
      b'.ty = b.ty ∧ b'.decl = b.decl := by
  obtain ⟨b₁, hb₁, hty, hdc⟩ := lookup_setAtE_fwd' (p := ph) (v := .bot) hb
  exact ⟨_, lookup_setAtE_self hb₁, rfl, hty, hdc⟩

theorem ckVarPos_endE (E : Env) (px ph : Pos) (c : Value) (i : Nat) : ckVarPos (endE E px ph c) i = ckVarPos E i := by
  rw [endE, ckVarPos_setAtE_any, ckVarPos_setAtE_any]

theorem back_endE (E : Env) (px ph : Pos) (c : Value) :
    (endE E px ph c).back?.map (fun fr : Frame => fr.binds.toList.map (·.decl)) =
      E.back?.map (fun fr : Frame => fr.binds.toList.map (·.decl)) := by
  rw [endE, back_setAtE_any, back_setAtE_any]

theorem topReadings_endE (s : MState) (px ph : Pos) (c : Value) :
    topReadings { s with env := endE s.env px ph c } = topReadings s := by
  unfold topReadings
  show (((endE s.env px ph c).back?.map (fun fr : Frame => fr.binds.toList.map (·.decl))).getD []).reverse = _
  rw [back_endE]

/-- [Repack] at a lent variable is the identity (a loan has no dependent constructor). -/
theorem runs_repackAt_lentG {n i f j l : Nat} {T : Value} {w : String} {st st' : MState} {b : Nat}
    (hcv : ckVarPos st.env i = some (.bind f j)) (hx : valAt st.env (.bind f j) = .loan l)
    (h : Runs (repackAt n (.var i) T w) st b () st') : st' = st := by
  cases n with
  | zero => unfold repackAt at h; simp only [runs_exhausted_iff] at h
  | succ k =>
    unfold repackAt at h
    obtain ⟨o, s₁, b₁, hc, h₁⟩ := Runs.bind_inv h
    obtain ⟨rfl, pos, hp, rfl⟩ := runs_content?_inv hc
    simp only [Place.steps] at hp
    rw [hcv] at hp; cases hp
    simp only [Place.steps, Value.follow, hx] at h₁
    obtain ⟨m, s₂, b₂, hm, h₂⟩ := Runs.bind_inv h₁
    obtain ⟨-, rfl⟩ := runs_ppPlace_inv hm
    exact runs_repackCheck_loan h₂

/-- **The path access to a lent variable** ends its borrow (held at a binding): `endE`. -/
theorem runs_accessPath_lentF {k i f j f' j' l : Nat} {c : Value} {s s' : MState} {b : Nat}
    (hF : FEnd s.env (.bind f j) (.bind f' j') l c) (hcv : ckVarPos s.env i = some (.bind f j))
    (h : Runs (Ochr.accessPath k (.var i)) s b () s') :
    s' = { s with env := endE s.env (.bind f j) (.bind f' j') c } := by
  cases k with
  | zero => unfold Ochr.accessPath at h; simp only [runs_exhausted_iff] at h
  | succ k =>
    unfold Ochr.accessPath at h
    simp only [Place.steps] at h
    rw [runs_get_bind] at h
    obtain ⟨pos, s₁, b₁, hv, h₁⟩ := Runs.bind_inv h
    obtain ⟨e1, hp⟩ := runs_varPos_inv hv
    have e1' := e1.symm; subst e1'
    rw [hcv] at hp; cases hp
    have hl : liveLoan s.env l = true := hF.liveL
    rw [hF.x] at h₁
    simp only [firstLiveLoanOnPath, hl, if_true] at h₁
    obtain ⟨_, s₂, b₂, he, h₂⟩ := Runs.bind_inv h₁
    have e2 := runs_endTopLoan_fend hF he
    subst e2
    cases k with
    | zero => unfold Ochr.accessPath at h₂; simp only [runs_exhausted_iff] at h₂
    | succ k =>
      unfold Ochr.accessPath at h₂
      simp only [Place.steps] at h₂
      rw [runs_get_bind] at h₂
      obtain ⟨pos, s₃, b₃, hv, h₃⟩ := Runs.bind_inv h₂
      obtain ⟨e3, hp⟩ := runs_varPos_inv hv
      have e3' := e3.symm; subst e3'
      simp only [ckVarPos_endE, hcv] at hp; cases hp
      have hw0 : valAt (endE s.env (.bind f j) (.bind f' j') c) (.bind f j) = c := by
        rw [hF.valAt_endE, if_pos rfl]
      simp only [hw0, firstLiveLoanOnPath_num hF.c] at h₃
      exact (runs_pure_inv h₃).2

/-- The read of a lent number variable after its [Repack]: the access ends the borrow (`endE`), then the
read as at a number. -/
theorem varLent_read {n i f j f' j' l : Nat} {D : Decisions} {s st' : MState} {b' : Nat}
    {T' T? : Option Value} {v c : Value} {bx : Binding}
    (hcv : ckVarPos s.env i = some (.bind f j)) (hbx : s.env[f]?.bind (fun fr : Frame => fr.binds[j]?) = some bx)
    (hF : FEnd s.env (.bind f j) (.bind f' j') l c)
    (hm : Mode s) (hD : DecTab D st') (hg : TablesGrow s st')
    (hr : Runs (do let __do_lift ← Ochr.readPlace n (Place.var i); pure (__do_lift, T')) s b' (v, T?) st') :
    v = c ∧ T? = T' ∧ Mode st' ∧ ∃ st₁, Quiet s st₁ ∧ KeepsInv s st₁ ∧
      (D.copy (D.placeDecl (DecideScope.topReadings s) (.var i)) = true →
        Kern { st₁ with env := endE st₁.env (.bind f j) (.bind f' j') c } st') ∧
      (D.copy (D.placeDecl (DecideScope.topReadings s) (.var i)) = false →
        Kern { st₁ with env := Env.setAtE (endE st₁.env (.bind f j) (.bind f' j') c) (.bind f j) .bot } st') := by
  obtain ⟨v', s₄, b₄, hrp, h₄⟩ := Runs.bind_inv hr
  obtain ⟨hvt, rfl⟩ := runs_pure_inv h₄
  simp only [Prod.mk.injEq] at hvt
  obtain ⟨e1, e2⟩ := hvt
  subst e2
  obtain ⟨bd, hbd, hbv, -, -⟩ := lookup_endE_px (ph := .bind f' j') (c := c) hbx
  have hn : NumAt { s with env := endE s.env (.bind f j) (.bind f' j') c } i f j bd :=
    ⟨by show ckVarPos (endE _ _ _ _) i = _; rw [ckVarPos_endE]; exact hcv, hbd, hbv ▸ hF.c⟩
  obtain ⟨hv, k, d, cp, b₆, b₇, hpd, hdc, hct, hcf⟩ :=
    runs_readPlace_after (fun m b₀ s₁ _ ha => runs_accessPath_lentF hF hcv ha) hn hm.inPlace hm.copying hrp
  have hvw : v = c := by rw [← hbv]; first | exact e1.trans hv | exact e1.symm.trans hv
  have hDe : DecTab D { s with env := endE s.env (.bind f j) (.bind f' j') c } :=
    DecTab.back hD ⟨hg.globals, hg.inds, hg.size, hg.old, hg.nextAbs, hg.nextLoan⟩
  have hd := decTab_placeDecl_at hDe hpd
  have hc := hDe.copy k d cp b₇ _ hdc
  rw [topReadings_endE] at hd
  rw [hd, hc]
  cases cp with
  | true =>
    obtain rfl := hct rfl
    exact ⟨hvw, rfl, ⟨hm.headEval, hm.copying, hm.inPlace, hm.erased⟩, s, Quiet.refl _, fun _ _ h => h,
      fun _ => Kern.rfl' _, (fun e => by cases e)⟩
  | false =>
    obtain ⟨X, rfl⟩ := hcf rfl
    exact ⟨hvw, rfl, ⟨hm.headEval, hm.copying, hm.inPlace, hm.erased⟩, s, Quiet.refl _, fun _ _ h => h,
      (fun e => by cases e), fun _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

set_option maxHeartbeats 4000000 in
/-- **`VarLentInv`**: the read of a number variable lent to a binding's borrow. -/
theorem varLentInv : VarLentInv := by
  intro n typed i hint st st' bh v T? f j b f' j' l c D hm hpos hb hT hF hD h
  have hg : TablesGrow st st' := Runs.grows (grows_evalCore _ _ _ _) h
  unfold Ochr.evalCore at h
  obtain ⟨b₁, h⟩ := Runs.tick_bind h
  obtain ⟨want, s₁, b₂, hw', h⟩ := Runs.bind_inv (runs_get_bind.mp h)
  obtain ⟨hw1, hw2⟩ := runs_wanted_inv hw'
  subst hw1 hw2
  simp only [Term.placeOperand?] at h
  obtain ⟨o, s₂, b₃, hp, h₁⟩ := Runs.bind_inv h
  clear h
  obtain ⟨rfl, rfl⟩ := runs_projIn_var hp
  simp only at h₁
  cases typed with
  | true =>
    simp only [if_true] at h₁
    obtain ⟨T', s₃, b₄, hpt, h₂⟩ := Runs.bind_inv h₁
    clear h₁
    obtain ⟨T'', hpt', rfl⟩ := Runs.map_inv hpt
    obtain ⟨rfl, rfl⟩ := runs_placeType_var hpos hb hT hpt'
    try simp only [if_true] at h₂
    obtain ⟨_, s₄, b₅, hra, h₃⟩ := Runs.bind_inv h₂
    have := runs_repackAt_lentG hpos hF.x hra
    subst this
    obtain ⟨hv, hT', hm', rest⟩ := varLent_read hpos hb hF hm hD hg h₃
    exact ⟨hv, (fun T e => by rw [hT'] at e; cases e; rfl), (fun _ => by rw [hT']; rfl), hm', rest⟩
  | false =>
    simp only [Bool.false_eq_true, if_false] at h₁
    split at h₁
    · obtain ⟨T', s₃, b₄, hpt, h₂⟩ := Runs.bind_inv h₁
      clear h₁
      obtain ⟨rfl, rfl⟩ := runs_placeTypeQ_var hpos hb hT hpt
      try simp only [Bool.false_eq_true, if_false, pure_bind] at h₂
      obtain ⟨hv, hT', hm', rest⟩ := varLent_read hpos hb hF hm hD hg h₂
      exact ⟨hv, (fun T e => by rw [hT'] at e; cases e; rfl), (fun e => by cases e), hm', rest⟩
    · try simp only [pure_bind, Bool.false_eq_true, if_false] at h₁
      obtain ⟨hv, hT', hm', rest⟩ := varLent_read hpos hb hF hm hD hg h₁
      exact ⟨hv, (fun T e => by rw [hT'] at e; cases e), (fun e => by cases e), hm', rest⟩

#print axioms dropBorrowInv
#print axioms varLentInv

end Ochr.Meaning.Steps.Machine

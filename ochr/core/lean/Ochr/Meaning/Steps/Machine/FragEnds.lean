import Ochr.Meaning.Steps.Machine.FragEndRuns
import Ochr.Meaning.Steps.Machine.FormFacts
import Ochr.Meaning.Steps.Machine.StepInv
import Ochr.Meaning.Steps.Machine.VarEndInv
import Ochr.Meaning.Steps.Machine.BorrowInv
import Ochr.Meaning.Steps.Machine.SeqInv

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
    have e2 := runs_endBorrow_fend hF.endAt he
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

theorem lt_of_getElem?' {α : Type _} {a : Array α} {i : Nat} {x : α} (h : a[i]? = some x) : i < a.size := by
  rcases Nat.lt_or_ge i a.size with hlt | hge
  · exact hlt
  · rw [Array.getElem?_eq_none hge] at h; cases h

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

/-! ## `BorrowLentInv`: `&x` of a lent number variable -/

/-- `borrowPlace` at a lent variable: the access ends its borrow (`endE`), then `x` is lent at the counter. -/
theorem runs_borrowPlace_lent {n i f j f' j' l : Nat} {c : Value} {bx : Binding} {st st' : MState} {b : Nat} {v : Value}
    (hcv : ckVarPos st.env i = some (.bind f j)) (hbx : st.env[f]?.bind (fun fr : Frame => fr.binds[j]?) = some bx)
    (hF : FEnd st.env (.bind f j) (.bind f' j') l c) (h : Runs (Ochr.borrowPlace n (.var i)) st b v st') :
    v = .borrow st.nextLoan c ∧
      ∃ X, st' = { st with
        env := Env.setAtE (endE st.env (.bind f j) (.bind f' j') c) (.bind f j) (.loan st.nextLoan)
        nextLoan := st.nextLoan + 1
        placeLog := X } := by
  obtain ⟨bd, hbd, hbv, -, -⟩ := lookup_endE_px (ph := .bind f' j') (c := c) hbx
  have hn : NumAt { st with env := endE st.env (.bind f j) (.bind f' j') c } i f j bd :=
    ⟨by show ckVarPos (endE _ _ _ _) i = _; rw [ckVarPos_endE]; exact hcv, hbd, hbv ▸ hF.c⟩
  cases n with
  | zero => unfold Ochr.borrowPlace at h; simp only [runs_exhausted_iff] at h
  | succ m =>
    unfold Ochr.borrowPlace at h
    obtain ⟨_, s₁, b₁, ha, h₁⟩ := Runs.bind_inv h
    clear h
    have := runs_accessPath_lentF hF hcv ha
    subst this
    obtain ⟨_, s₂, b₂, hai, h₂⟩ := Runs.bind_inv h₁
    clear h₁
    have := runs_accessInside_num hn hai
    subst this
    obtain ⟨w, s₃, b₃, hc, h₃⟩ := Runs.bind_inv h₂
    clear h₂
    obtain ⟨rfl, rfl⟩ := runs_content_var hn hc
    have hnum := hn.num
    have hx : ∀ x : Value, x.Num → x = .zero ∨ ∃ w, x = .succ w := fun x hx => by
      cases hx with
      | zero => exact .inl rfl
      | succ _ => exact .inr ⟨_, rfl⟩
    have hh : ∀ x, bd.val = x → x.hasHole = false := fun x ex => ex ▸ Value.Num.hasHole hnum
    rcases hx _ hnum with e | ⟨w', e⟩ <;> rw [e] at h₃ <;> simp only [] at h₃ <;> rw [hh _ e] at h₃ <;>
      simp only [Bool.false_eq_true, if_false] at h₃ <;>
      (obtain ⟨X, s₄, b₄, hle, h₄⟩ := Runs.bind_inv h₃
       obtain ⟨X, rfl⟩ := runs_logEffect_inv hle
       obtain ⟨l, s₅, b₅, hfl, h₅⟩ := Runs.bind_inv h₄
       obtain ⟨rfl, rfl⟩ := runs_freshLoan_inv hfl
       obtain ⟨_, s₆, b₆, hsp, h₆⟩ := Runs.bind_inv h₅
       obtain ⟨pos, v', hp, hu', rfl⟩ := runs_setPlace_inv hsp
       simp only [Place.steps] at hp hu'
       rw [hn.pos] at hp; cases hp
       simp only [Value.updAt, Option.some.injEq] at hu'
       subst hu'
       obtain ⟨rfl, rfl⟩ := runs_pure_inv h₆
       exact ⟨by rw [← hbv, e], X, rfl⟩)

set_option maxHeartbeats 4000000 in
/-- **`BorrowLentInv`**: `&x` of a number variable lent to a binding's borrow. -/
theorem borrowLentInv : BorrowLentInv := by
  intro n i hint st st' bh v T? f j b f' j' m c D hm hpos hb hty hF hD h
  unfold Ochr.evalCore at h
  obtain ⟨b₁, h⟩ := Runs.tick_bind h
  obtain ⟨want, s₁, b₂, hw, h⟩ := Runs.bind_inv (runs_get_bind.mp h)
  obtain ⟨hw1, hw2⟩ := runs_wanted_inv hw
  subst hw1 hw2
  simp only [Term.placeOperand?] at h
  obtain ⟨o, s₂, b₃, hp, h₁⟩ := Runs.bind_inv h
  clear h
  obtain ⟨rfl, rfl⟩ := runs_projIn_var hp
  simp only [if_true] at h₁
  obtain ⟨T', s₃, b₄, hpt, h₂⟩ := Runs.bind_inv h₁
  clear h₁
  obtain ⟨T'', hpt', rfl⟩ := Runs.map_inv hpt
  obtain ⟨rfl, rfl⟩ := runs_placeType_var hpos hb hty hpt'
  simp only [Value.typeHasRef, Bool.false_eq_true, if_false] at h₂
  obtain ⟨cb, s₄, b₅, hib, h₃⟩ := Runs.bind_inv h₂
  clear h₂
  have := runs_keep (keep_isBorrowable _ _) hib
  subst this
  split at h₃
  · obtain ⟨_, s₅, b₆, hpp, h₄⟩ := Runs.bind_inv h₃
    exact absurd h₄ (fun h => by simp only [runs_err_bind] at h)
  · obtain ⟨_, s₅, b₆, hra, h₄⟩ := Runs.bind_inv h₃
    have := runs_repackAt_lentG hpos hF.x hra
    subst this
    obtain ⟨bv, s₆, b₇, hbp, h₅⟩ := Runs.bind_inv h₄
    obtain ⟨rfl, X, rfl⟩ := runs_borrowPlace_lent hpos hb hF hbp
    obtain ⟨_, s₇, b₈, hpu, h₆⟩ := Runs.bind_inv h₅
    have := runs_pushTemp_inv hpu
    subst this
    obtain ⟨_, s₈, b₉, how, h₇⟩ := Runs.bind_inv h₆
    have := runs_openWrite_var how
    subst this
    obtain ⟨pv, s₉, b₁₀, hpp, h₈⟩ := Runs.bind_inv h₇
    obtain ⟨htop, rfl⟩ := runs_popTemp_inv hpp
    have hpv := topTemp_withTempT htop
    subst hpv
    obtain ⟨hvt, rfl⟩ := runs_pure_inv h₈
    simp only [Prod.mk.injEq] at hvt
    obtain ⟨rfl, rfl⟩ := hvt
    exact ⟨⟨hm.headEval, hm.copying, hm.inPlace, hm.erased⟩, s₅, Quiet.refl _, fun _ _ h => h, rfl, rfl,
      ⟨congrArg Env.erase (popTempE_pushTempTyE _ _ _).symm, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

/-! ## `SeqBorInv`: `u; w` with `u`'s value a borrow -/

theorem valAt_withTempT' (st : MState) (v : Value) (T? : Option Value) (q : Pos) :
    valAt (st.withTempT v T?).env q = valAt (Env.pushTempE st.env v) q := by
  rw [← valAt_erase, ← erase_withTemp st v T?, valAt_erase]; rfl

theorem allPos_withTempT' (st : MState) (v : Value) (T? : Option Value) :
    allPos (st.withTempT v T?).env = allPos (Env.pushTempE st.env v) := by
  rw [← allPos_erase, ← erase_withTemp st v T?, allPos_erase]; rfl

theorem pop_set_push (a : Array Value) (v w : Value) : ((a.push v).setIfInBounds a.size w).pop = a := by
  apply Array.ext_getElem?; intro k
  simp only [Array.getElem?_pop, Array.getElem?_setIfInBounds, Array.getElem?_push, Array.size_setIfInBounds,
    Array.size_push]
  by_cases h1 : k < a.size
  · have hk : k ≠ a.size := by omega
    have hk' : a.size ≠ k := by omega
    simp [h1, hk, hk']
  · simp [h1]

theorem pop_set_set_push (a : Array Value) (v w c : Value) {i : Nat} (hi : i < a.size) :
    (((a.push v).setIfInBounds a.size w).setIfInBounds i c).pop = a.setIfInBounds i c := by
  apply Array.ext_getElem?; intro k
  simp only [Array.getElem?_pop, Array.getElem?_setIfInBounds, Array.getElem?_push, Array.size_setIfInBounds,
    Array.size_push]
  by_cases h1 : k < a.size
  · have hk : k ≠ a.size := by omega
    by_cases e : i = k <;> simp [h1, hk, e, hi] <;> omega
  · have : i ≠ k := by omega
    simp [h1, this]

/-- **The discard's end, then its pop**: the borrow pushed as a temporary, its end (`endE`, the new
temporary its holder), then the pop, is the lender given `c`. -/
theorem popTempE_endE_push {E : Env} {fr : Frame} (hfr : E[E.size - 1]? = some fr) {px : Pos} (hpx : px ∈ allPos E)
    (v c : Value) (T : Option Value) :
    Env.popTempE (endE (Env.pushTempTyE E v T) px (.temp (E.size - 1) fr.temps.size) c) = Env.setAtE E px c := by
  have hs : (Env.pushTempTyE E v T).size = E.size := by simp [Env.pushTempTyE]
  apply Array.ext_getElem?
  intro a
  cases px with
  | bind f j =>
    simp only [Env.popTempE, endE, Env.setAtE, Env.pushTempTyE, Array.getElem?_modify, Array.size_modify]
    by_cases ha : E.size - 1 = a
    · subst ha
      rw [hfr]
      by_cases hf : f = E.size - 1
      · subst hf; simp [Array.set!, pop_set_push]
      · simp [hf, Array.set!, pop_set_push]
    · simp [ha]
  | temp f i =>
    obtain ⟨fr', hf', hi⟩ := mem_allPos_temp E f i hpx
    simp only [Env.popTempE, endE, Env.setAtE, Env.pushTempTyE, Array.getElem?_modify, Array.size_modify]
    by_cases ha : E.size - 1 = a
    · subst ha
      rw [hfr]
      by_cases hf : f = E.size - 1
      · subst hf
        rw [hfr] at hf'; cases hf'
        simp [Array.set!, pop_set_set_push _ _ _ _ hi]
      · simp [hf, Array.set!, pop_set_push]
    · simp [ha]

/-- **The discard of a borrow** (`dropValue`): pushed as a temporary, its end (`endE`, the temporary its
holder: the other positions as they were), the pop; the lender given `c` back. -/
theorem runs_dropValue_borrow {n l : Nat} {c : Value} {T : Option Value} {st st' : MState} {b : Nat} {px : Pos}
    (hc : c.Num) (hv : ∀ q ∈ allPos st.env, FVal (valAt st.env q)) (hx : valAt st.env px = .loan l)
    (hpx : px ∈ allPos st.env) (hl1 : ∀ q ∈ allPos st.env, valAt st.env q = .loan l → q = px)
    (hb : ∀ q ∈ allPos st.env, ∀ w', valAt st.env q ≠ .borrow l w')
    (h : Runs (Ochr.dropValue n (.borrow l c) T) st b () st') :
    st' = { st with env := Env.setAtE st.env px c } := by
  have hne : 0 < st.env.size := by
    rcases px with ⟨f, j⟩ | ⟨f, j⟩
    · obtain ⟨fr, -, hf, -⟩ := mem_allPos_bind _ _ _ hpx; have := lt_of_getElem?' hf; omega
    · obtain ⟨fr, hf, -⟩ := mem_allPos_temp _ _ _ hpx; have := lt_of_getElem?' hf; omega
  obtain ⟨fr, hfr⟩ : ∃ fr, st.env[st.env.size - 1]? = some fr :=
    ⟨_, Array.getElem?_eq_getElem (by omega : st.env.size - 1 < st.env.size)⟩
  have hA : allPos (st.withTempT (.borrow l c) T).env = allPos st.env ++ [.temp (st.env.size - 1) fr.temps.size] := by
    rw [allPos_withTempT', allPos_pushTempE _ _ fr hfr hne]
  have hnew : valAt (st.withTempT (.borrow l c) T).env (.temp (st.env.size - 1) fr.temps.size) = .borrow l c := by
    rw [valAt_withTempT', valAt_pushTempE_new _ _ fr hfr]
  have hold : ∀ q ∈ allPos st.env, valAt (st.withTempT (.borrow l c) T).env q = valAt st.env q := by
    intro q hq; rw [valAt_withTempT', valAt_pushTempE_mem (E := st.env) (v := .borrow l c) (fr := fr) (hfr := hfr) hq]
  have hcases : ∀ q ∈ allPos (st.withTempT (.borrow l c) T).env,
      q = .temp (st.env.size - 1) fr.temps.size ∨ q ∈ allPos st.env := by
    intro q hq; rw [hA, List.mem_append, List.mem_singleton] at hq; exact hq.symm
  have hW : EndAt (st.withTempT (.borrow l c) T).env px (.temp (st.env.size - 1) fr.temps.size) l c := by
    refine ⟨fun q hq => ?_, by rw [hA]; exact List.mem_append_left _ hpx, by rw [hA]; simp, by rw [hold px hpx]; exact hx,
      hnew, hc, fun q hq e => ?_, fun q hq w' e => ?_⟩
    · rcases hcases q hq with rfl | hq'
      · rw [hnew]; exact .bor l hc
      · rw [hold q hq']; exact hv q hq'
    · rcases hcases q hq with rfl | hq'
      · rw [hnew] at e; cases e
      · rw [hold q hq'] at e; exact hl1 q hq' e
    · rcases hcases q hq with rfl | hq'
      · rfl
      · rw [hold q hq'] at e; exact absurd e (hb q hq' w')
  cases n with
  | zero => unfold Ochr.dropValue at h; simp only [runs_exhausted_iff] at h
  | succ k =>
    unfold Ochr.dropValue at h
    obtain ⟨_, s₁, b₁, hp, h⟩ := Runs.bind_inv h
    have := runs_pushTemp_inv hp; subst this
    have hbr : (Value.borrow l c).borrowBelowRoot = false :=
      (Value.Num.anyAtom hc rfl (fun _ => rfl) : c.hasBorrow = false)
    rw [hbr] at h
    simp only [Bool.false_eq_true, if_false] at h
    obtain ⟨_, s₂, b₂, he, h⟩ := Runs.bind_inv h
    have := runs_endBorrow_fend hW he; subst this
    have h' : Runs ((fun _ => ()) <$> popTemp) _ b₂ () st' := h
    obtain ⟨pv, hpop, -⟩ := Runs.map_inv h'
    obtain ⟨-, rfl⟩ := runs_popTemp_inv hpop
    show { st.withTempT (.borrow l c) T with
      env := Env.popTempE (endE (st.withTempT (.borrow l c) T).env px (.temp (st.env.size - 1) fr.temps.size) c) } = _
    rw [withTempT_env, popTempE_endE_push hfr hpx]
    rfl

/-- **`SeqBorInv`**: `SeqInv`'s decomposition, and where `u`'s value is a borrow of a number whose
lender is the one position holding its loan and whose borrow no position holds, the discard gives the
lender `c` back and changes nothing else. -/
theorem seqBorInv : SeqBorInv := by
  intro n u w hint st st' bh v T? D hm htn htd hD h
  unfold Ochr.evalCore at h
  obtain ⟨b₁, h⟩ := Runs.tick_bind h
  obtain ⟨want, s₁, b₂, hw, h⟩ := Runs.bind_inv (runs_get_bind.mp h)
  obtain ⟨hw1, hw2⟩ := runs_wanted_inv hw
  subst hw1 hw2
  simp only [Term.placeOperand?] at h
  rw [runs_get_bind] at h
  obtain ⟨⟨v₀, T₀⟩, s₃, b₃, hu, h₁⟩ := Runs.bind_inv h
  clear h
  obtain ⟨_, s₄, b₄, hdv, h₂⟩ := Runs.bind_inv h₁
  clear h₁
  unfold demand at h₂
  peel h₂
  simp only [Bool.true_or, if_true] at h₂
  simp only at hdv
  refine ⟨_, s₃, { s₄ with tailDecl := _, tailNext := _, wantTy := _ }, v₀, T₀, _, b₄, Form.Kern.rfl' _, hm, htn, htd,
    .inr rfl, hu, ?_, fun l c px hv hc hvals hx hpx hl1 hb => ?_, rfl, h₂⟩
  · exact DecTab.back hD ((Runs.grows (grows_dropValue _ _ _) hdv).trans
      ((TablesGrow.of_fields (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)).trans (Runs.grows (grows_eval _ _ _ _) h₂)))
  · subst hv
    have := runs_dropValue_borrow hc hvals hx hpx hl1 hb hdv
    subst this
    exact ⟨s₃, Quiet.refl _, fun _ _ h => h, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
      ⟨rfl, rfl, rfl, rfl⟩⟩

#print axioms seqBorInv
#print axioms borrowLentInv
#print axioms dropBorrowInv
#print axioms varLentInv

end Ochr.Meaning.Steps.Machine

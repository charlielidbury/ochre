import Ochr.Meaning.Steps.FragPush

/-!
# The fragment's `let` (lead11)

`let x = u; w` at every fragment type: the right-hand side's value (a number, `()`, or a borrow with
other borrows live, `FragPush.rel_pushBind_borrowG`) moved into a pushed binding; the tail; then the
drop, which ends nothing (`⊥`, a number, `()`), ends the binding's borrow (`rel_end` at the binding,
then the pop), or fails (the binding lent to the value in flight, `DropLentFail`).
-/

namespace Ochr.Meaning.Steps.Form

open Ochr Ochr.Meaning Ochr.Meaning.Steps
open Classical

namespace FStT
variable {Γ : List FT} {st : MState} (h : FStT Γ st)
include h

theorem tempNoLoan : ∀ f i m, Pos.temp f i ∈ allPos st.env → valAt st.env (.temp f i) ≠ .loan m := by
  intro f i m hq e
  rcases h.temps f i hq with hn | hu | ⟨l, c, hb⟩
  · rw [e] at hn; cases hn
  · rw [e] at hu; cases hu
  · rw [e] at hb; cases hb

theorem loansLive : ∀ q ∈ allPos st.env, ∀ m, valAt st.env q = .loan m → liveLoan st.env m = true := by
  intro q hq m e
  obtain ⟨q', c, hq', hy⟩ := h.held q m hq e
  unfold liveLoan findBorrow
  exact List.find?_isSome.mpr ⟨_, hq', by rw [hy]; simp [Value.holdsBorrow]⟩

/-- The end of a borrow held at `ph`, in a fragment state with a value in flight. -/
theorem fendAt {ph : Pos} {l : Nat} {c : Value} (hph : ph ∈ allPos st.env) (hy : valAt st.env ph = .borrow l c) :
    ∃ px, FEnd st.env px ph l c := by
  obtain ⟨px, hpx, hx⟩ := h.lender ph l c hph hy
  have hc : c.Num := by
    have := h.vals _ hph; rw [hy] at this
    cases this with
    | num hn => cases hn
    | bor m hw => exact hw
  exact ⟨px, ⟨h.vals, h.tempNoLoan, hpx, hph, hx, hy, hc,
    fun q hq e => h.loan1 q _ l hq hpx e hx, fun q hq w e => h.bor1 q _ l w c hq hph e hy⟩⟩

theorem lender_bind {px : Pos} {l : Nat} (hpx : px ∈ allPos st.env) (hx : valAt st.env px = .loan l) :
    ∃ f j, px = .bind f j := by
  cases px with
  | bind f j => exact ⟨f, j, rfl⟩
  | temp f i => exact absurd hx (h.tempNoLoan f i l hpx)

end FStT

/-- The top frame's last binding is a position holding its value. -/
theorem valAt_top {E : Env} {fr : Frame} {b : Binding} (hfr : E[E.size - 1]? = some fr)
    (hb : fr.binds.back? = some b) :
    Pos.bind (E.size - 1) (fr.binds.size - 1) ∈ allPos E ∧ valAt E (.bind (E.size - 1) (fr.binds.size - 1)) = b.val :=
  lookup_pos (by rw [hfr]; rw [Array.back?_eq_getElem?] at hb; exact hb)

/-- A write keeps the top frame and its number of bindings. -/
theorem top_setAtE' {E : Env} {fr : Frame} (hfr : E[E.size - 1]? = some fr) (q : Pos) (v : Value) :
    ∃ fr', (Env.setAtE E q v)[(Env.setAtE E q v).size - 1]? = some fr' ∧ fr'.binds.size = fr.binds.size := by
  cases q with
  | bind f i =>
    simp only [Env.setAtE, Array.size_modify, Array.getElem?_modify, hfr]
    split <;> simp
  | temp f i =>
    simp only [Env.setAtE, Array.size_modify, Array.getElem?_modify, hfr]
    split <;> simp

theorem top_endE {E : Env} {fr : Frame} (hfr : E[E.size - 1]? = some fr) (px ph : Pos) (c : Value) :
    ∃ fr', (endE E px ph c)[(endE E px ph c).size - 1]? = some fr' ∧ fr'.binds.size = fr.binds.size := by
  obtain ⟨fr₁, h1, e1⟩ := top_setAtE' hfr ph .bot
  obtain ⟨fr₂, h2, e2⟩ := top_setAtE' h1 px c
  exact ⟨fr₂, h2, e2.trans e1⟩

theorem back_of_size {fr : Frame} (h : 0 < fr.binds.size) : ∃ b, fr.binds.back? = some b :=
  ⟨_, by rw [Array.back?_eq_getElem?]; exact Array.getElem?_eq_getElem (by omega)⟩

/-- The value a `let` pops is the one its tail returned, given the top frame's temporaries kept. -/
theorem popped_of_topTemps {st₂ st₃ st' : MState} {r v : Value} {T? : Option Value} (hne : 0 < st₂.env.size)
    (h₃ : topTemps st₃.env = topTemps (st₂.withTempT r T?).env) (h' : Kern st₃ (st'.withTempT v T?)) : v = r := by
  have e : topTemps (st'.withTempT v T?).env = topTemps (st₂.withTempT r T?).env := by
    rw [← h₃, ← topTemps_erase, ← h'.env, topTemps_erase]
  simp only [topTemps_withTempT] at e
  rcases h2 : st₂.env[st₂.env.size - 1]? with _ | fr₂
  · rw [Array.getElem?_eq_none_iff] at h2; omega
  rcases h1 : st'.env[st'.env.size - 1]? with _ | fr'
  · simp [topTemps, h1, h2] at e
  simp only [topTemps, h1, h2, Option.map_some, Option.some.injEq] at e
  have := congrArg Array.back? e
  simp only [Array.back?_push, Option.some.injEq] at this
  exact this

theorem top_of_erase {E E' : Env} {fr : Frame} (he : E.erase = E'.erase) (hfr : E[E.size - 1]? = some fr) :
    ∃ fr', E'[E'.size - 1]? = some fr' ∧ fr'.binds = fr.binds := by
  have hs : E'.size = E.size := by rw [← Env.erase_size E', ← he, Env.erase_size]
  have := Env.erase_get? E (E.size - 1)
  rw [he, Env.erase_get?, hfr] at this
  rcases h' : E'[E.size - 1]? with _ | fr'
  · rw [h'] at this; cases this
  · rw [h'] at this
    simp only [Option.map_some, Option.some.injEq] at this
    exact ⟨fr', by rw [hs]; exact h', (congrArg Frame.binds this : _)⟩

theorem topTemps_setAtE_bind (E : Env) (f j : Nat) (v : Value) : topTemps (Env.setAtE E (.bind f j) v) = topTemps E := by
  simp only [topTemps, Env.setAtE, Array.size_modify, Array.getElem?_modify]
  split <;> cases E[E.size - 1]? <;> rfl

section
variable {K : RunCtx} {ρ : Assignment} {φ : Future}

/-- **The drop of a `let`'s binding holding a borrow** (`DropBorrowInv`): both sides end the
binding's borrow (`rel_end` at the binding: the lender gets its content back), then pop it. -/
theorem drop_bor (hDB : DropBorrowInv) (hI : InvSteps) (hIE : InvEnd) (hPL : PlaceLocal K.D)
    {Γ : List FT} {n bh : Nat} {W st₃ : MState} {s₂ : SState} {π : Nat → Nat}
    (hF : FStT Γ W) (hp : Pre K ρ W) (hr : Rel K ρ φ π W s₂) (hS : Strict.SGood K.dm K.Γ φ s₂)
    {fr : Frame} {b : Binding} {l : Nat} {c : Value} (hfr : W.env[W.env.size - 1]? = some fr)
    (hb : fr.binds.back? = some b) (hbv : b.val = .borrow l c)
    (hrd : Runs (Ochr.dropTopBind n) W bh () st₃) :
    ∃ frs, s₂.env.getLast? = some frs ∧ s₂.shape (.bind s₂.topIdx (frs.binds.length - 1)) = some (π l) ∧
      EndOk K φ s₂ (π l) ∧ topTemps st₃.env = topTemps W.env ∧
      Pre K ρ st₃ ∧ Rel K ρ φ π st₃ (s₂.endLabel (π l)).dropLast := by
  obtain ⟨hph, hyv⟩ := valAt_top hfr hb
  rw [hbv] at hyv
  obtain ⟨px, he⟩ := hF.fendAt hph hyv
  obtain ⟨f, j, rfl⟩ := hF.lender_bind he.hpx he.x
  obtain ⟨W₁, hq, hki, hk⟩ := hDB n W st₃ bh fr b (.bind f j) l c hfr hb hbv he hrd
  have hr₁ : Rel K ρ φ π W₁ s₂ := hr.of_quiet hq hp.labels
  have he₁ : FEnd W₁.env (.bind f j) (.bind (W.env.size - 1) (fr.binds.size - 1)) l c := he.of_erase hq.env
  have hvE : ∀ q, valAt W₁.env q = valAt W.env q := fun q => by rw [← valAt_erase, ← hq.env, valAt_erase]
  have haE : allPos W₁.env = allPos W.env := by rw [← allPos_erase, ← hq.env, allPos_erase]
  have hlE : ∀ m, liveLoan W₁.env m = liveLoan W.env m := fun m => by
    unfold liveLoan findBorrow; rw [haE]; simp only [hvE]
  have hlv₁ : ∀ q ∈ allPos W₁.env, ∀ m, valAt W₁.env q = .loan m → liveLoan W₁.env m = true :=
    fun q hq' m hm₁ => by rw [hlE]; exact hF.loansLive q (haE ▸ hq') m (by rw [← hvE]; exact hm₁)
  obtain ⟨r', hhold, hrE⟩ := rel_end hr₁ hS he₁ hlv₁
  have hend := end_ok hr₁ hS he₁
  -- the reference's top binding holds `π l`
  obtain ⟨frs, hfrs, htop, hlen⟩ := skel_align K ρ W s₂ hr.skel fr hfr
  have hlast : s₂.env.getLast? = some frs := by
    rw [List.getLast?_eq_getElem?]; simpa [SState.topIdx] using hfrs
  have hyS : Pos.bind s₂.topIdx (frs.binds.length - 1) = .bind (W.env.size - 1) (fr.binds.size - 1) := by
    rw [htop, hlen]
  have hshS : s₂.shape (.bind s₂.topIdx (frs.binds.length - 1)) = some (π l) := by
    rw [hyS]
    exact hr.sim.2.1 _ l (by simp [IsTemp]) (by show Env.shape W.env _ = _; rw [shape_eq_shapeOf, hyv]; rfl)
  -- the pop of the ended binding
  obtain ⟨fr₁, hfr₁, hb₁⟩ := top_of_erase hq.env hfr
  have hsz : W₁.env.size = W.env.size := by rw [← Env.erase_size W₁.env, ← hq.env, Env.erase_size]
  obtain ⟨fr₂, hfr₂, hsz₂⟩ := top_endE hfr₁ (.bind f j) (.bind (W.env.size - 1) (fr.binds.size - 1)) c
  have hn : 0 < fr.binds.size := by
    rcases Nat.eq_zero_or_pos fr.binds.size with h0 | h0
    · rw [Array.back?_eq_getElem?, Array.getElem?_eq_none (by omega)] at hb; cases hb
    · exact h0
  have hn₂ : 0 < fr₂.binds.size := by rw [hsz₂, hb₁]; exact hn
  obtain ⟨b₂, hb₂⟩ := back_of_size hn₂
  have hsE : (endE W₁.env (.bind f j) (.bind (W.env.size - 1) (fr.binds.size - 1)) c).size = W₁.env.size := by
    simp [endE, Env.setAtE]
  have hbot : b₂.val = .bot := by
    obtain ⟨-, hv₂⟩ := valAt_top hfr₂ hb₂
    rw [hsE, hsz, hsz₂, hb₁, he₁.valAt_endE, if_neg he₁.ne, if_pos rfl] at hv₂
    exact hv₂.symm
  have hRp := rel_popBind_noSites hrE fr₂ b₂ hfr₂ hb₂ (fun L => by rw [hbot]; simp [Value.sitesOf])
    (fun L => by rw [hbot]; rfl)
  refine ⟨frs, hlast, hshS, hend, ?_, ?_, ?_⟩
  · rw [← topTemps_erase st₃.env, ← hk.env, topTemps_erase, topTemps_popBindE]
    unfold endE
    rw [topTemps_setAtE_bind, topTemps_setAtE_bind, ← topTemps_erase, ← hq.env, topTemps_erase]
  · have hinvE : Inv K.D K.Γ ({ W₁ with env := endE W₁.env (.bind f j) (.bind (W.env.size - 1) (fr.binds.size - 1)) c } : MState).norm :=
      hIE K.D K.Γ W₁ _ _ l c hPL he₁ (fun f₀ j₀ e b₀ hb₀ => by
        cases e
        have hbv₀ : b₀.val = .loan l := by rw [← (lookup_pos hb₀).2]; exact he₁.x
        exact (hF.lent f j b₀ l (by rw [← lookup_erase, hq.env, lookup_erase]; exact hb₀) hbv₀).2)
        (hki K.D K.Γ hp.inv)
    have hinvP := hI.popBind K.D K.Γ
      ({ W₁ with env := endE W₁.env (.bind f j) (.bind (W.env.size - 1) (fr.binds.size - 1)) c } : MState)
      fr₂ b₂ hPL hfr₂ hb₂ (.inl hbot) hinvE
    have hasg := asg_popBind (K := K) (ρ := ρ) (asg_endE he.c (Asg.of_quiet hq hp.asg hp.inv.wf6)) fr₂ hfr₂ hn₂
    have hctx : CtxS K ({ W₁ with env := Env.popBindE (endE W₁.env (.bind f j)
        (.bind (W.env.size - 1) (fr.binds.size - 1)) c) } : MState).norm :=
      hp.ctx.of_eq (by show W₁.inds = W.inds; exact hq.inds.symm) (by show W₁.globals = W.globals; exact hq.globals.symm)
    exact Pre.of_kern hk ⟨hctx, hinvP, hasg⟩
  · rw [SState.endLabel_eq hhold]; exact hRp.of_kern hk

end

end Ochr.Meaning.Steps.Form

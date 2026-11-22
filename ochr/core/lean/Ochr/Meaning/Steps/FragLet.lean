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

theorem lt_of_getElem? {α : Type _} {a : Array α} {i : Nat} {x : α} (h : a[i]? = some x) : i < a.size := by
  rcases Nat.lt_or_ge i a.size with hlt | hge
  · exact hlt
  · rw [Array.getElem?_eq_none hge] at h; cases h

/-- The variable `0` is the top frame's last binding. -/
theorem top_var0 {E : Env} {f j : Nat} {b : Binding} (hck : ckVarPos E 0 = some (.bind f j))
    (hlk : E[f]?.bind (fun fr : Frame => fr.binds[j]?) = some b) :
    ∃ fr, E[E.size - 1]? = some fr ∧ fr.binds.back? = some b ∧ f = E.size - 1 ∧ j = fr.binds.size - 1 := by
  unfold ckVarPos at hck
  split at hck
  · cases hck
    rcases hfr : E[E.size - 1]? with _ | fr
    · rw [hfr] at hlk; cases hlk
    · rw [hfr] at hlk
      have he : E[E.size - 1]! = fr := by simp [getElem!_def, hfr]
      rw [he] at hlk ⊢
      refine ⟨fr, rfl, ?_, rfl, by omega⟩
      rw [Array.back?_eq_getElem?]; simpa using hlk
  · cases hck

/-- **What the reference's `let` does after its tail**, in the two ways the fragment's drop goes: the
binding holds no label (its lenders, none, are ended) or holds one (it is ended). -/
def LetDrop (K : RunCtx) (φ : Future) (s₂ s₃ : SState) : Prop :=
  ∃ frs : SFrame, s₂.env.getLast? = some frs ∧
    ((s₂.shape (.bind s₂.topIdx (frs.binds.length - 1)) = none ∧ LetLendersOk K φ s₂ ∧ s₃ = (letLenders s₂).dropLast) ∨
     (∃ L, s₂.shape (.bind s₂.topIdx (frs.binds.length - 1)) = some L ∧ EndOk K φ s₂ L ∧ s₃ = (s₂.endLabel L).dropLast))

theorem letDrop_eval {K : RunCtx} {φ : Future} {s₂ s₃ : SState} (h : LetDrop K φ s₂ s₃) (x : Res) :
    (let held : Option Nat := match s₂.env.getLast? with
        | some fr => s₂.shape (.bind s₂.topIdx (fr.binds.length - 1))
        | none => none
      if (match held with | some l => EndOk K φ s₂ l | none => LetLendersOk K φ s₂) then
        let s := match held with | some l => s₂.endLabel l | none => letLenders s₂
        some (x, s.dropLast)
      else none) = some (x, s₃) := by
  obtain ⟨frs, hlast, ⟨hsh, hok, rfl⟩ | ⟨L, hsh, hok, rfl⟩⟩ := h
  · simp only [hlast, hsh, if_pos hok]
  · simp only [hlast, hsh, if_pos hok]

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
      (W.absTy.size ≤ st₃.absTy.size ∧ W.nextLoan ≤ st₃.nextLoan) ∧
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
  refine ⟨frs, hlast, hshS, hend, ?_, ⟨Nat.le_trans hq.absSize (Nat.le_of_eq (congrArg Array.size hk.absTy)),
    Nat.le_trans hq.nextLoan (Nat.le_of_eq hk.nextLoan)⟩, ?_, ?_⟩
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


/-- **The drop of a `let`'s binding that holds nothing** (`⊥`, a number, `()`; `DropNoopInv`): no
label held, none lent there (no site), so the reference ends nothing; both sides pop. -/
theorem drop_noop (hDN : DropNoopInv) (hI : InvSteps) (hIU : InvPopUnit) (hPL : PlaceLocal K.D)
    {n bh : Nat} {W st₃ : MState} {s₂ : SState} {π : Nat → Nat}
    (hp : Pre K ρ W) (hr : Rel K ρ φ π W s₂)
    {fr : Frame} {b : Binding} (hfr : W.env[W.env.size - 1]? = some fr) (hb : fr.binds.back? = some b)
    (hbv : b.val = .bot ∨ b.val.Num ∨ b.val = .unit)
    (hrd : Runs (Ochr.dropTopBind n) W bh () st₃) :
    LetDrop K φ s₂ s₂.dropLast ∧ topTemps st₃.env = topTemps W.env ∧
      (W.absTy.size ≤ st₃.absTy.size ∧ W.nextLoan ≤ st₃.nextLoan) ∧ Pre K ρ st₃ ∧ Rel K ρ φ π st₃ s₂.dropLast := by
  have hnl : b.val.loans = [] := by
    rcases hbv with e | e | e
    · rw [e]; simp [Value.loans]
    · exact e.loans
    · rw [e]; simp [Value.loans]
  have hnb : ∀ l, b.val.holdsBorrow l = false := fun l => by
    rcases hbv with e | e | e
    · rw [e]; rfl
    · exact e.holdsBorrow l
    · rw [e]; rfl
  have hnbor : ∀ l w, b.val ≠ .borrow l w := fun l w => by
    rcases hbv with e | e | e
    · rw [e]; intro e'; cases e'
    · exact e.not_borrow l w
    · rw [e]; intro e'; cases e'
  have hns : ∀ l pos, b.val.sitesOf l pos [] = [] := fun l pos => by
    rcases hbv with e | e | e
    · rw [e]; simp [Value.sitesOf]
    · exact e.sitesOf l pos []
    · rw [e]; simp [Value.sitesOf]
  have h₃ := hDN n W st₃ bh fr b hfr hb hnl hnbor hnb hrd
  obtain ⟨frs, hlast, hsh, hpos, hbv'⟩ := rel_top_shape_none hr fr b hfr hb hnb
  have hno := rel_noSites_at hr (pos := .bind (W.env.size - 1) (fr.binds.size - 1)) (fun l => by rw [hbv']; exact hns l _)
  have hll : letLenders s₂ = s₂ := letLenders_noop frs hlast (by rw [hpos]; exact hno)
  have hllok : LetLendersOk K φ s₂ := by
    unfold LetLendersOk; rw [hlast]; exact accessOk_noSites (by rw [hpos]; exact hno)
  have hn : 0 < fr.binds.size := by
    rcases Nat.eq_zero_or_pos fr.binds.size with h0 | h0
    · rw [Array.back?_eq_getElem?, Array.getElem?_eq_none (by omega)] at hb; cases hb
    · exact h0
  refine ⟨⟨frs, hlast, .inl ⟨hsh, hllok, by rw [hll]⟩⟩, ?_, ⟨Nat.le_of_eq (congrArg Array.size h₃.absTy),
    Nat.le_of_eq h₃.nextLoan⟩, ?_, ?_⟩
  · rw [← topTemps_erase st₃.env, ← h₃.env, topTemps_erase, topTemps_popBindE]
  · have hinv : Inv K.D K.Γ ({ W with env := Env.popBindE W.env } : MState).norm := by
      rcases hbv with e | e | e
      · exact hI.popBind K.D K.Γ W fr b hPL hfr hb (.inl e) hp.inv
      · exact hI.popBind K.D K.Γ W fr b hPL hfr hb (.inr e) hp.inv
      · exact hIU K.D K.Γ W fr b hPL hfr hb e hp.inv
    exact Pre.of_kern h₃ ⟨hp.ctx.of_eq rfl rfl, hinv, asg_popBind hp.asg fr hfr hn⟩
  · exact (rel_popBind_noSites hr fr b hfr hb (fun l => hns l _) hnb).of_kern h₃

/-- **The drop of a fragment `let`'s binding**, whatever it holds: nothing (`drop_noop`), a borrow
(`drop_bor`), or a loan (then its borrow is the value in flight, `FSt.order`, and the drop fails,
`DropLentFail`). -/
theorem drop_frag (hDN : DropNoopInv) (hDB : DropBorrowInv) (hDL : DropLentFail) (hI : InvSteps)
    (hIU : InvPopUnit) (hIE : InvEnd) (hPL : PlaceLocal K.D)
    {Γ : List FT} {A : FT} {n bh : Nat} {W st₃ : MState} {s₂ : SState} {π : Nat → Nat}
    (hF : FStT (A :: Γ) W) (hp : Pre K ρ W) (hr : Rel K ρ φ π W s₂) (hS : Strict.SGood K.dm K.Γ φ s₂)
    (hrd : Runs (Ochr.dropTopBind n) W bh () st₃) :
    ∃ s₃, LetDrop K φ s₂ s₃ ∧ topTemps st₃.env = topTemps W.env ∧
      (W.absTy.size ≤ st₃.absTy.size ∧ W.nextLoan ≤ st₃.nextLoan) ∧ Pre K ρ st₃ ∧ Rel K ρ φ π st₃ s₃ := by
  obtain ⟨f, j, b, hck, hlk, -, -, hhold⟩ := hF.top 0 A rfl
  obtain ⟨fr, hfr, hb, rfl, rfl⟩ := top_var0 hck hlk
  have hcases : b.val = .bot ∨ b.val.Num ∨ b.val = .unit ∨ (∃ m, b.val = .loan m) ∨ (∃ l c, b.val = .borrow l c) := by
    cases A with
    | nat => rcases hhold with h | h | h
             · exact .inr (.inl h)
             · exact .inl h
             · exact .inr (.inr (.inr (.inl h)))
    | unit => rcases hhold with h | h
              · exact .inr (.inr (.inl h))
              · exact .inl h
    | ref => rcases hhold with h | ⟨l, c, h, -⟩
             · exact .inl h
             · exact .inr (.inr (.inr (.inr ⟨l, c, h⟩)))
  rcases hcases with hv | hv | hv | ⟨m, hv⟩ | ⟨l, c, hv⟩
  · exact ⟨_, drop_noop hDN hI hIU hPL hp hr hfr hb (.inl hv) hrd⟩
  · exact ⟨_, drop_noop hDN hI hIU hPL hp hr hfr hb (.inr (.inl hv)) hrd⟩
  · exact ⟨_, drop_noop hDN hI hIU hPL hp hr hfr hb (.inr (.inr hv)) hrd⟩
  · exfalso
    obtain ⟨hph, hxv⟩ := valAt_top hfr hb
    obtain ⟨q', c, hq', hy⟩ := hF.held _ m hph (by rw [hxv, hv])
    cases q' with
    | bind f' j' =>
      obtain ⟨fr', b', hf', hj'⟩ := mem_allPos_bind _ _ _ hq'
      have hf'lt := lt_of_getElem? hf'
      rcases hF.order _ _ f' j' m c hph hq' (by rw [hxv, hv]) hy with h1 | ⟨h1, h2⟩
      · omega
      · subst h1; rw [hfr] at hf'; cases hf'; have := lt_of_getElem? hj'; omega
    | temp f' i' =>
      exact hDL n W st₃ bh fr b m f' i' c hfr hb hv hq' hy (fun q hq hh => by
        obtain ⟨w', hw⟩ := (FVal.holdsBorrow (hF.vals q hq) m).mp hh
        exact hF.bor1 q _ m w' c hq hq' hw hy) hrd
  · obtain ⟨frs, hlast, hsh, hend, htt, hgr, hP, hR⟩ := drop_bor hDB hI hIE hPL hF hp hr hS hfr hb hv hrd
    exact ⟨_, ⟨frs, hlast, .inr ⟨_, hsh, hend, rfl⟩⟩, htt, hgr, hP, hR⟩

end

theorem valAt_withTempT (st : MState) (v : Value) (T? : Option Value) (q : Pos) :
    valAt (st.withTempT v T?).env q = valAt (Env.pushTempE st.env v) q := by
  rw [← valAt_erase, ← erase_withTemp st v T?, valAt_erase]; rfl

theorem allPos_withTempT (st : MState) (v : Value) (T? : Option Value) :
    allPos (st.withTempT v T?).env = allPos (Env.pushTempE st.env v) := by
  rw [← allPos_erase, ← erase_withTemp st v T?, allPos_erase]; rfl

/-- In a fragment state with a borrow in flight, no position of the environment holds its label. -/
theorem FStT.noHold {Γ : List FT} {st : MState} {l : Nat} {c : Value} {T? : Option Value} (hne : 0 < st.env.size)
    (hF : FStT Γ (st.withTempT (.borrow l c) T?)) : ∀ q, Env.shape st.env q ≠ some l := by
  intro q hq
  obtain ⟨fr, hfr⟩ : ∃ fr, st.env[st.env.size - 1]? = some fr :=
    ⟨_, Array.getElem?_eq_getElem (by omega : st.env.size - 1 < st.env.size)⟩
  have hqm := mem_allPos_of_shape hq
  rw [shape_eq_shapeOf] at hq
  generalize hv : valAt st.env q = v at hq
  cases v <;> simp [shapeOf] at hq
  rename_i m w
  rw [hq] at hv
  have hntq : q ≠ .temp (st.env.size - 1) fr.temps.size := fun e => by
    rw [e] at hqm; obtain ⟨fr', hf', hi⟩ := mem_allPos_temp st.env _ _ hqm
    rw [hfr] at hf'; cases hf'; exact absurd hi (Nat.lt_irrefl _)
  have hval : ∀ q', q' ∈ allPos st.env → valAt (st.withTempT (.borrow l c) T?).env q' = valAt st.env q' := by
    intro q' hq'
    rw [valAt_withTempT]
    cases q' with
    | bind f i => exact valAt_pushTempE_bind _ _ f i
    | temp f i =>
      refine valAt_pushTempE_old _ _ fr hfr f i (fun e => ?_)
      obtain ⟨fr', hf', hi⟩ := mem_allPos_temp st.env _ _ (e ▸ hq')
      rw [hfr] at hf'; cases hf'; exact absurd hi (Nat.lt_irrefl _)
  have hA : ∀ q', q' ∈ allPos st.env → q' ∈ allPos (st.withTempT (.borrow l c) T?).env := fun q' h' => by
    rw [allPos_withTempT, allPos_pushTempE _ _ fr hfr hne]; exact List.mem_append_left _ h'
  have hT : Pos.temp (st.env.size - 1) fr.temps.size ∈ allPos (st.withTempT (.borrow l c) T?).env := by
    rw [allPos_withTempT, allPos_pushTempE _ _ fr hfr hne]; simp
  have hTv : valAt (st.withTempT (.borrow l c) T?).env (.temp (st.env.size - 1) fr.temps.size) = .borrow l c := by
    rw [valAt_withTempT, valAt_pushTempE_new _ _ fr hfr]
  exact hntq (hF.bor1 q _ l w c (hA q hqm) hT (by rw [hval q hqm, hv]) hTv)

section
variable {K : RunCtx} {ρ : Assignment} {φ : Future}

/-- **The push of a fragment `let`'s right-hand side** at its type (a number, `()`, or a borrow with
other borrows live): the relation, the step's hypotheses and the reference's goodness after it. -/
theorem push_frag (hI : InvSteps) (hIBU : InvBindUnit) (hPL : PlaceLocal K.D)
    {Γ : List FT} {A : FT} {st₁ stB : MState} {v₀ : Value} {x : Hint} {p : Bool} {π : Nat → Nat} {ru : Res}
    {s₁ : SState} (hv₀ : A.val v₀) (hne₁ : 0 < st₁.env.size) (hF₁ : FStT Γ (st₁.withTempT v₀ (some A.ty)))
    (hp₁ : Pre K ρ (st₁.withTempT v₀ (some A.ty))) (hr₁ : Rel K ρ φ π (st₁.withTempT v₀ (some A.ty)) s₁)
    (hS₁ : Strict.SGood K.dm K.Γ φ s₁)
    (hmu : meanV K ρ (fun l => φ (π l)) ru.2 v₀ = ru.1) (hau : StrAgree K ρ A.ty ru.2) (hlu : ru.2.label = (Value.heldLabel v₀).map π)
    (hgu : Strict.GoodRes K.dm.read ru) (hlabu : Strict.LabOk K.dm s₁ ru) (hlouu : LoU s₁ ru.2.label)
    (hkB : Kern { st₁ with env := Env.pushBindE st₁.env x (some A.ty) v₀ p A.rd } stB) :
    Pre K ρ stB ∧ Rel K ρ φ π stB (pushBindShaped s₁ { ty := ru.2, val := fun _ => ru.1, decl := A.rd }) ∧
      Strict.SGood K.dm K.Γ φ (pushBindShaped s₁ { ty := ru.2, val := fun _ => ru.1, decl := A.rd }) := by
  obtain ⟨fr₁, hfr₁⟩ : ∃ fr₁, st₁.env[st₁.env.size - 1]? = some fr₁ :=
    ⟨_, Array.getElem?_eq_getElem (by omega : st₁.env.size - 1 < st₁.env.size)⟩
  have hs₁ne : s₁.env ≠ [] := by
    have hfr₁' : (st₁.withTempT v₀ (some A.ty)).env[(st₁.withTempT v₀ (some A.ty)).env.size - 1]? = some { fr₁ with
        temps := fr₁.temps.push v₀, tempTys := fr₁.tempTys.push (some A.ty) } := by
      simp only [MState.withTempT, Array.size_modify, Array.getElem?_modify, if_true, hfr₁]; rfl
    obtain ⟨frs, hfrs, -, -⟩ := skel_align K ρ _ s₁ hr₁.skel _ hfr₁'
    intro e; rw [e] at hfrs; simp at hfrs
  have hSB := Strict.sgood_pushBindShaped hS₁ { ty := ru.2, val := fun _ => ru.1, decl := A.rd } rfl hgu hlabu hlouu hs₁ne
  refine ⟨?_, ?_, hSB⟩
  · -- the step's hypotheses after the push
    refine Pre.of_kern hkB ⟨hp₁.ctx.of_eq rfl rfl, ?_, ?_⟩
    · cases A with
      | nat => exact hI.bindNum K.D K.Γ st₁ x v₀ _ p hPL hv₀ hne₁ hp₁.inv
      | unit => cases hv₀; exact hIBU K.D K.Γ st₁ x _ p hPL hne₁ hp₁.inv
      | ref => obtain ⟨l, c, rfl, hc⟩ := hv₀; exact hI.bindBorrow K.D K.Γ st₁ x l c _ p hPL hc hne₁ hp₁.inv
    · cases A with
      | nat => exact asg_pushBind_num hv₀ hp₁.asg hne₁ x p _
      | unit => cases hv₀; exact asg_pushBind_inert Value.inert_unit .tUnit (fun _ => rfl) hp₁.asg hne₁ x p _
      | ref => obtain ⟨l, c, rfl, hc⟩ := hv₀; exact asg_pushBind_borrow hc hp₁.asg hne₁ x p _
  · -- the relation after the push
    cases A with
    | nat =>
      obtain ⟨m, hmv⟩ := hv₀.vmean
      have hru1 : ru.1 = .el0 Nat m := by rw [← hmu, ← meanV_eq_mean]; exact hmv _ _ _ _ _ _
      have hrul : ru.2.label = none := by rw [hlu, num_heldLabel hv₀]; rfl
      have hpb : pushBindShaped s₁ { ty := ru.2, val := fun _ => ru.1, decl := FT.nat.rd } =
          s₁.pushBind { ty := ru.2, val := fun _ => ru.1, decl := FT.nat.rd } := by
        unfold pushBindShaped; rw [hrul]
      rw [hpb]
      exact (rel_pushBind_num (rel_of_withTempT_num hv₀ hr₁) hne₁ x .tNat hv₀ p _ ru.2 hau ru.1
        (fun φ' hint' => by rw [hru1]; exact hmv _ _ _ _ _ _)).of_kern hkB
    | unit =>
      cases hv₀
      have hrul : ru.2.label = none := by rw [hlu]; rfl
      have hpb : pushBindShaped s₁ { ty := ru.2, val := fun _ => ru.1, decl := FT.unit.rd } =
          s₁.pushBind { ty := ru.2, val := fun _ => ru.1, decl := FT.unit.rd } := by
        unfold pushBindShaped; rw [hrul]
      rw [hpb]
      obtain ⟨a, ha⟩ := FVal.mean_const FVal.unit (fun m e => by cases e)
      have hru1 : ru.1 = a := by rw [← hmu, ← meanV_eq_mean]; exact ha _ _ _ _ _ _
      exact (rel_pushBind_inert (rel_of_withTempT_inert Value.inert_unit hr₁) hne₁ x .tUnit Value.inert_unit p _ ru.2
        hau ru.1 (fun φ' hint' => by rw [hru1]; exact ha _ _ _ _ _ _)).of_kern hkB
    | ref =>
      obtain ⟨l, c, rfl, hc⟩ := hv₀
      obtain ⟨m, hmv⟩ := hc.vmean
      have hru1 : ru.1 = .el0 Nat m := by rw [← hmu, ← meanV_eq_mean]; exact hmv _ _ _ _ _ _
      have hrul : ru.2.label = some (π l) := by rw [hlu]; rfl
      exact (rel_pushBind_borrowG hr₁ hS₁.uniq hne₁ (FStT.noHold hne₁ hF₁) hc x (.tRef .tNat) p _ ru.2 hau hrul
        (hlabu (π l) hrul).1 ru.1 (fun φ' hint' => by rw [hru1]; exact hmv _ _ _ _ _ _)).of_kern hkB

end

/-! ## The fragment's terms carry no embedded value, unknown or hole -/

theorem FTy.valsOk {Γ : List FT} {t : Term} {A : FT} (h : FTy Γ t A) (P : Value → Prop) : t.valsOk P := by
  induction h <;> simp_all [Term.valsOk]

theorem FTy.absBelow {Γ : List FT} {t : Term} {A : FT} (h : FTy Γ t A) (m : Nat) : t.absBelow m := by
  induction h with
  | letIn _ _ _ _ _ _ _ _ ih1 ih2 | seq _ _ _ _ _ _ _ ih1 ih2 =>
    intro σ hσ; simp only [Term.anyAtom, Bool.or_eq_true] at hσ
    rcases hσ with h | h
    · exact ih1 σ h
    · exact ih2 σ h
  | _ => simp_all [Term.absBelow, Term.anyAtom]

theorem FTy.noHole {Γ : List FT} {t : Term} {A : FT} (h : FTy Γ t A) : t.hasHolePrim = false := by
  induction h <;> simp_all [Term.hasHolePrim]

/-- An extension to a state is one to any later state whose counters only grew. -/
theorem Ext.grow {K : RunCtx} {ρ ρ' : Assignment} {Δ' : Nat → TyS} {π π' : Nat → Nat} {st₀ st₁ st' : MState}
    (h : Ext K ρ π st₀ st₁ ρ' Δ' π') (ha : st₁.absTy.size ≤ st'.absTy.size) (hl : st₁.nextLoan ≤ st'.nextLoan) :
    Ext K ρ π st₀ st' ρ' Δ' π' :=
  ⟨Nat.le_trans h.abs ha, Nat.le_trans h.lab hl, h.agree, h.ren⟩

theorem getElem!_of_getElem? {E : Env} {k : Nat} {fr : Frame} (h : E[k]? = some fr) : E[k]! = fr := by
  simp [getElem!_def, h]

/-- Two environments with the same frames' bindings have the same variables and lookups. -/
theorem ckVarPos_congr {E E' : Env} (hs : E'.size = E.size)
    (hb : ∀ f : Nat, (E'[f]?).map Frame.binds = (E[f]?).map Frame.binds) (i : Nat) : ckVarPos E' i = ckVarPos E i := by
  have : E'[E'.size - 1]!.binds = E[E.size - 1]!.binds := by
    rw [hs]; have := hb (E.size - 1)
    rcases h1 : E'[E.size - 1]? with _ | a <;> rcases h2 : E[E.size - 1]? with _ | b' <;>
      rw [h1, h2] at this <;> simp at this
    · simp [getElem!_def, h1, h2]
    · rw [getElem!_of_getElem? h1, getElem!_of_getElem? h2, this]
  unfold ckVarPos; rw [this, hs]

theorem lookup_congr {E E' : Env} (hb : ∀ f : Nat, (E'[f]?).map Frame.binds = (E[f]?).map Frame.binds) (f j : Nat) :
    E'[f]?.bind (fun fr : Frame => fr.binds[j]?) = E[f]?.bind (fun fr : Frame => fr.binds[j]?) := by
  have := hb f
  rcases h1 : E'[f]? with _ | a <;> rcases h2 : E[f]? with _ | b' <;> rw [h1, h2] at this <;> simp_all

theorem binds_withTempT (st : MState) (v : Value) (T? : Option Value) (f : Nat) :
    ((st.withTempT v T?).env[f]?).map Frame.binds = (st.env[f]?).map Frame.binds := by
  simp only [MState.withTempT, Array.getElem?_modify]
  split <;> cases st.env[f]? <;> rfl

theorem size_withTempT (st : MState) (v : Value) (T? : Option Value) : (st.withTempT v T?).env.size = st.env.size := by
  simp [MState.withTempT]

/-- The variables after a push: `0` is the new binding, `i + 1` the old `i`. -/
theorem ckVarPos_pushBindE {E : Env} {fr : Frame} (hfr : E[E.size - 1]? = some fr) (h : Hint) (ty : Option Value)
    (v : Value) (pf : Bool) (d : DeclInfo) :
    ckVarPos (Env.pushBindE E h ty v pf d) 0 = some (.bind (E.size - 1) fr.binds.size) ∧
      ∀ i, ckVarPos (Env.pushBindE E h ty v pf d) (i + 1) = ckVarPos E i := by
  have hs : (Env.pushBindE E h ty v pf d).size = E.size := by simp [Env.pushBindE]
  have htop : (Env.pushBindE E h ty v pf d)[E.size - 1]! =
      { fr with binds := fr.binds.push { hint := h, ty, val := v, proof := pf, decl := d } } := by
    apply getElem!_of_getElem?
    simp only [Env.pushBindE, Array.getElem?_modify, hfr, if_true]; rfl
  have hE : E[E.size - 1]! = fr := getElem!_of_getElem? hfr
  refine ⟨?_, fun i => ?_⟩
  · unfold ckVarPos; rw [hs, htop]; simp
  · unfold ckVarPos; rw [hs, htop, hE]
    simp only [Array.size_push]
    by_cases hi : i < fr.binds.size
    · rw [if_pos (by omega), if_pos hi]; congr 2; omega
    · rw [if_neg (by omega), if_neg hi]

/-- **A fragment state with a value in flight, the value bound**: the `let`'s push makes a fragment
state of the extended typing. -/
theorem fst_push {Γ : List FT} {A : FT} {st : MState} {v : Value} {T? : Option Value}
    (hF : FStT Γ (st.withTempT v T?)) (hv : A.val v) (x : Hint) (p : Bool) :
    FSt (A :: Γ) { st with env := Env.pushBindE st.env x (some A.ty) v p A.rd } := by
  have hne : 0 < st.env.size := by have := hF.frame; rwa [size_withTempT] at this
  obtain ⟨fr, hfr⟩ : ∃ fr, st.env[st.env.size - 1]? = some fr :=
    ⟨_, Array.getElem?_eq_getElem (by omega : st.env.size - 1 < st.env.size)⟩
  -- the state with the value in flight: the old positions, and the new temporary
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
  have hWT : Pos.temp (st.env.size - 1) fr.temps.size ∈ allPos (st.withTempT v T?).env := by rw [hWpos]; simp
  have hWcases : ∀ q, q ∈ allPos (st.withTempT v T?).env → q = .temp (st.env.size - 1) fr.temps.size ∨ q ∈ allPos st.env := by
    intro q hq; rw [hWpos, List.mem_append, List.mem_singleton] at hq; exact hq.symm
  have hfrW : (st.withTempT v T?).env[(st.withTempT v T?).env.size - 1]? =
      some { fr with temps := fr.temps.push v, tempTys := fr.tempTys.push T? } := by
    simp only [MState.withTempT, Array.size_modify, Array.getElem?_modify, if_true, hfr]; rfl
  -- the state after the push: the old positions, and the new binding
  obtain ⟨A₀, B₀, hA₀, hB₀⟩ := allPos_pushBindE st.env x (some A.ty) v p A.rd fr hfr hne
  have hnewNot : Pos.bind (st.env.size - 1) fr.binds.size ∉ allPos st.env := by
    rw [hA₀]; exact new_not_mem_pushBindE st.env x (some A.ty) v p A.rd fr hB₀
  have hPmem : ∀ q, q ∈ allPos (Env.pushBindE st.env x (some A.ty) v p A.rd) ↔
      q = .bind (st.env.size - 1) fr.binds.size ∨ q ∈ allPos st.env := by
    intro q; rw [hB₀, hA₀]; simp only [List.mem_append, List.mem_cons]
    constructor
    · rintro (h | h | h)
      · exact .inr (.inl h)
      · exact .inl h
      · exact .inr (.inr h)
    · rintro (h | h | h)
      · exact .inr (.inl h)
      · exact .inl h
      · exact .inr (.inr h)
  have hPnew : valAt (Env.pushBindE st.env x (some A.ty) v p A.rd) (.bind (st.env.size - 1) fr.binds.size) = v :=
    valAt_pushBindE_new st.env x _ v p A.rd fr hfr
  have hPold : ∀ q, q ∈ allPos st.env → valAt (Env.pushBindE st.env x (some A.ty) v p A.rd) q = valAt st.env q :=
    fun q hq => valAt_pushBindE_ne st.env x _ v p A.rd fr hfr q (fun e => hnewNot (e ▸ hq))
  have hvF : FVal v := by
    cases A with
    | nat => exact .num hv
    | unit => cases hv; exact .unit
    | ref => obtain ⟨l, c, rfl, hc⟩ := hv; exact .bor l hc
  have hvnl : ∀ m, v ≠ .loan m := fun m e => by
    subst e
    cases A with
    | nat => cases hv
    | unit => cases hv
    | ref => obtain ⟨_, _, h, _⟩ := hv; cases h
  -- each position after the push and its counterpart with the value in flight
  have hmap : ∀ q, q ∈ allPos (Env.pushBindE st.env x (some A.ty) v p A.rd) →
      ∃ q', q' ∈ allPos (st.withTempT v T?).env ∧
        valAt (st.withTempT v T?).env q' = valAt (Env.pushBindE st.env x (some A.ty) v p A.rd) q ∧
        (q = .bind (st.env.size - 1) fr.binds.size ↔ q' = .temp (st.env.size - 1) fr.temps.size) ∧
        (q ∈ allPos st.env → q' = q) := by
    intro q hq
    rcases (hPmem q).mp hq with rfl | hq'
    · exact ⟨_, hWT, by rw [hWnew, hPnew], ⟨fun _ => rfl, fun _ => rfl⟩, fun h => absurd h hnewNot⟩
    · exact ⟨q, hWmem q hq', by rw [hWold q hq', hPold q hq'],
        ⟨fun e => absurd (e ▸ hq') hnewNot, fun e => absurd e (hntq q hq')⟩, fun _ => rfl⟩
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
  have hlkP : ∀ f j, Pos.bind f j ∈ allPos st.env →
      (Env.pushBindE st.env x (some A.ty) v p A.rd)[f]?.bind (fun fr : Frame => fr.binds[j]?) =
        (st.withTempT v T?).env[f]?.bind (fun fr : Frame => fr.binds[j]?) := fun f j hq => by
    rw [bind_pushBindE_ne st.env x _ v p A.rd fr hfr f j (fun e => hnewNot (e ▸ hq)),
      lookup_congr (binds_withTempT st v T?) f j]
  refine ⟨fun q hq => ?_, fun f i hq => ?_, fun q q' l hq hq' e e' => ?_, fun q q' l w w' hq hq' e e' => ?_,
    fun q l hq e => ?_, fun q l c hq e => ?_, fun i B hi => ?_, fun f j f' j' l c hq hq' e e' => ?_,
    fun f j b l hb e => ?_, ?_⟩
  · -- vals
    obtain ⟨q', hq', hv', -, -⟩ := hmap q hq
    rw [← hv']; exact hF.vals q' hq'
  · -- temps
    have hq' : Pos.temp f i ∈ allPos st.env := ((hPmem _).mp hq).resolve_left (fun e => by cases e)
    show (valAt (Env.pushBindE st.env x (some A.ty) v p A.rd) (.temp f i)).Num ∨ _ = Value.unit
    rw [hPold _ hq']
    rcases hF.temps f i (hWmem _ hq') with h | h | ⟨l, c, h⟩
    · left; rwa [hWold _ hq'] at h
    · right; rwa [hWold _ hq'] at h
    · obtain ⟨f', j', e⟩ := hbind _ l c hq' (by rw [← hWold _ hq']; exact h); cases e
  · -- loan1
    have hq₁ : q ∈ allPos st.env := ((hPmem _).mp hq).resolve_left (fun e' => by subst e'; rw [hPnew] at e; exact hvnl l e)
    have hq₂ : q' ∈ allPos st.env := ((hPmem _).mp hq').resolve_left (fun e' => by subst e'; rw [hPnew] at e'; exact hvnl l e')
    rw [hPold _ hq₁] at e; rw [hPold _ hq₂] at e'
    exact hF.loan1 q q' l (hWmem _ hq₁) (hWmem _ hq₂) (by rw [hWold _ hq₁]; exact e) (by rw [hWold _ hq₂]; exact e')
  · -- bor1
    obtain ⟨m₁, hm₁, hv₁, hn₁, ho₁⟩ := hmap q hq
    obtain ⟨m₂, hm₂, hv₂, hn₂, ho₂⟩ := hmap q' hq'
    have := hF.bor1 m₁ m₂ l w w' hm₁ hm₂ (by rw [hv₁]; exact e) (by rw [hv₂]; exact e')
    rcases (hPmem _).mp hq with h1 | h1 <;> rcases (hPmem _).mp hq' with h2 | h2
    · rw [h1, h2]
    · exact absurd (this ▸ hn₁.mp h1) (by rw [ho₂ h2]; exact hntq _ h2)
    · exact absurd (this.symm ▸ hn₂.mp h2) (by rw [ho₁ h1]; exact hntq _ h1)
    · rw [← ho₁ h1, ← ho₂ h2]; exact this
  · -- held
    have hq₁ : q ∈ allPos st.env := ((hPmem _).mp hq).resolve_left (fun e' => by subst e'; rw [hPnew] at e; exact hvnl l e)
    rw [hPold _ hq₁] at e
    obtain ⟨q', c, hq', hy⟩ := hF.held q l (hWmem _ hq₁) (by rw [hWold _ hq₁]; exact e)
    rcases hWcases q' hq' with rfl | hq''
    · rw [hWnew] at hy
      exact ⟨_, _, c, (hPmem _).mpr (.inl rfl), by rw [hPnew]; exact hy⟩
    · rw [hWold _ hq''] at hy
      obtain ⟨f', j', rfl⟩ := hbind _ l c hq'' hy
      exact ⟨f', j', c, (hPmem _).mpr (.inr hq''), by rw [hPold _ hq'']; exact hy⟩
  · -- lender
    obtain ⟨m₁, hm₁, hv₁, -, -⟩ := hmap q hq
    obtain ⟨q', hq', hx⟩ := hF.lender m₁ l c hm₁ (by rw [hv₁]; exact e)
    rcases hWcases q' hq' with rfl | hq''
    · rw [hWnew] at hx; exact absurd hx (hvnl l)
    · exact ⟨q', (hPmem _).mpr (.inr hq''), by rw [hPold _ hq'', ← hWold _ hq'']; exact hx⟩
  · -- top
    obtain ⟨h0, hS⟩ := ckVarPos_pushBindE hfr x (some A.ty) v p A.rd
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
      subst hi
      refine ⟨_, _, _, h0, bind_pushBindE_new st.env x _ v p A.rd fr hfr, rfl, rfl, ?_⟩
      cases A with
      | nat => exact .inl hv
      | unit => exact .inl hv
      | ref => obtain ⟨l, c, rfl, hc⟩ := hv; exact .inr ⟨l, c, rfl, hc⟩
    | succ i =>
      simp only [List.getElem?_cons_succ] at hi
      obtain ⟨f, j, b, hck, hlk, h1, h2, h3⟩ := hF.top i B hi
      have hck' : ckVarPos st.env i = some (.bind f j) := by
        rw [← ckVarPos_congr (size_withTempT st v T?) (binds_withTempT st v T?)]; exact hck
      have hq : Pos.bind f j ∈ allPos st.env := ckVarPos_mem hck'
      exact ⟨f, j, b, by rw [hS]; exact hck', by rw [hlkP f j hq]; exact hlk, h1, h2, h3⟩
  · -- order
    have hq₁ : Pos.bind f j ∈ allPos st.env :=
      ((hPmem _).mp hq).resolve_left (fun e'' => by rw [e'', hPnew] at e; exact hvnl l e)
    rw [hPold _ hq₁] at e
    rcases (hPmem _).mp hq' with h2 | h2
    · obtain ⟨rfl, rfl⟩ : f' = st.env.size - 1 ∧ j' = fr.binds.size := by cases h2; exact ⟨rfl, rfl⟩
      obtain ⟨fr', b', hf', hj'⟩ := mem_allPos_bind _ _ _ hq₁
      have hflt := lt_of_getElem? hf'
      by_cases hfe : f = st.env.size - 1
      · subst hfe; rw [hfr] at hf'; cases hf'; exact .inr ⟨rfl, lt_of_getElem? hj'⟩
      · exact .inl (by omega)
    · rw [hPold _ h2] at e'
      exact hF.order f j f' j' l c (hWmem _ hq₁) (hWmem _ h2) (by rw [hWold _ hq₁]; exact e) (by rw [hWold _ h2]; exact e')
  · -- lent
    have hpos := (lookup_pos hb)
    have hq₁ : Pos.bind f j ∈ allPos st.env :=
      ((hPmem _).mp hpos.1).resolve_left (fun e'' => by
        have := hpos.2; rw [e'', hPnew, e] at this; exact hvnl l this)
    exact hF.lent f j b l (by rw [← hlkP f j hq₁]; exact hb) e
  · -- frame
    show 0 < (Env.pushBindE st.env x (some A.ty) v p A.rd).size
    simp [Env.pushBindE]; exact hne

section
variable {K : RunCtx} {ρ : Assignment} {φ : Future}

/-- **The fragment's `let x = u; w`, at `evalCore`**, at every type of the right-hand side and the
tail: from the steps of `u` (at the starting context) and of `w` (at every extension), the run facts
`FragRun`, the decisions `FragDec`, and the facts about the checker the push and the drop use. -/
theorem letF_core (hL : LetInv) (hR : FragRun K.D) (hdec : FragDec K.D) (hDN : DropNoopInv)
    (hDB : DropBorrowInv) (hDL : DropLentFail) (hI : InvSteps) (hIU : InvPopUnit) (hIBU : InvBindUnit)
    (hIE : InvEnd) (hPL : PlaceLocal K.D) (hc : Strict.FundCtx K)
    {Γ : List FT} {x : Hint} {u w : Term} {A B : FT} (hu : FTy Γ u A) (hw : FTy (A :: Γ) w B) {m : Nat}
    (ihu : EvalSim K ρ φ m u (FSt Γ) (· = true))
    (ihw : ∀ (Δ' : Nat → TyS) (ρ' : Assignment), EvalSim { K with Δ := Δ' } ρ' φ m w (FSt (A :: Γ)) (· = true)) :
    CoreSim K ρ φ (m + 1) (.letIn x u w) (FSt Γ) (· = true) := by
  intro st st' typed hint v T? s π hPst hty hm htn htd hcd hp hr hS hv hab hnh hfl hok hD bh h
  subst hty
  obtain ⟨du, st₀, st₁, stB, st₂, st₃, v₀, r, T₀, p, bh₁, bh₂, bh₃, hk₀, hm₀, htn₀, htd₀, htdB, hru, hdu,
    hkB, hmeB, htnB, hrw, hrd, hk₃, -, hD₁, hD₂⟩ := hL m x u w hint st st' bh v T? K.D hm htn htd hD h
  have hP₀ : FSt Γ st₀ := hPst.kern hk₀
  obtain ⟨rfl, hv₀, hme₁, hrd₁, hsz₁, hF₁⟩ := hR Γ u A m none st₀ st₁ bh₁ v₀ T₀ hu hP₀ (hp.of_kern hk₀).inv.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hm₀ (.inl htd₀) hD₁ hru
  have hm₁ : Mode st₁ := hm₀.of_modeEq hme₁
  have hmB : Mode stB := hm₁.of_modeEq hmeB
  have hduA : du = A.rd := hdu.symm.trans (hdec Γ u A st hu hPst).2
  have hne₁ : 0 < st₁.env.size := by rw [hsz₁]; exact hP₀.frame
  have hvu : u.valsOk (Strict.ValsP K ρ φ) := hu.valsOk _
  have hvw : w.valsOk (Strict.ValsP K ρ φ) := hw.valsOk _
  -- the step for `u`
  have hOu := ihu st₀ st₁ true none v₀ (some A.ty) s π hP₀ rfl hm₀ (.inl htd₀) (hp.of_kern hk₀)
    (hr.of_kern hk₀) hS hvu (fun σ hσ => hu.absBelow _ σ hσ) hu.noHole
    (by rw [scopeOf_rel hr]; exact (hdec Γ u A st hu hPst).1) (fun e => by cases e) hD₁ bh₁ hru
  rw [htn₀] at hOu
  obtain ⟨ρ₁, Δ₁, π₁, ru, s₁, he₁, hxu, hmu, hau, hlu, hp₁, hr₁⟩ := hOu
  have hxu' : runT K ρ φ false (.plain TyM.err) u s = some (ru, s₁) := hxu
  obtain ⟨hgu, hlabu, hlouu, hS₁⟩ := Strict.fund_all hc u hvu false (.plain TyM.err) s s₁ ru hS hxu'
  -- the push, on both sides
  have hkB' : Kern { st₁ with env := Env.pushBindE st₁.env x (some A.ty) v₀ p A.rd } stB := by rw [← hduA]; exact hkB
  obtain ⟨hpB, hrB, hSB⟩ := push_frag (K := { K with Δ := Δ₁ }) (ρ := ρ₁) (π := π₁) hI hIBU hPL hv₀ hne₁ hF₁ hp₁
    hr₁ hS₁ hmu (hau _ rfl) hlu hgu hlabu hlouu hkB'
  have hpb : pushBindShaped s₁ { ty := ru.2, val := fun _ => ru.1, decl := K.D.declOf (scopeOf s) u } =
      pushBindShaped s₁ { ty := ru.2, val := fun _ => ru.1, decl := A.rd } := by
    rw [scopeOf_rel hr, hdu, hduA]
  have hPB : FSt (A :: Γ) stB := (fst_push hF₁ hv₀ x p).kern hkB'
  -- the step for `w`, at the extended context
  have htdB' : stB.tailDecl = none ∨ stB.tailDecl = some (K.D.declOf (DecideScope.topReadings stB) w) :=
    .inr (by rw [htdB, hcd, (hdec Γ _ B st (.letIn Γ x u w A B hu hw) hPst).2, (hdec (A :: Γ) w B stB hw hPB).2])
  have hOw := ihw Δ₁ ρ₁ stB st₂ true none r T? _ π₁ hPB rfl hmB htdB' hpB hrB hSB (hw.valsOk _)
    (fun σ hσ => hw.absBelow _ σ hσ) hw.noHole (by rw [scopeOf_rel hrB]; exact (hdec (A :: Γ) w B stB hw hPB).1)
    (fun e => by cases e) hD₂ bh₂ hrw
  rw [htnB] at hOw
  obtain ⟨ρ₂, Δ₂, π₂, rw', s₂, he₂, hxw, hmw, haw, hlw, hp₂, hr₂⟩ := hOw
  have hxw' : runT K ρ φ st.curTail (.plain TyM.err) w
      (pushBindShaped s₁ { ty := ru.2, val := fun _ => ru.1, decl := A.rd }) = some (rw', s₂) := by
    rw [← wcong (fun m' => hw.absBelow m') Δ₁ ρ₁]; exact hxw
  obtain ⟨-, -, -, hS₂⟩ := Strict.fund_all hc w hvw st.curTail (.plain TyM.err) _ s₂ rw' hSB hxw'
  obtain ⟨-, -, -, -, hszW, hF₂⟩ := hR (A :: Γ) w B m none stB st₂ bh₂ r T? hw hPB hpB.inv.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hmB htdB' hD₂ hrw
  -- the drop
  obtain ⟨s₃, hLD, htt, ⟨hga, hgl⟩, hP₃, hR₃⟩ := drop_frag (K := { K with Δ := Δ₂ }) (ρ := ρ₂) (π := π₂)
    hDN hDB hDL hI hIU hIE hPL hF₂ hp₂ hr₂ hS₂ hrd
  have hne₂ : 0 < st₂.env.size := by rw [hszW]; exact hPB.frame
  obtain rfl : v = r := popped_of_topTemps hne₂ htt hk₃
  have hext : Ext K ρ π st st' ρ₂ Δ₂ π₂ :=
    (he₁.congr hk₀.absTy hk₀.nextLoan hkB.absTy hkB.nextLoan).trans
      ((he₂.grow hga hgl).congr rfl rfl (by rw [hk₃.absTy]; rfl) (by rw [hk₃.nextLoan]; rfl))
  refine ⟨ρ₂, Δ₂, π₂, rw', s₃, hext, ?_, hmw, haw, hlw, hP₃.of_kern hk₃, hR₃.of_kern hk₃⟩
  -- the reference's `let`
  rw [runT_letIn _ _ x u w s hfl, hxu']
  simp only [bind, Option.bind]
  rw [hpb, frag_hint (K := K) (ρ := ρ) (φ := φ) hw _ _ (.plain TyM.err), hxw']
  obtain ⟨frs, hlast, ⟨hsh, hok, rfl⟩ | ⟨L, hsh, hok, rfl⟩⟩ := hLD
  · simp only [hlast, hsh]; rw [if_pos (show LetLendersOk K φ s₂ from hok)]
  · simp only [hlast, hsh]; rw [if_pos (show EndOk K φ s₂ L from hok)]

end

end Ochr.Meaning.Steps.Form

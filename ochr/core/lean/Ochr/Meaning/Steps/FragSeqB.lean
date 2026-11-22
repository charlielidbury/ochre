import Ochr.Meaning.Steps.FragSeq
import Ochr.Meaning.Steps.FragBorrow
import Ochr.Meaning.Steps.Machine.InvSteps

/-!
# The fragment's `u; w` after a borrow (lead12)

`u`'s value, `borrow_l c`, is dropped: the discard ends `l` (the lender `px` gets `c` back, the parked
holder `⊥`, `SeqBorInv`), on the reference's side `discardEnd` ends `π l` at its holder. The relation
across the end is `FragEnd.rel_end` with the holder the value in flight; the `⊥` left in flight is
then popped (`Value.inert_bot`, `rel_of_withTemp_inert`), and the state is a fragment state again
(`FStT.endTemp`).
-/

namespace Ochr.Meaning.Steps.Form

open Ochr Ochr.Meaning Ochr.Meaning.Steps
open Classical

theorem push_setIfInBounds (a : Array Value) (v w : Value) : (a.push v).setIfInBounds a.size w = a.push w := by
  apply Array.ext_getElem?; intro i
  simp only [Array.getElem?_setIfInBounds, Array.getElem?_push, Array.size_push]
  by_cases h : i = a.size
  · subst h; simp
  · simp [h, Ne.symm h]

/-- **The end of the borrow in flight**: its holder, the new temporary, set to `⊥` and its lender `x`
given `c` back, is `x := c` with `⊥` in flight. -/
theorem endE_withTempT {st : MState} {fr : Frame} (hfr : st.env[st.env.size - 1]? = some fr) (f j : Nat)
    (v c : Value) (T? : Option Value) :
    endE (st.withTempT v T?).env (.bind f j) (.temp (st.env.size - 1) fr.temps.size) c =
      (({ st with env := Env.setAtE st.env (.bind f j) c } : MState).withTempT .bot T?).env := by
  apply Array.ext_getElem?
  intro a
  simp only [endE, Env.setAtE, MState.withTempT, Array.getElem?_modify, Array.size_modify]
  by_cases ha : st.env.size - 1 = a
  · subst ha
    rw [hfr]
    by_cases hf : f = st.env.size - 1
    · subst hf; simp [push_setIfInBounds]
    · simp [hf, push_setIfInBounds]
  · simp [ha]

theorem top_of_erase_temps {E E' : Env} {fr : Frame} (he : E.erase = E'.erase) (hfr : E[E.size - 1]? = some fr) :
    ∃ fr', E'[E'.size - 1]? = some fr' ∧ fr'.temps = fr.temps := by
  have hs : E'.size = E.size := by rw [← Env.erase_size E', ← he, Env.erase_size]
  have := Env.erase_get? E (E.size - 1)
  rw [he, Env.erase_get?, hfr] at this
  rcases h' : E'[E.size - 1]? with _ | fr'
  · rw [h'] at this; cases this
  · rw [h'] at this
    refine ⟨fr', by rw [hs]; exact h', ?_⟩
    have := congrArg (Option.map Frame.temps) this
    simpa [Frame.erase] using this

/-- A write keeps every binding (with its stored type and reading). -/
theorem lookup_setAtE_fwd {env : Env} {p : Pos} {v : Value} {f i : Nat} {b : Binding}
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

/-- **A fragment state with a borrow in flight, after the discard ends it**: the lender `x` given the
content `c` back and the value popped, a fragment state again. -/
theorem FStT.endTemp {Γ : List FT} {st : MState} {l : Nat} {c : Value} {T? : Option Value}
    (hF : FStT Γ (st.withTempT (.borrow l c) T?)) (hc : c.Num) {f₀ j₀ : Nat}
    (hpx : Pos.bind f₀ j₀ ∈ allPos st.env) (hx : valAt st.env (.bind f₀ j₀) = .loan l) :
    FSt Γ { st with env := (Env.setAtE st.env (.bind f₀ j₀) c) } := by
  have hne : 0 < st.env.size := by have := hF.frame; rwa [size_withTempT] at this
  obtain ⟨fr, hfr⟩ : ∃ fr, st.env[st.env.size - 1]? = some fr :=
    ⟨_, Array.getElem?_eq_getElem (by omega : st.env.size - 1 < st.env.size)⟩
  have hWpos : allPos (st.withTempT (.borrow l c) T?).env = allPos st.env ++ [.temp (st.env.size - 1) fr.temps.size] := by
    rw [allPos_withTempT, allPos_pushTempE _ _ fr hfr hne]
  have hWnew : valAt (st.withTempT (.borrow l c) T?).env (.temp (st.env.size - 1) fr.temps.size) = .borrow l c := by
    rw [valAt_withTempT, valAt_pushTempE_new _ _ fr hfr]
  have hntq : ∀ q, q ∈ allPos st.env → q ≠ .temp (st.env.size - 1) fr.temps.size := fun q hq e => by
    rw [e] at hq; obtain ⟨fr', hf', hi⟩ := mem_allPos_temp st.env _ _ hq
    rw [hfr] at hf'; cases hf'; exact absurd hi (Nat.lt_irrefl _)
  have hWold : ∀ q, q ∈ allPos st.env → valAt (st.withTempT (.borrow l c) T?).env q = valAt st.env q := by
    intro q hq; rw [valAt_withTempT]
    cases q with
    | bind f i => exact valAt_pushTempE_bind _ _ f i
    | temp f i => exact valAt_pushTempE_old _ _ fr hfr f i (hntq _ hq)
  have hWmem : ∀ q, q ∈ allPos st.env → q ∈ allPos (st.withTempT (.borrow l c) T?).env := fun q hq => by
    rw [hWpos]; exact List.mem_append_left _ hq
  have hNmem : Pos.temp (st.env.size - 1) fr.temps.size ∈ allPos (st.withTempT (.borrow l c) T?).env := by
    rw [hWpos]; exact List.mem_append_right _ (List.mem_singleton_self _)
  have hWcases : ∀ q, q ∈ allPos (st.withTempT (.borrow l c) T?).env → q = .temp (st.env.size - 1) fr.temps.size ∨ q ∈ allPos st.env := by
    intro q hq; rw [hWpos, List.mem_append, List.mem_singleton] at hq; exact hq.symm
  have hfrW : (st.withTempT (.borrow l c) T?).env[(st.withTempT (.borrow l c) T?).env.size - 1]? =
      some { fr with temps := fr.temps.push (.borrow l c), tempTys := fr.tempTys.push T? } := by
    simp only [MState.withTempT, Array.size_modify, Array.getElem?_modify, if_true, hfr]; rfl
  -- a borrow at an old position is at a binding
  have hbind : ∀ q m w, q ∈ allPos st.env → valAt st.env q = .borrow m w → ∃ f j, q = .bind f j := by
    intro q m w hq e
    cases q with
    | bind f j => exact ⟨f, j, rfl⟩
    | temp f i =>
      obtain ⟨h1, h2⟩ := hF.tempLast f i m w (hWmem _ hq) (by rw [hWold _ hq]; exact e) _ hfrW
      rw [size_withTempT] at h1
      simp only [Array.size_push] at h2
      exact absurd (by rw [h1, h2]; rfl) (hntq _ hq)
  -- `l`: lent at `x` only, held in flight only
  have hnoB : ∀ q, q ∈ allPos st.env → ∀ w, valAt st.env q ≠ .borrow l w := fun q hq w e =>
    hntq q hq (hF.bor1 q _ l w c (hWmem _ hq) hNmem (by rw [hWold _ hq]; exact e) hWnew)
  have hx1 : ∀ q, q ∈ allPos st.env → valAt st.env q = .loan l → q = .bind f₀ j₀ := fun q hq e =>
    hF.loan1 q _ l (hWmem _ hq) (hWmem _ hpx) (by rw [hWold _ hq]; exact e) (by rw [hWold _ hpx]; exact hx)
  -- the environment after
  have hA : allPos (Env.setAtE st.env (.bind f₀ j₀) c) = allPos st.env := allPos_setAtE _ _ _
  have hV : ∀ q, valAt (Env.setAtE st.env (.bind f₀ j₀) c) q = if q = .bind f₀ j₀ then c else valAt st.env q := fun q => by
    split
    · next e => rw [e]; exact valAt_setAtE_self _ hpx
    · next e => exact valAt_setAtE_other _ _ _ _ e
  have hcL : ∀ m, c ≠ .loan m := fun m e => by rw [e] at hc; cases hc
  have hcB : ∀ m w, c ≠ .borrow m w := fun m w e => by rw [e] at hc; cases hc
  -- an old value at a position other than `x`
  have hVo : ∀ q, q ≠ .bind f₀ j₀ → valAt (Env.setAtE st.env (.bind f₀ j₀) c) q = valAt st.env q := fun q hq => by rw [hV, if_neg hq]
  have hVW : ∀ q, q ∈ allPos st.env → q ≠ .bind f₀ j₀ → valAt (Env.setAtE st.env (.bind f₀ j₀) c) q = valAt (st.withTempT (.borrow l c) T?).env q :=
    fun q hq hqx => by rw [hVo q hqx, hWold q hq]
  have hnxL : ∀ q m, valAt (Env.setAtE st.env (.bind f₀ j₀) c) q = .loan m → q ≠ .bind f₀ j₀ := fun q m e hq => by
    rw [hq, hV, if_pos rfl] at e; exact hcL m e
  have hnxB : ∀ q m w, valAt (Env.setAtE st.env (.bind f₀ j₀) c) q = .borrow m w → q ≠ .bind f₀ j₀ := fun q m w e hq => by
    rw [hq, hV, if_pos rfl] at e; exact hcB m w e
  have hWL : st.env.size = (st.withTempT (.borrow l c) T?).env.size := (size_withTempT st _ T?).symm
  refine ⟨fun q hq => ?_, fun f i hq => ?_, fun q q' m hq hq' e e' => ?_, fun q q' m w w' hq hq' e e' => ?_,
    fun q m hq e => ?_, fun q m c' hq e => ?_, fun i B hi => ?_, fun f j f' j' m c' hq hq' e e' => ?_,
    fun f j b m hb e => ?_, by simp only [Env.setAtE, Array.size_modify]; exact hne⟩
  · rw [hA] at hq
    rw [hV]; split
    · exact .num hc
    · rw [← hWold q hq]; exact hF.vals q (hWmem q hq)
  · rw [hA] at hq
    rw [hVo _ (by simp)]
    rcases hF.temps f i (hWmem _ hq) with h | h | ⟨m, w, h⟩
    · left; rwa [hWold _ hq] at h
    · right; rwa [hWold _ hq] at h
    · obtain ⟨f', j', e⟩ := hbind _ m w hq (by rw [← hWold _ hq]; exact h); cases e
  · rw [hA] at hq hq'
    have h1 := hnxL q m e
    have h2 := hnxL q' m e'
    rw [hVW q hq h1] at e; rw [hVW q' hq' h2] at e'
    exact hF.loan1 q q' m (hWmem _ hq) (hWmem _ hq') e e'
  · rw [hA] at hq hq'
    have h1 := hnxB q m w e
    have h2 := hnxB q' m w' e'
    rw [hVW q hq h1] at e; rw [hVW q' hq' h2] at e'
    exact hF.bor1 q q' m w w' (hWmem _ hq) (hWmem _ hq') e e'
  · rw [hA] at hq
    have h1 := hnxL q m e
    rw [hVo q h1] at e
    have hml : m ≠ l := fun hm => h1 (hx1 q hq (hm ▸ e))
    obtain ⟨q', c', hq', hy⟩ := hF.held q m (hWmem _ hq) (by rw [hWold _ hq]; exact e)
    rcases hWcases q' hq' with rfl | hq''
    · rw [hWnew] at hy; cases hy; exact absurd rfl hml
    · rw [hWold _ hq''] at hy
      obtain ⟨f', j', rfl⟩ := hbind _ m c' hq'' hy
      have hne' : Pos.bind f' j' ≠ .bind f₀ j₀ := fun e' => by rw [e', hx] at hy; cases hy
      exact ⟨f', j', c', by rw [hA]; exact hq'', by rw [hVo _ hne']; exact hy⟩
  · rw [hA] at hq
    have h1 := hnxB q m c' e
    rw [hVo q h1] at e
    have hml : m ≠ l := fun hm => hnoB q hq c' (hm ▸ e)
    obtain ⟨q', hq', hxq⟩ := hF.lender q m c' (hWmem _ hq) (by rw [hWold _ hq]; exact e)
    rcases hWcases q' hq' with rfl | hq''
    · rw [hWnew] at hxq; cases hxq
    · rw [hWold _ hq''] at hxq
      have hne' : q' ≠ .bind f₀ j₀ := fun e' => by rw [e', hx] at hxq; cases hxq; exact hml rfl
      exact ⟨q', by rw [hA]; exact hq'', by rw [hVo _ hne']; exact hxq⟩
  · obtain ⟨f, j, b, hck, hlk, h1, h2, h3⟩ := hF.top i B hi
    have hck' : ckVarPos st.env i = some (.bind f j) := by
      rw [← ckVarPos_congr (size_withTempT st (.borrow l c) T?) (binds_withTempT st (.borrow l c) T?)]; exact hck
    have hlk' : st.env[f]?.bind (fun fr : Frame => fr.binds[j]?) = some b := by
      rw [← lookup_congr (binds_withTempT st (.borrow l c) T?)]; exact hlk
    obtain ⟨b', hb', ht', hd'⟩ := lookup_setAtE_fwd (p := .bind f₀ j₀) (v := c) hlk'
    obtain ⟨-, hvb⟩ := lookup_pos hb'
    obtain ⟨-, hvb0⟩ := lookup_pos hlk'
    refine ⟨f, j, b', by rw [Machine.ckVarPos_setAtE]; exact hck', hb', by rw [ht']; exact h1, by rw [hd']; exact h2, ?_⟩
    rw [← hvb, hV]
    split
    · next e =>
      have hbx : b.val = .loan l := by rw [← hvb0, e, hx]
      have := (hF.lent f j b l (by rw [lookup_congr (binds_withTempT st (.borrow l c) T?)]; exact hlk') hbx).1
      rw [h1] at this
      cases B with
      | nat => exact .inl hc
      | unit => simp [FT.ty] at this
      | ref => simp [FT.ty] at this
    · rw [hvb0]; exact h3
  · rw [hA] at hq hq'
    have h1 := hnxL _ m e
    have h2 := hnxB _ m c' e'
    exact hF.order f j f' j' m c' (hWmem _ hq) (hWmem _ hq') (by rw [← hVW _ hq h1]; exact e)
      (by rw [← hVW _ hq' h2]; exact e')
  · obtain ⟨b₀, hb₀, ht₀, hd₀⟩ := lookup_setAtE_decl hb
    have hp0 := lookup_pos hb
    have hne' : Pos.bind f j ≠ .bind f₀ j₀ := hnxL _ m (by rw [hp0.2]; exact e)
    have hv0 : b₀.val = .loan m := by rw [← (lookup_pos hb₀).2, ← hVo _ hne', hp0.2, e]
    obtain ⟨t1, t2⟩ := hF.lent f j b₀ m (by rw [lookup_congr (binds_withTempT st (.borrow l c) T?)]; exact hb₀) hv0
    exact ⟨by rw [← ht₀]; exact t1, by rw [← hd₀]; exact t2⟩

section
variable {K : RunCtx} {ρ : Assignment} {φ : Future}

/-- **The fragment's `u; w` after a borrow, at `evalCore`**: the step for `u` (a borrow `borrow_l c` in
flight, lent by a number binding `x`), the discard (`SeqBorInv`: after a quiet stretch, `x` gets `c`
back; the reference's `discardEnd` ends `π l` at its holder, strictly by `end_ok`; the relation by
`rel_end` with the holder in flight, then `⊥` popped), then the step for `w` from a fragment state
(`FStT.endTemp`). Assumes `SeqBorInv`, `FragRun`, `FragDec`, `InvEnd` (the end at a temporary
holder), `InvPopBot`, `PlaceLocal`. -/
theorem seqB_core (hSB : SeqBorInv) (hR : FragRun K.D) (hdec : FragDec K.D) (hIE : InvEnd) (hIPB : InvPopBot)
    (hPL : PlaceLocal K.D) (hc : Strict.FundCtx K) {Γ : List FT} {u w : Term} {B : FT} (hu : FTy Γ u .ref)
    (hw : FTy Γ w B) {m : Nat} (ihu : EvalSim K ρ φ m u (FSt Γ) (· = true))
    (ihw : ∀ (Δ' : Nat → TyS) (ρ' : Assignment), EvalSim { K with Δ := Δ' } ρ' φ m w (FSt Γ) (· = true)) :
    CoreSim K ρ φ (m + 1) (.seq u w) (FSt Γ) (· = true) := by
  intro st st' typed hint v T? s π hPst hty hm htn htd hcd hp hr hS hv hab hnh hfl hok hD bh h
  subst hty
  obtain ⟨st₀, st₁, stW, v₀, T₀, bh₁, bh₂, hk₀, hm₀, htn₀, htd₀, htdW, hru, hD₁, hdrop, htnW, hrw⟩ :=
    hSB m u w hint st st' bh v T? K.D hm htn htd hD h
  have hP₀ : FSt Γ st₀ := hPst.kern hk₀
  obtain ⟨rfl, ⟨l, c, rfl, hcN⟩, hme₁, -, -, hF₁⟩ := hR Γ u .ref m none st₀ st₁ bh₁ v₀ T₀ hu hP₀ (hp.of_kern hk₀).inv.2.2.2.2.2.2.2.2.2.2.2.2.2 hm₀ (.inl htd₀) hD₁ hru
  -- the step for `u`
  have hOu := ihu st₀ st₁ true none (.borrow l c) (some FT.ref.ty) s π hP₀ rfl hm₀ (.inl htd₀) (hp.of_kern hk₀)
    (hr.of_kern hk₀) hS (hu.valsOk _) (fun σ hσ => hu.absBelow _ σ hσ) hu.noHole
    (by rw [scopeOf_rel hr]; exact (hdec Γ u .ref st hu hPst).1) (fun e => by cases e) hD₁ bh₁ hru
  rw [htn₀] at hOu
  obtain ⟨ρ₁, Δ₁, π₁, ru, s₁, he₁, hxu, -, -, hlu, hp₁, hr₁⟩ := hOu
  have hxu' : runT K ρ φ false (.plain TyM.err) u s = some (ru, s₁) := hxu
  obtain ⟨-, -, -, hS₁⟩ := Strict.fund_all hc u (hu.valsOk _) false (.plain TyM.err) s s₁ ru hS hxu'
  -- the borrow in flight, its lender `x`
  have hne : 0 < st₁.env.size := by have := hF₁.frame; rwa [size_withTempT] at this
  obtain ⟨fr, hfr⟩ : ∃ fr, st₁.env[st₁.env.size - 1]? = some fr :=
    ⟨_, Array.getElem?_eq_getElem (by omega : st₁.env.size - 1 < st₁.env.size)⟩
  have hWpos : allPos (st₁.withTempT (.borrow l c) (some FT.ref.ty)).env = allPos st₁.env ++ [(.temp (st₁.env.size - 1) fr.temps.size)] := by
    rw [allPos_withTempT, allPos_pushTempE _ _ fr hfr hne]
  have hWnew : valAt (st₁.withTempT (.borrow l c) (some FT.ref.ty)).env (.temp (st₁.env.size - 1) fr.temps.size) = .borrow l c := by rw [valAt_withTempT, valAt_pushTempE_new _ _ fr hfr]
  have hntq : ∀ q, q ∈ allPos st₁.env → q ≠ (.temp (st₁.env.size - 1) fr.temps.size) := fun q hq e => by
    rw [e] at hq; obtain ⟨fr', hf', hi⟩ := mem_allPos_temp st₁.env _ _ hq
    rw [hfr] at hf'; cases hf'; exact absurd hi (Nat.lt_irrefl _)
  have hWold : ∀ q, q ∈ allPos st₁.env → valAt (st₁.withTempT (.borrow l c) (some FT.ref.ty)).env q = valAt st₁.env q := by
    intro q hq; rw [valAt_withTempT]
    cases q with
    | bind f i => exact valAt_pushTempE_bind _ _ f i
    | temp f i => exact valAt_pushTempE_old _ _ fr hfr f i (hntq _ hq)
  have hWmem : ∀ q, q ∈ allPos st₁.env → q ∈ allPos (st₁.withTempT (.borrow l c) (some FT.ref.ty)).env := fun q hq => by
    rw [hWpos]; exact List.mem_append_left _ hq
  have hNmem : (.temp (st₁.env.size - 1) fr.temps.size) ∈ allPos (st₁.withTempT (.borrow l c) (some FT.ref.ty)).env := by rw [hWpos]; exact List.mem_append_right _ (List.mem_singleton_self _)
  have hWcases : ∀ q, q ∈ allPos (st₁.withTempT (.borrow l c) (some FT.ref.ty)).env → q = (.temp (st₁.env.size - 1) fr.temps.size) ∨ q ∈ allPos st₁.env := by
    intro q hq; rw [hWpos, List.mem_append, List.mem_singleton] at hq; exact hq.symm
  obtain ⟨px, hpxW, hxW⟩ := hF₁.lender _ l c hNmem hWnew
  have hpx : px ∈ allPos st₁.env := (hWcases px hpxW).resolve_left (fun e => by rw [e, hWnew] at hxW; cases hxW)
  have hx : valAt st₁.env px = .loan l := by rw [← hWold _ hpx]; exact hxW
  obtain ⟨fx, jx, rfl⟩ : ∃ fx jx, px = .bind fx jx := by
    cases px with
    | bind fx jx => exact ⟨fx, jx, rfl⟩
    | temp f' i' =>
      rcases hF₁.temps f' i' hpxW with h' | h' | ⟨m', w', h'⟩ <;> rw [hxW] at h' <;> cases h'
  have hnoB : ∀ q ∈ allPos st₁.env, ∀ w', valAt st₁.env q ≠ .borrow l w' := fun q hq w' e =>
    hntq q hq (hF₁.bor1 q _ l w' c (hWmem _ hq) hNmem (by rw [hWold _ hq]; exact e) hWnew)
  -- the discard, on the checker's side
  obtain ⟨st₂, hq, hki, hkW, hmeW⟩ := hdrop l c (.bind fx jx) rfl hcN
    (fun q hq => by rw [← hWold q hq]; exact hF₁.vals q (hWmem q hq)) hx hpx
    (fun q hq e => hF₁.loan1 q _ l (hWmem _ hq) hpxW (by rw [hWold _ hq]; exact e) hxW) hnoB
  -- the end of `l` at the value in flight, after the quiet stretch
  have heW : FEnd (st₁.withTempT (.borrow l c) (some FT.ref.ty)).env (.bind fx jx) (.temp (st₁.env.size - 1) fr.temps.size) l c :=
    ⟨hF₁.vals, fun f' i' m' hq' e => (by
        rcases hF₁.temps f' i' hq' with h' | h' | ⟨_, _, h'⟩ <;> rw [e] at h' <;> cases h'),
     hpxW, hNmem, hxW, hWnew, hcN, fun q hq e => hF₁.loan1 q _ l hq hpxW e hxW,
     fun q hq w' e => hF₁.bor1 q _ l w' c hq hNmem e hWnew⟩
  have hlvW : ∀ q ∈ allPos (st₁.withTempT (.borrow l c) (some FT.ref.ty)).env, ∀ m', valAt (st₁.withTempT (.borrow l c) (some FT.ref.ty)).env q = .loan m' → liveLoan (st₁.withTempT (.borrow l c) (some FT.ref.ty)).env m' = true := fun q hq m' e => by
    obtain ⟨q', c', hq', hy⟩ := hF₁.held q m' hq e
    unfold liveLoan findBorrow
    exact List.find?_isSome.mpr ⟨q', hq', by rw [hy]; simp [Value.holdsBorrow]⟩
  have hqW := hq.withTempT (.borrow l c) (some FT.ref.ty)
  have heW₂ : FEnd (st₂.withTempT (.borrow l c) (some FT.ref.ty)).env (.bind fx jx) (.temp (st₁.env.size - 1) fr.temps.size) l c := heW.of_erase hqW.env
  have hvE : ∀ q, valAt (st₂.withTempT (.borrow l c) (some FT.ref.ty)).env q = valAt (st₁.withTempT (.borrow l c) (some FT.ref.ty)).env q := fun q => by rw [← valAt_erase, ← hqW.env, valAt_erase]
  have haE : allPos (st₂.withTempT (.borrow l c) (some FT.ref.ty)).env = allPos (st₁.withTempT (.borrow l c) (some FT.ref.ty)).env := by rw [← allPos_erase, ← hqW.env, allPos_erase]
  have hlE : ∀ m', liveLoan (st₂.withTempT (.borrow l c) (some FT.ref.ty)).env m' = liveLoan (st₁.withTempT (.borrow l c) (some FT.ref.ty)).env m' := fun m' => by
    unfold liveLoan findBorrow; rw [haE]; simp only [hvE]
  have hlv₂ : ∀ q ∈ allPos (st₂.withTempT (.borrow l c) (some FT.ref.ty)).env, ∀ m', valAt (st₂.withTempT (.borrow l c) (some FT.ref.ty)).env q = .loan m' → liveLoan (st₂.withTempT (.borrow l c) (some FT.ref.ty)).env m' = true :=
    fun q hq' m' e => by rw [hlE]; exact hlvW q (haE ▸ hq') m' (by rw [← hvE]; exact e)
  have hr₂ : Rel { K with Δ := Δ₁ } ρ₁ φ π₁ (st₂.withTempT (.borrow l c) (some FT.ref.ty)) s₁ := hr₁.of_quiet hqW hp₁.labels
  obtain ⟨r, hhold, hrE⟩ := rel_end hr₂ hS₁ heW₂ hlv₂
  have hend := end_ok hr₂ hS₁ heW₂
  have hrul : ru.2.label = some (π₁ l) := by rw [hlu]; rfl
  have hS₂ : Strict.SGood K.dm K.Γ φ (s₁.endAt (π₁ l) r) := Strict.endAt_sgood hS₁ hhold hend
  -- the state after the end: `x := c` with `⊥` in flight
  obtain ⟨fr₂, hfr₂, htm⟩ := top_of_erase_temps hq.env hfr
  have hsz₂ : st₂.env.size = st₁.env.size := by rw [← Env.erase_size st₂.env, ← hq.env, Env.erase_size]
  have hph : ((.temp (st₁.env.size - 1) fr.temps.size) : Pos) = .temp (st₂.env.size - 1) fr₂.temps.size := by rw [hsz₂, htm]
  have hstEq : ({ (st₂.withTempT (.borrow l c) (some FT.ref.ty)) with env := endE (st₂.withTempT (.borrow l c) (some FT.ref.ty)).env (.bind fx jx) (.temp (st₁.env.size - 1) fr.temps.size) c } : MState) = ({ st₂ with env := Env.setAtE st₂.env (.bind fx jx) c } : MState).withTempT .bot (some FT.ref.ty) := by
    rw [hph]
    show ({ st₂ with env := endE (st₂.withTempT (.borrow l c) (some FT.ref.ty)).env (.bind fx jx) (.temp (st₂.env.size - 1) fr₂.temps.size) c } : MState) = _
    rw [endE_withTempT hfr₂]
    rfl
  have hrX : Rel { K with Δ := Δ₁ } ρ₁ φ π₁ ({ st₂ with env := Env.setAtE st₂.env (.bind fx jx) c } : MState) (s₁.endAt (π₁ l) r) := by
    rw [hstEq] at hrE
    exact rel_of_withTemp_inert Value.inert_bot (Rel.of_kern (kern_withTemp _ .bot _).symm hrE)
  have hrW : Rel { K with Δ := Δ₁ } ρ₁ φ π₁ stW (s₁.endAt (π₁ l) r) := hrX.of_kern hkW
  -- the checker's invariant, assignment and fragment state after the discard
  have hdo : ∀ f j, Pos.bind fx jx = .bind f j → ∀ b, (st₂.withTempT (.borrow l c) (some FT.ref.ty)).env[f]?.bind (fun fr : Frame => fr.binds[j]?) = some b →
      b.decl = .other := by
    intro f j e b hb
    cases e
    have hb' : (st₁.withTempT (.borrow l c) (some FT.ref.ty)).env[fx]?.bind (fun fr : Frame => fr.binds[jx]?) = some b := by
      rw [← lookup_erase, hqW.env, lookup_erase]; exact hb
    exact (hF₁.lent fx jx b l hb' (by rw [← (lookup_pos hb').2]; exact hxW)).2
  have hinvE := hIE K.D K.Γ (st₂.withTempT (.borrow l c) (some FT.ref.ty)) (.bind fx jx) _ l c hPL heW₂ hdo (hki K.D K.Γ hp₁.inv)
  rw [hstEq] at hinvE
  have hasgE := asg_endE (K := { K with Δ := Δ₁ }) (ρ := ρ₁) (st := (st₂.withTempT (.borrow l c) (some FT.ref.ty))) (px := .bind fx jx) (ph := (.temp (st₁.env.size - 1) fr.temps.size)) hcN
    (Asg.of_quiet hqW hp₁.asg hp₁.inv.wf6)
  rw [hstEq] at hasgE
  have hpW : Pre { K with Δ := Δ₁ } ρ₁ stW :=
    ⟨hp₁.ctx.of_eq (by show stW.inds = st₁.inds; rw [← hkW.inds, ← hq.inds])
        (by show stW.globals = st₁.globals; rw [← hkW.globals, ← hq.globals]),
     by rw [← hkW.norm]; exact hIPB K.D K.Γ _ _ hinvE,
     by rw [← hkW.norm]; exact asg_of_withTempT hasgE⟩
  have hPX : FSt Γ ({ st₁ with env := Env.setAtE st₁.env (.bind fx jx) c } : MState) := hF₁.endTemp hcN hpx hx
  have hPW : FSt Γ stW := (hPX.of_erase (by
      show (Env.setAtE st₁.env (.bind fx jx) c).erase = (Env.setAtE st₂.env (.bind fx jx) c).erase
      rw [Machine.erase_setAtE, Machine.erase_setAtE, hq.env])).kern hkW
  have hmW : Mode stW := (hm₀.of_modeEq hme₁).of_modeEq hmeW
  -- the step for `w`
  have htdW' : stW.tailDecl = none ∨ stW.tailDecl = some (K.D.declOf (DecideScope.topReadings stW) w) := by
    rcases htdW with e | e
    · exact .inl e
    · exact .inr (by rw [e, hcd, (hdec Γ _ B st (.seq Γ u w .ref B hu hw) hPst).2, (hdec Γ w B stW hw hPW).2])
  have hOw := ihw Δ₁ ρ₁ stW st' true none v T? (s₁.endAt (π₁ l) r) π₁ hPW rfl hmW htdW' hpW hrW hS₂ (hw.valsOk _)
    (fun σ hσ => hw.absBelow _ σ hσ) hw.noHole (by rw [scopeOf_rel hrW]; exact (hdec Γ w B stW hw hPW).1)
    (fun e => by cases e) hD bh₂ hrw
  rw [htnW] at hOw
  obtain ⟨ρ₂, Δ₂, π₂, rw', s₃, he₂, hxw, hmw, haw, hlw, hp₂, hr₃⟩ := hOw
  have hxw' : runT K ρ φ st.curTail (.plain TyM.err) w (s₁.endAt (π₁ l) r) = some (rw', s₃) := by
    rw [← wcong (fun m' => hw.absBelow m') Δ₁ ρ₁]; exact hxw
  have hxs : runT K ρ φ st.curTail (hintM K ρ hint) (.seq u w) s = some (rw', s₃) := by
    rw [runT_seq _ _ u w s hfl]
    simp only [bind, Option.bind]
    rw [hxu']
    simp only
    rw [SM.guardMod_of (by unfold DiscardOk; rw [hrul]; exact hend)]
    simp only
    have hd : discardEnd ru.2 s₁ = s₁.endAt (π₁ l) r := by
      unfold discardEnd; rw [hrul]; exact SState.endLabel_eq hhold
    rw [hd, frag_hint (K := K) (ρ := ρ) (φ := φ) hw _ _ (.plain TyM.err)]; exact hxw'
  have hext : Ext K ρ π st stW ρ₁ Δ₁ π₁ :=
    (he₁.congr hk₀.absTy hk₀.nextLoan rfl rfl).grow (by rw [← hkW.absTy]; exact hq.absSize)
      (by rw [← hkW.nextLoan]; exact hq.nextLoan)
  exact ⟨ρ₂, Δ₂, π₂, rw', s₃, hext.trans he₂, hxs, hmw, haw, hlw, hp₂, hr₃⟩

end

end Ochr.Meaning.Steps.Form

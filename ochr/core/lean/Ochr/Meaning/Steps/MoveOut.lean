import Ochr.Meaning.Steps.FragPush
import Ochr.Meaning.Steps.BotWriteRel

/-!
# A borrow moved out of a binding into flight keeps the relation (lead20, 2026-11-22; docs/31 D145)

The read of a borrow variable whole moves the borrow out (the checker's `x ↦ ⊥`, the borrow in flight; the reference's
`readPlace`: the binding set to `moved`, the label taken from it and parked in a fresh temporary of the top frame). The
inverse of `FragPush.rel_pushBind_borrowG` (the value in flight moved into a pushed binding). It is general: any binding
holding `borrow_l w` with an inert content `w` (no label, no site), other borrows live; the reference's holder type of
`l` after the move is its recorded type (`heldTy`), which a good state's equals its binding holder's stored type
(`ColumnWrite.heldTy_eq_holderTy`, the hypothesis `hheld`).
-/

namespace Ochr.Meaning.Steps.Form

open Ochr Ochr.Meaning Ochr.Meaning.Steps
open Classical
open SStateB

/-- A write at one position that keeps whether it holds the borrow `L` keeps `L`'s liveness. -/
theorem liveLoan_setAtE_at {env : Env} {pos : Pos} {v' : Value} (hp : pos ∈ allPos env) {L : Nat}
    (h : v'.holdsBorrow L = (valAt env pos).holdsBorrow L) :
    liveLoan (Env.setAtE env pos v') L = liveLoan env L := by
  unfold liveLoan findBorrow
  rw [allPos_setAtE, find?_congr' (Q := fun p => (valAt env p).holdsBorrow L)]
  intro x _
  by_cases hx : x = pos
  · subst hx; rw [valAt_setAtE_self v' hp, h]
  · rw [valAt_setAtE_other env pos x v' hx]

theorem lent_pushTempShaped' (s : SState) (v : SVal) (l : Nat) : (s.pushTempShaped v l).lent = s.lent := by
  unfold SState.pushTempShaped; dsimp only; split <;> rfl

theorem size_setAtE (env : Env) (p : Pos) (v : Value) : (Env.setAtE env p v).size = env.size := by
  cases p <;> simp [Env.setAtE]

/-! ## The reference's side: the binding moved out and its label taken -/

section
variable {s : SState} {q : Pos} {L : Nat}

theorem holderOf_moveOut (huniq : s.Uniq) (hsh : s.shape q = some L) (hq : q ∈ s.positions) :
    (s.setAt q fun _ => .moved).holderOf L = some q := by
  have hl : (s.setAt q fun _ => .moved).Live L :=
    (SState.live_iff _ _).mpr ⟨q, by rw [SState.positions_setAt]; exact hq, by rw [SState.shape_setAt]; exact hsh⟩
  obtain ⟨r, hr₀⟩ := SState.holderOf_of_live hl
  have := (SState.holderOf_spec hr₀).2
  rw [SState.shape_setAt] at this
  rw [hr₀, huniq r q L this hsh]

variable (huniq : s.Uniq) (hsh : s.shape q = some L) (hq : q ∈ s.positions)
include huniq hsh hq

theorem moveOut_shape (p : Pos) :
    ((s.setAt q fun _ => .moved).takeLabel L).shape p = if p = q then none else s.shape p := by
  unfold SState.takeLabel; rw [holderOf_moveOut huniq hsh hq]; simp only [SState.shape_setAt]

theorem moveOut_valAt (p : Pos) :
    ((s.setAt q fun _ => .moved).takeLabel L).valAt p = if p = q then (fun _ => .moved) else s.valAt p := by
  unfold SState.takeLabel; rw [holderOf_moveOut huniq hsh hq]
  show ((s.setAt q fun _ => .moved).setAt q fun _ => .moved).valAt p = _
  split
  · next he => subst he; exact valAt_setAt_self _ _ _ (by rw [SState.positions_setAt]; exact hq)
  · next he =>
    rw [SState.valAt_setAt_ne _ _ _ _ (Ne.symm he), SState.valAt_setAt_ne _ _ _ _ (Ne.symm he)]

theorem moveOut_positions : ((s.setAt q fun _ => .moved).takeLabel L).positions = s.positions := by
  unfold SState.takeLabel; rw [holderOf_moveOut huniq hsh hq]
  show ((s.setAt q fun _ => .moved).setAt q fun _ => .moved).positions = _
  rw [SState.positions_setAt, SState.positions_setAt]

theorem moveOut_tyAt (p : Pos) : ((s.setAt q fun _ => .moved).takeLabel L).tyAt p = s.tyAt p := by
  unfold SState.takeLabel; rw [holderOf_moveOut huniq hsh hq]
  show ((s.setAt q fun _ => .moved).setAt q fun _ => .moved).tyAt p = _
  rw [tyAt_setAt, tyAt_setAt]

theorem moveOut_fields : ((s.setAt q fun _ => .moved).takeLabel L).lent = s.lent ∧
    ((s.setAt q fun _ => .moved).takeLabel L).heldTy = s.heldTy ∧
    ((s.setAt q fun _ => .moved).takeLabel L).heldMem = s.heldMem ∧
    ((s.setAt q fun _ => .moved).takeLabel L).nextLoan = s.nextLoan ∧
    ((s.setAt q fun _ => .moved).takeLabel L).topIdx = s.topIdx := by
  unfold SState.takeLabel; rw [holderOf_moveOut huniq hsh hq]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · show ((s.setAt q fun _ => .moved).setAt q fun _ => .moved).lent = _
    rw [SState.lent_setAt, SState.lent_setAt]
  · show ((s.setAt q fun _ => .moved).setAt q fun _ => .moved).heldTy = _
    cases q <;> rfl
  · show ((s.setAt q fun _ => .moved).setAt q fun _ => .moved).heldMem = _
    cases q <;> rfl
  · show ((s.setAt q fun _ => .moved).setAt q fun _ => .moved).nextLoan = _
    rw [SState.nextLoan_setAt', SState.nextLoan_setAt']
  · show ((s.setAt q fun _ => .moved).setAt q fun _ => .moved).topIdx = _
    rw [SStateB.topIdx_setAt, SStateB.topIdx_setAt]

theorem moveOut_skel : ((s.setAt q fun _ => .moved).takeLabel L).env.map (fun fr => fr.binds.map bindSkel) =
    s.env.map (fun fr => fr.binds.map bindSkel) := by
  unfold SState.takeLabel; rw [holderOf_moveOut huniq hsh hq]
  show ((s.setAt q fun _ => .moved).setAt q fun _ => .moved).env.map _ = _
  rw [skel_setAt, skel_setAt]

end

theorem moveOut_getLast {s : SState} {f i L : Nat} (huniq : s.Uniq) (hsh : s.shape (.bind f i) = some L)
    (hq : Pos.bind f i ∈ s.positions) {fr : SFrame} (hfr : s.env.getLast? = some fr) :
    ∃ fr', ((s.setAt (.bind f i) fun _ => .moved).takeLabel L).env.getLast? = some fr' ∧ fr'.temps = fr.temps := by
  unfold SState.takeLabel; rw [holderOf_moveOut huniq hsh hq]
  obtain ⟨fr₁, h₁, e₁⟩ := SStateB.getLast_setAt_bind s f i (fun _ => .moved) hfr
  obtain ⟨fr₂, h₂, e₂⟩ := SStateB.getLast_setAt_bind _ f i (fun _ => .moved) h₁
  exact ⟨fr₂, h₂, e₂.trans e₁⟩

section
variable {K : RunCtx} {ρ : Assignment} {φ : Future}

/-- **The borrow a binding holds, moved out into flight, keeps the relation** (the read of a borrow variable whole): the
checker's binding set to `⊥` and the borrow `borrow_l w` in flight; the reference's binding moved, the label `π l` taken
from it and parked in a fresh temporary of the top frame holding `w`'s meaning. Other borrows stay live where they
were. -/
theorem rel_moveOut {π : Nat → Nat} {st : MState} {s : SState} {l : Nat} {w : Value} {f i : Nat}
    (hr : Rel K ρ φ π st s) (huniq : s.Uniq) (hne : 0 < st.env.size)
    (hp : Pos.bind f i ∈ allPos st.env) (hv : valAt st.env (.bind f i) = .borrow l w) (hw : w.InertA)
    (hheld : s.heldTy (π l) = (s.tyAt (.bind f i)).m)
    (c : Sem) (hc : ∀ (φ' : Future) (hint : TyS), Value.mean K.dm K.M K.Γ ρ φ' hint w = c) :
    Rel K ρ φ π ({ st with env := Env.setAtE st.env (.bind f i) .bot }.withTemp (.borrow l w))
      (((s.setAt (.bind f i) fun _ => .moved).takeLabel (π l)).pushTempShaped (fun _ => c) (π l)) := by
  -- the checker's side
  have hshC : Env.shape st.env (.bind f i) = some l := by rw [shape_eq_shapeOf, hv]; rfl
  have hsz : (Env.setAtE st.env (.bind f i) .bot).size = st.env.size := size_setAtE _ _ _
  have hne₁ : 0 < (Env.setAtE st.env (.bind f i) .bot).size := by rw [hsz]; exact hne
  obtain ⟨fr, hfr⟩ : ∃ fr, (Env.setAtE st.env (.bind f i) .bot)[(Env.setAtE st.env (.bind f i) .bot).size - 1]? = some fr :=
    ⟨_, Array.getElem?_eq_getElem (by omega)⟩
  generalize hE₁ : Env.setAtE st.env (.bind f i) .bot = E₁ at hsz hne₁ hfr
  have hEc : ({ st with env := E₁ }.withTemp (.borrow l w)).env = Env.pushTempE E₁ (.borrow l w) := rfl
  have hpos₂ : allPos (Env.pushTempE E₁ (.borrow l w)) = allPos st.env ++ [.temp (E₁.size - 1) fr.temps.size] := by
    rw [allPos_pushTempE _ _ fr hfr hne₁, ← hE₁, allPos_setAtE]
  have hntS : Pos.temp (E₁.size - 1) fr.temps.size ∉ allPos st.env := fun h => by
    obtain ⟨fr', hf', hi⟩ := mem_allPos_temp _ _ _ h
    rw [← allPos_setAtE st.env (.bind f i) .bot, hE₁] at h
    obtain ⟨fr'', hf'', hi'⟩ := mem_allPos_temp _ _ _ h
    rw [hfr] at hf''; cases hf''; exact absurd hi' (Nat.lt_irrefl _)
  have hval₂ : ∀ p, valAt (Env.pushTempE E₁ (.borrow l w)) p =
      if p = .temp (E₁.size - 1) fr.temps.size then .borrow l w else if p = .bind f i then .bot else valAt st.env p := by
    intro p
    split
    · next he => subst he; exact valAt_pushTempE_new _ _ fr hfr
    · next he =>
      have h1 : valAt (Env.pushTempE E₁ (.borrow l w)) p = valAt E₁ p := by
        cases p with
        | bind f' i' => exact valAt_pushTempE_bind _ _ _ _
        | temp f' i' => exact valAt_pushTempE_old _ _ fr hfr _ _ he
      rw [h1, ← hE₁]
      split
      · next hq => subst hq; exact valAt_setAtE_self _ hp
      · next hq => exact valAt_setAtE_other _ _ _ _ hq
  have hshape₂ : ∀ p, Env.shape (Env.pushTempE E₁ (.borrow l w)) p =
      if p = .temp (E₁.size - 1) fr.temps.size then some l else if p = .bind f i then none else Env.shape st.env p := by
    intro p; rw [shape_eq_shapeOf, hval₂]
    split
    · rfl
    · split
      · rfl
      · rw [← shape_eq_shapeOf]
  have hmean₂ : ∀ (χ : Future) p, Env.mean K.dm K.M K.Γ ρ χ (Env.pushTempE E₁ (.borrow l w)) p =
      if p = .temp (E₁.size - 1) fr.temps.size then c else if p = .bind f i then .moved
      else Env.mean K.dm K.M K.Γ ρ χ st.env p := by
    intro χ p
    split
    · next he => subst he; rw [mean_pushTempE_new _ _ _ _ _ _ fr hfr]; exact hc _ _
    · next he =>
      rw [mean_pushTempE_other _ _ _ _ _ _ fr hfr _ _ he, ← hE₁]
      split
      · next hq =>
        subst hq
        obtain ⟨frb, b, hf, hb⟩ := mem_allPos_bind _ _ _ hp
        rw [mean_setAtE_bind _ _ _ _ _ _ _ _ _ frb b hf hb]; rfl
      · next hq => exact mean_setAtE_other _ _ _ _ _ _ _ _ _ hq
  have hliveC : ∀ L, liveLoan (Env.pushTempE E₁ (.borrow l w)) L = liveLoan st.env L := by
    intro L
    by_cases e : L = l
    · subst e
      rw [FEnd.liveLoan_of_shape hshC]
      unfold liveLoan findBorrow
      refine List.find?_isSome.mpr ⟨.temp (E₁.size - 1) fr.temps.size, by rw [hpos₂]; simp, ?_⟩
      rw [valAt_pushTempE_new _ _ fr hfr]; simp [Value.holdsBorrow]
    · have hb : (Value.borrow l w).holdsBorrow L = false := by
        simp only [Value.holdsBorrow, hw.holdsBorrow, Bool.or_false, beq_eq_false_iff_ne]; exact fun h => e h.symm
      unfold liveLoan; rw [findBorrow_pushTempE _ _ fr hfr hne₁ L hb]
      show liveLoan E₁ L = liveLoan st.env L
      rw [← hE₁]; exact liveLoan_setAtE_at hp (by rw [hv, hb]; rfl)
  have hsitesC : ∀ L, Env.sitesOf (Env.pushTempE E₁ (.borrow l w)) L = Env.sitesOf st.env L := by
    intro L
    rw [sitesOf_pushTempE' _ (.borrow l w) fr hfr hne₁ L (fun pos path => hw.sitesOf L pos _), ← hE₁]
    exact sitesOf_setAtE_noSites hp (fun L' pos path => by rw [hv]; exact hw.sitesOf L' pos _) (fun _ _ _ => rfl) L
  have hoccC : ∀ L, ({ st with env := E₁ }.withTemp (.borrow l w)).Occurs L → st.Occurs L := by
    rintro L ⟨v', hv', ha⟩
    rw [hEc, values_pushTempE _ _ fr hfr hne₁] at hv'
    rcases List.mem_append.mp hv' with hv'' | hv''
    · rw [← hE₁] at hv''
      rcases mem_values_setAtE hv'' with rfl | hv'''
      · exact absurd ha Bool.false_ne_true
      · exact ⟨v', hv''', ha⟩
    · rw [List.mem_singleton] at hv''; subst hv''
      exact ⟨_, List.mem_map.mpr ⟨_, hp, hv⟩, ha⟩
  -- the reference's side
  have hshq : s.shape (.bind f i) = some (π l) := hr.sim.2.1 _ l (by simp [IsTemp]) hshC
  have hqS : Pos.bind f i ∈ s.positions := hr.holders _ _ hshq
  obtain ⟨frs, hfrs, htop, -⟩ := skel_align K ρ st s hr.skel _
    (Array.getElem?_eq_getElem (by omega : st.env.size - 1 < st.env.size))
  have hlast : s.env.getLast? = some frs := by
    rw [List.getLast?_eq_getElem?]; simpa [SState.topIdx] using hfrs
  obtain ⟨frt, hfrt, -⟩ := moveOut_getLast huniq hshq hqS hlast
  obtain ⟨hlent, hheldT, hmemT, hnlT, htopT⟩ := moveOut_fields huniq hshq hqS
  generalize ht : (s.setAt (.bind f i) fun _ => .moved).takeLabel (π l) = t at hfrt hlent hheldT hmemT hnlT htopT
  have hshT := moveOut_shape huniq hshq hqS
  have hvalT := moveOut_valAt huniq hshq hqS
  have hposT := moveOut_positions huniq hshq hqS
  have htyT := moveOut_tyAt huniq hshq hqS
  have hskT := moveOut_skel huniq hshq hqS
  rw [ht] at hshT hvalT hposT htyT hskT
  have hnTS : newTemp t frt ∉ s.positions := by rw [← hposT]; exact newTemp_not_mem t hfrt
  have hsh₂ : ∀ p, (t.pushTempShaped (fun _ => c) (π l)).shape p =
      if p = newTemp t frt then some (π l) else if p = .bind f i then none else s.shape p := by
    intro p; rw [shape_pushTempShaped t _ _ hfrt, hshT]
  have hval₂S : ∀ p, (t.pushTempShaped (fun _ => c) (π l)).valAt p =
      if p = newTemp t frt then (fun _ => c) else if p = .bind f i then (fun _ => .moved) else s.valAt p := by
    intro p; rw [valAt_pushTempShaped' t _ _ hfrt, hvalT]
  have hpos₂S : ∀ p, p ∈ (t.pushTempShaped (fun _ => c) (π l)).positions ↔ p = newTemp t frt ∨ p ∈ s.positions := by
    intro p; rw [mem_positions_pushTempShaped t _ _ hfrt, hposT]
  have hnTidx : newTemp t frt = .temp (st.env.size - 1) frt.temps.length := by
    simp only [newTemp, htopT, htop]
  rw [hnTidx] at hnTS hsh₂ hval₂S hpos₂S
  have hliveX : ∀ L, (t.pushTempShaped (fun _ => c) (π l)).Live L ↔ s.Live L := by
    intro L
    rw [SState.live_iff, SState.live_iff]
    constructor
    · rintro ⟨p, -, hsp⟩
      rw [hsh₂] at hsp
      split at hsp
      · cases hsp; exact ⟨_, hqS, hshq⟩
      · split at hsp
        · cases hsp
        · exact ⟨p, hr.holders p L hsp, hsp⟩
    · rintro ⟨p, hp', hsp⟩
      by_cases hL : L = π l
      · subst hL; exact ⟨_, (hpos₂S _).mpr (.inl rfl), by rw [hsh₂, if_pos rfl]⟩
      · have h1 : p ≠ .temp (st.env.size - 1) frt.temps.length := fun e => hnTS (e ▸ hp')
        have h2 : p ≠ .bind f i := fun e => by rw [e, hshq] at hsp; exact hL (Option.some.inj hsp).symm
        exact ⟨p, (hpos₂S p).mpr (.inr hp'), by rw [hsh₂, if_neg h1, if_neg h2]; exact hsp⟩
  have hhold₂ : ∀ L, s.Live L → holderTy (t.pushTempShaped (fun _ => c) (π l)) L = holderTy s L := by
    intro L hL
    obtain ⟨r, hr₀⟩ := SState.holderOf_of_live ((hliveX L).mpr hL)
    have hrs := (SState.holderOf_spec hr₀).2
    rw [hsh₂] at hrs
    by_cases e : L = π l
    · subst e
      have hry : r = .temp (st.env.size - 1) frt.temps.length := by
        split at hrs
        · assumption
        · split at hrs
          · cases hrs
          · next h1 h2 => exact absurd (huniq _ _ _ hrs hshq) h2
      have hhs : s.holderOf (π l) = some (.bind f i) := by
        obtain ⟨r', hr'⟩ := SState.holderOf_of_live hL
        rw [hr', huniq _ _ _ (SState.holderOf_spec hr').2 hshq]
      unfold holderTy; rw [hr₀, hry, hhs]
      show (t.pushTempShaped (fun _ => c) (π l)).heldTy (π l) = (s.tyAt (.bind f i)).m
      rw [Strict.heldTy_pushTempShaped, hheldT, hheld]
    · have hr1 : r ≠ .temp (st.env.size - 1) frt.temps.length := fun e' => by
        rw [if_pos e'] at hrs; exact e (Option.some.inj hrs).symm
      rw [if_neg hr1] at hrs
      have hr2 : r ≠ .bind f i := fun e' => by rw [if_pos e'] at hrs; cases hrs
      rw [if_neg hr2] at hrs
      obtain ⟨r', hr₀'⟩ := SState.holderOf_of_live hL
      obtain rfl := huniq r r' L hrs (SState.holderOf_spec hr₀').2
      unfold holderTy; rw [hr₀, hr₀']
      cases r with
      | bind f' i' =>
        show ((t.pushTempShaped (fun _ => c) (π l)).tyAt _).m = _; rw [Strict.tyAt_pushTempShaped, htyT]
      | temp f' i' => show (t.pushTempShaped (fun _ => c) (π l)).heldTy L = s.heldTy L
                      rw [Strict.heldTy_pushTempShaped, hheldT]
  have hF : ∀ ψ, (RelF φ (t.pushTempShaped (fun _ => c) (π l)) ψ ∧ TypedLive K (t.pushTempShaped (fun _ => c) (π l)) ψ) →
      RelF φ s ψ ∧ TypedLive K s ψ :=
    fun ψ hψ => ⟨fun L hL => hψ.1 L (fun h' => hL ((hliveX L).mp h')),
      fun L hL => by have := hψ.2 L ((hliveX L).mpr hL); rwa [hhold₂ L hL] at this⟩
  refine ⟨?_, ?_, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · -- skel
    have h1 := skel_pushTempE K ρ { st with env := E₁ } (.borrow l w)
    have h2 : (SM' K ρ { st with env := E₁ }).env.map (fun fr => fr.binds.map bindSkel) =
        (SM' K ρ st).env.map (fun fr => fr.binds.map bindSkel) := by
      rw [← hE₁]; exact skel_setAtE K ρ st f i .bot
    have h3 := skel_pushTempShaped t (fun _ => c) (π l)
    exact h1.trans (h2.trans (hr.skel.trans (h3.trans hskT).symm))
  · -- fresh
    intro L hL ho
    show π L < (t.pushTempShaped (fun _ => c) (π l)).nextLoan
    rw [SState.nextLoan_pushTempShaped, hnlT]
    exact hr.fresh L hL (hoccC L ho)
  · -- the bindings mean the same
    intro ψ hψ p hpT
    show Env.mean K.dm K.M K.Γ ρ _ (Env.pushTempE E₁ (.borrow l w)) p = (t.pushTempShaped (fun _ => c) (π l)).valAt p ψ
    rw [hmean₂, hval₂S]
    cases p with
    | temp => exact absurd trivial hpT
    | bind f' i' =>
      have e1 : (Pos.bind f' i' = Pos.temp (E₁.size - 1) fr.temps.size) = False := eq_false (fun e => by cases e)
      have e2 : (Pos.bind f' i' = Pos.temp (st.env.size - 1) frt.temps.length) = False := eq_false (fun e => by cases e)
      simp only [e1, e2, if_false]
      by_cases hq : Pos.bind f' i' = Pos.bind f i
      · simp only [hq, if_true]
      · simp only [hq, if_false]; exact hr.sim.1 ψ (hF ψ hψ) _ hpT
  · -- the checker's holders at bindings
    intro p L hpT hsh
    have hsh' : Env.shape (Env.pushTempE E₁ (.borrow l w)) p = some L := hsh
    rw [hshape₂] at hsh'
    rw [hsh₂]
    cases p with
    | temp => exact absurd trivial hpT
    | bind f' i' =>
      rw [if_neg (fun e => by cases e)] at hsh' ⊢
      split at hsh'
      · cases hsh'
      · next hq => rw [if_neg hq]; exact hr.sim.2.1 _ L hpT hsh'
  · -- the reference's holders at bindings
    intro p L' hpT hsh
    rw [hsh₂] at hsh
    cases p with
    | temp => exact absurd trivial hpT
    | bind f' i' =>
      rw [if_neg (fun e => by cases e)] at hsh
      split at hsh
      · cases hsh
      · next hq =>
        obtain ⟨L, h1, h2⟩ := hr.sim.2.2.1 _ L' hpT hsh
        refine ⟨L, ?_, h2⟩
        show Env.shape (Env.pushTempE E₁ (.borrow l w)) _ = some L
        rw [hshape₂, if_neg (fun e => by cases e), if_neg hq]; exact h1
  · -- the checker's temporaries holding a borrow
    intro f' i' L hsh
    have hsh' : Env.shape (Env.pushTempE E₁ (.borrow l w)) (.temp f' i') = some L := hsh
    rw [hshape₂] at hsh'
    split at hsh'
    · next he =>
      cases hsh'
      obtain ⟨rfl, rfl⟩ := Pos.temp.inj he
      refine ⟨frt.temps.length, by rw [hsh₂, hsz, if_pos rfl], fun ψ _ => ?_⟩
      refine (hmean₂ (fun L => ψ (π L)) (.temp (E₁.size - 1) fr.temps.size)).trans ?_
      rw [if_pos rfl, hval₂S, hsz, if_pos rfl]
    · next he =>
      split at hsh'
      · cases hsh'
      · next hq =>
        obtain ⟨j, hj, hjv⟩ := hr.sim.2.2.2.1 f' i' L hsh'
        have hj1 : Pos.temp f' j ≠ .temp (st.env.size - 1) frt.temps.length := fun e => hnTS (e ▸ hr.holders _ _ hj)
        refine ⟨j, by rw [hsh₂, if_neg hj1, if_neg (fun e => by cases e)]; exact hj, fun ψ hψ => ?_⟩
        show Env.mean K.dm K.M K.Γ ρ _ (Env.pushTempE E₁ (.borrow l w)) (.temp f' i') = _
        rw [hmean₂, if_neg he, if_neg hq, hval₂S, if_neg hj1, if_neg (fun e => by cases e)]
        exact hjv ψ (hF ψ hψ)
  · -- the reference's temporaries holding a borrow
    intro f' j L' hsh
    rw [hsh₂] at hsh
    split at hsh
    · next he =>
      cases hsh
      obtain ⟨rfl, rfl⟩ := Pos.temp.inj he
      refine ⟨fr.temps.size, l, ?_, rfl⟩
      show Env.shape (Env.pushTempE E₁ (.borrow l w)) _ = _
      rw [hshape₂, ← hsz, if_pos rfl]
    · split at hsh
      · cases hsh
      · obtain ⟨i', L, h1, h2⟩ := hr.sim.2.2.2.2 f' j L' hsh
        have hi1 : Pos.temp f' i' ≠ .temp (E₁.size - 1) fr.temps.size := fun e => hntS (e ▸ mem_allPos_of_shape h1)
        refine ⟨i', L, ?_, h2⟩
        show Env.shape (Env.pushTempE E₁ (.borrow l w)) _ = _
        rw [hshape₂, if_neg hi1, if_neg (fun e => by cases e)]; exact h1
  · -- the renaming is one to one
    intro L₁ L₂ h₁ h₂ e
    have h₁' : liveLoan (Env.pushTempE E₁ (.borrow l w)) L₁ = true := h₁
    have h₂' : liveLoan (Env.pushTempE E₁ (.borrow l w)) L₂ = true := h₂
    rw [hliveC] at h₁' h₂'
    exact hr.inj L₁ L₂ h₁' h₂' e
  · -- the sites
    intro L hL x
    have hL' : liveLoan (Env.pushTempE E₁ (.borrow l w)) L = true := hL
    rw [hliveC] at hL'
    show x ∈ (t.pushTempShaped (fun _ => c) (π l)).lent (π L) ↔ x ∈ Env.sitesOf (Env.pushTempE E₁ (.borrow l w)) L
    rw [lent_pushTempShaped', hlent, hr.sites L hL' x, hsitesC]
  · -- the holders are positions
    intro p L hsh
    rw [hsh₂] at hsh
    split at hsh
    · next he => exact (hpos₂S p).mpr (.inl he)
    · split at hsh
      · cases hsh
      · exact (hpos₂S p).mpr (.inr (hr.holders p L hsh))
  · -- the records
    intro L hL
    have hLs := (hliveX L).mp hL
    rw [hhold₂ L hLs]
    show ((t.pushTempShaped (fun _ => c) (π l)).heldMem L).whole ∧
      (t.pushTempShaped (fun _ => c) (π l)).heldMem L ∈ₛ[K.dm.read] holderTy s L
    rw [Strict.heldMem_pushTempShaped, hmemT]; exact hr.records L hLs

end

end Ochr.Meaning.Steps.Form

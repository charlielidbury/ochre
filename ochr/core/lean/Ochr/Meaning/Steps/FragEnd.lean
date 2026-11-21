import Ochr.Meaning.Steps.ColumnReadEnd

/-!
# The fragment: ending one label among several (lead10)

The fragment of the simulation's induction (`Steps/Frag.lean`): `Z`, `S(u)`, a read of a number
variable, `let`, `;`, `&x` of a number variable, `x := u` at a number variable, `*y := u` through a
borrow, at `Nat`, `Unit` and `&Nat`. Its positions hold a number, `()`, `⊥`, a loan, or a borrow of a
number (`FVal`). Several borrows may be live at once (each lent by its own number variable); a read,
a borrow or a write of a lent variable ends its borrow, as do a `let`'s drop of a borrow binding and
a sequence's discard of a borrow. This file is the relation across that end, on both sides, where
other labels stay live (`rel_end`): the hardest of the fragment's plumbing, used four times. The
columns had it only where nothing else was live (`ColumnReadEnd.rel_afterEnd`).
-/

namespace Ochr.Meaning.Steps.Form

open Ochr Ochr.Meaning Ochr.Meaning.Steps
open Classical

/-- **A value a position of the fragment holds**: a number, `()`, `⊥`, a loan, or a borrow of a number. -/
inductive FVal : Value → Prop
  | num {v : Value} : v.Num → FVal v
  | unit : FVal .unit
  | bot : FVal .bot
  | loan (m : Nat) : FVal (.loan m)
  | bor (m : Nat) {w : Value} : w.Num → FVal (.borrow m w)

namespace FVal

theorem num_ne_loan {v : Value} (h : v.Num) (l : Nat) : v ≠ .loan l := by cases h <;> intro e <;> cases e

/-- The sites of a fragment value: its loan, at its root. -/
theorem sitesOf {v : Value} (h : FVal v) (l : Nat) (pos : Pos) (path : List Step) :
    v.sitesOf l pos path = if v = .loan l then [⟨pos, path, false⟩] else [] := by
  cases h with
  | num hn => rw [hn.sitesOf, if_neg (num_ne_loan hn l)]
  | unit => simp [Value.sitesOf]
  | bot => simp [Value.sitesOf]
  | loan m => by_cases e : m = l <;> simp [Value.sitesOf, e]
  | bor m hw => simp only [Value.sitesOf, hw.sitesOf]; simp

theorem loan_beq {a b : Nat} : (Value.loan a == Value.loan b) = true ↔ a = b := by
  show (a == b) = true ↔ a = b
  exact beq_iff_eq

/-- A fragment value holds the loan `l` exactly when it is `loan_l`. -/
theorem hasLoanM {v : Value} (h : FVal v) (l : Nat) : v.hasLoanM l = true ↔ v = .loan l := by
  unfold Value.hasLoanM
  cases h with
  | num hn =>
    rw [hn.anyAtom (P := (· == Value.loan l)) rfl (fun _ => rfl)]
    constructor
    · intro e; cases e
    · intro e; exact absurd e (num_ne_loan hn l)
  | unit => constructor <;> intro e <;> cases e
  | bot => constructor <;> intro e <;> cases e
  | loan m =>
    show (Value.loan m == Value.loan l || false) = true ↔ _
    rw [Bool.or_false, loan_beq]
    constructor
    · intro e; rw [e]
    · intro e; cases e; rfl
  | bor m hw =>
    show (Value.borrow m _ == Value.loan l || _) = true ↔ _
    rw [show (Value.borrow m _ == Value.loan l) = false from rfl, Bool.false_or,
      hw.anyAtom (P := (· == Value.loan l)) rfl (fun _ => rfl)]
    constructor <;> intro e <;> cases e

/-- A fragment value holds the borrow `l` exactly when it is `borrow_l` of a number. -/
theorem holdsBorrow {v : Value} (h : FVal v) (l : Nat) : v.holdsBorrow l = true ↔ ∃ w, v = .borrow l w := by
  cases h with
  | num hn =>
    rw [hn.holdsBorrow]
    constructor
    · intro e; cases e
    · rintro ⟨w, e⟩; exact absurd e (hn.not_borrow l w)
  | unit => constructor; · intro e; cases e
            · rintro ⟨_, e⟩; cases e
  | bot => constructor; · intro e; cases e
           · rintro ⟨_, e⟩; cases e
  | loan m => constructor; · intro e; cases e
              · rintro ⟨_, e⟩; cases e
  | bor m hw =>
    show (m == l || _) = true ↔ _
    rw [hw.holdsBorrow, Bool.or_false, beq_iff_eq]
    constructor
    · intro e; exact ⟨_, by rw [e]⟩
    · rintro ⟨w', e⟩; cases e; rfl

theorem hasAbs {v : Value} (h : FVal v) (σ : Nat) : v.hasAbs σ = false := by
  cases h with
  | num hn => exact hn.hasAbs σ
  | bor m hw => simp only [Value.hasAbs, Value.anyAtom] at *; exact hw.hasAbs σ
  | _ => rfl

end FVal

/-! ## The checker's side of an end -/

/-- **An end of one borrow in a fragment environment**: `l` is lent at the binding `px` (`loan_l`)
and held at `ph` (`borrow_l c`, `c` a number); every position holds a fragment value; no temporary
holds a loan; `loan_l` and `borrow_l` lie at those positions only. -/
structure FEnd (E : Env) (px ph : Pos) (l : Nat) (c : Value) : Prop where
  vals : ∀ q ∈ allPos E, FVal (valAt E q)
  tempNoLoan : ∀ f i m, Pos.temp f i ∈ allPos E → valAt E (.temp f i) ≠ .loan m
  hpx : px ∈ allPos E
  hph : ph ∈ allPos E
  x : valAt E px = .loan l
  y : valAt E ph = .borrow l c
  c : c.Num
  loan1 : ∀ q ∈ allPos E, valAt E q = .loan l → q = px
  bor1 : ∀ q ∈ allPos E, ∀ w, valAt E q = .borrow l w → q = ph

/-- `FEnd` reads only the values, which a temporary's stored type does not change. -/
theorem FEnd.of_erase {E E' : Env} {px ph : Pos} {l : Nat} {c : Value} (he : E.erase = E'.erase)
    (h : FEnd E px ph l c) : FEnd E' px ph l c := by
  have hv : ∀ q, valAt E' q = valAt E q := fun q => by rw [← valAt_erase, ← he, valAt_erase]
  have ha : allPos E' = allPos E := by rw [← allPos_erase, ← he, allPos_erase]
  refine ⟨fun q hq => ?_, fun f i m hq => ?_, ha ▸ h.hpx, ha ▸ h.hph, by rw [hv]; exact h.x, by rw [hv]; exact h.y,
    h.c, fun q hq e => h.loan1 q (ha ▸ hq) (by rw [← hv]; exact e),
    fun q hq w e => h.bor1 q (ha ▸ hq) w (by rw [← hv]; exact e)⟩
  · rw [hv]; exact h.vals q (ha ▸ hq)
  · rw [hv]; exact h.tempNoLoan f i m (ha ▸ hq)

/-- The environment after the end: the holder `⊥`, the lender its content back. -/
def endE (E : Env) (px ph : Pos) (c : Value) : Env := Env.setAtE (Env.setAtE E ph .bot) px c

namespace FEnd
variable {E : Env} {px ph : Pos} {l : Nat} {c : Value} (h : FEnd E px ph l c)
include h

theorem ne : ph ≠ px := fun e => by have := h.y; rw [e, h.x] at this; cases this

omit h in
theorem allPos_endE : allPos (endE E px ph c) = allPos E := by
  rw [endE, allPos_setAtE, allPos_setAtE]

theorem valAt_endE (q : Pos) :
    valAt (endE E px ph c) q = if q = px then c else if q = ph then .bot else valAt E q := by
  unfold endE
  split
  · next e => subst e; exact valAt_setAtE_self _ (by rw [allPos_setAtE]; exact h.hpx)
  · next e =>
    rw [valAt_setAtE_other _ _ _ _ e]
    split
    · next e' => subst e'; exact valAt_setAtE_self _ h.hph
    · next e' => exact valAt_setAtE_other _ _ _ _ e'

theorem vals_endE : ∀ q ∈ allPos (endE E px ph c), FVal (valAt (endE E px ph c) q) := by
  intro q hq
  rw [allPos_endE] at hq
  rw [h.valAt_endE]
  split
  · exact .num h.c
  · split
    · exact .bot
    · exact h.vals q hq

theorem shape_endE (q : Pos) :
    Env.shape (endE E px ph c) q = if q = ph then none else Env.shape E q := by
  rw [shape_eq_shapeOf, shape_eq_shapeOf, h.valAt_endE]
  split
  · next e => subst e; rw [if_neg (Ne.symm h.ne), h.x]; cases h.c <;> rfl
  · split <;> rfl

/-- The sites of every other label are kept; `l` has none left. -/
theorem sitesOf_endE (m : Nat) :
    Env.sitesOf (endE E px ph c) m = if m = l then [] else Env.sitesOf E m := by
  unfold Env.sitesOf
  rw [allPos_endE]
  split
  · next e =>
    subst e
    refine List.flatMap_eq_nil_iff.mpr fun q hq => ?_
    rw [(h.vals_endE q (by rw [allPos_endE]; exact hq)).sitesOf, if_neg]
    rw [h.valAt_endE]
    intro e
    split at e
    · exact FVal.num_ne_loan h.c _ e
    · split at e
      · cases e
      · next e1 e2 => exact e1 (h.loan1 q hq e)
  · next e =>
    apply flatMap_congr_mem
    intro q hq
    rw [(h.vals_endE q (by rw [allPos_endE]; exact hq)).sitesOf, (h.vals q hq).sitesOf, h.valAt_endE]
    split
    · next e1 => subst e1; rw [h.x, if_neg (FVal.num_ne_loan h.c _), if_neg (fun e' => e (by cases e'; rfl))]
    · split
      · next e1 e2 => subst e2; rw [h.y, if_neg (fun e' => by cases e'), if_neg (fun e' => by cases e')]
      · rfl

end FEnd

/-- A fragment value other than a loan means the same at every future and type. -/
theorem FVal.mean_const {v : Value} (h : FVal v) (hl : ∀ m, v ≠ .loan m) :
    ∃ a : Sem, ∀ (dm : DataModel) (C : CodeMeaning) (Γ : List IndDecl) (ρ : Assignment) (φ : Future) (hint : TyS),
      Value.mean dm C Γ ρ φ hint v = a := by
  cases h with
  | num hn => obtain ⟨m, hm⟩ := hn.vmean; exact ⟨_, hm⟩
  | unit => exact ⟨_, fun _ _ _ _ _ _ => rfl⟩
  | bot => exact ⟨_, fun _ _ _ _ _ _ => rfl⟩
  | loan m => exact absurd rfl (hl m)
  | bor m hw =>
    obtain ⟨k, hk⟩ := hw.vmean
    exact ⟨.el0 Nat k, fun dm C Γ ρ φ hint => by rw [Value.mean]; exact hk _ _ _ _ _ _⟩

section
variable {K : RunCtx} {ρ : Assignment} {φ : Future}

theorem skel_setAtE_temp (st : MState) (f i : Nat) (v' : Value) :
    (SM' K ρ { st with env := Env.setAtE st.env (.temp f i) v' }).env.map (fun fr => fr.binds.map bindSkel) =
      (SM' K ρ st).env.map (fun fr => fr.binds.map bindSkel) := by
  apply List.ext_getElem?
  intro f'
  simp only [SM', MState.sstate, List.getElem?_map, List.getElem?_zipIdx, Option.map_map,
    Array.getElem?_toList, hintAt_setAtE]
  simp only [Env.setAtE, Array.getElem?_modify]
  by_cases hf : f = f'
  · subst hf
    rcases hfr : st.env[f]? with _ | fr
    · simp
    · simp only [if_true, Option.map_some, Function.comp_apply]
      simp [Function.comp_def, bindSkel, List.map_map]
  · simp only [hf, if_false]
    rcases st.env[f']? with _ | fr'
    · rfl
    · simp [Function.comp_def, bindSkel, List.map_map]

theorem skel_setAtE' (st : MState) (p : Pos) (v' : Value) :
    (SM' K ρ { st with env := Env.setAtE st.env p v' }).env.map (fun fr => fr.binds.map bindSkel) =
      (SM' K ρ st).env.map (fun fr => fr.binds.map bindSkel) := by
  cases p with
  | bind f i => exact skel_setAtE K ρ st f i v'
  | temp f i => exact skel_setAtE_temp st f i v'

end

namespace FEnd
variable {E : Env} {px ph : Pos} {l : Nat} {c : Value} (h : FEnd E px ph l c)
include h

/-- A label occurring after the end occurred before. -/
theorem occurs_endE {st : MState} (hE : st.env = E) {m : Nat}
    (ho : ({ st with env := endE E px ph c } : MState).Occurs m) : st.Occurs m := by
  obtain ⟨v, hv, ha⟩ := ho
  rcases Form.mem_values_setAtE hv with rfl | hv
  · exact absurd ha (by rw [h.c.anyAtom (by rfl) (fun _ => by rfl)]; exact Bool.false_ne_true)
  rcases Form.mem_values_setAtE hv with rfl | hv
  · exact absurd ha (fun e => by cases e)
  · exact ⟨v, by rw [hE]; exact hv, ha⟩

/-- A borrow live after the end was live before, and is not `l`. -/
theorem liveLoan_endE {m : Nat} (hm : liveLoan (endE E px ph c) m = true) : liveLoan E m = true ∧ m ≠ l := by
  unfold liveLoan findBorrow at hm ⊢
  obtain ⟨q, hq, hb⟩ := List.find?_isSome.mp hm
  rw [allPos_endE] at hq
  rw [h.valAt_endE] at hb
  split at hb
  · rw [h.c.holdsBorrow] at hb; cases hb
  · split at hb
    · cases hb
    · next e1 e2 =>
      refine ⟨List.find?_isSome.mpr ⟨q, hq, hb⟩, fun e => ?_⟩
      subst e
      obtain ⟨w, hw⟩ := ((h.vals q hq).holdsBorrow m).mp hb
      exact e2 (h.bor1 q hq w hw)

end FEnd

/-! ## The reference's side: the holder, the strict end -/

section
variable {K : RunCtx} {ρ : Assignment} {φ : Future}

/-- The checker's meaning at a position holding a fragment value that is not a loan reads no future. -/
theorem mean_const_at {E : Env} {q : Pos} (hq : q ∈ allPos E) (hv : FVal (valAt E q))
    (hl : ∀ m, valAt E q ≠ .loan m) : ∃ a, ∀ χ, Env.mean K.dm K.M K.Γ ρ χ E q = a := by
  obtain ⟨a, ha⟩ := hv.mean_const hl
  exact ⟨a, fun χ => by rw [mean_eq_valAt K.dm K.M K.Γ ρ χ E q hq]; exact ha _ _ _ _ _ _⟩

/-- **The reference's holder of an ending label**, and what it holds: the checker's holder `ph`
holds `borrow_l c`; the reference holds `π l` at one position `r` (the same binding, or a temporary
matched by label), which means `c`'s meaning `cM` at every future the relation compares at. -/
theorem end_holder {π : Nat → Nat} {st : MState} {s : SState} (hr : Rel K ρ φ π st s)
    (hS : Strict.SGood K.dm K.Γ φ s) {px ph : Pos} {l : Nat} {c : Value} (he : FEnd st.env px ph l c) :
    ∃ r cM, s.holderOf (π l) = some r ∧ s.shape r = some (π l) ∧
      (∀ f j, ph = .bind f j → r = ph) ∧ (∀ f j, r = .bind f j → ph = r) ∧
      (∀ f j, r = .temp f j → ∃ i, ph = .temp f i) ∧
      (∀ dm C Γ ρ' φ' hint, Value.mean dm C Γ ρ' φ' hint c = cM) ∧
      ∀ ψ, (RelF φ s ψ ∧ TypedLive K s ψ) → s.valAt r ψ = cM := by
  obtain ⟨m, hm⟩ := he.c.vmean
  have hsh : Env.shape st.env ph = some l := by rw [shape_eq_shapeOf, he.y]; rfl
  have hmeanY : ∀ χ, Env.mean K.dm K.M K.Γ ρ χ st.env ph = .el0 Nat m := fun χ => by
    rw [mean_eq_valAt K.dm K.M K.Γ ρ χ st.env ph he.hph, he.y, Value.mean]; exact hm _ _ _ _ _ _
  -- the reference's position holding `π l`, and its meaning
  obtain ⟨r, hrs, hrph, hrb, hrt, hvr⟩ : ∃ r, s.shape r = some (π l) ∧ (∀ f j, ph = .bind f j → r = ph) ∧
      (∀ f j, r = .bind f j → ph = r) ∧ (∀ f j, r = .temp f j → ∃ i, ph = .temp f i) ∧
      ∀ ψ, (RelF φ s ψ ∧ TypedLive K s ψ) → s.valAt r ψ = .el0 Nat m := by
    cases hph : ph with
    | bind f j =>
      rw [hph] at hsh hmeanY
      refine ⟨.bind f j, hr.sim.2.1 _ l (fun h => h) hsh, fun _ _ _ => rfl, fun _ _ _ => rfl,
        fun _ _ e => (by cases e), fun ψ hψ => ?_⟩
      rw [← hr.sim.1 ψ hψ (.bind f j) (fun h => h)]
      exact hmeanY _
    | temp f i =>
      rw [hph] at hsh hmeanY
      obtain ⟨j, hj, hjv⟩ := hr.sim.2.2.2.1 f i l hsh
      refine ⟨.temp f j, hj, fun _ _ e => (by cases e), fun _ _ e => (by cases e), fun f' j' e => ?_,
        fun ψ hψ => ?_⟩
      · cases e; exact ⟨i, rfl⟩
      · rw [← hjv ψ hψ]; exact hmeanY _
  have hrpos : r ∈ s.positions := hr.holders r _ hrs
  have hhold : s.holderOf (π l) = some r := by
    obtain ⟨r', hr'⟩ := SState.holderOf_of_live ((SState.live_iff s _).mpr ⟨r, hrpos, hrs⟩)
    rw [hr', hS.uniq r' r _ (SState.holderOf_spec hr').2 hrs]
  exact ⟨r, .el0 Nat m, hhold, hrs, hrph, hrb, hrt, hm, hvr⟩

/-- What the end keeps of the reference's tables. -/
theorem endAt_tyAt' (s : SState) (L : Nat) (r q : Pos) : (s.endAt L r).tyAt q = s.tyAt q := by
  unfold SState.endAt; rw [Strict.tyAt_mapVals]; rfl

theorem endAt_live_iff {s : SState} {L : Nat} {r : Pos} (hu : s.Uniq) (hrs : s.shape r = some L) (y : Nat) :
    (s.endAt L r).Live y ↔ s.Live y ∧ y ≠ L := by
  rw [SState.live_iff, SState.live_iff, SState.endAt_positions, SState.endAt_shape]
  constructor
  · rintro ⟨p, hp, hsh⟩
    simp only at hsh
    split at hsh
    · cases hsh
    · next hpr =>
      refine ⟨⟨p, hp, hsh⟩, fun e => hpr ?_⟩
      subst e; exact hu p r _ hsh hrs
  · rintro ⟨⟨p, hp, hsh⟩, hne⟩
    refine ⟨p, hp, ?_⟩
    simp only
    rw [if_neg (fun e => by subst e; rw [hrs] at hsh; cases hsh; exact hne rfl)]
    exact hsh

theorem endAt_holderTy {s : SState} {L : Nat} {r : Pos} (hrs : s.shape r = some L) {y : Nat} (hy : y ≠ L) :
    holderTy (s.endAt L r) y = holderTy s y := by
  have hh : (s.endAt L r).holderOf y = s.holderOf y := by
    unfold SState.holderOf
    rw [SState.endAt_positions, SState.endAt_shape]
    congr 1
    funext p
    simp only
    split
    · next e => subst e; rw [hrs]; simp [hy.symm]
    · rfl
  unfold holderTy
  rw [hh]
  split
  · rw [endAt_tyAt']
  · rfl
  · rfl

/-- **The strict end passes**, and the holder's meaning is a member of the label's content type. -/
theorem end_ok {π : Nat → Nat} {st : MState} {s : SState} (hr : Rel K ρ φ π st s)
    (hS : Strict.SGood K.dm K.Γ φ s) {px ph : Pos} {l : Nat} {c : Value} (he : FEnd st.env px ph l c) :
    EndOk K φ s (π l) := by
  obtain ⟨m, hm⟩ := he.c.vmean
  obtain ⟨r, cM, hhold, hrs, -, -, -, hcM, hvr⟩ := end_holder hr hS he
  have hcm : cM = .el0 Nat m := by rw [← hcM K.dm K.M K.Γ ρ φ (.plain TyM.err), hm]
  intro r' hr' ψ hψ
  rw [hhold] at hr'; cases hr'
  have h1 := hS.holder ψ hψ r (π l) hrs
  rw [hvr ψ (typedFut_rel hS hψ), hcm] at h1 ⊢
  exact Strict.mem_of_pmem_el (fun e => by cases e) (fun _ _ _ _ e => by cases e) h1

/-- The typed future of a related good state is one the step compares at, and a strict one. -/
theorem typedFuture_typed {π : Nat → Nat} {st : MState} {s : SState} (hr : Rel K ρ φ π st s)
    (hS : Strict.SGood K.dm K.Γ φ s) : TypedFut K φ s (s.typedFuture φ) := by
  refine ⟨fun y hy => by simp [SState.typedFuture, hy], fun y hy => ?_⟩
  simp only [SState.typedFuture, hy, if_true]
  rw [heldTy_eq_holderTy hS hy]
  exact (hr.records y hy).2

/-- **The futures across the end**: a future the relation compares at after the end, updated at the
ended label by the holder's meaning, is one it compares at before; and the holder means `cM` there. -/
theorem end_fut {π : Nat → Nat} {st : MState} {s : SState} (hr : Rel K ρ φ π st s)
    (hS : Strict.SGood K.dm K.Γ φ s) {px ph : Pos} {l : Nat} {c : Value} (he : FEnd st.env px ph l c)
    {r : Pos} {cM : Sem} (hhold : s.holderOf (π l) = some r) (hrs : s.shape r = some (π l))
    (hvr : ∀ ψ, (RelF φ s ψ ∧ TypedLive K s ψ) → s.valAt r ψ = cM) {ψ : Future}
    (hψ : RelF φ (s.endAt (π l) r) ψ ∧ TypedLive K (s.endAt (π l) r) ψ) :
    (RelF φ s (ψ.upd (π l) cM) ∧ TypedLive K s (ψ.upd (π l) cM)) ∧ s.valAt r ψ = cM := by
  have hlive := endAt_live_iff hS.uniq hrs
  have hL : s.Live (π l) := (SState.live_iff s _).mpr ⟨r, hr.holders r _ hrs, hrs⟩
  -- `cM` is a whole member of the label's content type
  have hT := typedFuture_typed hr hS
  have hcmem : cM ∈ₛ[K.dm.read] holderTy s (π l) := by
    rw [← hvr _ (typedFut_rel hS hT), ← heldTy_eq_holderTy hS hL]
    exact end_ok hr hS he r hhold _ hT
  have hcw : cM.whole := Strict.mem_whole (DataModel.read_wholeFields K.dm) hcmem
  -- a future typed before the end, at the label's record
  have hF : ∀ x : Sem, x.whole → x ∈ₛ[K.dm.read] holderTy s (π l) →
      RelF φ s (ψ.upd (π l) x) ∧ TypedLive K s (ψ.upd (π l) x) := by
    intro x hxw hxm
    refine ⟨fun y hy => ?_, fun y hy => ?_⟩
    · have hne : y ≠ π l := fun e => hy (e ▸ hL)
      rw [Future.upd_other _ _ hne]
      exact hψ.1 y (fun h => hy ((hlive y).mp h).1)
    · by_cases hne : y = π l
      · subst hne; rw [Future.upd_same]; exact ⟨hxw, hxm⟩
      · rw [Future.upd_other _ _ hne, ← endAt_holderTy hrs hne]
        exact hψ.2 y ((hlive y).mpr ⟨hy, hne⟩)
  have hrec := hr.records (π l) hL
  have hv0 : s.valAt r ψ = cM := by
    rw [← hS.holderIndep hrs ψ (s.heldMem (π l))]
    exact hvr _ (hF _ hrec.1 hrec.2)
  exact ⟨hF cM hcw hcmem, hv0⟩

/-! ## The relation across the end -/

namespace FEnd
variable {E : Env} {px ph : Pos} {l : Nat} {c : Value} (h : FEnd E px ph l c)
include h

theorem px_ne_temp (f i : Nat) : px ≠ .temp f i := fun e => h.tempNoLoan f i l (e ▸ h.hpx) (by rw [← e]; exact h.x)

theorem mem_sitesOf {m : Nat} {x : Site} (hx : x ∈ Env.sitesOf E m) :
    x.pos ∈ allPos E ∧ valAt E x.pos = .loan m := by
  unfold Env.sitesOf at hx
  obtain ⟨q, hq, hxq⟩ := List.mem_flatMap.mp hx
  rw [(h.vals q hq).sitesOf] at hxq
  split at hxq
  · next e => rw [List.mem_singleton] at hxq; subst hxq; exact ⟨hq, e⟩
  · cases hxq

/-- The checker's meaning after the end, away from the two positions that changed. -/
theorem mean_endE_other {K : RunCtx} {ρ : Assignment} (χ : Future) {q : Pos} (hq : q ∈ allPos E)
    (hx : q ≠ px) (hy : q ≠ ph) :
    Env.mean K.dm K.M K.Γ ρ χ (endE E px ph c) q = Env.mean K.dm K.M K.Γ ρ χ E q := by
  rw [mean_eq_valAt K.dm K.M K.Γ ρ χ _ q (by rw [allPos_endE]; exact hq), mean_eq_valAt K.dm K.M K.Γ ρ χ E q hq,
    h.valAt_endE, if_neg hx, if_neg hy, endE, hintAt_setAtE, hintAt_setAtE]

/-- The checker's meaning at a position other than the lender reads the future only at the live
loans it holds. -/
theorem mean_E_future {K : RunCtx} {ρ : Assignment} {χ χ' : Future} {q : Pos} (hq : q ∈ allPos E)
    (hagree : ∀ m, valAt E q = .loan m → χ m = χ' m) :
    Env.mean K.dm K.M K.Γ ρ χ E q = Env.mean K.dm K.M K.Γ ρ χ' E q := by
  rw [mean_eq_valAt K.dm K.M K.Γ ρ χ E q hq, mean_eq_valAt K.dm K.M K.Γ ρ χ' E q hq]
  by_cases hl : ∃ m, valAt E q = .loan m
  · obtain ⟨m, hm⟩ := hl
    rw [hm, Value.mean, Value.mean]; exact hagree m hm
  · obtain ⟨a, ha⟩ := (h.vals q hq).mean_const (fun m e => hl ⟨m, e⟩)
    rw [ha, ha]

omit h in
theorem liveLoan_of_shape {E : Env} {q : Pos} {m : Nat} (hs : Env.shape E q = some m) : liveLoan E m = true := by
  unfold liveLoan findBorrow
  refine List.find?_isSome.mpr ⟨q, mem_allPos_of_shape hs, ?_⟩
  rw [shape_eq_shapeOf] at hs
  generalize valAt E q = v at hs
  cases v <;> simp [shapeOf] at hs
  subst hs; simp [Value.holdsBorrow]

theorem liveL : liveLoan E l = true := liveLoan_of_shape (q := ph) (by rw [shape_eq_shapeOf, h.y]; rfl)

end FEnd

/-- The reference's meaning after the end, away from the holder: the old meaning at the future that
gives the ended label the holder's meaning. -/
theorem endAt_valAt_ne {s : SState} {L : Nat} {r p : Pos} (hpr : p ≠ r) (ψ : Future) :
    (s.endAt L r).valAt p ψ = s.valAt p (ψ.upd L (s.valAt r ψ)) := by
  by_cases hp : p ∈ s.positions
  · rw [SState.endAt_valAt s L r p hp]; simp only [if_neg hpr]
  · rw [SState.endAt_valAt_not_mem s L r p hp, SState.valAt_of_not_mem s p hp]

/-- **The relation across the end of one borrow among several** (the fragment's [End]): the
checker's holder `⊥` and its lender given the content back (`endE`), the reference's label ended at
its holder (`endAt`); every other label stays live, with its holder, sites and record. -/
theorem rel_end {π : Nat → Nat} {st : MState} {s : SState} (hr : Rel K ρ φ π st s)
    (hS : Strict.SGood K.dm K.Γ φ s) {px ph : Pos} {l : Nat} {c : Value} (he : FEnd st.env px ph l c)
    (hlv : ∀ q ∈ allPos st.env, ∀ m, valAt st.env q = .loan m → liveLoan st.env m = true) :
    ∃ r, s.holderOf (π l) = some r ∧
      Rel K ρ φ π { st with env := endE st.env px ph c } (s.endAt (π l) r) := by
  obtain ⟨m, hm⟩ := he.c.vmean
  obtain ⟨r, cM, hhold, hrs, hrph, hrb, hrt, hcM, hvr⟩ := end_holder hr hS he
  have hcm : cM = .el0 Nat m := by rw [← hcM K.dm K.M K.Γ ρ φ (.plain TyM.err), hm]
  have hliveL := he.liveL
  have hshph : Env.shape st.env ph = some l := by rw [shape_eq_shapeOf, he.y]; rfl
  -- a label held where the checker holds `l` is `l`, held at `ph`
  have hisl : ∀ q l', q ∈ allPos st.env → Env.shape st.env q = some l' → π l' = π l → q = ph := by
    intro q l' hq hs e
    have := hr.inj l' l (FEnd.liveLoan_of_shape hs) hliveL e
    subst this
    rw [shape_eq_shapeOf] at hs
    generalize hv : valAt st.env q = v at hs
    cases v <;> simp [shapeOf] at hs
    subst hs; exact he.bor1 q hq _ hv
  -- the reference's other holders are not `r`
  have hnr : ∀ q l', s.shape q = some l' → l' ≠ π l → q ≠ r := fun q l' hq hne e => by
    subst e; rw [hrs] at hq; cases hq; exact hne rfl
  refine ⟨r, hhold, ?_, ?_, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · -- skel
    have h1 := skel_setAtE' (K := K) (ρ := ρ) ({ st with env := Env.setAtE st.env ph .bot } : MState) px c
    have h2 := skel_setAtE' (K := K) (ρ := ρ) st ph .bot
    exact h1.trans (h2.trans (hr.skel.trans (skel_endAt s _ r).symm))
  · -- fresh
    intro l' hl ho
    exact hr.fresh l' hl (he.occurs_endE rfl ho)
  · -- the meanings at bindings
    intro ψ hψ p hp
    obtain ⟨hF1, hv0⟩ := end_fut hr hS he hhold hrs hvr hψ
    cases p with
    | temp f i => exact absurd trivial hp
    | bind f j =>
      show Env.mean K.dm K.M K.Γ ρ _ (endE st.env px ph c) (.bind f j) = _
      by_cases hpr : Pos.bind f j = r
      · -- the holder, a binding: `⊥` on both sides
        have hph : ph = .bind f j := (hrb f j hpr.symm).trans hpr.symm
        have hmem : Pos.bind f j ∈ allPos st.env := hph ▸ he.hph
        rw [show (s.endAt (π l) r).valAt (.bind f j) ψ = .moved by
          rw [SState.endAt_valAt s _ r _ (by rw [hpr]; exact hr.holders r _ hrs)]; simp [hpr]]
        rw [mean_eq_valAt K.dm K.M K.Γ ρ _ _ _ (by rw [FEnd.allPos_endE]; exact hmem), he.valAt_endE,
          if_neg (fun e => he.ne (hph.trans e)), if_pos hph.symm, Value.mean]
      · rw [endAt_valAt_ne hpr, hv0, ← hr.sim.1 _ hF1 (.bind f j) (fun h => h)]
        show Env.mean K.dm K.M K.Γ ρ _ (endE st.env px ph c) (.bind f j) =
          Env.mean K.dm K.M K.Γ ρ _ st.env (.bind f j)
        by_cases hmem : Pos.bind f j ∈ allPos st.env
        · by_cases hpx : Pos.bind f j = px
          · -- the lender: its content back, which the ended label's future gives
            subst hpx
            rw [mean_eq_valAt K.dm K.M K.Γ ρ _ _ _ (by rw [FEnd.allPos_endE]; exact hmem), he.valAt_endE,
              if_pos rfl, mean_eq_valAt K.dm K.M K.Γ ρ _ st.env _ hmem, he.x, hcM, Value.mean, Future.upd_same]
          · have hpy : Pos.bind f j ≠ ph := fun e => hpr (e.trans (hrph f j e.symm).symm)
            rw [he.mean_endE_other _ hmem hpx hpy]
            refine he.mean_E_future hmem fun m' hm' => ?_
            show ψ (π m') = (ψ.upd (π l) cM) (π m')
            rw [Future.upd_other _ _ (fun e => hpx (he.loan1 _ hmem (by
              rw [hm', hr.inj m' l (hlv _ hmem m' hm') hliveL e])))]
        · rw [mean_bind_not_mem (by rw [FEnd.allPos_endE]; exact hmem), mean_bind_not_mem hmem]
  · -- the shapes at bindings, forward
    intro p l' hp hsh
    change Env.shape (endE st.env px ph c) p = some l' at hsh
    rw [he.shape_endE] at hsh
    split at hsh
    · cases hsh
    · next hpph =>
      have h1 := hr.sim.2.1 p l' hp hsh
      rw [SState.endAt_shape]; simp only
      rw [if_neg (fun e => hpph (hisl p l' (mem_allPos_of_shape hsh) hsh (by
        rw [e, hrs] at h1; exact (Option.some.inj h1).symm)))]
      exact h1
  · -- the shapes at bindings, back
    intro p l'' hp hsh
    rw [SState.endAt_shape] at hsh; simp only at hsh
    split at hsh
    · cases hsh
    · next hpr =>
      obtain ⟨l₀, h₀, he₀⟩ := hr.sim.2.2.1 p l'' hp hsh
      refine ⟨l₀, ?_, he₀⟩
      change Env.shape (endE st.env px ph c) p = some l₀
      rw [he.shape_endE]
      cases p with
      | temp => exact absurd trivial hp
      | bind f j =>
        rw [if_neg (fun e => hpr (e.trans (hrph f j e.symm).symm))]
        exact h₀
  · -- the temporaries, forward
    intro f i l' hsh
    change Env.shape (endE st.env px ph c) (.temp f i) = some l' at hsh
    rw [he.shape_endE] at hsh
    split at hsh
    · cases hsh
    · next hti =>
      obtain ⟨j, hj, hjv⟩ := hr.sim.2.2.2.1 f i l' hsh
      have hjr : Pos.temp f j ≠ r := fun e => hti (hisl _ l' (mem_allPos_of_shape hsh) hsh (by
        rw [e, hrs] at hj; exact (Option.some.inj hj).symm))
      refine ⟨j, ?_, fun ψ hψ => ?_⟩
      · rw [SState.endAt_shape]; simp only; rw [if_neg hjr]; exact hj
      · obtain ⟨hF1, hv0⟩ := end_fut hr hS he hhold hrs hvr hψ
        rw [endAt_valAt_ne hjr, hv0, ← hjv _ hF1]
        show Env.mean K.dm K.M K.Γ ρ _ (endE st.env px ph c) (.temp f i) =
          Env.mean K.dm K.M K.Γ ρ _ st.env (.temp f i)
        have hmem := mem_allPos_of_shape hsh
        rw [he.mean_endE_other _ hmem (fun e => he.px_ne_temp f i e.symm) hti]
        exact he.mean_E_future hmem (fun m' hm' => absurd hm' (he.tempNoLoan f i m' hmem))
  · -- the temporaries, back
    intro f j l'' hsh
    rw [SState.endAt_shape] at hsh; simp only at hsh
    split at hsh
    · cases hsh
    · next hjr =>
      obtain ⟨i, l₀, h₀, he₀⟩ := hr.sim.2.2.2.2 f j l'' hsh
      refine ⟨i, l₀, ?_, he₀⟩
      change Env.shape (endE st.env px ph c) (.temp f i) = some l₀
      rw [he.shape_endE, if_neg (fun e => hjr ?_)]
      · exact h₀
      · change Env.shape st.env (.temp f i) = some l₀ at h₀
        rw [e, hshph] at h₀; cases h₀
        exact hS.uniq _ r _ (by rw [hsh, he₀]) hrs
  · -- inj
    intro a b ha hb e
    exact hr.inj a b (he.liveLoan_endE ha).1 (he.liveLoan_endE hb).1 e
  · -- sites
    intro l' hl' x
    obtain ⟨hl'E, hne⟩ := he.liveLoan_endE hl'
    have hπ : π l' ≠ π l := fun e => hne (hr.inj l' l hl'E hliveL e)
    rw [he.sitesOf_endE, if_neg hne, ← hr.sites l' hl'E x]
    show x ∈ s.relend (π l) r (π l') ↔ _
    unfold SState.relend
    rw [if_neg hπ]
    constructor
    · intro hx
      obtain ⟨y, hy, hxy⟩ := List.mem_flatMap.mp hx
      have hyr : y.pos ≠ r := fun e => by
        obtain ⟨hyp, hyv⟩ := he.mem_sitesOf ((hr.sites l' hl'E y).mp hy)
        cases hrp : r with
        | bind f j =>
          rw [hrp] at e; rw [e, ← (hrb f j hrp).trans hrp, he.y] at hyv; cases hyv
        | temp f j =>
          rw [hrp] at e; rw [e] at hyv hyp; exact he.tempNoLoan f j l' hyp hyv
      rw [if_neg hyr, List.mem_singleton] at hxy
      subst hxy; exact hy
    · intro hx
      refine List.mem_flatMap.mpr ⟨x, hx, ?_⟩
      have hxr : x.pos ≠ r := fun e => by
        obtain ⟨hyp, hyv⟩ := he.mem_sitesOf ((hr.sites l' hl'E x).mp hx)
        cases hrp : r with
        | bind f j =>
          rw [hrp] at e; rw [e, ← (hrb f j hrp).trans hrp, he.y] at hyv; cases hyv
        | temp f j =>
          rw [hrp] at e; rw [e] at hyv hyp; exact he.tempNoLoan f j l' hyp hyv
      rw [if_neg hxr]; exact List.mem_singleton_self _
  · -- holders
    intro q l' hq
    rw [SState.endAt_shape] at hq; simp only at hq
    split at hq
    · cases hq
    · rw [SState.endAt_positions]; exact hr.holders q l' hq
  · -- records
    intro y hy
    obtain ⟨hy', hne⟩ := (endAt_live_iff hS.uniq hrs y).mp hy
    rw [endAt_holderTy hrs hne]
    exact hr.records y hy'

/-! ## The reference's [Access] that ends exactly one label among several -/

theorem relend_keep {s : SState} {L : Nat} {r : Pos} {m : Nat} (hm : m ≠ L) (h : ∀ x ∈ s.lent m, x.pos ≠ r) :
    s.relend L r m = s.lent m := by
  unfold SState.relend
  rw [if_neg hm]
  generalize s.lent m = xs at h
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.flatMap_cons, if_neg (h x (List.mem_cons_self ..)), ih fun y hy => h y (List.mem_cons_of_mem _ hy)]
    rfl

/-- After the end, no label is reached from `p` if none but the ended one was. -/
theorem endAt_reached {s : SState} {p : Pos} {hit : List Step → Bool} {L : Nat} {r : Pos} (hu : s.Uniq)
    (hrs : s.shape r = some L) (hreach : ∀ z, s.Live z → s.reached p hit z = true → z = L)
    (hnosite : ∀ z, s.Live z → z ≠ L → ∀ x ∈ s.lent z, x.pos ≠ r) :
    ∀ z, (s.endAt L r).Live z → (s.endAt L r).reached p hit z = false := by
  intro z hz
  obtain ⟨hz', hne⟩ := (endAt_live_iff hu hrs z).mp hz
  have e : (s.endAt L r).reached p hit z = s.reached p hit z := by
    unfold SState.reached
    rw [show (s.endAt L r).lent = s.relend L r from rfl, relend_keep hne (hnosite z hz' hne)]
  rw [e]
  cases h : s.reached p hit z
  · rfl
  · exact absurd (hreach z hz' h) hne

theorem accStep_none {t : SState} {p : Pos} {hit : List Step → Bool} (h : ∀ z, t.Live z → t.reached p hit z = false) :
    SState.accStep p hit t = t := by
  unfold SState.accStep
  rw [List.filter_eq_nil_iff.mpr fun z hz => by rw [h z hz]; exact Bool.false_ne_true]
  rfl

/-- **The [Access] of `p` ends exactly the label `L`**, where `L` is the only live label reached from
`p` and nothing is lent at its holder: the state after is the end at the holder, and the access is
strict where that end is. -/
theorem access_one {K : RunCtx} {φ : Future} {s : SState} {p : Pos} {hit : List Step → Bool} {L : Nat} {r : Pos}
    (hu : s.Uniq) (hrs : s.shape r = some L) (hrp : r ∈ s.positions) (hreachL : s.reached p hit L = true)
    (hreach : ∀ z, s.Live z → s.reached p hit z = true → z = L)
    (hnosite : ∀ z, s.Live z → z ≠ L → ∀ x ∈ s.lent z, x.pos ≠ r) :
    s.access p hit = s.endAt L r ∧ (EndOk K φ s L → AccessOk K φ s p hit) := by
  have hL : s.Live L := (SState.live_iff s L).mpr ⟨r, hrp, hrs⟩
  have hhold : s.holderOf L = some r := by
    obtain ⟨r', hr'⟩ := SState.holderOf_of_live hL
    rw [hr', hu r' r _ (SState.holderOf_spec hr').2 hrs]
  have hend := SState.endLabel_eq hhold
  have hnone := endAt_reached hu hrs hreach hnosite
  have hnotL : ¬ (s.endAt L r).Live L := fun h => ((endAt_live_iff hu hrs L).mp h).2 rfl
  have hfix : ∀ (M : List Nat), (∀ z ∈ M, z = L) → M.foldl SState.endLabel (s.endAt L r) = s.endAt L r := by
    intro M hM
    exact foldl_fix _ _ M fun z hz => by rw [hM z hz]; exact endLabel_of_not_live hnotL
  have hfilt : ∀ z ∈ s.liveLabels.filter (s.reached p hit), z = L := fun z hz =>
    hreach z (List.mem_filter.mp hz).1 (List.mem_filter.mp hz).2
  have hstep : SState.accStep p hit s = s.endAt L r := by
    unfold SState.accStep
    have hmem : L ∈ s.liveLabels.filter (s.reached p hit) := List.mem_filter.mpr ⟨hL, hreachL⟩
    cases e : s.liveLabels.filter (s.reached p hit) with
    | nil => rw [e] at hmem; cases hmem
    | cons a M =>
      have ha : a = L := hfilt a (by rw [e]; exact List.mem_cons_self ..)
      subst ha
      rw [List.foldl_cons, hend]
      exact hfix M fun z hz => hfilt z (by rw [e]; exact List.mem_cons_of_mem _ hz)
  have hfold : ∀ k, (List.range (k + 1)).foldl (fun t _ => SState.accStep p hit t) s = s.endAt L r := by
    intro k
    rw [List.range_succ_eq_map, List.foldl_cons, hstep]
    exact foldl_fix _ _ _ fun _ _ => accStep_none hnone
  refine ⟨?_, fun hok => ?_⟩
  · rw [SState.access_eq]
    obtain ⟨k, hk⟩ : ∃ k, s.liveLabels.length = k + 1 := by
      cases e : s.liveLabels with
      | nil => exact absurd hL (by unfold SState.Live; rw [e]; exact List.not_mem_nil)
      | cons a M => exact ⟨M.length, by simp⟩
    rw [hk]; exact hfold k
  · -- the strict ends: round `0` ends `L` (strict by `hok`), later rounds end nothing
    have hends : ∀ (M : List Nat), (∀ z ∈ M, z = L) → EndsOk K φ M s := by
      intro M hM
      cases M with
      | nil => trivial
      | cons a M =>
        obtain rfl := hM a (List.mem_cons_self ..)
        refine ⟨hok, ?_⟩
        rw [hend]
        have : ∀ (M' : List Nat) (t : SState), ¬ t.Live a → (∀ z ∈ M', z = a) → EndsOk K φ M' t := by
          intro M'
          induction M' with
          | nil => intro _ _ _; trivial
          | cons b M' ih =>
            intro t ht hb
            obtain rfl := hb b (List.mem_cons_self ..)
            refine ⟨fun r' hr' => absurd ((SState.live_iff t b).mpr ⟨r', SState.holderOf_spec hr'⟩) ht, ?_⟩
            rw [endLabel_of_not_live ht]
            exact ih t ht fun z hz => hb z (List.mem_cons_of_mem _ hz)
        exact this M _ hnotL fun z hz => hM z (List.mem_cons_of_mem _ hz)
    intro k _
    cases k with
    | zero => exact hends _ hfilt
    | succ k =>
      have hfold' : (List.range (k + 1)).foldl (fun t _ => accRound p hit t) s = s.endAt L r := hfold k
      rw [hfold', List.filter_eq_nil_iff.mpr fun z hz => by rw [hnone z hz]; exact Bool.false_ne_true]
      trivial

end

end Ochr.Meaning.Steps.Form

import Ochr.Meaning.Steps.ColumnReadEnd
import Ochr.Meaning.Steps.ColumnBStart

/-!
# The borrow column's states and the checker's runs of `B`'s sub-terms (lead9)

`def B : Nat := (let x = S(Z); let y = &x; *y := Z; x)`. The steps' preconditions are stated by the
EXACT environment (`Env.erase`, which every query the steps make ignores): one empty frame at the
body (`P0`); `x ↦ S(Z) : Nat` after `x` is bound (`PX`); `x ↦ loan_l`, `y ↦ borrow_l c : &Nat` after
`y` is bound (`PXY c`, `c` the content, `S(Z)` before the write and `Z` after). The checker's runs of
each sub-term, from the facts about the checker alone (`FormMachine.lean`), carry these shapes from
one sub-term to the next, and give the steps' side conditions (the value bound, the binding dropped).
-/

namespace Ochr.Meaning.Steps.Form.ColumnB

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.Steps.Form
open ColumnC ColumnC.Aux

/-! ## The environment's shapes -/

/-- `x`'s binding. -/
def bx (p : Bool) (v : Value) : Binding := { hint := ⟨"x"⟩, ty := some .tNat, val := v, proof := p, decl := duC }
/-- `y`'s binding. -/
def byB (q : Bool) (v : Value) : Binding :=
  { hint := ⟨"y"⟩, ty := some (.tRef .tNat), val := v, proof := q, decl := duY }

def E1 (p : Bool) (xv : Value) : Env := #[{ binds := #[bx p xv] }]
def E2 (p q : Bool) (xv yv : Value) : Env := #[{ binds := #[bx p xv, byB q yv] }]

/-- The body's entry: one empty frame. -/
def P0 (st : MState) : Prop := st.env.erase = stC.env
/-- The inner `let`'s entry and `&x`'s: `x ↦ S(Z) : Nat`, nothing else. -/
def PX (st : MState) : Prop := ∃ p, st.env.erase = E1 p (.succ .zero)
/-- The sequence's entry, the write's and the read's: `x ↦ loan_l`, `y ↦ borrow_l c`, nothing else. -/
def PXY (c : Value) (st : MState) : Prop := ∃ p q l, st.env.erase = E2 p q (.loan l) (.borrow l c)

theorem P0.kern {a b : MState} (h : Kern a b) (ha : P0 a) : P0 b := h.env.symm.trans ha
theorem PX.kern {a b : MState} (h : Kern a b) (ha : PX a) : PX b :=
  let ⟨p, hp⟩ := ha; ⟨p, h.env.symm.trans hp⟩
theorem PXY.kern {c : Value} {a b : MState} (h : Kern a b) (ha : PXY c a) : PXY c b :=
  let ⟨p, q, l, hp⟩ := ha; ⟨p, q, l, h.env.symm.trans hp⟩

/-! ## `Env.erase` commutes with the changes the steps make -/

theorem erase_modify (env : Env) (i : Nat) (g : Frame → Frame)
    (hg : ∀ fr, Frame.erase (g fr) = Frame.erase (g (Frame.erase fr))) :
    Env.erase (env.modify i g) = Env.erase ((Env.erase env).modify i g) := by
  apply Array.ext
  · simp [Env.erase]
  · intro j h1 h2
    simp only [Env.erase, Array.getElem_map, Array.getElem_modify]
    split
    · exact hg _
    · rfl

theorem erase_pushBindE (env : Env) (h : Hint) (T : Option Value) (v : Value) (p : Bool) (d : DeclInfo) :
    Env.erase (Env.pushBindE env h T v p d) = Env.erase (Env.pushBindE (Env.erase env) h T v p d) := by
  unfold Env.pushBindE
  rw [erase_modify _ _ _ (fun _ => rfl)]
  simp [Env.erase]

theorem erase_setAtE (env : Env) (f j : Nat) (v : Value) :
    Env.erase (Env.setAtE env (.bind f j) v) = Env.erase (Env.setAtE (Env.erase env) (.bind f j) v) := by
  unfold Env.setAtE
  exact erase_modify _ _ _ (fun _ => rfl)

theorem erase_E1 (p : Bool) (xv : Value) : Env.erase (E1 p xv) = E1 p xv := by simp [Env.erase, E1, Frame.erase]
theorem erase_E2 (p q : Bool) (xv yv : Value) : Env.erase (E2 p q xv yv) = E2 p q xv yv := by
  simp [Env.erase, E2, Frame.erase]
theorem erase_stC : Env.erase stC.env = stC.env := by simp [Env.erase, stC, Frame.erase]

/-- The top frame's readings, read off the exact environment. -/
theorem readings_of {st : MState} {E : Env} (h : st.env.erase = E) (hE : E.erase = E) :
    DecideScope.topReadings st = DecideScope.topReadings { st with env := E } :=
  topReadings_of_erase (h.trans hE.symm)

theorem P0.readings {st : MState} (h : P0 st) : DecideScope.topReadings st = [] :=
  (readings_of h erase_stC).trans rfl
theorem PX.readings {st : MState} (h : PX st) : DecideScope.topReadings st = [duC] :=
  let ⟨p, hp⟩ := h; (readings_of hp (erase_E1 _ _)).trans rfl
theorem PXY.readings {c : Value} {st : MState} (h : PXY c st) : DecideScope.topReadings st = [duY, duC] :=
  let ⟨p, q, l, hp⟩ := h; (readings_of hp (erase_E2 _ _ _ _)).trans rfl

/-! ## Queries on the shapes -/

theorem allPos_E1 (p : Bool) (xv : Value) : allPos (E1 p xv) = [.bind 0 0] := by
  rw [allPos_eq]; simp [E1, frameAllPos]
theorem allPos_E2 (p q : Bool) (xv yv : Value) : allPos (E2 p q xv yv) = [.bind 0 0, .bind 0 1] := by
  rw [allPos_eq]; simp [E2, frameAllPos, List.range_succ]

/-- What an exact environment says of the checker's own: positions, values, bindings, variables. -/
theorem env_facts {st : MState} {E : Env} (h : st.env.erase = E) (hE : E.erase = E) :
    allPos st.env = allPos E ∧ (∀ q, valAt st.env q = valAt E q) ∧
    (∀ f j : Nat, st.env[f]?.bind (fun fr : Frame => fr.binds[j]?) = E[f]?.bind (fun fr : Frame => fr.binds[j]?)) ∧
    (∀ i : Nat, ckVarPos st.env i = ckVarPos E i) ∧ (∀ l : Nat, liveLoan st.env l = liveLoan E l) := by
  have h' : st.env.erase = E.erase := h.trans hE.symm
  refine ⟨?_, fun q => ?_, fun f j => ?_, fun i => ?_, fun l => ?_⟩
  · rw [← allPos_erase, h', allPos_erase]
  · rw [← valAt_erase, h', valAt_erase]
  · rw [← lookup_erase, h', lookup_erase]
  · rw [← ckVarPos_erase, h', ckVarPos_erase]
  · rw [← liveLoan_erase, h', liveLoan_erase]

theorem PX.borrowPre {st : MState} (h : PX st) : BorrowPre 0 st := by
  obtain ⟨p, hp⟩ := h
  obtain ⟨ha, hv, hl, hc, hlv⟩ := env_facts hp (erase_E1 _ _)
  refine ⟨⟨0, 0, bx p (.succ .zero), by rw [hc]; rfl, by rw [hl]; rfl, .succ .zero, rfl⟩, fun l => ?_, ?_⟩
  · rw [hlv]; simp [liveLoan, findBorrow, allPos_E1]; rfl
  · intro q hq l _
    rw [ha, allPos_E1, List.mem_singleton] at hq
    subst hq
    rw [hv]; exact Value.Num.sitesOf (.succ .zero) l _ _

theorem PXY.derefVar {c : Value} (hc : c.Num) {st : MState} (h : PXY c st) : DerefVar 0 st := by
  obtain ⟨p, q, l, hp⟩ := h
  obtain ⟨-, -, hl, hck, -⟩ := env_facts hp (erase_E2 _ _ _ _)
  exact ⟨0, 1, byB q (.borrow l c), l, c, by rw [hck]; rfl, by rw [hl]; rfl, rfl, hc, rfl⟩

theorem PXY.readPre {st : MState} (h : PXY .zero st) : ∃ l w, ReadPre st l w := by
  obtain ⟨p, q, l, hp⟩ := h
  obtain ⟨ha, hv, hl, hck, -⟩ := env_facts hp (erase_E2 _ _ _ _)
  refine ⟨l, .zero, ⟨by rw [ha, allPos_E2], by rw [hck]; rfl, by rw [hv]; rfl, by rw [hv]; rfl, .zero, ?_, ?_⟩⟩
  · intro bx' hb; rw [hl] at hb; cases hb; rfl
  · intro by' hb; rw [hl] at hb; cases hb; rfl

end Ochr.Meaning.Steps.Form.ColumnB

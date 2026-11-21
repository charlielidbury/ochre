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

/-! ## The shapes after the steps' changes -/

theorem push_E0 (p : Bool) (xv : Value) :
    Env.erase (Env.pushBindE stC.env ⟨"x"⟩ (some .tNat) xv p duC) = E1 p xv := by
  simp [Env.pushBindE, stC, E1, bx, Env.erase, Frame.erase, duC]
theorem push_E1 (p q : Bool) (xv yv : Value) :
    Env.erase (Env.pushBindE (E1 p xv) ⟨"y"⟩ (some (.tRef .tNat)) yv q duY) = E2 p q xv yv := by
  simp [Env.pushBindE, E1, E2, bx, byB, Env.erase, Frame.erase]
theorem set_E1 (p : Bool) (xv w : Value) : Env.erase (Env.setAtE (E1 p xv) (.bind 0 0) w) = E1 p w := by
  simp [Env.setAtE, E1, bx, Env.erase, Frame.erase]
theorem set_E2_0 (p q : Bool) (xv yv w : Value) :
    Env.erase (Env.setAtE (E2 p q xv yv) (.bind 0 0) w) = E2 p q w yv := by
  simp [Env.setAtE, E2, bx, byB, Env.erase, Frame.erase]
theorem set_E2_1 (p q : Bool) (xv yv w : Value) :
    Env.erase (Env.setAtE (E2 p q xv yv) (.bind 0 1) w) = E2 p q xv w := by
  simp [Env.setAtE, E2, bx, byB, Env.erase, Frame.erase]

theorem ck_E1 (p : Bool) (xv : Value) : ckVarPos (E1 p xv) 0 = some (.bind 0 0) := rfl
theorem ck_E2_0 (p q : Bool) (xv yv : Value) : ckVarPos (E2 p q xv yv) 0 = some (.bind 0 1) := rfl
theorem ck_E2_1 (p q : Bool) (xv yv : Value) : ckVarPos (E2 p q xv yv) 1 = some (.bind 0 0) := rfl

/-! ## The checker's runs of `&x`, `*y := Z` and the read of `x` -/

section
variable {D : Decisions}

theorem size_E1 {st : MState} {p : Bool} {xv : Value} (h : st.env.erase = E1 p xv) : 0 < st.env.size := by
  rw [size_of_erase (h.trans (erase_E1 _ _).symm)]; exact Nat.zero_lt_one

/-- `eval` of `&x` from `x ↦ S(Z)`: `borrow_l S(Z)` at `&Nat`, `x ↦ loan_l`. -/
theorem run_bor (hE : EvalInv) (hB : BorrowNumInv) (hd : DecTab D stC) {g : Nat} {hint : Option Value}
    {st st' : MState} {bh : Nat} {v : Value} {T? : Option Value} (hX : PX st) (hm : Mode st)
    (htd : st.tailDecl = none) (hD : DecTab D st')
    (h : Runs (Ochr.eval (g + 9) true (.borrow (.var 0)) hint) st bh (v, T?) st') :
    ∃ p l, v = .borrow l (.succ .zero) ∧ T? = some (.tRef .tNat) ∧ Mode st' ∧ st'.env.erase = E1 p (.loan l) := by
  obtain ⟨st₀, st₁, bh', hk₀, hm₀, -, -, -, -, h₀, hk₁, hmm⟩ :=
    hE (g + 7) true _ hint st st' bh v T? D hm hD (fun _ e => by cases e) (fun _ _ _ e => by cases e)
      (by rw [hX.readings, declOf_bor hd]; exact duY_ok.1) (by rw [hX.readings, declOf_bor hd]; exact duY_ok.2)
      (.inl htd) h
  obtain ⟨p, hp⟩ := hX.kern hk₀
  obtain ⟨-, -, hl, hck, -⟩ := env_facts hp (erase_E1 _ _)
  obtain ⟨hm₁, c, hq, -, rfl, rfl, hk⟩ := hB (g + 6) 0 hint st₀ st₁ bh' v T? 0 0 (bx p (.succ .zero)) D hm₀
    (by rw [hck]; rfl) (by rw [hl]; rfl) (.succ .zero) rfl (DecTab.of_kern hk₁.symm hD) h₀
  refine ⟨p, c.nextLoan, rfl, rfl, hmm hm₁, ?_⟩
  rw [← hk₁.env, ← hk.env]
  show Env.erase (Env.setAtE c.env (.bind 0 0) (.loan c.nextLoan)) = _
  rw [erase_setAtE, ← hq.env, hp, set_E1]

/-- `eval` of `*y := Z` from `y ↦ borrow_l S(Z)`: `()` at `Unit`, `y ↦ borrow_l Z`. -/
theorem run_write (hE : EvalInv) (hZ : ZeroInv) (hA : AssignDerefInv) (hd : DecTab D stC) {g : Nat}
    {hint : Option Value} {st st' : MState} {bh : Nat} {v : Value} {T? : Option Value}
    (hXY : PXY (.succ .zero) st) (hm : Mode st) (htd : st.tailDecl = none) (hD : DecTab D st')
    (h : Runs (Ochr.eval (g + 6) true writeB hint) st bh (v, T?) st') :
    v = .unit ∧ T? = some .tUnit ∧ Mode st' ∧ PXY .zero st' := by
  obtain ⟨st₀, st₁, bh', hk₀, hm₀, -, htn₀, htd₀, -, h₀, hk₁, hmm⟩ :=
    hE (g + 4) true writeB hint st st' bh v T? D hm hD (fun _ e => by cases e) (fun _ _ _ e => by cases e)
      (by rw [hXY.readings]; exact (declOf_write_ok hd).1) (by rw [hXY.readings]; exact (declOf_write_ok hd).2)
      (.inl htd) h
  obtain ⟨p, q, l, hp⟩ := hXY.kern hk₀
  obtain ⟨-, -, hl, hck, -⟩ := env_facts hp (erase_E2 _ _ _ _)
  obtain ⟨a₀, a₁, a₂, hu, v₀, T₀, bh₁, f, j, b, lb, w, hka, hma, -, htda, hru, hD₁, hq, -, hme, hck₂, hl₂, hbw, hkw,
    rfl, rfl⟩ := hA (g + 3) 0 .zero hint st₀ st₁ bh' v T? D hm₀ htn₀ htd₀
      (fun f j b hc hb => by
        rw [hck, ck_E2_0] at hc; cases hc
        rw [hl] at hb; have hb' : some (byB q (.borrow l (.succ .zero))) = some b := hb; cases hb'; rfl)
      (DecTab.of_kern hk₁.symm hD) h₀
  have hra : DecideScope.topReadings a₀ = [duY, duC] := (PXY.readings ⟨p, q, l, hp⟩).symm ▸ topReadings_kern hka |>.symm
  obtain ⟨rfl, rfl, hkz, hmz⟩ := run_zero hE hZ hma hD₁ (by rw [hra]; exact flags_Zy hd)
    (by rw [hra, declOf_Zy hd]; exact duC_ok) htda hru
  have hp₂ : a₂.env.erase = E2 p q (.loan l) (.borrow l (.succ .zero)) :=
    hq.env.symm.trans (hkz.env.symm.trans (hka.env.symm.trans hp))
  obtain ⟨-, hv₂, hl₂', hck₂', -⟩ := env_facts hp₂ (erase_E2 _ _ _ _)
  rw [hck₂', ck_E2_0] at hck₂; cases hck₂
  rw [hl₂'] at hl₂; have hb₂ : some (byB q (.borrow l (.succ .zero))) = some b := hl₂; cases hb₂
  cases hbw
  have hk := hkw (fun m z e => by cases e) (fun l' => by
    rw [hv₂]; show Value.sitesOf l' (.bind 0 1) ([] ++ [.deref]) (Value.succ .zero) = []
    exact Value.Num.sitesOf (.succ .zero) l' (.bind 0 1) ([] ++ [.deref]))
  refine ⟨rfl, rfl, hmm (hmz.of_modeEq hme), p, q, l, ?_⟩
  rw [← hk₁.env, ← hk.env]
  show Env.erase (Env.setAtE a₂.env (.bind 0 1) (.borrow l .zero)) = _
  rw [erase_setAtE, hp₂, set_E2_1]

/-- `eval` of the read of `x` from `x ↦ loan_l`, `y ↦ borrow_l Z`: `Z` at `Nat`; `y ↦ ⊥`, `x ↦ Z` (a
copy) or `⊥` (a move). -/
theorem run_read (hE : EvalInv) (hVE : VarEndInv) (hd : DecTab D stC) {g : Nat} {hint : Option Value}
    {st st' : MState} {bh : Nat} {v : Value} {T? : Option Value} (hXY : PXY .zero st) (hm : Mode st)
    (htd : st.tailDecl = none ∨ st.tailDecl = some (D.declOf (DecideScope.topReadings st) (.place (.var 1))))
    (hD : DecTab D st') (h : Runs (Ochr.eval (g + 6) true (.place (.var 1)) hint) st bh (v, T?) st') :
    v = .zero ∧ T? = some .tNat ∧ Mode st' ∧ ∃ p q xv, (xv = .zero ∨ xv = .bot) ∧ st'.env.erase = E2 p q xv .bot := by
  obtain ⟨st₀, st₁, bh', hk₀, hm₀, -, -, -, -, h₀, hk₁, hmm⟩ :=
    hE (g + 4) true _ hint st st' bh v T? D hm hD (fun _ e => by cases e) (fun _ _ _ e => by cases e)
      (by rw [hXY.readings, declOf_x1 hd]; exact duC_ok.1) (by rw [hXY.readings, declOf_x1 hd]; exact duC_ok.2) htd h
  obtain ⟨p, q, l, hp⟩ := hXY.kern hk₀
  obtain ⟨ha, hv, hl, -, -⟩ := env_facts hp (erase_E2 _ _ _ _)
  obtain ⟨rfl, hT, hm₁, c, hq, -, hcopy, hmove⟩ := hVE (g + 3) true hint st₀ st₁ bh' v T? l .zero D hm₀
    (by rw [ha, allPos_E2]) (by rw [hv]; rfl) (by rw [hv]; rfl) .zero
    (fun bx' hb => by rw [hl] at hb; have hb' : some (bx p (.loan l)) = some bx' := hb; cases hb'; rfl)
    (DecTab.of_kern hk₁.symm hD) h₀
  refine ⟨rfl, hT rfl, hmm hm₁, ?_⟩
  have hpc : c.env.erase = E2 p q (.loan l) (.borrow l .zero) := hq.env.symm.trans hp
  have key : ∀ xv, Kern { c with env := Env.setAtE (Env.setAtE c.env (.bind 0 1) .bot) (.bind 0 0) xv } st₁ →
      st'.env.erase = E2 p q xv .bot := fun xv hk => by
    rw [← hk₁.env, ← hk.env]
    show Env.erase (Env.setAtE (Env.setAtE c.env (.bind 0 1) .bot) (.bind 0 0) xv) = _
    rw [erase_setAtE (Env.setAtE c.env (.bind 0 1) .bot), erase_setAtE c.env, hpc, set_E2_1, set_E2_0]
  cases hc : D.copy (D.placeDecl (DecideScope.topReadings st₀) (.var 1))
  · exact ⟨p, q, .bot, .inr rfl, key _ (hmove hc)⟩
  · exact ⟨p, q, .zero, .inl rfl, key _ (hcopy hc)⟩

end

/-- The top frame under a temporary pushed has the top frame's bindings. -/
theorem top_of_withTempT {st : MState} {v : Value} {T? : Option Value} {fr : Frame}
    (h : (st.withTempT v T?).env[(st.withTempT v T?).env.size - 1]? = some fr) :
    ∃ fr', st.env[st.env.size - 1]? = some fr' ∧ fr'.binds = fr.binds := by
  simp only [MState.withTempT, Array.size_modify, Array.getElem?_modify, if_true] at h
  cases e : st.env[st.env.size - 1]? with
  | none => rw [e] at h; simp at h
  | some fr' => rw [e] at h; simp at h; subst h; exact ⟨fr', rfl, rfl⟩

theorem top_withTempT {st : MState} {v : Value} {T? : Option Value} {fr : Frame}
    (h : st.env[st.env.size - 1]? = some fr) :
    (st.withTempT v T?).env[(st.withTempT v T?).env.size - 1]? =
      some { fr with temps := fr.temps.push v, tempTys := fr.tempTys.push T? } := by
  simp only [MState.withTempT, Array.size_modify, Array.getElem?_modify, if_true, h]; rfl

theorem top_popBindE {env : Env} {fr : Frame} (h : env[env.size - 1]? = some fr) :
    (Env.popBindE env)[(Env.popBindE env).size - 1]? = some { fr with binds := fr.binds.pop } := by
  simp only [Env.popBindE, Array.size_modify, Array.getElem?_modify, if_true, h]; rfl

/-- After a `let` whose tail left its binding on top of a frame `fr₂` (the tail's value parked above
it), and the drop that pops it: the frame below the end's temporary is `fr₂` without that binding. -/
theorem top_after_drop {a₂ a₃ st₁ st' : MState} {r v : Value} {T? : Option Value} {fr₂ : Frame}
    (hfr₂ : a₂.env[a₂.env.size - 1]? = some fr₂)
    (h₃ : Kern { a₂.withTempT r T? with env := Env.popBindE (a₂.withTempT r T?).env } a₃)
    (hk₃ : Kern a₃ (st₁.withTempT v T?)) (hk₁ : Kern st₁ st') :
    ∃ fr, st'.env[st'.env.size - 1]? = some fr ∧ fr.binds = fr₂.binds.pop := by
  have hp := top_popBindE (top_withTempT (v := r) (T? := T?) hfr₂)
  obtain ⟨f1, hf1, hb1⟩ := top_of_erase (h₃.env.trans hk₃.env) hp
  obtain ⟨f2, hf2, hb2⟩ := top_of_withTempT hf1
  obtain ⟨f3, hf3, hb3⟩ := top_of_erase hk₁.env hf2
  exact ⟨f3, hf3, by rw [hb3, hb2, hb1]⟩

/-! ## The sequence, the inner `let`, the body -/

section
variable {D : Decisions}

/-- `eval` of `*y := Z; x` from `y ↦ borrow_l S(Z)`: `Z` at `Nat`; `y ↦ ⊥`, `x ↦ Z` or `⊥`. -/
theorem run_seq (hE : EvalInv) (hZ : ZeroInv) (hA : AssignDerefInv) (hVE : VarEndInv) (hSq : SeqInv)
    (hd : DecTab D stC) {g : Nat} {hint : Option Value} {st st' : MState} {bh : Nat} {v : Value}
    {T? : Option Value} (hXY : PXY (.succ .zero) st) (hm : Mode st)
    (htd : st.tailDecl = none ∨ st.tailDecl = some (D.declOf (DecideScope.topReadings st) seqB)) (hD : DecTab D st')
    (h : Runs (Ochr.eval (g + 9) true seqB hint) st bh (v, T?) st') :
    v = .zero ∧ T? = some .tNat ∧ ∃ p q xv, (xv = .zero ∨ xv = .bot) ∧ st'.env.erase = E2 p q xv .bot := by
  obtain ⟨st₀, st₁, bh', hk₀, hm₀, -, htn₀, htd₀, hcd₀, h₀, hk₁, -⟩ :=
    hE (g + 7) true seqB hint st st' bh v T? D hm hD (fun _ e => by cases e) (fun _ _ _ e => by cases e)
      (by rw [hXY.readings, declOf_seq hd]; exact duC_ok.1) (by rw [hXY.readings, declOf_seq hd]; exact duC_ok.2)
      htd h
  obtain ⟨a₀, a₁, aW, v₀, T₀, bh₁, bh₂, hka, hma, -, htda, htdW, hru, hD₁, hdrop, -, hrw⟩ :=
    hSq (g + 6) writeB (.place (.var 1)) hint st₀ st₁ bh' v T? D hm₀ htn₀ htd₀ (DecTab.of_kern hk₁.symm hD) h₀
  obtain ⟨rfl, -, hm₁, hXY₁⟩ := run_write hE hZ hA hd (hXY.kern (hk₀.trans hka)) hma htda hD₁ hru
  have hXYW := hXY₁.kern (hdrop (fun _ => rfl) rfl).1
  obtain ⟨rfl, hT, -, p, q, xv, hxv, he⟩ := run_read hE hVE hd hXYW (hm₁.of_modeEq (hdrop (fun _ => rfl) rfl).2)
    (by
      rcases htdW with e | e
      · exact .inl e
      · exact .inr (by rw [e, hcd₀, (hXY.kern hk₀).readings, hXYW.readings, declOf_seq hd, declOf_x1 hd]))
    (DecTab.of_kern hk₁.symm hD) hrw
  exact ⟨rfl, hT, p, q, xv, hxv, hk₁.env.symm.trans he⟩

end

section
variable {D : Decisions}

/-- The drop of a binding holding `⊥` or a number, with the tail's value `r` parked above it. -/
theorem drop_bot_or_num (hDN : DropNoopInv) {n : Nat} {a₂ a₃ : MState} {r : Value} {T? : Option Value} {bh : Nat}
    {fr₂ : Frame} {b : Binding} (hfr₂ : a₂.env[a₂.env.size - 1]? = some fr₂) (hb : fr₂.binds.back? = some b)
    (hbv : b.val = .bot ∨ b.val.Num) (hrd : Runs (Ochr.dropTopBind n) (a₂.withTempT r T?) bh () a₃) :
    Kern { a₂.withTempT r T? with env := Env.popBindE (a₂.withTempT r T?).env } a₃ := by
  refine hDN n _ a₃ bh _ b (top_withTempT hfr₂) hb ?_ ?_ ?_ hrd
  · rcases hbv with e | e
    · rw [e]; simp [Value.loans]
    · exact e.loans
  · intro l w; rcases hbv with e | e
    · rw [e]; intro e'; cases e'
    · exact e.not_borrow l w
  · intro l; rcases hbv with e | e
    · rw [e]; rfl
    · exact e.holdsBorrow l

theorem size_pos_of_top {env : Env} {fr : Frame} (h : env[env.size - 1]? = some fr) : 0 < env.size := by
  rcases Nat.eq_zero_or_pos env.size with h0 | h0
  · rw [Array.getElem?_eq_none (by omega)] at h; cases h
  · exact h0

/-- `eval` of the inner `let y = &x; *y := Z; x` from `x ↦ S(Z)`: `Z` at `Nat`; after it the top
binding (`x`) holds `Z` or `⊥`. -/
theorem run_inner (hE : EvalInv) (hZ : ZeroInv) (hB : BorrowNumInv) (hA : AssignDerefInv) (hVE : VarEndInv)
    (hSq : SeqInv) (hL : LetInv) (hDN : DropNoopInv) (hd : DecTab D stC) {g : Nat} {hint : Option Value}
    {st st' : MState} {bh : Nat} {v : Value} {T? : Option Value} (hX : PX st) (hm : Mode st)
    (htd : st.tailDecl = none ∨ st.tailDecl = some (D.declOf (DecideScope.topReadings st) innerB))
    (hD : DecTab D st') (h : Runs (Ochr.eval (g + 12) true innerB hint) st bh (v, T?) st') :
    v = .zero ∧ T? = some .tNat ∧
      ∃ fr b, st'.env[st'.env.size - 1]? = some fr ∧ fr.binds.back? = some b ∧ (b.val = .bot ∨ b.val.Num) := by
  obtain ⟨st₀, st₁, bh', hk₀, hm₀, -, htn₀, htd₀, hcd₀, h₀, hk₁, -⟩ :=
    hE (g + 10) true innerB hint st st' bh v T? D hm hD (fun _ e => by cases e) (fun _ _ _ e => by cases e)
      (by rw [hX.readings, declOf_inner hd]; exact duC_ok.1) (by rw [hX.readings, declOf_inner hd]; exact duC_ok.2)
      htd h
  obtain ⟨du, a₀, a₁, aB, a₂, a₃, v₀, r, T₀, pB, b₁, b₂, b₃, hka, hma, -, htda, htdB, hru, hdu, hkB, hmeB, -, hrw,
    hrd, hk₃, -, hD₁, hD₂⟩ :=
    hL (g + 9) ⟨"y"⟩ (.borrow (.var 0)) seqB hint st₀ st₁ bh' v T? D hm₀ htn₀ htd₀ (DecTab.of_kern hk₁.symm hD) h₀
  have hX₀ := hX.kern hk₀
  obtain ⟨p, l, rfl, rfl, hm₁, he₁⟩ := run_bor hE hB hd (hX₀.kern hka) hma htda hD₁ hru
  obtain rfl : du = duY := by rw [← hdu, hX₀.readings, declOf_bor hd]
  have hXYB : PXY (.succ .zero) aB := ⟨p, pB, l, by
    rw [← hkB.env]
    show Env.erase (Env.pushBindE a₁.env _ _ _ _ _) = _
    rw [erase_pushBindE, he₁, push_E1]⟩
  obtain ⟨rfl, rfl, p', q', xv, hxv, he₂⟩ := run_seq hE hZ hA hVE hSq hd hXYB (hm₁.of_modeEq hmeB)
    (.inr (by rw [htdB, hcd₀, hX₀.readings, hXYB.readings, declOf_inner hd, declOf_seq hd])) hD₂ hrw
  obtain ⟨fr₂, hfr₂, hbs₂⟩ := top_of_erase ((erase_E2 p' q' xv .bot).trans he₂.symm)
    (fr := { binds := #[bx p' xv, byB q' .bot] }) rfl
  have h₃ := drop_bot_or_num hDN hfr₂ (b := byB q' .bot) (by rw [hbs₂]; rfl) (.inl rfl) hrd
  obtain rfl := popped_eq (size_pos_of_top hfr₂) h₃ hk₃
  obtain ⟨fr, hfr, hbs⟩ := top_after_drop hfr₂ h₃ hk₃ hk₁
  refine ⟨rfl, rfl, fr, bx p' xv, hfr, by rw [hbs, hbs₂]; rfl, ?_⟩
  rcases hxv with e | e
  · exact .inr (by rw [e]; exact .zero)
  · exact .inl e

/-- **The checker's run of the body of `B`**: its value is `Z`, at `Nat`. -/
theorem run_bodyB (hE : EvalInv) (hZ : ZeroInv) (hS : SuccInv) (hB : BorrowNumInv) (hA : AssignDerefInv)
    (hVE : VarEndInv) (hSq : SeqInv) (hL : LetInv) (hDN : DropNoopInv) (hd : DecTab D stC) {g : Nat}
    {hint : Option Value} {st st' : MState} {bh : Nat} {v : Value} {T? : Option Value} (hP : P0 st) (hm : Mode st)
    (htd : st.tailDecl = none ∨ st.tailDecl = some (D.declOf (DecideScope.topReadings st) bodyB))
    (hD : DecTab D st') (h : Runs (Ochr.eval (g + 15) true bodyB hint) st bh (v, T?) st') :
    v = .zero ∧ T? = some .tNat := by
  obtain ⟨st₀, st₁, bh', hk₀, hm₀, -, htn₀, htd₀, hcd₀, h₀, hk₁, -⟩ :=
    hE (g + 13) true bodyB hint st st' bh v T? D hm hD (fun _ e => by cases e) (fun _ _ _ e => by cases e)
      (by rw [hP.readings, declOf_bodyB hd]; exact duC_ok.1) (by rw [hP.readings, declOf_bodyB hd]; exact duC_ok.2)
      htd h
  obtain ⟨du, a₀, a₁, aB, a₂, a₃, v₀, r, T₀, pB, b₁, b₂, b₃, hka, hma, -, htda, htdB, hru, hdu, hkB, hmeB, -, hrw,
    hrd, hk₃, -, hD₁, hD₂⟩ :=
    hL (g + 12) ⟨"x"⟩ (.succ .zero) innerB hint st₀ st₁ bh' v T? D hm₀ htn₀ htd₀ (DecTab.of_kern hk₁.symm hD) h₀
  have hP₀ := hP.kern hk₀
  have hra : DecideScope.topReadings a₀ = [] := (hP₀.kern hka).readings
  obtain ⟨rfl, rfl, he, hm₁⟩ := run_SZ hE hZ hS hma hD₁ (by rw [hra]; exact flags_SZ hd) (by rw [hra]; exact flags_Z hd)
    (by rw [hra, declOf_SZ hd]; exact duC_ok) (by rw [hra]; exact declOf_Z_ok hd) htda hru
  obtain rfl : du = duC := by rw [← hdu, hP₀.readings, declOf_SZ hd]
  have hXB : PX aB := ⟨pB, by
    rw [← hkB.env]
    show Env.erase (Env.pushBindE a₁.env _ _ _ _ _) = _
    rw [erase_pushBindE, ← he, hP₀.kern hka, push_E0]⟩
  obtain ⟨rfl, rfl, fr₂, bx₂, hfr₂, hbx₂, hbv₂⟩ := run_inner hE hZ hB hA hVE hSq hL hDN hd hXB (hm₁.of_modeEq hmeB)
    (.inr (by rw [htdB, hcd₀, hP₀.readings, hXB.readings, declOf_bodyB hd, declOf_inner hd])) hD₂ hrw
  exact ⟨popped_eq (size_pos_of_top hfr₂) (drop_bot_or_num hDN hfr₂ hbx₂ hbv₂ hrd) hk₃, rfl⟩

end

end Ochr.Meaning.Steps.Form.ColumnB

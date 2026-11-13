import Ochr.Meaning.Locality

/-!
# Future-locality through the run's state operations (towards `run_congr`)

`RInv L s` bundles the invariant `run_congr` carries through a run: (I1), (I2) and `ShapeAt` (every
shape entry at a real position, with a label below the counter). Each state operation the run
uses keeps it: the ends, [Access], writes whose new meaning reads what the old one did, a fresh
label, pushes of constants, the holder transfers (a move parks the borrow again, a binding takes
it over), and the drop of a binding that holds nothing.
-/

namespace Ochr.Meaning

namespace SState

variable {L : Nat → Prop}

/-- The invariant `run_congr` carries. -/
def RInv (L : Nat → Prop) (s : SState) : Prop := Inv1 L s ∧ Inv2 L s ∧ ShapeAt s

/-! ## Ends and [Access] -/

theorem endAt_shapeAt {s : SState} (hsa : ShapeAt s) (l : Nat) (r : Pos) : ShapeAt (s.endAt l r) := by
  intro p x hp
  rw [endAt_shape] at hp
  simp only at hp
  split at hp
  · cases hp
  · obtain ⟨h1, h2⟩ := hsa p x hp
    refine ⟨by rw [endAt_positions]; exact h1, ?_⟩
    show x < (({ s with shape := fun p => if p = r then none else s.shape p } : SState).mapVals _).nextLoan
    exact h2

theorem endLabel_rinv {s : SState} (h : RInv L s) (l : Nat) : RInv L (s.endLabel l) := by
  obtain ⟨h1, h2, hsa⟩ := h
  obtain ⟨h1', h2'⟩ := endLabel_inv h1 h2 l
  refine ⟨h1', h2', ?_⟩
  cases e : s.holderOf l with
  | none => rw [endLabel_of_none e]; exact hsa
  | some r => rw [endLabel_eq e]; exact endAt_shapeAt hsa l r

theorem foldl_endLabel_rinv : ∀ (ls : List Nat) {s : SState}, RInv L s → RInv L (ls.foldl endLabel s)
  | [], _, h => h
  | l :: ls, _, h => foldl_endLabel_rinv ls (endLabel_rinv h l)

theorem accStep_rinv {s : SState} (h : RInv L s) (p : Pos) : RInv L (accStep p s) :=
  foldl_endLabel_rinv _ h

theorem iterR_accStep_rinv (p : Pos) : ∀ (k : Nat) {s : SState}, RInv L s → RInv L (iterR (accStep p) k s)
  | 0, _, h => h
  | k + 1, _, h => accStep_rinv (iterR_accStep_rinv p k h) p

theorem access_rinv {s : SState} (h : RInv L s) (p : Pos) : RInv L (s.access p) := by
  rw [access_eq, foldl_range_iterR]
  exact iterR_accStep_rinv p _ h

/-! ## Writes, a fresh label -/

theorem shape_setAt' (s : SState) (p : Pos) (v : SVal) : (s.setAt p v).shape = s.shape := by
  cases p <;> rfl

theorem nextLoan_setAt' (s : SState) (p : Pos) (v : SVal) : (s.setAt p v).nextLoan = s.nextLoan := by
  cases p <;> rfl

theorem live_setAt (s : SState) (p : Pos) (v : SVal) (y : Nat) : (s.setAt p v).Live y ↔ s.Live y := by
  rw [live_iff, live_iff, positions_setAt, shape_setAt']

theorem valAt_setAt_ne (s : SState) (p : Pos) (v : SVal) (q : Pos) (hne : p ≠ q) :
    (s.setAt p v).valAt q = s.valAt q := by
  cases p with
  | bind f i =>
    cases q with
    | bind f' i' =>
      simp only [setAt, valAt, List.getElem?_modify]
      by_cases hf : f = f'
      · subst hf
        have hi : i ≠ i' := fun e => hne (by rw [e])
        cases s.env[f]? with
        | none => rfl
        | some fr => simp [List.getElem?_modify, hi]
      · simp [hf]
    | temp f' i' =>
      simp only [setAt, valAt, List.getElem?_modify]
      by_cases hf : f = f'
      · subst hf; cases s.env[f]? <;> simp
      · simp [hf]
  | temp f i =>
    cases q with
    | bind f' i' =>
      simp only [setAt, valAt, List.getElem?_modify]
      by_cases hf : f = f'
      · subst hf; cases s.env[f]? <;> simp
      · simp [hf]
    | temp f' i' =>
      simp only [setAt, valAt, List.getElem?_modify]
      by_cases hf : f = f'
      · subst hf
        have hi : i ≠ i' := fun e => hne (by rw [e])
        cases s.env[f]? with
        | none => rfl
        | some fr => simp [List.getElem?_set_ne hi]
      · simp [hf]

/-- A write keeps the invariant when the new meaning reads what an old meaning there could
(`hv1`, and `hv2` if the position holds a borrow). -/
theorem setAt_rinv {s : SState} (h : RInv L s) (p : Pos) (v : SVal)
    (hv1 : FT (fun y => L y ∨ s.Live y) v)
    (hv2 : ∀ x, s.shape p = some x → FT (fun y => (L y ∧ ¬ s.Live y) ∨ (s.Live y ∧ x < y)) v) :
    RInv L (s.setAt p v) := by
  obtain ⟨h1, h2, hsa⟩ := h
  have hl : ∀ y, (s.setAt p v).Live y ↔ s.Live y := live_setAt s p v
  refine ⟨fun q => ?_, fun r x hr hs => ?_, fun q x hq => ?_⟩
  · rcases valAt_setAt s p v q with e | e
    · rw [e]; exact (h1 q).mono fun y hy => hy.imp_right (hl y).mpr
    · rw [e]; exact hv1.mono fun y hy => hy.imp_right (hl y).mpr
  · rw [shape_setAt'] at hs
    rw [positions_setAt] at hr
    have hm : FT (fun y => (L y ∧ ¬ s.Live y) ∨ (s.Live y ∧ x < y))
        ((s.setAt p v).valAt r) := by
      rcases valAt_setAt s p v r with e | e
      · rw [e]; exact h2 r x hr hs
      · rw [e]
        by_cases hpr : p = r
        · subst hpr; exact hv2 x hs
        · -- the write landed elsewhere, so r's meaning is the old one
          rw [← e, valAt_setAt_ne s p v r hpr]; exact h2 r x hr hs
    exact hm.mono fun y hy => by
      rcases hy with ⟨hL, hn⟩ | ⟨hy, hxy⟩
      · exact .inl ⟨hL, fun h' => hn ((hl y).mp h')⟩
      · exact .inr ⟨(hl y).mpr hy, hxy⟩
  · rw [shape_setAt'] at hq
    rw [positions_setAt, nextLoan_setAt']
    exact hsa q x hq

theorem freshLoan_rinv {s : SState} (h : RInv L s) : RInv L s.freshLoan.2 := by
  obtain ⟨h1, h2, hsa⟩ := h
  refine ⟨h1, h2, fun p x hp => ?_⟩
  obtain ⟨hp1, hp2⟩ := hsa p x hp
  exact ⟨hp1, Nat.lt_succ_of_lt hp2⟩

/-! ## Holder transfers: a move parks the borrow again -/

theorem takeLabel_shape (s : SState) (l : Nat) (q : Pos) :
    (s.takeLabel l).shape q = s.shape q ∨ (s.takeLabel l).shape q = none := by
  unfold takeLabel
  cases s.holderOf l with
  | none => exact .inl rfl
  | some r =>
    show (if q = r then none else s.shape q) = s.shape q ∨ (if q = r then none else s.shape q) = none
    split
    · exact .inr rfl
    · exact .inl rfl

theorem takeLabel_shapeAt {s : SState} (hsa : ShapeAt s) (l : Nat) : ShapeAt (s.takeLabel l) := by
  intro p x hp
  have hp' := takeLabel_shape_some hp
  refine ⟨by rw [takeLabel_positions]; exact (hsa p x hp').1, ?_⟩
  have : (s.takeLabel l).nextLoan = s.nextLoan := (shapeSub_takeLabel s l).2
  rw [this]; exact (hsa p x hp').2

/-- Parking keeps every shape entry at a real position below the counter. -/
theorem pushTempShaped_shapeAt {s : SState} (hsa : ShapeAt s) (hne : s.env ≠ []) (v : SVal) (l : Nat)
    (hl : l < s.nextLoan) : ShapeAt (s.pushTempShaped v l) := by
  obtain ⟨fr0, e⟩ : ∃ fr0, s.env.getLast? = some fr0 := by
    cases h : s.env.getLast? with
    | none => exact absurd (List.getLast?_eq_none_iff.mp h) hne
    | some fr0 => exact ⟨fr0, rfl⟩
  have e2 : s.env[s.topIdx]? = some fr0 := by
    rw [List.getLast?_eq_getElem?] at e; simpa [topIdx] using e
  intro q x hq
  have hnl : (s.pushTempShaped v l).nextLoan = s.nextLoan := nextLoan_pushTempShaped s v l
  rw [hnl, positions_pushTempShaped]
  unfold pushTempShaped at hq
  dsimp only at hq
  rw [pushTemp_getLast, e] at hq
  simp only [Option.map_some] at hq
  change (if q = Pos.temp (s.pushTemp v).topIdx ((fr0.temps ++ [v]).length - 1) then some l else s.shape q) = some x at hq
  split at hq
  · rename_i hqT
    cases hq
    refine ⟨?_, hl⟩
    rw [hqT, pushTemp_topIdx, mem_positions]
    simp only [lookup, pushTemp, List.getElem?_modify, e2]
    simp
  · obtain ⟨h1, h2⟩ := hsa q x hq
    exact ⟨mem_positions_pushTemp s v h1, h2⟩

/-- **A move of a borrow out of its holder** (`readPlace`): the holder is taken and the borrow
parked again, so the live labels are the same and the invariant is kept. -/
theorem transfer_rinv {s : SState} (h : RInv L s) (l : Nat) (hl : s.Live l) (c : Sem) :
    RInv L ((s.takeLabel l).pushTempShaped (fun _ => c) l) := by
  obtain ⟨h1, h2, hsa⟩ := h
  have hsat := takeLabel_shapeAt hsa l
  have hne : (s.takeLabel l).env ≠ [] := by
    intro he
    obtain ⟨q, hq, _⟩ := (live_iff s l).mp hl
    have : q ∈ (s.takeLabel l).positions := by rw [takeLabel_positions]; exact hq
    rw [positions_eq, he] at this
    simp at this
  have hlive : ∀ y, ((s.takeLabel l).pushTempShaped (fun _ => c) l).Live y ↔ s.Live y := by
    intro y
    constructor
    · intro hy
      rcases live_pushTempShaped_new hsat hy with h' | rfl
      · exact takeLabel_live_rev h'
      · exact hl
    · intro hy
      by_cases e : y = l
      · subst e; exact live_pushTempShaped_self _ _ y hne
      · exact live_pushTempShaped_old (takeLabel_live hy e)
  have hv : ∀ q, ((s.takeLabel l).pushTempShaped (fun _ => c) l).valAt q = s.valAt q ∨
      ((s.takeLabel l).pushTempShaped (fun _ => c) l).valAt q = (fun _ => .moved) ∨
      ((s.takeLabel l).pushTempShaped (fun _ => c) l).valAt q = fun _ => c := by
    intro q
    rw [valAt_pushTempShaped]
    rcases valAt_pushTemp (s.takeLabel l) (fun _ => c) q with e | e
    · rw [e]
      rcases takeLabel_valAt s l q with e' | e'
      · exact .inl e'
      · exact .inr (.inl e')
    · exact .inr (.inr e)
  refine ⟨fun q => ?_, fun r x hr hs => ?_, fun q x hq => ?_⟩
  · rcases hv q with e | e | e
    · rw [e]; exact (h1 q).mono fun y hy => hy.imp_right (hlive y).mpr
    · rw [e]; exact FT.const _ _
    · rw [e]; exact FT.const _ _
  · rcases hv r with e | e | e
    · rw [e]
      -- an old position holding x holds it in s too
      have hr' : r ∈ (s.takeLabel l).positions ∨ r ∉ (s.takeLabel l).positions := Classical.em _
      rcases hr' with hr' | hr'
      · rw [pushTempShaped_shape_old _ _ l hr'] at hs
        have hs' := takeLabel_shape_some hs
        have hrs : r ∈ s.positions := by rw [← takeLabel_positions s l]; exact hr'
        exact (h2 r x hrs hs').mono fun y hy => by
          rcases hy with ⟨hL, hn⟩ | ⟨hy, hxy⟩
          · exact .inl ⟨hL, fun h' => hn ((hlive y).mp h')⟩
          · exact .inr ⟨(hlive y).mpr hy, hxy⟩
      · have hrs : r ∉ s.positions := by rw [← takeLabel_positions s l]; exact hr'
        rw [valAt_of_not_mem _ _ hrs]; exact FT.const _ _
    · rw [e]; exact FT.const _ _
    · rw [e]; exact FT.const _ _
  · have hnl : (s.takeLabel l).nextLoan = s.nextLoan := (shapeSub_takeLabel s l).2
    obtain ⟨q', _, hs'⟩ := (live_iff s l).mp hl
    exact pushTempShaped_shapeAt hsat hne _ l (by rw [hnl]; exact (hsa q' l hs').2) q x hq

end SState

end Ochr.Meaning

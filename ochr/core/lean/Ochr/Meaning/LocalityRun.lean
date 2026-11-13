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

/-! ## Pushing a binding -/

theorem lookup_pushBind_old (s : SState) (b : SBinding) (q : Pos) (h : (s.lookup q).isSome) :
    (s.pushBind b).lookup q = s.lookup q := by
  cases q with
  | temp f i =>
    simp only [lookup, pushBind, List.getElem?_modify]
    split <;> cases s.env[f]? <;> simp
  | bind f i =>
    simp only [lookup, pushBind, List.getElem?_modify] at h ⊢
    split
    · cases e : s.env[f]? with
      | none => simp
      | some fr =>
        rw [e] at h
        simp only [Option.bind_some, Option.isSome_map] at h
        have hi : i < fr.binds.length := by
          cases ei : fr.binds[i]? with
          | none => rw [ei] at h; cases h
          | some _ => exact (List.getElem?_eq_some_iff.mp ei).1
        simp [List.getElem?_append_left hi]
    · cases s.env[f]? <;> simp

theorem mem_positions_pushBind (s : SState) (b : SBinding) {q : Pos} (h : q ∈ s.positions) :
    q ∈ (s.pushBind b).positions := by
  rw [mem_positions] at h ⊢
  rw [lookup_pushBind_old s b q h]; exact h

theorem lookup_pushBind_new (s : SState) (b : SBinding) (q : Pos) (hq : (s.lookup q).isSome = false)
    {w : SVal} (e : (s.pushBind b).lookup q = some w) : w = b.val := by
  cases q with
  | temp f i =>
    exfalso
    simp only [lookup, pushBind, List.getElem?_modify] at e hq
    split at e
    · cases h : s.env[f]? with
      | none => rw [h] at e; simp at e
      | some fr =>
        rw [h] at e hq
        simp only [Functor.map, Option.map_some, Option.bind_some] at e hq
        rw [e] at hq; simp at hq
    · have e' : ((fun a => a) <$> s.env[f]?) = s.env[f]? := by cases s.env[f]? <;> rfl
      rw [e'] at e; rw [e] at hq; simp at hq
  | bind f i =>
    simp only [lookup, pushBind, List.getElem?_modify] at e hq
    split at e
    · cases h : s.env[f]? with
      | none => rw [h] at e; simp at e
      | some fr =>
        rw [h] at e hq
        simp only [Option.bind_some, Option.isSome_map, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at hq
        have hi : ¬ i < fr.binds.length := fun hi => by
          rw [List.getElem?_eq_getElem hi] at hq; cases hq
        simp only [Functor.map, Option.map_some, Option.bind_some, Option.map_eq_some_iff] at e
        obtain ⟨b', hb', rfl⟩ := e
        rw [List.getElem?_append_right (by omega)] at hb'
        cases hk : i - fr.binds.length with
        | zero => rw [hk] at hb'; simp at hb'; rw [hb']
        | succ k => rw [hk] at hb'; simp at hb'
    · have e' : ((fun a => a) <$> s.env[f]?) = s.env[f]? := by cases s.env[f]? <;> rfl
      rw [e'] at e; rw [e] at hq; simp at hq

theorem valAt_pushBind (s : SState) (b : SBinding) (q : Pos) :
    (s.pushBind b).valAt q = s.valAt q ∨ (s.pushBind b).valAt q = b.val := by
  by_cases hq : q ∈ s.positions
  · left
    rw [valAt_eq, valAt_eq, lookup_pushBind_old s b q ((mem_positions s q).mp hq)]
  · have hq' : (s.lookup q).isSome = false := by
      rw [mem_positions] at hq; cases h : (s.lookup q).isSome <;> simp_all
    rw [valAt_eq]
    cases e : (s.pushBind b).lookup q with
    | none => left; rw [valAt_of_not_mem s q hq]; rfl
    | some w => right; exact lookup_pushBind_new s b q hq' e

theorem live_pushBind {s : SState} (hsa : ShapeAt s) (b : SBinding) (y : Nat) :
    (s.pushBind b).Live y ↔ s.Live y := by
  rw [live_iff, live_iff]
  constructor
  · rintro ⟨q, _, hs⟩
    exact ⟨q, (hsa q y hs).1, hs⟩
  · rintro ⟨q, hq, hs⟩
    exact ⟨q, mem_positions_pushBind s b hq, hs⟩

/-- Pushing a binding with a constant meaning and no borrow keeps the invariant. -/
theorem pushBind_rinv {s : SState} (h : RInv L s) (b : SBinding) (c : Sem) (hb : b.val = fun _ => c) :
    RInv L (s.pushBind b) := by
  obtain ⟨h1, h2, hsa⟩ := h
  have hl := live_pushBind hsa b
  refine ⟨fun q => ?_, fun r x hr hs => ?_, fun q x hq => ?_⟩
  · rcases valAt_pushBind s b q with e | e
    · rw [e]; exact (h1 q).mono fun y hy => hy.imp_right (hl y).mpr
    · rw [e, hb]; exact FT.const _ _
  · have hs' : s.shape r = some x := hs
    have hrs := (hsa r x hs').1
    rcases valAt_pushBind s b r with e | e
    · rw [e]
      exact (h2 r x hrs hs').mono fun y hy => by
        rcases hy with ⟨hL, hn⟩ | ⟨hy, hxy⟩
        · exact .inl ⟨hL, fun h' => hn ((hl y).mp h')⟩
        · exact .inr ⟨(hl y).mpr hy, hxy⟩
    · rw [e, hb]; exact FT.const _ _
  · have hq' : s.shape q = some x := hq
    exact ⟨mem_positions_pushBind s b (hsa q x hq').1, (hsa q x hq').2⟩

/-- A binding pushed as the holder of `l`: the new position holds `l`, every other entry is kept. -/
theorem pushBindLabeled_shape (s : SState) (b : SBinding) (l : Nat) (fr : SFrame)
    (hfr : (s.pushBind b).env.getLast? = some fr) (q : Pos) :
    ({ s.pushBind b with shape := fun p => if p = .bind (s.pushBind b).topIdx (fr.binds.length - 1) then some l
        else (s.pushBind b).shape p } : SState).shape q
      = if q = .bind (s.pushBind b).topIdx (fr.binds.length - 1) then some l else s.shape q := rfl

theorem pushBind_getLast (s : SState) (b : SBinding) :
    (s.pushBind b).env.getLast? = (s.env.getLast?).map fun fr => { fr with binds := fr.binds ++ [b] } := by
  simp only [pushBind, topIdx]
  rw [List.getLast?_eq_getElem?, List.getLast?_eq_getElem?, List.length_modify, List.getElem?_modify]
  simp

theorem pushBind_topIdx (s : SState) (b : SBinding) : (s.pushBind b).topIdx = s.topIdx := by
  simp [pushBind, topIdx]

/-- **A binding pushed as a holder** (`pushBindShaped`): a constant meaning; its label `l` is taken
from its old holder (a move) or is fresh, above every held label (a borrow parameter). -/
theorem pushBindShaped_rinv {s : SState} (h : RInv L s) (b : SBinding) (c : Sem) (hb : b.val = fun _ => c)
    (hl : ∀ l, b.ty.label = some l → (s.Live l ∨ ∀ q x, s.shape q = some x → x < l) ∧ l < s.nextLoan) :
    RInv L (pushBindShaped s b) := by
  unfold pushBindShaped
  cases hlab : b.ty.label with
  | none => exact pushBind_rinv h b c hb
  | some l =>
    obtain ⟨hlo, hln⟩ := hl l hlab
    obtain ⟨h1, h2, hsa⟩ := h
    have hsat := takeLabel_shapeAt hsa l
    have htl : (s.takeLabel l).nextLoan = s.nextLoan := (shapeSub_takeLabel s l).2
    dsimp only
    rw [pushBind_getLast]
    cases e : (s.takeLabel l).env.getLast? with
    | none =>
      -- no frame: nothing is pushed, and there are no positions
      have hnil : (s.takeLabel l).env = [] := List.getLast?_eq_none_iff.mp e
      have hpos : ((s.takeLabel l).pushBind b).positions = [] := by
        rw [positions_eq]; simp [pushBind, hnil]
      simp only [Option.map_none]
      refine ⟨?_, ?_, ?_⟩
      · intro q
        rw [valAt_of_not_mem _ _ (by rw [hpos]; exact List.not_mem_nil)]; exact FT.const _ _
      · intro r x hr _
        rw [hpos] at hr; cases hr
      · intro q x hq
        obtain ⟨hq1, hq2⟩ := hsat q x hq
        rw [positions_eq, hnil] at hq1; simp at hq1
    | some fr0 =>
      simp only [Option.map_some]
      have e2 : (s.takeLabel l).env[(s.takeLabel l).topIdx]? = some fr0 := by
        rw [List.getLast?_eq_getElem?] at e; simpa [topIdx] using e
      -- the new position
      have hnewpos : Pos.bind ((s.takeLabel l).pushBind b).topIdx ((fr0.binds ++ [b]).length - 1)
          ∈ ((s.takeLabel l).pushBind b).positions := by
        rw [pushBind_topIdx, mem_positions]
        simp only [lookup, pushBind, List.getElem?_modify, e2]
        simp
      have hnewold : Pos.bind ((s.takeLabel l).pushBind b).topIdx ((fr0.binds ++ [b]).length - 1)
          ∉ (s.takeLabel l).positions := by
        rw [pushBind_topIdx, mem_positions]
        simp [lookup, e2]
      generalize hN : Pos.bind ((s.takeLabel l).pushBind b).topIdx ((fr0.binds ++ [b]).length - 1) = N at hnewpos hnewold
      have hshape : ∀ q, ({ (s.takeLabel l).pushBind b with
          shape := fun p => if p = N then some l else ((s.takeLabel l).pushBind b).shape p } : SState).shape q
          = if q = N then some l else (s.takeLabel l).shape q := fun q => rfl
      generalize hF : ({ (s.takeLabel l).pushBind b with
          shape := fun p => if p = N then some l else ((s.takeLabel l).pushBind b).shape p } : SState) = F
        at hshape
      have hposF : F.positions = ((s.takeLabel l).pushBind b).positions := by rw [← hF]; rfl
      have hvalF : ∀ q, F.valAt q = ((s.takeLabel l).pushBind b).valAt q := by intro q; rw [← hF]; rfl
      have hnlF : F.nextLoan = s.nextLoan := by rw [← hF, ← htl]; rfl
      have hliveF : ∀ y, F.Live y ↔ s.Live y ∨ y = l := by
        intro y
        rw [live_iff]
        constructor
        · rintro ⟨q, _, hs⟩
          rw [hshape] at hs
          split at hs
          · cases hs; exact .inr rfl
          · exact .inl (takeLabel_live_rev ((live_iff _ y).mpr ⟨q, (hsat q y hs).1, hs⟩))
        · intro hy
          by_cases hyl : y = l
          · subst hyl; exact ⟨N, by rw [hposF]; exact hnewpos, by rw [hshape]; simp⟩
          · have hyt := takeLabel_live (hy.resolve_right hyl) hyl
            obtain ⟨q, hq, hs⟩ := (live_iff _ y).mp hyt
            refine ⟨q, by rw [hposF]; exact mem_positions_pushBind _ b hq, ?_⟩
            have hqN : q ≠ N := by intro e'; rw [e'] at hq; exact hnewold hq
            rw [hshape, if_neg hqN]; exact hs
      have hv : ∀ q, F.valAt q = s.valAt q ∨ F.valAt q = (fun _ => .moved) ∨ F.valAt q = fun _ => c := by
        intro q
        rw [hvalF]
        rcases valAt_pushBind (s.takeLabel l) b q with e | e
        · rw [e]
          rcases takeLabel_valAt s l q with e' | e'
          · exact .inl e'
          · exact .inr (.inl e')
        · rw [e, hb]; exact .inr (.inr rfl)
      refine ⟨fun q => ?_, fun r x hr hs => ?_, fun q x hq => ?_⟩
      · rcases hv q with e | e | e
        · rw [e]; exact (h1 q).mono fun y hy => hy.imp_right fun h' => (hliveF y).mpr (.inl h')
        · rw [e]; exact FT.const _ _
        · rw [e]; exact FT.const _ _
      · rw [hshape] at hs
        split at hs
        · rcases hv r with e | e | e
          · -- r is the new position: not a position of s, so its old meaning is constant
            rename_i hrN
            have hrs : r ∉ s.positions := by
              rw [← takeLabel_positions s l, hrN]; exact hnewold
            rw [e, valAt_of_not_mem _ _ hrs]; exact FT.const _ _
          · rw [e]; exact FT.const _ _
          · rw [e]; exact FT.const _ _
        · have hs' := takeLabel_shape_some hs
          have hrs : r ∈ s.positions := by rw [← takeLabel_positions s l]; exact (hsat r x hs).1
          rcases hv r with e | e | e
          · rw [e]
            exact (h2 r x hrs hs').mono fun y hy => by
              rcases hy with ⟨hL, hn⟩ | ⟨hy, hxy⟩
              · by_cases hF' : F.Live y
                · rcases (hliveF y).mp hF' with h' | rfl
                  · exact absurd h' hn
                  · rcases hlo with hlv | hfresh
                    · exact absurd hlv hn
                    · exact .inr ⟨hF', hfresh r x hs'⟩
                · exact .inl ⟨hL, hF'⟩
              · exact .inr ⟨(hliveF y).mpr (.inl hy), hxy⟩
          · rw [e]; exact FT.const _ _
          · rw [e]; exact FT.const _ _
      · rw [hshape] at hq
        rw [hposF, hnlF]
        split at hq
        · rename_i hqN
          cases hq; exact ⟨by rw [hqN]; exact hnewpos, hln⟩
        · obtain ⟨hq1, hq2⟩ := hsat q x hq
          exact ⟨mem_positions_pushBind _ b hq1, by rw [← htl]; exact hq2⟩

/-! ## Dropping the last binding -/

/-- The position `dropLast` removes. -/
def dropped (s : SState) : Option Pos := match s.env.getLast? with
  | some fr => some (.bind s.topIdx (fr.binds.length - 1))
  | none => none

theorem dropLast_shape (s : SState) (q : Pos) :
    s.dropLast.shape q = if some q = s.dropped then none else s.shape q := rfl

theorem lookup_dropLast (s : SState) (q : Pos) (hq : some q ≠ s.dropped) :
    s.dropLast.lookup q = s.lookup q := by
  cases q with
  | temp f i =>
    simp only [lookup, dropLast, List.getElem?_modify]
    split <;> cases s.env[f]? <;> simp
  | bind f i =>
    simp only [lookup, dropLast, List.getElem?_modify]
    split
    · rename_i hf
      cases e : s.env[f]? with
      | none => simp
      | some fr =>
        simp only [Functor.map, Option.map_some, Option.bind_some]
        have hlast : s.env.getLast? = some fr := by
          rw [List.getLast?_eq_getElem?]; rw [← hf] at e; simpa [topIdx] using e
        have hi : i ≠ fr.binds.length - 1 := by
          intro hi; apply hq; simp [dropped, hlast, hf, hi]
        by_cases hlt : i < fr.binds.length - 1
        · rw [List.getElem?_dropLast]; simp [hlt]
        · have h1 : fr.binds.dropLast[i]? = none := List.getElem?_eq_none (by simp; omega)
          have h2 : fr.binds[i]? = none := List.getElem?_eq_none (by omega)
          rw [h1, h2]
    · cases s.env[f]? <;> simp

theorem mem_positions_dropLast {s : SState} {q : Pos} (h : q ∈ s.dropLast.positions) :
    q ∈ s.positions ∧ some q ≠ s.dropped := by
  have hq : some q ≠ s.dropped := by
    intro e
    rw [mem_positions] at h
    unfold dropped at e
    cases el : s.env.getLast? with
    | none => rw [el] at e; cases e
    | some fr =>
      rw [el] at e
      simp only [Option.some.injEq] at e
      subst e
      have e2 : s.env[s.topIdx]? = some fr := by
        rw [List.getLast?_eq_getElem?] at el; simpa [topIdx] using el
      simp only [lookup, dropLast, List.getElem?_modify, e2] at h
      simp at h
  exact ⟨by rw [mem_positions, ← lookup_dropLast s q hq]; rw [mem_positions] at h; exact h, hq⟩

theorem mem_positions_dropLast' {s : SState} {q : Pos} (h : q ∈ s.positions) (hq : some q ≠ s.dropped) :
    q ∈ s.dropLast.positions := by
  rw [mem_positions] at h ⊢; rw [lookup_dropLast s q hq]; exact h

theorem valAt_dropLast (s : SState) (q : Pos) (hq : some q ≠ s.dropped) : s.dropLast.valAt q = s.valAt q := by
  rw [valAt_eq, valAt_eq, lookup_dropLast s q hq]

/-- **Dropping the last binding** keeps the invariant when no meaning reads the label it may hold
(the `let`'s drop ends that label first). -/
theorem dropLast_rinv {s : SState} (h : RInv L s)
    (hind : ∀ r x, s.dropped = some r → s.shape r = some x → ∀ p, Indep x (s.valAt p)) :
    RInv L s.dropLast := by
  obtain ⟨h1, h2, hsa⟩ := h
  have hlive : ∀ y, s.dropLast.Live y → s.Live y := by
    intro y hy
    rw [live_iff] at hy ⊢
    obtain ⟨q, hq, hs⟩ := hy
    obtain ⟨hq1, hq2⟩ := mem_positions_dropLast hq
    rw [dropLast_shape, if_neg hq2] at hs
    exact ⟨q, hq1, hs⟩
  -- a live label of s not live after the drop was held at the dropped position, so nobody reads it
  have hgone : ∀ y, s.Live y → ¬ s.dropLast.Live y → ∀ p, Indep y (s.valAt p) := by
    intro y hy hn p
    obtain ⟨q, hq, hs⟩ := (live_iff s y).mp hy
    by_cases hqd : some q = s.dropped
    · exact hind q y hqd.symm hs p
    · exact absurd ((live_iff _ y).mpr ⟨q, mem_positions_dropLast' hq hqd, by rw [dropLast_shape, if_neg hqd]; exact hs⟩) hn
  -- the labels the drop makes non-live are finitely many and unread: remove them
  have hD : ∀ (f : SVal) (S S' : Nat → Prop), FT S f →
      (∀ y, s.Live y → ¬ s.dropLast.Live y → Indep y f) →
      (∀ y, S y → S' y ∨ (s.Live y ∧ ¬ s.dropLast.Live y)) → FT S' f := by
    intro f S S' hf hind' hS
    open Classical in
    exact FT.removeList (S := S') (s.liveLabels.filter fun y => decide (¬ s.dropLast.Live y))
      (hf.mono fun y hy => by
        rcases hS y hy with h' | ⟨hl, hn⟩
        · exact .inl h'
        · exact .inr (List.mem_filter.mpr ⟨hl, by simpa using hn⟩))
      (fun y hy => by
        obtain ⟨hl, hn⟩ := List.mem_filter.mp hy
        exact hind' y hl (by simpa using hn))
  refine ⟨fun q => ?_, fun r x hr hs => ?_, fun q x hq => ?_⟩
  · by_cases hq : q ∈ s.dropLast.positions
    · rw [valAt_dropLast s q (mem_positions_dropLast hq).2]
      exact hD _ _ _ (h1 q) (fun y hl hn => hgone y hl hn q) fun y hy => by
        rcases hy with hL | hl
        · exact .inl (.inl hL)
        · by_cases hn : s.dropLast.Live y
          · exact .inl (.inr hn)
          · exact .inr ⟨hl, hn⟩
    · rw [valAt_of_not_mem _ _ hq]; exact FT.const _ _
  · obtain ⟨hr1, hr2⟩ := mem_positions_dropLast hr
    rw [dropLast_shape, if_neg hr2] at hs
    rw [valAt_dropLast s r hr2]
    exact hD _ _ _ (h2 r x hr1 hs) (fun y hl hn => hgone y hl hn r) fun y hy => by
      rcases hy with ⟨hL, hn⟩ | ⟨hy, hxy⟩
      · exact .inl (.inl ⟨hL, fun h' => hn (hlive y h')⟩)
      · by_cases hn : s.dropLast.Live y
        · exact .inl (.inr ⟨hn, hxy⟩)
        · exact .inr ⟨hy, hn⟩
  · rw [dropLast_shape] at hq
    split at hq
    · cases hq
    · rename_i hqd
      obtain ⟨hq1, hq2⟩ := hsa q x hq
      exact ⟨mem_positions_dropLast' hq1 hqd, hq2⟩

/-! ## A write that reads a fresh label, then the label parked (`borrowPlace`, a cell) -/

/-- **A write that reads a fresh label `l`, then `l` parked**: `borrowPlace` writes, at the lent
position, the final content of `l` into its old meaning, then parks the borrow. The new meaning
reads what the old did and `l`; `l` is above every held label, so holders stay ordered. -/
theorem writeFresh_park_rinv {s : SState} (h : RInv L s) (p : Pos) (v : SVal) (l : Nat) (c : Sem)
    (hne : s.env ≠ []) (hfresh : ∀ q x, s.shape q = some x → x < l) (hln : l < s.nextLoan)
    (hv1 : FT (fun y => L y ∨ s.Live y ∨ y = l) v)
    (hv2 : ∀ x, s.shape p = some x → FT (fun y => (L y ∧ ¬ s.Live y) ∨ (s.Live y ∧ x < y) ∨ y = l) v) :
    RInv L ((s.setAt p v).pushTempShaped (fun _ => c) l) := by
  obtain ⟨h1, h2, hsa⟩ := h
  have hsa₁ : ShapeAt (s.setAt p v) := fun q x hq => by
    rw [shape_setAt'] at hq
    rw [positions_setAt, nextLoan_setAt']; exact hsa q x hq
  have hne₁ : (s.setAt p v).env ≠ [] := by cases p <;> simpa [setAt] using hne
  have hl₁ : ∀ y, (s.setAt p v).Live y ↔ s.Live y := live_setAt s p v
  -- the live labels after parking
  have hlive : ∀ y, ((s.setAt p v).pushTempShaped (fun _ => c) l).Live y ↔ s.Live y ∨ y = l := by
    intro y
    constructor
    · intro hy
      rcases live_pushTempShaped_new hsa₁ hy with h' | rfl
      · exact .inl ((hl₁ y).mp h')
      · exact .inr rfl
    · rintro (hy | rfl)
      · exact live_pushTempShaped_old ((hl₁ y).mpr hy)
      · exact live_pushTempShaped_self _ _ _ hne₁
  have hv : ∀ q, ((s.setAt p v).pushTempShaped (fun _ => c) l).valAt q = s.valAt q ∨
      (q = p ∧ ((s.setAt p v).pushTempShaped (fun _ => c) l).valAt q = v) ∨
      ((s.setAt p v).pushTempShaped (fun _ => c) l).valAt q = fun _ => c := by
    intro q
    rw [valAt_pushTempShaped]
    rcases valAt_pushTemp (s.setAt p v) (fun _ => c) q with e | e
    · rw [e]
      by_cases hpq : p = q
      · subst hpq
        rcases valAt_setAt s p v p with e' | e'
        · exact .inl e'
        · exact .inr (.inl ⟨rfl, e'⟩)
      · exact .inl (valAt_setAt_ne s p v q hpq)
    · exact .inr (.inr e)
  refine ⟨fun q => ?_, fun r x hr hs => ?_, fun q x hq => ?_⟩
  · rcases hv q with e | ⟨_, e⟩ | e
    · rw [e]; exact (h1 q).mono fun y hy => hy.imp_right fun h' => (hlive y).mpr (.inl h')
    · rw [e]; exact hv1.mono fun y hy => by
        rcases hy with hL | hy | rfl
        · exact .inl hL
        · exact .inr ((hlive y).mpr (.inl hy))
        · exact .inr ((hlive y).mpr (.inr rfl))
    · rw [e]; exact FT.const _ _
  · by_cases hold : r ∈ (s.setAt p v).positions
    · rw [pushTempShaped_shape_old _ _ l hold, shape_setAt'] at hs
      have hrs : r ∈ s.positions := by rw [← positions_setAt s p v]; exact hold
      have hxl : x < l := hfresh r x hs
      have hS : ∀ y, ((L y ∧ ¬ s.Live y) ∨ (s.Live y ∧ x < y) ∨ y = l) →
          (L y ∧ ¬ ((s.setAt p v).pushTempShaped (fun _ => c) l).Live y) ∨
          (((s.setAt p v).pushTempShaped (fun _ => c) l).Live y ∧ x < y) := by
        intro y hy
        rcases hy with ⟨hL, hn⟩ | ⟨hy, hxy⟩ | rfl
        · by_cases hF : ((s.setAt p v).pushTempShaped (fun _ => c) l).Live y
          · rcases (hlive y).mp hF with h' | rfl
            · exact absurd h' hn
            · exact .inr ⟨hF, hxl⟩
          · exact .inl ⟨hL, hF⟩
        · exact .inr ⟨(hlive y).mpr (.inl hy), hxy⟩
        · exact .inr ⟨(hlive y).mpr (.inr rfl), hxl⟩
      rcases hv r with e | ⟨hrp, e⟩ | e
      · rw [e]; exact (h2 r x hrs hs).mono fun y hy => hS y (by
          rcases hy with h' | h'
          · exact .inl h'
          · exact .inr (.inl h'))
      · rw [e]; subst hrp
        exact (hv2 x hs).mono fun y hy => hS y hy
      · rw [e]; exact FT.const _ _
    · rcases hv r with e | ⟨hrp, e⟩ | e
      · have hrs : r ∉ s.positions := by rw [← positions_setAt s p v]; exact hold
        rw [e, valAt_of_not_mem _ _ hrs]; exact FT.const _ _
      · -- r = p is not a position: the write did nothing there
        subst hrp
        have hrs : r ∉ s.positions := by rw [← positions_setAt s r v]; exact hold
        rw [valAt_pushTempShaped]
        rcases valAt_pushTemp (s.setAt r v) (fun _ => c) r with e' | e'
        · rw [e']
          have : (s.setAt r v).valAt r = fun _ => .err := valAt_of_not_mem _ _ hold
          rw [this]; exact FT.const _ _
        · rw [e']; exact FT.const _ _
      · rw [e]; exact FT.const _ _
  · exact pushTempShaped_shapeAt hsa₁ hne₁ _ l (by rw [nextLoan_setAt']; exact hln) q x hq

end SState

end Ochr.Meaning

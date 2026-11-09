import Ochr.Meaning.Run

/-!
# The reference run's borrow primitives lose only information (milestone 3's monotonicity)

The step lemmas of milestone 3 compare the checker's state with the reference run's, and the
reference run's own borrow primitives are steps that may only *narrow* what a state means:
[End] (`SState.endLabel`) fixes a final content and forgets the holder, [Access]
(`SState.access`) is a fold of [End]s, and D84's drop at the join (`joinDrop`) sets places to
`⊥`. This file proves the first two `Below` their input, and the third when it drops only
roots, at the level `State.lean` states `Mean.semEnd_below`: the `Mean` a semantic state forgets
its types to (`SState.toMean`).

* `SState.endLabel_below`: [End] loses only information.
* `SState.access_below`: so does [Access], a fold of [End]s (`foldl_endLabel_below`).
* `Mean.semEnd_comm`, `SState.endLabel_comm`: two [End]s commute when one holder's meaning does
  not depend on the other's label, which (WF3)'s acyclicity guarantees for every pair
  (`SState.SWF3`, its semantic form, `endLabel_comm_of_SWF3`); plain equality, not only `Below`
  both ways. Without the hypothesis it is false (`Mean.semEnd_comm_cycle`).
* `joinDrop_below`: the drop at the join loses only information *when every dropped place is a
  root* (its path is `*`s only). With a field in the path it is false
  (`JoinDropCounterexample.joinDrop_not_below`): a partial move turns a whole value into an
  untyped tuple, which `⊑` puts below no element of a carrier (`Sem.updAt_field_not_le`).

Analogues on the toy model: `Ochr/Model/State2.lean` (`semEnd_below`, `endL_below`,
`access_below`, `drop_below`).
-/

namespace Ochr.Meaning

open Classical

/-! ## `mapVals`, `setAt` and the positions -/

namespace SState

/-- The binding at a position, if any. -/
def bindAt? (s : SState) (f i : Nat) : Option SBinding := s.env[f]?.bind (·.binds[i]?)

/-- The temporary at a position, if any. -/
def tempAt? (s : SState) (f i : Nat) : Option SVal := s.env[f]?.bind (·.temps[i]?)

/-- A position of the state: a binding or a temporary that exists. -/
def Valid (s : SState) : Pos → Prop
  | .bind f i => (s.bindAt? f i).isSome
  | .temp f i => (s.tempAt? f i).isSome

theorem valAt_of_not_valid (s : SState) (p : Pos) (h : ¬ s.Valid p) : s.valAt p = fun _ => .err := by
  cases p with
  | bind f i =>
    simp only [Valid, bindAt?, Option.isSome_iff_ne_none, ne_eq, Decidable.not_not] at h
    simp only [valAt, h]
  | temp f i =>
    simp only [Valid, tempAt?, Option.isSome_iff_ne_none, ne_eq, Decidable.not_not] at h
    simp only [valAt, h]

theorem bindAt?_mapVals (s : SState) (g : Pos → SVal → SVal) (f i : Nat) :
    (s.mapVals g).bindAt? f i = (s.bindAt? f i).map fun b => { b with val := g (.bind f i) b.val } := by
  simp only [bindAt?, mapVals, List.getElem?_map, List.getElem?_zipIdx]
  cases s.env[f]? with
  | none => rfl
  | some fr => simp [Function.comp_def, List.getElem?_map, List.getElem?_zipIdx]

theorem tempAt?_mapVals (s : SState) (g : Pos → SVal → SVal) (f i : Nat) :
    (s.mapVals g).tempAt? f i = (s.tempAt? f i).map (g (.temp f i)) := by
  simp only [tempAt?, mapVals, List.getElem?_map, List.getElem?_zipIdx]
  cases s.env[f]? with
  | none => rfl
  | some fr => simp [Function.comp_def, List.getElem?_map, List.getElem?_zipIdx]

theorem valid_mapVals (s : SState) (g : Pos → SVal → SVal) (p : Pos) :
    (s.mapVals g).Valid p ↔ s.Valid p := by
  cases p <;> simp [Valid, bindAt?_mapVals, tempAt?_mapVals]

/-- `mapVals` rewrites the meaning at every position that exists, and nothing else. -/
theorem valAt_mapVals (s : SState) (g : Pos → SVal → SVal) (p : Pos) :
    (s.mapVals g).valAt p = if s.Valid p then g p (s.valAt p) else fun _ => .err := by
  cases p with
  | bind f i =>
    have e : ∀ t : SState, t.valAt (.bind f i) =
        match t.bindAt? f i with | some b => b.val | none => fun _ => .err := fun _ => rfl
    rw [e, e, bindAt?_mapVals]
    by_cases hv : s.Valid (.bind f i)
    · rw [if_pos hv]
      obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp hv
      rw [hb]; rfl
    · rw [if_neg hv]
      have hn : s.bindAt? f i = none := by simpa [Valid] using hv
      rw [hn]; rfl
  | temp f i =>
    have e : ∀ t : SState, t.valAt (.temp f i) =
        match t.tempAt? f i with | some v => v | none => fun _ => .err := fun _ => rfl
    rw [e, e, tempAt?_mapVals]
    by_cases hv : s.Valid (.temp f i)
    · rw [if_pos hv]
      obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp hv
      rw [hb]; rfl
    · rw [if_neg hv]
      have hn : s.tempAt? f i = none := by simpa [Valid] using hv
      rw [hn]; rfl

@[simp] theorem valid_withShape (s : SState) (sh : Pos → Option Nat) (p : Pos) :
    ({ s with shape := sh } : SState).Valid p = s.Valid p := rfl

@[simp] theorem valAt_withShape (s : SState) (sh : Pos → Option Nat) (p : Pos) :
    ({ s with shape := sh } : SState).valAt p = s.valAt p := rfl

@[simp] theorem positions_withShape (s : SState) (sh : Pos → Option Nat) :
    ({ s with shape := sh } : SState).positions = s.positions := rfl

theorem positions_mapVals (s : SState) (g : Pos → SVal → SVal) : (s.mapVals g).positions = s.positions := by
  simp [positions, mapVals, Std.Legacy.Range.forIn'_eq_forIn'_range',
    Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]

/-- [End] at a label with a holder `r`, unfolded. -/
theorem endLabel_of_find (s : SState) (l : Nat) (r : Pos)
    (h : s.positions.find? (fun p => decide (s.shape p = some l)) = some r) :
    s.endLabel l = ({ s with shape := (s.toMean.semEnd r l).shape }).mapVals
      fun p _ => ((s.toMean.semEnd r l).val · p) := by
  unfold endLabel; rw [h]

/-- [End] at a label held nowhere does nothing. -/
theorem endLabel_of_find_none (s : SState) (l : Nat)
    (h : s.positions.find? (fun p => decide (s.shape p = some l)) = none) : s.endLabel l = s := by
  unfold endLabel; rw [h]

/-- After [End] at `l` with holder `r`, every position that exists, and every position but `r`,
means what `Mean.semEnd` says. (`endLabel` finds its holder among the state's positions, so `r`
exists too, but nothing here needs that.) -/
theorem endLabel_val (s : SState) (l : Nat) (r : Pos)
    (h : s.positions.find? (fun p => decide (s.shape p = some l)) = some r)
    (φ : Future) (q : Pos) (hq : s.Valid q ∨ q ≠ r) :
    (s.endLabel l).valAt q φ = (s.toMean.semEnd r l).val φ q := by
  rw [endLabel_of_find s l r h, valAt_mapVals, valid_withShape]
  by_cases hv : s.Valid q
  · rw [if_pos hv]
  · rw [if_neg hv]
    have hr : q ≠ r := hq.resolve_left hv
    simp only [Mean.semEnd, toMean, if_neg hr, valAt_of_not_valid s q hv]

theorem endLabel_shape (s : SState) (l : Nat) (r : Pos)
    (h : s.positions.find? (fun p => decide (s.shape p = some l)) = some r) :
    (s.endLabel l).shape = fun p => if p = r then none else s.shape p := by
  rw [endLabel_of_find s l r h]; rfl

/-- **[End] loses only information** (milestone 3: the step lemma for the checker's `endBorrow`
compares it with this; every lemma whose reference step ends a borrow, [Access], [Drop] and
`popFrame` among them, composes it). The semantic state after ending `l` is `Below` the one
before: it is `Mean.semEnd_below` at the holder, read back through `mapVals`. A label held
nowhere is inert. -/
theorem endLabel_below (s : SState) (l : Nat) : Below (s.endLabel l).toMean s.toMean := by
  cases h : s.positions.find? (fun p => decide (s.shape p = some l)) with
  | none => rw [endLabel_of_find_none s l h]; exact Below.refl _
  | some r =>
    intro φ'
    refine ⟨φ'.upd l (s.valAt r φ'), fun p => ?_, fun p l' hp => ?_⟩
    · show (s.endLabel l).valAt p φ' ⊑ s.valAt p _
      by_cases hv : s.Valid p
      · rw [endLabel_val s l r h φ' p (.inl hv)]
        simp only [Mean.semEnd, toMean]
        split
        · exact .moved _
        · exact Sem.le_refl _
      · have e : (s.endLabel l).valAt p = fun _ => .err := by
          rw [endLabel_of_find s l r h, valAt_mapVals, valid_withShape, if_neg hv]
        rw [e, valAt_of_not_valid s p hv]
        exact Sem.le_refl _
    · change (s.endLabel l).shape p = some l' at hp
      rw [endLabel_shape s l r h] at hp
      by_cases hpr : p = r
      · simp [hpr] at hp
      · exact (by simpa [hpr] using hp : s.shape p = some l')

/-- A fold of [End]s loses only information (the iterated form of `endLabel_below`; also what
`observation`'s "end every live borrow" is). -/
theorem foldl_endLabel_below (ls : List Nat) (s : SState) : Below (ls.foldl endLabel s).toMean s.toMean := by
  induction ls generalizing s with
  | nil => exact Below.refl _
  | cons l ls ih => exact (ih (s.endLabel l)).trans (endLabel_below s l)

/-- **[Access] loses only information** (milestone 3: `Steps/Borrow.lean`'s three [Access] lemmas,
and every reference step that reads, borrows or matches a place through `contentOf`). The
reference's access is a fold of [End]s, iterated, so it is `Below` its input by
`endLabel_below`; which labels it picks does not matter here. -/
theorem access_below (s : SState) (p : Pos) : Below (s.access p).toMean s.toMean := by
  have iter : ∀ (ns : List Nat) (t : SState), Below (ns.foldl (fun t _ =>
      (t.liveLabels.filter fun l => decide (t.dependsOn p l)).foldl endLabel t) t).toMean t.toMean := by
    intro ns
    induction ns with
    | nil => intro t; exact Below.refl _
    | cons _ ns ih => intro t; exact (ih _).trans (foldl_endLabel_below _ t)
  exact iter _ s

end SState

/-! ## Two [End]s commute under (WF3) -/

theorem Future.upd_comm (φ : Future) {l₁ l₂ : Nat} (h : l₁ ≠ l₂) (a b : Sem) :
    (φ.upd l₁ a).upd l₂ b = (φ.upd l₂ b).upd l₁ a := by
  funext l
  by_cases h₁ : l = l₁ <;> by_cases h₂ : l = l₂ <;> simp_all [Future.upd]

theorem Mean.not_dependsOn {m : Mean} {p : Pos} {l : Nat} (h : ¬ m.dependsOn p l) (φ : Future) (s : Sem) :
    m.val (φ.upd l s) p = m.val φ p := by
  exact Classical.byContradiction fun hne => h ⟨φ, s, Ne.symm hne⟩

/-- **Two ends commute** when one holder's meaning does not depend on the other's label (the
form (WF3) gives, `SState.endLabel_comm`). Plain equality of meanings, not only `Below` both ways:
if `r₁`'s content does not read `l₂`, ending `l₁` first fixes it to `r₁`'s content and ending `l₂`
then fixes it to `r₂`'s content at that, which is what ending `l₂` first and `l₁` second gives
too. Without the hypothesis it is false (`semEnd_comm_cycle`). Milestone 3: the step lemma for
[Access] (the checker ends every label whose loan occurs in the content, in its own order; the
reference ends only those the meaning depends on, in label order). -/
theorem Mean.semEnd_comm (m : Mean) {r₁ r₂ : Pos} {l₁ l₂ : Nat} (hr : r₁ ≠ r₂) (hl : l₁ ≠ l₂)
    (hind : ¬ m.dependsOn r₁ l₂ ∨ ¬ m.dependsOn r₂ l₁) :
    (m.semEnd r₁ l₁).semEnd r₂ l₂ = (m.semEnd r₂ l₂).semEnd r₁ l₁ := by
  simp only [Mean.semEnd, Mean.mk.injEq, true_and]
  refine ⟨funext fun φ => funext fun p => ?_, funext fun p => ?_⟩
  · by_cases hp₁ : p = r₁
    · subst hp₁; simp [hr]
    by_cases hp₂ : p = r₂
    · subst hp₂; simp [hr.symm]
    simp only [hp₁, hp₂, hr.symm, hr, if_false]
    rcases hind with h | h
    · rw [Mean.not_dependsOn h, Mean.not_dependsOn h, Future.upd_comm φ hl.symm]
    · rw [Mean.not_dependsOn h, Mean.not_dependsOn h, Future.upd_comm φ hl]
  · by_cases hp₁ : p = r₁ <;> by_cases hp₂ : p = r₂ <;> simp [hp₁, hp₂]

/-- **Without (WF3) two ends need not commute.** Borrow `0` held at `r₁` holds a loan of `1`,
borrow `1` held at `r₂` a loan of `0` (a cycle `loanUnder` forbids), and a third position reads
both loans. Ending `0` first fixes it to `φ 1`, so the third position reads `(φ 1, φ 1)`; ending
`1` first gives `(φ 0, φ 0)`. -/
theorem Mean.semEnd_comm_cycle : ∃ (m : Mean) (r₁ r₂ : Pos) (l₁ l₂ : Nat), r₁ ≠ r₂ ∧ l₁ ≠ l₂ ∧
    m.dependsOn r₁ l₂ ∧ m.dependsOn r₂ l₁ ∧
    (m.semEnd r₁ l₁).semEnd r₂ l₂ ≠ (m.semEnd r₂ l₂).semEnd r₁ l₁ := by
  let m : Mean := ⟨[], fun φ p => if p = .bind 0 0 then φ 1 else if p = .bind 0 1 then φ 0
      else .ctor "x" 0 [φ 0, φ 1], fun _ => none⟩
  refine ⟨m, .bind 0 0, .bind 0 1, 0, 1, by decide, by decide,
    ⟨fun _ => .moved, .proof, ?_⟩, ⟨fun _ => .moved, .proof, ?_⟩, fun h => ?_⟩
  · simp [m, Future.upd]
  · simp [m, Future.upd]
  · have := congrArg (fun m : Mean => m.val (fun l => if l = 0 then .proof else .moved) (.bind 0 2)) h
    simp [m, Mean.semEnd, Future.upd] at this

/-- `semEnd` at `p` reads its input only at `p` and at the holder. -/
theorem Mean.semEnd_val_congr {m m' : Mean} {r p : Pos} (l : Nat)
    (hp : ∀ φ, m.val φ p = m'.val φ p) (hr : ∀ φ, m.val φ r = m'.val φ r) (φ : Future) :
    (m.semEnd r l).val φ p = (m'.semEnd r l).val φ p := by
  simp only [Mean.semEnd]
  rw [hr, hp]

namespace SState

private theorem zipIdx_zipIdx {α : Type _} (l : List α) :
    l.zipIdx.zipIdx = l.zipIdx.map fun x => (x, x.2) := by
  apply List.ext_getElem <;> simp [List.getElem_zipIdx]

theorem mapVals_mapVals (s : SState) (g h : Pos → SVal → SVal) :
    (s.mapVals g).mapVals h = s.mapVals fun p v => h p (g p v) := by
  simp [mapVals, List.zipIdx_map, List.map_map, Function.comp_def, zipIdx_zipIdx]

theorem mapVals_congr (s : SState) {g g' : Pos → SVal → SVal}
    (h : ∀ p, s.Valid p → g p (s.valAt p) = g' p (s.valAt p)) : s.mapVals g = s.mapVals g' := by
  unfold mapVals
  congr 1
  apply List.map_congr_left
  rintro ⟨fr, fi⟩ hmem
  have hf : s.env[fi]? = some fr := List.mem_zipIdx_iff_getElem?.mp hmem
  dsimp only
  congr 1
  · apply List.map_congr_left
    rintro ⟨b, i⟩ hb
    have hbi : fr.binds[i]? = some b := List.mem_zipIdx_iff_getElem?.mp hb
    have hv : s.Valid (.bind fi i) := by simp [Valid, bindAt?, hf, hbi]
    have hval : s.valAt (.bind fi i) = b.val := by simp [valAt, hf, hbi]
    have := h _ hv
    rw [hval] at this
    simp only [this]
  · apply List.map_congr_left
    rintro ⟨v, i⟩ hvm
    have hti : fr.temps[i]? = some v := List.mem_zipIdx_iff_getElem?.mp hvm
    have hv : s.Valid (.temp fi i) := by simp [Valid, tempAt?, hf, hti]
    have hval : s.valAt (.temp fi i) = v := by simp [valAt, hf, hti]
    have := h _ hv
    rw [hval] at this
    simp only [this]

theorem shape_of_find {s : SState} {l : Nat} {r : Pos}
    (h : s.positions.find? (fun p => decide (s.shape p = some l)) = some r) : s.shape r = some l := by
  simpa using List.find?_some h

/-- Ending `l` does not move the holder of another label `l'`. -/
theorem find_endLabel (s : SState) {l l' : Nat} (hl : l ≠ l') :
    (s.endLabel l).positions.find? (fun p => decide ((s.endLabel l).shape p = some l')) =
      s.positions.find? (fun p => decide (s.shape p = some l')) := by
  cases h : s.positions.find? (fun p => decide (s.shape p = some l)) with
  | none => rw [endLabel_of_find_none s l h]
  | some r =>
    have hr := shape_of_find h
    rw [endLabel_shape s l r h, endLabel_of_find s l r h, positions_mapVals, positions_withShape]
    congr 1
    funext p
    by_cases hp : p = r
    · subst hp; simp [hr, hl]
    · simp [hp]

/-- Two [End]s in a row, unfolded: the state means `semEnd` twice. -/
theorem endLabel_endLabel (s : SState) {l₁ l₂ : Nat} {r₁ r₂ : Pos}
    (h₁ : s.positions.find? (fun p => decide (s.shape p = some l₁)) = some r₁)
    (h₂ : (s.endLabel l₁).positions.find? (fun p => decide ((s.endLabel l₁).shape p = some l₂)) = some r₂)
    (hr : r₂ ≠ r₁) :
    (s.endLabel l₁).endLabel l₂ =
      ({ s with shape := ((s.toMean.semEnd r₁ l₁).semEnd r₂ l₂).shape }).mapVals
        fun p _ => (((s.toMean.semEnd r₁ l₁).semEnd r₂ l₂).val · p) := by
  rw [endLabel_of_find _ l₂ r₂ h₂]
  have e : ({ s.endLabel l₁ with shape := ((s.endLabel l₁).toMean.semEnd r₂ l₂).shape } : SState) =
      ({ s with shape := ((s.toMean.semEnd r₁ l₁).semEnd r₂ l₂).shape } : SState).mapVals
        fun p _ => ((s.toMean.semEnd r₁ l₁).val · p) := by
    rw [endLabel_of_find s l₁ r₁ h₁]; rfl
  rw [e, mapVals_mapVals]
  apply mapVals_congr
  intro p hp
  funext φ
  exact Mean.semEnd_val_congr l₂ (fun ψ => endLabel_val s l₁ r₁ h₁ ψ p (.inl hp))
    (fun ψ => endLabel_val s l₁ r₁ h₁ ψ r₂ (.inr hr)) φ

/-- (WF3)'s relation on the semantic state: the content of borrow `k` depends on label `l`
(the meaning at `k`'s holder changes with `l`'s final content). This is the semantic shadow of
`loanUnder env l k` ("a loan of `l` occurs in the content of borrow `k`"): on `MState.sstate` it
is contained in `loanUnder` once a value's meaning is shown to read the future only at the loans
occurring in it, which needs that of `CodeMeaning.sealed`/`clo`/`pi` as a law. -/
def LoanDeps (s : SState) (l k : Nat) : Prop := ∃ r, s.shape r = some k ∧ s.dependsOn r l

/-- **Two [End]s commute** under (WF3): if the contents of `l₁` and `l₂` do not depend on each
other both ways, ending them in either order gives the *same* semantic state (not only states
`Below` each other both ways). Either label may be held nowhere. Milestone 3: the [Access] step
lemma (the checker ends every borrow whose loan occurs, in its own order; the reference ends, in
label order, those the meaning depends on), and `observation`'s end of every live borrow. -/
theorem endLabel_comm (s : SState) {l₁ l₂ : Nat} (hl : l₁ ≠ l₂)
    (hacyc : ¬ (s.LoanDeps l₂ l₁ ∧ s.LoanDeps l₁ l₂)) :
    (s.endLabel l₁).endLabel l₂ = (s.endLabel l₂).endLabel l₁ := by
  cases h₁ : s.positions.find? (fun p => decide (s.shape p = some l₁)) with
  | none =>
    have h₁' := (find_endLabel s hl.symm).trans h₁
    rw [endLabel_of_find_none s l₁ h₁, endLabel_of_find_none _ l₁ h₁']
  | some r₁ =>
  cases h₂ : s.positions.find? (fun p => decide (s.shape p = some l₂)) with
  | none =>
    have h₂' := (find_endLabel s hl).trans h₂
    rw [endLabel_of_find_none s l₂ h₂, endLabel_of_find_none _ l₂ h₂']
  | some r₂ =>
    have hs₁ := shape_of_find h₁
    have hs₂ := shape_of_find h₂
    have hr : r₁ ≠ r₂ := fun e => hl (Option.some.inj (hs₁.symm.trans (e ▸ hs₂)))
    have hind : ¬ s.toMean.dependsOn r₁ l₂ ∨ ¬ s.toMean.dependsOn r₂ l₁ := by
      by_cases a : s.toMean.dependsOn r₁ l₂
      · exact .inr fun b => hacyc ⟨⟨r₁, hs₁, a⟩, ⟨r₂, hs₂, b⟩⟩
      · exact .inl a
    rw [endLabel_endLabel s h₁ ((find_endLabel s hl).trans h₂) hr.symm,
      endLabel_endLabel s h₂ ((find_endLabel s hl.symm).trans h₁) hr,
      Mean.semEnd_comm _ hr hl hind]

/-- A well-founded relation has no cycle of length two. -/
theorem _root_.WellFounded.no_two_cycle {α : Sort _} {r : α → α → Prop} (h : WellFounded r) (a b : α)
    (hab : r a b) (hba : r b a) : False := by
  have key : ∀ x, Acc r x → ∀ y, r x y → r y x → False := by
    intro x hx
    induction hx with
    | intro x _ ih => intro y hxy hyx; exact ih y hyx x hyx hxy
  exact key a (h.apply a) b hab hba

/-- (WF3) in semantic form: ending borrows in the order of `LoanDeps` fixes each final content
once (docs/27 §3.3). -/
def SWF3 (s : SState) : Prop := WellFounded s.LoanDeps

/-- Under (WF3), any two distinct labels' ends commute. -/
theorem endLabel_comm_of_SWF3 (s : SState) (hwf : s.SWF3) {l₁ l₂ : Nat} (hl : l₁ ≠ l₂) :
    (s.endLabel l₁).endLabel l₂ = (s.endLabel l₂).endLabel l₁ :=
  endLabel_comm s hl fun ⟨a, b⟩ => hwf.no_two_cycle l₂ l₁ a b

end SState

/-! ## D84's drop at the join -/

namespace SState

theorem shape_setAt (s : SState) (p : Pos) (v : SVal) : (s.setAt p v).shape = s.shape := by
  cases p <;> rfl

/-- `setAt` changes the meaning at its own position, and nowhere else. -/
theorem valAt_setAt (s : SState) (p : Pos) (v : SVal) (q : Pos) :
    (s.setAt p v).valAt q = s.valAt q ∨ (s.setAt p v).valAt q = v := by
  cases p with
  | bind f i =>
    cases q with
    | bind f' i' =>
      by_cases h : f' = f ∧ i' = i
      · obtain ⟨rfl, rfl⟩ := h
        simp only [setAt, valAt, List.getElem?_modify]
        cases s.env[f']? with
        | none => left; rfl
        | some fr =>
          simp only [if_true, Option.bind_some]
          cases hb : fr.binds[i']? <;> simp [hb]
      · left
        simp only [setAt, valAt, List.getElem?_modify]
        by_cases hf : f = f'
        · subst hf
          have hi : i ≠ i' := fun e => h ⟨rfl, e.symm⟩
          cases s.env[f]? <;> simp [hi]
        · cases s.env[f']? <;> simp [hf]
    | temp f' i' =>
      left
      simp only [setAt, valAt, List.getElem?_modify]
      by_cases hf : f = f' <;> cases s.env[f']? <;> simp [hf]
  | temp f i =>
    cases q with
    | bind f' i' =>
      left
      simp only [setAt, valAt, List.getElem?_modify]
      by_cases hf : f = f' <;> cases s.env[f']? <;> simp [hf]
    | temp f' i' =>
      by_cases h : f' = f ∧ i' = i
      · obtain ⟨rfl, rfl⟩ := h
        simp only [setAt, valAt, List.getElem?_modify]
        cases s.env[f']? with
        | none => left; rfl
        | some fr =>
          simp only [if_true, Option.bind_some]
          by_cases hl : i' < fr.temps.length <;> simp [hl]
      · left
        simp only [setAt, valAt, List.getElem?_modify]
        by_cases hf : f = f'
        · subst hf
          have hi : i ≠ i' := fun e => h ⟨rfl, e.symm⟩
          cases s.env[f]? <;> simp [hi]
        · cases s.env[f']? <;> simp [hf]

/-- Setting a position to `⊥` loses only information. -/
theorem setAt_moved_below (s : SState) (p : Pos) : Below (s.setAt p fun _ => .moved).toMean s.toMean := by
  intro φ
  refine ⟨φ, fun q => ?_, fun q l h => by rwa [toMean, shape_setAt] at h⟩
  show (s.setAt p _).valAt q φ ⊑ s.valAt q φ
  rcases valAt_setAt s p (fun _ => .moved) q with e | e
  · rw [e]; exact Sem.le_refl _
  · rw [e]; exact .moved _

end SState

/-- Updating through `*`s only is updating the whole value (`*` is the identity on meanings). -/
theorem Sem.updAt_derefs (dm : DataModel) (Γ : List IndDecl) (T : TyM) (f : Sem → Sem) :
    ∀ (steps : List Step) (v : Sem), (∀ st ∈ steps, st = .deref) → Sem.updAt dm Γ T f steps v = some (f v)
  | [], _, _ => rfl
  | .deref :: sts, v, h => by
    show Sem.updAt dm Γ T f sts v = _
    exact Sem.updAt_derefs dm Γ T f sts v fun st hs => h st (List.mem_cons_of_mem _ hs)
  | .proj _ :: _, _, h => nomatch h _ (List.mem_cons_self ..)
  | .field _ :: _, _, h => nomatch h _ (List.mem_cons_self ..)

theorem resolve_steps {s : SState} {q : Place} {pos : Pos} {steps : List Step}
    (h : resolve s q = some (pos, steps)) : steps = q.steps.2 := by
  rcases hq : q.steps with ⟨i, st⟩
  simp only [resolve, hq, Option.map_eq_some_iff] at h
  obtain ⟨_, _, h⟩ := h
  cases h
  rfl

/-- An untyped tuple is below no element of a carrier. -/
theorem Sem.ctor_not_le_el0 {ty : String} {c : Nat} {fs : List Sem} {A : Type} {a : A} :
    ¬ (Sem.ctor ty c fs ⊑ Sem.el0 A a) := fun h => nomatch h

/-- Dropping a field of a whole constructor value (an element `el0` of a carrier, as every whole
data value is, D3) yields an untyped tuple, so it is not below the value, for every data model:
the mechanism of `joinDrop_not_below`. (The same holds for a named field `.field g`.) -/
theorem Sem.updAt_field_not_le (dm : DataModel) (Γ : List IndDecl) (T : TyM) (i : Nat) (A : Type)
    (x : A) (w : Sem) (hT : T ≠ .ty0 Nat)
    (hw : Sem.updAt dm Γ T (fun _ => .moved) [.proj i] (.el0 A x) = some w) : ¬ w ⊑ .el0 A x := by
  rw [Sem.updAt.eq_def] at hw
  simp only [if_neg hT] at hw
  split at hw
  · next d ps _ =>
    split at hw
    · next c fs _ =>
      split at hw
      · next fi hfi =>
        have e0 : Sem.updAt dm Γ (dm.fieldTy d ps c i (List.take i fs)) (fun _ => .moved) [] fi =
            some .moved := rfl
        rw [e0, Option.map_some, Option.some.injEq] at hw
        subst hw
        have hi : i < fs.length := (List.getElem?_eq_some_iff.mp hfi).1
        have hmem : Sem.moved ∈ fs.set i .moved :=
          List.mem_of_getElem? (by simp [hi] : (fs.set i .moved)[i]? = some .moved)
        have hnw : ¬ ∀ f ∈ fs.set i .moved, f.whole := fun h => by simpa [Sem.whole] using h _ hmem
        simp only [DataModel.ctorM, if_neg hnw]
        exact Sem.ctor_not_le_el0
      · cases hw
    · cases hw
  · cases hw

/-- Setting a place reached through `*`s only to `⊥`, as `joinDrop` does, loses only information. -/
theorem setAt_derefs_below (K : RunCtx) (s : SState) (pos : Pos) (steps : List Step)
    (hd : ∀ st ∈ steps, st = .deref) :
    Below (s.setAt pos fun φ' =>
      (Sem.updAt K.dm K.Γ (s.tyAt pos).m (fun _ => .moved) steps (s.valAt pos φ')).getD .err).toMean
      s.toMean := by
  have e : (fun φ' => (Sem.updAt K.dm K.Γ (s.tyAt pos).m (fun _ => .moved) steps (s.valAt pos φ')).getD .err) =
      fun _ => .moved := by
    funext φ'
    rw [Sem.updAt_derefs _ _ _ _ steps _ hd]
    rfl
  rw [e]
  exact SState.setAt_moved_below s pos

/-- **The drop at the join loses only information, when every dropped place is a root** (a
variable under `*`s only; milestone 3: `Steps/Match.lean`'s `evalMatch`/`evalMatchInd`, the
reference half of D84's [Join]). Each step of the drop is below: a copy place, a proof, a place
already `⊥` and an unresolved place are left alone, the place is accessed (`access_below`), a
borrow held at a dropped variable is ended (`endLabel_below`), and the place is set to `⊥`
(`setAt_derefs_below`).

The hypothesis cannot be dropped (`JoinDropCounterexample.joinDrop_not_below`): `Decide.jdMoves`
keeps a field step through a one-constructor type (`jdGrain`), so `x.0` of a pair can be in
`joinMoves`, and the drop turns a whole `x`, an `el0` of its carrier, into the untyped tuple
`ctor P 0 [⊥, b]`, which `⊑` puts below no `el0` (`Sem.updAt_field_not_le`). Under D84 that drop
is a definite change, not a loss of information, which is why the match statements compare the
checker's post-state with the reference's post-state rather than asking the drop to be `Below`
its input. -/
theorem joinDrop_below (K : RunCtx) (φ : Future) (t : Term) (s : SState)
    (hroot : ∀ q ∈ K.D.joinMoves (scopeOf s) (movedPlaces φ s) t, ∀ st ∈ q.steps.2, st = .deref) :
    Below (joinDrop K φ t s).toMean s.toMean := by
  unfold joinDrop
  generalize K.D.joinMoves (scopeOf s) (movedPlaces φ s) t = qs at hroot ⊢
  induction qs generalizing s with
  | nil => exact Below.refl _
  | cons q qs ih =>
    rw [List.foldl_cons]
    refine (ih _ fun q' hq' => hroot q' (List.mem_cons_of_mem _ hq')).trans ?_
    split
    · exact Below.refl _
    · split
      · next pos steps hres =>
        have hd : ∀ st ∈ steps, st = .deref := by
          rw [resolve_steps hres]; exact hroot q (List.mem_cons_self ..)
        refine Below.trans ?_ (SState.access_below s pos)
        dsimp only
        generalize s.access pos = s₁
        rcases hf : Sem.follow K.dm K.Γ (s₁.tyAt pos).m (s₁.valAt pos (s₁.closedFuture φ)) steps with _ | ⟨v, T⟩
        · exact Below.refl _
        · cases v <;> first
            | exact Below.refl _
            | refine (setAt_derefs_below K _ pos steps hd).trans ?_
              split
              · split
                · exact SState.endLabel_below _ _
                · exact Below.refl _
              · exact Below.refl _
      · exact Below.refl _

/-! ### The counterexample: a partial move at the join -/

namespace JoinDropCounterexample

/-- One declaration `P` with one constructor of two fields: every element is `()`, with fields
`()` and `()`. It covers no declaration, so its laws hold vacuously; the failure does not depend
on them (`Sem.updAt_field_not_le` holds for every data model). -/
noncomputable def dm : DataModel where
  covers _ := False
  car _ _ := Unit
  fieldTy _ _ _ _ _ := .ty0 Unit
  paramTy _ _ _ := .err
  pack _ _ _ _ := some ()
  tag _ := 0
  fields _ := [.el0 Unit (), .el0 Unit ()]
  rank _ := 0
  tag_pack _ h := h.elim
  fields_pack _ h := h.elim
  pack_fields _ h := h.elim
  pack_isSome h := h.elim
  rank_lt _ _ h := h.elim

def decl : IndDecl := { name := "P" }

/-- The decisions: the join drops `x.0`, field `0` of variable `x` (what `Decide.jdGrain` keeps
for a one-constructor type: one arm moved `x.0`, the other did not). -/
def D : Decisions where
  flags _ _ := (false, false)
  placeDecl _ _ := .other
  declOf _ _ := .other
  copy _ := false
  piSort _ _ := 1
  joinMoves _ _ _ := [.proj 0 (.var 0)]

noncomputable def K : RunCtx where
  dm := dm
  Γ := [decl]
  C := { global := fun _ => (.err, .plain .err), sealed := fun _ _ _ _ => .err,
         clo := fun _ _ _ _ _ => .err, pi := fun _ _ _ _ _ => .err, paramTy := fun _ _ _ _ => .plain .err }
  D := D

/-- One frame, one binding `x : P` holding the whole value `P((), ())`. -/
def s : SState :=
  { env := [{ binds := [{ ty := .plain (.ty0 Unit), val := fun _ => .el0 Unit () }] }], shape := fun _ => none,
    nextLoan := 0 }

theorem unit_ne_nat : TyM.ty0 Unit ≠ .ty0 Nat := fun h => by
  have e : Unit = Nat := TyM.ty0.inj h
  have : cast e.symm (0 : Nat) = cast e.symm 1 := Subsingleton.elim _ _
  have h2 := congrArg (cast e) this
  simp only [cast_cast, cast_eq] at h2
  exact absurd h2 (by decide)

theorem params_isSome : ∃ ps, dm.paramsOf decl (.ty0 Unit) = some ps := ⟨_, dif_pos ⟨[], rfl⟩⟩

theorem dataOf_eq (ps : List Sem) (hps : dm.paramsOf decl (.ty0 Unit) = some ps) :
    TyM.dataOf dm [decl] (.ty0 Unit) = some (decl, ps) := by
  simp [TyM.dataOf, hps]

theorem fieldsOf_eq (ps : List Sem) :
    dm.fieldsOf decl ps (.el0 Unit ()) = some (0, [.el0 Unit (), .el0 Unit ()]) := dif_pos rfl

theorem drop_isSome : ∃ w, Sem.updAt dm [decl] (.ty0 Unit) (fun _ => .moved) [.proj 0] (.el0 Unit ()) = some w := by
  obtain ⟨ps, hps⟩ := params_isSome
  rw [Sem.updAt.eq_def]
  simp only [if_neg unit_ne_nat, dataOf_eq ps hps, fieldsOf_eq ps]
  exact ⟨_, rfl⟩

/-- Following `x.0` reaches the whole field `()`: the drop is not skipped. -/
theorem follow_eq : Sem.follow dm [decl] (.ty0 Unit) (.el0 Unit ()) [.proj 0] = some (.el0 Unit (), .ty0 Unit) := by
  obtain ⟨ps, hps⟩ := params_isSome
  simp only [Sem.follow, Sem.step.eq_def, if_neg unit_ne_nat, Sem.stepField, dataOf_eq ps hps, fieldsOf_eq ps]
  rfl

/-- No label is live in `s`, so [Access] does nothing. -/
theorem access_eq (p : Pos) : s.access p = s := by
  have h0 : s.positions.filterMap s.shape = [] := List.filterMap_eq_nil_iff.mpr fun _ _ => rfl
  have h : s.liveLabels = [] := by simp only [SState.liveLabels, h0, List.mergeSort_nil]
  unfold SState.access
  rw [h]
  rfl

/-- **The drop at the join is not `Below` its input in general.** `x : P` holds `P((), ())`; the
join drops `x.0` (after [Access], which ends nothing, and reading `x.0`, which is whole); then `x`
means `ctor "P" 0 [⊥, ()]`, which is below no element of `P`'s carrier, so no future makes the
state after the drop below the state before. -/
theorem joinDrop_not_below (φ : Future) (t : Term) : ¬ Below (joinDrop K φ t s).toMean s.toMean := by
  obtain ⟨w, hw⟩ := drop_isSome
  have hres : resolve s (.proj 0 (.var 0)) = some (.bind 0 0, [.proj 0]) := rfl
  have hj : joinDrop K φ t s = s.setAt (.bind 0 0) fun _ => w := by
    unfold joinDrop
    simp only [K, D, List.foldl_cons, List.foldl_nil, Bool.false_eq_true, if_false, hres, access_eq]
    have e1 : (s.tyAt (.bind 0 0)).m = .ty0 Unit := rfl
    have e2 : s.valAt (.bind 0 0) = fun _ => .el0 Unit () := rfl
    have e3 : [Step.proj 0].isEmpty = false := rfl
    simp only [e1, e2, e3, follow_eq, Bool.false_eq_true, if_false, hw, Option.getD_some]
  intro h
  obtain ⟨φ, hle, _⟩ := h noFuture
  have hx := hle (.bind 0 0)
  rw [hj] at hx
  exact Sem.updAt_field_not_le dm [decl] (.ty0 Unit) 0 Unit () w unit_ne_nat hw hx

end JoinDropCounterexample

/-! ## [Access] leaves nothing it depends on (`access_post`) -/

private theorem filterMap_length_le {α β : Type _} (L : List α) (f g : α → Option β)
    (h : ∀ x, g x = none ∨ g x = f x) : (L.filterMap g).length ≤ (L.filterMap f).length := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rcases h a with ha | ha
    · rw [List.filterMap_cons_none ha]
      cases hf : f a <;> simp [hf] <;> omega
    · simp only [List.filterMap_cons, ha]
      cases f a <;> simp <;> omega

private theorem filterMap_length_lt {α β : Type _} (L : List α) (f g : α → Option β)
    (h : ∀ x, g x = none ∨ g x = f x) (x : α) (hx : x ∈ L) (hg : g x = none) (hf : f x ≠ none) :
    (L.filterMap g).length < (L.filterMap f).length := by
  induction L with
  | nil => cases hx
  | cons a L ih =>
    have hle := filterMap_length_le L f g h
    rcases List.mem_cons.mp hx with rfl | hx'
    · rw [List.filterMap_cons_none hg]
      obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp hf
      rw [List.filterMap_cons_some hb]; simp; omega
    · have := ih hx'
      rcases h a with ha | ha
      · rw [List.filterMap_cons_none ha]
        cases hfa : f a <;> simp [hfa] <;> omega
      · simp only [List.filterMap_cons, ha]
        cases f a <;> simp <;> omega

namespace SState

theorem positions_endLabel (s : SState) (l : Nat) : (s.endLabel l).positions = s.positions := by
  cases h : s.positions.find? (fun p => decide (s.shape p = some l)) with
  | none => rw [endLabel_of_find_none s l h]
  | some r => rw [endLabel_of_find s l r h, positions_mapVals, positions_withShape]

theorem mem_liveLabels (s : SState) (l : Nat) : l ∈ s.liveLabels ↔ ∃ p ∈ s.positions, s.shape p = some l := by
  simp [liveLabels, List.mem_filterMap]

/-- A live label has a holder for [End] to find. -/
theorem find_of_mem_liveLabels {s : SState} {l : Nat} (h : l ∈ s.liveLabels) :
    ∃ r, s.positions.find? (fun p => decide (s.shape p = some l)) = some r := by
  obtain ⟨q, hq, hql⟩ := (mem_liveLabels s l).mp h
  cases hf : s.positions.find? (fun p => decide (s.shape p = some l)) with
  | none => exact absurd (List.find?_eq_none.mp hf q hq) (by simp [hql])
  | some r => exact ⟨r, rfl⟩

/-- [End] never makes a label live. -/
theorem liveLabels_endLabel_le (s : SState) (l : Nat) :
    (s.endLabel l).liveLabels.length ≤ s.liveLabels.length := by
  cases h : s.positions.find? (fun p => decide (s.shape p = some l)) with
  | none => rw [endLabel_of_find_none s l h]; exact Nat.le_refl _
  | some r =>
    simp only [liveLabels, List.length_mergeSort, positions_endLabel, endLabel_shape s l r h]
    exact filterMap_length_le _ _ _ fun p => by by_cases hp : p = r <;> simp [hp]

/-- [End] of a live label leaves one live label fewer. -/
theorem liveLabels_endLabel_lt (s : SState) (l : Nat) (hl : l ∈ s.liveLabels) :
    (s.endLabel l).liveLabels.length < s.liveLabels.length := by
  obtain ⟨r, h⟩ := find_of_mem_liveLabels hl
  simp only [liveLabels, List.length_mergeSort, positions_endLabel, endLabel_shape s l r h]
  exact filterMap_length_lt _ _ _ (fun p => by by_cases hp : p = r <;> simp [hp]) r
    (List.mem_of_find?_eq_some h) (by simp) (by simp [shape_of_find h])

theorem liveLabels_foldl_endLabel_le (ls : List Nat) (s : SState) :
    (ls.foldl endLabel s).liveLabels.length ≤ s.liveLabels.length := by
  induction ls generalizing s with
  | nil => exact Nat.le_refl _
  | cons l ls ih => exact Nat.le_trans (ih _) (liveLabels_endLabel_le s l)

end SState

namespace SState

/-- One round of [Access] at `p`: end, in label order, every live label `p` depends on. -/
noncomputable def accessRound (p : Pos) (s : SState) : SState :=
  (s.liveLabels.filter fun l => decide (s.dependsOn p l)).foldl endLabel s

theorem access_eq_rounds (s : SState) (p : Pos) :
    s.access p = (List.range s.liveLabels.length).foldl (fun t _ => accessRound p t) s := rfl

/-- A round either finds nothing to end, and then `p` depends on no live label, or ends at least
one live label. -/
theorem accessRound_cases (s : SState) (p : Pos) :
    (accessRound p s = s ∧ ∀ l ∈ s.liveLabels, ¬ s.dependsOn p l) ∨
      (accessRound p s).liveLabels.length < s.liveLabels.length := by
  unfold accessRound
  cases hF : s.liveLabels.filter (fun l => decide (s.dependsOn p l)) with
  | nil =>
    left
    refine ⟨rfl, fun l hl hd => ?_⟩
    have := List.filter_eq_nil_iff.mp hF l hl
    simp [hd] at this
  | cons l ls =>
    right
    have hl : l ∈ s.liveLabels := (List.mem_filter.mp (hF ▸ List.mem_cons_self ..)).1
    exact Nat.lt_of_le_of_lt (liveLabels_foldl_endLabel_le ls _) (liveLabels_endLabel_lt s l hl)

private theorem rounds_fixed (p : Pos) (t : SState) (ht : accessRound p t = t) :
    ∀ ns : List Nat, ns.foldl (fun t _ => accessRound p t) t = t := by
  intro ns
  induction ns with
  | nil => rfl
  | cons _ ns ih => rw [List.foldl_cons, ht, ih]

private theorem rounds_post (p : Pos) :
    ∀ (ns : List Nat) (t : SState), t.liveLabels.length ≤ ns.length →
      ∀ l ∈ (ns.foldl (fun t _ => accessRound p t) t).liveLabels,
        ¬ (ns.foldl (fun t _ => accessRound p t) t).dependsOn p l := by
  intro ns
  induction ns with
  | nil =>
    intro t ht l hl
    simp only [List.length_nil, Nat.le_zero, List.length_eq_zero_iff] at ht
    simp [ht] at hl
  | cons _ ns ih =>
    intro t ht
    rw [List.foldl_cons]
    rcases accessRound_cases t p with ⟨hfix, hpost⟩ | hlt
    · rw [hfix, rounds_fixed p t hfix]; exact hpost
    · exact ih _ (by simp only [List.length_cons] at ht; omega)

/-- **After [Access] at `p`, `p` depends on no live label** (the spine's form of the toy
`access_post` and `read_post_live`, `Ochr/Model/State2.lean`). Each round ends every live label
`p` depends on; a round that ends something leaves fewer live labels, and there are as many
rounds as live labels at the start, so the last round finds nothing to end. Unconditional: no
(WF1)–(WF3) is needed. Milestone 3: `Steps/Borrow.lean`'s `accessPath_step`/`accessInside_step`
(their second conjunct: the accessed content no longer depends on a live label) and, through
them, `readPlace_step` and `borrowPlace_step`.

"Depends" is `Mean.dependsOn`, a change of one label's final content. That the content is then
the same under *every* future needs, in addition, that it reads the future only at live labels
(`SState.LocalTo`, as in `observation_const` below): a meaning can be unmoved by each single
label and still read infinitely many. -/
theorem access_post (s : SState) (p : Pos) :
    ∀ l ∈ (s.access p).liveLabels, ¬ (s.access p).dependsOn p l := by
  rw [access_eq_rounds]
  exact rounds_post p _ s (by simp)

end SState

end Ochr.Meaning

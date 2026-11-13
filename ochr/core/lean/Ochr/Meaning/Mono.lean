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
* `SState.access_post`: after [Access] at `p`, `p` depends on no live label. Unconditional.
* `SState.foldl_endLabel_indep`, `observation_upd_live`: under (WF3), after ending every live
  borrow nothing depends on a label that was live, so an observation reads no live label;
  `observation_const`: with locality too (`SState.LocalTo`, the semantic (WF2)), it means the
  same under every future. Each hypothesis is needed (`ObservationCounterexamples`).
* `SState.ShapeBelow` (every held label is below the counter) and `SState.ReadsBelow` (no meaning
  depends on a label at or above it): kept by [End], [Access], the drop at the join (`ShapeSub`:
  they only forget), by [Read] (`readPlace_shapeBelow`: a moved borrow is parked under its own
  label), and by [Borrow] and [Call], whose fresh label was held nowhere, has exactly one holder
  afterwards (the temporary it is parked in, D14) and is read only where the borrow puts it
  (`borrowPlace_fresh`, `callOf_fresh`, `borrowPlace_readsBelow`).

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
  rePointed _ _ := []
  typeDecl _ _ := .other

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

/-! ## Ending every live borrow: what an observation reads -/

theorem Future.upd_upd_same (φ : Future) (l : Nat) (a b : Sem) : (φ.upd l a).upd l b = φ.upd l b := by
  funext l'
  by_cases h : l' = l <;> simp [Future.upd, h]

/-- After ending `k`, nothing depends on `k` unless `k`'s holder did (a borrow holding its own
loan). -/
theorem Mean.semEnd_dependsOn_self {m : Mean} {r p : Pos} {k : Nat}
    (h : (m.semEnd r k).dependsOn p k) : m.dependsOn r k := by
  refine Classical.byContradiction fun hr => ?_
  obtain ⟨φ, x, hne⟩ := h
  apply hne
  simp only [Mean.semEnd]
  split
  · rfl
  · rw [Mean.not_dependsOn hr, Future.upd_upd_same]

/-- After ending `k` at `r`, a dependence on another label `l` was there before, directly or
through `k`: `p` read `k`, and `k`'s final content, `r`'s content, read `l`. -/
theorem Mean.semEnd_dependsOn {m : Mean} {r p : Pos} {k l : Nat} (hl : l ≠ k)
    (h : (m.semEnd r k).dependsOn p l) : m.dependsOn p l ∨ (m.dependsOn p k ∧ m.dependsOn r l) := by
  refine Classical.byContradiction fun hn => ?_
  have hpl : ¬ m.dependsOn p l := fun h' => hn (.inl h')
  obtain ⟨φ, x, hne⟩ := h
  apply hne
  simp only [Mean.semEnd]
  split
  · rfl
  · by_cases hrl : m.dependsOn r l
    · have hpk : ¬ m.dependsOn p k := fun h' => hn (.inr ⟨h', hrl⟩)
      rw [Mean.not_dependsOn hpk, Mean.not_dependsOn hpk, Mean.not_dependsOn hpl]
    · rw [Mean.not_dependsOn hrl, Future.upd_comm φ hl, Mean.not_dependsOn hpl]

namespace SState

/-- [End] on the semantic state depends as `semEnd` does (a position that does not exist means
`err` under every future, so it depends on nothing). -/
theorem endLabel_dependsOn {s : SState} {k : Nat} {r : Pos}
    (h : s.positions.find? (fun p => decide (s.shape p = some k)) = some r) {p : Pos} {l : Nat}
    (hd : (s.endLabel k).dependsOn p l) : (s.toMean.semEnd r k).dependsOn p l := by
  obtain ⟨φ, x, hne⟩ := hd
  by_cases hv : s.Valid p
  · refine ⟨φ, x, ?_⟩
    rw [← endLabel_val s k r h φ p (.inl hv), ← endLabel_val s k r h _ p (.inl hv)]
    exact hne
  · have e : (s.endLabel k).valAt p = fun _ => .err := by
      rw [endLabel_of_find s k r h, valAt_mapVals, valid_withShape, if_neg hv]
    exfalso
    apply hne
    show (s.endLabel k).valAt p φ = (s.endLabel k).valAt p (φ.upd l x)
    rw [e]

end SState

namespace SState

/-- The invariant of ending the labels `E` of `s₀` one after another (`foldl_endLabel_indep`):
the positions are kept; a shape entry is kept or was a holder of an ended label; every
dependence was there in `s₀`, or reaches a label `s₀`'s state depended on along (WF3)'s relation;
and nothing depends on an ended label. -/
private structure EndsInv (s₀ t : SState) (E : List Nat) : Prop where
  pos : t.positions = s₀.positions
  shape : ∀ p, t.shape p = s₀.shape p ∨ (t.shape p = none ∧ ∃ k ∈ E, s₀.shape p = some k)
  dep : ∀ p l, t.dependsOn p l →
    s₀.dependsOn p l ∨ ∃ l₀, s₀.dependsOn p l₀ ∧ Relation.TransGen s₀.LoanDeps l l₀
  ended : ∀ p, ∀ l ∈ E, ¬ t.dependsOn p l

/-- A holder's dependence is a path to its own label. -/
private theorem EndsInv.holder {s₀ t : SState} {E : List Nat} (I : EndsInv s₀ t E) {r : Pos}
    {k l : Nat} (hr : s₀.shape r = some k) (hd : t.dependsOn r l) : Relation.TransGen s₀.LoanDeps l k := by
  rcases I.dep r l hd with h | ⟨l₀, h₀, htg⟩
  · exact .single ⟨r, hr, h⟩
  · exact .tail htg ⟨r, hr, h₀⟩

private theorem EndsInv.extend {s₀ t : SState} {E : List Nat} (I : EndsInv s₀ t E) (k : Nat) (p : Pos) :
    t.shape p = s₀.shape p ∨ (t.shape p = none ∧ ∃ k' ∈ E ++ [k], s₀.shape p = some k') :=
  (I.shape p).imp_right fun ⟨h1, k', hk', h2⟩ => ⟨h1, k', List.mem_append_left _ hk', h2⟩

private theorem endsInv_step {s₀ t : SState} {E : List Nat} (hwf : s₀.SWF3) (I : EndsInv s₀ t E)
    {k : Nat} (hk : k ∈ s₀.liveLabels) : EndsInv s₀ (t.endLabel k) (E ++ [k]) := by
  have irr : ¬ Relation.TransGen s₀.LoanDeps k k := fun h => hwf.transGen.no_two_cycle k k h h
  cases hf : t.positions.find? (fun p => decide (t.shape p = some k)) with
  | none =>
    rw [endLabel_of_find_none t k hf]
    have hkE : k ∈ E := by
      obtain ⟨q, hq, hqk⟩ := (mem_liveLabels s₀ k).mp hk
      rcases I.shape q with e | ⟨_, k', hk', hqk'⟩
      · exact absurd (List.find?_eq_none.mp hf q (I.pos ▸ hq)) (by simp [e, hqk])
      · rw [hqk] at hqk'; cases hqk'; exact hk'
    refine ⟨I.pos, I.extend k, I.dep, fun p l hl => ?_⟩
    rcases List.mem_append.mp hl with h | h
    · exact I.ended p l h
    · rw [List.mem_singleton.mp h]; exact I.ended p k hkE
  | some r =>
    have htr : t.shape r = some k := shape_of_find hf
    have hsr : s₀.shape r = some k := by
      rcases I.shape r with e | ⟨e, _⟩
      · rw [← e]; exact htr
      · rw [e] at htr; cases htr
    have self : ¬ t.dependsOn r k := fun h => irr (I.holder hsr h)
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [positions_endLabel, I.pos]
    · intro p
      rw [endLabel_shape t k r hf]
      by_cases hp : p = r
      · subst hp; exact .inr ⟨by simp, k, by simp, hsr⟩
      · simpa [hp] using I.extend k p
    · intro p l hd
      have hd' := endLabel_dependsOn hf hd
      by_cases hlk : l = k
      · subst hlk; exact absurd (Mean.semEnd_dependsOn_self hd') self
      · rcases Mean.semEnd_dependsOn hlk hd' with h | ⟨hpk, hrl⟩
        · exact I.dep p l h
        · have h1 := I.holder hsr hrl
          rcases I.dep p k hpk with h2 | ⟨l₁, h₁, h3⟩
          · exact .inr ⟨k, h2, h1⟩
          · exact .inr ⟨l₁, h₁, h1.trans h3⟩
    · intro p l hl hd
      have hd' := endLabel_dependsOn hf hd
      by_cases hlk : l = k
      · subst hlk; exact self (Mean.semEnd_dependsOn_self hd')
      · have hlE : l ∈ E := by simpa [hlk] using hl
        rcases Mean.semEnd_dependsOn hlk hd' with h | ⟨_, hrl⟩
        · exact I.ended p l hlE h
        · exact I.ended r l hlE hrl

private theorem endsInv_foldl {s₀ : SState} (hwf : s₀.SWF3) :
    ∀ (ls : List Nat) (t : SState) (E : List Nat),
      (∀ k ∈ ls, k ∈ s₀.liveLabels) → EndsInv s₀ t E → EndsInv s₀ (ls.foldl endLabel t) (E ++ ls)
  | [], t, E, _, I => by simpa using I
  | k :: ls, t, E, hls, I => by
    rw [List.foldl_cons, show E ++ k :: ls = (E ++ [k]) ++ ls by simp]
    exact endsInv_foldl hwf ls _ _ (fun k' h => hls k' (List.mem_cons_of_mem _ h))
      (endsInv_step hwf I (hls k (List.mem_cons_self ..)))

/-- **Ending live labels in turn leaves nothing depending on them**, under (WF3) in its semantic
form, in any order and with repetitions. Ending `k` fixes `k` to its holder's content, so nothing
depends on `k` afterwards unless that content did, which would be a cycle through `k`; and a
later end makes a position depend only on what it or the ended holder already depended on.
Without (WF3) it is false (`ObservationCounterexamples.not_indep_without_SWF3`). Milestone 3:
`Steps/Obs.lean`'s `observe_step` and `idType_step`, through `observation_upd_live`. -/
theorem foldl_endLabel_indep (s : SState) (hwf : s.SWF3) (ls : List Nat)
    (hls : ∀ k ∈ ls, k ∈ s.liveLabels) : ∀ p, ∀ l ∈ ls, ¬ (ls.foldl endLabel s).dependsOn p l := by
  have I := endsInv_foldl hwf ls s [] hls
    ⟨rfl, fun _ => .inl rfl, fun _ _ h => .inl h, fun _ _ h => nomatch h⟩
  intro p l hl
  exact I.ended p l (by simpa using hl)

end SState

/-- **An observation reads no live label** (under (WF3)): changing the final content of a label
live in the observed state changes neither the result nor any compared position (the result is
the caller's, so only the positions are at stake). This is the form that holds of every state;
`observation_const` is the strong form. Milestone 3: `Steps/Obs.lean`'s `observe_step` and
`idType_step` (the checker reads the owners after ending every borrow; the reference's
observation must not see the live labels the checker's ends forget). -/
theorem observation_upd_live (φ : Future) (r : Res) (s : SState) (hwf : s.SWF3) {l : Nat}
    (hl : l ∈ s.liveLabels) (x : Sem) : observation (φ.upd l x) [] [] r s = observation φ [] [] r s := by
  simp only [observation]
  congr 1
  apply List.map_congr_left
  intro p _
  exact Mean.not_dependsOn (SState.foldl_endLabel_indep s hwf _ (fun _ h => h) p l hl) φ x

namespace SState

/-- The state factors through the labels `L`: futures agreeing on `L` give every position the
same meaning (the form of `run_congr`'s hypothesis `hs`, `Lemmas.lean`). The semantic form of
(WF2) on the reference state (every loan has its borrow in the state) is
`s.LocalTo (· ∈ s.liveLabels)`; a sealed program holding an inert loan (a hole whose borrow is
outside the run) breaks it. -/
def LocalTo (s : SState) (L : Nat → Prop) : Prop :=
  ∀ p (φ φ' : Future), (∀ l, L l → φ l = φ' l) → s.valAt p φ = s.valAt p φ'

/-- [End] keeps locality: the ended label is fixed to the holder's content, which is local too. -/
theorem endLabel_localTo {s : SState} {L : Nat → Prop} (h : s.LocalTo L) (k : Nat) :
    (s.endLabel k).LocalTo L := by
  cases hf : s.positions.find? (fun p => decide (s.shape p = some k)) with
  | none => rw [endLabel_of_find_none s k hf]; exact h
  | some r =>
    intro p φ φ' hφ
    rw [endLabel_of_find s k r hf, valAt_mapVals, valid_withShape]
    split
    · simp only [Mean.semEnd, toMean]
      split
      · rfl
      · apply h p
        intro l hl
        simp only [Future.upd]
        split
        · exact h r φ φ' hφ
        · exact hφ l hl
    · rfl

theorem foldl_endLabel_localTo {s : SState} {L : Nat → Prop} (h : s.LocalTo L) :
    ∀ ls : List Nat, (ls.foldl endLabel s).LocalTo L := by
  intro ls
  induction ls generalizing s with
  | nil => exact h
  | cons k ls ih => exact ih (endLabel_localTo h k)

end SState

/-- A meaning that reads the future only at the finitely many labels `L`, and changes with none
of them, is constant. (Without the locality it need not be: reading infinitely many labels, a
meaning can be unmoved by each one.) -/
theorem const_of_local (f : Future → Sem) : ∀ L : List Nat,
    (∀ φ φ', (∀ l ∈ L, φ l = φ' l) → f φ = f φ') → (∀ l ∈ L, ∀ φ x, f (φ.upd l x) = f φ) →
    ∀ φ φ', f φ = f φ'
  | [], hloc, _ => fun φ φ' => hloc φ φ' (by simp)
  | l :: L, hloc, hind => by
    have hloc' : ∀ φ φ', (∀ l' ∈ L, φ l' = φ' l') → f φ = f φ' := by
      intro φ φ' h
      rw [← hind l (List.mem_cons_self ..) φ (φ' l)]
      apply hloc
      intro l' hl'
      by_cases e : l' = l
      · simp [Future.upd, e]
      · have hl'' : l' ∈ L := (List.mem_cons.mp hl').resolve_left e
        simp [Future.upd, e, h l' hl'']
    exact const_of_local f L hloc' fun l' hl' => hind l' (List.mem_cons_of_mem _ hl')

/-- **An observation means the same under every future** when the observed state reads the
future only at its live labels (`LocalTo`, the semantic (WF2)) and (WF3) holds: after ending
every live borrow, each position is local to the live labels and depends on none of them, so it
is constant (`const_of_local`). This is what makes `Id`'s meaning a plain proposition. Both
hypotheses are needed (`ObservationCounterexamples`). Milestone 3: `Steps/Obs.lean`'s
`idType_step`. -/
theorem observation_const (r : Res) (s : SState) (hwf : s.SWF3) (hloc : s.LocalTo (· ∈ s.liveLabels))
    (φ φ' : Future) : observation φ [] [] r s = observation φ' [] [] r s := by
  simp only [observation]
  congr 1
  apply List.map_congr_left
  intro p _
  exact const_of_local (fun ψ => (s.liveLabels.foldl SState.endLabel s).valAt p ψ) s.liveLabels
    (fun ψ ψ' h => SState.foldl_endLabel_localTo hloc _ p ψ ψ' fun l hl => h l hl)
    (fun l hl ψ x => Mean.not_dependsOn (SState.foldl_endLabel_indep s hwf _ (fun _ h => h) p l hl) ψ x)
    φ φ'

namespace ObservationCounterexamples

/-- Without (WF3): borrow `0` held at `x₀` holds a loan of `1`, borrow `1` held at `x₁` a loan of
`0`, and `x₂` holds a pair of both loans. -/
def cyc : SState :=
  { env := [{ binds := [{ ty := .plain .err, val := fun φ => φ 1 }, { ty := .plain .err, val := fun φ => φ 0 },
      { ty := .plain .err, val := fun φ => .ctor "x" 0 [φ 0, φ 1] }] }],
    shape := fun p => if p = .bind 0 0 then some 0 else if p = .bind 0 1 then some 1 else none,
    nextLoan := 2 }

theorem cyc_positions : cyc.positions = [.bind 0 0, .bind 0 1, .bind 0 2] := by
  simp [SState.positions, cyc, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    List.range'_succ]

/-- After ending `0` and then `1`, `x₂` reads `(φ 1, φ 1)`: it still depends on the live label `1`. -/
theorem cyc_ends (φ : Future) :
    ([0, 1].foldl SState.endLabel cyc).valAt (.bind 0 2) φ = .ctor "x" 0 [φ 1, φ 1] := by
  have h0 : cyc.positions.find? (fun p => decide (cyc.shape p = some 0)) = some (.bind 0 0) := by
    rw [cyc_positions]; rfl
  have h1 : (cyc.endLabel 0).positions.find? (fun p => decide ((cyc.endLabel 0).shape p = some 1)) =
      some (.bind 0 1) :=
    (SState.find_endLabel cyc (by decide)).trans (by rw [cyc_positions]; rfl)
  have e1 : ∀ q ψ, q ≠ .bind 0 0 → (cyc.endLabel 0).valAt q ψ = cyc.valAt q (ψ.upd 0 (ψ 1)) := by
    intro q ψ hq
    rw [SState.endLabel_val cyc 0 _ h0 ψ q (.inr hq)]
    simp only [Mean.semEnd, SState.toMean, if_neg hq]
    rfl
  show ((cyc.endLabel 0).endLabel 1).valAt (.bind 0 2) φ = _
  rw [SState.endLabel_val _ 1 _ h1 φ _ (.inr (by decide))]
  simp only [Mean.semEnd, SState.toMean, if_neg (by decide : Pos.bind 0 2 ≠ .bind 0 1)]
  rw [e1 _ _ (by decide), e1 _ _ (by decide)]
  simp [cyc, SState.valAt, Future.upd]

theorem not_indep_without_SWF3 :
    0 ∈ cyc.liveLabels ∧ 1 ∈ cyc.liveLabels ∧ ([0, 1].foldl SState.endLabel cyc).dependsOn (.bind 0 2) 1 := by
  refine ⟨(SState.mem_liveLabels _ _).mpr ⟨.bind 0 0, by simp [cyc_positions], rfl⟩,
    (SState.mem_liveLabels _ _).mpr ⟨.bind 0 1, by simp [cyc_positions], rfl⟩,
    ⟨fun _ => .moved, .proof, ?_⟩⟩
  show ([0, 1].foldl SState.endLabel cyc).valAt (.bind 0 2) (fun _ => .moved) ≠
    ([0, 1].foldl SState.endLabel cyc).valAt (.bind 0 2) (Future.upd (fun _ => .moved) 1 .proof)
  rw [cyc_ends, cyc_ends]
  simp [Future.upd]

/-- Without locality: `x₀` holds an inert loan of `0` (no borrow of `0` is held), so no label is
live, (WF3) holds vacuously, and the observation is `[r, φ 0]`. -/
def inert : SState :=
  { env := [{ binds := [{ ty := .plain .err, val := fun φ => φ 0 }] }], shape := fun _ => none,
    nextLoan := 1 }

theorem inert_SWF3 : inert.SWF3 :=
  ⟨fun a => ⟨a, fun _ ⟨_, h, _⟩ => nomatch h⟩⟩

theorem observation_not_const (r : Res) :
    observation (fun _ => .moved) [] [] r inert ≠ observation (fun _ => .proof) [] [] r inert := by
  have h0 : inert.positions.filterMap inert.shape = [] := List.filterMap_eq_nil_iff.mpr fun _ _ => rfl
  have hl : inert.liveLabels = [] := by simp only [SState.liveLabels, h0, List.mergeSort_nil]
  have hp : inert.positions = [.bind 0 0] := by
    simp [SState.positions, inert, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  simp only [observation, List.zipIdx_nil, hl, List.foldl_nil, hp]
  simp [inert, SState.valAt]

end ObservationCounterexamples

/-! ## The shape invariant: every held label is below the counter, so fresh labels are fresh -/

namespace SState

/-- Every label the shape holds is below the label counter, so the label `freshLoan` hands out
is held nowhere (`freshLoan_fresh`). On `MState.sstate` this is the freshness half of (WF6) for
*borrow* labels, which (WF6) as stated does not give: it bounds `Value.loans`, and the label of
`borrow ℓ w` is not among a value's loans (`Value.loans (.borrow _ w) = w.loans`). -/
def ShapeBelow (s : SState) : Prop := ∀ p l, s.shape p = some l → l < s.nextLoan

/-- `s'` holds only borrows `s` holds, at the same positions, and has the same counter: what every
step that forgets or rewrites meanings leaves (`endLabel`, `access`, `setAt`, `mapVals`,
`takeLabel`, `joinDrop`). -/
def ShapeSub (s' s : SState) : Prop :=
  (∀ p l, s'.shape p = some l → s.shape p = some l) ∧ s'.nextLoan = s.nextLoan

theorem ShapeSub.refl (s : SState) : ShapeSub s s := ⟨fun _ _ h => h, rfl⟩

theorem ShapeSub.trans {a b c : SState} (h₁ : ShapeSub a b) (h₂ : ShapeSub b c) : ShapeSub a c :=
  ⟨fun p l h => h₂.1 p l (h₁.1 p l h), h₁.2.trans h₂.2⟩

theorem ShapeBelow.of_sub {s' s : SState} (h : ShapeSub s' s) (hs : s.ShapeBelow) : s'.ShapeBelow :=
  fun p l hp => h.2 ▸ hs p l (h.1 p l hp)

theorem shapeSub_setAt (s : SState) (p : Pos) (v : SVal) : ShapeSub (s.setAt p v) s := by
  cases p <;> exact ShapeSub.refl s

theorem shapeSub_mapVals (s : SState) (g : Pos → SVal → SVal) : ShapeSub (s.mapVals g) s :=
  ShapeSub.refl s

theorem shapeSub_endLabel (s : SState) (l : Nat) : ShapeSub (s.endLabel l) s := by
  cases h : s.positions.find? (fun p => decide (s.shape p = some l)) with
  | none => rw [endLabel_of_find_none s l h]; exact ShapeSub.refl s
  | some r =>
    refine ⟨fun p k hp => ?_, by rw [endLabel_of_find s l r h]; rfl⟩
    rw [endLabel_shape s l r h] at hp
    by_cases hpr : p = r
    · simp [hpr] at hp
    · simpa [hpr] using hp

theorem shapeSub_foldl_endLabel (ls : List Nat) (s : SState) : ShapeSub (ls.foldl endLabel s) s := by
  induction ls generalizing s with
  | nil => exact ShapeSub.refl s
  | cons l ls ih => exact (ih _).trans (shapeSub_endLabel s l)

theorem shapeSub_access (s : SState) (p : Pos) : ShapeSub (s.access p) s := by
  rw [access_eq_rounds]
  generalize List.range s.liveLabels.length = ns
  induction ns generalizing s with
  | nil => exact ShapeSub.refl s
  | cons _ ns ih => exact (ih _).trans (shapeSub_foldl_endLabel _ s)

end SState

/-- D84's drop at the join holds no new borrow and keeps the counter (with `shapeSub_access`, the
forgetting steps of `Steps/Match.lean`'s and `Steps/Borrow.lean`'s lemmas keep `ShapeBelow`). -/
theorem shapeSub_joinDrop (K : RunCtx) (φ : Future) (t : Term) (s : SState) :
    SState.ShapeSub (joinDrop K φ t s) s := by
  unfold joinDrop
  generalize K.D.joinMoves (scopeOf s) (movedPlaces φ s) t = qs
  induction qs generalizing s with
  | nil => exact SState.ShapeSub.refl s
  | cons q qs ih =>
    rw [List.foldl_cons]
    refine (ih _).trans ?_
    split
    · exact SState.ShapeSub.refl s
    · split
      · next pos steps _ =>
        refine SState.ShapeSub.trans ?_ (SState.shapeSub_access s pos)
        dsimp only
        generalize s.access pos = s₁
        rcases Sem.follow K.dm K.Γ (s₁.tyAt pos).m (s₁.valAt pos (s₁.closedFuture φ)) steps with _ | ⟨v, T⟩
        · exact SState.ShapeSub.refl _
        · cases v <;> first
            | exact SState.ShapeSub.refl _
            | refine (SState.shapeSub_setAt _ pos _).trans ?_
              split
              · split
                · exact SState.shapeSub_endLabel _ _
                · exact SState.ShapeSub.refl _
              · exact SState.ShapeSub.refl _
      · exact SState.ShapeSub.refl s

namespace SState

/-- **A fresh label is held nowhere**, and the counter moves past it, so the invariant is kept
(the [Borrow] and borrow-returning [Call] halves of `Steps/Borrow.lean`'s `borrowPlace_step` and
`Steps/Call.lean`'s `closeCall_step`: the label the checker's `nextLoan` hands out is the
reference's). -/
theorem freshLoan_fresh (s : SState) (hs : s.ShapeBelow) :
    s.freshLoan.1 = s.nextLoan ∧ s.freshLoan.1 < s.freshLoan.2.nextLoan ∧
      (∀ p, s.freshLoan.2.shape p ≠ some s.freshLoan.1) ∧ s.freshLoan.2.ShapeBelow :=
  ⟨rfl, Nat.lt_succ_self _, fun p h => Nat.lt_irrefl _ (hs p _ h),
    fun p l h => Nat.lt_succ_of_lt (hs p l h)⟩

theorem shapeSub_pushBind (s : SState) (b : SBinding) : ShapeSub (s.pushBind b) s := ShapeSub.refl s
theorem shapeSub_pushTemp (s : SState) (v : SVal) : ShapeSub (s.pushTemp v) s := ShapeSub.refl s
theorem shapeSub_pushFrame (s : SState) : ShapeSub s.pushFrame s := ShapeSub.refl s
theorem shapeSub_dropLast (s : SState) : ShapeSub s.dropLast s :=
  ⟨fun p l h => by
    simp only [SState.dropLast] at h
    split at h <;> split at h <;> simp_all,
   rfl⟩

theorem nextLoan_setAt (s : SState) (p : Pos) (v : SVal) : (s.setAt p v).nextLoan = s.nextLoan := by
  cases p <;> rfl

/-- Taking a borrow from its holder (D14) holds no new borrow. -/
theorem shapeSub_takeLabel (s : SState) (l : Nat) : ShapeSub (s.takeLabel l) s := by
  unfold takeLabel
  split
  · next r _ =>
    refine ⟨fun p k hp => ?_, nextLoan_setAt s r _⟩
    by_cases hpr : p = r
    · simp [hpr] at hp
    · simpa [hpr] using hp
  · exact ShapeSub.refl s

theorem shapeSub_foldl_takeLabel (ls : List Nat) (s : SState) : ShapeSub (ls.foldl takeLabel s) s := by
  induction ls generalizing s with
  | nil => exact ShapeSub.refl s
  | cons l ls ih => exact (ih _).trans (shapeSub_takeLabel s l)

/-- Parking a borrow (D14) makes one new position, if any, the holder of `l`. -/
theorem pushTempShaped_shape (s : SState) (v : SVal) (l : Nat) :
    ∃ T : Option Pos, ∀ q, (s.pushTempShaped v l).shape q = if some q = T then some l else s.shape q := by
  unfold pushTempShaped
  dsimp only
  split
  · next fr _ =>
    refine ⟨some (.temp (s.pushTemp v).topIdx (fr.temps.length - 1)), fun q => ?_⟩
    simp only [Option.some.injEq]
    rfl
  · exact ⟨none, fun q => by simp only [reduceCtorEq, if_false]; rfl⟩

theorem nextLoan_pushTempShaped (s : SState) (v : SVal) (l : Nat) :
    (s.pushTempShaped v l).nextLoan = s.nextLoan := by
  unfold pushTempShaped; dsimp only; split <;> rfl

theorem shapeBelow_pushTempShaped {s : SState} (hs : s.ShapeBelow) (v : SVal) {l : Nat}
    (hl : l < s.nextLoan) : (s.pushTempShaped v l).ShapeBelow := by
  obtain ⟨T, hT⟩ := pushTempShaped_shape s v l
  intro q k hq
  rw [nextLoan_pushTempShaped]
  rw [hT] at hq
  split at hq
  · cases hq; exact hl
  · exact hs q k hq

/-- A label held nowhere is held at most once after it is parked. -/
theorem pushTempShaped_unique (s : SState) (v : SVal) {l : Nat} (hl : ∀ q, s.shape q ≠ some l) :
    ∀ q q', (s.pushTempShaped v l).shape q = some l → (s.pushTempShaped v l).shape q' = some l → q = q' := by
  obtain ⟨T, hT⟩ := pushTempShaped_shape s v l
  intro q q' hq hq'
  rw [hT] at hq hq'
  split at hq
  · split at hq'
    · next h₁ h₂ => exact Option.some.inj (h₁.trans h₂.symm)
    · exact absurd hq' (hl q')
  · exact absurd hq (hl q)


/-- A fresh label, parked: the invariant is kept, the label is below the counter, and it has at
most one holder. -/
theorem fresh_park {s : SState} (hs : s.ShapeBelow) {k : Nat} (hk : k < s.nextLoan)
    (hfree : ∀ q, s.shape q ≠ some k) (v : SVal) :
    (s.pushTempShaped v k).ShapeBelow ∧ k < (s.pushTempShaped v k).nextLoan ∧
      ∀ q q', (s.pushTempShaped v k).shape q = some k → (s.pushTempShaped v k).shape q' = some k → q = q' :=
  ⟨shapeBelow_pushTempShaped hs v hk, by rw [nextLoan_pushTempShaped]; exact hk,
    pushTempShaped_unique s v hfree⟩
end SState

/-- Binding a borrow records its label in the shape; the invariant is kept when the label is
below the counter, which every result label is (`borrowPlace_fresh`, `callOf_fresh`). -/
theorem pushBindShaped_shapeBelow (s : SState) (b : SBinding) (hs : s.ShapeBelow)
    (hl : ∀ l, b.ty.label = some l → l < s.nextLoan) : (pushBindShaped s b).ShapeBelow := by
  unfold pushBindShaped
  split
  · next l hb =>
    have h₁ : (s.takeLabel l).ShapeBelow := SState.ShapeBelow.of_sub (SState.shapeSub_takeLabel s l) hs
    have hn : (s.takeLabel l).nextLoan = s.nextLoan := (SState.shapeSub_takeLabel s l).2
    dsimp only
    split
    · intro p l' h
      dsimp only at h ⊢
      split at h
      · cases h; show l < (s.takeLabel l).nextLoan; rw [hn]; exact hl l hb
      · exact h₁ p l' h
    · exact h₁
  · exact hs

theorem contentOf_shapeSub (K : RunCtx) (φ : Future) (p : Place) (s : SState)
    {x : Sem × TyS × Pos × List Step} {s' : SState} (h : contentOf K φ p s = some (x, s')) :
    SState.ShapeSub s' s := by
  unfold contentOf at h
  split at h
  · next pos steps _ =>
    dsimp only at h
    split at h
    · cases h; exact SState.shapeSub_access s pos
    · cases h
  · cases h

theorem setContent_shapeSub (K : RunCtx) (φ : Future) (pos : Pos) (steps : List Step) (v : Sem)
    (s : SState) {u : PUnit} {s' : SState} (h : setContent K φ pos steps v s = some (u, s')) :
    SState.ShapeSub s' s := by
  unfold setContent at h
  dsimp only at h
  split at h
  · cases h; exact SState.shapeSub_setAt _ _ _
  · cases h

/-- **[Borrow] keeps the shape invariant, and its label is fresh**: the result's label was held
nowhere before, is below the new counter, and has exactly one holder after the borrow, the
temporary it is parked in (D14; the binder takes it over, `pushBindShaped_shapeBelow`).
Milestone 3: `Steps/Borrow.lean`'s `borrowPlace_step`. -/
theorem borrowPlace_fresh (K : RunCtx) (φ : Future) (p : Place) (s : SState) (hs : s.ShapeBelow)
    {v : Sem} {T : TyS} {s' : SState} (h : borrowPlace K φ p s = some ((v, T), s')) :
    s'.ShapeBelow ∧ ∃ l, T.label = some l ∧ l < s'.nextLoan ∧ (∀ q, s.shape q ≠ some l) ∧
      ∀ q q', s'.shape q = some l → s'.shape q' = some l → q = q' := by
  unfold borrowPlace at h
  cases hc : contentOf K φ p s with
  | none => simp [hc] at h
  | some x =>
    obtain ⟨⟨v₀, T₀, pos, steps⟩, s₁⟩ := x
    have hsub := contentOf_shapeSub K φ p s hc
    have h₁ : s₁.ShapeBelow := SState.ShapeBelow.of_sub hsub hs
    obtain ⟨_, hlt, hfresh, hb⟩ := SState.freshLoan_fresh s₁ h₁
    simp only [hc, Option.bind_eq_bind, Option.bind_some] at h
    split at h
    · cases h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨⟨_, rfl⟩, rfl⟩ := h
      refine ⟨SState.shapeBelow_pushTempShaped (SState.ShapeBelow.of_sub (SState.shapeSub_setAt _ _ _) hb) _
          (by rw [SState.nextLoan_setAt]; exact hlt), s₁.freshLoan.1, rfl,
        by rw [SState.nextLoan_pushTempShaped, SState.nextLoan_setAt]; exact hlt, fun q hq => ?_,
        SState.pushTempShaped_unique _ _ fun q hq => hfresh q ((SState.shapeSub_setAt _ _ _).1 q _ hq)⟩
      have := hs q _ hq
      rw [← hsub.2] at this
      exact Nat.lt_irrefl _ this

/-- **A call keeps the shape invariant, and a borrow it returns has a fresh label**: the
arguments' parked borrows are taken (`takeLabel`); the borrow-returning case takes `freshLoan`
and parks the result, so its label was held nowhere before, is below the new counter, and has
one holder. Milestone 3: `Steps/Call.lean`'s `closeCall_step`. -/
theorem callOfL_fresh.{u} (L : Lvl.{u}) (ps : List PiParam) (out : PiOut) (fv : Sem) (args : List Res) (s : SState)
    (hs : s.ShapeBelow) {r : Sem} {T : TyS} {s' : SState}
    (h : callOfL L ps out fv args s = some ((r, T), s')) :
    s'.ShapeBelow ∧ ∀ l, T.label = some l → l < s'.nextLoan ∧ (∀ q, s.shape q ≠ some l) ∧
      ∀ q q', s'.shape q = some l → s'.shape q' = some l → q = q' := by
  unfold callOfL at h
  try dsimp only at h
  have hsub := SState.shapeSub_foldl_takeLabel ((((args.zip ps).filter (·.2.isRef)).map (·.1.2.label)).filterMap id) s
  have hs₀ := SState.ShapeBelow.of_sub hsub hs
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨_, rfl⟩, rfl⟩ := h
    exact ⟨SState.ShapeBelow.of_sub (SState.shapeSub_mapVals _ _) hs₀, fun l hl => by
      simp [TyS.plain] at hl⟩
  · simp only [SState.freshLoan, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨_, rfl⟩, rfl⟩ := h
    obtain ⟨_, _, hfresh, hb⟩ := SState.freshLoan_fresh _ hs₀
    obtain ⟨hb', hlt', huniq⟩ := SState.fresh_park
      (SState.ShapeBelow.of_sub (SState.shapeSub_mapVals _ _) hb) (Nat.lt_succ_self _)
      (fun q hq => hfresh q hq) _
    refine ⟨hb', fun l hl => ?_⟩
    simp only [Option.some.injEq] at hl
    subst hl
    refine ⟨hlt', fun q hq => ?_, huniq⟩
    have := hs q _ hq
    rw [← hsub.2] at this
    exact Nat.lt_irrefl _ this
  · cases h

theorem callOf_fresh (fv : Res) (args : List Res) (s : SState)
    (hs : s.ShapeBelow) {r : Sem} {T : TyS} {s' : SState} (h : callOf fv args s = some ((r, T), s')) :
    s'.ShapeBelow ∧ ∀ l, T.label = some l → l < s'.nextLoan ∧ (∀ q, s.shape q ≠ some l) ∧
      ∀ q q', s'.shape q = some l → s'.shape q' = some l → q = q' := by
  unfold callOf at h
  split at h
  · split at h
    · exact callOfL_fresh _ _ _ _ _ _ hs h
    · exact callOfL_fresh _ _ _ _ _ _ hs h
    · exact callOfL_fresh _ _ _ _ _ _ hs h
    · cases h
  · cases h

/-- [Read] keeps the shape invariant and the counter: its access and its move only forget, and a
moved borrow is parked under the label it already had (D14). Milestone 3: `Steps/Borrow.lean`'s
`readPlace_step`. -/
theorem readPlace_shapeBelow (K : RunCtx) (φ : Future) (p : Place) (copy : Bool) (s : SState)
    (hs : s.ShapeBelow) {x : Res} {s' : SState} (h : readPlace K φ p copy s = some (x, s')) :
    s'.ShapeBelow ∧ s'.nextLoan = s.nextLoan := by
  unfold readPlace at h
  cases hc : contentOf K φ p s with
  | none => simp [hc] at h
  | some y =>
    obtain ⟨⟨v, T, pos, steps⟩, s₁⟩ := y
    have hsub := contentOf_shapeSub K φ p s hc
    have h₁ := SState.ShapeBelow.of_sub hsub hs
    simp only [hc, Option.bind_eq_bind, Option.bind_some] at h
    split at h
    · cases h
    · split at h
      · cases h; exact ⟨h₁, hsub.2⟩
      · cases hs2 : setContent K φ pos steps .moved s₁ with
        | none => simp [hs2] at h
        | some z =>
          obtain ⟨u, s₂⟩ := z
          have hsub2 := setContent_shapeSub K φ pos steps .moved s₁ hs2
          have h₂ := SState.ShapeBelow.of_sub hsub2 h₁
          simp only [hs2, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨_, rfl⟩ := h
          split
          · next l hl =>
            have hpos : s₁.shape pos = some l := by
              split at hl
              · exact hl
              · cases hl
            have h₃ := SState.ShapeBelow.of_sub (SState.shapeSub_takeLabel s₂ l) h₂
            have hn : (s₂.takeLabel l).nextLoan = s.nextLoan :=
              (SState.shapeSub_takeLabel s₂ l).2.trans (hsub2.2.trans hsub.2)
            refine ⟨SState.shapeBelow_pushTempShaped h₃ _ (by rw [hn, ← hsub.2]; exact h₁ pos l hpos), ?_⟩
            rw [SState.nextLoan_pushTempShaped, hn]
          · exact ⟨h₂, hsub2.2.trans hsub.2⟩

/-! ### Its semantic companion: no meaning reads a label not yet handed out

`ShapeBelow` makes a fresh label collide with no *holder*; `ReadsBelow` makes it collide with no
*loan*: no position's meaning depends on the final content of a label at or above the counter,
so a fresh borrow's label is read only where the borrow puts it. -/

/-- A meaning as a function of the future depends on label `l` (`Mean.dependsOn`, for one
position). -/
def SVal.DependsOn (v : SVal) (l : Nat) : Prop := ∃ φ x, v φ ≠ v (φ.upd l x)

theorem SVal.not_dependsOn {v : SVal} {l : Nat} (h : ¬ v.DependsOn l) (φ : Future) (x : Sem) :
    v (φ.upd l x) = v φ :=
  Classical.byContradiction fun hne => h ⟨φ, x, Ne.symm hne⟩

/-- A meaning computed pointwise from another depends only where that one does. -/
theorem SVal.dependsOn_comp {v : SVal} {G : Sem → Sem} {l : Nat}
    (h : SVal.DependsOn (fun φ => G (v φ)) l) : v.DependsOn l := by
  refine Classical.byContradiction fun hv => ?_
  obtain ⟨φ, x, hne⟩ := h
  exact hne (by simp only [SVal.not_dependsOn hv])

theorem SVal.dependsOn_updAt {dm : DataModel} {Γ : List IndDecl} {T : TyM} {f : Sem → Sem}
    {steps : List Step} {v : SVal} {l : Nat}
    (h : SVal.DependsOn (fun φ => (Sem.updAt dm Γ T f steps (v φ)).getD .err) l) : v.DependsOn l :=
  SVal.dependsOn_comp (G := fun w => (Sem.updAt dm Γ T f steps w).getD .err) h

namespace SState

/-- No position's meaning depends on a label at or above the counter. -/
def ReadsBelow (s : SState) : Prop := ∀ p l, s.dependsOn p l → l < s.nextLoan

theorem readsBelow_endLabel {s : SState} (hs : s.ReadsBelow) (k : Nat) : (s.endLabel k).ReadsBelow := by
  cases hf : s.positions.find? (fun p => decide (s.shape p = some k)) with
  | none => rw [endLabel_of_find_none s k hf]; exact hs
  | some r =>
    intro p l hd
    rw [(shapeSub_endLabel s k).2]
    have hd' := endLabel_dependsOn hf hd
    by_cases hlk : l = k
    · subst hlk; exact hs r l (Mean.semEnd_dependsOn_self hd')
    · rcases Mean.semEnd_dependsOn hlk hd' with h | ⟨_, h⟩
      · exact hs p l h
      · exact hs r l h

theorem readsBelow_foldl_endLabel {s : SState} (hs : s.ReadsBelow) :
    ∀ ls : List Nat, (ls.foldl endLabel s).ReadsBelow := by
  intro ls
  induction ls generalizing s with
  | nil => exact hs
  | cons k ls ih => exact ih (readsBelow_endLabel hs k)

theorem readsBelow_access {s : SState} (hs : s.ReadsBelow) (p : Pos) : (s.access p).ReadsBelow := by
  rw [access_eq_rounds]
  generalize List.range s.liveLabels.length = ns
  induction ns generalizing s with
  | nil => exact hs
  | cons _ ns ih => exact ih (readsBelow_foldl_endLabel hs _)

theorem readsBelow_freshLoan {s : SState} (hs : s.ReadsBelow) : s.freshLoan.2.ReadsBelow :=
  fun p l h => Nat.lt_succ_of_lt (hs p l h)

/-- Setting a position to a meaning that reads only labels below the counter keeps the invariant. -/
theorem readsBelow_setAt {s : SState} (hs : s.ReadsBelow) (p : Pos) (v : SVal)
    (hv : ∀ l, v.DependsOn l → l < s.nextLoan) : (s.setAt p v).ReadsBelow := by
  intro q l ⟨φ, x, hne⟩
  rw [(shapeSub_setAt s p v).2]
  rcases valAt_setAt s p v q with e | e
  · exact hs q l ⟨φ, x, by simpa [toMean, e] using hne⟩
  · exact hv l ⟨φ, x, by simpa [toMean, e] using hne⟩


theorem valAt_pushTemp (s : SState) (v : SVal) (q : Pos) :
    (s.pushTemp v).valAt q = s.valAt q ∨ (s.pushTemp v).valAt q = v := by
  cases q with
  | bind f i =>
    left
    simp only [pushTemp, valAt, List.getElem?_modify]
    by_cases hf : s.topIdx = f <;> cases s.env[f]? <;> simp [hf]
  | temp f i =>
    simp only [pushTemp, valAt, List.getElem?_modify]
    by_cases hf : s.topIdx = f
    · cases hfr : s.env[f]? with
      | none => left; simp
      | some fr =>
        by_cases hi : i < fr.temps.length
        · left; simp [hf, List.getElem?_append_left hi]
        · by_cases hie : i = fr.temps.length
          · right; subst hie; simp [hf]
          · left
            have e1 : fr.temps[i]? = none := List.getElem?_eq_none (by omega)
            have e2 : (fr.temps ++ [v])[i]? = none := List.getElem?_eq_none (by simp; omega)
            simp [hf, e1, e2]
    · left; cases s.env[f]? <;> simp [hf]

theorem valAt_pushTempShaped (s : SState) (v : SVal) (l : Nat) (q : Pos) :
    (s.pushTempShaped v l).valAt q = (s.pushTemp v).valAt q := by
  unfold pushTempShaped; dsimp only; split <;> rfl

/-- Parking a meaning that reads only labels below the counter keeps the invariant. -/
theorem readsBelow_pushTempShaped {s : SState} (hs : s.ReadsBelow) (v : SVal) (l : Nat)
    (hv : ∀ l, v.DependsOn l → l < s.nextLoan) : (s.pushTempShaped v l).ReadsBelow := by
  intro q k ⟨φ, x, hne⟩
  rw [nextLoan_pushTempShaped]
  have e₀ := valAt_pushTempShaped s v l q
  rcases valAt_pushTemp s v q with e | e
  · exact hs q k ⟨φ, x, by simpa [toMean, e₀, e] using hne⟩
  · exact hv k ⟨φ, x, by simpa [toMean, e₀, e] using hne⟩
end SState

theorem contentOf_readsBelow (K : RunCtx) (φ : Future) (p : Place) (s : SState) (hs : s.ReadsBelow)
    {x : Sem × TyS × Pos × List Step} {s' : SState} (h : contentOf K φ p s = some (x, s')) :
    s'.ReadsBelow := by
  unfold contentOf at h
  split at h
  · next pos steps _ =>
    dsimp only at h
    split at h
    · cases h; exact SState.readsBelow_access hs pos
    · cases h
  · cases h

/-- **[Borrow]'s fresh label is read only where the borrow puts it**: the borrowed place reads the
fresh label, which is below the new counter, and otherwise only what it read before. Milestone 3:
`Steps/Borrow.lean`'s `borrowPlace_step`. -/
theorem borrowPlace_readsBelow (K : RunCtx) (φ : Future) (p : Place) (s : SState) (hs : s.ReadsBelow)
    {v : Sem} {T : TyS} {s' : SState} (h : borrowPlace K φ p s = some ((v, T), s')) : s'.ReadsBelow := by
  unfold borrowPlace at h
  cases hc : contentOf K φ p s with
  | none => simp [hc] at h
  | some x =>
    obtain ⟨⟨v₀, T₀, pos, steps⟩, s₁⟩ := x
    have h₁ : s₁.ReadsBelow := contentOf_readsBelow K φ p s hs hc
    simp only [hc, Option.bind_eq_bind, Option.bind_some] at h
    split at h
    · cases h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨_, rfl⟩ := h
      refine SState.readsBelow_pushTempShaped ?_ _ _ fun _ ⟨_, _, hne⟩ => absurd rfl hne
      apply SState.readsBelow_setAt (SState.readsBelow_freshLoan h₁)
      intro l hl
      show l < s₁.nextLoan + 1
      by_cases e : l = s₁.nextLoan
      · omega
      · have hold : (s₁.freshLoan.2.valAt pos).DependsOn l := by
          refine Classical.byContradiction fun hn => ?_
          obtain ⟨ψ, y, hne⟩ := hl
          apply hne
          have e2 : (ψ.upd l y) s₁.freshLoan.1 = ψ s₁.freshLoan.1 := Future.upd_other ψ y (Ne.symm e)
          simp only [SVal.not_dependsOn hn, e2]
        exact Nat.lt_succ_of_lt (h₁ pos l hold)

/-- D84's drop at the join reads no new label. -/
theorem joinDrop_readsBelow (K : RunCtx) (φ : Future) (t : Term) (s : SState) (hs : s.ReadsBelow) :
    (joinDrop K φ t s).ReadsBelow := by
  unfold joinDrop
  generalize K.D.joinMoves (scopeOf s) (movedPlaces φ s) t = qs
  induction qs generalizing s with
  | nil => exact hs
  | cons q qs ih =>
    rw [List.foldl_cons]
    apply ih
    split
    · exact hs
    · split
      · next pos steps _ =>
        have h₁ := SState.readsBelow_access hs pos
        dsimp only
        generalize s.access pos = s₁ at h₁
        rcases Sem.follow K.dm K.Γ (s₁.tyAt pos).m (s₁.valAt pos (s₁.closedFuture φ)) steps with _ | ⟨v, T⟩
        · exact h₁
        · have h₂ : (if steps.isEmpty then (match s₁.shape pos with
              | some l => s₁.endLabel l | none => s₁) else s₁).ReadsBelow := by
            split
            · split
              · exact SState.readsBelow_endLabel h₁ _
              · exact h₁
            · exact h₁
          cases v <;> first
            | exact h₁
            | exact SState.readsBelow_setAt h₂ pos _ fun l hl => h₂ pos l (SVal.dependsOn_updAt hl)
      · exact hs

end Ochr.Meaning

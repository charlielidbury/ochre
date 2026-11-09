import Ochr.Meaning.Run

/-!
# The reference run's borrow primitives lose only information (milestone 3's monotonicity)

The step lemmas of milestone 3 compare the checker's state with the reference run's, and the
reference run's own borrow primitives are steps that may only *narrow* what a state means:
[End] (`SState.endLabel`) fixes a final content and forgets the holder, [Access]
(`SState.access`) is a fold of [End]s, and D84's drop at the join (`joinDrop`) sets places to
`⊥`. This file proves each is `Below` its input, at the level `State.lean` states
`Mean.semEnd_below`: the `Mean` a semantic state forgets its types to (`SState.toMean`).

* `SState.endLabel_below`: [End] loses only information.
* `SState.access_below`: so does [Access], a fold of [End]s.
* `Mean.semEnd_comm`, `SState.endLabel_comm`: two [End]s commute when one holder's meaning does
  not depend on the other's label, which (WF3)'s acyclicity guarantees for every pair
  (`SWF3`, its semantic form); plain equality, not only `Below` both ways.
* `joinDrop_below`: the drop at the join loses only information *when every dropped place is a
  root* (its path is `*`s only). With a field in the path it is false (`joinDrop_not_below`):
  a partial move turns a whole value into an untyped tuple, which `⊑` puts below nothing but
  itself.

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
means what `Mean.semEnd` says. (A holder that is not a position of the state is never found by
`endLabel`, but nothing here needs that.) -/
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

end Ochr.Meaning

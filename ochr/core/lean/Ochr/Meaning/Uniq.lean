import Ochr.Meaning.RunPresInd

/-!
# Each borrow label has one holder (`SState.Uniq`)

The reference state holds each borrow label at ONE position: a label is made with one holder
(`borrowPlace`, a borrow-returning call: a fresh label parked in a new temporary), `takeLabel` moves
it (a move of the holder, the `let` that binds it, an assignment at a root, a call's frame), an end or
a drop removes it. Every other operation leaves the shape or only forgets entries (`ShapeSub`).

It is a fact about the reference state alone, carried by the fundamental lemma's invariant
(`Strict.SGood.uniq`, docs/31 D117); the simulation's relation carried it first (`Rel.uniq`, D114).
Its only use inside the model: `takeLabel l` (which forgets the FIRST holder `find?` meets) leaves no
holder of `l`, so the new holder is the only one.
-/

namespace Ochr.Meaning

namespace SState

/-- Each label is held at one position at most. -/
def Uniq (s : SState) : Prop := ∀ p q l, s.shape p = some l → s.shape q = some l → p = q

theorem Uniq.of_shape {s' s : SState} (h : ∀ p l, s'.shape p = some l → s.shape p = some l)
    (hu : s.Uniq) : s'.Uniq :=
  fun p q l hp hq => hu p q l (h p l hp) (h q l hq)

theorem Uniq.of_sub {s' s : SState} (h : ShapeSub s' s) (hu : s.Uniq) : s'.Uniq := hu.of_shape h.1

theorem Uniq.of_eq {s' s : SState} (h : s'.shape = s.shape) (hu : s.Uniq) : s'.Uniq :=
  hu.of_shape fun p l hp => h ▸ hp

/-- No entry at all: unique. -/
theorem uniq_of_none {s : SState} (h : ∀ p, s.shape p = none) : s.Uniq :=
  fun p _ _ hp _ => by rw [h p] at hp; cases hp

/-- A label with no holder among the positions has no shape entry (entries are at positions). -/
theorem free_of_holderOf_none {s : SState} (hsa : ShapeAt s) {l : Nat} (h : s.holderOf l = none) :
    ∀ q, s.shape q ≠ some l := by
  intro q hq
  have hp := (hsa q l hq).1
  unfold holderOf at h
  have := List.find?_eq_none.mp h q hp
  simp [hq] at this

/-- After `takeLabel l` no position holds `l`. -/
theorem takeLabel_free {s : SState} (hu : s.Uniq) (hsa : ShapeAt s) (l : Nat) :
    ∀ q, (s.takeLabel l).shape q ≠ some l := by
  intro q hq
  have hq' := takeLabel_shape_some hq
  unfold takeLabel at hq
  cases e : s.holderOf l with
  | none => exact free_of_holderOf_none hsa e q hq'
  | some r =>
    rw [e] at hq
    change (if q = r then none else s.shape q) = some l at hq
    have hr := (holderOf_spec e).2
    have := hu q r l hq' hr
    rw [if_pos this] at hq; cases hq

/-- A new holder of a label no position holds keeps the labels unique. -/
theorem Uniq.put {s' s : SState} {N : Pos} {l : Nat} (hu : s.Uniq) (hfree : ∀ q, s.shape q ≠ some l)
    (h : ∀ q, s'.shape q = if q = N then some l else s.shape q) : s'.Uniq := by
  intro p q m hp hq
  rw [h] at hp hq
  by_cases ep : p = N
  · by_cases eq : q = N
    · rw [ep, eq]
    · rw [if_pos ep] at hp; rw [if_neg eq] at hq
      cases hp; exact absurd hq (hfree q)
  · rw [if_neg ep] at hp
    by_cases eq : q = N
    · rw [if_pos eq] at hq; cases hq; exact absurd hp (hfree p)
    · rw [if_neg eq] at hq; exact hu p q m hp hq

theorem Uniq.takeLabel {s : SState} (hu : s.Uniq) (l : Nat) : (s.takeLabel l).Uniq :=
  hu.of_sub (shapeSub_takeLabel s l)

theorem Uniq.pushTempShaped {s : SState} (hu : s.Uniq) (v : SVal) {l : Nat}
    (hfree : ∀ q, s.shape q ≠ some l) : (s.pushTempShaped v l).Uniq := by
  obtain ⟨T, hT⟩ := pushTempShaped_shape s v l
  cases T with
  | none => exact hu.of_shape fun p m hp => by rw [hT] at hp; simpa using hp
  | some N => exact hu.put (N := N) hfree fun q => by rw [hT]; simp only [Option.some.injEq]

/-- A move's parking (`readPlace`, a call's frame): the label taken from its holder, then parked. -/
theorem Uniq.take_park {s : SState} (hu : s.Uniq) (hsa : ShapeAt s) (v : SVal) (l : Nat) :
    ((s.takeLabel l).pushTempShaped v l).Uniq :=
  (hu.takeLabel l).pushTempShaped v (takeLabel_free hu hsa l)

/-- The new holder at a position `pos` after `takeLabel` (`assignAt` at a root). -/
theorem Uniq.take_put {s : SState} (hu : s.Uniq) (hsa : ShapeAt s) (l : Nat) (pos : Pos) :
    ({ s.takeLabel l with shape := fun q => if q = pos then some l else (s.takeLabel l).shape q } : SState).Uniq :=
  (hu.takeLabel l).put (takeLabel_free hu hsa l) fun _ => rfl

theorem Uniq.pushBind {s : SState} (hu : s.Uniq) (b : SBinding) : (s.pushBind b).Uniq := hu.of_eq rfl
theorem Uniq.pushTemp {s : SState} (hu : s.Uniq) (v : SVal) : (s.pushTemp v).Uniq := hu.of_eq rfl
theorem Uniq.setAt {s : SState} (hu : s.Uniq) (p : Pos) (v : SVal) : (s.setAt p v).Uniq :=
  hu.of_sub (shapeSub_setAt s p v)
theorem Uniq.mapVals {s : SState} (hu : s.Uniq) (g : Pos → SVal → SVal) : (s.mapVals g).Uniq :=
  hu.of_sub (shapeSub_mapVals s g)
theorem Uniq.endLabel {s : SState} (hu : s.Uniq) (l : Nat) : (s.endLabel l).Uniq :=
  hu.of_sub (shapeSub_endLabel s l)
theorem Uniq.foldl_endLabel {s : SState} (hu : s.Uniq) (ls : List Nat) : (ls.foldl SState.endLabel s).Uniq :=
  hu.of_sub (shapeSub_foldl_endLabel ls s)
theorem Uniq.access {s : SState} (hu : s.Uniq) (p : Pos) (hit : List Step → Bool) : (s.access p hit).Uniq :=
  hu.of_sub (shapeSub_access s p hit)
theorem Uniq.dropLast {s : SState} (hu : s.Uniq) : s.dropLast.Uniq := hu.of_sub (shapeSub_dropLast s)
theorem Uniq.setLent {s : SState} (hu : s.Uniq) (l : Nat) (xs : List Site) : (s.setLent l xs).Uniq :=
  hu.of_eq rfl
theorem Uniq.endAt {s : SState} (hu : s.Uniq) (l : Nat) (r : Pos) : (s.endAt l r).Uniq :=
  hu.of_shape fun p m hp => by
    rw [endAt_shape] at hp; simp only at hp; split at hp
    · cases hp
    · exact hp

end SState

/-- The `let`'s binding (`pushBindShaped`): the label taken from its holder, the binding its holder. -/
theorem SState.Uniq.pushBindShaped {s : SState} (hu : s.Uniq) (hsa : SState.ShapeAt s) (b : SBinding) :
    (pushBindShaped s b).Uniq := by
  unfold Ochr.Meaning.pushBindShaped
  split
  · next l _ =>
    dsimp only
    split
    · exact ((hu.takeLabel l).pushBind b).put (SState.takeLabel_free hu hsa l) fun _ => rfl
    · exact (hu.takeLabel l).pushBind b
  · exact hu.pushBind b

end Ochr.Meaning

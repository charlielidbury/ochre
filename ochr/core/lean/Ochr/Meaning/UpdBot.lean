import Ochr.Meaning.SitesWrite

/-!
# Writing `⊥` at a path, on values: what it keeps (L3's bookkeeping)

The checker's write of `⊥` at a path (`Value.updAt (fun _ => ⊥)`) adds no atom other than `⊥`: an
atom the written value has, whose test does not look below a constructor, a borrow, a mark or a
successor, the value had before (`anyAtom_of_updAt_bot`). At a non-empty path the top constructor
is kept (`updAt_bot_top`). These give the relation's `fresh`, `inj` and holder clauses after the
write (`botWrite_step`).
-/

namespace Ochr.Meaning

/-- A test on atoms that reads a constructor value, a borrow, a mark or a successor by its own data
only, never by what it holds, and is false of `⊥`. -/
structure ShallowAtom (P : Value → Bool) : Prop where
  bot : P .bot = false
  ind : ∀ ty c h ps fs fs', P (.ind ty c h ps fs) = P (.ind ty c h ps fs')
  borrow : ∀ m w w', P (.borrow m w) = P (.borrow m w')
  gloan : ∀ m w w', P (.gloan m w) = P (.gloan m w')
  succ : ∀ w w', P (.succ w) = P (.succ w')

theorem anyAtomList_set {P : Value → Bool} : ∀ (fs : List Value) (i : Nat) (w w' : Value), fs[i]? = some w →
    (w'.anyAtom P = true → w.anyAtom P = true) →
    Value.anyAtomList P (fs.set i w') = true → Value.anyAtomList P fs = true
  | [], _, _, _, h, _, _ => by simp at h
  | x :: xs, 0, w, w', h, hw, ha => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    simp only [List.set_cons_zero, Value.anyAtomList, Bool.or_eq_true] at ha ⊢
    rcases ha with ha | ha
    · exact .inl (hw ha)
    · exact .inr ha
  | x :: xs, i + 1, w, w', h, hw, ha => by
    simp only [List.getElem?_cons_succ] at h
    simp only [List.set_cons_succ, Value.anyAtomList, Bool.or_eq_true] at ha ⊢
    rcases ha with ha | ha
    · exact .inl ha
    · exact .inr (anyAtomList_set xs i w w' h hw ha)

/-- **Writing `⊥` adds no atom** a shallow test sees. -/
theorem anyAtom_of_updAt_bot {P : Value → Bool} (hP : ShallowAtom P) :
    ∀ (steps : List Step) (v v' : Value), Value.updAt (fun _ => .bot) steps v = some v' →
      v'.anyAtom P = true → v.anyAtom P = true
  | [], v, v', h, ha => by
    simp only [Value.updAt, Option.some.injEq] at h
    subst h
    simp [Value.anyAtom, hP.bot] at ha
  | st :: ss, v, v', h, ha => by
    cases v with
    | gloan m w =>
      simp only [Value.updAt] at h
      obtain ⟨w', hw', rfl⟩ := Option.map_eq_some_iff.mp h
      rw [Value.anyAtom] at ha ⊢
      simp only [← hP.gloan m w w', Bool.or_eq_true] at ha ⊢
      rcases ha with ha | ha
      · exact .inl ha
      · exact .inr (anyAtom_of_updAt_bot hP (st :: ss) w w' hw' ha)
    | borrow m w =>
      cases st with
      | deref =>
        simp only [Value.updAt] at h
        obtain ⟨w', hw', rfl⟩ := Option.map_eq_some_iff.mp h
        rw [Value.anyAtom] at ha ⊢
        simp only [← hP.borrow m w w', Bool.or_eq_true] at ha ⊢
        rcases ha with ha | ha
        · exact .inl ha
        · exact .inr (anyAtom_of_updAt_bot hP ss w w' hw' ha)
      | proj _ | field _ => simp [Value.updAt] at h
    | succ w =>
      cases st with
      | proj i =>
        cases i with
        | zero =>
          simp only [Value.updAt] at h
          obtain ⟨w', hw', rfl⟩ := Option.map_eq_some_iff.mp h
          rw [Value.anyAtom] at ha ⊢
          simp only [← hP.succ w w', Bool.or_eq_true] at ha ⊢
          rcases ha with ha | ha
          · exact .inl ha
          · exact .inr (anyAtom_of_updAt_bot hP ss w w' hw' ha)
        | succ _ => simp [Value.updAt] at h
      | deref | field _ => simp [Value.updAt] at h
    | ind ty c hh ps fs =>
      obtain ⟨-, w, w', hw, hw', rfl⟩ := updAt_ind_inv h
      rw [Value.anyAtom] at ha ⊢
      simp only [hP.ind ty c hh ps (fs.set st.fieldIdx w') fs, Bool.or_eq_true] at ha ⊢
      rcases ha with ha | ha | ha
      · exact .inl ha
      · exact .inr (.inl ha)
      · exact .inr (.inr (anyAtomList_set fs st.fieldIdx w w' hw
          (anyAtom_of_updAt_bot hP ss w w' hw') ha))
    | _ => simp [Value.updAt] at h
termination_by steps v => (steps.length, sizeOf v)

/-- The label of the borrow a value is, if it is one (`Env.shape` of the position holding it). -/
def topLabel : Value → Option Nat
  | .borrow l _ => some l
  | _ => none

/-- At a non-empty path the written value's top is the old one's: a borrow stays the same borrow. -/
theorem updAt_bot_top {st : Step} {ss : List Step} {v v' : Value}
    (h : Value.updAt (fun _ => .bot) (st :: ss) v = some v') : topLabel v' = topLabel v := by
  cases v with
  | gloan m w =>
    simp only [Value.updAt] at h
    obtain ⟨w', -, rfl⟩ := Option.map_eq_some_iff.mp h
    rfl
  | borrow m w =>
    cases st with
    | deref =>
      simp only [Value.updAt] at h
      obtain ⟨w', -, rfl⟩ := Option.map_eq_some_iff.mp h
      rfl
    | proj _ | field _ => simp [Value.updAt] at h
  | succ w =>
    cases st with
    | proj i =>
      cases i with
      | zero =>
        simp only [Value.updAt] at h
        obtain ⟨w', -, rfl⟩ := Option.map_eq_some_iff.mp h
        rfl
      | succ _ => simp [Value.updAt] at h
    | deref | field _ => simp [Value.updAt] at h
  | ind ty c hh ps fs =>
    obtain ⟨-, w, w', -, -, rfl⟩ := updAt_ind_inv h
    rfl
  | _ => simp [Value.updAt] at h

end Ochr.Meaning

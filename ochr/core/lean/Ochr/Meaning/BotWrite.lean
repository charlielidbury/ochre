import Ochr.Meaning.Places
import Ochr.Meaning.Value

/-!
# Writing `⊥` at a path, on meanings (L2; docs/31 D28, D29 point 5 e, D31)

The checker's [Drop] and [Move] write `⊥` at a path of a value (`Value.updAt (fun _ => ⊥)`); the
reference writes `moved` at the same path of the value's meaning (`Sem.updAt … (fun _ => moved)`).
`mean_updAt_bot` says the two agree: the meaning of the written value is the written meaning.

It needs three things of the value, each a fact about reachable states:
- it records its parameters and holds no sealed program (`RecPlain`: (WF10), and what a drop or a
  move writes into, which the access before it has made a plain value), so a field after the
  written one means the same though the earlier fields it is typed at have changed (the audit's
  A13 closed by D29's point 5 e: no value in Ω reads a hint but its own);
- the hint names, at each constructor value on the path, the value's own declaration at its
  recorded parameters' meanings (`DataOn`: docs/31 D31, the data agreement a binding's type and
  the fields' hints have with the values they hold), the declaration being data, not `Prop`;
- at each `S` on the path, the predecessor means a number (a write below a partly moved number has
  no meaning in the reference: `Sem.updAt` steps into a number only).
-/

namespace Ochr.Meaning

section
variable (dm : DataModel) (C : CodeMeaning) (Γ : List IndDecl) (ρ : Assignment) (φ : Future)

/-- A value records its parameters and holds no sealed program: its meaning reads no hint but
its own (`mean_hintFree`). -/
def RecPlain (v : Value) : Prop := v.anyAtom (Value.bareCtor Γ) = false ∧ v.anyAtom Value.isSealed = false

theorem recPlain_ind {ty : String} {c : Nat} {h : Hint} {ps fs : List Value}
    (hv : RecPlain Γ (.ind ty c h ps fs)) : Value.bareCtor Γ (.ind ty c h ps fs) = false ∧
      ∀ x ∈ fs, RecPlain Γ x := by
  obtain ⟨hb, hs⟩ := hv
  simp only [Value.anyAtom, Bool.or_eq_false_iff] at hb hs
  refine ⟨hb.1, fun x hx => ⟨?_, ?_⟩⟩
  · have := hb.2.2; clear hb hs
    induction fs with
    | nil => cases hx
    | cons y ys ih =>
      simp only [Value.anyAtomList, Bool.or_eq_false_iff] at this
      rcases List.mem_cons.mp hx with rfl | hx
      · exact this.1
      · exact ih hx this.2
  · have := hs.2.2; clear hb hs
    induction fs with
    | nil => cases hx
    | cons y ys ih =>
      simp only [Value.anyAtomList, Bool.or_eq_false_iff] at this
      rcases List.mem_cons.mp hx with rfl | hx
      · exact this.1
      · exact ih hx this.2

/-- **A recorded, unsealed value means the same at every hint** (`Value.mean`'s form of
`hintFree_of_recorded`). -/
theorem mean_hintFree : ∀ (w : Value), RecPlain Γ w → ∀ h h',
    Value.mean dm C Γ ρ φ h w = Value.mean dm C Γ ρ φ h' w
  | .borrow l w, ⟨hb, hs⟩ => by
    intro h h'
    simp only [Value.anyAtom, Value.bareCtor, Value.isSealed, Bool.false_or] at hb hs
    simp only [Value.mean]; exact mean_hintFree w ⟨hb, hs⟩ h h'
  | .gloan l w, ⟨hb, hs⟩ => by
    intro h h'
    simp only [Value.anyAtom, Value.bareCtor, Value.isSealed, Bool.false_or] at hb hs
    simp only [Value.mean]; exact mean_hintFree w ⟨hb, hs⟩ h h'
  | .ind ty c hd ps fs, ⟨hb, _⟩ => by
    intro h h'
    simp only [Value.mean]
    cases ps with
    | nil =>
      simp only [Value.anyAtom, Value.bareCtor] at hb
      split
      · next d hd' =>
        rw [hd'] at hb
        have hpe : d.params.isEmpty = true := by
          cases h : d.params.isEmpty <;> simp [h] at hb ⊢
        simp [hpe]
      · rfl
    | cons p ps => simp
  | .sealed _, ⟨_, hs⟩ => by simp [Value.anyAtom, Value.isSealed] at hs
  | .zero, _ | .unit, _ | .gfn _, _ | .clo _ _ _, _ | .loan _, _ | .bot, _
  | .abs _, _ | .proof, _ | .tNat, _ | .tUnit, _ | .tEq _ _ _, _ | .tRef _, _
  | .tPi _ _ _, _ | .sort _, _ | .tInd _ _, _ | .succ _, _ => fun _ _ => by simp only [Value.mean]

theorem fieldHint_eq (d : IndDecl) (ps : List Sem) (c i : Nat) (e : List Sem) :
    fieldHint dm d ps c i e = ⟨dm.fieldTy d ps c i e, none, none, dm.fieldData d ps c i e⟩ := rfl

/-- Fields that record their parameters and hold no sealed program mean the same whatever the
earlier fields they are typed at. -/
theorem meanFields_earlier (d : IndDecl) (ps : List Sem) (c : Nat) :
    ∀ (fs : List Value) (k : Nat) (e e' : List Sem), (∀ x ∈ fs, RecPlain Γ x) →
      Value.meanFields dm C Γ ρ φ d ps c k e fs = Value.meanFields dm C Γ ρ φ d ps c k e' fs
  | [], _, _, _, _ => by simp [Value.meanFields]
  | x :: xs, k, e, e', h => by
    simp only [Value.meanFields]
    have hx := mean_hintFree dm C Γ ρ φ x (h x (List.mem_cons_self ..))
      ⟨dm.fieldTy d ps c k e, none, none, dm.fieldData d ps c k e⟩
      ⟨dm.fieldTy d ps c k e', none, none, dm.fieldData d ps c k e'⟩
    rw [hx, meanFields_earlier d ps c xs (k + 1) _ (e' ++ _) (fun y hy => h y (List.mem_cons_of_mem _ hy))]

/-- Field `i`'s meaning is its value read at its hint, after the earlier fields. -/
theorem meanFields_getElem? (d : IndDecl) (ps : List Sem) (c : Nat) :
    ∀ (fs : List Value) (k : Nat) (e : List Sem) (i : Nat) (w : Value), fs[i]? = some w →
      (Value.meanFields dm C Γ ρ φ d ps c k e fs)[i]? =
        some (Value.mean dm C Γ ρ φ (fieldHint dm d ps c (k + i) (e ++ (Value.meanFields dm C Γ ρ φ d ps c k e fs).take i)) w)
  | [], _, _, _, _, h => by simp at h
  | x :: xs, k, e, 0, w, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    simp [Value.meanFields, fieldHint_eq]
  | x :: xs, k, e, i + 1, w, h => by
    simp only [List.getElem?_cons_succ] at h
    simp only [Value.meanFields, List.getElem?_cons_succ, List.take_succ_cons]
    rw [meanFields_getElem? d ps c xs (k + 1) _ i w h]
    simp only [List.append_assoc, List.singleton_append, Nat.add_right_comm k 1 i, Nat.add_assoc]

/-- **Writing field `i`**: the fields' meanings are the old ones with field `i` replaced by the new
value read at field `i`'s hint, when every field records its parameters and holds no sealed
program (a later field is typed at the changed earlier fields, and does not read its type). -/
theorem meanFields_set (d : IndDecl) (ps : List Sem) (c : Nat) :
    ∀ (fs : List Value) (k : Nat) (e : List Sem) (i : Nat) (w : Value), i < fs.length → (∀ x ∈ fs, RecPlain Γ x) →
      Value.meanFields dm C Γ ρ φ d ps c k e (fs.set i w) =
        (Value.meanFields dm C Γ ρ φ d ps c k e fs).set i
          (Value.mean dm C Γ ρ φ (fieldHint dm d ps c (k + i) (e ++ (Value.meanFields dm C Γ ρ φ d ps c k e fs).take i)) w)
  | [], _, _, _, _, hi, _ => by simp at hi
  | x :: xs, k, e, 0, w, _, h => by
    simp only [List.set_cons_zero, Value.meanFields, List.set_cons_zero, fieldHint_eq, Nat.add_zero,
      List.take_zero, List.append_nil, List.cons.injEq, true_and]
    exact meanFields_earlier dm C Γ ρ φ d ps c xs (k + 1) _ _ (fun y hy => h y (List.mem_cons_of_mem _ hy))
  | x :: xs, k, e, i + 1, w, hi, h => by
    simp only [List.set_cons_succ, Value.meanFields, List.take_succ_cons, List.cons.injEq, true_and]
    rw [meanFields_set d ps c xs (k + 1) _ i w (by simpa using hi) (fun y hy => h y (List.mem_cons_of_mem _ hy))]
    simp only [List.append_assoc, List.singleton_append, Nat.add_right_comm k 1 i, Nat.add_assoc]

theorem Sem.asNat_some {s : Sem} {n : Nat} (h : s.asNat = some n) : s = .el0 Nat n := by
  unfold Sem.asNat Sem.as at h
  split at h
  · rename_i B b
    split at h
    · rename_i hB; subst hB; cases h; rfl
    · cases h
  · cases h

theorem Sem.asNat_el0 (n : Nat) : (Sem.el0 Nat n).asNat = some n := by simp [Sem.asNat, Sem.as]

theorem Sem.succ_el0 (n : Nat) : (Sem.el0 Nat n).succ = .el0 Nat (n + 1) := by
  simp [Sem.succ, Sem.asNat_el0]

/-- The field a step names, as `Sem.updAt` reads it. -/
def _root_.Ochr.Step.fieldIdx : Step → Nat
  | .proj i => i
  | .field g => g.idx
  | .deref => 0

theorem _root_.Ochr.Step.fieldIdx_eq (st : Step) :
    (match st with | .proj i => i | .field g => g.idx | .deref => 0) = st.fieldIdx := by cases st <;> rfl

/-- Writing at a path of a constructor value writes one field. -/
theorem updAt_ind_inv {f : Value → Value} {st : Step} {ss : List Step} {ty : String} {c : Nat} {hh : Hint}
    {ps fs : List Value} {v' : Value} (h : Value.updAt f (st :: ss) (.ind ty c hh ps fs) = some v') :
    st ≠ .deref ∧ ∃ w w', fs[st.fieldIdx]? = some w ∧ Value.updAt f ss w = some w' ∧
      v' = .ind ty c hh ps (fs.set st.fieldIdx w') := by
  cases st with
  | deref => simp [Value.updAt] at h
  | proj i =>
    cases c with
    | zero =>
      simp only [Value.updAt] at h
      split at h
      · rename_i w hw
        obtain ⟨w', hw', rfl⟩ := Option.map_eq_some_iff.mp h
        exact ⟨nofun, w, w', hw, hw', rfl⟩
      · cases h
    | succ c => simp [Value.updAt] at h
  | field g =>
    simp only [Value.updAt] at h
    split at h
    · rename_i w hw
      obtain ⟨w', hw', rfl⟩ := Option.map_eq_some_iff.mp h
      have hw2 : fs[g.idx]? = some w := by
        split at hw
        · exact hw
        · cases hw
      exact ⟨nofun, w, w', hw2, hw', rfl⟩
    · cases h

/-- A constructor value that records its parameters, of a data declaration, means its packing. -/
theorem mean_ind {H : TyS} {ty : String} {c : Nat} {hh : Hint} {ps fs : List Value} {d : IndDecl}
    (hf : Γ.find? (·.name == ty) = some d) (hb : Value.bareCtor Γ (.ind ty c hh ps fs) = false)
    (hs : d.sort ≠ 0) :
    Value.mean dm C Γ ρ φ H (.ind ty c hh ps fs) =
      dm.ctorM d (Value.meanParams dm C Γ ρ φ d 0 [] ps) c
        (Value.meanFields dm C Γ ρ φ d (Value.meanParams dm C Γ ρ φ d 0 [] ps) c 0 [] fs) := by
  have hbare : (ps.isEmpty && !d.params.isEmpty) = false := by
    cases ps with
    | nil => simp only [Value.bareCtor, hf] at hb; simp [hb]
    | cons _ _ => rfl
  have hs' : (d.sort == 0) = false := by simpa using hs
  simp only [Value.mean, hf, hbare, Bool.false_eq_true, ↓reduceIte, hs']

/-- **The hint decodes the value along the path as the value is built** (docs/31 D31): at each
constructor value on the path, `H` names the value's own declaration (data, not `Prop`, covered by
the model) at its recorded parameters' meanings, and the field stepped into is decoded at its own
hint; at each `S`, `H` is `Nat` and the predecessor means a number. Marks and `*` are transparent.
This is the data agreement a binding's type and the fields' hints have with the values they hold
(a typing fact of the checker, to be a clause of `Good`), read along one path. -/
def DataOn : TyS → List Step → Value → Prop
  | _, [], _ => True
  | H, .deref :: ss, .borrow _ w => DataOn H ss w
  | H, st :: ss, .gloan _ w => DataOn H (st :: ss) w
  | H, .proj 0 :: ss, .succ w =>
    H.isNat Γ ∧ (∃ n, (Value.mean dm C Γ ρ φ (.plain (.ty0 Nat)) w).asNat = some n) ∧
      DataOn (.plain (.ty0 Nat)) ss w
  | H, st :: ss, .ind ty c _ ps fs =>
    ∃ d, Γ.find? (·.name == ty) = some d ∧ dm.covers d ∧ d.sort ≠ 0 ∧
      H.dataDecl Γ = some (d, Value.meanParams dm C Γ ρ φ d 0 [] ps) ∧
      ∀ w, fs[st.fieldIdx]? = some w →
        DataOn (fieldHint dm d (Value.meanParams dm C Γ ρ φ d 0 [] ps) c st.fieldIdx
          ((Value.meanFields dm C Γ ρ φ d (Value.meanParams dm C Γ ρ φ d 0 [] ps) c 0 [] fs).take st.fieldIdx)) ss w
  | _, _, _ => False
termination_by _ ss v => (ss.length, sizeOf v)

theorem recPlain_of_mark {l : Nat} {w : Value} (h : RecPlain Γ (.gloan l w)) : RecPlain Γ w := by
  obtain ⟨hb, hs⟩ := h
  simp only [Value.anyAtom, Value.bareCtor, Value.isSealed, Bool.false_or] at hb hs
  exact ⟨hb, hs⟩

theorem recPlain_of_borrow {l : Nat} {w : Value} (h : RecPlain Γ (.borrow l w)) : RecPlain Γ w := by
  obtain ⟨hb, hs⟩ := h
  simp only [Value.anyAtom, Value.bareCtor, Value.isSealed, Bool.false_or] at hb hs
  exact ⟨hb, hs⟩

theorem recPlain_of_succ {w : Value} (h : RecPlain Γ (.succ w)) : RecPlain Γ w := by
  obtain ⟨hb, hs⟩ := h
  simp only [Value.anyAtom, Value.bareCtor, Value.isSealed, Bool.false_or] at hb hs
  exact ⟨hb, hs⟩

theorem Sem.updAt_nil' (T : TyS) (f : Sem → Sem) (s : Sem) : Sem.updAt dm Γ T f [] s = some (f s) := by
  rw [Sem.updAt.eq_def]

theorem Sem.updAt_deref' (T : TyS) (f : Sem → Sem) (sts : List Step) (s : Sem) :
    Sem.updAt dm Γ T f (.deref :: sts) s = Sem.updAt dm Γ T f sts s := by
  rw [Sem.updAt.eq_def]

theorem Sem.updAt_nat' (T : TyS) (f : Sem → Sem) (sts : List Step) (s : Sem) (n : Nat)
    (hT : T.isNat Γ) (hs : s.asNat = some (n + 1)) :
    Sem.updAt dm Γ T f (.proj 0 :: sts) s = (Sem.updAt dm Γ (.plain (.ty0 Nat)) f sts (.el0 Nat n)).map Sem.succ := by
  rw [Sem.updAt.eq_def]
  simp only [hT, ↓reduceIte, hs]

theorem Sem.updAt_data' (T : TyS) (f : Sem → Sem) (st : Step) (sts : List Step) (s : Sem) {d : IndDecl}
    {ps : List Sem} {c : Nat} {fs : List Sem} {fi : Sem}
    (hst : st ≠ .deref) (hd : T.dataDecl Γ = some (d, ps))
    (hf : dm.fieldsOf d ps s = some (c, fs)) (hi : fs[st.fieldIdx]? = some fi) :
    Sem.updAt dm Γ T f (st :: sts) s =
      (Sem.updAt dm Γ (fieldHint dm d ps c st.fieldIdx (fs.take st.fieldIdx)) f sts fi).map fun fi' =>
        dm.ctorM d ps c (fs.set st.fieldIdx fi') := by
  cases st with
  | deref => exact absurd rfl hst
  | proj i =>
    have hT : ¬ T.isNat Γ := fun h => by rw [h.1] at hd; cases hd
    rw [Sem.updAt.eq_def]
    simp only [hT, ↓reduceIte, hd, hf]
    simp only [Step.fieldIdx] at hi ⊢
    simp only [hi]
  | field g =>
    have hT : ¬ T.isNat Γ := fun h => by rw [h.1] at hd; cases hd
    rw [Sem.updAt.eq_def]
    simp only [hT, ↓reduceIte, hd, hf]
    simp only [Step.fieldIdx] at hi ⊢
    simp only [hi]

/-- **L2: writing `⊥` at a path commutes with the meaning** (docs/31 D28, D29 point 5 e, D31): the
meaning of the checker's written value is the reference's written meaning, for a value that records
its parameters and holds no sealed program, read at a hint that decodes it along the path. -/
theorem mean_updAt_bot : ∀ (steps : List Step) (H : TyS) (v v' : Value),
    Value.updAt (fun _ => .bot) steps v = some v' → RecPlain Γ v → DataOn dm C Γ ρ φ H steps v →
    Sem.updAt dm Γ H (fun _ => .moved) steps (Value.mean dm C Γ ρ φ H v) =
      some (Value.mean dm C Γ ρ φ H v')
  | [], H, v, v', h, _, _ => by
    simp only [Value.updAt, Option.some.injEq] at h
    subst h
    simp only [Sem.updAt_nil', Value.mean]
  | st :: ss, H, v, v', h, hv, hd => by
    cases v with
    | gloan l w =>
      simp only [Value.updAt] at h
      obtain ⟨w', hw', rfl⟩ := Option.map_eq_some_iff.mp h
      have hd' : DataOn dm C Γ ρ φ H (st :: ss) w := by cases st <;> simpa [DataOn] using hd
      simp only [Value.mean]
      exact mean_updAt_bot (st :: ss) H w w' hw' (recPlain_of_mark Γ hv) hd'
    | borrow l w =>
      cases st with
      | deref =>
        simp only [Value.updAt] at h
        obtain ⟨w', hw', rfl⟩ := Option.map_eq_some_iff.mp h
        have hd' : DataOn dm C Γ ρ φ H ss w := by simpa [DataOn] using hd
        simp only [Value.mean, Sem.updAt_deref']
        exact mean_updAt_bot ss H w w' hw' (recPlain_of_borrow Γ hv) hd'
      | proj i => simp [Value.updAt] at h
      | field g => simp [Value.updAt] at h
    | succ w =>
      cases st with
      | proj i =>
        cases i with
        | zero =>
          simp only [Value.updAt] at h
          obtain ⟨w', hw', rfl⟩ := Option.map_eq_some_iff.mp h
          obtain ⟨hH, ⟨n, hn⟩, hd'⟩ : H.isNat Γ ∧ (∃ n, (Value.mean dm C Γ ρ φ (.plain (.ty0 Nat)) w).asNat = some n) ∧
              DataOn dm C Γ ρ φ (.plain (.ty0 Nat)) ss w := by simpa [DataOn] using hd
          have IH := mean_updAt_bot ss (.plain (.ty0 Nat)) w w' hw' (recPlain_of_succ Γ hv) hd'
          rw [Sem.asNat_some hn] at IH
          simp only [Value.mean, Sem.asNat_some hn, Sem.succ_el0]
          rw [Sem.updAt_nat' dm Γ H _ ss _ n hH (Sem.asNat_el0 (n + 1)), IH, Option.map_some]
        | succ i => simp [Value.updAt] at h
      | deref => simp [Value.updAt] at h
      | field g => simp [Value.updAt] at h
    | ind ty c hh ps fs =>
      obtain ⟨hst, w, w', hw, hw', rfl⟩ := updAt_ind_inv h
      obtain ⟨d, hf, hcov, hsort, hdata, hrec⟩ : ∃ d, Γ.find? (·.name == ty) = some d ∧ dm.covers d ∧
          d.sort ≠ 0 ∧ H.dataDecl Γ = some (d, Value.meanParams dm C Γ ρ φ d 0 [] ps) ∧
          ∀ w, fs[st.fieldIdx]? = some w →
            DataOn dm C Γ ρ φ (fieldHint dm d (Value.meanParams dm C Γ ρ φ d 0 [] ps) c st.fieldIdx
              ((Value.meanFields dm C Γ ρ φ d (Value.meanParams dm C Γ ρ φ d 0 [] ps) c 0 [] fs).take st.fieldIdx)) ss w := by
        cases st with
        | deref => exact absurd rfl hst
        | proj i => simpa only [DataOn] using hd
        | field g => simpa only [DataOn] using hd
      obtain ⟨hbare, hfs⟩ := recPlain_ind Γ hv
      have hbare' : Value.bareCtor Γ (.ind ty c hh ps (fs.set st.fieldIdx w')) = false := by
        cases ps <;> simp only [Value.bareCtor] at hbare ⊢ <;> exact hbare
      have hi : st.fieldIdx < fs.length := (List.getElem?_eq_some_iff.mp hw).1
      have hget := meanFields_getElem? dm C Γ ρ φ d (Value.meanParams dm C Γ ρ φ d 0 [] ps) c fs 0 [] st.fieldIdx w hw
      have hset := meanFields_set dm C Γ ρ φ d (Value.meanParams dm C Γ ρ φ d 0 [] ps) c fs 0 [] st.fieldIdx w' hi hfs
      simp only [Nat.zero_add, List.nil_append] at hget hset
      have IH := mean_updAt_bot ss _ w w' hw' (hfs w (List.mem_of_getElem? hw)) (hrec w hw)
      rw [mean_ind dm C Γ ρ φ hf hbare hsort, mean_ind dm C Γ ρ φ hf hbare' hsort, hset,
        Sem.updAt_data' dm Γ H _ st ss _ hst hdata (dm.fieldsOf_ctorM c _ hcov) hget, IH, Option.map_some]
    | _ => simp [Value.updAt] at h
termination_by steps _ v => (steps.length, sizeOf v)

end

end Ochr.Meaning

import Ochr.Meaning.DataModel.Exists.Knot.Grammar

/-!
# What `nestableSet` computes (exists8, step 2)

`Check.nestableSet` (D107, D120, D121) starts from the type parameters that are passed to no
declaration of the other sort, and removes, each round, those that occur somewhere other than at a
nestable position of a field type, the table of the round's own set read for `d`; it stops when a
round removes none, after at most `np` rounds. `nestableSet_spec`: every parameter in the result is a
type parameter, passed to no declaration of the other sort, and occurs only nestably in every field
type, read against the result itself (a post-fixpoint).
-/

namespace Ochr.Meaning.DataModel.Exists.Knot

open Ochr

/-- The set before the rounds: the type parameters passed to no declaration of the other sort. -/
def nsInit (st : SortTable) (d : IndDecl) : List Bool :=
  (List.range d.params.length).map fun i => d.paramIsType i &&
    !(true && !(d.ctors.zipIdx.all fun ((_, fields), c) => fields.all fun (_, FT) =>
      !FT.passOther st d.sort (d.deepVars c) (d.params.length - 1 - i)))

/-- One round: keep the parameters that occur only nestably, read against the round's set. -/
def nsStep (nest : NestTable) (d : IndDecl) (cur : List Bool) : List Bool :=
  (List.range d.params.length).map fun i => cur.getD i false &&
    d.ctors.zipIdx.all fun ((_, fields), c) => fields.all fun (_, FT) =>
      FT.nestOk (fun m j => if m == d.name then cur.getD j false else nest m j) (d.deepVars c) (d.params.length - 1 - i)

/-- The rounds, as a recursive function: at most `m`, stopping when one changes nothing. -/
def nsIter (step : List Bool → List Bool) : Nat → List Bool → List Bool
  | 0, S => S
  | m + 1, S => if step S == S then S else nsIter step m (step S)

theorem forIn_nsIter (step : List Bool → List Bool) : ∀ (l : List Nat) (S : List Bool),
    (Id.run (forIn l S fun _ r => do
      let S' := step r
      if S' == r then pure (ForInStep.done r) else pure (ForInStep.yield S'))) = nsIter step l.length S
  | [], _ => rfl
  | _ :: l, S => by
    simp only [List.forIn_cons, Id.run, nsIter, List.length_cons]
    split
    · rfl
    · exact forIn_nsIter step l _

theorem nestableSet_eq (nest : NestTable) (st : SortTable) (d : IndDecl) :
    nestableSet nest st d = nsIter (nsStep nest d) d.params.length (nsInit st d) := by
  unfold nestableSet
  have h := forIn_nsIter (nsStep nest d) (List.range' 0 d.params.length) (nsInit st d)
  simp only [List.length_range'] at h
  rw [← h]
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Id.run, bind_pure]
  simp only [ite_true, Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]; rfl

theorem getD_map_range {f : Nat → Bool} {n i : Nat} : ((List.range n).map f).getD i false = (decide (i < n) && f i) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map]
  by_cases h : i < n
  · simp [h]
  · rw [List.getElem?_eq_none (by simpa using h)]; simp [h]

/-- The number of parameters in a set. -/
def nsCount (np : Nat) (S : List Bool) : Nat := ((List.range np).filter fun i => S.getD i false).length

theorem nsStep_le {nest : NestTable} {d : IndDecl} {S : List Bool} {i : Nat}
    (h : (nsStep nest d S).getD i false = true) : S.getD i false = true := by
  unfold nsStep at h
  rw [getD_map_range] at h
  simp only [Bool.and_eq_true] at h
  exact h.2.1

theorem nsStep_length (nest : NestTable) (d : IndDecl) (S : List Bool) : (nsStep nest d S).length = d.params.length := by
  simp [nsStep]

theorem filter_lt {n : Nat} {p q : Nat → Bool} (hle : ∀ i, p i = true → q i = true) {k : Nat} (hk : k < n)
    (hp : p k = false) (hq : q k = true) : ((List.range n).filter p).length < ((List.range n).filter q).length := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [List.range_succ, List.filter_append, List.filter_append, List.length_append, List.length_append]
    by_cases hkn : k < n
    · have h1 := ih hkn
      have h2 : ([n].filter p).length ≤ ([n].filter q).length := by
        cases hpn : p n
        · simp [hpn]
        · simp [hpn, hle n hpn]
      omega
    · have hk' : k = n := by omega
      subst hk'
      have h1 : ((List.range k).filter p).length ≤ ((List.range k).filter q).length :=
        List.Sublist.length_le (by
          rw [show (List.range k).filter p = ((List.range k).filter q).filter p by
            rw [List.filter_filter]; congr 1; funext i; cases hpi : p i <;> simp [hpi, hle i]]
          exact List.filter_sublist)
      simp [hp, hq]
      omega

/-- A round that changes the set removes a parameter. -/
theorem nsStep_count {nest : NestTable} {d : IndDecl} {S : List Bool} (hl : S.length = d.params.length)
    (hne : (nsStep nest d S == S) = false) :
    nsCount d.params.length (nsStep nest d S) < nsCount d.params.length S := by
  have hex : ∃ k, k < d.params.length ∧ (nsStep nest d S).getD k false = false ∧ S.getD k false = true := by
    refine Classical.byContradiction fun hn => ?_
    have heq : nsStep nest d S = S := by
      apply List.ext_getElem (by rw [nsStep_length, hl])
      intro k h1 h2
      have hk : k < d.params.length := by rw [nsStep_length] at h1; exact h1
      have e1 : (nsStep nest d S).getD k false = (nsStep nest d S)[k] := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1]; rfl
      have e2 : S.getD k false = S[k] := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]; rfl
      rw [← e1, ← e2]
      cases hs : (nsStep nest d S).getD k false
      · cases hS : S.getD k false
        · rfl
        · exact absurd ⟨k, hk, hs, hS⟩ hn
      · exact (nsStep_le hs).symm
    rw [heq] at hne
    simp at hne
  obtain ⟨k, hk, h1, h2⟩ := hex
  exact filter_lt (fun i hi => nsStep_le hi) hk h1 h2

/-- **The rounds end at a fixed point or at the empty set**, below where they started. -/
theorem nsIter_spec (nest : NestTable) (d : IndDecl) : ∀ (m : Nat) (S : List Bool), S.length = d.params.length →
    (nsIter (nsStep nest d) m S).length = d.params.length ∧
    (∀ i, (nsIter (nsStep nest d) m S).getD i false = true → S.getD i false = true) ∧
    (nsStep nest d (nsIter (nsStep nest d) m S) = nsIter (nsStep nest d) m S ∨
      nsCount d.params.length (nsIter (nsStep nest d) m S) + m ≤ nsCount d.params.length S)
  | 0, S, hl => ⟨hl, fun _ h => h, .inr (by simp [nsIter])⟩
  | m + 1, S, hl => by
    simp only [nsIter]
    split
    · rename_i he
      exact ⟨hl, fun _ h => h, .inl (by simpa using he)⟩
    · rename_i he
      obtain ⟨h1, h2, h3⟩ := nsIter_spec nest d m (nsStep nest d S) (nsStep_length nest d S)
      have hc := nsStep_count hl (by simpa using he)
      refine ⟨h1, fun i h => nsStep_le (h2 i h), ?_⟩
      rcases h3 with h3 | h3
      · exact .inl h3
      · exact .inr (by omega)

theorem nsCount_le (np : Nat) (S : List Bool) : nsCount np S ≤ np := by
  unfold nsCount
  exact Nat.le_trans (List.length_filter_le _ _) (by simp)

theorem nsCount_zero {np : Nat} {S : List Bool} (hl : S.length = np) (h : nsCount np S = 0) :
    ∀ i, S.getD i false = false := by
  intro i
  by_cases hi : i < np
  · cases hS : S.getD i false
    · rfl
    · exfalso
      unfold nsCount at h
      rw [List.length_eq_zero_iff, List.filter_eq_nil_iff] at h
      exact h i (List.mem_range.2 hi) hS
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl

theorem nestableSet_spec (nest : NestTable) (st : SortTable) (d : IndDecl) :
    (∀ i, (nestableSet nest st d).getD i false = true → d.paramIsType i = true) ∧
    (∀ i, (nestableSet nest st d).getD i false = true → ∀ c j FT, fieldTerm d c j = some FT →
      FT.passOther st d.sort (d.deepVars c) (d.params.length - 1 - i) = false) ∧
    (∀ i, (nestableSet nest st d).getD i false = true → ∀ c j FT, fieldTerm d c j = some FT →
      FT.nestOk (fun m j => if m == d.name then (nestableSet nest st d).getD j false else nest m j) (d.deepVars c)
        (d.params.length - 1 - i) = true) := by
  rw [nestableSet_eq]
  have hinit : (nsInit st d).length = d.params.length := by simp [nsInit]
  obtain ⟨hl, hle, hfix⟩ := nsIter_spec nest d d.params.length (nsInit st d) hinit
  generalize nsIter (nsStep nest d) d.params.length (nsInit st d) = R at hl hle hfix ⊢
  -- either a fixed point, or the empty set
  have hfix' : ∀ i, R.getD i false = true → (nsStep nest d R).getD i false = true := by
    rcases hfix with hfix | hfix
    · intro i h; rw [hfix]; exact h
    · have := nsCount_le d.params.length (nsInit st d)
      have h0 := nsCount_zero hl (by omega)
      intro i h; rw [h0 i] at h; cases h
  have hinit' : ∀ i, R.getD i false = true → i < d.params.length ∧ d.paramIsType i = true ∧
      (d.ctors.zipIdx.all fun ((_, fields), c) => fields.all fun (_, FT) =>
        !FT.passOther st d.sort (d.deepVars c) (d.params.length - 1 - i)) = true := by
    intro i h
    have := hle i h
    unfold nsInit at this
    rw [getD_map_range] at this
    simpa using this
  refine ⟨fun i h => (hinit' i h).2.1, fun i h c j FT hFT => ?_, fun i h c j FT hFT => ?_⟩
  · have := (allFields_iff d (fun c FT => !FT.passOther st d.sort (d.deepVars c) (d.params.length - 1 - i))).1
      (hinit' i h).2.2 c j FT hFT
    simpa using this
  · have := hfix' i h
    unfold nsStep at this
    rw [getD_map_range] at this
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact (allFields_iff d (fun c FT => FT.nestOk (fun m j => if m == d.name then R.getD j false else nest m j)
      (d.deepVars c) (d.params.length - 1 - i))).1 this.2.2 c j FT hFT

end Ochr.Meaning.DataModel.Exists.Knot

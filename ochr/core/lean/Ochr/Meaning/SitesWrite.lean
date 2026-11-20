import Ochr.Meaning.BotWrite

/-!
# Writing `⊥` at a path, on sites (L3's sites half)

The checker's write of `⊥` at a path removes exactly the sites at or under the path: a site of a
borrow at a strict prefix of the path (a mark on the way) stays, a site off the path stays. So
after an access that has ended every live borrow lent at, over or under the place, every live
borrow keeps its sites (`botWrite_step`'s `sites` clause).
-/

namespace Ochr.Meaning

mutual
/-- Every site of a value held at `pos`, read at `path`, is at `pos` and extends `path`. -/
theorem sitesOf_prefix (l : Nat) (pos : Pos) : ∀ (path : List Step) (v : Value) (x : Site),
    x ∈ Value.sitesOf l pos path v → x.pos = pos ∧ path <+: x.path
  | path, .loan m, x, h => by
    simp only [Value.sitesOf] at h
    split at h
    · simp only [List.mem_singleton] at h; subst h; exact ⟨rfl, List.prefix_refl _⟩
    · cases h
  | path, .gloan m w, x, h => by
    simp only [Value.sitesOf] at h
    split at h
    · simp only [List.mem_singleton] at h; subst h; exact ⟨rfl, List.prefix_refl _⟩
    · exact sitesOf_prefix l pos path w x h
  | path, .sealed t, x, h => by
    simp only [Value.sitesOf] at h
    split at h
    · simp only [List.mem_singleton] at h; subst h; exact ⟨rfl, List.prefix_refl _⟩
    · cases h
  | path, .borrow _ w, x, h => by
    simp only [Value.sitesOf] at h
    obtain ⟨hp, hx⟩ := sitesOf_prefix l pos (path ++ [.deref]) w x h
    exact ⟨hp, (List.prefix_append _ _).trans hx⟩
  | path, .succ w, x, h => by
    simp only [Value.sitesOf] at h
    obtain ⟨hp, hx⟩ := sitesOf_prefix l pos (path ++ [.proj 0]) w x h
    exact ⟨hp, (List.prefix_append _ _).trans hx⟩
  | path, .ind ty c _ _ fs, x, h => by
    simp only [Value.sitesOf] at h
    exact sitesOfFields_prefix l pos path ty c 0 fs x h
  | _, .zero, _, h | _, .unit, _, h | _, .gfn _, _, h | _, .clo _ _ _, _, h | _, .bot, _, h
  | _, .abs _, _, h | _, .proof, _, h | _, .tNat, _, h | _, .tUnit, _, h | _, .tEq _ _ _, _, h
  | _, .tRef _, _, h | _, .tPi _ _ _, _, h | _, .sort _, _, h | _, .tInd _ _, _, h => by
    simp [Value.sitesOf] at h

theorem sitesOfFields_prefix (l : Nat) (pos : Pos) (path : List Step) (ty : String) (c : Nat) :
    ∀ (i : Nat) (ws : List Value) (x : Site), x ∈ Value.sitesOfFields l pos path ty c i ws → x.pos = pos ∧ path <+: x.path
  | _, [], x, h => by simp [Value.sitesOfFields] at h
  | i, w :: ws, x, h => by
    simp only [Value.sitesOfFields, List.mem_append] at h
    rcases h with h | h
    · obtain ⟨hp, hx⟩ := sitesOf_prefix l pos (path ++ [.field ⟨ty, c, i, ""⟩]) w x h
      exact ⟨hp, (List.prefix_append _ _).trans hx⟩
    · exact sitesOfFields_prefix l pos path ty c (i + 1) ws x h
end

/-- A field's sites, by index. -/
theorem mem_sitesOfFields (l : Nat) (pos : Pos) (path : List Step) (ty : String) (c : Nat) :
    ∀ (i : Nat) (ws : List Value) (x : Site), x ∈ Value.sitesOfFields l pos path ty c i ws ↔
      ∃ j w, ws[j]? = some w ∧ x ∈ Value.sitesOf l pos (path ++ [.field ⟨ty, c, i + j, ""⟩]) w
  | _, [], x => by simp [Value.sitesOfFields]
  | i, w :: ws, x => by
    simp only [Value.sitesOfFields, List.mem_append, mem_sitesOfFields l pos path ty c (i + 1) ws x]
    constructor
    · rintro (h | ⟨j, w', hj, h⟩)
      · exact ⟨0, w, rfl, by simpa using h⟩
      · exact ⟨j + 1, w', by simpa using hj, by rwa [show i + (j + 1) = i + 1 + j by omega]⟩
    · rintro ⟨j, w', hj, h⟩
      cases j with
      | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at hj; subst hj; exact .inl (by simpa using h)
      | succ j =>
        simp only [List.getElem?_cons_succ] at hj
        exact .inr ⟨j, w', hj, by rwa [show i + 1 + j = i + (j + 1) by omega]⟩

theorem walkKey_append (a b : List Step) : walkKey (a ++ b) = walkKey a ++ walkKey b := List.map_append

/-- A path through a field other than the written one is not under the written path. -/
theorem not_under_of_key_ne {path y ss : List Step} {a b : Step} (hy : path ++ [a] <+: y)
    (hab : a.key ≠ b.key) : ¬ (walkKey (path ++ b :: ss)).isPrefixOf (walkKey y) = true := by
  intro h
  rw [List.isPrefixOf_iff_prefix] at h
  obtain ⟨t, rfl⟩ := hy
  simp only [walkKey_append, List.append_assoc, List.singleton_append] at h
  obtain ⟨u, hu⟩ := h
  simp only [walkKey, List.map_cons, List.cons_append, List.append_assoc] at hu
  have := List.append_cancel_left hu
  simp only [List.cons.injEq] at this
  exact hab this.1.symm

/-- A path strictly above the written one is not under it. -/
theorem not_under_strict {path ss : List Step} {b : Step} :
    ¬ (walkKey (path ++ b :: ss)).isPrefixOf (walkKey path) = true := by
  intro h
  rw [List.isPrefixOf_iff_prefix] at h
  have := h.length_le
  simp [walkKey] at this
  omega

/-- **The write of `⊥` at a path removes exactly the sites at or under it.** -/
theorem sitesOf_updAt_bot (l : Nat) (pos : Pos) : ∀ (steps path : List Step) (v v' : Value),
    Value.updAt (fun _ => .bot) steps v = some v' → ∀ x,
      x ∈ Value.sitesOf l pos path v' ↔
        (x ∈ Value.sitesOf l pos path v ∧ ¬ (walkKey (path ++ steps)).isPrefixOf (walkKey x.path) = true)
  | [], path, v, v', h, x => by
    simp only [Value.updAt, Option.some.injEq] at h
    subst h
    simp only [Value.sitesOf, List.not_mem_nil, false_iff, not_and, Decidable.not_not, List.append_nil]
    intro hx
    rw [List.isPrefixOf_iff_prefix]
    exact (sitesOf_prefix l pos path v x hx).2.map Step.key
  | st :: ss, path, v, v', h, x => by
    cases v with
    | gloan m w =>
      simp only [Value.updAt] at h
      obtain ⟨w', hw', rfl⟩ := Option.map_eq_some_iff.mp h
      simp only [Value.sitesOf]
      split
      · simp only [List.mem_singleton]
        constructor
        · rintro rfl; exact ⟨rfl, not_under_strict⟩
        · exact fun h => h.1
      · exact sitesOf_updAt_bot l pos (st :: ss) path w w' hw' x
    | borrow k w =>
      cases st with
      | deref =>
        simp only [Value.updAt] at h
        obtain ⟨w', hw', rfl⟩ := Option.map_eq_some_iff.mp h
        simp only [Value.sitesOf]
        rw [sitesOf_updAt_bot l pos ss (path ++ [Step.deref]) w w' hw' x, List.append_assoc, List.singleton_append]
      | proj i => simp [Value.updAt] at h
      | field g => simp [Value.updAt] at h
    | succ w =>
      cases st with
      | proj i =>
        cases i with
        | zero =>
          simp only [Value.updAt] at h
          obtain ⟨w', hw', rfl⟩ := Option.map_eq_some_iff.mp h
          simp only [Value.sitesOf]
          rw [sitesOf_updAt_bot l pos ss (path ++ [Step.proj 0]) w w' hw' x, List.append_assoc, List.singleton_append]
        | succ i => simp [Value.updAt] at h
      | deref => simp [Value.updAt] at h
      | field g => simp [Value.updAt] at h
    | ind ty c hh ps fs =>
      obtain ⟨hst, w, w', hw, hw', rfl⟩ := updAt_ind_inv h
      -- the written field's step names the field the sites are read through
      have hkey : (Step.field ⟨ty, c, st.fieldIdx, ""⟩).key = st.key := by
        cases st with
        | deref => exact absurd rfl hst
        | proj i =>
          cases c with
          | zero => rfl
          | succ c => simp [Value.updAt] at h
        | field g =>
          simp only [Value.updAt] at h
          split at h
          · rename_i w0 hw0
            split at hw0
            · rename_i hc
              simp only [Bool.and_eq_true, beq_iff_eq] at hc
              simp [Step.key, Step.fieldIdx, hc.2]
            · cases hw0
          · cases h
      simp only [Value.sitesOf, mem_sitesOfFields, Nat.zero_add]
      constructor
      · rintro ⟨j, u, hj, hx⟩
        by_cases hjk : j = st.fieldIdx
        · subst hjk
          rw [List.getElem?_set_self (List.getElem?_eq_some_iff.mp hw).1, Option.some.injEq] at hj
          subst hj
          rw [sitesOf_updAt_bot l pos ss _ w w' hw' x] at hx
          refine ⟨⟨st.fieldIdx, w, hw, hx.1⟩, ?_⟩
          have := hx.2
          simp only [walkKey_append, List.append_assoc, List.singleton_append] at this ⊢
          simpa [walkKey, hkey] using this
        · rw [List.getElem?_set_ne (Ne.symm hjk)] at hj
          refine ⟨⟨j, u, hj, hx⟩, not_under_of_key_ne (sitesOf_prefix l pos _ u x hx).2 ?_⟩
          simp only [Step.key]
          cases st with
          | deref => exact absurd rfl hst
          | proj i => simp only [Step.fieldIdx] at hjk; intro e; simp at e; omega
          | field g => simp only [Step.fieldIdx] at hjk; intro e; simp at e; omega
      · rintro ⟨⟨j, u, hj, hx⟩, hnot⟩
        by_cases hjk : j = st.fieldIdx
        · subst hjk
          rw [hw, Option.some.injEq] at hj
          subst hj
          refine ⟨st.fieldIdx, w', List.getElem?_set_self (List.getElem?_eq_some_iff.mp hw).1, ?_⟩
          rw [sitesOf_updAt_bot l pos ss _ w w' hw' x]
          refine ⟨hx, ?_⟩
          simp only [walkKey_append, List.append_assoc, List.singleton_append] at hnot ⊢
          simpa [walkKey, hkey] using hnot
        · exact ⟨j, u, by rw [List.getElem?_set_ne (Ne.symm hjk)]; exact hj, hx⟩
    | _ => simp [Value.updAt] at h
termination_by steps _ v => (steps.length, sizeOf v)

end Ochr.Meaning

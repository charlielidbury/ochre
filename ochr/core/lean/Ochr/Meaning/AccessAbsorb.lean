import Ochr.Meaning.RelendComm
import Ochr.Meaning.Locality

/-!
# An access through a filled prefix is the access of the prefix (the lent-prefix absorption)

The reference accesses the shortest lent prefix of a dropped place whole (`accessLentPrefix`); the
checker accesses the place itself, or its filled parent. The two accesses end the same borrows when
the sites at the position are as (WF12) and the minimality of the lent prefix leave them: no live
site strictly above the prefix's key `K`, and a live borrow with a site at or below `K` has a fill
at `K` (`AbsorbInv`). Then every access whose path's key extends `K` reaches the same live labels,
round by round, since ending a borrow passes its sites to the borrows of its content (`relend`),
which keeps the invariant (`AbsorbInv.endLabel`). So the two accesses are equal (`access_absorb`).
-/

namespace Ochr.Meaning

namespace SState

/-- The sites at `pos` against the key `K` of a filled prefix: a live site whose key is a prefix of
`K` is at `K`, and a live borrow with a site at or below `K` has a fill at `K`. -/
def AbsorbInv (s : SState) (pos : Pos) (K : List (Nat × Nat)) : Prop :=
  (∀ m ∈ s.liveLabels, ∀ x ∈ s.lent m, x.pos = pos → pathKey x.path <+: K → pathKey x.path = K) ∧
  (∀ m ∈ s.liveLabels, ∀ x ∈ s.lent m, x.pos = pos → K <+: pathKey x.path →
    ∃ y ∈ s.lent m, y.pos = pos ∧ pathKey y.path = K ∧ y.fill = true)

theorem mem_liveLabels_of_endLabel {s : SState} {l m : Nat} (h : m ∈ (s.endLabel l).liveLabels) :
    m ∈ s.liveLabels := by
  rw [mem_liveLabels] at h ⊢
  obtain ⟨p, hp, hs⟩ := h
  rw [positions_endLabel] at hp
  refine ⟨p, hp, ?_⟩
  cases hf : s.positions.find? (fun p => decide (s.shape p = some l)) with
  | none => rw [endLabel_of_find_none s l hf] at hs; exact hs
  | some r =>
    rw [endLabel_shape s l r hf] at hs
    dsimp only at hs
    split at hs
    · cases hs
    · exact hs

theorem lent_endLabel {s : SState} {l : Nat} {r : Pos}
    (h : s.positions.find? (fun p => decide (s.shape p = some l)) = some r) :
    (s.endLabel l).lent = s.relend l r := by
  rw [endLabel_of_find s l r h]; rfl

theorem live_of_find {s : SState} {l : Nat} {r : Pos}
    (h : s.positions.find? (fun p => decide (s.shape p = some l)) = some r) : l ∈ s.liveLabels := by
  rw [mem_liveLabels]
  exact ⟨r, List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

end SState

theorem pathKey_append (a b : List Step) : pathKey (a ++ b) = pathKey a ++ pathKey b := by
  simp [pathKey]

theorem pathKey_deref (π : List Step) : pathKey (.deref :: π) = pathKey π := rfl

theorem key_none_deref {st : Step} (h : st.key = none) : st = .deref := by
  cases st <;> simp_all [Step.key]

/-! ## [End]'s sites, taken apart -/

theorem relendOne_kept {L : Nat → List Site} {l : Nat} {r : Pos} {x : Site}
    (h : x.pos ≠ r) : relendOne L l r x = [x] := relendOne_off h

/-- A site after [End] at `(l, r)` is a site off the holder, kept, or a site of `l` adjusted for a
site at the holder (docs/31 D67: every site at the holder is re-rooted). -/
theorem mem_relend {s : SState} {l : Nat} {r : Pos} {m : Nat} {z : Site} (h : z ∈ s.relend l r m) :
    m ≠ l ∧ ∃ x ∈ s.lent m, (z = x ∧ x.pos ≠ r) ∨
      (x.pos = r ∧ ∃ y ∈ s.lent l, z = adjust x (inContent x.path) y) := by
  rw [relend_eq] at h
  split at h
  · cases h
  · rename_i hml
    refine ⟨hml, ?_⟩
    obtain ⟨x, hx, hz⟩ := List.mem_flatMap.mp h
    refine ⟨x, hx, ?_⟩
    by_cases hk : x.pos = r
    · rw [relendOne_at hk] at hz
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hz
      exact .inr ⟨hk, y, hy, rfl⟩
    · rw [relendOne_kept hk] at hz
      exact .inl ⟨List.mem_singleton.mp hz, hk⟩

theorem mem_relend_kept {s : SState} {l : Nat} {r : Pos} {m : Nat} {x : Site} (hx : x ∈ s.lent m)
    (hml : m ≠ l) (hk : x.pos ≠ r) : x ∈ s.relend l r m := by
  rw [relend_eq, if_neg hml]
  exact List.mem_flatMap.mpr ⟨x, hx, by rw [relendOne_kept hk]; exact List.mem_singleton_self x⟩

theorem mem_relend_adjust {s : SState} {l : Nat} {r : Pos} {m : Nat} {x y : Site}
    (hx : x ∈ s.lent m) (hml : m ≠ l) (hr : x.pos = r) (hy : y ∈ s.lent l) :
    adjust x (inContent x.path) y ∈ s.relend l r m := by
  rw [relend_eq, if_neg hml]
  exact List.mem_flatMap.mpr ⟨x, hx, by rw [relendOne_at hr]; exact List.mem_map_of_mem hy⟩

theorem pathKey_inContent (σ : List Step) : pathKey (inContent σ) = pathKey σ := by
  unfold inContent; split <;> rfl

theorem adjust_fill {x y : Site} {π : List Step} (h : y.fill = true) : adjust x π y = y := by
  unfold adjust; simp [h]

theorem adjust_nofill {x y : Site} {π : List Step} (h : y.fill = false) :
    adjust x π y = { y with path := y.path ++ π, fill := x.fill } := by
  unfold adjust; simp [h]

/-! ## The invariant survives an end -/

namespace SState

theorem AbsorbInv.endLabel {s : SState} {pos : Pos} {K : List (Nat × Nat)} (hI : s.AbsorbInv pos K)
    (l : Nat) : (s.endLabel l).AbsorbInv pos K := by
  cases hf : s.positions.find? (fun p => decide (s.shape p = some l)) with
  | none => rw [endLabel_of_find_none s l hf]; exact hI
  | some r =>
    have hl := live_of_find hf
    have hlent := lent_endLabel hf
    refine ⟨fun m hm z hz hzp hpre => ?_, fun m hm z hz hzp hpre => ?_⟩
    · have hm' := mem_liveLabels_of_endLabel hm
      rw [hlent] at hz
      obtain ⟨hml, x, hx, (⟨rfl, -⟩ | ⟨hr, y, hy, rfl⟩)⟩ := mem_relend hz
      · exact hI.1 m hm' z hx hzp hpre
      · cases hfill : y.fill
        · rw [adjust_nofill hfill] at hzp hpre ⊢
          simp only at hzp hpre ⊢
          rw [pathKey_append] at hpre ⊢
          have hy' : pathKey y.path <+: K := (List.prefix_append _ _).trans hpre
          have hyK := hI.1 l hl y hy hzp hy'
          rw [hyK] at hpre ⊢
          have hlen := hpre.length_le
          simp only [List.length_append] at hlen
          have : pathKey (inContent x.path) = [] := List.eq_nil_of_length_eq_zero (by omega)
          rw [this, List.append_nil]
        · rw [adjust_fill hfill] at hzp hpre ⊢
          exact hI.1 l hl y hy hzp hpre
    · have hm' := mem_liveLabels_of_endLabel hm
      rw [hlent] at hz ⊢
      obtain ⟨hml, x, hx, (⟨rfl, hk⟩ | ⟨hr, y, hy, rfl⟩)⟩ := mem_relend hz
      · obtain ⟨y₀, hy₀, hy₀p, hy₀K, hy₀f⟩ := hI.2 m hm' z hx hzp hpre
        -- `y₀` is at `pos`, where `z` is, off the holder: kept
        exact ⟨y₀, mem_relend_kept hy₀ hml (by rw [hy₀p, ← hzp]; exact hk), hy₀p, hy₀K, hy₀f⟩
      · have hy₁ : ∃ y₁ ∈ s.lent l, y₁.pos = pos ∧ pathKey y₁.path = K ∧ y₁.fill = true := by
          cases hfill : y.fill
          · rw [adjust_nofill hfill] at hzp hpre
            simp only at hzp hpre
            rw [pathKey_append] at hpre
            have hKy : K <+: pathKey y.path := by
              rcases List.prefix_or_prefix_of_prefix (List.prefix_append (pathKey y.path) (pathKey (inContent x.path))) hpre with h | h
              · rw [hI.1 l hl y hy hzp h]; exact List.prefix_refl _
              · exact h
            exact hI.2 l hl y hy hzp hKy
          · rw [adjust_fill hfill] at hzp hpre
            exact hI.2 l hl y hy hzp hpre
        obtain ⟨y₁, hy₁, hy₁p, hy₁K, hy₁f⟩ := hy₁
        refine ⟨y₁, ?_, hy₁p, hy₁K, hy₁f⟩
        have := mem_relend_adjust hx hml hr hy₁
        rwa [adjust_fill hy₁f] at this

theorem AbsorbInv.foldl_endLabel {pos : Pos} {K : List (Nat × Nat)} :
    ∀ (ls : List Nat) {s : SState}, s.AbsorbInv pos K → (ls.foldl SState.endLabel s).AbsorbInv pos K
  | [], _, h => h
  | l :: ls, _, h => AbsorbInv.foldl_endLabel ls (h.endLabel l)

end SState

/-! ## Two accesses through a filled prefix are one -/

namespace SState

/-- Under the invariant, an access at a path whose key extends `K` reaches a live label exactly
when the access at `K` does. -/
theorem reached_absorb {s : SState} {pos : Pos} {ψ₁ ψ₂ : List Step} (hI : s.AbsorbInv pos (pathKey ψ₁))
    (h12 : pathKey ψ₁ <+: pathKey ψ₂) {m : Nat} (hm : m ∈ s.liveLabels) :
    s.reached pos (dataHit ψ₁) m = s.reached pos (dataHit ψ₂) m := by
  unfold SState.reached dataHit
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, List.isPrefixOf_iff_prefix]
  constructor
  · rintro ⟨x, hx, hxp, h | h⟩
    · have := hI.1 m hm x hx hxp h
      exact ⟨x, hx, hxp, .inl (by rw [this]; exact h12)⟩
    · obtain ⟨y, hy, hyp, hyK, -⟩ := hI.2 m hm x hx hxp h
      exact ⟨y, hy, hyp, .inl (by rw [hyK]; exact h12)⟩
  · rintro ⟨x, hx, hxp, h | h⟩
    · exact ⟨x, hx, hxp, List.prefix_or_prefix_of_prefix h h12⟩
    · exact ⟨x, hx, hxp, .inr (h12.trans h)⟩

/-- **An access through a filled prefix is the access of the prefix**: under the invariant at the
prefix's key, accessing at any path extending it ends the same borrows, round by round. -/
theorem access_absorb {s : SState} {pos : Pos} {ψ₁ ψ₂ : List Step} (hI : s.AbsorbInv pos (pathKey ψ₁))
    (h12 : pathKey ψ₁ <+: pathKey ψ₂) : s.access pos (dataHit ψ₁) = s.access pos (dataHit ψ₂) := by
  unfold SState.access
  suffices h : ∀ (L : List Nat) (t : SState), t.AbsorbInv pos (pathKey ψ₁) →
      L.foldl (fun t _ => (t.liveLabels.filter (t.reached pos (dataHit ψ₁))).foldl SState.endLabel t) t =
      L.foldl (fun t _ => (t.liveLabels.filter (t.reached pos (dataHit ψ₂))).foldl SState.endLabel t) t from
    h _ s hI
  intro L
  induction L with
  | nil => intro t _; rfl
  | cons a L ih =>
    intro t ht
    simp only [List.foldl_cons]
    have hf : t.liveLabels.filter (t.reached pos (dataHit ψ₁)) = t.liveLabels.filter (t.reached pos (dataHit ψ₂)) :=
      List.filter_congr fun m hm => reached_absorb ht h12 hm
    rw [hf]
    exact ih _ (AbsorbInv.foldl_endLabel _ ht)

end SState

/-! ## The lent prefix: what minimality gives, and accessing twice -/

theorem pathKey_take_prefix (steps : List Step) {i j : Nat} (h : i ≤ j) :
    pathKey (steps.take i) <+: pathKey (steps.take j) := by
  have : steps.take i <+: steps.take j := by
    rw [show steps.take i = (steps.take j).take i by rw [List.take_take, Nat.min_eq_left h]]
    exact List.take_prefix _ _
  exact this.filterMap _

/-- The lent prefix is the first prefix of the path with a live site at it. -/
theorem lentPrefix_spec {s : SState} {pos : Pos} {steps ψ : List Step} (h : lentPrefix s pos steps = some ψ) :
    ∃ j, j < steps.length ∧ ψ = steps.take j ∧
      (∀ i, i < j → s.liveLabels.any (s.reached pos fun ψ' => pathKey ψ' == pathKey (steps.take i)) = false) := by
  unfold lentPrefix at h
  rw [List.find?_map] at h
  obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨-, hjr, hmin⟩ := List.find?_range_eq_some.mp hj
  refine ⟨j, List.mem_range.mp hjr, rfl, fun i hi => ?_⟩
  have := hmin i hi
  simpa using this

theorem pathKey_take_succ (steps : List Step) (j : Nat) :
    pathKey (steps.take (j + 1)) = pathKey (steps.take j) ++ ((steps[j]?).bind Step.key).toList := by
  rw [List.take_add_one, pathKey_append]
  cases steps[j]? with
  | none => simp [pathKey]
  | some v => cases hv : v.key <;> simp [pathKey, hv]

/-- Every prefix of a prefix's key is the key of a shorter prefix (the keys of `steps.take i` grow
by at most one field per step, `*` adding none). -/
theorem exists_take_key {steps : List Step} :
    ∀ {j : Nat} {P : List (Nat × Nat)}, P <+: pathKey (steps.take j) → ∃ i ≤ j, pathKey (steps.take i) = P
  | 0, P, h => ⟨0, Nat.le_refl _, by
      have : P = [] := List.prefix_nil.mp (by simpa [pathKey] using h)
      simp [this, pathKey]⟩
  | j + 1, P, h => by
    rw [pathKey_take_succ] at h
    by_cases h' : P <+: pathKey (steps.take j)
    · obtain ⟨i, hi, e⟩ := exists_take_key h'
      exact ⟨i, Nat.le_succ_of_le hi, e⟩
    · refine ⟨j + 1, Nat.le_refl _, ?_⟩
      rw [pathKey_take_succ]
      rcases List.prefix_or_prefix_of_prefix h (List.prefix_append _ _) with h1 | h1
      · exact absurd h1 h'
      · obtain ⟨u, rfl⟩ := h1
        have hu : u <+: ((steps[j]?).bind Step.key).toList :=
          (List.prefix_append_right_inj (pathKey (steps.take j))).mp h
        cases ht : (steps[j]?).bind Step.key with
        | none =>
          rw [ht] at hu
          have : u = [] := List.prefix_nil.mp (by simpa using hu)
          subst this; simp at h'
        | some b =>
          rw [ht] at hu
          rcases u with _ | ⟨c, u⟩
          · simp at h'
          · obtain ⟨t, ht'⟩ := hu
            simp only [Option.toList_some, List.cons_append, List.cons.injEq, List.append_eq_nil_iff] at ht'
            simp [ht'.1, ht'.2.1]

/-- **No live site strictly above the lent prefix** (its minimality): the first half of `AbsorbInv`. -/
theorem lentPrefix_above {s : SState} {pos : Pos} {steps ψ : List Step} (h : lentPrefix s pos steps = some ψ) :
    ∀ m ∈ s.liveLabels, ∀ x ∈ s.lent m, x.pos = pos → pathKey x.path <+: pathKey ψ → pathKey x.path = pathKey ψ := by
  obtain ⟨j, -, rfl, hmin⟩ := lentPrefix_spec h
  intro m hm x hx hxp hpre
  obtain ⟨i, hij, hi⟩ := exists_take_key hpre
  rcases Nat.lt_or_ge i j with hlt | hge
  · have := hmin _ hlt
    rw [List.any_eq_false] at this
    exfalso
    apply this m hm
    unfold SState.reached
    rw [List.any_eq_true]
    exact ⟨x, hx, by simp [hxp, hi]⟩
  · have : i = j := by omega
    subst this; exact hi.symm

namespace SState

/-- Accessing twice is accessing once: after an access nothing it reaches is left. -/
theorem access_access (s : SState) (p : Pos) (hit : List Step → Bool) :
    (s.access p hit).access p hit = s.access p hit :=
  access_of_unreached _ p hit (access_post s p hit)

end SState

end Ochr.Meaning

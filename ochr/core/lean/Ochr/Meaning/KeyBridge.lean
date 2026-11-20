import Ochr.Meaning.SitesFollow
import Ochr.Meaning.WF

/-!
# The two keys of a path, and where they meet (docs/31 D67)

The reference compares paths by `pathKey`, its `*`s erased (a borrow means its content); the
checker's statements about its own values compare by `walkKey`, step by step (its walk tells `*`
from a field). They meet in the relation, at the sites of one position (the reference's are the
checker's, `Rel.sites`) and the checker's walks of the value there:
* one way for free: a positional prefix is an erased prefix (`pathKey_prefix_of_walkKey`);
* the other way, the walk lemma: under (WF1) every site path and every successful walk at a
  position is the position's `*` (if it holds a borrow) followed by fields only (`site_shaped`,
  `walk_shaped`), so two of them place their `*`s alike and the two comparisons agree
  (`walkKey_prefix_of_shaped`, `walkKey_eq_of_shaped`), but for a walk that stops before the
  borrow's `*`. The fact it rests on (no borrow under a mark, no borrow under a borrow's content,
  so every site at a borrow holder is under its `*`) is (WF1)'s first half, a read-off clause
  swept EXACTLY (`lake exe sweep`, on the suite and the probes).
-/

namespace Ochr.Meaning

/-! ## The free direction -/

theorem pathKey_eq_filterMap (a : List Step) : pathKey a = (walkKey a).filterMap id := by
  simp [pathKey, walkKey, List.filterMap_map]

theorem pathKey_prefix_of_walkKey {a b : List Step} (h : walkKey a <+: walkKey b) : pathKey a <+: pathKey b := by
  rw [pathKey_eq_filterMap, pathKey_eq_filterMap]; exact h.filterMap _

theorem pathKey_eq_of_walkKey {a b : List Step} (h : walkKey a = walkKey b) : pathKey a = pathKey b := by
  rw [pathKey_eq_filterMap, pathKey_eq_filterMap, h]

/-! ## Paths of fields only -/

/-- Every step a field: no `*`. -/
def Fields (a : List Step) : Prop := ∀ st ∈ a, st.key ≠ none

theorem walkKey_fields : ∀ {a : List Step}, Fields a → walkKey a = (pathKey a).map some
  | [], _ => rfl
  | st :: a, h => by
    obtain ⟨k, hk⟩ := Option.ne_none_iff_exists'.mp (h st (List.mem_cons_self ..))
    have ih := walkKey_fields (a := a) fun s hs => h s (List.mem_cons_of_mem _ hs)
    simp only [walkKey, pathKey, List.map_cons, List.filterMap_cons, hk] at ih ⊢
    rw [ih]

theorem fields_take {a : List Step} (h : Fields a) (k : Nat) : Fields (a.take k) :=
  fun st hs => h st (List.mem_of_mem_take hs)

theorem map_some_prefix {L M : List (Nat × Nat)} : L.map some <+: M.map some ↔ L <+: M := by
  constructor
  · intro h
    rw [List.prefix_iff_eq_take] at h ⊢
    rw [List.length_map, ← List.map_take] at h
    exact (List.map_inj_right fun _ _ e => Option.some.inj e).mp h
  · exact fun h => h.map _

/-! ## The shape of a position's paths under (WF1) -/

/-- A `*` step reaches something only through a borrow. -/
theorem hasBorrow_of_stepV_deref : ∀ (v u : Value), stepV .deref v = some u → v.hasBorrow = true
  | .gloan m w, u, h => by
    have : stepV .deref (.gloan m w) = stepV .deref w := rfl
    rw [this] at h
    have := hasBorrow_of_stepV_deref w u h
    simp only [Value.hasBorrow] at this ⊢
    rw [Value.anyAtom]; simp [this]
  | .borrow _ _, _, _ => by simp [Value.hasBorrow, Value.anyAtom]
  | .loan _, _, h | .sealed _, _, h | .succ _, _, h | .ind _ _ _ _ _, _, h | .zero, _, h | .unit, _, h
  | .gfn _, _, h | .clo _ _ _, _, h | .bot, _, h | .abs _, _, h | .proof, _, h | .tNat, _, h | .tUnit, _, h
  | .tEq _ _ _, _, h | .tRef _, _, h | .tPi _ _ _, _, h | .sort _, _, h | .tInd _ _, _, h => by
    simp [stepV] at h

/-- **A walk in a borrow-free value is fields only.** -/
theorem walk_fields : ∀ (ss : List Step) (v u : Value), v.hasBorrow = false → v.follow ss = some u → Fields ss
  | [], _, _, _, _ => fun _ h => absurd h List.not_mem_nil
  | st :: ss, v, u, hv, h => by
    simp only [Value.follow] at h
    cases hs : stepV st v with
    | none => simp [hs] at h
    | some v' =>
      rw [hs, Option.bind_some] at h
      have hv' : v'.hasBorrow = false := by
        cases hb : v'.hasBorrow
        · rfl
        · simp only [Value.hasBorrow] at hb hv
          rw [anyAtom_of_stepV st v v' hs hb] at hv; cases hv
      have hst : st.key ≠ none := by
        cases st with
        | deref => rw [hasBorrow_of_stepV_deref v v' hs] at hv; cases hv
        | proj _ => simp [Step.key]
        | field _ => simp [Step.key]
      intro s hs'
      rcases List.mem_cons.mp hs' with rfl | hs'
      · exact hst
      · exact walk_fields ss v' u hv' h s hs'

theorem anyAtom_false_of_mem {P : Value → Bool} {u : Value} {vs : List Value} (hm : u ∈ vs)
    (h : Value.anyAtomList P vs = false) : u.anyAtom P = false := by
  cases hb : u.anyAtom P
  · rfl
  · rw [valueAnyAtomList_of_mem hm hb] at h; cases h

mutual
/-- **The sites in a borrow-free value lie at fields-only paths below it.** -/
theorem sites_fields (l : Nat) (pos : Pos) : ∀ (path : List Step) (v : Value) (x : Site),
    v.hasBorrow = false → x ∈ Value.sitesOf l pos path v → ∃ σ, x.path = path ++ σ ∧ Fields σ
  | path, .loan m, x, _, h => by
    simp only [Value.sitesOf] at h
    split at h
    · simp only [List.mem_singleton] at h; subst h; exact ⟨[], by simp, fun _ h => absurd h List.not_mem_nil⟩
    · cases h
  | path, .gloan m w, x, hv, h => by
    simp only [Value.sitesOf] at h
    split at h
    · simp only [List.mem_singleton] at h; subst h; exact ⟨[], by simp, fun _ h => absurd h List.not_mem_nil⟩
    · have hw : w.hasBorrow = false := by
        simp only [Value.hasBorrow] at hv ⊢; rw [Value.anyAtom] at hv; simpa using hv
      exact sites_fields l pos path w x hw h
  | path, .sealed t, x, _, h => by
    simp only [Value.sitesOf] at h
    split at h
    · simp only [List.mem_singleton] at h; subst h; exact ⟨[], by simp, fun _ h => absurd h List.not_mem_nil⟩
    · cases h
  | _, .borrow _ _, _, hv, _ => by simp [Value.hasBorrow, Value.anyAtom] at hv
  | path, .succ w, x, hv, h => by
    simp only [Value.sitesOf] at h
    have hw : w.hasBorrow = false := by
      simp only [Value.hasBorrow] at hv ⊢; rw [Value.anyAtom] at hv; simpa using hv
    obtain ⟨σ, hx, hσ⟩ := sites_fields l pos (path ++ [.proj 0]) w x hw h
    refine ⟨.proj 0 :: σ, by rw [hx]; simp, fun st hs => ?_⟩
    rcases List.mem_cons.mp hs with rfl | hs
    · simp [Step.key]
    · exact hσ st hs
  | path, .ind ty c hh ps fs, x, hv, h => by
    simp only [Value.sitesOf] at h
    simp only [Value.hasBorrow] at hv; rw [Value.anyAtom] at hv; simp only [Bool.or_eq_false_iff] at hv
    exact sitesFields_fields l pos path ty c 0 fs x (fun w hw => anyAtom_false_of_mem hw hv.2.2) h
  | _, .zero, _, _, h | _, .unit, _, _, h | _, .gfn _, _, _, h | _, .clo _ _ _, _, _, h | _, .bot, _, _, h
  | _, .abs _, _, _, h | _, .proof, _, _, h | _, .tNat, _, _, h | _, .tUnit, _, _, h | _, .tEq _ _ _, _, _, h
  | _, .tRef _, _, _, h | _, .tPi _ _ _, _, _, h | _, .sort _, _, _, h | _, .tInd _ _, _, _, h => by
    simp [Value.sitesOf] at h

theorem sitesFields_fields (l : Nat) (pos : Pos) (path : List Step) (ty : String) (c : Nat) :
    ∀ (i : Nat) (ws : List Value) (x : Site), (∀ w ∈ ws, w.hasBorrow = false) →
      x ∈ Value.sitesOfFields l pos path ty c i ws → ∃ σ, x.path = path ++ σ ∧ Fields σ
  | _, [], x, _, h => by simp [Value.sitesOfFields] at h
  | i, w :: ws, x, hws, h => by
    simp only [Value.sitesOfFields, List.mem_append] at h
    rcases h with h | h
    · obtain ⟨σ, hx, hσ⟩ := sites_fields l pos (path ++ [.field ⟨ty, c, i, ""⟩]) w x (hws w (List.mem_cons_self ..)) h
      refine ⟨.field ⟨ty, c, i, ""⟩ :: σ, by rw [hx]; simp, fun st hs => ?_⟩
      rcases List.mem_cons.mp hs with rfl | hs
      · simp [Step.key]
      · exact hσ st hs
    · exact sitesFields_fields l pos path ty c (i + 1) ws x (fun u hu => hws u (List.mem_cons_of_mem _ hu)) h
end

/-! ## Site paths and walks at one position -/

/-- (WF1)'s first half at one position, in two halves: a borrow's content is borrow-free, any other
value is. -/
structure WF1At (v : Value) : Prop where
  content : ∀ b w, v = .borrow b w → w.hasBorrow = false
  other : v.isBorrow = false → v.hasBorrow = false

theorem wf1At_of_WF1 {env : Env} (h : WF1 env) {p : Pos} (hp : p ∈ allPos env) : WF1At (valAt env p) := by
  have h1 := h.1 p hp
  generalize valAt env p = v at h1
  cases v <;> exact ⟨by simp_all, by simp_all [Value.isBorrow]⟩

/-- A site path at a position: fields only, or the borrow's `*` then fields. -/
def SiteShaped (v : Value) (a : List Step) : Prop :=
  (v.isBorrow = false ∧ Fields a) ∨ (v.isBorrow = true ∧ ∃ r, a = .deref :: r ∧ Fields r)

/-- A walk at a position: fields only, or nothing or the borrow's `*` then fields. -/
def WalkShaped (v : Value) (a : List Step) : Prop :=
  (v.isBorrow = false ∧ Fields a) ∨ (v.isBorrow = true ∧ (a = [] ∨ ∃ r, a = .deref :: r ∧ Fields r))

theorem site_shaped {v : Value} (hv : WF1At v) {l : Nat} {pos : Pos} {x : Site}
    (hx : x ∈ v.sitesOf l pos []) : SiteShaped v x.path := by
  cases hb : v.isBorrow
  · obtain ⟨σ, hσ, hf⟩ := sites_fields l pos [] v x (hv.other hb) hx
    exact .inl ⟨hb, by rw [hσ]; simpa using hf⟩
  · cases v with
    | borrow b w =>
      simp only [Value.sitesOf] at hx
      obtain ⟨σ, hσ, hf⟩ := sites_fields l pos [.deref] w x (hv.content b w rfl) (by simpa using hx)
      exact .inr ⟨rfl, σ, by rw [hσ]; rfl, hf⟩
    | _ => simp [Value.isBorrow] at hb

theorem walk_shaped {v u : Value} (hv : WF1At v) {ss : List Step} (h : v.follow ss = some u) :
    WalkShaped v ss := by
  cases hb : v.isBorrow
  · exact .inl ⟨hb, walk_fields ss v u (hv.other hb) h⟩
  · cases v with
    | borrow b w =>
      refine .inr ⟨rfl, ?_⟩
      cases ss with
      | nil => exact .inl rfl
      | cons st ss =>
        cases st with
        | deref =>
          simp only [Value.follow, stepV, Option.bind_some] at h
          exact .inr ⟨ss, rfl, walk_fields ss w u (hv.content b w rfl) h⟩
        | proj i => simp [Value.follow, stepV] at h
        | field g => simp [Value.follow, stepV] at h
    | _ => simp [Value.isBorrow] at hb

theorem walkShaped_take {v : Value} {a : List Step} (h : WalkShaped v a) (k : Nat) : WalkShaped v (a.take k) := by
  rcases h with ⟨hb, hf⟩ | ⟨hb, rfl | ⟨r, rfl, hf⟩⟩
  · exact .inl ⟨hb, fields_take hf k⟩
  · exact .inr ⟨hb, .inl (by simp)⟩
  · cases k with
    | zero => exact .inr ⟨hb, .inl rfl⟩
    | succ k => exact .inr ⟨hb, .inr ⟨r.take k, by simp, fields_take hf k⟩⟩

theorem fields_nil_of_pathKey {r : List Step} (hf : Fields r) (h : pathKey r = []) : r = [] := by
  cases r with
  | nil => rfl
  | cons st r =>
    obtain ⟨k, hk⟩ := Option.ne_none_iff_exists'.mp (hf st (List.mem_cons_self ..))
    simp [pathKey, hk] at h

theorem walkKey_deref_fields {r : List Step} (hf : Fields r) :
    walkKey (.deref :: r) = none :: (pathKey r).map some := by
  rw [show walkKey (.deref :: r) = none :: walkKey r from rfl, walkKey_fields hf]

theorem walkKey_eq_iff_fields {a b : List Step} (ha : Fields a) (hb : Fields b) :
    walkKey a = walkKey b ↔ pathKey a = pathKey b := by
  rw [walkKey_fields ha, walkKey_fields hb]
  exact ⟨fun h => (List.map_inj_right fun _ _ e => Option.some.inj e).mp h, fun h => by rw [h]⟩

/-! ## The walk lemma: where erased comparisons give positional ones -/

/-- A site path strictly above a walk by `pathKey` is strictly above it by `walkKey`. -/
theorem walkKey_strict_of_site_walk {v : Value} {a b : List Step} (ha : SiteShaped v a) (hb : WalkShaped v b)
    (hp : pathKey a <+: pathKey b) (hne : pathKey a ≠ pathKey b) :
    walkKey a <+: walkKey b ∧ walkKey a ≠ walkKey b := by
  rcases ha with ⟨hB, hfa⟩ | ⟨hB, r, rfl, hfr⟩ <;> rcases hb with ⟨hB', hfb⟩ | ⟨hB', rfl | ⟨r', rfl, hfr'⟩⟩ <;>
    simp only [hB] at hB' <;> try cases hB'
  · rw [walkKey_fields hfa, walkKey_fields hfb]
    exact ⟨map_some_prefix.2 hp, fun h => hne ((walkKey_eq_iff_fields hfa hfb).1 (by rw [walkKey_fields hfa, walkKey_fields hfb]; exact h))⟩
  · exact absurd (List.prefix_nil.mp hp) hne
  · rw [walkKey_deref_fields hfr, walkKey_deref_fields hfr']
    rw [pathKey_deref, pathKey_deref] at hp hne
    refine ⟨List.cons_prefix_cons.mpr ⟨rfl, map_some_prefix.2 hp⟩, fun h => hne ?_⟩
    simp only [List.cons.injEq, true_and] at h
    exact (List.map_inj_right fun _ _ e => Option.some.inj e).mp h

/-- Two site paths at one position: a prefix by `pathKey` is a prefix by `walkKey`. -/
theorem walkKey_prefix_of_sites {v : Value} {a b : List Step} (ha : SiteShaped v a) (hb : SiteShaped v b)
    (hp : pathKey a <+: pathKey b) : walkKey a <+: walkKey b := by
  rcases ha with ⟨hB, hfa⟩ | ⟨hB, r, rfl, hfr⟩ <;> rcases hb with ⟨hB', hfb⟩ | ⟨hB', r', rfl, hfr'⟩ <;>
    simp only [hB] at hB' <;> try cases hB'
  · rw [walkKey_fields hfa, walkKey_fields hfb]; exact map_some_prefix.2 hp
  · rw [walkKey_deref_fields hfr, walkKey_deref_fields hfr']
    rw [pathKey_deref, pathKey_deref] at hp
    exact List.cons_prefix_cons.mpr ⟨rfl, map_some_prefix.2 hp⟩

/-- A site path at a strict prefix of a walk by `pathKey` is at a strict prefix by `walkKey`: the
same prefix, or, where the site is the borrow's whole content (`[*]`) and the prefix stops before
the `*` (`[]`), the next one. -/
theorem walkKey_take_of_site {v : Value} {a b : List Step} (ha : SiteShaped v a) (hb : WalkShaped v b)
    {k : Nat} (hk : k < b.length) (he : pathKey a = pathKey (b.take k)) (hs : pathKey (b.take k) ≠ pathKey b) :
    ∃ k' < b.length, walkKey a = walkKey (b.take k') := by
  rcases ha with ⟨hB, hfa⟩ | ⟨hB, r, rfl, hfr⟩ <;> rcases hb with ⟨hB', hfb⟩ | ⟨hB', rfl | ⟨r', rfl, hfr'⟩⟩ <;>
    simp only [hB] at hB' <;> try cases hB'
  · exact ⟨k, hk, (walkKey_eq_iff_fields hfa (fields_take hfb k)).2 he⟩
  · simp at hk
  · cases k with
    | zero =>
      simp only [List.take_zero, pathKey_deref] at he hs
      have hr : r = [] := fields_nil_of_pathKey hfr (by simpa [pathKey] using he)
      subst hr
      have hr' : r' ≠ [] := by rintro rfl; exact hs rfl
      refine ⟨1, by cases r' with | nil => exact absurd rfl hr' | cons _ _ => simp, ?_⟩
      simp [walkKey]
    | succ k =>
      refine ⟨k + 1, hk, ?_⟩
      simp only [List.take_succ_cons, pathKey_deref] at he ⊢
      rw [walkKey_deref_fields hfr, walkKey_deref_fields (fields_take hfr' k), he]

/-- A walk above a site path by `pathKey` is above it by `walkKey` (a walk that stops before the
borrow's `*` is above everything). -/
theorem walkKey_prefix_of_walk_site {v : Value} {a b : List Step} (ha : WalkShaped v a) (hb : SiteShaped v b)
    (hp : pathKey a <+: pathKey b) : walkKey a <+: walkKey b := by
  rcases ha with ⟨hB, hfa⟩ | ⟨hB, rfl | ⟨r, rfl, hfr⟩⟩ <;> rcases hb with ⟨hB', hfb⟩ | ⟨hB', r', rfl, hfr'⟩ <;>
    simp only [hB] at hB' <;> try cases hB'
  · rw [walkKey_fields hfa, walkKey_fields hfb]; exact map_some_prefix.2 hp
  · exact List.nil_prefix
  · rw [walkKey_deref_fields hfr, walkKey_deref_fields hfr']
    rw [pathKey_deref, pathKey_deref] at hp
    exact List.cons_prefix_cons.mpr ⟨rfl, map_some_prefix.2 hp⟩

end Ochr.Meaning

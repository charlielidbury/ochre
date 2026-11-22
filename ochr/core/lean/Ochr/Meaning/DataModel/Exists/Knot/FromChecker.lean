import Ochr.Meaning.DataModel.Exists.Knot.Grammar

/-!
# From the checker's checks to the grammar (exists7, groundwork for step 2)

Step 2 of the lane: the checker's acceptance of a declaration gives `GrammarOk` / `PGrammarOk` (exists7 called them `GrammarCoreOk` / `PGrammarCoreOk`; since D172 they are the whole grammar),
as an implication between decidable functions (the checker's `nestableSet`, `sortNestViolation`, pure
mirrors of `firstOrderTerm` and `readViolation`), the bridge from `checkInd`'s monadic run to those
functions being named facts for the machine lane. The argument (HANDOFF, docs/34 §18.12): a variable
that varies between the knot's comparisons (`varVaries`) reaches, through declared types, a nestable
parameter or a field whose type mentions `d`; the checker's `deepVars` is the closure of a term's
variables under declared types; so an off-spine node reading a varying variable is a D120 violation
(`readViolation`) or makes the nestable parameter not nestable (`nestableSet`, D107 with D120's
`deepVars`).

Proved here (no assumed fact): `deepVars`' loop is an explicit iteration (`deepVars_eq_iter`) that holds
everything reached through declared types within `np + k` steps (`mem_deepIter`, `mem_deepVars`); a
varying variable (`varVaries`) reaches, within that many steps, a nestable parameter or a field whose
declared type mentions `d` (`reach_varies`, given the [Ind] telescope rule `TeleOk`); so a term reading
a varying variable deep-reads such a variable (`deepVars_bad`). The rest of step 2 (exists8): the mirrors
and the bundle of checks (`Checks.lean`), `nestableSet`'s loop (`NestLoop.lean`), the main induction
and the theorem `grammar_of_checks` (`FromChecks.lean`).
-/

namespace Ochr.Meaning.DataModel.Exists.Knot

open Ochr

/-- The variables variable `u`'s declared type reads, in the field scope (as `IndDecl.deepVars`). -/
def tyVarsOf (d : IndDecl) (c : Nat) (u : Nat) : List Nat :=
  match d.varType c u with
  | none => []
  | some T => if u < d.params.length then T.freeVars.map (u + 1 + ·) else T.freeVars

/-- `deepVars`' loop, as a recursive function: at most `m` rounds, each adding the variables the
current ones' declared types read, stopping when a round adds none. -/
def deepIter (d : IndDecl) (c : Nat) : Nat → List Nat → List Nat
  | 0, acc => acc
  | m + 1, acc =>
    let next := (acc ++ acc.flatMap (tyVarsOf d c)).eraseDups
    if next.length == acc.length then acc else deepIter d c m next

theorem forIn_deepIter (d : IndDecl) (c : Nat) : ∀ (l : List Nat) (acc : List Nat),
    (Id.run (forIn l acc fun _ r => do
      let next := (r ++ r.flatMap (tyVarsOf d c)).eraseDups
      if next.length == r.length then pure (ForInStep.done r) else pure (ForInStep.yield next))) =
      deepIter d c l.length acc
  | [], _ => rfl
  | _ :: l, acc => by
    simp only [List.forIn_cons, Id.run, deepIter, List.length_cons]
    split
    · rfl
    · exact forIn_deepIter d c l _

/-- **`deepVars` is `deepIter`** for `np + k` rounds from the term's free variables. -/
theorem deepVars_eq_iter (d : IndDecl) (c : Nat) (t : Term) :
    d.deepVars c t = deepIter d c (d.params.length + (((d.ctors[c]?).map (·.2)).getD []).length) t.freeVars := by
  unfold IndDecl.deepVars
  have h := forIn_deepIter d c
    (List.range' 0 (d.params.length + ((Option.map (fun x => x.snd) d.ctors[c]?).getD []).length)) t.freeVars
  simp only [List.length_range'] at h
  rw [← h]
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Id.run, bind_pure]
  congr 1
  simp [Std.Legacy.Range.size]

/-! ## `deepIter` reaches the closure -/

theorem eraseDups_nodup_eq : ∀ (l : List Nat), l.Nodup → l.eraseDups = l
  | [], _ => rfl
  | a :: as, h => by
    rw [List.eraseDups_cons]
    have ha : a ∉ as := (List.nodup_cons.1 h).1
    have hf : as.filter (fun b => !b == a) = as := by
      rw [List.filter_eq_self]
      intro b hb
      have : b ≠ a := fun e => ha (e ▸ hb)
      simpa using this
    rw [hf, eraseDups_nodup_eq as (List.nodup_cons.1 h).2]
termination_by l => l.length

theorem eraseDups_nodup : ∀ (l : List Nat), l.eraseDups.Nodup
  | [] => List.nodup_nil
  | a :: as => by
    rw [List.eraseDups_cons]
    have : (as.filter fun b => !b == a).length < as.length + 1 :=
      Nat.lt_add_one_of_le (List.length_filter_le _ as)
    refine List.nodup_cons.2 ⟨fun hm => ?_, eraseDups_nodup _⟩
    rw [List.mem_eraseDups, List.mem_filter] at hm
    simp at hm
termination_by l => l.length

theorem eraseDups_ne_nil {l : List Nat} (h : l ≠ []) : l.eraseDups ≠ [] := by
  cases l with
  | nil => exact absurd rfl h
  | cons a as => rw [List.eraseDups_cons]; exact List.cons_ne_nil _ _

/-- A round that adds no length adds no variable (for a list without duplicates). -/
theorem subset_of_round {acc X : List Nat} (hn : acc.Nodup)
    (h : (acc ++ X).eraseDups.length = acc.length) : ∀ x ∈ X, x ∈ acc := by
  rw [List.eraseDups_append, eraseDups_nodup_eq acc hn, List.length_append] at h
  have h0 : (X.removeAll acc).eraseDups = [] := List.eq_nil_of_length_eq_zero (by omega)
  have h1 : X.removeAll acc = [] := by
    cases hX : X.removeAll acc with
    | nil => rfl
    | cons a l => rw [hX] at h0; exact absurd h0 (eraseDups_ne_nil (List.cons_ne_nil _ _))
  intro x hx
  refine Classical.byContradiction fun hxa => ?_
  have : x ∈ X.removeAll acc := by
    rw [List.removeAll, List.mem_filter]
    exact ⟨hx, by simpa using hxa⟩
  rw [h1] at this; cases this

/-- `w` is reached from `v` through declared types in at most `m` steps. -/
inductive ReachIn (d : IndDecl) (c : Nat) : Nat → Nat → Nat → Prop
  | refl (m v : Nat) : ReachIn d c m v v
  | step (m v u w : Nat) (hu : u ∈ tyVarsOf d c v) (h : ReachIn d c m u w) : ReachIn d c (m + 1) v w

theorem ReachIn.mono {d : IndDecl} {c : Nat} : ∀ {m m' v w : Nat}, m ≤ m' → ReachIn d c m v w → ReachIn d c m' v w
  | _, _, _, _, _, .refl _ _ => .refl _ _
  | _ + 1, m' + 1, _, _, hm, .step _ _ u _ hu h => .step _ _ u _ hu (h.mono (by omega))
  | _ + 1, 0, _, _, hm, _ => absurd hm (by omega)

/-- A list closed under one step holds everything reached from its members. -/
theorem mem_of_closed {d : IndDecl} {c : Nat} {acc : List Nat} (hc : ∀ u ∈ acc, ∀ x ∈ tyVarsOf d c u, x ∈ acc) :
    ∀ {m v w : Nat}, v ∈ acc → ReachIn d c m v w → w ∈ acc
  | _, _, _, hv, .refl _ _ => hv
  | _, _, _, hv, .step _ _ u _ hu h => mem_of_closed hc (hc _ hv u hu) h

/-- **`deepIter` for `m` rounds holds everything reached in at most `m` steps.** -/
theorem mem_deepIter (d : IndDecl) (c : Nat) : ∀ (m : Nat) (acc : List Nat), acc.Nodup →
    ∀ v ∈ acc, ∀ w, ReachIn d c m v w → w ∈ deepIter d c m acc
  | 0, acc, _, v, hv, w, h => by
    cases h with
    | refl => exact hv
  | m + 1, acc, hn, v, hv, w, h => by
    simp only [deepIter]
    split
    · rename_i heq
      have hsub := subset_of_round hn (by simpa using heq)
      exact mem_of_closed (fun u hu x hx => hsub x (List.mem_flatMap.2 ⟨u, hu, hx⟩)) hv h
    · have hnext : ∀ x, x ∈ acc ∨ x ∈ acc.flatMap (tyVarsOf d c) → x ∈ (acc ++ acc.flatMap (tyVarsOf d c)).eraseDups :=
        fun x hx => List.mem_eraseDups.2 (List.mem_append.2 hx)
      cases h with
      | refl => exact mem_deepIter d c m _ (eraseDups_nodup _) v (hnext v (.inl hv)) v (.refl _ _)
      | step _ _ u _ hu h' =>
        exact mem_deepIter d c m _ (eraseDups_nodup _) u (hnext u (.inr (List.mem_flatMap.2 ⟨v, hv, hu⟩))) w h'

theorem foldl_add_nodup {β : Type} (l : List (Nat × β)) : ∀ (acc : List Nat), acc.Nodup →
    (l.foldl (fun acc (o : Nat × β) => if acc.contains o.1 then acc else acc ++ [o.1]) acc).Nodup := by
  induction l with
  | nil => intro acc h; exact h
  | cons x l ih =>
    intro acc h
    simp only [List.foldl_cons]
    apply ih
    split
    · exact h
    · rename_i hc
      rw [List.nodup_append]
      refine ⟨h, List.nodup_cons.2 ⟨List.not_mem_nil, List.nodup_nil⟩, fun a ha b hb => ?_⟩
      simp only [List.mem_singleton] at hb
      subst hb
      intro e; subst e
      simp [ha] at hc

theorem freeVars_nodup (t : Term) : t.freeVars.Nodup := by
  unfold Term.freeVars
  exact foldl_add_nodup _ [] List.nodup_nil

/-- **`deepVars` holds every variable reached from the term's own through declared types** in at most
`np + k` steps. -/
theorem mem_deepVars {d : IndDecl} {c : Nat} {t : Term} {v w : Nat} (hv : v ∈ t.freeVars)
    (h : ReachIn d c (d.params.length + (((d.ctors[c]?).map (·.2)).getD []).length) v w) :
    w ∈ d.deepVars c t := by
  rw [deepVars_eq_iter]
  exact mem_deepIter d c _ _ (freeVars_nodup t) v hv w h

/-! ## A varying variable reaches a nestable parameter or a field whose type mentions `d` -/

/-- A variable the checker's rules forbid off the spine: a nestable parameter (D107), or a field whose
declared type mentions `d` (D120). -/
def BadVar (d : IndDecl) (c : Nat) (u : Nat) : Prop :=
  (u < d.params.length ∧ d.nestable.getD (d.params.length - 1 - u) false = true) ∨
  (d.params.length ≤ u ∧ ∃ T, d.varType c u = some T ∧ T.mentionsType d.name = true)

theorem fs_length (d : IndDecl) (c : Nat) : (((d.ctors[c]?).map (·.2)).getD []).length = DataLib.arity d c := by
  unfold DataLib.arity; cases d.ctors[c]? <;> rfl

theorem varType_param {d : IndDecl} {c u : Nat} (hu : u < d.params.length) :
    d.varType c u = some (paramTerm d (d.params.length - 1 - u)) := by
  unfold IndDecl.varType paramTerm
  rw [if_pos hu, List.getElem?_eq_getElem (by omega)]
  rfl

theorem varType_field {d : IndDecl} {c u : Nat} (h1 : d.params.length ≤ u) (h2 : u < d.params.length + DataLib.arity d c) :
    d.varType c u = fieldTerm d c (d.params.length + DataLib.arity d c - 1 - u) := by
  unfold IndDecl.varType fieldTerm DataLib.arity at *
  rw [if_neg (by omega)]
  rcases hc : d.ctors[c]? with _ | cs
  · simp [hc] at h2; omega
  · simp [hc]

variable {d : IndDecl} {c : Nat}

theorem reach_param : ∀ (j : Nat), j < d.params.length → paramVaries d j = true →
    ∃ w, ReachIn d c (j + 1) (d.params.length - 1 - j) w ∧ BadVar d c w := by
  intro j
  induction j using Nat.strongRecOn with
  | ind j ih =>
    intro hj hv
    rw [paramVaries] at hv
    simp only [Bool.or_eq_true, List.any_eq_true] at hv
    rcases hv with hn | ⟨u', hu', hv'⟩
    · exact ⟨_, .refl _ _, .inl ⟨by omega, by rw [show d.params.length - 1 - (d.params.length - 1 - j) = j by omega]; exact hn⟩⟩
    · split at hv'
      · rename_i hlt
        obtain ⟨w, hw, hb⟩ := ih (j - 1 - u') (by omega) (by omega) hv'
        have hstep : d.params.length - 1 - (j - 1 - u') ∈ tyVarsOf d c (d.params.length - 1 - j) := by
          unfold tyVarsOf
          rw [varType_param (by omega)]
          dsimp only
          rw [if_pos (by omega), show d.params.length - 1 - (d.params.length - 1 - j) = j by omega]
          exact List.mem_map.2 ⟨u', hu', by omega⟩
        exact ⟨w, .step _ _ _ _ hstep (hw.mono (by omega)), hb⟩
      · cases hv'

/-- The telescope rule ([Ind]: a field's type mentions only the parameters and the earlier fields), in
the checker's own form (`IndDecl.fieldRefs`). -/
def TeleOk (d : IndDecl) : Prop :=
  ∀ c i FT, fieldTerm d c i = some FT → ∀ r ∈ d.fieldRefs c FT, r < i

theorem tele_var {d : IndDecl} {c i : Nat} {FT : Term} (ht : TeleOk d) (hFT : fieldTerm d c i = some FT)
    {v : Nat} (hv : v ∈ FT.freeVars) (h1 : d.params.length ≤ v) (h2 : v < d.params.length + DataLib.arity d c) :
    d.params.length + DataLib.arity d c - 1 - v < i := by
  apply ht c i FT hFT
  unfold IndDecl.fieldRefs
  refine List.mem_filterMap.2 ⟨v, hv, ?_⟩
  have : ((d.ctors[c]?).map (·.2.length)).getD 0 = DataLib.arity d c := rfl
  simp only [this, h1, h2, decide_true, Bool.and_self, if_true]

theorem reach_field (ht : TeleOk d) : ∀ (jf : Nat), jf < DataLib.arity d c → fieldVaries d c jf = true →
    ∃ w, ReachIn d c (jf + d.params.length + 1) (d.params.length + DataLib.arity d c - 1 - jf) w ∧ BadVar d c w := by
  intro jf
  induction jf using Nat.strongRecOn with
  | ind jf ih =>
    intro hj hv
    rw [fieldVaries] at hv
    cases hFT : fieldTerm d c jf with
    | none => rw [hFT] at hv; cases hv
    | some FT =>
      rw [hFT] at hv
      simp only [Bool.or_eq_true, List.any_eq_true] at hv
      have hvt : d.varType c (d.params.length + DataLib.arity d c - 1 - jf) = some FT := by
        rw [varType_field (by omega) (by omega), show d.params.length + DataLib.arity d c - 1 -
          (d.params.length + DataLib.arity d c - 1 - jf) = jf by omega, hFT]
      have hty : tyVarsOf d c (d.params.length + DataLib.arity d c - 1 - jf) = FT.freeVars := by
        unfold tyVarsOf; rw [hvt]; dsimp only; rw [if_neg (by omega)]
      rcases hv with hm | ⟨v, hvm, hv'⟩
      · exact ⟨_, .refl _ _, .inr ⟨by omega, FT, hvt, hm⟩⟩
      · by_cases h1 : v < d.params.length
        · rw [if_pos h1] at hv'
          obtain ⟨w, hw, hb⟩ := reach_param (c := c) (d.params.length - 1 - v) (by omega) hv'
          rw [show d.params.length - 1 - (d.params.length - 1 - v) = v by omega] at hw
          exact ⟨w, .step (jf + d.params.length) _ v _ (by rw [hty]; exact hvm) (hw.mono (by omega)), hb⟩
        · rw [if_neg h1] at hv'
          by_cases h2 : v < d.params.length + DataLib.arity d c
          · rw [if_pos h2] at hv'
            have hlt := tele_var ht hFT hvm (by omega) h2
            rw [dif_pos hlt] at hv'
            obtain ⟨w, hw, hb⟩ := ih _ hlt (by omega) hv'
            rw [show d.params.length + DataLib.arity d c - 1 - (d.params.length + DataLib.arity d c - 1 - v) = v by omega] at hw
            exact ⟨w, .step (jf + d.params.length) _ v _ (by rw [hty]; exact hvm) (hw.mono (by omega)), hb⟩
          · rw [if_neg h2] at hv'; cases hv'

/-- **A varying variable reaches a bad one** within `np + k` steps through declared types. -/
theorem reach_varies (ht : TeleOk d) {v : Nat} (hv : varVaries d c v = true) :
    ∃ w, ReachIn d c (d.params.length + DataLib.arity d c) v w ∧ BadVar d c w := by
  unfold varVaries at hv
  by_cases h1 : v < d.params.length
  · rw [if_pos h1] at hv
    obtain ⟨w, hw, hb⟩ := reach_param (c := c) (d.params.length - 1 - v) (by omega) hv
    rw [show d.params.length - 1 - (d.params.length - 1 - v) = v by omega] at hw
    exact ⟨w, hw.mono (by omega), hb⟩
  · rw [if_neg h1] at hv
    by_cases h2 : v < d.params.length + DataLib.arity d c
    · rw [if_pos h2] at hv
      obtain ⟨w, hw, hb⟩ := reach_field ht _ (by omega) hv
      rw [show d.params.length + DataLib.arity d c - 1 - (d.params.length + DataLib.arity d c - 1 - v) = v by omega] at hw
      exact ⟨w, hw.mono (by omega), hb⟩
    · rw [if_neg h2] at hv; cases hv

/-- **A term reading a varying variable deep-reads a bad one** (`deepVars`, the checker's reads). -/
theorem deepVars_bad (ht : TeleOk d) {t : Term} {v : Nat} (hv : v ∈ t.freeVars) (hvv : varVaries d c v = true) :
    ∃ w ∈ d.deepVars c t, BadVar d c w := by
  obtain ⟨w, hw, hb⟩ := reach_varies ht hvv
  exact ⟨w, mem_deepVars hv (by rw [fs_length]; exact hw), hb⟩

end Ochr.Meaning.DataModel.Exists.Knot

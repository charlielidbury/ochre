import Ochr.Meaning.Steps.Machine.CheckItem
import Ochr.Meaning.DataModel.Exists.Knot.Checks

/-!
# `CheckIndGivesChecks`, toward a proof (machine10)

The bridge from `checkInd`'s accepted run to `Knot.IndChecks` (`DataModel/Exists/Knot/Checks.lean`). Proved here,
the pieces (standard axioms):

* `runs_forIn_all`: every element of a loop whose body always continues was visited, from a state with the
  start's tables;
* `runs_fieldTele_vals`: `fieldTele` (all fields) ran its continuation at every field of the constructor;
* `firstOrder_foB`: `firstOrderTerm` accepting gives the pure mirror `Knot.foB` at the state's declarations
  (and `firstOrderArgs` gives `foArgsB`; `firstOrderCallArgs` gives that no argument mentions the type);
* `readViolation_rvB`: `readViolation` finding none gives `Knot.rvB … = false`.

Left (machine10's handoff): the assembly, a second peel of `checkInd` as in `CheckItem.runs_checkInd_tables` that
keeps `declared`'s answer (freshness), the [Ind] loop's `late.isEmpty` (`TeleOk`), and, through
`runs_forIn_all` and `runs_fieldTele_vals`, the continuation's run at every field (its `firstOrderTerm`,
`readViolation` and `sortNestViolation` answers), at a state whose declarations are `declEnv` (the stub's).
-/

namespace Ochr.Meaning.Steps.Machine

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.DecideScope Ochr.Meaning.Steps.Slice
open Ochr.Meaning.Steps.Form

/-- **Every element of a loop whose body always continues was visited**, from a state with the tables of the
start (each body only grows them). -/
theorem runs_forIn_all {α β : Type} {xs : List α} {b : β} {body : α → β → M (ForInStep β)}
    (hg : ∀ a b, GrowsM (body a b))
    (hy : ∀ a b s bh y s', Runs (body a b) s bh y s' → ∃ b', y = .yield b') :
    ∀ {s s' : MState} {bh : Nat} {r : β}, Runs (forIn xs b body) s bh r s' →
      TablesGrow s s' ∧ ∀ a ∈ xs, ∃ b' s₁ bh₁ y s₂, TablesGrow s s₁ ∧ Runs (body a b') s₁ bh₁ y s₂ := by
  induction xs generalizing b with
  | nil =>
    intro s s' bh r h
    rw [List.forIn_nil] at h
    obtain ⟨_, rfl⟩ := runs_pure_inv h
    exact ⟨TablesGrow.refl _, fun a ha => absurd ha List.not_mem_nil⟩
  | cons a as ih =>
    intro s s' bh r h
    rw [List.forIn_cons] at h
    obtain ⟨y, s₁, b₁, h₁, h₂⟩ := Runs.bind_inv h
    obtain ⟨b', rfl⟩ := hy _ _ _ _ _ _ h₁
    have hg₁ := Runs.grows (hg a b) h₁
    obtain ⟨hT, hall⟩ := ih (b := b') h₂
    refine ⟨hg₁.trans hT, fun a' ha' => ?_⟩
    rcases List.mem_cons.1 ha' with rfl | ha'
    · exact ⟨b, s, bh, _, s₁, TablesGrow.refl _, h₁⟩
    · obtain ⟨b'', s₃, bh₃, y₃, s₄, hT₃, h₃⟩ := hall a' ha'
      exact ⟨b'', s₃, bh₃, y₃, s₄, hg₁.trans hT₃, h₃⟩

set_option maxHeartbeats 8000000 in
/-- **`fieldTele` (all fields) called its continuation at every field**, from a state with the tables of the
start. -/
theorem runs_fieldTele_vals {f : Nat} {d : IndDecl} {ps : List Value} {c : Nat} {val : Nat → Value → M Value}
    (hval : ∀ j T, GrowsM (val j T)) {s s' : MState} {bh : Nat} {r : List (String × Value × Value)}
    (h : Runs (Ochr.fieldTele f d ps c val none) s bh r s') :
    ∀ j fname FT, (((d.ctors[c]?).map (·.2)).getD [])[j]? = some (fname, FT) →
      ∃ T s₁ bh₁ v s₂, TablesGrow s s₁ ∧ Runs (val j T) s₁ bh₁ v s₂ := by
  have hET : ∀ (G : Tab) (f : Nat) (t : Term), GrowsIn G (Ochr.evalType f t) := fun G f => (machineGrows f).evalType
  have hval' : ∀ (G : Tab) j T, GrowsIn G (val j T) := fun G j T => growsIn_of_growsM (hval j T)
  cases f with
  | zero => unfold Ochr.fieldTele at h; simp only [runs_exhausted_iff] at h
  | succ k =>
  unfold Ochr.fieldTele at h
  dsimp (config := { proj := false }) only at h
  intro j fname FT hj
  rcases hc : d.ctors[c]? with _ | ⟨cn, fields⟩
  · rw [hc] at h
    exact (runs_err_false h).elim
  rw [hc] at hj
  simp only [Option.map_some, Option.getD_some] at hj
  rw [hc] at h
  dsimp (config := { proj := false }) only at h
  by_cases hp : (ps.length != d.params.length) = true
  · rw [if_pos hp] at h
    obtain ⟨_, _, _, he, _⟩ := Runs.bind_inv h; exact (runs_err_false he).elim
  rw [if_neg hp] at h
  obtain ⟨_, s₁, b₁, hg₁, h⟩ := Runs.grows_bind (fun G => by grows_goI) h
  obtain ⟨r', s₂, b₂, h₂, -⟩ := Runs.bind_inv h
  replace h₂ := Runs.onFail_inv h₂
  obtain ⟨_, s₃, b₃, hg₃, h₂⟩ := Runs.grows_bind (fun G => by grows_goI) h₂
  obtain ⟨_, s₄, b₄, hg₄, h₂⟩ := Runs.grows_bind (fun G => by grows_goI) h₂
  obtain ⟨top, s₅, b₅, hg₅, h₂⟩ := Runs.grows_bind (fun G => by grows_goI) h₂
  obtain ⟨out, s₆, b₆, h₆, -⟩ := Runs.bind_inv h₂
  obtain ⟨-, hall⟩ := runs_forIn_all (fun a b => growsM_of_growsIn fun G => by grows_goI)
    (fun a b s bh y s' hr => by
      obtain ⟨_, _, _, _, hr⟩ := Runs.bind_inv hr
      obtain ⟨_, _, _, _, hr⟩ := Runs.bind_inv hr
      obtain ⟨_, _, _, _, hr⟩ := Runs.bind_inv hr
      obtain ⟨_, _, _, _, hr⟩ := Runs.bind_inv hr
      exact ⟨_, (runs_pure_inv hr).1⟩) h₆
  obtain ⟨b', s₇, b₇, y, s₈, hT₇, h₇⟩ := hall ((fname, FT), j) (List.mem_zipIdx_iff_getElem?.2 hj)
  obtain ⟨T, s₉, b₉, hg₉, h₇⟩ := Runs.grows_bind (fun G => by grows_goI) h₇
  obtain ⟨v, s₁₀, b₁₀, h₁₀, -⟩ := Runs.bind_inv h₇
  exact ⟨T, s₉, b₉, v, s₁₀, ((((hg₁.trans hg₃).trans hg₄).trans hg₅).trans hT₇).trans hg₉, h₁₀⟩

theorem runs_lookupInd_inv {m : String} {s s' : MState} {b : Nat} {dm : IndDecl} (h : Runs (lookupInd m) s b dm s') :
    s.inds.find? (·.name == m) = some dm ∧ s' = s := by
  unfold lookupInd at h
  rw [runs_get_bind] at h
  split at h
  · rename_i d hd
    obtain ⟨rfl, rfl⟩ := runs_pure_inv h
    exact ⟨hd, rfl⟩
  · exact (runs_err_false h).elim

/-- **`firstOrderTerm` accepting gives its pure mirror** `Knot.foB`, at the declarations of the state it ran in. -/
theorem firstOrder_foB (nest : NestTable) (n : String) (np k : Nat) :
    (∀ t, ∀ {s s' : MState} {b : Nat}, Runs (firstOrderTerm nest n np k t) s b true s' →
      DataModel.Exists.Knot.foB s.inds nest n np t = true) ∧
    (∀ as, ∀ {s s' : MState} {b : Nat}, Runs (firstOrderCallArgs nest n np k as) s b true s' →
      Term.mentionsTypeList n as = false) ∧
    (∀ m dm i as, ∀ {s s' : MState} {b : Nat}, Runs (firstOrderArgs nest n np k m dm i as) s b true s' →
      DataModel.Exists.Knot.foArgsB s.inds nest n np m dm i as = true) := by
  refine firstOrderTerm.mutual_induct n
    (fun t => ∀ {s s' : MState} {b : Nat}, Runs (firstOrderTerm nest n np k t) s b true s' →
      DataModel.Exists.Knot.foB s.inds nest n np t = true)
    (fun as => ∀ {s s' : MState} {b : Nat}, Runs (firstOrderCallArgs nest n np k as) s b true s' →
      Term.mentionsTypeList n as = false)
    (fun m dm i as => ∀ {s s' : MState} {b : Nat}, Runs (firstOrderArgs nest n np k m dm i as) s b true s' →
      DataModel.Exists.Knot.foArgsB s.inds nest n np m dm i as = true)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intros; rfl
  · intros; rfl
  · intro j s s' b h
    unfold firstOrderTerm at h
    obtain ⟨he, -⟩ := runs_pure_inv h
    simp only [DataModel.Exists.Knot.foB]; exact he.symm
  · intro m as ih s s' b h
    unfold firstOrderTerm at h
    obtain ⟨dm, s₁, b₁, h₁, h₂⟩ := Runs.bind_inv h
    obtain ⟨hf, rfl⟩ := runs_lookupInd_inv h₁
    simp only [DataModel.Exists.Knot.foB, hf]
    exact ih dm h₂
  · intro f as hd ih s s' b h
    unfold firstOrderTerm at h
    rw [runs_get_bind] at h
    have key : Term.mentionsTypeList n as = false := by
      split at h
      · split at h
        · split at h
          · exact ih h
          · exact absurd (runs_pure_inv h).1 Bool.noConfusion
        · exact absurd (runs_pure_inv h).1 Bool.noConfusion
      · exact absurd (runs_pure_inv h).1 Bool.noConfusion
    simp only [DataModel.Exists.Knot.foB, key]; rfl
  · intro A a b' hm s s' b h
    unfold firstOrderTerm at h
    rw [if_pos hm] at h
    exact absurd (runs_pure_inv h).1 Bool.noConfusion
  · intro A a b' hm _ s s' b h
    simp only [Bool.not_eq_true] at hm
    simp only [DataModel.Exists.Knot.foB]
    simp only [Bool.or_eq_false_iff] at hm
    rw [hm.1.1, hm.1.2, hm.2]; rfl
  · intro t h1 h2 h3 h4 h5 h6 s s' b h
    unfold firstOrderTerm at h
    split at h
    all_goals first
      | exact absurd rfl (h1)
      | exact absurd rfl h2
      | exact absurd rfl (h3 _)
      | exact absurd rfl (h4 _ _)
      | exact absurd rfl (h5 _ _ _)
      | exact absurd rfl (h6 _ _ _)
      | exact absurd (runs_pure_inv h).1 Bool.noConfusion
  · intros; rfl
  · intro t ts _ ih s s' b h
    unfold firstOrderCallArgs at h
    obtain ⟨ok, s₁, b₁, h₁, h₂⟩ := Runs.bind_inv h
    cases ok
    · rw [if_neg Bool.false_ne_true] at h₂; exact absurd (runs_pure_inv h₂).1 Bool.noConfusion
    rw [if_pos rfl] at h₂
    have hm : Term.mentionsType n t = false := by
      cases hmt : Term.mentionsType n t
      · rfl
      · rw [if_pos hmt] at h₁; exact absurd (runs_pure_inv h₁).1 Bool.noConfusion
    simp only [Term.mentionsTypeList, hm, ih h₂, Bool.or_false]
  · intros; rfl
  · intro m dm i t ts ih1 ih2 s s' b h
    unfold firstOrderArgs at h
    obtain ⟨ok, s₁, b₁, h₁, h₂⟩ := Runs.bind_inv h
    cases ok
    · rw [if_neg Bool.false_ne_true] at h₂; exact absurd (runs_pure_inv h₂).1 Bool.noConfusion
    rw [if_pos rfl] at h₂
    have hT := Runs.grows (growsM_of_growsIn fun G => by grows_goI) h₁
    have hrest := ih2 h₂
    rw [hT.inds] at hrest
    simp only [DataModel.Exists.Knot.foArgsB, hrest, Bool.and_true]
    by_cases hp : dm.paramIsType i = true
    · rw [if_neg (by simp [hp])] at h₁
      obtain ⟨c, s₂, b₂, h₃, h₄⟩ := Runs.bind_inv h₁
      cases c
      · rw [if_neg Bool.false_ne_true] at h₄; exact absurd (runs_pure_inv h₄).1 Bool.noConfusion
      rw [if_pos rfl] at h₄
      have hT₂ := Runs.grows (growsM_of_growsIn fun G => by grows_goI) h₃
      have hfo := ih1 h₃
      rw [if_pos hp, hfo, (runs_pure_inv h₄).1.symm]; rfl
    · rw [if_pos (by simp [hp])] at h₁
      rw [if_neg hp, (runs_pure_inv h₁).1.symm]

/-- **`readViolation` finding none gives its pure mirror** `Knot.rvB` false, at the declarations of the state. -/
theorem readViolation_rvB (reads : Term → Option Nat) :
    (∀ t, ∀ {s s' : MState} {b : Nat}, Runs (readViolation reads t) s b none s' →
      DataModel.Exists.Knot.rvB s.inds reads t = false) ∧
    (∀ m dm i as, ∀ {s s' : MState} {b : Nat}, Runs (readViolationArgs reads m dm i as) s b none s' →
      DataModel.Exists.Knot.rvArgsB s.inds reads dm i as = false) := by
  refine readViolation.mutual_induct reads
    (fun t => ∀ {s s' : MState} {b : Nat}, Runs (readViolation reads t) s b none s' →
      DataModel.Exists.Knot.rvB s.inds reads t = false)
    (fun m dm i as => ∀ {s s' : MState} {b : Nat}, Runs (readViolationArgs reads m dm i as) s b none s' →
      DataModel.Exists.Knot.rvArgsB s.inds reads dm i as = false)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro m as ih s s' b h
    unfold readViolation at h
    obtain ⟨dm, s₁, b₁, h₁, h₂⟩ := Runs.bind_inv h
    obtain ⟨hf, rfl⟩ := runs_lookupInd_inv h₁
    simp only [DataModel.Exists.Knot.rvB, hf]
    exact ih dm h₂
  · intro f as hd s s' b h
    unfold readViolation at h
    have := (runs_pure_inv h).1
    simp only [DataModel.Exists.Knot.rvB]
    cases hr : reads (.call f as hd)
    · rfl
    · rw [hr] at this; cases this
  · intro A a b' s s' b h
    unfold readViolation at h
    have := (runs_pure_inv h).1
    simp only [DataModel.Exists.Knot.rvB]
    cases hr : reads (.eq A a b')
    · rfl
    · rw [hr] at this; cases this
  · intro t h1 h2 h3 s s' b h
    unfold DataModel.Exists.Knot.rvB
    split
    all_goals first
      | exact absurd rfl (h1 _ _)
      | exact absurd rfl (h2 _ _ _)
      | exact absurd rfl (h3 _ _ _)
      | rfl
  · intros; rfl
  · intro m dm i t ts hp ihr iht s s' b h
    unfold readViolationArgs at h
    rw [if_pos hp] at h
    obtain ⟨o, s₁, b₁, h₁, h₂⟩ := Runs.bind_inv h
    have hs := runs_keep ((keep_readViolation reads).1 t) h₁
    subst hs
    cases o
    · have := iht h₁
      simp only [DataModel.Exists.Knot.rvArgsB, if_pos hp, this, ihr h₂, Bool.or_false]
    · exact absurd (runs_pure_inv h₂).1 (by simp)
  · intro m dm i t ts hp u hu _ s s' b h
    unfold readViolationArgs at h
    rw [if_neg hp] at h
    simp only [hu] at h
    exact absurd (runs_pure_inv h).1 (by simp)
  · intro m dm i t ts hp hn ihr s s' b h
    unfold readViolationArgs at h
    rw [if_neg hp] at h
    have hr : reads t = none := by
      cases h' : reads t
      · rfl
      · exact (hn _ h').elim
    simp only [hr] at h
    simp only [DataModel.Exists.Knot.rvArgsB, if_neg hp, hr, Option.isSome_none, Bool.false_or]
    exact ihr h

end Ochr.Meaning.Steps.Machine

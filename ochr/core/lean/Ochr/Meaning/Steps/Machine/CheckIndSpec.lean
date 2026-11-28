import Ochr.Meaning.Steps.Machine.CheckIndChecks

/-!
# `CheckIndGivesChecks`, proved (exists12, from machine10's pieces and plan)

The bridge from `checkInd`'s accepted run to `Knot.IndChecks` (`DataModel/Exists/Knot/Checks.lean`), the one
part of `Assembly.ItemFacts` machine10 left open (`CheckIndChecks.lean`'s handoff: "a second peel of `checkInd`
as in `CheckItem.runs_checkInd_tables` that keeps `declared`'s answer, the [Ind] loop's `late.isEmpty`, and,
through `runs_forIn_all` and `runs_fieldTele_vals`, the continuation's run at every field").

* `runs_checkInd_peel`: the declared test's answer (the name is fresh among the declarations) and the [Ind]
  loop (`TeleOk`);
* `runs_checkInd_fields`: at every field, the continuation `fieldTele` runs passed `firstOrderTerm` (its mirror
  `foB`, by `firstOrder_foB`), `readViolation` (`rvB`, by `readViolation_rvB`) and `sortNestViolation`, at a
  state whose declarations are `declEnv`'s (the stub's), with the nesting table `ownNest`;
* `checkIndGivesChecks`: the assembly.

The continuation is one large term in which the do-notation copies each `if`'s continuation into both arms, so
hypothesis-side `split` exceeds simp's step limit (machine11's trap 4); each `if` is taken apart with
`runs_ite_inv` and each `match` on a run's result with `rcases` on the result. A hypothesis that `subst`
reintroduces after a newer one of the same name takes the name back (the trap of `hC` here): clear the old one.
-/

namespace Ochr.Meaning.Steps.Machine
open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.DecideScope Ochr.Meaning.Steps.Slice
open Ochr.Meaning.Steps.Form

theorem runs_discard_inv' {α : Type} {x : M α} {st st' : MState} {b : Nat} {u : PUnit}
    (h : Runs (discard x) st b u st') : ∃ a, Runs x st b a st' := by
  have e : (discard x : M PUnit) = x >>= fun _ => pure PUnit.unit := by
    simp only [discard, Functor.mapConst, Function.comp_def]
    rfl
  rw [e] at h
  obtain ⟨a, s₁, b₁, h₁, h₂⟩ := Runs.bind_inv h
  obtain ⟨-, rfl⟩ := runs_pure_inv h₂
  exact ⟨a, h₁⟩

/-- A run of an `if`: one branch, with its condition. -/
theorem runs_ite_inv {α : Type} {c : Prop} [Decidable c] {x y : M α} {s s' : MState} {b : Nat} {a : α}
    (h : Runs (if c then x else y) s b a s') : (c ∧ Runs x s b a s') ∨ (¬ c ∧ Runs y s b a s') := by
  by_cases hc : c
  · rw [if_pos hc] at h; exact .inl ⟨hc, h⟩
  · rw [if_neg hc] at h; exact .inr ⟨hc, h⟩

theorem runs_throw_false {α : Type} {e : Fail} {a : α} {st st' : MState} {b : Nat}
    (h : Runs (throw e : M α) st b a st') : False := by
  obtain ⟨L, left, log, h⟩ := h
  cases h

/-- **`undeclaredCheck` passing**: no name its terms mention is undeclared, at the state's tables. -/
theorem runs_undeclaredCheck_inv {self own : Option String} {ts : List Term} {s s' : MState} {b : Nat} {u : Unit}
    (h : Runs (undeclaredCheck self ts own) s b u s') :
    Term.undeclaredList (fun m => s.globals.any (·.name == m))
      (fun m => self == some m || (own != some m && s.inds.any (·.name == m))) ts = none := by
  unfold undeclaredCheck at h
  rw [runs_get_bind] at h
  dsimp only at h
  split at h
  · assumption
  · exact (runs_throw_false h).elim

/-- A run of `x >>= k` keeping `x`'s run and its growth. -/
theorem Runs.grows_bind' {α β : Type} {x : M α} {k : α → M β} {s s' : MState} {b : Nat} {r : β}
    (hx : ∀ G, GrowsIn G x) (h : Runs (x >>= k) s b r s') :
    ∃ a s₁ b₁, TablesGrow s s₁ ∧ Runs x s b a s₁ ∧ Runs (k a) s₁ b₁ r s' := by
  obtain ⟨a, s₁, b₁, h₁, h₂⟩ := Runs.bind_inv h
  exact ⟨a, s₁, b₁, Runs.grows (growsM_of_growsIn hx) h₁, h₁, h₂⟩

set_option maxHeartbeats 8000000 in
theorem runs_checkInd_peel {d : IndDecl} {st st' : MState} {b : Nat} (h : Runs (checkInd d) st b () st') :
    (st.inds.any fun e => e.name == d.name || e.ctors.any (·.1 == d.name)) = false ∧ DataModel.Exists.Knot.TeleOk d := by
  have hET : ∀ (G : Tab) (f : Nat) (t : Term), GrowsIn G (Ochr.evalType f t) := fun G f => (machineGrows f).evalType
  have hFT : ∀ (G : Tab) (f : Nat) (d : IndDecl) (ps : List Value) (c : Nat) (val : Nat → Value → M Value),
      (∀ i v, GrowsIn G (val i v)) → ∀ upto, GrowsIn G (Ochr.fieldTele f d ps c val upto) :=
    fun G f => (machineGrows f).fieldTele
  unfold checkInd at h
  dsimp (config := { proj := false }) only at h
  obtain ⟨c, s₁, b₁, hd, h⟩ := Runs.bind_inv h
  obtain ⟨hc, hs₁⟩ := runs_declared_inv hd
  subst hs₁
  clear hd
  cases c
  case true =>
    rw [if_pos rfl] at h
    obtain ⟨_, _, _, he, _⟩ := Runs.bind_inv h; exact (runs_err_false he).elim
  rw [if_neg Bool.false_ne_true] at h
  obtain ⟨_, s₂, b₂, hg₂, h⟩ := Runs.grows_bind (fun G => by grows_goI) h
  by_cases hsort : d.sort > 1
  · rw [if_pos hsort] at h
    obtain ⟨_, _, _, he, _⟩ := Runs.bind_inv h; exact (runs_err_false he).elim
  rw [if_neg hsort] at h
  rw [runs_get_bind, runs_get_bind, runs_modify_bind] at h
  obtain ⟨_, s₃, b₃, hg₃, h⟩ := Runs.grows_bind (fun G => by grows_goI) h
  obtain ⟨_, s₄, b₄, hg₄, hL, h⟩ := Runs.grows_bind' (fun G => by grows_goI) h
  obtain ⟨_, s₅, b₅, hg₅, h⟩ := Runs.grows_bind (fun G => by grows_goI) h
  obtain ⟨x, s₆, b₆, hg₆, hTel, h⟩ := Runs.grows_bind' (fun G => by grows_goI) h
  obtain ⟨sc, ns, l⟩ := x
  obtain ⟨_, s₇a, b₇a, hg₇a, h128, h⟩ := Runs.grows_bind' (fun G => by grows_goI) h
  obtain ⟨_, s₇, b₇, hg₇, hTP, h⟩ := Runs.grows_bind' (fun G => by grows_goI) h
  obtain ⟨_, s₇b, b₇b, hg₇b, hUP, h⟩ := Runs.grows_bind' (fun G => by grows_goI) h
  obtain ⟨_, s₈, b₈, hg₈, hUF, h⟩ := Runs.grows_bind' (fun G => by grows_goI) h
  obtain ⟨_, s₈b, b₈b, hg₈b, hHD, h⟩ := Runs.grows_bind' (fun G => by grows_goI) h
  obtain ⟨ps, s₉, b₉, hg₉, hPs, h⟩ := Runs.grows_bind' (fun G => by grows_goI) h
  obtain ⟨_, s₁₀, b₁₀, hg₁₀, hFL, h⟩ := Runs.grows_bind' (fun G => by grows_goI) h
  -- the [Ind] loop: every field's later references are empty
  obtain ⟨-, hallC⟩ := runs_forIn_all (fun a b => growsM_of_growsIn fun G => by grows_goI)
    (fun a b s bh y s' hr => by
      obtain ⟨_, _, _, _, hr⟩ := Runs.bind_inv hr
      exact ⟨_, (runs_pure_inv hr).1⟩) hL
  refine ⟨?_, ?_⟩
  · cases e : (s₁.inds.any fun e => e.name == d.name || e.ctors.any (·.1 == d.name))
    · rfl
    · rw [e, Bool.or_true] at hc; cases hc
  intro c i FT hFT
  unfold fieldTerm at hFT
  obtain ⟨⟨fname, FT'⟩, h1, h2⟩ := Option.map_eq_some_iff.1 hFT
  obtain ⟨⟨cn, fields⟩, h3, h4⟩ := Option.bind_eq_some_iff.1 h1
  simp only at h2
  subst h2
  obtain ⟨b', s₁', bh₁, y, s₂', -, hB⟩ := hallC ((cn, fields), c) (List.mem_zipIdx_iff_getElem?.2 h3)
  obtain ⟨_, s₃', b₃', hI, -⟩ := Runs.bind_inv hB
  obtain ⟨-, hallF⟩ := runs_forIn_all (fun a b => growsM_of_growsIn fun G => by grows_goI)
    (fun a b s bh y s' hr => by
      dsimp only at hr
      split at hr
      · exact ⟨_, (runs_pure_inv hr).1⟩
      · obtain ⟨_, _, _, he, _⟩ := Runs.bind_inv hr; exact (runs_err_false he).elim) hI
  obtain ⟨_, _, _, _, _, -, hF⟩ := hallF ((fname, FT'), i) (List.mem_zipIdx_iff_getElem?.2 h4)
  dsimp only at hF
  split at hF
  · rename_i he
    intro r hr
    rcases Nat.lt_or_ge r i with hlt | hge
    · exact hlt
    · have hmem : r ∈ (d.fieldRefs c FT').filter (fun x => decide (x ≥ i)) := List.mem_filter.2 ⟨hr, by simp; omega⟩
      rw [List.isEmpty_iff.1 he] at hmem
      cases hmem
  · obtain ⟨_, _, _, he, _⟩ := Runs.bind_inv hF; exact (runs_err_false he).elim

set_option maxHeartbeats 8000000 in
theorem runs_checkInd_fields {d : IndDecl} {st st' : MState} {b : Nat} (h : Runs (checkInd d) st b () st') :
    let d' : IndDecl := { d with nestable := nestableSet (nestTableOf st.inds) (sortTableOf st.inds d) d }
    ∀ (c : Nat) (cn : String) (fields : List (String × Term)), d.ctors[c]? = some (cn, fields) →
    ∀ (j : Nat) (fname : String) (FT : Term), fields[j]? = some (fname, FT) →
      DataModel.Exists.Knot.foB (DataModel.Exists.Knot.declEnv st.inds d') (DataModel.Exists.Knot.ownNest st.inds d')
          d.name d.params.length FT = true ∧
        DataModel.Exists.Knot.rvB (DataModel.Exists.Knot.declEnv st.inds d') (DataModel.Exists.Knot.readsOf d' c) FT = false ∧
        sortNestViolation (sortTableOf st.inds d') d.name d.sort FT = none := by
  have hET : ∀ (G : Tab) (f : Nat) (t : Term), GrowsIn G (Ochr.evalType f t) := fun G f => (machineGrows f).evalType
  have hFT : ∀ (G : Tab) (f : Nat) (d : IndDecl) (ps : List Value) (c : Nat) (val : Nat → Value → M Value),
      (∀ i v, GrowsIn G (val i v)) → ∀ upto, GrowsIn G (Ochr.fieldTele f d ps c val upto) :=
    fun G f => (machineGrows f).fieldTele
  unfold checkInd at h
  dsimp (config := { proj := false }) only at h
  obtain ⟨c, s₁, b₁, hd, h⟩ := Runs.bind_inv h
  obtain ⟨hc, hs₁⟩ := runs_declared_inv hd
  subst hs₁
  clear hd
  cases c
  case true =>
    rw [if_pos rfl] at h
    obtain ⟨_, _, _, he, _⟩ := Runs.bind_inv h; exact (runs_err_false he).elim
  rw [if_neg Bool.false_ne_true] at h
  obtain ⟨_, s₂, b₂, hg₂, h⟩ := Runs.grows_bind (fun G => by grows_goI) h
  by_cases hsort : d.sort > 1
  · rw [if_pos hsort] at h
    obtain ⟨_, _, _, he, _⟩ := Runs.bind_inv h; exact (runs_err_false he).elim
  rw [if_neg hsort] at h
  rw [runs_get_bind, runs_get_bind, runs_modify_bind] at h
  intro d'
  obtain ⟨_, s₃, b₃, hg₃, h⟩ := Runs.grows_bind (fun G => by grows_goI) h
  obtain ⟨_, s₄, b₄, hg₄, hL, h⟩ := Runs.grows_bind' (fun G => by grows_goI) h
  obtain ⟨_, s₅, b₅, hg₅, h⟩ := Runs.grows_bind (fun G => by grows_goI) h
  obtain ⟨x, s₆, b₆, hg₆, hTel, h⟩ := Runs.grows_bind' (fun G => by grows_goI) h
  obtain ⟨sc, ns, l⟩ := x
  obtain ⟨_, s₇a, b₇a, hg₇a, h128, h⟩ := Runs.grows_bind' (fun G => by grows_goI) h
  obtain ⟨_, s₇, b₇, hg₇, hTP, h⟩ := Runs.grows_bind' (fun G => by grows_goI) h
  obtain ⟨_, s₇b, b₇b, hg₇b, hUP, h⟩ := Runs.grows_bind' (fun G => by grows_goI) h
  obtain ⟨_, s₈, b₈, hg₈, hUF, h⟩ := Runs.grows_bind' (fun G => by grows_goI) h
  obtain ⟨_, s₈b, b₈b, hg₈b, hHD, h⟩ := Runs.grows_bind' (fun G => by grows_goI) h
  obtain ⟨ps, s₉, b₉, hg₉, hPs, h⟩ := Runs.grows_bind' (fun G => by grows_goI) h
  obtain ⟨_, s₁₀, b₁₀, hg₁₀, hFL, h⟩ := Runs.grows_bind' (fun G => by grows_goI) h
  obtain ⟨-, hallC⟩ := runs_forIn_all (fun a b => growsM_of_growsIn fun G => by grows_goI)
    (fun a b s bh y s' hr => by
      obtain ⟨_, _, _, _, hr⟩ := Runs.bind_inv hr
      obtain ⟨_, _, _, _, hr⟩ := Runs.bind_inv hr
      exact ⟨_, (runs_pure_inv hr).1⟩) hFL
  have hs2 : s₂.inds = s₁.inds := hg₂.inds
  have hT9 : s₉.inds = s₁.inds ++ [{ d' with ctors := [], nestable := [], declaring := true }] := by
    rw [hg₉.inds, hg₈b.inds, hg₈.inds, hg₇b.inds, hg₇.inds, hg₇a.inds, hg₆.inds, hg₅.inds, hg₄.inds, hg₃.inds]
    show s₂.inds ++ _ = _
    rw [hs2]
  intro c cn fields hc j fname FT hj
  obtain ⟨b', s₁', bh₁, y, s₂', hT₁, hB⟩ := hallC ((cn, fields), c) (List.mem_zipIdx_iff_getElem?.2 hc)
  obtain ⟨f, s₃', b₃', hfl, hB⟩ := Runs.bind_inv hB
  obtain ⟨_, s₄', b₄', hTele, -⟩ := Runs.bind_inv hB
  obtain ⟨_, hTele⟩ := runs_discard_inv' hTele
  have hv := runs_fieldTele_vals (fun j T => growsM_of_growsIn fun G => by grows_goI) hTele
  obtain ⟨T, s₅', b₅', v, s₆', hT₅, hC⟩ := hv j fname FT (by
    show (((d.ctors[c]?).map (·.2)).getD [])[j]? = _
    rw [hc]; exact hj)
  have hfj : fields[j]! = (fname, FT) := by simp [getElem!_def, hj]
  have h3' : s₃' = s₁' := runs_keep keep_fuelLeft hfl
  rcases runs_ite_inv hC with ⟨-, hC⟩ | ⟨-, hC⟩
  · exact (runs_err_bind_false hC).elim
  obtain ⟨fl, s₇', b₇', hfl7, hC⟩ := Runs.bind_inv hC
  have h7 : s₇' = s₅' := runs_keep keep_fuelLeft hfl7
  obtain ⟨lv, s₈', b₈', hSort, hC⟩ := Runs.bind_inv hC
  have hg8 := Runs.grows (growsM_of_growsIn fun G => by grows_goI) hSort
  rcases runs_ite_inv hC with ⟨-, hC⟩ | ⟨-, hC⟩
  · exact (runs_err_bind_false hC).elim
  obtain ⟨nv, s₉', b₉', hNV, hC⟩ := Runs.bind_inv hC
  have h9 : s₉' = s₈' := runs_keep ((keep_nestViolation _ _ _ _).1 _) hNV
  rcases nv with _ | ⟨m, a, why⟩
  rotate_left
  · exact (runs_err_bind_false hC).elim
  obtain ⟨fo, s₁₀', b₁₀', hFO, hC⟩ := Runs.bind_inv hC
  have h10 : s₁₀' = s₉' := runs_keep ((keep_firstOrder _ _ _ _).1 _) hFO
  have hI9 : s₉'.inds = DataModel.Exists.Knot.declEnv s₁.inds d' := by
    rw [h9, hg8.inds, h7, hT₅.inds, h3', hT₁.inds, hT9]; rfl
  rcases runs_ite_inv hC with ⟨h3, hC'⟩ | ⟨h3, hC'⟩
  · exact (runs_err_bind_false hC').elim
  clear hC
  have hfoT : fo = true := by simpa using h3
  subst hfoT
  have hC := hC'
  have hFOB : DataModel.Exists.Knot.foB (DataModel.Exists.Knot.declEnv s₁.inds d') (DataModel.Exists.Knot.ownNest s₁.inds d')
      d.name d.params.length FT = true := by
    have := (firstOrder_foB _ _ _ _).1 _ hFO
    rw [hI9] at this
    rw [hfj] at this
    rw [← this]
    congr 1
    funext m' j'
    simp only [DataModel.Exists.Knot.ownNest, hs2]
    rfl
  rcases runs_ite_inv hC with ⟨-, hC⟩ | ⟨-, hC⟩
  · exact (runs_err_bind_false hC).elim
  rcases runs_ite_inv hC with ⟨-, hC⟩ | ⟨-, hC⟩
  · obtain ⟨_, sa, _, hA1, hC⟩ := Runs.bind_inv hC
    obtain ⟨_, sb, _, hA2, hC⟩ := Runs.bind_inv hC
    obtain ⟨_, sc', _, hA3, hC⟩ := Runs.bind_inv hC
    obtain ⟨cp, sd, _, hA4, hC⟩ := Runs.bind_inv hC
    have hgA : TablesGrow s₁₀' sd :=
      (((Runs.grows (growsM_of_growsIn fun G => by grows_goI) hA1).trans
        (Runs.grows (growsM_of_growsIn fun G => by grows_goI) hA2)).trans
        (Runs.grows (growsM_of_growsIn fun G => by grows_goI) hA3)).trans
        (Runs.grows (growsM_of_growsIn fun G => by grows_goI) hA4)
    rcases runs_ite_inv hC with ⟨-, hC⟩ | ⟨-, hC⟩
    · have hRS : sd.inds = DataModel.Exists.Knot.declEnv s₁.inds d' := by rw [hgA.inds, h10, hI9]
      revert hC; rw [hfj]; intro hC
      obtain ⟨rv, sR, bR, hRV, hC⟩ := Runs.bind_inv hC
      rcases rv with _ | ⟨what, u⟩
      rotate_left
      · exact (runs_err_bind_false hC).elim
      generalize hsv : sortNestViolation (sortTableOf s₂.inds d) d.name d.sort FT = sv at hC
      rcases sv with _ | m'
      rotate_left
      · exact (runs_err_bind_false hC).elim
      exact ⟨hFOB, by rw [← hRS]; exact (readViolation_rvB _).1 _ hRV, by rw [← hsv, hs2]; rfl⟩
    · exact (runs_err_bind_false hC).elim
  · have hRS : s₁₀'.inds = DataModel.Exists.Knot.declEnv s₁.inds d' := by rw [h10, hI9]
    revert hC; rw [hfj]; intro hC
    obtain ⟨rv, sR, bR, hRV, hC⟩ := Runs.bind_inv hC
    rcases rv with _ | ⟨what, u⟩
    rotate_left
    · exact (runs_err_bind_false hC).elim
    generalize hsv : sortNestViolation (sortTableOf s₂.inds d) d.name d.sort FT = sv at hC
    rcases sv with _ | m'
    rotate_left
    · exact (runs_err_bind_false hC).elim
    exact ⟨hFOB, by rw [← hRS]; exact (readViolation_rvB _).1 _ hRV, by rw [← hsv, hs2]; rfl⟩

/-- **`CheckIndGivesChecks`, PROVED** (machine10's plan, assembled by exists12): an accepted `checkInd`
appends the entry `d'` (`d` with its nestable set) passing `Knot.IndChecks` at the declarations
before it: fresh (`declared`), the stored nestable set (`runs_checkInd_tables`), the telescope (the
[Ind] loop, `runs_checkInd_peel`), and at every field the three checks (`runs_checkInd_fields`). -/
theorem runs_checkInd_checks {d : IndDecl} {st st' : MState} {b : Nat} (hr : Runs (checkInd d) st b () st') :
    DataModel.Exists.Knot.IndChecks st.inds
      { d with nestable := nestableSet (nestTableOf st.inds) (sortTableOf st.inds d) d } := by
  obtain ⟨hfr, htele⟩ := runs_checkInd_peel hr
  have hF := runs_checkInd_fields hr
  refine ⟨?_, rfl, ?_, ?_, ?_, ?_⟩
  · rw [List.find?_eq_none]
    intro e he
    have := List.any_eq_false.1 hfr e he
    simp only [Bool.or_eq_true, not_or] at this
    simpa using this.1
  · exact htele
  all_goals
    intro c i FT hFT
    have hFT' := hFT
    unfold fieldTerm at hFT'
    obtain ⟨⟨fname, FT'⟩, h1, h2⟩ := Option.map_eq_some_iff.1 hFT'
    obtain ⟨⟨cn, fields⟩, h3, h4⟩ := Option.bind_eq_some_iff.1 h1
    simp only at h2
    subst h2
  · exact (hF c cn fields h3 i fname FT' h4).1
  · exact (hF c cn fields h3 i fname FT' h4).2.1
  · exact (hF c cn fields h3 i fname FT' h4).2.2

theorem checkIndGivesChecks : DataModel.Exists.Knot.CheckIndGivesChecks := by
  intro d st st' fuel hrun
  have hr := runs_of_runMachine_fst hrun
  exact ⟨_, (runs_checkInd_tables hr).2, runs_checkInd_checks hr⟩

end Ochr.Meaning.Steps.Machine

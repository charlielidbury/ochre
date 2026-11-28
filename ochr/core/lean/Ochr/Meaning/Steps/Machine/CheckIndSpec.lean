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

/-- **`firstOrderTerm` passing at a call**: the called global is found, with a stored type that is a written
Π-type whose codomain is a sort (`firstOrderTerm`'s call clause). With D140 (`runs_checkInd_heads`) the sort
is `Prop` or `Type`. -/
theorem runs_firstOrder_call {nest : NestTable} {n : String} {np k : Nat} {f : String} {as : List Term} {hd : Bool}
    {s s' : MState} {b : Nat}
    (h : Runs (firstOrderTerm nest n np k (.call (.const f) as hd)) s b true s') :
    ∃ g, s.globals.find? (·.name == f) = some g ∧
      ∃ cs hs ds l rd, g.ty = .tPi cs (.pi hs ds (.sort l)) rd := by
  rw [firstOrderTerm, runs_get_bind] at h
  split at h
  · rename_i g hg
    refine ⟨g, hg, ?_⟩
    split at h
    · rename_i cs hs ds cod rd hty
      split at h
      · rename_i l
        exact ⟨cs, hs, ds, l, rd, hty⟩
      all_goals first
        | (simp only [if_neg (by simp)] at h; cases (runs_pure_inv h).1)
        | (rw [if_neg (by simp)] at h; cases (runs_pure_inv h).1)
    · cases (runs_pure_inv h).1
  · cases (runs_pure_inv h).1

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
  -- main's D141: a parameter whose reading is "any" is rejected (the loop passing)
  obtain ⟨_, s₈a, b₈a, hg₈a, h141, h⟩ := Runs.grows_bind' (fun G => by grows_goI) h
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
        sortNestViolation (sortTableOf st.inds d') d.name d.sort FT = none ∧
        (∀ f as hd, FT = .call (.const f) as hd → ∃ g, st.globals.find? (·.name == f) = some g ∧
          ∃ cs hs ds l rd, g.ty = .tPi cs (.pi hs ds (.sort l)) rd) := by
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
  -- main's D141: a parameter whose reading is "any" is rejected (the loop passing)
  obtain ⟨_, s₈a, b₈a, hg₈a, h141, h⟩ := Runs.grows_bind' (fun G => by grows_goI) h
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
    rw [hg₉.inds, hg₈b.inds, hg₈a.inds, hg₈.inds, hg₇b.inds, hg₇.inds, hg₇a.inds, hg₆.inds, hg₅.inds, hg₄.inds, hg₃.inds]
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
  have hFOC : ∀ f as hd, FT = .call (.const f) as hd → ∃ g, s₁.globals.find? (·.name == f) = some g ∧
      ∃ cs hs ds l rd, g.ty = .tPi cs (.pi hs ds (.sort l)) rd := by
    intro f as hd hFTc
    have hFO' := hFO
    rw [hfj, hFTc] at hFO'
    obtain ⟨g, hg, rest⟩ := runs_firstOrder_call hFO'
    have hG : s₉'.globals = s₁.globals := by
      rw [h9, hg8.globals, h7, hT₅.globals, h3', hT₁.globals, hg₉.globals, hg₈b.globals, hg₈a.globals, hg₈.globals,
        hg₇b.globals, hg₇.globals, hg₇a.globals, hg₆.globals, hg₅.globals, hg₄.globals, hg₃.globals]
      exact hg₂.globals
    rw [hG] at hg
    exact ⟨g, hg, rest⟩
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
      exact ⟨hFOB, by rw [← hRS]; exact (readViolation_rvB _).1 _ hRV, by rw [← hsv, hs2]; rfl, hFOC⟩
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
    exact ⟨hFOB, by rw [← hRS]; exact (readViolation_rvB _).1 _ hRV, by rw [← hsv, hs2]; rfl, hFOC⟩

set_option maxHeartbeats 8000000 in
/-- **D140's loop passing** (merged by exists13): of every field whose whole type is a parameter, that parameter is
written `Prop` or `Type`; of every field whose whole type is a call of a global, given what `firstOrderTerm` found
(`hcall`: the global with a written Π-type into a sort), the sort is `Prop` or `Type`. Read off the run of
`checkInd`'s D140 loop, kept by a peel as `runs_checkInd_peel` keeps its steps. -/
theorem runs_checkInd_heads_mem {d : IndDecl} {st st' : MState} {b : Nat} (h : Runs (checkInd d) st b () st')
    (hcall : ∀ cn fields, (cn, fields) ∈ d.ctors → ∀ fname f as hd, (fname, Term.call (.const f) as hd) ∈ fields →
      ∃ g, st.globals.find? (·.name == f) = some g ∧ ∃ cs hs ds l rd, g.ty = .tPi cs (.pi hs ds (.sort l)) rd) :
    (∀ cn fields, (cn, fields) ∈ d.ctors → ∀ fname v, (fname, Term.place (.var v)) ∈ fields → (hv : v < d.params.length) →
      ∃ l, l ≤ 1 ∧ (d.params[d.params.length - 1 - v]'(by omega)).2 = .sort l) ∧
    (∀ cn fields, (cn, fields) ∈ d.ctors → ∀ fname f as hd, (fname, Term.call (.const f) as hd) ∈ fields →
      ∃ cs hs ds l rd, l ≤ 1 ∧ (st.globals.find? (·.name == f)).map (·.ty) = some (.tPi cs (.pi hs ds (.sort l)) rd)) := by
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
  -- main's D141: a parameter whose reading is "any" is rejected (the loop passing)
  obtain ⟨_, s₈a, b₈a, hg₈a, h141, h⟩ := Runs.grows_bind' (fun G => by grows_goI) h
  obtain ⟨_, s₈b, b₈b, hg₈b, hHD, h⟩ := Runs.grows_bind' (fun G => by grows_goI) h
  obtain ⟨-, hallC⟩ := runs_forIn_all (fun a b => growsM_of_growsIn fun G => by grows_goI)
    (fun a b s bh y s' hr => by
      obtain ⟨_, _, _, _, hr⟩ := Runs.bind_inv hr
      exact ⟨_, (runs_pure_inv hr).1⟩) hHD
  have hG8 : s₈a.globals = s₁.globals := by
    rw [hg₈a.globals, hg₈.globals, hg₇b.globals, hg₇.globals, hg₇a.globals, hg₆.globals, hg₅.globals, hg₄.globals,
      hg₃.globals]
    exact hg₂.globals
  refine ⟨fun cn fields hc fname v hf hv => ?_, fun cn fields hc fname f as hd hf => ?_⟩
  all_goals
    obtain ⟨_, s₁', bh₁, y, s₂', hT₁, hB⟩ := hallC (cn, fields) hc
    obtain ⟨_, s₃', b₃', hI, -⟩ := Runs.bind_inv hB
    obtain ⟨-, hallF⟩ := runs_forIn_all (fun a b => growsM_of_growsIn fun G => by grows_goI)
      (fun a b s bh y s' hr => by
        dsimp only at hr
        repeat' (first | rw [runs_get_bind] at hr | split at hr)
        all_goals first
          | exact ⟨_, (runs_pure_inv hr).1⟩
          | (obtain ⟨_, _, _, he, _⟩ := Runs.bind_inv hr; exact (runs_err_false he).elim)) hI
    obtain ⟨_, s₄', bh₄, y4, s₅', hT₄, hF⟩ := hallF _ hf
    have hG4 : s₄'.globals = s₁.globals := by rw [hT₄.globals, hT₁.globals, hG8]
    dsimp only at hF
  · rw [dif_pos hv] at hF
    rcases runs_ite_inv hF with ⟨hc', -⟩ | ⟨-, hF⟩
    · split at hc'
      · rename_i heq; exact ⟨0, by omega, heq⟩
      · rename_i heq; exact ⟨1, by omega, heq⟩
      · cases hc'
    · exact (runs_err_bind_false hF).elim
  · obtain ⟨g, hfind, cs, hs, ds, l, rd, hty⟩ := hcall cn fields hc fname f as hd hf
    rw [runs_get_bind, hG4, hfind] at hF
    dsimp only at hF
    rw [hty] at hF
    dsimp only at hF
    refine ⟨cs, hs, ds, l, rd, ?_, by rw [hfind]; simp [hty]⟩
    rcases runs_ite_inv hF with ⟨hc', -⟩ | ⟨-, hF⟩
    · split at hc'
      · rename_i heq; cases heq; omega
      · rename_i heq; cases heq; omega
      · cases hc'
    · exact (runs_err_bind_false hF).elim

/-- **The heads of an accepted declaration's field types are small, from what is written** (exists13; the
checker's D140 with `firstOrderTerm`'s call clause): a parameter that is a field's whole type is declared at a
written `Prop` or `Type`; a global whose call is a field's whole type has, at the state the declaration is
checked from, a stored type that is a written Π-type into `Prop` or `Type`. `Assembly.FieldHeads` is this at
the program's items. -/
theorem runs_checkInd_heads {d : IndDecl} {st st' : MState} {b : Nat} (h : Runs (checkInd d) st b () st') :
    (∀ c i v, fieldTerm d c i = some (.place (.var v)) → v < d.params.length →
      ∃ l, l ≤ 1 ∧ DataModel.Exists.Knot.paramTerm d (d.params.length - 1 - v) = .sort l) ∧
    (∀ c i f as hd, fieldTerm d c i = some (.call (.const f) as hd) →
      ∃ cs hs ds l rd, l ≤ 1 ∧ (st.globals.find? (·.name == f)).map (·.ty) = some (.tPi cs (.pi hs ds (.sort l)) rd)) := by
  have hF := runs_checkInd_fields h
  have hcall : ∀ cn fields, (cn, fields) ∈ d.ctors → ∀ fname f as hd, (fname, Term.call (.const f) as hd) ∈ fields →
      ∃ g, st.globals.find? (·.name == f) = some g ∧ ∃ cs hs ds l rd, g.ty = .tPi cs (.pi hs ds (.sort l)) rd := by
    intro cn fields hc fname f as hd hf
    obtain ⟨c, hc'⟩ := List.mem_iff_getElem?.1 hc
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hf
    exact (hF c cn fields hc' j fname _ hj).2.2.2 f as hd rfl
  obtain ⟨hP, hC⟩ := runs_checkInd_heads_mem h hcall
  have hft : ∀ c i FT, fieldTerm d c i = some FT → ∃ cn fields fname, (cn, fields) ∈ d.ctors ∧ (fname, FT) ∈ fields := by
    intro c i FT hFT
    unfold fieldTerm at hFT
    obtain ⟨⟨fname, FT'⟩, h1, h2⟩ := Option.map_eq_some_iff.1 hFT
    obtain ⟨⟨cn, fields⟩, h3, h4⟩ := Option.bind_eq_some_iff.1 h1
    simp only at h2
    subst h2
    exact ⟨cn, fields, fname, List.mem_of_getElem? h3, List.mem_of_getElem? h4⟩
  refine ⟨fun c i v hFT hv => ?_, fun c i f as hd hFT => ?_⟩
  · obtain ⟨cn, fields, fname, hc, hf⟩ := hft c i _ hFT
    obtain ⟨l, hl, he⟩ := hP cn fields hc fname v hf hv
    refine ⟨l, hl, ?_⟩
    unfold DataModel.Exists.Knot.paramTerm
    rw [List.getElem?_eq_getElem (by omega)]
    exact he
  · obtain ⟨cn, fields, fname, hc, hf⟩ := hft c i _ hFT
    exact hC cn fields hc fname f as hd hf

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
  · exact (hF c cn fields h3 i fname FT' h4).2.2.1

theorem checkIndGivesChecks : DataModel.Exists.Knot.CheckIndGivesChecks := by
  intro d st st' fuel hrun
  have hr := runs_of_runMachine_fst hrun
  exact ⟨_, (runs_checkInd_tables hr).2, runs_checkInd_checks hr⟩

end Ochr.Meaning.Steps.Machine

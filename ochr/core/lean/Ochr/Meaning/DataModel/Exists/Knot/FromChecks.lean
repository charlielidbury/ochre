import Ochr.Meaning.DataModel.Exists.Knot.Checks
import Ochr.Meaning.DataModel.Exists.Knot.Guard
import Ochr.Meaning.DataModel.Exists.Knot.NestLoop

/-!
# Acceptance gives the grammar (exists8, step 2)

`grammarOk_of_checks` / `pgrammarOk_of_checks`: a declaration that passes the checker's checks
(`IndChecks`, `Checks.lean`) satisfies the grammar the knot assumes (`GrammarOk`, `PGrammarOk`). The
induction follows the field type's spine, where the checks and the grammar walk the same nodes:
* an off-spine node (a call, an equation, a value argument) is steady: it does not mention `d`
  (`firstOrderTerm`), holds no embedded value (`FieldsNoVal`), and if it read a varying variable it
  would read, through declared types, a nestable parameter (which `nestableSet` then removes: the
  node is not a nestable position, `Term.nestOk`) or a field whose type mentions `d` (a
  `readViolation`), by `FromChecker.deepVars_bad`;
* a type argument that is not steady mentions `d` or reads a varying parameter (the spine's only
  variables are parameters), and in both cases it stands at a nestable parameter (`firstOrderTerm`'s
  nesting test, or `Term.nestOk` at the nestable parameter it reads) of a declaration of `d`'s sort,
  and is itself headed by one (`sortNestViolation`, or `Term.passOther`).
-/

namespace Ochr.Meaning.DataModel.Exists.Knot

open Ochr

/-! ## Free variables and `deepVars` of subterms -/

theorem mem_placeOccsList_inv {c : Nat} {x : Nat × Place × PKind} :
    ∀ {as : List Term}, x ∈ Term.placeOccsList c as → ∃ a ∈ as, x ∈ a.placeOccs c
  | [], h => by simp [Term.placeOccsList] at h
  | b :: bs, h => by
    rw [Term.placeOccsList, List.mem_append] at h
    rcases h with h | h
    · exact ⟨b, List.mem_cons_self .., h⟩
    · obtain ⟨a, ha, h'⟩ := mem_placeOccsList_inv h
      exact ⟨a, List.mem_cons_of_mem _ ha, h'⟩

theorem mem_freeVars_tind_iff {m : String} {as : List Term} {v : Nat} :
    v ∈ (Term.tind m as).freeVars ↔ ∃ a ∈ as, v ∈ a.freeVars := by
  constructor
  · intro hv
    obtain ⟨c, p, k, hm, hc, rfl⟩ := (FrameLocal.mem_freeVars _ v).mp hv
    simp only [Term.placeOccs] at hm
    obtain ⟨a, ha, h⟩ := mem_placeOccsList_inv hm
    exact ⟨a, ha, (FrameLocal.mem_freeVars _ _).mpr ⟨c, p, k, h, hc, rfl⟩⟩
  · rintro ⟨a, ha, hv⟩
    exact mem_freeVars_tind ha hv

/-- Every element of `deepIter` is reached from the start within as many steps as rounds. -/
theorem reach_of_deepIter (d : IndDecl) (c : Nat) : ∀ (m : Nat) (acc : List Nat) (w : Nat),
    w ∈ deepIter d c m acc → ∃ v ∈ acc, ReachIn d c m v w
  | 0, acc, w, h => ⟨w, h, .refl _ _⟩
  | m + 1, acc, w, h => by
    simp only [deepIter] at h
    split at h
    · exact ⟨w, h, .refl _ _⟩
    · obtain ⟨v', hv', hr⟩ := reach_of_deepIter d c m _ w h
      rcases List.mem_append.1 (List.mem_eraseDups.1 hv') with h1 | h1
      · exact ⟨v', h1, hr.mono (by omega)⟩
      · obtain ⟨u, hu, hx⟩ := List.mem_flatMap.1 h1
        exact ⟨u, hu, .step _ _ _ _ hx hr⟩

/-- **`deepVars` is the closure**: every variable it holds is reached from one of the term's own. -/
theorem reach_of_deepVars {d : IndDecl} {c : Nat} {t : Term} {w : Nat} (h : w ∈ d.deepVars c t) :
    ∃ v ∈ t.freeVars, ReachIn d c (d.params.length + (((d.ctors[c]?).map (·.2)).getD []).length) v w := by
  rw [deepVars_eq_iter] at h
  exact reach_of_deepIter d c _ _ w h

/-- `deepVars` is monotone in the term's free variables. -/
theorem deepVars_mono {d : IndDecl} {c : Nat} {t t' : Term} (h : ∀ v ∈ t.freeVars, v ∈ t'.freeVars) {w : Nat}
    (hw : w ∈ d.deepVars c t) : w ∈ d.deepVars c t' := by
  obtain ⟨v, hv, hr⟩ := reach_of_deepVars hw
  exact mem_deepVars (h v hv) hr

theorem deepVars_tind_arg {d : IndDecl} {c : Nat} {m : String} {as : List Term} {a : Term} (ha : a ∈ as) {w : Nat}
    (hw : w ∈ d.deepVars c a) : w ∈ d.deepVars c (.tind m as) :=
  deepVars_mono (fun _ hv => mem_freeVars_tind ha hv) hw

/-- A variable the term `.tind m as` reads is read by one of its arguments. -/
theorem deepVars_tind_inv {d : IndDecl} {c : Nat} {m : String} {as : List Term} {w : Nat}
    (hw : w ∈ d.deepVars c (.tind m as)) : ∃ a ∈ as, w ∈ d.deepVars c a := by
  obtain ⟨v, hv, hr⟩ := reach_of_deepVars hw
  obtain ⟨a, ha, hva⟩ := mem_freeVars_tind_iff.1 hv
  exact ⟨a, ha, mem_deepVars hva hr⟩

/-! ## The declarations the checks look up, and the ones the grammar looks up -/

/-- A name the checks find while checking `d`'s fields is found in the program (the declarations
before `d`, then `d` as stored, then any later ones), at a declaration with the same parameters,
whose nestable set is the checks' table and whose sort is the sort table's. -/
theorem env_find {Γ0 rest : List IndDecl} {d dm : IndDecl} {m : String} (hfresh : Γ0.find? (·.name == d.name) = none)
    (h : (declEnv Γ0 d).find? (·.name == m) = some dm) :
    ∃ M, (Γ0 ++ d :: rest).find? (·.name == m) = some M ∧ M.params = dm.params ∧
      (∀ j, nestOf M j = ownNest Γ0 d m j) ∧ sortTableOf Γ0 d m = some M.sort ∧
      (M = d ∨ M ∈ Γ0) ∧ (m = d.name → M = d) := by
  unfold declEnv at h
  rw [List.find?_append] at h
  cases h0 : Γ0.find? (·.name == m) with
  | some M =>
    rw [h0] at h
    simp only [Option.some_or, Option.some.injEq] at h
    subst h
    have hm : M.name = m := by simpa using List.find?_some h0
    have hne : (m == d.name) = false := by
      rw [beq_eq_false_iff_ne]
      rintro rfl
      rw [hfresh] at h0; cases h0
    refine ⟨M, by rw [List.find?_append, h0]; rfl, rfl, fun j => ?_, ?_, .inr (List.mem_of_find?_eq_some h0), ?_⟩
    · simp [ownNest, hne, nestTableOf, h0, nestOf]
    · simp [sortTableOf, hne, h0]
    · intro e; rw [e] at hne; simp at hne
  | none =>
    rw [h0] at h
    simp only [Option.none_or, List.find?_cons, List.find?_nil] at h
    split at h
    · rename_i hn
      simp only [Option.some.injEq] at h
      subst h
      have hdm : d.name = m := by simpa using hn
      refine ⟨d, ?_, rfl, fun j => ?_, ?_, .inl rfl, fun _ => rfl⟩
      · rw [List.find?_append, h0, Option.none_or, List.find?_cons]
        simp [hdm]
      · simp [ownNest, hdm, nestOf]
      · simp [sortTableOf, hdm]
    · cases h

/-! ## An off-spine node is steady -/

/-- A nestable parameter of `d`, as a variable of a field's scope. -/
def NestVar (d : IndDecl) (w : Nat) : Prop :=
  w < d.params.length ∧ d.nestable.getD (d.params.length - 1 - w) false = true

/-- **An off-spine node is steady** when it does not mention `d`, holds no embedded value, reads
(through declared types) no variable whose declared type mentions `d`, and reads no nestable
parameter. -/
theorem steadyB_of_reads {d : IndDecl} {c : Nat} (ht : TeleOk d) {t : Term} (hm : t.mentionsType d.name = false)
    (hv : t.anyAtom (fun _ => true) = false) (hr : readsOf d c t = none)
    (hn : ∀ w, NestVar d w → w ∉ d.deepVars c t) : steadyB d c t = true := by
  simp only [steadyB, hm, hv, Bool.not_false, Bool.true_and, List.all_eq_true, Bool.not_eq_true']
  intro v hvt
  cases hvv : varVaries d c v with
  | false => rfl
  | true =>
    exfalso
    obtain ⟨w, hw, hb⟩ := deepVars_bad ht hvt hvv
    rcases hb with ⟨h1, h2⟩ | ⟨_, T, hT, hTm⟩
    · exact hn w ⟨h1, h2⟩ hw
    · unfold readsOf at hr
      have := List.find?_eq_none.1 hr w hw
      simp [hT, hTm] at this

/-- A varying parameter reaches, through the parameters' declared types, a nestable one
(`FromChecker.reach_param`, whose chain stays among the parameters). -/
theorem reach_param_nest {d : IndDecl} {c : Nat} : ∀ (j : Nat), j < d.params.length → paramVaries d j = true →
    ∃ w, ReachIn d c (j + 1) (d.params.length - 1 - j) w ∧ NestVar d w := by
  intro j
  induction j using Nat.strongRecOn with
  | ind j ih =>
    intro hj hv
    rw [paramVaries] at hv
    simp only [Bool.or_eq_true, List.any_eq_true] at hv
    rcases hv with hn | ⟨u', hu', hv'⟩
    · exact ⟨_, .refl _ _, by omega, by rw [show d.params.length - 1 - (d.params.length - 1 - j) = j by omega]; exact hn⟩
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

/-- **A varying parameter's variable reads a nestable one** (`deepVars`). -/
theorem deepVars_nest {d : IndDecl} {c : Nat} {t : Term} {v : Nat} (hv : v ∈ t.freeVars) (hvn : v < d.params.length)
    (hvv : varVaries d c v = true) : ∃ w, NestVar d w ∧ w ∈ d.deepVars c t := by
  unfold varVaries at hvv
  rw [if_pos hvn] at hvv
  obtain ⟨w, hr, hw⟩ := reach_param_nest (c := c) (d.params.length - 1 - v) (by omega) hvv
  rw [show d.params.length - 1 - (d.params.length - 1 - v) = v by omega] at hr
  exact ⟨w, hw, mem_deepVars hv (hr.mono (by omega))⟩

/-- An argument that reads `w` where `passOtherArgs` is false stands in a declaration of sort `s`. -/
theorem passOtherArgs_sort {st : SortTable} {s : Nat} {vars : Term → List Nat} {w : Nat} {m : String} :
    ∀ {as : List Term}, Term.passOtherArgs st s vars w m as = false → ∀ b ∈ as, w ∈ vars b → st m = some s
  | [], _, b, hb, _ => by cases hb
  | a :: as, h, b, hb, hw => by
    rw [Term.passOtherArgs] at h
    simp only [Bool.or_eq_false_iff] at h
    rcases List.mem_cons.1 hb with rfl | hb
    · have := h.1.1
      simp only [Bool.and_eq_false_iff, bne_eq_false_iff_eq] at this
      rcases this with e | e
      · exact e
      · simp [hw] at e
    · exact passOtherArgs_sort h.2 b hb hw

/-- The sort table's sort is the program's declaration's. -/
theorem st_find {Γ0 rest : List IndDecl} {d M : IndDecl} {m : String} {s : Nat} (hfresh : Γ0.find? (·.name == d.name) = none)
    (h : sortTableOf Γ0 d m = some s) (hM : (Γ0 ++ d :: rest).find? (·.name == m) = some M) : M.sort = s := by
  unfold sortTableOf at h
  split at h
  · rename_i e
    have e' : m = d.name := by simpa using e
    subst e'
    rw [List.find?_append, hfresh, Option.none_or, List.find?_cons] at hM
    simp at hM
    subst hM
    simpa using h
  · obtain ⟨M', h1, h2⟩ := Option.map_eq_some_iff.1 h
    rw [List.find?_append, h1, Option.some_or] at hM
    cases hM
    exact h2

/-! ## The induction along the spine -/

/-- What the induction needs besides the checks at the field: the name is fresh, the fields are a
telescope, and no declaration's value parameter is nestable (`d`'s by `nestableSet`, the earlier
ones' by theirs). -/
structure FieldHyp (Γ0 : List IndDecl) (d : IndDecl) : Prop where
  fresh : Γ0.find? (·.name == d.name) = none
  tele : TeleOk d
  p1 : ∀ j, d.nestable.getD j false = true → d.paramIsType j = true
  val0 : ∀ M ∈ Γ0, ∀ j, nestOf M j = true → M.paramIsType j = true

/-- What the induction concludes of a term on the spine: the grammar of `d`'s sort, and its varying
variables are parameters. -/
def SpineRes (Γ : List IndDecl) (d : IndDecl) (c : Nat) (t : Term) : Prop :=
  (d.sort ≠ 0 → spineB Γ d c t = true) ∧ (d.sort = 0 → pspineB Γ d c t = true) ∧
    ∀ v ∈ t.freeVars, varVaries d c v = true → v < d.params.length

/-- The same, of the arguments of `M(…)` from parameter `j`. -/
def SpineArgsRes (Γ : List IndDecl) (d : IndDecl) (c : Nat) (M : IndDecl) (j : Nat) (pre as : List Term) : Prop :=
  (d.sort ≠ 0 → spineArgsB Γ d c M j pre as = true) ∧ (d.sort = 0 → pspineArgsB Γ d c M j pre as = true) ∧
    ∀ a ∈ as, ∀ v ∈ a.freeVars, varVaries d c v = true → v < d.params.length

theorem freeVars_var (v : Nat) : (Term.place (.var v)).freeVars = [v] := by
  simp [Term.freeVars, Term.freeOccs, Term.placeOccs, Place.root]

theorem steady_noVary {d : IndDecl} {c : Nat} {t : Term} (h : steadyB d c t = true) :
    ∀ v ∈ t.freeVars, varVaries d c v = true → v < d.params.length := by
  intro v hv hvv
  have := (steadyB_sound h).2 v hv
  rw [this] at hvv; cases hvv

theorem nestOkArgs_head {nest : NestTable} {vars : Term → List Nat} {w : Nat} {m : String} {j : Nat} {a : Term}
    {as : List Term} (h : (∀ a' ∈ a :: as, w ∉ vars a') ∨ Term.nestOkArgs nest vars w m j (a :: as) = true)
    (hw : w ∈ vars a) : nest m j = true ∧ a.nestOk nest vars w = true := by
  rcases h with h | h
  · exact absurd hw (h a (List.mem_cons_self ..))
  · rw [Term.nestOkArgs] at h
    simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h
    rcases h.1 with h1 | h1
    · simp [hw] at h1
    · exact h1

theorem nestOkArgs_tail {nest : NestTable} {vars : Term → List Nat} {w : Nat} {m : String} {j : Nat} {a : Term}
    {as : List Term} (h : (∀ a' ∈ a :: as, w ∉ vars a') ∨ Term.nestOkArgs nest vars w m j (a :: as) = true) :
    (∀ a' ∈ as, w ∉ vars a') ∨ Term.nestOkArgs nest vars w m (j + 1) as = true := by
  rcases h with h | h
  · exact .inl fun a' ha' => h a' (List.mem_cons_of_mem _ ha')
  · rw [Term.nestOkArgs] at h
    simp only [Bool.and_eq_true] at h
    exact .inr h.2

section
variable {Γ0 rest : List IndDecl} {d : IndDecl} {c : Nat}

mutual
/-- **The checks give the grammar along the spine.** -/
theorem spine_of_checks (H : FieldHyp Γ0 d) : ∀ (t : Term),
    foB (declEnv Γ0 d) (ownNest Γ0 d) d.name d.params.length t = true →
    rvB (declEnv Γ0 d) (readsOf d c) t = false →
    sortNestViolation (sortTableOf Γ0 d) d.name d.sort t = none →
    t.anyAtom (fun _ => true) = false →
    (∀ w, NestVar d w → w ∈ d.deepVars c t → t.nestOk (ownNest Γ0 d) (d.deepVars c) w = true) →
    (∀ w, NestVar d w → t.passOther (sortTableOf Γ0 d) d.sort (d.deepVars c) w = false) →
    SpineRes (Γ0 ++ d :: rest) d c t
  | .nat, _, _, _, _, _, _ => ⟨fun _ => by simp [spineB], fun _ => by simp [pspineB],
      by simp [Term.freeVars, Term.freeOccs, Term.placeOccs]⟩
  | .unit, _, _, _, _, _, _ => ⟨fun _ => by simp [spineB], fun _ => by simp [pspineB],
      by simp [Term.freeVars, Term.freeOccs, Term.placeOccs]⟩
  | .place p, hfo, _, _, _, _, _ => by
    cases p with
    | var v =>
      simp only [foB, decide_eq_true_eq] at hfo
      refine ⟨fun _ => by simp [spineB, hfo], fun _ => by simp [pspineB, hfo], ?_⟩
      intro v' hv' _
      rw [freeVars_var, List.mem_singleton] at hv'
      subst hv'; exact hfo
    | _ => simp [foB] at hfo
  | .tind m as, hfo, hrv, hsv, hav, hno, hpo => by
    simp only [foB] at hfo
    split at hfo
    · rename_i dm hdm
      obtain ⟨M, hM, hpar, hnest, hst, hM0, -⟩ := env_find (rest := rest) H.fresh hdm
      simp only [rvB, hdm] at hrv
      simp only [sortNestViolation] at hsv
      have hsv2 : Term.mentionsTypeList d.name as = true → sortTableOf Γ0 d m = some d.sort := by
        intro hm
        refine Classical.byContradiction fun hne => ?_
        rw [if_pos (by simp [hm, hne])] at hsv
        cases hsv
      have hsv1 : sortNestViolationArgs (sortTableOf Γ0 d) d.name d.sort as = none := by
        split at hsv
        · cases hsv
        · exact hsv
      have hR := spineArgs_of_checks H hdm hM hpar hnest hst hM0 0 [] as hfo hrv hsv1 hsv2
        (by simpa [Term.anyAtom] using hav)
        (fun w hw => by
          by_cases hw' : w ∈ d.deepVars c (.tind m as)
          · exact .inr (by simpa [Term.nestOk] using hno w hw hw')
          · exact .inl fun a ha hwa => hw' (deepVars_tind_arg ha hwa))
        (fun w hw => by simpa [Term.passOther] using hpo w hw)
      refine ⟨fun hs => by simp only [spineB, hM]; exact hR.1 hs, fun hs => by simp only [pspineB, hM]; exact hR.2.1 hs,
        fun v hv hvv => ?_⟩
      obtain ⟨a, ha, hva⟩ := mem_freeVars_tind_iff.1 hv
      exact hR.2.2 a ha v hva hvv
    · cases hfo
  | .call f as hd, hfo, hrv, _, hav, hno, _ => by
    cases f with
    | const g =>
      simp only [foB, Bool.not_eq_true'] at hfo
      have hst : steadyB d c (.call (.const g) as hd) = true := by
        refine steadyB_of_reads H.tele (by simp [Term.mentionsType, hfo]) hav (by simpa [rvB] using hrv) ?_
        intro w hw hwt
        have := hno w hw hwt
        simp [Term.nestOk, hwt] at this
      exact ⟨fun _ => by simp [spineB, hst], fun _ => by simp [pspineB, hst], steady_noVary hst⟩
    | _ => simp [foB] at hfo
  | .eq A a b, hfo, hrv, _, hav, hno, _ => by
    simp only [foB, Bool.and_eq_true, Bool.not_eq_true'] at hfo
    have hst : steadyB d c (.eq A a b) = true := by
      refine steadyB_of_reads H.tele (by simp [Term.mentionsType, hfo]) hav (by simpa [rvB] using hrv) ?_
      intro w hw hwt
      have := hno w hw hwt
      simp [Term.nestOk, hwt] at this
    exact ⟨fun _ => by simp [spineB, hst], fun _ => by simp [pspineB, hst], steady_noVary hst⟩
  | .borrow _, hfo, _, _, _, _, _ | .assign _ _, hfo, _, _, _, _, _ | .letIn _ _ _, hfo, _, _, _, _, _
  | .seq _ _, hfo, _, _, _, _, _ | .matchNat _ _ _, hfo, _, _, _, _, _ | .const _, hfo, _, _, _, _, _
  | .val _, hfo, _, _, _, _, _ | .sort _, hfo, _, _, _, _, _ | .pi _ _ _, hfo, _, _, _, _, _
  | .fix _ _ _ _ _ _, hfo, _, _, _, _, _ | .zero, hfo, _, _, _, _, _ | .succ _, hfo, _, _, _, _, _
  | .tt, hfo, _, _, _, _, _ | .cong _ _, hfo, _, _, _, _, _ | .ref _, hfo, _, _, _, _, _
  | .id _ _ _, hfo, _, _, _, _, _ | .ascribe _ _, hfo, _, _, _, _, _ | .prim _ _, hfo, _, _, _, _, _
  | .ctor _ _ _ _ _, hfo, _, _, _, _, _ | .matchInd _ _ _, hfo, _, _, _, _, _ => by simp [foB] at hfo

/-- The arguments of `m(…)` from parameter `j`, `m` found at `dm` by the checks and at `M` in the
program. -/
theorem spineArgs_of_checks (H : FieldHyp Γ0 d) {m : String} {dm M : IndDecl}
    (hdm : (declEnv Γ0 d).find? (·.name == m) = some dm) (hM : (Γ0 ++ d :: rest).find? (·.name == m) = some M)
    (hpar : M.params = dm.params) (hnest : ∀ j, nestOf M j = ownNest Γ0 d m j)
    (hst : sortTableOf Γ0 d m = some M.sort) (hM0 : M = d ∨ M ∈ Γ0) :
    ∀ (j : Nat) (pre as : List Term),
    foArgsB (declEnv Γ0 d) (ownNest Γ0 d) d.name d.params.length m dm j as = true →
    rvArgsB (declEnv Γ0 d) (readsOf d c) dm j as = false →
    sortNestViolationArgs (sortTableOf Γ0 d) d.name d.sort as = none →
    (Term.mentionsTypeList d.name as = true → sortTableOf Γ0 d m = some d.sort) →
    Term.anyAtomList (fun _ => true) as = false →
    (∀ w, NestVar d w → (∀ a ∈ as, w ∉ d.deepVars c a) ∨ Term.nestOkArgs (ownNest Γ0 d) (d.deepVars c) w m j as = true) →
    (∀ w, NestVar d w → Term.passOtherArgs (sortTableOf Γ0 d) d.sort (d.deepVars c) w m as = false) →
    SpineArgsRes (Γ0 ++ d :: rest) d c M j pre as
  | j, pre, [], _, _, _, _, _, _, _ => ⟨fun _ => by simp [spineArgsB], fun _ => by simp [pspineArgsB], by simp⟩
  | j, pre, a :: as, hfo, hrv, hsv, hsM, hav, hno, hpo => by
    simp only [foArgsB, Bool.and_eq_true] at hfo
    obtain ⟨hfa, hfr⟩ := hfo
    simp only [rvArgsB, Bool.or_eq_false_iff] at hrv
    obtain ⟨hra, hrr⟩ := hrv
    simp only [sortNestViolationArgs, Option.or_eq_none_iff] at hsv
    obtain ⟨hsa, hsr⟩ := hsv
    simp only [Term.anyAtomList, Bool.or_eq_false_iff] at hav
    obtain ⟨hava, havr⟩ := hav
    have hpoA : ∀ w, NestVar d w → (sortTableOf Γ0 d m != some d.sort && (d.deepVars c a).contains w) = false ∧
        a.passOther (sortTableOf Γ0 d) d.sort (d.deepVars c) w = false ∧
        Term.passOtherArgs (sortTableOf Γ0 d) d.sort (d.deepVars c) w m as = false := by
      intro w hw
      have := hpo w hw
      rw [Term.passOtherArgs] at this
      simp only [Bool.or_eq_false_iff] at this
      exact ⟨this.1.1, this.1.2, this.2⟩
    have hR := spineArgs_of_checks H hdm hM hpar hnest hst hM0 (j + 1) (pre ++ [a]) as hfr hrr hsr
      (fun h => hsM (by simp [Term.mentionsTypeList, h])) havr (fun w hw => nestOkArgs_tail (hno w hw))
      (fun w hw => (hpoA w hw).2.2)
    have hMty : M.paramIsType j = dm.paramIsType j := by unfold IndDecl.paramIsType; rw [hpar]
    by_cases hty : dm.paramIsType j = true
    · rw [if_pos hty] at hfa hra
      simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hfa
      obtain ⟨hfa1, hfa2⟩ := hfa
      have hA := spine_of_checks H a hfa1 hra hsa hava
        (fun w hw hwa => (nestOkArgs_head (hno w hw) hwa).2) (fun w hw => (hpoA w hw).2.1)
      -- a type argument that is not steady stands at a nestable parameter of a declaration of
      -- `d`'s sort, and is itself headed by one
      have key : steadyB d c a = false → ownNest Γ0 d m j = true ∧ M.sort = d.sort ∧
          ∀ m' as' M', a = .tind m' as' → (Γ0 ++ d :: rest).find? (·.name == m') = some M' → M'.sort = d.sort := by
        intro hns
        have hcase : a.mentionsType d.name = true ∨ ∃ v ∈ a.freeVars, varVaries d c v = true := by
          simp only [steadyB, hava, Bool.not_false, Bool.and_true, Bool.and_eq_false_iff, Bool.not_eq_false',
            List.all_eq_false] at hns
          rcases hns with h | ⟨v, hv, hvv⟩
          · exact .inl h
          · exact .inr ⟨v, hv, by simpa using hvv⟩
        rcases hcase with hmen | ⟨v, hv, hvv⟩
        · have h1 : ownNest Γ0 d m j = true := by simpa [hmen] using hfa2
          have h2 := st_find H.fresh (hsM (by simp [Term.mentionsTypeList, hmen])) hM
          refine ⟨h1, h2, fun m' as' M' he hM' => ?_⟩
          subst he
          by_cases hm' : m' = d.name
          · subst hm'
            rw [List.find?_append, H.fresh, Option.none_or, List.find?_cons] at hM'
            simp at hM'
            rw [← hM']
          · have hml : Term.mentionsTypeList d.name as' = true := by
              simpa [Term.mentionsType, hm'] using hmen
            simp only [sortNestViolation] at hsa
            have : sortTableOf Γ0 d m' = some d.sort := by
              refine Classical.byContradiction fun hne => ?_
              rw [if_pos (by simp [hml, hne])] at hsa
              cases hsa
            exact st_find H.fresh this hM'
        · obtain ⟨w, hw, hwa⟩ := deepVars_nest hv (hA.2.2 v hv hvv) hvv
          have h1 := (nestOkArgs_head (hno w hw) hwa).1
          have h2 : sortTableOf Γ0 d m = some d.sort := by
            have := (hpoA w hw).1
            simp only [Bool.and_eq_false_iff, bne_eq_false_iff_eq] at this
            rcases this with e | e
            · exact e
            · simp [hwa] at e
          refine ⟨h1, st_find H.fresh h2 hM, fun m' as' M' he hM' => ?_⟩
          subst he
          obtain ⟨b, hb, hwb⟩ := deepVars_tind_inv hwa
          have := (hpoA w hw).2.1
          rw [Term.passOther] at this
          exact st_find H.fresh (passOtherArgs_sort this b hb hwb) hM'
      refine ⟨fun hs => ?_, fun hs => ?_, ?_⟩
      · simp only [spineArgsB, hMty, hty, if_true, Bool.and_eq_true, Bool.or_eq_true]
        refine ⟨⟨hA.1 hs, ?_⟩, hR.1 hs⟩
        cases hsa' : steadyB d c a
        · obtain ⟨k1, -, k3⟩ := key hsa'
          refine .inr ⟨by rw [hnest]; exact k1, ?_⟩
          unfold notPropDecl
          split
          · rename_i m' as'
            split
            · rename_i M' hM'
              have := k3 m' as' M' rfl hM'
              simp [this, hs]
            · rfl
          · rfl
        · exact .inl rfl
      · simp only [pspineArgsB, hMty, hty, if_true, Bool.and_eq_true, Bool.or_eq_true]
        refine ⟨⟨hA.2.1 hs, ?_⟩, hR.2.1 hs⟩
        cases hsa' : steadyB d c a
        · obtain ⟨k1, k2, -⟩ := key hsa'
          exact .inr ⟨by rw [hnest]; exact k1, by simp [k2, hs]⟩
        · exact .inl rfl
      · intro a' ha' v hv hvv
        rcases List.mem_cons.1 ha' with rfl | ha'
        · exact hA.2.2 v hv hvv
        · exact hR.2.2 a' ha' v hv hvv
    · rw [if_neg hty] at hfa hra
      have hsteady : steadyB d c a = true := by
        refine steadyB_of_reads H.tele (by simpa using hfa) hava (by simpa using hra) (fun w hw hwa => ?_)
        have h1 := (nestOkArgs_head (hno w hw) hwa).1
        rw [← hnest] at h1
        have : M.paramIsType j = true := by
          rcases hM0 with rfl | hM0
          · exact H.p1 j h1
          · exact H.val0 M hM0 j h1
        rw [hMty] at this
        exact hty this
      have hty' : M.paramIsType j = false := by rw [hMty]; simpa using hty
      refine ⟨fun hs => ?_, fun hs => ?_, ?_⟩
      · simp only [spineArgsB, hty', Bool.false_eq_true, if_false, Bool.and_eq_true]
        exact ⟨hsteady, hR.1 hs⟩
      · simp only [pspineArgsB, hty', Bool.false_eq_true, if_false, Bool.and_eq_true]
        exact ⟨hsteady, hR.2.1 hs⟩
      · intro a' ha' v hv hvv
        rcases List.mem_cons.1 ha' with rfl | ha'
        · exact steady_noVary hsteady v hv hvv
        · exact hR.2.2 a' ha' v hv hvv
end

end

/-! ## Acceptance gives the grammar -/

/-- **A declaration that passes the checker's checks is in the grammar**, of its sort, in any program
that declares it after the declarations `Γ0` it was checked against. Assumes, besides the checks
(`IndChecks`, what `checkInd` establishes: the bridge `CheckIndGivesChecks` is the machine lane's),
that its field types hold no embedded value (`FieldsNoVal`, a fact about resolution) and that no
earlier declaration's value parameter is nestable (`hval`, this theorem's third conclusion at each
earlier declaration: the assembly's induction carries it). -/
theorem grammar_of_checks {Γ0 : List IndDecl} {d : IndDecl} (h : IndChecks Γ0 d) (hnv : FieldsNoVal d)
    (hval : ∀ M ∈ Γ0, ∀ j, nestOf M j = true → M.paramIsType j = true) (rest : List IndDecl) :
    (d.sort ≠ 0 → GrammarOk (Γ0 ++ d :: rest) d) ∧ (d.sort = 0 → PGrammarOk (Γ0 ++ d :: rest) d) ∧
      (∀ j, nestOf d j = true → d.paramIsType j = true) := by
  obtain ⟨P1, P2, P3⟩ := nestableSet_spec (nestTableOf Γ0) (sortTableOf Γ0 d) d
  rw [← h.nest] at P1 P2 P3
  have H : FieldHyp Γ0 d := ⟨h.fresh, h.tele, P1, hval⟩
  have hres : ∀ c i FT, fieldTerm d c i = some FT → SpineRes (Γ0 ++ d :: rest) d c FT := by
    intro c i FT hFT
    refine spine_of_checks H FT (h.fo c i FT hFT) (h.rv c i FT hFT) (h.sv c i FT hFT) (hnv c i FT hFT) ?_ ?_
    · intro w hw _
      have := P3 (d.params.length - 1 - w) hw.2 c i FT hFT
      rwa [show d.params.length - 1 - (d.params.length - 1 - w) = w by have := hw.1; omega] at this
    · intro w hw
      have := P2 (d.params.length - 1 - w) hw.2 c i FT hFT
      rwa [show d.params.length - 1 - (d.params.length - 1 - w) = w by have := hw.1; omega] at this
  exact ⟨fun hs c i FT hFT => (hres c i FT hFT).1 hs, fun hs c i FT hFT => (hres c i FT hFT).2.1 hs, P1⟩

end Ochr.Meaning.DataModel.Exists.Knot

import Ochr.Meaning.DataModel.Exists.Knot.Interp
import Ochr.Meaning.DataModel.Exists.FrameLocal.Run

/-!
# The knot, part 4: the interpreter is guarded (exists5)

`ftyK` is a `KnotSpec`'s field types (`knotK`): at records agreeing below `n` and parameters agreeing
below `n` (`ParAgree`, at `d`'s nestable parameters), the field types agree below `n`. By induction
on the field index (the canonical frames are EQUAL: everything in them that could differ varies and
is a dummy, `canFrame_eq`) and on the spine (`semT_steady`: a steady argument's value is the same;
`semT_agree`: a varying one's agrees below `n`, through `hpar` for an earlier declaration and through
the hypothesis on the records for `d`'s own occurrences).
-/

namespace Ochr.Meaning.DataModel.Exists.Knot

open Ochr Ochr.Meaning Ochr.Meaning.DataLib Ochr.Meaning.Canonical
open Classical

/-! ## Small facts about the grammar -/

theorem find_name {Γ : List IndDecl} {n : String} {M : IndDecl} (h : Γ.find? (·.name == n) = some M) :
    M.name = n ∧ M ∈ Γ := by
  refine ⟨?_, List.mem_of_find?_eq_some h⟩
  have := List.find?_some h
  simpa using this

theorem paramVaries_false {d : IndDecl} {j : Nat} (h : paramVaries d j = false) :
    d.nestable.getD j false = false ∧ ∀ u ∈ (paramTerm d j).freeVars, u < j → paramVaries d (j - 1 - u) = false := by
  rw [paramVaries] at h
  simp only [Bool.or_eq_false_iff, List.any_eq_false] at h
  refine ⟨h.1, fun u hu hlt => ?_⟩
  have := h.2 u hu
  simpa [hlt] using this

theorem mem_freeVars_tind {n : String} {as : List Term} {a : Term} (ha : a ∈ as) {v : Nat} (hv : v ∈ a.freeVars) :
    v ∈ (Term.tind n as).freeVars := by
  have := FrameLocal.freeVars_sub (t := .tind n as) (u := a) (n := 0)
    (fun x hx => by simpa [Term.placeOccs] using FrameLocal.mem_placeOccsList ha hx) v hv
  simpa using this

theorem mentionsTypeList_false {n : String} {as : List Term} (h : Term.mentionsTypeList n as = false) :
    ∀ a ∈ as, a.mentionsType n = false := by
  induction as with
  | nil => intro a ha; cases ha
  | cons b bs ih =>
    intro a ha
    rw [Term.mentionsTypeList] at h
    simp only [Bool.or_eq_false_iff] at h
    rcases List.mem_cons.1 ha with rfl | ha
    · exact h.1
    · exact ih h.2 a ha

/-! ## Unfolding the interpreter -/

section
variable (K : RunCtx) (ρ : Assignment) (d : IndDecl)

theorem semT_tind (R : List Sem → Rec) (ps : List Sem) (s : SState) (h : TyS) (n : String) (as : List Term) :
    semT K ρ d R ps s h (.tind n as) = match K.Γ.find? (·.name == n) with
      | some M => .ty (uTyR M (recFor K d R M (itpArgs K ρ d R ps s M 0 [] as)))
      | none => .ty TyM.err := by
  simp only [semT]
  cases K.Γ.find? (·.name == n) <;> rfl

theorem semT_var (R : List Sem → Rec) (ps : List Sem) (s : SState) (h : TyS) (v : Nat) (hv : v < d.params.length) :
    semT K ρ d R ps s h (.place (.var v)) = ps.getD (d.params.length - 1 - v) .err := by
  rw [semT, if_pos hv]

theorem semT_other (R : List Sem → Rec) (ps : List Sem) (s : SState) (h : TyS) (t : Term)
    (h1 : ∀ n as, t ≠ .tind n as) (h2 : ∀ v, t ≠ .place (.var v)) :
    semT K ρ d R ps s h t = valOf K ρ s h t := by
  rw [semT]
  · exact fun n as e => h1 n as e
  · exact fun v e => h2 v e

theorem itpArgs_nil (R : List Sem → Rec) (ps : List Sem) (s : SState) (M : IndDecl) (j : Nat) (pre : List Sem) :
    itpArgs K ρ d R ps s M j pre [] = [] := by
  rw [itpArgs]

theorem itpArgs_cons (R : List Sem → Rec) (ps : List Sem) (s : SState) (M : IndDecl) (j : Nat) (pre : List Sem)
    (a : Term) (as : List Term) :
    itpArgs K ρ d R ps s M j pre (a :: as) =
      argSem K ρ d R ps s M j pre a :: itpArgs K ρ d R ps s M (j + 1) (pre ++ [argSem K ρ d R ps s M j pre a]) as := by
  rw [itpArgs]

theorem argSem_eq (R : List Sem → Rec) (ps : List Sem) (s : SState) (M : IndDecl) (j : Nat) (pre : List Sem) (a : Term) :
    argSem K ρ d R ps s M j pre a = if M.paramIsType j then semT K ρ d R ps s (.plain TyM.err) a
      else valOf K ρ s (.plain TyM.err) a := by
  rw [argSem]

end

/-! ## A quiet term reads neither the record nor a varying parameter -/

section
variable (K : RunCtx) (ρ : Assignment) (d : IndDecl) (c : Nat)

/-- Parameter lists equal at the parameters that do not vary. -/
def PsSteady (ps ps' : List Sem) : Prop := ∀ j, paramVaries d j = false → ps.getD j .err = ps'.getD j .err

/-- A term that does not name `d` and reads no varying variable. -/
def Quiet (t : Term) : Prop := t.mentionsType d.name = false ∧ ∀ v ∈ t.freeVars, varVaries d c v = false

variable {K ρ d c}

theorem quiet_args {n : String} {as : List Term} (h : Quiet d c (.tind n as)) :
    n ≠ d.name ∧ ∀ a ∈ as, Quiet d c a := by
  have h1 := h.1
  rw [Term.mentionsType] at h1
  simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at h1
  exact ⟨h1.1, fun a ha => ⟨mentionsTypeList_false h1.2 a ha, fun v hv => h.2 v (mem_freeVars_tind ha hv)⟩⟩

theorem ne_of_find {Γ : List IndDecl} {n : String} {M : IndDecl} (hM : Γ.find? (·.name == n) = some M)
    (hn : n ≠ d.name) : M ≠ d := fun e => hn (by rw [← (find_name hM).1, e])

mutual
theorem semT_quiet {R R' : List Sem → Rec} {ps ps' : List Sem} {s : SState} (hps : PsSteady d ps ps') :
    ∀ {t : Term}, Spine K.Γ d c t → Quiet d c t → ∀ h, semT K ρ d R ps s h t = semT K ρ d R' ps' s h t
  | _, .nat, _, _ => by
    rw [semT_other K ρ d R ps s _ _ (fun _ _ e => by cases e) (fun _ e => by cases e),
      semT_other K ρ d R' ps' s _ _ (fun _ _ e => by cases e) (fun _ e => by cases e)]
  | _, .unit, _, _ => by
    rw [semT_other K ρ d R ps s _ _ (fun _ _ e => by cases e) (fun _ e => by cases e),
      semT_other K ρ d R' ps' s _ _ (fun _ _ e => by cases e) (fun _ e => by cases e)]
  | _, .param v hv, hq, h => by
    rw [semT_var K ρ d R ps s h v hv, semT_var K ρ d R' ps' s h v hv]
    have := hq.2 v (FrameLocal.root_mem_place (.var v))
    unfold varVaries at this
    rw [if_pos hv] at this
    exact hps _ this
  | _, .tind n as M hM hargs, hq, h => by
    rw [semT_tind, semT_tind, hM]
    obtain ⟨hn, hqa⟩ := quiet_args hq
    simp only [recFor, if_neg (ne_of_find hM hn)]
    rw [itpArgs_quiet hps hargs hqa []]
  | _, .call _ _ _ _, _, _ => by
    rw [semT_other K ρ d R ps s _ _ (fun _ _ e => by cases e) (fun _ e => by cases e),
      semT_other K ρ d R' ps' s _ _ (fun _ _ e => by cases e) (fun _ e => by cases e)]
  | _, .eq _ _ _ _, _, _ => by
    rw [semT_other K ρ d R ps s _ _ (fun _ _ e => by cases e) (fun _ e => by cases e),
      semT_other K ρ d R' ps' s _ _ (fun _ _ e => by cases e) (fun _ e => by cases e)]

theorem itpArgs_quiet {R R' : List Sem → Rec} {ps ps' : List Sem} {s : SState} (hps : PsSteady d ps ps') :
    ∀ {M : IndDecl} {j : Nat} {pre as : List Term}, SpineArgs K.Γ d c M j pre as → (∀ a ∈ as, Quiet d c a) →
      ∀ vpre, itpArgs K ρ d R ps s M j vpre as = itpArgs K ρ d R' ps' s M j vpre as
  | _, _, _, _, .nil _ _ _, _, vpre => by rw [itpArgs_nil, itpArgs_nil]
  | _, _, _, _, .type M j pre a as hty ha _ _ hrest, hq, vpre => by
    have e : argSem K ρ d R ps s M j vpre a = argSem K ρ d R' ps' s M j vpre a := by
      rw [argSem_eq, argSem_eq, if_pos hty, if_pos hty]
      exact semT_quiet hps ha (hq a (List.mem_cons_self ..)) _
    rw [itpArgs_cons, itpArgs_cons, e,
      itpArgs_quiet hps hrest (fun b hb => hq b (List.mem_cons_of_mem _ hb)) _]
  | _, _, _, _, .value M j pre a as hty _ _ hrest, hq, vpre => by
    have e : argSem K ρ d R ps s M j vpre a = argSem K ρ d R' ps' s M j vpre a := by
      rw [argSem_eq, argSem_eq, if_neg (by simp [hty]), if_neg (by simp [hty])]
    rw [itpArgs_cons, itpArgs_cons, e,
      itpArgs_quiet hps hrest (fun b hb => hq b (List.mem_cons_of_mem _ hb)) _]
end

end

/-! ## Varying arguments agree below the depth -/

theorem freeVars_sort (l : Nat) : (Term.sort l).freeVars = [] := by
  simp [Term.freeVars, Term.freeOccs, Term.placeOccs]

theorem freeVars_unit : (Term.unit).freeVars = [] := by
  simp [Term.freeVars, Term.freeOccs, Term.placeOccs]

theorem paramTerm_type {M : IndDecl} {j : Nat} (h : M.paramIsType j = true) : (paramTerm M j).freeVars = [] := by
  unfold IndDecl.paramIsType at h
  unfold paramTerm
  split at h
  · rename_i hp _ hm; rw [hm]; simp [freeVars_sort]
  · cases h
  · rename_i hm; rw [hm]; simp [freeVars_unit]

/-- `ParAgree` at a parameter that does not vary is equality. -/
theorem psSteady_of_parAgree {d : IndDecl} {n : Nat} {ps ps' : List Sem}
    (hp : ParAgree (fun j => d.nestable.getD j false) n ps ps') : PsSteady d ps ps' := by
  intro j hj
  have hN := (paramVaries_false hj).1
  rcases h1 : ps[j]? with _ | v
  · have h2 : ps'[j]? = none := by rw [List.getElem?_eq_none_iff] at h1 ⊢; rw [← hp.1]; exact h1
    simp [List.getD_eq_getElem?_getD, h1, h2]
  · rcases h2 : ps'[j]? with _ | v'
    · have : ps[j]? = none := by rw [List.getElem?_eq_none_iff] at h2 ⊢; rw [hp.1]; exact h2
      rw [this] at h1; cases h1
    · have := hp.2 j v v' h1 h2
      simp only [hN, Bool.false_eq_true, if_false] at this
      simp [List.getD_eq_getElem?_getD, h1, h2, this]

theorem steady_quiet {d : IndDecl} {c : Nat} {t : Term} (h : Steady d c t) : Quiet d c t := ⟨h.1.1, h.2⟩

/-- What a varying type argument is: a parameter, or a data-sorted declaration applied. -/
def DataLike (Γ : List IndDecl) (t : Term) : Prop :=
  (∃ v, t = .place (.var v)) ∨ ∀ n' as' M', t = .tind n' as' → Γ.find? (·.name == n') = some M' → M'.sort ≠ 0

/-- The relation the arguments of `M(…)` satisfy so far, at records and parameters agreeing below `n`:
at `M`'s nestable parameters below `n`, elsewhere equal, and equal wherever the argument is steady. -/
def ArgRel (d : IndDecl) (c : Nat) (M : IndDecl) (n : Nat) (pre : List Term) (vs vs' : List Sem) : Prop :=
  vs.length = vs'.length ∧ vs.length = pre.length ∧ ∀ k v v', vs[k]? = some v → vs'[k]? = some v' →
    (if nestOf M k then SemAgree n v v' else v = v') ∧ (∀ a, pre[k]? = some a → Steady d c a → v = v')

theorem ArgRel.nil (d : IndDecl) (c : Nat) (M : IndDecl) (n : Nat) : ArgRel d c M n [] [] [] :=
  ⟨rfl, rfl, fun k v v' h => by simp at h⟩

theorem ArgRel.snoc {d : IndDecl} {c : Nat} {M : IndDecl} {n : Nat} {pre : List Term} {vs vs' : List Sem}
    (h : ArgRel d c M n pre vs vs') (a : Term) (v v' : Sem)
    (h1 : if nestOf M pre.length then SemAgree n v v' else v = v') (h2 : Steady d c a → v = v') :
    ArgRel d c M n (pre ++ [a]) (vs ++ [v]) (vs' ++ [v']) := by
  refine ⟨by simp [h.1], by simp [h.2.1], fun k w w' hw hw' => ?_⟩
  by_cases hk : k < vs.length
  · rw [List.getElem?_append_left hk] at hw
    rw [List.getElem?_append_left (by rw [← h.1]; exact hk)] at hw'
    obtain ⟨e1, e2⟩ := h.2.2 k w w' hw hw'
    exact ⟨e1, fun b hb => e2 b (by rwa [List.getElem?_append_left (by rw [← h.2.1]; exact hk)] at hb)⟩
  · have hk' : k = vs.length := by
      have := (List.getElem?_eq_some_iff.1 hw).1; simp at this; omega
    subst hk'
    rw [List.getElem?_append_right (Nat.le_refl _)] at hw
    rw [h.1, List.getElem?_append_right (Nat.le_refl _)] at hw'
    simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at hw hw'
    subst hw hw'
    refine ⟨by rw [h.2.1]; exact h1, fun b hb hs => ?_⟩
    rw [h.2.1, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, List.getElem?_cons_zero,
      Option.some.injEq] at hb
    subst hb; exact h2 hs

theorem ArgRel.parAgree {d : IndDecl} {c : Nat} {M : IndDecl} {n : Nat} {pre : List Term} {vs vs' : List Sem}
    (h : ArgRel d c M n pre vs vs') : ParAgree (fun j => M.nestable.getD j false) n vs vs' :=
  ⟨h.1, fun k v v' hv hv' => (h.2.2 k v v' hv hv').1⟩

section
variable {K : RunCtx} {ρ : Assignment} {d : IndDecl} {c : Nat}
variable {n : Nat} {R R' : List Sem → Rec} {ps ps' : List Sem} {s : SState}

/-- The hints of the next argument agree when the earlier arguments its parameter type mentions are
steady (and so equal). -/
theorem hint_eq (hpty : ParamTyLocal K.dm K.Γ) {M : IndDecl} (hM : M ∈ K.Γ) {j : Nat} {pre : List Term}
    {vs vs' : List Sem} (h : ArgRel d c M n pre vs vs') (hj : vs.length = j)
    (hh : ∀ u ∈ (paramTerm M j).freeVars, u < j → ∀ a, pre[j - 1 - u]? = some a → Steady d c a) :
    K.dm.paramTy M j vs = K.dm.paramTy M j vs' := by
  apply hpty M hM j vs vs' hj (by rw [← h.1]; exact hj)
  intro u hu hlt
  rcases e1 : vs[j - 1 - u]? with _ | v
  · have : vs'[j - 1 - u]? = none := by
      rw [List.getElem?_eq_none_iff] at e1 ⊢; rw [← h.1]; exact e1
    rw [this]
  · have hk : j - 1 - u < vs'.length := by rw [← h.1, hj]; omega
    obtain ⟨a, ha⟩ : ∃ a, pre[j - 1 - u]? = some a := by
      have : j - 1 - u < pre.length := by rw [← h.2.1, hj]; omega
      exact ⟨_, List.getElem?_eq_getElem this⟩
    have := (h.2.2 _ v _ e1 (List.getElem?_eq_getElem hk)).2 a ha (hh u hu hlt a ha)
    rw [List.getElem?_eq_getElem hk, this]

end

/-- What guardedness rests on, at records `R`, `R'` and parameters `ps`, `ps'` agreeing below `n`. -/
structure GuardHyp (K : RunCtx) (d : IndDecl) (n : Nat) (R R' : List Sem → Rec) (ps ps' : List Sem) : Prop where
  hs : d.sort ≠ 0
  hR : RAgree (fun j => d.nestable.getD j false) n R R'
  hp : ParAgree (fun j => d.nestable.getD j false) n ps ps'
  hpar : ∀ M ∈ K.Γ, M ≠ d → ∀ n, RAgree (fun j => M.nestable.getD j false) n (K.dm.recOf M) (K.dm.recOf M)
  hpty : ParamTyLocal K.dm K.Γ

section
variable {K : RunCtx} {ρ : Assignment} {d : IndDecl} {c : Nat}
variable {n : Nat} {R R' : List Sem → Rec} {ps ps' : List Sem} {s : SState}

theorem recFor_agree (G : GuardHyp K d n R R' ps ps') {M : IndDecl} (hMΓ : M ∈ K.Γ) {vs vs' : List Sem}
    (h : ParAgree (fun j => M.nestable.getD j false) n vs vs') :
    RecAgree n (recFor K d R M vs) (recFor K d R' M vs') := by
  unfold recFor
  by_cases hMd : M = d
  · subst hMd; rw [if_pos rfl, if_pos rfl]; exact G.hR vs vs' h
  · rw [if_neg hMd, if_neg hMd]; exact G.hpar M hMΓ hMd n vs vs' h

theorem sem_eq_other (h' : TyS) (t : Term) (h1 : ∀ n as, t ≠ .tind n as) (h2 : ∀ v, t ≠ .place (.var v)) :
    semT K ρ d R ps s h' t = semT K ρ d R' ps' s h' t := by
  rw [semT_other K ρ d R ps s h' t h1 h2, semT_other K ρ d R' ps' s h' t h1 h2]

mutual
theorem semT_agree (G : GuardHyp K d n R R' ps ps') :
    ∀ {t : Term}, Spine K.Γ d c t → (¬ Steady d c t → DataLike K.Γ t) → ∀ h,
      SemAgree n (semT K ρ d R ps s h t) (semT K ρ d R' ps' s h t)
  | _, .nat, _, h => .inl (sem_eq_other h _ (fun _ _ e => by cases e) (fun _ e => by cases e))
  | _, .unit, _, h => .inl (sem_eq_other h _ (fun _ _ e => by cases e) (fun _ e => by cases e))
  | _, .call _ _ _ _, _, h => .inl (sem_eq_other h _ (fun _ _ e => by cases e) (fun _ e => by cases e))
  | _, .eq _ _ _ _, _, h => .inl (sem_eq_other h _ (fun _ _ e => by cases e) (fun _ e => by cases e))
  | _, .param v hv, _, h => by
    rw [semT_var K ρ d R ps s h v hv, semT_var K ρ d R' ps' s h v hv]
    rcases e1 : ps[d.params.length - 1 - v]? with _ | w
    · have e2 : ps'[d.params.length - 1 - v]? = none := by
        rw [List.getElem?_eq_none_iff] at e1 ⊢; rw [← G.hp.1]; exact e1
      exact .inl (by simp [List.getD_eq_getElem?_getD, e1, e2])
    · rcases e2 : ps'[d.params.length - 1 - v]? with _ | w'
      · have : ps[d.params.length - 1 - v]? = none := by
          rw [List.getElem?_eq_none_iff] at e2 ⊢; rw [G.hp.1]; exact e2
        rw [this] at e1; cases e1
      · have := G.hp.2 _ w w' e1 e2
        simp only [List.getD_eq_getElem?_getD, e1, e2, Option.getD_some]
        split at this
        · exact this
        · exact .inl this
  | _, .tind n' as M hM hargs, hdl, h => by
    by_cases hst : Steady d c (.tind n' as)
    · exact .inl (semT_quiet (ρ := ρ) (s := s) (psSteady_of_parAgree G.hp) (.tind n' as M hM hargs) (steady_quiet hst) h)
    · have hMs : M.sort ≠ 0 := by
        rcases hdl hst with ⟨v, e⟩ | hD
        · cases e
        · exact hD _ _ _ rfl hM
      have hMΓ := (find_name hM).2
      rw [semT_tind, semT_tind, hM]
      have hA := itpArgs_agree G hMΓ hargs [] [] (ArgRel.nil d c M n) rfl
      simp only [List.nil_append] at hA
      exact .inr ⟨M, _, _, hMs, rfl, rfl, recFor_agree G hMΓ hA.parAgree⟩

theorem itpArgs_agree (G : GuardHyp K d n R R' ps ps') {M : IndDecl} (hMΓ : M ∈ K.Γ) :
    ∀ {j : Nat} {pre as : List Term}, SpineArgs K.Γ d c M j pre as →
      ∀ (vs vs' : List Sem), ArgRel d c M n pre vs vs' → vs.length = j →
      ArgRel d c M n (pre ++ as) (vs ++ itpArgs K ρ d R ps s M j vs as) (vs' ++ itpArgs K ρ d R' ps' s M j vs' as)
  | _, _, _, .nil _ _ _, vs, vs', h, _ => by simpa [itpArgs_nil] using h
  | _, _, _, .type _ j pre a as hty ha hn hA hrest, vs, vs', h, hj => by
    -- the argument runs with no hint (docs/31 D172), so the two sides' hints agree trivially
    rw [itpArgs_cons, itpArgs_cons, argSem_eq, argSem_eq, if_pos hty, if_pos hty]
    have hpl : pre.length = j := by rw [← h.2.1, hj]
    have hv : (if nestOf M pre.length then
        SemAgree n (semT K ρ d R ps s (.plain TyM.err) a) (semT K ρ d R' ps' s (.plain TyM.err) a)
        else semT K ρ d R ps s (.plain TyM.err) a = semT K ρ d R' ps' s (.plain TyM.err) a) ∧
        (Steady d c a → semT K ρ d R ps s (.plain TyM.err) a = semT K ρ d R' ps' s (.plain TyM.err) a) := by
      by_cases hst : Steady d c a
      · have e := semT_quiet (ρ := ρ) (s := s) (R := R) (R' := R') (psSteady_of_parAgree G.hp) ha (steady_quiet hst) (.plain TyM.err)
        refine ⟨?_, fun _ => e⟩
        split
        · exact .inl e
        · exact e
      · have e := semT_agree G ha (fun _ => .inr (hA hst).2) (.plain TyM.err)
        rw [hpl, if_pos (hn hst)]
        exact ⟨e, fun h => absurd h hst⟩
    have h' := h.snoc a _ _ hv.1 hv.2
    have := itpArgs_agree G hMΓ hrest _ _ h' (by simp [hj])
    simpa [List.append_assoc] using this
  | _, _, _, .value _ j pre a as hty ha hh hrest, vs, vs', h, hj => by
    rw [itpArgs_cons, itpArgs_cons, argSem_eq, argSem_eq, if_neg (by simp [hty]), if_neg (by simp [hty])]
    have h' := h.snoc a (valOf K ρ s (.plain TyM.err) a) (valOf K ρ s (.plain TyM.err) a)
      (by split <;> first | exact .inl rfl | rfl) (fun _ => rfl)
    have := itpArgs_agree G hMΓ hrest _ _ h' (by simp [hj])
    simpa [List.append_assoc] using this
end

end

/-! ## The field type, the canonical frame, and the knot -/

section
variable (K : RunCtx) (ρ : Assignment) (d : IndDecl)

theorem itpT_tind (R : List Sem → Rec) (ps : List Sem) (s : SState) (h : TyS) (n : String) (as : List Term) :
    itpT K ρ d R ps s h (.tind n as) = match K.Γ.find? (·.name == n) with
      | some M => .data M (recFor K d R M (itpArgs K ρ d R ps s M 0 [] as))
      | none => .ty TyM.err := by
  simp only [itpT]
  cases K.Γ.find? (·.name == n) <;> rfl

theorem itpT_other (R : List Sem → Rec) (ps : List Sem) (s : SState) (h : TyS) (t : Term)
    (h1 : ∀ n as, t ≠ .tind n as) : itpT K ρ d R ps s h t = .ty (semT K ρ d R ps s h t).asTy := by
  rw [itpT]
  exact fun n as e => h1 n as e

theorem ftyK_eq (R : List Sem → Rec) (ps : List Sem) (c i : Nat) (es : List Small) :
    ftyK K ρ d R ps c i es = match fieldTerm d c i with
      | some FT => itpT K ρ d R ps
          (canFrame K d ps c i es fun j => if _h : j < i then shapeTyP (shapeOf (ftyK K ρ d R ps c j (es.take j))) else TyM.err)
          (.plain (TyM.univ 1)) FT
      | none => .ty TyM.err := by
  rw [ftyK]
  cases fieldTerm d c i <;> rfl

end

section
variable {K : RunCtx} {ρ : Assignment} {d : IndDecl} {c : Nat}

/-- **The canonical frames are equal** at parameters equal where they do not vary and at earlier
canonical types equal where the fields are a non-varying index. -/
theorem canFrame_eq (hpty : ParamTyLocal K.dm K.Γ) (hdΓ : d ∈ K.Γ) {ps ps' : List Sem} (hl : ps.length = ps'.length)
    (hps : PsSteady d ps ps') {i : Nat} {es : List Small} {tyOf tyOf' : Nat → TyM}
    (hty : ∀ j < i, fieldVaries d c j = false → (d.indexFields c).contains j = true → tyOf j = tyOf' j) :
    canFrame K d ps c i es tyOf = canFrame K d ps' c i es tyOf' := by
  unfold canFrame
  congr 2
  · apply List.map_congr_left
    intro j _
    by_cases hj : j < i
    · rw [if_pos hj, if_pos hj]
      by_cases hc : fieldVaries d c j = false ∧ (d.indexFields c).contains j = true
      · rw [if_pos hc, if_pos hc, hty j hj hc.1 hc.2]
      · rw [if_neg hc, if_neg hc]
    · rw [if_neg hj, if_neg hj]
  · apply List.map_congr_left
    intro j _
    by_cases hv : paramVaries d j
    · rw [if_pos hv, if_pos hv]
    · rw [if_neg hv, if_neg hv]
      have hv' : paramVaries d j = false := by simpa using hv
      have e1 : ps.getD j .err = ps'.getD j .err := hps j hv'
      by_cases hjl : j < ps.length
      · rw [if_pos hjl, if_pos (by rw [← hl]; exact hjl), e1]
        have hP : K.dm.paramTy d j (ps.take j) = K.dm.paramTy d j (ps'.take j) := by
          apply hpty d hdΓ j _ _ (by simp; omega) (by simp; omega)
          intro u hu hlt
          have hu' := (paramVaries_false hv').2 u hu hlt
          have := hps _ hu'
          have hk : j - 1 - u < ps.length := by omega
          have hk' : j - 1 - u < ps'.length := by omega
          rw [List.getElem?_take, List.getElem?_take, if_pos (by omega), if_pos (by omega),
            List.getElem?_eq_getElem hk, List.getElem?_eq_getElem hk']
          simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, List.getElem?_eq_getElem hk',
            Option.getD_some] at this
          rw [this]
        rw [hP]
      · rw [if_neg hjl, if_neg (by rw [← hl]; exact hjl), e1]

end

/-! ## Guardedness, assembled -/

section
variable {K : RunCtx} {ρ : Assignment} {d : IndDecl} {c : Nat}

theorem quiet_of_fieldVaries {i : Nat} {FT : Term} (hv : fieldVaries d c i = false) (hFT : fieldTerm d c i = some FT) :
    Quiet d c FT := by
  rw [fieldVaries, hFT] at hv
  simp only [Bool.or_eq_false_iff, List.any_eq_false] at hv
  refine ⟨hv.1, fun v hvm => ?_⟩
  have h := hv.2 v hvm
  unfold varVaries
  by_cases h1 : v < d.params.length
  · rw [if_pos h1] at h ⊢; simpa using h
  · rw [if_neg h1] at h ⊢
    by_cases h2 : v < d.params.length + arity d c
    · rw [if_pos h2] at h ⊢
      split at h
      · simpa using h
      · simp at h
    · rw [if_neg h2]

theorem itpT_quiet {R R' : List Sem → Rec} {ps ps' : List Sem} {s : SState} (hps : PsSteady d ps ps') {t : Term}
    (ht : Spine K.Γ d c t) (hq : Quiet d c t) (h : TyS) :
    itpT K ρ d R ps s h t = itpT K ρ d R' ps' s h t := by
  cases ht with
  | tind n as M hM hargs =>
    rw [itpT_tind, itpT_tind, hM]
    obtain ⟨hn, hqa⟩ := quiet_args hq
    simp only [recFor, if_neg (ne_of_find hM hn)]
    rw [itpArgs_quiet hps hargs hqa []]
  | _ =>
    rw [itpT_other _ _ _ _ _ _ _ _ (fun _ _ e => by cases e), itpT_other _ _ _ _ _ _ _ _ (fun _ _ e => by cases e),
      semT_quiet hps (by constructor <;> assumption) hq h]

/-- **A field that does not vary has the same field type at every record**, and at parameters equal
where they do not vary. -/
theorem ftyK_quiet (hspine : ∀ c i FT, fieldTerm d c i = some FT → Spine K.Γ d c FT)
    (hpty : ParamTyLocal K.dm K.Γ) (hdΓ : d ∈ K.Γ) {R R' : List Sem → Rec} {ps ps' : List Sem}
    (hl : ps.length = ps'.length) (hps : PsSteady d ps ps') :
    ∀ (i : Nat) (es : List Small), fieldVaries d c i = false →
      ftyK K ρ d R ps c i es = ftyK K ρ d R' ps' c i es := by
  intro i
  induction i using Nat.strongRecOn with
  | ind i ih =>
    intro es hv
    rw [ftyK_eq, ftyK_eq]
    cases hFT : fieldTerm d c i with
    | none => rfl
    | some FT =>
      dsimp only
      rw [canFrame_eq hpty hdΓ hl hps (tyOf' := fun j => if _h : j < i then
          shapeTyP (shapeOf (ftyK K ρ d R' ps' c j (es.take j))) else TyM.err)
        (fun j hj hvj _ => by simp only [dif_pos hj]; rw [ih j hj _ hvj])]
      exact itpT_quiet hps (hspine c i FT hFT) (quiet_of_fieldVaries hv hFT) _

theorem itpT_agree {n : Nat} {R R' : List Sem → Rec} {ps ps' : List Sem} {s : SState}
    (G : GuardHyp K d n R R' ps ps') {t : Term} (ht : Spine K.Γ d c t) (h : TyS) :
    FTyAgree n (itpT K ρ d R ps s h t) (itpT K ρ d R' ps' s h t) := by
  cases ht with
  | tind n' as M hM hargs =>
    rw [itpT_tind, itpT_tind, hM]
    have hMΓ := (find_name hM).2
    have hA := itpArgs_agree (ρ := ρ) (s := s) G hMΓ hargs [] [] (ArgRel.nil d c M n) rfl
    simp only [List.nil_append] at hA
    exact data_agree M (recFor_agree G hMΓ hA.parAgree)
  | _ =>
    rw [itpT_other _ _ _ _ _ _ _ _ (fun _ _ e => by cases e), itpT_other _ _ _ _ _ _ _ _ (fun _ _ e => by cases e)]
    exact semAgree_fty (semT_agree (c := c) G (by constructor <;> assumption)
      (fun _ => .inr fun _ _ _ e => by cases e) h)

/-- **The interpreter is guarded.** -/
theorem ftyK_agree (hspine : ∀ c i FT, fieldTerm d c i = some FT → Spine K.Γ d c FT) (hdΓ : d ∈ K.Γ)
    {n : Nat} {R R' : List Sem → Rec} {ps ps' : List Sem} (G : GuardHyp K d n R R' ps ps')
    (i : Nat) (es : List Small) :
    FTyAgree n (ftyK K ρ d R ps c i es) (ftyK K ρ d R' ps' c i es) := by
  rw [ftyK_eq, ftyK_eq]
  cases hFT : fieldTerm d c i with
  | none => exact FTyAgree.refl _ _
  | some FT =>
    dsimp only
    rw [canFrame_eq G.hpty hdΓ G.hp.1 (psSteady_of_parAgree G.hp) (tyOf' := fun j => if _h : j < i then
        shapeTyP (shapeOf (ftyK K ρ d R' ps' c j (es.take j))) else TyM.err)
      (fun j hj hvj _ => by
        simp only [dif_pos hj]
        rw [ftyK_quiet hspine G.hpty hdΓ G.hp.1 (psSteady_of_parAgree G.hp) j _ hvj])]
    exact itpT_agree G (hspine c i FT hFT) _

end

/-- **The knot of an accepted data-sorted declaration**: the interpreter's field types, guarded. -/
noncomputable def knotK (K : RunCtx) (ρ : Assignment) (d : IndDecl) (hs : d.sort ≠ 0) (hdΓ : d ∈ K.Γ)
    (hspine : ∀ c i FT, fieldTerm d c i = some FT → Spine K.Γ d c FT)
    (hpar : ∀ M ∈ K.Γ, M ≠ d → ∀ n, RAgree (fun j => M.nestable.getD j false) n (K.dm.recOf M) (K.dm.recOf M))
    (hpty : ParamTyLocal K.dm K.Γ) : KnotSpec where
  d := d
  N := fun j => d.nestable.getD j false
  fty := fun R ps c i es => ftyK K ρ d R ps c i es
  pEntry := pEntryTy
  guarded := fun _ _ _ hR _ _ hp c i es => ftyK_agree (c := c) hspine hdΓ ⟨hs, hR, hp, hpar, hpty⟩ i es
  pEntry_agree := fun _ _ _ hp j => pEntryTy_agree hp j

end Ochr.Meaning.DataModel.Exists.Knot

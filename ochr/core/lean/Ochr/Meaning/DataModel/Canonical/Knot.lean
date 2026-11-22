import Ochr.Meaning.DataModel.Canonical.Layout

/-!
# The canonical construction: the knot, guarded by path length (docs/34 §18)

A declaration's canonical record at parameters reads, at a field's key, the field's type (`fty`),
which may hold the declaration's OWN records (a recursive field `D(ā)`, a nested one `List(D(ā))`,
a self occurrence whose argument is the declaration, `DD(DD(A))`). The record is defined by its
approximations (`approx n`: right on paths shorter than `n`) and read at a path from the
approximation one longer than the path (`recK`). It is the fixed point (`recK_kind`, `recK_cont`)
when the field types are GUARDED: their kinds do not depend on the declaration's records, and their
continuations agree on paths shorter than `n` whenever the records and the nestable parameters do
(`KnotSpec.guarded`). That is the positivity condition of `Positivity.lean`, semantically: the
declaration's records reach its field types only at data positions. A record built so is itself
parametric in its nestable parameters (`recK_agree`), which is what a later declaration nesting in
it uses.
-/

namespace Ochr.Meaning.Canonical

open Ochr Ochr.Meaning Ochr.Meaning.DataLib

/-! ## Agreement below a depth -/

/-- Two records agree on paths shorter than `n`. -/
def RecAgree (n : Nat) (r r' : Rec) : Prop := ∀ q : List RStep, q.length < n → r q = r' q

/-- Two meanings agree below `n`: equal, or the code of one declaration at records agreeing below
`n`. -/
def SemAgree (n : Nat) (v v' : Sem) : Prop :=
  v = v' ∨ ∃ (d : IndDecl) (r r' : Rec), d.sort ≠ 0 ∧ v = .ty (uTyR d r) ∧ v' = .ty (uTyR d r') ∧ RecAgree n r r'

/-- Parameter lists agree below `n`: at the nestable parameters `N` as `SemAgree`, elsewhere equal. -/
def ParAgree (N : Nat → Bool) (n : Nat) (ps ps' : List Sem) : Prop :=
  ps.length = ps'.length ∧ ∀ j v v', ps[j]? = some v → ps'[j]? = some v' →
    if N j then SemAgree n v v' else v = v'

/-- Record functions agree below `n` at parameters agreeing below `n`. -/
def RAgree (N : Nat → Bool) (n : Nat) (R R' : List Sem → Rec) : Prop :=
  ∀ ps ps', ParAgree N n ps ps' → RecAgree n (R ps) (R' ps')

/-- Field types agree below `n`: the same kind, and continuations agreeing below `n`. -/
def FTyAgree (n : Nat) (F F' : FTy) : Prop := F.kind = F'.kind ∧ RecAgree n F.cont F'.cont

theorem RecAgree.mono {n m : Nat} {r r' : Rec} (h : RecAgree n r r') (hm : m ≤ n) : RecAgree m r r' :=
  fun q hq => h q (Nat.lt_of_lt_of_le hq hm)

theorem SemAgree.mono {n m : Nat} {v v' : Sem} (h : SemAgree n v v') (hm : m ≤ n) : SemAgree m v v' := by
  rcases h with h | ⟨d, r, r', hs, h1, h2, h3⟩
  · exact .inl h
  · exact .inr ⟨d, r, r', hs, h1, h2, h3.mono hm⟩

theorem SemAgree.symm {n : Nat} {v v' : Sem} (h : SemAgree n v v') : SemAgree n v' v := by
  rcases h with h | ⟨d, r, r', hs, h1, h2, h3⟩
  · exact .inl h.symm
  · exact .inr ⟨d, r', r, hs, h2, h1, fun q hq => (h3 q hq).symm⟩

theorem ParAgree.mono {N : Nat → Bool} {n m : Nat} {ps ps' : List Sem} (h : ParAgree N n ps ps') (hm : m ≤ n) :
    ParAgree N m ps ps' := by
  refine ⟨h.1, fun j v v' hv hv' => ?_⟩
  have := h.2 j v v' hv hv'
  split at this
  · rw [if_pos (by assumption)]; exact this.mono hm
  · rw [if_neg (by assumption)]; exact this

theorem ParAgree.symm {N : Nat → Bool} {n : Nat} {ps ps' : List Sem} (h : ParAgree N n ps ps') :
    ParAgree N n ps' ps := by
  refine ⟨h.1.symm, fun j v v' hv hv' => ?_⟩
  have := h.2 j v' v hv' hv
  split at this
  · rw [if_pos (by assumption)]; exact this.symm
  · rw [if_neg (by assumption)]; exact this.symm

theorem ParAgree.refl (N : Nat → Bool) (n : Nat) (ps : List Sem) : ParAgree N n ps ps := by
  refine ⟨rfl, fun j v v' hv hv' => ?_⟩
  rw [hv] at hv'
  cases hv'
  split
  · exact .inl rfl
  · rfl

/-! ## The keys, classified -/

inductive StepKind : Type 1
  | field (c i : Nat) (es : List Small)
  | cont (c i : Nat) (es : List Small)
  | param (j : Nat)
  | paramCont (j : Nat)
  | junk

/-- What a step is: a field's key (as many earlier fields as its index), the step to its
continuation (one more, the last `•`), a parameter's key or the step to its continuation. -/
def classify (s : RStep) : StepKind :=
  if s.2.2.length = s.2.1 then .field s.1 s.2.1 s.2.2
  else if s.2.2.length = s.2.1 + 1 then
    match s.2.2.getLast? with
    | some .proof => .cont s.1 s.2.1 s.2.2.dropLast
    | some .other => if s.2.1 = 0 then .param s.1 else .junk
    | _ => .junk
  else if s.2.1 = 0 then
    match s.2.2 with
    | [.other, .other] => .paramCont s.1
    | _ => .junk
  else .junk

theorem classify_field (c i : Nat) (es : List Small) (h : es.length = i) :
    classify (c, i, es) = .field c i es := by simp [classify, h]

theorem classify_cont (c i : Nat) (es : List Small) (h : es.length = i) :
    classify (contStep c i es) = .cont c i es := by
  simp [classify, contStep, h]

theorem classify_param (j : Nat) : classify (j, 0, [.other]) = .param j := by simp [classify]

theorem classify_paramCont (j : Nat) : classify (paramContStep j) = .paramCont j := by
  simp [classify, paramContStep]

/-! ## A declaration's record, by its approximations -/

/-- The record of the data type a parameter is. -/
noncomputable def paramRec (ps : List Sem) (j : Nat) : Rec :=
  match ps[j]? with
  | some (.ty T) => (FTy.ty T).cont
  | _ => dummyRec

/-- What the knot is given: a data-sorted declaration, its nestable parameters, its field types
as functions of its own record function, and its parameters' entries. -/
structure KnotSpec where
  d : IndDecl
  N : Nat → Bool
  fty : (List Sem → Rec) → List Sem → Nat → Nat → List Small → FTy
  pEntry : List Sem → Nat → Entry
  guarded : ∀ n R R', RAgree N n R R' → ∀ ps ps', ParAgree N n ps ps' →
    ∀ c i es, FTyAgree n (fty R ps c i es) (fty R' ps' c i es)
  pEntry_agree : ∀ n ps ps', ParAgree N n ps ps' → ∀ j, pEntry ps j = pEntry ps' j

variable (S : KnotSpec)

/-- One unfolding: each key read from the field types at the given record function. -/
noncomputable def stepRec (R : List Sem → Rec) (ps : List Sem) : List RStep → Entry
  | [] => .none
  | s :: q => match classify s with
    | .field c i es => match q with
      | [] => (S.fty R ps c i es).kind
      | _ => .none
    | .cont c i es => (S.fty R ps c i es).cont q
    | .param j => match q with
      | [] => S.pEntry ps j
      | _ => .none
    | .paramCont j => paramRec ps j q
    | .junk => .none

/-- The approximations: `approx n` is right on paths shorter than `n`. -/
noncomputable def approx : Nat → List Sem → Rec
  | 0 => fun _ _ => .none
  | n + 1 => stepRec S (approx n)

/-- **The canonical record**: at a path, the approximation one longer than it. -/
noncomputable def recK (ps : List Sem) : Rec := fun p => approx S (p.length + 1) ps p

/-! ## The approximations stabilize, and their limit is the fixed point -/

theorem paramRec_agree {N : Nat → Bool} {n : Nat} {ps ps' : List Sem} (hp : ParAgree N n ps ps') (j : Nat) :
    RecAgree n (paramRec ps j) (paramRec ps' j) := by
  intro q hq
  unfold paramRec
  rcases h1 : ps[j]? with _ | v
  · have : ps'[j]? = none := by
      rw [List.getElem?_eq_none_iff] at h1 ⊢; rw [← hp.1]; exact h1
    rw [this]
  · rcases h2 : ps'[j]? with _ | v'
    · have : ps[j]? = none := by
        rw [List.getElem?_eq_none_iff] at h2 ⊢; rw [hp.1]; exact h2
      rw [this] at h1; cases h1
    · have h := hp.2 j v v' h1 h2
      have hs : SemAgree n v v' := by
        split at h
        · exact h
        · exact .inl h
      rcases hs with rfl | ⟨d, r, r', hd, rfl, rfl, hr⟩
      · rfl
      · simp only [FTy.cont, dataView_uTyR d r hd, dataView_uTyR d r' hd]
        exact hr q hq

theorem approx_stab : ∀ n m, n ≤ m → RAgree S.N n (approx S n) (approx S m)
  | 0, _, _ => fun _ _ _ q hq => absurd hq (Nat.not_lt_zero _)
  | n + 1, m, hm => by
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have ih := approx_stab n m' (by omega)
    intro ps ps' hp q hq
    show stepRec S (approx S n) ps q = stepRec S (approx S m') ps' q
    have hp' := hp.mono (Nat.le_succ n)
    have hg := S.guarded n _ _ ih ps ps' hp'
    cases q with
    | nil => rfl
    | cons s q' =>
      have hq' : q'.length < n := by simpa using hq
      simp only [stepRec]
      cases classify s with
      | field c i es =>
        cases q' with
        | nil => exact (hg c i es).1
        | cons _ _ => rfl
      | cont c i es => exact (hg c i es).2 q' hq'
      | param j =>
        cases q' with
        | nil => exact S.pEntry_agree (n + 1) ps ps' hp j
        | cons _ _ => rfl
      | paramCont j => exact paramRec_agree hp j q' (Nat.lt_succ_of_lt hq')
      | junk => rfl

/-- The canonical record is parametric in the nestable parameters (what a declaration nesting in
this one uses). -/
theorem recK_agree (n : Nat) : RAgree S.N n (recK S) (recK S) := by
  intro ps ps' hp q hq
  exact approx_stab S (q.length + 1) (q.length + 1) (Nat.le_refl _) ps ps'
    (hp.mono (by omega)) q (Nat.lt_succ_self _)

theorem approx_recK (n : Nat) : RAgree S.N n (approx S n) (recK S) := by
  intro ps ps' hp q hq
  show approx S n ps q = approx S (q.length + 1) ps' q
  exact (approx_stab S (q.length + 1) n (by omega) ps' ps (hp.symm.mono (by omega)) q
    (Nat.lt_succ_self _)).symm

/-- **The knot, at a field's key**: the record holds the field type's kind, the field type read at
the record itself. -/
theorem recK_kind (ps : List Sem) (c i : Nat) (es : List Small) (h : es.length = i) :
    recK S ps (kindKey c i es) = (S.fty (recK S) ps c i es).kind := by
  show stepRec S (approx S 1) ps [(c, i, es)] = _
  simp only [stepRec, classify_field c i es h]
  exact (S.guarded 0 _ _ (fun _ _ _ q hq => absurd hq (Nat.not_lt_zero _)) ps ps
    (ParAgree.refl _ _ _) c i es).1

/-- **The knot, past a field's key**: the record continues as the field type's record. -/
theorem recK_cont (ps : List Sem) (c i : Nat) (es : List Small) (h : es.length = i) (q : List RStep) :
    recK S ps (contStep c i es :: q) = (S.fty (recK S) ps c i es).cont q := by
  show stepRec S (approx S (q.length + 1)) ps (contStep c i es :: q) = _
  simp only [stepRec, classify_cont c i es h]
  exact (S.guarded (q.length + 1) _ _ (approx_recK S _) ps ps (ParAgree.refl _ _ _) c i es).2 q
    (Nat.lt_succ_self _)

theorem recK_param (ps : List Sem) (j : Nat) : recK S ps (paramKey j) = S.pEntry ps j := by
  show stepRec S (approx S 1) ps [(j, 0, [.other])] = _
  simp only [stepRec, classify_param]

theorem recK_paramCont (ps : List Sem) (j : Nat) (q : List RStep) :
    recK S ps (paramContStep j :: q) = paramRec ps j q := by
  show stepRec S (approx S (q.length + 1)) ps (paramContStep j :: q) = _
  simp only [stepRec, classify_paramCont]

/-- The record continues as the field type's record (as a function). -/
theorem recK_contRec (ps : List Sem) (c i : Nat) (es : List Small) (h : es.length = i) :
    contRec (recK S ps) (contStep c i es) = (S.fty (recK S) ps c i es).cont :=
  funext fun q => recK_cont S ps c i es h q

/-- **Faithfulness at a field, for any knot**: the universal signature at the canonical record
means the field type read at that record (the earlier fields projected to the index fields). -/
theorem recK_shape (ps : List Sem) (c i : Nat) (es : List Small) (h : es.length = i)
    (hL : (S.fty (recK S) ps c i (projIdx S.d c es)).Lvl0) :
    shapeTyP (uShape S.d (recK S ps) c i es) = (S.fty (recK S) ps c i (projIdx S.d c es)).mean := by
  have hl : (projIdx S.d c es).length = i := by simp [projIdx, h]
  exact shapeTyP_uShape S.d (recK S ps) c i es _ hL (recK_kind S ps c i _ hl) (recK_contRec S ps c i _ hl)

/-! ## The pieces field types are made of, and their agreement -/

/-- Parameter `j` read as a type. -/
def parTy (ps : List Sem) (j : Nat) : TyM :=
  match ps[j]? with
  | some v => v.asTy
  | none => TyM.err

/-- Parameter `j`'s entry: its type's kind. -/
noncomputable def pEntryTy (ps : List Sem) (j : Nat) : Entry := (FTy.ty (parTy ps j)).kind

theorem FTyAgree.refl (n : Nat) (F : FTy) : FTyAgree n F F := ⟨rfl, fun _ _ => rfl⟩

theorem semAgree_fty {n : Nat} {v v' : Sem} (h : SemAgree n v v') : FTyAgree n (.ty v.asTy) (.ty v'.asTy) := by
  rcases h with rfl | ⟨d, r, r', hd, rfl, rfl, hr⟩
  · exact FTyAgree.refl _ _
  · refine ⟨?_, ?_⟩
    · simp [Sem.asTy, FTy.kind, dataView_uTyR d r hd, dataView_uTyR d r' hd]
    · intro q hq
      simp only [Sem.asTy, FTy.cont, dataView_uTyR d r hd, dataView_uTyR d r' hd]
      exact hr q hq

/-- A parameter read as a type, at agreeing parameters: agreeing field types. -/
theorem parTy_agree {N : Nat → Bool} {n : Nat} {ps ps' : List Sem} (hp : ParAgree N n ps ps') (j : Nat) :
    FTyAgree n (.ty (parTy ps j)) (.ty (parTy ps' j)) := by
  unfold parTy
  rcases h1 : ps[j]? with _ | v
  · have : ps'[j]? = none := by
      rw [List.getElem?_eq_none_iff] at h1 ⊢; rw [← hp.1]; exact h1
    rw [this]; exact FTyAgree.refl _ _
  · rcases h2 : ps'[j]? with _ | v'
    · have : ps[j]? = none := by
        rw [List.getElem?_eq_none_iff] at h2 ⊢; rw [hp.1]; exact h2
      rw [this] at h1; cases h1
    · have h := hp.2 j v v' h1 h2
      split at h
      · exact semAgree_fty h
      · subst h; exact FTyAgree.refl _ _

theorem pEntryTy_agree {N : Nat → Bool} {n : Nat} {ps ps' : List Sem} (hp : ParAgree N n ps ps') (j : Nat) :
    pEntryTy ps j = pEntryTy ps' j := (parTy_agree hp j).1

/-- **A parameter's entry, value parameters kept small** (exists9): a type parameter's kind
(`pEntryTy`), a value parameter's small reading, which `RecordsFaithful.values` asks a record to keep at
`paramKey` (`pEntryTy` there gives `.none`: a value is no type). -/
noncomputable def pEntryV (d : IndDecl) (ps : List Sem) (j : Nat) : Entry :=
  if d.paramIsType j then pEntryTy ps j else .small (ps.getD j .err).small

/-- Agreeing parameters have the same entries: at a value parameter they are equal, or, at a nestable
one, two type codes (both read small as `other`). -/
theorem pEntryV_agree {d : IndDecl} {N : Nat → Bool} {n : Nat} {ps ps' : List Sem} (hp : ParAgree N n ps ps')
    (j : Nat) : pEntryV d ps j = pEntryV d ps' j := by
  unfold pEntryV
  split
  · exact pEntryTy_agree hp j
  · congr 1
    rcases e : ps[j]? with _ | v
    · have e' : ps'[j]? = none := by
        rw [List.getElem?_eq_none_iff] at e ⊢; rw [← hp.1]; exact e
      simp [List.getD_eq_getElem?_getD, e, e']
    · obtain ⟨v', e'⟩ : ∃ v', ps'[j]? = some v' := by
        have : j < ps'.length := by rw [← hp.1]; exact (List.getElem?_eq_some_iff.1 e).1
        exact ⟨_, List.getElem?_eq_getElem this⟩
      have h := hp.2 j v v' e e'
      simp only [List.getD_eq_getElem?_getD, e, e', Option.getD_some]
      split at h
      · rcases h with rfl | ⟨_, _, _, _, rfl, rfl, _⟩
        · rfl
        · rfl
      · rw [h]

/-- A data type at records agreeing below `n`. -/
theorem data_agree {n : Nat} (d : IndDecl) {r r' : Rec} (h : RecAgree n r r') :
    FTyAgree n (.data d r) (.data d r') := ⟨rfl, h⟩

/-- A one-parameter list holding a data type's code at agreeing records agrees at a nestable
parameter `0`. -/
theorem parAgree_one {N : Nat → Bool} (hN : N 0 = true) {n : Nat} (d : IndDecl) (hd : d.sort ≠ 0) {r r' : Rec}
    (h : RecAgree n r r') : ParAgree N n [.ty (uTyR d r)] [.ty (uTyR d r')] := by
  refine ⟨rfl, fun j v v' hv hv' => ?_⟩
  cases j with
  | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hv hv'
    subst hv hv'
    rw [if_pos hN]
    exact .inr ⟨d, r, r', hd, rfl, rfl, h⟩
  | succ j => simp at hv

end Ochr.Meaning.Canonical

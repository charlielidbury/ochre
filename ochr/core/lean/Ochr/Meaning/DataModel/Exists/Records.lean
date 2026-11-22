import Ochr.Meaning.DataModel.Exists.Knot.TruthExists
import Ochr.Meaning.DataModel.Exists.Piece3

/-!
# Piece 6: records that read value parameters only small (exists9)

`RecordsFaithful.smallOnly` asks a declaration's record at a parameter list to be the record at any
list whose level-0 value parameters have the same small readings (the run's constructor clause solves a
value parameter to `ofSmall` of the small reading a record keeps, a junk tree with no name and no
record, and then reads the record there). The knot's records do not: its canonical frame binds a value
parameter that does not vary by its value, and a field type reading it strictly (`Eq(B, b, b)` for
`W (b : B)`, `B` a data type) fails at the junk tree (docs/34 §18.14). So the model's record is the
knot's at the CANONICAL parameters (`canonPs`): each value parameter that does not vary and has a
level-0 type is replaced by the member of its type with its small reading (`rebuildM`). On a list of
members this changes nothing (`canonPs_typed`, members of one level-0 type with one small reading are
equal, `Piece3.memTy_small_inj`); it maps a list and its small-reading variant to related lists
(`canonPs_small`); and it keeps the knot's parametricity (`canonPs_parAgree`) and the truth records'
monotonicity (`canonPs_propLe`), because it rebuilds only at parameters that do not vary, whose types
read only parameters that do not vary (`ParamTyLocalD`).
-/

namespace Ochr.Meaning.DataModel.Exists.Records

open Ochr Ochr.Meaning Ochr.Meaning.DataLib Ochr.Meaning.Canonical Ochr.Meaning.DataModel.Exists.Knot
open Classical

/-- Induction on a list from its end. -/
@[elab_as_elim]
theorem snoc_induction {motive : List Sem → Prop} (nil : motive [])
    (snoc : ∀ qs v, motive qs → motive (qs ++ [v])) (ps : List Sem) : motive ps := by
  rw [← List.reverse_reverse ps]
  generalize ps.reverse = rs
  induction rs with
  | nil => exact nil
  | cons v rs ih => rw [List.reverse_cons]; exact snoc _ _ ih

section
variable (dm : DataModel) (P : Nat → List Sem → TyM) (d : IndDecl)

/-- The member of `T` with the small reading `sm` (`err` when there is none). -/
noncomputable def rebuildM (T : TyM) (sm : Small) : Sem :=
  if h : ∃ v, v ∈ₛ[dm.read] T ∧ v.small = sm then h.choose else .err

/-- The canonical parameter after the canonical earlier ones `acc`. -/
noncomputable def canonStep (acc : List Sem) (v : Sem) : Sem :=
  if paramVaries d acc.length = false then
    match P acc.length acc with
    | .t0 A c => rebuildM dm (.t0 A c) v.small
    | _ => v
  else v

/-- **The canonical parameters.** -/
noncomputable def canonPs (ps : List Sem) : List Sem :=
  ps.foldl (fun acc v => acc ++ [canonStep dm P d acc v]) []

theorem canonPs_append (ps : List Sem) (v : Sem) :
    canonPs dm P d (ps ++ [v]) = canonPs dm P d ps ++ [canonStep dm P d (canonPs dm P d ps) v] := by
  simp [canonPs, List.foldl_append]

theorem canonPs_length (ps : List Sem) : (canonPs dm P d ps).length = ps.length := by
  induction ps using snoc_induction with
  | nil => rfl
  | snoc qs v ih => rw [canonPs_append]; simp [ih]

theorem canonPs_take (ps : List Sem) (j : Nat) : canonPs dm P d (ps.take j) = (canonPs dm P d ps).take j := by
  induction ps using snoc_induction generalizing j with
  | nil => simp [canonPs]
  | snoc qs v ih =>
    rw [canonPs_append]
    by_cases hj : j ≤ qs.length
    · rw [List.take_append_of_le_length hj, List.take_append_of_le_length (by rw [canonPs_length]; exact hj), ih]
    · have h1 : (qs ++ [v]).take j = qs ++ [v] := List.take_of_length_le (by simp; omega)
      have h2 : (canonPs dm P d qs ++ [canonStep dm P d (canonPs dm P d qs) v]).take j =
          canonPs dm P d qs ++ [canonStep dm P d (canonPs dm P d qs) v] :=
        List.take_of_length_le (by simp [canonPs_length]; omega)
      rw [h1, h2, canonPs_append]

/-- Position `j` of the canonical list: the step at the canonical prefix. -/
theorem canonPs_getElem (ps : List Sem) (j : Nat) (hj : j < ps.length) :
    (canonPs dm P d ps)[j]? = some (canonStep dm P d ((canonPs dm P d ps).take j) ps[j]) := by
  have e : ps.take (j + 1) = ps.take j ++ [ps[j]] := List.take_succ_eq_append_getElem hj
  have h := canonPs_take dm P d ps (j + 1)
  rw [e, canonPs_append, canonPs_take] at h
  have hl : ((canonPs dm P d ps).take (j + 1)).length = j + 1 := by
    simp [canonPs_length]; omega
  have := congrArg (·[j]?) h
  rw [List.getElem?_append_right (by simp [canonPs_length]; omega)] at this
  simp only [List.length_take, canonPs_length, Nat.min_eq_left (Nat.le_of_lt hj), Nat.sub_self,
    List.getElem?_cons_zero] at this
  rw [this, List.getElem?_take_of_lt (Nat.lt_succ_self j)]

/-- Members at the declared types (at the earlier parameters). -/
def Typed (ps : List Sem) : Prop := ∀ j (h : j < ps.length), ps[j] ∈ₛ[dm.read] P j (ps.take j)

/-- **On a list of members the canonical parameters are the parameters.** -/
theorem canonPs_typed (ps : List Sem) (h : Typed dm P ps) : canonPs dm P d ps = ps := by
  induction ps using snoc_induction with
  | nil => rfl
  | snoc qs v ih =>
    have hq : Typed dm P qs := fun j hj => by
      have := h j (by simp; omega)
      simp only [List.getElem_append_left hj] at this
      rwa [List.take_append_of_le_length (Nat.le_of_lt hj)] at this
    have hv : v ∈ₛ[dm.read] P qs.length qs := by
      have := h qs.length (by simp)
      simp only [List.getElem_append_right (Nat.le_refl _), Nat.sub_self, List.getElem_cons_zero] at this
      rwa [List.take_left' rfl] at this
    rw [canonPs_append, ih hq]
    congr 2
    unfold canonStep
    split
    · split
      · rename_i A c e
        rw [e] at hv
        have hex : ∃ w, w ∈ₛ[dm.read] TyM.t0 A c ∧ w.small = v.small := ⟨v, hv, rfl⟩
        unfold rebuildM
        rw [dif_pos hex]
        exact Piece3.memTy_small_inj dm c hex.choose_spec.1 hv hex.choose_spec.2
      · rfl
    · rfl

/-- The step at a parameter that does not vary, given its type. -/
noncomputable def stepAt (T : TyM) (v : Sem) : Sem :=
  match T with
  | .t0 A c => rebuildM dm (.t0 A c) v.small
  | _ => v

theorem canonStep_nonvary (acc : List Sem) (v : Sem) (h : paramVaries d acc.length = false) :
    canonStep dm P d acc v = stepAt dm (P acc.length acc) v := by
  unfold canonStep stepAt; rw [if_pos h]

theorem canonStep_vary (acc : List Sem) (v : Sem) (h : paramVaries d acc.length = true) :
    canonStep dm P d acc v = v := by
  unfold canonStep; rw [if_neg (by simp [h])]

/-- A varying parameter is kept. -/
theorem canonPs_vary (ps : List Sem) (j : Nat) (hj : j < ps.length) (hv : paramVaries d j = true) :
    (canonPs dm P d ps)[j]? = some ps[j] := by
  rw [canonPs_getElem dm P d ps j hj, canonStep_vary]
  simpa [canonPs_length, Nat.min_eq_left (Nat.le_of_lt hj)] using hv

/-- The parameter types are local in the varying parameters (`ParamTyLocalD`, for a function). -/
def LocalP : Prop :=
  ∀ (j : Nat) (ps ps' : List Sem), ps.length = j → ps'.length = j → paramVaries d j = false →
    (∀ u, u < j → paramVaries d u = false → ps[u]? = ps'[u]?) → P j ps = P j ps'

/-- **Two lists whose steps agree at each parameter that does not vary have canonical forms equal
there.** -/
theorem canonPs_agree (hP : LocalP P d) (ps ps' : List Sem) (hl : ps.length = ps'.length)
    (hstep : ∀ j (hj : j < ps.length) (hj' : j < ps'.length), paramVaries d j = false →
      stepAt dm (P j ((canonPs dm P d ps).take j)) ps[j] = stepAt dm (P j ((canonPs dm P d ps).take j)) ps'[j]) :
    ∀ j, paramVaries d j = false → (canonPs dm P d ps)[j]? = (canonPs dm P d ps')[j]? := by
  intro j
  induction j using Nat.strongRecOn with
  | ind j ih =>
    intro hv
    by_cases hj : j < ps.length
    · have hj' : j < ps'.length := hl ▸ hj
      have hlen : ((canonPs dm P d ps).take j).length = j := by simp [canonPs_length]; omega
      have hlen' : ((canonPs dm P d ps').take j).length = j := by simp [canonPs_length]; omega
      rw [canonPs_getElem dm P d ps j hj, canonPs_getElem dm P d ps' j hj',
        canonStep_nonvary dm P d _ _ (by rw [hlen]; exact hv), canonStep_nonvary dm P d _ _ (by rw [hlen']; exact hv),
        hlen, hlen']
      have hPe : P j ((canonPs dm P d ps).take j) = P j ((canonPs dm P d ps').take j) := by
        apply hP j _ _ hlen hlen' hv
        intro u hu hvu
        rw [List.getElem?_take, List.getElem?_take, if_pos hu, if_pos hu]
        exact ih u hu hvu
      rw [← hPe, hstep j hj hj' hv]
    · have h1 : (canonPs dm P d ps)[j]? = none := by
        rw [List.getElem?_eq_none_iff, canonPs_length]; omega
      have h2 : (canonPs dm P d ps')[j]? = none := by
        rw [List.getElem?_eq_none_iff, canonPs_length]; omega
      rw [h1, h2]

/-- **Parametricity is kept** (what `knot_exists`' `hpar` reads of an earlier declaration): lists
agreeing below `n` at the nestable parameters and equal elsewhere have canonical forms that do. -/
theorem canonPs_parAgree (hP : LocalP P d) {n : Nat} {ps ps' : List Sem}
    (h : ParAgree (fun j => d.nestable.getD j false) n ps ps') :
    ParAgree (fun j => d.nestable.getD j false) n (canonPs dm P d ps) (canonPs dm P d ps') := by
  have hnv : ∀ j (hj : j < ps.length) (hj' : j < ps'.length), paramVaries d j = false → ps[j] = ps'[j] := by
    intro j hj hj' hv
    have := h.2 j ps[j] ps'[j] (List.getElem?_eq_getElem hj) (List.getElem?_eq_getElem hj')
    have hN : d.nestable.getD j false = false := (paramVaries_false hv).1
    simp only [List.getD_eq_getElem?_getD] at hN
    simpa [hN] using this
  have hag := canonPs_agree dm P d hP ps ps' h.1 (fun j hj hj' hv => by rw [hnv j hj hj' hv])
  refine ⟨by rw [canonPs_length, canonPs_length]; exact h.1, fun j v v' e e' => ?_⟩
  by_cases hv : paramVaries d j = false
  · have := hag j hv
    rw [e, e'] at this
    cases this
    have hN := (paramVaries_false hv).1
    simp only [hN, Bool.false_eq_true, if_false]
  · have hv' : paramVaries d j = true := by simpa using hv
    have hj : j < ps.length := by
      have := (List.getElem?_eq_some_iff.1 e).1; rwa [canonPs_length] at this
    have hj' : j < ps'.length := by
      have := (List.getElem?_eq_some_iff.1 e').1; rwa [canonPs_length] at this
    rw [canonPs_vary dm P d ps j hj hv'] at e
    rw [canonPs_vary dm P d ps' j hj' hv'] at e'
    cases e; cases e'
    exact h.2 j _ _ (List.getElem?_eq_getElem hj) (List.getElem?_eq_getElem hj')

/-- **Monotonicity is kept** (what `truth_exists`' `hmono` reads of an earlier declaration). -/
theorem canonPs_propLe (hP : LocalP P d) {ps ps' : List Sem} (h : PropLe d ps ps') :
    PropLe d (canonPs dm P d ps) (canonPs dm P d ps') := by
  have hnv : ∀ j (hj : j < ps.length) (hj' : j < ps'.length), paramVaries d j = false → ps[j] = ps'[j] := by
    intro j hj hj' hv
    rcases h.2 j ps[j] ps'[j] (List.getElem?_eq_getElem hj) (List.getElem?_eq_getElem hj') with e | ⟨hN, _⟩
    · exact e.symm
    · have := (paramVaries_false hv).1; rw [this] at hN; cases hN
  have hag := canonPs_agree dm P d hP ps ps' h.1.symm (fun j hj hj' hv => by rw [hnv j hj hj' hv])
  refine ⟨by rw [canonPs_length, canonPs_length]; exact h.1, fun j v v' e e' => ?_⟩
  by_cases hv : paramVaries d j = false
  · have := hag j hv
    rw [e, e'] at this
    cases this
    exact .inl rfl
  · have hv' : paramVaries d j = true := by simpa using hv
    have hj : j < ps.length := by
      have := (List.getElem?_eq_some_iff.1 e).1; rwa [canonPs_length] at this
    have hj' : j < ps'.length := by
      have := (List.getElem?_eq_some_iff.1 e').1; rwa [canonPs_length] at this
    rw [canonPs_vary dm P d ps j hj hv'] at e
    rw [canonPs_vary dm P d ps' j hj' hv'] at e'
    cases e; cases e'
    exact h.2 j _ _ (List.getElem?_eq_getElem hj) (List.getElem?_eq_getElem hj')

/-- **A list and its small-reading variant** (`RecordsFaithful.smallOnly`'s hypothesis): the variant's
canonical form equals the members at every parameter that does not vary, and differs at a varying one
only by a value of the same small reading, where the member has a level-0 type. -/
theorem canonPs_small (hP : LocalP P d) {ps ps' : List Sem} (ht : Typed dm P ps) (hl : ps'.length = ps.length)
    (h : ∀ (j : Nat) (v v' : Sem), ps[j]? = some v → ps'[j]? = some v' →
      v' = v ∨ ((∃ (A : Type) (c : Code0 A), P j (ps.take j) = .t0 A c ∧ v ∈ₛ[dm.read] .t0 A c) ∧ v'.small = v.small)) :
    (canonPs dm P d ps').length = ps.length ∧ ∀ j v v', ps[j]? = some v → (canonPs dm P d ps')[j]? = some v' →
      v' = v ∨ (paramVaries d j = true ∧ (∃ (A : Type) (c : Code0 A), P j (ps.take j) = .t0 A c ∧ v ∈ₛ[dm.read] .t0 A c) ∧
        v'.small = v.small) := by
  have hc := canonPs_typed dm P d ps ht
  have hag := canonPs_agree dm P d hP ps ps' hl.symm (by
    intro j hj hj' hv
    rw [hc]
    rcases h j ps[j] ps'[j] (List.getElem?_eq_getElem hj) (List.getElem?_eq_getElem hj') with e | ⟨⟨A, c, hT, hm⟩, hs⟩
    · rw [e]
    · unfold stepAt; rw [hT]; dsimp only; rw [hs])
  refine ⟨by rw [canonPs_length, hl], fun j v v' e e' => ?_⟩
  by_cases hv : paramVaries d j = false
  · have := hag j hv
    rw [hc, e, e'] at this
    cases this
    exact .inl rfl
  · have hv' : paramVaries d j = true := by simpa using hv
    have hj' : j < ps'.length := by
      have := (List.getElem?_eq_some_iff.1 e').1; rwa [canonPs_length] at this
    rw [canonPs_vary dm P d ps' j hj' hv'] at e'
    cases e'
    rcases h j v ps'[j] e (List.getElem?_eq_getElem hj') with e2 | ⟨hT, hs⟩
    · exact .inl e2
    · exact .inr ⟨hv', hT, hs⟩

end

/-! ## The knot reads a varying value parameter only small -/

/-- A member of a level-0 type has a small reading other than `other` (so no value of the same small
reading is a type value, `.ty X`, whose small reading is `other`). -/
theorem mem_t0_small (dm : DataModel) {A : Type} (c : Code0 A) {v : Sem} (hv : v ∈ₛ[dm.read] .t0 A c) :
    v.small ≠ .other := by
  obtain ⟨a, rfl⟩ := hv
  cases c with
  | prop P => simp [Code0.enc, Sem.small]
  | nat => simp [Code0.enc, Sem.small]
  | unit => simp [Code0.enc, Sem.small]
  | pi C t => simp [Code0.enc, Sem.small]
  | err => exact a.elim
  | data d r =>
    show (dm.readFn d r A a).small ≠ .other
    unfold DataModel.readFn
    split
    · rename_i hB
      obtain ⟨k, hk⟩ := (DataLib.mem_iff_meanC dm.sig d r (dm.meanC (cast hB a))).2 ⟨cast hB a, rfl⟩
      cases k with
      | zero => obtain ⟨x, _⟩ := hk; exact x.elim
      | succ k =>
        obtain ⟨c, fs, he, _⟩ := (DataLib.rz_succ_iff dm.sig k d r _).1 hk
        rw [he]; simp [Sem.small]
    · simp [Sem.small]

/-- **No field type reads a varying value parameter** (exists9; a fact about the checker, enforced by
typing, decidable): a value parameter whose type reads a nestable parameter occurs free in no field
type. Such a parameter could only stand where a type is expected: a steady node reads no varying
variable, and a value argument of an applied type is steady. -/
def VaryValFree (d : IndDecl) : Prop :=
  ∀ c i FT, fieldTerm d c i = some FT → ∀ v ∈ FT.freeVars, v < d.params.length →
    paramVaries d (d.params.length - 1 - v) = true → d.paramIsType (d.params.length - 1 - v) = true

/-- Parameter lists equal at every parameter the term reads. -/
def PsAt (np : Nat) (ps ps' : List Sem) (t : Term) : Prop :=
  ∀ v ∈ t.freeVars, v < np → ps.getD (np - 1 - v) .err = ps'.getD (np - 1 - v) .err

section
variable {K : RunCtx} {ρ : Assignment} {d : IndDecl} {c : Nat} {R : List Sem → Rec} {ps ps' : List Sem} {s : SState}

mutual
theorem semT_psAt : ∀ {t : Term}, Spine K.Γ d c t → PsAt d.params.length ps ps' t →
    ∀ h, semT K ρ d R ps s h t = semT K ρ d R ps' s h t
  | _, .nat, _, _ => by
    rw [semT_other K ρ d R ps s _ _ (fun _ _ e => by cases e) (fun _ e => by cases e),
      semT_other K ρ d R ps' s _ _ (fun _ _ e => by cases e) (fun _ e => by cases e)]
  | _, .unit, _, _ => by
    rw [semT_other K ρ d R ps s _ _ (fun _ _ e => by cases e) (fun _ e => by cases e),
      semT_other K ρ d R ps' s _ _ (fun _ _ e => by cases e) (fun _ e => by cases e)]
  | _, .param v hv, hq, h => by
    rw [semT_var K ρ d R ps s h v hv, semT_var K ρ d R ps' s h v hv]
    exact hq v (FrameLocal.root_mem_place (.var v)) hv
  | _, .tind n as M hM hargs, hq, h => by
    rw [semT_tind, semT_tind, hM]
    dsimp only
    rw [itpArgs_psAt hargs (fun a ha v hv hlt => hq v (mem_freeVars_tind ha hv) hlt) []]
  | _, .call _ _ _ _, _, _ => by
    rw [semT_other K ρ d R ps s _ _ (fun _ _ e => by cases e) (fun _ e => by cases e),
      semT_other K ρ d R ps' s _ _ (fun _ _ e => by cases e) (fun _ e => by cases e)]
  | _, .eq _ _ _ _, _, _ => by
    rw [semT_other K ρ d R ps s _ _ (fun _ _ e => by cases e) (fun _ e => by cases e),
      semT_other K ρ d R ps' s _ _ (fun _ _ e => by cases e) (fun _ e => by cases e)]

theorem itpArgs_psAt : ∀ {M : IndDecl} {j : Nat} {pre as : List Term}, SpineArgs K.Γ d c M j pre as →
    (∀ a ∈ as, PsAt d.params.length ps ps' a) →
      ∀ vpre, itpArgs K ρ d R ps s M j vpre as = itpArgs K ρ d R ps' s M j vpre as
  | _, _, _, _, .nil _ _ _, _, vpre => by rw [itpArgs_nil, itpArgs_nil]
  | _, _, _, _, .type M j pre a as hty ha _ _ hrest, hq, vpre => by
    have e : argSem K ρ d R ps s M j vpre a = argSem K ρ d R ps' s M j vpre a := by
      rw [argSem_eq, argSem_eq, if_pos hty, if_pos hty]
      exact semT_psAt ha (hq a (List.mem_cons_self ..)) _
    rw [itpArgs_cons, itpArgs_cons, e,
      itpArgs_psAt hrest (fun b hb => hq b (List.mem_cons_of_mem _ hb)) _]
  | _, _, _, _, .value M j pre a as hty _ hrest, hq, vpre => by
    have e : argSem K ρ d R ps s M j vpre a = argSem K ρ d R ps' s M j vpre a := by
      rw [argSem_eq, argSem_eq, if_neg (by simp [hty]), if_neg (by simp [hty])]
    rw [itpArgs_cons, itpArgs_cons, e,
      itpArgs_psAt hrest (fun b hb => hq b (List.mem_cons_of_mem _ hb)) _]
end

theorem itpT_psAt {t : Term} (ht : Spine K.Γ d c t) (hq : PsAt d.params.length ps ps' t) (h : TyS) :
    itpT K ρ d R ps s h t = itpT K ρ d R ps' s h t := by
  cases ht with
  | tind n as M hM hargs =>
    rw [itpT_tind, itpT_tind, hM]
    dsimp only
    rw [itpArgs_psAt hargs (fun a ha v hv hlt => hq v (mem_freeVars_tind ha hv) hlt) []]
  | _ =>
    rw [itpT_other _ _ _ _ _ _ _ _ (fun _ _ e => by cases e), itpT_other _ _ _ _ _ _ _ _ (fun _ _ e => by cases e),
      semT_psAt (c := c) (by constructor <;> assumption) hq h]

/-- **The knot's field types at parameter lists equal where they do not vary and at every parameter a
field type reads.** -/
theorem ftyK_psAt (hspine : ∀ c i FT, fieldTerm d c i = some FT → Spine K.Γ d c FT)
    (hpty : ParamTyLocalD K.dm d) (hdΓ : d ∈ K.Γ) (hl : ps.length = ps'.length) (hps : PsSteady d ps ps')
    (hfree : ∀ i FT, fieldTerm d c i = some FT → PsAt d.params.length ps ps' FT) :
    ∀ (i : Nat) (es : List Small), ftyK K ρ d R ps c i es = ftyK K ρ d R ps' c i es := by
  intro i
  induction i using Nat.strongRecOn with
  | ind i ih =>
    intro es
    rw [ftyK_eq, ftyK_eq]
    cases hFT : fieldTerm d c i with
    | none => rfl
    | some FT =>
      dsimp only
      rw [canFrame_eq hpty hdΓ hl hps (tyOf' := fun j => if _h : j < i then
          shapeTyP (shapeOf (ftyK K ρ d R ps' c j (es.take j))) else TyM.err)
        (fun j hj _ _ => by simp only [dif_pos hj]; rw [ih j hj _])]
      exact itpT_psAt (hspine c i FT hFT) (hfree i FT hFT) _

end

/-- A knot's record at two parameter lists is the same when its field types, parameter entries and
parameters' records are. -/
theorem recK_congr (S : KnotSpec) {ps ps' : List Sem}
    (hf : ∀ R c i es, S.fty R ps c i es = S.fty R ps' c i es) (he : ∀ j, S.pEntry ps j = S.pEntry ps' j)
    (hr : ∀ j, paramRec ps j = paramRec ps' j) : recK S ps = recK S ps' := by
  funext p
  show approx S (p.length + 1) ps p = approx S (p.length + 1) ps' p
  show stepRec S (approx S p.length) ps p = stepRec S (approx S p.length) ps' p
  cases p with
  | nil => rfl
  | cons st q => simp only [stepRec, hf, he, hr]

/-- **A knot's record reads a type parameter back** (`PreludeModel.paramTyOf_recK` with the entry
asked only at that parameter). -/
theorem paramTyOf_recK' (dm : DataModel) (S : KnotSpec) (ps : List Sem) (j : Nat) (hS : S.pEntry ps j = pEntryTy ps j)
    {A : Type} (c : Code0 A) (h : ps[j]? = some (.ty (.t0 A c))) : dm.paramTyOf (recK S ps) j = .t0 A c := by
  have hpar : parTy ps j = .t0 A c := by simp [parTy, h, Sem.asTy]
  have hk : recK S ps (paramKey j) = (FTy.ty (.t0 A c)).kind := by
    rw [recK_param, hS]; unfold pEntryTy; rw [hpar]
  unfold DataModel.paramTyOf
  rw [hk]
  rcases hv : dataView (.t0 A c) with _ | ⟨d', r'⟩
  · simp [FTy.kind, hv]
  · have hkd : (FTy.ty (.t0 A c)).kind = .data d' := by simp [FTy.kind, hv]
    rw [hkd]
    have hc : contRec (recK S ps) (paramContStep j) = r' := by
      funext q
      show recK S ps (paramContStep j :: q) = r' q
      rw [recK_paramCont]
      simp [paramRec, h, FTy.cont, hv]
    obtain ⟨-, he⟩ := dataView_some hv
    simp only
    rw [hc, tyR_eq_uTyR, ← he]

section
variable (K : RunCtx) (ρ : Assignment) (d : IndDecl) (hs : d.sort ≠ 0) (hdΓ : d ∈ K.Γ)
  (hspine : ∀ c i FT, fieldTerm d c i = some FT → Spine K.Γ d c FT)
  (hpar : ∀ M ∈ K.Γ, M ≠ d → ∀ n, RAgree (fun j => M.nestable.getD j false) n (K.dm.recOf M) (K.dm.recOf M))
  (hpty : ParamTyLocalD K.dm d)

/-- **The model's record of a data-sorted declaration**: the knot's at the canonical parameters. -/
noncomputable def recCanon : List Sem → Rec :=
  fun ps => recK (knotK K ρ d hs hdΓ hspine hpar hpty) (canonPs K.dm (K.dm.paramTy d) d ps)

/-- **Piece 6 for a data-sorted declaration**: the records `recCanon` are faithful (`types`, `values`,
`smallOnly`) at any context whose model has them and the same parameter types at `d`. Assumes, besides
the knot's: `hTyP` (a type parameter's type has no level-0 member; the run-defined parameter types
read a universe, `Params.pty_type`), `hfree` (`VaryValFree`, a fact about the checker), and `hleaf`, the clause
`leafOk` itself (OPEN: the knot's field types at members are never the raw code of a `Prop`-sorted
declaration; a property of the run, see docs/34 §18.14). -/
theorem recordsFaithful_canon
    (hTyP : ∀ j qs, d.paramIsType j = true → ∀ (A : Type) (c : Code0 A) (v : Sem), K.dm.paramTy d j qs = .t0 A c →
      ¬ v ∈ₛ[K.dm.read] .t0 A c)
    (hfree : VaryValFree d) (K' : RunCtx)
    (hrec : K'.dm.recOf d = recCanon K ρ d hs hdΓ hspine hpar hpty) (hpt : K'.dm.paramTy d = K.dm.paramTy d)
    (hleaf : ∀ ps, ps.length = d.params.length → ParamsTyped K'.dm d ps → K'.dm.RecLeafOk d (K'.dm.recOf d ps)) :
    RecordsFaithfulAt K' d := by
  have htyped : ∀ ps, ParamsTyped K'.dm d ps → Typed K.dm (K.dm.paramTy d) ps := fun ps h j hj => by
    have := h j hj; rw [hpt] at this; exact this
  have hcanon : ∀ ps, ParamsTyped K'.dm d ps → K'.dm.recOf d ps = recK (knotK K ρ d hs hdΓ hspine hpar hpty) ps :=
    fun ps h => by rw [hrec]; show recK _ (canonPs _ _ _ ps) = _; rw [canonPs_typed _ _ _ ps (htyped ps h)]
  refine ⟨?types, ?values, ?smallOnly, hleaf⟩
  case types =>
    intro ps j A c _ hty hps hj
    rw [hcanon ps hps]
    exact paramTyOf_recK' K'.dm _ ps j (by simp [knotK, pEntryV, hty]) c hj
  case values =>
    intro ps j v A c hps hj hT hv
    rw [hcanon ps hps, recK_param]
    have hty : d.paramIsType j = false := by
      cases e : d.paramIsType j
      · rfl
      · exact absurd hv (hTyP j _ e A c v (hpt ▸ hT))
    simp [knotK, pEntryV, hty, List.getD_eq_getElem?_getD, hj]
  case smallOnly =>
    intro ps ps' hps hl hrel
    rw [hcanon ps hps, hrec]
    show recK _ (canonPs _ _ _ ps') = _
    have hrel' : ∀ (j : Nat) (v v' : Sem), ps[j]? = some v → ps'[j]? = some v' →
        v' = v ∨ ((∃ (A : Type) (c : Code0 A), K.dm.paramTy d j (ps.take j) = .t0 A c ∧ v ∈ₛ[K.dm.read] .t0 A c) ∧
          v'.small = v.small) := fun j v v' h1 h2 => by
      rcases hrel j v v' h1 h2 with e | ⟨⟨A, c, hT, hm⟩, hsm⟩
      · exact .inl e
      · exact .inr ⟨⟨A, c, hpt ▸ hT, hm⟩, hsm⟩
    obtain ⟨hlq, hq⟩ := canonPs_small K.dm (K.dm.paramTy d) d hpty (htyped ps hps) hl hrel'
    generalize canonPs K.dm (K.dm.paramTy d) d ps' = q at hlq hq ⊢
    -- at a position, `ps` and `q` are equal, or `d`'s parameter there varies, is a value parameter, and
    -- the two have one small reading, neither a type value
    have hpos : ∀ j, ps.getD j .err = q.getD j .err ∨
        (paramVaries d j = true ∧ d.paramIsType j = false ∧ (ps.getD j .err).small = (q.getD j .err).small ∧
          (ps.getD j .err).small ≠ .other) := by
      intro j
      by_cases hj : j < ps.length
      · have hj' : j < q.length := by rw [hlq]; exact hj
        rcases hq j ps[j] q[j] (List.getElem?_eq_getElem hj) (List.getElem?_eq_getElem hj') with e | ⟨hv, ⟨A, c, hT, hm⟩, hsm⟩
        · left; simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, List.getElem?_eq_getElem hj', e]
        · right
          have hty : d.paramIsType j = false := by
            cases e : d.paramIsType j
            · rfl
            · exact absurd hm (hTyP j _ e A c _ hT)
          simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, List.getElem?_eq_getElem hj',
            Option.getD_some]
          exact ⟨hv, hty, hsm.symm, mem_t0_small K.dm c hm⟩
      · left
        have h1 : ps[j]? = none := List.getElem?_eq_none_iff.2 (by omega)
        have h2 : q[j]? = none := List.getElem?_eq_none_iff.2 (by omega)
        simp [List.getD_eq_getElem?_getD, h1, h2]
    have hsteady : PsSteady d ps q := fun j hv => by
      rcases hpos j with e | ⟨hv', _⟩
      · exact e
      · rw [hv] at hv'; cases hv'
    have hfreeq : ∀ (c i : Nat) (FT : Term), fieldTerm d c i = some FT → PsAt d.params.length ps q FT := by
      intro c i FT hFT v hv hlt
      rcases hpos (d.params.length - 1 - v) with e | ⟨hvar, hty, _⟩
      · exact e
      · have := hfree c i FT hFT v hv hlt hvar
        rw [hty] at this; cases this
    symm
    apply recK_congr
    · intro R c i es
      exact ftyK_psAt (K := K) (ρ := ρ) (c := c) hspine hpty hdΓ hlq.symm hsteady (hfreeq c) i es
    · intro j
      show pEntryV d ps j = pEntryV d q j
      unfold pEntryV
      rcases hpos j with e | ⟨_, hty, hsm, _⟩
      · split
        · unfold pEntryTy parTy
          have : ps[j]? = q[j]? := by
            by_cases hj : j < ps.length
            · have hj' : j < q.length := by rw [hlq]; exact hj
              simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, List.getElem?_eq_getElem hj',
                Option.getD_some] at e
              rw [List.getElem?_eq_getElem hj, List.getElem?_eq_getElem hj', e]
            · rw [List.getElem?_eq_none_iff.2 (by omega), List.getElem?_eq_none_iff.2 (by omega)]
          rw [this]
        · rw [e]
      · rw [if_neg (by simp [hty]), if_neg (by simp [hty]), hsm]
    · intro j
      unfold paramRec
      rcases hpos j with e | ⟨_, _, hsm, hne⟩
      · by_cases hj : j < ps.length
        · have hj' : j < q.length := by rw [hlq]; exact hj
          simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, List.getElem?_eq_getElem hj',
            Option.getD_some] at e
          rw [List.getElem?_eq_getElem hj, List.getElem?_eq_getElem hj', e]
        · rw [List.getElem?_eq_none_iff.2 (by omega), List.getElem?_eq_none_iff.2 (by omega)]
      · have hj : j < ps.length := by
          rcases Nat.lt_or_ge j ps.length with h | h
          · exact h
          · exfalso; apply hne; simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none_iff.2 h, Sem.small]
        have hj' : j < q.length := by rw [hlq]; exact hj
        simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, List.getElem?_eq_getElem hj',
          Option.getD_some] at hsm hne
        rw [List.getElem?_eq_getElem hj, List.getElem?_eq_getElem hj']
        have h1 : ∀ X, ps[j] ≠ .ty X := fun X e => hne (by rw [e]; rfl)
        have h2 : ∀ X, q[j] ≠ .ty X := fun X e => hne (by rw [hsm, e]; rfl)
        rcases e1 : ps[j] with _ | _ | _ | _ | _ | _ | _ | _ <;> rcases e2 : q[j] with _ | _ | _ | _ | _ | _ | _ | _ <;>
          first | rfl | exact absurd e1 (h1 _) | exact absurd e2 (h2 _)

/-- **Parametricity of the model's records** (`Inv.par`): the canonical form keeps `ParAgree`. -/
theorem par_canon (n : Nat) :
    RAgree (fun j => d.nestable.getD j false) n (recCanon K ρ d hs hdΓ hspine hpar hpty)
      (recCanon K ρ d hs hdΓ hspine hpar hpty) := fun ps ps' h =>
  recK_agree (knotK K ρ d hs hdΓ hspine hpar hpty) n _ _ (canonPs_parAgree K.dm (K.dm.paramTy d) d hpty h)

end

/-! ## The same for a `Prop`-sorted declaration (the truth spec) -/

section
variable {K : RunCtx} {ρ : Assignment} {d : IndDecl} {c : Nat} {T : List Sem → Prop} {ps ps' : List Sem} {s : SState}

mutual
theorem semP_psAt : ∀ {t : Term}, PSpine K.Γ d c t → PsAt d.params.length ps ps' t →
    ∀ h, semP K ρ d T ps s h t = semP K ρ d T ps' s h t
  | _, .nat, _, _ => by
    rw [semP_other K ρ d T ps s _ _ (fun _ _ e => by cases e) (fun _ e => by cases e),
      semP_other K ρ d T ps' s _ _ (fun _ _ e => by cases e) (fun _ e => by cases e)]
  | _, .unit, _, _ => by
    rw [semP_other K ρ d T ps s _ _ (fun _ _ e => by cases e) (fun _ e => by cases e),
      semP_other K ρ d T ps' s _ _ (fun _ _ e => by cases e) (fun _ e => by cases e)]
  | _, .param v hv, hq, h => by
    rw [semP_var K ρ d T ps s h v hv, semP_var K ρ d T ps' s h v hv]
    exact hq v (FrameLocal.root_mem_place (.var v)) hv
  | _, .tind n as M hM hargs, hq, h => by
    rw [semP_tind, semP_tind, hM]
    dsimp only
    rw [itpArgsP_psAt hargs (fun a ha v hv hlt => hq v (mem_freeVars_tind ha hv) hlt) []]
  | _, .call _ _ _ _, _, _ => by
    rw [semP_other K ρ d T ps s _ _ (fun _ _ e => by cases e) (fun _ e => by cases e),
      semP_other K ρ d T ps' s _ _ (fun _ _ e => by cases e) (fun _ e => by cases e)]
  | _, .eq _ _ _ _, _, _ => by
    rw [semP_other K ρ d T ps s _ _ (fun _ _ e => by cases e) (fun _ e => by cases e),
      semP_other K ρ d T ps' s _ _ (fun _ _ e => by cases e) (fun _ e => by cases e)]

theorem itpArgsP_psAt : ∀ {M : IndDecl} {j : Nat} {pre as : List Term}, PSpineArgs K.Γ d c M j pre as →
    (∀ a ∈ as, PsAt d.params.length ps ps' a) →
      ∀ vpre, itpArgsP K ρ d T ps s M j vpre as = itpArgsP K ρ d T ps' s M j vpre as
  | _, _, _, _, .nil _ _ _, _, vpre => by rw [itpArgsP_nil, itpArgsP_nil]
  | _, _, _, _, .type M j pre a as hty ha _ _ hrest, hq, vpre => by
    have e : argSemP K ρ d T ps s M j vpre a = argSemP K ρ d T ps' s M j vpre a := by
      rw [argSemP_eq, argSemP_eq, if_pos hty, if_pos hty]
      exact semP_psAt ha (hq a (List.mem_cons_self ..)) _
    rw [itpArgsP_cons, itpArgsP_cons, e,
      itpArgsP_psAt hrest (fun b hb => hq b (List.mem_cons_of_mem _ hb)) _]
  | _, _, _, _, .value M j pre a as hty _ hrest, hq, vpre => by
    have e : argSemP K ρ d T ps s M j vpre a = argSemP K ρ d T ps' s M j vpre a := by
      rw [argSemP_eq, argSemP_eq, if_neg (by simp [hty]), if_neg (by simp [hty])]
    rw [itpArgsP_cons, itpArgsP_cons, e,
      itpArgsP_psAt hrest (fun b hb => hq b (List.mem_cons_of_mem _ hb)) _]
end

theorem itpP_psAt {t : Term} (ht : PSpine K.Γ d c t) (hq : PsAt d.params.length ps ps' t) (h : TyS) :
    itpP K ρ d T ps s h t = itpP K ρ d T ps' s h t := by
  cases ht with
  | tind n as M hM hargs =>
    rw [itpP_tind, itpP_tind, hM]
    dsimp only
    rw [itpArgsP_psAt hargs (fun a ha v hv hlt => hq v (mem_freeVars_tind ha hv) hlt) []]
  | _ =>
    rw [itpP_other _ _ _ _ _ _ _ _ (fun _ _ e => by cases e), itpP_other _ _ _ _ _ _ _ _ (fun _ _ e => by cases e),
      semP_psAt (c := c) (by constructor <;> assumption) hq h]

/-- **The truth interpreter's field types at parameter lists equal where they do not vary and at every
parameter a field type reads.** -/
theorem ftyP_psAt (hspine : ∀ c i FT, fieldTerm d c i = some FT → PSpine K.Γ d c FT)
    (hpty : ParamTyLocalD K.dm d) (hdΓ : d ∈ K.Γ) (hl : ps.length = ps'.length) (hps : PsSteady d ps ps')
    (hfree : ∀ i FT, fieldTerm d c i = some FT → PsAt d.params.length ps ps' FT) :
    ∀ (i : Nat) (es : List Small), ftyP K ρ d T ps c i es = ftyP K ρ d T ps' c i es := by
  intro i
  induction i using Nat.strongRecOn with
  | ind i ih =>
    intro es
    rw [ftyP_eq, ftyP_eq]
    cases hFT : fieldTerm d c i with
    | none => rfl
    | some FT =>
      dsimp only
      rw [canFrame_eq hpty hdΓ hl hps (tyOf' := fun j => if _h : j < i then
          shapeTyP (shapeOf (ftyP K ρ d T ps' c j (es.take j))) else TyM.err)
        (fun j hj _ _ => by simp only [dif_pos hj]; rw [ih j hj _])]
      exact itpP_psAt (hspine c i FT hFT) (hfree i FT hFT) _

end

section
variable (K : RunCtx) (ρ : Assignment) (d : IndDecl) (T : List Sem → Prop) (hdΓ : d ∈ K.Γ)
  (hspine : ∀ c i FT, fieldTerm d c i = some FT → PSpine K.Γ d c FT) (hpty : ParamTyLocalD K.dm d)

/-- **The model's record of a `Prop`-sorted declaration**: the truth spec's at the canonical parameters. -/
noncomputable def recCanonP : List Sem → Rec :=
  fun ps => recK (truthSpec K ρ d T) (canonPs K.dm (K.dm.paramTy d) d ps)

include hdΓ hspine hpty in
/-- **Piece 6 for a `Prop`-sorted declaration**: the records `recCanonP` (the truth spec's at the canonical
parameters) are faithful (`types`, `values`,
`smallOnly`) at any context whose model has them and the same parameter types at `d`. Assumes, besides
the knot's: `hTyP` (a type parameter's type has no level-0 member; the run-defined parameter types
read a universe, `Params.pty_type`), `hfree` (`VaryValFree`, a fact about the checker), and `hleaf`, the clause
`leafOk` itself (OPEN: the knot's field types at members are never the raw code of a `Prop`-sorted
declaration; a property of the run, see docs/34 §18.14). -/
theorem recordsFaithful_canonP
    (hTyP : ∀ j qs, d.paramIsType j = true → ∀ (A : Type) (c : Code0 A) (v : Sem), K.dm.paramTy d j qs = .t0 A c →
      ¬ v ∈ₛ[K.dm.read] .t0 A c)
    (hfree : VaryValFree d) (K' : RunCtx)
    (hrec : K'.dm.recOf d = recCanonP K ρ d T) (hpt : K'.dm.paramTy d = K.dm.paramTy d)
    (hleaf : ∀ ps, ps.length = d.params.length → ParamsTyped K'.dm d ps → K'.dm.RecLeafOk d (K'.dm.recOf d ps)) :
    RecordsFaithfulAt K' d := by
  have htyped : ∀ ps, ParamsTyped K'.dm d ps → Typed K.dm (K.dm.paramTy d) ps := fun ps h j hj => by
    have := h j hj; rw [hpt] at this; exact this
  have hcanon : ∀ ps, ParamsTyped K'.dm d ps → K'.dm.recOf d ps = recK (truthSpec K ρ d T) ps :=
    fun ps h => by rw [hrec]; show recK _ (canonPs _ _ _ ps) = _; rw [canonPs_typed _ _ _ ps (htyped ps h)]
  refine ⟨?types, ?values, ?smallOnly, hleaf⟩
  case types =>
    intro ps j A c _ hty hps hj
    rw [hcanon ps hps]
    exact paramTyOf_recK' K'.dm _ ps j (by simp [truthSpec, pEntryV, hty]) c hj
  case values =>
    intro ps j v A c hps hj hT hv
    rw [hcanon ps hps, recK_param]
    have hty : d.paramIsType j = false := by
      cases e : d.paramIsType j
      · rfl
      · exact absurd hv (hTyP j _ e A c v (hpt ▸ hT))
    simp [truthSpec, pEntryV, hty, List.getD_eq_getElem?_getD, hj]
  case smallOnly =>
    intro ps ps' hps hl hrel
    rw [hcanon ps hps, hrec]
    show recK _ (canonPs _ _ _ ps') = _
    have hrel' : ∀ (j : Nat) (v v' : Sem), ps[j]? = some v → ps'[j]? = some v' →
        v' = v ∨ ((∃ (A : Type) (c : Code0 A), K.dm.paramTy d j (ps.take j) = .t0 A c ∧ v ∈ₛ[K.dm.read] .t0 A c) ∧
          v'.small = v.small) := fun j v v' h1 h2 => by
      rcases hrel j v v' h1 h2 with e | ⟨⟨A, c, hT, hm⟩, hsm⟩
      · exact .inl e
      · exact .inr ⟨⟨A, c, hpt ▸ hT, hm⟩, hsm⟩
    obtain ⟨hlq, hq⟩ := canonPs_small K.dm (K.dm.paramTy d) d hpty (htyped ps hps) hl hrel'
    generalize canonPs K.dm (K.dm.paramTy d) d ps' = q at hlq hq ⊢
    -- at a position, `ps` and `q` are equal, or `d`'s parameter there varies, is a value parameter, and
    -- the two have one small reading, neither a type value
    have hpos : ∀ j, ps.getD j .err = q.getD j .err ∨
        (paramVaries d j = true ∧ d.paramIsType j = false ∧ (ps.getD j .err).small = (q.getD j .err).small ∧
          (ps.getD j .err).small ≠ .other) := by
      intro j
      by_cases hj : j < ps.length
      · have hj' : j < q.length := by rw [hlq]; exact hj
        rcases hq j ps[j] q[j] (List.getElem?_eq_getElem hj) (List.getElem?_eq_getElem hj') with e | ⟨hv, ⟨A, c, hT, hm⟩, hsm⟩
        · left; simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, List.getElem?_eq_getElem hj', e]
        · right
          have hty : d.paramIsType j = false := by
            cases e : d.paramIsType j
            · rfl
            · exact absurd hm (hTyP j _ e A c _ hT)
          simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, List.getElem?_eq_getElem hj',
            Option.getD_some]
          exact ⟨hv, hty, hsm.symm, mem_t0_small K.dm c hm⟩
      · left
        have h1 : ps[j]? = none := List.getElem?_eq_none_iff.2 (by omega)
        have h2 : q[j]? = none := List.getElem?_eq_none_iff.2 (by omega)
        simp [List.getD_eq_getElem?_getD, h1, h2]
    have hsteady : PsSteady d ps q := fun j hv => by
      rcases hpos j with e | ⟨hv', _⟩
      · exact e
      · rw [hv] at hv'; cases hv'
    have hfreeq : ∀ (c i : Nat) (FT : Term), fieldTerm d c i = some FT → PsAt d.params.length ps q FT := by
      intro c i FT hFT v hv hlt
      rcases hpos (d.params.length - 1 - v) with e | ⟨hvar, hty, _⟩
      · exact e
      · have := hfree c i FT hFT v hv hlt hvar
        rw [hty] at this; cases this
    symm
    apply recK_congr
    · intro R c i es
      exact ftyP_psAt (K := K) (ρ := ρ) (c := c) (T := T) hspine hpty hdΓ hlq.symm hsteady (hfreeq c) i es
    · intro j
      show pEntryV d ps j = pEntryV d q j
      unfold pEntryV
      rcases hpos j with e | ⟨_, hty, hsm, _⟩
      · split
        · unfold pEntryTy parTy
          have : ps[j]? = q[j]? := by
            by_cases hj : j < ps.length
            · have hj' : j < q.length := by rw [hlq]; exact hj
              simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, List.getElem?_eq_getElem hj',
                Option.getD_some] at e
              rw [List.getElem?_eq_getElem hj, List.getElem?_eq_getElem hj', e]
            · rw [List.getElem?_eq_none_iff.2 (by omega), List.getElem?_eq_none_iff.2 (by omega)]
          rw [this]
        · rw [e]
      · rw [if_neg (by simp [hty]), if_neg (by simp [hty]), hsm]
    · intro j
      unfold paramRec
      rcases hpos j with e | ⟨_, _, hsm, hne⟩
      · by_cases hj : j < ps.length
        · have hj' : j < q.length := by rw [hlq]; exact hj
          simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, List.getElem?_eq_getElem hj',
            Option.getD_some] at e
          rw [List.getElem?_eq_getElem hj, List.getElem?_eq_getElem hj', e]
        · rw [List.getElem?_eq_none_iff.2 (by omega), List.getElem?_eq_none_iff.2 (by omega)]
      · have hj : j < ps.length := by
          rcases Nat.lt_or_ge j ps.length with h | h
          · exact h
          · exfalso; apply hne; simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none_iff.2 h, Sem.small]
        have hj' : j < q.length := by rw [hlq]; exact hj
        simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, List.getElem?_eq_getElem hj',
          Option.getD_some] at hsm hne
        rw [List.getElem?_eq_getElem hj, List.getElem?_eq_getElem hj']
        have h1 : ∀ X, ps[j] ≠ .ty X := fun X e => hne (by rw [e]; rfl)
        have h2 : ∀ X, q[j] ≠ .ty X := fun X e => hne (by rw [hsm, e]; rfl)
        rcases e1 : ps[j] with _ | _ | _ | _ | _ | _ | _ | _ <;> rcases e2 : q[j] with _ | _ | _ | _ | _ | _ | _ | _ <;>
          first | rfl | exact absurd e1 (h1 _) | exact absurd e2 (h2 _)

include hpty in
/-- **Monotonicity of the model's records** (`Inv.mono`), from the truth records' (`truth_exists`'
second conclusion) through `canonPs_propLe`. -/
theorem mono_canonP
    (hm : ∀ ps ps', PropLe d ps ps' → ∀ c i es, es.length = i →
      ShapeLe (uShape d (recK (truthSpec K ρ d T) ps) c i es) (uShape d (recK (truthSpec K ρ d T) ps') c i es))
    (ps ps' : List Sem) (h : PropLe d ps ps') (c i : Nat) (es : List Small) (hes : es.length = i) :
    ShapeLe (uShape d (recCanonP K ρ d T ps) c i es) (uShape d (recCanonP K ρ d T ps') c i es) :=
  hm _ _ (canonPs_propLe K.dm (K.dm.paramTy d) d hpty h) c i es hes

end

end Ochr.Meaning.DataModel.Exists.Records

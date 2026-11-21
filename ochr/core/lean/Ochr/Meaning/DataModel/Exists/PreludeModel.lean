import Ochr.Meaning.DataModel.Exists.RunLemmas
import Ochr.Meaning.DataModel.Canonical.Knot
import Ochr.Meaning.Consistency
import Ochr.Prelude

/-!
# The first instance: a data model faithful to the library's declarations (kernel-checked)

`Pair (A B : Type) := Mk(fst : A, snd : B)`, `False : Prop`, `True : Prop := I`,
`And (P Q : Prop) : Prop := Intro(l : P, r : Q)`, as the checker stores them after the library
(asserted natively: `prelude_inds`). The model (`dmPre`): `Pair` and `And` by the knot of a
two-parameter declaration whose fields are its parameters (`twoK`), `False` and `True` by the empty
record (they have no fields); `paramTy` the parameters' sorts. Then, kernel-checked, at EVERY run
context whose data model is `dmPre` and whose declarations are the library's (any decisions, any
globals, any Δ and assignment):
* `recordsFaithful`, `fieldsFaithful`, `paramsFaithful`, hence `ctxFaithful`;
* `dataFaithful`: `DataFaithful` at every program state declaring the library, under any decisions;
* and each bundle at one concrete context, the checker's decisions included (`instance_*`).
WHAT RESTS ON A NATIVE CHECK: that the library's program state is what `progMeaning` produces from
the library's items needs the checker run in the kernel, which it cannot do; `prelude_inds` asserts
natively that the checker's declarations after the library are `preludeDecls`, and every theorem
here is about a state or context whose declarations are `preludeDecls`.
This is the instance test the restated faithfulness (rulings (M-a), (S)) owes before it is used:
`RecordsFaithful` had no instance at any non-empty `Γ` before them (`RecordsCE.lean`). The runs are
read through piece 3's first lemmas (`RunLemmas.lean`): a variable reads its binding, `Sort l` is
`Type_l`.
-/

namespace Ochr.Meaning.DataModel.Exists.PreludeModel

open Ochr Ochr.Meaning Ochr.Meaning.DataLib Ochr.Meaning.Canonical Ochr.Meaning.DataModel.Exists.RunLemmas

def hn (n : String) : Hint := ⟨n⟩

/-! ## The declarations, as the checker stores them -/

def pairD : IndDecl :=
  { name := "Pair", params := [(hn "A", .sort 1), (hn "B", .sort 1)], sort := 1,
    ctors := [("Mk", [("fst", .place (.var 1)), ("snd", .place (.var 0))])], nestable := [true, true] }
def falseD : IndDecl := { name := "False", sort := 0 }
def trueD : IndDecl := { name := "True", sort := 0, ctors := [("I", [])] }
def andD : IndDecl :=
  { name := "And", params := [(hn "P", .sort 0), (hn "Q", .sort 0)], sort := 0,
    ctors := [("Intro", [("l", .place (.var 1)), ("r", .place (.var 0))])], nestable := [true, true] }

def preludeDecls : List IndDecl := [pairD, falseD, trueD, andD]

/-- Two declarations agree in every field the model and the run read. -/
def sameDecl (a b : IndDecl) : Bool :=
  a.name == b.name && a.sort == b.sort && a.nestable == b.nestable && a.copy == b.copy &&
    a.abstract == b.abstract && a.unsized == b.unsized && a.declaring == b.declaring &&
    a.params.length == b.params.length &&
    (a.params.zip b.params).all (fun pq => pq.1.1.name == pq.2.1.name && pq.1.2 == pq.2.2) &&
    a.ctors.length == b.ctors.length &&
    (a.ctors.zip b.ctors).all fun cc => cc.1.1 == cc.2.1 && cc.1.2.length == cc.2.2.length &&
      (cc.1.2.zip cc.2.2).all fun ff => ff.1.1 == ff.2.1 && ff.1.2 == ff.2.2

/-- The library's items, as `resolveDecl` makes them. -/
def preludeItems : List Item :=
  Prelude.decls.filterMap fun d => match Surface.resolveProgram Prelude.decls d with
    | .ok it => some it
    | .error _ => none

-- `prelude_inds`: after the library, the checker's inductive declarations are `preludeDecls`
#guard let inds := (globalsAfter {} preludeItems).2
  preludeItems.length == 4 && inds.length == 4 && (inds.zip preludeDecls).all fun ab => sameDecl ab.1 ab.2

/-! ## The model -/

/-- A declaration with two parameters and one constructor whose fields are the parameters, in order
(`Pair`, `And`): its fields' types are its parameters' (`parTy`), both parameters nestable. -/
noncomputable def twoK (d : IndDecl) : KnotSpec where
  d := d
  N := fun _ => true
  fty := fun _ ps c i _ => if c = 0 ∧ i = 0 then .ty (parTy ps 0) else if c = 0 ∧ i = 1 then .ty (parTy ps 1)
    else .ty TyM.err
  pEntry := pEntryTy
  guarded := fun n R R' hR ps ps' hp c i es => by
    split
    · exact parTy_agree hp 0
    · split
      · exact parTy_agree hp 1
      · exact FTyAgree.refl _ _
  pEntry_agree := fun _ _ _ hp j => pEntryTy_agree hp j

/-- Which declarations the knot builds. -/
def isTwo (d : IndDecl) : Prop := d.name = "Pair" ∨ d.name = "And"

open Classical in
/-- **The library's data model.** -/
noncomputable def dmPre : DataModel where
  covers _ := True
  recOf d ps := if isTwo d then recK (twoK d) ps else fun _ => .none
  paramTy d _ _ := if d.name = "Pair" then TyM.univ 1 else if d.name = "And" then TyM.univ 0 else TyM.err

theorem recOf_two (d : IndDecl) (h : isTwo d) (ps : List Sem) : dmPre.recOf d ps = recK (twoK d) ps := by
  simp [dmPre, h]

theorem recOf_none (d : IndDecl) (h : ¬ isTwo d) (ps : List Sem) : dmPre.recOf d ps = fun _ => .none := by
  simp [dmPre, h]

theorem paramTy_pair (j : Nat) (ps : List Sem) : dmPre.paramTy pairD j ps = TyM.univ 1 := by
  simp [dmPre, pairD]

theorem paramTy_and (j : Nat) (ps : List Sem) : dmPre.paramTy andD j ps = TyM.univ 0 := by
  simp [dmPre, andD]

theorem paramTy_other (d : IndDecl) (h1 : d.name ≠ "Pair") (h2 : d.name ≠ "And") (j : Nat) (ps : List Sem) :
    dmPre.paramTy d j ps = TyM.err := by
  simp [dmPre, h1, h2]

theorem isTwo_pair : isTwo pairD := .inl rfl
theorem isTwo_and : isTwo andD := .inr rfl
theorem not_isTwo_false : ¬ isTwo falseD := by simp [isTwo, falseD]
theorem not_isTwo_true : ¬ isTwo trueD := by simp [isTwo, trueD]

/-! ## Members of the universes -/

/-- A member of `Type₀` is a level-1 code. -/
theorem mem_univ1 (R : DataRead) (v : Sem) (h : v ∈ₛ[R] TyM.univ 1) :
    ∃ (A : Type) (c : Code0 A), v = .ty (.t0 A c) ∧ c.level = some 1 := by
  obtain ⟨⟨A, c, hc⟩, he⟩ := h
  exact ⟨A, c, he.symm, hc⟩

/-- A member of `Prop` is a proposition's code. -/
theorem mem_univ0 (R : DataRead) (v : Sem) (h : v ∈ₛ[R] TyM.univ 0) : ∃ P : Prop, v = .ty (TyM.prop P) := by
  obtain ⟨⟨P⟩, he⟩ := h
  exact ⟨P, he.symm⟩

/-- A level-1 code that is a data code over the model's own carrier is a data type's code
(`uTyR`): since (M-a) a `Prop`-sorted declaration's raw code has no level. -/
theorem own_data_uTyR {B : Type} {d : IndDecl} {r : Rec} (hl : (Code0.data d r B).level = some 1)
    (hB : B = ucar d r) : d.sort ≠ 0 ∧ TyM.t0 B (.data d r B) = uTyR d r := by
  have hs : d.sort ≠ 0 := by
    intro h0
    simp [Code0.level, h0] at hl
  refine ⟨hs, ?_⟩
  have hs' : (d.sort == 0) = false := by simpa using hs
  subst hB
  simp [uTyR, hs']

/-- **The kind a level-1 code gets is `LeafOk`**: a data type's code goes to a `.data` entry, any
other level-1 code to a leaf that holds no data code over the model's carrier. -/
theorem leafOk_kind (dm : DataModel) {A : Type} (c : Code0 A) (hl : c.level = some 1 ∨ c.level = some 0)
    (d : IndDecl) (r : Rec) (cc i : Nat) (es : List Small)
    (hk : r (kindKey cc i (projIdx d cc es)) = (FTy.ty (.t0 A c)).kind) : dm.LeafOk (uShape d r cc i es) := by
  unfold uShape
  rw [hk]
  rcases hv : dataView (.t0 A c) with _ | ⟨d', r'⟩
  · have hkd : (FTy.ty (.t0 A c)).kind = .leaf A c := by simp [FTy.kind, hv]
    rw [hkd]
    show dm.LeafOk (Shape.leaf A c)
    intro d'' r'' hdc hB
    cases c with
    | data d₀ r₀ A₀ =>
      simp only [Code0.dataCode?, Option.some.injEq, Prod.mk.injEq] at hdc
      obtain ⟨rfl, rfl⟩ := hdc
      have hl1 : (Code0.data d₀ r₀ A).level = some 1 := by
        rcases hl with hl | hl
        · exact hl
        · simp only [Code0.level] at hl; split at hl <;> simp at hl
      obtain ⟨hs, he⟩ := own_data_uTyR hl1 hB
      rw [he, dataView_uTyR _ _ hs] at hv
      cases hv
    | _ => simp [Code0.dataCode?] at hdc
  · have hkd : (FTy.ty (.t0 A c)).kind = .data d' := by simp [FTy.kind, hv]
    rw [hkd]
    show dm.LeafOk (if d'.sort == 0 then _ else _)
    split <;> trivial

/-! ## Generic facts of the knot used here -/

/-- **A knot's record reads a type parameter back**: with the parameters' entries their types'
kinds (`pEntryTy`), the record keeps a level-0 type parameter's code (`paramTyOf`), by its kind and,
for a data type, its continuation. -/
theorem paramTyOf_recK (dm : DataModel) (S : KnotSpec) (hS : S.pEntry = pEntryTy) (ps : List Sem) (j : Nat)
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

/-- The decls of the library, one by one. -/
theorem mem_prelude {d : IndDecl} (h : d ∈ preludeDecls) : d = pairD ∨ d = falseD ∨ d = trueD ∨ d = andD := by
  simpa [preludeDecls] using h

/-- Typed parameters of `Pair` are members of `Type₀`; of `And`, of `Prop`. -/
theorem pair_typed {ps : List Sem} (h : ParamsTyped dmPre pairD ps) (j : Nat) (hj : j < ps.length) :
    ∃ (A : Type) (c : Code0 A), ps[j] = .ty (.t0 A c) ∧ c.level = some 1 := by
  have := h j hj
  rw [paramTy_pair] at this
  exact mem_univ1 _ _ this

theorem and_typed {ps : List Sem} (h : ParamsTyped dmPre andD ps) (j : Nat) (hj : j < ps.length) :
    ∃ P : Prop, ps[j] = .ty (TyM.prop P) := by
  have := h j hj
  rw [paramTy_and] at this
  exact mem_univ0 _ _ this

/-- A typed parameter of a two-parameter declaration, as a type of level `1` or `0`. -/
theorem two_typed {d : IndDecl} (hd : d = pairD ∨ d = andD) {ps : List Sem} (h : ParamsTyped dmPre d ps)
    (j : Nat) (hj : j < ps.length) :
    ∃ (A : Type) (c : Code0 A), ps[j] = .ty (.t0 A c) ∧ (c.level = some 1 ∨ c.level = some 0) := by
  rcases hd with rfl | rfl
  · obtain ⟨A, c, h1, h2⟩ := pair_typed h j hj
    exact ⟨A, c, h1, .inl h2⟩
  · obtain ⟨P, h1⟩ := and_typed h j hj
    exact ⟨_, _, h1, .inr rfl⟩

theorem isTwo_of {d : IndDecl} (hd : d = pairD ∨ d = andD) : isTwo d := by
  rcases hd with rfl | rfl
  · exact isTwo_pair
  · exact isTwo_and

theorem twoK_pEntry (d : IndDecl) : (twoK d).pEntry = pEntryTy := rfl

/-! ## `RecordsFaithful` -/

theorem univ1_ne_t0 {A : Type} (c : Code0 A) : TyM.univ 1 ≠ .t0 A c := fun h => by cases h
theorem univ0_ne_t0 {A : Type} (c : Code0 A) : TyM.univ 0 ≠ .t0 A c := fun h => by cases h

/-- **`RecordsFaithful` at the library** (every run context with `dmPre` and the library's
declarations). -/
theorem recordsFaithful (K : RunCtx) (hdm : K.dm = dmPre) (hΓ : K.Γ = preludeDecls) : RecordsFaithful K := by
  cases K with
  | mk dm Γ C D Δ Λ cur =>
  dsimp only at hdm hΓ
  subst hdm hΓ
  refine ⟨?types, ?values, ?smallOnly, ?leafOk⟩
  case types =>
    intro d hd ps j A c hlen _ _ hj
    rcases mem_prelude hd with rfl | rfl | rfl | rfl
    · rw [recOf_two _ isTwo_pair]; exact paramTyOf_recK _ _ rfl ps j c hj
    · simp [falseD] at hlen; subst hlen; simp at hj
    · simp [trueD] at hlen; subst hlen; simp at hj
    · rw [recOf_two _ isTwo_and]; exact paramTyOf_recK _ _ rfl ps j c hj
  case values =>
    intro d hd ps j v A c _ _ hT hv
    rcases mem_prelude hd with rfl | rfl | rfl | rfl
    · exact absurd hT (by rw [paramTy_pair]; exact univ1_ne_t0 c)
    · rw [paramTy_other _ (by decide) (by decide)] at hT
      cases hT; exact absurd hv (DataModel.err_mem_false _ _)
    · rw [paramTy_other _ (by decide) (by decide)] at hT
      cases hT; exact absurd hv (DataModel.err_mem_false _ _)
    · exact absurd hT (by rw [paramTy_and]; exact univ0_ne_t0 c)
  case smallOnly =>
    intro d hd ps ps' _ hl hps
    -- at the library no parameter has a level-0 type, so the lists are equal
    have heq : ∀ (hd2 : d = pairD ∨ d = andD), ps' = ps := by
      intro hd2
      apply List.ext_getElem? 
      intro j
      rcases h1 : ps[j]? with _ | v
      · rw [List.getElem?_eq_none_iff] at h1 ⊢; omega
      · rcases h2 : ps'[j]? with _ | v'
        · rw [List.getElem?_eq_none_iff] at h2
          obtain ⟨hj, -⟩ := List.getElem?_eq_some_iff.1 h1; omega
        · rcases hps j v v' h1 h2 with h | ⟨⟨A, c, hT, -⟩, -⟩
          · rw [h]
          · rcases hd2 with rfl | rfl
            · exact absurd hT (by rw [paramTy_pair]; exact univ1_ne_t0 c)
            · exact absurd hT (by rw [paramTy_and]; exact univ0_ne_t0 c)
    rcases mem_prelude hd with rfl | rfl | rfl | rfl
    · rw [heq (.inl rfl)]
    · rw [recOf_none _ not_isTwo_false, recOf_none _ not_isTwo_false]
    · rw [recOf_none _ not_isTwo_true, recOf_none _ not_isTwo_true]
    · rw [heq (.inr rfl)]
  case leafOk =>
    intro d hd ps hlen hpt c i e hc hi he
    rcases mem_prelude hd with hd | hd | hd | hd
    rotate_left
    · subst hd; simp [falseD] at hc
    · subst hd
      rw [recOf_none _ not_isTwo_true]
      show dmPre.LeafOk (uShape trueD (fun _ => .none) c i e)
      intro d' r' hdc; simp [Code0.dataCode?] at hdc
    all_goals
      have hd2 : d = pairD ∨ d = andD := by first | exact .inl hd | exact .inr hd
      rw [recOf_two _ (isTwo_of hd2)]
      have hc0 : c = 0 := by rcases hd2 with rfl | rfl <;> simp [pairD, andD] at hc <;> omega
      have hi2 : i < 2 := by rcases hd2 with rfl | rfl <;> simp [DataLib.arity, pairD, andD, hc0] at hi <;> omega
      have hpl : ps.length = 2 := by rcases hd2 with rfl | rfl <;> simpa [pairD, andD] using hlen
      subst hc0
      obtain ⟨A, cd, hpA, hlv⟩ := two_typed hd2 hpt i (by omega)
      apply leafOk_kind dmPre cd hlv
      have hpe : (projIdx d 0 e).length = i := by rw [projIdx_len, he]
      rw [recK_kind _ ps 0 i _ hpe]
      have hpar : parTy ps i = .t0 A cd := by simp [parTy, List.getElem?_eq_getElem (show i < ps.length by omega), hpA, Sem.asTy]
      show (if 0 = 0 ∧ i = 0 then FTy.ty (parTy ps 0) else if 0 = 0 ∧ i = 1 then FTy.ty (parTy ps 1) else FTy.ty TyM.err).kind = _
      rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
      · simp [hpar]
      · simp [hpar]

/-! ## `FieldsFaithful` and `ParamsFaithful` -/

/-- The field terms of a two-parameter declaration: field `i` of constructor `0` reads parameter `i`. -/
theorem fieldTerm_two {d : IndDecl} (hd : d = pairD ∨ d = andD) {c i : Nat} {FT : Term}
    (h : fieldTerm d c i = some FT) : c = 0 ∧ i < 2 ∧ FT = .place (.var (1 - i)) := by
  rcases hd with rfl | rfl <;>
  · rcases c with _ | c
    · rcases i with _ | _ | i <;> simp [fieldTerm, pairD, andD] at h <;> simp [h]
    · simp [fieldTerm, pairD, andD] at h

/-- The field types of a two-parameter declaration at the knot's record: the parameters. -/
theorem fieldTy_two {d : IndDecl} (hd : d = pairD ∨ d = andD) {ps : List Sem} (hpt : ParamsTyped dmPre d ps)
    (i : Nat) (hi : i < 2) (hpl : ps.length = 2) (e : List Sem) (he : e.length = i) :
    dmPre.fieldTy d ps 0 i e = ps[i].asTy := by
  obtain ⟨A, cd, hpA, -⟩ := two_typed hd hpt i (by omega)
  have hpar : parTy ps i = .t0 A cd := by
    simp [parTy, List.getElem?_eq_getElem (show i < ps.length by omega), hpA, Sem.asTy]
  unfold DataModel.fieldTy DataModel.fieldTyR
  rw [recOf_two _ (isTwo_of hd), shapeTy_eq_shapeTyP]
  have hl : (e.map Sem.small).length = i := by simp [he]
  have hfty : ∀ es, (twoK d).fty (recK (twoK d)) ps 0 i es = .ty (parTy ps i) := by
    intro es
    show (if 0 = 0 ∧ i = 0 then FTy.ty (parTy ps 0) else if 0 = 0 ∧ i = 1 then FTy.ty (parTy ps 1) else FTy.ty TyM.err) = _
    rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl <;> simp
  rw [show dmPre.sig.shape d (recK (twoK d) ps) 0 i (e.map Sem.small) = uShape (twoK d).d (recK (twoK d) ps) 0 i (e.map Sem.small) from rfl]
  rw [recK_shape (twoK d) ps 0 i _ hl (by rw [hfty]; exact ⟨A, cd, hpar⟩), hfty]
  simp [FTy.mean, hpar, hpA, Sem.asTy]

/-- **`FieldsFaithful` at the library**, at every run context with `dmPre` and its declarations:
whatever the decisions, a field's type, where its run is defined, is the model's. -/
theorem fieldsFaithful (K : RunCtx) (hdm : K.dm = dmPre) (hΓ : K.Γ = preludeDecls) (ρ : Assignment) :
    FieldsFaithful K ρ := by
  cases K with
  | mk dm Γ C D Δ Λ cur =>
  dsimp only at hdm hΓ
  subst hdm hΓ
  intro d hd ps c i e FT hlen hpt _ he hFT r s' hr
  rcases mem_prelude hd with hd | hd | hd | hd
  rotate_left
  · subst hd; simp [fieldTerm, falseD] at hFT
  · subst hd; rcases c with _ | c <;> simp [fieldTerm, trueD] at hFT
  all_goals
    have hd2 : d = pairD ∨ d = andD := by first | exact .inl hd | exact .inr hd
    have hpl : ps.length = 2 := by rcases hd2 with rfl | rfl <;> simpa [pairD, andD] using hlen
    obtain ⟨rfl, hi, rfl⟩ := fieldTerm_two hd2 hFT
    have hvar : (1 - i) = ps.length - 1 - i := by omega
    rw [hvar] at hr
    have harity : e.length ≤ DataLib.arity d 0 := by
      rcases hd2 with rfl | rfl <;> simp [DataLib.arity, pairD, andD] <;> omega
    have h1 := runT_teleFrame_param _ ρ noFuture false _ dmPre D d ps 0 e harity i (by omega) rfl hr
    rw [h1, fieldTy_two hd2 hpt i hi hpl e he]

/-- **`ParamsFaithful` at the library**: a parameter's declared sort runs to its universe. -/
theorem paramsFaithful (K : RunCtx) (hdm : K.dm = dmPre) (hΓ : K.Γ = preludeDecls) (ρ : Assignment) :
    ParamsFaithful K ρ := by
  cases K with
  | mk dm Γ C D Δ Λ cur =>
  dsimp only at hdm hΓ
  subst hdm hΓ
  intro d hd ps j hn PT _ _ hPT r s' hr
  rcases mem_prelude hd with rfl | rfl | rfl | rfl
  · have hP : PT = .sort 1 := by
      rcases j with _ | _ | j <;> simp [pairD] at hPT <;> exact hPT.2.symm
    subst hP
    unfold run at hr
    rw [runT_sort] at hr
    cases hr
    rw [paramTy_pair]; rfl
  · simp [falseD] at hPT
  · simp [trueD] at hPT
  · have hP : PT = .sort 0 := by
      rcases j with _ | _ | j <;> simp [andD] at hPT <;> exact hPT.2.symm
    subst hP
    unfold run at hr
    rw [runT_sort] at hr
    cases hr
    rw [paramTy_and]; rfl

/-! ## The three bundles, and their instances -/

/-- **`CtxFaithful` at the library.** -/
theorem ctxFaithful (K : RunCtx) (hdm : K.dm = dmPre) (hΓ : K.Γ = preludeDecls) : CtxFaithful K :=
  fun Δ ρ => ⟨fieldsFaithful { K with Δ := Δ } hdm hΓ ρ, paramsFaithful { K with Δ := Δ } hdm hΓ ρ,
    recordsFaithful K hdm hΓ⟩

/-- **`DataFaithful` at every program state declaring the library**, under any decisions. -/
theorem dataFaithful (D : MState → Decisions) (P : ProgState) (hP : P.inds = preludeDecls) :
    Assembly.DataFaithful dmPre D P :=
  fun st hst _ => ctxFaithful (P.ctx dmPre D st) rfl (by show st.inds = _; rw [hst, hP])

/-- The model covers every declaration. -/
theorem covered (P : ProgState) : P.Covered dmPre := fun _ _ => trivial

/-- The program state after the library: its declarations, no global. -/
def preludeState : ProgState := { inds := preludeDecls }

/-- A concrete run context: the library's state, under the checker's decisions (the chain's). -/
noncomputable def instK (fuel : Nat) : RunCtx :=
  preludeState.ctx dmPre (chainDecisions fuel) { inds := preludeDecls }

theorem instance_records (fuel : Nat) : RecordsFaithful (instK fuel) := recordsFaithful _ rfl rfl
theorem instance_fields (fuel : Nat) (ρ : Assignment) : FieldsFaithful (instK fuel) ρ := fieldsFaithful _ rfl rfl ρ
theorem instance_params (fuel : Nat) (ρ : Assignment) : ParamsFaithful (instK fuel) ρ := paramsFaithful _ rfl rfl ρ
theorem instance_ctx (fuel : Nat) : CtxFaithful (instK fuel) := ctxFaithful _ rfl rfl

/-- **The existence statement's conclusion at the library's state**: a data model covering it and
faithful to it under the checker's decisions. (That this state is the program meaning of the
library's items needs the checker run in the kernel, which it cannot do; `prelude_inds` asserts
natively that the checker's declarations after the library are `preludeDecls`.) -/
theorem instance_data (fuel : Nat) :
    ∃ dm : DataModel, preludeState.Covered dm ∧ Assembly.DataFaithful dm (chainDecisions fuel) preludeState :=
  ⟨dmPre, covered _, dataFaithful _ _ rfl⟩

end Ochr.Meaning.DataModel.Exists.PreludeModel

import Ochr.Meaning.DataModel.Exists.Proto.Knot

/-!
# Prototype: the hard declarations through the knot

Each declaration as the checker records it (parameters `var 0 …` from the last; fields after),
its nestable parameters, and its field types as functions of its own record function, read as the
reference run reads the field-type terms: a parameter is its value; `M(ā)` is `M`'s code at `M`'s
canonical record at the arguments' meanings (`uTyR M (recK M …)`); the declaration's own
occurrences go through the record function given. Guardedness is proved for each: the positivity
condition, semantically. The knot then gives the canonical record (`recK`), and `recK_shape` its
faithfulness at every field.

Covered: `List`, `Box`, `Duo` (the formers nested in); `Rose` (nested), `DD` (`DD(DD(A))`: a self
occurrence whose argument is the declaration), `RN` (`List(RN(Duo(A, A)))`: non-uniform nesting),
`BB` (`Box(BB(Box(A)))`), `NN` (two levels), `RP` (through two formers), `HN` (a large parameter
shifted along the unfolding, with self-nesting at the other parameter).
-/

namespace Ochr.Meaning.DataModel.Exists.Proto

open Ochr Ochr.Meaning Ochr.Meaning.DataLib

def hn (n : String) : Hint := ⟨n⟩

/-- Parameter `j`'s meaning. -/
def parSem (ps : List Sem) (j : Nat) : Sem := ps.getD j .err

theorem semAgree_parSem {N : Nat → Bool} {n : Nat} {ps ps' : List Sem} (hp : ParAgree N n ps ps') (j : Nat)
    (hN : N j = true) : SemAgree n (parSem ps j) (parSem ps' j) := by
  unfold parSem
  rcases h1 : ps[j]? with _ | v
  · have h2 : ps'[j]? = none := by
      rw [List.getElem?_eq_none_iff] at h1 ⊢; rw [← hp.1]; exact h1
    simp [List.getD_eq_getElem?_getD, h1, h2]; exact .inl rfl
  · rcases h2 : ps'[j]? with _ | v'
    · have : ps[j]? = none := by
        rw [List.getElem?_eq_none_iff] at h2 ⊢; rw [hp.1]; exact h2
      rw [this] at h1; cases h1
    · have h := hp.2 j v v' h1 h2
      rw [if_pos hN] at h
      simp [List.getD_eq_getElem?_getD, h1, h2]; exact h

theorem eq_parSem {N : Nat → Bool} {n : Nat} {ps ps' : List Sem} (hp : ParAgree N n ps ps') (j : Nat)
    (hN : N j = false) : parSem ps j = parSem ps' j := by
  unfold parSem
  rcases h1 : ps[j]? with _ | v
  · have h2 : ps'[j]? = none := by
      rw [List.getElem?_eq_none_iff] at h1 ⊢; rw [← hp.1]; exact h1
    simp [List.getD_eq_getElem?_getD, h1, h2]
  · rcases h2 : ps'[j]? with _ | v'
    · have : ps[j]? = none := by
        rw [List.getElem?_eq_none_iff] at h2 ⊢; rw [hp.1]; exact h2
      rw [this] at h1; cases h1
    · have h := hp.2 j v v' h1 h2
      rw [if_neg (by simp [hN])] at h
      simp [List.getD_eq_getElem?_getD, h1, h2, h]

/-- One- and two-element parameter lists agreeing pointwise agree, every parameter nestable. -/
theorem parAgree_single {n : Nat} {x x' : Sem} (h : SemAgree n x x') :
    ParAgree (fun _ => true) n [x] [x'] := by
  refine ⟨rfl, fun j v v' hv hv' => ?_⟩
  simp only [if_true]
  cases j with
  | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at hv hv'; subst hv hv'; exact h
  | succ j => simp at hv

theorem parAgree_pair {n : Nat} {x x' y y' : Sem} (hx : SemAgree n x x') (hy : SemAgree n y y') :
    ParAgree (fun _ => true) n [x, y] [x', y'] := by
  refine ⟨rfl, fun j v v' hv hv' => ?_⟩
  simp only [if_true]
  match j, hv, hv' with
  | 0, hv, hv' => simp only [List.getElem?_cons_zero, Option.some.injEq] at hv hv'; subst hv hv'; exact hx
  | 1, hv, hv' => simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hv hv'; subst hv hv'; exact hy
  | j + 2, hv, _ => simp at hv

/-- A data type at records agreeing below `n` agrees as a meaning. -/
theorem semAgree_data {n : Nat} (d : IndDecl) (hd : d.sort ≠ 0) {r r' : Rec} (h : RecAgree n r r') :
    SemAgree n (.ty (uTyR d r)) (.ty (uTyR d r')) := .inr ⟨d, r, r', hd, rfl, rfl, h⟩

/-! ## `List`, `Box`, `Duo` -/

def listD : IndDecl :=
  { name := "List", params := [(hn "A", .sort 1)],
    ctors := [("Nil", []), ("Cons", [("h", .place (.var 0)), ("t", .tind "List" [.place (.var 0)])])] }

noncomputable def listFty (R : List Sem → Rec) (ps : List Sem) (c i : Nat) (_ : List Small) : FTy :=
  if c = 1 ∧ i = 0 then .ty (parTy ps 0) else if c = 1 ∧ i = 1 then .data listD (R ps) else .ty TyM.err

noncomputable def listK : KnotSpec where
  d := listD
  N := fun _ => true
  fty := listFty
  pEntry := pEntryTy
  guarded := fun n R R' hR ps ps' hp c i es => by
    unfold listFty
    split
    · exact parTy_agree hp 0
    · split
      · exact data_agree _ (hR ps ps' hp)
      · exact FTyAgree.refl _ _
  pEntry_agree := fun _ _ _ hp j => pEntryTy_agree hp j

def boxD : IndDecl :=
  { name := "Box", params := [(hn "A", .sort 1)], ctors := [("MkBox", [("x", .place (.var 0))])] }

noncomputable def boxK : KnotSpec where
  d := boxD
  N := fun _ => true
  fty := fun _ ps c i _ => if c = 0 ∧ i = 0 then .ty (parTy ps 0) else .ty TyM.err
  pEntry := pEntryTy
  guarded := fun n R R' hR ps ps' hp c i es => by
    split
    · exact parTy_agree hp 0
    · exact FTyAgree.refl _ _
  pEntry_agree := fun _ _ _ hp j => pEntryTy_agree hp j

def duoD : IndDecl :=
  { name := "Duo", params := [(hn "A", .sort 1), (hn "B", .sort 1)],
    ctors := [("MkDuo", [("fst", .place (.var 1)), ("snd", .place (.var 0))])] }

noncomputable def duoK : KnotSpec where
  d := duoD
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

theorem sort_ne (d : IndDecl) (h : d.sort = 1) : d.sort ≠ 0 := by rw [h]; decide

/-! ## `Rose`: nested in `List` -/

def roseD : IndDecl :=
  { name := "Rose", params := [(hn "A", .sort 1)],
    ctors := [("Node", [("a", .place (.var 0)), ("kids", .tind "List" [.tind "Rose" [.place (.var 0)]])])] }

noncomputable def roseK : KnotSpec where
  d := roseD
  N := fun _ => true
  fty := fun R ps c i _ => if c = 0 ∧ i = 0 then .ty (parTy ps 0)
    else if c = 0 ∧ i = 1 then .data listD (recK listK [.ty (uTyR roseD (R ps))]) else .ty TyM.err
  pEntry := pEntryTy
  guarded := fun n R R' hR ps ps' hp c i es => by
    split
    · exact parTy_agree hp 0
    · split
      · exact data_agree _ (recK_agree listK n _ _
          (parAgree_single (semAgree_data roseD (sort_ne _ rfl) (hR ps ps' hp))))
      · exact FTyAgree.refl _ _
  pEntry_agree := fun _ _ _ hp j => pEntryTy_agree hp j

/-! ## `DD`: a self occurrence whose argument is the declaration, `DD(DD(A))` -/

def ddD : IndDecl :=
  { name := "DD", params := [(hn "A", .sort 1)],
    ctors := [("DLeaf", []), ("DNode", [("x", .tind "DD" [.tind "DD" [.place (.var 0)]])])] }

noncomputable def ddK : KnotSpec where
  d := ddD
  N := fun _ => true
  fty := fun R ps c i _ => if c = 1 ∧ i = 0 then .data ddD (R [.ty (uTyR ddD (R ps))]) else .ty TyM.err
  pEntry := pEntryTy
  guarded := fun n R R' hR ps ps' hp c i es => by
    split
    · exact data_agree _ (hR _ _ (parAgree_single (semAgree_data ddD (sort_ne _ rfl) (hR ps ps' hp))))
    · exact FTyAgree.refl _ _
  pEntry_agree := fun _ _ _ hp j => pEntryTy_agree hp j

/-! ## `RN`: non-uniform nesting, `List(RN(Duo(A, A)))` -/

def rnD : IndDecl :=
  { name := "RN", params := [(hn "A", .sort 1)],
    ctors := [("NodeN", [("a", .place (.var 0)),
      ("kids", .tind "List" [.tind "RN" [.tind "Duo" [.place (.var 0), .place (.var 0)]]])])] }

/-- `Duo(A, A)`'s meaning. -/
noncomputable def duoAA (ps : List Sem) : Sem := .ty (uTyR duoD (recK duoK [parSem ps 0, parSem ps 0]))

noncomputable def rnK : KnotSpec where
  d := rnD
  N := fun _ => true
  fty := fun R ps c i _ => if c = 0 ∧ i = 0 then .ty (parTy ps 0)
    else if c = 0 ∧ i = 1 then .data listD (recK listK [.ty (uTyR rnD (R [duoAA ps]))]) else .ty TyM.err
  pEntry := pEntryTy
  guarded := fun n R R' hR ps ps' hp c i es => by
    split
    · exact parTy_agree hp 0
    · split
      · have hA := semAgree_parSem hp 0 rfl
        have hduo : SemAgree n (duoAA ps) (duoAA ps') :=
          semAgree_data duoD (sort_ne _ rfl) (recK_agree duoK n _ _ (parAgree_pair hA hA))
        exact data_agree _ (recK_agree listK n _ _
          (parAgree_single (semAgree_data rnD (sort_ne _ rfl) (hR _ _ (parAgree_single hduo)))))
      · exact FTyAgree.refl _ _
  pEntry_agree := fun _ _ _ hp j => pEntryTy_agree hp j

/-! ## `BB`, `NN`, `RP`: nesting through `Box`, two levels of `List`, `List` and `Duo` -/

def bbD : IndDecl :=
  { name := "BB", params := [(hn "A", .sort 1)],
    ctors := [("BLeaf", [("a", .place (.var 0))]),
      ("BNode", [("b", .tind "Box" [.tind "BB" [.tind "Box" [.place (.var 0)]]])])] }

noncomputable def bbK : KnotSpec where
  d := bbD
  N := fun _ => true
  fty := fun R ps c i _ => if c = 0 ∧ i = 0 then .ty (parTy ps 0)
    else if c = 1 ∧ i = 0 then
      .data boxD (recK boxK [.ty (uTyR bbD (R [.ty (uTyR boxD (recK boxK [parSem ps 0]))]))])
    else .ty TyM.err
  pEntry := pEntryTy
  guarded := fun n R R' hR ps ps' hp c i es => by
    split
    · exact parTy_agree hp 0
    · split
      · have hbox := semAgree_data boxD (sort_ne _ rfl)
          (recK_agree boxK n _ _ (parAgree_single (semAgree_parSem hp 0 rfl)))
        exact data_agree _ (recK_agree boxK n _ _
          (parAgree_single (semAgree_data bbD (sort_ne _ rfl) (hR _ _ (parAgree_single hbox)))))
      · exact FTyAgree.refl _ _
  pEntry_agree := fun _ _ _ hp j => pEntryTy_agree hp j

def nnD : IndDecl :=
  { name := "NN", params := [(hn "A", .sort 1)],
    ctors := [("NNode", [("kids", .tind "List" [.tind "List" [.tind "NN" [.place (.var 0)]]])])] }

noncomputable def nnK : KnotSpec where
  d := nnD
  N := fun _ => true
  fty := fun R ps c i _ => if c = 0 ∧ i = 0 then
      .data listD (recK listK [.ty (uTyR listD (recK listK [.ty (uTyR nnD (R ps))]))])
    else .ty TyM.err
  pEntry := pEntryTy
  guarded := fun n R R' hR ps ps' hp c i es => by
    split
    · have h1 := semAgree_data nnD (sort_ne _ rfl) (hR ps ps' hp)
      have h2 := semAgree_data listD (sort_ne _ rfl) (recK_agree listK n _ _ (parAgree_single h1))
      exact data_agree _ (recK_agree listK n _ _ (parAgree_single h2))
    · exact FTyAgree.refl _ _
  pEntry_agree := fun _ _ _ hp j => pEntryTy_agree hp j

def rpD : IndDecl :=
  { name := "RP", params := [(hn "A", .sort 1)],
    ctors := [("NodeP", [("a", .place (.var 0)),
      ("kids", .tind "List" [.tind "Duo" [.tind "RP" [.place (.var 0)], .nat]])])] }

noncomputable def rpK : KnotSpec where
  d := rpD
  N := fun _ => true
  fty := fun R ps c i _ => if c = 0 ∧ i = 0 then .ty (parTy ps 0)
    else if c = 0 ∧ i = 1 then
      .data listD (recK listK [.ty (uTyR duoD (recK duoK [.ty (uTyR rpD (R ps)), .ty TyM.nat]))])
    else .ty TyM.err
  pEntry := pEntryTy
  guarded := fun n R R' hR ps ps' hp c i es => by
    split
    · exact parTy_agree hp 0
    · split
      · have h1 := semAgree_data rpD (sort_ne _ rfl) (hR ps ps' hp)
        have h2 := semAgree_data duoD (sort_ne _ rfl) (recK_agree duoK n _ _ (parAgree_pair h1 (.inl (rfl : Sem.ty TyM.nat = _))))
        exact data_agree _ (recK_agree listK n _ _ (parAgree_single h2))
      · exact FTyAgree.refl _ _
  pEntry_agree := fun _ _ _ hp j => pEntryTy_agree hp j

/-! ## `HN`: a large parameter shifted along the unfolding, and self-nesting at `A`

`HN (f : Π(x : Nat). Type) (A : Type) := HB(a : A) | HS(y : App0(f), r : HN(λx. f(S(x)), HN(f, A)))`.
How the run applies a function meaning to a number (`app`) and what `λx. f(S(x))` means (`shiftF`)
are left abstract: the knot does not read them. -/

def hnD : IndDecl :=
  { name := "HN", params := [(hn "f", .pi [hn "x"] [.nat] (.sort 1)), (hn "A", .sort 1)],
    ctors := [("HB", [("a", .place (.var 0))]),
      ("HS", [("y", .call (.const "App0") [.place (.var 1)] false),
        ("r", .tind "HN" [.fix ⟨"lam"⟩ [hn "x"] [.nat] (.sort 1) none (.call (.place (.var 2)) [.succ (.place (.var 0))] false),
          .tind "HN" [.place (.var 1), .place (.var 0)]])])] }

section
variable (app : Sem → Nat → TyM) (shiftF : Sem → Sem)

theorem parAgree_hn {n : Nat} {x y y' : Sem} (hy : SemAgree n y y') :
    ParAgree (fun j => j == 1) n [x, y] [x, y'] := by
  refine ⟨rfl, fun j v v' hv hv' => ?_⟩
  match j, hv, hv' with
  | 0, hv, hv' => simp only [List.getElem?_cons_zero, Option.some.injEq] at hv hv'; subst hv hv'; simp
  | 1, hv, hv' => simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hv hv'; subst hv hv'; simpa using hy
  | j + 2, hv, _ => simp at hv

noncomputable def hnK : KnotSpec where
  d := hnD
  N := fun j => j == 1
  fty := fun R ps c i _ => if c = 0 ∧ i = 0 then .ty (parTy ps 1)
    else if c = 1 ∧ i = 0 then .ty (app (parSem ps 0) 0)
    else if c = 1 ∧ i = 1 then .data hnD (R [shiftF (parSem ps 0), .ty (uTyR hnD (R ps))])
    else .ty TyM.err
  pEntry := pEntryTy
  guarded := fun n R R' hR ps ps' hp c i es => by
    have hf : parSem ps 0 = parSem ps' 0 := eq_parSem hp 0 rfl
    split
    · exact parTy_agree hp 1
    · split
      · rw [hf]; exact FTyAgree.refl _ _
      · split
        · rw [hf]
          exact data_agree _ (hR _ _ (parAgree_hn (semAgree_data hnD (sort_ne _ rfl) (hR ps ps' hp))))
        · exact FTyAgree.refl _ _
  pEntry_agree := fun _ _ _ hp j => pEntryTy_agree hp j

end

end Ochr.Meaning.DataModel.Exists.Proto

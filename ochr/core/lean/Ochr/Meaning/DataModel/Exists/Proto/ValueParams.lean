import Ochr.Meaning.DataModel.Exists.Proto.Hard

/-!
# Prototype: a value parameter whose argument is a value of the declaration being defined

`G1 (A : Type) (a : A) := MkG1(x : A, e : Eq(A, x, a))` and `T1 := Leaf1 | Node1(t : T1, g : G1(T1, t))`
(D107's question 2): `T1` sits at `G1`'s type parameter `A`, which types the value parameter `a`,
whose argument is the earlier field `t`, a `T1` value. A canonical record reads a value parameter
ONLY through its small reading (here: the equation `x = a`, keyed by small readings, and `a` kept
small at its key), so (i) the knot of `T1` stays guarded: `t`'s small reading holds none of `T1`'s
records; (ii) the record at the actual `t` is the record at the tree rebuilt from `t`'s small
reading (`recK_small`, the generic form of `RecordsFaithful.smallOnly`), so the field type the run
computes from `t` is the one the record keys by `t.small` (`t1_g_faithful`).

(Today's checker rejects this `G1`: an equation's type counts as passing `A` to a type function, so
`A` is not nestable. `G2 (A) (a : A) := MkG2(x : A)` is accepted (`Positivity.MustStay`); it is the
same construction without the equation.)
-/

namespace Ochr.Meaning.DataModel.Exists.Proto

open Ochr Ochr.Meaning Ochr.Meaning.DataLib Ochr.Meaning.Canonical

/-- Parameter lists that differ only at value parameters `V`, there with the same small reading
and neither a type. -/
def SmallRel (V : Nat → Bool) (ps ps' : List Sem) : Prop :=
  ps.length = ps'.length ∧ ∀ j v v', ps[j]? = some v → ps'[j]? = some v' →
    v = v' ∨ (V j = true ∧ v.small = v'.small ∧ (∀ T, v ≠ .ty T) ∧ (∀ T, v' ≠ .ty T))

theorem paramRec_small {V : Nat → Bool} {ps ps' : List Sem} (h : SmallRel V ps ps') (j : Nat) :
    paramRec ps j = paramRec ps' j := by
  unfold paramRec
  rcases h1 : ps[j]? with _ | v
  · have : ps'[j]? = none := by
      rw [List.getElem?_eq_none_iff] at h1 ⊢; rw [← h.1]; exact h1
    rw [this]
  · rcases h2 : ps'[j]? with _ | v'
    · have : ps[j]? = none := by
        rw [List.getElem?_eq_none_iff] at h2 ⊢; rw [h.1]; exact h2
      rw [this] at h1; cases h1
    · rcases h.2 j v v' h1 h2 with rfl | ⟨-, -, hv, hv'⟩
      · rfl
      · cases v with
        | ty T => exact absurd rfl (hv T)
        | _ => cases v' with
          | ty T => exact absurd rfl (hv' T)
          | _ => rfl

/-- **A record reads its value parameters only through their small readings**, when its field
types and entries do. -/
theorem recK_small (S : KnotSpec) (V : Nat → Bool)
    (hf : ∀ R ps ps', SmallRel V ps ps' → ∀ c i es, S.fty R ps c i es = S.fty R ps' c i es)
    (he : ∀ ps ps', SmallRel V ps ps' → ∀ j, S.pEntry ps j = S.pEntry ps' j)
    {ps ps' : List Sem} (h : SmallRel V ps ps') : recK S ps = recK S ps' := by
  funext p
  show approx S (p.length + 1) ps p = approx S (p.length + 1) ps' p
  show stepRec S (approx S p.length) ps p = stepRec S (approx S p.length) ps' p
  have h1 := hf (approx S p.length) ps ps' h
  have h2 := he ps ps' h
  have h3 := paramRec_small h
  cases p with
  | nil => rfl
  | cons s q => simp only [stepRec, h1, h2, h3]

def g1D : IndDecl :=
  { name := "G1", params := [(hn "A", .sort 1), (hn "a", .place (.var 0))],
    ctors := [("MkG1", [("x", .place (.var 1)), ("e", .eq (.place (.var 1)) (.place (.var 3)) (.place (.var 0)))])] }

/-- `G1`'s field types: `x : A`, and the equation `x = a` keyed by small readings. -/
noncomputable def g1K : KnotSpec where
  d := g1D
  N := fun j => j == 0
  fty := fun _ ps c i es => if c = 0 ∧ i = 0 then .ty (parTy ps 0)
    else if c = 0 ∧ i = 1 then .ty (TyM.prop (es.getD 0 .other = (parSem ps 1).small)) else .ty TyM.err
  pEntry := fun ps j => if j = 1 then .small (parSem ps 1).small else pEntryTy ps j
  guarded := fun n R R' _ ps ps' hp c i es => by
    have ha : parSem ps 1 = parSem ps' 1 := eq_parSem hp 1 rfl
    split
    · exact parTy_agree hp 0
    · rw [ha]; exact FTyAgree.refl _ _
  pEntry_agree := fun n ps ps' hp j => by
    rw [eq_parSem hp 1 rfl, pEntryTy_agree hp j]

theorem smallRel_get {V : Nat → Bool} {ps ps' : List Sem} (h : SmallRel V ps ps') (j : Nat) (hj : V j = false) :
    ps[j]? = ps'[j]? := by
  rcases h1 : ps[j]? with _ | v
  · rw [eq_comm, List.getElem?_eq_none_iff, ← h.1]; exact List.getElem?_eq_none_iff.1 h1
  · rcases h2 : ps'[j]? with _ | v'
    · rw [List.getElem?_eq_none_iff] at h2; have := h.1; rw [List.getElem?_eq_none_iff.2 (by omega)] at h1; cases h1
    · rcases h.2 j v v' h1 h2 with rfl | ⟨hv, -⟩
      · rfl
      · rw [hj] at hv; cases hv

theorem smallRel_small {V : Nat → Bool} {ps ps' : List Sem} (h : SmallRel V ps ps') (j : Nat) :
    (parSem ps j).small = (parSem ps' j).small := by
  unfold parSem
  rcases h1 : ps[j]? with _ | v
  · have h2 : ps'[j]? = none := by
      rw [List.getElem?_eq_none_iff] at h1 ⊢; rw [← h.1]; exact h1
    simp [List.getD_eq_getElem?_getD, h1, h2]
  · rcases h2 : ps'[j]? with _ | v'
    · rw [List.getElem?_eq_none_iff] at h2; have := h.1; rw [List.getElem?_eq_none_iff.2 (by omega)] at h1; cases h1
    · simp only [List.getD_eq_getElem?_getD, h1, h2, Option.getD_some]
      rcases h.2 j v v' h1 h2 with rfl | ⟨-, hs, -⟩
      · rfl
      · exact hs

theorem parTy_small {V : Nat → Bool} {ps ps' : List Sem} (h : SmallRel V ps ps') (j : Nat) (hj : V j = false) :
    parTy ps j = parTy ps' j := by
  unfold parTy; rw [smallRel_get h j hj]

theorem ofSmall_not_ty : ∀ (sv : Small) (T : TyM), ofSmall sv ≠ .ty T
  | .el _ _, _ => by simp [ofSmall]
  | .proof, _ => by simp [ofSmall]
  | .node _ _, _ => by simp [ofSmall]
  | .other, _ => by simp [ofSmall]

theorem g1K_small_fty (R : List Sem → Rec) (ps ps' : List Sem) (h : SmallRel (fun j => j == 1) ps ps')
    (c i : Nat) (es : List Small) : g1K.fty R ps c i es = g1K.fty R ps' c i es := by
  show (if c = 0 ∧ i = 0 then _ else _) = (if c = 0 ∧ i = 0 then _ else _)
  rw [parTy_small h 0 rfl, smallRel_small h 1]

theorem g1K_small_entry (ps ps' : List Sem) (h : SmallRel (fun j => j == 1) ps ps') (j : Nat) :
    g1K.pEntry ps j = g1K.pEntry ps' j := by
  show (if j = 1 then _ else _) = (if j = 1 then _ else _)
  by_cases hj : j = 1
  · rw [if_pos hj, if_pos hj, smallRel_small h 1]
  · rw [if_neg hj, if_neg hj]
    unfold pEntryTy
    rw [parTy_small h j (by simp [hj])]

/-! ## `T1 := Leaf1 | Node1(t : T1, g : G1(T1, t))` -/

def t1D : IndDecl :=
  { name := "T1", ctors := [("Leaf1", []), ("Node1", [("t", .tind "T1" []), ("g", .tind "G1" [.tind "T1" [], .place (.var 1)])])] }

theorem parAgree_g1 {n : Nat} {x x' y : Sem} (hx : SemAgree n x x') :
    ParAgree (fun j => j == 0) n [x, y] [x', y] := by
  refine ⟨rfl, fun j v v' hv hv' => ?_⟩
  match j, hv, hv' with
  | 0, hv, hv' => simp only [List.getElem?_cons_zero, Option.some.injEq] at hv hv'; subst hv hv'; simpa using hx
  | 1, hv, hv' => simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hv hv'; subst hv hv'; simp
  | j + 2, hv, _ => simp at hv

/-- `T1`'s field types: `t` its own record (no parameters), `g` `G1` at `T1` and at the tree rebuilt
from `t`'s small reading (what the record keys `g` by). -/
noncomputable def t1K : KnotSpec where
  d := t1D
  N := fun _ => false
  fty := fun R _ c i es => if c = 1 ∧ i = 0 then .data t1D (R [])
    else if c = 1 ∧ i = 1 then .data g1D (recK g1K [.ty (uTyR t1D (R [])), ofSmall (es.getD 0 .other)])
    else .ty TyM.err
  pEntry := pEntryTy
  guarded := fun n R R' hR _ _ _ c i es => by
    have hr := hR [] [] (ParAgree.refl _ _ _)
    split
    · exact data_agree _ hr
    · split
      · exact data_agree _ (recK_agree g1K n _ _ (parAgree_g1 (semAgree_data t1D (sort_ne _ rfl) hr)))
      · exact FTyAgree.refl _ _
  pEntry_agree := fun _ _ _ hp j => pEntryTy_agree hp j

/-- **`g`'s type, at the actual `t`, is the one the record keys by `t`'s small reading**: what the
run computes from `t` (`G1(T1, t)`: `G1`'s code at its record at `T1` and `t`) is the canonical
field type. -/
theorem t1_g_faithful (t : Sem) (ht : ∀ T, t ≠ .ty T) :
    (t1K.fty (recK t1K) [] 1 1 [t.small]).mean = uTyR g1D (recK g1K [.ty (uTyR t1D (recK t1K [])), t]) := by
  show uTyR g1D (recK g1K [.ty (uTyR t1D (recK t1K [])), ofSmall t.small]) = _
  congr 1
  apply recK_small g1K (fun j => j == 1) g1K_small_fty g1K_small_entry
  refine ⟨rfl, fun j v v' hv hv' => ?_⟩
  match j, hv, hv' with
  | 0, hv, hv' => simp only [List.getElem?_cons_zero, Option.some.injEq] at hv hv'; subst hv hv'; exact .inl rfl
  | 1, hv, hv' =>
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hv hv'; subst hv hv'
    exact .inr ⟨rfl, small_ofSmall _, ofSmall_not_ty _, ht⟩
  | j + 2, hv, _ => simp at hv

end Ochr.Meaning.DataModel.Exists.Proto

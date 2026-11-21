import Ochr.Meaning.DataModel.Exists.Proto.Hard

/-!
# Prototype: values of the hard declarations are members (kernel-checked)

On the universal signature, at the canonical records the knot builds: the shapes read off the
records are the field types (`rose_shape_a`, …), and constructor values built from them are
members (`DataLib.Mem`): a rose tree with a nested forest, `DNode(DLeaf)` of `DD(Nat)` (its field
lives at `DD(DD(Nat))`'s record).
-/

namespace Ochr.Meaning.DataModel.Exists.Proto

open Ochr Ochr.Meaning Ochr.Meaning.DataLib Ochr.Meaning.Canonical

theorem dataView_nondata {B : Type} {c : Code0 B} (h : c.isData = false) : dataView (.t0 B c) = none := by
  unfold dataView
  rw [dif_neg]
  rintro ⟨⟨d, r⟩, hs, he⟩
  have hs' : (d.sort == 0) = false := by simpa using hs
  simp only [uTyR, hs', Bool.false_eq_true, if_false] at he
  obtain ⟨e, hh⟩ := TyM.t0_inj he
  have := Code0.congr_heq (fun c => c.isData) c _ e hh
  simp only [Code0.isData] at this
  have h' : c.isData = true := this
  rw [h'] at h; cases h

theorem kind_nondata {B : Type} {c : Code0 B} (h : c.isData = false) : (FTy.ty (.t0 B c)).kind = .leaf B c := by
  simp [FTy.kind, dataView_nondata h]

theorem kind_data (d : IndDecl) (r : Rec) (hd : d.sort ≠ 0) : (FTy.ty (uTyR d r)).kind = .data d := by
  simp [FTy.kind, dataView_uTyR d r hd]

theorem cont_data (d : IndDecl) (r : Rec) (hd : d.sort ≠ 0) : (FTy.ty (uTyR d r)).cont = r := by
  simp [FTy.cont, dataView_uTyR d r hd]

/-- The shape at a key holding a data-sorted declaration: a `sub` at the continuation. -/
theorem uShape_sub (d : IndDecl) (r : Rec) (c i : Nat) (es : List Small) (d' : IndDecl) (r' : Rec)
    (hd : d'.sort ≠ 0) (hk : r (kindKey c i (projIdx d c es)) = .data d')
    (hc : contRec r (contStep c i (projIdx d c es)) = r') : uShape d r c i es = .sub d' r' := by
  have hs : (d'.sort == 0) = false := by simpa using hd
  simp only [uShape, hk, hs, Bool.false_eq_true, if_false, hc]


/-! ## `Rose(Nat)` -/

noncomputable def rR : Rec := recK roseK [.ty TyM.nat]
noncomputable def rL : Rec := recK listK [.ty (uTyR roseD rR)]



theorem rose_shape_a (es : List Small) (h : es = []) : uShape roseD rR 0 0 es = .leaf Nat .nat := by
  subst h
  apply uShape_leaf
  rw [projIdx_nil, rR, recK_kind roseK _ 0 0 [] rfl]
  exact kind_nondata rfl

theorem rose_shape_kids (es : List Small) (h : es.length = 1) : uShape roseD rR 0 1 es = .sub listD rL := by
  apply uShape_sub _ _ _ _ _ _ _ (sort_ne _ rfl)
  · rw [rR, recK_kind roseK _ 0 1 _ (by rw [projIdx_len, h])]; rfl
  · rw [rR, recK_contRec roseK _ 0 1 _ (by rw [projIdx_len, h])]; rfl

theorem list_shape_h (es : List Small) (h : es = []) : uShape listD rL 1 0 es = .sub roseD rR := by
  subst h
  apply uShape_sub _ _ _ _ _ _ _ (sort_ne _ rfl)
  · rw [projIdx_nil, rL, recK_kind listK _ 1 0 [] rfl]; exact kind_data roseD rR (sort_ne _ rfl)
  · rw [projIdx_nil, rL, recK_contRec listK _ 1 0 [] rfl]; exact cont_data roseD rR (sort_ne _ rfl)

theorem list_shape_t (es : List Small) (h : es.length = 1) : uShape listD rL 1 1 es = .sub listD rL := by
  apply uShape_sub _ _ _ _ _ _ _ (sort_ne _ rfl)
  · rw [rL, recK_kind listK _ 1 1 _ (by rw [projIdx_len, h])]; rfl
  · rw [rL, recK_contRec listK _ 1 1 _ (by rw [projIdx_len, h])]; rfl

theorem nil_mem : DataLib.Mem uSig listD rL (.dat "List" rL 0 []) :=
  (DataLib.mem_iff uSig listD rL _).2 ⟨⟨0, by decide⟩, [], rfl, rfl⟩

theorem cons_mem (x xs : Sem) (hx : DataLib.Mem uSig roseD rR x) (hxs : DataLib.Mem uSig listD rL xs) :
    DataLib.Mem uSig listD rL (.dat "List" rL 1 [x, xs]) := by
  refine (DataLib.mem_iff uSig listD rL _).2 ⟨⟨1, by decide⟩, [x, xs], rfl, ?_⟩
  refine ⟨x, [xs], rfl, ?_, xs, [], rfl, ?_, rfl⟩
  · show FitsOneM uSig (uShape listD rL 1 0 []) x
    rw [list_shape_h _ rfl]; exact hx
  · show FitsOneM uSig (uShape listD rL 1 1 [x.small]) xs
    rw [list_shape_t _ rfl]; exact hxs

theorem node_mem (n : Nat) (kids : Sem) (hk : DataLib.Mem uSig listD rL kids) :
    DataLib.Mem uSig roseD rR (.dat "Rose" rR 0 [.el0 Nat n, kids]) := by
  refine (DataLib.mem_iff uSig roseD rR _).2 ⟨⟨0, by decide⟩, [.el0 Nat n, kids], rfl, ?_⟩
  refine ⟨.el0 Nat n, [kids], rfl, ?_, kids, [], rfl, ?_, rfl⟩
  · show FitsOneM uSig (uShape roseD rR 0 0 []) _
    rw [rose_shape_a _ rfl]; exact ⟨n, rfl⟩
  · show FitsOneM uSig (uShape roseD rR 0 1 [(Sem.el0 Nat n).small]) kids
    rw [rose_shape_kids _ rfl]; exact hk

/-- **`Node(5, [Node(6, [])])` is a member of `Rose(Nat)`** at its canonical record: the forest is a
member of `List` at the record the knot gives the nested field. -/
theorem rose_example : DataLib.Mem uSig roseD rR
    (.dat "Rose" rR 0 [.el0 Nat 5, .dat "List" rL 1 [.dat "Rose" rR 0 [.el0 Nat 6, .dat "List" rL 0 []],
      .dat "List" rL 0 []]]) :=
  node_mem 5 _ (cons_mem _ _ (node_mem 6 _ nil_mem) nil_mem)

/-! ## `DD(Nat)`: `DNode(DLeaf)`, the field at `DD(DD(Nat))`'s record -/

noncomputable def dR : Rec := recK ddK [.ty TyM.nat]
noncomputable def dR2 : Rec := recK ddK [.ty (uTyR ddD dR)]

theorem dd_shape_x (es : List Small) (h : es = []) : uShape ddD dR 1 0 es = .sub ddD dR2 := by
  subst h
  apply uShape_sub _ _ _ _ _ _ _ (sort_ne _ rfl)
  · rw [projIdx_nil, dR, recK_kind ddK _ 1 0 [] rfl]; rfl
  · rw [projIdx_nil, dR, recK_contRec ddK _ 1 0 [] rfl]; rfl

theorem dd_example : DataLib.Mem uSig ddD dR (.dat "DD" dR 1 [.dat "DD" dR2 0 []]) := by
  refine (DataLib.mem_iff uSig ddD dR _).2 ⟨⟨1, by decide⟩, _, rfl, ?_⟩
  refine ⟨_, [], rfl, ?_, rfl⟩
  show FitsOneM uSig (uShape ddD dR 1 0 []) _
  rw [dd_shape_x _ rfl]
  exact (DataLib.mem_iff uSig ddD dR2 _).2 ⟨⟨0, by decide⟩, [], rfl, rfl⟩

end Ochr.Meaning.DataModel.Exists.Proto

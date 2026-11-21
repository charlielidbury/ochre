import Ochr.Meaning.Data

/-!
# The canonical construction: reading a field type into a record (docs/34 §18)

A record is a function of paths. An entry names what sits at a key, a data type's declaration
(`.data d _`, the stored record unused) or a leaf's code, and NEVER holds a record: the record of the
data type at a key is the CONTINUATION of the path past that key. Keys (all `RStep`s, told apart
by the length of their list of small readings):
* `[(c, i, es)]` with `es.length = i`: what field `i` of constructor `c` is, after the earlier
  fields read small (`kindKey`);
* `(c, i, es ++ [.proof]) :: q`: the record of that field's data type, at `q` (`contStep`);
* `[(j, 0, [.other])]` (`paramKey j`, as today) and `(j, 0, [.other, .other]) :: q`
  (`paramContStep`): parameter `j`'s entry and the record of its data type.

The signature is then ONE function of the record (`uShape`), with no program in it: a data entry
gives a `sub` (a `prf` for a `Prop`-sorted declaration) at the continuation, a leaf entry its leaf.
So the carriers (`ucar`) and the types of records (`uTyR`) depend on nothing but the record. The
earlier fields are projected to the constructor's index fields before the record is read
(`FieldTyIdx` holds at every record, `uShape_idx`).

A leaf's type is its code, always (`shapeTyP`, every model's `shapeTy`), so a data code over a
foreign carrier (a junk code of `Type₀`'s carrier) is an ordinary leaf.
-/

namespace Ochr.Meaning.Canonical

open Ochr Ochr.Meaning Ochr.Meaning.DataLib

/-! The keys (`kindKey`, `contStep`, `paramKey`, `paramContStep`), `contRec`, `projIdx`, the
universal signature `uShape`/`uSig` and `uShape_idx` are the library's (`DataLib/Universal.lean`,
ported from here). -/

/-- The record a data entry stored before the port (none now). -/
def dummyRec : Rec := fun _ => .none

/-- The carrier of `D` at a record: a function of the record alone. -/
def ucar (d : IndDecl) (r : Rec) : Type := DataLib.car uSig d r

/-- A data type's code at a record. -/
def uTyR (d : IndDecl) (r : Rec) : TyM :=
  if d.sort == 0 then TyM.prop (Nonempty (ucar d r)) else .t0 (ucar d r) (.data d r (ucar d r))

/-- Every model's types of data types are these (the signature is universal). -/
theorem tyR_eq_uTyR (dm : DataModel) (d : IndDecl) (r : Rec) : dm.tyR d r = uTyR d r := rfl

theorem car_eq_ucar (dm : DataModel) (d : IndDecl) (r : Rec) : dm.car d r = ucar d r := rfl

/-- A shape's type, for every model (`DataModel.shapeTy`, which reads no record function). -/
def shapeTyP : Shape → TyM
  | .leaf B c => .t0 B c
  | .sub d r => if d.sort == 0 then TyM.err else uTyR d r
  | .prf d r => if d.sort == 0 then uTyR d r else TyM.err

theorem shapeTy_eq_shapeTyP (dm : DataModel) (s : Shape) : dm.shapeTy s = shapeTyP s := by
  cases s <;> rfl

/-! ## Reading a type into a record: its kind and its continuation -/

theorem data_heq_inj {A A' : Type} {d d' : IndDecl} {r r' : Rec} (hA : A = A')
    (h : HEq (Code0.data d r A) (Code0.data d' r' A')) : d = d' ∧ r = r' := by
  subst hA; cases h; exact ⟨rfl, rfl⟩

theorem uTyR_inj {d d' : IndDecl} {r r' : Rec} (hs : d.sort ≠ 0) (hs' : d'.sort ≠ 0)
    (h : uTyR d r = uTyR d' r') : d = d' ∧ r = r' := by
  have e1 : (d.sort == 0) = false := by simpa using hs
  have e2 : (d'.sort == 0) = false := by simpa using hs'
  simp only [uTyR, e1, e2, Bool.false_eq_true, if_false] at h
  obtain ⟨hA, hh⟩ := TyM.t0_inj h
  exact data_heq_inj hA hh

open Classical in
/-- The declaration and record of a type that is a data type's code at a record (data-sorted,
the model's carrier): a junk code, a proposition, a number type are not. -/
noncomputable def dataView (T : TyM) : Option (IndDecl × Rec) :=
  if h : ∃ p : IndDecl × Rec, p.1.sort ≠ 0 ∧ T = uTyR p.1 p.2 then some h.choose else none

theorem dataView_uTyR (d : IndDecl) (r : Rec) (hs : d.sort ≠ 0) : dataView (uTyR d r) = some (d, r) := by
  have h : ∃ p : IndDecl × Rec, p.1.sort ≠ 0 ∧ uTyR d r = uTyR p.1 p.2 := ⟨(d, r), hs, rfl⟩
  unfold dataView
  rw [dif_pos h]
  obtain ⟨hs', he⟩ := h.choose_spec
  obtain ⟨h1, h2⟩ := uTyR_inj hs hs' he
  congr 1
  exact Prod.ext h1.symm h2.symm

theorem dataView_some {T : TyM} {d : IndDecl} {r : Rec} (h : dataView T = some (d, r)) :
    d.sort ≠ 0 ∧ T = uTyR d r := by
  unfold dataView at h
  split at h
  · rename_i hx
    have := hx.choose_spec
    simp only [Option.some.injEq] at h
    rw [h] at this
    exact this
  · cases h

/-- **A field's type as the construction reads it**: a declaration at a record (any sort; the
knot's own occurrences and the formers it nests in come this way, read off the field type's
syntax), or a type (a parameter's value, a type function's result, an equation, `Nat`). -/
inductive FTy : Type 3
  | data (d : IndDecl) (r : Rec)
  | ty (T : TyM)

def FTy.mean : FTy → TyM
  | .data d r => uTyR d r
  | .ty T => T

/-- What the record stores at the field's key. -/
noncomputable def FTy.kind : FTy → Entry
  | .data d _ => .data d
  | .ty T => match dataView T with
    | some (d, _) => .data d
    | none => match T with
      | .t0 B c => .leaf B c
      | _ => .none

/-- What the record holds past the field's key: the field's data type's record. -/
noncomputable def FTy.cont : FTy → Rec
  | .data _ r => r
  | .ty T => match dataView T with
    | some (_, r) => r
    | none => dummyRec

/-- A field type of carrier level 0 (every first-order field type is). -/
def FTy.Lvl0 : FTy → Prop
  | .data _ _ => True
  | .ty T => ∃ B c, T = .t0 B c

/-- **The core of faithfulness**: a record holding a field type's kind at the field's key and its
continuation past it means that type there, whatever kind of type it is (a data type of either
sort, a junk code, a proposition, `Nat`, a function type). -/
theorem shapeTyP_uShape (d : IndDecl) (r : Rec) (c i : Nat) (es : List Small) (F : FTy) (hF : F.Lvl0)
    (hk : r (kindKey c i (projIdx d c es)) = F.kind)
    (hc : contRec r (contStep c i (projIdx d c es)) = F.cont) :
    shapeTyP (uShape d r c i es) = F.mean := by
  unfold uShape
  rw [hk, hc]
  cases F with
  | data d' r' =>
    simp only [FTy.kind, FTy.cont, FTy.mean]
    by_cases hs : (d'.sort == 0) = true
    · simp [hs, shapeTyP]
    · simp [hs, shapeTyP]
  | ty T =>
    simp only [FTy.kind, FTy.cont, FTy.mean]
    rcases hv : dataView T with _ | ⟨d', r'⟩
    · obtain ⟨B, cd, rfl⟩ := hF
      simp [shapeTyP]
    · obtain ⟨hs, rfl⟩ := dataView_some hv
      have hs' : (d'.sort == 0) = false := by simpa using hs
      simp [hs', shapeTyP]

end Ochr.Meaning.Canonical

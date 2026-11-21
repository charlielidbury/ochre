import Ochr.Meaning.DataLib.Members

/-!
# The data model's library: the universal signature (docs/34 §18)

A record is a function of paths, and an entry names what sits at a key (a declaration, a leaf's
code, a value read small) and never holds a record: the record of the data type at a key is the
CONTINUATION of the path past the key. Keys (all `RStep`s, told apart by the length of their list
of small readings):
* `[(c, i, es)]` with `es.length = i`: what field `i` of constructor `c` is, after the earlier
  fields read small (`kindKey`);
* `(c, i, es ++ [.proof]) :: q`: the record of that field's data type, at `q` (`contStep`);
* `[(j, 0, [.other])]` (`paramKey j`): parameter `j`'s entry; `(j, 0, [.other, .other]) :: q`
  (`paramContStep`): the record of its data type.

The signature is then ONE function of the record (`uShape`), with no program in it, so the
carriers, the members and the types of data types depend on nothing but the record; what a program
decides is only its records (`DataModel.recOf`). The earlier fields are projected to the
constructor's index fields before the record is read, so a field's shape reads only those
(`uShape_idx`: the rules' `FieldTyIdx`, at every record).
-/

namespace Ochr.Meaning.DataLib

/-- What field `i` of constructor `c` is, after the earlier fields read small. -/
def kindKey (c i : Nat) (es : List Small) : List RStep := [(c, i, es)]
/-- The step to the record of that field's data type. -/
def contStep (c i : Nat) (es : List Small) : RStep := (c, i, es ++ [.proof])
/-- Where a record keeps parameter `j`'s entry (a type parameter's kind, a level-0 value parameter
read small). Field `0`'s key has no earlier fields, so it is no field's key. -/
def _root_.Ochr.Meaning.paramKey (j : Nat) : List RStep := [(j, 0, [.other])]
/-- The step to the record of parameter `j`'s data type. -/
def paramContStep (j : Nat) : RStep := (j, 0, [.other, .other])

/-- The record past a step. -/
def contRec (r : Rec) (s : RStep) : Rec := fun q => r (s :: q)

/-- The earlier fields, read only at the constructor's index fields (`IndDecl.indexFields`). -/
def projIdx (d : IndDecl) (c : Nat) (es : List Small) : List Small :=
  es.zipIdx.map fun sk => if (d.indexFields c).contains sk.2 then sk.1 else .other

theorem projIdx_len (d : IndDecl) (c : Nat) (es : List Small) : (projIdx d c es).length = es.length := by
  simp [projIdx]

theorem projIdx_nil (d : IndDecl) (c : Nat) : projIdx d c [] = [] := rfl

/-- **A field's shape, read off the record alone.** A data entry is a `sub` at the continuation (a
`prf` for a `Prop`-sorted declaration), a leaf entry its leaf, anything else the error leaf. -/
def uShape (d : IndDecl) (r : Rec) (c i : Nat) (es : List Small) : Shape :=
  match r (kindKey c i (projIdx d c es)) with
  | .data d' => if d'.sort == 0 then .prf d' (contRec r (contStep c i (projIdx d c es)))
      else .sub d' (contRec r (contStep c i (projIdx d c es)))
  | .leaf B cd => .leaf B cd
  | _ => .leaf PEmpty .err

/-- **The universal signature.** -/
def uSig : Sig := ⟨uShape⟩

/-- **`FieldTyIdx` by construction**: the shape reads the earlier fields only at index fields. -/
theorem uShape_idx (d : IndDecl) (r : Rec) (c i : Nat) (es es' : List Small)
    (h : projIdx d c es = projIdx d c es') : uShape d r c i es = uShape d r c i es' := by
  unfold uShape; rw [h]

theorem uShape_data (d : IndDecl) (r : Rec) (c i : Nat) (es : List Small) (d' : IndDecl)
    (hk : r (kindKey c i (projIdx d c es)) = .data d') :
    uShape d r c i es = if d'.sort == 0 then .prf d' (contRec r (contStep c i (projIdx d c es)))
      else .sub d' (contRec r (contStep c i (projIdx d c es))) := by
  simp only [uShape, hk]

theorem uShape_leaf (d : IndDecl) (r : Rec) (c i : Nat) (es : List Small) {B : Type} (cd : Code0 B)
    (hk : r (kindKey c i (projIdx d c es)) = .leaf B cd) : uShape d r c i es = .leaf B cd := by
  simp only [uShape, hk]

end Ochr.Meaning.DataLib

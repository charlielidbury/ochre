import Ochr.Meaning.Run
import Ochr.Meaning.DataModel.Old

/-!
# Reading one field ended the borrow of another: the audit's A1 was not fixed for packed data (built)

docs/31 D25 (third lead, 2026-11-19). [Access] for a read of `p.0` ends the labels what it
observes of `p`'s position depends on (`SState.access`, `obsDep`: SOME future, changed at the
label alone to SOME value, changes the observation). The batch's stage 4 made the observation the
content at the place's path, so that a borrow of `p.1` survives a read of `p.0`, and checked it on
a position whose meaning is the tuple `P(ψ l, c)` at EVERY future (`Adequacy_flipped.access_other_field`).

The run's own meanings are not that. A value with a lent field means, at the future `ψ`,
`ctorM d ps c [a, ψ l]`, and `ctorM` packed its fields when all are whole and meant `err` when the
packing failed. So at a future that gives `l` a whole value outside the field's type (`•` at a
`Nat` field) the value was `err` (`old_collapse`), a field of `err` cannot be read
(`follow_err_field`), and the observation of `p.0` was `err` there and the content of `p.0`
elsewhere: it depended on `l` (`old_sibling_dep`). So the reference's read of `p.0` ended the
borrow of `p.1`, a later write through it was lost, and on the accepted `Disjoint`
(`Regress/AdequacyProbes.lean`; `DisjointIs` proves the write is seen) the run's result was not
the checker's. A fault of the model.

Fixed: an ill-typed constructor value means the tuple of its fields, never `err` (`ctorM`). A
constructor value's fields are then read whatever the others hold (`DataModel.parts_ctorM`,
`sibling_read`; since docs/31 D32 a constructor value describes itself, and since docs/34's port it
is a tree, nothing else).

The old meaning is recorded against the frozen copy of the layer before the port
(`DataModel/Old.lean`): with whole fields that do not pack it was `err` (`old_collapse`), and no
field of `err` can be read (`follow_err_field`, the same in both layers), so a read that succeeded
at one future failed at another that gave the label a whole value outside its field's type.
-/

namespace Ochr.Meaning.Regress.SiblingAccess
open Ochr Ochr.Meaning

open Classical in
/-- `ctorM` as it first was: an ill-typed constructor value means `err`. -/
noncomputable def ctorMOld (dm : Old.DataModel) (d : IndDecl) (ps : List Old.Sem) (c : Nat) (fs : List Old.Sem) : Old.Sem :=
  if ∀ f ∈ fs, f.whole then
    match dm.pack d ps c fs with
    | some x => .el0 (dm.car d ps) x
    | none => .err
  else .dat d.name ps c fs none

/-- With whole fields that do not pack, the old meaning is `err`. -/
theorem old_collapse (dm : Old.DataModel) (d : IndDecl) (ps : List Old.Sem) (c : Nat) (fs : List Old.Sem)
    (hw : ∀ f ∈ fs, f.whole) (hp : dm.pack d ps c fs = none) : ctorMOld dm d ps c fs = .err := by
  unfold ctorMOld
  rw [if_pos hw, hp]

variable (dm : DataModel) (Γ : List IndDecl)

/-- No field of `err` can be read, at any type. -/
theorem follow_err_field (T : TyS) (g : FieldRef) (sts : List Step) :
    Sem.follow dm Γ T .err (.field g :: sts) = none := rfl

/-- **The positive form.** A field of a constructor value is its field, whatever the other fields
hold: lent, moved, or outside their types (read off the value itself, a tree). -/
theorem sibling_read (d : IndDecl) (ps : List Sem) (c i : Nat) (fs : List Sem) :
    Sem.stepField dm Γ c i (dm.ctorM d ps c fs)
      = (fs[i]?).map fun f => (f, contentTyS dm Γ d.name (dm.recOf d ps) c i (fs.take i) f) := by
  simp [Sem.stepField, DataModel.ctorM, DataModel.ctorR]

end Ochr.Meaning.Regress.SiblingAccess

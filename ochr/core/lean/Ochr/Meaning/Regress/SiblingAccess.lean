import Ochr.Meaning.Run

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
`sibling_read`; since docs/31 D32 a constructor value describes itself, its element aside).
-/

namespace Ochr.Meaning.Regress.SiblingAccess
open Ochr Ochr.Meaning

variable (dm : DataModel) (Γ : List IndDecl)

open Classical in
/-- `ctorM` as it first was: an ill-typed constructor value means `err`. -/
noncomputable def ctorMOld (d : IndDecl) (ps : List Sem) (c : Nat) (fs : List Sem) : Sem :=
  if ∀ f ∈ fs, f.whole then
    match dm.pack d ps c fs with
    | some x => .el0 (dm.car d ps) x
    | none => .err
  else .dat d.name ps c fs none

/-- With whole fields that do not pack, the old meaning is `err`. -/
theorem old_collapse (d : IndDecl) (ps : List Sem) (c : Nat) (fs : List Sem)
    (hw : ∀ f ∈ fs, f.whole) (hp : dm.pack d ps c fs = none) : ctorMOld dm d ps c fs = .err := by
  unfold ctorMOld
  rw [if_pos hw, hp]

/-- No field of `err` can be read, at any type. -/
theorem follow_err_field (T : TyS) (g : FieldRef) (sts : List Step) :
    Sem.follow dm Γ T .err (.field g :: sts) = none := rfl

/-- **The old dependence.** If a read of a field succeeds at one future, and some whole value of
the label `l` does not pack, then the content read depended on `l` under the old meaning, whatever
field is read: the two futures give a content and `none`. -/
theorem old_sibling_dep (T : TyS) (g : FieldRef) (sts : List Step) (d : IndDecl) (ps : List Sem) (c : Nat)
    (fs : Sem → List Sem) (l : Nat) (φ : Future) (x : Sem)
    (hgood : (Sem.follow dm Γ T (ctorMOld dm d ps c (fs (φ l))) (.field g :: sts)).isSome)
    (hw : ∀ f ∈ fs x, f.whole) (hp : dm.pack d ps c (fs x) = none) :
    Sem.follow dm Γ T (ctorMOld dm d ps c (fs (φ l))) (.field g :: sts)
      ≠ Sem.follow dm Γ T (ctorMOld dm d ps c (fs ((φ.upd l x) l))) (.field g :: sts) := by
  rw [Future.upd_same, old_collapse dm d ps c (fs x) hw hp, follow_err_field]
  intro e
  rw [e] at hgood
  cases hgood

/-- **The positive form.** A field of a constructor value is its field, whatever the other fields
hold: lent, moved, or outside their types (since docs/31 D32 read off the value itself). -/
theorem sibling_read (d : IndDecl) (ps : List Sem) (c i : Nat) (fs : List Sem) :
    Sem.stepField dm Γ c i (dm.ctorM d ps c fs)
      = (fs[i]?).map fun f => (f, contentTyS dm Γ d.name ps c i (fs.take i) f) := by
  obtain ⟨el, hel⟩ := ctorM_dat dm d ps c fs
  rw [hel]
  simp [Sem.stepField]

end Ochr.Meaning.Regress.SiblingAccess

import Ochr.Meaning.Strict.Ops

/-!
# The read off the program's declarations (a finding, 2026-11-21, and its repair)

`MemReads dm Γ` asked of EVERY type: a whole value a read path reaches in a member is a member of
the type the read gives it. The by-name read typed a field through the declaration it found BY
NAME in `Γ`; a data code of an undeclared declaration (the signature is universal) has members whose
fields read at `err`: `Fresh.C(5)` at a record giving field `0` a `Nat` leaf read `5` at `err`, so
`MemReads` held in no model (kernel-checked at spine-model 9911399e). Route (c) types a read by the
type it starts at (`DataModel.readTy`): `fresh_read` (its field at `Nat`), and
`ReadMember.follow_good` (every read of a member of any data code gives a member) with no hypothesis.
Since the dependent-values unit `MemReads` is deleted (reads are strict, `Run.ReadGood`).
-/

namespace Ochr.Meaning.Strict.MemReadsCE

open Ochr Ochr.Meaning

/-- A declaration the program does not declare: one constructor with one field. -/
def dF : IndDecl := { name := "Fresh", ctors := [("C", [("x", .nat)])] }

/-- A record giving that field the leaf `Nat`. -/
def rF : Rec
  | [(0, 0, [])] => .leaf Nat .nat
  | _ => .none

/-- The field, by name. -/
def g : FieldRef := { ty := "Fresh", ctor := 0, idx := 0, name := "x" }

/-- `Fresh.C(5)` is a member of `Fresh` at `rF`, in every data model. -/
theorem mem (dm : DataModel) : Sem.dat "Fresh" rF 0 [.el0 Nat 5] ∈ₛ[dm.read] dm.tyR dF rF := by
  refine (dm.mem_tyR dF rF rfl _).2 ((DataLib.mem_iff dm.sig dF rF _).2
    ⟨⟨0, by decide⟩, [.el0 Nat 5], rfl, ?_⟩)
  show ∃ f fs', [Sem.el0 Nat 5] = f :: fs' ∧ _ ∧ _
  refine ⟨.el0 Nat 5, [], rfl, ?_, rfl⟩
  show ∃ b, DataLib.encLeaf Code0.nat b = Sem.el0 Nat 5
  exact ⟨5, rfl⟩

/-- **The typed read (route (c)) reads `Fresh.C(5)`'s field at `Nat`**, whatever `Γ` declares: the
declaration comes from the type, not from `Γ` by name. (The by-name read gave `err` here, so
`MemReads` failed for every model and every `Γ` without a `Fresh`: the finding of 2026-11-21, at
spine-model 9911399e, `not_memReads`.) -/
theorem fresh_read (dm : DataModel) (Γ : List IndDecl) :
    Sem.follow dm Γ (.plain (dm.tyR dF rF)) (.dat "Fresh" rF 0 [.el0 Nat 5]) [.field g]
      = some (.el0 Nat 5, .plain TyM.nat) := by
  have hown : ¬ dm.OwnCarrier Code0.nat := by
    rintro ⟨d, r, h, -⟩; cases h
  have hdc : (TyS.plain (dm.tyR dF rF)).m.dataCode? = some (dF, rF) := rfl
  have hsh : dm.sig.shape dF rF 0 0 [] = .leaf Nat .nat := rfl
  have hrt : dm.readTy Γ dF rF 0 0 [] (.el0 Nat 5) = some TyM.nat := by
    simp only [DataModel.readTy, List.map_nil, hsh, DataModel.shapeReadTy, if_neg hown]; rfl
  simp only [Sem.follow, Sem.step, Sem.stepField, g, hdc, Option.bind]
  simp [show dF.name = "Fresh" from rfl, hrt]

end Ochr.Meaning.Strict.MemReadsCE

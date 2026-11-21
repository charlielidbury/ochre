import Ochr.Meaning.Run
import Ochr.Examples.Nat

/-!
# The reference read a constructor value through another declaration of the same carrier (built; fixed by D32)

docs/31 D31 (fifth lead, 2026-11-19; found attacking L2, the drop's write of `⊥` at a path). The
reference navigates data by its TYPE MEANING: a match's tag (`indTag`), a field read
(`Sem.follow`, `Sem.stepField`), a write or drop at a path (`Sem.updAt`) and [Rec]'s rank all
decode a constructor value's meaning through `TyM.dataOf`, the FIRST declaration of `Γ` (with
parameters chosen classically, `DataModel.paramsOf`) whose carrier is the type's. Carriers do not
determine declarations: two declarations may have equal carriers, which Lean can neither prove nor
refute for two types of the same size, and a data model may make true. Then the reference decodes
the value with the other declaration's constructors and fields.

The model below satisfies every law of `DataModel` and covers both declarations (as `CtxOk`
requires of `Γ`): `B1 := T1 | F1` and `B2 := F2 | T2`, both with carrier `Bool`, `B1` storing `T1`
as `true` and `B2` storing `T2` as `true`. The checker's `T2` (constructor 1 of `B2`) means
`el0 Bool true`, at the type `B2`, whose meaning is `ty0 Bool`; the reference's match reads its
tag through `B1` and gets constructor `0` (`tag_wrong`), so it takes the arm `F2`. On the program
`match T2 { F2 => Z, T2 => S(Z) }` the reference computes `Z` where the checker computes `S(Z)`,
and so `Id(Nat, …, S(Z))`, which the checker proves by `refl`, is false in the model. The same
decoding is in the field read, the write and the drop at a path (`Sem.stepField`, `Sem.updAt`):
there the other declaration's field list is read and its name written into the result.

So every step lemma that navigates data is false at this model, and at the generic model it is
unprovable (a proof would have to refute that an earlier declaration's carrier equals the value's,
which for two carriers of the same size Lean cannot do). The fix (D31): decode by the type's
structured data (`TyS.data`: the declaration's NAME and the parameters' meanings, which every
binding's type and every field's hint already carry, D8), never by its carrier.

Fixed, first by decoding through the type's declaration name (D31), then for good by D32: a
constructor value describes itself (since docs/34's port, a tree: name, record, constructor,
fields), so the match reads `T2`'s constructor off the value at any type (`tag_right`), and the
value is a member of `B2`'s code (`T2_mem`). The counterexample against the old definitions is kept,
unbuilt, in `DataOfChoice_189132fd.lean`. Since the port no data model chooses carriers: they are
built from the signature, and nothing is read through them.
-/

open Ochr.Test

ochr DataOfChoice uses Nats {
  inductive B1 := T1 | F1
  inductive B2 := F2 | T2
  -- the match on `T2` takes the arm `T2`: the checker proves its result is `S(Z)`
  def PickT2 : Nat := (let x = T2; match x { F2 => Z, T2 => S(Z) })
  def PickT2Is : Id(Nat, PickT2, S(Z)) := refl
  -- the control: the result is not `Z`
  reject def PickT2Z : Id(Nat, PickT2, Z) := refl
}

namespace Ochr.Meaning.Regress.DataOfChoice
open Ochr Ochr.Meaning

def B1 : IndDecl := { name := "B1", ctors := [("T1", []), ("F1", [])] }
def B2 : IndDecl := { name := "B2", ctors := [("F2", []), ("T2", [])] }

/-- A data model of `B1` and `B2`: no fields, the empty record. -/
def dm : DataModel where
  covers d := d = B1 ∨ d = B2
  recOf _ _ := natRec
  paramTy _ _ _ := .err

/-- The decisions play no part. -/
def D : Decisions where
  flags _ _ := (false, false)
  placeDecl _ _ := .other
  declOf _ _ := .other
  «copy» _ := false
  piSort _ _ := 1
  joinMoves _ _ _ := []
  rePointed _ _ := []
  typeDecl _ _ := .other

/-- The run context: the model above, `Γ = [B1, B2]` (the order the program declares them in);
the code meaning and the decisions play no part. -/
noncomputable def K : RunCtx where
  dm := dm
  Γ := [B1, B2]
  C := { global := fun _ => (.err, .plain .err), sealed := fun _ _ _ _ => .err,
         clo := fun _ _ _ _ _ => .err, pi := fun _ _ _ _ _ => .err, paramTy := fun _ _ _ _ => .plain .err }
  D := D



variable (ρ : Assignment) (φ : Future) (H : TyS)

/-- The checker's `T2` means constructor `1` of `B2`, describing itself: its declaration's name,
its record, constructor `1`, no fields. -/
theorem mean_T2 : Value.mean K.dm K.C K.Γ ρ φ H (.ind "B2" 1 ⟨"T2"⟩ [] []) = .dat "B2" natRec 1 [] := by
  simp [Value.mean, K, B1, B2, Value.meanParams, Value.meanFields, DataModel.ctorR, dm]

/-- The type `B2` is the code naming `B2` and its record. -/
theorem mean_B2 : Value.mean K.dm K.C K.Γ ρ φ H (.tInd "B2" []) = .ty (dm.tyR B2 natRec) := by
  simp [Value.mean, K, B1, B2, Value.meanParams, DataModel.tyM, dm, paramsOk_nil]

/-- **The reference's match reads constructor `1`** at any type the value is held at: the value is
read, not decoded through a declaration found by its carrier (`DataOfChoice_189132fd`: the match
took the arm `F2`) or through its type at all. -/
theorem tag_right (T : TyS) : indTag (Value.mean K.dm K.C K.Γ ρ φ H (.ind "B2" 1 ⟨"T2"⟩ [] [])) T = .el0 Nat 1 := by
  rw [mean_T2]; rfl

/-- The value is a member of its type: constructor `1` of `B2`, at `B2`'s record, with no fields. -/
theorem T2_mem : Value.mean K.dm K.C K.Γ ρ φ H (.ind "B2" 1 ⟨"T2"⟩ [] []) ∈ₛ[dm.read] dm.tyM B2 [] := by
  rw [mean_T2]
  exact (DataModel.mem_tyR dm B2 natRec rfl _).2 ((DataLib.mem_iff dm.sig B2 natRec _).2 ⟨⟨1, by decide⟩, [], rfl, rfl⟩)

/-- A value held at a type that names no declaration (as a call's result was typed, `.plain`) is
still read: nothing is decoded through a type. -/
theorem indTag_plain (T : TyM) : indTag (.dat "B2" natRec 1 []) (.plain T) = .el0 Nat 1 := rfl

end Ochr.Meaning.Regress.DataOfChoice

import Ochr.Meaning.DataModel.Exists.Piece3

/-!
# Definitions the existence statements share (moved out of `General.lean`, exists5)

* `setRec`: a model with one declaration's records replaced (the knot's records are tried out in it).
* `GlobalsTyped`: the globals a field type can call return types of `Prop` or `Type₀` (finding 2's
  obligation, `General.globals_typed`).
-/

namespace Ochr.Meaning.DataModel.Exists

open Ochr Ochr.Meaning

open Classical in
/-- The model with `d`'s records replaced. -/
noncomputable def setRec (dm : DataModel) (d : IndDecl) (R : List Sem → Rec) : DataModel :=
  { dm with recOf := fun d' => if d' = d then R else dm.recOf d' }

theorem setRec_self (dm : DataModel) (d : IndDecl) (R : List Sem → Rec) : (setRec dm d R).recOf d = R := by
  simp [setRec]

theorem setRec_other (dm : DataModel) {d d' : IndDecl} (R : List Sem → Rec) (h : d' ≠ d) :
    (setRec dm d R).recOf d' = dm.recOf d' := by
  simp [setRec, h]

@[simp] theorem setRec_read (dm : DataModel) (d : IndDecl) (R : List Sem → Rec) : (setRec dm d R).read = dm.read := rfl

@[simp] theorem setRec_paramTy (dm : DataModel) (d : IndDecl) (R : List Sem → Rec) :
    (setRec dm d R).paramTy = dm.paramTy := rfl

/-- **The globals of a program state are typed where a field type can call them**: each global whose
stored type is a function type into a sort, applied (`callOf`) at members of its domains, returns a
member of the codomain, a code of `Prop` or of `Type₀` (`Probes.DMXBoundary`: the checker admits no
other codomain in a field type), or does not run. `Step2.EvTGood` is this at one global. -/
def GlobalsTyped (dm : DataModel) (P : ProgState) : Prop :=
  ∀ (n : String) (g : GDef), P.globals.find? (·.name == n) = some g →
    (∃ caps hs ds l rd, g.ty = .tPi caps (.pi hs ds (.sort l)) rd ∧ l ≤ 1) →
  ∀ (args : List Res) (s : SState) (r : Res) (s' : SState),
    callOf dm.read (P.baseC.global n) args s = some (r, s') →
      ∃ (A : Type) (c : Code0 A), r.1 = .ty (.t0 A c) ∧ (c.level = some 1 ∨ c.level = some 0)

/-- **A name a prefix declares is found identically in the longer list** (the one-line lemma the
simulation's link needs once it says "the checker's declarations are a prefix of the context's list";
docs/34 §18.13). -/
theorem find_of_prefix {Γ₀ Γ : List IndDecl} (h : Γ₀ <+: Γ) {n : String} {d : IndDecl}
    (hd : Γ₀.find? (·.name == n) = some d) : Γ.find? (·.name == n) = some d := by
  obtain ⟨t, rfl⟩ := h
  rw [List.find?_append, hd]; rfl

end Ochr.Meaning.DataModel.Exists

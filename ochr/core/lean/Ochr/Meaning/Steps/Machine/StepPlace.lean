import Ochr.Meaning.Steps.Machine.IH

/-!
# The step of the induction for the machine's block: reads, borrows, assignments, drops, a place's type

Each function at fuel `nf + 1`, its body walked by `grows_go ih` (the induction hypothesis at `nf`).
-/

namespace Ochr.Meaning.Steps.Machine

open Ochr Ochr.Meaning Ochr.Meaning.Steps

variable {tb : Tab} {nf : Nat}

theorem step_openWrite (ih : MachineGrows tb nf) :
    ∀ (p : Place), GrowsIn tb (Ochr.openWrite ((nf + 1)) p) := by
  intro p
  unfold Ochr.openWrite; grows_go ih

theorem step_readPlace (ih : MachineGrows tb nf) :
    ∀ (p : Place), GrowsIn tb (Ochr.readPlace ((nf + 1)) p) := by
  intro p
  unfold Ochr.readPlace; grows_go ih

theorem step_copyRead (ih : MachineGrows tb nf) :
    ∀ (p : Place), GrowsIn tb (Ochr.copyRead ((nf + 1)) p) := by
  intro p
  unfold Ochr.copyRead; grows_go ih

theorem step_borrowPlace (ih : MachineGrows tb nf) :
    ∀ (p : Place), GrowsIn tb (Ochr.borrowPlace ((nf + 1)) p) := by
  intro p
  unfold Ochr.borrowPlace; grows_go ih

theorem step_assignPlace (ih : MachineGrows tb nf) :
    ∀ (p : Place), GrowsIn tb (Ochr.assignPlace ((nf + 1)) p) := by
  intro p
  unfold Ochr.assignPlace; grows_go ih

theorem step_dropTopBind (ih : MachineGrows tb nf) :
    GrowsIn tb (Ochr.dropTopBind ((nf + 1))) := by
  unfold Ochr.dropTopBind; grows_go ih

theorem step_endLoansOfTopBind (ih : MachineGrows tb nf) :
    ∀ (f : Nat), GrowsIn tb (Ochr.endLoansOfTopBind ((nf + 1)) f) := by
  intro f
  unfold Ochr.endLoansOfTopBind; grows_go ih

theorem step_dropValue (ih : MachineGrows tb nf) :
    ∀ (v : Value) (T : Option Value), GrowsIn tb (Ochr.dropValue ((nf + 1)) v T) := by
  intro v T
  unfold Ochr.dropValue; grows_go ih

theorem step_endLoansOfTopTemp (ih : MachineGrows tb nf) :
    GrowsIn tb (Ochr.endLoansOfTopTemp ((nf + 1))) := by
  unfold Ochr.endLoansOfTopTemp; grows_go ih

theorem step_popFrame (ih : MachineGrows tb nf) :
    GrowsIn tb (Ochr.popFrame ((nf + 1))) := by
  unfold Ochr.popFrame; grows_go ih

theorem step_placeTypeQ (ih : MachineGrows tb nf) :
    ∀ (p : Place), GrowsIn tb (Ochr.placeType? ((nf + 1)) p) := by
  intro p
  unfold Ochr.placeType?; grows_go ih

theorem step_placeType (ih : MachineGrows tb nf) :
    ∀ (p : Place), GrowsIn tb (Ochr.placeType ((nf + 1)) p) := by
  intro p
  unfold Ochr.placeType; grows_go ih

theorem step_natPlace (ih : MachineGrows tb nf) :
    ∀ (q : Place), GrowsIn tb (Ochr.natPlace ((nf + 1)) q) := by
  intro q
  unfold Ochr.natPlace; grows_go ih

theorem step_projIn (ih : MachineGrows tb nf) :
    ∀ (p : Place), GrowsIn tb (Ochr.projIn ((nf + 1)) p) := by
  intro p
  unfold Ochr.projIn; grows_go ih

theorem step_projMatch (ih : MachineGrows tb nf) :
    ∀ (q : Place) (i : Nat) (k : Place → Term), GrowsIn tb (Ochr.projMatch ((nf + 1)) q i k) := by
  intro q i k
  unfold Ochr.projMatch; grows_go ih

theorem step_depFieldType (ih : MachineGrows tb nf) :
    ∀ (d : IndDecl) (ps : List Value) (g : FieldRef) (q : Place) (declared : Bool), GrowsIn tb (Ochr.depFieldType ((nf + 1)) d ps g q declared) := by
  intro d ps g q declared
  unfold Ochr.depFieldType; grows_go ih

end Ochr.Meaning.Steps.Machine

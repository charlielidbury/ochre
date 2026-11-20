import Ochr.Meaning.Steps.Machine.IH

/-!
# The step of the induction for the machine's block: matches, refinement, generalisation

Each function at fuel `n + 1`, its body walked by `grows_go ih` (the induction hypothesis at `n`).
-/

namespace Ochr.Meaning.Steps.Machine

open Ochr Ochr.Meaning Ochr.Meaning.Steps

variable {tb : Tab} {nf : Nat}

theorem step_refine (ih : MachineGrows tb nf) :
    ∀ (σ : Nat) (r : Value), GrowsIn tb (Ochr.refine ((nf + 1)) σ r) := by
  intro σ r
  unfold Ochr.refine; grows_go ih

theorem step_evalMatch (ih : MachineGrows tb nf) :
    ∀ (typed : Bool) (p : Place) (z : Term) (s : Term) (expected : Option Value) (tail : Bool), GrowsIn tb (Ochr.evalMatch ((nf + 1)) typed p z s expected tail) := by
  intro typed p z s expected tail
  unfold Ochr.evalMatch; grows_go ih

theorem step_natScrutinee (ih : MachineGrows tb nf) :
    ∀ (p : Place), GrowsIn tb (Ochr.natScrutinee ((nf + 1)) p) := by
  intro p
  unfold Ochr.natScrutinee; grows_go ih

theorem step_generalizeNeutral (ih : MachineGrows tb nf) :
    ∀ (p : Place) (n : Value), GrowsIn tb (Ochr.generalizeNeutral ((nf + 1)) p n) := by
  intro p n
  unfold Ochr.generalizeNeutral; grows_go ih

theorem step_sealedResultTypeQ (ih : MachineGrows tb nf) :
    ∀ (t : Term), GrowsIn tb (Ochr.sealedResultType? ((nf + 1)) t) := by
  intro t
  unfold Ochr.sealedResultType?; grows_go ih

theorem step_renormAll (ih : MachineGrows tb nf) :
    GrowsIn tb (Ochr.renormAll ((nf + 1))) := by
  unfold Ochr.renormAll; grows_go ih

theorem step_renormV (ih : MachineGrows tb nf) :
    ∀ (v : Value), GrowsIn tb (Ochr.renormV ((nf + 1)) v) := by
  intro v
  unfold Ochr.renormV; grows_go ih

theorem step_renormT (ih : MachineGrows tb nf) :
    ∀ (t : Term), GrowsIn tb (Ochr.renormT ((nf + 1)) t) := by
  intro t
  unfold Ochr.renormT; grows_go ih

theorem step_splitThenClose (ih : MachineGrows tb nf) :
    ∀ (p : Place) (z : Term) (s : Term) (σ : Nat) (expected : Option Value), GrowsIn tb (Ochr.splitThenClose ((nf + 1)) p z s σ expected) := by
  intro p z s σ expected
  unfold Ochr.splitThenClose; grows_go ih

theorem step_splitArmsThenClose (ih : MachineGrows tb nf) :
    ∀ (mt : Term) (σ : Nat) (arms : List (M Value × Term)) (harms : ∀ a ∈ arms, GrowsIn tb a.1) (expected : Option Value), GrowsIn tb (Ochr.splitArmsThenClose ((nf + 1)) mt σ arms expected) := by
  intro mt σ arms harms expected
  unfold Ochr.splitArmsThenClose; grows_go ih

theorem step_ctorRefinement (ih : MachineGrows tb nf) :
    ∀ (d : IndDecl) (ps : List Value) (c : Nat), GrowsIn tb (Ochr.ctorRefinement ((nf + 1)) d ps c) := by
  intro d ps c
  unfold Ochr.ctorRefinement; grows_go ih

theorem step_scrutType (ih : MachineGrows tb nf) :
    ∀ (p : Place) (ty : String), GrowsIn tb (Ochr.scrutType ((nf + 1)) p ty) := by
  intro p ty
  unfold Ochr.scrutType; grows_go ih

theorem step_evalMatchByType (ih : MachineGrows tb nf) :
    ∀ (typed : Bool) (p : Place) (ty : String) (arms : List (Hint × Term)) (expected : Option Value) (tail : Bool), GrowsIn tb (Ochr.evalMatchByType ((nf + 1)) typed p ty arms expected tail) := by
  intro typed p ty arms expected tail
  unfold Ochr.evalMatchByType; grows_go ih

theorem step_evalMatchInd (ih : MachineGrows tb nf) :
    ∀ (typed : Bool) (p : Place) (ty : String) (arms : List (Hint × Term)) (expected : Option Value) (tail : Bool), GrowsIn tb (Ochr.evalMatchInd ((nf + 1)) typed p ty arms expected tail) := by
  intro typed p ty arms expected tail
  unfold Ochr.evalMatchInd; grows_go ih

theorem step_etaInPlace (ih : MachineGrows tb nf) :
    ∀ (σ : Nat) (d : IndDecl) (ps : List Value), GrowsIn tb (Ochr.etaInPlace ((nf + 1)) σ d ps) := by
  intro σ d ps
  unfold Ochr.etaInPlace; grows_go ih

theorem step_etaPlace (ih : MachineGrows tb nf) :
    ∀ (q : Place), GrowsIn tb (Ochr.etaPlace ((nf + 1)) q) := by
  intro q
  unfold Ochr.etaPlace; grows_go ih

theorem step_movedPlace (ih : MachineGrows tb nf) :
    ∀ (q : Place), GrowsIn tb (Ochr.movedPlace ((nf + 1)) q) := by
  intro q
  unfold Ochr.movedPlace; grows_go ih

end Ochr.Meaning.Steps.Machine

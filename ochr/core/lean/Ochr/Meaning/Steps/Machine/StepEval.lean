import Ochr.Meaning.Steps.Machine.IH

/-!
# The step of the induction for the machine's block: evaluation

Each function at fuel `nf + 1`, its body walked by `grows_go ih` (the induction hypothesis at `nf`).
-/

namespace Ochr.Meaning.Steps.Machine

open Ochr Ochr.Meaning Ochr.Meaning.Steps

variable {tb : Tab} {nf : Nat}

theorem step_mkEqM (ih : MachineGrows tb nf) :
    ∀ (A : Value) (a : Value) (b : Value), GrowsIn tb (Ochr.mkEqM ((nf + 1)) A a b) := by
  intro A a b
  unfold Ochr.mkEqM; grows_go ih

theorem step_rewriteGoal (ih : MachineGrows tb nf) :
    ∀ (rev : Bool) (h : Term) (G : Value), GrowsIn tb (Ochr.rewriteGoal ((nf + 1)) rev h G) := by
  intro rev h G
  unfold Ochr.rewriteGoal; grows_go ih

theorem step_expectTy (ih : MachineGrows tb nf) :
    ∀ (what : String) (T : Option Value) (A : Value), GrowsIn tb (Ochr.expectTy ((nf + 1)) what T A) := by
  intro what T A
  unfold Ochr.expectTy; grows_go ih

theorem step_eval (ih : MachineGrows tb nf) :
    ∀ (typed : Bool) (t : Term) (hint : Option Value), GrowsIn tb (Ochr.eval ((nf + 1)) typed t hint) := by
  intro typed t hint
  unfold Ochr.eval; grows_go ih

theorem step_evalAt (ih : MachineGrows tb nf) :
    ∀ (typed : Bool) (t : Term) (hint : Option Value), GrowsIn tb (Ochr.evalAt ((nf + 1)) typed t hint) := by
  intro typed t hint
  unfold Ochr.evalAt; grows_go ih

theorem step_jMotiveAt (ih : MachineGrows tb nf) :
    ∀ (A : Term) (P : Term) (av : Value), GrowsIn tb (Ochr.jMotiveAt ((nf + 1)) A P av) := by
  intro A P av
  unfold Ochr.jMotiveAt; grows_go ih

set_option maxHeartbeats 4000000 in
theorem step_evalCore (ih : MachineGrows tb nf) :
    ∀ (typed : Bool) (t : Term) (hint : Option Value), GrowsIn tb (Ochr.evalCore ((nf + 1)) typed t hint) := by
  intro typed t hint
  unfold Ochr.evalCore; grows_go ih

theorem step_lentProofAssign (ih : MachineGrows tb nf) :
    ∀ (p : Place) (u : Term), GrowsIn tb (Ochr.lentProofAssign ((nf + 1)) p u) := by
  intro p u
  unfold Ochr.lentProofAssign; grows_go ih

theorem step_evalTInd (ih : MachineGrows tb nf) :
    ∀ (typed : Bool) (n : String) (as : List Term), GrowsIn tb (Ochr.evalTInd ((nf + 1)) typed n as) := by
  intro typed n as
  unfold Ochr.evalTInd; grows_go ih

theorem step_evalParams (ih : MachineGrows tb nf) :
    ∀ (n : String) (as : List Term) (typed : Bool), GrowsIn tb (Ochr.evalParams ((nf + 1)) n as typed) := by
  intro n as typed
  unfold Ochr.evalParams; grows_go ih

theorem step_checkParams (ih : MachineGrows tb nf) :
    ∀ (d : IndDecl) (n : String) (vs : Array Value) (tys : Array (Option Value)), GrowsIn tb (Ochr.checkParams ((nf + 1)) d n vs tys) := by
  intro d n vs tys
  unfold Ochr.checkParams; grows_go ih

theorem step_evalCtor (ih : MachineGrows tb nf) :
    ∀ (typed : Bool) (ty : String) (c : Nat) (h : Hint) (pts : List Term) (as : List Term) (hint : Option Value), GrowsIn tb (Ochr.evalCtor ((nf + 1)) typed ty c h pts as hint) := by
  intro typed ty c h pts as hint
  unfold Ochr.evalCtor; grows_go ih

end Ochr.Meaning.Steps.Machine

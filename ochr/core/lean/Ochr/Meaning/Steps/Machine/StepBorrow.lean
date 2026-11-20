import Ochr.Meaning.Steps.Machine.IH

/-!
# The step of the induction for the machine's block: borrows ([End], [Access], [Repack])

Each function at fuel `n + 1`, its body walked by `grows_go ih` (the induction hypothesis at `n`).
-/

namespace Ochr.Meaning.Steps.Machine

open Ochr Ochr.Meaning Ochr.Meaning.Steps

variable {tb : Tab} {nf : Nat}

theorem step_endBorrow (ih : MachineGrows tb nf) :
    ∀ (l : Nat), GrowsIn tb (Ochr.endBorrow ((nf + 1)) l) := by
  intro l
  unfold Ochr.endBorrow; grows_go ih

theorem step_lentUnknown (ih : MachineGrows tb nf) :
    ∀ (v : Value), GrowsIn tb (Ochr.lentUnknown ((nf + 1)) v) := by
  intro v
  unfold Ochr.lentUnknown; grows_go ih

theorem step_repackCheck (ih : MachineGrows tb nf) :
    ∀ (what : String) (v : Value) (T : Value), GrowsIn tb (Ochr.repackCheck ((nf + 1)) what v T) := by
  intro what v T
  unfold Ochr.repackCheck; grows_go ih

theorem step_repackAt (ih : MachineGrows tb nf) :
    ∀ (p : Place) (T : Value) (what : String), GrowsIn tb (Ochr.repackAt ((nf + 1)) p T what) := by
  intro p T what
  unfold Ochr.repackAt; grows_go ih

theorem step_bodyReturns (ih : MachineGrows tb nf) :
    ∀ (what : String) (v : Value) (T : Value) (lent : List Place) (lentWhat : String), GrowsIn tb (Ochr.bodyReturns ((nf + 1)) what v T lent lentWhat) := by
  intro what v T lent lentWhat
  unfold Ochr.bodyReturns; grows_go ih

theorem step_endAll (ih : MachineGrows tb nf) :
    GrowsIn tb (Ochr.endAll ((nf + 1))) := by
  unfold Ochr.endAll; grows_go ih

theorem step_obsResult (ih : MachineGrows tb nf) :
    ∀ (r : Value) (σw? : Option Nat), GrowsIn tb (Ochr.obsResult ((nf + 1)) r σw?) := by
  intro r σw?
  unfold Ochr.obsResult; grows_go ih

theorem step_endTopLoan (ih : MachineGrows tb nf) :
    ∀ (l : Nat) (site : String), GrowsIn tb (Ochr.endTopLoan ((nf + 1)) l site) := by
  intro l site
  unfold Ochr.endTopLoan; grows_go ih

theorem step_accessPath (ih : MachineGrows tb nf) :
    ∀ (p : Place), GrowsIn tb (Ochr.accessPath ((nf + 1)) p) := by
  intro p
  unfold Ochr.accessPath; grows_go ih

theorem step_accessInside (ih : MachineGrows tb nf) :
    ∀ (p : Place) (owned : Bool), GrowsIn tb (Ochr.accessInside ((nf + 1)) p owned) := by
  intro p owned
  unfold Ochr.accessInside; grows_go ih

theorem step_accessNeutralHead (ih : MachineGrows tb nf) :
    ∀ (p : Place), GrowsIn tb (Ochr.accessNeutralHead ((nf + 1)) p) := by
  intro p
  unfold Ochr.accessNeutralHead; grows_go ih

end Ochr.Meaning.Steps.Machine

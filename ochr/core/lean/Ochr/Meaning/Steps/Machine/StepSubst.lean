import Ochr.Meaning.Steps.Machine.IH

/-!
# The step of the induction for the machine's block: substitution and normal forms

Each function at fuel `nf + 1`, its body walked by `grows_go ih` (the induction hypothesis at `nf`).
-/

namespace Ochr.Meaning.Steps.Machine

open Ochr Ochr.Meaning Ochr.Meaning.Steps

variable {tb : Tab} {nf : Nat}

theorem step_substV (ih : MachineGrows tb nf) :
    ∀ (x : Value) (r : Value) (v : Value), GrowsIn tb (Ochr.substV ((nf + 1)) x r v) := by
  intro x r v
  unfold Ochr.substV; grows_go ih

theorem step_substT (ih : MachineGrows tb nf) :
    ∀ (x : Value) (r : Value) (t : Term), GrowsIn tb (Ochr.substT ((nf + 1)) x r t) := by
  intro x r t
  unfold Ochr.substT; grows_go ih

theorem step_substEnv (ih : MachineGrows tb nf) :
    ∀ (x : Value) (r : Value) (types : Bool), GrowsIn tb (Ochr.substEnv ((nf + 1)) x r types) := by
  intro x r types
  unfold Ochr.substEnv; grows_go ih

theorem step_nfSealed (ih : MachineGrows tb nf) :
    ∀ (t : Term), GrowsIn tb (Ochr.nfSealed ((nf + 1)) t) := by
  intro t
  unfold Ochr.nfSealed; grows_go ih

end Ochr.Meaning.Steps.Machine

import Ochr.Meaning.Steps.Machine.IH

/-!
# The step of the induction for the machine's block: the comparison

Each function at fuel `nf + 1`, its body walked by `grows_go ih` (the induction hypothesis at `nf`).
-/

namespace Ochr.Meaning.Steps.Machine

open Ochr Ochr.Meaning Ochr.Meaning.Steps

variable {tb : Tab} {nf : Nat}

theorem step_conv (ih : MachineGrows tb nf) :
    ∀ (v : Value) (w : Value), GrowsIn tb (Ochr.conv ((nf + 1)) v w) := by
  intro v w
  unfold Ochr.conv; grows_go ih

theorem step_convList (ih : MachineGrows tb nf) :
    ∀ (as : List Value) (bs : List Value), GrowsIn tb (Ochr.convList ((nf + 1)) as bs) := by
  intro as bs
  unfold Ochr.convList; grows_go ih

theorem step_convTList (ih : MachineGrows tb nf) :
    ∀ (as : List Term) (bs : List Term), GrowsIn tb (Ochr.convTList ((nf + 1)) as bs) := by
  intro as bs
  unfold Ochr.convTList; grows_go ih

theorem step_convPi (ih : MachineGrows tb nf) :
    ∀ (P : Value) (Q : Value), GrowsIn tb (Ochr.convPi ((nf + 1)) P Q) := by
  intro P Q
  unfold Ochr.convPi; grows_go ih

theorem step_convT (ih : MachineGrows tb nf) :
    ∀ (t : Term) (u : Term), GrowsIn tb (Ochr.convT ((nf + 1)) t u) := by
  intro t u
  unfold Ochr.convT; grows_go ih

theorem step_convFn (ih : MachineGrows tb nf) :
    ∀ (f : Value) (g : Value), GrowsIn tb (Ochr.convFn ((nf + 1)) f g) := by
  intro f g
  unfold Ochr.convFn; grows_go ih

theorem step_convFnRun (ih : MachineGrows tb nf) :
    ∀ (f : Value) (g : Value) (pf : Value) (cs : List Value) (hs : List Hint) (ds : List Term) (c : Term), GrowsIn tb (Ochr.convFnRun ((nf + 1)) f g pf cs hs ds c) := by
  intro f g pf cs hs ds c
  unfold Ochr.convFnRun; grows_go ih

end Ochr.Meaning.Steps.Machine

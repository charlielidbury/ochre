import Ochr.Meaning.Steps.Machine.IH

/-!
# The step of the induction for the machine's block: the join and stuck blocks

Each function at fuel `nf + 1`, its body walked by `grows_go ih` (the induction hypothesis at `nf`).
-/

namespace Ochr.Meaning.Steps.Machine

open Ochr Ochr.Meaning Ochr.Meaning.Steps

variable {tb : Tab} {nf : Nat}

theorem step_staticJoin (ih : MachineGrows tb nf) :
    ∀ (mt : Term), GrowsIn tb (Ochr.staticJoin ((nf + 1)) mt) := by
  intro mt
  unfold Ochr.staticJoin; grows_go ih

theorem step_joinDrop (ih : MachineGrows tb nf) :
    ∀ (mt : Term) (run : M (Value × Option Value)) (hrun : GrowsIn tb run), GrowsIn tb (Ochr.joinDrop ((nf + 1)) mt run) := by
  intro mt run hrun
  unfold Ochr.joinDrop; grows_go ih

theorem step_joinCont (ih : MachineGrows tb nf) :
    ∀ (mt : Term) (k : Value → Value → M Unit) (hk : ∀ r R, GrowsIn tb (k r R)), GrowsIn tb (Ochr.joinCont ((nf + 1)) mt k) := by
  intro mt k hk
  unfold Ochr.joinCont; grows_go ih

theorem step_joinEnds (ih : MachineGrows tb nf) :
    ∀ (mt : Term) (tail : Bool) (run : M (Value × Option Value)) (hrun : GrowsIn tb run), GrowsIn tb (Ochr.joinEnds ((nf + 1)) mt tail run) := by
  intro mt tail run hrun
  unfold Ochr.joinEnds; grows_go ih

theorem step_blockEntry (ih : MachineGrows tb nf) :
    ∀ (mt : Term), GrowsIn tb (Ochr.blockEntry ((nf + 1)) mt) := by
  intro mt
  unfold Ochr.blockEntry; grows_go ih

theorem step_entryAccess (ih : MachineGrows tb nf) :
    ∀ (capsS : Array (Place × Nat)), GrowsIn tb (Ochr.entryAccess ((nf + 1)) capsS) := by
  intro capsS
  unfold Ochr.entryAccess; grows_go ih

theorem step_dropAtJoin (ih : MachineGrows tb nf) :
    ∀ (q : Place), GrowsIn tb (Ochr.dropAtJoin ((nf + 1)) q) := by
  intro q
  unfold Ochr.dropAtJoin; grows_go ih

theorem step_blockCaptures (ih : MachineGrows tb nf) :
    ∀ (mt : Term) (armMovedAll : List Place), GrowsIn tb (Ochr.blockCaptures ((nf + 1)) mt armMovedAll) := by
  intro mt armMovedAll
  unfold Ochr.blockCaptures; grows_go ih

theorem step_closeBlock (ih : MachineGrows tb nf) :
    ∀ (mt : Term) (arms : List BlockArm) (harms : ∀ a ∈ arms, GrowsIn tb a.setup ∧ ∀ r, GrowsIn tb (a.body r)) (B? : Option Value), GrowsIn tb (Ochr.closeBlock ((nf + 1)) mt arms B?) := by
  intro mt arms harms B?
  unfold Ochr.closeBlock; grows_go ih

end Ochr.Meaning.Steps.Machine

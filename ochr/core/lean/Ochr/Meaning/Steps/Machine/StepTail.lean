import Ochr.Meaning.Steps.Machine.IH

/-!
# The step of the induction for the machine's block: observations, Id, tail position, [Fix]

Each function at fuel `n + 1`, its body walked by `grows_go ih` (the induction hypothesis at `n`).
-/

namespace Ochr.Meaning.Steps.Machine

open Ochr Ochr.Meaning Ochr.Meaning.Steps

variable {tb : Tab} {nf : Nat}

/-- `observe` at `n + 1` (as `evalType_succ`: the fuel's match sits under `inStatement`). -/
theorem observe_succ (n : Nat) (typed : Bool) (t : Term) (A : Value) (W : List Pos) (refs : List (Place × Value)) :
    Ochr.observe (n + 1) typed t A W refs = inStatement (do
      let o := (← get).obsFrame
      let f ← topIdx
      let fr := (← get).env[f]!
      modify fun s => { s with obsFrame := some (f, fr.binds.size, fr.temps.size) }
      let (v, T) ← onFail (eval n typed t A) (modify fun s => { s with obsFrame := o })
      modify fun s => { s with obsFrame := none }
      expectTy n "a side of Id" T A
      pushTemp v
      for (y, σ) in refs do
        fire .ObsRef fun _ => s!"{σ} written through a re-pointed borrow"
        assignPlace n (.deref y) σ
      let v ← popTemp
      let v ← obsResult n v none
      let ws ← W.mapM getAt
      pure (v, ws)) := rfl

theorem step_observe (ih : MachineGrows tb nf) :
    ∀ (typed : Bool) (t : Term) (A : Value) (W : List Pos) (refs : List (Place × Value)), GrowsIn tb (Ochr.observe ((nf + 1)) typed t A W refs) := by
  intro typed t A W refs
  rw [observe_succ]; grows_go ih

theorem step_idType (ih : MachineGrows tb nf) :
    ∀ (typed : Bool) (A : Term) (t : Term) (u : Term), GrowsIn tb (Ochr.idType ((nf + 1)) typed A t u) := by
  intro typed A t u
  unfold Ochr.idType; grows_go ih

theorem step_stuckScrutinee (ih : MachineGrows tb nf) :
    ∀ (t : Term), GrowsIn tb (Ochr.stuckScrutinee ((nf + 1)) t) := by
  intro t
  unfold Ochr.stuckScrutinee; grows_go ih

theorem step_findSplit (ih : MachineGrows tb nf) :
    ∀ (f : String) (G : Value), GrowsIn tb (Ochr.findSplit ((nf + 1)) f G) := by
  intro f G
  unfold Ochr.findSplit; grows_go ih

theorem step_generalizeFound (ih : MachineGrows tb nf) :
    ∀ (n : Value) (T : Value), GrowsIn tb (Ochr.generalizeFound ((nf + 1)) n T) := by
  intro n T
  unfold Ochr.generalizeFound; grows_go ih

theorem step_splitTarget (ih : MachineGrows tb nf) :
    ∀ (f : String), GrowsIn tb (Ochr.splitTarget ((nf + 1)) f) := by
  intro f
  unfold Ochr.splitTarget; grows_go ih

theorem step_checkTail (ih : MachineGrows tb nf) :
    ∀ (t : Term) (k : Value → Value → M Unit) (hk : ∀ r R, GrowsIn tb (k r R)), GrowsIn tb (Ochr.checkTail ((nf + 1)) t k) := by
  intro t k hk
  unfold Ochr.checkTail; grows_go ih

theorem step_checkTailAt (ih : MachineGrows tb nf) :
    ∀ (t : Term) (k : Value → Value → M Unit) (hk : ∀ r R, GrowsIn tb (k r R)), GrowsIn tb (Ochr.checkTailAt ((nf + 1)) t k) := by
  intro t k hk
  unfold Ochr.checkTailAt; grows_go ih

theorem step_checkFix (ih : MachineGrows tb nf) :
    ∀ (fv : Value) (cs : List Value) (t : Term) (capRec : Array (Option Nat)) (rd : List (DeclInfo × Value)), GrowsIn tb (Ochr.checkFix ((nf + 1)) fv cs t capRec rd) := by
  intro fv cs t capRec rd
  unfold Ochr.checkFix; grows_go ih

end Ochr.Meaning.Steps.Machine

import Ochr.Meaning.Steps.Machine.IH

/-!
# The step of the induction for the machine's block: calls

Each function at fuel `nf + 1`, its body walked by `grows_go ih` (the induction hypothesis at `nf`).
-/

namespace Ochr.Meaning.Steps.Machine

open Ochr Ochr.Meaning Ochr.Meaning.Steps

variable {tb : Tab} {nf : Nat}

theorem step_unknownLent (ih : MachineGrows tb nf) :
    ∀ (what : String) (ls : List Nat), GrowsIn tb (Ochr.unknownLent ((nf + 1)) what ls) := by
  intro what ls
  unfold Ochr.unknownLent; grows_go ih

theorem step_lentLeafCheck (ih : MachineGrows tb nf) :
    ∀ (p : Place) (Tv : Option Value), GrowsIn tb (Ochr.lentLeafCheck ((nf + 1)) p Tv) := by
  intro p Tv
  unfold Ochr.lentLeafCheck; grows_go ih

theorem step_stmtCallee (ih : MachineGrows tb nf) :
    ∀ (fv : Value) (fT : Option Value) (cls? : Option Nat), GrowsIn tb (Ochr.stmtCallee ((nf + 1)) fv fT cls?) := by
  intro fv fT cls?
  unfold Ochr.stmtCallee; grows_go ih

theorem step_evalCall (ih : MachineGrows tb nf) :
    ∀ (typed : Bool) (f : Term) (as : List Term) (head : Bool) (cls? : Option Nat) (res? : Option DeclInfo) (given : Option (Value × List Value)), GrowsIn tb (Ochr.evalCall ((nf + 1)) typed f as head cls? res? given) := by
  intro typed f as head cls? res? given
  unfold Ochr.evalCall; grows_go ih

theorem step_argHint (ih : MachineGrows tb nf) :
    ∀ (fv : Value) (fT : Option Value) (ws : Array Value), GrowsIn tb (Ochr.argHint ((nf + 1)) fv fT ws) := by
  intro fv fT ws
  unfold Ochr.argHint; grows_go ih

theorem step_funTypeQ (ih : MachineGrows tb nf) :
    ∀ (fv : Value) (fT : Option Value), GrowsIn tb (Ochr.funType? ((nf + 1)) fv fT) := by
  intro fv fT
  unfold Ochr.funType?; grows_go ih

theorem step_funType (ih : MachineGrows tb nf) :
    ∀ (fv : Value) (fT : Option Value), GrowsIn tb (Ochr.funType ((nf + 1)) fv fT) := by
  intro fv fT
  unfold Ochr.funType; grows_go ih

theorem step_callType (ih : MachineGrows tb nf) :
    ∀ (piTy : Value) (ws : Array Value) (tys : Array (Option Value)), GrowsIn tb (Ochr.callType ((nf + 1)) piTy ws tys) := by
  intro piTy ws tys
  unfold Ochr.callType; grows_go ih

theorem step_declCallType (ih : MachineGrows tb nf) :
    ∀ (piTy : Value) (ws : Array Value), GrowsIn tb (Ochr.declCallType ((nf + 1)) piTy ws) := by
  intro piTy ws
  unfold Ochr.declCallType; grows_go ih

theorem step_paramTypes (ih : MachineGrows tb nf) :
    ∀ (piTy : Value) (ws : List Value) (need : List Nat), GrowsIn tb (Ochr.paramTypes ((nf + 1)) piTy ws need) := by
  intro piTy ws need
  unfold Ochr.paramTypes; grows_go ih

theorem step_bindTyQ (ih : MachineGrows tb nf) :
    ∀ (pos : Pos), GrowsIn tb (Ochr.bindTy? ((nf + 1)) pos) := by
  intro pos
  unfold Ochr.bindTy?; grows_go ih

theorem step_endBorrowArgs (ih : MachineGrows tb nf) :
    ∀ (n : Nat), GrowsIn tb (Ochr.endBorrowArgs ((nf + 1)) n) := by
  intro n
  unfold Ochr.endBorrowArgs; grows_go ih

theorem step_runBody (ih : MachineGrows tb nf) :
    ∀ (fv : Value) (cs : List Value) (t : Term) (rd : List (DeclInfo × Value)) (ws : Array Value) (B : Option Value), GrowsIn tb (Ochr.runBody ((nf + 1)) fv cs t rd ws B) := by
  intro fv cs t rd ws B
  unfold Ochr.runBody; grows_go ih

theorem step_runBodyCore (ih : MachineGrows tb nf) :
    ∀ (fv : Value) (cs : List Value) (t : Term) (rd : List (DeclInfo × Value)) (ws : Array Value) (B : Option Value) (self : Hint) (hs : List Hint) (ds : List Term) (c : Term) (body : Term), GrowsIn tb (Ochr.runBodyCore ((nf + 1)) fv cs t rd ws B self hs ds c body) := by
  intro fv cs t rd ws B self hs ds c body
  unfold Ochr.runBodyCore; grows_go ih

set_option maxHeartbeats 4000000 in
theorem step_callFn (ih : MachineGrows tb nf) :
    ∀ (typed : Bool) (fT : Option Value) (n : Nat) (tys : Array (Option Value)) (head : Bool) (cls? : Option Nat) (recUid? : Option Nat) (res : DeclInfo) (fills : Array Bool) (want : Bool) (defer : Bool) (resTy : Option Value), GrowsIn tb (Ochr.callFn ((nf + 1)) typed fT n tys head cls? recUid? res fills want defer resTy) := by
  intro typed fT n tys head cls? recUid? res fills want defer resTy
  unfold Ochr.callFn; grows_go ih

theorem step_closeCall (ih : MachineGrows tb nf) :
    ∀ (n : Nat) (kind : Kind) (res : DeclInfo) (fills : Array Bool) (tys : Array (Option Value)), GrowsIn tb (Ochr.closeCall ((nf + 1)) n kind res fills tys) := by
  intro n kind res fills tys
  unfold Ochr.closeCall; grows_go ih

end Ochr.Meaning.Steps.Machine

import Ochr.Meaning.Steps.Machine.IH

/-!
# The step of the induction for the machine's block: values' types, fields, captures

Each function at fuel `nf + 1`, its body walked by `grows_go ih` (the induction hypothesis at `nf`).
-/

namespace Ochr.Meaning.Steps.Machine

open Ochr Ochr.Meaning Ochr.Meaning.Steps

variable {tb : Tab} {nf : Nat}

theorem step_packedErr (ih : MachineGrows tb nf) :
    ∀ (v : Value) (T : Value), GrowsIn tb (Ochr.packedErr ((nf + 1)) v T) := by
  intro v T
  unfold Ochr.packedErr; grows_go ih

theorem step_convVal (ih : MachineGrows tb nf) :
    ∀ (v : Value) (T : Value), GrowsIn tb (Ochr.convVal ((nf + 1)) v T) := by
  intro v T
  unfold Ochr.convVal; grows_go ih

theorem step_valTypeQ (ih : MachineGrows tb nf) :
    ∀ (v : Value), GrowsIn tb (Ochr.valType? ((nf + 1)) v) := by
  intro v
  unfold Ochr.valType?; grows_go ih

theorem step_valType (ih : MachineGrows tb nf) :
    ∀ (v : Value), GrowsIn tb (Ochr.valType ((nf + 1)) v) := by
  intro v
  unfold Ochr.valType; grows_go ih

theorem step_sealedTypeQ (ih : MachineGrows tb nf) :
    ∀ (t : Term), GrowsIn tb (Ochr.sealedType? ((nf + 1)) t) := by
  intro t
  unfold Ochr.sealedType?; grows_go ih

theorem step_fieldDeclType (ih : MachineGrows tb nf) :
    ∀ (p : Place), GrowsIn tb (Ochr.fieldDeclType ((nf + 1)) p) := by
  intro p
  unfold Ochr.fieldDeclType; grows_go ih

theorem step_fieldTele (ih : MachineGrows tb nf) :
    ∀ (d : IndDecl) (ps : List Value) (c : Nat) (val : Nat → Value → M Value) (hval : ∀ i v, GrowsIn tb (val i v)) (upto : Option Nat), GrowsIn tb (Ochr.fieldTele ((nf + 1)) d ps c val upto) := by
  intro d ps c val hval upto
  unfold Ochr.fieldTele; grows_go ih

theorem step_fieldTypes (ih : MachineGrows tb nf) :
    ∀ (d : IndDecl) (ps : List Value) (c : Nat), GrowsIn tb (Ochr.fieldTypes ((nf + 1)) d ps c) := by
  intro d ps c
  unfold Ochr.fieldTypes; grows_go ih

theorem step_fieldTypesOf (ih : MachineGrows tb nf) :
    ∀ (d : IndDecl) (ps : List Value) (c : Nat) (fs : List Value) (upto : Option Nat), GrowsIn tb (Ochr.fieldTypesOf ((nf + 1)) d ps c fs upto) := by
  intro d ps c fs upto
  unfold Ochr.fieldTypesOf; grows_go ih

theorem step_fieldsGeneric (ih : MachineGrows tb nf) :
    ∀ (d : IndDecl) (ps : List Value) (c : Nat), GrowsIn tb (Ochr.fieldsGeneric ((nf + 1)) d ps c) := by
  intro d ps c
  unfold Ochr.fieldsGeneric; grows_go ih

theorem step_fieldTypeAt (ih : MachineGrows tb nf) :
    ∀ (d : IndDecl) (sol : Array (Option Value)) (c : Nat) (i : Nat) (earlier : List Value), GrowsIn tb (Ochr.fieldTypeAt ((nf + 1)) d sol c i earlier) := by
  intro d sol c i earlier
  unfold Ochr.fieldTypeAt; grows_go ih

theorem step_indValTypeQ (ih : MachineGrows tb nf) :
    ∀ (t : String) (c : Nat) (fs : List Value), GrowsIn tb (Ochr.indValType? ((nf + 1)) t c fs) := by
  intro t c fs
  unfold Ochr.indValType?; grows_go ih

theorem step_bindDataFields (ih : MachineGrows tb nf) :
    ∀ (p : Place) (d : IndDecl) (ps : List Value) (c : Nat) (arm : Term), GrowsIn tb (Ochr.bindDataFields ((nf + 1)) p d ps c arm) := by
  intro p d ps c arm
  unfold Ochr.bindDataFields; grows_go ih

theorem step_piSort (ih : MachineGrows tb nf) :
    ∀ (T : Value), GrowsIn tb (Ochr.piSort ((nf + 1)) T) := by
  intro T
  unfold Ochr.piSort; grows_go ih

/-- `evalType` at `n + 1` (its equation lemmas time out when generated: the fuel's match sits under
`inStatement`; at `n + 1` the unfolding is `rfl`). -/
theorem evalType_succ (n : Nat) (t : Term) : Ochr.evalType (n + 1) t = inStatement (do
      let (v, T) ← eval n true t
      match T with
      | some (.sort _) => pure v
      | some T => err s!"{t.pp []} is not a type (it has type {T})"
      | none => pure v) := rfl

theorem step_evalType (ih : MachineGrows tb nf) :
    ∀ (t : Term), GrowsIn tb (Ochr.evalType ((nf + 1)) t) := by
  intro t
  rw [evalType_succ]; grows_go ih

theorem step_capture (ih : MachineGrows tb nf) :
    ∀ (t : Term), GrowsIn tb (Ochr.capture ((nf + 1)) t) := by
  intro t
  unfold Ochr.capture; grows_go ih

end Ochr.Meaning.Steps.Machine
